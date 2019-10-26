/************************************************************************/
/* Module:	lint.p							*/
/************************************************************************/

:- op(1190,fx,'type').
:- op(1190,fx,'pred').
:- op(1190,fx,'dcg').
:- op(100,fx,'*').
:- op(850,xfx,'::').
:- op(1200,xfx,'<--').

l_body([],[],true).
l_body([X|Y],[Z|T],(X::Z, U)) :- l_body(Y,T,U).

(X::int <-- true) :- integer(X).
(X::float <-- true) :- float(X).
(X::str <-- true) :- atom(X).
foreign(X,Y,_)::goal <-- X::str, Y::str.
(X::T <-- U) :- X=..[F|L], length(L,N), clause(l_rec(F,N,T,R),true), l_body(L,R,U).

l_mem(X,[X|_]).
l_mem(X,[_|Y]) :- l_mem(X,Y).

l_meta(true,_) :- !.
l_meta((A,B),L) :- !, l_meta(A,L), l_meta(B,L).
l_meta('$VAR'(N)::T,L) :- l_mem(N-S,L), !, S=T.
l_meta(A,L) :- (A<--B), l_meta(B,L).

l_why_not((A,B),W,L) :- !, (l_meta(A,L), !, l_why_not(B,W,L); l_why_not(A,W,L)).
l_why_not(A,W,L) :- !, ((A<--B), !, l_why_not(B,W,L); W=A).

l_is_type(X) :- var(X), !.
l_is_type(*X) :- !, l_is_type(X).
l_is_type(X) :- atom(X).

l_is_type_list([]).
l_is_type_list([X|Y]) :- l_is_type(X), l_is_type_list(Y).

l_decl(T,E) :-
  (E=..[F|L], length(L,N), l_is_type(T), l_is_type_list(L), !;
     write('! Error illegal type declaration '), write(T), write(' = '), write(E),
     write('.'), nl, fail),
  (clause(l_rec(F,N,S,_),true), !,
     write('! Warning overloading of '),
     write(F), write('/'), write(N), 
     write(' by '), write(T), write(' and '),
     write(S), write('.'), nl; true),
  assertz(l_rec(F,N,T,L)).

l_err_msg(typing(X,E::T)) :-
  write('! Typing error in: '), write(X), write('.'), nl,
  write('! '), write(E), write(' has not type '), write(T), write('.'), nl. 
l_err_msg(cut_in_or(X)) :-
  write('! Cut (!) in or (;) error in :'), write(X), write('.'), nl.

l_err(E) :-
  retract(l_err_count(N)), !,
  M is N+1,
  assertz(l_err_count(M)),
  (M=<20 -> 
    nl,
    l_err_msg(E),
    current_input(I), line_count(I,C), current_stream(F,_,I),
    write('! In '), write(F), write(' line '), write(C), write('.'), nl;
   M=20 -> 
    write('! Too many errors, supressing subsequent errors.'), nl; true).

l_app([],X,X).
l_app([X|Y],Z,[X|T]) :- l_app(Y,Z,T).

l_hand1(end_of_file) :- !.
l_hand1((:- op(X,Y,Z))) :- !, op(X,Y,Z).
l_hand1((:- reconsult(F))) :- !, l_consult1(F).
l_hand1((:- type T=E+F)) :- !, l_hand1((:- type T=E)), l_hand1((:- type T=F)).
l_hand1((:- type T=E)) :- !, l_decl(T,E).
l_hand1((:- type T==E)) :- !, l_decl(T,E).
l_hand1((:- pred E)) :- !, l_decl(goal,E).
l_hand1((:- dcg E)) :- !, E=..[F|L], l_app(L,[*X,*X],R), G=..[F|R], l_decl(goal,G).
l_hand1(_).

l_consult1(F) :-
  write('! Reading types of '), write(F), nl,
  seeing(T),
  see(F),
  repeat,
    read(C),
    l_hand1(C),
    C=end_of_file, !,
  seen,
  see(T).

l_cut((A,B)) :- (l_cut(A); l_cut(B)).
l_cut(!) :- !.

l_cut_in_or((A,B)) :- (l_cut_in_or(A); l_cut_in_or(B)).
l_cut_in_or((A;B)) :- (l_cut(A); l_cut(B)).

l_chk(X) :- 
  numbervars(X,0,_), 
  (l_meta(X::goal,_); l_why_not(X::goal,W,_), l_err(typing(X,W))), !.
  
l_hand2(end_of_file) :- !.
l_hand2((:- op(_,_,_))) :- !.
l_hand2((:- reconsult(F))) :- !, l_consult2(F).
l_hand2((:- _)) :- !.
l_hand2((:- type _)) :- !.
l_hand2((:- pred _)) :- !.
l_hand2((:- dcg _)) :- !.
l_hand2((H-->B)) :- !, expand_term((H-->B),X), l_hand2(X).
l_hand2(X) :- l_chk(X), 
  (X = (_:-T), l_cut_in_or(T) -> l_err(cut_in_or(X)); true).

l_consult2(F) :-
  nl, 
  write('! Reading clauses of '), write(F), nl,
  seeing(T),
  see(F),
  repeat,
    read(C),
    l_hand2(C),
    C=end_of_file, !,
  seen,
  see(T).

lint(F) :-
  (retract(l_rec(_,_,_,_)), fail; true),
  (retract(l_err_count(_)), fail; true),
  l_consult1('predef.p'),
  assertz(l_err_count(0)),
  l_consult1(F),
  l_consult2(F).

