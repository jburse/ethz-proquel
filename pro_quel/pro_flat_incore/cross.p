/************************************************************************/
/* Module:   	cross.p                                                 */
/* Autor:	Jan Burse						*/
/* Date:	29.10.91						*/
/* Language:	SICStus Prolog						*/
/* Machine:	SunOS 4.1.1						*/
/* Usage:	?- cross(<main module>)					*/
/************************************************************************/

insert(F) :- F, !.
insert(F) :- assert(F).

pred_of(A,_) :- var(A), !, fail.
pred_of((A,B),X) :- !, (pred_of(A,X); pred_of(B,X)).
pred_of((A;B),X) :- !, (pred_of(A,X); pred_of(B,X)).
pred_of((A->B),X) :- !, (pred_of(A,X); pred_of(B,X)).
pred_of((\+A),X) :- !, pred_of(A,X).
pred_of(set_of(_,A,_),X) :- X=set_of/3; pred_of(A,X).
pred_of(H,P/A) :- !, \+ predicate_property(H,built_in), functor(H,P,A).

pred_of_dcg(A,_) :- var(A), !, fail.
pred_of_dcg([],_) :- !, fail.
pred_of_dcg(!,_) :- !, fail.
pred_of_dcg([_|_],_) :- !, fail.
pred_of_dcg({A},X) :- !, pred_of(A,X).
pred_of_dcg((A,B),X) :- !, (pred_of_dcg(A,X); pred_of_dcg(B,X)).
pred_of_dcg(H,P/A) :- !, functor(H,P,A1), A is A1+2.

handle(_,(:-reconsult(R))) :- !, getit(R).
handle(_,(:-op(X,Y,Z))) :- !, op(X,Y,Z).
handle(_,end_of_file) :- !.
handle(M,(H-->B)) :- !,
  functor(H,P,A1), A is A1+2,
  assert(clus(M,P,A)),
  insert(defs(M,P,A)),
  (pred_of_dcg(B,Q/C),
     insert(uses(Q,C,M)),
     fail; true).
handle(M,(H:-B)) :- !, 
  functor(H,P,A), 
  assert(clus(M,P,A)),
  insert(defs(M,P,A)),
  (pred_of(B,Q/C), 
     insert(uses(Q,C,M)),
     fail; true).
handle(M,H) :- !,
  functor(H,P,A), 
  insert(defs(M,P,A)).

getit(M) :-
  write('Reading '), write(M), nl, 
  assert(mods(M)),
  seeing(T),
  see(M),
  repeat,
    read(C),
    handle(M,C),
    C=end_of_file, !,
  seen, 
  see(T).

write_list([]).
write_list([X|Y]) :- 
  write(X), write_list(Y).

size_list([],0).
size_list([X|Y],N) :- 
  name(X,L), length(L,M), size_list(Y,J), N is M+J.

write_comment(L) :-
  write('/*'), write_list(L), size_list(L,N), M is 70-N, tab(M), write('*/'),
  nl.

write_stars :-
  write('/************************************************************************/'),
  nl.

prep_list([X],[X,')']).
prep_list([X|Y],[X,','|Z]) :- prep_list(Y,Z).

prep_wide([],[]).
prep_wide([X|Y],[S,' '|Z]) :- name(S,[X]), prep_wide(Y,Z).

cross(R) :-
  (retract(mods(_)), fail; true),
  (retract(defs(_,_,_)), fail; true),
  (retract(clus(_,_,_)), fail; true),
  (retract(uses(_,_,_)), fail; true),
  getit(R),
  (uses(P,A,M), \+ defs(_,P,A),
    write_list(['Warning: ',P,'/',A,' (',M,') not declared.']), nl, 
    fail; true),
  (mods(M),
    write_stars,
    write_stars,
    name(M,L1), prep_wide(L1,L2),
    write_comment(['              '|L2]),
    write_comment([]),
    write_comment([' Export:']),
    (defs(M,P,A), findall(N,(uses(P,A,N), N\==M),L), L\==[], prep_list(L,H),
       write_comment(['              ',P,'/',A,' ('|H]),
       fail; true),
    write_comment([' Import:']),
    (mods(N), defs(N,P,A), uses(P,A,M), M\==N,
       write_comment(['              ',P,'/',A,' (',N,')']),
       fail; true),
    write_stars,
    write_stars,
    fail; true),
  write('Module'), write('	'), write('Predicates'), write('	'), 
  write('Clauses'), nl,
  write('------------------------------------------'), nl, 
  (mods(M),
    write(M), write('	'), 
     findall([],defs(M,P,A),L1),
     length(L1,N1),
     write(N1), write('	'),
     findall([],clus(M,P,A),L2),
     length(L2,N2),
     write(N2), nl, fail; true).
