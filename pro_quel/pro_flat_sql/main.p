/************************************************************************/
/************************************************************************/
/*              m a i n . p                                             */
/*                                                                      */
/* Export:                                                              */
/*              db_tab/2 (meta.p)                                       */
/*              mem/2 (parser.p,checker.p,meta.p,eval.p)                */
/*              append/3 (meta.p)                                       */
/*              set_of/3 (checker.p,eval.p)                             */
/* Import:                                                              */
/*              scantokens/3 (parser.p)                                 */
/*              uscntokens/3 (parser.p)                                 */
/*              parsrule/5 (parser.p)                                   */
/*              parscom/3 (parser.p)                                    */
/*              uparform/3 (parser.p)                                   */
/*              uparrule/5 (parser.p)                                   */
/*              upardecl/4 (parser.p)                                   */
/*              chk/3 (checker.p)                                       */
/*              rewrite_form/4 (checker.p)                              */
/*              norm/3 (checker.p)                                      */
/*              varof/2 (checker.p)                                     */
/*              allowed/2 (checker.p)                                   */
/*              predof/3 (checker.p)                                    */
/*              stratified/2 (checker.p)                                */
/*              plan/2 (checker.p)                                      */
/*              db_fetch/1 (meta.p)                                     */
/*              db_insert/1 (meta.p)                                    */
/*              db_delete/1 (meta.p)                                    */
/*              ev_open_db/1 (eval.p)                                   */
/*              ev_close_db/0 (eval.p)                                  */
/*              ev_create_pred/2 (eval.p)                               */
/*              ev_clear_pred/1 (eval.p)                                */
/*              ev_drop_pred/1 (eval.p)                                 */
/*              ev_insert_res/3 (eval.p)                                */
/*              ev_query_res/4 (eval.p)                                 */
/*              err/1 (error.p)                                         */
/************************************************************************/
/************************************************************************/

:- op(1190,fx,'type').
:- op(1190,fx,'pred').
:- op(1190,fx,'dcg').
:- op(100,fx,'*').

(type X) :- write((:- type X)), nl.
(pred X) :- write((:- pred X)), nl.
(dcg X) :- write((:- dcg X)), nl.

:- multifile db_tab/2.

:- reconsult('parser.p').
:- reconsult('checker.p').
:- reconsult('meta.p').
:- reconsult('eval.p').
:- reconsult('error.p').

/************************************************************************/
/************************************************************************/
/* S C H E M A								*/
/************************************************************************/
/************************************************************************/

:- type fact = cache(str) + deps(str,int,str,int) + pred(str,str) 
             + rule(str,int,str) + type(str,str) + used(str,int,str).

:- pred db_tab(str,*etype). /* mini data base schema */

db_tab(cache,[s]).
db_tab(deps,[s,n(i),s,n(i)]).
db_tab(pred,[s,s]).
db_tab(rule,[s,n(i),s]).
db_tab(type,[s,s]).
db_tab(used,[s,n(i),s]).

/************************************************************************/
/************************************************************************/
/* U T I L I T I E S							*/
/************************************************************************/
/************************************************************************/

:- pred verbose.

:- pred mem(A,*A).
:- pred append(*A,*A,*A).
:- pred set_of(A,goal,*A).

:- pred readline(*int).
:- pred count(int).

:- pred enter(A).
:- pred collect(*A).
:- pred temp(A).
:- pred counter(int).

mem(X,[X|_]).
mem(X,[_|Y]) :- mem(X,Y).

append([],X,X).
append([X|Y],Z,[X|T]) :- append(Y,Z,T).

set_of(X,P,_) :- P, enter(X), fail.
set_of(_,_,L) :- collect(L).

enter(X) :- clause(temp(X),true), !.
enter(X) :- assertz(temp(X)).

collect([X|Y]) :- retract(temp(X)), !, collect(Y).
collect([]).

readline([X|Y]) :- get0(X), X\==10, !, readline(Y).
readline([]).

count(X) :- retract(counter(Y)), !, X is Y+1, assert(counter(X)).

/************************************************************************/
/************************************************************************/
/* O U T P U T								*/
/************************************************************************/
/************************************************************************/

:- pred fill_space(A,int).
:- pred show_col(*etype,*form).
:- pred show_underline(*etype).
:- pred show_result(*etype,mix).
:- pred show_iter(*int,*str).

show_iter([],[]) :- nl.
show_iter([X|Y],[Z|T]) :-
  write(Z), write(':'), write(X), write(' '), !, show_iter(Y,T).

fill_space(X,N) :-
  name(X,L), length(L,M), S is N-M, tab(S).

show_col([],[]) :- nl.
show_col([s|R],[var(X)|Y]) :-
  write(X), fill_space(X,20), tab(1), !, show_col(R,Y).
show_col([n(i)|R],[var(X)|Y]) :-
  fill_space(X,5), write(X), tab(1), !, show_col(R,Y).
show_col([n(f)|R],[var(X)|Y]) :-
  fill_space(X,10), write(X), tab(1), !, show_col(R,Y).

show_underline([]) :- nl.
show_underline([s|Y]) :-
  write('--------------------'), tab(1), !, show_underline(Y).
show_underline([n(i)|Y]) :-
  write('-----'), tab(1), !, show_underline(Y).
show_underline([n(f)|Y]) :- 
  write('----------'), tab(1), !, show_underline(Y).

show_result([],[]) :- nl.
show_result([s|R],[X|Y]) :-
  write(X), fill_space(X,20), tab(1), !, show_result(R,Y).
show_result([n(i)|R],[X|Y]) :-
  fill_space(X,5), write(X), tab(1), !, show_result(R,Y).
show_result([n(f)|R],[X|Y]) :-
  H is integer(X), fill_space(H,5), format("~4f",X), tab(1), !, show_result(R,Y).


/************************************************************************/
/************************************************************************/
/* P L A N   E X E C U T I O N						*/
/************************************************************************/
/************************************************************************/

:- pred exec(*scc).
:- pred exec_scc(scc).
:- pred insert_rule(str).
:- pred iter_fixpoint(*int,*str).
:- pred flush_pred(str).

exec([]).
exec([X|Y]) :- exec(Y), exec_scc(X).

insert_rule(R) :-
  name(R,CS),
  scantokens(TS,CS,[]),
  parsrule(P,H,Q,TS,[]),
  rewrite_form(Q,Q1,0,_),
  norm(Q1,[],NQ),
  ev_insert_res(P,H,NQ).

exec_scc(P-_) :-
  db_fetch(cache(P)), !.
exec_scc(P-[]) :- !, 
  (db_fetch(rule(P,_,R)), insert_rule(R), fail; true),
  db_insert(cache(P)).
exec_scc(_-S) :-
  (mem(Q,S), 
     db_fetch(rule(Q,KEY,R)), 
     \+ (db_fetch(deps(_,KEY,U,_)), mem(U,S)),
     insert_rule(R), fail; true),
  findall(C,(mem(Q,S),ev_count_pred(Q,C)),L),
  iter_fixpoint(L,S),
  (mem(Q,S), db_insert(cache(Q)), fail; true).

iter_fixpoint(L,S) :-
  show_iter(L,S),
  (mem(Q,S),
    db_fetch(rule(Q,KEY,R)),
    \+ \+ (db_fetch(deps(_,KEY,U,_)), mem(U,S)),
    insert_rule(R), fail; true),
  findall(C,(mem(Q,S),ev_count_pred(Q,C)),L1),
  (L1\==L -> iter_fixpoint(L1,S); true).

flush_pred(P) :-
  (\+ db_fetch(cache(P)) -> true;
   ev_clear_pred(P),
   db_delete(cache(P)),
   set_of(Q,db_fetch(deps(Q,_,P,_)),S),
   (mem(Q,S), flush_pred(Q), fail; true)).


/************************************************************************/
/************************************************************************/
/* M A I N   L O O P							*/
/************************************************************************/
/************************************************************************/

:- pred interpret(com).
:- pred proquel(str).

interpret(quit).
interpret(none).
interpret(verbose) :- 
  (\+clause(verbose,true) -> assertz(verbose); retract(verbose)).
interpret(define(N,T)) :- 
  (db_fetch(type(N,_)) -> err(type_already_decl(N));
    set_of(N1,type_of(T,N1),NS),
    (mem(N1,NS),(db_fetch(type(N1,_))->true;err(type_not_decl(N1))),fail;true),\+err_flag,
    upartype(T,L1,[]), uscntokens(L1,L2,[]),
    name(S,L2), db_insert(type(N,S)),
    (mem(N1,NS), db_insert(used(N1,0,N)), fail; true)).
interpret(create(P,A)) :- 
  (db_fetch(pred(P,_)) -> err(pred_already_decl(P));
    set_of(N1,(mem(T,A), type_of(T,N1)),NS),
    (mem(N1,NS),(db_fetch(type(N1,_))->true;err(type_not_decl(N1))),fail;true),\+err_flag,
    expand_list(A,A1),
    ev_create_pred(P,A1), 
    upardecl(A,L1,[]), 
    uscntokens(L1,L2,[]), 
    name(S,L2), db_insert(pred(P,S)),
    (mem(N1,NS), db_insert(used(N1,1,P)), fail; true)).
interpret(undefine(N)) :-
  (db_fetch(used(N,K,S)), err(type_used_in(N,K,S)), fail; true), \+err_flag,
    db_delete(used(_,0,N)),
    db_delete(type(N,_)).
interpret(drop(P)) :-
  (\+ db_fetch(pred(P,_)) -> err(pred_not_decl(P));
    db_fetch(deps(Q,_,P,_)), Q\==P -> err(pred_used_in(P,Q));
    flush_pred(P),
    db_delete(used(_,1,P)),
    db_delete(pred(P,_)),
    db_delete(rule(P,_,_)),
    db_delete(deps(P,_,_,_)),
    ev_drop_pred(P)).
interpret(clear(P)) :-
  (\+ db_fetch(pred(P,_)) -> err(pred_not_decl(P));
    flush_pred(P),
    db_delete(rule(P,_,_)),
    db_delete(deps(P,_,_,_))).
interpret(list) :- 
  (db_fetch(type(P,T)), write(P), write(' = '), write(T), nl, fail; true),
  (db_fetch(pred(P,T)), write(P), write(T), nl, fail; true).
interpret(list(P)) :- 
  (\+ db_fetch(pred(P,_)) -> err(pred_not_decl(P));
    (db_fetch(rule(P,_,S)), write(S), nl, fail; true)).
interpret(query(Q)) :- 
  chk(Q,f,L), \+err_flag,
  rewrite_form(Q,Q1,0,_),
  norm(Q1,[],NQ),
  set_of(var(V),varof(Q,V),H),
  findall(S,(mem(E,H),chk(E,e(S),L)),T),
  allowed(H,NQ), \+err_flag,
  plan(Q,PL),
  exec(PL),
  (T=[] -> (ev_query_res(H,NQ,T,X) -> write('yes'); write('no')), nl;
    show_col(T,H), show_underline(T), 
    (ev_query_res(H,NQ,T,X), show_result(T,X), fail; true)).
interpret(assert(P,H,Q)) :- 
  chk(pred(P,H),f,L), chk(Q,f,L), \+err_flag,
  uparrule(P,H,Q,L1,[]),
  uscntokens(L1,L2,[]),
  name(S,L2),
  (\+db_fetch(rule(P,_,S)) ->
    flush_pred(P),
    rewrite_form(Q,Q1,0,_),
    norm(Q1,[],NQ),
    allowed(H,NQ), \+err_flag,
    stratified(P,Q), \+err_flag,
    repeat, count(KEY), \+db_fetch(rule(P,KEY,_)), !,
    db_insert(rule(P,KEY,S)),
    set_of(U-SG,predof(Q,U,SG),K),
    (mem(U-SG,K), db_insert(deps(P,KEY,U,SG)), fail; true); true).
interpret(retract(P,H,Q)) :- 
  uparrule(P,H,Q,L1,[]),
  uscntokens(L1,L,[]),
  name(S,L),
  (db_fetch(rule(P,KEY,S)) ->
    flush_pred(P),
    db_delete(rule(P,KEY,S)),
    db_delete(deps(P,KEY,_,_)); true).

proquel(S) :-
  ev_open_db(S),
  (retract(counter(_)), fail; true),
  assert(counter(0)),
  repeat,
    (retract(err_flag), fail; true), 
    readline(X),
    scantokens(L,X,[]), \+err_flag,
    parscom(C,L,[]), \+err_flag,
    interpret(C), \+err_flag,
    C=quit, !,
  ev_close_db.

/************************************************************************/
/* .									*/
/************************************************************************/
