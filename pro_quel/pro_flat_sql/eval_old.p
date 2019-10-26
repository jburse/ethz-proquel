/************************************************************************/
/* Module:      eval.p                                                  */
/* Project:     ProQuel                                                 */
/* Language:    SICStus Prolog 0.7 #6                                   */
/* Machine:     SunOS 4.1.1                                             */
/* Export:                                                              */
/*              ev_open_db/1 (main.p)                                   */
/*              ev_close_db/0 (main.p)                                  */
/*              ev_create_pred/2 (main.p)                               */
/*              ev_drop_pred/1 (main.p)                                 */
/*              ev_assert_rule/4 (main.p)                               */
/*              ev_retract_rule/2 (main.p)                              */
/*              ev_query_res/4 (main.p)                                 */
/* Import:                                                              */
/*              mem/2 (main.p)                                       */
/*              set_of/3 (main.p)                                       */
/*              t_token/3 (parser.p)                                    */
/*              var_of/2 (checker.p)                                    */
/*              or_of/2 (checker.p)                                     */
/*              pred_of/3 (checker.p)                                   */
/*              db_fetch/1 (meta.p)                                     */
/*              db_insert/1 (meta.p)                                    */
/*              db_delete/1 (meta.p)                                    */
/*              g_stat/3 (meta.p)                                       */
/*              g_atom/3 (meta.p)                                       */
/*              sql_exec/2 (meta.p)                                     */
/*              sql_sel2/3 (meta.p)                                     */
/*              sql_exec2/2 (meta.p)                                    */
/*              err/2 (error.p)                                         */
/************************************************************************/

:- type ass = ass(str,expr).
:- pred trans_expr(form,*ass,expr).
:- pred trans_list(*form,*ass,*expr).
:- pred trans_where(*form,expr,*ass,*cond,*cond).

:- type rec = rec(*range,*cond,int).
:- pred trans_form(form,*ass,rec,rec).
:- pred trans_query(*form,form,selstat).
:- pred tab_name(str,str).

trans_expr(cst(C,T),_,cst(C,T)).
trans_expr(neg(E),L,neg(F)) :- trans_expr(E,L,F).
trans_expr(int(E),L,trunc(F)) :- trans_expr(E,L,F).
trans_expr(float(E),L,F) :- trans_expr(E,L,F).
trans_expr(add(E,F),L,add(G,H)) :- trans_expr(E,L,G), trans_expr(F,L,H).
trans_expr(sub(E,F),L,sub(G,H)) :- trans_expr(E,L,G), trans_expr(F,L,H).
trans_expr(mul(E,F),L,mul(G,H)) :- trans_expr(E,L,G), trans_expr(F,L,H).
trans_expr(quo(E,F),L,quo(G,H)) :- trans_expr(E,L,G), trans_expr(F,L,H).
trans_expr(div(E,F),L,trunc(quo(G,H))) :- trans_expr(E,L,G), trans_expr(F,L,H).
trans_expr(mod(E,F),L,mod(G,H)) :- trans_expr(E,L,G), trans_expr(F,L,H).
trans_expr(var(V,_),L,E) :- mem(ass(V,F),L), !, E=F.

trans_list([],_,[]).
trans_list([E|F],L,[G|H]) :- trans_expr(E,L,G), trans_list(F,L,H).

trans_where([],_,_,H,H).
trans_where([E|F],attr(A,C),L,I,O) :-
  trans_expr(E,L,K),
  (K=attr(A,C), !, H=I; H=[eq(K,attr(A,C))|I]),
  D is C+1,
  trans_where(F,attr(A,D),L,H,O).

tab_name(P,T) :-
  name(P,L), append("PRO_",L,R), name(T,R).

trans_form(true,_,H,H).
trans_form(not(E),L,rec(F,W,A),rec(F,[not(sel(S1,F1,W1))|W],B)) :-
  set_of(V,var_of(E,V),R),
  trans_list(R,L,S1),
  trans_form(E,L,rec([],[],A),rec(F1,W1,B)).
trans_form(and(E,F),L,I,O) :-
  trans_form(E,L,I,H),
  trans_form(F,L,H,O).
trans_form(ex(var(V,_),E),L,I,O) :-
  trans_form(E,[ass(V,_)|L],I,O).
trans_form(eq(_,P,Q),L,rec(F,W,A),rec(F,V,A)) :-
  trans_expr(P,L,K),
  trans_expr(Q,L,J),
  (K=J, !, V=W; V=[eq(K,J)|W]).
trans_form(ls(_,P,Q),L,rec(F,W,A),rec(F,[ls(K,J)|W],A)) :-
  trans_expr(P,L,K),
  trans_expr(Q,L,J).
trans_form(gr(_,P,Q),L,rec(F,W,A),rec(F,[gr(K,J)|W],A)) :-
  trans_expr(P,L,K),
  trans_expr(Q,L,J).
trans_form(nq(_,P,Q),L,rec(F,W,A),rec(F,[nq(K,J)|W],A)) :-
  trans_expr(P,L,K),
  trans_expr(Q,L,J).
trans_form(lq(_,P,Q),L,rec(F,W,A),rec(F,[lq(K,J)|W],A)) :-
  trans_expr(P,L,K),
  trans_expr(Q,L,J).
trans_form(gq(_,P,Q),L,rec(F,W,A),rec(F,[gq(K,J)|W],A)) :-
  trans_expr(P,L,K),
  trans_expr(Q,L,J).
trans_form(pred(P,E),L,rec(F,W,A),rec([range(T,A)|F],V,B)) :-
  B is A+1,
  trans_where(E,attr(A,0),L,W,V),
  tab_name(P,T).

trans_query(H,NQ1,sel(S,F,W)) :-
  trans_form(NQ1,L,rec([],[],0),rec(F,W,_)),
  trans_list(H,L,S).

/************************************************************************/
/************************************************************************/

:- pred ev_open_db(str).
:- pred ev_close_db.
:- pred ev_create_pred(str,*etype).
:- pred ev_drop_pred(str).
:- pred ev_clear_pred(str).

:- pred types_to_cols_and_types(*etype,int,*def).
:- pred flush_pred(str).

ev_open_db(S) :- 
  sql_open_db(S,0).

ev_close_db :- 
  sql_close_db.

types_to_cols_and_types([],_,[]).
types_to_cols_and_types([T|X],N,[def(N,T)|Y]) :-
  M is N+1, types_to_cols_and_types(X,M,Y).

ev_create_pred(P,Ts) :-
  types_to_cols_and_types(Ts,0,CTs),
  tab_name(P,T),
  sql_exec2([],create(T,CTs)).

flush_pred(P) :-
  db_fetch(cache(P)), !,
    tab_name(P,T),
    sql_exec2([],delete(range(T,0),[])),
    db_delete(cache(P)),
    (db_fetch(deps(Q,_,P,_)), 
       flush_pred(Q), 
       fail; true); 
  true.

ev_drop_pred(P) :-
  flush_pred(P),
  db_delete(trans(P,_,_,_)),
  tab_name(P,T),
  sql_exec2([],drop(T)).

ev_clear_pred(P) :-
  flush_pred(P),
  db_delete(trans(P,_,_,_)).

/************************************************************************/
/************************************************************************/

:- pred p_deps(*str,*token,*token).
:- pred p_deps1(*str,*token,*token).
:- pred g_deps(*str,*int,*int).
:- pred g_deps1(*str,*int,*int).

g_deps([X|Y])		--> "(", g_atom(X), g_deps1(Y), ")".
g_deps([])		--> "".
g_deps1([X|Y])		--> ",", g_atom(X), g_deps1(Y).
g_deps1([])		--> "".

p_deps([X|Y])		--> [tlpar], !, [tid(X)], p_deps1(Y), [trpar].
p_deps([])		--> [].
p_deps1([X|Y])		--> [tcomma], !, [tid(X)], p_deps1(Y).
p_deps1([])		--> [].

/************************************************************************/
/************************************************************************/

:- pred disj(*str,*str).
:- pred insert_table_nonrec(str,*str).
:- pred insert_table_rec(str,*str).
:- type cnt = cnt(str,int).
:- pred iterate_fixpoint(*cnt,*str).

disj(X,Y) :- (mem(Z,X), mem(Z,Y), !, fail; true).

insert_table_nonrec(P,SCC) :-
  db_fetch(trans(P,_,DEPSSTR,INSSTR)),
  name(DEPSSTR,DEPSCHS),
  t_token(DEPSTOKS,DEPSCHS,_),
  p_deps(DEPS,DEPSTOKS,_),
  disj(DEPS,SCC),
  sql_exec([],INSSTR), fail; true.

insert_table_rec(P,SCC) :-
  db_fetch(trans(P,_,DEPSSTR,INSSTR)),
  name(DEPSSTR,DEPSCHS),
  t_token(DEPSTOKS,DEPSCHS,_),
  p_deps(DEPS,DEPSTOKS,_),
  \+disj(DEPS,SCC),
  sql_exec([],INSSTR), fail; true.

iterate_fixpoint(Cs,SCC) :-
  findall(cnt(Q,C),(mem(Q,SCC),
     insert_table_rec(Q,SCC),
     tab_name(Q,T),
     sql_sel2([],sel([count(all)],[range(T,0)],[]),[dint(C)])),Cs2),
  write(Cs), nl,
  (Cs=Cs2, !; iterate_fixpoint(Cs2,SCC)).

/************************************************************************/
/************************************************************************/

:- pred ev_assert_rule(str,int,*form,form).
:- pred ev_retract_rule(str,int).
:- pred ev_eval_order(*scc).
:- pred ev_query_res(*scc,*form,form,*data).

:- pred var_to_data(*form,*data).
:- pred eval_order(*scc).

ev_assert_rule(P,KEY,H,NQ) :-
  flush_pred(P), 
  (or_of(NQ,NQ1),
     trans_query(H,and(NQ1,not(pred(P,H))),S),
     tab_name(P,T),
     g_stat(insert(T,S),INSCHS,[]),
     name(INSSTR,INSCHS),
     set_of(Q,pred_of(NQ1,Q,_),L),
     g_deps(L,DEPSCHS,[]),
     name(DEPSSTR,DEPSCHS),
     db_insert(trans(P,KEY,DEPSSTR,INSSTR)), fail; true).

ev_retract_rule(P,KEY) :-
  flush_pred(P),
  db_delete(trans(P,KEY,_,_)).

eval_order([]).
eval_order([scc(P,_)|X]) :-
  db_fetch(cache(P)), !,
  eval_order(X).
eval_order([scc(P,[])|X]) :- !,
  eval_order(X),
  insert_table_nonrec(P,[]),
  db_insert(cache(P)).
eval_order([scc(_,SCC)|X]) :- 
  eval_order(X), 
  findall(cnt(Q,C),(mem(Q,SCC),
     insert_table_nonrec(Q,SCC),
     db_insert(cache(Q)),
     tab_name(Q,T),
     sql_sel2([],sel([count(all)],[range(T,0)],[]),[dint(C)])),Cs),
  iterate_fixpoint(Cs,SCC).

var_to_data([],[]).
var_to_data([var(_,en(ni))|X],[dint(_)|Z]) :- var_to_data(X,Z).
var_to_data([var(_,en(nf))|X],[dfloat(_)|Z]) :- var_to_data(X,Z).
var_to_data([var(_,es)|X],[dstr(_)|Z]) :- var_to_data(X,Z).

ev_query_res(EV,H,NQ,X) :-
  var_to_data(H,X),
  eval_order(EV),
  or_of(NQ,NQ1),
  trans_query(H,NQ1,S),
  sql_sel2([],S,X).

/************************************************************************/
/* .									*/
/************************************************************************/
