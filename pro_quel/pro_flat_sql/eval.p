/************************************************************************/
/************************************************************************/
/*              e v a l . p                                             */
/*                                                                      */
/* Export:                                                              */
/*              ev_open_db/1 (main.p)                                   */
/*              ev_close_db/0 (main.p)                                  */
/*              ev_create_pred/2 (main.p)                               */
/*              ev_clear_pred/1 (main.p)                                */
/*              ev_drop_pred/1 (main.p)                                 */
/*              ev_insert_res/3 (main.p)                                */
/*              ev_query_res/3 (main.p)                                 */
/* Import:                                                              */
/*              mem/2 (main.p)                                          */
/*              set_of/3 (main.p)                                       */
/*              varof/2 (checker.p)                                     */
/*              orof/2 (checker.p)                                      */
/*              sql_sel2/3 (meta.p)                                     */
/*              sql_exec2/2 (meta.p)                                    */
/************************************************************************/
/************************************************************************/

/************************************************************************/
/************************************************************************/
/* S Q L   T R A N S L A T O R						*/
/************************************************************************/
/************************************************************************/

:- type eassoc = str-expr.
:- pred trans_expr(form,*eassoc,expr).
:- pred trans_list(*form,*eassoc,*expr).
:- pred trans_where(*form,int,int,*eassoc,*cond,*cond).

:- type rec = rec(*range,*cond,int).
:- pred trans_form(form,*eassoc,rec,rec).
:- pred trans_query(*form,form,selstat).

trans_expr(cstr(C),_,cstr(C)).
trans_expr(cint(C),_,cint(C)).
trans_expr(cfloat(C),_,cfloat(C)).
trans_expr(neg(E),L,neg(F)) :- trans_expr(E,L,F).
trans_expr(int(E),L,trunc(F)) :- trans_expr(E,L,F).
trans_expr(float(E),L,F) :- trans_expr(E,L,F).
trans_expr(add(E,F),L,add(G,H)) :- trans_expr(E,L,G), trans_expr(F,L,H).
trans_expr(sub(E,F),L,sub(G,H)) :- trans_expr(E,L,G), trans_expr(F,L,H).
trans_expr(mul(E,F),L,mul(G,H)) :- trans_expr(E,L,G), trans_expr(F,L,H).
trans_expr(quo(E,F),L,quo(G,H)) :- trans_expr(E,L,G), trans_expr(F,L,H).
trans_expr(div(E,F),L,trunc(quo(G,H))) :- trans_expr(E,L,G), trans_expr(F,L,H).
trans_expr(mod(E,F),L,mod(G,H)) :- trans_expr(E,L,G), trans_expr(F,L,H).
trans_expr(var(V),L,E) :- mem(V-F,L), !, E=F.

trans_list([],_,[]).
trans_list([E|F],L,[G|H]) :- trans_expr(E,L,G), trans_list(F,L,H).

trans_where([],_,_,_,H,H).
trans_where([E|F],A,C,L,I,O) :-
  trans_expr(E,L,K),
  (K=attr(A,C) -> H=I; H=[eq(K,attr(A,C))|I]),
  D is C+1, trans_where(F,A,D,L,H,O).

trans_form(true,_,H,H).
trans_form(not(E),L,rec(F,W,A),rec(F,[not(sel(S1,F1,W1))|W],B)) :-
  set_of(var(V),varof(E,V),R),
  trans_list(R,L,S1),
  trans_form(E,L,rec([],[],A),rec(F1,W1,B)).
trans_form(and(E,F),L,I,O) :-
  trans_form(E,L,I,H),
  trans_form(F,L,H,O).
trans_form(ex(V,E),L,I,O) :-
  trans_form(E,[V-_|L],I,O).
trans_form(eq(P,Q),L,rec(F,W,A),rec(F,V,A)) :-
  trans_expr(P,L,K),
  trans_expr(Q,L,J),
  (K=J -> V=W; V=[eq(K,J)|W]).
trans_form(ls(P,Q),L,rec(F,W,A),rec(F,[ls(K,J)|W],A)) :-
  trans_expr(P,L,K),
  trans_expr(Q,L,J).
trans_form(gr(P,Q),L,rec(F,W,A),rec(F,[gr(K,J)|W],A)) :-
  trans_expr(P,L,K),
  trans_expr(Q,L,J).
trans_form(nq(P,Q),L,rec(F,W,A),rec(F,[nq(K,J)|W],A)) :-
  trans_expr(P,L,K),
  trans_expr(Q,L,J).
trans_form(lq(P,Q),L,rec(F,W,A),rec(F,[lq(K,J)|W],A)) :-
  trans_expr(P,L,K),
  trans_expr(Q,L,J).
trans_form(gq(P,Q),L,rec(F,W,A),rec(F,[gq(K,J)|W],A)) :-
  trans_expr(P,L,K),
  trans_expr(Q,L,J).
trans_form(pred(P,E),L,rec(F,W,A),rec([P-A|F],V,B)) :-
  B is A+1,
  trans_where(E,A,0,L,W,V).

trans_query(H,NQ1,sel(S,F,W)) :-
  trans_form(NQ1,L,rec([],[],0),rec(F,W,_)),
  trans_list(H,L,S).

/************************************************************************/
/************************************************************************/
/* S Q L   E V A L U A T O R						*/
/************************************************************************/
/************************************************************************/

:- pred ev_open_db(str).
:- pred ev_close_db.
:- pred ev_create_pred(str,*etype).
:- pred ev_clear_pred(str).
:- pred ev_drop_pred(str).
:- pred ev_count_pred(str,int).
:- pred ev_insert_res(str,*form,form).
:- pred ev_query_res(*form,form,*etype,mix).

ev_open_db(S) :- sql_open_db(S,0).

ev_close_db :- sql_close_db.

ev_create_pred(P,T) :- sql_exec2(create(P,T)).

ev_clear_pred(P) :- sql_exec2(delete(P-0,[])).

ev_drop_pred(P) :- sql_exec2(drop(P)).

ev_count_pred(P,N) :- sql_sel2(sel([count],[P-0],[]),[n(i)],[N]).

ev_insert_res(P,E,F) :-
  (orof(F,Q),
     trans_query(E,Q,S),
     sql_exec2(insert(P,S)),
     fail; true).

ev_query_res(E,F,T,X) :-
  orof(F,Q),
  trans_query(E,Q,S),
  sql_sel2(S,T,X).

/************************************************************************/
/* .									*/
/************************************************************************/
