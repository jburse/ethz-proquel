/************************************************************************/
/************************************************************************/
/*              e v a l . p                                             */
/*                                                                      */
/* Export:                                                              */
/*              ev_open_db/1 (main.p)                                   */
/*              ev_close_db/0 (main.p)                                  */
/*              ev_create_pred/2 (main.p)                               */
/*              ev_drop_pred/1 (main.p)                                 */
/*              ev_clear_pred/1 (main.p)                                */
/*              ev_insert_res/3 (main.p)                                */
/*              ev_query_res/4 (main.p)                                 */
/* Import:                                                              */
/*              mem/2 (main.p)                                          */
/*              orof/2 (checker.p)                                      */
/*              pg_exec2/1 (meta.p)                                     */
/************************************************************************/
/************************************************************************/

/************************************************************************/
/************************************************************************/
/* P O S T G R E S   T R A N S L A T O R				*/
/************************************************************************/
/************************************************************************/

:- type vassoc = str-expr.

:- pred trans_expr(form,*vassoc,*vassoc,expr).
:- pred trans_list(*form,*vassoc,*vassoc,*expr).
:- pred trans_where(*form,int,int,*vassoc,*vassoc,*cond,*cond).

trans_expr(cstr(C),L,L,cstr(C)).
trans_expr(cint(C),L,L,cint(C)).
trans_expr(cfloat(C),L,L,cfloat(C)).
trans_expr(neg(E),I,O,neg(F)) :- !, trans_expr(E,I,O,F).
trans_expr(add(E,F),I,O,add(G,J)) :- trans_expr(E,I,H,G), !, trans_expr(F,H,O,J).
trans_expr(sub(E,F),I,O,sub(G,J)) :- trans_expr(E,I,H,G), !, trans_expr(F,H,O,J).
trans_expr(mul(E,F),I,O,mul(G,J)) :- trans_expr(E,I,H,G), !, trans_expr(F,H,O,J).
trans_expr(quo(E,F),I,O,quo(G,J)) :- trans_expr(E,I,H,G), !, trans_expr(F,H,O,J).
trans_expr(var(V),I,O,X) :- !, (mem(V-X,I) -> O=I; O=[V-X|I]).

trans_list([],L,L,[]).
trans_list([X|Y],I,O,[Z|T]) :- 
  trans_expr(X,I,H,Z), !, trans_list(Y,H,O,T).

trans_where([],_,_,V,V,L,L).
trans_where([X|Y],A,C,P,Q,I,O) :-
  trans_expr(X,P,K,Z),
  (Z=A-C -> H=I; H=[eq(A-C,Z)|I]),
  D is C+1, !, trans_where(Y,A,D,K,Q,H,O).

:- type rec = rec(*vassoc,*range,*cond,int,*str).

:- pred trans_form(form,rec,rec).
:- pred trans_assoc(*vassoc,int,int,*expr,*vassoc).
:- pred trans_query(*form,form,*expr,*range,*cond,*str).

trans_assoc([],_,_,[],[]).
trans_assoc([V-X|L],A,C,[X|R],[V-(A-C)|T]) :-
  D is C+1, !, trans_assoc(L,A,D,R,T).

trans_form(true,H,H).
trans_form(and(E,F),I,O) :-
  trans_form(E,I,H),
  !, trans_form(F,H,O).
trans_form(ex(V,E),rec(A,R,C,N,L),O) :-
  !, trans_form(E,rec([V-_|A],R,C,N,L),O).
trans_form(eq(P,Q),rec(A,R,C,N,L),rec(D,R,H,N,L)) :-
  trans_expr(P,A,B,X), 
  trans_expr(Q,B,D,Y),  
  !, (X=Y -> H=C; H=[eq(X,Y)|C]).
trans_form(ls(P,Q),rec(A,R,C,N,L),rec(D,R,[ls(X,Y)|C],N,L)) :-
  trans_expr(P,A,B,X), 
  !, trans_expr(Q,B,D,Y).
trans_form(gr(P,Q),rec(A,R,C,N,L),rec(D,R,[gr(X,Y)|C],N,L)) :-
  trans_expr(P,A,B,X), 
  !, trans_expr(Q,B,D,Y).
trans_form(lq(P,Q),rec(A,R,C,N,L),rec(D,R,[lq(X,Y)|C],N,L)) :-
  trans_expr(P,A,B,X), 
  !, trans_expr(Q,B,D,Y).
trans_form(gq(P,Q),rec(A,R,C,N,L),rec(D,R,[gq(X,Y)|C],N,L)) :-
  trans_expr(P,A,B,X), 
  !, trans_expr(Q,B,D,Y).
trans_form(nq(P,Q),rec(A,R,C,N,L),rec(D,R,[nq(X,Y)|C],N,L)) :-
  trans_expr(P,A,B,X), 
  !, trans_expr(Q,B,D,Y).
trans_form(pred(P,E),rec(A,R,C,N,L),rec(B,[P-N|R],D,M,L)) :-
  trans_where(E,N,0,A,B,C,D), !, M is N+1.
trans_form(not(E),rec(A,R,C,N,L),rec(B,[W-N],[],K,T)) :-
  number_chars(N,J), 
  atom_chars(W,[95|J]),
  trans_assoc(A,N,0,S,B),
  pg_exec2(into(W,S,R,C)),
  M is N+1,
  trans_form(E,rec(B,[W-N],[],M,[W|L]),rec(_,Q,D,K,T)),
  !, pg_exec2(delete(N,Q,D)).

trans_query(E,F,S,R,C,D) :-
  trans_form(F,rec([],[],[],1,[]),rec(B,R,C,_,D)),
  trans_list(E,B,_,S).

/************************************************************************/
/************************************************************************/
/* P O S T G R E S   E V A L U A T O R					*/
/************************************************************************/
/************************************************************************/

:- pred ev_open_db(str).
:- pred ev_close_db.
:- pred ev_create_pred(str,*etype).
:- pred ev_clear_pred(str).
:- pred ev_count_pred(str,int).
:- pred ev_drop_pred(str).
:- pred ev_insert_res(str,*form,form).
:- pred ev_query_res(*form,form,*etype,mix).

ev_open_db(X) :- pg_open_db(X).

ev_close_db :- pg_close_db.

ev_create_pred(P,T) :- 
  pg_exec2(create(P,T)).

ev_drop_pred(P) :- 
  pg_exec2(drop(P)).

ev_clear_pred(P) :- 
  pg_exec2(delete(0,[P-0],[])).

ev_count_pred(P,X) :- 
  pg_exec2(sel([oid(0)],[P-0],[])),
  pg_get_buf(B),
  pg_count_tuples(B,X).

ev_insert_res(P,E,F) :-
  (orof(F,Q),
    trans_query(E,Q,S,R,C,D),
    pg_exec2(append(0,S,[P-0|R],C)), 
    (mem(W,D), pg_exec2(drop(W)), fail; true), fail; true).

ev_query_res(E,F,T,X) :-
  orof(F,Q),
  trans_query(E,Q,S,R,C,D),
  pg_exec2(sel(S,R,C)),
  pg_get_buf(B),
  pg_count_tuples(B,K), J is K-1,
  findall(X,(pg_index(0,J,N),pg_get_vals(T,X,B,N,0)),L),
  (mem(W,D), pg_exec2(drop(W)), fail; true),
  mem(X,L).
