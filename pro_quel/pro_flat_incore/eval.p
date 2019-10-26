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
/*              ev_query_res/4 (main.p)                                 */
/* Import:                                                              */
/*              memcut/2 (checker.p)                                    */
/*              orof/2 (checker.p)                                      */
/************************************************************************/
/************************************************************************/

/************************************************************************/
/************************************************************************/
/* P R O L O G   T R A N S L A T O R					*/
/************************************************************************/
/************************************************************************/

:- type qassoc = str-A.

:- pred make_and(A,B,C).
:- pred trans_expr(form,*qassoc,A,B).
:- pred trans_list(*form,*qassoc,mix,A).
:- pred trans_form(form,*qassoc,A).
:- pred trans_query(*form,form,mix,A).

make_and(true,X,X) :- !.
make_and(X,true,X) :- !.
make_and(X,Y,(X,Y)).

trans_expr(cstr(C),_,C,true).
trans_expr(cint(C),_,C,true).
trans_expr(cfloat(C),_,C,true).
trans_expr(neg(E),L,X,Q) :- trans_expr(E,L,F,Q1), make_and(Q1,X is -F,Q).
trans_expr(int(E),L,X,Q) :- trans_expr(E,L,F,Q1), make_and(Q1,X is integer(F),Q).
trans_expr(float(E),L,X,Q) :- trans_expr(E,L,F,Q1), make_and(Q1,X is float(F),Q).
trans_expr(add(E,F),L,X,Q) :- trans_expr(E,L,R,Q1), trans_expr(F,L,S,Q2),
  make_and(Q1,Q2,Q3), make_and(Q3,X is R+S,Q).
trans_expr(sub(E,F),L,X,Q) :- trans_expr(E,L,R,Q1), trans_expr(F,L,S,Q2),
  make_and(Q1,Q2,Q3), make_and(Q3,X is R-S,Q).
trans_expr(mul(E,F),L,X,Q) :- trans_expr(E,L,R,Q1), trans_expr(F,L,S,Q2), 
  make_and(Q1,Q2,Q3), make_and(Q3,X is R*S,Q).
trans_expr(quo(E,F),L,X,Q) :- trans_expr(E,L,R,Q1), trans_expr(F,L,S,Q2),
  make_and(Q1,Q2,Q3), make_and(Q3,X is R/S,Q).
trans_expr(div(E,F),L,X,Q) :- trans_expr(E,L,R,Q1), trans_expr(F,L,S,Q2),
  make_and(Q1,Q2,Q3), make_and(Q3,X is R//S,Q).
trans_expr(mod(E,F),L,X,Q) :- trans_expr(E,L,R,Q1), trans_expr(F,L,S,Q2),
  make_and(Q1,Q2,Q3), make_and(Q3,X is R mod S,Q).
trans_expr(var(V),L,E,true) :- memcut(V-E,L).

trans_list([],_,[],true).
trans_list([A|B],L,[X|Y],Q) :-
 trans_expr(A,L,X,Q1), trans_list(B,L,Y,Q2), make_and(Q1,Q2,Q).

trans_form(true,_,true).
trans_form(not(A),_,\+Q) :- trans_form(A,_,Q).
trans_form(and(A,B),L,Q) :- trans_form(A,L,Q1), trans_form(B,L,Q2), make_and(Q1,Q2,Q).
trans_form(ex(V,A),L,Q) :- trans_form(A,[V-_|L],Q).
trans_form(eq(E,F),L,Q) :- trans_expr(E,L,R,Q1), trans_expr(F,L,S,Q2),
  make_and(Q1,Q2,Q3), (R=S -> Q=Q3; make_and(Q3,R==S,Q)).
trans_form(ls(E,F),L,Q) :- trans_expr(E,L,R,Q1), trans_expr(F,L,S,Q2),
  make_and(Q1,Q2,Q3), make_and(Q3,R@<S,Q).
trans_form(gr(E,F),L,Q) :- trans_expr(E,L,R,Q1), trans_expr(F,L,S,Q2),
  make_and(Q1,Q2,Q3), make_and(Q3,R@>S,Q).
trans_form(lq(E,F),L,Q) :- trans_expr(E,L,R,Q1), trans_expr(F,L,S,Q2),
  make_and(Q1,Q2,Q3), make_and(Q3,R@=<S,Q).
trans_form(gq(E,F),L,Q) :- trans_expr(E,L,R,Q1), trans_expr(F,L,S,Q2),
  make_and(Q1,Q2,Q3), make_and(Q3,R@>=S,Q).
trans_form(nq(E,F),L,Q) :- trans_expr(E,L,R,Q1), trans_expr(F,L,S,Q2),
  make_and(Q1,Q2,Q3), make_and(Q3,R\==S,Q).
trans_form(pred(P,A),L,Q) :-
  trans_list(A,L,E,Q1), Q2=..[P|E], make_and(Q1,Q2,Q).

trans_query(E,F,L,Q) :-
  trans_form(F,A,Q1), trans_list(E,A,L,Q2), make_and(Q1,Q2,Q).

/************************************************************************/
/************************************************************************/
/* P R O L O G   E V A L U A T O R					*/
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

:- pred arity(str,int).

ev_open_db(_).

ev_close_db.

ev_create_pred(P,T) :-
  length(T,N), assert(arity(P,N)).

ev_clear_pred(P) :-
  arity(P,N), length(L,N), Q=..[P|L], 
  (retract(Q), fail; true).

ev_drop_pred(P) :-
  arity(P,N), length(L,N), Q=..[P|L], 
  (retract(Q), fail; true),
  retract(arity(P,N)).

ev_count_pred(P,C) :-
  arity(P,N), length(L,N), Q=..[P|L],
  findall([],Q,H), length(H,C).

:- pred insert_tupel(A).

insert_tupel(X) :- 
  (clause(X,true) -> true; assertz(X)).

ev_insert_res(P,E,F) :-
  (orof(F,N),
    trans_query(E,N,X,Q),
    H=..[P|X],
    (Q, insert_tupel(H), fail; true), fail; true).

ev_query_res(E,F,_,X) :-
  orof(F,N),
  trans_query(E,N,X,Q),
  Q.


/************************************************************************/
/* .									*/
/************************************************************************/

