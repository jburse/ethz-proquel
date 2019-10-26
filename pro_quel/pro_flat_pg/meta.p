/************************************************************************/
/************************************************************************/
/*              m e t a . p                                             */
/*                                                                      */
/* Export:                                                              */
/*              db_fetch/1 (checker.p,main.p)                           */
/*              db_insert/1 (main.p)                                    */
/*              db_delete/1 (main.p)                                    */
/*              pg_exec2/1 (eval.p)                                     */
/* Import:                                                              */
/*              db_tab/2 (main.p)                                       */
/*              mem/2 (main.p)                                          */
/************************************************************************/
/************************************************************************/

/************************************************************************/
/************************************************************************/
/* M I N I  D A T A B A S E						*/
/************************************************************************/
/************************************************************************/

:- pred db_fetch(fact). /* retrieve all matching facts */
:- pred db_insert(fact). /* insert fact */
:- pred db_delete(fact). /* remove all matching facts */

:- pred const_var(etype,A,expr).
:- pred db_fetch1(*etype,mix,int,*cond,*expr,*etype,mix).
:- pred db_insert1(*etype,mix,*expr).
:- pred db_delete1(*etype,mix,int,*cond).

const_var(n(i),X,cint(X)).
const_var(n(f),X,cfloat(X)).
const_var(s,X,cstr(X)).

db_fetch1([S|R],[X|Y],N,W,[0-N|Q],[S|T],[X|Z]) :-
  var(X), !, M is N+1, db_fetch1(R,Y,M,W,Q,T,Z).
db_fetch1([S|R],[X|Y],N,[eq(H,0-N)|W],Q,T,Z) :-
  const_var(S,X,H), M is N+1, db_fetch1(R,Y,M,W,Q,T,Z).
db_fetch1([],[],_,[],[],[],[]).

db_insert1([S|R],[X|Y],[H|Q]) :-
  const_var(S,X,H), db_insert1(R,Y,Q).
db_insert1([],[],[]).

db_delete1([_|R],[X|Y],N,W) :-
  var(X), !, M is N+1, db_delete1(R,Y,M,W).
db_delete1([S|R],[X|Y],N,[eq(H,0-N)|W]) :-
  const_var(S,X,H), M is N+1, db_delete1(R,Y,M,W).
db_delete1([],[],_,[]).

db_fetch(P) :-
  P=..[F|L], db_tab(F,S),
  db_fetch1(S,L,0,W,E,T,X), 
  pg_exec2(sel(E,[F-0],W)), 
  pg_fetch(T,X).

db_insert(P) :-
  P=..[F|L], db_tab(F,S),
  db_insert1(S,L,E),
  pg_exec2(append(0,E,[F-0],[])).

db_delete(P) :-
  P=..[F|L], db_tab(F,S),
  db_delete1(S,L,0,W),
  pg_exec2(delete(0,[F-0],W)).

/************************************************************************/
/************************************************************************/
/* P O S T G R E S   G E N E R A T O R					*/
/************************************************************************/
/************************************************************************/

:- type stat = create(str,*etype) + drop(str) + delete(int,*range,*cond) +
               append(int,*expr,*range,*cond) + sel(*expr,*range,*cond) +
               into(str,*expr,*range,*cond).

:- type cond = eq(expr,expr) + gr(expr,expr) + ls(expr,expr) + nq(expr,expr) +
               lq(expr,expr) + gq(expr,expr).

:- type range = str - int.

:- dcg g_stat(stat).
:- dcg g_selstat(*expr,*range,*cond).
:- dcg g_defs(int,*etype).
:- dcg g_defs2(int,*etype).
:- dcg g_type(etype).
:- dcg g_where(*cond).
:- dcg g_where2(*cond).
:- dcg g_cond(cond).
:- dcg g_res(int,*expr).
:- dcg g_res2(int,*expr).
:- dcg g_from(*range).
:- dcg g_from2(*range).
:- dcg g_range(range).

g_stat(create(P,L))     --> "create ", g_tab(P), g_defs(0,L).
g_stat(drop(P))         --> "destroy ", g_tab(P).
g_stat(delete(P,F,W))   --> "delete ", g_alias(P), g_from(F), g_where(W).
g_stat(append(P,S,F,W)) --> "append ", g_alias(P), g_selstat(S,F,W).
g_stat(sel(S,F,W))      --> "retrieve ", g_selstat(S,F,W).
g_stat(into(P,S,F,W))	--> "retrieve into ", g_tab(P), g_selstat(S,F,W).

g_selstat(E,F,W)	--> g_res(0,E), g_from(F), g_where(W).

g_defs(_,[])		--> "(c0=int4)".
g_defs(N,[T|R])		--> "(", g_col(N), "=", g_type(T), {M is N+1}, g_defs2(M,R).
g_defs2(_,[])		--> ")".
g_defs2(N,[T|R])	--> ",", g_col(N), "=", g_type(T), {M is N+1}, g_defs2(M,R).

g_type(s)		--> "text".
g_type(n(f))		--> "float8".
g_type(n(i))		--> "int4".

g_where([])             --> "".
g_where([A|B])          --> [10], "where ", g_cond(A), g_where2(B).
g_where2([])            --> "".
g_where2([A|B])         --> [10], "and ", g_cond(A), g_where2(B).

g_cond(eq(X,Y))		--> g_expr(X), "=", g_expr(Y).
g_cond(gr(X,Y))		--> g_expr(X), ">", g_expr(Y).
g_cond(ls(X,Y))		--> g_expr(X), "<", g_expr(Y).
g_cond(nq(X,Y))		--> g_expr(X), "!=", g_expr(Y).
g_cond(gq(X,Y))		--> g_expr(X), ">=", g_expr(Y).
g_cond(lq(X,Y))		--> g_expr(X), "<=", g_expr(Y).

g_from([])              --> "".
g_from([R|L])           --> [10], "from ", g_range(R), g_from2(L).
g_from2([])             --> "".
g_from2([R|L])          --> ",", g_range(R), g_from2(L).

g_range(R-A)            --> g_alias(A), " in ", g_tab(R).

g_res(_,[])		--> "(c0=0)".
g_res(N,[E|R])		--> "(", g_col(N), "=", g_expr(E), {M is N+1}, g_res2(M,R).
g_res2(_,[])		--> ")".
g_res2(N,[E|R])		--> ",", g_col(N), "=", g_expr(E), {M is N+1}, g_res2(M,R).

:- type expr = add(expr,expr) + sub(expr,expr) + neg(expr) + mul(expr,expr) +
               quo(expr,expr) + mod(expr,expr) + cstr(str) + cint(int) +
               cfloat(float) + (int - int) + oid(int).

:- dcg g_expr(expr).
:- dcg g_term(expr).
:- dcg g_faktor(expr).
:- dcg g_col(int).
:- dcg g_alias(int).
:- dcg g_tab(str).
:- dcg g_atom(int).
:- dcg g_atom(float).
:- dcg g_atom(str).
:- dcg g_atom2(*int).
:- dcg g_str(str).
:- dcg g_str2(*int).

g_expr(add(X,Y))	--> !, g_expr(X), " + ", g_term(Y).
g_expr(sub(X,Y))	--> !, g_expr(X), " - ", g_term(Y).
g_expr(neg(X))		--> !, "- ", g_term(X).
g_expr(X)		--> g_term(X).

g_term(mul(X,Y))	--> !, g_term(X), " * ", g_faktor(Y).
g_term(quo(X,Y))	--> !, g_term(X), " / ", g_faktor(Y).
g_term(mod(X,Y))	--> !, g_term(X), " % ", g_faktor(Y).
g_term(X)		--> g_faktor(X).

g_faktor(cstr(C))	--> !, [34], g_str(C), [34], "::text".
g_faktor(cint(C))	--> !, g_atom(C).
g_faktor(cfloat(C))	--> !, g_atom(C).
g_faktor(A-C) 		--> !, g_alias(A), ".", g_col(C).
g_faktor(oid(A))	--> !, g_alias(A), ".oid".
g_faktor(X)		--> "(", g_expr(X), ")".

g_col(C)		--> "c", g_atom(C).

g_alias(A)		--> "a", g_atom(A).

g_tab(R)		--> "r", g_atom(R).

g_atom(X)		--> {name(X,L)}, g_atom2(L).
g_atom2([X|Y])		--> [X], g_atom2(Y).
g_atom2([])		--> [].

g_str(X)		--> {name(X,L)}, g_str2(L).
g_str2([34|Y])		--> !, [92, 34], g_atom2(Y).
g_str2([X|Y])		--> [X], g_atom2(Y).
g_str2([])		--> [].

/************************************************************************/
/************************************************************************/
/* P O S T G R E S   I N T E R F A C E					*/
/************************************************************************/
/************************************************************************/

foreign_file('postgres_interface.o',[pg_open_db,pg_close_db,
  pg_exec,pg_get_val,pg_get_buf,pg_count_tuples]).

foreign(pg_open_db,c,pg_open_db(+string)).
foreign(pg_close_db,c,pg_close_db).
foreign(pg_exec,c,pg_exec(+string)).
foreign(pg_get_buf,c,pg_get_buf(-address)).
foreign(pg_count_tuples,c,pg_count_tuples(+address,-integer)).
foreign(pg_get_val,c,pg_get_val(+address,+integer,+integer,-string)).

:- load_foreign_files(['postgres_interface.o'], 
        ['/home/mint/postgres/obj.sunos4/libpq.a']).

:- pred pg_open_db(str).
:- pred pg_close_db.
:- pred pg_exec(str).
:- pred pg_get_buf(int).
:- pred pg_count_tuples(int,int).
:- pred pg_get_val(int,int,int,str).

:- pred pg_convert_value(etype,str,A).
:- pred pg_get_vals(*etype,mix,int,int,int).
:- pred pg_exec2(stat).
:- pred pg_index(int,int,int).
:- pred pg_fetch(*etype,mix).

pg_convert_value(s,X,X).
pg_convert_value(n(i),X,Y) :- atom_chars(X,L), number_chars(Y,L).
pg_convert_value(n(f),X,Y) :- atom_chars(X,L), number_chars(Y,L).

pg_get_vals([S|R],[X|Y],B,N,C) :-
  pg_get_val(B,N,C,H), pg_convert_value(S,H,X),
  D is C+1, pg_get_vals(R,Y,B,N,D).
pg_get_vals([],[],_,_,_).

pg_exec2(E) :-
  g_stat(E,L,[]), name(S,L),
  (clause(verbose,true) -> write(S), write(';'), nl; true),
  pg_exec(S).

pg_index(L,H,X) :-
  L=<H,
  M is (L+H)//2,
  (A is M-1, pg_index(L,A,X);
   X=M;
   !, B is M+1, pg_index(B,H,X)).

pg_fetch(T,X) :-
  pg_get_buf(B),
  pg_count_tuples(B,K), J is K-1,
  findall(X,(pg_index(0,J,N),pg_get_vals(T,X,B,N,0)),L),
  mem(X,L).

/************************************************************************/
/* .									*/
/************************************************************************/
