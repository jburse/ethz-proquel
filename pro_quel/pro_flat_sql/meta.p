/************************************************************************/
/************************************************************************/
/*              m e t a . p                                             */
/*                                                                      */
/* Export:                                                              */
/*              db_fetch/1 (checker.p,main.p)                           */
/*              db_insert/1 (main.p)                                    */
/*              db_delete/1 (main.p)                                    */
/*              sql_sel2/3 (eval.p)                                     */
/*              sql_exec2/2 (eval.p)                                    */
/* Import:                                                              */
/*              mem/2 (main.p)                                          */
/*              append/3 (main.p)                                       */
/*		db_tab/2 (main.p)					*/
/************************************************************************/
/************************************************************************/

/************************************************************************/
/************************************************************************/
/* M I N I   D A T A B A S E						*/
/************************************************************************/
/************************************************************************/

:- pred db_fetch(fact). /* retrieve fact from mini data base */
:- pred db_insert(fact). /* insert fact into mini data base */
:- pred db_delete(fact). /* delete facts from mini data base */

:- pred db_fetch1(*etype,mix,int,*cond,*expr,*etype,mix). /*build sel expr and cond*/
:- pred db_insert1(*etype,mix,*expr). /* build insert expr */
:- pred db_delete1(*etype,mix,int,*cond). /* build delete cond */

:- pred const_var(etype,A,expr).

const_var(n(i),X,cint(X)).
const_var(n(f),X,cfloat(X)).
const_var(s,X,cstr(X)).

db_fetch1([],[],_,[],[],[],[]).
db_fetch1([S|R],[X|Y],N,W,[attr(0,N)|T],[S|Q],[X|Z]) :-
  var(X), !, M is N+1, db_fetch1(R,Y,M,W,T,Q,Z).
db_fetch1([S|R],[X|Y],N,[eq(C,attr(0,N))|W],T,Q,Z) :-
  M is N+1, const_var(S,X,C), db_fetch1(R,Y,M,W,T,Q,Z).

db_insert1([],[],[]).
db_insert1([S|R],[X|Y],[D|Z]) :-
  const_var(S,X,D), db_insert1(R,Y,Z).

db_delete1([],[],_,[]).
db_delete1([_|R],[X|Y],N,Z) :-
  var(X), !, M is N+1, db_delete1(R,Y,M,Z).
db_delete1([S|R],[X|Y],N,[eq(C,attr(0,N))|Z]) :-
  M is N+1, const_var(S,X,C), db_delete1(R,Y,M,Z).

db_fetch(P) :- 
  P=..[F|L], db_tab(F,T),
  db_fetch1(T,L,0,W,S,H,X), 
  sql_sel2(sel(S,[F-0],W),H,X).

db_insert(P) :-
  P=..[F|L], db_tab(F,T),
  db_insert1(T,L,V),
  sql_exec2(append(F,values(V))).

db_delete(P) :-
  P=..[F|L], db_tab(F,T),
  db_delete1(T,L,0,W),
  sql_exec2(delete(F-0,W)).

/************************************************************************/
/************************************************************************/
/* S Q L   G E N E R A T O R						*/
/************************************************************************/
/************************************************************************/

:- type stat = create(str,*etype) + drop(str) + delete(range,*cond) + 
               insert(str,selstat) + append(str,selstat).
:- type selstat = sel(*expr,*range,*cond) + union(selstat,selstat) + 
                  minus(selstat,selstat) + values(*expr).
:- type cond = eq(expr,expr) + gr(expr,expr) + ls(expr,expr) + nq(expr,expr) +
               lq(expr,expr) + gq(expr,expr) + not(selstat).
:- type range = str-int.

:- dcg g_stat(stat).
:- dcg g_selstat(selstat).
:- dcg g_selexpr(*expr).
:- dcg g_selexpr2(*expr).
:- dcg g_defs(int,*etype).
:- dcg g_defs2(int,*etype).
:- dcg g_type(etype).
:- dcg g_where(*cond).
:- dcg g_where2(*cond).
:- dcg g_cond(cond).
:- dcg g_from(*range).
:- dcg g_from2(*range).
:- dcg g_range(range).

g_stat(create(R,L))	--> "CREATE TABLE ", g_atom(R), g_defs(0,L).
g_stat(drop(R))		--> "DROP TABLE ", g_atom(R).
g_stat(delete(P,W))	--> "DELETE FROM ", g_range(P), g_where(W).
g_stat(append(P,S))	--> "INSERT INTO ", g_atom(P), [10], g_selstat(S).
g_stat(insert(P,S)) 	--> "INSERT INTO ", g_atom(P), [10], g_selstat(S),
  [10], "MINUS SELECT * FROM ", g_atom(P).

g_selstat(sel(S,F,W))	--> "SELECT ",g_selexpr(S),[10],"FROM ",g_from(F),g_where(W).
g_selstat(union(A,B))	--> g_selstat(A), [10], "UNION ", g_selstat(B).
g_selstat(minus(A,B))	--> g_selstat(A), [10], "MINUS ", g_selstat(B).
g_selstat(values(S))	--> "VALUES(", g_selexpr(S), ")".

g_defs(_,[])		--> "(C0 CHAR(2))".
g_defs(N,[T|R])		--> "(", g_col(N), " ", g_type(T), {M is N+1}, g_defs2(M,R).
g_defs2(_,[])		--> ")".
g_defs2(N,[T|R])	--> ",", g_col(N), " ", g_type(T), {M is N+1}, g_defs2(M,R).

g_type(s)		--> "CHAR(32)".
g_type(n(f))		--> "FLOAT".
g_type(n(i))		--> "INTEGER".

g_where([])		--> "".
g_where([A|B])		--> [10], "WHERE ", g_cond(A), g_where2(B).
g_where2([])		--> "".
g_where2([A|B])		--> [10], "AND ", g_cond(A), g_where2(B).

g_cond(eq(X,Y))		--> g_expr(X), "=", g_expr(Y).
g_cond(gr(X,Y))		--> g_expr(X), ">", g_expr(Y).
g_cond(ls(X,Y))		--> g_expr(X), "<", g_expr(Y).
g_cond(nq(X,Y))		--> g_expr(X), "<>", g_expr(Y).
g_cond(gq(X,Y))		--> g_expr(X), ">=", g_expr(Y).
g_cond(lq(X,Y))		--> g_expr(X), "<=", g_expr(Y).
g_cond(not(S))		--> "NOT EXISTS (", g_selstat(S), ")".

g_from([])		--> "DUAL".
g_from([R|L])		--> g_range(R), g_from2(L).
g_from2([])		--> "".
g_from2([R|L])		--> ",", g_range(R), g_from2(L).

g_range(R-A)		--> g_atom(R), " ", g_alias(A).

g_selexpr([])		--> "0".
g_selexpr([R|L])	--> g_expr(R), g_selexpr2(L).
g_selexpr2([])		--> "".
g_selexpr2([R|L])	--> ",", g_expr(R), g_selexpr2(L).

:- type expr = add(expr,expr) + sub(expr,expr) + neg(expr) + mul(expr,expr) +
            trunc(expr) + quo(expr,expr) +  
            attr(int,int) + count + mod(expr,expr) + cint(int) +
            cfloat(float) + cstr(str).

:- dcg g_expr(expr).
:- dcg g_term(expr).
:- dcg g_faktor(expr).

g_expr(add(X,Y))	--> !, g_expr(X), "+", g_term(Y).
g_expr(sub(X,Y))	--> !, g_expr(X), "-", g_term(Y).
g_expr(neg(X))		--> !, "-", g_term(X).
g_expr(X)		--> g_term(X).

g_term(mul(X,Y))	--> !, g_term(X), "*", g_faktor(Y).
g_term(quo(X,Y))	--> !, g_term(X), "/", g_faktor(Y).
g_term(X)		--> g_faktor(X).

g_faktor(cstr(C))	--> !, "'", g_str(C), "'".
g_faktor(cint(C))	--> !, g_atom(C).
g_faktor(cfloat(C))	--> !, g_atom(C).
g_faktor(attr(A,C)) 	--> !, g_alias(A), ".", g_col(C).
g_faktor(count)		--> !, "COUNT(*)".
g_faktor(mod(X,Y))	--> !, "MOD(", g_expr(X), ",", g_expr(Y), ")".
g_faktor(trunc(X))	--> !, "TRUNC(", g_expr(X), ")".
g_faktor(X)		--> "(", g_expr(X), ")".

:- dcg g_atom(A).
:- dcg g_atom2(*int).
:- dcg g_str(str).
:- dcg g_str2(*int).
:- dcg g_col(int).
:- dcg g_alias(int).

g_col(C)		--> "C", g_atom(C).

g_alias(A)		--> "A", g_atom(A).

g_atom(X)		--> {name(X,L)}, g_atom2(L).
g_atom2([X|Y])		--> [X], g_atom2(Y).
g_atom2([])		--> [].

g_str(X)		--> {name(X,L)}, g_str2(L).
g_str2([39|Y])		--> !, [39, 39], g_str2(Y).
g_str2([X|Y])		--> [X], g_str2(Y).
g_str2([])		--> [].

/************************************************************************/
/************************************************************************/
/* S Q L   I N T E R F A C E						*/
/************************************************************************/
/************************************************************************/

foreign_file('sql_inter.o',[
	sql_open_cursor,
        sql_put_variable,
	sql_fetch_row,
        sql_get_column,
	sql_close_cursor,
        sql_exec_cursor,
        sql_open_db,
        sql_close_db]).

foreign(sql_open_cursor,c,sql_open_cursor(+string,-address)).
foreign(sql_put_variable,c,sql_put_variable(+address,+integer,+string)).
foreign(sql_fetch_row,c,sql_fetch_row(+address,-integer)).
foreign(sql_get_column,c,sql_get_column(+address,+integer,-string)).
foreign(sql_close_cursor,c,sql_close_cursor(+address)).
foreign(sql_exec_cursor,c,sql_exec_cursor(+address)).
foreign(sql_open_db,c,sql_open_db(+string,-integer)).
foreign(sql_close_db,c,sql_close_db).

:- load_foreign_files(['sql_inter.o'],['/home/mint/oracle/rdbms/lib/osntab.o',
	'/home/mint/oracle/c/lib/libocic.a',
	'/home/mint/oracle/rdbms/lib/libsqlnet.a',
	'/home/mint/oracle/rdbms/lib/libora.a',
	'/usr/5lib/libc.a']).

:- pred sql_open_cursor(str,int).
:- pred sql_fetch_row(int,int).
:- pred sql_get_column(int,int,str).
:- pred sql_close_cursor(int).
:- pred sql_exec_cursor(int).
:- pred sql_open_db(str,int).
:- pred sql_close_db.

:- pred sql_redo_fetch(int).
:- pred sql_convert_column(etype,str,A).
:- pred sql_get_columns(int,int,*etype,mix).

sql_redo_fetch(C) :- sql_fetch_row(C,0), (true; !, sql_redo_fetch(C)).

sql_convert_column(s,X,X).
sql_convert_column(n(i),X,Y) :-
  atom_chars(X,L), number_chars(Y,L).
sql_convert_column(n(f),X,Y) :-
  atom_chars(X,L),
  (\+ mem(46,L) -> append(L,[46,48],K);		/* n to n.0 */
   L=[46|R] -> K=[48,46|R]; 			/* .n to 0.n */
   L=[45,46|R] -> K=[45,48,46|R];		/* -.n to -0.n */
   K=L),
  number_chars(Y,K).

sql_get_columns(_,_,[],[]).
sql_get_columns(C,I,[S|R],[X|Y]) :-
  sql_get_column(C,I,H),
  sql_convert_column(S,H,X),
  J is I+1, !, sql_get_columns(C,J,R,Y).

:- pred sql_sel(str,*etype,mix).
:- pred sql_exec(str).
:- pred sql_sel2(selstat,*etype,mix).
:- pred sql_exec2(stat).

sql_sel(S,T,X) :-
  (clause(verbose,true) -> write(S), nl; true),
  sql_open_cursor(S,C),
  findall(X,(sql_redo_fetch(C), sql_get_columns(C,0,T,X)),L),
  sql_close_cursor(C),
  mem(X,L).

sql_exec(S) :-
  (clause(verbose,true) -> write(S), nl; true),
  sql_open_cursor(S,C), sql_exec_cursor(C), sql_close_cursor(C).

sql_sel2(G,T,X) :-
  g_selstat(G,L,[]), atom_chars(S,L), sql_sel(S,T,X).

sql_exec2(G) :-
  g_stat(G,L,[]), atom_chars(S,L), sql_exec(S).

/************************************************************************/
/* .									*/
/************************************************************************/
