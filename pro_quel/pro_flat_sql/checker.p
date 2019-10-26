/************************************************************************/
/************************************************************************/
/*              c h e c k e r . p                                       */
/*                                                                      */
/* Export:                                                              */
/*              chk/3 (main.p)                                          */
/*              rewrite_form/4 (main.p)                                 */
/*              norm/3 (main.p)                                         */
/*              varof/2 (eval.p,main.p)                                 */
/*              orof/2 (eval.p)                                         */
/*              allowed/2 (main.p)                                      */
/*              predof/3 (main.p)                                       */
/*              stratified/2 (main.p)                                   */
/*              plan/2 (main.p)                                         */
/* Import:                                                              */
/*              mem/2 (main.p)                                          */
/*              set_of/3 (main.p)                                       */
/*              scantokens/3 (parser.p)                                 */
/*              parsdecl/4 (parser.p)                                   */
/*              db_fetch/1 (meta.p)                                     */
/*              err/1 (error.p)                                         */
/************************************************************************/
/************************************************************************/

/************************************************************************/
/************************************************************************/
/* E X P A N D   T Y P E						*/
/************************************************************************/
/************************************************************************/

/* The expand_list/2 predicate replace all type name occurences in a type
   by their definition. The type_of/2 predicate gives the type names that 
   occure in a type. */

:- pred expand_type(etype,etype).
:- pred expand_list(*etype,*etype).
:- pred type_of(etype,str).

expand_type(s,s).
expand_type(n(i),n(i)).
expand_type(n(f),n(f)).
expand_type(i(N),T) :-
  db_fetch(type(N,S)), name(S,CS), scantokens(TS,CS,[]), 
  parstype(H,TS,[]), expand_type(H,T).

expand_list([],[]).
expand_list([X|Y],[Z|T]) :-
  expand_type(X,Z), expand_list(Y,T).

type_of(s,_) :- fail.
type_of(n(i),_) :- fail.
type_of(n(f),_) :- fail.
type_of(i(N),N).

/************************************************************************/
/************************************************************************/
/* S O R T   I N F E R E N C E						*/
/************************************************************************/
/************************************************************************/

/* the chk/3 predicate infers the sorts of the given form. A formula
   has the sort descriptor f, an expression of type T the sort descriptor
   e(T). */

:- type ftype = f + e(etype). 		/* extended sort descriptor */
:- type tassoc = str-etype. 		/* variable name type pairs */

:- pred chk(form,ftype,*tassoc). 	/* check form */
:- pred chklist(*form,*etype,*tassoc). 	/* check expression list */

chk(senti,e(_),_) :- !.
chk(cstr(_),e(s),_) :- !.
chk(cint(_),e(n(i)),_) :- !.
chk(cfloat(_),e(n(f)),_) :- !.
chk(var(V),e(T),L) :- mem(V-S,L), !, (S=T -> true; err(type_mismatch(var(V),e(T)))).
chk(neg(A),e(n(T)),L) :- !, chk(A,e(n(T)),L).
chk(int(A),e(n(i)),L) :- !, chk(A,e(n(f)),L).
chk(float(A),e(n(f)),L) :- !, chk(A,e(n(i)),L).
chk(add(A,B),e(n(T)),L) :- !, chk(A,e(n(T)),L), chk(B,e(n(T)),L).
chk(sub(A,B),e(n(T)),L) :- !, chk(A,e(n(T)),L), chk(B,e(n(T)),L).
chk(mul(A,B),e(n(T)),L) :- !, chk(A,e(n(T)),L), chk(B,e(n(T)),L).
chk(quo(A,B),e(n(f)),L) :- !, chk(A,e(n(f)),L), chk(B,e(n(f)),L).
chk(div(A,B),e(n(i)),L) :- !, chk(A,e(n(i)),L), chk(B,e(n(i)),L).
chk(mod(A,B),e(n(i)),L) :- !, chk(A,e(n(i)),L), chk(B,e(n(i)),L).
chk(true,f,_) :- !.
chk(eq(A,B),f,L) :- !, chk(A,e(T),L), chk(B,e(T),L).
chk(nq(A,B),f,L) :- !, chk(A,e(T),L), chk(B,e(T),L).
chk(ls(A,B),f,L) :- !, chk(A,e(T),L), chk(B,e(T),L).
chk(gr(A,B),f,L) :- !, chk(A,e(T),L), chk(B,e(T),L).
chk(lq(A,B),f,L) :- !, chk(A,e(T),L), chk(B,e(T),L).
chk(gq(A,B),f,L) :- !, chk(A,e(T),L), chk(B,e(T),L).
chk(not(A),f,L) :- !, chk(A,f,L).
chk(and(A,B),f,L) :- !, chk(A,f,L), chk(B,f,L).
chk(or(A,B),f,L) :- !, chk(A,f,L), chk(B,f,L).
chk(imp(A,B),f,L) :- !, chk(A,f,L), chk(B,f,L).
chk(ex(W,A),f,L) :- !, chk(A,f,[W-_|L]).
chk(all(W,A),f,L) :- !, chk(A,f,[W-_|L]).
chk(pred(P,A),f,L) :- !,
  (db_fetch(pred(P,T)) -> 
     name(T,CS), scantokens(TS,CS,[]), 
     parsdecl(D1,TS,[]), expand_list(D1,D),
     length(A,N1), length(D,N2),
     (N1>N2 -> err(too_many_arguments(pred(P,A)));
      N1<N2 -> err(too_few_arguments(pred(P,A)));
      chklist(A,D,L)); err(pred_not_decl(P))).
chk(E,T,_) :- err(type_mismatch(E,T)).

chklist([],[],_).
chklist([A|B],[P|Q],L) :- chk(A,e(P),L), chklist(B,Q,L).

/************************************************************************/
/************************************************************************/
/* R E W R I T E   F O R M						*/
/************************************************************************/
/************************************************************************/

/* the rewrite_form/2 predicate replaces sentinels (_) by existential
   quantifiers. The elemination is performed by replacing an atom A(_)
   by #X A(X) where X is a fresh variable. Example:

   ships(X,_) & cargoes(X,Y,_,_) ==>
     #X0 ships(X,X0) & #X1 #X2 cargoes(X,Y,X1,X2)

   ships(X,_) & ~cargoes(X,_,_,_) ==>
     #X0 ships(X,X0) & ~#X1 #X2 #X3 cargoes(X,X1,X2,X3)

*/

:- pred rewrite_form(form,form,int,int).
:- pred rewrite_term(form,form,form,form,int,int).
:- pred rewrite_list(*form,*form,form,form,int,int).

rewrite_form(true,true,N,N).
rewrite_form(not(A),not(B),N,M) :- rewrite_form(A,B,N,M).
rewrite_form(and(A,B),and(C,D),N,M) :- rewrite_form(A,C,N,H), rewrite_form(B,D,H,M).
rewrite_form(or(A,B),or(C,D),N,M) :- rewrite_form(A,C,N,H), rewrite_form(B,D,H,M).
rewrite_form(imp(A,B),imp(C,D),N,M) :- rewrite_form(A,C,N,H), rewrite_form(B,D,H,M).
rewrite_form(ex(W,A),ex(W,B),N,M) :- rewrite_form(A,B,N,M).
rewrite_form(all(W,A),all(W,B),N,M) :- rewrite_form(A,B,N,M).
rewrite_form(eq(A,B),C,N,M) :- rewrite_term(A,X,eq(X,Y),D,N,H), rewrite_term(B,Y,D,C,H,M).
rewrite_form(nq(A,B),C,N,M) :- rewrite_term(A,X,nq(X,Y),D,N,H), rewrite_term(B,Y,D,C,H,M).
rewrite_form(ls(A,B),C,N,M) :- rewrite_term(A,X,ls(X,Y),D,N,H), rewrite_term(B,Y,D,C,H,M).
rewrite_form(lq(A,B),C,N,M) :- rewrite_term(A,X,lq(X,Y),D,N,H), rewrite_term(B,Y,D,C,H,M).
rewrite_form(gr(A,B),C,N,M) :- rewrite_term(A,X,gr(X,Y),D,N,H), rewrite_term(B,Y,D,C,H,M).
rewrite_form(gq(A,B),C,N,M) :- rewrite_term(A,X,gq(X,Y),D,N,H), rewrite_term(B,Y,D,C,H,M).
rewrite_form(pred(P,L),C,N,M) :- rewrite_list(L,R,pred(P,R),C,N,M).

rewrite_term(senti,var(W),A,ex(W,A),N,M) :- name(N,L), name(W,[88|L]), M is N+1.
rewrite_term(var(V),var(V),A,A,N,N).
rewrite_term(cstr(X),cstr(X),A,A,N,N).
rewrite_term(cint(X),cint(X),A,A,N,N).
rewrite_term(cfloat(X),cfloat(X),A,A,N,N).
rewrite_term(neg(X),neg(Y),A,B,N,M) :- rewrite_term(X,Y,A,B,N,M).
rewrite_term(int(X),int(Y),A,B,N,M) :- rewrite_term(X,Y,A,B,N,M).
rewrite_term(float(X),float(Y),A,B,N,M) :- rewrite_term(X,Y,A,B,N,M).
rewrite_term(add(X,Y),add(Z,T),A,B,N,M) :- 
  rewrite_term(X,Z,A,C,N,H), rewrite_term(Y,T,C,B,H,M).
rewrite_term(sub(X,Y),sub(Z,T),A,B,N,M) :- 
  rewrite_term(X,Z,A,C,N,H), rewrite_term(Y,T,C,B,H,M).
rewrite_term(mul(X,Y),mul(Z,T),A,B,N,M) :- 
  rewrite_term(X,Z,A,C,N,H), rewrite_term(Y,T,C,B,H,M).
rewrite_term(div(X,Y),div(Z,T),A,B,N,M) :- 
  rewrite_term(X,Z,A,C,N,H), rewrite_term(Y,T,C,B,H,M).
rewrite_term(mod(X,Y),mod(Z,T),A,B,N,M) :- 
  rewrite_term(X,Z,A,C,N,H), rewrite_term(Y,T,C,B,H,M).
rewrite_term(quo(X,Y),quo(Z,T),A,B,N,M) :- 
  rewrite_term(X,Z,A,C,N,H), rewrite_term(Y,T,C,B,H,M).

rewrite_list([],[],A,A,N,N).
rewrite_list([X|Y],[Z|T],A,B,N,M) :- rewrite_term(X,Z,A,C,N,H), rewrite_list(Y,T,C,B,H,M).

/************************************************************************/
/************************************************************************/
/* N O R M A L I Z E R							*/
/************************************************************************/
/************************************************************************/

/* The predicate norm/3 normalizes a formula. The normalization rules are 
   given as ==>/2 facts. The predicate norm/3 applies the rules as long as 
   possible and returns the formula if it cannot be further reduced. */

:- op(850,xfx,'==>').

:- pred form==>form. 			/* the rewrite rules */
:- pred get_arg(form,int,form).		/* traversing of the terms */
:- pred put_arg(form,int,form,form).	/* modification of the terms */
:- pred try_first(form,*int,form).	/* try terms above the last term */
:- pred try_next(form,*int,*int,form).	/* try terms on left of the last term */
:- pred norm(form,*int,form).		/* normalize term */

/* eliminate imp and all */
imp(X,Y)		==> or(not(X),Y).
all(W,X)		==> not(ex(W,not(X))).

/* move not inside */
not(and(X,Y))		==> or(not(X),not(Y)).
not(or(X,Y))		==> and(not(X),not(Y)).
not(not(X))		==> X.

/* move or outside */
and(X,or(Y,Z))		==> or(and(X,Y),and(X,Z)).
and(or(X,Y),Z)		==> or(and(X,Z),and(Y,Z)).
ex(W,or(X,Y))		==> or(ex(W,X),ex(W,Y)).

/* not of comparison */
not(ls(X,Y))		==> gq(X,Y).
not(gr(X,Y))		==> lq(X,Y).
not(eq(X,Y))		==> nq(X,Y).
not(gq(X,Y))		==> ls(X,Y).
not(lq(X,Y))		==> gr(X,Y).
not(nq(X,Y))		==> eq(X,Y).

get_arg(and(X,_),0,X).
get_arg(and(_,Y),1,Y).
get_arg(or(X,_),0,X).
get_arg(or(_,Y),1,Y).
get_arg(imp(X,_),0,X).
get_arg(imp(_,Y),1,Y).
get_arg(not(X),0,X).
get_arg(ex(_,X),0,X).
get_arg(all(_,X),0,X).

put_arg(and(_,Y),0,Z,and(Z,Y)).
put_arg(and(X,_),1,Z,and(X,Z)).
put_arg(or(_,Y),0,Z,or(Z,Y)).
put_arg(or(X,_),1,Z,or(X,Z)).
put_arg(imp(_,Y),0,Z,imp(Z,Y)).
put_arg(imp(X,_),1,Z,imp(X,Z)).
put_arg(not(_),0,Z,not(Z)).
put_arg(ex(V,_),0,Z,ex(V,Z)).
put_arg(all(V,_),0,Z,all(V,Z)).

try_first(X,[],Y) :- X==>Y.
try_first(X,[N|P],Y) :- get_arg(X,N,Z), try_first(Z,P,T), put_arg(X,N,T,Y).

try_next(X,[],P,Y) :- try_first(X,P,Y).
try_next(X,[_|_],[],Y) :- X==>Y.
try_next(X,[N|P],[N|Q],Y) :- get_arg(X,N,Z), try_next(Z,P,Q,T), put_arg(X,N,T,Y).
try_next(X,[N|_],[M|Q],Y) :- get_arg(X,M,Z), M>N, try_first(Z,Q,T), put_arg(X,M,T,Y).

norm(X,P,Y) :- try_next(X,P,Q,Z), !, norm(Z,Q,Y).
norm(X,_,X).

/************************************************************************/
/************************************************************************/
/* A L L O W E D N E S S   C H E C K					*/
/************************************************************************/
/************************************************************************/

/* The predicate allowed/2 checks the allowedness of a rule or query. It is
   called with an expression list and a normalized formula. The predicate
   calls ok/2 and checks the boundess of the expression list for all the
   or-free parts of the normalized formula. */

:- pred varof(form,str). /* str occurs free in form */
:- pred bound(form,*str). /* form is input expression */
:- pred ok(form,*str). /* form is allowed for input */
:- pred orof(form,form). /* enumerate the or free parts */
:- pred allowed(*form,form). /* rule allowed */

varof(ex(W,F),V) :- !, varof(F,V), W\==V.
varof(all(W,F),V) :- !, varof(F,V), W\==V.
varof(and(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(or(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(imp(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(not(X),V) :- !, varof(X,V).
varof(pred(_,L),V) :- !, mem(X,L), varof(X,V).
varof(lq(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(gq(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(nq(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(ls(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(gr(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(eq(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(true,_) :- !, fail.
varof(add(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(sub(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(mod(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(div(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(quo(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(mul(X,Y),V) :- !, (varof(X,V); varof(Y,V)).
varof(float(X),V) :- !, varof(X,V).
varof(int(X),V) :- !, varof(X,V).
varof(neg(X),V) :- !, varof(X,V).
varof(cstr(_),_) :- !, fail.
varof(cint(_),_) :- !, fail.
varof(cfloat(_),_) :- !, fail.
varof(var(V),V) :- !.

bound(X,S) :- (varof(X,V), (mem(V,S) -> true; err(unbound_var(V))), fail; true).

ok(true,_).
ok(eq(X,Y),S) :- (X=var(_)->bound(Y,S);Y=var(_)->bound(X,S);bound(X,S), bound(Y,S)).
ok(ls(X,Y),S) :- bound(X,S), bound(Y,S).
ok(gr(X,Y),S) :- bound(X,S), bound(Y,S).
ok(lq(X,Y),S) :- bound(X,S), bound(Y,S).
ok(gq(X,Y),S) :- bound(X,S), bound(Y,S).
ok(nq(X,Y),S) :- bound(X,S), bound(Y,S).
ok(and(X,Y),S) :- ok(X,S), set_of(V,(mem(V,S);varof(X,V)),R), ok(Y,R).
ok(ex(W,X),S) :- set_of(V,(mem(V,S),V\==W),R), ok(X,R).
ok(not(X),S) :- bound(X,S), ok(X,S).
ok(pred(_,A),S) :- (mem(E,A), (E=var(_) -> true;bound(E,S)), fail; true).

orof(or(A,B),C) :- !, (orof(A,C);orof(B,C)).
orof(A,A).

allowed(E,NQ) :-
  (orof(NQ,Q), ok(Q,[]),
     set_of(V,varof(Q,V),S),
     (mem(A,E), bound(A,S), fail; true), fail; true).

/************************************************************************/
/************************************************************************/
/* S T R A T I F I C A T I O N   C H E C K				*/
/************************************************************************/
/************************************************************************/

:- type sgn = str-int.

:- pred predof(form,str,int).
:- pred notsafe(str,str,int,*str).
:- pred stratified(str,form).

predof(ex(_,E),P,S) :- predof(E,P,S).
predof(all(_,E),P,S) :- predof(E,P,S).
predof(not(E),P,S) :- predof(E,P,S1), S is 1-S1.
predof(and(E,F),P,S) :- predof(E,P,S); predof(F,P,S).
predof(or(E,F),P,S) :- predof(E,P,S); predof(F,P,S).
predof(imp(E,F),P,S) :- predof(E,P,S1), S is 1-S1; predof(F,P,S).
predof(pred(P,_),P,1).

notsafe(P,P,0,_).
notsafe(P,Q,SG,L) :-
  \+ mem(Q,L), 
  set_of(H-SG2,(db_fetch(deps(Q,_,H,SG1)), SG2 is SG*SG1),S),
  mem(H-SG2,S),
  notsafe(P,H,SG2,[Q|L]).

stratified(P,F) :-
  set_of(Q-SG,predof(F,Q,SG),S),
  (mem(Q-SG,S), notsafe(P,Q,SG,[P]), err(not_strat(Q)), fail; true).

/************************************************************************/
/************************************************************************/
/* P L A N   G E N E R A T I O N					*/
/************************************************************************/
/************************************************************************/

:- type scc = str - *str.

:- pred sccforpred(str,*str,*scc,*scc,*str).
:- pred sccforlist(*str,*str,*scc,*scc,*str).
:- pred plan(form,*scc).

sccforpred(P,S,H,H,[P]) :-
  mem(P,S), !.
sccforpred(P,_,H,H,[]) :-
  mem(Q-L,H), (Q=P; mem(P,L)), !.
sccforpred(P,S,I,O2,R2) :-
  set_of(Q,db_fetch(deps(P,_,Q,_)),L),
  sccforlist(L,[P|S],I,O,R),
  !, (mem(U,R), mem(U,S) -> O2=O, R2=[P|R]; O2=[P-R|O], R2=[]).

sccforlist([],_,H,H,[]).
sccforlist([P|Q],S,I,O,R) :-
  sccforpred(P,S,I,H,R1),
  sccforlist(Q,S,H,O,R2),
  !, set_of(U,(mem(U,R1);mem(U,R2)),R).

plan(F,P) :-
  set_of(Q,predof(F,Q,_),L),
  !, sccforlist(L,[],[],P,_).

/************************************************************************/
/* .									*/
/************************************************************************/
