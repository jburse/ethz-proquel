/************************************************************************/
/************************************************************************/
/*              e r r o r . p                                           */
/*                                                                      */
/* Export:                                                              */
/*              err/1 (parser.p,checker.p,main.p)                       */
/* Import:                                                              */
/*              tabcharcomb/3 (parser.p)                                */
/*              uscntokens/3 (parser.p)                                 */
/*              uscntoken/3 (parser.p)                                  */
/*              uscnchars/3 (parser.p)                                  */
/*              uparform/3 (parser.p)                                   */
/************************************************************************/
/************************************************************************/

/************************************************************************/
/************************************************************************/
/* M E S S A G E S							*/
/************************************************************************/
/************************************************************************/

:- pred err(err).
:- pred err_flag.

:- type err = scan(serr,*int) + 
              pars(perr,*token) + type_already_decl(str) + type_not_decl(str) +
              pred_already_decl(str) + pred_not_decl(str) +
              pred_used_in(str,str) + type_used_in(str,int,str) +
                /* sort inference */
              type_mismatch(form,ftype) + too_few_arguments(form) +
              too_many_arguments(form) +
                /* allowedness check */
              unbound_var(str) +
                /* stratification check */
              not_strat(str).
:- type serr = illegal_ch + unbal_comment + unbal_str.
:- type perr = token_expect(token) + garbage_line + faktor_expect + 
               type_expect + on_off_expect.

:- pred e_err(err,*int,*int).
:- pred e_msg(err,*int,*int).
:- pred e_smsg(serr,*int,*int).
:- pred e_pmsg(perr,*int,*int).

e_err(E)			--> "*** Error: ", e_msg(E), ".".

e_msg(scan(E,L)) 		--> e_smsg(E), " at '", uscnchars(L), "'".
e_msg(pars(E,L)) 		--> e_pmsg(E), " at '", uscntokens(L), "'".

e_smsg(illegal_ch) 		--> "Illegal character".
e_smsg(unbal_comment) 		--> "Unbalanced comment".
e_smsg(unbal_str) 		--> "Unbalanced string".

e_pmsg(token_expect(tid(_))) 	--> !, "Identifier expected".
e_pmsg(token_expect(tvar(_))) 	--> !, "Variable expected".
e_pmsg(token_expect(tstr(_))) 	--> !, "String expected".
e_pmsg(token_expect(X)) 	--> "'", tabcharcomb(X), "' expected".
e_pmsg(garbage_line) 		--> "Line not properly ended".
e_pmsg(faktor_expect) 		--> "Faktor expected".
e_pmsg(type_expect) 		--> "Type expected".

e_msg(pred_already_decl(P)) --> 
  "Predicate ", uscntoken(tid(P)), " already declared".
e_msg(pred_not_decl(P))	--> 
  "Predicate ", uscntoken(tid(P)), " not declared".
e_msg(pred_used_in(P,Q)) --> 
  "Predicate ", uscntoken(tid(P)), " still used in predicate ", uscntoken(tid(Q)).
e_msg(type_mismatch(E,T)) --> 
  {uparform(E,L,[])}, uscntokens(L), " is not ", e_type(T).
e_msg(too_few_arguments(E)) --> 
  "Too few arguments in ", {uparform(E,L,[])}, uscntokens(L).
e_msg(too_many_arguments(E)) --> 
  "Too many arguments in ", {uparform(E,L,[])}, uscntokens(L).
e_msg(unbound_var(V)) -->
  uscntoken(tvar(V)), " not bound".
e_msg(not_strat(X)) -->
  "Predicate ", uscntoken(tid(X)), " induces a negative cycle".
e_msg(type_already_decl(P)) -->
  "Type ", uscntoken(tid(P)), " already declared".
e_msg(type_not_decl(P)) -->
  "Type ", uscntoken(tid(P)), " not declared".
e_msg(type_used_in(P,0,Q)) -->
  "Type ", uscntoken(tid(P)), " still used in type ", uscntoken(tid(Q)).
e_msg(type_used_in(P,1,Q)) -->
  "Type ", uscntoken(tid(P)), " still used in predicate ", uscntoken(tid(Q)).
 
:- pred e_type(ftype,*int,*int).

e_type(f) --> "a formula".
e_type(e(X)) --> {var(X)}, "an expression".
e_type(e(s)) --> "a string expression".
e_type(e(n(X))) --> {var(X)}, "a numeric expression".
e_type(e(n(i))) --> "an integer expression".
e_type(e(n(f))) --> "a float expression".

err(X) :- e_err(X,L,[]), name(S,L), write(S), nl, !, assertz(err_flag).

/****************************************************************/
/* .								*/
/****************************************************************/


