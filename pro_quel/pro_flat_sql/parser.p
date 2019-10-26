/************************************************************************/
/************************************************************************/
/*              p a r s e r . p                                         */
/*                                                                      */
/* Export:                                                              */
/*              tabcharcomb/3 (error.p)                                 */
/*              scantokens/3 (checker.p,main.p)                         */
/*              uscntokens/3 (error.p,main.p)                           */
/*              uscntoken/3 (error.p)                                   */
/*              uscnchars/3 (error.p)                                   */
/*              parsrule/5 (main.p)                                     */
/*              parsdecl/4 (checker.p)                                  */
/*              parscom/3 (main.p)                                      */
/*              uparform/3 (error.p,main.p)                             */
/*              uparrule/5 (main.p)                                     */
/*              upardecl/4 (main.p)                                     */
/* Import:                                                              */
/*              mem/2 (main.p)                                          */
/*              err/1 (error.p)                                         */
/************************************************************************/
/************************************************************************/

/************************************************************************/
/************************************************************************/
/* S C A N N E R 							*/
/************************************************************************/
/************************************************************************/

:- type token = tsp +
                /* parametric tokens */
             tid(str) + tvar(str) + tfloat(float) + 
             tint(int) + tstr(str) + 
                /* reserved words */
             tcreate + tlist +
             tstr + tdrop + tquery + tquit + tassert + ttrue +
             tfloat + tretract + tint + tmod + tdiv + topen +
             tdefine + tundefine +
	     tclose + tverbose + ton + toff + tclear + 
                /* character combinations */
             tlimp + trimp + tand + tor + tnot + tex + tall +
             teq + tls + tgr + tnq + tgq + tlq + tstar + tslash + 
             tminus + tplus + tlpar + trpar + tcomma + tsenti.

:- dcg tabcharcomb(token). /* dcg for the character combinations */
:- pred tabresword(*int,token). /* table with reserved words */

tabcharcomb(tnq) 	--> "\=".
tabcharcomb(tlq) 	--> "<=".
tabcharcomb(tgq) 	--> ">=".
tabcharcomb(tlpar) 	--> "(".
tabcharcomb(trpar) 	--> ")".
tabcharcomb(tcomma) 	--> ",".
tabcharcomb(tlimp) 	--> "<-".
tabcharcomb(trimp)	--> "->".
tabcharcomb(tand) 	--> "&".
tabcharcomb(tor)	--> "|".
tabcharcomb(tnot) 	--> "~".
tabcharcomb(tex) 	--> "#".
tabcharcomb(tall) 	--> "@".
tabcharcomb(tminus) 	--> "-".
tabcharcomb(tplus) 	--> "+".
tabcharcomb(tls) 	--> "<".
tabcharcomb(teq) 	--> "=".
tabcharcomb(tgr) 	--> ">".
tabcharcomb(tstar) 	--> "*".
tabcharcomb(tslash) 	--> "/".
tabcharcomb(tsenti)	--> "_".

tabresword("create",	tcreate).
tabresword("list",	tlist).
tabresword("str",	tstr).
tabresword("drop",	tdrop).
tabresword("query",	tquery).
tabresword("quit",	tquit).
tabresword("assert",	tassert).
tabresword("true",	ttrue).
tabresword("float",	tfloat).
tabresword("retract",	tretract).
tabresword("int",	tint).
tabresword("mod",	tmod).
tabresword("div",	tdiv).
tabresword("open",	topen).
tabresword("close",	tclose).
tabresword("verbose",	tverbose).
tabresword("on",	ton).
tabresword("off",	toff).
tabresword("clear",	tclear).
tabresword("define",	tdefine).
tabresword("undefine",	tundefine).

:- dcg charcap(int). 		/* classify as capital letter character */
:- dcg charsmall(int). 		/* classify as small letter character */
:- dcg chardigit(int). 		/* classify as digit character */

charcap(X) 		--> [X], {X=<90,X>=65}.
charsmall(X) 		--> [X], {X=<122,X>=97}.
chardigit(X) 		--> [X], {X=<57,X>=48}.

:- dcg scanerr(serr). 		/* generate scanner error with actual pos */
:- dcg scantokens(*token). 	/* scan token list */
:- dcg scantoken(token). 	/* scan token */
:- dcg scancomment. 		/* scan comment */
:- dcg scanident(*int). 	/* scan letters and digits */
:- dcg scanmant(*int). 		/* scan digits of mantissa, fraction and exponent */
:- dcg scanfrac(*int). 		/* scan digits of fraction and exponent */
:- dcg scanstring(*int). 	/* scan rest of string */
:- dcg scanexpo(*int).		/* scan digits of exponent */

scanerr(E,L,L) :- err(scan(E,L)).

scantokens(X) 		--> " ", !, scantokens(X).
scantokens(X) 		--> "/*", !, scancomment, scantokens(X).
scantokens([X|R]) 	--> scantoken(X), !, scantokens(R).
scantokens(X) 		--> [_], !, scanerr(illegal_ch), scantokens(X).
scantokens([]) 		--> [].

scantoken(tvar(Z))	--> charcap(X), !, scanident(Y), {atom_chars(Z,[X|Y])}.
scantoken(Z) 		--> charsmall(X), !, scanident(Y), 
  {tabresword([X|Y],Z) -> true; atom_chars(H,[X|Y]), Z=tid(H)}.
scantoken(Z) 		--> chardigit(X), !, scanmant(Y), 
  {mem(46,Y) -> number_chars(H,[X|Y]), Z=tfloat(H); number_chars(K,[X|Y]), Z=tint(K)}.
scantoken(tstr(Z))	--> "'", !, scanstring(X), {atom_chars(Z,X)}.
scantoken(Z) 		--> tabcharcomb(Z).

scancomment 		--> "*/", !.
scancomment 		--> [_], !, scancomment.
scancomment 		--> scanerr(unbal_comment).

scanident([X|Y])	--> charcap(X), !, scanident(Y).
scanident([X|Y])	--> charsmall(X), !, scanident(Y).
scanident([X|Y])	--> chardigit(X), !, scanident(Y).
scanident([])		--> [].

scanmant([X|Y])		--> chardigit(X), !, scanmant(Y).
scanmant([46,X|Y])	--> ".", chardigit(X), !, scanfrac(Y). 
scanmant([])		--> [].

scanfrac([X|Y])		--> chardigit(X), !, scanfrac(Y).
scanfrac([69,X|Y])	--> "E", chardigit(X), !, scanexpo(Y).
scanfrac([69,45,X|Y])	--> "E-", chardigit(X), !, scanexpo(Y).
scanfrac([])		--> [].

scanexpo([X|Y])		--> chardigit(X), !, scanexpo(Y).
scanexpo([])		--> [].

scanstring([39|Y])	--> "''", !, scanstring(Y).
scanstring([])		--> "'", !. 
scanstring([X|Y])	--> [X], !, scanstring(Y).
scanstring([])		--> scanerr(unbal_str).

/************************************************************************/
/************************************************************************/
/* U N S C A N N E R 	 						*/
/************************************************************************/
/************************************************************************/

:- dcg uscntokens(*token). 	/* unscan token list */
:- dcg uscntoken(token). 	/* unscan token */
:- dcg uscnchars(*int). 	/* unscan list of characters */
:- dcg uscnstring(*int). 	/* unscan list of characters of a string */

uscntokens([X|Y])	--> uscntoken(X), !, uscntokens(Y).
uscntokens([]) 		--> [].

uscntoken(tsp)		--> " ".
uscntoken(tid(X)) 	--> {atom_chars(X,L)}, uscnchars(L).
uscntoken(tvar(X)) 	--> {atom_chars(X,L)}, uscnchars(L).
uscntoken(tfloat(X)) 	--> {number_chars(X,L)}, uscnchars(L).
uscntoken(tint(X)) 	--> {number_chars(X,L)}, uscnchars(L).
uscntoken(tstr(X)) 	--> "'", {atom_chars(X,L)}, uscnstring(L), "'".
uscntoken(X) 		--> tabcharcomb(X).
uscntoken(X) 		--> {tabresword(L,X)}, uscnchars(L).

uscnchars([X|Y])	--> [X], uscnchars(Y).
uscnchars([])		--> [].

uscnstring([39|Y])	--> !, "''", uscnstring(Y).
uscnstring([X|Y])	--> [X], uscnstring(Y).
uscnstring([])		--> [].

/************************************************************************/
/************************************************************************/
/* P A R S E R	 							*/
/************************************************************************/
/************************************************************************/

:- dcg parserr(perr). 		/* generate parsr error with actual pos */
:- dcg parsck(token). 		/* check for current token */
:- dcg parsfin. 		/* check for end of stream */

parserr(E,L,L) :- err(pars(E,L)).

parsck(X,[X|L],L) :- !.
parsck(X,L,L) :- err(pars(token_expect(X),L)).

parsfin(L,L) :- !.
parsfin(L,_) :- err(pars(garbage_line,L)).

:- type form =  /* formulas */
            imp(form,form) + or(form,form) + and(form,form) + not(form) +
            all(str,form) + ex(str,form) + true + eq(form,form) +
            nq(form,form) + ls(form,form) + gr(form,form) +
            lq(form,form) + gq(form,form) + pred(str,*form) +
               /* expressions */
            var(str) + neg(form) + sub(form,form) + add(form,form) + senti +
            mod(form,form) + div(form,form) + mul(form,form) + quo(form,form) + 
            int(form) + float(form) + cint(int) + cfloat(float) + cstr(str).

:- dcg parsform(form). 		/* parse formula */
:- dcg parsform2(form,form). 	/* parse rest of formula */
:- dcg parsdisj(form). 		/* parse disjunction */
:- dcg parsdisj2(form,form). 	/* parse rest of disjunction */
:- dcg parsconj(form). 		/* parse conjunction */
:- dcg parsconj2(form,form). 	/* parse rest of conjunction */
:- dcg parsprim(form). 		/* parse primformula */
:- dcg parsprim2(form,form). 	/* parse rest of primformula */
:- dcg parsxpr(form).		/* parse expression */
:- dcg parsxpr2(form,form). 	/* parse rest of expression */
:- dcg parsterm(form). 		/* parse term */
:- dcg parsterm2(form,form). 	/* parse rest of term */
:- dcg parsfaktor(form). 	/* parse faktor */
:- dcg parsarg(*form). 		/* parse arguments */
:- dcg parsarg2(*form). 	/* parse rest of arguments */

parsform(B)			--> parsdisj(A), parsform2(A,B).
parsform2(A,imp(A,B))		--> [trimp], !, parsdisj(B).
parsform2(A,A)			--> [].

parsdisj(B)			--> parsconj(A), parsdisj2(A,B).
parsdisj2(A,C)			--> [tor], !, parsconj(B), parsdisj2(or(A,B),C).
parsdisj2(A,A)			--> [].

parsconj(B)			--> parsprim(A), parsconj2(A,B).
parsconj2(A,C)			--> [tand], !, parsprim(B), parsconj2(and(A,B),C).
parsconj2(A,A)			--> [].

parsprim(not(A))		--> [tnot], !, parsprim(A).
parsprim(all(V,A))		--> [tall], !, parsck(tvar(V)), parsprim(A).
parsprim(ex(V,A))		--> [tex], !, parsck(tvar(V)), parsprim(A).
parsprim(true)			--> [ttrue], !.
parsprim(A)			--> parsxpr(B), parsprim2(B,A).
parsprim2(A,eq(A,B))		--> [teq], !, parsxpr(B).
parsprim2(A,ls(A,B))		--> [tls], !, parsxpr(B).
parsprim2(A,gr(A,B))		--> [tgr], !, parsxpr(B).
parsprim2(A,gq(A,B))		--> [tgq], !, parsxpr(B).
parsprim2(A,lq(A,B))		--> [tlq], !, parsxpr(B).
parsprim2(A,nq(A,B))		--> [tnq], !, parsxpr(B).
parsprim2(A,A)			--> [].

parsxpr(B)			--> [tminus], !, parsterm(A), parsxpr2(neg(A),B).
parsxpr(B)			--> parsterm(A), parsxpr2(A,B).
parsxpr2(A,C)			--> [tminus], !, parsterm(B), parsxpr2(sub(A,B),C).
parsxpr2(A,C)			--> [tplus], !, parsterm(B), parsxpr2(add(A,B),C).
parsxpr2(A,A)			--> [].

parsterm(B)			--> parsfaktor(A), parsterm2(A,B).
parsterm2(A,C)			--> [tstar], !, parsfaktor(B), parsterm2(mul(A,B),C).
parsterm2(A,C)			--> [tslash], !, parsfaktor(B), parsterm2(quo(A,B),C).
parsterm2(A,C)			--> [tmod], !, parsfaktor(B), parsterm2(mod(A,B),C).
parsterm2(A,C)			--> [tdiv], !, parsfaktor(B), parsterm2(div(A,B),C).
parsterm2(A,A)			--> [].

parsfaktor(senti)		--> [tsenti], !.
parsfaktor(cint(X))		--> [tint(X)], !.
parsfaktor(cfloat(X))		--> [tfloat(X)], !.
parsfaktor(cstr(X))		--> [tstr(X)], !.
parsfaktor(var(V))		--> [tvar(V)], !.
parsfaktor(int(X))		--> [tint],!,parsck(tlpar),parsxpr(X),parsck(trpar).
parsfaktor(float(X))		--> [tfloat],!,parsck(tlpar),parsxpr(X),parsck(trpar).
parsfaktor(A)			--> [tlpar], !, parsform(A), parsck(trpar).
parsfaktor(pred(P,A))		--> [tid(P)], !, parsarg(A).
parsfaktor(_)			--> parserr(faktor_expect).

parsarg([A|B])			--> [tlpar], !, parsxpr(A), parsarg2(B), parsck(trpar).
parsarg([])			--> [].
parsarg2([A|B])			--> [tcomma], !, parsxpr(A), parsarg2(B).
parsarg2([])			--> [].

:- type etype = n(ntype) + s + i(str). 	/* expression types */

:- type ntype = i + f. 			/* numeric expression types */

:- type com = verbose + create(str,*etype) + define(str,etype) +
           drop(str) + clear(str) + assert(str,*form,form) + undefine(str) +
           retract(str,*form,form) + list(str) + list + query(form) +
           quit + none.

:- dcg parscom(com).			/* parse command */
:- dcg parsrule(str,*form,form).	/* parse rule */
:- dcg parsrule2(form).			/* parse rest of rule */
:- dcg parsdecl(*etype).		/* parse declaration */
:- dcg parsdecl2(*etype).		/* parse rest of declaration */
:- dcg parstype(etype).			/* parse type */
:- dcg parsdef(str,etype).		/* parse definition */

parsrule(P,A,B)		--> parsck(tid(P)), parsarg(A), parsrule2(B).
parsrule2(Q)		--> [tlimp], !, parsform(Q).
parsrule2(true)		--> [].

parsdecl([A|B])		--> [tlpar], !, parstype(A), parsdecl2(B), parsck(trpar).
parsdecl([])		--> [].
parsdecl2([A|B])	--> [tcomma], !, parstype(A), parsdecl2(B).
parsdecl2([])		--> [].

parstype(n(i))		--> [tint], !.
parstype(n(f))		--> [tfloat], !.
parstype(s)		--> [tstr], !.
parstype(i(N))		--> [tid(N)], !.
parstype(_)		--> parserr(type_expect).

parscom(verbose)	--> [tverbose], !, parsfin. 
parscom(define(N,T))	--> [tdefine], !, parsck(tid(N)), parsck(teq), parstype(T), parsfin.
parscom(create(P,A))	--> [tcreate], !, parsck(tid(P)), parsdecl(A), parsfin.
parscom(undefine(N))	--> [tundefine], !, parsck(tid(N)), parsfin.
parscom(drop(P))	--> [tdrop], !, parsck(tid(P)), parsfin.
parscom(clear(P))	--> [tclear], !, parsck(tid(P)), parsfin.
parscom(assert(P,A,B))	--> [tassert], !, parsrule(P,A,B), parsfin.
parscom(retract(P,A,B))	--> [tretract], !, parsrule(P,A,B), parsfin.
parscom(list(P))	--> [tlist, tid(P)], !, parsfin.
parscom(list)		--> [tlist], !, parsfin.
parscom(query(Q))	--> [tquery], !, parsform(Q), parsfin.
parscom(quit)		--> [tquit], !, parsfin.
parscom(none)		--> [], !, parsfin.

/************************************************************************/
/************************************************************************/
/* U N P A R S E R							*/
/************************************************************************/
/************************************************************************/

:- dcg uparform(form).		/* unparse formula */
:- dcg upardisj(form).		/* unparse disjunction */
:- dcg uparconj(form).		/* unparse conjunction */
:- dcg uparprim(form).		/* unparse primformula */
:- dcg uparexpr(form).		/* unparse expression */
:- dcg uparterm(form).		/* unparse term */
:- dcg uparfaktor(form).	/* unparse faktor */
:- dcg upararg(*form).		/* unparse arguments */
:- dcg upararg2(*form).		/* unparse rest of arguments */

uparform(imp(A,B))		--> !, upardisj(A), [trimp], upardisj(B).
uparform(A)			--> upardisj(A).

upardisj(or(A,B))		--> !, upardisj(A), [tor], uparconj(B).
upardisj(A)			--> uparconj(A).

uparconj(and(A,B))		--> !, uparconj(A), [tand], uparprim(B).
uparconj(A)			--> uparprim(A).

uparprim(not(A))		--> !, [tnot], uparprim(A).
uparprim(all(V,A))		--> !, [tall, tvar(V), tsp], uparprim(A).
uparprim(ex(V,A))		--> !, [tex, tvar(V), tsp], uparprim(A).
uparprim(true)			--> !, [ttrue].
uparprim(ls(E,F))		--> !, uparexpr(E), [tls], uparexpr(F).
uparprim(gr(E,F))		--> !, uparexpr(E), [tgr], uparexpr(F).
uparprim(eq(E,F))		--> !, uparexpr(E), [teq], uparexpr(F).
uparprim(nq(E,F))		--> !, uparexpr(E), [tnq], uparexpr(F).
uparprim(lq(E,F))		--> !, uparexpr(E), [tlq], uparexpr(F).
uparprim(gq(E,F))		--> !, uparexpr(E), [tgq], uparexpr(F).
uparprim(A)			--> uparexpr(A).

uparexpr(add(A,B))		--> !, uparexpr(A), [tplus], uparterm(B).
uparexpr(sub(A,B))		--> !, uparexpr(A), [tminus], uparterm(B).
uparexpr(neg(A))		--> !, [tminus], uparterm(A).
uparexpr(A)			--> uparterm(A).

uparterm(mul(A,B))		--> !, uparterm(A), [tstar], uparfaktor(B).
uparterm(quo(A,B))		--> !, uparterm(A), [tslash], uparfaktor(B).
uparterm(div(A,B))		--> !, uparterm(A), [tsp, tdiv, tsp], uparfaktor(B).
uparterm(mod(A,B))		--> !, uparterm(A), [tsp, tmod, tsp], uparfaktor(B).
uparterm(A)			--> uparfaktor(A).

uparfaktor(senti)		--> !, [tsenti].
uparfaktor(cint(X))		--> !, [tint(X)].
uparfaktor(cfloat(X))		--> !, [tfloat(X)].
uparfaktor(cstr(X))		--> !, [tstr(X)].
uparfaktor(var(V))		--> !, [tvar(V)].
uparfaktor(pred(P,A))		--> !, [tid(P)], upararg(A).
uparfaktor(int(X))		--> !, [tint], [tlpar], uparexpr(X), [trpar].
uparfaktor(float(X))		--> !, [tfloat], [tlpar], uparexpr(X), [trpar].
uparfaktor(A)			--> [tlpar], uparform(A), [trpar].

upararg([A|B])			--> [tlpar], uparexpr(A), upararg2(B), [trpar].
upararg([])			--> [].
upararg2([A|B])			--> [tcomma], uparexpr(A), upararg2(B).
upararg2([])			--> [].

:- dcg uparrule(str,*form,form).	/* unparse rule */
:- dcg uparrule2(form).			/* unparse rest of rule */
:- dcg upardecl(*etype).		/* unparse declaration */
:- dcg upardecl2(*etype).		/* unparse rest of declaration */
:- dcg upartype(etype).			/* unparse expression type */

uparrule(P,A,B)			--> [tid(P)], upararg(A), uparrule2(B).
uparrule2(true)			--> !.
uparrule2(B)			--> [tlimp], uparform(B).

upardecl([X|Y])			--> [tlpar], upartype(X), upardecl2(Y), [trpar].
upardecl([])			--> [].
upardecl2([X|Y])		--> [tcomma], upartype(X), upardecl2(Y).
upardecl2([])			--> [].

upartype(n(i))			--> [tint].
upartype(n(f))			--> [tfloat].
upartype(s)			--> [tstr].
upartype(i(N))			--> [tid(N)].

/************************************************************************/
/* .									*/
/************************************************************************/
