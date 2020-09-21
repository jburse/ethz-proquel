/**
 * Boole's Method from 1847
 * https://stackoverflow.com/a/63603544/502187
 * Variant that can check simultaneously tautology and antilogy.
 *
 * Verbose write statements and more
 * firendly operators by Joseph Vidal-Rosset
 *
 * Warranty & Liability
 * To the extent permitted by applicable law and unless explicitly
 * otherwise agreed upon, XLOG Technologies GmbH makes no warranties
 * regarding the provided information. XLOG Technologies GmbH assumes
 * no liability that any problems might be solved with the information
 * provided by XLOG Technologies GmbH.
 *
 * Rights & License
 * All industrial property rights regarding the information - copyright
 * and patent rights in particular - are the sole property of XLOG
 * Technologies GmbH. If the company was not the originator of some
 * excerpts, XLOG Technologies GmbH has at least obtained the right to
 * reproduce, change and translate the information.
 *
 * Reproduction is restricted to the whole unaltered document. Reproduction
 * of the information is only allowed for non-commercial uses. Selling,
 * giving away or letting of the execution of the library is prohibited.
 * The library can be distributed as part of your applications and libraries
 * for execution provided this comment remains unchanged.
 *
 * Restrictions
 * Only to be distributed with programs that add significant and primary
 * functionality to the library. Not to be distributed with additional
 * software intended to replace any components of the library.
 *
 * Trademarks
 * Jekejeke is a registered trademark of XLOG Technologies GmbH.
 */

:- op(700, xfy, <=>).
:- op(600, xfy, =>).
:- op(500, xfy, v).
:- op(400, xfy, &).
:- op(300, fy, ~).

/**
 * eval(A, R):
 * The predicate succeeds in R with a partial evaluated
 * Boolean formula. The predicate starts with the leaves
 * and calls simp after forming new nodes.
 */
% eval(+Formula, -Formula)
eval(A, A) :- var(A), !.
eval(A => B, R) :- !, eval(A, X), eval(B, Y), simp(X => Y, R).
eval(A <=> B, R) :- !, eval(A, X), eval(B, Y), simp(X <=> Y, R).
eval(A v B, R) :- !, eval(A, X), eval(B, Y), simp(X v Y, R).
eval(A & B, R) :- !, eval(A, X), eval(B, Y), simp(X & Y, R).
eval(~A, R) :- !, eval(A, X), simp(~X, R).
eval(A, A).

/**
 * simp(A, B):
 * The predicate succeeds in B with a simpler formula than A,
 * or if an immediately simpler formula is not possible with
 * formula B itself.
 */
% simp(+Formula, -Formula)
simp(A, A) :- var(A), !.
simp(A => _, 1) :- A == 0, !.
simp(A => B, X) :- B == 0, !, simp(~A, X).
simp(A => B, B) :- A == 1, !.
simp(_ => B, 1) :- B == 1, !.
simp(A <=> B, X) :- A == 0, !, simp(~B, X).
simp(A <=> B, X) :- B == 0, !, simp(~A, X).
simp(A <=> B, B) :- A == 1, !.
simp(A <=> B, A) :- B == 1, !.
simp(A v B, B) :- A == 0, !.
simp(A v B, A) :- B == 0, !.
simp(A v _, 1) :- A == 1, !.
simp(_ v B, 1) :- B == 1, !.
simp(A & _, 0) :- A == 0, !.
simp(_ & B, 0) :- B == 0, !.
simp(A & B, B) :- A == 1, !.
simp(A & B, A) :- B == 1, !.
simp(~A, 1) :- A == 0, !.
simp(~A, 0) :- A == 1, !.
simp(A, A).

taut(A, T, N) :-
    eval(A, B),
    write_term(A, [variable_names(N)]), nl,
    write_term(B, [variable_names(N)]), nl,
    write('------------------------------'), nl,
    term_variables(B, L), taut(B, L, T, N).

taut(T, [], T, _).
taut(A, [B|_], T, N) :-
  catch((putSubst(B, 1, N), B = 1,
         taut(A, T, N), throw(T)), T, true),
  putSubst(B, 0, N), B = 0,
  taut(A, S, N), T = S.

putSubst(B, V, N) :-
    write_term(B, [variable_names(N)]),
    write(' = '),
    write(V), write(':'), nl.

quine:-
    read_term(A, [variable_names(N)]),
    (  taut(A, T, N) ->
       (T == 1 ->
          write('to prove that the formula is a tautology.'), nl
       ;
          write('to prove that the formula is an antilogy.'), nl
       )
    ;
      write('to prove that the formula is neither a tautology nor an antilogy.'), nl
    ).