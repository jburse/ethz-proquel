/*  File:    quineweb.pl
    Created: Sep 16 2020
    Purpose: help on https://swi-prolog.discourse.group/t/swi-prolog-php-html/2937
*/

:- module(quineweb,
          [quine/0,
           getFormula/4,
	   op(700, xfy, <=>),
	   op(600, xfy, =>),
	   op(500, xfy, v),
	   op(400, xfy, &),
	   op(300, fy, ~)
          ]).

eval(A, A) :- var(A), !.
eval(A => B, R) :- !, eval(A, X), eval(B, Y), simp(X => Y, R).
eval(A <=> B, R) :- !, eval(A, X), eval(B, Y), simp(X <=> Y, R).
eval(A v B, R) :- !, eval(A, X), eval(B, Y), simp(X v Y, R).
eval(A & B, R) :- !, eval(A, X), eval(B, Y), simp(X & Y, R).
eval(~A, R) :- !, eval(A, X), simp(~X, R).
eval(A, A).

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

boole :-
    get_wff(_A,_L).

get_wff(A,L) :-
    read_term(A, [variable_names(_N)]),
    time(judge(A,L)),
    last(L,R),
    (
	last(L,1) ->  write('to prove that the formula is a tautology, i.e. that its truth value is always '),
		 write(R),write(' .'),nl,nl,nl,
		 boole
    ;

    last(L,0) -> write('to prove that the formula is not a tautology, i.e. that its truth value can be '),
		 write(R),write(' .'),nl,nl,nl,
		 boole
    ).

% Second prover, Quine prover more practical and more verbose:
% First, write "quine" + Enter.
% Second, write only your formula + Enter.



taut(A, T, N) :-
    eval(A, B),
    write_term(A, [variable_names(N)]),nl,
    write_term(B, [variable_names(N)]),nl,
    write('------------------------------'),nl,
    term_variables(B, L), taut(B, L, T, N),nl.

/*
taut(T, [], T, _) :- !.
taut(A, [B|_], T, N) :- catch((B = 0,taut(A, T, N), throw(T)), T, true),
                        B = 1, write(N),nl,nl,taut(A, S, N), T = S.
*/

taut(T, [], T, _) :- !.
taut(A, [B|_], T, N) :- catch((putSubst(B, 1, N), B = 1, taut(A, T, N), throw(T)), T, true),
                        putSubst(B, 0, N), B = 0,
  taut(A, S, N), T = S.

putSubst(B, V, N) :-
    write_term(B, [variable_names(N)]),
    write(' = '),
    write(V), write(':'), nl, nl.

quine:-
    getFormula(current_input,_A,_N,_T).

getFormula(Stream, A, N, T) :-
    read_term(Stream, A, [variable_names(N)]),
    (  time(taut(A, T, N))
    -> /* here is the missing outer if-then-else */
       (T == 1 ->
          write('to prove that the formula is a tautology.')
       ;
          write('to prove that the formula is an antilogy.')
       )
    ;
      write('to prove that the formula is neither a tautology nor an antilogy.')
    ).