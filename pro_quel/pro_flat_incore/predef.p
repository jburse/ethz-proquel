
:- pred (goal:-goal).
:- pred (goal,goal).
:- pred (goal;goal).
:- pred (\+ goal).
:- pred (goal->goal).
:- pred var(_).
:- pred true.
:- pred repeat.
:- pred fail.
:- pred !.

:- pred clause(goal,goal).
:- pred assertz(goal).
:- pred asserta(goal).
:- pred assert(goal).
:- pred retract(goal).

:- type fun = [str|mix].
:- type mix = [A|mix] + [].
:- pred A=..fun.
:- pred length(mix,int).
:- pred length(*A,int).
:- pred findall(A,goal,*A).
:- pred 'C'(*A,A,*A).

:- pred atom_chars(str,*int).
:- pred number_chars(int,*int).
:- pred number_chars(float,*int).
:- pred name(int,*int).
:- pred name(str,*int).
:- pred name(float,*int).
:- pred foreign_file(str,*str).
:- pred load_foreign_files(*str,*str).

:- pred nl.
:- pred get0(int).
:- pred tab(int).
:- pred format(*int,A).
:- pred write(A).

:- pred A = A.
:- pred A == A.
:- pred A \== A.
:- pred A @< A.
:- pred A @> A.
:- pred A @>= A.
:- pred A @=< A.

:- pred int is int.
:- pred int < int.
:- pred int > int.
:- pred int >= int.
:- pred int =< int.
:- pred int =:= int.
:- pred int =\= int.

:- type *A = [] + [A|*A].

:- type int = int - int.
:- type int == int + int.
:- type int = int * int.
:- type int = -int.
:- type int = int // int.
:- type int = int mod int.

:- pred float is float.
:- pred float < float.
:- pred float > float.
:- pred float >= float.
:- pred float =< float.
:- pred float =:= float.
:- pred float =\= float.

:- type float = float - float.
:- type float == float + float.
:- type float = float * float.
:- type float = -float.
:- type float = float / float.

:- type int = integer(float).
:- type float = float(int).
