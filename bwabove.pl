% Declaration of the on/2 predicate.
:- dynamic on/2.

above(X,Y) :- on(X,Y).
above(X,Y) :- on(X,Z), above(Z,Y).
