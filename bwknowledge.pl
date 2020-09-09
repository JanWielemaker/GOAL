% Declaration of the on/2 predicate.
:- dynamic on/2.
% only blocks can be on top of another object.
block(X) :- on(X, _).
% the table is always clear.
clear(table).
% a block is clear if nothing is on top of it.
clear(X) :- block(X), not( on(_, X) ).
% the tower predicate holds for any stack of blocks that sits on the table.
tower([X]) :- on(X, table).
tower([X,Y| T]) :- on(X, Y), tower([Y|T]).
