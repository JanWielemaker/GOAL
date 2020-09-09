:- module(goal,
          [ (use)/1,                    % use +File as +Type
            bel/1,                      % Query
            goal/1,                     % Query

            op(800, fx, use)
          ]).

:- thread_local
    knowledge/1.

use File as knowledge :-
    !,
    ensure_loaded(File:File),
    asserta(knowledge(File)),
    thread_local(File:goal/1).
use File as beliefs :-
    !,
    knowledge(Module),
    ensure_loaded(Module:File).
use File as goals :-
    !,
    read_file_to_terms(File, Goals, []),
    knowledge(Module),
    maplist(assert_goal(Module), Goals).

assert_goal(Module, Goal) :-
    assertz(Module:goal(Goal)).

bel(Qry) :-
    knowledge(Module),
    call(Module:Qry).

goal(Qry) :-
    knowledge(Module),
    call(Module:Qry).
