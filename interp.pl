:- module(goal,
          [ (use)/1,                    % use +File as +Type
            bel/1,                      % Query
            goal/1,                     % Query

            op(800, fx, use)
          ]).
:- use_module(library(apply)).
:- use_module(library(prolog_code)).
:- use_module(library(readutil)).

:- thread_local
    knowledge/1.

use File as knowledge :-
    !,
    context_module(Me),
    assertz(File:term_expansion(In,Out) :- Me:'GOAL_expansion'(In,Out)),
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
    setup_call_cleanup(
        b_setval('GOAL_mode', goal),
        Module:Qry,
        b_setval('GOAL_mode', [])).

:- public
    bg_call/2,
    'GOAL_expansion'/2.

bg_call(_Wrapped, Head) :-
    b_getval('GOAL_mode', goal),
    !,
    knowledge(Module),
    Module:goal(Goal),
    comma_list(Goal, Facts),
    member(Head, Facts).
bg_call(Wrapped, _Head) :-
    call(Wrapped).

'GOAL_expansion'((:- dynamic(Spec)), Clauses) :-
    comma_list(Spec, PIs),
    maplist(state_pred, PIs, Clauses).

state_pred(PI, [ (:- thread_local(PI)),
                 (:- wrap_predicate(Head, 'GOAL', Wrapped,
                                    Me:bg_call(Wrapped, Head)))
               ]) :-
    pi_head(PI, Head),
    context_module(Me).
