:- module(goal,
          [ (use)/1,                    % use +File as +Type
            bel/1,                      % Query
            goal/1,                     % Query
            a_goal/1,                   % Query
            goal_a/1,                   % Query

            adopt/1,                    % Goal
            drop/1,                     % Query
            insert/1,                   % +Beliefs
            delete/1,                   % +Beliefs

            beliefs/0,                  % List beliefs
            goals/0,                    % List goals

            step/1,                     % ?Id

            load_knowledge_from_file/2, % +Module, +File
            load_knowledge_from_string/2, % +Module, +String
            load_beliefs_from_file/1,	% +File
            load_beliefs_from_string/1,	% +String
            create_agent/2,             % +Knowledge:list(module),+Options

            op(800,  fx, use),          % use +File as +Type
            op(800,  fx, define),
            op(700, xfx, with),
            op(100,  fx, pre),
            op(100, yfx, post)
          ]).
:- use_module(library(apply)).
:- use_module(library(prolog_code)).
:- use_module(library(readutil)).
:- use_module(library(error)).
:- use_module(library(debug)).
:- use_module(library(listing)).
:- use_module(library(lists)).
:- use_module(library(prolog_wrap), []).

:- thread_local
    agent_module/2,                     % ?Role, ?Module
    goal_id/1,                          % Id
    goal_fact/2.                        % Id, Fact


		 /*******************************
		 *           JAVA API		*
		 *******************************/

%!  load_knowledge_from_file(+Module, +File) is det.
%!  load_knowledge_from_string(+Module, +String) is det.
%
%   Load source String into Module as a  GOAL knowledge entity. A loaded
%   knowledge module is independent from agents, i.e., it may be used by
%   any number (including zero) agents.

load_knowledge_from_file(Module, File) :-
    context_module(Me),
    assertz(Module:term_expansion(In,Out) :- Me:'GOAL_expansion'(In,Out)),
    ensure_loaded(Module:File).

load_knowledge_from_string(Module, String) :-
    context_module(Me),
    assertz(Module:term_expansion(In,Out) :- Me:'GOAL_expansion'(In,Out)),
    setup_call_cleanup(
        open_string(String, In),
        load_files(Module:Module, [if(true), stream(In)]),
        close(In)).

%!  load_beliefs_from_file(+File) is det.
%!  load_beliefs_from_string(+String) is det.
%
%   Load beliefs into the knowledge module Module as beliefs for the
%   current agent.

load_beliefs_from_file(File) :-
    agent_module(knowledge, Module),
    ensure_loaded(Module:File).

load_beliefs_from_string(String) :-
    agent_module(knowledge, Module),
    setup_call_cleanup(
        open_string(String, In),
        load_files(Module:Module, [if(true), stream(In)]),
        close(In)).

%!  create_agent(+Knowledge:list(module), +Options) is det.
%
%   Initialise an agent from a list of   knowledge  modules. If only one
%   module is given, this module  is   associated  with  the agent using
%   agent_module/2. If multiple knowledge modules are  given we create a
%   new module named as below that inherits from the given modules
%
%       'Module1&Module2&...ModuleN'
%
%   If multiple modules define the same  predicate we add _link clauses_
%   to the shared module trying the knowledge modules one-by-one.

create_agent(Knowledge, _Options) :-
    knowledge_module(Knowledge, Module),
    asserta(agent_module(knowledge, Module)).

knowledge_module([Module], Module) :-
    !.
knowledge_module(Modules, Shared) :-
    atomic_list_concat(Modules, '&', Shared),
    (   is_shared_knowledge_module(Shared, Modules)
    ->  true
    ;   with_mutex('GOAL_knowledge', create_knowledge_module(Modules, Shared))
    ).

is_shared_knowledge_module(Shared, Modules) :-
    current_predicate(Shared:'__GOAL_knowledge'/1),
    \+ predicate_property(Shared:'__GOAL_knowledge'(_), imported_from(_)),
    Shared:'__GOAL_knowledge'(Modules).

create_knowledge_module(Modules, Shared) :-
    is_shared_knowledge_module(Shared, Modules),
    !.
create_knowledge_module(Modules, Shared) :-
    forall(member(M, Modules),
           add_import_module(Shared, M, end)),
    import_shared_predicates(Shared, Modules),
    asserta(Shared:'__GOAL_knowledge'(Modules)).

import_shared_predicates(Shared, Modules) :-
    maplist(defines, Modules, Defines),
    append(Defines, AllDefines),
    msort(AllDefines, Sorted),
    from_multiple(Sorted, FromMultiple),
    maplist(multi_import(Shared, Modules), FromMultiple).

defines(Module, PIs) :-
    findall(PI, defines1(Module, PI), PIs0),
    sort(PIs0, PIs).

defines1(Module, PI) :-
    current_predicate(Module:PI),
    pi_head(PI, Head),
    \+ predicate_property(Module:Head, imported_from(_)).

from_multiple([], []).
from_multiple([H,H|T0], [H|T]) :-
    delete_leading(T0, H, T1),
    from_multiple(T1, T).

delete_leading(H, [H|T], L) :-
    !,
    delete_leading(H, T, L).
delete_leading(_, List, List).

multi_import(Shared, Modules, PI) :-
    pi_head(PI, Head),
    forall(( member(M, Modules),
             defines1(M, PI)
           ),
           assertz((Shared:Head :- M:Head))).


		 /*******************************
		 *         DEFINE AGENT		*
		 *******************************/

%!  use(+Spec) is det.
%
%   Spec is of the shape `File as Type`. Loads File as data of Type for
%   the current agent.

use File as knowledge :-
    !,
    load_knowledge_from_file(File, File),
    asserta(agent_module(knowledge, File)).
use File as beliefs :-
    !,
    load_beliefs_from_file(File).
use File as goals :-
    !,
    absolute_file_name(File, Path,
                       [ file_type(prolog),
                         access(read)
                       ]),
    read_file_to_terms(Path, Goals, []),
    maplist(adopt, Goals).
use File as actionspec :-
    !,
    absolute_file_name(File, Path,
                       [ extensions([pl,act2g]),
                         access(read)
                       ]),
    read_file_to_terms(Path, Actions, [module(goal)]),
    asserta(agent_module(actionspec, File)),
    maplist(assert_action, Actions).
use _ as Type :-
    domain_error(goal_file_type, Type).


		 /*******************************
		 *   QUERY BELIEFS AND FACTS	*
		 *******************************/

%!  bel(+Qry)
%
%   True when agent believes Qry to be true.

bel(Qry) :-
    agent_module(knowledge, Module),
    setup_call_cleanup(
        b_setval('GOAL_mode', believe),
        Module:Qry,
        b_setval('GOAL_mode', [])).

%!  goal(+Qry)
%
%   True when Qry is part of one of the agent's goals.

goal(Qry) :-
    goal(Qry, _).
goal(Qry, Id) :-
    agent_module(knowledge, Module),
    goal_id(Id),
    setup_call_cleanup(
        b_setval('GOAL_mode', goal(Id)),
        Module:Qry,
        b_setval('GOAL_mode', [])).

a_goal(Qry) :-
    goal(Qry),
    not(bel(Qry)).

goal_a(Qry) :-
    goal(Qry),
    bel(Qry).


		 /*******************************
		 *        UPDATE ACTIONS	*
		 *******************************/

%!  adopt(+Goal)
%
%   Add a goal to the agent's goals.
%
%   @tbd Goal should not be  believed  and   should  not  be subsumed by
%   another goal.

adopt(Goal) :-
    variant_sha1(Goal, Id),
    comma_list(Goal, Facts),
    maplist(adopt_fact(Id), Facts).

adopt_fact(_Id, Fact) :-
    var(Fact),
    !,
    instantiation_error(Fact).
adopt_fact(_Id, not(Fact)) :-
    !,
    domain_error(positive_literal, not(Fact)).
adopt_fact(Id, Fact) :-
    (   goal_id(Id)
    ->  true
    ;   assertz(goal_id(Id))
    ),
    assertz(goal_fact(Id, Fact)).

%!  drop(+Goal)

drop(Qry) :-
    forall(goal(Qry, Id),
           drop_id(Id)).

drop_id(Id) :-
    retractall(goal_id(Id)),
    retractall(goal_fact(Id, _)).

%!  insert(+Udp)

insert(Udp) :-
    comma_list(Udp, Literals),
    maplist(insert_fact, Literals).

insert_fact(Var) :-
    var(Var),
    !,
    instantiation_error(Var).
insert_fact(not(Qry)) :-
    !,
    agent_module(knowledge, Module),
    belief(Module:Qry),
    drop_facts(Module, Qry).
insert_fact(Qry) :-
    agent_module(knowledge, Module),
    belief(Module:Qry),
    insert_fact(Module, Qry).

%!  delete(+Udp)
%
%   Inverse of insert/1.

delete(Udp) :-
    comma_list(Udp, Literals),
    maplist(delete_fact, Literals).

delete_fact(Var) :-
    var(Var),
    !,
    instantiation_error(Var).
delete_fact(not(Qry)) :-
    !,
    agent_module(knowledge, Module),
    belief(Module:Qry),
    insert_fact(Module, Qry).
delete_fact(Qry) :-
    agent_module(knowledge, Module),
    belief(Module:Qry),
    drop_facts(Module, Qry).

belief(Module:Qry) :-
    predicate_property(Module:Qry, thread_local),
    !.
belief(_:Qry) :-
    type_error(belief, Qry).

insert_fact(Module, Fact) :-
    debug(goal(update), 'Now I believe ~p', [Fact]),
    assertz(Module:Fact).

drop_facts(Module, Fact) :-
    (   debugging(goal(update))
    ->  forall(retract(Module:Fact),
               debug(goal(update), 'I no longer believe ~p', [Fact]))
    ;   retractall(Module:Fact)
    ).


		 /*******************************
		 *            STATE		*
		 *******************************/

beliefs :-
    dynamics(Goals),
    beliefs(Goals).

dynamics(Goals) :-
    agent_module(knowledge, Module),
    findall(Goal, Module:'__GOAL_belief'(Goal), Goals).

beliefs([]).
beliefs([H|T]) :-
    forall(bel(H),
           portray_clause(H)),
    (   T == []
    ->  true
    ;   nl,
        beliefs(T)
    ).

goals :-
    findall(Id, goal_id(Id), Ids),
    list_goals(Ids, 1).

list_goals([], _).
list_goals([H|T], I) :-
    format('% Goal ~w~n', [I]),
    list_goal(H),
    (   T == []
    ->  true
    ;   nl,
        I2 is I + 1,
        list_goals(T, I2)
    ).

list_goal(Id) :-
    findall(Fact, goal_fact(Id,Fact), Facts),
    comma_list(Conj, Facts),
    portray_clause(Conj).


		 /*******************************
		 *           ACTIONSPEC		*
		 *******************************/

%!  assert_action(+Action)
%
%

assert_action(use _Module as knowledge) :-
    !.
assert_action(define Id with pre {Pre} post {Post}) :-
    !,
    agent_module(actionspec, Module),
    assertz(Module:action(Id, Pre, Post)).
assert_action(Action) :-
    domain_error('GOAL_action', Action).

%!  step(?Id) is semidet.

step(Id) :-
    agent_module(actionspec, Module),
    Module:action(Id, Pre, Post),
    bel(Pre),
    !,
    insert(Post),
    !.



		 /*******************************
		 *      KNOWLEDGE REWRITE	*
		 *******************************/

:- public
    bg_call/2,
    'GOAL_expansion'/2.

bg_call(_Wrapped, Head) :-
    b_getval('GOAL_mode', goal(Id)),
    !,
    goal_fact(Id, Head).
bg_call(Wrapped, _Head) :-
    call(Wrapped).

'GOAL_expansion'(begin_of_file, (:- discontiguous('__GOAL_belief'/1))).
'GOAL_expansion'((:- dynamic(Spec)), Clauses) :-
    comma_list(Spec, PIs),
    maplist(state_pred, PIs, Clauses).

state_pred(PI, [ (:- thread_local(PI)),
                 (:- wrap_predicate(Head, 'GOAL', Wrapped,
                                    Me:bg_call(Wrapped, Head))),
                 '__GOAL_belief'(Head)
               ]) :-
    pi_head(PI, Head),
    context_module(Me).
