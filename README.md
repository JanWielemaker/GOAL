# GOAL in Prolog

This repo provides a (very) partial implementation of the
[GOAL agent programming
language](https://en.wikipedia.org/wiki/GOAL_agent_programming_language)

The purpose of this implementation is to illustrate how agent state can
be handled using SWI-Prolog modules and thread-local storage.

## Running

Run as

    swipl demo.pl

Some useful goals (see goal.pl for more):

| Command | Description |
|---|---|
| ?- beliefs. | List all beliefs   |
| ?- goals.   | List all goals     |
| ?- debug(goal(update)). | When stepping, show modifying beliefs |
| ?- step(S). | Try to make a step |

