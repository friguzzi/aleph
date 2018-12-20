:- module(test_aleph,
  [test_aleph/0]).
:- use_module(library(plunit)).


test_aleph:-
  run_tests.


:- begin_tests(abduce, []).

:-ensure_loaded(library(examples/abduce)).

test(induce,[true(Program = [(parent(_658, _660):-father(_658, _660)), (parent(_682, _684):-mother(_682, _684)), parent(dad(dad(bob)), mum(bob))])]):-
  induce(Program).

:- end_tests(abduce).
/*
:- begin_tests(animals, []).

:-ensure_loaded(library(examples/animals)).

test(induce_tree):-
  induce_tree.

:- end_tests(animals).

:- begin_tests(constraints, []).

:-ensure_loaded(library(examples/constraints)).

test(induce_constraints):-
  induce_constraints(Constraints).

:- end_tests(constraints).
*/
