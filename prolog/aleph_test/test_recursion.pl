:- module(test_aleph,
  [test_aleph/0]).
:- use_module(library(plunit)).


test_aleph:-
  run_tests.


:- begin_tests(recursion, []).

:-ensure_loaded(library(examples/recursion)).

test(induce,[true(Program = 
  [(mem(_1114, _1116):-_1116=[_1132|_1134], mem(_1114, _1134)),  
  (mem(_1246, _1248):-_1248=[_1246|_1260])])]):-
  induce(Program).

:- end_tests(recursion).
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
