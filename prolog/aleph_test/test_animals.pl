:- module(test_aleph,
  [test_aleph/0]).
:- use_module(library(plunit)).


test_aleph:-
  run_tests.


:- begin_tests(animals, []).

:-ensure_loaded(library(examples/animals)).

test(induce_tree,[true(Program = 
  [(class(_378, _380):-not(has_covering(_378, hair)), _380=nmammal),  
  (class(_478, _480):-has_covering(_478, hair), _480=mammal)])]):-
  induce_tree(Program).

:- end_tests(animals).
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
