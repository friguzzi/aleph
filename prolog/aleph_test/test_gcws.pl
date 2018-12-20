:- module(test_aleph,
  [test_aleph/0]).
:- use_module(library(plunit)).


test_aleph:-
  run_tests.


:- begin_tests(gcws, []).

:-ensure_loaded(library(examples/gcws)).

test(induce):-
  open('gwcs_in.txt',read,S),
  set_input(S),!,
  rdhyp,
  set_input(user_input),
  sphyp,
  show(gcws),
  close(S).

:- end_tests(gcws).
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
