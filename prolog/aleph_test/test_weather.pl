:- module(test_aleph,
  [test_aleph/0]).
:- use_module(library(plunit)).


test_aleph:-
  run_tests.


:- begin_tests(weather, []).

:-ensure_loaded(library(examples/weather)).

test(induce_tree,[true(Program = 
  [(class(_2924, _2926):-not((outlook(_2924, rain), windy(_2924, true))), random(_2926, [0.7142857142857143-play, 0.2857142857142857-dont_play])), 
   (class(_3084, _3086):-outlook(_3084, rain), windy(_3084, true), random(_3086, [0.75-dont_play, 0.25-play]))])]):-
  induce_tree(Program).

:- end_tests(weather).
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
