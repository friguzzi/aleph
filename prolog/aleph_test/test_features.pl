:- module(test_aleph,
  [test_aleph/0]).
:- use_module(library(plunit)).


test_aleph:-
  run_tests.


:- begin_tests(features, []).

:-ensure_loaded(library(examples/features)).

test(induce_features,[true(F =
  [(eastbound(_1272):-has_car(_1272,_1284),closed(_1284)),
  (eastbound(_1230):-has_car(_1230,_1242),load(_1242,triangle,1)),
  (eastbound(_1180):-has_car(_1180,_1192),closed(_1192),wheels(_1192,2)),
  (eastbound(_1130):-has_car(_1130,_1142),closed(_1142),has_car(_1130,_1158)),
  (eastbound(_1076):-has_car(_1076,_1088),load(_1088,triangle,1),has_car(_1076,_1108)),
  (eastbound(_1026):-has_car(_1026,_1038),has_car(_1026,_1050),closed(_1050)),
  (eastbound(_972):-has_car(_972,_984),has_car(_972,_996),load(_996,triangle,1)),
  (eastbound(_924):-has_car(_924,_936),short(_936),closed(_936)),
  (eastbound(_872):-has_car(_872,_884),short(_884),load(_884,triangle,1)),
  (eastbound(_818):-has_car(_818,_830),shape(_830,rectangle),load(_830,triangle,1))]
  )]):-
  induce_features(F).

:- end_tests(features).
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
