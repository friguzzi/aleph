:- module(test_aleph,
  [test_aleph/0]).
:- use_module(library(plunit)).


test_aleph:-
  run_tests.


:- begin_tests(constraints, []).

:-ensure_loaded(library(examples/constraints)).

test(induce_constraints,[true(Program = 
  [(aleph_false:-human(E),male(E),female(E)),
  (aleph_false:-human(F),female(F),male(F)),
  (aleph_false:-human(G),not(male(G)),not(female(G))),
  (aleph_false:-human(H),not(female(H)),not(male(H)))]
  )]):-
  induce_constraints(Program).

:- end_tests(constraints).
% not working