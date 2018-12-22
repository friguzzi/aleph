:- module(test_aleph,
  [test_aleph/0]).
:- use_module(library(plunit)).


test_aleph:-
  run_tests.


:- begin_tests(posonly, []).

:-ensure_loaded(library(examples/posonly)).

test(induce,[true(Program = 
 [class(_,reptile),
 (class(F,reptile):-has_legs(F,4)),
 (class(G,fish):-has_covering(G,none)),
 (class(H,mammal):-has_covering(H,hair)),
 (class(I,bird):-has_covering(I,feathers))]
 )]):-
  set_random(seed(111)),
  induce(Program).

:- end_tests(posonly).

% not working