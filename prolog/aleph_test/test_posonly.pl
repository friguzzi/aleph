:- module(test_aleph,
  [test_aleph/0]).
:- use_module(library(plunit)).


test_aleph:-
  run_tests.


:- begin_tests(posonly, []).

:-ensure_loaded(library(examples/posonly)).

test(induce,[true(Program = 
  [(class(_1384, reptile):-has_covering(_1384, scales)),  
  (class(_1534, fish):-has_gills(_1534)),  
  (class(_1670, mammal):-has_covering(_1670, hair)),  
  (class(_1820, bird):-has_covering(_1820, feathers))])]):-
  induce(Program).

:- end_tests(posonly).

