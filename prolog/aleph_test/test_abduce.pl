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

