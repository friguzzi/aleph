:- module(test_aleph,
  [test_aleph/0]).
:- use_module(library(plunit)).


test_aleph:-
  run_tests.


:- begin_tests(trains, []).

:-ensure_loaded(library(examples/trains)).

test(induce,[true(F =
  [(eastbound(_834):-has_car(_834, _846), short(_846), closed(_846))]
  )]):-
  induce(F).

:- end_tests(trains).

