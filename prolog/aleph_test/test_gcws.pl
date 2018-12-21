:- module(test_aleph,
  [test_aleph/0]).
:- use_module(library(plunit)).


test_aleph:-
  run_tests.


:- begin_tests(gcws, []).

:-ensure_loaded(library(examples/gcws)).

test(induce):-
  open('gcws_in.txt',read,S),
  set_input(S),!,
  rdhyp,
  set_input(user_input),
  sphyp,
  show(gcws),
  close(S).

:- end_tests(gcws).
