:- module(test_aleph,
  [test_aleph/0]).
:- use_module(library(plunit)).


test_aleph:-
  run_tests.


:- begin_tests(gcws, []).

:-ensure_loaded(library(examples/gcws)).

test(induce):-
  tmp_file_stream(utf8,File,Stream),
  write(Stream,'normal(A).'),
  close(Stream),
  open(File,read,S),
  set_input(S),!,
  rdhyp,
  set_input(user_input),
  sphyp,
  show(gcws),
  close(S),
  delete_file(File).

:- end_tests(gcws).
