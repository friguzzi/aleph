:- module(test_aleph,
  [test_aleph/0]).
:- use_module(library(plunit)).


test_aleph:-
  run_tests.

:- begin_tests(abduce, []).

:-ensure_loaded(library(examples/abduce)).

test(induce,[true(Program = 
  [(parent(_658, _660):-father(_658, _660)), 
  (parent(_682, _684):-mother(_682, _684)), 
  parent(dad(dad(bob)), mum(bob))])]):-
  induce(Program).

:- end_tests(abduce).

:- begin_tests(animals, []).

:-ensure_loaded(library(examples/animals)).

test(induce_tree,[true(Program = 
  [  (class(_478, _480):-has_covering(_478, hair), _480=mammal),
  (class(_378, _380):-not(has_covering(_378, hair)), _380=nmammal)])]):-
  induce_tree(Program).

:- end_tests(animals).

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



:- begin_tests(posonly, []).

:-ensure_loaded(library(examples/posonly)).

test(induce,[true(Program = 
    [class(_F,reptile),(class(G,reptile):-has_legs(G,4)),(class(H,fish):-has_covering(H,none)),(class(I,mammal):-has_covering(I,hair)),(class(J,bird):-has_covering(J,feathers))]
)]

%  [class(_,reptile),
%  (class(F,reptile):-has_legs(F,4)),
%  (class(G,fish):-has_covering(G,none)),
%  (class(H,mammal):-has_covering(H,hair)),
%  (class(I,bird):-has_covering(I,feathers))]
%  )]
 ):-
  set_random(seed(111)),
  induce(Program).

:- end_tests(posonly).

:- begin_tests(good, []).

:-ensure_loaded(library(examples/good)).

test(good,[true(C = 
  [(eastbound(A) :-
   has_car(A,B), closed(B), load(B,triangle,1)),
  (eastbound(A) :-
   has_car(A,B), short(B), closed(B))])
  ]):-
  sat(1),reduce,good_clauses(C).

:- end_tests(good).

:- begin_tests(modes, []).

:-ensure_loaded(library(examples/modes)).

test(induce_modes,[true(M = 
  [mode(*,eastbound(+type1)),
  mode(*,has_car(+type1,-type13)),
  mode(*,short(+type13)),mode(*,closed(+type13)),mode(*,long(+type13)),mode(*,open_car(+type13)),mode(*,double(+type13)),mode(*,jagged(+type13)),mode(*,load(+type13,-type15,-type16)),mode(*,wheels(+type13,+type16)),mode(*,shape(+type13,-type9)),mode(1,+type1= #type1),mode(1,+type13= #type13),mode(1,+type15= #type15),mode(1,+type16= #type16),mode(1,+type9= #type9),mode(1,+type9= +type15),mode(1,not(short(+type13))),mode(1,not(closed(+type13))),mode(1,not(long(+type13))),mode(1,not(open_car(+type13))),mode(1,not(double(+type13))),mode(1,not(jagged(+type13))),mode(1,not(wheels(+type13,+type16)))]

  
  )]):-
  induce_modes(M).

:- end_tests(modes).

:- begin_tests(recursion, []).

:-ensure_loaded(library(examples/recursion)).

test(induce,[true(Program = 
  [(mem(_1114, _1116):-_1116=[_1132|_1134], mem(_1114, _1134)),  
  (mem(_1246, _1248):-_1248=[_1246|_1260])])]):-
  induce(Program).

:- end_tests(recursion).

:- begin_tests(refine, []).

:-ensure_loaded(library(examples/refine)).

test(induce,[true(C = 
  (eastbound(_4810):-has_car(_4810, _4822), short(_4822), closed(_4822)))]):-
  sat(1),reduce(C).

:- end_tests(refine).

:- begin_tests(train, []).

:-ensure_loaded(library(examples/train)).

test(induce,[true(F =
  [(eastbound(_834):-has_car(_834, _846), short(_846), closed(_846))]
  )]):-
  induce(F).

:- end_tests(train).

:- begin_tests(weather, []).

:-ensure_loaded(library(examples/weather)).

test(induce_tree,[true(Program = 
  [   (class(_3084, _3086):-outlook(_3084, rain), windy(_3084, true), random(_3086, [0.75-dont_play, 0.25-play])),
  (class(_2924, _2926):-not((outlook(_2924, rain), windy(_2924, true))), random(_2926, [0.7142857142857143-play, 0.2857142857142857-dont_play]))])]):-
  induce_tree(Program).

:- end_tests(weather).

:- begin_tests(wedge, []).

:-ensure_loaded(library(examples/wedge)).

test(induce_tree,[true(Program = 
[ (f(_4682, _4684):-lteq(_4682, 0.0), predict(_4682, _4684, [1.0, 1.0, 0.0])),
(f(_4526, _4528):-not(lteq(_4526, 0.0)), predict(_4526, _4528, [-1.0, 1.0, 0.0]))]
     )]):-
  induce_tree(Program).

:- end_tests(wedge).

:- begin_tests(interactive_mem, []).

:-ensure_loaded(library(examples/interactive_mem)).

test(induce_incremental,[true(Program = 
[(mem(_316, _318):-_318=[_316|_330]),(mem(_196, _198):-_198=[_214|_216], mem(_196, _216))]
     )]):-
  tmp_file_stream(utf8,File,Stream),
  write(Stream,'
mem(1,[1]).
overgeneral.
show(constraints).
none.
ok.
ok.
none.
mem(1,[2,1]).
because(overgeneral,not(mem(1,[2,3]))).
none.
ok.
ok.
none.
none.
'),
  close(Stream),
  open(File,read,S),
  set_input(S),!,
  induce_incremental(Program),
  close(S),
  delete_file(File).

:- end_tests(interactive_mem).

:- begin_tests(interactive_animals, []).

:-ensure_loaded(library(examples/interactive_animals)).

test(induce_tree,[true(Program = 
[  (class(_514, _516):-has_covering(_514, hair), _516=mammal),
(class(_402, _404):-not(has_covering(_402, hair)), _404=nmammal)
])]):-
  tmp_file_stream(utf8,File,Stream),
  write(Stream,'1.'),
  close(Stream),
  open(File,read,S),
  set_input(S),!,
  induce_tree(Program),
  close(S),
  delete_file(File).

:- end_tests(interactive_animals).

:- begin_tests(numbers_guess, []).

:-ensure_loaded(library(examples/numbers_guess)).

test(reduce,[true(A = (p(_3438):-gteq(_3438, 9)))]):-
  sat(1),
  reduce(A).

:- end_tests(numbers_guess).

:- begin_tests(numbers_ineq, []).

:-ensure_loaded(library(examples/numbers_ineq)).

test(reduce,[true(A = (p(_6732):-gteq(_6732, 8)))]):-
  sat(1),
  reduce(A).

:- end_tests(numbers_ineq).

:- begin_tests(numbers_line, []).

:-ensure_loaded(library(examples/numbers_line)).

test(reduce,[true(A = (p(_6186, _6188):-lin_regress1(_6188, _6186, 2, 0, 0.0)))]):-
  sat(1),
  reduce(A).

:- end_tests(numbers_line).

:- begin_tests(numbers_miline, []).

:-ensure_loaded(library(examples/numbers_miline)).

test(reduce,[true(A = (p(_8242, _8244, _8246):-lin_regress1(_8242, _8246, _8244, 2, 0, 0.0)))]):-
  sat(1),
  reduce(A).

:- end_tests(numbers_miline).

:- begin_tests(portray_train, []).

:-ensure_loaded(library(examples/portray_train)).

test(induce,[true(F =
  [(eastbound(_834):-has_car(_834, _846), short(_846), closed(_846))]
  )]):-
  induce(F).

:- end_tests(portray_train).