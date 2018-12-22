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
  [(class(_378, _380):-not(has_covering(_378, hair)), _380=nmammal),  
  (class(_478, _480):-has_covering(_478, hair), _480=mammal)])]):-
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
  [(1,(eastbound(_1272):-has_car(_1272,_1284),closed(_1284))),
  (2,(eastbound(_1230):-has_car(_1230,_1242),load(_1242,triangle,1))),
  (3,(eastbound(_1180):-has_car(_1180,_1192),closed(_1192),wheels(_1192,2))),
  (4,(eastbound(_1130):-has_car(_1130,_1142),closed(_1142),has_car(_1130,_1158))),
  (5,(eastbound(_1076):-has_car(_1076,_1088),load(_1088,triangle,1),has_car(_1076,_1108))),
  (6,(eastbound(_1026):-has_car(_1026,_1038),has_car(_1026,_1050),closed(_1050))),
  (7,(eastbound(_972):-has_car(_972,_984),has_car(_972,_996),load(_996,triangle,1))),
  (8,(eastbound(_924):-has_car(_924,_936),short(_936),closed(_936))),
  (9,(eastbound(_872):-has_car(_872,_884),short(_884),load(_884,triangle,1))),
  (10,(eastbound(_818):-has_car(_818,_830),shape(_830,rectangle),load(_830,triangle,1)))]
  )]):-
  induce_features(F).

:- end_tests(features).

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

:- begin_tests(posonly, []).

:-ensure_loaded(library(examples/posonly)).

test(induce,[true(Program = 
  [class(E,reptile),
  (class(F,reptile):-has_legs(F,4)),
  class(G,fish),
  (class(H,mammal):-has_covering(H,hair)),
  (class(I,bird):-has_covering(I,feathers))]
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

:- begin_tests(recursion, []).

:-ensure_loaded(library(examples/recursion)).

test(induce,[true(Program = 
  [(mem(_1114, _1116):-_1116=[_1132|_1134], mem(_1114, _1134)),  
  (mem(_1246, _1248):-_1248=[_1246|_1260])])]):-
  induce(Program).

:- end_tests(recursion).

:- begin_tests(trains, []).

:-ensure_loaded(library(examples/trains)).

test(induce,[true(F =
  [(eastbound(_834):-has_car(_834, _846), short(_846), closed(_846))]
  )]):-
  induce(F).

:- end_tests(trains).

:- begin_tests(weather, []).

:-ensure_loaded(library(examples/weather)).

test(induce_tree,[true(Program = 
  [(class(_2924, _2926):-not((outlook(_2924, rain), windy(_2924, true))), random(_2926, [0.7142857142857143-play, 0.2857142857142857-dont_play])), 
   (class(_3084, _3086):-outlook(_3084, rain), windy(_3084, true), random(_3086, [0.75-dont_play, 0.25-play]))])]):-
  induce_tree(Program).

:- end_tests(weather).

