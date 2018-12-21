% Simple illustration of interactive construction of tree-based models
% within Aleph
% To run do the following:
%       a. Load Aleph
%       b. read_all(animals).
%       c. induce_tree.

/** <examples>
?- induce_tree.
*/

:-use_module(library(aleph)).
:- if(current_predicate(use_rendering/1)).
:- use_rendering(prolog).
:- endif.
:- aleph.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% specify tree type

:- set(tree_type,classification).
:- set(classes,[mammal,nmammal]).
:- set(minpos,2).       % minimum examples in leaf for splitting
:- set(prune_tree,true).
:- set(confidence,0.25).% pruning conf parameter used by C4.5
:- set(evalfn,entropy).
:- set(dependent,2).	% second argument of class/2 is the one to predict


%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Mode declarations
:- set(lookahead,2).	% to allow lookahead to lteq/2

:- modeh(1,class(+animal,-class)).
:- modeb(1,has_gills(+animal)).
:- modeb(1,has_covering(+animal,#covering)).
:- modeb(1,has_legs(+animal,#integer)).
:- modeb(1,homeothermic(+animal)).
:- modeb(1,has_eggs(+animal)).
:- modeb(1,not(has_gills(+animal))).
:- modeb(1,nhas_gills(+animal)).
:- modeb(*,habitat(+animal,#habitat)).
:- modeb(1,has_milk(+animal)).

:-determination(class/2,has_gills/1).
:-determination(class/2,has_covering/2).
:-determination(class/2,has_legs/2).
:-determination(class/2,momeotermic/1).
:-determination(class/2,has_egss/1).
:-determination(class/2,nhas_gills/1).
:-determination(class/2,habitat/2).
:-determination(class/2,has_milk/1).

:-begin_bg.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Types

animal(dog).  animal(dolphin).  animal(platypus).  animal(bat).
animal(trout).  animal(herring).  animal(shark). animal(eel).
animal(lizard).  animal(crocodile).  animal(t_rex).  animal(turtle).
animal(snake).  animal(eagle).  animal(ostrich).  animal(penguin).
animal(cat). animal(dragon).  animal(girl).  animal(boy).


class(mammal).  class(fish).  class(reptile).  class(bird).

covering(hair).  covering(none).  covering(scales).  covering(feathers).

habitat(land).  habitat(water).  habitat(air).  habitat(caves).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Background knowledge

has_covering(dog,hair).
has_covering(dolphin,none).
has_covering(platypus,hair).
has_covering(bat,hair).
has_covering(trout,scales).
has_covering(herring,scales).
has_covering(shark,none).
has_covering(eel,none).
has_covering(lizard,scales).
has_covering(crocodile,scales).
has_covering(t_rex,scales).
has_covering(snake,scales).
has_covering(turtle,scales).
has_covering(eagle,feathers).
has_covering(ostrich,feathers).
has_covering(penguin,feathers).

has_legs(dog,4).
has_legs(dolphin,0).
has_legs(platypus,2).
has_legs(bat,2).
has_legs(trout,0).
has_legs(herring,0).
has_legs(shark,0).
has_legs(eel,0).
has_legs(lizard,4).
has_legs(crocodile,4).
has_legs(t_rex,4).
has_legs(snake,0).
has_legs(turtle,4).
has_legs(eagle,2).
has_legs(ostrich,2).
has_legs(penguin,2).

has_milk(dog).
has_milk(cat).
has_milk(dolphin).
has_milk(bat).
has_milk(platypus).


homeothermic(dog).
homeothermic(cat).
homeothermic(dolphin).
homeothermic(platypus).
homeothermic(bat).
homeothermic(eagle).
homeothermic(ostrich).
homeothermic(penguin).


habitat(dog,land).
habitat(dolphin,water).
habitat(platypus,water).
habitat(bat,air).
habitat(bat,caves).
habitat(trout,water).
habitat(herring,water).
habitat(shark,water).
habitat(eel,water).
habitat(lizard,land).
habitat(crocodile,water).
habitat(crocodile,land).
habitat(t_rex,land).
habitat(snake,land).
habitat(turtle,water).
habitat(eagle,air).
habitat(eagle,land).
habitat(ostrich,land).
habitat(penguin,water).

has_eggs(platypus).
has_eggs(trout).
has_eggs(herring).
has_eggs(shark).
has_eggs(eel).
has_eggs(lizard).
has_eggs(crocodile).
has_eggs(t_rex).
has_eggs(snake).
has_eggs(turtle).
has_eggs(eagle).
has_eggs(ostrich).
has_eggs(penguin).

has_gills(trout).
has_gills(herring).
has_gills(shark).
has_gills(eel).

nhas_gills(X) :- animal(X), not(has_gills(X)).

:-end_bg.
:-begin_in_pos.
class(bat,mammal).
class(dog,mammal).
class(bat,mammal).
class(bat,mammal).
class(dog,mammal).
class(platypus,mammal).


class(eagle,nmammal).
class(eagle,nmammal).
class(ostrich,nmammal).
class(shark,nmammal).
class(crocodile,nmammal).
class(shark,nmammal).
class(penguin,nmammal).
class(shark,nmammal).
class(crocodile,nmammal).
class(crocodile,nmammal).
class(shark,nmammal).
class(snake,nmammal).
class(t_rex,nmammal).
class(crocodile,nmammal).
:-end_in_pos.

:-begin_in_neg.

:-end_in_neg.

:-aleph_read_all.
