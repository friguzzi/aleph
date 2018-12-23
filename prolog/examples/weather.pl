/** <examples>
?- induce_tree(Program).
*/

:-use_module(library(aleph)).
:- aleph.
:- if(current_predicate(use_rendering/1)).
:- use_rendering(prolog).
:- endif.
:- modeh(1,class(+day,-class)).
:- modeb(1,outlook(+day,#outlook)).
:- modeb(1,temp(+day,-temp)).
:- modeb(1,humidity(+day,-humidity)).
:- modeb(1,windy(+day,#windy)).
:- modeb(*,lteq(+temp,#temp)).
:- modeb(*,lteq(+humidity,#humidity)).

:- determination(class/2,outlook/2).
:- determination(class/2,temp/2).
:- determination(class/2,humidity/2).
:- determination(class/2,windy/2).
:- determination(class/2,lteq/2).

% :- aleph_set(tree_type,classification).
:- aleph_set(tree_type,class_probability).
:- aleph_set(classes,[play,dont_play]).
:- aleph_set(minpos,2).	% minimum examples in leaf for splitting
:- aleph_set(clauselength,5).
:- aleph_set(lookahead,2).	% to allow lookahead to lteq/2
:- aleph_set(prune_tree,true).
:- aleph_set(confidence,0.25).% pruning conf parameter used by C4.5
:- aleph_set(evalfn,entropy).
% :- aleph_set(evalfn,gini).
:- aleph_set(dependent,2).	% second arg of class/2 is to predicted

:-begin_bg.

% type predicates
outlook(sunny).
outlook(overcast).
outlook(rain).

windy(true).
windy(false).

temp(64).
temp(65).
temp(68).
temp(69).
temp(70).
temp(71).
temp(75).
temp(80).
temp(81).
temp(83).
temp(85).

humidity(65).
humidity(70).
humidity(75).
humidity(80).
humidity(85).
humidity(86).
humidity(90).
humidity(95).
humidity(96).


lteq(X,Y):-
	var(Y), !,
	X = Y.
lteq(X,Y):-
	number(X), number(Y),
	X =< Y.

outlook(Day,Outlook):-
	table(Day,Outlook,_,_,_).
temp(Day,Temp):-
	table(Day,_,Temp,_,_).
humidity(Day,Humidity):-
	table(Day,_,_,Humidity,_).
windy(Day,Windy):-
	table(Day,_,_,_,Windy).

table(d1,sunny,75,70,true).
table(d2,sunny,80,90,true).
table(d3,sunny,85,85,false).
table(d4,sunny,72,95,false).
table(d5,sunny,69,70,false).
table(d6,overcast,72,90,true).
table(d7,overcast,83,86,false).
table(d8,overcast,64,65,true).
table(d9,overcast,81,75,false).
table(d10,rain,71,80,true).
table(d11,rain,65,70,true).
table(d12,rain,75,80,false).
table(d13,rain,68,80,false).
table(d14,rain,70,96,false).

:-end_bg.
:-begin_in_pos.
class(d1,play).
class(d2,dont_play).
class(d3,dont_play).
class(d4,dont_play).
class(d5,play).
class(d6,play).
class(d7,play).
class(d8,play).
class(d9,play).
class(d10,dont_play).
class(d11,dont_play).
class(d12,play).
class(d13,play).
class(d14,play).
:-end_in_pos.

:-begin_in_neg.
:-end_in_neg.
:-aleph_read_all.
