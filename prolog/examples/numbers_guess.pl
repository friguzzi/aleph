% Simple illustration of the use multiple-recall to guess
% 	constants
% To run do the following:
%	a. Load Aleph
%	b. read_all(ineq).
%	c. sat(1).
%	d. reduce.
/** <examples>
?- sat(1),reduce(A).
*/
:- use_module(library(aleph)).
:- if(current_predicate(use_rendering/1)).
:- use_rendering(prolog).
:- endif.
:- aleph.

:- modeh(1,p(+number)).
:- modeb(*,gteq(+number,#number)).

:- determination(p/1,gteq/2).

:-begin_bg.
% definition to use during normal evaluation
gteq(X,Value):-
	number(X), number(Value), !,
        X >= Value.
% definition to use during construction of bottom clause
gteq(X,Y):-
	number(X), var(Y), !,
	guess(X,Y).

guess(X,Y):- 
	Y is X.
guess(X,Y):- 
	Y is 2*X.
guess(X,Y):- 
	Y is 3*X.

:-end_bg.
:-begin_in_pos.

p(3).
p(5).
p(8).
p(9).
p(10).

:-end_in_pos.
:-begin_in_neg.
p(1).
p(2).
p(4).
p(6).

:-end_in_neg.

:-aleph_read_all.