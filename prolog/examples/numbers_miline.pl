% Simple illustration of the use of multi-instance lazy evaluation
%       a predicate to construct a line is called during
%       the search to obtain a linear equation
% For realistic examples a proper regression predicate will be needed
%	(usually better to implement this in C, and call it from Prolog)
% To run do the following:
%       a. Load Aleph
%       b. read_all(line).
%       c. sat(1).
%       d. reduce.
/** <examples>
?- sat(1),reduce(A).
*/
:- use_module(library(aleph)).
:- if(current_predicate(use_rendering/1)).
:- use_rendering(prolog).
:- endif.
:- aleph.


:- mode(1,p(+bag,+indep,+dep)).
:- mode(1,lin_regress1(+bag,+dep,+indep,#number,#number,#number)).

:- determination(p/3,lin_regress1/6).

:- lazy_evaluate(lin_regress1/6).

% this predicate does not need substitutions from negative examples

:- positive_only(lin_regress1/6).

:- aleph_set(portray_literals,true).

aleph_portray(p(Bag,A,B)):-
	write(p(Bag,A,B)).
aleph_portray(lin_regress1(B,Y,X,M,C,E)):-
	write(' exists '), write(X),
	write(' in bag '), write(B), write(' such that '),
	write(Y), write(' is '),
	write(M), write(' * '),
	write(X), write(' + '),
	write(C), write(' +/- '),
	write(E).


:-begin_bg.


nlist([]).
nlist([_|_]).

% definition for use during normal evaluation
lin_regress1(_,Y,X,M,C,Error):-
	number(X), number(Y),
	nonvar(M), nonvar(C), nonvar(Error), !,
	Y1 is M*X + C,
	Diff is (Y - Y1),
	(Diff > 0 -> E1 = Diff; E1 is -1*Diff),
	E1 =< Error.

% definition for use during lazy evaluation
lin_regress1(B,Y,X,M,C,Error):-
	nlist(B), nlist(X), nlist(Y),
	var(M), var(C), !,
	em_regress(B,Y,X,M,C,Error).

% otherwise: for bottom clause
lin_regress1(_,Y,X,0.0,Y,0.0):-
	X \= Y.


% Approximate EM algorithm for estimating best fitting line through instances
%	finds best line after 10 random restarts
em_regress([Bags|_],[YVals|_],[XVals|_],M,C,Error):-
 	Inf is inf,
	em_regress(10,Bags,YVals,XVals,Inf,Inf,Inf,M,C,Error).

em_regress(0,_,_,_,M,C,E,M,C,E):- !.
em_regress(N,Bags,YVals,XVals,_,_,E0,M,C,E):-
	random_vals([Mr,Cr]),
	em_regress(Bags,YVals,XVals,Mr,Cr,E0,M1,C1,E1),
	(E1 > 0.0 ->
		N1 is N - 1,
		em_regress(N1,Bags,YVals,XVals,M1,C1,E1,M,C,E);
		M = M1,
		C = C1,
		E = E1).
	
em_regress(Bags,YVals,XVals,M0,C0,E0,M,C,E):-
	find_new_instances(Bags,YVals,XVals,M0,C0,0.0,YVals1,XVals1,E1),
	E1 < E0, !,
	(E1 > 0.0 ->
		l_regress1(YVals1,XVals1,M1,C1),
		em_regress(Bags,YVals,XVals,M1,C1,E1,M,C,E);
		M = M0,
		C = C0,
		E = E1).
em_regress(_,_,_,M,C,E,M,C,E).


l_regress1(YVals,XVals,M,C):-
	YVals = [Y1,Y2|_],
	XVals = [X1,X2|_],
	(X2=:=X1->
		M is (Y2-Y1)*1e10
	;
		M is (Y2-Y1)/(X2-X1)
	),
	C is Y1 - M*X1.

find_new_instances(Bags,YVals,XVals,M,C,E,YVals1,XVals1,E1):-
	get_closest_instances(Bags,YVals,XVals,M,C,E,[],E1,Instances),
	get_bag_instances(Instances,YVals1,XVals1).

get_closest_instances([],_,_,_,_,E,I,E,I).
get_closest_instances([Bag|Bags],[Y|YVals],[X|XVals],M0,C0,E0,I0,E,I):-
	Error is (Y - M0*X - C0)^2,
	(aleph_delete(Bag-[OldE,_],I0,Left) ->
		(Error < OldE ->
			I1 = [Bag-[Error,[Y,X]]|Left],
			E1 is E0 + Error - OldE;
			I1 = I0,
			E1 = E0);
		I1 = [Bag-[Error,[Y,X]]|I0],
		E1 is E0 + Error),
	get_closest_instances(Bags,YVals,XVals,M0,C0,E1,I1,E,I).

get_bag_instances([],[],[]).
get_bag_instances([_-[_,[Y,X]]|Instances],[Y|YVals],[X|XVals]):-
	get_bag_instances(Instances,YVals,XVals).

random_vals([]).
random_vals([A|B]):-
	aleph_random(A),
	random_vals(B).

:-end_bg.
:-begin_in_pos.
p(b1,1,2).
p(b1,1,3).
p(b1,1,4).
p(b2,2,4).
p(b3,3,6).
p(b4,4,8).
:-end_in_pos.
:-begin_in_neg.
p(b,1,0).
p(b,2,5).
p(b,3,9). 

:-end_in_neg.

:-aleph_read_all.