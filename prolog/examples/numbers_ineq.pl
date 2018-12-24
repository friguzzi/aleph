% Simple illustration of the use of lazy evaluation
% 	a FOIL-like inequality predicate is called during
% 	the search to obtain a constant that does not appear in
%	the bottom clause
% To run do the following:
%	a. Load Aleph
%	b. read_all(ineq).
%	c. sat(1).
%	d. reduce.

:- use_module(library(aleph)).
:- if(current_predicate(use_rendering/1)).
:- use_rendering(prolog).
:- endif.
:- aleph.

:- modeh(1,p(+number)).
:- modeb(1,gteq(+number,#number)).

:- lazy_evaluate(gteq/2).

:- determination(p/1,gteq/2).


:-begin_bg.
% definition to use during lazy evaluation
lteq([P,N],Value):-
        !,
        find_cutoff(lte,P,N,Value).
% definition to use during normal evaluation
lteq(X,Value):-
	number(X), number(Value), !,
        X =< Value.
% definition to use during construction of bottom clause
lteq(X,X).
 
% definition to use during lazy evaluation
gteq([P,N],Value):-
        !,
        find_cutoff(gte,P,N,Value).
% definition to use during normal evaluation
gteq(X,Value):-
	number(X), number(Value), !,
        X >= Value.
% definition to use during construction of bottom clause
gteq(X,X).


find_cutoff(gte,[],N,Value):-
	!,
	list_max(N,Value).
find_cutoff(gte,P,[],Value):-
	!,
	list_min(P,Value).
find_cutoff(lte,[],N,Value):-
	!,
	list_min(N,Value).
find_cutoff(lte,P,[],Value):-
	!,
	list_max(P,Value).
find_cutoff(C,P,N,Value):-
        sort(P,Ps), sort(N,Ns),         	% Ps, Ns are in ascending order
        length(P,P0), length(N,N0),
        PriorFrac is P0/(P0+N0),
        PriorBits is -log(PriorFrac)/log(2),    % bits required to encode a prior pos
        find_loss(C,Ps,P,N,P0,N0,PriorBits,PLosses),   % losses made by each pos cutoff
        find_loss(C,Ns,P,N,P0,N0,PriorBits,NLosses),   % losses made by each neg cutoff
	keysort(PLosses,[PL1-PV1|_]),
	keysort(NLosses,[NL1-NV1|_]),
	(NL1 < PL1 -> Value is NV1 ; Value is PV1).


find_loss(_,[],_,_,_,_,_,[]).
find_loss(C,[X|T],Ps,Ns,P0,N0,PriorBits,[Loss-X|T1]):-
	find_covered(C,X,Ps,P0,P1),
	find_covered(C,X,Ns,N0,N1),
        PostFrac is (P1+0.001)/(P1+N1),
        PostBits is -log(PostFrac)/log(2),      % bits required to encode a post pos
        GainBits is P1*(PriorBits - PostBits),  % total bits gained
        Loss is -GainBits,
        find_loss(C,T,Ps,Ns,P0,N0,PriorBits,T1).

find_covered(lte,_,[],N,N):- !.
find_covered(lte,X,[Y|T],N,N1):-
	Y > X, !,
	length([Y|T],N0),
	N1 is N - N0.
find_covered(gte,_,[],_,0):- !.
find_covered(gte,X,[Y|T],_,N1):-
	Y >= X, !,
	length([Y|T],N1).
find_covered(C,X,[_|T],N,N1):-
	find_covered(C,X,T,N,N1).

list_max([H|T],X):-
	find_elem(max,T,H,X).

list_min([H|T],X):-
	find_elem(min,T,H,X).

find_elem(_,[],X,X).
find_elem(max,[H|T],X,Y):-
	(H > X -> find_elem(max,T,H,Y); find_elem(max,T,X,Y)).
find_elem(min,[H|T],X,Y):-
	(H < X -> find_elem(min,T,H,Y); find_elem(min,T,X,Y)).
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