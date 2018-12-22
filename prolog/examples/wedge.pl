% Simple illustration of constructing tree-based models within Aleph
% To run do the following:
%       a. Load Aleph
%       b. read_all(wedge).
%       c. induce_tree.

% Model trees are constructed by specifying a predicate that
% will be used for model construction for examples in a leaf.
% The user has to provide a definition for this predicate that
% is able to: (a) construct the model; and (b) predict using
% the model constructed. The trick used is the same as that
% for lazy evaluation.

% Learning a model tree
% The function to be learnt is:
%             y = f(x) =  x + 1 (x =< 0)
%                      = -x + 1 ( x > 0)
% That is:
%
%                 |
%                /|\
%               / | \
%              /  |  \
%      --------------------------
%                 0

% what Aleph actually learns with the data given is:
%             y = f(x) =  x + 1 (x =< -0.5)
%                      = -x + 1 ( x > -0.5)
% adding more examples rectifies this: see wedge.f

/** <examples>
?- induce(Program).
*/
:-use_module(library(aleph)).
:- if(current_predicate(use_rendering/1)).
:- use_rendering(prolog).
:- endif.
:- aleph.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% specify tree type

:- aleph_set(tree_type,model).
:- aleph_set(evalfn,mse).
:- aleph_set(minpos,2).       % minimum examples in leaf for splitting
:- aleph_set(mingain,0.01).	% toy example needs this to be low
:- aleph_set(dependent,2).	% second argument of f/2 is to predicted
:- aleph_set(verbosity,10).

% specify predicate definition to use for model construction
:- model(predict/3).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Mode declarations

:- modeh(1,f(+x,-y)).
:- modeb(1,lteq(+x,#threshold)).
:- modeb(1,predict(+x,-y,#params)).

:- determination(f/2,lteq/2).
:- determination(f/2,predict/3).

:-begin_bg.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Type definitions

threshold(-0.5).
threshold(0.0).
threshold(0.5).

params([_Slope,_Constant,_Sd]).

list([_|_]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Background

lteq(X,Y):-
        var(Y), !,
        X = Y.
lteq(X,Y):-
        number(X), number(Y),
        X =< Y.

% definition for model construction (parameter estimation)
predict(X,Y,[M,C,Sd]):-
	list(X),
	list(Y), !,
	l_regress1(Y,X,M,C,Sd).
% definition for prediction
predict(X,Y,[M,C,_]):-
	number(X), var(Y), !,
	Y is M*X + C.
% definition for model checking
predict(X,Y,[M,C,Sd]):-
	number(Y), number(X), !,
	Y1 is M*X + C,
	Diff is Y - Y1,
	abs_val(Diff,ADiff),
	ADiff =< 3*Sd.

% very simple univariate linear regression
l_regress1([YVals|_],[XVals|_],M,C,0.0):-
        YVals = [Y1,Y2|_],
        XVals = [X1,X2|_],
        M is (Y2-Y1)/(X2-X1),
        C is Y1 - M*X1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constraints

% remove redundant checks for =<
% prune((_:-Body)):-
% 	has_literal(lteq(X,Y),Body,Left),
% 	has_literal(lteq(X1,Y1),Left,_),
% 	X == X1,
% 	Y1 =< Y.
% 
% has_literal(L,(L,L1),L1).
% has_literal(L,(_,L1),Left):-
% 	!,
% 	has_literal(L,L1,Left).
% has_literal(L,L,true).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Utilities

abs_val(X,Y):- X < 0, !, Y is -X.
abs_val(X,X):- X >= 0.

:-end_bg.
:-begin_in_pos.

f(-1.0,0.0).
f(-0.5,0.5).
% f(-0.25,0.75).	% adding this results in the correct theory
f(0.0,1.0).
f(0.5,0.5).
f(1.0,0.0).

:-end_in_pos.
:-begin_in_neg.
:-end_in_neg.
:-aleph_read_all.

