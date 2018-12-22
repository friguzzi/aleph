% Simple illustration of the learning of recursive predicates
%       in Aleph
% To run do the following:
%       a. induce.
/** <examples>
?- induce(Program).
*/
:- use_module(library(aleph)).
:- if(current_predicate(use_rendering/1)).
:- use_rendering(prolog).
:- endif.
:- aleph.
% :- modeh(*,mem(+any,+list)).
% :- modeb(*,mem(+any,+list)).
% :- modeb(1,((+list) = ([-any|-list]))).

:- mode(*,mem(+any,+list)).
:- mode(1,((+list) = ([-any|-list]))).

:- aleph_set(i,3).
:- aleph_set(noise,0).


:- determination(mem/2,mem/2).
:- determination(mem/2,'='/2).

:-begin_bg.

:-end_bg.
:-begin_in_pos.
mem(0,[0]).
mem(1,[1]).
mem(2,[2]).
mem(3,[3]).
mem(4,[4]).
mem(0,[0,0]).
mem(0,[0,1]).
mem(0,[0,2]).
mem(1,[0,1]).
mem(0,[1,0]).
mem(0,[2,0]).
mem(1,[1,1]).
mem(1,[2,1]).
mem(1,[1,2]).
mem(2,[2,2]).
mem(2,[3,2]).
mem(2,[2,3]).
mem(3,[2,3]).
mem(3,[4,2,3]).
:-end_in_pos.
:-begin_in_neg.
mem(0,[1,2]).
mem(0,[1]).
mem(1,[0]).
mem(3,[]).
mem(2,[]).
mem(2,[3]).
:-end_in_neg.

:-aleph_read_all.
