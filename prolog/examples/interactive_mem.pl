% Simple illustration of using Aleph to do incremental learning
% To run do the following:
%       a. Load Aleph
%       b. read_all(mem).
%       c. induce_incremental.
% After that, just follow the menus on screen.

% :- modeh(*,mem(+any,+list)).
% :- modeb(*,mem(+any,+list)).
% :- modeb(1,((+list) = ([-any|-list]))).
:- use_module(library(aleph)).
:- aleph.
:- if(current_predicate(use_rendering/1)).
:- use_rendering(prolog).
:- endif.

:- mode(*,mem(+any,+list)).
:- mode(1,((+list) = ([-any|-list]))).

:- aleph_set(i,3).
:- aleph_set(noise,0).
:- aleph_set(print,1).


:- determination(mem/2,mem/2).
:- determination(mem/2,'='/2).

:-aleph_read_all.