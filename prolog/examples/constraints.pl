/* Simple illustration of the extraction of integrity constraints
       by Aleph
 To run do the following:
       c. induce_constraints(Constraints)
 This will learn a set of (possibly redundant) constraints that hold
 in the background knowledge. The procedure is similar to that used
 by DeRaedt et al in Claudien. Constraints that are ``nearly true''
 can be obtained by changing the noise parameter.
*/
/** <examples>
?- induce_constraints(Constraints).
*/
:- use_module(library(aleph)).
:- if(current_predicate(use_rendering/1)).
:- use_rendering(prolog).
:- endif.
:- aleph.

:- modeh(1,aleph_false).

:- modeb(*,human(-person)).

:- modeb(1,male(+person)).
:- modeb(1,female(+person)).
:- modeb(1,not(male(+person))).
:- modeb(1,not(female(+person))).

:- determination(aleph_false/0,human/1).
:- determination(aleph_false/0,male/1).
:- determination(aleph_false/0,female/1).
:- determination(aleph_false/0,(not)/1).

:- aleph_set(noise,0).

:-begin_bg.
male('Fred').
female('Wilma').
human('Fred').
human('Wilma').
:-end_bg.
:-begin_in_pos.
:-end_in_pos.
:-begin_in_neg.
:-end_in_neg.
:-aleph_read_all.

