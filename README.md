# aleph

## Introduction

Porting of Aleph for SWI-Prolog.

Aleph is an Inductive Logic Programming system developed by [Ashwin Srinivasan](https://www.bits-pilani.ac.in/goa/ashwin/profile):

http://www.cs.ox.ac.uk/activities/machlearn/Aleph/

This pack contains a porting of Aleph v.5 to SWI-Prolog. The porting was done by [Fabrizio Riguzzi](http://ml.unife.it/fabrizio-riguzzi/).

Two files are included: `aleph_orig.pl` is a direct porting of Aleph for Yap, while `aleph.pl` is modoule-file that can run also under SWISH.
`aleph.pl` was developed by Paolo Niccolò Giubelli  and Fabrizio Riguzzi.


## Usage
`aleph_orig.pl` can be used as the original Aleph.

`aleph.pl` differs because it uses a single input file instead of three files for background, positive and negative examples.

The input file for `aleph.pl` must be structured as follows:

### 1. Module loading
```
:- use_module(library(aleph)).
```
### 2. Aleph initialization
```
:- aleph.
```
### 3. Directives
Nothing has changed here, you can use `modeh/2`, `modeb/2`, `determination/2` as documented in the [manual](#manual) except that `set/2` and `setting/2` are replaced by `aleph_set/2` and 
   `aleph_setting/2`.
```
% e.g.: 
:- modeh(*,grandparent(+person,-person)).
:- modeh(*,parent(+person,-person)).

:- modeb(*,mother(+person,-person)).
:- modeb(*,father(+person,-person)).
:- modeb(*,parent(+person,-person)).

:- aleph_set(verbose,1).

% ...
```
### 4. Background Knowledge Section
Nothing has changed here except you need to enclose this section with *begin_bg/0* and *end_bg/0* directives. Between them you can put your background clauses. 
```
% Background knoweledge is delimited by begin_bg/0 and end_bg/0
% predicates. Look at the 
% E.g.:
:-begin_bg.
person(bob).
person(dad(bob)).
%...
:-end_bg.
```
### 5. Positive Examples Section
```
% The positive examples section is delimited by begin_in_pos/0 and end_in_pos/0
% directives.
% E.g.:
:-begin_in_pos.
grandparent(dad(dad(bob)),bob).
grandparent(dad(mum(bob)),bob).
%...
:-end_in_pos.
```
### 6. Negative Examples Section
```
% The negative examples section is delimited by begin_in_neg/0 and end_in_neg/0
% directives. Negative examples must be listed as facts.
% E.g.:
:-begin_in_neg.
grandparent(bob,bob). % bob is not a grandparent of bob
%...
:-end_in_neg.
```

## New induction commands

You can use the usual Aleph commands for performing learning.
   Moreover, the following predicates were added. 
   Their arity has been increased by one compared to the original version. 
   The (new) output argument returns the result of the command.<br />


- `induce(-Program)`
- `induce_tree(-Program)`
- `induce_cover(-Program)`
- `induce_modes(-Modes)`
- `induce_incremental(-Program)`
- `induce_max(-Program)`
- `induce_features(-Features)`
- `induce_constraints(-Constraints)`
- `induce_theory(-Program)`
- `induce_clauses(-Program)`
- `covers(-Ex)`
- `coversn(-Ex)`
- `reduce(-Cl)`
- `addgcws(-Cl)`
- `good_clauses(-Cls)`

## Manual
The manual can be found at http://www.cs.ox.ac.uk/activities/machlearn/Aleph/.

## Examples
The examples have been downloaded from http://www.comlab.ox.ac.uk/oucl/research/areas/machlearn/Aleph/misc/examples.zip and ported to SWI-Prolog.