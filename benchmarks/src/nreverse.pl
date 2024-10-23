% generated: 25 October 1989
% option(s):
%
%   nreverse
%
%   David H. D. Warren
%   Copyright: Public domain
%
%   "naive"-reverse a list of 30 integers

:- module(_,[],[default,assertions,nativeprops]).

:- entry top.

:- set_prolog_flag(single_var_warnings, off).
:- set_prolog_flag(multi_arity_warnings, off).

top:-nreverse.

nreverse :- nreverse([1,2,3,4,5,6,7,8,9,10,11,12,
		      13,14,15,16,17,18,19,20,21,
		      22,23,24,25,26,27,28,29,30],_).

nreverse([X|L0],L) :- nreverse(L0,L1), concatenate(L1,[X],L).
nreverse([],[]).

concatenate([X|L1],L2,[X|L3]) :- concatenate(L1,L2,L3).
concatenate([],L,L).
