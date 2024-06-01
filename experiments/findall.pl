:- module(_1,[],[assertions,nativeprops]).

:- use_module(library(aggregates)).

:- set_prolog_flag(single_var_warnings, off).

:- export(relation/2).
:- export(relation2/2).
relation(a,b).
relation(c,d).

relation2(b, X).
relation2(c, d).

:- entry example1(Z): (mshare([[Z]]), linear([Z])).

example1(Z) :-
    % using analysis on relation we should be able to prove that Z is ground after the call to findall.
    findall(X, relation(_, X), Z).

:- entry example1bis(Z): (mshare([[Z]]), linear([Z])).
example1bis(Z) :-
    findall(X, relation2(_, X), Z).

:- entry example2(Z): (mshare([[Z]]), linear([Z])).

example2(Z) :-
    % Z should be linear after the call to findall, but we currently do not infer this property
    findall((X,L), relation(_, X), Z).

:- entry example3.

example3 :-
    % just check that findall behaves correctly with the $bottom abstract substitution
    fail,
    findall(X, relation(a, X), R).
