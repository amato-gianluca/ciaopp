:- module(_1,[],[assertions,nativeprops]).

:- use_module(library(aggregates)).

:- set_prolog_flag(single_var_warnings, off).

relation(a,b).
relation(c,d).

:- entry example1(Z): mshare([[Z]]).
:- export(example1/1).

example1(Z) :-
    % Z should be ground after the call to findall
    findall(X, relation(_, X), Z).

:- entry example2(Z): mshare([[Z]]).
:- export(example2/1).
example2(Z) :-
    findall((X,L), relation(_, X), [(_,A), (_,B)]).
