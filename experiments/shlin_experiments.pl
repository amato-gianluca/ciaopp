:- module(_1,[],[assertions,nativeprops]).

:- set_prolog_flag(single_var_warnings, off).

:- entry q.

q :-
    X = Y,
    p(X).
    % here Y should not be linear but shfrlin incorrectly infers this property

p(t(U,U)).
