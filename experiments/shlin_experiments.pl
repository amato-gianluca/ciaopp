:- module(_1,[],[assertions,nativeprops]).

:- set_prolog_flag(single_var_warnings, off).

:- entry example1.

example1 :-
    X = Y,
    p(Y).
    % here X should not be linear but shfrlin incorrectly infers this property

p(t(U,U)).

:- entry example2(X): (linear([X])).

example2(X) :-
    % here X should not BE linear but shfrlin does not infer this property if
    % we do not add the assertion var(X).
    nothing.

nothing.