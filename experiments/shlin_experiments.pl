:- module(_1,[],[assertions,nativeprops]).

:- set_prolog_flag(single_var_warnings, off).

:- entry example1.

example1 :-
    X = Y,
    p(Y).
    % here X should not be linear but shfrlin incorrectly infers this property

p(t(U,U)).

:- entry example2(X): linear([X]).

example2(X) :-
    % here X should not BE linear but shfrlin does not infer this property if
    % we do not add the assertion var(X).
    nothing.

% Example 30, Hill et al 2004, "A Correct, Precise and Efficient Integration ..."

:- entry example3(X, X1, X2, Y, Y1, Y2, Z):
    (mshare([[X,X1], [X, X2], [X, Y, Z], [Y, Y1], [Y, Y2]]),
     linear([X, X1, X2, Y, Y1, Y2, Z])).

example3(X, X1, X2, Y, Y1, Y2, Z) :-
    X = Y,
    % [X,X1,X2,Y,Y2] is not possible ma proving it requires option mgu_shlin_noindcheck=on
    nothing.

nothing.
