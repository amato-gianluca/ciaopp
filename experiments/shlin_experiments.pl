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
    % [X,X1,X2,Y,Y2] is not possible ma proving it requires option mgu_shlin_optimize=noindcheck
    nothing.

% Example 5.17, Amato and Scozzari 2010, "On the interaction between sharingand linearity"

:- entry example4(V, W, X, Y, Z): (mshare([[X,V],[X,Y],[Z,W]]), linear([V, W, X, Y])).

example4(V, W, X, Y, Z) :-
    X = f(Y, Z).
    % [V,X,Y] is not possible ma proving it requires option mgu_shlin_optimize=optimal

% Section 6.3 new paper on matching

% It does not seem possible to replicate the example, due to the fact that
% matching is used in PLAI differently than in the paper.

:- entry example5(X, Y, Z): (mshare([[X, Y], [Y, Z]]), linear([X, Y, Z])).

example5(X, Y, Z) :-
    mymember(X, [Y]).

mymember(U, [U|V]) :- nothing.
mymember(U, [V|W]) :- mymember(U, W).

nothing.

% A new example to test the optimal matching
:- entry example6(X, Y, Z): (mshare([[X, Y], [X, Z]]), linear([X])).

example6(X, Y, Z) :-
    q(X).
    % Y and Z cannot share here, but proving this requires matching_shlin_optimize=optimal.

q(X).
