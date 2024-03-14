:- module(_1,[],[assertions,nativeprops]).

:- set_prolog_flag(single_var_warnings, off).

% Example 6.2 "Optimality in Dependent Analysis of Sharing"

:- entry example1(X, Y, Z): mshare([[X, Y],[Y, Z]]).

% We use t(U) instead of U to bypass share optimization when goal and
% head are variants.
example1(t(U), V, W) :-
    % [U, V, W] is not possible here
    nothing.

:- entry example2(X, Y, Z): mshare([[X, Y],[X, Z]]).

% Example 6.3 "Optimality in Dependent Analysis of Sharing"

example2(t(U, V), H, K) :-
    % [H, K, U] is not possible here
    nothing.

% Example 6.19 "Optimality in Dependent Analysis of Sharing"

:- entry example3(X, Y, Z, W): mshare([[X, W], [X, Z], [Y, W], [Y, Z]]).

example3(f(U, H), f(U, K), S, T) :-
    % [S, T, H] is not possible here
    nothing.

nothing.