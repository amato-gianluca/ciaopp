:- module(_1,[],[assertions,nativeprops]).

:- set_prolog_flag(single_var_warnings, off).

% Example 6.2 "Optimality in Dependent Analysis of Sharing"

:- entry example1(X, Y, Z): mshare([[X, Y],[Y, Z]]).

% We use t(U) instead of U to bypass share optimization when goal and
% head are variants.
example1(t(U), V, W) :-
    % [U, V, W] is not possible here (need -fmgu_sh_optimize=on)
    nothing.

:- entry example2(X, Y, Z): mshare([[X, Y],[X, Z]]).

% Example 6.3 "Optimality in Dependent Analysis of Sharing"

example2(t(U, V), H, K) :-
    % [H, K, U] is not possible here (need -fmgu_sh_optimize=on)
    nothing.

% Example 6.19 "Optimality in Dependent Analysis of Sharing"

:- entry example3(X, Y, Z, W): mshare([[X, W], [X, Z], [Y, W], [Y, Z]]).

example3(f(U, H), f(U, K), S, T) :-
    % [S, T, H] is not possible here
    nothing.

:- entry example4(X, Y, Z) : mshare([[X], [Y], [Z]]).

% Example 7.13 "Optimality in Dependent Analysis of Sharing"

example4(X, Y, Z) :-
    example4bis(t(X), t(Y), t(Z)).
    % [X, Y, Z] is not possible here (need -fmgu_sh_optimize=on)

% We refine the result of the sharing analysis to overcome the low precision
% of forward unification in share.

:- trust pred example4bis(X, Y, Z): mshare([[X], [Y], [Z]]) => mshare([[X, Y], [Y, Z]]).

example4bis(X, Y, Z) :-
    Y = f(X, Z).

nothing.
