:- module(_,[],[assertions,nativeprops]).

:- set_prolog_flag(single_var_warnings, off).

% Example 6, King, "A Synergistic Analysis for Sharing and Groundness which traces Linearity"

% Entry substitution cannot be expressed in ShLin, which cannot prove that X, Y and Z are linear
% at the exit.

:- entry example1(U, V, W, X, Y, Z): (nonvar([([U, X], [U,X]), ([V, X], [V, X]), ([W, X], [W]), ([Y], [Y]), ([Z], [Z])]),
    mshare([[U, X], [V, X], [W, X], [Y], [Z]]), linear([U, V, W, Y, Z])).

example1(U, V, W, X, Y, Z) :-
    X = f(Y, Z),
    W = g.

% Example 5.10, Amato and Scozzari

% Entry substitution cannot be expressed in ShLin, which cannot prove that V is linear
% at the exit.

:- entry example2(U, V, X, Y): (nonvar([([X], []), ([X,U],[X,U]), ([X,Y],[X,Y]), ([Y,V],[Y, V])]),
    mshare([[X], [X,U], [X,Y], [Y, V]]), linear([U, Y, V])).

example2(U, V, X, Y) :-
    X = r(Y, Y).

% Example 5.13, Amato and Scozzari

:- entry example3(U, V, W, X, Y): (mshare([[U,X], [V,X], [W, X], [Y]]), linear([U, V, W, X, Y])).

example3(U, V, W, X, Y) :-
    X = r(Y, Y)
    % Sharing group [U,V,W,X,Y] cannot be obtained here, and proving it requires the optimal unification
    % for ShLin2 (it also works with optimal ShLin2).
    .

% Example 5.14, Amato and Scozzari

:- entry example4(U, X, Y, Z): (mshare([[U,X], [X, Y], [Y, Z]]), linear([U, X, Y, Z])).

example4(U, X, Y, Z) :-
    X = r(Y)
    % U and Z are linear, and proving it requires the optimal unification for ShLin2 (it also
    % works with optimal ShLin).
    .

% Section 6.1, Amato and Scozzari

:- entry example5.

% We need the optimal ShLin2 or ShLin to prove that L is ground at the exit of example5. Standard mgu
% for ShLin2 is not enough.

% If we replace the body of example5 witth difflist(L, H, H) the matching operation loses precision
% and we cannot prove anymore that L is ground.

example5 :- difflist(L, H, T), H=T.

% It seems that optimal ShLin cannot prove that L is linear at the exit of difflist/2. Check this.

difflist(L, H, T) :- L=[], H=T.
difflist(L, H, T) :- L=[X|L1], H=[X|H1], difflist(L1, H1, T).

% Section 6.2, Amato and Scozzari

% We need the optimal ShLin2 to prove that L is linear at the exit of example6. Optimal ShLin
% is not enough.

:- entry example6.

% Optimal ShLin2 can prove that, at the end of example6, L is linear and [L, D, X1, X2] are never
% in the same sharing group.

example6 :-
    difflist1(L, D),
    D = [X1,X2|H]-T.

% It seems that optimal ShLin cannot prove that L is linear at the exit of difflist1/2. Check this.

:- entry difflist1(L, D): (mshare([[L], [D]]), linear([L, D])).

difflist1(L, D) :- L=[], D = H-H.
difflist1(L, D) :- L=[X|L1], D=[X|H]-T, D1 = H-T, difflist1(L1, D1).
