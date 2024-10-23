:- module(_,[],[default,assertions,nativeprops]).

:- entry top.

:- set_prolog_flag(single_var_warnings, off).
:- set_prolog_flag(multi_arity_warnings, off).

enable_tabling.                         % so we can expand

% AS: removed tabling
% :- table d/1.
% :- table e/1.

top :-
    % AS: removed tabling
    % abolish_all_tables,
    d(_), fail.
top.

% Two mutually recursive predicates:
d(X) :- e(Y), Y < 20000, X is Y + 1.
d(0).

e(X) :- d(Y), Y < 20000, X is Y + 1.
e(0).
