% generated: 20 November 1989
% option(s):
%
%   boyer
%
%   Evan Tick (from Lisp version by R. P. Gabriel)
%
%   November 1985
%
%   prove arithmetic theorem

:- module(_,[],[assertions,nativeprops]).

:- set_prolog_flag(single_var_warnings, off).

:- entry p(A): ground(A).

p(A).
p(A) :- p([_|A]).