:- module(as_bags, [], [assertions, basicmodes, nativeprops]).

% :- use_package(debug).
% :- use_package(rtchecks).

:- doc(title, "Bags module for Amato and Scozzari domains").
:- doc(author, "Gianluca Amato").
:- doc(author, "Francesca Scozzari").

:- doc(module,"
This module implements bags (multisets of terms) and is used by domains in the as_* collection. A multiset is an
*ordered* list of terms of the form `T-N`, where `T` is a term and `N` is a natural number representing its
multiplicity.
").

:- use_module(library(terms_vars), [varsbag/3]).
:- use_module(domain(as_aux)).

:- push_prolog_flag(read_hiord, on).

:- prop isbag(+T, +B) + is_det
   # "@var{B} is a bag of elements of type @var{T}.".

:- meta_predicate isbag(pred(1), +).
:- export(isbag/2).
:- test isbag(var, []) + (not_fails, is_det).
:- test isbag(var, [X-2, Y-1]) + (not_fails, is_det).
:- test isbag(term, [X-0, Y-1]) + (fails, is_det).
:- test isbag(var, [X-1, X-1]) + (fails, is_det).
:- test isbag(int, [5-4]) + (not_fails, is_det).
:- test isbag(var, [5-4]) + (fails, is_det).

isbag(_T, []).
isbag(T, [X-V]) :-
   T(X),
   int(V),
   V > 0.
isbag(T, [X1-V1,X2-V2|Rest]) :-
   X1 @< X2,
   int(V1),
   V1 > 0,
   T(X1),
   isbag([X2-V2|Rest]).

:- prop isbag(+B) + is_det
   # "@var{B} is a bag".

:- export(isbag/1).
:- test isbag([hello-1, world-2]) + (not_fails, is_det).

isbag(B) :- isbag(term, B).

:- pop_prolog_flag(read_hiord).

:- pred bag_empty(?B) => isbag(B) + is_det
   # "@var{B} is an empty bag".

:- export(bag_empty/1).
:- test bag_empty(B) => (B = []) + (not_fails, is_det).
:- test bag_empty([]) + (not_fails, is_det).
:- test bag_empty([hello]) + (fails, is_det).

bag_empty([]).

:- pred bag_support(+B, -S): isbag * ivar => ordlist(S) + (not_fails, is_det)
   # "@var{S} is the support of @var{B}.".

:- export(bag_support/2).
:- test bag_support([X-1, hello-1, world-2], S) => (S == [X, hello, world]) + (not_fails, is_det).

bag_support([], []).
bag_support([X-_|RestB], [X|RestS]) :-
   bag_support(RestB, RestS).

:- pred bag_from_set(+S, -B): ordlist * ivar => isbag(B) + (not_fails, is_det)
   # "@var{B} is the bag corresponding to the set @var{S} where all elements have multiplicity one.".

:- export(bag_from_set/2).
:- test bag_from_set([X, hello, world], S) => (S == [X-1, hello-1, world-1]) + (not_fails, is_det).

bag_from_set([], []).
bag_from_set([X|RestS], [X-1|RestB]) :-
   bag_from_set(RestS, RestB).

:- pred bag_from_list(+L, -B): list * ivar => isbag(B) + (not_fails, is_det)
   # "@var{B} is the bag corresponding to the list @var{L} where the multiplicity of each element is the number of its
   occurrences in @var{L}.".

:- export(bag_from_list/2).
:- test bag_from_list([X, world, hello, X, Y, world, X], S)
   => (S == [X-3, Y-1, hello-1, world-2])
   + (not_fails, is_det).

bag_from_list(L, B) :-
   bag_from_list0(L, [], B).

bag_from_list0([], B, B).
bag_from_list0([X|Rest], B0, B) :-
   bag_union(B0, [X-1], B1),
   bag_from_list0(Rest, B1, B).

:- pred bag_union(+B1, +B2, -B): isbag * isbag * ivar => isbag(B) + (not_fails, is_det)
   # "@var{B} is the multiset union of @var{B1} and @var{B2}.".

:- export(bag_union/3).
:- test bag_union([X-2, Y-3, hello-2, world-1], [Y-1, world-4, zz-1], S)
   => (S == [X-2, Y-4, hello-2, world-5, zz-1])
   + (not_fails, is_det).

bag_union([], B2, B2) :- !.
bag_union(B1, [], B1) :- !.
bag_union([X1-V1|Rest1], [X2-V2|Rest2], B) :-
   compare(Rel, X1, X2),
   (
      Rel == '=' -> V is V1 + V2, B = [X1-V|Rest], bag_union(Rest1, Rest2, Rest)
      ; Rel == '<' -> B = [X1-V1|Rest],  bag_union(Rest1, [X2-V2|Rest2], Rest)
      ; B = [X2-V2|Rest], bag_union([X1-V1|Rest1], Rest2, Rest)
   ).

:- pred bag_projection(+B, +S, -Proj): isbag * ordlist * ivar => isbag(B) + (not_fails, is_det)
   # "@var{Proj} is the projection of the bag @var{B} on the set of variables @var{S}.".

:- export(bag_projection/3).
:- test bag_projection([X-2, Y-4, hello-2, world-5], [Y, world], S) => (S == [Y-4, world-5]) + (not_fails, is_det).
:- test bag_projection([X-2, Y-4, hello-2, world-5], [], S) => bag_empty(S) + (not_fails, is_det).

bag_projection([], _S, []) :- !.
bag_projection(_B, [], []) :- !.
bag_projection([X-V|RestB], [Y|RestS], B) :-
   compare(Rel, X, Y),
   (
      Rel == '=' -> B=[X-V|Rest], bag_projection(RestB, RestS, Rest)
      ; Rel == '<' ->  bag_projection(RestB, [Y|RestS], B)
      ; bag_projection([X-V|RestB], RestS, B)
   ).

:- pred bag_vars(?T, -B): term * ivar => isbag(B) + (not_fails, is_det)
   # "@var{B} is the bag of variables occuring in @var{T}, with multiplicities corresponding to the number of
   occurrences.".

:- export(bag_vars/2).
:- test bag_vars(t(X, X, p(X, Y), f(Z, Y, X)), S) => (S = [X-4, Y-2, Z-1]) + (not_fails, is_det).

bag_vars(T, B) :-
   varsbag(T, Vars, []),
   bag_from_list(Vars, B).
