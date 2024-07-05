:- module(as_bags, [], [assertions, basicmodes, nativeprops, indexer]).

% :- use_package(debug).
% :- use_package(rtchecks).

:- use_module(library(sets)).
:- use_module(library(terms_vars)).
:- use_module(domain(as_aux)).

:- push_prolog_flag(read_hiord, on).

:- prop isbag(+T, ?B)
   + is_det
   # "@var{B} is a bag of elements of type @var{T}.".
:- export(isbag/2).
:- index isbag(?, +).

isbag(_T, []).
isbag(T, [X-V]) :-
   T(X),
   V > 0.
isbag(T, [X1-V1,X2-V2|Rest]) :-
   X1 @< X2,
   V1 > 0,
   T(X1),
   isbag([X2-V2|Rest]).

:- prop isbag(?B)
   + is_det
   # "@var{B} is a bag".
:- export(isbag/1).

isbag(B) :- isbag(term, B).

:- pop_prolog_flag(read_hiord).

:- prop bag_empty(?B)
   => isbag(B)
   + is_det
   # "@var{B} is an empty bag".
:- export(bag_empty/1).

bag_empty([]).

:- prop bag_support(+B, -S)
   : isbag * ivar => ordlist(S).
   + (not_fails, is_det)
   # "@var{S} is the support of @var{B}.".
:- export(bag_support/2).

bag_support([], []).
bag_support([X-_|RestB], [X|RestS]) :-
   bag_support(RestB, RestS).

:- prop bag_from_set(+S, -B)
   : ordlist * ivar => isbag(B)
   + (not_fails, is_det)
   # "@var{B} is the bag corresponding to the set @var{S} where all
   elements have multiplicity one.".
:- export(bag_from_set/2).

bag_from_set([], []).
bag_from_set([X|RestS], [X-1|RestB]) :-
   bag_from_set(RestS, RestB).

:- prop bag_from_list(+S, -B)
   : list * ivar => isbag(B)
   + (not_fails, is_det)
   # "@var{B} is the bag corresponding to the list @var{S} where the
   multiplicity of each element is the number of its occurrences in @var{S}.".
:- export(bag_from_list/2).

bag_from_list(S, B) :-
    bag_from_list0(S, [], B).

bag_from_list0([], B, B).
bag_from_list0([X|Rest], B0, B) :-
   bag_union(B0, [X-1], B1),
   bag_from_list0(Rest, B1, B).

:- pred bag_union(+B1, +B2, -B)
   : isbag * isbag * ivar => isbag(B)
   + (not_fails, is_det)
   # "@var{B} is the multiset union of @var{B1} and @var{B2}.".
:- export(bag_union/3).

bag_union([], B2, B2) :- !.
bag_union(B1, [], B1) :- !.
bag_union([X1-V1|Rest1], [X2-V2|Rest2], B) :-
   compare(Rel, X1, X2),
   bag_union0(Rel, X1, V1, X2, V2, Rest1, Rest2, B).

bag_union0(=, X1, V1, _X2, V2, Rest1, Rest2, [X1-V|Rest]) :-
   V is V1 + V2,
   bag_union(Rest1, Rest2, Rest).
bag_union0(<, X1, V1, X2, V2, Rest1, Rest2, [X1-V1|Rest]) :-
   bag_union(Rest1, [X2-V2|Rest2], Rest).
bag_union0(>, X1, V1, X2, V2, Rest1, Rest2, [X2-V2|Rest]) :-
   bag_union([X1-V1|Rest1], Rest2, Rest).

:- pred bag_projection(+B, +S, -Proj)
   : isbag * ordlist * ivar => isbag(B)
   + (not_fails, is_det)
   # "@var{Proj} is the projection of the bag @var{B} on the set of variables @var{S}.".
:- export(bag_projection/3).

bag_projection([], _S, []).
bag_projection(_B, [], []).
bag_projection([X-V|RestB], [Y|RestS], B) :-
   compare(Rel, X, Y),
   bag_projection0(Rel, X, V, RestB, Y, RestS, B).

bag_projection0(=, X, V, RestB, _Y, RestS, [X-V|Rest]) :-
   bag_projection(RestB, RestS, Rest).
bag_projection0(<, _X, _V, RestB, Y, RestS, B) :-
   bag_projection(RestB, [Y|RestS], B).
bag_projection0(>, X, V, RestB, _Y, RestS, B) :-
   bag_projection([X-V|RestB], RestS, B).

:- pred bag_vars(?T, -B)
   : term * ivar => isbag(B)
   + (not_fails, is_det)
   # "@var{B} is the bag of variables occuring in @var{T}.".
:- export(bag_vars/2).

bag_vars(T, B) :-
   varsbag(T, Vars, []),
   bag_from_list(Vars, B).
