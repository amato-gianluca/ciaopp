:- module(as_aux, [], [assertions,basicmodes,nativeprops]).

:- doc(title, "Common module for Amato and Scozzari domains").
:- doc(author, "Gianluca Amato").
:- doc(author, "Francesca Scozzari").

:- doc(module,"
This module is in common among all domains in the as_* collection.
").

:- use_module(library(sort)).
:- use_module(library(sets)).
:- use_module(library(terms_vars)).
:- use_module(library(terms_check)).
:- use_module(library(iso_misc)).
:- use_module(library(idlists)).

%------------------------------------------------------------------------
% ASSERTIONS
%-------------------------------------------------------------------------

:- prop memberof(L, T)
   # "@var{T} is a member of list @var{L}".
:- export(memberof/2).

memberof(L, T)
   :- member(T, L).

:- prop ordlist(T, S)
   # "@var{S} is an ordered list of elements of type T".
:- export(ordlist/2).

ordlist(_T, []).
ordlist(T, S) :-
   ordnlist(T, S).

:- prop ordlist(T)
   # "@var{S} is an ordered list of".
:- export(ordlist/1).

ordlist(S) :-
   ordlist(term, S).

:- push_prolog_flag(read_hiord, on).

:- prop ordnlist(T, S)
   # "@var{S} is an ordered non-empty list of elements of type T".
:- meta_predicate ordnlist(pred(1),?).
:- export(ordnlist/2).

ordnlist(T, [X]) :-
   T(X).
ordnlist(T, [X1,X2|Xs]) :-
   T(X1),
   X1 @< X2,
   ordnlist(T, [X2|Xs]).

:- pop_prolog_flag(read_hiord).

:- prop independent_from(?Term1, ?Term2)
   # "@var{Term1} and @var{Term2} do not share variables".
:- export(independent_from/2).

independent_from(Term1, Term2) :-
   varset(Term1, Vars1),
   varset(Term2, Vars2),
   ord_disjoint(Vars1, Vars2).

:- prop superset_vars_of(?Term1, ?Term2)
   # "@var{Term2} has a superset of the variables of @var{Term1}".
:- export(superset_vars_of/2).

superset_vars_of(Term1, Term2) :-
   varset(Term1, Vars1),
   varset(Term2, Vars2),
   ord_subset(Vars1, Vars2).

:- prop same_vars_of(?Term1, ?Term2)
   # "@var{Term1} and @var{Term2} have the same variables".
:- export(same_vars_of/2).

same_vars_of(Term1, Term2) :-
   varset(Term1, Vars1),
   varset(Term2, Vars2),
   Vars1 == Vars2.

:- prop predicate_of(+Goal,-Pred)
   : cgoal * ivar => atm(Pred)
   # "@var{Pred} is the predicate of @var{Goal}".
:- export(predicate_of/2).

predicate_of(Goal, Pred) :-
   remove_module(Pred, Pred0),
   functor(Goal, Name, Arity),
   remove_module(Name, RealName),
   atom_concat(RealName, '/', Pred1),
   atom_number(N, Arity),
   atom_concat(Pred1, N, Pred0).

:- prop remove_module(+Atom, -Atom0)
   : atm * ivar => atm(Atom0)
   # "@var{Atom0} is the result of removing the module name from @var{Atom}".

remove_module(Atom, Atom0) :-
   sub_atom(Atom, Pos, _, _, ':'), !,
   Pos1 is Pos+1,
   sub_atom(Atom, Pos1, _, 0, Atom0).
remove_module(Atom, Atom).

:- prop unifier_no_cyclic(+Unifier)
   : unifier
   # "@var{Unifier} is a unifier without cyclic bindings".
:- export(unifier_no_cyclic/1).

unifier_no_cyclic([]).
unifier_no_cyclic([X = T|Rest]) :-
   varset(T, Vt),
   ord_test_member(Vt, X, no),
   unifier_no_cyclic(Rest).

%------------------------------------------------------------------------
% AUXILIARY OPERATIONS
%-------------------------------------------------------------------------

:- pred if_not_nil(+List, +Token, -List1, ?List2)
   :: list(List2) : list * term * ivar * term  => (term(List1), term(List2))
   + (not_fails, is_det).
:- export(if_not_nil/4).

if_not_nil([], _, Xs, Xs) :- !.
if_not_nil(_, X, [X|Xs], Xs).

:- push_prolog_flag(read_hiord, on).

:- pred all_couples(+List,+Pred)
   : list *  cgoal
   # "The predicate @var{Pred} is true for all couples of elements of @var{List}".
:- meta_predicate all_couples(?, pred(2)).
:- export(all_couples/2).

all_couples([], _).
all_couples([X|Xs], Pred) :-
   all_couples0(X, Xs, Pred),
   all_couples(Xs, Pred).

:- pred all_couples0(?Term,+List,+Pred)
   : term * list * cgoal
   # "The predicate @var{Pred} is true for all different couples (@var(Term), X)
   with X in @var(List)".

all_couples0(_, [], _).
all_couples0(X, [Y|Ys], Pred) :-
   Pred(X, Y),
   all_couples0(X, Ys, Pred).

:- pop_prolog_flag(read_hiord).

:- pred duplicates(+List, -Duplicates)
   : list * ivar => ordlist(Duplicates)
   + (not_fails, is_det)
   # "@var{Duplicates} contains the duplicate elements of @var{List}. It does not
   perform any instantiation".
:- export(duplicates/2).

duplicates(List, Duplicates) :-
   duplicates0(List, Duplicates0),
   sort(Duplicates0, Duplicates).

:- pred duplicates0(+List, -Duplicates)
   : list * ivar => list(Duplicates)
   + (not_fails, is_det)
   # "@var{Duplicates} contains the duplicate elements of @var{List}. It does not
   perform any instantiation".

duplicates0([], []).
duplicates0([X|Tail], [X|Duplicates]) :-
   memberchk(X, Tail),
   !,
   duplicates0(Tail, Duplicates).
duplicates0([_|Tail], Duplicates) :-
   duplicates0(Tail, Duplicates).

:- pred unifiable_with_occurs_check(+T1, +T2, -Unifier)
   : term * term * ivar => unifier(Unifier)
   + is_det
   # "@var{Unifier} is the unifier of @var{T1} and @var{T2} with occurs check".
:- export(unifiable_with_occurs_check/3).

unifiable_with_occurs_check(T1, T2, Unifier) :-
   unifiable(T1, T2, Unifier),
   unifier_no_cyclic(Unifier).

:- pred duplicate_vars(+T, -Vars, -DVars)
   : term * ivar * ivar => (ordlist(var, Vars),  ordlist(var, UVars))
   + (not_fails, is_det)
   # "@var{Vars} is the list of variables in @var{T}, @var{DVars} is the list of
   duplicate variables in T".
:- export(duplicate_vars/3).

duplicate_vars(T, Vars, DVars) :-
   varsbag(T, Bag, []),
   duplicates(Bag, DVars),
   sort(Bag, Vars).

:- pred unique_vars(+T, -Vars, -UVars)
   : term * ivar * ivar => (ordlist(var, Vars),  ordlist(var, UVars))
   + (not_fails, is_det)
   # "@var{Vars} is the list of variables in @var{T}, @var{UVars} is the list of
   variables which only occur once in @var{T}".
:- export(unique_vars/3).

unique_vars(T, Vars, UVars) :-
   duplicate_vars(T, Vars, DVars),
   ord_subtract(Vars, DVars, UVars).
