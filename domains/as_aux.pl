:- module(as_aux, [], [assertions, basicmodes, nativeprops, indexer]).

:- use_package(debug).
:- use_package(rtchecks).

:- doc(title, "Common module for Amato and Scozzari domains").
:- doc(author, "Gianluca Amato").
:- doc(author, "Francesca Scozzari").

:- doc(module,"
This module is in common among all domains in the as_* collection.
").

:- use_module(library(sort)).
:- use_module(library(lists)).
:- use_module(library(sets)).
:- use_module(library(terms_vars)).
:- use_module(library(terms_check)).
:- use_module(library(iso_misc)).
:- use_module(library(idlists)).

:- use_module(domain(as_bags)).

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
:- index ordlist(?, +).

ordlist(_T, []).
ordlist(T, S) :-
   ordnlist(T, S).

:- prop ordlist(T)
   # "@var{S} is an ordered list of".
:- meta_predicate ordlist(pred(1),?).
:- export(ordlist/1).

ordlist(S) :-
   ordlist(term, S).

:- push_prolog_flag(read_hiord, on).

:- prop ordnlist(T, S)
   # "@var{S} is an ordered non-empty list of elements of type T".
:- meta_predicate ordnlist(pred(1),?).
:- export(ordnlist/2).
:- index ordlistn(?, +).

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

:- prop multiplicity(X)
   # "@var{X} is a non negative integer or the atom 'inf'".
:- export(multiplicity/1).

multiplicity(inf) :- !.
multiplicity(X) :-
   X >= 0.

%------------------------------------------------------------------------
% AUXILIARY OPERATIONS
%-------------------------------------------------------------------------

:- pred if_not_nil(+List, +Token, -List1, ?List2)
   :: list(List2) : list * term * ivar * term  => (term(List1), term(List2))
   + (not_fails, is_det).
:- export(if_not_nil/4).

if_not_nil([], _, Xs, Xs) :- !.
if_not_nil(_, X, [X|Xs], Xs).

:- pred unifiable_with_occurs_check(?T1, ?T2, -Unifier)
   : term * term * ivar => unifier(Unifier)
   + is_det
   # "@var{Unifier} is the unifier of @var{T1} and @var{T2} with occurs check".
:- export(unifiable_with_occurs_check/3).

unifiable_with_occurs_check(T1, T2, Unifier) :-
   unifiable(T1, T2, Unifier),
   unifier_no_cyclic(Unifier).

%------------------------------------------------------------------------
% SHARING GROUPS AND BAGS
%-------------------------------------------------------------------------

:- pred chiMax(+Sh, +Lin, +Bt, -Mul)
   : ordlist(var) * ordlist(var) * isbag(var) * ivar => multiplicity(Mul)
   + (not_fails, is_det)
   # "@var{Mul} is the maximum multiplicity of the sharing group @var{Sh} with linear
   variables @var{Lin} w.r.t. the term represented by the bag of variables @var{Bt}".
:- export(chiMax/4).

chiMax(Sh, Lin, Bt, Mul) :-
   chiMax0(Sh, Lin, Bt, 0, Mul).

chiMax0([], _Lin, _Bt, M, M) :- !.
chiMax0(_Sh, _Lin, [], M, M) :- !.
chiMax0([X|RestO], Lin, [Y-N|RestBt], Mul0, Mul) :-
   compare(Rel, X, Y),
   (
      Rel = '=' ->
         (
            ord_member(X, Lin)  ->
               Mul1 is Mul0 + N,
               chiMax0(RestO, Lin, RestBt, Mul1, Mul)
            ;
               Mul = inf
         )
      ; Rel = '<' ->
         chiMax0(RestO, Lin, [Y-N|RestBt], Mul0, Mul)
      ; Rel = '>' ->
         chiMax0([X|RestO], Lin, RestBt, Mul0, Mul)
   ).

:- pred linearizable(+O, +Bag)
   : ordlist(var) * isbag(var)
   + is_det
   # "Determines if the sharing group @var{O} is linear w.r.t. the term represented by the
   bag of variables @var{Bag}, assuming all variables are linear.".
:- export(linearizable/2).

linearizable(O, Bag) :- linearizable0(O, Bag, 0).

linearizable0([], _, _) :- !.
linearizable0(_, [], _) :- !.
linearizable0([X|RestO], [Y-N|RestBag], Status) :-
   compare(Rel, X, Y),
   (
      Rel = '=' ->
         ( Status = 0, N = 1 -> linearizable0(RestO, RestBag, 1) ; fail )
      ; Rel = '<' ->
         linearizable0(RestO, [Y-N|RestBag], Status)
      ; Rel = '>' ->
         linearizable0([X|RestO], RestBag, Status)
   ).
