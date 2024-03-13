:- module(as_sharing_aux, [], [assertions,regtypes,basicmodes,nativeprops]).

%:- use_package(trace).
:- use_package(rtchecks).

:- doc(title, "Common module for Amato and Scozzari domains using Sharing").
:- doc(author, "Gianluca Amato").
:- doc(author, "Francesca Scozzari").

:- doc(module,"
This module is in common among all domain by Amato and Scozzari which use
sharing information.
").

:- use_module(library(lists)).
:- use_module(library(sets)).
:- use_module(library(lsets)).
:- use_module(library(terms_check)).
:- use_module(library(terms_vars)).

:- use_module(domain(as_aux)).

% :- use_module(engine(io_basic)).

%------------------------------------------------------------------------
% ASSERTIONS
%-------------------------------------------------------------------------

:- prop asub_sh(ASub) # "@var{ASub} is a non-bottom sharing abstract substitution".
:- export(asub_sh/1).

% we do not explicitly encode the empty sharing set.
asub_sh(Sh)
  :- ordlist(ordnlist(var), Sh).

:- regtype asub_sh_u(ASub) #  "@var{ASub} is an unordered sharing abstract substitution".
:- export(asub_sh_u/1).

asub_sh_u(ASub) :-
   % note that list(ordlist(var)) would not work
   list(list(var), ASub).

%-------------------------------------------------------------------------
% projected_gvars(+Sh,+Vars,-Gv)
%
% Gv is the set of variables in Vars which are ground w.r.t. Sh.
%-------------------------------------------------------------------------

:- pred projected_gvars(+Sh, +Vars, -Gv)
   : asub_sh * {ordlist(var), superset_vars_of(Sh)} * ivar
   => ( ordlist(var, Gv), independent_from(Sh, Gv), superset_vars_of(Gv, Vars) )
   + (not_fails, is_det).
:- export(projected_gvars/3).

projected_gvars([], Vars, Vars) :- !.
projected_gvars(_ASub, [], []) :- !.
projected_gvars(ASub, Vars, Gv) :-
   merge_list_of_lists(ASub, NonGround),
   ord_subtract(Vars, NonGround, Gv).

%-------------------------------------------------------------------------
% rel(+Sh,+Vars,-Sh_rel,-Sh_nrel)
%
% Partition sharing groups in Sh in those which are disjoint from Vars
% (Sh_nrel) and those which are not (Sh_rel).
%-------------------------------------------------------------------------

:- pred rel(+Sh, +Vars, -Sh_rel, -Sh_nrel)
   : asub_sh * ordlist(var) * ivar * ivar => (asub_sh(Sh_rel), asub_sh(Sh_nrel)).
:- export(rel/4).

rel(Sh, Vars, Sh_rel, Sh_nrel) :-
   ord_split_lists_from_list(Vars, Sh, Sh_rel, Sh_nrel).

%-------------------------------------------------------------------------
% project_sh(+Sh,+Vars,-Proj)
%
% Proj is the projection of Sh onto the variables in Vars.
%-------------------------------------------------------------------------

:- pred project_sh(+Sh, +Vars, -Proj)
   : asub_sh * ordlist(var) * ivar => asub_sh(Proj)
   + (not_fails, is_det).
:- export(project_sh/3).

project_sh([], _Vars, []) :- !.
project_sh([S|Rest], Vars, Sh_ex) :-
   ord_intersection(S, Vars, S_ex),
   project_sh(Rest, Vars, Rest_ex),
   ( S_ex = [] -> Sh_ex = Rest_ex ; insert(Rest_ex, S_ex, Sh_ex) ).


%-------------------------------------------------------------------------
% bin(+Sh1, +Sh2, -Sh)
%
% Sh is the binary union of Sh1 and Sh2.
%-------------------------------------------------------------------------

:- pred bin(Sh1, Sh2, Sh)
   : asub_sh * asub_sh * ivar => asub_sh(Sh)
   + (not_fails, is_det).
:- export(bin/3).

bin([], _, []).
bin(_, [], []).
bin([X|Rest], Sh, Result) :-
   bin0(X, Sh, Sh_bin),
   bin(Rest, Sh, Rest_bin),
   ord_union(Rest_bin, Sh_bin, Result).

bin0(_, [], []).
bin0(X, [Y|Rest], Result) :-
   ord_union(X, Y, XY),
   bin0(X, Rest, Rest_bin),
   insert(Rest_bin, XY, Result).

%-------------------------------------------------------------------------
% star_union(+Sh, -Star)
%
% Star is the star union of the sharing groups in Sh.
%-------------------------------------------------------------------------

:- pred star_union(+Sh, -Star)
   : asub_sh * ivar => asub_sh(Star)
   + (not_fails, is_det).
:- export(star_union/2).

star_union(Sh, Star) :-
   closure_under_union(Sh, Star).

%-------------------------------------------------------------------------
% independent(+Sh, S, T)
%
% Determines where S and T are definitely independent given the sharing
% information in Sh.
%-------------------------------------------------------------------------

:- pred ind(+Sh, ?S, ?T)
  : asub_sh * term * term
  + is_det.
:- export(ind/3).

ind(Sh, S, T) :-
   varset(S, Vs),
   varset(T, Vt),
   rel(Sh, Vs, Sh_s, _),
   rel(Sh, Vt, Sh_t, _),
   ord_disjoint(Sh_s, Sh_t).

%-------------------------------------------------------------------------
% mgu_sh(+Sh, Fv, +Sub, -Sh_mgu)
%
% Sh_mgu is the result of the unification of Sh with the substitution Sub.
% Variables in Fv are considered to be free.
%-------------------------------------------------------------------------

:- pred mgu_sh(+Sh, +Fv, +Sub, -Sh_mgu)
   : asub_sh * ordlist(var) * unifier * ivar => asub_sh(Sh_mgu)
   + (not_fails, is_det).
:- export(mgu_sh/4).

mgu_sh(Sh, _Fv, [], Sh).
mgu_sh(Sh, Fv, [X=T|Rest], Sh_mgu) :-
   mgu_sh_binding(Sh, X, T, Fv, Sh0, Fv0),
   mgu_sh(Sh0, Fv0, Rest, Sh_mgu).

%-------------------------------------------------------------------------
% mgu_sh_binding(+Sh, X, T, -Sh_mgu)
%
% Sh_mgu is the result of the unification of Sh with the binding {X/T}.
%-------------------------------------------------------------------------

:- pred mgu_sh_binding(+Sh, ?Vars_x, ?Vars_t, +Fv, -Sh_mgu, -Fv_mgu)
   : asub_sh * var * term *  ordlist(var) * ivar * ivar => (asub_sh(Sh_mgu), ordlist(var, Fv_mgu))
   + (not_fails, is_det).

mgu_sh_binding(Sh, X, T, Fv, Sh_mgu, Fv_mgu) :-
   ord_member(X, Fv), !,
   varset(T, Vt),
   rel(Sh, [X], Sh_x, Sh_x_neg),
   rel(Sh, Vt, Sh_t, Sh_t_neg),
   ord_intersection(Sh_x_neg, Sh_t_neg, Sh_rel_neg),
   bin(Sh_x, Sh_t, Sh0),
   ord_union(Sh_rel_neg, Sh0, Sh_mgu),
   ord_subtract(Fv, [X], Fv_mgu).

mgu_sh_binding(Sh, X, T, Fv, Sh_mgu, Fv_mgu) :-
   varset(T, Vt),
   ord_intersection_diff(Vt, Fv, Vt_f, Vt_nf),
   rel(Sh, [X], Sh_x, Sh_x_neg),
   rel(Sh, Vt_f, Sh_t_f, Sh_t_f_neg),
   rel(Sh, Vt_nf, Sh_t_nf, Sh_t_nf_neg),
   ord_intersect_all([Sh_x_neg, Sh_t_f_neg, Sh_t_nf_neg], Sh_rel_neg),
   star_union(Sh_x, Sh_x_star),
   star_union(Sh_t_f, Sh_t_f_star),
   star_union(Sh_t_nf, Sh_t_nf_star),
   bin(Sh_x, Sh_t_f_star, Sh0),
   bin(Sh_x_star, Sh_t_nf_star, Sh1),
   bin(Sh1, Sh_t_f_star, Sh2),
   merge_list_of_lists([Sh_rel_neg, Sh0, Sh1, Sh2], Sh_mgu),
   ord_subtract(Fv, Vt_f, Fv0),
   ord_subtract(Fv0, [X], Fv_mgu).

%-------------------------------------------------------------------------
% match_sh(+Sh1, +Sv1, +Sh2, -Match)
%
% Match is the abstract matching between Sh1 (over the variables in Sv1)
% and Sh2, where Sh1 is the abstract substitution which should not be
% further instantiated.
%
% With respect to the general definition of matching, we only consider
% the special case in which the variables of Sh2 (not even provided as
% are a superset of Sv1.
%-------------------------------------------------------------------------

:- pred match_sh(+Sh1,+Sv1,+Sh2,-Match)
   : asub_sh * {ordlist(var), superset_vars_of(Sh1)} * asub_sh * ivar => asub_sh(Match)
   + (not_fails, is_det).
:- export(match_sh/4).

% TODO: optimize with clause match_sh(Sh1, [], Sh2, []).
% TODO: make it faster by converting to use tail recursion

match_sh(Sh1, Sv1, Sh2, Match) :-
   rel(Sh2, Sv1, Intersect, Disjunct),
   star_union(Intersect, Star),
   match_sh0(Star, Sh1, Sv1, Match0),
   ord_union(Disjunct, Match0, Match).

:- pred match_sh0(+Sh2_star, +Sh1, +Sv1, -PartialMatch)
   : asub_sh * asub_sh * {ordlist(var), superset_vars_of(Sh1)} * ivar => asub_sh(PartialMatch)
   + (not_fails, is_det).

match_sh0([],_Sh1,_Sv1, []).
match_sh0([Xs|Xss], Sh1, Sv1, PartialMatch) :-
   match_sh0(Xss, Sh1, Sv1, PartialMatch0),
   ord_intersection(Xs, Sv1, Xs_proj),
   ( ord_member(Xs_proj,Sh1) -> insert(PartialMatch0, Xs, PartialMatch); PartialMatch = PartialMatch0 ).

%------------------------------------------------------------------------
% UNUSED AUXILIARY OPERATIONS
%-------------------------------------------------------------------------

:- pred aexists_sh(+Sh, +Vars, -Sh_ex)
   : asub_sh * ordlist(var) * ivar => asub_sh(Sh_ex).
   + (not_fails, is_det).

aexists_sh(Sh, Vars, Sh_ex) :-
   aexists_sh0(Sh, Vars, Sh_ex0),
   list_to_list_of_lists(Vars, Sh_ex1),
   ord_union(Sh_ex0, Sh_ex1, Sh_ex).

aexists_sh0([], _Vars, []) :- !.
aexists_sh0([S|Rest], Vars, Sh_ex) :-
   ord_subtract(S, Vars, S_ex),
   aexists_sh0(Rest, Vars, Rest_ex),
   ( S_ex = [] -> Sh_ex = Rest_ex ; insert(Rest_ex, S_ex, Sh_ex) ).
