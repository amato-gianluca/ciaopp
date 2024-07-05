:- module(as_sharing, [], [assertions, basicmodes, nativeprops, indexer]).

% :- use_package(debug).
% :- use_package(rtchecks).

:- doc(title, "sharing abstract domain").
:- doc(module,"
This module is an independent reimplementation of the Sharing domain presented in:

Gianluca Amato and Francesca Scozzari,
Optimality in goal-dependent analysis of Sharing
(2009) Theory and Practice of Logic Programming, 9 (5), pp. 617-689.
https://dx.doi.org/10.1017/S1471068409990111
").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(as_sharing, [default]).

:- include(as_template).

%------------------------------------------------------------------------
% I/O CIAOPP PREDICATES
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% input_interface(+Prop,?Kind,?Struc0,-Struc1)
%
% Prop is a native property that is relevant to domain (i.e., the domain
% knows how to fully (Kind=perfect) or approximately (Kind=approx)
% abstract it and Struct1 is a (domain defined) structure resulting of
% adding the (domain dependent) information conveyed by Prop to structure
% Struct0. This way, the properties relevant to a domain are being
% accumulated. Later, the resulting structure will be handled by
% input_user_interface/5.
%-------------------------------------------------------------------------

:- dom_impl(_, input_interface/4, [noq]).
:- pred input_interface(+Prop, ?Kind, ?Struc0, -Struc1)
   :: atm(Kind) : term * term * term * ivar => (atm(Kind), term(Struc0), term(Struc1))
   + (not_fails, is_det).

input_interface(Prop, Kind, Struc0, Struc1) :-
   sharing:input_interface(Prop, Kind, Struc0, Struc1).

%-------------------------------------------------------------------------
% input_user_interface(?Struct,+Qv,-ASub,+Sg,+MaybeCallASub)
%
% ASub is the abstraction of the information collected in Struct (a domain
% defined structure, see input_interface/4) on variables Qv relative to
% the literal Sg.
%
% Struct may be free if a pred assertion is specified without call conditions.
%
% MaybeCallASub seems to be either 'no' or 'yes(Appr)' where Appr is an
% abstract substitution. However, the second form is only used in the file
% plai/apply_assertions_old.pl.
%
% TODO: Understand the role of MaybeCallASub.
%-------------------------------------------------------------------------

:- dom_impl(_, input_user_interface/5, [noq]).
:- pred input_user_interface(?Struct, +Qv, -ASub, +Sg, +MaybeCallASub)
   : term * {ordlist(var), same_vars_of(Sg)} * ivar * cgoal * cgoal => asub(ASub)
   + (not_fails, is_det).

input_user_interface(Struct, Qv, ASub, Sg, MaybeCallASub) :-
   sharing:input_user_interface(Struct, Qv, ASub, Sg, MaybeCallASub).

%-------------------------------------------------------------------------
% asub_to_native(+ASub,+Qv,+OutFlag,-NativeStat,-NativeComp)
%
% NativeStat and NativeComp are the list of native (state and
% computational, resp.) properties that are the concretization of abstract
% substitution ASub on variables Qv. These are later translated to the
% properties which are visible in the preprocessing unit.
%
% OutFlag seems to be either yes (when called from asub_to_out) or no
% (when called from asub_to_info). However, plai does not seem to use
% asub_to_info.
%
% TODO: Understand with more precision the role of OutFlag.
%-------------------------------------------------------------------------

:- dom_impl(_, asub_to_native/5, [noq]).
:- pred asub_to_native(+ASub, +Qv, +OutFlag, -NativeStat, -NativeComp)
   : asub * {ordlist(var), superset_vars_of(ASub)} * memberof([yes,no]) * ivar * ivar
   + (is_det).

asub_to_native('$bottom', _Qv, _OutFlag, _NativeStat, _NativeComp) :- !, fail.
asub_to_native(ASub, Qv, _OutFlag, NativeStat, []) :-
   if_not_nil(ASub, sharing(ASub), NativeStat, NativeStat0),
   ground(ASub, Qv, Gv),
   if_not_nil(Gv, ground(Gv), NativeStat0, []).

%------------------------------------------------------------------------
% DOMAIN ASSERTIONS
%-------------------------------------------------------------------------

:- prop sharing_group(S) # "@var{S} is a sharing group.".
:- export(sharing_group/1).

sharing_group(S) :-
   ordlist_nonempty(var, S).

:- prop asub_sh(Sh) # "@var{Sh} is a (non bottom) abstract substitution".
:- export(asub_sh/1).

asub_sh(Sh) :-
   ordlist(sharing_group, Sh).

% An unordered abstract substitution is the result of renaming the variables in an
% abstract substitution, possibly breaking any ordering that was present in the
% original stucture.

:- prop sharing_group_u(S) # "@var{S} is an unordered sharing group.".
:- export(sharing_group_u/1).

sharing_group_u(S) :-
   list_nonempty(var, S).

:- prop asub_sh_u(Sh) # "@var{Sh} is a (non bottom) unordered abstract substitution".
:- export(asub_sh_u/1).

asub_sh_u(Sh) :-
   list(sharing_group_u, Sh).

%-------------------------------------------------------------------------
% DOMAIN PREDICATES
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% nasub(+ASub)
%
% ASub is a (non-bottom) abstract substitution.
%-------------------------------------------------------------------------

:- prop nasub(ASub).

nasub(Sh) :-
   asub_sh(Sh).

%-------------------------------------------------------------------------
% nasub_u(+ASub)
%
% ASub_u is a (non-bottom) unordered abstract substitution.
%-------------------------------------------------------------------------

:- prop nasub_u(ASub).

nasub_u(Sh) :-
   asub_sh_u(Sh).

%-------------------------------------------------------------------------
% reorder(+ASub_u,-ASub)
%
% ASub is the result of sorting the unordered abstract substitution ASub_u.
%-------------------------------------------------------------------------

:- pred reorder(+ASub_u, -ASub)
   : nasub_u * ivar => nasub(ASub)
   + (not_fails, is_det).

reorder(Sh_u, Sh) :-
   sort_list_of_lists(Sh_u, Sh).

%-------------------------------------------------------------------------
% top(+Vars,+Top)
%
% Top is the largest abstract substitution on variable Vars.
%-------------------------------------------------------------------------

:- pred top(+Vars, -Top)
   : ordlist(var) * ivar => nasub(Top)
   + (not_fails, is_det).

top(Vars, Top) :-
   % note that powerset does not generate the empty set
   powerset(Vars, Top).

%------------------------------------------------------------------------
% augment(+ASub,+Vars,-Aug)
%
% Augment the abstract substitution ASub adding the fresh variables Vars
% to get the abstract substitution Aug.
%-------------------------------------------------------------------------

:- pred augment(+ASub, +Vars, -Aug)
   : (nasub * {ordlist(var), independent_from(ASub)} * ivar) => nasub(Aug)
   + (not_fails, is_det).

augment(Sh, Vars, Aug) :-
   list_to_list_of_lists(Vars, Sh0),
   ord_union(Sh, Sh0, Aug).

%-------------------------------------------------------------------------
% project(+ASub,+Vars,-Proj)
%
% Proj is the projection of ASub onto the variables in Vars.
%-------------------------------------------------------------------------

:- pred project(+ASub, +Vars, -Proj)
   : nasub * ordlist(var) * ivar => nasub(Proj)
   + (not_fails, is_det).

project(Sh, Vars, Proj) :-
   project0(Sh, Vars, [], Proj).

:- pred project0(+Sh, +Vars, +Proj0, -Proj)
   : nasub * ordlist(var) * nasub * ivar => nasub(Proj)
   + (not_fails, is_det).

project0([], _Vars, Proj, Proj).
project0([S|Ss], Vars, Proj0, Proj) :-
   ord_intersection(S, Vars, S_proj),
   ( S_proj = [] -> Proj1 = Proj0 ; insert(Proj0, S_proj, Proj1) ),
   project0(Ss, Vars, Proj1, Proj).

%-------------------------------------------------------------------------
% join(+ASub1,+ASub2,Join)
%
% Join is the lub (join) og ASub1 and ASub2.
%-------------------------------------------------------------------------

:- pred join(+ASub1, +ASub2, -Join)
   : nasub * nasub * ivar => nasub(Join)
   + (not_fails, is_det).

join(Sh1, Sh2, Join) :-
   ord_union(Sh1, Sh2, Join).

%------------------------------------------------------------------------%
% meet(+ASub1,+ASub2,-Meet)
%
% Meet is the glb (meet) of ASub1 and Sh2.
%------------------------------------------------------------------------%

:- pred meet(+ASub1, +ASub2, -Meet)
   : nasub * nasub * ivar => asub(Meet)
   + (not_fails, is_det).

meet(Sh1, Sh2, Meet):-
   ord_intersection(Sh1, Sh2, Meet).

%------------------------------------------------------------------------%
% unknown(+ASub,+Vars,-Unk)
%
% Unk is obtained by ASub considering all possible instantiations of the
% variables in Vars.
%------------------------------------------------------------------------%

:- pred unknown(+ASub, +Vars, -Unk)
   : nasub * ordlist(var) * ivar => nasub(Unk)
   + (not_fails, is_det).

unknown(ASub, Vars, Unk) :-
   rel(ASub, Vars, Rel, NRel),
   star_union(Rel, Unk0),
   ord_union(NRel, Unk0, Unk).

%-------------------------------------------------------------------------
% mgu(+ASub,+Fv,+Sub,MGU)
%
% MGU is the result of the unification of ASub with the substitution  Sub.
% Variables in Fv are considered to be free.
%-------------------------------------------------------------------------

% TODO: Optimize by replacing Sub with a specialized version where terms are
% replaced by their bag of variables.

:- pred mgu(+ASub, +Fv, +Sub, -MGU)
   : nasub * ordlist(var) * unifier_no_cyclic * ivar => nasub(MGU)
   + (not_fails, is_det).

mgu(Sh, Fv, Sub, MGU) :-
   current_pp_flag(mgu_sh_optimize, optimal), !,
   mgu0(Sh, Fv, Sub, MGU).
mgu(Sh, _Fv, Sub, MGU) :-
   mgu0(Sh, [], Sub, MGU).

:- index mgu0(?, ?, +, ?).

mgu0(Sh, _Fv, [], Sh).
mgu0(Sh, Fv, [X=T|Rest], MGU) :-
   mgu_binding(Sh, X, T, Fv, MGU0, Fv0),
   mgu0(MGU0, Fv0, Rest, MGU).

%-------------------------------------------------------------------------
% mgu_binding(+Sh,+X,+T,+Fv,-MGU,-MGU_fr)
%
% MGU is the result of the unification of Sh with the binding {X/T},
% while MGU_fr is the set of definitively free variables after the
% unification. Fv is the set of free variables before the unification.
%-------------------------------------------------------------------------

:- pred mgu_binding(+Sh, ?Vars_x, ?Vars_t, +Fv, -MGU_sh, -MGU_fr)
   : nasub * var * term * ordlist(var) * ivar * ivar => (nasub(MGU_sh), ordlist(var, MGU_fr))
   + (not_fails, is_det).

mgu_binding(Sh, X, T, Fv, MGU_sh, MGU_fr) :-
   ord_member(X, Fv), !,
   varset(T, Vt),
   rel3(Sh, [X], Vt, Rel_X, Rel_T, NRel),
   bin(Rel_X, Rel_T, MGU0),
   ord_union(NRel, MGU0, MGU_sh),
   ord_delete(Fv, X, MGU_fr).

% TODO: optimize

mgu_binding(Sh, X, T, Fv, MGU_sh, MGU_fr) :-
   unique_vars(T, Vars_t, UVars_t),
   ord_intersection(UVars_t, Fv, Y),
   ord_subtract(Vars_t, Y, Z),
   rel(Sh, [X], Rel_X, NRel_X),
   rel(Sh, Y, Rel_Y, NRel_Y),
   rel(Sh, Z, Rel_Z, NRel_Z),
   ord_intersect_all([NRel_X, NRel_Y, NRel_Z], NRel),
   star_union(Rel_Y, Star_Y),
   bin(Rel_X, Star_Y, Sh0),
   (Rel_Z = [] ->
      ord_union(NRel, Sh0, MGU_sh)
   ;
      star_union(Rel_X, Star_X),
      star_union(Rel_Z, Star_Z),
      bin(Star_X, Star_Z, Sh1),
      bin(Sh1, Star_Y, Sh2),
      merge_list_of_lists([NRel, Sh0, Sh1, Sh2], MGU_sh)
   ),
   ord_subtract(Fv, Vars_t, Fv0),
   ord_delete(Fv0, X, MGU_fr).

%-------------------------------------------------------------------------
% match(+ASub1,+Sv1,+ASub2,-Match)
%
% Match is the abstract matching between ASub1 (over the variables in Sv1)
% and ASub2, where ASub1 is the abstract substitution which should not be
% further instantiated.
%
% With respect to the general definition of matching, we only consider
% the special case in which the variables in ASub2 (not even provided as
% input) are a superset of Sv1.
%-------------------------------------------------------------------------

:- pred match(+ASub1, +Sv1, +ASub2, -Match)
   : nasub * {ordlist(var), superset_vars_of(ASub1)} * nasub * ivar => nasub(Match)
   + (not_fails, is_det).

match(Sh1, Sv1, Sh2, Match) :-
   rel(Sh2, Sv1, Rel, NRel),
   star_union(Rel, Star),
   match0(Star, Sh1, Sv1, [], StarMatch),
   ord_union(NRel, StarMatch, Match).

:- pred match0(+Star, +Sh1, +Sv1, +Match0, -Match)
   : nasub * nasub * {ordlist(var), superset_vars_of(Sh1)} * nasub * ivar => nasub(Match)
   + (not_fails, is_det).

match0([],_Sh1,_Sv1, Match, Match).
match0([X|Xs], Sh1, Sv1, Match0, Match) :-
   ord_intersection(X, Sv1, X_proj),
   ( ord_member(X_proj,Sh1) -> insert(Match0, X, Match1) ;  Match1 = Match0 ),
   match0(Xs, Sh1, Sv1, Match1, Match).

%-------------------------------------------------------------------------
% ng_vars(+ASub,-NGv)
%
% NGv contains the set of non-ground variables in ASub.
%-------------------------------------------------------------------------

:- pred ng_vars(+ASub, -NGv)
   : nasub * ivar => ordlist(var, NGv)
   + (not_fails, is_det).

ng_vars(Sh, NGv) :-
   vars(Sh, NGv).

%-------------------------------------------------------------------------
% make_ground(+ASub,+Gv,-Succ).
%
% Succ is the result of restricting the abstract substitution ASub to
% case when variables in Gv are ground.
%-------------------------------------------------------------------------

% TODO: change name to restrict_ground

:- pred make_ground(+ASub, +Gv, -Succ)
   : nasub * ordlist(var) * ivar => nasub(Succ)
   + (not_fails, is_det).

make_ground(Sh, Gv, Sh_g) :-
   rel(Sh, Gv, _, Sh_g).

%-------------------------------------------------------------------------
% restrict_var(+ASub,+V,-Succ).
%
% Succ is the result of restricting the abstract substitution ASub to the
% case when V is a variable.
%-------------------------------------------------------------------------

:- pred restrict_var(+ASub, +V, -Succ)
   : nasub * var * ivar => nasub(Succ)
   + (not_fails, is_det).

restrict_var(Sh, V, Sh) :-
   ord_member_list_of_lists(V, Sh), !.
restrict_var(_Sh, _, '$bottom').

%-------------------------------------------------------------------------
% restrict_identical(+ASub,+MGU,-Succ).
%
% Succ is the result of restricting the abstract substitution ASub to the
% sharing groups which make all the binding in MGU to be equalities.
%-------------------------------------------------------------------------

:- pred restrict_identical(+ASub, +MGU, -Succ)
   : nasub * unifier_no_cyclic * ivar => nasub(Succ)
   + (not_fails, is_det).

:- export(restrict_identical/3).
:- test restrict_identical(Call, MGU, Succ): (Call = [[X],[X,Y],[X,Z],[Y],[Z]], MGU = [X = f(Y)])
        => (Succ = [[X,Y],[Z]]) + (not_fails, is_det).

:- index restrict_identical(?, +, ?).

restrict_identical(Sh, [], Sh).
restrict_identical(Sh, [X=T|Rest], Succ) :-
   varset(T, Vt),
   restrict_identical0(Sh, X, Vt, Sh0),
   restrict_identical(Sh0, Rest, Succ).

restrict_identical0([], _X, _Vt, []).
restrict_identical0([S|Ss], X, Vt, [S|Ss1]) :-
   ord_test_member(S, X, XinS),
   (ord_intersect(S, Vt) -> VtinS=yes ; VtinS=no),
   XinS == VtinS, !,
   restrict_identical0(Ss, X, Vt, Ss1).
restrict_identical0([_S|Ss], X, Vt, Ss1) :-
   restrict_identical0(Ss, X, Vt, Ss1).

%-------------------------------------------------------------------------
% AUXILIARY PREDICATES
%-------------------------------------------------------------------------

:- pred rel(+Sh, +Vars, -Rel, -NRel)
   : nasub * ordlist(var) * ivar * ivar => (nasub(Rel), nasub(NRel))
   + (not_fails, is_det)
   # "Partition sharing groups in @var{Sh} in those which are disjoint
      from @var{Vars} (@var{NRel}) and those which are not (@var{Rel}).".
:- export(rel/4).

rel(Sh, [X], Rel, NRel) :-
   % optimization for single variable
   !,
   ord_split_lists(Sh, X, Rel, NRel).
rel(Sh, Vars, Rel, NRel) :-
   ord_split_lists_from_list(Vars, Sh, Rel, NRel).
   % alternative:
   % split_lists_from_list(Vars, Sh, Rel, NRel).

:- pred rel3(+Sh, +Vs1, +Vs2, -Rel1, -Rel2, -NRel)
   : nasub * ordlist(var) * ordlist(var) * ivar * ivar * ivar => (asub_sh(Rel), asub_sh(NRel), asub_sh(NRel))
   + (not_fails, is_det)
   # "Partition sharing groups in @var{Sh} in those which contains variables in @var{Vs1},
   variables in @var{Vs2} and those which are disjoint from both.".
:- export(rel3/6).

% TODO: optimize

rel3(Sh, Vs1, Vs2, Rel1, Rel2, NRel) :-
   rel(Sh, Vs1, Rel1, NRel1),
   rel(Sh, Vs2, Rel2, NRel2),
   ord_intersection(NRel1, NRel2, NRel).

:- pred bin(+Sh1, +Sh2, -Bin)
   : nasub * nasub * ivar => nasub(Bin)
   + (not_fails, is_det)
   # "@var{Bin} is binary union extended elementwise to sharing sets @var{Sh1}
      and @var{Sh2}.".
:- export(bin/3).

bin(Sh1, Sh2, Bin) :-
   bin0(Sh1, Sh2, [], Bin).
   % alternative:
   % setproduct_lists(Sh1, Sh2, Bin0, []),
   % sort(Bin0, Bin).

bin0([], _Sh2, Bin, Bin).
bin0([S|Ss], Sh2, Bin0, Bin) :-
   bin1(S, Sh2, Bin0, Bin1),
   bin0(Ss, Sh2, Bin1, Bin).

:- index bin1(?, +, ?, ?).

bin1(_, [], Bin, Bin).
bin1(S, [R|Rs], Bin0, Bin) :-
   ord_union(S, R, SR),
   insert(Bin0, SR, Bin1),
   bin1(S, Rs, Bin1, Bin).

:- pred bin_all(+ShList, -Bin)
   : list(nasub) * ivar => nasub(Bin)
   + (not_fails, is_det)
   # "@var{Bin} is the bin operator applied to all sharing sets in @var{ShList}.".
:- export(bin_all/2).

bin_all([], []).
bin_all([Sh], Sh).
bin_all([Sh1,Sh2|Shs], Bin) :-
   bin(Sh1, Sh2, Bin0),
   bin_all([Bin0|Shs], Bin).

:- pred star_union(+Sh, -Star)
   : nasub * ivar => nasub(Star)
   + (not_fails, is_det)
   # "@var{Star} is the star union of the sharing groups in @var{Sh}.".
:- export(star_union/2).

star_union(Sh, Star) :-
   % note that closure_under_union does not generate the empty set
   closure_under_union(Sh, Star).

:- pred vars(+Sh, -NGv)
   : nasub * ivar
   => ( ordlist(var, NGv), same_vars_of(Sh, NGv) )
   + (not_fails, is_det)
   # "@var{NGv} is the set of non-ground variables in @var{Sh}.".
:- export(vars/2).

vars(Sh, NGv) :-
   merge_list_of_lists(Sh, NGv).

:- pred ground(+Sh, +Vars, -Gv)
   : nasub * {ordlist(var), superset_vars_of(Sh)} * ivar
   => ( ordlist(var, Gv), independent_from(Sh, Gv), superset_vars_of(Gv, Vars) )
   + (not_fails, is_det)
   # "@var{Gv} is the set of variables in @var{Vars} which are ground w.r.t. @var{Sh}".
:- export(ground/3).

ground(Sh, Vars, Gv) :-
   vars(Sh, NGv),
   ord_subtract(Vars, NGv, Gv).

:- pred unique_vars(?T, -Vars, -UVars)
   : term * ivar * ivar => (ordlist(var, Vars),  ordlist(var, UVars))
   + (not_fails, is_det)
   # "@var{Vars} is the list of variables in @var{T}, @var{UVars} is the list of
   variables which only occur once in @var{T}.".
:- export(unique_vars/3).

unique_vars(T, Vars, UVars) :-
   bag_vars(T, Bt),
   unique_vars0(Bt, Vars, UVars).

unique_vars0([], [], []).
unique_vars0([X-N|Rest], [X|Vrest], UVrest) :-
   (N=1 -> UVrest = [X|UVrest0] ; UVrest = UVrest0),
   unique_vars0(Rest, Vrest, UVrest0).
