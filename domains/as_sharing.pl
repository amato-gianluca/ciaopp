:- module(as_sharing, [], [assertions, regtypes, basicmodes, nativeprops, indexer]).

:- use_package(debug).
:- use_package(rtchecks).
%:- use_module(engine(io_basic)).

:- doc(title, "sharing abstract domain").
:- doc(module,"
This module is an independent reimplementation of the Sharing domain.
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
% abstract it) and Struct1 is a (domain defined) structure resulting of
% adding the (domain dependent) information conveyed by Prop to structure
% Struct0. This way, the properties relevant to a domain are being
% accumulated. Later, the resulting structure will be handled by
% input_user_interface/5.
%-------------------------------------------------------------------------

:- dom_impl(_, input_interface/4, [noq]).
:- pred input_interface(+Prop, ?Kind, ?Struc0, -Struc1)
   :: atm(Kind) : term * term * term * ivar => (atm(Kind), term(Struc0), term(Struc1)).

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
% of abstract substitution ASub on variables Qv. These are later
% translated to the properties which are visible in the preprocessing unit.
%
% OutFlag seems to be either yes (when called from asub_to_out) or no
% (when called from asub_to_info).
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
   ground_vars(ASub, Qv, Gv),
   if_not_nil(Gv, ground(Gv), NativeStat0, []).

%------------------------------------------------------------------------
% DOMAIN ASSERTIONS
%-------------------------------------------------------------------------

:- prop nasub(ASub) # "@var{ASub} is a non empty abstract substitution".

nasub(Sh) :-
   ordlist(ordlist(var), Sh).

:- prop nasub_u(ASub) # "@var{ASub} is a non empty unordered abstract substitution".

nasub_u(Sh) :-
   % note that list(ordlist(var)) does not work
   list(list(var), Sh).

%-------------------------------------------------------------------------
% DOMAIN PREDICATES
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% normalize(+ASub_u,-ASub)
%
% ASub is the result of normalizing abstract substitution ASub_u.
%-------------------------------------------------------------------------

:- pred normalize(+ASub_u, -ASub)
   : nasub_u * ivar => nasub(ASub)
   + (not_fails, is_det).

normalize(Sh_u, Sh) :-
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
project0([S|Rest], Vars, Proj0, Proj) :-
   ord_intersection(S, Vars, S_proj),
   ( S_proj = [] -> Proj1 = Proj0 ; insert(Proj0, S_proj, Proj1) ),
   project0(Rest, Vars, Proj1, Proj).

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

%-------------------------------------------------------------------------
% mgu(+ASub,Fv,+Sub,MGU)
%
% MGU is the result of the unification of ASub with the substitution  Sub.
% Variables in Fv are considered to be free.
%-------------------------------------------------------------------------

% TODO: Uptimize by replacing ASub with a specialized version where terms are
% replaced by their variables

:- pred mgu(+ASub, +Fv, +Sub, -MGU)
   : nasub * ordlist(var) * unifier_no_cyclic * ivar => nasub(MGU)
   + (not_fails, is_det).

mgu(Sh, Fv, Sub, MGU) :-
   ( current_pp_flag(mgu_sh_optimize, on) ->
      mgu0(Sh, Fv, Sub, MGU)
   ;
      mgu0(Sh, [], Sub, MGU) ).

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

:- pred mgu_binding(+Sh, ?Vars_x, ?Vars_t, Fv, MGU_sh, MGU_fr)
   : nasub * var * term * ordlist(var) * ivar * ivar => (nasub(MGU_sh), ordlist(var, MGU_fr))
   + (not_fails, is_det).

mgu_binding(Sh, X, T, Fv, MGU_sh, MGU_fr) :-
   ord_member(X, Fv), !,
   varset(T, Vt),
   rel(Sh, [X], Sh_x, Sh_x_neg),
   rel(Sh, Vt, Sh_t, Sh_t_neg),
   ord_intersection(Sh_x_neg, Sh_t_neg, Sh_rel_neg),
   bin(Sh_x, Sh_t, Sh0),
   ord_union(Sh_rel_neg, Sh0, MGU_sh),
   ord_subtract(Fv, [X], MGU_fr).

mgu_binding(Sh, X, T, Fv, MGU_sh, MGU_fr) :-
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
   merge_list_of_lists([Sh_rel_neg, Sh0, Sh1, Sh2], MGU_sh),
   ord_subtract(Fv, Vt_f, Fv0),
   ord_subtract(Fv0, [X], MGU_fr).

%-------------------------------------------------------------------------
% match(+ASub1,+Sv1,+ASub2,-Match)
%
% Match is the abstract matching between ASub1 (over the variables in Sv1)
% and ASub2, where ASub1 is the abstract substitution which should not be
% further instantiated.
%
% With respect to the general definition of matching, we only consider
% the special case in which the variables of ASub2 (not even provided as
% are a superset of Sv1.
%-------------------------------------------------------------------------

:- pred match(+ASub1, +Sv1, +ASub2, -Match)
   : nasub * {ordlist(var), superset_vars_of(ASub1)} * nasub * ivar => nasub(Match)
   + (not_fails, is_det).

% TODO: Optimize with clause match(Sh1, [], Sh2, []).
% TODO: Make it faster by converting to use tail recursion

match(Sh1, Sv1, Sh2, Match) :-
   rel(Sh2, Sv1, Intersect, Disjunct),
   star_union(Intersect, Star),
   match0(Star, Sh1, Sv1, Match0),
   ord_union(Disjunct, Match0, Match).

:- pred match0(+Sh2_star, +Sh1, +Sv1, -PartialMatch)
   : nasub * nasub * {ordlist(var), superset_vars_of(Sh1)} * ivar => nasub(PartialMatch)
   + (not_fails, is_det).

match0([],_Sh1,_Sv1, []).
match0([Xs|Xss], Sh1, Sv1, PartialMatch) :-
   match0(Xss, Sh1, Sv1, PartialMatch0),
   ord_intersection(Xs, Sv1, Xs_proj),
   ( ord_member(Xs_proj,Sh1) -> insert(PartialMatch0, Xs, PartialMatch); PartialMatch = PartialMatch0 ).

%-------------------------------------------------------------------------
% AUXILIARY PREDICATES
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% rel(+Sh,+Vars,-Sh_rel,-Sh_nrel)
%
% Partition sharing groups in Sh in those which are disjoint from Vars
% (Sh_nrel) and those which are not (Sh_rel).
%-------------------------------------------------------------------------

:- pred rel(+Sh, +Vars, -Sh_rel, -Sh_nrel)
   : nasub * ordlist(var) * ivar * ivar => (nasub(Sh_rel), nasub(Sh_nrel)).
:- export(rel/4).

rel(Sh, Vars, Sh_rel, Sh_nrel) :-
   ord_split_lists_from_list(Vars, Sh, Sh_rel, Sh_nrel).

%-------------------------------------------------------------------------
% bin(+Sh1,+Sh2,-Bin)
%
% Bin is the binary union of Sh1 and Sh2.
%-------------------------------------------------------------------------

:- pred bin(Sh1, Sh2, Bin)
   : nasub * nasub * ivar => nasub(Bin)
   + (not_fails, is_det).
:- export(bin/3).

bin(Sh1, Sh2, Bin) :-
   bin0(Sh1, Sh2, [], Bin).

:- pred bin0(Sh1, Sh2, Bin0, Bin)
   : nasub * nasub * nasub * ivar => nasub(Bin)
   + (not_fails, is_det).

bin0([], _, Bin, Bin).
bin0([X|Rest], Sh, Bin0, Bin) :-
   bin1(X, Sh, [], BinX),
   ord_union(Bin0, BinX, Bin1),
   bin0(Rest, Sh, Bin1, Bin).

:- pred bin1(X, Sh, Bin0, Bin)
   : ordnlist(var) * nasub * nasub * ivar => nasub(Bin)
   + (not_fails, is_det).
:- index bin1(?, +, ?, ?).

bin1(_, [], Bin, Bin).
bin1(X, [Y|Rest], Bin0, Bin) :-
   ord_union(X, Y, XY),
   insert(Bin0, XY, Bin1),
   bin1(X, Rest, Bin1, Bin).

%-------------------------------------------------------------------------
% star_union(+Sh,-Star)
%
% Star is the star union of the sharing groups in Sh.
%-------------------------------------------------------------------------

:- pred star_union(+Sh, -Star)
   : nasub * ivar => nasub(Star)
   + (not_fails, is_det).
:- export(star_union/2).

star_union(Sh, Star) :-
   closure_under_union(Sh, Star).

%-------------------------------------------------------------------------
% ground_vars(+Sh,+Vars,-Gv)
%
% Gv is the set of variables in Vars which are ground w.r.t. Sh.
%-------------------------------------------------------------------------

:- pred ground_vars(+Sh, +Vars, -Gv)
   : nasub * {ordlist(var), superset_vars_of(Sh)} * ivar
   => ( ordlist(var, Gv), independent_from(Sh, Gv), superset_vars_of(Gv, Vars) )
   + (not_fails, is_det).
:- export(ground_vars/3).

ground_vars(Sh, Vars, Gv) :-
   merge_list_of_lists(Sh, Sh_ng),
   ord_subtract(Vars, Sh_ng, Gv).
