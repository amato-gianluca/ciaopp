:- module(as_sharing, [], [assertions, regtypes, basicmodes, nativeprops]).

:- use_package(debug).
:- use_package(rtchecks).

:- doc(title, "sharing abstract domain").
:- doc(author, "Gianluca Amato").
:- doc(author, "Francesca Scozzari").

:- doc(module,"
This module is an independent reimplementation of the Sharing domain.
").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(as_sharing, [default]).

:- use_module(ciaopp(preprocess_flags)).
:- use_module(library(lists)).
:- use_module(library(sets)).
:- use_module(library(lsets)).
:- use_module(library(terms_check)).
:- use_module(library(terms_vars)).

:- use_module(domain(as_aux)).
:- use_module(domain(sharing), [input_interface/4, input_user_interface/5]).

%:- use_module(engine(io_basic)).

%------------------------------------------------------------------------
% ASSERTIONS
%-------------------------------------------------------------------------


:- prop asub(ASub)
   # "@var{ASub} is an abstract substitution".

% the value '$bottom' has a special meaning withing the PLAI analyzer and MUST be
% used to represent unreachable states.

asub('$bottom'). % TODO: optimize with cut
asub(ASub) :-
   nasub(ASub).

:- prop nasub(ASub)
   # "@var{ASub} is a non empty abstract substitution".

nasub(ASub) :-
   asub_sh(ASub).

:- prop asub_u(ASub)
   # "@var{ASub} is an unordered abstract substitution".

asub_u('$bottom'). % TODO: optimize with cut
asub_u(ASub) :-
   asub_sh_u(ASub).

%------------------------------------------------------------------------
% DOMAIN PREDICATES
%-------------------------------------------------------------------------

%------------------------------------------------------------------------
% augment_asub(+ASub,+Vars,-ASub0)
%
% Augment the abstract substitution ASub adding the fresh variables Vars
% to get the abstract substitution ASub0.
%-------------------------------------------------------------------------

:- dom_impl(_, augment_asub/3, [noq]).
:- pred augment_asub(+ASub, +Vars, -ASub0)
   : (nasub * {ordlist(var), independent_from(ASub)} * ivar) => nasub(ASub0)
   + (not_fails, is_det).

% TODO: optimize with clause augment_asub(ASub,[],ASub).
augment_asub(ASub, Vars, ASub0) :-
   list_to_list_of_lists(Vars, Vars0),
   ord_union(ASub, Vars0, ASub0).

%-------------------------------------------------------------------------
% unknown_entry(+Sg,+Vars,-Entry)
%
% Entry is the "topmost" abstraction of variables Vars corresponding to
% literal Sg.
%
% TODO: Understand the role of Sg.
%-------------------------------------------------------------------------

:- dom_impl(_, unknown_entry/3, [noq]).
:- pred unknown_entry(+Sg, +Vars, -Entry)
   : cgoal * {ordlist(var), same_vars_of(Sg)} * ivar => asub(Entry)
   + (not_fails, is_det).

unknown_entry(_Sg, Vars, Entry) :-
   % note that powerset does not generate the empty set
   powerset(Vars,Entry).

%-------------------------------------------------------------------------
% abs_sort(+ASub_u,-ASub)
%
% ASub is the result of sorting abstract substitution ASub_u.
%-------------------------------------------------------------------------

:- dom_impl(_, abs_sort/2, [noq]).
:- pred abs_sort(+ASub_u, -ASub)
   : asub_u * ivar => asub(ASub)
   + (not_fails, is_det).

abs_sort('$bottom', '$bottom'). % TODO: optimize with cut
abs_sort(ASub_u, ASub) :-
   sort_list_of_lists(ASub_u, ASub).

%-------------------------------------------------------------------------
% project(Sg,Vars,HvFv_u,ASub,Proj)
%
% Projects the abstract substitution ASub onto the variables of list Vars
% resulting in the projected abstract substitution Proj.
%
% TODO: Understand the role of Sg and HvFv_u.
%-------------------------------------------------------------------------

:- dom_impl(_, project/5, [noq]).
:- pred project(+Sg, +Vars, +HvFv_u, +ASub, ?Proj)
   : cgoal * {list(var), same_vars_of(Sg)} * list(var) * nasub * ivar => asub(Proj)
   + (not_fails, is_det).

project(_Sg, Vars, _HvFv_u, ASub, Proj) :-
   project_sh(ASub, Vars, Proj).

%-------------------------------------------------------------------------
% call_to_entry(+Sv,+Sg,Hv,+Head,+ClauseKey,+Fv,+Proj,-Entry,-ExtraInfo)
%
% Obtains the abstract substitution Entry which results from adding the
% abstraction of the unification Sg = Head to abstract substitution Proj
% (the call substitution for Sg projected on its variables Sv) and then
% projecting the resulting substitution onto Hv (the variables of Head)
% plus Fv (the free variables of the relevant clause). ExtraInfo is
% information which can be reused during the exit_to_prime step.
%-------------------------------------------------------------------------

:- dom_impl(_, call_to_entry/9, [noq]).
:- pred call_to_entry(+Sv, +Sg, +Hv, +Head, +ClauseKey, +Fv, +Proj, -Entry, -ExtraInfo)
   :  {ordlist(var), same_vars_of(Sg), superset_vars_of(Proj)} * cgoal * {ordlist(var), same_vars_of(Head)} * cgoal *
         term * {ordlist(var), independent_from(Hv)} * nasub * ivar * ivar
   => (asub(Entry), unifier(ExtraInfo))
   + (not_fails, is_det).

% save unifier in the ExtraInfo parameter, so that we can use it in exit_to_prime

call_to_entry(_Sv, Sg, Hv, Head, _ClauseKey, Fv, Proj, Entry, Unifier) :-
   unifiable(Sg, Head, Unifier),
   augment_asub(Proj, Hv, ASub),
   mgu_sh(ASub, Hv, Unifier, Entry0),
   project(Head, Hv, [], Entry0, Entry1),
   augment_asub(Entry1, Fv, Entry).

%-------------------------------------------------------------------------
% exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)
%
% Computes the abstract substitution Prime which results from adding the
% abstraction of the unification Sg = Head to abstract substitution Exit
% (the exit substitution for a clause Head projected over its variables
% Hv), projecting the resulting substitution onto Sv.
%-------------------------------------------------------------------------

:- dom_impl(_, exit_to_prime/7, [noq]).
:- pred exit_to_prime(+Sg, +Hv, +Head, +Sv, +Exit, +ExtraInfo, -Prime)
   : cgoal * {ordlist(var), same_vars_of(Head)} * cgoal * {ordlist(var), same_vars_of(Sg)} * asub * unifier * ivar
   => (asub(Prime))
   + (not_fails, is_det).

% take the unifier from the ExtraInfo parameter

exit_to_prime(_Sg, _Hv, _Head, _Sv, '$bottom', _Unifier, '$bottom'). % TODO: optimize with cut
exit_to_prime(Sg, _Hv, _Head, Sv, Exit, Unifier, Prime) :-
   augment_asub(Exit, Sv, ASub),
   mgu_sh(ASub, Sv, Unifier, Prime0),
   project(Sg, Sv, [], Prime0, Prime).

%-------------------------------------------------------------------------
% compute_lub(+ListASub,-LubASub)
%
% LubASub is the least upper bound of the abstract substitutions in
% list ListASub.
%-------------------------------------------------------------------------

:- dom_impl(_, compute_lub/2, [noq]).
:- pred compute_lub(+ListASub, -LubASub)
   : list(asub) * ivar => asub(LubASub)
   + (not_fails, is_det).

compute_lub([ASub], ASub).
compute_lub([ASub1,ASub2|ASubs], LubASub) :-
   compute_lub_el(ASub1, ASub2, ASub3),
   compute_lub([ASub3|ASubs], LubASub).

:- pred compute_lub(+ASub1, +ASub2, -ASub)
   : asub * asub * ivar => asub(ASub)
   + (not_fails, is_det).

compute_lub_el('$bottom', ASub, ASub) :- !.
compute_lub_el(ASub, '$bottom', ASub). % TODO: optimize with cut
compute_lub_el(ASub1, ASub2, Lub) :-
   ord_union(ASub1, ASub2, Lub).

%-------------------------------------------------------------------------
% extend(+Sg,+Prime,+Sv,+Call,-Succ)
%
% Succ is the extension the information given by Prime (success abstract
% substitution over the goal variables Sv) to the rest of the variables
% of the clause in which the goal occurs (those over which abstract
% substitution Call is defined on). I.e., it is like a conjunction of the
% information in Prime and Call, except that they are defined over
% different sets of variables, and that Prime is a successor
% substitution to Call in the execution of the program.
%-------------------------------------------------------------------------

:- dom_impl(_, extend/5, [noq]).
:- pred extend(+Sg,+Prime,+Sv,+Call,-Succ)
   : cgoal * asub * {ordlist(var), same_vars_of(Sg), superset_vars_of(Prime)} * nasub * ivar => asub(Succ)
   + (not_fails, is_det).

extend(_Sg, '$bottom', _Sv, _Call, '$bottom').  % TODO: optimize with cut
extend(_Sg, Prime, Sv, Call, Succ) :-
   match_sh(Prime, Sv, Call, Succ).

%-------------------------------------------------------------------------
% call_to_success_fact(+Sg,+Hv,+Head,+K,+Sv,+Call,+Proj,-Prime,-Succ)
%
% Specialized version of call_to_entry + entry_to_exit + exit_to_prime
% + extend for a fact Head.
%-------------------------------------------------------------------------

:- dom_impl(_, call_to_success_fact/9, [noq]).
:- pred call_to_success_fact(+Sg, +Hv, +Head, +K, +Sv, +Call, +Proj, -Prime, -Succ)
   : cgoal * {ordlist(var), same_vars_of(Head)} * cgoal * term *
      {ordlist(var), same_vars_of(Sg), superset_vars_of(Proj)} * nasub * nasub * ivar * ivar
   => ( nasub(Prime), nasub(Succ), superset_vars_of(Prime, Sv) )
   + (not_fails, is_det).

% TODO: Optimize, by avoiding the use call_to_entry and exit_to_prime
call_to_success_fact(Sg, Hv, Head, K, Sv, Call, Proj, Prime, Succ) :-
   call_to_entry(Sv, Sg, Hv, Head, K, [], Proj, Entry, ExtraInfo),
   exit_to_prime(Sg, Hv, Head, Sv, Entry, ExtraInfo, Prime),
   extend(Sg, Prime, Sv, Call, Succ).

%-------------------------------------------------------------------------
% special_builtin(+SgKey,+Sg,+Subgoal,-Type,-Condvars)
%
% Predicate Sg is considered a "builtin" of type Type. Types are
% domain dependent. The actual builtin is executed by body_succ_builtin,
% whose base implementation calls either success_builtin for usual types of
% builtins or call_to_success_builtin for particular predicates. The later is
% called when Type is of the form special(SgKey). Condvars is used to pass
% information to success_builtin.
%
% TODO: Understand the role of Subgoal.
%-------------------------------------------------------------------------

:- dom_impl(_, special_builtin/5, [noq]).
:- pred special_builtin(+SgKey, +Sg, +Subgoal, -Type, -Condvars)
   : {atm, predicate_of(Sg), predicate_of(Subgoal)} * cgoal * cgoal * ivar * ivar
   => (term(Type), term(Condvars))
   + is_det.

special_builtin('true/0', _, _, unchanged, _).
special_builtin('=/2', Sg, _ , '=/2', Sg).

%-------------------------------------------------------------------------
% success_builtin(+Type,+Sv,+Condvars,+HvFv_u,+Call,-Succ)
%
% Obtains the success for some particular builtins. Type and Condvars
% come from the special_builtin predicate.
%-------------------------------------------------------------------------

:- dom_impl(_, success_builtin/6, [noq]).
:- pred success_builtin(+Type,+Sv,?Condvars,+HvFv_u,+Call,-Succ)
   : term * ordlist(var) * term * list(var) * nasub * ivar => asub(Succ)
   + (not_fails, is_det).

success_builtin(unchanged, _ , _ , _, Call, Call).
success_builtin('=/2', _, T1=T2, _, Call, Result) :-
   unifiable(T1, T2,  Unifier),
   mgu_sh(Call, [], Unifier, Result).

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
% defined structure, see input_interface/4) on variables Qv.
%
% TODO: understand the role of Sg and MaybeCallASub.
%-------------------------------------------------------------------------

:- dom_impl(_, input_user_interface/5, [noq]).

% Struct may be free if a pred assertion is specified without call conditions.
:- pred input_user_interface(?Struct, +Qv, -ASub, +Sg, +MaybeCallASub)
   : term * {ordlist(var), same_vars_of(Sg)} * ivar * cgoal * term => asub(ASub)
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
% TODO: understand the role of OutFlag.
%-------------------------------------------------------------------------

:- dom_impl(_, asub_to_native/5, [noq]).
:- pred asub_to_native(+ASub, +Qv, +OutFlag, -NativeStat, -NativeComp)
   : asub * {ordlist(var), superset_vars_of(ASub)} * term * ivar * ivar
   + (is_det).

asub_to_native('$bottom', _Qv, _OutFlag, _NativeStat, _NativeComp) :- !, fail.
asub_to_native(ASub, Qv, _OutFlag, NativeStat, []) :-
   if_not_nil(ASub, sharing(ASub), NativeStat, NativeStat0),
   projected_gvars(ASub, Qv, Gv),
   if_not_nil(Gv, ground(Gv), NativeStat0, []).

%-------------------------------------------------------------------------
% unknown_call(+Sg,+Vars,+Call,-Succ)
%
% Succ is the result of adding to Call the ``topmost'' abstraction of the
% variables Vars involved in a literal Sg whose definition is not present
% in the preprocessing unit.
%
% It is a particular type of match where the abstract substitution on
% non-instantiable variables is the top of the domain.
%-------------------------------------------------------------------------

:- dom_impl(_, unknown_call/4, [noq]).
:- pred unknown_call(+Sg, +Vars, +Call, -Succ)
   : cgoal * {ordlist(var), same_vars_of(Sg)} * nasub * ivar => asub(Succ)
   + (not_fails, is_det).

% TODO: optimize adding the clause unknown_call(_Sg,_Vars,[],[])

% TODO: optimize using a custom implementation such as:
% unknown_call(Sg, Vars, Call, Succ) :-
%   rel(Call, Vars, Intersect, Disjunct),
%   star_union(Intersect, Star),
%   ord_union(Star, Disjunct, Succ).

unknown_call(Sg, Vars, Call, Succ) :-
   unknown_entry(Sg, Vars, Top),
   extend(Sg, Top, Vars, Call, Succ).

%------------------------------------------------------------------------%
% amgu(+Sg,+Head,+ASub,-AMGU)
%
% AMGU is the abstract unification between ASub and the unifiers of Sg and
% Head.
%
% TODO: understand which options enable the use of this predicate.
%------------------------------------------------------------------------%

:- dom_impl(_, amgu/4, [noq]).
:- pred amgu(+Sg, +Head, +ASub, -AMGU)
   : cgoal * cgoal * nasub * ivar => nasub(AMGU)
   + (not_fails, is_det).

amgu(Sg, Head, ASub, AMGU):-
   unifiable(Sg, Head, Unifier),
   mgu_sh(ASub, [], Unifier, AMGU).

%------------------------------------------------------------------------%
% glb(+ASub0,+ASub1,-GlbASub)
%
% GlbASub is the glb between ASub0 and ASub1.
%
% It is used to combine assertions provided by the user with trust
% predicates with the result of the analysis.
%------------------------------------------------------------------------%

:- dom_impl(_, glb/3, [noq]).
:- pred glb(+ASub0,+ASub1,-GlbASub)
   : asub * asub * ivar => asub(GlbASub)
   + (not_fails, is_det).

glb('$bottom', _ASub1, '$bottom') :- !.
glb(_ASub0, '$bottom', '$bottom'). % TODO: optimize with cut
glb(ASub0, ASub1, Glb):-
    ord_intersection(ASub0, ASub1, Glb).

%------------------------------------------------------------------------
% AUXILIARY ASSERTIONS
%-------------------------------------------------------------------------

:- prop asub_sh(Sh)
   # "@var{Sh} is a non-bottom sharing abstract substitution".
:- export(asub_sh/1).

% we do not explicitly encode the empty sharing set.
asub_sh(Sh)
  :- ordlist(ordnlist(var), Sh).

:- regtype asub_sh_u(Sh) #  "@var{ASub} is an unordered sharing abstract substitution".
:- export(asub_sh_u/1).

asub_sh_u(Sh) :-
   % note that list(ordlist(var)) would not work
   list(list(var), Sh).

%-------------------------------------------------------------------------
% AUXILIARY PREDICATES
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% project_sh(+Sh,+Vars,-Proj)
%
% Proj is the projection of Sh onto the variables in Vars.
%-------------------------------------------------------------------------

:- pred project_sh(+Sh, +Vars, -Proj)
   : asub_sh * ordlist(var) * ivar => asub_sh(Proj)
   + (not_fails, is_det).
:- export(project_sh/3).

project_sh([], _Vars, []).
project_sh([S|Rest], Vars, Sh_ex) :-
   ord_intersection(S, Vars, S_ex),
   project_sh(Rest, Vars, Rest_ex),
   ( S_ex = [] -> Sh_ex = Rest_ex ; insert(Rest_ex, S_ex, Sh_ex) ).

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

% TODO: optimize adding the clause projected_gvars([], Vars, Vars) :- !.
% TODO: optimize adding the clause projected_gvars(_ASub, [], []) :- !.
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
% bin(+Sh1, +Sh2, -Sh)
%
% Sh is the binary union of Sh1 and Sh2.
%-------------------------------------------------------------------------

:- pred bin(Sh1, Sh2, Sh)
   : asub_sh * asub_sh * ivar => asub_sh(Sh)
   + (not_fails, is_det).
:- export(bin/3).

bin([], _, []).
bin([X|Rest], Sh, Result) :-
   bin0(X, Sh, Sh_bin),
   bin(Rest, Sh, Rest_bin),
   ord_union(Rest_bin, Sh_bin, Result).

:- pred bin0(X, Sh2, Sh)
   : ordnlist(var) * asub_sh * ivar => asub_sh(Sh)
   + (not_fails, is_det).

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
% mgu_sh(+Sh, Fv, +Sub, -Sh_mgu)
%
% Sh_mgu is the result of the unification of Sh with the substitution Sub.
% Variables in Fv are considered to be free.
%-------------------------------------------------------------------------

:- pred mgu_sh(+Sh, +Fv, +Sub, -Sh_mgu)
   : asub_sh * ordlist(var) * unifier * ivar => asub_sh(Sh_mgu)
   + (not_fails, is_det).
:- export(mgu_sh/4).

% TODO: optimize by replacing Sub with a specialized version where terms are
% replaced by their variables

mgu_sh(Sh, Fv, Sub, Sh_mgu) :-
   ( current_pp_flag(mgu_sh_optimize, on) ->  mgu_sh0(Sh, Fv, Sub, Sh_mgu)
      ; mgu_sh0(Sh, [], Sub, Sh_mgu) ).

mgu_sh0(Sh, _Fv, [], Sh).
mgu_sh0(Sh, Fv, [X=T|Rest], Sh_mgu) :-
   mgu_sh_binding(Sh, X, T, Fv, Sh0, Fv0),
   mgu_sh0(Sh0, Fv0, Rest, Sh_mgu).

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
% UNUSED AUXILIARY PREDICATES
%-------------------------------------------------------------------------

:- pred aexists_sh(+Sh, +Vars, -Sh_ex)
   : asub_sh * ordlist(var) * ivar => asub_sh(Sh_ex)
   + (not_fails, is_det).

aexists_sh(Sh, Vars, Sh_ex) :-
   aexists_sh0(Sh, Vars, Sh_ex0),
   list_to_list_of_lists(Vars, Sh_ex1),
   ord_union(Sh_ex0, Sh_ex1, Sh_ex).

:- pred aexists_sh0(+Sh, +Vars, -Sh_ex)
   : asub_sh * ordlist(var) * ivar => asub_sh(Sh_ex)
   + (not_fails, is_det).

aexists_sh0([], _Vars, []) :- !.
aexists_sh0([S|Rest], Vars, Sh_ex) :-
   ord_subtract(S, Vars, S_ex),
   aexists_sh0(Rest, Vars, Rest_ex),
   ( S_ex = [] -> Sh_ex = Rest_ex ; insert(Rest_ex, S_ex, Sh_ex) ).
