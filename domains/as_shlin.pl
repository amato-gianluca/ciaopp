:- module(as_shlin, [], [assertions, regtypes, basicmodes, nativeprops]).

:- use_package(debug).
:- use_package(rtchecks).

:- doc(title, "sharing X linarity abstract domain").
:- doc(author, "Gianluca Amato").
:- doc(author, "Francesca Scozzari").

:- doc(module,"
This module is an independent reimplementation of the Sharing X Linearity domain.
").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(as_shlin, [default]).

:- use_module(library(lists)).
:- use_module(library(lsets)).
:- use_module(library(sets)).
:- use_module(library(terms_vars)).
:- use_module(library(iso_misc)).

:- use_module(domain(as_aux)).
:- use_module(domain(as_sharing)).
:- use_module(domain(sharing), [input_interface/4, input_user_interface/5]).

%:- use_module(engine(io_basic)).

%------------------------------------------------------------------------
% ASSERTIONS
%-------------------------------------------------------------------------

% the value $bottom has a special meaning withing the PLAI analyzer and MUST be
% used to represent unreachable states.

:- prop asub(ASub)
   # "@var{ASub} is an abstract substitution".

asub('$bottom'). % TODO: optimize with cut
asub(ASub) :-
   nasub(ASub).

:- prop nasub(ASub) # "@var{ASub} is a non empty abstract substitution".

nasub(ASub) :-
   asub_shlin(ASub).

:- prop asub_u(ASub) # "@var{ASub} is an unordered abstract substitution".

asub_u('$bottom'). % TODO: optimize with cut
asub_u(ASub) :-
   asub_shlin_u(ASub).

%------------------------------------------------------------------------
% FIXED CIAOPP PREDICATES
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

augment_asub(ASub, Vars, ASub0) :-
   augment_shlin(ASub, Vars, ASub0).

%-------------------------------------------------------------------------
% unknown_entry(+Sg,+Vars,-Entry)
%
% Entry is the "topmost" abstraction for the variable in  Vars
% appearing in the literal Sg.
%
% It is used when to call or entry predicate exists
%-------------------------------------------------------------------------

:- dom_impl(_, unknown_entry/3, [noq]).
:- pred unknown_entry(+Sg, +Vars, -Entry)
   : cgoal * {ordlist(var), same_vars_of(Sg)} * ivar => asub(Entry)
   + (not_fails, is_det).

unknown_entry(_Sg, Vars, Entry) :-
   top_shlin(Vars, Entry).

%-------------------------------------------------------------------------
% abs_sort(+ASub_u,-ASub)
%
% ASub is the result of sorting abstract substitution ASub_u.
%-------------------------------------------------------------------------

:- dom_impl(_, abs_sort/2, [noq]).
:- pred abs_sort(+ASub_u, -ASub)
   : asub_u * ivar => asub(ASub)
   + (not_fails, is_det).

abs_sort('$bottom', '$bottom') :- !.
abs_sort(ASub_u, ASub) :-
   sort_shlin(ASub_u, ASub).

%-------------------------------------------------------------------------
% project(Sg,Vars,HvFv_u,ASub,Proj)
%
% Projects the abstract substitution ASub onto the variables of list Vars,
% corresponding to goal Sg, resulting in the projected abstract
% substitution Proj. HvFv_u contains the unordered list of varibles of the
% clause.
%-------------------------------------------------------------------------

:- dom_impl(_, project/5, [noq]).
:- pred project(+Sg, +Vars, +HvFv_u, +ASub, ?Proj)
   : cgoal * {list(var), same_vars_of(Sg)} * list(var) * nasub * ivar => asub(Proj)
   + (not_fails, is_det).

project(_Sg, Vars, _HvFv_u, ASub, Proj) :-
   project_shlin(ASub, Vars, Proj).

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
   => (asub(Entry), unifier_no_cyclic(ExtraInfo))
   + (not_fails, is_det).

% save unifier in the ExtraInfo parameter, so that we can use it in exit_to_prime

call_to_entry(_Sv, Sg, Hv, Head, _ClauseKey, Fv, Proj, Entry, Unifier) :-
   unifiable_with_occurs_check(Sg, Head, Unifier),
   augment_shlin(Proj, Hv, ASub),
   mgu_shlin(ASub, Hv, Unifier, Entry0),
   project_shlin(Entry0, Hv, Entry1),
   augment_shlin(Entry1, Fv, Entry).

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
   : cgoal * {ordlist(var), same_vars_of(Head)} * cgoal * {ordlist(var), same_vars_of(Sg)} * asub * unifier_no_cyclic * ivar
   => (asub(Prime))
   + (not_fails, is_det).

% take the unifier from the ExtraInfo parameter

exit_to_prime(_Sg, _Hv, _Head, _Sv, '$bottom', _Unifier, '$bottom'). % TODO: optimize with cut
exit_to_prime(_Sg, _Hv, _Head, Sv, Exit, Unifier, Prime) :-
   augment_shlin(Exit, Sv, ASub),
   mgu_shlin(ASub, Sv, Unifier, Prime0),
   project_shlin(Prime0, Sv, Prime).

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
   lub_shlin(ASub1, ASub2, Lub).

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

extend(_Sg, '$bottom', _Sv, _Call, '$bottom').
extend(_Sg, Prime, Sv, Call, Succ) :-
   match_shlin(Prime, Sv, Call, Succ).

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
% Subgoal seems to be used when ciaopp is in transformation mode. Otherwise
% it is the same of Sg.
%
% TODO: Understand with more precision the role of Subgoal.
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
   unifiable_with_occurs_check(T1, T2,  Unifier),
   mgu_shlin(Call, [], Unifier, Result).

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
% TODO: optimize using a custom implementation

unknown_call(_Sg, Vars, Call, Succ) :-
   top_shlin(Vars, Top),
   match_shlin(Top, Vars, Call, Succ).

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
   unifiable_with_occurs_check(Sg, Head, Unifier),
   mgu_shlin(ASub, [], Unifier, AMGU).

%------------------------------------------------------------------------
% VARIABLE CIAOPP PREDICATES
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

input_interface(linear(X), perfect, (Sh,Lin0), (Sh,Lin)) :-
   ord_union(Lin0, X, Lin).
input_interface(free(X), perfect, (Sh,Lin0), (Sh,Lin)) :-
   var(X),
   insert(Lin0, X, Lin).
input_interface(Info, Kind, (Sh0,Lin), (Sh,Lin)) :-
   sharing:input_interface(Info, Kind, Sh0, Sh).

%-------------------------------------------------------------------------
% input_user_interface(?Struct,+Qv,-ASub,+Sg,+MaybeCallASub)
%
% ASub is the abstraction of the information collected in Struct (a domain
% defined structure, see input_interface/4) on variables Qv relative to
% the literal Sg.
%
% TODO: Understand the role of MaybeCallASub.
%-------------------------------------------------------------------------

:- dom_impl(_, input_user_interface/5, [noq]).

% Struct may be free if a pred assertion is specified without call conditions.
:- pred input_user_interface(?Struct, +Qv, -ASub, +Sg, +MaybeCallASub)
   : term * {ordlist(var), same_vars_of(Sg)} * ivar * cgoal * term => asub(ASub)
   + (not_fails, is_det).

input_user_interface((Sh, Lin), Qv, (ASub_sh,ASub_lin), Sg, MaybeCallASub):-
   sharing:input_user_interface(Sh, Qv, ASub_sh, Sg, MaybeCallASub),
   merge_list_of_lists(ASub_sh, Vsh),
   ord_intersection(Lin, Vsh, ASub_lin).

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
asub_to_native((Sh, Lin), Qv, _OutFlag, NativeStat, []) :-
   if_not_nil(Sh, sharing(Sh), NativeStat, NativeStat0),
   gvars(Sh, Qv, Gv),
   if_not_nil(Gv, ground(Gv), NativeStat0, NativeStat1),
   if_not_nil(Lin, linear(Lin), NativeStat1, []).

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
   glb_shlin(ASub0, ASub1, Glb).

%------------------------------------------------------------------------
% DOMAIN ASSERTIONS
%-------------------------------------------------------------------------

:- prop asub_shlin(ShLin)
   # "@var{ShLin} is a non-bottom sharing x linearity abstract substitution".
:- export(asub_shlin/1).

asub_shlin((Sh, Lin)) :-
   asub_sh(Sh),
   ordlist(var, Lin),
   % Lin only contains variables in Sh, since ground variables are linear by definition
   merge_list_of_lists(Sh, VSh),
   ord_subset(Lin, VSh).

:- regtype asub_shlin_u(ShLin) #  "@var{ShLin} is an unordered sharing x linearity abstract substitution".
:- export(asub_shlin_u/1).

asub_shlin_u((Sh, Lin)) :-
   asub_sh_u(Sh),
   list(var, Lin).

%-------------------------------------------------------------------------
% DOMAIN PREDICATES
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% sort_shlin(+ASub_u,-ASub)
%
% ASub is the result of sorting abstract substitution ASub_u.
%-------------------------------------------------------------------------

:- pred sort_shlin(+ASub_u, -ASub)
   : asub_shlin_u * ivar => asub_shlin(ASub)
   + (not_fails, is_det).
:- export(sort_shlin/2).

sort_shlin((Sh_u, Lin_u), (Sh, Lin)) :-
   sort_sh(Sh_u, Sh),
   sort(Lin_u, Lin).

%-------------------------------------------------------------------------
% top_shlin(+Vars,+Top)
%
% Top is the largest abstract substitution on variable Vars.
%-------------------------------------------------------------------------

:- pred top_shlin(+Vars, -Top)
   : ordlist(var) * ivar => asub_shlin(Top)
   + (not_fails, is_det).

top_shlin(Vars, (Sh, [])) :-
   top_sh(Vars, Sh).

%------------------------------------------------------------------------
% augment_shlin(+ASub,+Vars,-ASub0)
%
% Augment the abstract substitution ASub adding the fresh variables Vars
% to get the abstract substitution ASub0.
%-------------------------------------------------------------------------

:- pred augment_shlin(+ASub, +Vars, -ASub0)
   : (asub_shlin * {ordlist(var), independent_from(ASub)} * ivar) => asub_shlin(ASub0)
   + (not_fails, is_det).
:- export(augment_shlin/3).

% TODO: optimize with clause augment_shlin(ASub,[],ASub).
augment_shlin((Sh, Lin), Vars, (Sh0, Lin0)) :-
   augment_sh(Sh, Vars, Sh0),
   ord_union(Lin, Vars, Lin0).

%-------------------------------------------------------------------------
% project_shlin(+ShLin,+Vars,-Proj)
%
% Proj is the projection of ShLin onto the variables in Vars.
%-------------------------------------------------------------------------

:- pred project_shlin(+ShLin, +Vars, -Proj)
   : asub_shlin * ordlist(var) * ivar => asub_shlin(Proj)
   + (not_fails, is_det).
:- export(project_shlin/3).

project_shlin((Sh, Lin), Vars, (Proj_sh, Proj_lin)) :-
   project_sh(Sh, Vars, Proj_sh),
   ord_intersection(Lin, Vars, Proj_lin).

%-------------------------------------------------------------------------
% lub_shlin(+ASub1,+Asub2,Lub)
%
% Lub is the lub of ASub1 and ASub2.
%-------------------------------------------------------------------------

:- pred lub_shlin(+ASub1, +ASub2, -Lub)
   : asub_shlin * asub_shlin * ivar => asub_shlin(Lub)
   + (not_fails, is_det).
:- export(lub_shlin/3).

lub_shlin((Sh1, Lin1), (Sh2, Lin2), (Lub_sh, Lub_lin)) :-
   lub_sh(Sh1, Sh2, Lub_sh),
   ord_intersection(Lin1, Lin2, Lub_lin).


%------------------------------------------------------------------------%
% glb_shlin(+ASub1,+ASub2,-Glb)
%
% Glb is the glb between ASub1 and ASub2.
%------------------------------------------------------------------------%

:- pred glb_shlin(+ASub1,+ASub2,-Glb)
   : asub_shlin * asub_shlin * ivar => asub_shlin(Glb)
   + (not_fails, is_det).
:- export(glb_shlin/3).

glb_shlin((Sh1, Lin1), (Sh2, Lin2), (Glb_sh, Glb_lin)):-
   glb_sh(Sh1, Sh2, Glb_sh),
   ord_union(Lin1, Lin2, Glb_lin).

%-------------------------------------------------------------------------
% mgu_shlin(+ASub, Fv, +Sub, -MGU)
%
% MGU is the result of the unification of ASub with the substitution
% Sub. Variables in Fv are considered to be free (but this does not help
% the precision of the analysis).
%-------------------------------------------------------------------------

:- pred mgu_shlin(+ASub, +Fv, +Sub, -MGU)
   : asub_shlin * ordlist(var) * unifier_no_cyclic * ivar => asub_shlin(MGU)
   + (not_fails, is_det).

mgu_shlin(ASub, _Fv, [], ASub).
mgu_shlin(ASub, Fv, [X=T|Rest], MGU) :-
   mgu_shlin_binding(ASub, X, T, ASub0),
   mgu_shlin(ASub0, Fv, Rest, MGU).

:- pred mgu_shlin_binding(+Sh, ?Vars_x, ?Vars_t, MGU)
   : nasub * var * term * ivar => nasub(MGU)
   + (not_fails, is_det).

mgu_shlin_binding(ShLin, X, T, (MGU_sh, MGU_lin)) :-
   ShLin = (Sh, Lin),
   varset(X, Vx),
   varset(T, Vt),
   rel(Sh, Vx, Rx, Rx_neg),
   rel(Sh, Vt, Rt, Rt_neg),
   varset(Rx, Vrx),
   varset(Rt, Vrt),
   ord_intersection(Rx_neg, Rt_neg, Rel_neg),
   (ind(Sh, X, T) -> Ind = yes ; Ind = no),
   (lin(ShLin, T) -> Lint = yes ; Lint = no),
   (lin(ShLin, X) -> Linx = yes ; Linx = no),
   (Lint=yes, Ind=yes -> Sx = Rx ; star_union(Rx, Sx)),
   (Linx=yes, Ind=yes -> St = Rt ; star_union(Rt, St)),
   bin(Sx, St, Sxt),
   ord_union(Rel_neg, Sxt, MGU_sh),
   (
   Linx = yes, Lint = yes ->
      ord_intersection(Vrx, Vrt, Vrtx),
      ord_subtract(Lin, Vrtx, Lin0)
   ; Linx = yes ->
      ord_subtract(Lin, Vrx, Lin0)
   ; Lint = yes ->
      ord_subtract(Lin, Vrt, Lin0)
   ;
      ord_union(Vrx, Vrt, Vrtx),
      ord_subtract(Lin, Vrtx, Lin0)
   ),
   merge_list_of_lists(MGU_sh, Vsh),
   ord_intersection(Vsh, Lin0, MGU_lin).

%-------------------------------------------------------------------------
% match_shlin(+ASub1, +Sv1, +ASub2, -Match)
%
% Match is the abstract matching between ASub1 (over the variables in Sv1)
% and ASub2, where ASub1 is the abstract substitution which should not be
% further instantiated.
%
% With respect to the general definition of matching, we only consider
% the special case in which the variables in ASub2 (not even provided in
% input) are a superset of Sv1.
%-------------------------------------------------------------------------

:- pred match_shlin(+ASub1,+Sv1,_ASub2,-Match)
   : nasub * {ordlist(var), superset_vars_of(ASub1)} * nasub * ivar => nasub(Match)
   + (not_fails, is_det).

match_shlin((Prime_sh, Prime_lin), Sv1, (Call_sh, Call_lin), (Succ_sh, Succ_lin)) :-
   match_sh(Prime_sh, Sv1, Call_sh, Succ_sh), % we do not use linearity here
   ord_subtract(Call_lin, Sv1, Call_lin_noprime),
   merge_list_of_lists(Prime_sh, Prime_noground),
   ord_subtract(Prime_noground, Prime_lin, Prime_nonlin),
   rel(Call_sh, Prime_nonlin, Call_sh_rel_nonlin, _),
   merge_list_of_lists(Call_sh_rel_nonlin, Call_nonprime),
   ord_subtract(Call_lin_noprime, Call_nonprime, Lin1),
   ord_union(Prime_lin, Lin1, Lin2),
   merge_list_of_lists(Succ_sh, Succ_noground),
   ord_intersection(Lin2, Succ_noground, Succ_lin).

%-------------------------------------------------------------------------
% AUXILIARY PREDICATES
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% independent(+Sh, ?S, ?T)
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
% lin(+ShLin, ?T)
%
% Determines whether the term T is definitvely linear with respect to
% the sharing and linearity information in ShLin.
%-------------------------------------------------------------------------

:- pred lin(+ShLin, ?T)
   : asub_shlin * term
   + is_det.

:- export(lin/2).
lin((Sh, Lin), T) :-
   varset(T, Vt),
   varset(Sh, Vsh),
   ord_subtract(Vsh, Lin, NoLin),
   ord_disjoint(Vt, NoLin),
   all_couples(Vt, ind(Sh)),
   varsbag(T, Bag, []),
   duplicates(Bag, Duplicates),
   ord_disjoint(Duplicates, Vsh).
