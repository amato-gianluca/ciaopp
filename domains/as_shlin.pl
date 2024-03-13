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
:- use_module(library(terms_check)).
:- use_module(library(terms_vars)).
:- use_module(library(iso_misc)).

:- use_module(domain(as_aux)).
:- use_module(domain(as_sharing_aux)).
:- use_module(domain(sharing), [input_interface/4, input_user_interface/5]).

:- use_module(engine(io_basic)).

%------------------------------------------------------------------------
% ASSERTIONS
%-------------------------------------------------------------------------

:- prop asub(ASub) # "@var{ASub} is an abstract substitution".

% the value $bottom has a special meaning withing the PLAI analyzer and MUST be
% used to represent unreachable states.

asub('$bottom'). % TODO: optimize with cut
asub(ASub) :-
   nasub(ASub).

:- prop nasub(ASub) # "@var{ASub} is a non empty abstract substitution".

% in the lin component we do not keep the ground variables, since they are
% automatically linear.

nasub((Sh, Lin)) :-
   asub_sh(Sh),
   ordlist(var, Lin).
   % varset(Lin, VLin),
   % varset(Sh, VSh),
   % ord_subset(VLin, VSh).

:- prop asub_u(ASub) # "@var{ASub} is an unordered abstract substitution".

asub_u('$bottom'). % TODO: optimize with cut
asub_u((Sh, Lin)) :-
   asub_sh_u(Sh),
   list(var, Lin).

%------------------------------------------------------------------------
% DOMAIN OPERATIONS
%-------------------------------------------------------------------------

%------------------------------------------------------------------------
% augment_asub(+ASub,+Vars,-ASub0)
%
% Augment the abstract substitution ASub adding the fresh variables Vars
% to get the abstract substitution ASub0.
%-------------------------------------------------------------------------

:- dom_impl(_, augment_asub/3, [noq]).
:- pred augment_asub(+ASub, +Vars, -ASub0)
   : (asub * {ordlist(var), independent_from(ASub)} * ivar) => asub(ASub0)
   + (not_fails, is_det).

% TODO: optimize with clause augment_asub(ASub,[],ASub).
augment_asub((Sh, Lin), Vars, (Sh0, Lin0)) :-
   list_to_list_of_lists(Vars, Vars0),
   ord_union(Sh, Vars0, Sh0),
   ord_union(Lin, Vars, Lin0).

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

unknown_entry(_Sg, Vars, (Sh, Lin)) :-
   % note that powerset does not generate the empty set
   powerset(Vars, Sh),
   Lin = [].

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
abs_sort((Sh_u, Lin_u), (Sh, Lin)) :-
   sort_list_of_lists(Sh_u, Sh),
   sort(Lin_u, Lin).

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
   : cgoal * {list(var), same_vars_of(Sg)} * list(var) * asub * ivar => asub(Proj)
   + (not_fails, is_det).

% the following lines are probably needed for builtins
% project(_Sg, _Vars, _HvFv_u, '$bottom', '$bottom') :- !.

project(_Sg, Vars, _HvFv_u, (Sh, Lin), (Proj_sh, Proj_lin)) :-
   project_sh(Sh, Vars, Proj_sh),
   ord_intersection(Lin, Vars, Proj_lin).

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
   mgu_shlin(ASub, Hv, Unifier, Entry0),
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
   mgu_shlin(ASub, Sv, Unifier, Prime0),
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

compute_lub([ASub], ASub) :- !.
compute_lub([ASub1,ASub2|ASubs], LubASub) :-
   compute_lub_el(ASub1, ASub2, ASub3),
   compute_lub([ASub3|ASubs], LubASub).

:- pred compute_lub(+ASub1, +ASub2, -ASub)
   : asub * asub * ivar => asub(ASub)
   + (not_fails, is_det).

compute_lub_el('$bottom', ASub, ASub). % TODO: optimize with cut
compute_lub_el(ASub, '$bottom', ASub).% TODO: optimize with cut
compute_lub_el((Sh1, Lin1), (Sh2, Lin2), (Lub_sh, Lub_lin)) :-
   ord_union(Sh1, Sh2, Lub_sh),
   ord_union(Lin1, Lin2, Lub_lin).

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

extend(_Sg, '$bottom', _Sv, _Call, '$bottom') :- !.
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
% TODO: Understand the role of Sg, Subgoal and Condvars.
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
   mgu_shlin(Call, [], Unifier, Result).

%-------------------------------------------------------------------------
% input_interface(+Prop,+Kind,?Struc0,-Struc1)
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
:- pred input_interface(+Prop, -Kind, ?Struc0, -Struc1)
   : term * ivar * term * ivar => (atm(Kind), term(Struc0), term(Struc1)).

input_interface(Prop, Kind, Struc0, Struc1) :-
   sharing:input_interface(Prop, Kind, Struc0, Struc1).

%-------------------------------------------------------------------------
% input_user_interface(?Struct,+Qv,-ASub,+Sg,+MaybeCallASub)
%
% ASub is the abstraction of the information collected in Struct (a domain
% defined structure, see input_interface/4) on variables Qv.
%
% TODO: understand the role of Sg and MaybeCallASub
%-------------------------------------------------------------------------

:- dom_impl(_, input_user_interface/5, [noq]).

% Struct may be free if a pred assertion is specified without call conditions.
:- pred input_user_interface(?Struct, +Qv, -ASub, +Sg, +MaybeCallASub)
   : term * {ordlist(var), same_vars_of(Sg)} * ivar * cgoal * term => asub(ASub)
   + (not_fails, is_det).

input_user_interface(Struct, Qv, ASub, Sg, MaybeCallASub) :-
   sharing:input_user_interface(Struct, Qv, Sh, Sg, MaybeCallASub),
   ASub = (Sh, []).

%-------------------------------------------------------------------------
% asub_to_native(+ASub,+Qv,+OutFlag,-NativeStat,-NativeComp)
%
% NativeStat and NativeComp are the list of native (state and
% computational, resp.) properties that are the concretization of abstract
% of abstract substitution ASub on variables Qv. These are later
% translated to the properties which are visible in the preprocessing unit.
%
% TODO: understand the role of OutFlag
%-------------------------------------------------------------------------

:- dom_impl(_, asub_to_native/5, [noq]).
:- pred asub_to_native(+ASub, +Qv, +OutFlag, -NativeStat, -NativeComp)
   : asub * {ordlist(var), superset_vars_of(ASub)} * term * ivar * ivar
   + (is_det).

asub_to_native('$bottom', _Qv, _OutFlag, _NativeStat, _NativeComp) :- !, fail.
asub_to_native((Sh, Lin), Qv, _OutFlag, NativeStat, []) :-
   if_not_nil(Sh, sharing(Sh), NativeStat, NativeStat0),
   projected_gvars(Sh, Qv, Gv),
   if_not_nil(Gv, ground(Gv), NativeStat0, NativeStat1),
   if_not_nil(Lin, linearity(Lin), NativeStat1, []).

%-------------------------------------------------------------------------
% unknown_call(+Sg,+Vars,+Call,-Succ)
%
% Succ is the result of adding to Call the ``topmost'' abstraction of the
% variables Vars involved in a literal Sg whose definition is not present
% in the preprocessing unit. I.e., it is like the conjunction of the
% information in Call with the top for a subset of its variables.
%-------------------------------------------------------------------------

:- dom_impl(_, unknown_call/4, [noq]).
:- pred unknown_call(+Sg, +Vars, +Call, -Succ)
   : cgoal * {ordlist(var), same_vars_of(Sg)} * nasub * ivar => asub(Succ)
   + (not_fails, is_det).

% TODO: optimize adding the clause unknown_call(_Sg,_Vars,[],[])
% TODO: I don't think this is correct
unknown_call(_Sg, Vars, (Call_sh, Call_lin), (Succ_sh, Succ_lin)) :-
   rel(Call_sh, Vars, Intersect, Disjunct),
   star_union(Intersect, Star),
   ord_union(Star, Disjunct, Succ_sh),
   ord_intersection(Call_lin, Vars, Succ_lin).

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
   mgu_shlin(ASub, [], Unifier, AMGU).

%-------------------------------------------------------------------------
% mgu_shlin(+ASub, Fv, +Sub, -MGU)
%
% MGU is the result of the unification of ASub with the substitution
% Sub. Variables in Fv are considered to be free (but this does not help
% the precision of the analysis).
%-------------------------------------------------------------------------

:- pred mgu_shlin(+ASub, +Fv, +Sub, -MGU)
   : nasub * ordlist(var) * unifier * ivar => nasub(MGU)
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
   (Linx = yes, Lint = yes ->
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
   MGU_lin = Lin0.

%-------------------------------------------------------------------------
% match_shlin(+ASub1, +Sv1, +ASub2, -Match)
%
% Match is the abstract matching between ASuv1 (over the variables in Sv1)
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

match_shlin(ASub1, _Sv1, _ASub2, ASub1).

%------------------------------------------------------------------------
% AUXILIARY OPERATIONS
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% lin(+ShLin, T)
%
% Determines whether the term T is definitvely linear with respect to
% the sharing and linearity information in ShLin.
%-------------------------------------------------------------------------

:- pred lin(+ShLin, ?T)
   : asub * term
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
