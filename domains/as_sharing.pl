:- module(as_sharing, [], [assertions, regtypes, basicmodes, nativeprops]).

%:- use_package(trace).
:- use_package(rtchecks).

:- doc(title, "sharing abstract domain").
:- doc(author, "Gianluca Amato").
:- doc(author, "Francesca Scozzari").

:- doc(module,"
This module is an independent reimplementation of the Sharing domain.
").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(as_sharing, [default]).

:- use_module(library(lists)).
:- use_module(library(lsets)).
:- use_module(library(sets)).
:- use_module(library(terms_check)).
:- use_module(library(terms_vars)).

:- use_module(domain(as_aux)).
:- use_module(domain(as_sharing_aux)).
:- use_module(domain(sharing), [input_interface/4, input_user_interface/5]).

%:- use_module(engine(io_basic)).

%------------------------------------------------------------------------
% ASSERTIONS
%-------------------------------------------------------------------------

:- prop asub(ASub) # "@var{ASub} is an abstract substitution".
:- export(asub/1).

% the value $bottom has a special meaning withing the PLAI analyzer and MUST be
% used to represent unreachable states.

asub('$bottom'). % TODO: optimize with cut
asub(ASub) :-
   nasub(ASub).

:- prop nasub(ASub) # "@var{ASub} is a non empty abstract substitution".

nasub(ASub) :-
   asub_sh(ASub).

:- prop asub_u(ASub) # "@var{ASub} is an unordered abstract substitution".

asub_u('$bottom'). % TODO: optimize with cut
asub_u(ASub) :-
   asub_sh_u(ASub).

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
   : cgoal * {list(var), same_vars_of(Sg)} * list(var) * asub * ivar => asub(Proj)
   + (not_fails, is_det).

% the following lines are probably needed for builtins
% project(_Sg, _Vars, _HvFv_u, '$bottom', '$bottom') :- !.

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
         term * {ordlist(var), independent_from(Hv)} * asub_sh * ivar * ivar
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

compute_lub([ASub], ASub) :- !.
compute_lub([ASub1,ASub2|ASubs], LubASub) :-
   compute_lub_el(ASub1, ASub2, ASub3),
   compute_lub([ASub3|ASubs], LubASub).

:- pred compute_lub(+ASub1, +ASub2, -ASub)
   : asub * asub * ivar => asub(ASub)
   + (not_fails, is_det).

compute_lub_el('$bottom', ASub, ASub) :- !.
compute_lub_el(ASub, '$bottom', ASub).% TODO: optimize with cut
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
   : cgoal * asub * {ordlist(var), same_vars_of(Sg), superset_vars_of(Prime)} * asub_sh * ivar => asub(Succ)
   + (not_fails, is_det).

extend(_Sg, '$bottom', _Sv, _Call, '$bottom') :- !.
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
      {ordlist(var), same_vars_of(Sg), superset_vars_of(Proj)} * asub_sh * asub_sh * ivar * ivar
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
   : term * ordlist(var) * term * list(var) * asub_sh * ivar => asub(Succ)
   + (not_fails, is_det).

success_builtin(unchanged, _ , _ , _, Call, Call).
success_builtin('=/2', _, T1=T2, _, Call, Result) :-
   unifiable(T1, T2,  Unifier),
   mgu_sh(Call, [], Unifier, Result).

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
   sharing:input_user_interface(Struct, Qv, ASub, Sg, MaybeCallASub).

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
asub_to_native(ASub, Qv, _OutFlag, NativeStat, []) :-
   if_not_nil(ASub, sharing(ASub), NativeStat, NativeStat0),
   projected_gvars(ASub, Qv, Gv),
   if_not_nil(Gv, ground(Gv), NativeStat0, []).

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
   : cgoal * {ordlist(var), same_vars_of(Sg)} * asub_sh * ivar => asub(Succ)
   + (not_fails, is_det).

% TODO: optimize adding the clause unknown_call(_Sg,_Vars,[],[])
% TODO: I don't think this is correct
unknown_call(_Sg, Vars, Call, Succ) :-
   rel(Call, Vars, Intersect, Disjunct),
   star_union(Intersect, Star),
   ord_union(Star, Disjunct, Succ).

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
   : cgoal * cgoal * asub_sh * ivar => nasub(AMGU)
   + (not_fails, is_det).

amgu(Sg, Head, ASub, AMGU):-
   unifiable(Sg, Head, Unifier),
   mgu_sh(ASub, [], Unifier, AMGU).
