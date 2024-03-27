:- doc(author, "Gianluca Amato").
:- doc(author, "Francesca Scozzari").

:- set_prolog_flag(multi_arity_warnings, off).

:- use_module(ciaopp(preprocess_flags)).

:- use_module(library(lists)).
:- use_module(library(sets)).
:- use_module(library(lsets)).
:- use_module(library(terms_vars)).

:- use_module(domain(as_aux)).

:- use_module(domain(sharing), [input_interface/4, input_user_interface/5]).

%------------------------------------------------------------------------
% FIXED ASSERTIONS
%-------------------------------------------------------------------------

% the value $bottom has a special meaning withing the PLAI analyzer and MUST be
% used to represent unreachable states.

:- prop asub(ASub)
   # "@var{ASub} is an abstract substitution".

asub('$bottom') :- !.
asub(ASub) :-
   nasub(ASub).

:- prop asub_u(ASub) # "@var{ASub} is an unordered abstract substitution".

asub_u('$bottom') :- !.
asub_u(ASub) :-
   nasub_u(ASub).

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
   augment(ASub, Vars, ASub0).

%-------------------------------------------------------------------------
% unknown_entry(+Sg,+Vars,-Entry)
%
% Entry is the "topmost" abstraction for the variable in  Vars
% appearing in the literal Sg.
%
% It is used when no call or entry assertion exists
%-------------------------------------------------------------------------

:- dom_impl(_, unknown_entry/3, [noq]).
:- pred unknown_entry(+Sg, +Vars, -Entry)
   : cgoal * {ordlist(var), same_vars_of(Sg)} * ivar => asub(Entry)
   + (not_fails, is_det).

unknown_entry(_Sg, Vars, Entry) :-
   top(Vars, Entry).

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
   normalize(ASub_u, ASub).

%-------------------------------------------------------------------------
% project(Sg,Vars,HvFv_u,ASub,Proj)
%
% Projects the abstract substitution ASub onto the variables of list Vars,
% corresponding to goal Sg, resulting in the projected abstract
% substitution Proj. HvFv_u contains the unordered list of variables of the
% clause.
%-------------------------------------------------------------------------

:- dom_impl(_, project/5, [noq]).
:- pred project(+Sg, +Vars, +HvFv_u, +ASub, ?Proj)
   : cgoal * {list(var), same_vars_of(Sg)} * list(var) * nasub * ivar => asub(Proj)
   + (not_fails, is_det).

project(_Sg, Vars, _HvFv_u, ASub, Proj) :-
   project(ASub, Vars, Proj).

%-------------------------------------------------------------------------
% call_to_entry(+Sv,+Sg,Hv,+Head,+ClauseKey,+Fv,+Proj,-Entry,-ExtraInfo)
%
% Obtains the abstract substitution Entry which results from adding the
% abstraction of the unification Sg = Head to abstract substitution Proj
% (the call substitution for Sg projected on its variables Sv) and then
% projecting the resulting substitution onto Hv (the variables of Head)
% plus Fv (the free variables of the relevant clause). ExtraInfo is
% information which can be reused during the exit_to_prime step. Finally,
% ClauseKey is the identifier of the clause under consideration.
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
   augment(Proj, Hv, ASub),
   mgu(ASub, Hv, Unifier, Entry0),
   project(Entry0, Hv, Entry1),
   augment(Entry1, Fv, Entry).

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

exit_to_prime(_Sg, _Hv, _Head, _Sv, '$bottom', _Unifier, '$bottom') :- !.
exit_to_prime(_Sg, _Hv, _Head, Sv, Exit, Unifier, Prime) :-
   augment(Exit, Sv, ASub),
   mgu(ASub, Sv, Unifier, Prime0),
   project(Prime0, Sv, Prime).

%-------------------------------------------------------------------------
% compute_lub(+ListASub,-LubASub)
%
% LubASub is the least upper bound of the abstract substitutions in
% non-empty list ListASub.
%-------------------------------------------------------------------------

:- dom_impl(_, compute_lub/2, [noq]).
:- pred compute_lub(+ListASub, -LubASub)
   : list(asub) * ivar => asub(LubASub)
   + (not_fails, is_det).

compute_lub([ASub], ASub).
compute_lub([ASub1,ASub2|ASubs], LubASub) :-
   compute_lub_el(ASub1, ASub2, ASub3),
   compute_lub([ASub3|ASubs], LubASub).

:- pred compute_lub(+ASub1, +ASub2, -Lub)
   : asub * asub * ivar => asub(Lub)
   + (not_fails, is_det).

compute_lub_el('$bottom', ASub, ASub) :- !.
compute_lub_el(ASub, '$bottom', ASub) :- !.
compute_lub_el(ASub1, ASub2, Lub) :-
   join(ASub1, ASub2, Lub).

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
   match(Prime, Sv, Call, Succ).

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

call_to_success_fact(Sg, Hv, Head, _K, Sv, Call, _Proj, Prime, Succ) :-
   unifiable_with_occurs_check(Sg, Head, Unifier),
   augment(Call, Hv, Call0),
   mgu(Call0, Hv, Unifier, Succ0),
   varset(Call, Vcall),
   project(Succ0, Sv, Prime),
   project(Succ0, Vcall, Succ).

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
   : {atm, predicate_of(Sg)} * cgoal * cgoal * ivar * ivar
   => (term(Type), term(Condvars))
   + is_det.

special_builtin('true/0', _, _, unchanged, _).
special_builtin('=/2', Sg, _ , '=/2', Sg).

%-------------------------------------------------------------------------
% success_builtin(+Type,+Sv,?Condvars,+HvFv_u,+Call,-Succ)
%
% Obtains the success substitution for given builtins. Type and Condvars
% come from the special_builtin predicate. Sv is the set of variable in
% the builtin and HvFv_u is the set of all clause variables.
%-------------------------------------------------------------------------

:- dom_impl(_, success_builtin/6, [noq]).
:- pred success_builtin(+Type,+Sv,?Condvars,+HvFv_u,+Call,-Succ)
   : term * ordlist(var) * term * list(var) * nasub * ivar => asub(Succ)
   + (not_fails, is_det).

success_builtin(unchanged, _ , _ , _, Call, Call).
success_builtin('=/2', _, T1=T2, _, Call, Result) :-
   unifiable_with_occurs_check(T1, T2,  Unifier),
   mgu(Call, [], Unifier, Result).

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

% TODO: Optimize using a custom implementation

unknown_call(_Sg, Vars, Call, Succ) :-
   top(Vars, Top),
   match(Top, Vars, Call, Succ).

%------------------------------------------------------------------------%
% amgu(+Sg,+Head,+ASub,-AMGU)
%
% AMGU is the abstract unification between ASub and the unifiers of Sg and
% Head.
%
% TODO: Understand which are the options which enable the use of this
% predicate.
%------------------------------------------------------------------------%

:- dom_impl(_, amgu/4, [noq]).
:- pred amgu(+Sg, +Head, +ASub, -AMGU)
   : cgoal * cgoal * nasub * ivar => nasub(AMGU)
   + (not_fails, is_det).

amgu(Sg, Head, ASub, AMGU):-
   unifiable_with_occurs_check(Sg, Head, Unifier),
   mgu(ASub, [], Unifier, AMGU).

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
   : asub * asub * ivar => asub(GlbAsub).
   + (not_fails, is_det).

glb('$bottom', _ASub1, '$bottom') :- !.
glb(_ASub0, '$bottom', '$bottom') :- !.
glb(ASub0, ASub1, Glb):-
   meet(ASub0, ASub1, Glb).

%------------------------------------------------------------------------
% FIXED DECLARATIONS
%-------------------------------------------------------------------------

:- export(nasub/1).
:- export(nasub_u/1).
:- export(normalize/2).
:- export(top/2).
:- export(augment/3).
:- export(project/3).
:- export(join/3).
:- export(meet/3).
:- export(mgu/4).
:- export(match/4).

:- redefining(nasub/1).
:- redefining(nasub_u/1).
:- redefining(normalize/2).
:- redefining(top/2).
:- redefining(augment/3).
:- redefining(project/3).
:- redefining(join/3).
:- redefining(meet/3).
:- redefining(mgu/4).
:- redefining(match/4).
:- redefining(vars/2).
:- redefining(linvars/2).
:- redefining(groundvars/2).
:- redefining(bin/3).
