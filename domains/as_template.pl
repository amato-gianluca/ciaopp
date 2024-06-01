:- doc(author, "Gianluca Amato").
:- doc(author, "Francesca Scozzari").

:- set_prolog_flag(multi_arity_warnings, off).

:- use_module(ciaopp(preprocess_flags)).

:- use_module(library(lists)).
:- use_module(library(sets)).
:- use_module(library(lsets)).
:- use_module(library(terms_vars)).
:- use_module(library(format)).

:- use_module(domain(as_aux)).
:- use_module(domain(as_bags)).

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
% It is used when no call or entry assertion exists.
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
% ASub is the result of sorting abstract substitution ASub_u. This
% is needed when variables get renamed by internal PLAI mechanisms.
% Due to renaming, ordered structures might not be ordered anymore
% and need to be sorted.
%-------------------------------------------------------------------------

:- dom_impl(_, abs_sort/2, [noq]).
:- pred abs_sort(+ASub_u, -ASub)
   : asub_u * ivar => asub(ASub)
   + (not_fails, is_det).

abs_sort('$bottom', '$bottom') :- !.
abs_sort(ASub_u, ASub) :-
   reorder(ASub_u, ASub).

%-------------------------------------------------------------------------
% project(Sg,Vars,HvFv_u,ASub,Proj)
%
% Projects the abstract substitution ASub onto the variables of list Vars,
% corresponding to goal Sg, resulting in the projected abstract
% substitution Proj. HvFv_u contains the unordered list of variables of the
% clause.
%
% The only cases when the variables is Sg are a proper superset of the
% variables in Vars seem to be related to dynamic predicates.
%-------------------------------------------------------------------------

:- dom_impl(_, project/5, [noq]).
:- pred project(+Sg, +Vars, +HvFv_u, +ASub, ?Proj)
   : {cgoal, superset_vars_of(Vars)} * list(var) * list(var) * asub * ivar => asub(Proj)
   + (not_fails, is_det).

% The '$bottom' case seems to only occur when using the builtin 'fail/0'.
project(_,_,_,'$bottom','$bottom') :- !.
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
   => (asub(Entry))
   + (not_fails, is_det).

% In the ExtraInfo parameter put both the Unifier (used when extend_implementation is mgu to increase performance)
% and the entry substitution (used when extend_implementation is match to increase precision).

call_to_entry(_Sv, Sg, Hv, Head, _ClauseKey, Fv, Proj, Entry, (Unifier, Entry0)) :-
   unifiable_with_occurs_check(Sg, Head, Unifier),
   augment(Proj, Hv, ASub),
   mgu(ASub, Hv, Unifier, Entry0),
   project(Entry0, Hv, Entry1),
   augment(Entry1, Fv, Entry).

%-------------------------------------------------------------------------
% exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)
%
% Computes the abstract substitution Prime which results from adding the
% abstraction of the unification Sg = Head to the abstract substitution Exit
% (the exit substitution over all variables of the clause), projecting the
% resulting substitution onto Sv.
%
% ExtraInfo is the information saved during the call_to_entry step. Sv
% and Hv are the variables of Sg and Head, respectively.
%-------------------------------------------------------------------------

:- dom_impl(_, exit_to_prime/7, [noq]).
:- pred exit_to_prime(+Sg, +Hv, +Head, +Sv, +Exit, +ExtraInfo, -Prime)
   : cgoal * {ordlist(var), same_vars_of(Head)} * cgoal * {ordlist(var), same_vars_of(Sg)} * asub * term * ivar
   => (asub(Prime))
   + (not_fails, is_det).

% I ExtraInfo parameter

exit_to_prime(_Sg, _Hv, _Head, _Sv, '$bottom', _ExtraInfo, '$bottom') :- !.
exit_to_prime(_Sg, Hv, _Head, Sv, Exit, (Unifier, Entry0), Prime) :-
   project(Exit, Hv, Exit0),
   (
      current_pp_flag(as_use_match, no) ->
         augment(Exit0, Sv, ASub),
         mgu(ASub, Sv, Unifier, Prime0)
      ;
         match(Exit0, Hv, Entry0, Prime0)
   ),
   project(Prime0, Sv, Prime).

%-------------------------------------------------------------------------
% compute_lub(+ListASub,-LubASub)
%
% LubASub is the least upper bound of the abstract substitutions in the
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
%
% The only cases when the variables is Sg are a proper superset of the
% variables in Sv seem to be related to dynamic predicates.
%-------------------------------------------------------------------------

:- dom_impl(_, extend/5, [noq]).
:- pred extend(+Sg,+Prime,+Sv,+Call,-Succ)
   : {cgoal,  superset_vars_of(Sv)} * asub * {ordlist(var), superset_vars_of(Prime)} * nasub * ivar => asub(Succ)
   + (not_fails, is_det).

extend(_Sg, '$bottom', _Sv, _Call, '$bottom') :- !.
extend(_Sg, Prime, Sv, Call, Succ) :-
   (
      current_pp_flag(as_use_match, no) ->
         % TODO: replace varset with a more efficient implementation
         varset(Call, Vars),
         copy_term_nat((Sv, Prime), (Sv0, Prime0)),
         build_unifier(Sv, Sv0, MGU),
         %abs_sort(Prime0, Prime1),
         join(Prime0, Call, CallExtended),
         mgu(CallExtended, [], MGU, Succ0),
         project(Succ0, Vars, Succ)
      ;
         match(Prime, Sv, Call, Succ)
   ).

build_unifier([], [], []).
build_unifier([V|Rest], [V0|Rest0], [V=V0|RestMGU]) :-
   build_unifier(Rest, Rest0, RestMGU).

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

% special_builtin(SgKey, Sg, Subgoal, unchanged, Condvars) :-
%    format('SPECIAL BUILTIN: ~w~n', special_builtin(SgKey, Sg, Subgoal, Type, Condvars)), !.

special_builtin('!/0',_,_,unchanged,_).
special_builtin('\\==/2',_,_,unchanged,_).
special_builtin('assert/1',_,_,unchanged,_).
special_builtin('asserta/1',_,_,unchanged,_).
special_builtin('assertz/1',_,_,unchanged,_).
special_builtin('not_free/1', _, _, unchanged, _).
special_builtin('retractall/1', _, _, unchanged, _).
special_builtin('statistics/0',_,_,unchanged,_).
special_builtin('true/0', _, _, unchanged, _).
special_builtin('write/1',_,_,unchanged,_).
%-------------------------------------------------------------------------
special_builtin('=:=/2',_,_,ground,_).
special_builtin('=\\=/2',_,_,ground,_).
special_builtin('>=/2',_,_,ground,_).
special_builtin('>/2',_,_,ground,_).
special_builtin('</2',_,_,ground,_).
special_builtin('=</2',_,_,ground,_).
special_builtin('atom/1',_,_,ground,_).
special_builtin('atomic/1',_,_,ground,_).
special_builtin('is/2',_,_,ground,_).
special_builtin('integer/1',_,_,ground,_).
special_builtin('number/1',_,_,ground,_).
special_builtin('statistics/2',_,_,ground,_).
special_builtin('atom_codes/2',_,_,ground,_).
%-------------------------------------------------------------------------
special_builtin('fail/0',_,_,bottom,_).
%-------------------------------------------------------------------------
special_builtin('assert/2', assert(_,Z), _, some, Gv) :-
   varset(Z, Gv).
special_builtin('asserta/2', asserta(_,Z), _, some, Gv) :-
   varset(Z, Gv).
special_builtin('assertz/2', assertz(_,Z), _, some, Gv) :-
   varset(Z, Gv).
special_builtin('compare/3',compare(X,_,_), _,some, Gv):-
   varset(X, Gv).
special_builtin('functor/3', functor(_X,Y,Z), _, some, Gv) :-
   varset([Y,Z], Gv).
special_builtin('write/2', write(X,_Y), _, some, Gv) :-
   varset(X, Gv).
%-------------------------------------------------------------------------
special_builtin('=/2', Sg, _ , '=/2', Sg).
special_builtin('==/2','=='(X,Y),_,'==/2',p(X,Y)).
special_builtin('arg/3', Sg, _, 'arg/3', Sg).
special_builtin('findall/3', findall(X,_,Z), _, 'findall/3', findall(X,_,Z)).
special_builtin('free/1', free(X) ,_,'free/1', p(X)).
special_builtin('recorded/3', recorded(_,Y,Z), _, 'recorded/3',p(Y,Z)).
special_builtin('retract/1', retract(X), _, 'recorded/3', p(X,b)).

%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% success_builtin(+Type,+Sv,?Condvars,+HvFv_u,+Call,-Succ)
%
% Obtains the success substitution for given builtins. Type and Condvars
% come from the special_builtin predicate. Sv is the set of variable in
% the builtin and HvFv_u is the set of all clause variables.
%-------------------------------------------------------------------------

:- dom_impl(_, success_builtin/6, [noq]).
:- pred success_builtin(+Type, +Sv, ?Condvars, +HvFv_u, +Call, -Succ)
   : term * ordlist(var) * term * list(var) * nasub * ivar => asub(Succ)
   + (not_fails, is_det).
:- export(success_builtin/6).

success_builtin(unchanged, _ , _ , _, Call, Call).
success_builtin(bottom, _ , _ , _, _, '$bottom').
success_builtin(some, _, Gv, _, Call, Succ) :-
   make_ground(Call, Gv, Succ).
success_builtin(ground, Sv, _, _, Call, Succ) :-
   make_ground(Call, Sv, Succ).
success_builtin('=/2', _, T1=T2, _, Call, Result) :-
   unifiable_with_occurs_check(T1, T2,  Unifier),
   mgu(Call, [], Unifier, Result).
success_builtin('==/2', _Sv, p(X, Y), _, Call, Succ) :-
   unifiable_with_occurs_check(X, Y, Unifier), !,
   restrict_identical(Call, Unifier, Succ).
success_builtin('==/2', _, _, _, _, '$bottom').
success_builtin('arg/3', _, arg(X,Y,Z), HvFv_u, Call, Succ) :-
   varset(X, Gv),
   make_ground(Call, Gv, Call0),
   (
      var(Y) ->
         mgu(Call0, [], [Y=f(Z, _)], Call1),
         sort(HvFv_u, HvFv),
         project(Call1, HvFv, Succ)
      ;
         functor(Y, _, N),
         (
            N = 0 ->
               Succ = '$bottom'
            ;
               sh_any_arg_all_args(N, Y, Z, Call0, Succs),
               compute_lub(Succs, Succ)
         )
   ).
success_builtin('free/1', _Sv, p(X), _, Call, Succ):-
   var(X),
   restrict_var(Call, X, Succ).
success_builtin('free/1', _Sv, _Condvars, _ , _Call,'$bottom').
success_builtin('findall/3', _, findall(X, _, Z), _, Call, Succ) :-
   varset(X, Vx),
   check_ground(Call, Vx), !,
   varset(Z, Vz),
   make_ground(Call, Vz, Succ).
% NOTE: This is correct only because before calling the built-in 'findall' the
% PLAI analyzer calls the built-in '$meta'.
success_builtin('findall/3', _, _, _, Call, Call).
success_builtin('recorded/3', _, p(X, Y), _, Call, Succ) :-
   varset(Y, Vy),
   make_ground(Call, Vy, Call0),
   varset(X, Vx),
   unknown(Call0, Vx, Succ).

sh_any_arg_all_args(0, _, _, _, []) :- !.
sh_any_arg_all_args(N, Y, Z, Call, [Succ|Succs]):-
   arg(N, Y, NY),
   (
      unifiable_with_occurs_check(NY, Z, Unifier) ->
         mgu(Call, [], Unifier, Succ)
      ;
         Succ = '$bottom'
   ),
   N1 is N-1,
   sh_any_arg_all_args(N1, Y, Z, Call, Succs).

%-------------------------------------------------------------------------
% unknown_call(+Sg,+Vars,+Call,-Succ)
%
% Succ is the result of executing an unknown goal Sg, using variables in
% Vars, starting from the abstract substitution Call.
%-------------------------------------------------------------------------

:- dom_impl(_, unknown_call/4, [noq]).
:- pred unknown_call(+Sg, +Vars, +Call, -Succ)
   : cgoal * {ordlist(var), same_vars_of(Sg)} * nasub * ivar => asub(Succ)
   + (not_fails, is_det).

unknown_call(Sg, Vars, Call, Succ) :-
   % print the unknown call since it might be caused by unsupported builtins
   format('UNKNOWN CALL: ~w~n', Sg),
   unknown(Call, Vars, Succ).

%------------------------------------------------------------------------%
% amgu(+Sg,+Head,+ASub,-AMGU)
%
% AMGU is the abstract unification between ASub and the unifiers of Sg and
% Head.
%
% TODO: Understand which options enable the use of this predicate.
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

%------------------------------------------------------------------------%
% AUXILIARY PREDICATES
%------------------------------------------------------------------------%

%-------------------------------------------------------------------------
% check_ground(+ASub, -Vars)
%
% Succeed if all variables in Vars are ground w.r.t. ASub
%-------------------------------------------------------------------------

:- pred check_ground(+ASub, +Vars)
   : nasub * ordlist(var)
   + (is_det).

check_ground(ASub, Vars) :-
   ng_vars(ASub, NGv),
   ord_disjoint(NGv, Vars).

%------------------------------------------------------------------------
% FIXED DECLARATIONS
%-------------------------------------------------------------------------

:- export(nasub/1).
:- export(nasub_u/1).
:- export(reorder/2).
:- export(top/2).
:- export(augment/3).
:- export(project/3).
:- export(join/3).
:- export(meet/3).
:- export(mgu/4).
:- export(match/4).
