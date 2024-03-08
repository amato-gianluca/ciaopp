:- module(as_sharing, [], [assertions,regtypes,basicmodes,nativeprops,datafacts]).

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

:- use_module(library(lists), [list_to_list_of_lists/2,powerset/2]).
:- use_module(library(lsets), [sort_list_of_lists/2,closure_under_union/2]).
:- use_module(library(sets), [ord_intersection/3,ord_union/3,ord_subtract/3,ord_intersect/2,insert/3,ord_test_member/3]).
:- use_module(domain(sharing), [call_to_entry/9,exit_to_prime/7,project_share/3,lub/3,extend/5,unknown_call/4]).
:- use_module(domain(share_aux), [if_not_nil/4]).

:- regtype asub(A) # "@var{A} is an abstract substitution".

asub('$bottom').
asub(Sh) :-
   asub_sh(Sh).

:- regtype asub_sh(A) # "@var{A} is a non-empty abstract substitution".

asub_sh([]).
asub_sh([S]) :-
   set_vars(S).
asub_sh([S1,S2|Rest]) :-
   set_vars(S1),
   S1 @< S2,
   asub_sh([S2|Rest]).

:- regtype set_vars(A) #  "@var{A} is a set of variables".

set_vars([X]) :-
   var(X).
set_vars([X1,X2|Rest]) :-
   var(X1),
   X1 @< X2,
   set_vars([X2|Rest]).

:- regtype asub_u(A) #  "@var{A} is an unordered abstract substitution".

asub_u('$bottom').
asub_u(Sh) :-
   list(list(var), Sh).

%-------------------------------------------------------------------------
% unknown_entry(+Sg,+Vars,-Entry)
%
% Entry is the "topmost" abstraction of variables Vars corresponding to
% literal Sg.
%
% TODO: Understand the role of Sg.
%-------------------------------------------------------------------------

:- dom_impl(_, unknown_entry/3, [noq]).
:- pred unknown_entry(+Sg,+Vars,-Entry)
   : cgoal * list(var) * var => asub(Entry)
   + (not_fails, is_det).

unknown_entry(_Sg,Vars,Entry):-
   powerset(Vars,Sh),
   sort_list_of_lists(Sh,Entry).

%-------------------------------------------------------------------------
% abs_sort(+ASub_u,-ASub)
%
% ASub is the result of sorting abstract substitution ASub_u.
%-------------------------------------------------------------------------

:- dom_impl(_, abs_sort/2, [noq]).
:- pred abs_sort(+ASub_u,-ASub)
   : asub_u * var => asub(ASub)
   + (not_fails, is_det).

abs_sort('$bottom','$bottom'):- !.
abs_sort(ASub_u, ASub):-
    sort_list_of_lists(ASub_u,ASub).

%-------------------------------------------------------------------------
% project(Sg,Vars,HvFv_u,ASub,Proj)
%
% Projects the abstract substitution ASub onto the variables of list Vars
% resulting in the projected abstract substitution Proj.
%
% TODO: Understand the role of Sg and HvFv_u
%-------------------------------------------------------------------------

:- dom_impl(_, project/5, [noq]).
:- pred project(+Sg,+Vars,+HvFv_u,+ASub,?Proj)
   : cgoal * list(var) * term * asub * var => asub(Proj)
   + (not_fails, is_det).

project(_Sg,_Vars,_HvFv_u,'$bottom','$bottom').
project(_Sg,Vars,_HvFv_u,ASub,Proj):-
   project_share(Vars,ASub,Proj).

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
:- pred call_to_entry(+Sv,+Sg,+Hv,+Head,+ClauseKey,+Fv,+Proj,-Entry,-ExtraInfo)
   :  list(var) * cgoal * list(var) * cgoal * term * list(var) * asub * var * var
   => (asub(Entry), term(ExtraInfo))
   + (not_fails, is_det).

% TODO: Implement linearity
call_to_entry(Sv,Sg,Hv,Head,ClauseKey,Fv,Proj,Entry,ExtraInfo):-
   sharing:call_to_entry(Sv,Sg,Hv,Head,ClauseKey,Fv,Proj,Entry,ExtraInfo).

%-------------------------------------------------------------------------
% exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)
%
% Computes the abstract substitution Prime which results from adding the
% abstraction of the unification Sg = Head to abstract substitution Exit
% (the exit substitution for a clause Head projected over its variables
% Hv), projecting the resulting substitution onto Sv.
%-------------------------------------------------------------------------

:- dom_impl(_, exit_to_prime/7, [noq]).
:- pred exit_to_prime(+Sg,+Hv,+Head,+Sv,+Exit,+ExtraInfo,-Prime)
   : cgoal * list(var) * cgoal * list(var) * asub * term * var
   => (asub(Prime))
   + (not_fails, is_det).

% TODO: Implement linearity
exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_Flag,'$bottom'):- !.
exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :-
   sharing:exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).

%-------------------------------------------------------------------------
% compute_lub(+ListASub,-LubASub)
%
% LubASub is the least upper bound of the abstract substitutions in
% list ListASub.
%-------------------------------------------------------------------------

:- dom_impl(_, compute_lub/2, [noq]).
:- pred compute_lub(+ListASub,-LubASub)
   : list(asub) * var => asub(LubASub)
   + (not_fails, is_det).

compute_lub([X],X):- !.
compute_lub([ASub1,ASub2|Rest],LubASub):-
   compute_lub_el(ASub1,ASub2,ASub3),
   compute_lub([ASub3|Rest],LubASub).

compute_lub_el('$bottom',ASub,ASub):- !.
compute_lub_el(ASub,'$bottom',ASub):- !.
compute_lub_el(ASub1,ASub2,Lub):-
   sharing:lub(ASub1,ASub2,Lub).

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
   : cgoal * asub * list(var) * asub *  var => asub(Succ)
   + (not_fails, is_det).

extend(_Sg,'$bottom',_Sv,_Call,Succ):- !,
   Succ = '$bottom'.
extend(_Sg,_Prime,[],Call,Succ):- !,
   Call = Succ.
% TODO: Implement linearity
extend(Sg,Prime,Sv,Call,Succ):-
   sharing:extend(Sg,Prime,Sv,Call,Succ).

%-------------------------------------------------------------------------
% call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ)
%
% Specialized version of call_to_entry + entry_to_exit + exit_to_prime
% + extend for a fact Head.
%-------------------------------------------------------------------------

:- dom_impl(_, call_to_success_fact/9, [noq]).
:- pred call_to_success_fact(+Sg,+Hv,+Head,+K,+Sv,+Call,+Proj,-Prime,-Succ)
   : cgoal * list * cgoal * term * list * asub * asub * term * term
   => ( asub(Prime), asub(Succ) ) + (not_fails, is_det).

% TODO: Optimizate, by avoiding the use call_to_entry and exit_to_prime
call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
   as_sharing:call_to_entry(Sv,Sg,Hv,Head,K,[],Proj,Entry,ExtraInfo),
   as_sharing:exit_to_prime(Sg,Hv,Head,Sv,Entry,ExtraInfo,Prime),
   as_sharing:extend(Sg,Prime,Sv,Call,Succ).

%-------------------------------------------------------------------------
% special_builtin(+SgKey,+Sg,+Subgoal,-Type,-Condvars)
%
% Predicate Sg is considered a "builtin" of type Type. Types are
% domain dependent. The actual builtin is executed by body_succ_builtin,
% whose base implementation calls either success_builtin for usual types of
% builtins or call_to_success_builtin for particular predicates. The later is
% called when Type is of the form special(SgKey).
%
% TODO: Understand the role of Sg, Subgoal and Condvars.
%-------------------------------------------------------------------------

:- dom_impl(_, special_builtin/5, [noq]).
:- pred special_builtin(+SgKey,+Sg,+Subgoal,-Type,-Condvars)
   : atom * cgoal * term * var * var => (atom(Type), var(Condvars)).

special_builtin('true/0',_,_,unchanged,_).

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
:- pred input_interface(+Prop,-Kind,?Struc0,-Struc1)
   : term * var * term * var => (atom(Kind), term(Struc0), term(Struct1)).

% TODO: implement correctly
input_interface(_Prop,'approx',[],[]).

%-------------------------------------------------------------------------
% input_user_interface(Struct,Qv,ASub,Sg,MaybeCallASub)
%
% ASub is the abstraction of the information collected in Struct (a domain
% defined structure, see input_interface/4) on variables Qv.
%
% TODO: The role of Sg and MaybeCallASub is not clear.
%-------------------------------------------------------------------------

:- dom_impl(_, input_user_interface/5, [noq]).
:- pred input_user_interface(+Struct,+Qv,-ASub,+Sg,+MaybeCallASub)
   : term * list(var) * var * cgoal * term => asub(ASub)
   + (not_fails, is_det).

% TODO: implement everything
input_user_interface(_Struct,Qv,ASub,Sg,_MaybeCallASub):-
   unknown_entry(Sg,Qv,ASub).

%-------------------------------------------------------------------------
% asub_to_native(ASub,Qv,OutFlag,NativeStat,NativeComp)
%
% NativeStat and NativeComp are the list of native (state and
% computational, resp.) properties that are the concretization of abstract
% of abstract substitution ASub on variables Qv. These are later
% translated to the properties which are visible in the preprocessing unit.
%-------------------------------------------------------------------------

:- dom_impl(_, asub_to_native/5, [noq]).
:- pred asub_to_native(+ASub,+Qv,+OutFlag,-NativeStat,-NativeComp)
   : asub * list(var) * term * var * var.

asub_to_native('$bottom',_Qv,_OutFlag,[],[]) :- !, fail.
asub_to_native(Sh,_Qv,_OutFlag,NativeStat,[]):-
    if_not_nil(Sh,sharing(Sh),NativeStat,[]).

%-------------------------------------------------------------------------
% unknown_call(Sg,Vars,Call,Succ)
%
% Succ is the result of adding to Call the ``topmost'' abstraction of the
% variables Vars involved in a literal Sg whose definition is not present
% in the preprocessing unit. I.e., it is like the conjunction of the
% information in Call with the top for a subset of its variables.
%-------------------------------------------------------------------------

:- dom_impl(_, unknown_call/4, [noq]).
:- pred unknown_call(+Sg,+Vars,+Call,-Succ)
   : cgoal * list(var) * asub * var => asub(Succ)
   + (not_fails, is_det).

unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
unknown_call(Sg,Vars,Call,Succ):-
    sharing:unknown_call(Sg,Vars,Call,Succ).

%-------------------------------------------------------------------------

:- pred rel(+Sh, +Vars, -Sh_rel)
   : list(list(var)) * list(var) * var => list(list(var),Sh_rel).

rel([], _, []) :- !.
rel([X|Rest], Vars, [X|Rest_rel]) :-
   ord_intersect(X, Vars), !,
   rel(Rest, Vars, Rest_rel).
rel([_|Rest], Vars, Rest_rel) :-
   rel(Rest, Vars, Rest_rel).

:- pred aexists_sh(+Sh, +Vars, -Sh_ex)
   : asub_sh * list(var) * var => asub_sh(Sh_ex).
   + (not_fails, is_det).

aexists_sh(Sh, Vars, Sh_ex) :-
   aexists_sh0(Sh, Vars, Sh_ex0),
   list_to_list_of_lists(Vars, Sh_ex1),
   ord_union(Sh_ex0, Sh_ex1, Sh_ex).

aexists_sh0([], _Vars, []) :- !.
aexists_sh0([S|Rest], Vars, Sh_ex) :-
   ord_subtract(S, Vars, S_ex),
   aexists_sh0(Rest, Vars, Rest_ex),
   ( S_ex = [] -> Sh_ex = Rest_ex ; insert(Rest_ex, S_ex, Sh_ex)).

:- pred aexists(+ASub, Vars, -ASub_ex)
   : asub * list(var) * var => asub(ASub_ex)
   + (not_fails, is_det).

aexists('$bottom', _, '$bottom') :- !.
aexists((Sh, Lin), Vars, (Sh_ex, Lin_ex)) :-
   aexists_sh(Sh, Vars, Sh_ex),
   ord_union(Lin, Vars, Lin_ex).

star(Sh, Star) :-
   closure_under_union(Sh, Star).

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

amgu_sh(Sh, Vars_x, Vars_t, Sh_mgu) :-
   rel(Sh, [Vars_x], Sh_x),
   rel(Sh, Vars_t, Sh_t),
   ord_subtract(Sh, Sh_x, Sh_nrel0),
   ord_subtract(Sh_nrel0, Sh_t, Sh_nrel),
   star(Sh_x, Sh_x_star),
   star(Sh_t, Sh_t_star),
   bin(Sh_x_star, Sh_t_star, Sh0),
   ord_union(Sh0, Sh_nrel, Sh_mgu).
