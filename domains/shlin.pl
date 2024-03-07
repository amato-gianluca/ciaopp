:- module(shlin, [], [assertions,regtypes,basicmodes,nativeprops,datafacts]).

%:- use_package(trace).
:- use_package(rtchecks).

:- doc(title, "sharing x linearity (abstract domain)").
:- doc(author, "Gianluca Amato").
:- doc(author, "Francesca Scozzari").

:- doc(module,"
This module implements the Sharing X Linearity abstract domain.
").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(shlin, [default]).

%------------------------------------------------------------------------%
%                    Meaning of the Program Variables                    %
%                                                                        %
% _sh       : suffix indicating the sharing component                    %
% _lin      : suffix indicating the linearity component                  %
% Sh and Lin: for simplicity, they will represent ASub_sh and ASub_lin   %
%------------------------------------------------------------------------%

:- use_module(library(lists), [powerset/2]).
:- use_module(library(lsets), [sort_list_of_lists/2]).
:- use_module(library(sets), [ord_intersection/3,ord_union/3,ord_subtract/3]).
:- use_module(domain(sharing), [call_to_entry/9,exit_to_prime/7,project_share/3,lub/3,extend/5,unknown_call/4]).
:- use_module(domain(share_aux), [if_not_nil/4]).

:- regtype asub(A) # "@var{A} is an abstract substitution".

asub('$bottom').
asub((Sh, Lin)) :-
   list(list(var),Sh),
   list(var, Lin).

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

unknown_entry(_Sg,Vars,(Entry_sh, Entry_lin)):-
   powerset(Vars,Sh),
   sort_list_of_lists(Sh,Entry_sh),
   Entry_lin = Vars.

%-------------------------------------------------------------------------
% abs_sort(+ASub_u,-ASub)
%
% ASub is the result of sorting abstract substitution ASub_u.
%-------------------------------------------------------------------------

:- dom_impl(_, abs_sort/2, [noq]).
:- pred abs_sort(+ASub_u,-ASub)
   : asub(ASub_u) => asub(ASub)
   + (not_fails, is_det).

abs_sort('$bottom','$bottom'):- !.
abs_sort((Sh_u,Lin_u),(Sh,Lin)):-
    sort_list_of_lists(Sh_u,Sh),
    sort(Lin_u,Lin).

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

project(_Sg,_Vars,_HvFv_u,'$bottom','$bottom'):- !.
project(_Sg,Vars,_HvFv_u,(Sh, Lin),(Proj_sh,Proj_lin)):-
   project_share(Vars,Sh,Proj_sh),
   ord_intersection(Lin,Vars,Proj_lin).


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
call_to_entry(Sv,Sg,Hv,Head,ClauseKey,Fv,(Proj_sh, _Proj_lin),(Entry_sh, Entry_lin),ExtraInfo):-
   sharing:call_to_entry(Sv,Sg,Hv,Head,ClauseKey,Fv,Proj_sh,Entry_sh,ExtraInfo),
   Entry_lin = [].

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
exit_to_prime(Sg,Hv,Head,Sv,(Exit_sh,_Exit_lin),ExtraInfo,(Prime_sh,Prime_lin)) :-
   sharing:exit_to_prime(Sg,Hv,Head,Sv,Exit_sh,ExtraInfo,Prime_sh),
   Prime_lin=[].

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
compute_lub_el((ASub1_sh,ASub1_lin),(ASub2_sh,ASub2_lin),(Lub_sh,Lub_lin)):-
   sharing:lub(ASub1_sh,ASub2_sh,Lub_sh),
   ord_union(ASub1_lin,ASub2_lin,Lub_lin).

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
extend(Sg,(Prime_sh,Prime_lin),Sv,(Call_sh,_Call_lin),(Succ_sh,Succ_lin)):-
   sharing:extend(Sg,Prime_sh,Sv,Call_sh,Succ_sh),
   Succ_lin = Prime_lin.

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
   shlin:call_to_entry(Sv,Sg,Hv,Head,K,[],Proj,Entry,ExtraInfo),
   shlin:exit_to_prime(Sg,Hv,Head,Sv,Entry,ExtraInfo,Prime),
   shlin:extend(Sg,Prime,Sv,Call,Succ).

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
asub_to_native((Sh,Lin),_Qv,_OutFlag,NativeStat,[]):-
    if_not_nil(Sh,sharing(Sh),NativeStat,NativeStat0),
    if_not_nil(Lin,linear(Lin),NativeStat0,[]).

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
unknown_call(Sg,Vars,(Call_sh,Call_lin),(Succ_sh,Succ_lin)):-
    sharing:unknown_call(Sg,Vars,Call_sh,Succ_sh),
    ord_subtract(Call_lin,Vars,Succ_lin).
