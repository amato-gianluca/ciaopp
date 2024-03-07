:- module(shlin, [], [assertions,regtypes,basicmodes,nativeprops,datafacts]).

:- use_package(rtchecks).

:- doc(title, "sharing x linearity (abstract domain)").
:- doc(author, "Gianluca Amato").
:- doc(author, "Francesca Scozzari").

:- doc(module,"
This module implements the Sharing X Linearity abstract domain.
").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(shlin, [default]).

:- regtype asub(A) # "@var{A} is an abstract substitution".
asub('$bottom').
asub('$top').

%-------------------------------------------------------------------------
% unknown_entry/3
%-------------------------------------------------------------------------

:- dom_impl(_, unknown_entry/3, [noq]).
:- pred unknown_entry(+Sg,+Qv,-Call)
   : cgoal * list * term => asub(Call) + (not_fails, is_det).
unknown_entry(_Sg,_Qv,Call):-
    Call = '$top'.

%-------------------------------------------------------------------------
% abs_sort/2
%-------------------------------------------------------------------------

:- dom_impl(_, abs_sort/2, [noq]).
:- pred abs_sort(+Asub,-Asub_s) : asub(Asub) => asub(Asub_s)
   + (not_fails, is_det).
abs_sort(Asub,Asub_s):-
    Asub_s = Asub.

%-------------------------------------------------------------------------
% project/5
%-------------------------------------------------------------------------

:- dom_impl(_, project/5, [noq]).
:- pred project(+Sg,+Vars,+HvFv_u,+Asub,?Proj)
   : term * list(var) * term * asub * term => asub(Proj)
   + (not_fails, is_det).
project(_Sg,_Vars,_HvFv_u,'$bottom','$bottom') :- !.
project(_Sg,_Vars,_HvFv_u,ASub,ASub).

%-------------------------------------------------------------------------
% call_to_entry/9
%-------------------------------------------------------------------------

:- dom_impl(_, call_to_entry/9, [noq]).
:- pred call_to_entry(+Sv,+Sg,+Hv,+Head,+ClauseKey,+Fv,+Proj,-Entry,-ExtraInfo)
   : ( list(Sv), cgoal(Sg), list(Hv), cgoal(Head), term(K), list(Fv), asub(Proj)) % cheaper properties
   => (asub(Entry), var(ExtraInfo)) + (not_fails, is_det).
call_to_entry(_Sv,_Sg,_Hv,_Head,_ClauseKey,_Fv,_Proj,Entry,_ExtraInfo):-
    Entry='$top'.

%-------------------------------------------------------------------------
% exit_to_prime/7
%-------------------------------------------------------------------------

:- dom_impl(_, exit_to_prime/7, [noq]).
:- pred exit_to_prime(+Sg,+Hv,+Head,+Sv,+Exit,?ExtraInfo,-Prime)
   : term * list * cgoal * cgoal * asub * term * term
   => ( var(ExtraInfo), asub(Prime)).
exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_Flag,Prime) :- !,
    Prime = '$bottom'.
exit_to_prime(_Sg,_Hv,_Head,_Sv,_Exit,_ExtraInfo,Prime) :-
    Prime = '$top'.

%-------------------------------------------------------------------------
% compute_lub/2
%-------------------------------------------------------------------------

:- dom_impl(_, compute_lub/2, [noq]).
:- pred compute_lub(+ListASub,-Lub)
   : list(asub, ListASub) => asub(Lub) + (not_fails, is_det).
compute_lub([X],X):- !.
compute_lub([ASub1,ASub2|Xs],Lub):-
    compute_lub_el(ASub1,ASub2,ASubLub),
    compute_lub([ASubLub|Xs],Lub).

compute_lub_el('$bottom',ASub,ASub):- !.
compute_lub_el(_ASub1,_ASub2,'$top').

%-------------------------------------------------------------------------
% extend/5
%-------------------------------------------------------------------------

:- dom_impl(_, extend/5, [noq]).
:- pred extend(+Sg,+Prime,+Sv,+Call,-Succ)
   : term * asub * list * asub * term => asub(Succ) + (not_fails, is_det).
extend(_Sg,'$bottom',_Sv,_Call,Succ):- !,
    Succ = '$bottom'.
extend(_Sg,_Prime,_Sv,Call,Succ):-
    Call = Succ.

%-------------------------------------------------------------------------
% call_to_success_fact/9
%-------------------------------------------------------------------------

:- dom_impl(_, call_to_success_fact/9, [noq]).
:- pred call_to_success_fact(+Sg,+Hv,+Head,+K,+Sv,+Call,+Proj,-Prime,-Succ)
   : cgoal * list * cgoal * term * list * asub * asub * term * term
   => ( asub(Prime), asub(Succ) ) + (not_fails, is_det).
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,'$bottom','$bottom','$bottom'):- !.
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,Prime,Succ):-
    Prime = '$top',
    Succ = '$top'.

%-------------------------------------------------------------------------
% special_builtin/5
%-------------------------------------------------------------------------

:- dom_impl(_, special_builtin/5, [noq]).
:- pred special_builtin(+SgKey,+Sg,+Subgoal,-Type,-Condvars)
   : term * cgoal * term * term * term.
special_builtin('true/0',_,_,unchanged,_).

%-------------------------------------------------------------------------
% input_user_interface/5
%-------------------------------------------------------------------------

:- dom_impl(_, input_user_interface/5, [noq]).
:- pred input_user_interface(?InputUser,+Qv,-ASub,+Sg,+MaybeCallASub)
   : term * list * term * term * term
   => asub(ASub) + (not_fails, is_det).
input_user_interface(_,_Qv,ASub,_Sg,_MaybeCallASub):-
    ASub='$top'.

%-------------------------------------------------------------------------
% input_interface/4
%-------------------------------------------------------------------------

:- dom_impl(_, input_interface/4, [noq]).
:- pred input_interface(+Prop,-Kind,?Struc0,-Struc1).
input_interface(_Prop,_Kind,_Struc0,_Struc1) :- fail.

%-------------------------------------------------------------------------
% asub_to_native/5
%-------------------------------------------------------------------------

:- dom_impl(_, asub_to_native/5, [noq]).
:- pred asub_to_native(+ASub,+Qv,+OutFlag,-ASub_user,-Comps)
   : asub * list * term * term * term.
asub_to_native('$bottom',_Qv,_OutFlag,[],[]) :- !, fail.
asub_to_native(_ASub,_Qv,_OutFlag,[top],[]).

%-------------------------------------------------------------------------
% unknown_call/4
%-------------------------------------------------------------------------

:- dom_impl(_, unknown_call/4, [noq]).
:- pred unknown_call(+Sg,+Vars,+Call,-Succ)
   : cgoal * list * asub * term => asub(Succ) + (not_fails, is_det).
unknown_call(_Sg,_Vars,_Call,Succ):-
    Succ = '$top'.
