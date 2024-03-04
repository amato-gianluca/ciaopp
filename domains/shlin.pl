:- module(shlin, [], [assertions, regtypes]).

:- doc(title, "sharing x linearity (abstract domain)").
:- doc(author, "Gianluca Amato").
:- doc(author, "Francesca Scozzari").

:- doc(module,"
This module implements the Sharing X Linearity abstract domain.
").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(shlin, [default]).

%-------------------------------------------------------------------------%
%                    Meaning of the Program Variables                     %
%                                                                         %
% _sh       : suffix indicating the sharing component                     %
% _lin      : suffix indicating the freeness component                    %
% Sh and Lin: for simplicity, they will represent ASub_sh and ASub_fr     %
%             respectively                                                %
% BPrime    : similar to the abstract prime constraint: abstract          %
%             subtitution obtained after the analysis of the clause being %
%             considered still projected onto Hv (i.e. just before going  %
%             Sv and thus, to Prime)                                      %
% Binds     : List of primitive bindings corresponding to the unification %
%             of Term1 = Term2.                                           %
% Gv        : set of ground variables (can be added as a prefix of a set  %
%             of variables, e.g. GvHv means the set of ground variables of%
%             the head variables)                                         %
% Tv        : set of variables in a term                                  %
% _args     : Added as a prefix of a term, means the set of variables     %
%             s.t. the i-th set contains the set of variables (ordered) in%
%             the i-th argument of the Term                               %
% Star      : a closure under union of a set of sets (can be added as a   %
%             suffix of a set of sets)                                    %
% ShareArgs : Set of sets of numbers in which each set represents the     %
%             possible set sharing among the argument positions indicated %
%             by the numbers                                              %
%-------------------------------------------------------------------------%

:- regtype asub(A) # "@var{A} is an abstract substitution".
asub('$bottom').
asub('$top').

%------------------------------------------------------------------------%
% project(+,+,+,+,-)
% project(Sg,Vars,HvFv_u,ASub,Proj)
% Proj_sh is obtained as in the sharing domain. Proj_lin is the result of
% intersecting ASub_lin with Vars.
%------------------------------------------------------------------------%
:- dom_impl(_, project/5, [noq]).
project(_Sg,_Vars,_HvFv_u,'$bottom','$bottom') :- !.
project(_Sg,_Vars,_HvFv_u,ASub,ASub).

%------------------------------------------------------------------------
% input_user_interface(+,+,-,+,+)
% input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)
% Obtaining the abstract substitution for ShLin from the user supplied
% information just consists in taking the Sharing first and the var(Fv)
% element of InputUser, and construct from them the Linearity.
%------------------------------------------------------------------------%
:- dom_impl(_, input_user_interface/5, [noq]).
input_user_interface(_,_Qv,ASub,_Sg,_MaybeCallASub):-
    ASub='$top'.

:- dom_impl(_, input_interface/4, [noq]).
input_interface(_Prop,_Kind,_Struc0,_Struc1) :- fail.

%------------------------------------------------------------------------%
% call_to_entry(+,+,+,+,+,+,+,-,-)
% call_to_entry(Sv,Sg,Hv,Head,ClauseKey,Fv,Proj,Entry,ExtraInfo)
% It obtains the abstract substitution (Entry) which results from adding
% the abstraction of the Sg = Head to Proj, later projecting the
% resulting substitution onto Hv.
%------------------------------------------------------------------------%
:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(_Sv,_Sg,_Hv,_Head,_ClauseKey,_Fv,_Proj,Entry,_ExtraInfo):-
    Entry='$top'.

%-------------------------------------------------------------------------
% special_builtin(+,+,+,-,-)                                             |
% special_builtin(SgKey,Sg,Subgoal,Type,Condvars)                        |
% Satisfied if the builtin does not need a very complex action. It       |
% divides builtins into groups determined by the flag returned in the    |
% second argument + some special handling for some builtins:             |
%                                                                        |
% (1) new_ground if the builtin makes all variables ground whithout      |
%     imposing any condition on the previous freeness values of the      |
%     variables                                                          |
% (2) old_ground if the builtin requires the variables to be ground      |
% (3) old_new_ground" if the builtin requires some variables to be       |
%     ground and grounds the rest                                        |
% (4) unchanged if we cannot infer anything from the builtin, the        |
%     substitution remains unchanged and there are no conditions imposed |
%     on the previous freeness values of the variables.                  |
% (5) some if it makes some variables ground without imposing conditions |
% (6) Sgkey, special handling of some particular builtins                |
%--------------------------------------------------------------------

:- dom_impl(_, special_builtin/5, [noq]).
special_builtin('true/0',_,_,unchanged,_).

%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%-------------------------------------------------------------------------
:- dom_impl(_, call_to_success_fact/9, [noq]).

call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,'$bottom','$bottom','$bottom'):- !.
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,Prime,Succ):-
    Prime = '$top',
    Succ = '$top'.

%-------------------------------------------------------------------------
% abs_sort(+,-)                                                          |
% abs_sort(Asub,Asub_s)                                                  |
% it sorts the set of X/Value in Asub obtaining Asub_s.                  |
%-------------------------------------------------------------------------
:- dom_impl(_, abs_sort/2, [noq]).
abs_sort(Asub,Asub_s):-
    Asub_s = Asub.

%------------------------------------------------------------------------%
% extend(+,+,+,+,-)                                                      %
% extend(Sg,Prime,Sv,Call,Succ)                                          %
% If Prime = bottom, Succ = bottom. If Sv = [], Call = Succ.             %
% Otherwise, Succ is computed updating the values of Call with those in  %
% Prime                                                                  %
%------------------------------------------------------------------------%
:- dom_impl(_, extend/5, [noq]).
extend(_Sg,'$bottom',_Sv,_Call,Succ):- !,
    Succ = '$bottom'.
extend(_Sg,_Prime,_Sv,Call,Succ):-
    Call = Succ.

%------------------------------------------------------------------------%
% exit_to_prime(+,+,+,+,+,-,-)
% exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)
% It computes the prime abstract substitution Prime, i.e.  the result of
% going from the abstract substitution over the head variables (Exit), to
% the abstract substitution over the variables in the subgoal.
%------------------------------------------------------------------------%
:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_Flag,Prime) :- !,
    Prime = '$bottom'.
exit_to_prime(_Sg,_Hv,_Head,_Sv,_Exit,_ExtraInfo,Prime) :-
    Prime = '$top'.

%------------------------------------------------------------------------%
% compute_lub(+,-)
% compute_lub(ListASub,Lub)
% It computes the lub of a set of Asub. For each two abstract
% substitutions ASub1 and ASub2 in ListASub, obtaining the lub is just
% (1) merging the Sh1 and Sh2
% (2) intesecting Lin1 and Lin2
%------------------------------------------------------------------------%
:- dom_impl(_, compute_lub/2, [noq]).
compute_lub([X],X):- !.
compute_lub([ASub1,ASub2|Xs],Lub):-
    compute_lub_el(ASub1,ASub2,ASubLub),
    compute_lub([ASubLub|Xs],Lub).

compute_lub_el('$bottom',ASub,ASub):- !.
compute_lub_el(_ASub1,_ASub2,'$top').

%------------------------------------------------------------------------%
% asub_to_native(+,+,+,-,-)                                              %
% asub_to_native(ASub,Qv,OutFlag,ASub_user,Comps)                        %
% The user friendly format consists in extracting the ground variables   %
% and the nonground variables                                            %
%------------------------------------------------------------------------%

:- dom_impl(_, asub_to_native/5, [noq]).
asub_to_native('$bottom',_Qv,_OutFlag,[],[]) :- !, fail.
asub_to_native(_ASub,_Qv,_OutFlag,[top],[]).

%-----------------------------------------------------------------------
% unknown_entry(+,+,-)                                                 |
% unknown_entry(Sg,Qv,Call)                                            |
% The top value is  X/any forall X in the set of variables             |
%-----------------------------------------------------------------------

% This is needed when a predicate has not :- pred assetions.
:- dom_impl(_, unknown_entry/3, [noq]).
unknown_entry(_Sg,_Qv,Call):-
    Call = '$top'.

%------------------------------------------------------------------------%
% unknown_call(+,+,+,-)                                                  %
% unknown_call(Sg,Vars,Call,Succ)                                        %
% Gives the "top" value for the variables involved in a                  %
% literal whose definition is not present, and adds this top value to    %
% Call                                                                   %
%------------------------------------------------------------------------%

:- dom_impl(_, unknown_call/4, [noq]).
unknown_call(_Sg,_Vars,_Call,Succ):-
    Succ = '$top'.
