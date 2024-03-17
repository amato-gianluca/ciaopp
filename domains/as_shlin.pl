:- module(as_shlin, [], [assertions, regtypes, basicmodes, nativeprops, indexer, fsyntax]).

:- use_package(debug).
:- use_package(rtchecks).
%:- use_module(engine(io_basic)).

:- doc(title, "sharing * linarity abstract domain").
:- doc(module,"
This module is an independent reimplementation of the Sharing X Linearity domain.
").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(as_shlin, [default]).

:- include(as_template).
:- use_module(domain(as_sharing)).

%------------------------------------------------------------------------
% I/O CIAOPP PREDICATES
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

input_interface(linear(X), perfect, (Sh, Lin0), (Sh, Lin)) :-
   list(var, X),
   ord_union(Lin0, X, Lin).
input_interface(free(X), perfect, (Sh, Lin0), (Sh, Lin)) :-
   var(X),
   insert(Lin0, X, Lin).
input_interface(Info, Kind, (Sh0, Lin), (Sh, Lin)) :-
   sharing:input_interface(Info, Kind, Sh0, Sh).

%-------------------------------------------------------------------------
% input_user_interface(?Struct,+Qv,-ASub,+Sg,+MaybeCallASub)
%
% ASub is the abstraction of the information collected in Struct (a domain
% defined structure, see input_interface/4) on variables Qv relative to
% the literal Sg.
%
% Struct may be free if a pred assertion is specified without call conditions.
%
% TODO: Understand the role of MaybeCallASub.
%-------------------------------------------------------------------------

:- dom_impl(_, input_user_interface/5, [noq]).
:- pred input_user_interface(?Struct, +Qv, -ASub, +Sg, +MaybeCallASub)
   : term * {ordlist(var), same_vars_of(Sg)} * ivar * cgoal * term => asub(ASub)
   + (not_fails, is_det).

input_user_interface((Sh, Lin), Qv, (ASub_sh, ASub_lin), Sg, MaybeCallASub):-
   sharing:input_user_interface(Sh, Qv, ASub_sh, Sg, MaybeCallASub),
   vars(ASub_sh, Vsh),
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

%------------------------------------------------------------------------
% DOMAIN ASSERTIONS
%-------------------------------------------------------------------------

:- prop nasub(ASub) # "@var{ASub} is a non empty abstract substitution".

nasub((Sh, Lin)) :-
   as_sharing:nasub(Sh),
   ordlist(var, Lin),
   % Lin only contains variables in Sh, since ground variables are linear by definition
   vars(Sh, VSh),
   ord_subset(Lin, VSh).

:- regtype nasub_u(ASub) # "@var{ASub} is a non empty unordered abstract substitution".

nasub_u((Sh, Lin)) :-
   as_sharing:nasub_u(Sh),
   list(var, Lin).

%-------------------------------------------------------------------------
% DOMAIN PREDICATES
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% normalize(+ASub_u,-ASub)
%
% ASub is the result of normalizing abstract substitution ASub_u.
%-------------------------------------------------------------------------

:- pred normalize(+ASub_u, -ASub)
   : nasub_u * ivar => nasub(ASub)
   + (not_fails, is_det).

normalize((Sh_u, Lin_u), (Sh, Lin)) :-
   as_sharing:normalize(Sh_u, Sh),
   sort(Lin_u, Lin).

%-------------------------------------------------------------------------
% top(+Vars,+Top)
%
% Top is the largest abstract substitution on variable Vars.
%-------------------------------------------------------------------------

:- pred top(+Vars, -Top)
   : ordlist(var) * ivar => nasub(Top)
   + (not_fails, is_det).

top(Vars, (Sh, [])) :-
   as_sharing:top(Vars, Sh).

%------------------------------------------------------------------------
% augment(+ASub,+Vars,-Aug)
%
% Augment the abstract substitution ASub adding the fresh variables Vars
% to get the abstract substitution Aug.
%-------------------------------------------------------------------------

:- pred augment(+ASub, +Vars, -Aug)
   : (nasub * {ordlist(var), independent_from(ShLin)} * ivar) => nasub(Aug)
   + (not_fails, is_det).

augment((Sh, Lin), Vars, (Sh0, Lin0)) :-
   as_sharing:augment(Sh, Vars, Sh0),
   ord_union(Lin, Vars, Lin0).

%-------------------------------------------------------------------------
% project(+ASub,+Vars,-Proj)
%
% Proj is the projection of ASub onto the variables in Vars.
%-------------------------------------------------------------------------

:- pred project(+ASub, +Vars, -Proj)
   : nasub * ordlist(var) * ivar => nasub(Proj)
   + (not_fails, is_det).

project((Sh, Lin), Vars, (Proj_sh, Proj_lin)) :-
   as_sharing:project(Sh, Vars, Proj_sh),
   ord_intersection(Lin, Vars, Proj_lin).

%-------------------------------------------------------------------------
% join(+ASub1,+ASub2,Join)
%
% Join is the lub (join) og ASub1 and ASub2.
%-------------------------------------------------------------------------

:- pred join(+ASub1, +ASub2, -Join)
   : nasub * nasub * ivar => nasub(Join)
   + (not_fails, is_det).

join((Sh1, Lin1), (Sh2, Lin2), (Join_sh, Join_lin)) :-
   as_sharing:join(Sh1, Sh2, Join_sh),
   ord_intersection(Lin1, Lin2, Join_lin).

%------------------------------------------------------------------------%
% meet(+ASub1,+ASub2,-Meet)
%
% Meet is the glb (meet) of ASub1 and Sh2.
%------------------------------------------------------------------------%

:- pred meet(+ASub1, +ASub2, -Meet)
   : nasub * nasub * ivar => asub(Meet)
   + (not_fails, is_det).

meet((Sh1, Lin1), (Sh2, Lin2), (Meet_sh, Meet_lin)):-
   as_sharing:meet(Sh1, Sh2, Meet_sh),
   ord_union(Lin1, Lin2, Meet_lin).

%-------------------------------------------------------------------------
% mgu(+ASub,Fv,+Sub,-MGU)
%
% MGU is the result of the unification of ASub with the substitution Sub.
% Variables in Fv are considered to be free.
%-------------------------------------------------------------------------

:- pred mgu(+ASub, +Fv, +Sub, -MGU)
   : nasub * ordlist(var) * unifier_no_cyclic * ivar => nasub(MGU)
   + (not_fails, is_det).
:- index mgu(?, ?, +, ?).

mgu(ShLin, _Fv, [], ShLin).
mgu(ShLin, Fv, [X=T|Rest], MGU) :-
   mgu_binding(ShLin, X, T, MGU0),
   mgu(MGU0, Fv, Rest, MGU).

%-------------------------------------------------------------------------
% mgu_binding(+ShLin,X,T,-MGU)
%
% MGU is the result of the unification of ShLin with the binding {X/T}.
%-------------------------------------------------------------------------

:- pred mgu_binding(+ShLin, ?Vars_x, ?Vars_t, MGU)
   : asub * var * term * ivar => asub(MGU)
   + (not_fails, is_det).

mgu_binding(ShLin, X, T, (MGU_sh, MGU_lin)) :-
   ShLin = (Sh, Lin),
   rel(Sh, ~varset(X), Sh_x, NSh_x),
   rel(Sh, ~varset(T), Sh_t, NSh_t),
   Sh0 = ~ord_intersection(NSh_x, NSh_t),
   (lin(ShLin, T) -> Lint = yes ; Lint = no),
   (lin(ShLin, X) -> Linx = yes ; Linx = no),
   ( current_pp_flag(mgu_shlin_noindcheck, on) ->
      mgu_binding_sh_noind(Sh_x, Sh_t, Linx, Lint, Sh1)
   ;
      (ind(Sh, X, T) -> Ind = yes ; Ind = no),
      mgu_binding_sh(Sh_x, Sh_t, Ind, Linx, Lint, Sh1)
   ),
   MGU_sh = ~ord_union(Sh0, Sh1),
   Lin0 = ~mgu_binding_lin(Lin, ~vars(Sh_x), ~vars(Sh_t), Linx, Lint),
   MGU_lin = ~ord_intersection(Lin0, ~vars(MGU_sh)).

mgu_binding_sh(Sh_x, Sh_t, Ind, Linx, Lint) := ~bin(R_x, R_t) :-
   R_x = (Lint=yes, Ind=yes ? Sh_x | ~star_union(Sh_x)),
   R_t = (Linx=yes, Ind=yes ? Sh_t | ~star_union(Sh_t)).

mgu_binding_sh_noind(Sh_x, Sh_t, yes, yes) := ~bin(~ord_union(Sh_x, ~bin(Sh_x, Sh_xt)), ~ord_union(Sh_t, ~bin(Sh_t, Sh_xt))) :-
   !,
   Sh_xt = ~star_union(~ord_intersection(Sh_x, Sh_t)).
mgu_binding_sh_noind(Sh_x, Sh_t, _, yes) := ~bin(Sh_x, ~star_union(Sh_t)) :- !.
mgu_binding_sh_noind(Sh_x, Sh_t, yes, _) := ~bin(Sh_t, ~star_union(Sh_x)) :- !.
mgu_binding_sh_noind(Sh_x, Sh_t, _, _) := ~bin(~star_union(Sh_x), ~star_union(Sh_t)).

mgu_binding_lin(Lin, Sx, St, yes, yes) := ~ord_subtract(Lin, ~ord_intersection(Sx, St)) :- !.
mgu_binding_lin(Lin, Sx, _St, yes, _) := ~ord_subtract(Lin, Sx) :- !.
mgu_binding_lin(Lin, _Sx, St, _, yes) := ~ord_subtract(Lin, St) :- !.
mgu_binding_lin(Lin, Sx, St, _, :) := ~ord_subtract(Lin, ~ord_union(Sx, St)).

%-------------------------------------------------------------------------
% match(+Prime,+Pv,+Call,-Match)
%
% Match is the abstract matching between Prime (over the variables in Pv)
% and Call, where Prime is the abstract substitution which should not be
% further instantiated.
%
% With respect to the general definition of matching, we only consider
% the special case in which the variables in Call (not even provided
% explicityl input) are a superset of Pv.
%-------------------------------------------------------------------------

:- pred match(+Prime, +Pv, +Call, -Match)
   : nasub * {ordlist(var), superset_vars_of(Prime)} * nasub * ivar => nasub(Match)
   + (not_fails, is_det).

match(Prime, Pv, (Call_sh, Call_lin), (Match_sh, Match_lin)) :-
   Prime = (Prime_sh, Prime_lin),
   as_sharing:match(Prime_sh, Pv, Call_sh, Match_sh), % we do not use linearity here
   nonlin_vars(Prime, Prime_nolin),
   rel(Call_sh, Prime_nolin, Call_sh_rel_nolin, _),
   vars(Call_sh_rel_nolin, Call_removelin),
   ord_subtract(Call_lin, Pv, Call_lin0),
   ord_subtract(Call_lin0, Call_removelin, Call_lin1),
   ord_union(Prime_lin, Call_lin1, Match_lin0),
   vars(Match_sh, Match_noground),
   ord_intersection(Match_lin0, Match_noground, Match_lin).

%-------------------------------------------------------------------------
% AUXILIARY PREDICATES
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% ind(+Sh,?S,?T)
%
% Determines where S and T are definitely independent given the sharing
% information in Sh.
%-------------------------------------------------------------------------

:- pred ind(+Sh, ?S, ?T)
   % I am not able to use as_sharing:nasub in the call assertion
   : term * term * term
   + is_det.
:- export(ind/3).

ind(Sh, S, T) :-
   varset(S, Vs),
   varset(T, Vt),
   rel(Sh, Vs, Rel_s, _),
   rel(Sh, Vt, Rel_t, _),
   ord_disjoint(Rel_s, Rel_t).

%-------------------------------------------------------------------------
% lin(+ShLin,?T)
%
% Determines whether the term T is definitvely linear with respect to
% the sharing and linearity information in ShLin.
%-------------------------------------------------------------------------

:- pred lin(+ShLin, ?T)
   : asub * term
   + is_det.
:- export(lin/2).

lin(ShLin, T) :-
   ShLin = (Sh, _),
   duplicate_vars(T, Vars_t, DVars_t),
   nonlin_vars(ShLin, NGv, NLin),
   ord_disjoint(Vars_t, NLin),
   all_couples(Vars_t, ind(Sh)),
   ord_disjoint(NGv, DVars_t).

%-------------------------------------------------------------------------
% nonlin_vars(+ShLin,-NGv,-NLin)
%
% Determines the set of non-linear and non-ground variables in ShLin.
%-------------------------------------------------------------------------

:- pred nonlin_vars(+ShLin, -NGv, -NLin)
   : asub * ivar * ivar => (ordlist(var, NGv), ordlist(var, NLin))
   + (not_fails, is_det).

nonlin_vars((Sh, Lin), NGv, NLin) :-
   vars(Sh, NGv),
   ord_subtract(NGv, Lin, NLin).

%-------------------------------------------------------------------------
% nonlin_vars(+ShLin,-NLin)
%
% Determines the set of non-linear variables in ShLin.
%-------------------------------------------------------------------------

:- pred nonlin_vars(+ShLin, -NLin)
   : asub * ivar  => ordlist(var, NLin)
   + (not_fails, is_det).

nonlin_vars(ShLin) := ~nonlin_vars(ShLin, _).