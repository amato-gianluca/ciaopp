:- module(as_shlin2, [], [assertions, regtypes, basicmodes, nativeprops, indexer, fsyntax]).

:- use_package(debug).
:- use_package(rtchecks).
:- use_module(engine(io_basic)).

:- doc(title, "ShLin2 abstract domain").
:- doc(module,"
This module is an implementation of the ShLin2 abstract domain.
").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(as_shlin2, [default]).

:- include(as_template).
:- use_module(domain(as_sharing)).
:- use_module(domain(as_shlin)).
:- use_module(domain(as_bags)).

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

input_user_interface((Sh, Lin), _Qv, ASub, _Sg, _MaybeCallASub):-
   from_shlin(Sh, Lin, ASub).

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
asub_to_native(ASub, Qv, _OutFlag, NativeStat, []) :-
   sharing(ASub, Sh),
   as_shlin2:lin(ASub, Lin),
   if_not_nil(Sh, sharing(Sh), NativeStat, NativeStat0),
   gvars(Sh, Qv, Gv),
   if_not_nil(Gv, ground(Gv), NativeStat0, NativeStat1),
   if_not_nil(Lin, linear(Lin), NativeStat1, NativeStat2),
   if_not_nil(ASub, shlin2(ASub), NativeStat2, []).

%------------------------------------------------------------------------
% DOMAIN ASSERTIONS
%-------------------------------------------------------------------------

:- prop shlin2group(O) # "@var{O} is a sharing group in the ShLin2 domain".

shlin2group((Sh, Lin)) :-
   ordnlist(var, Sh),
   ordlist(var, Lin),
   ord_subset(Lin, Sh).

:- prop nasub(ASub) # "@var{ASub} is a non empty abstract substitution".

nasub(ASub) :-
   ordlist(shlin2group, ASub).

:- regtype nasub_u(ASub) # "@var{ASub} is a non empty unordered abstract substitution".

nasub_u(ASub) :-
   list(shlin2group, ASub).

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

normalize(ASub_u, ASub) :-
   sort(ASub_u, ASub).

%-------------------------------------------------------------------------
% top(+Vars,+Top)
%
% Top is the largest abstract substitution on variable Vars.
%-------------------------------------------------------------------------

:- pred top(+Vars, -Top)
   : ordlist(var) * ivar => nasub(Top)
   + (not_fails, is_det).

top(Vars, Top) :-
   as_sharing:top(Vars, Sh),
   from_shlin(Sh, [], Top).

%------------------------------------------------------------------------
% augment(+ASub,+Vars,-Aug)
%
% Augment the abstract substitution ASub adding the fresh variables Vars
% to get the abstract substitution Aug.
%-------------------------------------------------------------------------

:- pred augment(+ASub, +Vars, -Aug)
   : (nasub * {ordlist(var), independent_from(ShLin)} * ivar) => nasub(Aug)
   + (not_fails, is_det).

augment([], _Vars, []).
augment([(Sh, Lin)|Rest], Vars, [(Aug_sh, Aug_Lin)|Aug_rest]) :-
   as_sharing:augment(Sh, Vars, Aug_sh),
   ord_union(Lin, Vars, Aug_Lin),
   augment(Rest, Vars, Aug_rest).

%-------------------------------------------------------------------------
% project(+ASub,+Vars,-Proj)
%
% Proj is the projection of ASub onto the variables in Vars.
%-------------------------------------------------------------------------

:- pred project(+ASub, +Vars, -Proj)
   : nasub * ordlist(var) * ivar => nasub(Proj)
   + (not_fails, is_det).

project([], _Vars, []).
project([(Sh, Lin)|Rest], Vars, [(Proj_sh, Proj_lin)|Proj_rest]) :-
   as_sharing:project(Sh, Vars, Proj_sh),
   ord_intersection(Lin, Vars, Proj_lin),
   project(Rest, Vars, Proj_rest).

%-------------------------------------------------------------------------
% join(+ASub1,+ASub2,Join)
%
% Join is the lub (join) og ASub1 and ASub2.
%-------------------------------------------------------------------------

:- pred join(+ASub1, +ASub2, -Join)
   : nasub * nasub * ivar => nasub(Join)
   + (not_fails, is_det).

join(ASub1, [], ASub1) :- !.
join([], ASub2, ASub2) :- !.
% TODO: normalization ?
join(ASub1, ASub2, ASub) :-
   ord_union(ASub1, ASub2, ASub).

%------------------------------------------------------------------------%
% meet(+ASub1,+ASub2,-Meet)
%
% Meet is the glb (meet) of ASub1 and Sh2.
%------------------------------------------------------------------------%

:- pred meet(+ASub1, +ASub2, -Meet)
   : nasub * nasub * ivar => asub(Meet)
   + (not_fails, is_det).

% TODO: normalization ?
meet(Sh1, Sh2, Meet):-
   ord_intersection(Sh1, Sh2, Meet).

%-------------------------------------------------------------------------
% mgu(+ASub,Fv,+Sub,MGU)
%
% MGU is the result of the unification of ASub with the substitution  Sub.
% Variables in Fv are considered to be free.
%-------------------------------------------------------------------------

:- pred mgu(+ASub, +Fv, +Sub, -MGU)
   : nasub * ordlist(var) * unifier_no_cyclic * ivar => nasub(MGU)
   + (not_fails, is_det).

:- index mgu(?, ?, +, ?).
mgu(ASub, _Fv, [], ASub).
mgu(ASub, Fv, [X=T|Rest], MGU) :-
   mgu_binding(ASub, X, T, MGU0),
   mgu(MGU0, Fv, Rest, MGU).

mgu_binding(ASub, X, T, MGU0) :-
   bag_vars(T, Bt),
   split(ASub, [X], NRel_x, Rel_x_lin, Rel_x_nlin),
   split(ASub, Bt, NRel_t, Rel_t_lin, Rel_t_nlin),
   ord_intersection(NRel_x, NRel_t, NRel),
   ord_subtract(ASub, NRel, ASub0),
   (
      Rel_x_nlin == [], ord_subset(Rel_x_lin, NRel_t) ->
         bin(Rel_x_lin, Rel_t_lin, ASub1),
         star_union(Rel_x_lin, Rel_x_lin_star),
         bin(Rel_x_lin_star, Rel_t_nlin, ASub2),
         merge_list_of_lists([ASub0, ASub1, ASub2], MGU0)
      ; Rel_t_nlin == [], ord_subset(Rel_t_lin, NRel_x) ->
         bin(Rel_t_lin, Rel_x_lin, ASub1),
         star_union(Rel_t_lin, Rel_t_lin_star),
         bin(Rel_t_lin_star, Rel_x_nlin, ASub2),
         merge_list_of_lists([ASub0, ASub1, ASub2], MGU0)
      ;
         ord_union(Rel_x_lin, Rel_x_nlin, Rel_x),
         star_union(Rel_x, Rel_x_star),
         ord_union(Rel_t_lin, Rel_t_nlin, Rel_t),
         star_union(Rel_t, Rel_t_star),
         bin(Rel_x_star, Rel_t_star, ASub1),
         ord_union(ASub0, ASub1, MGU0)
   ).

:- pred split(+ASub, +Bt,-NRel, -Rel_lin, -Rel_nlin)
   # "Split the 2-sharing groups in @var{ASub} wrt the bag of variables @var{Bt},
   in the not-relevant, relevant linear and relevant non-linear groups.".

split([], _Bt, [], [], []).
split([(Sh, Lin)|Rest], Bt, NRel, Rel_lin, Rel_nlin) :-
   split(Rest, Bt, NRel0, Rel_lin0, Rel_nlin0),
   as_shlin:chiMax(Sh, Lin, Bt, Mul),
   (
      Mul = 0 ->
         NRel = [(Sh, Lin)|NRel0],
         Rel_lin = Rel_lin0,
         Rel_nlin = Rel_nlin0
      ; Mul = 1 ->
         NRel = NRel0,
         Rel_lin = [(Sh, Lin)|Rel_lin0],
         Rel_nlin = Rel_nlin0
      ;
         NRel = NRel0,
         Rel_lin = Rel_lin0,
         Rel_nlin = [(Sh, Lin)|Rel_nlin0]
   ).

:- pred bin(+ASub1, +ASub2, -Bin)
   : nasub * nasub * ivar => nasub(Bin)
   + (not_fails, is_det)
   # "@var{Bin} is the combination of two abstract substitutions @var{ASub1} and @var{ASub2}.".

bin(Sh1, Sh2, Bin) :-
   bin0(Sh1, Sh2, [], Bin).

bin0([], _, Bin, Bin).
bin0([X|Rest], Sh, Bin0, Bin) :-
   bin1(X, Sh, [], BinX),
   ord_union(Bin0, BinX, Bin1),
   bin0(Rest, Sh, Bin1, Bin).

:- index bin1(?, +, ?, ?).

bin1(_, [], Bin, Bin).
bin1((Sh1, Lin1), [(Sh2, Lin2)|Rest], Bin0, Bin) :-
   ord_union(Sh1, Sh2, Sh),
   ord_union_symdiff(Lin1, Lin2, _, Lin),
   insert(Bin0, (Sh, Lin), Bin1),
   bin1((Sh1, Lin1), Rest, Bin1, Bin).

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

match(Prime, Pv, Call, Match) :-
   copy_term_nat((Prime, Pv), (Prime0, Pv0)),
   build_unifier(Pv, Pv0, MGU),
   join(Prime0, Call, CallExtended),
   mgu(CallExtended, [], MGU, Match).

build_unifier([], [], []).
build_unifier([V|Rest], [V0|Rest0], [V=V0|RestMGU]) :-
   build_unifier(Rest, Rest0, RestMGU).

%-------------------------------------------------------------------------
% AUXILIARY PREDICATES
%-------------------------------------------------------------------------

:- pred from_shlin(+Sh, +Lin, -ASub)
   : asub_sh * ordlist(var) * ivar => nasub(ASub)
   + (not_fails, is_det)
   # "@var{ASub} is the abstract subtituion obtained by merging the sharing information
   in @var{Sh} and linearity information in @var{Lin}.".

from_shlin([], _Lin, []).
from_shlin([O|RestSh], Lin, [(O, OLin)|RestShLin2]) :-
   ord_intersection(O, Lin, OLin),
   from_shlin(RestSh, Lin, RestShLin2).

:- pred vars(ASub, Vars)
   : nasub * ivar => ordlist(var, Vars)
   + (not_fails, is_det)
   # "@{Vars} is the set of variables in the abstract substitution @{ASub}.".

vars(ASub, Vars) :-
   sharing(ASub, Sh),
   as_sharing:vars(Sh, Vars).

:- pred sharing(+ASub, -Sh)
   : nasub * ivar => asub_sh(Sh)
   + (not_fails, is_det)
   # "@var{Sh} is the set of sharing groups of the abstract substitution @var{ASub}.".

sharing([], []).
sharing([(Sh, _Lin)|Rest], Sharing) :-
   sharing(Rest, RestSharing),
   insert(RestSharing, Sh, Sharing).

:- pred lin(+ASub, -Lin)
   : nasub * ivar => ordlist(var, Lin)
   + (not_fails, is_det)
   # "@var{Lin} is the set of definite linear non-ground variables in the abstract
   substitution @var{ASub}, without the ground variables.".

lin(ASub, Lin) :-
   vars(ASub, Vars),
   nlin(ASub, NLin),
   ord_subtract(Vars, NLin, Lin).

:- pred lin(+ASub, -NLin)
   : nasub * ivar => ordlist(var, NLin)
   + (not_fails, is_det)
   # "@var{NLin} is the set of possible non-linear variables in the abstract
   substitution @var{ASub}.".

nlin([], []).
nlin([(Sh, Lin)|Rest], NLin) :-
   nlin(Rest, RestNLin),
   ord_subtract(Sh, Lin, NLin0),
   ord_union(NLin0, RestNLin, NLin).
