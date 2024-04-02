:- module(as_shlin2, [], [assertions, regtypes, basicmodes, nativeprops, indexer, fsyntax]).

:- use_package(debug).
:- use_package(rtchecks).
%:- use_module(engine(io_basic)).

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

input_user_interface((Sh, Lin), Qv, ASub, Sg, MaybeCallASub):-
   sharing:input_user_interface(Sh, Qv, ASub_sh, Sg, MaybeCallASub),
   as_sharing:vars(ASub_sh, Vsh),
   ord_intersection(Lin, Vsh, ASub_lin),
   from_shlin(ASub_sh, ASub_lin, ASub).

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

:- export(shlin2group/1).
:- test shlin2group(O) : (O = ([X, Y], [X, Y])) => true + (not_fails, is_det).
:- test shlin2group(O) : (O = ([X, Y], [X])) => true + (not_fails, is_det).
:- test shlin2group(O) : (O = ([X, Z], [X, Y])) + (fails, is_det).
:- test shlin2group(O) : (O = ([], [])) + (fails, is_det).

shlin2group((Sh, Lin)) :-
   Sh \= [],
   ordnlist(var, Sh),
   ordlist(var, Lin),
   ord_subset(Lin, Sh).

:- prop nasub(ASub) # "@var{ASub} is a non empty abstract substitution".

:- export(nasub/1).
:- test nasub(ASub): (ASub = []) + (not_fails, is_det).
:- test nasub(ASub): (ASub = [([X, Y], [X]), ([X, Y], [Y]), ([X, Y, Z], [X])]) + (not_fails, is_det).
:- test nasub(ASub): (ASub = [([],[]), ([X, Y], [X])]) + (fails, is_det).
:- test nasub(ASub): (ASub = [([X, Y, Z], [X]), ([Z], []), ([Y], [])]) + (fails, is_det).
:- test nasub(ASub): (ASub = [([X, Y], [X, Y]), ([X, Y], [X])]) + (fails, is_det).
:- test nasub(ASub): (ASub = [([X, Y], [X]), ([X, Y], [X, Y])]) + (fails, is_det).

nasub(ASub) :-
   ordlist(shlin2group, ASub),
   no_redundants(ASub).

no_redundants([]).
no_redundants([(Sh, Lin)|Rest]) :-
   no_redundants0(Sh, Lin, Rest),
   no_redundants(Rest).

no_redundants0(Sh, Lin, [(Sh1, Lin1)|Rest]) :-
   Sh == Sh1, !,
   \+ ord_subset(Lin, Lin1),
   no_redundants0(Sh, Lin, Rest).
no_redundants0(_Sh, _Lin, _Rest).

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

:- export(normalize/2).
:- test normalize(ASub_u, ASub): (ASub_u = []) => (ASub = []) + (not_fails, is_det).
:- test normalize(ASub_u, ASub): (ASub_u = [([X, Y], [X])]) => (ASub = [([X, Y], [X])]) + (not_fails, is_det).
:- test normalize(ASub_u, ASub): (ASub_u = [([X, Y], [X]), ([X, Y], [X, Y])]) => (ASub = [([X, Y], [X])]) + (not_fails, is_det).
:- test normalize(ASub_u, ASub): (ASub_u = [([X, Y], [X, Y]), ([X, Y], [Y])]) => (ASub = [([X, Y], [Y])]) + (not_fails, is_det).

normalize(ASub_u, ASub) :-
   sort(ASub_u, ASub0),
   remove_redundants(ASub0, ASub).

remove_redundants([], []).
remove_redundants([([], _)|Rest], RestNorm) :- !,
   remove_redundants(Rest, RestNorm).
remove_redundants([(Sh, Lin)|Rest], RestNorm) :-
   remove_redundants0(Sh, Lin, Rest, Rest0, SelfRedundant),
   (
      SelfRedundant = yes ->
         RestNorm = RestNorm0
      ;
         RestNorm = [(Sh, Lin)|RestNorm0]
   ),
   remove_redundants(Rest0, RestNorm0).

remove_redundants0(Sh, Lin, [(Sh1, Lin1)|Rest], RestRemoved, SelfRedundant) :-
   Sh == Sh1, !,
   (
      ord_subset(Lin, Lin1) ->
         RestRemoved = RestRemoved0,
         SelfRedundant = SelfRedundant0
      ;
         (ord_subset(Lin1, Lin) -> SelfRedundant = yes ; SelfRedundant = SelfRedundant0),
         RestRemoved = [(Sh1, Lin1)|RestRemoved0]
   ),
   remove_redundants0(Sh, Lin, Rest, RestRemoved0, SelfRedundant0).
remove_redundants0(_Sh, _Lin, ASub, ASub, no) :- !.

%-------------------------------------------------------------------------
% top(+Vars,+Top)
%
% Top is the largest abstract substitution on variable Vars.
%-------------------------------------------------------------------------

:- pred top(+Vars, -Top)
   : ordlist(var) * ivar => nasub(Top)
   + (not_fails, is_det).

:- export(top/2).
:- test top(Vars, Top): (Vars = []) => (Top = []) + (not_fails, is_det).
:- test top(Vars, Top): (Vars = [X, Y]) => (Top = [([X], []), ([X, Y], []), ([Y], [])]) + (not_fails, is_det).

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

:- export(augment/3).
:- test augment(Asub, Vars, Aug): (Asub = [], Vars = [X, Y]) => (Aug = [ ([X], [X]), ([Y], [Y]) ]) + (not_fails, is_det).
:- test augment(Asub, Vars, Aug): (_ = [X], Asub = [([U, V], [U])], Vars = [X, Y]) => (Aug = [ ([X], [X]), ([U,V], [U]), ([Y], [Y]) ]) + (not_fails, is_det).

augment(ASub, Vars, Aug) :-
   augment0(Vars, ASub0),
   ord_union(ASub, ASub0, Aug).

augment0([], []).
augment0([X|Rest], [([X], [X])|RestAug]) :-
   augment0(Rest, RestAug).

%-------------------------------------------------------------------------
% project(+ASub,+Vars,-Proj)
%
% Proj is the projection of ASub onto the variables in Vars.
%-------------------------------------------------------------------------

:- pred project(+ASub, +Vars, -Proj)
   : nasub * ordlist(var) * ivar => nasub(Proj)
   + (not_fails, is_det).

:- export(project/3).
:- test project(ASub, Vars, Proj): (ASub = [], Vars = [X, Y]) => (Proj = []) + (not_fails, is_det).
:- test project(ASub, Vars, Proj): (ASub = [([X, Y], [X, Y]), ([X, Y, Z], [X, Y, Z]), ([Z], [Z])], Vars = [X, Y]) => (Proj = [([X, Y], [X, Y])]) + (not_fails, is_det).
:- test project(ASub, Vars, Proj): (ASub = [([X, Y], [X]), ([X, Y, Z], [X, Y])], Vars = [X, Y]) => (Proj = [([X, Y], [X])]) + (not_fails, is_det).

project(ASub, Vars, Proj) :-
   project0(ASub, Vars, Proj0),
   sort(Proj0, Proj1),
   remove_redundants(Proj1, Proj).

project0([], _Vars, []).
project0([(Sh, Lin)|Rest], Vars, [(Proj_sh, Proj_lin)|Proj_rest]) :-
   ord_intersection(Sh, Vars, Proj_sh),
   ord_intersection(Lin, Vars, Proj_lin),
   project0(Rest, Vars, Proj_rest).

%-------------------------------------------------------------------------
% join(+ASub1,+ASub2,Join)
%
% Join is the lub (join) og ASub1 and ASub2.
%-------------------------------------------------------------------------

:- pred join(+ASub1, +ASub2, -Join)
   : nasub * nasub * ivar => nasub(Join)
   + (not_fails, is_det).

:- export(join/3).
:- test join(ASub1, ASub2, Join): (ASub1 = [], ASub2 = [([X], [X])]) => (Join = ASub2) + (not_fails, is_det).
:- test join(ASub1, ASub2, Join): (ASub2 = [], ASub1 = [([X], [X])]) => (Join = ASub1) + (not_fails, is_det).
:- test join(ASub1, ASub2, Join): (ASub1 = [([X, Y], [X]), ([U], [])], ASub2 = [([X, Y], [X, Y]), ([V], [V])])
                                => (Join = [([X, Y], [X]), ([U], []), ([V], [V])]) + (not_fails, is_det).

join(ASub1, [], ASub1) :- !.
join([], ASub2, ASub2) :- !.
join(ASub1, ASub2, ASub) :-
   ord_union(ASub1, ASub2, ASub0),
   remove_redundants(ASub0, ASub).

%------------------------------------------------------------------------%
% meet(+ASub1,+ASub2,-Meet)
%
% Meet is the glb (meet) of ASub1 and Sh2.
%------------------------------------------------------------------------%

:- pred meet(+ASub1, +ASub2, -Meet)
   : nasub * nasub * ivar => asub(Meet)
   + (not_fails, is_det).

:- export(meet/3).
:- test meet(ASub1, ASub2, Meet): (ASub1 = [], ASub2 = [([X], [X])]) => (Meet = []) + (not_fails, is_det).
:- test meet(ASub1, ASub2, Meet): (ASub2 = [], ASub1 = [([X], [X])]) => (Meet = []) + (not_fails, is_det).
:- test meet(ASub1, ASub2, Meet): (ASub1 = [([X, Y, Z], [X, Y]), ([U], [U])], ASub2 = [([X, Y, Z], [X, Y]), ([X, Y, Z], [Y, Z])])
                                => (Meet = [([X, Y, Z], [Y])]) + (not_fails, is_det) .

meet(_ASub1, [], []) :- !.
meet([], _ASub2, []) :- !.
meet(ASub1, ASub2, Meet) :-
   meet0(ASub1, ASub2, Meet0),
   remove_redundants(Meet0, Meet).

meet0([], _ASub2, []).
meet0([(Sh1, Lin1)|Rest], ASub2, Meet):-
   meet1(Sh1, Lin1, ASub2, Meet0),
   meet0(Rest, ASub2, Meet1),
   ord_union(Meet0, Meet1, Meet).

meet1(_Sh1, _Lin1, [], []).
meet1(Sh1, Lin1, [(Sh2, Lin2)|Rest], Meet) :-
   compare(Rel, Sh1, Sh2),
   (
      Rel = (=) ->
         ord_intersection(Lin1, Lin2, Lin),
         Meet = [(Sh1, Lin)|RestMeet],
         meet1(Sh1, Lin1, Rest, RestMeet)
      ; Rel = (<) ->
         Meet = []
      ;
         meet1(Sh1, Lin1, Rest, Meet)
   ).

%-------------------------------------------------------------------------
% mgu(+ASub,Fv,+Sub,MGU)
%
% MGU is the result of the unification of ASub with the substitution  Sub.
% Variables in Fv are considered to be free.
%-------------------------------------------------------------------------

:- pred mgu(+ASub, +Fv, +Sub, -MGU)
   : nasub * ordlist(var) * unifier_no_cyclic * ivar => nasub(MGU)
   + (not_fails, is_det).

:- export(mgu/4).
:- test mgu(ASub, Fv, Sub, MGU): (ASub=[], Fv=[], Sub=[X=t(Y,Z), Y=Z]) => (MGU=[]) + (not_fails, is_det).
:- test mgu(ASub, Fv, Sub, MGU)
   : (ASub=[([U],[U]), ([V],[V]), ([X],[X]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=U])
   => (MGU=[([U, X], [U,X]), ([V],[V]), ([Y],[Y]), ([Z],[Z]) ]) + (not_fails, is_det).
:- test mgu(ASub, Fv, Sub, MGU)
   : (ASub=[([U],[U]), ([V],[V]), ([X],[X]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=U, Y=f(U, V)])
   => (MGU=[([U, X, Y], [U, X, Y]), ([V, Y],[V, Y]), ([Z],[Z]) ]) + (not_fails, is_det).
:- test mgu(ASub, Fv, Sub, MGU)
   : (ASub=[([U],[U]), ([V],[V]), ([X],[X]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=U, Y=f(U, V), Z=V])
   => (MGU=[([U, X, Y], [U, X, Y]), ([V, Y, Z],[V, Y, Z])]) + (not_fails, is_det).
:- test mgu(ASub, Fv, Sub, MGU)
   : (ASub=[([X,U],[X,U]), ([X,V],[X,V]), ([X,W],[W]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=f(Y, Z)])
   => (MGU=[([X,U,Y], [X,U,Y]), ([X,U,Z],[X,U,Z]), ([X,V,Y],[X,V,Y]), ([X,V,Z],[X,V,Z]), ([X,W,Y],[W]),  ([X,W,Y,Z],[W]), ([X,W,Z],[W])]) + (not_fails, is_det).
:- test mgu(ASub, Fv, Sub, MGU)
   : (ASub=[([X,U],[X,U]), ([X,V],[X,V]), ([X,W],[W]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=f(Y, Z),W=a])
   => (MGU=[([X,U,Y], [X,U,Y]), ([X,U,Z],[X,U,Z]), ([X,V,Y],[X,V,Y]), ([X,V,Z],[X,V,Z])]) + (not_fails, is_det).

:- index mgu(?, ?, +, ?).
mgu(ASub, _Fv, [], ASub).
mgu(ASub, Fv, [X=T|Rest], MGU) :-
   mgu_binding(ASub, X, T, MGU0),
   mgu(MGU0, Fv, Rest, MGU).

mgu_binding(ASub, X, T, MGU0) :-
   bag_vars(T, Bt),
   split(ASub, [X-1], NRel_x, Rel_x_lin, Rel_x_nlin),
   split(ASub, Bt, NRel_t, Rel_t_lin, Rel_t_nlin),
   ord_intersection(NRel_x, NRel_t, NRel),
   (
      Rel_x_nlin == [], ord_subset(Rel_x_lin, NRel_t) ->
         bin(Rel_x_lin, Rel_t_lin, ASub1),
         star_union(Rel_x_lin, Rel_x_lin_star),
         bin(Rel_x_lin_star, Rel_t_nlin, ASub2),
         merge_list_of_lists([NRel, ASub1, ASub2], MGU0)
      ; Rel_t_nlin == [], ord_subset(Rel_t_lin, NRel_x) ->
         bin(Rel_t_lin, Rel_x_lin, ASub1),
         star_union(Rel_t_lin, Rel_t_lin_star),
         bin(Rel_t_lin_star, Rel_x_nlin, ASub2),
         merge_list_of_lists([NRel, ASub1, ASub2], MGU0)
      ;
         ord_union(Rel_x_lin, Rel_x_nlin, Rel_x),
         star_union(Rel_x, Rel_x_star),
         ord_union(Rel_t_lin, Rel_t_nlin, Rel_t),
         star_union(Rel_t, Rel_t_star),
         bin(Rel_x_star, Rel_t_star, ASub1),
         ord_union(NRel, ASub1, MGU0)
   ).

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

:- export(match/4).
:- test match(Prime, Pv, Call, Match)
   : (Prime=[([X, Y],[])], Pv=[X, Y, Z], Call=[([X, Y], [X]), ([Y, U], [U]), ([Z, U], []), ([U],[U])])
   => (Match=[([X, Y],[]), ([X, Y, U],[]), ([U],[U])]) + (not_fails, is_det).

match(Prime, Pv, Call, Match) :-
   rel(Call, Pv, NRel, Rel),
   relbar(Rel, Pv, Relbar),
   match0(Prime, Lv, Rel, Relbar, Match0,),

match0([], _Pv, _Rel, _Relbar, []).
match0([(Sh, Lin)|Rest], Pv, Rel, Relbar, [Match|RestMatch]) :-
   match1(Sh, Lin, Pv, Call, Match),
   match0(Rest, Pv, Call, RestMatch).

match1(Sh, Lin, Pv, Rel, Relbar, Match) :-
   star_union(Rel, Rel_star),
   match2(Sh, Lin, Pv, Rel_star, Relbar, Match)

match2(_Sh, _Lin, _Pv, [], _Relbar, []).
match2(Sh, Lin, Pv, [(X_sh, X_lin)|Rest_rel_star], Relbar, [Res|RestRes]) :-
   Sh == X_sh,
   ord_subset(Lin, X_lin),
   match_meet(Sh, Lin, X_sh, X_lin, Pv, Res_sh, Res_lin),

match_meet(Lin1, Lin2, Vars1, Lin) :-
   ord_intersection(Lin1, Lin2, Lina),
   ord_intersection(Lin2, Vars, Linb),
   ord_union(Lina, Linb, Lin).

relbar([], Vars, []).
relbar([(Sh, Lin)|Rest], Vars, [(Sh, Lin)|RestBar]) :-
   ord_disjoint(Vars, Lin), !,
   relbar(Rest, Vars, RestBar).
relbar([(Sh, Lin)|Rest], Vars, RestBar) :-
   relbar(Rest, Vars, RestBar).


%-------------------------------------------------------------------------
% AUXILIARY PREDICATES
%-------------------------------------------------------------------------

:- pred from_sharing(+Sh, -ASub)
   : asub_sh * ivar => nasub(ASub)
   + (not_fails, is_det)
   # "@var{ASub} is the abstract subtitution obtained by the sharing information @var{Sh}
   without linearity information.".

:- export(from_sharing/2).
:- test from_sharing(Sh, ASub): (Sh = []) => (ASub = []) + (not_fails, is_det).
:- test from_sharing(Sh, ASub): (Sh = [[X], [X, Z]]) => (ASub = [([X], []), ([X, Z], [])]) + (not_fails, is_det).

from_sharing([], []).
from_sharing([X|RestSh], [(X, [])|Rest]) :-
   from_sharing(RestSh, Rest).

:- pred from_shlin(+Sh, +Lin, -ASub)
   : asub_sh * ordlist(var) * ivar => nasub(ASub)
   + (not_fails, is_det)
   # "@var{ASub} is the abstract subtituion obtained by merging the sharing information
   in @var{Sh} and linearity information in @var{Lin}.".

:- export(from_shlin/3).
:- test from_shlin(Sh, Lin, ASub): (Sh = [], Lin=[X, Y] ) => (ASub = []) + (not_fails, is_det).
:- test from_shlin(Sh, Lin, ASub): (Sh = [[X], [X,Z]], Lin=[X, Y] ) => (ASub = [([X], [X]), ([X,Z], [X])]) + (not_fails, is_det).

from_shlin([], _Lin, []).
from_shlin([O|RestSh], Lin, [(O, OLin)|RestShLin2]) :-
   ord_intersection(O, Lin, OLin),
   from_shlin(RestSh, Lin, RestShLin2).

:- pred vars(ASub, Vars)
   : nasub * ivar => ordlist(var, Vars)
   + (not_fails, is_det)
   # "@{Vars} is the set of variables in the abstract substitution @{ASub}.".
:- export(vars/2).
:- test vars(ASub, Vars): (ASub = []) => (Vars = []) + (not_fails, is_det).
:- test vars(ASub, Vars): (ASub = [([X], [X]), ([X,Z], [X])]) => (Vars = [X, Z]) + (not_fails, is_det).

vars(ASub, Vars) :-
   sharing(ASub, Sh),
   as_sharing:vars(Sh, Vars).

:- pred sharing(+ASub, -Sh)
   : nasub * ivar => asub_sh(Sh)
   + (not_fails, is_det)
   # "@var{Sh} is the set of sharing groups of the abstract substitution @var{ASub}.".
:- export(sharing/2).
:- test sharing(ASub, Sharing): (ASub = []) => (Sharing = []) + (not_fails, is_det).
:- test sharing(ASub, Sharing): (ASub = [([X], [X]), ([X,Z], [X])]) => (Sharing = [[X], [X,Z]]) + (not_fails, is_det).

sharing([], []).
sharing([(Sh, _Lin)|Rest], Sharing) :-
   sharing(Rest, RestSharing),
   insert(RestSharing, Sh, Sharing).

:- pred lin(+ASub, -Lin)
   : nasub * ivar => ordlist(var, Lin)
   + (not_fails, is_det)
   # "@var{Lin} is the set of definite linear non-ground variables in the abstract
   substitution @var{ASub}, without the ground variables.".
:- export(lin/2).
:- test lin(ASub, Lin): (ASub = []) => (Lin = []) + (not_fails, is_det).
:- test lin(ASub, Lin): (ASub = [([X], [X]), ([X,Z], [X])]) => (Lin = [X]) + (not_fails, is_det).
:- test lin(ASub, Lin): (ASub = [([X], [X]), ([X,Z], [X]), ([X, Z, Y], [X, Z, Y])]) => (Lin = [X, Y]) + (not_fails, is_det).

lin(ASub, Lin) :-
   vars(ASub, Vars),
   nlin(ASub, NLin),
   ord_subtract(Vars, NLin, Lin).

:- pred nlin(+ASub, -NLin)
   : nasub * ivar => ordlist(var, NLin)
   + (not_fails, is_det)
   # "@var{NLin} is the set of possible non-linear variables in the abstract
   substitution @var{ASub}.".
:- export(nlin/2).
:- test nlin(ASub, Lin): (ASub = []) => (Lin = []) + (not_fails, is_det).
:- test nlin(ASub, Lin): (ASub = [([X], [X]), ([X,Z], [X])]) => (Lin = [Z]) + (not_fails, is_det).
:- test nlin(ASub, Lin): (ASub = [([X], [X]), ([X,Z], [X]), ([X, Z, Y], [X, Z, Y])]) => (Lin = [Z]) + (not_fails, is_det).

nlin([], []).
nlin([(Sh, Lin)|Rest], NLin) :-
   nlin(Rest, RestNLin),
   ord_subtract(Sh, Lin, NLin0),
   ord_union(NLin0, RestNLin, NLin).

:- pred split(+ASub, +Bt, -NRel, -Rel_lin, -Rel_nlin)
   : nasub * isbag(var) * ivar * ivar * ivar => (nasub(NRel), nasub(Rel_lin), nasub(Rel_nlin))
   + (not_fails, is_det)
   # "Split the 2-sharing groups in @var{ASub} wrt the bag of variables @var{Bt},
   in the not-relevant, relevant linear and relevant non-linear groups.".

:- export(split/5).
:- test split(ASub, Bt, NRel, Rel_lin, Rel_nlin): (ASub=[], Bt=[X-2,Y-3]) => (NRel=[], Rel_lin=[], Rel_nlin=[]) + (not_fails, is_det).
:- test split(ASub, Bt, NRel, Rel_lin, Rel_nlin)
   : (ASub=[([X, Y],[Y]), ([X, Z],[X, Z]), ([Z],[])], Bt=[X-1,Y-2])
   => (NRel=[ ([Z],[])], Rel_lin=[([X, Z],[X, Z])], Rel_nlin=[([X, Y],[Y])]) + (not_fails, is_det).

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

:- export(bin/3).
:- test bin(ASub1, ASub2, Bin): (ASub1 = [], ASub2 = [([X], [X])]) => (Bin = []) + (not_fails, is_det).
:- test bin(ASub1, ASub2, Bin): (ASub2 = [], ASub1 = [([X], [X])]) => (Bin = [])+ (not_fails, is_det).
:- test bin(ASub1, ASub2, Bin): (ASub1 = [([X, Y], [X, Y])], ASub2 = [([X], [X]), ([Z], [Z])]) => (Bin = [([X, Y], [Y]), ([X, Y, Z], [X, Y, Z])]) + (not_fails, is_det).
:- test bin(ASub1, ASub2, Bin): (ASub1 = [([X], [X]), ([Y], [Y])], ASub2 = [([X], [X]), ([Y], [Y])]) => (Bin = [([X], []), ([X, Y], [X, Y]), ([Y], [])]) + (not_fails, is_det).
:- test bin(ASub1, ASub2, Bin): (ASub1 = [([X], [X]), ([Y], [Y])], ASub2 = [([X, Y], []), ([Y], [Y])]) => (Bin = [ ([X, Y], []), ([Y], [])]) + (not_fails, is_det).

bin(Sh1, Sh2, Bin) :-
   bin0(Sh1, Sh2, [], Bin0),
   remove_redundants(Bin0, Bin).

bin0([], _, Bin, Bin).
bin0([X|Rest], Sh, Bin0, Bin) :-
   bin1(X, Sh, [], BinX),
   ord_union(Bin0, BinX, Bin1),
   bin0(Rest, Sh, Bin1, Bin).

%:- index bin1(?, +, ?, ?).

bin1(_, [], Bin, Bin).
bin1((Sh1, Lin1), [(Sh2, Lin2)|Rest], Bin0, Bin) :-
   ord_union(Sh1, Sh2, Sh),
   ord_subtract(Lin1, Sh2, Lina),
   ord_subtract(Lin2, Sh1, Linb),
   ord_union(Lina, Linb, Lin),
   insert(Bin0, (Sh, Lin), Bin1),
   bin1((Sh1, Lin1), Rest, Bin1, Bin).

:- pred star_union(+ASub, -Star)
   : nasub * ivar => nasub(Star)
   + (not_fails, is_det)
   # "@var{Star} is the star union of @var{ASub}.".

:- export(star_union/2).
:- test star_union(ASub, Star): (ASub = []) => (Star = []) + (not_fails, is_det).
:- test star_union(ASub, Star): (ASub = []) => (Star = []) + (not_fails, is_det).
:- test star_union(ASub, Star): (ASub = [([X], [X])]) => (Star = [([X], [])]) + (not_fails, is_det).
:- test star_union(ASub, Star): (ASub = [([X], [X]), ([Y],  [Y])]) => (Star = [([X], []), ([X, Y], []), ([Y], [])]) + (not_fails, is_det).

star_union(ASub, Star):-
   sharing(ASub, Sh),
   as_sharing:star_union(Sh, ShStar),
   from_sharing(ShStar, Star).

:- pred rel(+ASub, +Vars, -NRel, -Rel)
   : nasub * ordlist(var) * ivar * ivar => (nasub(NRel), nasub(Rel))
   + (not_fails, is_det)
   # "@var{Rel} is the set of relevant sharing groups in @var{ASub} wrt the variables in @var{Vars}.".

:- export(rel/4).
:- test rel(ASub, Vars, NRel, Rel): (ASub = [], Vars = [X, Y]) => (Rel = []) + (not_fails, is_det).
:- test rel(ASub, Vars, NRel, Rel):
   (ASub = [([X, Y], [X, Y]), ([X, Y, Z], [X, Y, Z]), ([Z], [Z])], Vars = [X, Y])
   => (Rel = [([X, Y], [X, Y]), ([X, Y, Z], [X, Y, Z])]) + (not_fails, is_det).

rel([], _Vars, [], []).
rel([(Sh, Lin)|Rest], Vars, NRel, Rel) :-
   ( ord_disjoint(Sh, Vars) ->
      NRel = [(Sh, Lin)|NRel0],
      Rel = Rel0
   ;
      NRel = NRel0,
      Rel = [(Sh, Lin)|Rel0]
   ),
   rel(Rest, Vars, NRel0, Rel0).