:- module(as_shlin2, [], [assertions, regtypes, basicmodes, nativeprops, indexer]).

:- use_package(debug).
% :- use_package(rtchecks).

:- doc(title, "ShLin2 abstract domain").
:- doc(module,"
This module is an implementation of the ShLin2 abstract domain. It is based on
[A. King, A synergistic analysis for sharing and groundness which traces linearity.
https://dx.doi.org/10.1007/3-540-57880-3_24]. The optimal mgu algorithm is
implemented following [G. Amato, F. Scozzari. On the interaction between sharing
and linearity. http://dx.doi.org/10.1017/S1471068409990160].
").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(as_shlin2, [default]).

:- include(as_template).

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

 % TODO: we abuse not_free for 2-sharing groups.
input_interface(shlin2(X), perfect, (Sh, Lin, ShLin2_0), (Sh, Lin, ShLin2)) :-
   list(shlin2group_u, X), !,
   sort_deep(X, ASub_u),
   sort(ASub_u, ASub0),
   remove_redundants(ASub0, ASub1),
   ( var(ShLin2_0) -> ShLin2 = ASub1 ; meet(ShLin2_0, ASub1, ShLin2) ).
input_interface(linear(X), perfect, (Sh, Lin0, ShLin2), (Sh, Lin, ShLin2)) :-
   list(var, X), !,
   sort(X, X1),
   ord_union(Lin0, X1, Lin).
input_interface(free(X), approx, (Sh, Lin0, ShLin2), (Sh, Lin, ShLin2)) :-
   var(X), !,
   insert(Lin0, X, Lin).
input_interface(Info, Kind, (Sh0, Lin, ShLin2), (Sh, Lin, ShLin2)) :-
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

input_user_interface((Sh, Lin, ShLin2), Qv, ASub, Sg, MaybeCallASub):-
   sharing:input_user_interface(Sh, Qv, ASub_sh, Sg, MaybeCallASub),
   from_sharing(ASub_sh, ASub1),
   (var(ShLin2) -> ASub2 = ASub1 ; meet(ASub1, ShLin2, ASub2)),
   (var(Lin) -> ASub = ASub2 ; linearize(ASub2, Lin, ASub)).

%-------------------------------------------------------------------------
% asub_to_native(+ASub,+Qv,+OutFlag,-NativeStat,-NativeComp)
%
% NativeStat and NativeComp are the list of native (stat<e and
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
   lin(ASub, Lin),
   ground(ASub, Qv, Gv),
   if_not_nil(Sh, sharing(Sh), NativeStat, NativeStat0),
   if_not_nil(Gv, ground(Gv), NativeStat0, NativeStat1),
   if_not_nil(Lin, linear(Lin), NativeStat1, NativeStat2),
   (
      current_pp_flag(shlin2_full_output, on) ->
         if_not_nil(ASub, shlin2(ASub), NativeStat2, [])
      ;
         NativeStat2 = []
   ).

%------------------------------------------------------------------------
% DOMAIN ASSERTIONS
%-------------------------------------------------------------------------

:- prop shlin2group(ShLin) # "@var{ShLin} is a 2-sharing group.".

:- export(shlin2group/1).
:- test shlin2group(ShLin) : (ShLin = ([X, Y], [X, Y])) => true + (not_fails, is_det).
:- test shlin2group(ShLin) : (ShLin = ([X, Y], [X])) => true + (not_fails, is_det).
:- test shlin2group(ShLin) : (ShLin = ([X, Z], [X, Y])) + (fails, is_det).
:- test shlin2group(ShLin) : (ShLin = ([X, Y], [Y, X]))+ (fails, is_det).

shlin2group((Sh, Lin)) :-
   ordlist(var, Sh),
   ordlist(var, Lin),
   ord_subset(Lin, Sh).

:- regtype shlin2group_u(ShLin) # "@var{ShLin} is an unordered 2-sharing group.".

:- export(shlin2group_u/1).
:- test shlin2group_u(ShLin) : (ShLin = ([X, Y], [X, Y])) => true + (not_fails, is_det).
:- test shlin2group_u(ShLin) : (ShLin = ([X, Y], [X])) => true + (not_fails, is_det).
:- test shlin2group_u(ShLin) : (ShLin = ([X, Z], [X, Y])) => true + (not_fails, is_det).
:- test shlin2group_u(ShLin) : (ShLin = ([X, Y], [Y, X])) => true + (not_fails, is_det).

shlin2group_u((Sh, Lin)) :-
   list(var, Sh),
   list(var, Lin).

:- prop asub_sh(ASub_sh) # "@var{ASub_sh} is a non empty element of the Sharing domain.".

asub_sh(ASub_sh) :-
   ordlist(ordlist(var), ASub_sh).

:- prop nasub(ASub) # "@var{ASub} is a non empty abstract substitution.".

:- export(nasub/1).
:- test nasub(ASub): (ASub = []) + (not_fails, is_det).
:- test nasub(ASub): (ASub = [([X, Y], [X]), ([X, Y], [Y]), ([X, Y, Z], [X])]) + (not_fails, is_det).
:- test nasub(ASub): (ASub = [([],[]), ([X, Y], [X])]) + (fails, is_det).
:- test nasub(ASub): (ASub = [([X, Y, Z], [X]), ([Z], []), ([Y], [])]) + (fails, is_det).
:- test nasub(ASub): (ASub = [([X, Y], [X, Y]), ([X, Y], [X])]) + (fails, is_det).
:- test nasub(ASub): (ASub = [([X, Y], [X]), ([X, Y], [X, Y])]) + (fails, is_det).

nasub(ASub) :-
   (ASub = [(Sh,_Lin)|_Rest ] -> Sh \= [] ; true),
   nasub_extended(ASub).

:- prop nasub_extended(ASub) # "@var{ASub} is a non empty abstract substitution with possibly the empty sharing group.".

nasub_extended(ASub) :-
   % the empty 2-sharing group is not allowed
   ordlist(shlin2group, ASub),
   no_redundants(ASub).

no_redundants([]).
no_redundants([(Sh, Lin)|Rest]) :-
   no_redundants0(Sh, Lin, Rest),
   no_redundants(Rest).

no_redundants0(Sh, Lin, [(Sh1, Lin1)|Rest]) :-
   Sh == Sh1, !,
   % due to the ordering, if (Sh, Lin) is more general than (Sh, Lin1), it comes
   % first in the abstract substitution.
   \+ ord_subset(Lin, Lin1),
   no_redundants0(Sh, Lin, Rest).
no_redundants0(_Sh, _Lin, _Rest).

:- regtype nasub_u(ASub) # "@var{ASub} is a non empty unordered abstract substitution.".

nasub_u(ASub) :-
   list(shlin2group_u, ASub).

%-------------------------------------------------------------------------
% DOMAIN PREDICATES
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% redorder(+ASub_u,-ASub)
%
% ASub is the result of sorting abstract substitution ASub_u.
%-------------------------------------------------------------------------

:- pred reorder(+ASub_u, -ASub)
   : nasub_u * ivar => nasub(ASub)
   + (not_fails, is_det).

:- export(reorder/2).
:- test reorder(ASub_u, ASub): (ASub_u = []) => (ASub = []) + (not_fails, is_det).
:- test reorder(ASub_u, ASub): (ASub_u = [([X, Y], [X])]) => (ASub = [([X, Y], [X])]) + (not_fails, is_det).
:- test reorder(ASub_u, ASub): (ASub_u = [([X, Y], [X]), ([Y, X], [Y])])
   => (ASub = [([X, Y], [X]), ([X, Y], [Y])]) + (not_fails, is_det).

reorder(ASub_u, ASub) :-
   % sort each 2-sharing group
   sort_deep(ASub_u, ASub_u0),
   % sort the list of ordered 2-sharing groups
   sort(ASub_u0, ASub).

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
   powerset(Vars, Top_sh),
   from_sharing(Top_sh, Top).

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
:- test augment(Asub, Vars, Aug): (Asub = [], Vars = [X, Y])
   => (Aug = [ ([X], [X]), ([Y], [Y]) ]) + (not_fails, is_det).
:- test augment(Asub, Vars, Aug): (_ = [X], Asub = [([U, V], [U])], Vars = [X, Y])
   => (Aug = [ ([X], [X]), ([U,V], [U]), ([Y], [Y]) ]) + (not_fails, is_det).

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
:- test project(ASub, Vars, Proj): (ASub = [([X, Y], [X, Y]), ([X, Y, Z], [X, Y, Z]), ([Z], [Z])], Vars = [X, Y])
   => (Proj = [([X, Y], [X, Y])]) + (not_fails, is_det).
:- test project(ASub, Vars, Proj): (ASub = [([X, Y], [X]), ([X, Y, Z], [X, Y])], Vars = [X, Y])
   => (Proj = [([X, Y], [X])]) + (not_fails, is_det).

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
% Join is the lub (join) of ASub1 and ASub2.
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
   % TODO: devise a predicate combining ord_union and remove_redundants
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
:- test meet(ASub1, ASub2, Meet): (ASub1 = [([X, Y, Z], [X, Y]), ([U], [U])], ASub2 = [([X, Y, Z], [Y, Z])])
   => (Meet = [([X, Y, Z], [X, Y, Z])]) + (not_fails, is_det) .
:- test meet(ASub1, ASub2, Meet)
   : (ASub1 = [([U, V, X, Y], [U]), ([U, V, X, Y], [V])], ASub2 = [([U, V, X, Y], [X]), ([U, V, X, Y], [Y])])
   => (Meet = [([U, V, X, Y], [U, X]), ([U, V, X, Y], [U, Y]), ([U, V, X, Y], [V , X]), ([U, V, X, Y], [V, Y])])
   + (not_fails, is_det).

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

:- index meet1(?, ?, +, ?).

meet1(_Sh1, _Lin1, [], []).
meet1(Sh1, Lin1, [(Sh2, Lin2)|Rest], Meet) :-
   compare(Rel, Sh1, Sh2),
   (
      Rel = (=) ->
         ord_union(Lin1, Lin2, Lin),
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

mgu(ASub, Fv, Sub, MGU) :-
   (current_pp_flag(mgu_shlin2_optimize, optimal) ->
      mgu_optimal(ASub, Fv, Sub, MGU)
   ;
      mgu_standard(ASub, Fv, Sub, MGU)
   ).

%--------------------- OPTIMAL MGU ---------------------------
% This is the mgu in [G. Amato, F. Scozzari. On the interaction between sharing and linearity].
% http://dx.doi.org/10.1017/S1471068409990160

:- export(mgu_optimal/4).
:- test mgu_optimal(ASub, Fv, Sub, MGU): (ASub=[], Fv=[], Sub=[X=t(Y,Z), Y=Z]) => (MGU=[]) + (not_fails, is_det).
:- test mgu_optimal(ASub, Fv, Sub, MGU)
   : (ASub=[([U],[U]), ([V],[V]), ([X],[X]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=U])
   => (MGU=[([U, X], [U,X]), ([V],[V]), ([Y],[Y]), ([Z],[Z]) ]) + (not_fails, is_det).
:- test mgu_optimal(ASub, Fv, Sub, MGU)
   : (ASub=[([U],[U]), ([V],[V]), ([X],[X]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=U, Y=f(U, V)])
   => (MGU=[([U, X, Y], [U, X, Y]), ([V, Y],[V, Y]), ([Z],[Z]) ]) + (not_fails, is_det).
:- test mgu_optimal(ASub, Fv, Sub, MGU)
   : (ASub=[([U],[U]), ([V],[V]), ([X],[X]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=U, Y=f(U, V), Z=V])
   => (MGU=[([U, X, Y], [U, X, Y]), ([V, Y, Z],[V, Y, Z])]) + (not_fails, is_det).
:- test mgu_optimal(ASub, Fv, Sub, MGU)
   : (ASub=[([X,U],[X,U]), ([X,V],[X,V]), ([X,W],[W]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=f(Y, Z)])
   => (MGU=[([X,U,Y], [X,U,Y]), ([X,U,Z],[X,U,Z]), ([X,V,Y],[X,V,Y]), ([X,V,Z],[X,V,Z]), ([X,W,Y],[W]),
      ([X,W,Y,Z],[W]), ([X,W,Z],[W])]) + (not_fails, is_det).
:- test mgu_optimal(ASub, Fv, Sub, MGU)
   : (ASub=[([X,U],[X,U]), ([X,V],[X,V]), ([X,W],[W]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=f(Y, Z),W=a])
   => (MGU=[([X,U,Y], [X,U,Y]), ([X,U,Z],[X,U,Z]), ([X,V,Y],[X,V,Y]), ([X,V,Z],[X,V,Z])]) + (not_fails, is_det).
:- test mgu_optimal(ASub, Fv, Sub, MGU)
   : (ASub=[([X], []), ([X,U],[X,U]), ([X,Y],[X,Y]), ([Y,V],[Y, V])], Fv=[], Sub=[X=r(Y, Y)])
   => (MGU=[([X,U,Y],[]),([X,U,Y,V],[]),([X,Y],[]),([X,Y,V],[])]) + (not_fails, is_det).
:- test mgu_optimal(ASub, Fv, Sub, MGU)
   : (ASub=[([X, U], [X, U])], Fv=[], Sub=[X=U]) => (MGU = [([X, U], [])]) + (not_fails, is_det).
:- test mgu_optimal(ASub, Fv, Sub, MGU)
   : (ASub=[([X, Y], [X])], Fv=[], Sub=[X=Y]) => (MGU = [([X,Y], [])]) + (not_fails, is_det).

:- index mgu_optimal(?, ?, +, ?).

mgu_optimal(ASub, _Fv, [], ASub).
mgu_optimal(ASub, Fv, [X=T|Rest], MGU) :-
   mgu_binding_optimal(ASub, X, T, MGU0),
   remove_redundants(MGU0, MGU1),
   mgu_optimal(MGU1, Fv, Rest, MGU).

mgu_binding_optimal(ASub, X, T, MGU) :-
   bag_vars(T, Bt),
   mgu_split_optimal(ASub, [X-1], Bt, NRel, Rel_x_lin, Rel_x_nlin, Rel_t_lin, Rel_t_nlin, Rel_t_snlin, Rel_xt_linx,
                                      Rel_xt_lint, Rel_xt_linxt, Rel_xt_nlin),
   star_union(Rel_x_lin, Rel_x_lin_star),
   star_union(Rel_x_nlin, Rel_x_nlin_star),
   star_union(Rel_t_lin, Rel_t_lin_star),
   star_union(Rel_t_nlin, Rel_t_nlin_star),
   star_union(Rel_t_snlin, Rel_t_snlin_star),
   star_union(Rel_xt_linx, Rel_xt_linx_star),
   star_union(Rel_xt_lint, Rel_xt_lint_star),
   star_union(Rel_xt_linxt, Rel_xt_linxt_star),
   star_union(Rel_xt_nlin, Rel_xt_nlin_star),
   % first case
   bin_all([
      [([],[])|Rel_x_lin_star], [([],[])|Rel_x_nlin_star], [([],[])|Rel_t_lin_star], [([],[])|Rel_t_nlin_star],
      [([],[])|Rel_t_snlin_star], [([],[])|Rel_xt_linx_star], [([],[])|Rel_xt_lint_star], [([],[])|Rel_xt_linxt_star],
      [([],[])|Rel_xt_nlin_star]
   ], Rel_x_plus),
   merge_list_of_lists([Rel_x_nlin, Rel_xt_nlin, Rel_xt_lint], Rel_x_nlin0),
   merge_list_of_lists([Rel_t_nlin, Rel_t_nlin, Rel_t_snlin, Rel_xt_nlin, Rel_xt_linx], Rel_t_nlin0),
   bin_all([Rel_x_nlin0,  Rel_x_plus, Rel_t_nlin0], Bin1),
   % second case
   bin_all([Rel_t_lin_star, [([],[])|Rel_xt_lint_star], [([],[])|Rel_xt_linxt_star], Rel_x_nlin], Bin2a),
   bin_all([Rel_t_lin_star, Rel_xt_lint_star, [([],[])|Rel_xt_linxt_star]], Bin2b),
   ord_union(Bin2a, Bin2b, Bin2),
   % third case
   bin_all([Rel_x_lin_star, [([],[])|Rel_xt_linx_star], [([],[])|Rel_xt_linxt_star], Rel_t_snlin], Bin3a),
   bin_all([Rel_x_lin_star, Rel_xt_linx_star, [([],[])|Rel_xt_linxt_star]], Bin3b),
   ord_union(Bin3a, Bin3b, Bin3),
   % fourth case
   ord_union(Rel_t_lin, Rel_t_nlin, Rel_t_nat),
   mgu_binding_optimal0([([],[])|Rel_t_nat], Rel_x_lin, Bt, Bin4a),
   ( Bin4a == [] -> Bin4 = Rel_xt_linxt_star ; bin([([],[])|Rel_xt_linxt_star], Bin4a, Bin4) ),
   % fifth case
   ord_union(Rel_xt_linx, Rel_xt_nlin, Rel_xt_nlin0),
   mgu_filter_linearizable(Rel_xt_nlin0, Bt, Rel_xt_linearizable0),
   ord_union(Rel_xt_linx, Rel_xt_linearizable0, Rel_xt_linearizable),
   star_union(Rel_xt_linearizable, Rel_xt_linearizable_star),
   % put all togethet
   merge_list_of_lists([NRel, Bin1, Bin2, Bin3, Bin4, Rel_xt_linearizable_star], MGU).

mgu_binding_optimal0([], _, _, []) :- !.
mgu_binding_optimal0([ShLin|Rest], Rel_x_lin, Bt, MGU) :-
   ShLin = (Sh, Lin),
   chiMax(Sh, Lin, Bt, Mult),
   % TODO: memoize these values ?
   star_union_limited(Rel_x_lin, Mult, Rel_x_lin_star),
   bin(Rel_x_lin_star, [ShLin], MGU0),
   mgu_binding_optimal0(Rest, Rel_x_lin, Bt, MGU1),
   ord_union(MGU0, MGU1, MGU).

star_union_limited(S, N, Star) :-
   star_union_limited0(S, N, empty, Star).

star_union_limited0(_S, 0, _, [([],[])]) :- !.
star_union_limited0(_S, N, _, []) :- N < 0, !.
star_union_limited0([], _N, yes, [([],[])]) :- !.
star_union_limited0([], _N, _, []) :- !.
star_union_limited0([(Sh, Lin)|Xs], N, Full, S) :-
   N1 is N-1,
   star_union_limited0(Xs, N1, no, S1),
   bin([(Sh, Lin)], S1, Res1),
   N2 is N-2,
   ( Full \= no -> Full0 = yes ; Full0 = no ),
   star_union_limited0(Xs, N2, Full0, S2),
   bin([(Sh, [])], S2, Res2),
   star_union_limited0(Xs, N, Full, Res3),
   merge_list_of_lists([Res1, Res2, Res3], S).

mgu_split_optimal([], _, _, [], [], [], [], [], [], [], [], [], []).
mgu_split_optimal([ShLin|Rest], Bx, Bt, NRel, Rel_x_lin, Rel_x_nlin, Rel_t_lin, Rel_t_nlin, Rel_t_snlin, Rel_xt_linx,
                  Rel_xt_lint, Rel_xt_linxt, Rel_xt_nlin) :-
   ShLin = (Sh, Lin),
   chiMax(Sh, Lin, Bx, Mulx),
   chiMax(Sh, Lin, Bt, Mult),
   (
      Mulx = 0 -> (
         Mult = 0 ->
            NRel = [ShLin|NRel0],
            mgu_split_optimal(Rest, Bx, Bt, NRel0, Rel_x_lin, Rel_x_nlin, Rel_t_lin, Rel_t_nlin, Rel_t_snlin,
                              Rel_xt_linx, Rel_xt_lint, Rel_xt_linxt, Rel_xt_nlin)
         ; Mult = 1 ->
            Rel_t_lin = [ShLin|Rel_t_lin0],
            mgu_split_optimal(Rest, Bx, Bt, NRel, Rel_x_lin, Rel_x_nlin, Rel_t_lin0, Rel_t_nlin, Rel_t_snlin,
                              Rel_xt_linx, Rel_xt_lint, Rel_xt_linxt, Rel_xt_nlin)
         ; Mult = inf ->
            Rel_t_snlin = [ShLin|Rel_t_snlin0],
            mgu_split_optimal(Rest, Bx, Bt, NRel, Rel_x_lin, Rel_x_nlin, Rel_t_lin, Rel_t_nlin, Rel_t_snlin0,
                              Rel_xt_linx, Rel_xt_lint, Rel_xt_linxt, Rel_xt_nlin)
         ;
            Rel_t_nlin = [ShLin|Rel_t_nlin0],
            mgu_split_optimal(Rest, Bx, Bt, NRel, Rel_x_lin, Rel_x_nlin, Rel_t_lin, Rel_t_nlin0, Rel_t_snlin,
                              Rel_xt_linx, Rel_xt_lint, Rel_xt_linxt, Rel_xt_nlin)
      ) ; Mulx = 1 -> (
         Mult = 0 ->
            Rel_x_lin = [ShLin|Rel_x_lin0],
            mgu_split_optimal(Rest, Bx, Bt, NRel, Rel_x_lin0, Rel_x_nlin, Rel_t_lin, Rel_t_nlin, Rel_t_snlin,
                              Rel_xt_linx, Rel_xt_lint, Rel_xt_linxt, Rel_xt_nlin)
         ; Mult = 1 ->
            Rel_xt_linxt = [ShLin|Rel_xt_linxt0],
            mgu_split_optimal(Rest, Bx, Bt, NRel, Rel_x_lin, Rel_x_nlin, Rel_t_lin, Rel_t_nlin, Rel_t_snlin,
                              Rel_xt_linx, Rel_xt_lint, Rel_xt_linxt0, Rel_xt_nlin)
         ;
            Rel_xt_linx = [ShLin|Rel_xt_linx0],
            mgu_split_optimal(Rest, Bx, Bt, NRel, Rel_x_lin, Rel_x_nlin, Rel_t_lin, Rel_t_nlin, Rel_t_snlin,
                              Rel_xt_linx0, Rel_xt_lint, Rel_xt_linxt, Rel_xt_nlin)
      ) ; (
         Mult = 0 ->
            Rel_x_nlin = [ShLin|Rel_x_nlin0],
            mgu_split_optimal(Rest, Bx, Bt, NRel, Rel_x_lin, Rel_x_nlin0, Rel_t_lin, Rel_t_nlin, Rel_t_snlin,
                              Rel_xt_linx, Rel_xt_lint, Rel_xt_linxt, Rel_xt_nlin)
         ; Mult = 1 ->
            Rel_xt_lint = [ShLin|Rel_xt_lint0],
            mgu_split_optimal(Rest, Bx, Bt, NRel, Rel_x_lin, Rel_x_nlin, Rel_t_lin, Rel_t_nlin, Rel_t_snlin,
                              Rel_xt_linx, Rel_xt_lint0, Rel_xt_linxt, Rel_xt_nlin)
         ;
            Rel_xt_nlin = [ShLin|Rel_xt_nlin0],
            mgu_split_optimal(Rest, Bx, Bt, NRel, Rel_x_lin, Rel_x_nlin, Rel_t_lin, Rel_t_nlin, Rel_t_snlin,
                              Rel_xt_linx, Rel_xt_lint, Rel_xt_linxt, Rel_xt_nlin0)
      )
   ).

mgu_filter_linearizable([], _, []).
mgu_filter_linearizable([ShLin|Rest], Bt, [ShLin|LinRest]) :-
   ShLin = (Sh, _),
   linearizable(Sh, Bt), !,
   mgu_filter_linearizable(Rest, Bt, LinRest).
mgu_filter_linearizable([_ShLin|Rest], Bt, LinRest) :-
   mgu_filter_linearizable(Rest, Bt, LinRest).

%--------------------- STANDARD MGU ---------------------------
% This is the mgu in [A. King, A synergistic analysis for sharing and groundness which traces linearity]
% https://dx.doi.org/10.1007/3-540-57880-3_24

:- export(mgu_standard/4).
:- test mgu_standard(ASub, Fv, Sub, MGU): (ASub=[], Fv=[], Sub=[X=t(Y,Z), Y=Z]) => (MGU=[]) + (not_fails, is_det).
:- test mgu_standard(ASub, Fv, Sub, MGU)
   : (ASub=[([U],[U]), ([V],[V]), ([X],[X]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=U])
   => (MGU=[([U, X], [U,X]), ([V],[V]), ([Y],[Y]), ([Z],[Z]) ]) + (not_fails, is_det).
:- test mgu_standard(ASub, Fv, Sub, MGU)
   : (ASub=[([U],[U]), ([V],[V]), ([X],[X]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=U, Y=f(U, V)])
   => (MGU=[([U, X, Y], [U, X, Y]), ([V, Y],[V, Y]), ([Z],[Z]) ]) + (not_fails, is_det).
:- test mgu_standard(ASub, Fv, Sub, MGU)
   : (ASub=[([U],[U]), ([V],[V]), ([X],[X]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=U, Y=f(U, V), Z=V])
   => (MGU=[([U, X, Y], [U, X, Y]), ([V, Y, Z],[V, Y, Z])]) + (not_fails, is_det).
:- test mgu_standard(ASub, Fv, Sub, MGU)
   : (ASub=[([X,U],[X,U]), ([X,V],[X,V]), ([X,W],[W]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=f(Y, Z)])
   => (MGU=[([X,U,Y], [X,U,Y]), ([X,U,Z],[X,U,Z]), ([X,V,Y],[X,V,Y]), ([X,V,Z],[X,V,Z]), ([X,W,Y],[W]),
      ([X,W,Y,Z],[W]), ([X,W,Z],[W])]) + (not_fails, is_det).
:- test mgu_standard(ASub, Fv, Sub, MGU)
   : (ASub=[([X,U],[X,U]), ([X,V],[X,V]), ([X,W],[W]), ([Y],[Y]), ([Z],[Z])], Fv=[], Sub=[X=f(Y, Z),W=a])
   => (MGU=[([X,U,Y], [X,U,Y]), ([X,U,Z],[X,U,Z]), ([X,V,Y],[X,V,Y]), ([X,V,Z],[X,V,Z])]) + (not_fails, is_det).
:- test mgu_standard(ASub, Fv, Sub, MGU)
   : (ASub=[([X, U], [X, U])], Fv=[], Sub=[X=U]) => (MGU = [([X, U], [])]) + (not_fails, is_det).
:- test mgu_standard(ASub, Fv, Sub, MGU)
   : (ASub=[([X, Y], [X])], Fv=[], Sub=[X=Y]) => (MGU = [([X,Y], [])]) + (not_fails, is_det).
:- test mgu_standard(ASub, Fv, Sub, MGU)
   : (ASub=[([U, V], [U]), ([U, X], [U, X]), ([V],[V]), ([X],[X])], Fv=[], Sub=[X=V])
   => (MGU = [([U,V,X],[]),([V,X],[V,X])] ) + (not_fails, is_det).

:- index mgu_standard(?, ?, +, ?).

mgu_standard(ASub, _Fv, [], ASub).
mgu_standard(ASub, Fv, [X=T|Rest], MGU) :-
   mgu_binding_standard(ASub, X, T, MGU0),
   mgu_standard(MGU0, Fv, Rest, MGU).

mgu_binding_standard(ASub, X, T, MGU) :-
   bag_vars(T, Bt),
   mgu_split_standard(ASub, [X-1], NRel_x, Rel_x_lin, Rel_x_nlin),
   mgu_split_standard(ASub, Bt, NRel_t, Rel_t_lin, Rel_t_nlin),
   ord_intersection(NRel_x, NRel_t, NRel),
   (
      Rel_x_nlin == [], ord_subset(Rel_x_lin, NRel_t) ->
         bin(Rel_x_lin, Rel_t_lin, ASub1),
         star_union(Rel_x_lin, Rel_x_lin_star),
         bin(Rel_x_lin_star, Rel_t_nlin, ASub2),
         ord_union(ASub1, ASub2, ASub3),
         remove_redundants(ASub3, ASub4),
         ord_union(NRel, ASub4, MGU)
      ; Rel_t_nlin == [], ord_subset(Rel_t_lin, NRel_x) ->
         bin(Rel_t_lin, Rel_x_lin, ASub1),
         star_union(Rel_t_lin, Rel_t_lin_star),
         bin(Rel_t_lin_star, Rel_x_nlin, ASub2),
         ord_union(ASub1, ASub2, ASub3),
         remove_redundants(ASub3, ASub4),
         ord_union(NRel, ASub4, MGU)
      ;
         ord_union(Rel_x_lin, Rel_x_nlin, Rel_x),
         star_union(Rel_x, Rel_x_star),
         ord_union(Rel_t_lin, Rel_t_nlin, Rel_t),
         star_union(Rel_t, Rel_t_star),
         bin(Rel_x_star, Rel_t_star, ASub1),
         ord_union(NRel, ASub1, MGU)
   ).

:- pred mgu_split_standard(+ASub, +Bt, -NRel, -Rel_lin, -Rel_nlin)
   : nasub * isbag(var) * ivar * ivar * ivar => (nasub(NRel), nasub(Rel_lin), nasub(Rel_nlin))
   + (not_fails, is_det)
   # "Split the 2-sharing groups in @var{ASub} wrt the bag of variables @var{Bt},
   in the not-relevant, relevant linear and relevant non-linear groups.".

:- export(mgu_split_standard/5).
:- test mgu_split_standard(ASub, Bt, NRel, Rel_lin, Rel_nlin): (ASub=[], Bt=[X-2,Y-3])
   => (NRel=[], Rel_lin=[], Rel_nlin=[]) + (not_fails, is_det).
:- test mgu_split_standard(ASub, Bt, NRel, Rel_lin, Rel_nlin)
   : (ASub=[([X, Y],[Y]), ([X, Z],[X, Z]), ([Z],[])], Bt=[X-1,Y-2])
   => (NRel=[ ([Z],[])], Rel_lin=[([X, Z],[X, Z])], Rel_nlin=[([X, Y],[Y])]) + (not_fails, is_det).

mgu_split_standard([], _Bt, [], [], []).
mgu_split_standard([(Sh, Lin)|Rest], Bt, NRel, Rel_lin, Rel_nlin) :-
   mgu_split_standard(Rest, Bt, NRel0, Rel_lin0, Rel_nlin0),
   chiMax(Sh, Lin, Bt, Mul),
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

%-------------------------------------------------------------------------
% match(+Prime,+Pv,+Call,-Match)
%
% Match is the abstract matching between Prime (over the variables in Pv)
% and Call, where Prime is the abstract substitution which should not be
% further instantiated.
%
% With respect to the general definition of matching, we only consider
% the special case in which the variables in Call (not even provided
% explicitly as input) are a superset of Pv.
%-------------------------------------------------------------------------

:- pred match(+Prime, +Pv, +Call, -Match)
   : nasub * {ordlist(var), superset_vars_of(Prime)} * nasub * ivar => nasub(Match)
   + (not_fails, is_det).

:- export(match/4).
:- test match(Prime, Pv, Call, Match)
   : (Prime=[([X, Y],[])], Pv=[X, Y, Z], Call=[([X, Y], [X]), ([Y, U], [U]), ([Z, U], []), ([U],[U])])
   => (Match=[([X, Y],[]), ([X, Y, U],[]), ([U],[U])]) + (not_fails, is_det).
:- test match(Prime, Pv, Call, Match)
   : (Prime=[([X],[])], Pv=[X, Y, Z], Call=[([X], [X]),  ([X, U], [X, U]), ([X, V], [V]), ([U, V],[U, V])])
   => (Match=[([X],[]), ([X, U], []), ([X, U, V],[]), ([X, V],[]), ([U,V], [U,V])]) + (not_fails, is_det).
:- test match(Prime, Pv, Call, Match)
   : (Prime=[([X],[X])], Pv=[X], Call=[([X, Y], [X]), ([X, Z], [X])])
   => (Match=[([X,Y],[X]),([X,Z],[X])]) + (not_fails, is_det).

match(Prime, Pv, Call, Match) :-
   rel(Call, Pv, Rel, NRel),
   powerset(Rel, Rel_subs),
   match0(Prime, Pv, Rel_subs, Match0),
   remove_redundants(Match0, Match1),
   ord_union(NRel, Match1, Match).

:- index match0(?, ?, +, ?).

match0(_Prime, _Pv, [], []).
match0(Prime, Pv, [X|Rest_subs], Match) :-
   upluslist(X, (X_sh, X_lin)),
   match1(Prime, Pv, X, X_sh, X_lin, Match0),
   match0(Prime, Pv, Rest_subs, RestMatch),
   ord_union(Match0, RestMatch, Match).

match1([], _Pv, _X, _X_sh, _X_lin,  []).
match1([(Sh, Lin)|Rest], Pv, X, X_sh, X_lin, [Match|RestMatch]) :-
   ord_intersection(X_sh, Pv, X_sh_restricted),
   ord_intersection(X_lin, Pv, X_lin_restricted),
   ord_subset(Lin, X_lin_restricted),
   X_sh_restricted == Sh, !,
   relbar(X, Lin, X_bar),
   upluslist(X_bar, (X_bar_sh, _)),
   ord_subtract(X_lin, X_bar_sh, Lin1),
   Match = (X_sh, Lin1),
   match1(Rest, Pv, X, X_sh, X_lin, RestMatch).
match1([_|Rest], Pv, X, X_sh, X_lin, Match) :-
   match1(Rest, Pv, X, X_sh, X_lin, Match).

relbar([], _Vars, []).
relbar([(Sh, Lin)|Rest], Vars, [(Sh, Lin)|RestBar]) :-
   ord_disjoint(Vars, Lin), !,
   relbar(Rest, Vars, RestBar).
relbar([_|Rest], Vars, RestBar) :-
   relbar(Rest, Vars, RestBar).

%-------------------------------------------------------------------------
% make_ground(+Call,+Gv,+Succ).
%
% Succ is the result of grounding the variable in Gv in the abstract
% substitution Call.
%-------------------------------------------------------------------------

:- pred make_ground(+Call, +Gv, -Succ)
   : nasub * ordlist(var) * ivar => nasub(Succ)
   + (not_fails, is_det).

make_ground(Call, Gv, Succ) :-
   rel(Call, Gv, _, Succ).

%-------------------------------------------------------------------------
% restrict_var(+Call,+V,+Succ).
%
% Succ is the result of restringing the abstract substitution Call to the
% case when V is a variable.
%-------------------------------------------------------------------------

:- pred restrict_var(+Call, +V, -Succ)
   : nasub * var * ivar => nasub(Succ)
   + (not_fails, is_det).

restrict_var(Call, V, Succ) :-
   possible_nonground(V, Call), !,
   make_linear(Call, V, Succ).
restrict_var(_Call, _, '$bottom').

make_linear([], _, []).
make_linear([(Sh, Lin)|Rest], V, [(Sh, Lin0)|Rest0]) :-
   insert(Lin, V, Lin0),
   make_linear(Rest, V, Rest0).

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
:- test from_shlin(Sh, Lin, ASub): (Sh = [[X], [X,Z]], Lin=[X, Y] )
   => (ASub = [([X], [X]), ([X,Z], [X])]) + (not_fails, is_det).

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

vars([], []).
vars([(Sh, _Lin)|Rest], Vars) :-
   vars(Rest, RestVars),
   ord_union(RestVars, Sh, Vars).

:- pred ground(ASub, Vars, Ground)
   : nasub * {ordlist(var), superset_vars_of(ASub)} * ivar
   => ( ordlist(var, Ground), independent_from(ASub, Ground), superset_vars_of(Ground, Vars) )
   + (not_fails, is_det)
   # "@{Ground} is the set of ground variables the abstract substitution @{ASub} w.r.t. the variables
   of interest in @{Vars}".
:- export(ground/3).

ground(ASub, Vars, Ground) :-
   vars(ASub, NGv),
   ord_subtract(Vars, NGv, Ground).

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

:- pred nlin(+ASub, -NLin)
   : nasub * ivar => ordlist(var, NLin)
   + (not_fails, is_det)
   # "@var{NLin} is the set of possible non-linear variables in the abstract
   substitution @var{ASub}.".
:- export(nlin/2).
:- test nlin(ASub, Lin): (ASub = []) => (Lin = []) + (not_fails, is_det).
:- test nlin(ASub, Lin): (ASub = [([X], [X]), ([X,Z], [X])]) => (Lin = [Z]) + (not_fails, is_det).
:- test nlin(ASub, Lin): (ASub = [([X], [X]), ([X,Z], [X]), ([X, Z, Y], [X, Z, Y])])
   => (Lin = [Z]) + (not_fails, is_det).

nlin([], []).
nlin([(Sh, Lin)|Rest], NLin) :-
   nlin(Rest, RestNLin),
   ord_subtract(Sh, Lin, NLin0),
   ord_union(NLin0, RestNLin, NLin).

:- pred lin(+ASub, -Lin)
   : nasub * ivar => ordlist(var, Lin)
   + (not_fails, is_det)
   # "@var{Lin} is the set of definite linear non-ground variables in the abstract
   substitution @var{ASub}.".
:- export(lin/2).
:- test lin(ASub, Lin): (ASub = []) => (Lin = []) + (not_fails, is_det).
:- test lin(ASub, Lin): (ASub = [([X], [X]), ([X,Z], [X])]) => (Lin = [X]) + (not_fails, is_det).
:- test lin(ASub, Lin): (ASub = [([X], [X]), ([X,Z], [X]), ([X, Z, Y], [X, Z, Y])])
   => (Lin = [X, Y]) + (not_fails, is_det).

lin(ASub, Lin) :-
   vars(ASub, Vars),
   nlin(ASub, NLin),
   ord_subtract(Vars, NLin, Lin).

:- pred linearize(+ASub, +Lin, -ASubLin)
   : nasub * ordlist(var) * ivar => nasub(ASubLin)
   + (not_fails, is_det)
   # "@var{ASubLin} is the abstract substitution obtained from @var{ASub} by making linear all
   variables in @var{Lin}.".

linearize(ASub, Lin, ASubLin) :-
   linearize0(ASub, Lin, ASubLin0),
   remove_redundants(ASubLin0, ASubLin).

linearize0([], _, []).
linearize0([(Sh, Lin0)|Rest0], Lin, [(Sh, Lin1)|Rest1]) :-
   ord_intersection(Sh, Lin, LinNew),
   ord_union(LinNew, Lin0, Lin1),
   linearize0(Rest0, Lin, Rest1).

:- pred uplus(ShLin1, ShLin2, UPlus)
   : shlin2group * shlin2group * ivar => shlin2group(UPlus)
   + (not_fails, is_det)
   # "@var{UPlus} is the union of the 2-sharing groups @var{ShLin1} and @var{ShLin2}.".

:- export(uplus/3).
:- test uplus(ShLin1, ShLin2, UPlus): (ShLin1 = ([X, Y], [X]), ShLin2 = ([X, Z], [X, Z]))
   => (UPlus = ([X, Y, Z], [Z])) + (not_fails, is_det).

uplus((Sh1, Lin1), (Sh2, Lin2), (Sh, Lin)) :-
   ord_union(Sh1, Sh2, Sh),
   ord_subtract(Lin1, Sh2, Lina),
   ord_subtract(Lin2, Sh1, Linb),
   ord_union(Lina, Linb, Lin).

:- pred upluslist(+List, ?UPlus)
   : list(shlin2group, List) => shlin2group(UPlus)
   + (not_fails, is_det)
   # "@var{UPlus} is the union of the 2-sharing groups in @var{List}.".

:- test upluslist(List, UPlus): (List = [([X, Y], [X]), ([X, Z], [X, Z]), ([Y, U], [Y, U])])
   => (UPlus = ([X, Y, Z, U], [Z, U])) + (not_fails, is_det).

upluslist([], ([],[])).
upluslist([ShLin], ShLin).
upluslist([ShLin1, ShLin2|Rest], UPlus) :-
   uplus(ShLin1, ShLin2, ShLin),
   upluslist([ShLin|Rest], UPlus).

:- pred bin(+ASub1, +ASub2, -Bin)
   : nasub_extended * nasub_extended * ivar => nasub_extended(Bin)
   + (not_fails, is_det)
   # "@var{Bin} is the combination of two abstract substitutions @var{ASub1} and @var{ASub2}.".

:- export(bin/3).
:- test bin(ASub1, ASub2, Bin): (ASub1 = [], ASub2 = [([X], [X])]) => (Bin = []) + (not_fails, is_det).
:- test bin(ASub1, ASub2, Bin): (ASub2 = [], ASub1 = [([X], [X])]) => (Bin = [])+ (not_fails, is_det).
:- test bin(ASub1, ASub2, Bin): (ASub1 = [([X, Y], [X, Y])], ASub2 = [([X], [X]), ([Z], [Z])])
   => (Bin = [([X, Y], [Y]), ([X, Y, Z], [X, Y, Z])]) + (not_fails, is_det).
:- test bin(ASub1, ASub2, Bin): (ASub1 = [([X], [X]), ([Y], [Y])], ASub2 = [([X], [X]), ([Y], [Y])])
   => (Bin = [([X], []), ([X, Y], [X, Y]), ([Y], [])]) + (not_fails, is_det).
:- test bin(ASub1, ASub2, Bin): (ASub1 = [([X], [X]), ([Y], [Y])], ASub2 = [([X, Y], []), ([Y], [Y])])
   => (Bin = [ ([X, Y], []), ([Y], [])]) + (not_fails, is_det).

bin(Sh1, Sh2, Bin) :-
   bin0(Sh1, Sh2, Bin0),
   remove_redundants(Bin0, Bin).

% TODO: for some strange reason, without the cut the program becomes non-deterministic
bin0([], _, []).
bin0([X|Rest], Sh, Bin) :-
   bin0(Rest, Sh, RestBin),
   bin1(X, Sh, BinX),
   ord_union(RestBin, BinX, Bin).

%:- index bin1(?, +, ?, ?).

bin1(_, [], []).
bin1(ShLin1, [ShLin2|Rest], Bin) :-
   bin1(ShLin1, Rest, RestBin),
   uplus(ShLin1, ShLin2, ShLin),
   insert(RestBin, ShLin, Bin).

:- pred bin_all(+ShLinList, -Bin)
   : list(nasub_extended) * ivar => nasub_extended(Bin)
   + (not_fails, is_det)
   # "@var{Bin} is the bin operator applied to all sharing sets in @var{ShLinList}.".
:- export(bin_all/2).

bin_all([], []).
bin_all([X], X).
bin_all([X,Y|Rest], Bin) :-
   bin(X, Y, Bin0),
   bin_all([Bin0|Rest], Bin).

:- pred star_union(+ASub, -Star)
   : nasub * ivar => nasub(Star)
   + (not_fails, is_det)
   # "@var{Star} is the star union of @var{ASub}.".

:- export(star_union/2).
:- test star_union(ASub, Star): (ASub = []) => (Star = []) + (not_fails, is_det).
:- test star_union(ASub, Star): (ASub = []) => (Star = []) + (not_fails, is_det).
:- test star_union(ASub, Star): (ASub = [([X], [X])]) => (Star = [([X], [])]) + (not_fails, is_det).
:- test star_union(ASub, Star): (ASub = [([X], [X]), ([Y],  [Y])])
   => (Star = [([X], []), ([X, Y], []), ([Y], [])]) + (not_fails, is_det).

star_union(ASub, Star):-
   sharing(ASub, Sh),
   closure_under_union(Sh, Star_sh),
   from_sharing(Star_sh, Star).

:- pred rel(+ASub, +Vars, -Rel, -NRel)
   : nasub * ordlist(var) * ivar * ivar => (nasub(Rel), nasub(NRel))
   + (not_fails, is_det)
   # "@var{Rel} is the set of relevant sharing groups in @var{ASub} wrt the variables in @var{Vars}.".

:- export(rel/4).
:- test rel(ASub, Vars, Rel, NRel): (ASub = [], Vars = [X, Y]) => (Rel = []) + (not_fails, is_det).
:- test rel(ASub, Vars, Rel, NRel):
   (ASub = [([X, Y], [X, Y]), ([X, Y, Z], [X, Y, Z]), ([Z], [Z])], Vars = [X, Y])
   => (Rel = [([X, Y], [X, Y]), ([X, Y, Z], [X, Y, Z])]) + (not_fails, is_det).

rel([], _Vars, [], []).
rel([(Sh, Lin)|Rest], Vars, Rel, NRel) :-
   ( ord_disjoint(Sh, Vars) ->
      NRel = [(Sh, Lin)|NRel0],
      Rel = Rel0
   ;
      NRel = NRel0,
      Rel = [(Sh, Lin)|Rel0]
   ),
   rel(Rest, Vars, Rel0, NRel0).

:- pred sort_deep(L0, L1)
   : list(shlin2group_u) * ivar => list(shlin2group, L1).
   + (not_fails, is_det)
   # "@var{L1} is the result of sorting each of the 2-sharing groups in the list @var{L0}.".

sort_deep([], []).
sort_deep([(Sh_u, Lin_u)|Rest_u], [(Sh, Lin)|Rest]) :-
   sort(Sh_u, Sh),
   sort(Lin_u, Lin),
   sort_deep(Rest_u, Rest).

:- pred remove_redundants(OL, ASub)
   : ordlist(shlin2group) * ivar => nasub(ASub)
   + (not_fails, is_det)
   # "@var{ASub} is the abstract substitution resulting from removing the redundant 2-sharing groups in the
   ordered list @var{OL}.".

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

:- pred possible_nonground(+ASub, +V)
   : nasub * var
   + (is_det)
   # "True if the variable @var{V} is a possible non-ground variable in the abstract substitution @var{ASub}".

possible_nonground([(Sh, _Lin)|_Rest], V) :-
   ord_member(V, Sh), !.
possible_nonground([_|Rest], V) :-
   possible_nonground(Rest, V).