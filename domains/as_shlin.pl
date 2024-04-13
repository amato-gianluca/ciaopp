:- module(as_shlin, [], [assertions, regtypes, basicmodes, nativeprops, indexer, fsyntax]).

:- use_package(debug).
:- use_package(rtchecks).
%:- use_module(library(format)).

:- doc(title, "Sharing * Lin abstract domain").
:- doc(module,"
This module is an independent reimplementation of the Sharing * Lin abstract domain.
The optimal mgu algorithm is implemented following [G. Amato, F. Scozzari. On the interaction
between sharing and linearity. http://dx.doi.org/10.1017/S1471068409990160].
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
   list(var, X), !,
   sort(X, X1),
   ord_union(Lin0, X1, Lin).
input_interface(free(X), perfect, (Sh, Lin0), (Sh, Lin)) :-
   var(X), !,
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
   ground(Sh, Qv, Gv),
   if_not_nil(Gv, ground(Gv), NativeStat0, NativeStat1),
   if_not_nil(Lin, linear(Lin), NativeStat1, []).

%------------------------------------------------------------------------
% DOMAIN ASSERTIONS
%-------------------------------------------------------------------------

:- prop nasub(ASub) # "@var{ASub} is a non empty abstract substitution".
:- redefining(nasub/1).

nasub((Sh, Lin)) :-
   asub_sh(Sh),
   ordlist(var, Lin),
   % Lin only contains variables in Sh, since ground variables are linear by definition
   vars(Sh, VSh),
   ord_subset(Lin, VSh).

:- regtype nasub_u(ASub) # "@var{ASub} is a non empty unordered abstract substitution".
:- redefining(nasub_u/1).

nasub_u((Sh, Lin)) :-
   asub_sh_u(Sh),
   list(var, Lin).

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
:- redefining(reorder/2).

reorder((Sh_u, Lin_u), (Sh, Lin)) :-
   as_sharing:reorder(Sh_u, Sh),
   sort(Lin_u, Lin).

%-------------------------------------------------------------------------
% top(+Vars,+Top)
%
% Top is the largest abstract substitution on variable Vars.
%-------------------------------------------------------------------------

:- pred top(+Vars, -Top)
   : ordlist(var) * ivar => nasub(Top)
   + (not_fails, is_det).
:- redefining(top/2).

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
:- redefining(augment/3).

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
:- redefining(project/3).

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
:- redefining(join/3).

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
:- redefining(meet/3).

meet((Sh1, Lin1), (Sh2, Lin2), (Meet_sh, Meet_lin)):-
   as_sharing:meet(Sh1, Sh2, Meet_sh),
   ord_union(Lin1, Lin2, Lin),
   vars(Meet_sh, Vars),
   ord_intersection(Lin, Vars, Meet_lin).

%-------------------------------------------------------------------------
% mgu(+ASub,Fv,+Sub,-MGU)
%
% MGU is the result of the unification of ASub with the substitution Sub.
% Variables in Fv are considered to be free.
%-------------------------------------------------------------------------

:- pred mgu(+ASub, +Fv, +Sub, -MGU)
   : nasub * ordlist(var) * unifier_no_cyclic * ivar => nasub(MGU)
   + (not_fails, is_det).
:- redefining(mgu/4).

mgu(ASub, Fv, Sub, MGU) :-
   (current_pp_flag(mgu_shlin2_optimize, optimal) ->
      mgu_optimal(ASub, Fv, Sub, MGU)
   ;
      mgu_standard(ASub, Fv, Sub, MGU)
   ).

%--------------------- OPTIMAL MGU ---------------------------
% This is the mgu in [G. Amato, F. Scozzari. On the interaction between sharing and linearity].
% http://dx.doi.org/10.1017/S1471068409990160

mgu_optimal(ShLin, _Fv, [], ShLin).
mgu_optimal(ShLin, Fv, [X=T|Rest], MGU) :-
   mgu_binding_optimal(ShLin, X, T, MGU0),
   mgu(MGU0, Fv, Rest, MGU).

mgu_binding_optimal(ShLin, X, T, (MGU_sh, MGU_lin)) :-

   ShLin = (Sh, Lin),
   bag_vars(T, Bt),
   mgu_split(Sh, Lin, Bt, X, Sh_x, Sh_t,
             Rel_t_inf, Rel_t_one, Rel_t_nat, Rel_t_nlin,
             Rel_xt_one, Rel_xt_linearizable, Rel_xt_nlin, Rel_x, NRel),
   (Rel_t_nlin = [], Rel_xt_nlin=[] -> Lint = yes ; Lint = no),
   % if X is ground we put Linx=no, but this does not change the result
   (ord_member(X, Lin) -> Linx = yes ; Linx = no),
   (
      Linx = yes ->
         star_union(Rel_x, Rel_x_plus),
         ord_union(Rel_xt_one, Rel_xt_linearizable, Rel_xt),
         star_union_real(Rel_xt, Rel_xt_star),
         bin(Rel_x_plus, Rel_xt_star, BinTmp0),
         bin(Rel_t_inf, BinTmp0, Bin0),
         bin_all([[[]|Rel_xt], Rel_xt_nlin, BinTmp0], Bin1),
         powerset(Rel_x, Rel_x_power),
         mgu_binding_optimal0(Rel_t_nat, Rel_x_power, Bt, Lin, Rel_a),
         star_union_real(Rel_xt_one, Rel_xt_one_star),
         bin(Rel_a, Rel_xt_one_star, Bin2),
         star_union(Rel_xt_linearizable, Rel_xt_linearizable_plus),
         merge_list_of_lists([Bin0, Bin1, Bin2, Rel_xt_linearizable_plus], BinRes)
      ;
         ord_union(Rel_xt_nlin, Rel_t_nlin, Rel_a),
         ord_union(Sh_t, Sh_x, Rel),
         star_union_real(Rel, Rel_star),
         bin_all([Rel_a, Sh_x, Rel_star], Bin0),
         star_union(Rel_t_one, Rel_t_one_plus),
         ord_union(Rel_x, Rel_xt_one, Rel_b),
         star_union(Rel_xt_one, Rel_xt_one_plus),
         bin_all([Rel_t_one_plus, Rel_b, [[]|Rel_xt_one_plus]], Bin1),
         merge_list_of_lists([Bin0, Bin1, Rel_xt_one_plus], BinRes)
   ),
   ord_union(NRel, BinRes, MGU_sh),
   mgu_binding_lin(Lin, Sh_x, Sh_t, MGU_sh, Linx, Lint, MGU_lin).

:- pred mgu_binding_optimal0(+Sh, +Powerset_rel_x, +Bt, +Lin, -Result)
   # "This computes the most complex part of the mgu for Sharing * Linearity, which
   depends on the choice of particular subsets of Rel_x.".

mgu_binding_optimal0([], _, _, _, []).
mgu_binding_optimal0([O|Rest], Rel_x_power, Bt, Lin, Result) :-
   chiMax(O, Lin, Bt, Mul),
   mgu_binding_optimal1(O, Rel_x_power, Mul, Result0),
   sort(Result0, Result1),
   mgu_binding_optimal0(Rest, Rel_x_power, Bt, Lin, ResultRest),
   ord_union(Result1, ResultRest, Result).

mgu_binding_optimal1(_O, [], _Mul, []).
mgu_binding_optimal1(O, [Z|Rest], Mul, [Y|RestResult]) :-
   length(Z, Size),
   Size =< Mul, !,
   vars(Z, Vz),
   ord_union(O, Vz, Y),
   mgu_binding_optimal1(O, Rest, Mul, RestResult).
mgu_binding_optimal1(O, [_Z|Rest], Mul, Result) :-
   mgu_binding_optimal1(O, Rest, Mul, Result).

:- pred mgu_split(+Sh, +Lin, +Bt, ?X, Sh_x, Sh_t, -Rel_t_inf, -Rel_t_one, -Rel_t_nat, -Rel_t_nlin,
                  Rel_xt_lin, -Rel_xt_linearizable, -Rel_xt_nlin, -Rel_x, -NRel)
   # "Split the shring groups in @var{Sh} on the last four arguments
      according to their maximum multiplicity w.r.t. the set of linear
      variables @var{Lin} and the term represented by the bag of variables @var{Bt}.".

mgu_split([], _Lin, _Bt, _X, [], [], [], [], [], [], [], [], [], [], []).
mgu_split([O|Rest], Lin, Bt, X, Sh_x, Sh_t, Rel_t_inf, Rel_t_one, Rel_t_nat, Rel_t_nlin,
                                Rel_xt_lin, Rel_xt_linearizable, Rel_xt_nlin, Rel_x, NRel) :-
   chiMax(O, Lin, Bt, Mul),
   (
      ord_member(X, O) ->
         Sh_x = [O|Sh_x0],
         (
            Mul = 0 ->
               Rel_x = [O|Rel_x0],
               mgu_split(Rest, Lin, Bt, X, Sh_x0, Sh_t, Rel_t_inf, Rel_t_one, Rel_t_nat, Rel_t_nlin,
                         Rel_xt_lin, Rel_xt_linearizable, Rel_xt_nlin, Rel_x0, NRel)
            ; Mul = 1 ->
               Sh_t = [O|Sh_t0],
               Rel_xt_lin = [O|Rel_xt_lin0],
               Rel_xt_linearizable = [O|Rel_xt_linearizable0],
               mgu_split(Rest, Lin, Bt, X, Sh_x0, Sh_t0, Rel_t_inf, Rel_t_one, Rel_t_nat, Rel_t_nlin,
                         Rel_xt_lin0, Rel_xt_linearizable0, Rel_xt_nlin, Rel_x, NRel)
            ;
               Sh_t = [O|Sh_t0],
               Rel_xt_nlin = [O|Rel_xt_nlin0],
               (
                  linearizable(O, Bt) ->
                     Rel_xt_linearizable = [O|Rel_xt_linearizable0]
                  ;
                     Rel_xt_linearizable = Rel_xt_linearizable0
               ),
               mgu_split(Rest, Lin, Bt, X, Sh_x0, Sh_t0, Rel_t_inf, Rel_t_one, Rel_t_nat, Rel_t_nlin,
                         Rel_xt_lin, Rel_xt_linearizable0, Rel_xt_nlin0, Rel_x, NRel)
         )
      ;
         (
            Mul = inf ->
               Sh_t = [O|Sh_t0],
               Rel_t_inf = [O|Rel_t_inf0],
               Rel_t_nlin = [O|Rel_t_nlin0],
               mgu_split(Rest, Lin, Bt, X, Sh_x, Sh_t0, Rel_t_inf0, Rel_t_one, Rel_t_nat, Rel_t_nlin0,
                         Rel_xt_lin, Rel_xt_linearizable, Rel_xt_nlin, Rel_x, NRel)
            ; Mul = 1 ->
               Sh_t = [O|Sh_t0],
               Rel_t_one = [O|Rel_t_one0],
               Rel_t_nat = [O|Rel_t_nat0],
               mgu_split(Rest, Lin, Bt, X, Sh_x, Sh_t0, Rel_t_inf, Rel_t_one0, Rel_t_nat0, Rel_t_nlin,
                         Rel_xt_lin, Rel_xt_linearizable, Rel_xt_nlin, Rel_x, NRel)
            ; Mul > 1 ->
               Sh_t = [O|Sh_t0],
               Rel_t_nat = [O|Rel_t_nat0],
               Rel_t_nlin = [O|Rel_t_nlin0],
               mgu_split(Rest, Lin, Bt, X, Sh_x, Sh_t0, Rel_t_inf, Rel_t_one, Rel_t_nat0, Rel_t_nlin0,
                         Rel_xt_lin, Rel_xt_linearizable, Rel_xt_nlin, Rel_x, NRel)
            ;
               NRel = [O|NRel0],
               mgu_split(Rest, Lin, Bt, X, Sh_x, Sh_t, Rel_t_inf, Rel_t_one, Rel_t_nat, Rel_t_nlin,
                         Rel_xt_lin, Rel_xt_linearizable, Rel_xt_nlin, Rel_x, NRel0)
         )
   ).

%--------------------- STANDARD MGU ---------------------------

mgu_standard(ShLin, _Fv, [], ShLin).
mgu_standard(ShLin, Fv, [X=T|Rest], MGU) :-
   mgu_binding_standard(ShLin, X, T, MGU0),
   mgu(MGU0, Fv, Rest, MGU).

mgu_binding_standard(ShLin, X, T, (MGU_sh, MGU_lin)) :-
   ShLin = (Sh, Lin),
   bag_vars(T, Bt),
   bag_support(Bt, Vt),
   rel(Sh, [X], Sh_x, NSh_x),
   rel(Sh, Vt, Sh_t, NSh_t),
   ord_intersection(NSh_x, NSh_t, NSh),
   (islin(Sh, Lin, Bt) -> Lint = yes ; Lint = no),
   % if X is ground we put Linx=no, but this does not change the result
   (ord_member(X, Lin) -> Linx = yes ; Linx = no),
   (
      current_pp_flag(mgu_shlin_optimize, noindcheck) ->
         mgu_binding_sh_noind(Sh_x, Sh_t, Linx, Lint, Sh0)
      ;
         (ord_disjoint(Sh_x, Sh_t) -> Ind = yes ; Ind = no),
         mgu_binding_sh(Sh_x, Sh_t, Ind, Linx, Lint, Sh0)
   ),
   ord_union(NSh, Sh0, MGU_sh),
   mgu_binding_lin(Lin, Sh_x, Sh_t, MGU_sh, Linx, Lint, MGU_lin).

mgu_binding_sh_noind(Sh_x, Sh_t, yes, yes, Res) :- !,
   star_union(~ord_intersection(Sh_x, Sh_t), Sh_xt),
   bin(~ord_union(Sh_x, ~bin(Sh_x, Sh_xt)), ~ord_union(Sh_t, ~bin(Sh_t, Sh_xt)), Res).
mgu_binding_sh_noind(Sh_x, Sh_t, _, yes,Res) :- !,
   bin(Sh_x, ~star_union(Sh_t), Res).
mgu_binding_sh_noind(Sh_x, Sh_t, yes, _, Res) :- !,
   bin(Sh_t, ~star_union(Sh_x), Res).
mgu_binding_sh_noind(Sh_x, Sh_t, _, _, Res) :- !,
   bin(~star_union(Sh_x), ~star_union(Sh_t), Res).

mgu_binding_sh(Sh_x, Sh_t, Ind, Linx, Lint, Res) :-
   (Lint=yes, Ind=yes -> R_x = Sh_x ; star_union(Sh_x, R_x)),
   (Linx=yes, Ind=yes -> R_t = Sh_t ; star_union(Sh_t, R_t)),
   bin(R_x, R_t, Res).

mgu_binding_lin(Lin, Sh_x, Sh_t, MGU_sh, Linx, Lint, MGU_lin) :-
   mgu_binding_lin0(Lin,  ~vars(Sh_x), ~vars(Sh_t), Linx, Lint, Lin0),
   ord_intersection(Lin0, ~vars(MGU_sh), MGU_lin).

mgu_binding_lin0(Lin, Sx, St, yes, yes, Res) :- !,
   ord_intersection(Sx, St, Sxt),
   ord_subtract(Lin, Sxt, Res).
mgu_binding_lin0(Lin, Sx, _St, yes, _, Res) :- !,
   ord_subtract(Lin, Sx, Res).
mgu_binding_lin0(Lin, _Sx, St, _, yes, Res) :- !,
   ord_subtract(Lin, St, Res).
mgu_binding_lin0(Lin, Sx, St, _, _, Res) :-
   ord_union(Sx, St, Sxt),
   ord_subtract(Lin, Sxt, Res).

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
:- redefining(match/4).

match(Prime, Pv, Call, Match) :-
   current_pp_flag(match_shlin_optimize, optimal) ->
      match_optimal(Prime, Pv, Call, Match)
   ;
      match_standard(Prime, Pv, Call, Match).

%--------------------- OPTIMAL MATCH ---------------------------

:- export(match_optimal/4).
:- test match_optimal(Prime, Pv, Call, Match)
   : (Prime=([[X]],[X]), Pv=[X], Call=([[X, Y], [X,Z]],  [X]))
   => (Match=([[X,Y], [X,Z]],[X])) + (not_fails, is_det).
:- test match_optimal(Prime, Pv, Call, Match)
   : (Prime=([[X], [X,Y]], [X,Y]), Pv=[X, Y], Call=([[X, Y, W], [X, Z]], [X, Z]))
   => (Match=([[X,Y,W],[X,Z]], [X,Y,Z])) + (not_fails, is_det).

match_optimal((Sh1, Lin1), Pv, (Sh2, Lin2), (Match_sh, Match_lin)) :-
   rel(Sh2, Pv, Rel2, NRel2),
   match_optimal_sbar(Rel2, Lin1, Sbar, NoSbar),
   match_optimal0(Sh1, Lin1, Pv, Sbar, NoSbar, Match_sh0, Match_nlin0),
   ord_union(NRel2, Match_sh0, Match_sh),
   ord_subtract(Lin2, Match_nlin0, Match_lin0),
   ord_union(Lin1, Match_lin0, Match_lin1),
   as_sharing:vars(Match_sh, Vars),
   ord_intersection(Match_lin1, Vars , Match_lin).

match_optimal_sbar([], _, [], []).
match_optimal_sbar([B|Rest], Lin1, [B|Sbar], NoSbar) :-
   ord_disjoint(B, Lin1), !,
   match_optimal_sbar(Rest, Lin1, Sbar, NoSbar).
match_optimal_sbar([B|Rest], Lin1, Sbar, [B|NoSbar]) :-
   match_optimal_sbar(Rest, Lin1, Sbar, NoSbar).

match_optimal0([], _Lin1, _Pv, _Sbar, _NoSbar, [], []).
match_optimal0([B|Rest], Lin1, Pv, Sbar, NoSbar, Match_sh, Match_nlin) :-
   match_optimal_filter(Sbar, B, Pv, Sbar_filtered),
   match_optimal_filter(NoSbar, B, Pv, NoSbar_filtered),
   star_union(Sbar_filtered, Sbar_star),
   match_optimal_star_union(NoSbar_filtered, Lin1, Rel2_star),
   match_optimal_reduce(Rel2_star, Rel2_reduced),
   match_optimal_bin([([],[])|Rel2_reduced], [[]|Sbar_star], B, Pv, Match_sh0, Match_nlin0),
   match_optimal0(Rest, Lin1, Pv, Sbar, NoSbar, Match_sh1, Match_nlin1),
   ord_union(Match_sh0, Match_sh1, Match_sh),
   ord_union(Match_nlin0, Match_nlin1, Match_nlin).

match_optimal_bin([], _, _, _, [],[]).
match_optimal_bin([(X, X_nl)|Xs], NoSbar_star, B, Pv, Bin, NLin) :-
   match_optimal_bin0(X, X_nl, NoSbar_star, B, Pv, Bin0, NLin0),
   match_optimal_bin(Xs, NoSbar_star, B, Pv, Bin1, NLin1),
   ord_union(Bin0, Bin1, Bin),
   ord_union(NLin0, NLin1, NLin).

match_optimal_bin0(_X, _X_nl, [], _B, _Pv, [], []).
match_optimal_bin0(X, X_nl, [S|Rest], B, Pv, Bin, NLin) :-
   ord_union(X, S, XS),
   ord_intersection(XS, Pv, XS_restricted),
   B == XS_restricted, !,
   ord_union(S, X, Y),
   ord_union(X_nl, S, NLin1),
   match_optimal_bin0(X, X_nl, Rest, B, Pv, Bin0, NLin0),
   insert(Bin0, Y, Bin),
   ord_union(NLin1, NLin0, NLin).
match_optimal_bin0(X, X_nl, [_|Rest], B, Pv, Bin, NLin) :-
   match_optimal_bin0(X, X_nl, Rest, B, Pv, Bin, NLin).


match_optimal_filter([], _B, _Pv, []).
match_optimal_filter([X|Xs], B, Pv, [X|Ys]) :-
   ord_intersection(X, Pv, X_restr),
   ord_subset(X_restr, B), !,
   match_optimal_filter(Xs, B, Pv, Ys).
match_optimal_filter([_|Xs], B,  Pv, Ys) :-
   match_optimal_filter(Xs, B, Pv, Ys).

match_optimal_reduce([],[]).
match_optimal_reduce([X],[X]) :- !.
match_optimal_reduce([(X, X_nl), (Y, Y_nl)|Rest],Bin) :-
   X == Y, !,
   ord_union(X_nl, Y_nl, Z_nl),
   match_optimal_reduce([(X, Z_nl)|Rest], Bin).
match_optimal_reduce([(X, X_nl)|Rest], [(X, X_nl)|BinRest]) :-
   match_optimal_reduce(Rest, BinRest).

star2([], _B, _Pv, []).
star2([(X, X_nl)|Xs], B, Pv, [(X, X_nl)|Ys]) :-
   ord_intersection(X, Pv, X_restr),
   X_restr == B, !,
   star2(Xs, B, Pv, Ys).
star2([_|Xs], B, Pv, Ys) :-
   star2(Xs, B, Pv, Ys).

match_optimal_star_union(Rel2_filtered, Lin1, Rel2_star) :-
   star1(Rel2_filtered, [], Lin1, Rel2_star).

star1([], L, _Lin1, L).
star1([X|Xs], Temp, Lin1, Star) :-
   add_to_star(Temp, X, Lin1, Temp1),
   sort(Temp1,Temp2),
   star1(Xs, Temp2, Lin1, Star).

add_to_star([], X_ann, _Lin1, [(X_ann, [])]).
add_to_star([(Y, Y_nl)|Ys], X, Lin1, [(Y, Y_nl), (Z, Z_nl)|Arg_share_star]) :-
   ord_intersection(X, Y, XY),
   ord_disjoint(XY, Lin1), !,
   ord_union(X, Y, Z),
   ord_union(Y_nl, XY, Z_nl),
   add_to_star(Ys, X, Lin1, Arg_share_star).
add_to_star([(Y, Y_nl)|Ys], X, Lin1, [(Y, Y_nl) | Arg_share_star]) :-
   add_to_star(Ys, X, Lin1, Arg_share_star).

%--------------------- STANDARD MATCH ---------------------------

match_standard(Prime, Pv, (Call_sh, Call_lin), (Match_sh, Match_lin)) :-
   Prime = (Prime_sh, Prime_lin),
   as_sharing:match(Prime_sh, Pv, Call_sh, Match_sh), % we do not use linearity here
   nlin(Prime, Prime_nolin),
   rel(Call_sh, Prime_nolin, Call_sh_rel_nolin, _),
   vars(Call_sh_rel_nolin, Call_removelin),
   ord_subtract(Call_lin, Pv, Call_lin0),
   ord_subtract(Call_lin0, Call_removelin, Call_lin1),
   ord_union(Prime_lin, Call_lin1, Match_lin0),
   vars(Match_sh, Match_noground),
   ord_intersection(Match_lin0, Match_noground, Match_lin).

%-------------------------------------------------------------------------
% make_ground(+Call,+Gv,+Succ).
%
% Succ is the result of grounding the variable in Gv in the abstract
% substitution Call.
%-------------------------------------------------------------------------

:- pred make_ground(+Call, +Gv, -Succ)
   : nasub * ordlist(var) * ivar => nasub(Succ)
   + (not_fails, is_det).

make_ground((Sh,Lin), Gv, (Succ_sh, Succ_lin)) :-
   rel(Sh, Gv, _, Succ_sh),
   ord_subtract(Lin, Gv, Succ_lin).

%-------------------------------------------------------------------------
% AUXILIARY PREDICATES
%-------------------------------------------------------------------------

:- pred islin(+Sh, +Lin, +Bt)
   : asub_sh * ordlist(var) * isbag(var)
   + is_det
   # "Determines whether the term represented by the bag @var{Bt} is definitively
   linear with respect to the sharing and linearity information in @var{Sh} and
   @var{Lin}.".

islin([], _Lin, _Bt).
islin([O|Rest], Lin, Bt) :-
   chiMax(O, Lin, Bt, 1), !,
   islin(Rest, Lin, Bt).

:- pred nlin(+ShLin, -NLin)
   : asub * ivar  => ordlist(var, NLin)
   + (not_fails, is_det)
   # "@var{NLin} is the set of non-linear variables in @var{ShLin}.".

nlin((Sh, Lin), NLin) :-
   vars(Sh, NGv),
   ord_subtract(NGv, Lin, NLin).

:- pred star_union_real(+Sh, -Star)
   # "@var{Star} is the result of the star union of the set of sharing groups @var{Sh},
   with the addition of the empty sharing group.".

star_union_real(Sh, [[]|Star]) :- star_union(Sh, Star).

:- pred nl(+Sh, -Result)
   : asub_sh * ivar => ordlist(var, Result)
   + (not_fails, is_det)
   # "@var{Result} is the set of variables occuring at least twice in @var{Sh}.".

nl([], []).
nl([X|Rest], NL) :-
   nl(Rest, NL0),
   nl0(X, Rest, NL1),
   ord_union(NL0, NL1, NL).

:- index nl0(?, +, ?).

nl0(_X1, [], []).
nl0(X1, [X2 | Rest], NL) :-
   nl0(X1, Rest, NL0),
   ord_intersection(X1, X2, X),
   ord_union(X, NL0, NL).
