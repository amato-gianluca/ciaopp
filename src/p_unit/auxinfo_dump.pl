:- module(_, [], [assertions, hiord, datafacts]).

:- doc(module, "This library provides support for saving (dump) and
   loading (restore) auxiliary data (e.g., type definitions) from
   PLAI's analysis results. Data can be serialized to/from predicates,
   files, etc.").

:- use_module(ciaopp(infer/infer_dom), [knows_of/2]).
:- use_module(ciaopp(plai/domains), [collect_types_in_abs/4, rename_types_in_abs/4]).

:- use_module(typeslib(typeslib), [dump_types/2, restore_types/2]).

:- use_module(library(aggregates), [findall/3]).

:- data acc_ty/1. % accumulates required types

:- export(acc_auxiliary_info/2).
:- pred acc_auxiliary_info(AbsInt,ASubs)
   # "Accumulates auxiliary info from the list of abstract
   substitutions @var{ASubs} of domain @var{AbsInt}. It is expected
   that you issue a call to this one for every item you dump.".

acc_auxiliary_info(AbsInt,ASubs):-
    knows_of(regtypes,AbsInt), !,
    collect_all_types_in_abs(ASubs,AbsInt).
acc_auxiliary_info(_AbsInt,_ASubs).

collect_all_types_in_abs([ASub|ASubs],AbsInt):-
    collect_types_in_abs(ASub,AbsInt,[],AbsTypes2), % TODO: remove first arg
    ( % (failure-driven loop)
      member(AbsType, AbsTypes2),
      ( acc_ty(AbsType) -> true
      ; assertz_fact(acc_ty(AbsType))
      ),
      fail
    ; true
    ),
    collect_all_types_in_abs(ASubs,AbsInt).
collect_all_types_in_abs([],_AbsInt).

:- export(dump_auxiliary_info/1).
:- meta_predicate dump_auxiliary_info(pred(1)).
:- pred dump_auxiliary_info(AssertPred)
   # "Dumps auxiliary info collected previously. The dumping is
   performed by calling @var{AssertPred}(Info) on every Info item
   collected. It is expected that you issue a call to this one after
   you have finished processing your own items you are going to
   dump. It can be either before or after actually dumping them.".

dump_auxiliary_info(AssertPred):-
    findall(AbsType, acc_ty(AbsType), AbsTypes0),
    retractall_fact(acc_ty(_)),
    dump_types(AbsTypes0, AssertPred).

:- export(restore_auxiliary_info/2).
:- meta_predicate restore_auxiliary_info(pred(1),?).
:- pred restore_auxiliary_info(ConsultPred,Dict)
   # "Restores the auxiliary data dumped with
   @pred{dump_auxiliary_info/1}. The dumped info is obtained on
   backtracking by calling @tt{ConsultPred(Info)}. Additionally,
   @var{Dict} is unified with relocation data to adjust references
   (e.g., types names) saved in other data structures (see
   @pred{imp_auxiliary_info/4}).".

restore_auxiliary_info(ConsultPred,Dict):-
    restore_types(ConsultPred, Rens),
    Names = [], % TODO: 'Names' is not saved, is it fine for eterms? (JFMC)
    Dict = (Rens,Names).

:- export(imp_auxiliary_info/4).
:- pred imp_auxiliary_info(AbsInt,Dict,ASubs,NewASubs)
   # "Processes the list of abstract substitutions @var{ASubs} of
   domain @var{AbsInt} through the auxiliary info structure
   @var{Dict}, obtaining the list @var{NewASubs} in the same
   order. The latter should replace the former in your items being
   restored. Thus, you have to issue a call to this one for every item
   you restore and before actually restoring it.".

imp_auxiliary_info(AbsInt,Dict,ASubs,NewASubs):-
    rename_all_types_in_abs(ASubs,AbsInt,Dict,NewASubs).

rename_all_types_in_abs([ASub0|ASubs0],AbsInt,Dict,[ASub|ASubs]):-
    rename_types_in_abs(ASub0,AbsInt,Dict,ASub),
    rename_all_types_in_abs(ASubs0,AbsInt,Dict,ASubs).
rename_all_types_in_abs([],_AbsInt,_Dict,[]).

%% % Sample Use Code:
%% 
%% :- module(dump_example,[dump/1,restore/1]).
%% 
%% :- use_module(ciaopp(plai/plai_db), [complete/7]).
%% :- use_module(ciaopp(p_unit/auxinfo_dump)).
%% 
%% :- data my_complete/7.  % stores copies of complete/7
%% :- data aux/1.          % stores required type definitions
%% 
%% dump(AbsInt):-
%%      current_fact(complete(SgKey,AbsInt,Sg,Proj,Primes,Id,Parents)),
%%      asserta_fact(my_complete(SgKey,AbsInt,Sg,Proj,Primes,Id,Parents)),
%%      acc_auxiliary_info(AbsInt,[Proj|Primes]),
%%      fail.
%% dump(AbsInt):-
%%      dump_auxiliary_info(AbsInt,asserta_if_not_yet).
%% 
%% asserta_if_not_yet(X):- current_fact(aux(X)), !.
%% asserta_if_not_yet(X):- asserta_fact(aux(X)).
%% 
%% restore_aux(X):- retract_fact(aux(X)).
%% 
%% restore(AbsInt):-
%%      restore_auxiliary_info(restore_aux,Dict),
%%      retract_fact(my_complete(SgKey,AbsInt,Sg,Proj0,Primes0,Id,Parents)),
%%      imp_auxiliary_info(AbsInt,Dict,[Proj0|Primes0],[Proj|Primes]),
%%      asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Primes,Id,Parents)),
%%      fail.
%% restore(_AbsInt).
%% 
