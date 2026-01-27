:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(nreverse,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    nreverse,
    true(true).

:- true pred nreverse.

nreverse :-
    true((
        mshare([[_1]]),
        linear(_1)
    )),
    nreverse([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30],_1),
    true(ground([_1])).

:- true pred nreverse(_A,L)
   : ( (_A=[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]),
       mshare([[L]]),
       linear(L) )
   => ground([L]).

:- true pred nreverse(_A,L)
   : ( mshare([[L]]),
       ground([_A]), linear(L) )
   => ground([_A,L]).

nreverse([X|L0],L) :-
    true((
        mshare([[L],[L1]]),
        ground([X,L0]),
        linear(L),
        linear(L1)
    )),
    nreverse(L0,L1),
    true((
        mshare([[L]]),
        ground([X,L0,L1]),
        linear(L)
    )),
    concatenate(L1,[X],L),
    true(ground([L,X,L0,L1])).
nreverse([],[]).

:- true pred concatenate(_A,L2,L)
   : ( (L2=[_B]),
       mshare([[L]]),
       ground([_A,_B]), linear(L) )
   => ground([_A,L,_B]).

:- true pred concatenate(_A,L2,L)
   : ( mshare([[L]]),
       ground([_A,L2]), linear(L) )
   => ground([_A,L2,L]).

concatenate([X|L1],L2,[X|L3]) :-
    true((
        mshare([[L3]]),
        ground([L2,X,L1]),
        linear(L3)
    )),
    concatenate(L1,L2,L3),
    true(ground([L2,X,L1,L3])).
concatenate([],L,L).


