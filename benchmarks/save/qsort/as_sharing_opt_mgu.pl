:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(qsort,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    qsort,
    true(true).

:- true pred qsort.

qsort :-
    true(mshare([[_1]])),
    qsort([27,74,17,33,94,18,46,83,65,2,32,53,28,85,99,47,28,82,6,11,55,29,39,81,90,37,10,0,66,51,7,21,85,27,31,63,75,4,95,99,11,28,61,74,18,92,40,53,59,8],_1,[]),
    true(ground([_1])).

:- true pred qsort(_A,R,R0)
   : ( (_A=[27,74,17,33,94,18,46,83,65,2,32,53,28,85,99,47,28,82,6,11,55,29,39,81,90,37,10,0,66,51,7,21,85,27,31,63,75,4,95,99,11,28,61,74,18,92,40,53,59,8]), (R0=[]),
       mshare([[R]]) )
   => ground([R]).

:- true pred qsort(_A,R,R0)
   : ( (R0=[_B|_C]),
       mshare([[R]]),
       ground([_A,_B,_C]) )
   => ground([_A,R,_B,_C]).

:- true pred qsort(_A,R,R0)
   : ( mshare([[R]]),
       ground([_A,R0]) )
   => ground([_A,R,R0]).

qsort([X|L],R,R0) :-
    true((
        mshare([[R],[L1],[L2],[R1]]),
        ground([R0,X,L])
    )),
    partition(L,X,L1,L2),
    true((
        mshare([[R],[R1]]),
        ground([R0,X,L,L1,L2])
    )),
    qsort(L2,R1,R0),
    true((
        mshare([[R]]),
        ground([R0,X,L,L1,L2,R1])
    )),
    qsort(L1,R,[X|R1]),
    true(ground([R,R0,X,L,L1,L2,R1])).
qsort([],R,R).

:- true pred partition(_A,Y,L1,L2)
   : ( mshare([[L1],[L2]]),
       ground([_A,Y]) )
   => ground([_A,Y,L1,L2]).

partition([X|L],Y,[X|L1],L2) :-
    true((
        mshare([[L2],[L1]]),
        ground([Y,X,L])
    )),
    X=<Y,
    !,
    true((
        mshare([[L2],[L1]]),
        ground([Y,X,L])
    )),
    partition(L,Y,L1,L2),
    true(ground([Y,L2,X,L,L1])).
partition([X|L],Y,L1,[X|L2]) :-
    true((
        mshare([[L1],[L2]]),
        ground([Y,X,L])
    )),
    partition(L,Y,L1,L2),
    true(ground([Y,L1,X,L,L2])).
partition([],_1,[],[]).


