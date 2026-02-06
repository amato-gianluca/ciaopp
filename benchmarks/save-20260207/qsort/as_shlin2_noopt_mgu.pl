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
    true((
        mshare([[_1]]),
        linear(_1),
        shlin2([([_1],[_1])])
    )),
    qsort([27,74,17,33,94,18,46,83,65,2,32,53,28,85,99,47,28,82,6,11,55,29,39,81,90,37,10,0,66,51,7,21,85,27,31,63,75,4,95,99,11,28,61,74,18,92,40,53,59,8],_1,[]),
    true(ground([_1])).

:- true pred qsort(_A,R,R0)
   : ( (_A=[27,74,17,33,94,18,46,83,65,2,32,53,28,85,99,47,28,82,6,11,55,29,39,81,90,37,10,0,66,51,7,21,85,27,31,63,75,4,95,99,11,28,61,74,18,92,40,53,59,8]), (R0=[]),
       mshare([[R]]),
       linear(R), shlin2([([R],[R])]) )
   => ground([R]).

:- true pred qsort(_A,R,R0)
   : ( (R0=[_B|_C]),
       mshare([[R]]),
       ground([_A,_B,_C]), linear(R), shlin2([([R],[R])]) )
   => ground([_A,R,_B,_C]).

:- true pred qsort(_A,R,R0)
   : ( mshare([[R]]),
       ground([_A,R0]), linear(R), shlin2([([R],[R])]) )
   => ground([_A,R,R0]).

qsort([X|L],R,R0) :-
    true((
        mshare([[R],[L1],[L2],[R1]]),
        ground([R0,X,L]),
        linear(R),
        linear(L1),
        linear(L2),
        linear(R1),
        shlin2([([R],[R]),([L1],[L1]),([L2],[L2]),([R1],[R1])])
    )),
    partition(L,X,L1,L2),
    true((
        mshare([[R],[R1]]),
        ground([R0,X,L,L1,L2]),
        linear(R),
        linear(R1),
        shlin2([([R],[R]),([R1],[R1])])
    )),
    qsort(L2,R1,R0),
    true((
        mshare([[R]]),
        ground([R0,X,L,L1,L2,R1]),
        linear(R),
        shlin2([([R],[R])])
    )),
    qsort(L1,R,[X|R1]),
    true(ground([R,R0,X,L,L1,L2,R1])).
qsort([],R,R).

:- true pred partition(_A,Y,L1,L2)
   : ( mshare([[L1],[L2]]),
       ground([_A,Y]), linear(L1), linear(L2), shlin2([([L1],[L1]),([L2],[L2])]) )
   => ground([_A,Y,L1,L2]).

partition([X|L],Y,[X|L1],L2) :-
    true((
        mshare([[L2],[L1]]),
        ground([Y,X,L]),
        linear(L2),
        linear(L1),
        shlin2([([L2],[L2]),([L1],[L1])])
    )),
    X=<Y,
    !,
    true((
        mshare([[L2],[L1]]),
        ground([Y,X,L]),
        linear(L2),
        linear(L1),
        shlin2([([L2],[L2]),([L1],[L1])])
    )),
    partition(L,Y,L1,L2),
    true(ground([Y,L2,X,L,L1])).
partition([X|L],Y,L1,[X|L2]) :-
    true((
        mshare([[L1],[L2]]),
        ground([Y,X,L]),
        linear(L1),
        linear(L2),
        shlin2([([L1],[L1]),([L2],[L2])])
    )),
    partition(L,Y,L1,L2),
    true(ground([Y,L1,X,L,L2])).
partition([],_1,[],[]).


