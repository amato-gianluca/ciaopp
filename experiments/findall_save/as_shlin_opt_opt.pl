:- module(_2,[],[assertions,nativeprops]).

:- use_module(library(aggregates)).

:- set_prolog_flag(single_var_warnings,off).

:- export(relation/2).

:- export(relation2/2).

:- true pred relation(_A,_B)
   : mshare([[_A],[_A,_B],[_B]])
   => ground([_A,_B]).

relation(a,b).
relation(c,d).

:- true pred relation2(_A,X)
   : mshare([[_A],[_A,X],[X]])
   => ( mshare([[X]]),
        ground([_A]) ).

relation2(b,X).
relation2(c,d).

:- entry example1(Z)
   : ( mshare([Z],[[Z]]), linear([Z]) ).

:- true pred example1(Z)
   : ( mshare([[Z]]),
       linear(Z) )
   => ground([Z]).

example1(Z) :-
    true((
        mshare([[Z],[X],[_1]]),
        linear(Z),
        linear(X),
        linear(_1)
    )),
    findall(X,relation(_1,X),Z),
    true((
        mshare([[X],[_1]]),
        ground([Z]),
        linear(X),
        linear(_1)
    )).

:- entry example1bis(Z)
   : ( mshare([Z],[[Z]]), linear([Z]) ).

:- true pred example1bis(Z)
   : ( mshare([[Z]]),
       linear(Z) )
   => mshare([[Z]]).

example1bis(Z) :-
    true((
        mshare([[Z],[X],[_1]]),
        linear(Z),
        linear(X),
        linear(_1)
    )),
    findall(X,relation2(_1,X),Z),
    true((
        mshare([[Z],[X],[_1]]),
        linear(X),
        linear(_1)
    )).

:- entry example2(Z)
   : ( mshare([Z],[[Z]]), linear([Z]) ).

:- true pred example2(Z)
   : ( mshare([[Z]]),
       linear(Z) )
   => mshare([[Z]]).

example2(Z) :-
    true((
        mshare([[Z],[X],[L],[_1]]),
        linear(Z),
        linear(X),
        linear(L),
        linear(_1)
    )),
    findall((X,L),relation(_1,X),Z),
    true((
        mshare([[Z],[X],[L],[_1]]),
        linear(X),
        linear(L),
        linear(_1)
    )).

:- entry example3.

:- true pred example3
   + fails.

example3 :-
    true((
        mshare([[X],[R]]),
        linear(X),
        linear(R)
    )),
    fail,
    true(fails(_)),
    findall(X,relation(a,X),R),
    true(fails(_)).


