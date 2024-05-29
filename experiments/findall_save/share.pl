:- module(_2,[],[assertions,nativeprops]).

:- use_module(library(aggregates)).

:- set_prolog_flag(single_var_warnings,off).

:- export(example1/1).

:- export(example2/1).

:- true pred relation(_A,_B)
   : mshare([[_A],[_A,_B],[_B]])
   => ground([_A,_B]).

relation(a,b).
relation(c,d).

:- entry example1(Z)
   : mshare([Z],[[Z]]).

:- true pred example1(Z)
   : mshare([[Z]])
   => ground([Z]).

example1(Z) :-
    true(mshare([[Z],[X],[_1]])),
    findall(X,relation(_1,X),Z),
    true((
        mshare([[X],[_1]]),
        ground([Z])
    )).

:- entry example2(Z)
   : mshare([Z],[[Z]]).

:- true pred example2(Z)
   : mshare([[Z]])
   => mshare([[Z]]).

example2(Z) :-
    true(mshare([[Z],[X],[L],[_1]])),
    findall((X,L),relation(_1,X),Z),
    true(mshare([[Z],[X],[L],[_1]])).


