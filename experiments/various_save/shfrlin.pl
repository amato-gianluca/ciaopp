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
   : mshare([[Z]])
   => ground([Z]).

example1(Z) :-
    true((
        mshare([[Z],[X],[_1]]),
        var(X),
        var(_1),
        linear(X),
        linear(_1)
    )),
    findall(X,relation(_1,X),Z),
    true((
        mshare([[X],[_1]]),
        var(X),
        var(_1),
        ground([Z]),
        linear(X),
        linear(_1)
    )).

:- entry example1bis(Z)
   : ( mshare([Z],[[Z]]), linear([Z]) ).

:- true pred example1bis(Z)
   : mshare([[Z]])
   => mshare([[Z]]).

example1bis(Z) :-
    true((
        mshare([[Z],[X],[_1]]),
        var(X),
        var(_1),
        linear(X),
        linear(_1)
    )),
    findall(X,relation2(_1,X),Z),
    true((
        mshare([[Z],[X],[_1]]),
        var(X),
        var(_1),
        linear(X),
        linear(_1)
    )).

:- entry example2(Z)
   : ( mshare([Z],[[Z]]), linear([Z]) ).

:- true pred example2(Z)
   : mshare([[Z]])
   => mshare([[Z]]).

example2(Z) :-
    true((
        mshare([[Z],[X],[L],[_1]]),
        var(X),
        var(L),
        var(_1),
        linear(X),
        linear(L),
        linear(_1)
    )),
    findall((X,L),relation(_1,X),Z),
    true((
        mshare([[Z],[X],[L],[_1]]),
        var(X),
        var(L),
        var(_1),
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
        var(X),
        var(R),
        linear(X),
        linear(R)
    )),
    fail,
    true(fails(_)),
    findall(X,relation(a,X),R),
    true(fails(_)).

:- entry example4(Var,Vars,Link)
   : mshare([Var,Vars,Link],[[Var],[Vars],[Link]]).

:- true pred example4(Var,Vars,Link)
   : mshare([[Var],[Vars],[Link]])
   => mshare([[Var],[Vars],[Link]]).

example4(Term,Vars,Link) :-
    true((
        mshare([[Term],[Vars],[Link],[F],[Args]]),
        var(F),
        var(Args),
        linear(F),
        linear(Args)
    )),
    Term=..[F|Args],
    true((
        mshare([[Term,Args],[Vars],[Link]]),
        ground([F])
    )).

:- entry example5(A)
   : ground(A).

:- true pred example5(A)
   : ground([A])
   => ground([A]).

:- true pred example5(A)
   : ( (A=[_A|_B]),
       mshare([[_A]]),
       var(_A), ground([_B]), linear(_A) )
   => ( mshare([[_A]]),
        ground([_B]) ).

:- true pred example5(A)
   : ( (A=[_A|_B]),
       mshare([[_A],[_B]]),
       var(_A), linear(_A) )
   => mshare([[_A],[_A,_B],[_B]]).

example5(A).
example5(A) :-
    true((mshare([[A],[_1]]),var(_1),linear(_1);mshare([[_1]]),var(_1),ground([A]),linear(_1))),
    example5([_1|A]),
    true((mshare([[A],[A,_1],[_1]]);mshare([[_1]]),ground([A]))).


