:- module(_2,[],[assertions,nativeprops]).

:- use_module(library(aggregates)).

:- set_prolog_flag(single_var_warnings,off).

:- export(relation/2).

:- export(relation2/2).

:- true pred relation(_A,_B)
   : ( mshare([[_A],[_A,_B],[_B]]),
       shlin2([([_A],[]),([_A,_B],[]),([_B],[])]) )
   => ground([_A,_B]).

relation(a,b).
relation(c,d).

:- true pred relation2(_A,X)
   : ( mshare([[_A],[_A,X],[X]]),
       shlin2([([_A],[]),([_A,X],[]),([X],[])]) )
   => ( mshare([[X]]),
        ground([_A]), shlin2([([X],[])]) ).

relation2(b,X).
relation2(c,d).

:- entry example1(Z)
   : ( mshare([Z],[[Z]]), linear([Z]) ).

:- true pred example1(Z)
   : ( mshare([[Z]]),
       linear(Z), shlin2([([Z],[Z])]) )
   => ground([Z]).

example1(Z) :-
    true((
        mshare([[Z],[X],[_1]]),
        linear(Z),
        linear(X),
        linear(_1),
        shlin2([([Z],[Z]),([X],[X]),([_1],[_1])])
    )),
    findall(X,relation(_1,X),Z),
    true((
        mshare([[X],[_1]]),
        ground([Z]),
        linear(X),
        linear(_1),
        shlin2([([X],[X]),([_1],[_1])])
    )).

:- entry example1bis(Z)
   : ( mshare([Z],[[Z]]), linear([Z]) ).

:- true pred example1bis(Z)
   : ( mshare([[Z]]),
       linear(Z), shlin2([([Z],[Z])]) )
   => ( mshare([[Z]]),
        shlin2([([Z],[])]) ).

example1bis(Z) :-
    true((
        mshare([[Z],[X],[_1]]),
        linear(Z),
        linear(X),
        linear(_1),
        shlin2([([Z],[Z]),([X],[X]),([_1],[_1])])
    )),
    findall(X,relation2(_1,X),Z),
    true((
        mshare([[Z],[X],[_1]]),
        linear(X),
        linear(_1),
        shlin2([([Z],[]),([X],[X]),([_1],[_1])])
    )).

:- entry example2(Z)
   : ( mshare([Z],[[Z]]), linear([Z]) ).

:- true pred example2(Z)
   : ( mshare([[Z]]),
       linear(Z), shlin2([([Z],[Z])]) )
   => ( mshare([[Z]]),
        shlin2([([Z],[])]) ).

example2(Z) :-
    true((
        mshare([[Z],[X],[L],[_1]]),
        linear(Z),
        linear(X),
        linear(L),
        linear(_1),
        shlin2([([Z],[Z]),([X],[X]),([L],[L]),([_1],[_1])])
    )),
    findall((X,L),relation(_1,X),Z),
    true((
        mshare([[Z],[X],[L],[_1]]),
        linear(X),
        linear(L),
        linear(_1),
        shlin2([([Z],[]),([X],[X]),([L],[L]),([_1],[_1])])
    )).

:- entry example3.

:- true pred example3
   + fails.

example3 :-
    true((
        mshare([[X],[R]]),
        linear(X),
        linear(R),
        shlin2([([X],[X]),([R],[R])])
    )),
    fail,
    true(fails(_)),
    findall(X,relation(a,X),R),
    true(fails(_)).

:- entry example4(Var,Vars,Link)
   : mshare([Var,Vars,Link],[[Var],[Vars],[Link]]).

:- true pred example4(Var,Vars,Link)
   : ( mshare([[Var],[Vars],[Link]]),
       shlin2([([Var],[]),([Vars],[]),([Link],[])]) )
   => ( mshare([[Var],[Vars],[Link]]),
        shlin2([([Var],[]),([Vars],[]),([Link],[])]) ).

example4(Term,Vars,Link) :-
    true((
        mshare([[Term],[Vars],[Link],[F],[Args]]),
        linear(F),
        linear(Args),
        shlin2([([Term],[]),([Vars],[]),([Link],[]),([F],[F]),([Args],[Args])])
    )),
    Term=..[F|Args],
    true((
        mshare([[Term,Args],[Vars],[Link]]),
        ground([F]),
        shlin2([([Term,Args],[]),([Vars],[]),([Link],[])])
    )).

:- entry example5(A)
   : ground(A).

:- true pred example5(A)
   : ground([A])
   => ground([A]).

:- true pred example5(A)
   : ( (A=[_A|_B]),
       mshare([[_A]]),
       ground([_B]), linear(_A), shlin2([([_A],[_A])]) )
   => ( mshare([[_A]]),
        ground([_B]), linear(_A), shlin2([([_A],[_A])]) ).

:- true pred example5(A)
   : ( (A=[_A|_B]),
       mshare([[_A],[_B]]),
       linear(_A), linear(_B), shlin2([([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[_A],[_B]]),
        linear(_A), linear(_B), shlin2([([_A],[_A]),([_B],[_B])]) ).

example5(A).
example5(A) :-
    true((mshare([[A],[_1]]),linear(A),linear(_1),shlin2([([A],[A]),([_1],[_1])]);mshare([[_1]]),ground([A]),linear(_1),shlin2([([_1],[_1])]))),
    example5([_1|A]),
    true((mshare([[A],[_1]]),linear(A),linear(_1),shlin2([([A],[A]),([_1],[_1])]);mshare([[_1]]),ground([A]),linear(_1),shlin2([([_1],[_1])]))).


