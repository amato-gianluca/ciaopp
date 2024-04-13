:- module(_1,[],[assertions,nativeprops]).

:- set_prolog_flag(single_var_warnings,off).

:- entry example1.

:- true pred example1.

example1 :-
    true((
        mshare([[X],[Y]]),
        var(X),
        var(Y),
        linear(X),
        linear(Y)
    )),
    X=Y,
    true((
        mshare([[X,Y]]),
        var(X),
        var(Y),
        linear(X),
        linear(Y)
    )),
    p(Y),
    true((
        mshare([[X,Y]]),
        linear(X)
    )).

:- true pred p(_A)
   : ( mshare([[_A]]),
       var(_A), linear(_A) )
   => mshare([[_A]]).

p(t(U,U)).

:- entry example2(X)
   : linear([X]).

:- true pred example2(X)
   : mshare([[X]])
   => mshare([[X]]).

example2(X) :-
    true(mshare([[X]])),
    nothing,
    true(mshare([[X]])).

:- entry example3(X,X1,X2,Y,Y1,Y2,Z)
   : ( mshare([X,X1,X2,Y,Y1,Y2,Z],[[X,X1],[X,X2],[X,Y,Z],[Y,Y1],[Y,Y2]]), linear([X,X1,X2,Y,Y1,Y2,Z]) ).

:- true pred example3(X,X1,X2,Y,Y1,Y2,Z)
   : mshare([[X,X1],[X,X2],[X,Y,Z],[Y,Y1],[Y,Y2]])
   => mshare([[X,X1,X2,Y,Y1],[X,X1,X2,Y,Y1,Y2],[X,X1,X2,Y,Y1,Y2,Z],[X,X1,X2,Y,Y1,Z],[X,X1,X2,Y,Y2],[X,X1,X2,Y,Y2,Z],[X,X1,X2,Y,Z],[X,X1,Y,Y1],[X,X1,Y,Y1,Y2],[X,X1,Y,Y1,Y2,Z],[X,X1,Y,Y1,Z],[X,X1,Y,Y2],[X,X1,Y,Y2,Z],[X,X1,Y,Z],[X,X2,Y,Y1],[X,X2,Y,Y1,Y2],[X,X2,Y,Y1,Y2,Z],[X,X2,Y,Y1,Z],[X,X2,Y,Y2],[X,X2,Y,Y2,Z],[X,X2,Y,Z],[X,Y,Y1,Y2,Z],[X,Y,Y1,Z],[X,Y,Y2,Z],[X,Y,Z]]).

example3(X,X1,X2,Y,Y1,Y2,Z) :-
    true(mshare([[X,X1],[X,X2],[X,Y,Z],[Y,Y1],[Y,Y2]])),
    X=Y,
    true(mshare([[X,X1,X2,Y,Y1],[X,X1,X2,Y,Y1,Y2],[X,X1,X2,Y,Y1,Y2,Z],[X,X1,X2,Y,Y1,Z],[X,X1,X2,Y,Y2],[X,X1,X2,Y,Y2,Z],[X,X1,X2,Y,Z],[X,X1,Y,Y1],[X,X1,Y,Y1,Y2],[X,X1,Y,Y1,Y2,Z],[X,X1,Y,Y1,Z],[X,X1,Y,Y2],[X,X1,Y,Y2,Z],[X,X1,Y,Z],[X,X2,Y,Y1],[X,X2,Y,Y1,Y2],[X,X2,Y,Y1,Y2,Z],[X,X2,Y,Y1,Z],[X,X2,Y,Y2],[X,X2,Y,Y2,Z],[X,X2,Y,Z],[X,Y,Y1,Y2,Z],[X,Y,Y1,Z],[X,Y,Y2,Z],[X,Y,Z]])),
    nothing,
    true(mshare([[X,X1,X2,Y,Y1],[X,X1,X2,Y,Y1,Y2],[X,X1,X2,Y,Y1,Y2,Z],[X,X1,X2,Y,Y1,Z],[X,X1,X2,Y,Y2],[X,X1,X2,Y,Y2,Z],[X,X1,X2,Y,Z],[X,X1,Y,Y1],[X,X1,Y,Y1,Y2],[X,X1,Y,Y1,Y2,Z],[X,X1,Y,Y1,Z],[X,X1,Y,Y2],[X,X1,Y,Y2,Z],[X,X1,Y,Z],[X,X2,Y,Y1],[X,X2,Y,Y1,Y2],[X,X2,Y,Y1,Y2,Z],[X,X2,Y,Y1,Z],[X,X2,Y,Y2],[X,X2,Y,Y2,Z],[X,X2,Y,Z],[X,Y,Y1,Y2,Z],[X,Y,Y1,Z],[X,Y,Y2,Z],[X,Y,Z]])).

:- entry example4(V,W,X,Y,Z)
   : ( mshare([V,W,X,Y,Z],[[X,V],[X,Y],[Z,W]]), linear([V,W,X,Y]) ).

:- true pred example4(V,W,X,Y,Z)
   : mshare([[V,X],[W,Z],[X,Y]])
   => mshare([[V,W,X,Y,Z],[V,W,X,Z],[V,X,Y],[W,X,Y,Z],[X,Y]]).

example4(V,W,X,Y,Z) :-
    true(mshare([[V,X],[W,Z],[X,Y]])),
    X=f(Y,Z),
    true(mshare([[V,W,X,Y,Z],[V,W,X,Z],[V,X,Y],[W,X,Y,Z],[X,Y]])).

:- entry example5(X,Y,Z)
   : ( mshare([X,Y,Z],[[X,Y],[Y,Z]]), linear([X,Y,Z]) ).

:- true pred example5(X,Y,Z)
   : mshare([[X,Y],[Y,Z]])
   => mshare([[X,Y],[X,Y,Z],[Y,Z]]).

example5(X,Y,Z) :-
    true(mshare([[X,Y],[Y,Z]])),
    mymember(X,[Y]),
    true(mshare([[X,Y],[X,Y,Z],[Y,Z]])).

:- true pred mymember(U,_A)
   : ( (_A=[_B]),
       mshare([[U,_B],[_B]]) )
   => mshare([[U,_B],[_B]]).

:- true pred mymember(U,_A)
   : ( mshare([[U]]),
       ground([_A]) )
   => ground([U,_A]).

mymember(U,[U|V]) :-
    true((mshare([[U]]),ground([V]);ground([U,V]))),
    nothing,
    true((mshare([[U]]),ground([V]);ground([U,V]))).
mymember(U,[V|W]) :-
    true((mshare([[U]]),ground([V,W]);mshare([[U,V],[V]]),ground([W]))),
    mymember(U,W),
    true((mshare([[V]]),ground([U,W]);ground([U,V,W]))).

:- true pred nothing.

nothing.

:- entry example6(X,Y,Z)
   : ( mshare([X,Y,Z],[[X,Y],[X,Z]]), linear([X]) ).

:- true pred example6(X,Y,Z)
   : mshare([[X,Y],[X,Z]])
   => mshare([[X,Y],[X,Y,Z],[X,Z]]).

example6(X,Y,Z) :-
    true(mshare([[X,Y],[X,Z]])),
    q(X),
    true(mshare([[X,Y],[X,Y,Z],[X,Z]])).

:- true pred q(X)
   : mshare([[X]])
   => mshare([[X]]).

q(X).


