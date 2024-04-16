:- module(_1,[],[assertions,nativeprops]).

:- prop shlin2(X)+native.

:- impl_defined(shlin2/1).

:- set_prolog_flag(single_var_warnings,off).

:- entry example1(U,V,W,X,Y,Z)
   : ( shlin2([([U,X],[U,X]),([V,X],[V,X]),([W,X],[W]),([Y],[Y]),([Z],[Z])]), mshare([U,V,W,X,Y,Z],[[U,X],[V,X],[W,X],[Y],[Z]]), linear([U,V,W,Y,Z]) ).

:- true pred example1(U,V,W,X,Y,Z)
   : mshare([[U,X],[V,X],[W,X],[Y],[Z]])
   => ( mshare([[U,V,X,Y],[U,V,X,Y,Z],[U,V,X,Z],[U,X,Y],[U,X,Y,Z],[U,X,Z],[V,X,Y],[V,X,Y,Z],[V,X,Z]]),
        ground([W]) ).

example1(U,V,W,X,Y,Z) :-
    true(mshare([[U,V,W,X],[U,V,X],[U,W,X],[U,X],[V,W,X],[V,X],[W,X],[Y],[Z]])),
    X=f(Y,Z),
    true(mshare([[U,V,W,X,Y],[U,V,W,X,Y,Z],[U,V,W,X,Z],[U,V,X,Y],[U,V,X,Y,Z],[U,V,X,Z],[U,W,X,Y],[U,W,X,Y,Z],[U,W,X,Z],[U,X,Y],[U,X,Y,Z],[U,X,Z],[V,W,X,Y],[V,W,X,Y,Z],[V,W,X,Z],[V,X,Y],[V,X,Y,Z],[V,X,Z],[W,X,Y],[W,X,Y,Z],[W,X,Z]])),
    W=g,
    true((
        mshare([[U,V,X,Y],[U,V,X,Y,Z],[U,V,X,Z],[U,X,Y],[U,X,Y,Z],[U,X,Z],[V,X,Y],[V,X,Y,Z],[V,X,Z]]),
        ground([W])
    )).

:- entry example2(U,V,X,Y)
   : ( shlin2([([X],[]),([X,U],[X,U]),([X,Y],[X,Y]),([Y,V],[Y,V])]), mshare([U,V,X,Y],[[X],[X,U],[X,Y],[Y,V]]), linear([U,Y,V]) ).

:- true pred example2(U,V,X,Y)
   : mshare([[U,X],[V,Y],[X],[X,Y]])
   => mshare([[U,V,X,Y],[U,X,Y],[V,X,Y],[X,Y]]).

example2(U,V,X,Y) :-
    true(mshare([[U,V,X,Y],[U,X],[U,X,Y],[V,X,Y],[V,Y],[X],[X,Y]])),
    X=r(Y,Y),
    true(mshare([[U,V,X,Y],[U,X,Y],[V,X,Y],[X,Y]])).

:- entry example3(U,V,W,X,Y)
   : ( mshare([U,V,W,X,Y],[[U,X],[V,X],[W,X],[Y]]), linear([U,V,W,X,Y]) ).

:- true pred example3(U,V,W,X,Y)
   : mshare([[U,X],[V,X],[W,X],[Y]])
   => mshare([[U,V,W,X,Y],[U,V,X,Y],[U,W,X,Y],[U,X,Y],[V,W,X,Y],[V,X,Y],[W,X,Y]]).

example3(U,V,W,X,Y) :-
    true(mshare([[U,V,W,X],[U,V,X],[U,W,X],[U,X],[V,W,X],[V,X],[W,X],[Y]])),
    X=r(Y,Y),
    true(mshare([[U,V,W,X,Y],[U,V,X,Y],[U,W,X,Y],[U,X,Y],[V,W,X,Y],[V,X,Y],[W,X,Y]])).

:- entry example4(U,X,Y,Z)
   : ( mshare([U,X,Y,Z],[[U,X],[X,Y],[Y,Z]]), linear([U,X,Y,Z]) ).

:- true pred example4(U,X,Y,Z)
   : mshare([[U,X],[X,Y],[Y,Z]])
   => mshare([[U,X,Y],[U,X,Y,Z],[X,Y],[X,Y,Z]]).

example4(U,X,Y,Z) :-
    true(mshare([[U,X],[U,X,Y],[U,X,Y,Z],[X,Y],[X,Y,Z],[Y,Z]])),
    X=r(Y),
    true(mshare([[U,X,Y],[U,X,Y,Z],[X,Y],[X,Y,Z]])).

:- entry example5.

:- true pred example5.

example5 :-
    true(mshare([[L],[H],[T]])),
    difflist(L,H,T),
    true(mshare([[L,H],[L,H,T],[H,T]])),
    H=T,
    true(mshare([[L,H,T],[H,T]])).

:- true pred difflist(L,H,T)
   : mshare([[L],[H],[T]])
   => mshare([[L,H],[L,H,T],[H,T]]).

:- true pred difflist(L,H,T)
   : mshare([[L],[L,H],[H],[T]])
   => mshare([[L,H],[L,H,T],[H,T]]).

difflist(L,H,T) :-
    true((mshare([[L],[L,H],[H],[T]]);mshare([[L],[H],[T]]))),
    L=[],
    true((
        mshare([[H],[T]]),
        ground([L])
    )),
    H=T,
    true((
        mshare([[H,T]]),
        ground([L])
    )).
difflist(L,H,T) :-
    true((mshare([[L],[L,H],[H],[T],[X],[L1],[H1]]);mshare([[L],[H],[T],[X],[L1],[H1]]))),
    L=[X|L1],
    true((mshare([[L,H,X],[L,H,X,L1],[L,H,L1],[L,X],[L,X,L1],[L,L1],[H],[T],[H1]]);mshare([[L,X],[L,X,L1],[L,L1],[H],[T],[H1]]))),
    H=[X|H1],
    true((mshare([[L,H,X],[L,H,X,L1],[L,H,X,L1,H1],[L,H,X,H1],[L,H,L1,H1],[L,L1],[H,H1],[T]]);mshare([[L,H,X],[L,H,X,L1],[L,H,X,L1,H1],[L,H,X,H1],[L,L1],[H,H1],[T]]))),
    difflist(L1,H1,T),
    true(mshare([[L,H,T,X,L1,H1],[L,H,T,X,H1],[L,H,T,L1,H1],[L,H,X],[L,H,X,L1,H1],[L,H,L1,H1],[H,T,H1]])).

:- entry example6.

:- true pred example6.

example6 :-
    true(mshare([[L],[D],[T],[X1],[X2],[H]])),
    difflist1(L,D),
    true(mshare([[L,D],[D],[T],[X1],[X2],[H]])),
    D=[X1,X2|H]-T,
    true(mshare([[L,D,T],[L,D,T,X1],[L,D,T,X1,X2],[L,D,T,X1,X2,H],[L,D,T,X1,H],[L,D,T,X2],[L,D,T,X2,H],[L,D,T,H],[L,D,X1],[L,D,X1,X2],[L,D,X1,X2,H],[L,D,X1,H],[L,D,X2],[L,D,X2,H],[L,D,H],[D,T],[D,T,X1],[D,T,X1,X2],[D,T,X1,X2,H],[D,T,X1,H],[D,T,X2],[D,T,X2,H],[D,T,H],[D,X1],[D,X1,X2],[D,X1,X2,H],[D,X1,H],[D,X2],[D,X2,H],[D,H]])).

:- entry difflist1(L,D)
   : ( mshare([L,D],[[L],[D]]), linear([L,D]) ).

:- true pred difflist1(L,D)
   : mshare([[L],[D]])
   => mshare([[L,D],[D]]).

:- true pred difflist1(L,D)
   : mshare([[L],[L,D],[D]])
   => mshare([[L,D],[D]]).

difflist1(L,D) :-
    true((mshare([[L],[L,D],[D],[H]]);mshare([[L],[D],[H]]))),
    L=[],
    true((
        mshare([[D],[H]]),
        ground([L])
    )),
    D=H-H,
    true((
        mshare([[D,H]]),
        ground([L])
    )).
difflist1(L,D) :-
    true((mshare([[L],[L,D],[D],[X],[L1],[T],[H],[D1]]);mshare([[L],[D],[X],[L1],[T],[H],[D1]]))),
    L=[X|L1],
    true((mshare([[L,D,X],[L,D,X,L1],[L,D,L1],[L,X],[L,X,L1],[L,L1],[D],[T],[H],[D1]]);mshare([[L,X],[L,X,L1],[L,L1],[D],[T],[H],[D1]]))),
    D=[X|H]-T,
    true((mshare([[L,D,X],[L,D,X,L1],[L,D,X,L1,T],[L,D,X,L1,T,H],[L,D,X,L1,H],[L,D,X,T],[L,D,X,T,H],[L,D,X,H],[L,D,L1,T],[L,D,L1,T,H],[L,D,L1,H],[L,L1],[D,T],[D,T,H],[D,H],[D1]]);mshare([[L,D,X],[L,D,X,L1],[L,D,X,L1,T],[L,D,X,L1,T,H],[L,D,X,L1,H],[L,D,X,T],[L,D,X,T,H],[L,D,X,H],[L,L1],[D,T],[D,T,H],[D,H],[D1]]))),
    D1=H-T,
    true((mshare([[L,D,X],[L,D,X,L1],[L,D,X,L1,T,H,D1],[L,D,X,L1,T,D1],[L,D,X,L1,H,D1],[L,D,X,T,H,D1],[L,D,X,T,D1],[L,D,X,H,D1],[L,D,L1,T,H,D1],[L,D,L1,T,D1],[L,D,L1,H,D1],[L,L1],[D,T,H,D1],[D,T,D1],[D,H,D1]]);mshare([[L,D,X],[L,D,X,L1],[L,D,X,L1,T,H,D1],[L,D,X,L1,T,D1],[L,D,X,L1,H,D1],[L,D,X,T,H,D1],[L,D,X,T,D1],[L,D,X,H,D1],[L,L1],[D,T,H,D1],[D,T,D1],[D,H,D1]]))),
    difflist1(L1,D1),
    true(mshare([[L,D,X],[L,D,X,L1,T,H,D1],[L,D,X,L1,T,D1],[L,D,X,L1,H,D1],[L,D,X,T,H,D1],[L,D,X,T,D1],[L,D,X,H,D1],[L,D,L1,T,H,D1],[L,D,L1,T,D1],[L,D,L1,H,D1],[D,T,H,D1],[D,T,D1],[D,H,D1]])).

:- prop shlin2(X)
   + native.

:- true pred shlin2(X)
   : mshare([[X]])
   => mshare([[X]]).



