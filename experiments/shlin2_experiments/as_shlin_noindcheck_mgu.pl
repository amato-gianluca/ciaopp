:- module(_1,[],[assertions,nativeprops]).

:- set_prolog_flag(single_var_warnings,off).

:- entry example1(U,V,W,X,Y,Z)
   : ( nonvar([([U,X],[U,X]),([V,X],[V,X]),([W,X],[W]),([Y],[Y]),([Z],[Z])]), mshare([U,V,W,X,Y,Z],[[U,X],[V,X],[W,X],[Y],[Z]]), linear([U,V,W,Y,Z]) ).

:- true pred example1(U,V,W,X,Y,Z)
   : ( mshare([[U,X],[V,X],[W,X],[Y],[Z]]),
       linear(U), linear(V), linear(W), linear(Y), linear(Z) )
   => ( mshare([[U,X,Y],[U,X,Y,Z],[U,X,Z],[V,X,Y],[V,X,Y,Z],[V,X,Z]]),
        ground([W]), linear(U), linear(V) ).

example1(U,V,W,X,Y,Z) :-
    true((
        mshare([[U,X],[V,X],[W,X],[Y],[Z]]),
        linear(U),
        linear(V),
        linear(W),
        linear(Y),
        linear(Z)
    )),
    X=f(Y,Z),
    true((
        mshare([[U,X,Y],[U,X,Y,Z],[U,X,Z],[V,X,Y],[V,X,Y,Z],[V,X,Z],[W,X,Y],[W,X,Y,Z],[W,X,Z]]),
        linear(U),
        linear(V),
        linear(W)
    )),
    W=g,
    true((
        mshare([[U,X,Y],[U,X,Y,Z],[U,X,Z],[V,X,Y],[V,X,Y,Z],[V,X,Z]]),
        ground([W]),
        linear(U),
        linear(V)
    )).

:- entry example2(U,V,X,Y)
   : ( nonvar([([X],[]),([X,U],[X,U]),([X,Y],[X,Y]),([Y,V],[Y,V])]), mshare([U,V,X,Y],[[X],[X,U],[X,Y],[Y,V]]), linear([U,Y,V]) ).

:- true pred example2(U,V,X,Y)
   : ( mshare([[U,X],[V,Y],[X],[X,Y]]),
       linear(U), linear(V), linear(Y) )
   => mshare([[U,V,X,Y],[U,X,Y],[V,X,Y],[X,Y]]).

example2(U,V,X,Y) :-
    true((
        mshare([[U,X],[V,Y],[X],[X,Y]]),
        linear(U),
        linear(V),
        linear(Y)
    )),
    X=r(Y,Y),
    true(mshare([[U,V,X,Y],[U,X,Y],[V,X,Y],[X,Y]])).

:- entry example3(U,V,W,X,Y)
   : ( mshare([U,V,W,X,Y],[[U,X],[V,X],[W,X],[Y]]), linear([U,V,W,X,Y]) ).

:- true pred example3(U,V,W,X,Y)
   : ( mshare([[U,X],[V,X],[W,X],[Y]]),
       linear(U), linear(V), linear(W), linear(X), linear(Y) )
   => ( mshare([[U,V,X,Y],[U,W,X,Y],[U,X,Y],[V,W,X,Y],[V,X,Y],[W,X,Y]]),
        linear(Y) ).

example3(U,V,W,X,Y) :-
    true((
        mshare([[U,X],[V,X],[W,X],[Y]]),
        linear(U),
        linear(V),
        linear(W),
        linear(X),
        linear(Y)
    )),
    X=r(Y,Y),
    true((
        mshare([[U,V,X,Y],[U,W,X,Y],[U,X,Y],[V,W,X,Y],[V,X,Y],[W,X,Y]]),
        linear(Y)
    )).

:- entry example4(U,X,Y,Z)
   : ( mshare([U,X,Y,Z],[[U,X],[X,Y],[Y,Z]]), linear([U,X,Y,Z]) ).

:- true pred example4(U,X,Y,Z)
   : ( mshare([[U,X],[X,Y],[Y,Z]]),
       linear(U), linear(X), linear(Y), linear(Z) )
   => ( mshare([[U,X,Y,Z],[X,Y]]),
        linear(U), linear(Z) ).

example4(U,X,Y,Z) :-
    true((
        mshare([[U,X],[X,Y],[Y,Z]]),
        linear(U),
        linear(X),
        linear(Y),
        linear(Z)
    )),
    X=r(Y),
    true((
        mshare([[U,X,Y,Z],[X,Y]]),
        linear(U),
        linear(Z)
    )).

:- entry example5.

:- true pred example5.

example5 :-
    true((
        mshare([[L],[H],[T]]),
        linear(L),
        linear(H),
        linear(T)
    )),
    difflist(L,H,T),
    true(mshare([[L,H],[L,H,T],[H,T]])),
    H=T,
    true(mshare([[L,H,T],[H,T]])).

:- true pred difflist(L,H,T)
   : ( mshare([[L],[H],[T]]),
       linear(L), linear(H), linear(T) )
   => mshare([[L,H],[L,H,T],[H,T]]).

difflist(L,H,T) :-
    true((
        mshare([[L],[H],[T]]),
        linear(L),
        linear(H),
        linear(T)
    )),
    L=[],
    true((
        mshare([[H],[T]]),
        ground([L]),
        linear(H),
        linear(T)
    )),
    H=T,
    true((
        mshare([[H,T]]),
        ground([L]),
        linear(H),
        linear(T)
    )).
difflist(L,H,T) :-
    true((
        mshare([[L],[H],[T],[X],[L1],[H1]]),
        linear(L),
        linear(H),
        linear(T),
        linear(X),
        linear(L1),
        linear(H1)
    )),
    L=[X|L1],
    true((
        mshare([[L,X],[L,L1],[H],[T],[H1]]),
        linear(L),
        linear(H),
        linear(T),
        linear(X),
        linear(L1),
        linear(H1)
    )),
    H=[X|H1],
    true((
        mshare([[L,H,X],[L,L1],[H,H1],[T]]),
        linear(L),
        linear(H),
        linear(T),
        linear(X),
        linear(L1),
        linear(H1)
    )),
    difflist(L1,H1,T),
    true(mshare([[L,H,T,L1,H1],[L,H,X],[L,H,L1,H1],[H,T,H1]])).

:- entry example6.

:- true pred example6.

example6 :-
    true((
        mshare([[L],[D],[T],[X1],[X2],[H]]),
        linear(L),
        linear(D),
        linear(T),
        linear(X1),
        linear(X2),
        linear(H)
    )),
    difflist1(L,D),
    true(mshare([[L,D],[D],[T],[X1],[X2],[H]])),
    D=[X1,X2|H]-T,
    true(mshare([[L,D,T],[L,D,T,X1],[L,D,T,X1,X2],[L,D,T,X1,X2,H],[L,D,T,X1,H],[L,D,T,X2],[L,D,T,X2,H],[L,D,T,H],[L,D,X1],[L,D,X1,X2],[L,D,X1,X2,H],[L,D,X1,H],[L,D,X2],[L,D,X2,H],[L,D,H],[D,T],[D,T,X1],[D,T,X1,X2],[D,T,X1,X2,H],[D,T,X1,H],[D,T,X2],[D,T,X2,H],[D,T,H],[D,X1],[D,X1,X2],[D,X1,X2,H],[D,X1,H],[D,X2],[D,X2,H],[D,H]])).

:- entry difflist1(L,D)
   : ( mshare([L,D],[[L],[D]]), linear([L,D]) ).

:- true pred difflist1(L,D)
   : ( mshare([[L],[D]]),
       linear(L), linear(D) )
   => mshare([[L,D],[D]]).

difflist1(L,D) :-
    true((
        mshare([[L],[D],[H]]),
        linear(L),
        linear(D),
        linear(H)
    )),
    L=[],
    true((
        mshare([[D],[H]]),
        ground([L]),
        linear(D),
        linear(H)
    )),
    D=H-H,
    true((
        mshare([[D,H]]),
        ground([L]),
        linear(H)
    )).
difflist1(L,D) :-
    true((
        mshare([[L],[D],[X],[L1],[T],[H],[D1]]),
        linear(L),
        linear(D),
        linear(X),
        linear(L1),
        linear(T),
        linear(H),
        linear(D1)
    )),
    L=[X|L1],
    true((
        mshare([[L,X],[L,L1],[D],[T],[H],[D1]]),
        linear(L),
        linear(D),
        linear(X),
        linear(L1),
        linear(T),
        linear(H),
        linear(D1)
    )),
    D=[X|H]-T,
    true((
        mshare([[L,D,X],[L,L1],[D,T],[D,H],[D1]]),
        linear(L),
        linear(D),
        linear(X),
        linear(L1),
        linear(T),
        linear(H),
        linear(D1)
    )),
    D1=H-T,
    true((
        mshare([[L,D,X],[L,L1],[D,T,D1],[D,H,D1]]),
        linear(L),
        linear(D),
        linear(X),
        linear(L1),
        linear(T),
        linear(H),
        linear(D1)
    )),
    difflist1(L1,D1),
    true(mshare([[L,D,X],[L,D,L1,T,H,D1],[L,D,L1,T,D1],[L,D,L1,H,D1],[D,T,H,D1],[D,T,D1],[D,H,D1]])).


