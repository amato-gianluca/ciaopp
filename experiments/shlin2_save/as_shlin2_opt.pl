:- module(_1,[],[assertions,nativeprops]).

:- prop shlin2(X)+native.

:- impl_defined(shlin2/1).

:- set_prolog_flag(single_var_warnings,off).

:- entry example1(U,V,W,X,Y,Z)
   : ( shlin2([([U,X],[U,X]),([V,X],[V,X]),([W,X],[W]),([Y],[Y]),([Z],[Z])]), mshare([U,V,W,X,Y,Z],[[U,X],[V,X],[W,X],[Y],[Z]]), linear([U,V,W,Y,Z]) ).

:- true pred example1(U,V,W,X,Y,Z)
   : ( mshare([[U,X],[V,X],[W,X],[Y],[Z]]),
       linear(U), linear(V), linear(W), linear(Y), linear(Z), shlin2([([U,X],[U,X]),([V,X],[V,X]),([W,X],[W]),([Y],[Y]),([Z],[Z])]) )
   => ( mshare([[U,X,Y],[U,X,Z],[V,X,Y],[V,X,Z]]),
        ground([W]), linear(U), linear(V), linear(X), linear(Y), linear(Z), shlin2([([U,X,Y],[U,X,Y]),([U,X,Z],[U,X,Z]),([V,X,Y],[V,X,Y]),([V,X,Z],[V,X,Z])]) ).

example1(U,V,W,X,Y,Z) :-
    true((
        mshare([[U,X],[V,X],[W,X],[Y],[Z]]),
        linear(U),
        linear(V),
        linear(W),
        linear(Y),
        linear(Z),
        shlin2([([U,X],[U,X]),([V,X],[V,X]),([W,X],[W]),([Y],[Y]),([Z],[Z])])
    )),
    X=f(Y,Z),
    true((
        mshare([[U,X,Y],[U,X,Z],[V,X,Y],[V,X,Z],[W,X,Y],[W,X,Y,Z],[W,X,Z]]),
        linear(U),
        linear(V),
        linear(W),
        shlin2([([U,X,Y],[U,X,Y]),([U,X,Z],[U,X,Z]),([V,X,Y],[V,X,Y]),([V,X,Z],[V,X,Z]),([W,X,Y],[W]),([W,X,Y,Z],[W]),([W,X,Z],[W])])
    )),
    W=g,
    true((
        mshare([[U,X,Y],[U,X,Z],[V,X,Y],[V,X,Z]]),
        ground([W]),
        linear(U),
        linear(V),
        linear(X),
        linear(Y),
        linear(Z),
        shlin2([([U,X,Y],[U,X,Y]),([U,X,Z],[U,X,Z]),([V,X,Y],[V,X,Y]),([V,X,Z],[V,X,Z])])
    )).

:- entry example2(U,V,X,Y)
   : ( shlin2([([X],[]),([X,U],[X,U]),([X,Y],[X,Y]),([Y,V],[Y,V])]), mshare([U,V,X,Y],[[X],[X,U],[X,Y],[Y,V]]), linear([U,Y,V]) ).

:- true pred example2(U,V,X,Y)
   : ( mshare([[U,X],[V,Y],[X],[X,Y]]),
       linear(U), linear(V), linear(Y), shlin2([([U,X],[U,X]),([V,Y],[V,Y]),([X],[]),([X,Y],[X,Y])]) )
   => ( mshare([[U,V,X,Y],[U,X,Y],[V,X,Y],[X,Y]]),
        shlin2([([U,V,X,Y],[]),([U,X,Y],[]),([V,X,Y],[]),([X,Y],[])]) ).

example2(U,V,X,Y) :-
    true((
        mshare([[U,X],[V,Y],[X],[X,Y]]),
        linear(U),
        linear(V),
        linear(Y),
        shlin2([([U,X],[U,X]),([V,Y],[V,Y]),([X],[]),([X,Y],[X,Y])])
    )),
    X=r(Y,Y),
    true((
        mshare([[U,V,X,Y],[U,X,Y],[V,X,Y],[X,Y]]),
        shlin2([([U,V,X,Y],[]),([U,X,Y],[]),([V,X,Y],[]),([X,Y],[])])
    )).

:- entry example3(U,V,W,X,Y)
   : ( mshare([U,V,W,X,Y],[[U,X],[V,X],[W,X],[Y]]), linear([U,V,W,X,Y]) ).

:- true pred example3(U,V,W,X,Y)
   : ( mshare([[U,X],[V,X],[W,X],[Y]]),
       linear(U), linear(V), linear(W), linear(X), linear(Y), shlin2([([U,X],[U,X]),([V,X],[V,X]),([W,X],[W,X]),([Y],[Y])]) )
   => ( mshare([[U,V,X,Y],[U,W,X,Y],[U,X,Y],[V,W,X,Y],[V,X,Y],[W,X,Y]]),
        linear(Y), shlin2([([U,V,X,Y],[U,V,Y]),([U,W,X,Y],[U,W,Y]),([U,X,Y],[Y]),([V,W,X,Y],[V,W,Y]),([V,X,Y],[Y]),([W,X,Y],[Y])]) ).

example3(U,V,W,X,Y) :-
    true((
        mshare([[U,X],[V,X],[W,X],[Y]]),
        linear(U),
        linear(V),
        linear(W),
        linear(X),
        linear(Y),
        shlin2([([U,X],[U,X]),([V,X],[V,X]),([W,X],[W,X]),([Y],[Y])])
    )),
    X=r(Y,Y),
    true((
        mshare([[U,V,X,Y],[U,W,X,Y],[U,X,Y],[V,W,X,Y],[V,X,Y],[W,X,Y]]),
        linear(Y),
        shlin2([([U,V,X,Y],[U,V,Y]),([U,W,X,Y],[U,W,Y]),([U,X,Y],[Y]),([V,W,X,Y],[V,W,Y]),([V,X,Y],[Y]),([W,X,Y],[Y])])
    )).

:- entry example4(U,X,Y,Z)
   : ( mshare([U,X,Y,Z],[[U,X],[X,Y],[Y,Z]]), linear([U,X,Y,Z]) ).

:- true pred example4(U,X,Y,Z)
   : ( mshare([[U,X],[X,Y],[Y,Z]]),
       linear(U), linear(X), linear(Y), linear(Z), shlin2([([U,X],[U,X]),([X,Y],[X,Y]),([Y,Z],[Y,Z])]) )
   => ( mshare([[U,X,Y,Z]]),
        linear(U), linear(Z), shlin2([([U,X,Y,Z],[U,Z])]) ).

example4(U,X,Y,Z) :-
    true((
        mshare([[U,X],[X,Y],[Y,Z]]),
        linear(U),
        linear(X),
        linear(Y),
        linear(Z),
        shlin2([([U,X],[U,X]),([X,Y],[X,Y]),([Y,Z],[Y,Z])])
    )),
    X=r(Y),
    true((
        mshare([[U,X,Y,Z]]),
        linear(U),
        linear(Z),
        shlin2([([U,X,Y,Z],[U,Z])])
    )).

:- entry example5.

:- true pred example5.

example5 :-
    true((
        mshare([[L],[H],[T]]),
        linear(L),
        linear(H),
        linear(T),
        shlin2([([L],[L]),([H],[H]),([T],[T])])
    )),
    difflist(L,H,T),
    true((
        mshare([[L,H],[H,T]]),
        linear(L),
        linear(H),
        linear(T),
        shlin2([([L,H],[L,H]),([H,T],[H,T])])
    )),
    H=T,
    true((
        mshare([[H,T]]),
        ground([L]),
        shlin2([([H,T],[])])
    )).

:- true pred difflist(L,H,T)
   : ( mshare([[L],[H],[T]]),
       linear(L), linear(H), linear(T), shlin2([([L],[L]),([H],[H]),([T],[T])]) )
   => ( mshare([[L,H],[H,T]]),
        linear(L), linear(H), linear(T), shlin2([([L,H],[L,H]),([H,T],[H,T])]) ).

difflist(L,H,T) :-
    true((
        mshare([[L],[H],[T]]),
        linear(L),
        linear(H),
        linear(T),
        shlin2([([L],[L]),([H],[H]),([T],[T])])
    )),
    L=[],
    true((
        mshare([[H],[T]]),
        ground([L]),
        linear(H),
        linear(T),
        shlin2([([H],[H]),([T],[T])])
    )),
    H=T,
    true((
        mshare([[H,T]]),
        ground([L]),
        linear(H),
        linear(T),
        shlin2([([H,T],[H,T])])
    )).
difflist(L,H,T) :-
    true((
        mshare([[L],[H],[T],[X],[L1],[H1]]),
        linear(L),
        linear(H),
        linear(T),
        linear(X),
        linear(L1),
        linear(H1),
        shlin2([([L],[L]),([H],[H]),([T],[T]),([X],[X]),([L1],[L1]),([H1],[H1])])
    )),
    L=[X|L1],
    true((
        mshare([[L,X],[L,L1],[H],[T],[H1]]),
        linear(L),
        linear(H),
        linear(T),
        linear(X),
        linear(L1),
        linear(H1),
        shlin2([([L,X],[L,X]),([L,L1],[L,L1]),([H],[H]),([T],[T]),([H1],[H1])])
    )),
    H=[X|H1],
    true((
        mshare([[L,H,X],[L,L1],[H,H1],[T]]),
        linear(L),
        linear(H),
        linear(T),
        linear(X),
        linear(L1),
        linear(H1),
        shlin2([([L,H,X],[L,H,X]),([L,L1],[L,L1]),([H,H1],[H,H1]),([T],[T])])
    )),
    difflist(L1,H1,T),
    true((
        mshare([[L,H,X],[L,H,L1,H1],[H,T,H1]]),
        linear(L),
        linear(H),
        linear(T),
        linear(X),
        linear(L1),
        linear(H1),
        shlin2([([L,H,X],[L,H,X]),([L,H,L1,H1],[L,H,L1,H1]),([H,T,H1],[H,T,H1])])
    )).

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
        linear(H),
        shlin2([([L],[L]),([D],[D]),([T],[T]),([X1],[X1]),([X2],[X2]),([H],[H])])
    )),
    difflist1(L,D),
    true((
        mshare([[L,D],[D],[T],[X1],[X2],[H]]),
        linear(L),
        linear(T),
        linear(X1),
        linear(X2),
        linear(H),
        shlin2([([L,D],[L,D]),([D],[]),([T],[T]),([X1],[X1]),([X2],[X2]),([H],[H])])
    )),
    D=[X1,X2|H]-T,
    true((
        mshare([[L,D,T],[L,D,X1],[L,D,X2],[L,D,H],[D,T],[D,T,X1],[D,T,X1,X2],[D,T,X1,X2,H],[D,T,X1,H],[D,T,X2],[D,T,X2,H],[D,T,H],[D,X1],[D,X1,X2],[D,X1,X2,H],[D,X1,H],[D,X2],[D,X2,H],[D,H]]),
        linear(L),
        shlin2([([L,D,T],[L,D,T]),([L,D,X1],[L,D,X1]),([L,D,X2],[L,D,X2]),([L,D,H],[L,D,H]),([D,T],[]),([D,T,X1],[]),([D,T,X1,X2],[]),([D,T,X1,X2,H],[]),([D,T,X1,H],[]),([D,T,X2],[]),([D,T,X2,H],[]),([D,T,H],[]),([D,X1],[]),([D,X1,X2],[]),([D,X1,X2,H],[]),([D,X1,H],[]),([D,X2],[]),([D,X2,H],[]),([D,H],[])])
    )).

:- entry difflist1(L,D)
   : ( mshare([L,D],[[L],[D]]), linear([L,D]) ).

:- true pred difflist1(L,D)
   : ( mshare([[L],[D]]),
       linear(L), linear(D), shlin2([([L],[L]),([D],[D])]) )
   => ( mshare([[L,D],[D]]),
        linear(L), shlin2([([L,D],[L,D]),([D],[])]) ).

difflist1(L,D) :-
    true((
        mshare([[L],[D],[H]]),
        linear(L),
        linear(D),
        linear(H),
        shlin2([([L],[L]),([D],[D]),([H],[H])])
    )),
    L=[],
    true((
        mshare([[D],[H]]),
        ground([L]),
        linear(D),
        linear(H),
        shlin2([([D],[D]),([H],[H])])
    )),
    D=H-H,
    true((
        mshare([[D,H]]),
        ground([L]),
        linear(H),
        shlin2([([D,H],[H])])
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
        linear(D1),
        shlin2([([L],[L]),([D],[D]),([X],[X]),([L1],[L1]),([T],[T]),([H],[H]),([D1],[D1])])
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
        linear(D1),
        shlin2([([L,X],[L,X]),([L,L1],[L,L1]),([D],[D]),([T],[T]),([H],[H]),([D1],[D1])])
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
        linear(D1),
        shlin2([([L,D,X],[L,D,X]),([L,L1],[L,L1]),([D,T],[D,T]),([D,H],[D,H]),([D1],[D1])])
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
        linear(D1),
        shlin2([([L,D,X],[L,D,X]),([L,L1],[L,L1]),([D,T,D1],[D,T,D1]),([D,H,D1],[D,H,D1])])
    )),
    difflist1(L1,D1),
    true((
        mshare([[L,D,X],[L,D,L1,T,D1],[L,D,L1,H,D1],[D,T,H,D1],[D,T,D1],[D,H,D1]]),
        linear(L),
        linear(X),
        linear(L1),
        shlin2([([L,D,X],[L,D,X]),([L,D,L1,T,D1],[L,D,L1,T,D1]),([L,D,L1,H,D1],[L,D,L1,H,D1]),([D,T,H,D1],[]),([D,T,D1],[]),([D,H,D1],[])])
    )).

:- prop shlin2(X)
   + native.

:- true pred shlin2(X)
   : ( mshare([[X]]),
       shlin2([([X],[])]) )
   => ( mshare([[X]]),
        shlin2([([X],[])]) ).



