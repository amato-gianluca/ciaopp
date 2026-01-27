:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(sendmore,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true((
        mshare([[D],[E],[Y],[C1],[N],[R],[C2],[O],[C3],[S],[M]]),
        linear(D),
        linear(E),
        linear(Y),
        linear(C1),
        linear(N),
        linear(R),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([D],[D]),([E],[E]),([Y],[Y]),([C1],[C1]),([N],[N]),([R],[R]),([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    digit(D),
    true((
        mshare([[E],[Y],[C1],[N],[R],[C2],[O],[C3],[S],[M]]),
        ground([D]),
        linear(E),
        linear(Y),
        linear(C1),
        linear(N),
        linear(R),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([E],[E]),([Y],[Y]),([C1],[C1]),([N],[N]),([R],[R]),([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    digit(E),
    true((
        mshare([[Y],[C1],[N],[R],[C2],[O],[C3],[S],[M]]),
        ground([D,E]),
        linear(Y),
        linear(C1),
        linear(N),
        linear(R),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([Y],[Y]),([C1],[C1]),([N],[N]),([R],[R]),([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    D=\=E,
    true((
        mshare([[Y],[C1],[N],[R],[C2],[O],[C3],[S],[M]]),
        ground([D,E]),
        linear(Y),
        linear(C1),
        linear(N),
        linear(R),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([Y],[Y]),([C1],[C1]),([N],[N]),([R],[R]),([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    sumdigit(0,D,E,Y,C1),
    true((
        mshare([[N],[R],[C2],[O],[C3],[S],[M]]),
        ground([D,E,Y,C1]),
        linear(N),
        linear(R),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([N],[N]),([R],[R]),([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    digit(N),
    true((
        mshare([[R],[C2],[O],[C3],[S],[M]]),
        ground([D,E,Y,C1,N]),
        linear(R),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([R],[R]),([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    N=\=Y,
    true((
        mshare([[R],[C2],[O],[C3],[S],[M]]),
        ground([D,E,Y,C1,N]),
        linear(R),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([R],[R]),([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    N=\=E,
    true((
        mshare([[R],[C2],[O],[C3],[S],[M]]),
        ground([D,E,Y,C1,N]),
        linear(R),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([R],[R]),([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    N=\=D,
    true((
        mshare([[R],[C2],[O],[C3],[S],[M]]),
        ground([D,E,Y,C1,N]),
        linear(R),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([R],[R]),([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    digit(R),
    true((
        mshare([[C2],[O],[C3],[S],[M]]),
        ground([D,E,Y,C1,N,R]),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    R=\=N,
    true((
        mshare([[C2],[O],[C3],[S],[M]]),
        ground([D,E,Y,C1,N,R]),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    R=\=Y,
    true((
        mshare([[C2],[O],[C3],[S],[M]]),
        ground([D,E,Y,C1,N,R]),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    R=\=E,
    true((
        mshare([[C2],[O],[C3],[S],[M]]),
        ground([D,E,Y,C1,N,R]),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    R=\=D,
    true((
        mshare([[C2],[O],[C3],[S],[M]]),
        ground([D,E,Y,C1,N,R]),
        linear(C2),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([C2],[C2]),([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    sumdigit(C1,N,R,E,C2),
    true((
        mshare([[O],[C3],[S],[M]]),
        ground([D,E,Y,C1,N,R,C2]),
        linear(O),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([O],[O]),([C3],[C3]),([S],[S]),([M],[M])])
    )),
    digit(O),
    true((
        mshare([[C3],[S],[M]]),
        ground([D,E,Y,C1,N,R,C2,O]),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([C3],[C3]),([S],[S]),([M],[M])])
    )),
    O=\=R,
    true((
        mshare([[C3],[S],[M]]),
        ground([D,E,Y,C1,N,R,C2,O]),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([C3],[C3]),([S],[S]),([M],[M])])
    )),
    O=\=N,
    true((
        mshare([[C3],[S],[M]]),
        ground([D,E,Y,C1,N,R,C2,O]),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([C3],[C3]),([S],[S]),([M],[M])])
    )),
    O=\=Y,
    true((
        mshare([[C3],[S],[M]]),
        ground([D,E,Y,C1,N,R,C2,O]),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([C3],[C3]),([S],[S]),([M],[M])])
    )),
    O=\=E,
    true((
        mshare([[C3],[S],[M]]),
        ground([D,E,Y,C1,N,R,C2,O]),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([C3],[C3]),([S],[S]),([M],[M])])
    )),
    O=\=D,
    true((
        mshare([[C3],[S],[M]]),
        ground([D,E,Y,C1,N,R,C2,O]),
        linear(C3),
        linear(S),
        linear(M),
        shlin2([([C3],[C3]),([S],[S]),([M],[M])])
    )),
    sumdigit(C2,E,O,N,C3),
    true((
        mshare([[S],[M]]),
        ground([D,E,Y,C1,N,R,C2,O,C3]),
        linear(S),
        linear(M),
        shlin2([([S],[S]),([M],[M])])
    )),
    leftdigit(S),
    true((
        mshare([[M]]),
        ground([D,E,Y,C1,N,R,C2,O,C3,S]),
        linear(M),
        shlin2([([M],[M])])
    )),
    S=\=O,
    true((
        mshare([[M]]),
        ground([D,E,Y,C1,N,R,C2,O,C3,S]),
        linear(M),
        shlin2([([M],[M])])
    )),
    S=\=R,
    true((
        mshare([[M]]),
        ground([D,E,Y,C1,N,R,C2,O,C3,S]),
        linear(M),
        shlin2([([M],[M])])
    )),
    S=\=N,
    true((
        mshare([[M]]),
        ground([D,E,Y,C1,N,R,C2,O,C3,S]),
        linear(M),
        shlin2([([M],[M])])
    )),
    S=\=Y,
    true((
        mshare([[M]]),
        ground([D,E,Y,C1,N,R,C2,O,C3,S]),
        linear(M),
        shlin2([([M],[M])])
    )),
    S=\=E,
    true((
        mshare([[M]]),
        ground([D,E,Y,C1,N,R,C2,O,C3,S]),
        linear(M),
        shlin2([([M],[M])])
    )),
    S=\=D,
    true((
        mshare([[M]]),
        ground([D,E,Y,C1,N,R,C2,O,C3,S]),
        linear(M),
        shlin2([([M],[M])])
    )),
    leftdigit(M),
    true(ground([D,E,Y,C1,N,R,C2,O,C3,S,M])),
    M=\=S,
    true(ground([D,E,Y,C1,N,R,C2,O,C3,S,M])),
    M=\=O,
    true(ground([D,E,Y,C1,N,R,C2,O,C3,S,M])),
    M=\=R,
    true(ground([D,E,Y,C1,N,R,C2,O,C3,S,M])),
    M=\=N,
    true(ground([D,E,Y,C1,N,R,C2,O,C3,S,M])),
    M=\=Y,
    true(ground([D,E,Y,C1,N,R,C2,O,C3,S,M])),
    M=\=E,
    true(ground([D,E,Y,C1,N,R,C2,O,C3,S,M])),
    M=\=D,
    true(ground([D,E,Y,C1,N,R,C2,O,C3,S,M])),
    sumdigit(C3,S,M,O,M),
    true(ground([D,E,Y,C1,N,R,C2,O,C3,S,M])),
    fail,
    true(fails(_)).
top.

:- true pred sumdigit(C,A,B,S,D)
   : ( (B=D), ground([C,A,B,S]) )
   => ground([C,A,B,S]).

:- true pred sumdigit(C,A,B,S,D)
   : ( mshare([[D]]),
       ground([C,A,B,S]), linear(D), shlin2([([D],[D])]) )
   => ground([C,A,B,S,D]).

:- true pred sumdigit(C,A,B,S,D)
   : ( (C=0),
       mshare([[S],[D]]),
       ground([A,B]), linear(S), linear(D), shlin2([([S],[S]),([D],[D])]) )
   => ground([A,B,S,D]).

sumdigit(C,A,B,S,D) :-
    true((mshare([[S],[D],[X]]),ground([C,A,B]),linear(S),linear(D),linear(X),shlin2([([S],[S]),([D],[D]),([X],[X])]);mshare([[D],[X]]),ground([C,A,B,S]),linear(D),linear(X),shlin2([([D],[D]),([X],[X])]);mshare([[X]]),ground([C,A,B,S,D]),linear(X),shlin2([([X],[X])]))),
    X is C+A+B,
    true((mshare([[S],[D]]),ground([C,A,B,X]),linear(S),linear(D),shlin2([([S],[S]),([D],[D])]);mshare([[D]]),ground([C,A,B,S,X]),linear(D),shlin2([([D],[D])]);ground([C,A,B,S,D,X]))),
    'sumdigit/5/1/$disj/1'(S,D,X),
    true(ground([C,A,B,S,D,X])).

:- true pred 'sumdigit/5/1/$disj/1'(S,D,X)
   : ground([S,D,X])
   => ground([S,D,X]).

:- true pred 'sumdigit/5/1/$disj/1'(S,D,X)
   : ( mshare([[D]]),
       ground([S,X]), linear(D), shlin2([([D],[D])]) )
   => ground([S,D,X]).

:- true pred 'sumdigit/5/1/$disj/1'(S,D,X)
   : ( mshare([[S],[D]]),
       ground([X]), linear(S), linear(D), shlin2([([S],[S]),([D],[D])]) )
   => ground([S,D,X]).

'sumdigit/5/1/$disj/1'(S,D,X) :-
    true((mshare([[S],[D]]),ground([X]),linear(S),linear(D),shlin2([([S],[S]),([D],[D])]);mshare([[D]]),ground([S,X]),linear(D),shlin2([([D],[D])]);ground([S,D,X]))),
    X<10,
    !,
    true((mshare([[S],[D]]),ground([X]),linear(S),linear(D),shlin2([([S],[S]),([D],[D])]);mshare([[D]]),ground([S,X]),linear(D),shlin2([([D],[D])]);ground([S,D,X]))),
    S=X,
    true((mshare([[D]]),ground([S,X]),linear(D),shlin2([([D],[D])]);ground([S,D,X]))),
    D=0,
    true(ground([S,D,X])).
'sumdigit/5/1/$disj/1'(S,D,X) :-
    true((mshare([[S],[D]]),ground([X]),linear(S),linear(D),shlin2([([S],[S]),([D],[D])]);mshare([[D]]),ground([S,X]),linear(D),shlin2([([D],[D])]);ground([S,D,X]))),
    S is X-10,
    true((mshare([[D]]),ground([S,X]),linear(D),shlin2([([D],[D])]);ground([S,D,X]))),
    D=1,
    true(ground([S,D,X])).

:- true pred digit(_A)
   : ( mshare([[_A]]),
       linear(_A), shlin2([([_A],[_A])]) )
   => ground([_A]).

digit(0).
digit(1).
digit(2).
digit(3).
digit(4).
digit(5).
digit(6).
digit(7).
digit(8).
digit(9).

:- true pred leftdigit(_A)
   : ( mshare([[_A]]),
       linear(_A), shlin2([([_A],[_A])]) )
   => ground([_A]).

leftdigit(1).
leftdigit(2).
leftdigit(3).
leftdigit(4).
leftdigit(5).
leftdigit(6).
leftdigit(7).
leftdigit(8).
leftdigit(9).


