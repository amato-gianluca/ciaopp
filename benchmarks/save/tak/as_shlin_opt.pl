:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(tak,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    tak,
    true(true).

:- true pred tak.

tak :-
    true((
        mshare([[_1]]),
        linear(_1)
    )),
    tak(18,12,6,_1),
    true(ground([_1])).

:- true pred tak(X,Y,Z,A)
   : ( (X=18), (Y=12), (Z=6),
       mshare([[A]]),
       linear(A) )
   => ground([A]).

:- true pred tak(X,Y,Z,A)
   : ( mshare([[A]]),
       ground([X,Y,Z]), linear(A) )
   => ground([X,Y,Z,A]).

tak(X,Y,Z,A) :-
    true((
        mshare([[A]]),
        ground([X,Y,Z]),
        linear(A)
    )),
    X=<Y,
    true((
        mshare([[A]]),
        ground([X,Y,Z]),
        linear(A)
    )),
    Z=A,
    true(ground([X,Y,Z,A])).
tak(X,Y,Z,A) :-
    true((
        mshare([[A],[X1],[A1],[Y1],[A2],[Z1],[A3]]),
        ground([X,Y,Z]),
        linear(A),
        linear(X1),
        linear(A1),
        linear(Y1),
        linear(A2),
        linear(Z1),
        linear(A3)
    )),
    X>Y,
    true((
        mshare([[A],[X1],[A1],[Y1],[A2],[Z1],[A3]]),
        ground([X,Y,Z]),
        linear(A),
        linear(X1),
        linear(A1),
        linear(Y1),
        linear(A2),
        linear(Z1),
        linear(A3)
    )),
    X1 is X-1,
    true((
        mshare([[A],[A1],[Y1],[A2],[Z1],[A3]]),
        ground([X,Y,Z,X1]),
        linear(A),
        linear(A1),
        linear(Y1),
        linear(A2),
        linear(Z1),
        linear(A3)
    )),
    tak(X1,Y,Z,A1),
    true((
        mshare([[A],[Y1],[A2],[Z1],[A3]]),
        ground([X,Y,Z,X1,A1]),
        linear(A),
        linear(Y1),
        linear(A2),
        linear(Z1),
        linear(A3)
    )),
    Y1 is Y-1,
    true((
        mshare([[A],[A2],[Z1],[A3]]),
        ground([X,Y,Z,X1,A1,Y1]),
        linear(A),
        linear(A2),
        linear(Z1),
        linear(A3)
    )),
    tak(Y1,Z,X,A2),
    true((
        mshare([[A],[Z1],[A3]]),
        ground([X,Y,Z,X1,A1,Y1,A2]),
        linear(A),
        linear(Z1),
        linear(A3)
    )),
    Z1 is Z-1,
    true((
        mshare([[A],[A3]]),
        ground([X,Y,Z,X1,A1,Y1,A2,Z1]),
        linear(A),
        linear(A3)
    )),
    tak(Z1,X,Y,A3),
    true((
        mshare([[A]]),
        ground([X,Y,Z,X1,A1,Y1,A2,Z1,A3]),
        linear(A)
    )),
    tak(A1,A2,A3,A),
    true(ground([X,Y,Z,A,X1,A1,Y1,A2,Z1,A3])).


