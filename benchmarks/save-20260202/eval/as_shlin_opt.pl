:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(eval,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    t_(1000,1),
    true(true).

t(D,N) :-
    time(t_(D,N)).

:- true pred t_(D,N)
   : ( (D=1000), (N=1) ).

t_(D,N) :-
    true((
        mshare([[Expr]]),
        ground([D,N]),
        linear(Expr)
    )),
    add(D,Expr),
    true(ground([D,N,Expr])),
    't_/2/1/$disj/1'(N,Expr),
    true(ground([D,N,Expr])).

:- true pred 't_/2/1/$disj/1'(N,Expr)
   : ground([N,Expr])
   => ground([N,Expr]).

't_/2/1/$disj/1'(N,Expr) :-
    true((
        mshare([[V]]),
        ground([N,Expr]),
        linear(V)
    )),
    repeat(N),
    true((
        mshare([[V]]),
        ground([N,Expr]),
        linear(V)
    )),
    V is Expr,
    true(ground([N,Expr,V])),
    integer(V),
    true(ground([N,Expr,V])),
    fail,
    true(fails(_)).
't_/2/1/$disj/1'(N,Expr).

:- true pred add(N,_A)
   : ( mshare([[_A]]),
       ground([N]), linear(_A) )
   => ground([N,_A]).

add(0,1) :-
    !,
    true(true).
add(N,Expr+N) :-
    true((
        mshare([[Expr],[N2]]),
        ground([N]),
        linear(Expr),
        linear(N2)
    )),
    N2 is N-1,
    true((
        mshare([[Expr]]),
        ground([N,N2]),
        linear(Expr)
    )),
    add(N2,Expr),
    true(ground([N,Expr,N2])).

:- true pred repeat(N)
   : ground([N])
   => ground([N]).

repeat(N).
repeat(N) :-
    true((
        mshare([[N1]]),
        ground([N]),
        linear(N1)
    )),
    N>0,
    true((
        mshare([[N1]]),
        ground([N]),
        linear(N1)
    )),
    N1 is N-1,
    true(ground([N,N1])),
    repeat(N1),
    true(ground([N,N1])).


