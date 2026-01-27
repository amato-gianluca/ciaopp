:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(derive,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    ops8,
    true(true),
    log10,
    true(true),
    divide10,
    true(true).

:- true pred ops8.

ops8 :-
    true((
        mshare([[_1]]),
        var(_1),
        linear(_1)
    )),
    d((x+1)*((x^2+2)*(x^3+3)),x,_1),
    true(ground([_1])).

:- true pred log10.

log10 :-
    true((
        mshare([[_1]]),
        var(_1),
        linear(_1)
    )),
    d(log(log(log(log(log(log(log(log(log(log(x)))))))))),x,_1),
    true(ground([_1])).

:- true pred divide10.

divide10 :-
    true((
        mshare([[_1]]),
        var(_1),
        linear(_1)
    )),
    d(x/x/x/x/x/x/x/x/x/x,x,_1),
    true(ground([_1])).

:- true pred d(_1,X,_A)
   : ( (_1=x/x/x/x/x/x/x/x/x/x), (X=x),
       mshare([[_A]]),
       var(_A), linear(_A) )
   => ground([_A]).

:- true pred d(_1,X,_A)
   : ( mshare([[_A]]),
       var(_A), ground([_1,X]), linear(_A) )
   => ground([_1,X,_A]).

:- true pred d(_1,X,_A)
   : ( (_1=log(log(log(log(log(log(log(log(log(log(x))))))))))), (X=x),
       mshare([[_A]]),
       var(_A), linear(_A) )
   => ground([_A]).

:- true pred d(_1,X,_A)
   : ( (_1=(x+1)*((x^2+2)*(x^3+3))), (X=x),
       mshare([[_A]]),
       var(_A), linear(_A) )
   => ground([_A]).

d(U+V,X,DU+DV) :-
    !,
    true((
        mshare([[DU],[DV]]),
        var(DU),
        var(DV),
        ground([X,U,V]),
        linear(DU),
        linear(DV)
    )),
    d(U,X,DU),
    true((
        mshare([[DV]]),
        var(DV),
        ground([X,U,V,DU]),
        linear(DV)
    )),
    d(V,X,DV),
    true(ground([X,U,V,DU,DV])).
d(U-V,X,DU-DV) :-
    !,
    true((
        mshare([[DU],[DV]]),
        var(DU),
        var(DV),
        ground([X,U,V]),
        linear(DU),
        linear(DV)
    )),
    d(U,X,DU),
    true((
        mshare([[DV]]),
        var(DV),
        ground([X,U,V,DU]),
        linear(DV)
    )),
    d(V,X,DV),
    true(ground([X,U,V,DU,DV])).
d(U*V,X,DU*V+U*DV) :-
    !,
    true((
        mshare([[DU],[DV]]),
        var(DU),
        var(DV),
        ground([X,U,V]),
        linear(DU),
        linear(DV)
    )),
    d(U,X,DU),
    true((
        mshare([[DV]]),
        var(DV),
        ground([X,U,V,DU]),
        linear(DV)
    )),
    d(V,X,DV),
    true(ground([X,U,V,DU,DV])).
d(U/V,X,(DU*V-U*DV)/V^2) :-
    !,
    true((
        mshare([[DU],[DV]]),
        var(DU),
        var(DV),
        ground([X,U,V]),
        linear(DU),
        linear(DV)
    )),
    d(U,X,DU),
    true((
        mshare([[DV]]),
        var(DV),
        ground([X,U,V,DU]),
        linear(DV)
    )),
    d(V,X,DV),
    true(ground([X,U,V,DU,DV])).
d(U^N,X,DU*N*U^N1) :-
    !,
    true((
        mshare([[DU],[N1]]),
        var(DU),
        var(N1),
        ground([X,U,N]),
        linear(DU),
        linear(N1)
    )),
    integer(N),
    true((
        mshare([[DU],[N1]]),
        var(DU),
        var(N1),
        ground([X,U,N]),
        linear(DU),
        linear(N1)
    )),
    N1 is N-1,
    true((
        mshare([[DU]]),
        var(DU),
        ground([X,U,N,N1]),
        linear(DU)
    )),
    d(U,X,DU),
    true(ground([X,U,N,DU,N1])).
d(-U,X,-DU) :-
    !,
    true((
        mshare([[DU]]),
        var(DU),
        ground([X,U]),
        linear(DU)
    )),
    d(U,X,DU),
    true(ground([X,U,DU])).
d(exp(U),X,exp(U)*DU) :-
    !,
    true((
        mshare([[DU]]),
        var(DU),
        ground([X,U]),
        linear(DU)
    )),
    d(U,X,DU),
    true(ground([X,U,DU])).
d(log(U),X,DU/U) :-
    !,
    true((
        mshare([[DU]]),
        var(DU),
        ground([X,U]),
        linear(DU)
    )),
    d(U,X,DU),
    true(ground([X,U,DU])).
d(X,X,1) :-
    !,
    true(ground([X])).
d(_1,_2,0).


