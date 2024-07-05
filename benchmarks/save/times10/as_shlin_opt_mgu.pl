:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(times10,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    times10,
    true(true).

:- true pred times10.

times10 :-
    true((
        mshare([[_1]]),
        linear(_1)
    )),
    d(x*x*x*x*x*x*x*x*x*x,x,_1),
    true(ground([_1])).

:- true pred d(_1,X,_A)
   : ( (_1=x*x*x*x*x*x*x*x*x*x), (X=x),
       mshare([[_A]]),
       linear(_A) )
   => ground([_A]).

:- true pred d(_1,X,_A)
   : ( mshare([[_A]]),
       ground([_1,X]) )
   => ground([_1,X,_A]).

:- true pred d(_1,X,_A)
   : ( mshare([[_A]]),
       ground([_1,X]), linear(_A) )
   => ground([_1,X,_A]).

d(U+V,X,DU+DV) :-
    !,
    true((mshare([[DU],[DU,DV],[DV]]),ground([X,U,V]);mshare([[DU],[DV]]),ground([X,U,V]),linear(DU),linear(DV))),
    d(U,X,DU),
    true((
        mshare([[DV]]),
        ground([X,U,V,DU])
    )),
    d(V,X,DV),
    true(ground([X,U,V,DU,DV])).
d(U-V,X,DU-DV) :-
    !,
    true((mshare([[DU],[DU,DV],[DV]]),ground([X,U,V]);mshare([[DU],[DV]]),ground([X,U,V]),linear(DU),linear(DV))),
    d(U,X,DU),
    true((
        mshare([[DV]]),
        ground([X,U,V,DU])
    )),
    d(V,X,DV),
    true(ground([X,U,V,DU,DV])).
d(U*V,X,DU*V+U*DV) :-
    !,
    true((mshare([[DU],[DU,DV],[DV]]),ground([X,U,V]);mshare([[DU],[DV]]),ground([X,U,V]),linear(DU),linear(DV))),
    d(U,X,DU),
    true((
        mshare([[DV]]),
        ground([X,U,V,DU])
    )),
    d(V,X,DV),
    true(ground([X,U,V,DU,DV])).
d(U/V,X,(DU*V-U*DV)/V^2) :-
    !,
    true((mshare([[DU],[DU,DV],[DV]]),ground([X,U,V]);mshare([[DU],[DV]]),ground([X,U,V]),linear(DU),linear(DV))),
    d(U,X,DU),
    true((
        mshare([[DV]]),
        ground([X,U,V,DU])
    )),
    d(V,X,DV),
    true(ground([X,U,V,DU,DV])).
d(U^N,X,DU*N*U^N1) :-
    !,
    true((mshare([[DU],[DU,N1],[N1]]),ground([X,U,N]);mshare([[DU],[N1]]),ground([X,U,N]),linear(DU),linear(N1))),
    integer(N),
    true((mshare([[DU],[DU,N1],[N1]]),ground([X,U,N]);mshare([[DU],[N1]]),ground([X,U,N]),linear(DU),linear(N1))),
    N1 is N-1,
    true((mshare([[DU]]),ground([X,U,N,N1]);mshare([[DU]]),ground([X,U,N,N1]),linear(DU))),
    d(U,X,DU),
    true(ground([X,U,N,DU,N1])).
d(-U,X,-DU) :-
    !,
    true((mshare([[DU]]),ground([X,U]);mshare([[DU]]),ground([X,U]),linear(DU))),
    d(U,X,DU),
    true(ground([X,U,DU])).
d(exp(U),X,exp(U)*DU) :-
    !,
    true((mshare([[DU]]),ground([X,U]);mshare([[DU]]),ground([X,U]),linear(DU))),
    d(U,X,DU),
    true(ground([X,U,DU])).
d(log(U),X,DU/U) :-
    !,
    true((mshare([[DU]]),ground([X,U]);mshare([[DU]]),ground([X,U]),linear(DU))),
    d(U,X,DU),
    true(ground([X,U,DU])).
d(X,X,1) :-
    !,
    true(ground([X])).
d(_1,_2,0).

