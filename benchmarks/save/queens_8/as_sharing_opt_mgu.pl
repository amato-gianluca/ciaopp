:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(queens_8,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(mshare([[Qs]])),
    queens(8,Qs),
    true(ground([Qs])),
    fail,
    true(fails(_)).
top.

:- true pred queens(N,Qs)
   : ( (N=8),
       mshare([[Qs]]) )
   => ground([Qs]).

queens(N,Qs) :-
    true((
        mshare([[Qs],[Ns]]),
        ground([N])
    )),
    range(1,N,Ns),
    true((
        mshare([[Qs]]),
        ground([N,Ns])
    )),
    queens(Ns,[],Qs),
    true(ground([N,Qs,Ns])).

:- true pred queens(UnplacedQs,Qs,_A)
   : ( (Qs=[]),
       mshare([[_A]]),
       ground([UnplacedQs]) )
   => ground([UnplacedQs,_A]).

:- true pred queens(UnplacedQs,Qs,_A)
   : ( (Qs=[_B|_C]),
       mshare([[_A]]),
       ground([UnplacedQs,_B,_C]) )
   => ground([UnplacedQs,_A,_B,_C]).

queens([],Qs,Qs).
queens(UnplacedQs,SafeQs,Qs) :-
    true((
        mshare([[Qs],[UnplacedQs1],[Q]]),
        ground([UnplacedQs,SafeQs])
    )),
    queens_8:select(UnplacedQs,UnplacedQs1,Q),
    true((
        mshare([[Qs]]),
        ground([UnplacedQs,SafeQs,UnplacedQs1,Q])
    )),
    not_attack(SafeQs,Q),
    true((
        mshare([[Qs]]),
        ground([UnplacedQs,SafeQs,UnplacedQs1,Q])
    )),
    queens(UnplacedQs1,[Q|SafeQs],Qs),
    true(ground([UnplacedQs,SafeQs,Qs,UnplacedQs1,Q])).

:- true pred not_attack(Xs,X)
   : ground([Xs,X])
   => ground([Xs,X]).

not_attack(Xs,X) :-
    true(ground([Xs,X])),
    not_attack(Xs,X,1),
    true(ground([Xs,X])).

:- true pred not_attack(_A,_1,_2)
   : ( (_2=1), ground([_A,_1]) )
   => ground([_A,_1]).

:- true pred not_attack(_A,_1,_2)
   : ground([_A,_1,_2])
   => ground([_A,_1,_2]).

not_attack([],_1,_2) :-
    !,
    true(ground([_1,_2])).
not_attack([Y|Ys],X,N) :-
    true((
        mshare([[N1]]),
        ground([X,N,Y,Ys])
    )),
    X=\=Y+N,
    true((
        mshare([[N1]]),
        ground([X,N,Y,Ys])
    )),
    X=\=Y-N,
    true((
        mshare([[N1]]),
        ground([X,N,Y,Ys])
    )),
    N1 is N+1,
    true(ground([X,N,Y,Ys,N1])),
    not_attack(Ys,X,N1),
    true(ground([X,N,Y,Ys,N1])).

:- true pred select(_A,Xs,X)
   : ( mshare([[Xs],[X]]),
       ground([_A]) )
   => ground([_A,Xs,X]).

select([X|Xs],Xs,X).
select([Y|Ys],[Y|Zs],X) :-
    true((
        mshare([[X],[Zs]]),
        ground([Y,Ys])
    )),
    queens_8:select(Ys,Zs,X),
    true(ground([X,Y,Ys,Zs])).

:- true pred range(N,_A,_B)
   : ( (N=1),
       mshare([[_B]]),
       ground([_A]) )
   => ground([_A,_B]).

:- true pred range(N,_A,_B)
   : ( mshare([[_B]]),
       ground([N,_A]) )
   => ground([N,_A,_B]).

range(N,N,[N]) :-
    !,
    true(ground([N])).
range(M,N,[M|Ns]) :-
    true((
        mshare([[Ns],[M1]]),
        ground([M,N])
    )),
    M<N,
    true((
        mshare([[Ns],[M1]]),
        ground([M,N])
    )),
    M1 is M+1,
    true((
        mshare([[Ns]]),
        ground([M,N,M1])
    )),
    range(M1,N,Ns),
    true(ground([M,N,Ns,M1])).


