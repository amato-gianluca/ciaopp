:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

:- dynamic prime/1.

:- dynamic candidate/1.

'\006\call_in_module'(sieve,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    clean,
    true(true),
    primes(10000),
    !,
    true(true).

:- true pred clean.

clean :-
    true(mshare([[_1],[_2]])),
    retractall(prime(_1)),
    true(mshare([[_1],[_2]])),
    retractall(candidate(_2)),
    true(mshare([[_1],[_2]])).

:- true pred primes(N)
   : (N=10000).

primes(N) :-
    true(ground([N])),
    'primes/1/1/$disj/1'(N),
    true(ground([N])),
    sieve(N),
    true(ground([N])).

:- true pred 'primes/1/1/$disj/1'(N)
   : ground([N])
   => ground([N]).

'primes/1/1/$disj/1'(N) :-
    true((
        mshare([[I]]),
        ground([N])
    )),
    range(2,N,I),
    true(ground([N,I])),
    'primes/1/1/$disj/1/1/1/$disj/1'(I),
    !,
    true(ground([N,I])),
    fail,
    true(fails(_)).
'primes/1/1/$disj/1'(N).

:- true pred 'primes/1/1/$disj/1/1/1/$disj/1'(I)
   : ground([I])
   => ground([I]).

'primes/1/1/$disj/1/1/1/$disj/1'(I) :-
    true(ground([I])),
    assertz(candidate(I)),
    !,
    true(ground([I])),
    fail,
    true(fails(_)).
'primes/1/1/$disj/1/1/1/$disj/1'(I).

:- true pred sieve(Max)
   : ground([Max])
   => ground([Max]).

sieve(Max) :-
    true((
        mshare([[First]]),
        ground([Max])
    )),
    retract(candidate(First)),
    !,
    true((
        mshare([[First]]),
        ground([Max])
    )),
    assertz(prime(First)),
    true((
        mshare([[First]]),
        ground([Max])
    )),
    First<Max,
    true(ground([Max,First])),
    sieve(First,2,Max),
    true(ground([Max,First])),
    sieve(Max),
    true(ground([Max,First])).
sieve(_1).

:- true pred sieve(N,Mul,Max)
   : ( (Mul=2), ground([N,Max]) )
   => ground([N,Max]).

:- true pred sieve(N,Mul,Max)
   : ground([N,Mul,Max])
   => ground([N,Mul,Max]).

sieve(N,Mul,Max) :-
    true((
        mshare([[I],[Mul2]]),
        ground([N,Mul,Max])
    )),
    I is N*Mul,
    true((
        mshare([[Mul2]]),
        ground([N,Mul,Max,I])
    )),
    I=<Max,
    !,
    true((
        mshare([[Mul2]]),
        ground([N,Mul,Max,I])
    )),
    'sieve/3/1/$disj/1'(I),
    true((
        mshare([[Mul2]]),
        ground([N,Mul,Max,I])
    )),
    Mul2 is Mul+1,
    true(ground([N,Mul,Max,I,Mul2])),
    sieve(N,Mul2,Max),
    true(ground([N,Mul,Max,I,Mul2])).
sieve(_1,_2,_3).

:- true pred 'sieve/3/1/$disj/1'(I)
   : ground([I])
   => ground([I]).

'sieve/3/1/$disj/1'(I) :-
    true(ground([I])),
    retract(candidate(I)),
    !,
    true(ground([I])),
    true,
    true(ground([I])).
'sieve/3/1/$disj/1'(I).

:- true pred range(Low,High,I)
   : ( (Low=2),
       mshare([[I]]),
       ground([High]) )
   => ground([High,I]).

:- true pred range(Low,High,I)
   : ( mshare([[I]]),
       ground([Low,High]) )
   => ground([Low,High,I]).

range(Low,High,Low) :-
    true(ground([Low,High])),
    Low=<High,
    true(ground([Low,High])).
range(Low,High,I) :-
    true((
        mshare([[I],[Low2]]),
        ground([Low,High])
    )),
    Low2 is Low+1,
    true((
        mshare([[I]]),
        ground([Low,High,Low2])
    )),
    Low2=<High,
    true((
        mshare([[I]]),
        ground([Low,High,Low2])
    )),
    range(Low2,High,I),
    true(ground([Low,High,I,Low2])).


