:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(perfect,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(mshare([[C],[X]])),
    findall(C,perfect(100,C),X),
    true((
        mshare([[C]]),
        ground([X])
    )),
    ok(X),
    true((
        mshare([[C]]),
        ground([X])
    )).

:- true pred ok(_A)
   : ground([_A])
   => ground([_A]).

ok([3213876088517980551083924184681057554444177758164088967397376,12554203470773361527671578846336104669690446551334525075456,191561942608236107294793378084303638130997321548169216,46768052394588893382517909811217778170473142550528,182687704666362864775460301858080473799697891328,44601490397061246283066714178813853366747136,2787593149816327892690784192460327776944128,10889035741470030830754200461521744560128,2658455991569831744654692615953842176,166153499473114483824745506383331328,40564819207303336344294875201536,9903520314282971830448816128,38685626227663735544086528,2417851639228158837784576,9444732965670570950656,2305843008139952128,144115187807420416,35184367894528,137438691328,8589869056,33550336,2096128,8128,496,28,6]).

:- true pred divisible(X,Y)
   : ground([X,Y])
   => ground([X,Y]).

divisible(X,Y) :-
    true((
        mshare([[N]]),
        ground([X,Y])
    )),
    N is Y*Y,
    true(ground([X,Y,N])),
    N=<X,
    true(ground([X,Y,N])),
    X mod Y=:=0,
    true(ground([X,Y,N])).
divisible(X,Y) :-
    true((
        mshare([[Y1]]),
        ground([X,Y])
    )),
    Y<X,
    true((
        mshare([[Y1]]),
        ground([X,Y])
    )),
    Y1 is Y+1,
    true(ground([X,Y,Y1])),
    divisible(X,Y1),
    true(ground([X,Y,Y1])).

:- true pred isprime(_A,X)
   : ( mshare([[X]]),
       ground([_A]) )
   => ground([_A,X]).

isprime([X|_1],X) :-
    true((
        mshare([[Y]]),
        ground([X,_1])
    )),
    Y is 2,
    true(ground([X,_1,Y])),
    X>1,
    true(ground([X,_1,Y])),
    'isprime/2/1/$disj/1'(X,Y),
    true(ground([X,_1,Y])).
isprime([_1|T],Z) :-
    true((
        mshare([[Z]]),
        ground([_1,T])
    )),
    isprime(T,Z),
    true(ground([Z,_1,T])).

:- true pred 'isprime/2/1/$disj/1'(X,Y)
   : ground([X,Y])
   => ground([X,Y]).

'isprime/2/1/$disj/1'(X,Y) :-
    true(ground([X,Y])),
    divisible(X,Y),
    !,
    true(ground([X,Y])),
    fail,
    true(fails(_)).
'isprime/2/1/$disj/1'(X,Y).

:- true pred power(_1,K,R)
   : ( (_1=2), (K=_A-1),
       mshare([[R]]),
       ground([_A]) )
   => ground([R,_A]).

:- true pred power(_1,K,R)
   : ( mshare([[R]]),
       ground([_1,K]) )
   => ground([_1,K,R]).

:- true pred power(_1,K,R)
   : ( (_1=2),
       mshare([[R]]),
       ground([K]) )
   => ground([K,R]).

power(_1,0,1) :-
    !,
    true(ground([_1])).
power(N,K,R) :-
    true((
        mshare([[R],[K1],[R1]]),
        ground([N,K])
    )),
    K1 is K-1,
    true((
        mshare([[R],[R1]]),
        ground([N,K,K1])
    )),
    power(N,K1,R1),
    true((
        mshare([[R]]),
        ground([N,K,K1,R1])
    )),
    R is R1*N,
    true(ground([N,K,R,K1,R1])).

:- true pred calc(_A,K,R)
   : ( (_A=2),
       mshare([[R]]),
       ground([K]) )
   => ground([K,R]).

calc(2,K,R) :-
    true((
        mshare([[R],[X],[R1],[R2]]),
        ground([K])
    )),
    power(2,K,X),
    true((
        mshare([[R],[R1],[R2]]),
        ground([K,X])
    )),
    R1 is X-1,
    true((
        mshare([[R],[R2]]),
        ground([K,X,R1])
    )),
    power(2,K-1,R2),
    true((
        mshare([[R]]),
        ground([K,X,R1,R2])
    )),
    R is R1*R2,
    true(ground([K,R,X,R1,R2])).

:- true pred listperf(_A,R)
   : ( mshare([[R]]),
       ground([_A]) )
   => ground([_A,R]).

listperf([K|_1],R) :-
    true((
        mshare([[R]]),
        ground([K,_1])
    )),
    calc(2,K,R),
    true(ground([R,K,_1])).
listperf([_1|T],Z) :-
    true((
        mshare([[Z]]),
        ground([_1,T])
    )),
    listperf(T,Z),
    true(ground([Z,_1,T])).

:- true pred generateList(N,_A)
   : ( mshare([[_A]]),
       ground([N]) )
   => ground([N,_A]).

generateList(0,[]).
generateList(N,[X|Xs]) :-
    true((
        mshare([[X],[X,Xs],[Xs],[N1]]),
        ground([N])
    )),
    N>0,
    true((
        mshare([[X],[X,Xs],[Xs],[N1]]),
        ground([N])
    )),
    X is N+1,
    true((
        mshare([[Xs],[N1]]),
        ground([N,X])
    )),
    N1 is N-1,
    true((
        mshare([[Xs]]),
        ground([N,X,N1])
    )),
    generateList(N1,Xs),
    true(ground([N,X,Xs,N1])).

:- true pred perfect(N,C)
   : ( (N=100),
       mshare([[C]]) )
   => ground([C]).

perfect(N,C) :-
    true((
        mshare([[C],[R],[L],[P]]),
        ground([N])
    )),
    generateList(N,R),
    true((
        mshare([[C],[L],[P]]),
        ground([N,R])
    )),
    findall(L,isprime(R,L),P),
    true((
        mshare([[C],[L]]),
        ground([N,R,P])
    )),
    listperf(P,C),
    true((
        mshare([[L]]),
        ground([N,C,R,P])
    )).


