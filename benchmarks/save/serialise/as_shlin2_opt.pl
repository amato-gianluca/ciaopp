:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(serialise,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    serialise,
    true(true).

:- true pred serialise.

serialise :-
    true((
        mshare([[Codes],[_1]]),
        linear(Codes),
        linear(_1),
        shlin2([([Codes],[Codes]),([_1],[_1])])
    )),
    atom_codes('ABLE WAS I ERE I SAW ELBA',Codes),
    true((
        mshare([[_1]]),
        ground([Codes]),
        linear(_1),
        shlin2([([_1],[_1])])
    )),
    serialise(Codes,_1),
    true((
        mshare([[_1]]),
        ground([Codes]),
        shlin2([([_1],[])])
    )).

:- true pred serialise(L,R)
   : ( mshare([[R]]),
       ground([L]), linear(R), shlin2([([R],[R])]) )
   => ( mshare([[R]]),
        ground([L]), shlin2([([R],[])]) ).

serialise(L,R) :-
    true((
        mshare([[R],[A],[T],[_1]]),
        ground([L]),
        linear(R),
        linear(A),
        linear(T),
        linear(_1),
        shlin2([([R],[R]),([A],[A]),([T],[T]),([_1],[_1])])
    )),
    pairlists(L,R,A),
    true((
        mshare([[R,A],[T],[_1]]),
        ground([L]),
        linear(R),
        linear(A),
        linear(T),
        linear(_1),
        shlin2([([R,A],[R,A]),([T],[T]),([_1],[_1])])
    )),
    arrange(A,T),
    true((
        mshare([[R,A,T],[_1]]),
        ground([L]),
        linear(T),
        linear(_1),
        shlin2([([R,A,T],[T]),([_1],[_1])])
    )),
    numbered(T,1,_1),
    true((
        mshare([[R,A,T]]),
        ground([L,_1]),
        linear(T),
        shlin2([([R,A,T],[T])])
    )).

:- true pred pairlists(_A,_B,_C)
   : ( mshare([[_B],[_C]]),
       ground([_A]), linear(_B), linear(_C), shlin2([([_B],[_B]),([_C],[_C])]) )
   => ( mshare([[_B,_C]]),
        ground([_A]), linear(_B), linear(_C), shlin2([([_B,_C],[_B,_C])]) ).

pairlists([X|L],[Y|R],[pair(X,Y)|A]) :-
    true((
        mshare([[Y],[R],[A]]),
        ground([X,L]),
        linear(Y),
        linear(R),
        linear(A),
        shlin2([([Y],[Y]),([R],[R]),([A],[A])])
    )),
    pairlists(L,R,A),
    true((
        mshare([[Y],[R,A]]),
        ground([X,L]),
        linear(Y),
        linear(R),
        linear(A),
        shlin2([([Y],[Y]),([R,A],[R,A])])
    )).
pairlists([],[],[]).

:- true pred arrange(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_A), linear(_B), shlin2([([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[_A,_B]]),
        linear(_B), shlin2([([_A,_B],[_B])]) ).

arrange([X|L],tree(T1,X,T2)) :-
    true((
        mshare([[X],[L],[T1],[T2],[L1],[L2]]),
        linear(X),
        linear(L),
        linear(T1),
        linear(T2),
        linear(L1),
        linear(L2),
        shlin2([([X],[X]),([L],[L]),([T1],[T1]),([T2],[T2]),([L1],[L1]),([L2],[L2])])
    )),
    split(L,X,L1,L2),
    true((
        mshare([[X],[X,L],[L,L1],[L,L2],[T1],[T2]]),
        linear(X),
        linear(T1),
        linear(T2),
        linear(L1),
        linear(L2),
        shlin2([([X],[X]),([X,L],[X]),([L,L1],[L,L1]),([L,L2],[L,L2]),([T1],[T1]),([T2],[T2])])
    )),
    arrange(L1,T1),
    true((
        mshare([[X],[X,L],[L,T1,L1],[L,L2],[T2]]),
        linear(X),
        linear(T1),
        linear(T2),
        linear(L2),
        shlin2([([X],[X]),([X,L],[X]),([L,T1,L1],[T1]),([L,L2],[L,L2]),([T2],[T2])])
    )),
    arrange(L2,T2),
    true((
        mshare([[X],[X,L],[L,T1,L1],[L,T2,L2]]),
        linear(X),
        linear(T1),
        linear(T2),
        shlin2([([X],[X]),([X,L],[X]),([L,T1,L1],[T1]),([L,T2,L2],[T2])])
    )).
arrange([],void).

:- true pred split(_A,X,L1,L2)
   : ( mshare([[_A],[X],[L1],[L2]]),
       linear(_A), linear(X), linear(L1), linear(L2), shlin2([([_A],[_A]),([X],[X]),([L1],[L1]),([L2],[L2])]) )
   => ( mshare([[_A,X],[_A,L1],[_A,L2],[X]]),
        linear(X), linear(L1), linear(L2), shlin2([([_A,X],[X]),([_A,L1],[_A,L1]),([_A,L2],[_A,L2]),([X],[X])]) ).

split([X|L],X,L1,L2) :-
    !,
    true((
        mshare([[X],[L1],[L2],[L]]),
        linear(X),
        linear(L1),
        linear(L2),
        linear(L),
        shlin2([([X],[X]),([L1],[L1]),([L2],[L2]),([L],[L])])
    )),
    split(L,X,L1,L2),
    true((
        mshare([[X],[X,L],[L1,L],[L2,L]]),
        linear(X),
        linear(L1),
        linear(L2),
        shlin2([([X],[X]),([X,L],[X]),([L1,L],[L1,L]),([L2,L],[L2,L])])
    )).
split([X|L],Y,[X|L1],L2) :-
    true((
        mshare([[Y],[L2],[X],[L],[L1]]),
        linear(Y),
        linear(L2),
        linear(X),
        linear(L),
        linear(L1),
        shlin2([([Y],[Y]),([L2],[L2]),([X],[X]),([L],[L]),([L1],[L1])])
    )),
    before(X,Y),
    !,
    true((
        mshare([[Y],[L2],[X],[L],[L1]]),
        linear(Y),
        linear(L2),
        linear(X),
        linear(L),
        linear(L1),
        shlin2([([Y],[Y]),([L2],[L2]),([X],[X]),([L],[L]),([L1],[L1])])
    )),
    split(L,Y,L1,L2),
    true((
        mshare([[Y],[Y,L],[L2,L],[X],[L,L1]]),
        linear(Y),
        linear(L2),
        linear(X),
        linear(L1),
        shlin2([([Y],[Y]),([Y,L],[Y]),([L2,L],[L2,L]),([X],[X]),([L,L1],[L,L1])])
    )).
split([X|L],Y,L1,[X|L2]) :-
    true((
        mshare([[Y],[L1],[X],[L],[L2]]),
        linear(Y),
        linear(L1),
        linear(X),
        linear(L),
        linear(L2),
        shlin2([([Y],[Y]),([L1],[L1]),([X],[X]),([L],[L]),([L2],[L2])])
    )),
    before(Y,X),
    !,
    true((
        mshare([[Y],[L1],[X],[L],[L2]]),
        linear(Y),
        linear(L1),
        linear(X),
        linear(L),
        linear(L2),
        shlin2([([Y],[Y]),([L1],[L1]),([X],[X]),([L],[L]),([L2],[L2])])
    )),
    split(L,Y,L1,L2),
    true((
        mshare([[Y],[Y,L],[L1,L],[X],[L,L2]]),
        linear(Y),
        linear(L1),
        linear(X),
        linear(L2),
        shlin2([([Y],[Y]),([Y,L],[Y]),([L1,L],[L1,L]),([X],[X]),([L,L2],[L,L2])])
    )).
split([],_1,[],[]).

:- true pred before(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_A), linear(_B), shlin2([([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[_A],[_B]]),
        linear(_A), linear(_B), shlin2([([_A],[_A]),([_B],[_B])]) ).

before(pair(X1,_1),pair(X2,_2)) :-
    true((
        mshare([[X1],[_1],[X2],[_2]]),
        linear(X1),
        linear(_1),
        linear(X2),
        linear(_2),
        shlin2([([X1],[X1]),([_1],[_1]),([X2],[X2]),([_2],[_2])])
    )),
    X1<X2,
    true((
        mshare([[_1],[_2]]),
        ground([X1,X2]),
        linear(_1),
        linear(_2),
        shlin2([([_1],[_1]),([_2],[_2])])
    )).

:- true pred numbered(_A,N0,N)
   : ( (N0=1),
       mshare([[_A],[N]]),
       linear(_A), linear(N), shlin2([([_A],[_A]),([N],[N])]) )
   => ( mshare([[_A]]),
        ground([N]), linear(_A), shlin2([([_A],[_A])]) ).

:- true pred numbered(_A,N0,N)
   : ( mshare([[_A],[N]]),
       ground([N0]), linear(_A), linear(N), shlin2([([_A],[_A]),([N],[N])]) )
   => ( mshare([[_A]]),
        ground([N0,N]), linear(_A), shlin2([([_A],[_A])]) ).

numbered(tree(T1,pair(_1,N1),T2),N0,N) :-
    true((
        mshare([[N],[T1],[T2],[_1],[N1],[N2]]),
        ground([N0]),
        linear(N),
        linear(T1),
        linear(T2),
        linear(_1),
        linear(N1),
        linear(N2),
        shlin2([([N],[N]),([T1],[T1]),([T2],[T2]),([_1],[_1]),([N1],[N1]),([N2],[N2])])
    )),
    numbered(T1,N0,N1),
    true((
        mshare([[N],[T1],[T2],[_1],[N2]]),
        ground([N0,N1]),
        linear(N),
        linear(T1),
        linear(T2),
        linear(_1),
        linear(N2),
        shlin2([([N],[N]),([T1],[T1]),([T2],[T2]),([_1],[_1]),([N2],[N2])])
    )),
    N2 is N1+1,
    true((
        mshare([[N],[T1],[T2],[_1]]),
        ground([N0,N1,N2]),
        linear(N),
        linear(T1),
        linear(T2),
        linear(_1),
        shlin2([([N],[N]),([T1],[T1]),([T2],[T2]),([_1],[_1])])
    )),
    numbered(T2,N2,N),
    true((
        mshare([[T1],[T2],[_1]]),
        ground([N0,N,N1,N2]),
        linear(T1),
        linear(T2),
        linear(_1),
        shlin2([([T1],[T1]),([T2],[T2]),([_1],[_1])])
    )).
numbered(void,N,N).


