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
        linear(_1)
    )),
    atom_codes('ABLE WAS I ERE I SAW ELBA',Codes),
    true((
        mshare([[_1]]),
        ground([Codes]),
        linear(_1)
    )),
    serialise(Codes,_1),
    true((
        mshare([[_1]]),
        ground([Codes])
    )).

:- true pred serialise(L,R)
   : ( mshare([[R]]),
       ground([L]), linear(R) )
   => ( mshare([[R]]),
        ground([L]) ).

serialise(L,R) :-
    true((
        mshare([[R],[A],[T],[_1]]),
        ground([L]),
        linear(R),
        linear(A),
        linear(T),
        linear(_1)
    )),
    pairlists(L,R,A),
    true((
        mshare([[R,A],[T],[_1]]),
        ground([L])
    )),
    arrange(A,T),
    true((
        mshare([[R,A,T],[_1]]),
        ground([L])
    )),
    numbered(T,1,_1),
    true((
        mshare([[R,A,T]]),
        ground([L,_1])
    )).

:- true pred pairlists(_A,_B,_C)
   : ( mshare([[_B],[_C]]),
       ground([_A]), linear(_B), linear(_C) )
   => ( mshare([[_B,_C]]),
        ground([_A]) ).

pairlists([X|L],[Y|R],[pair(X,Y)|A]) :-
    true((
        mshare([[Y],[R],[A]]),
        ground([X,L]),
        linear(Y),
        linear(R),
        linear(A)
    )),
    pairlists(L,R,A),
    true((
        mshare([[Y],[R,A]]),
        ground([X,L])
    )).
pairlists([],[],[]).

:- true pred arrange(_A,_B)
   : mshare([[_A],[_B]])
   => mshare([[_A,_B]]).

:- true pred arrange(_A,_B)
   : mshare([[_A],[_A,_B],[_B]])
   => mshare([[_A,_B]]).

arrange([X|L],tree(T1,X,T2)) :-
    true((mshare([[X],[X,L],[X,L,T1],[X,L,T1,T2],[X,L,T2],[X,T1],[X,T1,T2],[X,T2],[L],[L,T1],[L,T1,T2],[L,T2],[T1],[T1,T2],[T2],[L1],[L2]]),linear(L1),linear(L2);mshare([[X],[X,L],[X,L,T1],[X,L,T1,T2],[X,L,T2],[X,T1],[X,T1,T2],[X,T2],[L],[T1],[T1,T2],[T2],[L1],[L2]]),linear(L1),linear(L2))),
    split(L,X,L1,L2),
    true((mshare([[X],[X,L],[X,L,T1],[X,L,T1,T2],[X,L,T1,T2,L1],[X,L,T1,T2,L1,L2],[X,L,T1,T2,L2],[X,L,T1,L1],[X,L,T1,L1,L2],[X,L,T1,L2],[X,L,T2],[X,L,T2,L1],[X,L,T2,L1,L2],[X,L,T2,L2],[X,L,L1],[X,L,L1,L2],[X,L,L2],[X,T1],[X,T1,T2],[X,T2],[L,T1,T2,L1],[L,T1,T2,L1,L2],[L,T1,T2,L2],[L,T1,L1],[L,T1,L1,L2],[L,T1,L2],[L,T2,L1],[L,T2,L1,L2],[L,T2,L2],[L,L1],[L,L1,L2],[L,L2],[T1],[T1,T2],[T2]]);mshare([[X],[X,L],[X,L,T1],[X,L,T1,T2],[X,L,T1,T2,L1],[X,L,T1,T2,L1,L2],[X,L,T1,T2,L2],[X,L,T1,L1],[X,L,T1,L1,L2],[X,L,T1,L2],[X,L,T2],[X,L,T2,L1],[X,L,T2,L1,L2],[X,L,T2,L2],[X,L,L1],[X,L,L1,L2],[X,L,L2],[X,T1],[X,T1,T2],[X,T2],[L,L1],[L,L1,L2],[L,L2],[T1],[T1,T2],[T2]]))),
    arrange(L1,T1),
    true((mshare([[X],[X,L],[X,L,T1,T2,L1],[X,L,T1,T2,L1,L2],[X,L,T1,L1],[X,L,T1,L1,L2],[X,L,T2],[X,L,T2,L2],[X,L,L2],[X,T2],[L,T1,T2,L1],[L,T1,T2,L1,L2],[L,T1,L1],[L,T1,L1,L2],[L,T2,L2],[L,L2],[T2]]);mshare([[X],[X,L],[X,L,T1,T2,L1],[X,L,T1,T2,L1,L2],[X,L,T1,L1],[X,L,T1,L1,L2],[X,L,T2],[X,L,T2,L2],[X,L,L2],[X,T2],[L,T1,T2,L1],[L,T1,T2,L1,L2],[L,T1,L1],[L,T1,L1,L2],[L,L2],[T2]]))),
    arrange(L2,T2),
    true(mshare([[X],[X,L],[X,L,T1,T2,L1,L2],[X,L,T1,L1],[X,L,T2,L2],[L,T1,T2,L1,L2],[L,T1,L1],[L,T2,L2]])).
arrange([],void).

:- true pred split(_A,X,L1,L2)
   : ( mshare([[_A],[_A,X],[X],[L1],[L2]]),
       linear(L1), linear(L2) )
   => mshare([[_A,X],[_A,X,L1],[_A,X,L1,L2],[_A,X,L2],[_A,L1],[_A,L1,L2],[_A,L2],[X]]).

:- true pred split(_A,X,L1,L2)
   : mshare([[_A],[_A,X],[X],[L1],[L2]])
   => mshare([[_A,X],[_A,X,L1],[_A,X,L1,L2],[_A,X,L2],[_A,L1],[_A,L1,L2],[_A,L2],[X]]).

:- true pred split(_A,X,L1,L2)
   : mshare([[_A],[_A,X],[_A,X,L2],[_A,L2],[X],[X,L2],[L1],[L2]])
   => mshare([[_A,X],[_A,X,L1],[_A,X,L1,L2],[_A,X,L2],[_A,L1],[_A,L1,L2],[_A,L2],[X]]).

:- true pred split(_A,X,L1,L2)
   : mshare([[_A],[_A,X],[_A,X,L1],[_A,L1],[X],[X,L1],[L1],[L2]])
   => mshare([[_A,X],[_A,X,L1],[_A,X,L1,L2],[_A,X,L2],[_A,L1],[_A,L1,L2],[_A,L2],[X]]).

:- true pred split(_A,X,L1,L2)
   : mshare([[_A],[_A,X],[_A,X,L1],[_A,X,L1,L2],[_A,X,L2],[_A,L1],[_A,L1,L2],[_A,L2],[X],[X,L1],[X,L1,L2],[X,L2],[L1],[L1,L2],[L2]])
   => mshare([[_A,X],[_A,X,L1],[_A,X,L1,L2],[_A,X,L2],[_A,L1],[_A,L1,L2],[_A,L2],[X]]).

split([X|L],X,L1,L2) :-
    !,
    true((mshare([[X],[X,L1],[X,L1,L2],[X,L1,L2,L],[X,L1,L],[X,L2],[X,L2,L],[X,L],[L1],[L1,L2],[L1,L2,L],[L1,L],[L2],[L2,L],[L]]);mshare([[X],[X,L1],[X,L1,L],[X,L],[L1],[L1,L],[L2],[L]]);mshare([[X],[X,L2],[X,L2,L],[X,L],[L1],[L2],[L2,L],[L]]);mshare([[X],[X,L],[L1],[L2],[L]]);mshare([[X],[X,L],[L1],[L2],[L]]),linear(L1),linear(L2))),
    split(L,X,L1,L2),
    true(mshare([[X],[X,L1,L2,L],[X,L1,L],[X,L2,L],[X,L],[L1,L2,L],[L1,L],[L2,L]])).
split([X|L],Y,[X|L1],L2) :-
    true((mshare([[Y],[Y,L2],[Y,L2,X],[Y,L2,X,L],[Y,L2,X,L,L1],[Y,L2,X,L1],[Y,L2,L],[Y,L2,L,L1],[Y,L2,L1],[Y,X],[Y,X,L],[Y,X,L,L1],[Y,X,L1],[Y,L],[Y,L,L1],[Y,L1],[L2],[L2,X],[L2,X,L],[L2,X,L,L1],[L2,X,L1],[L2,L],[L2,L,L1],[L2,L1],[X],[X,L],[X,L,L1],[X,L1],[L],[L,L1],[L1]]);mshare([[Y],[Y,L2],[Y,L2,X],[Y,L2,X,L],[Y,L2,X,L,L1],[Y,L2,X,L1],[Y,L2,L],[Y,X],[Y,X,L],[Y,X,L,L1],[Y,X,L1],[Y,L],[L2],[L2,X],[L2,X,L],[L2,X,L,L1],[L2,X,L1],[L2,L],[X],[X,L],[X,L,L1],[X,L1],[L],[L1]]);mshare([[Y],[Y,X],[Y,X,L],[Y,X,L,L1],[Y,X,L1],[Y,L],[Y,L,L1],[Y,L1],[L2],[X],[X,L],[X,L,L1],[X,L1],[L],[L,L1],[L1]]);mshare([[Y],[Y,X],[Y,X,L],[Y,X,L,L1],[Y,X,L1],[Y,L],[L2],[X],[X,L],[X,L,L1],[X,L1],[L],[L1]]);mshare([[Y],[Y,X],[Y,X,L],[Y,L],[L2],[X],[X,L],[L],[L1]]),linear(L2),linear(L1))),
    before(X,Y),
    !,
    true((mshare([[Y],[Y,L2],[Y,L2,X],[Y,L2,X,L],[Y,L2,X,L,L1],[Y,L2,X,L1],[Y,L2,L],[Y,L2,L,L1],[Y,L2,L1],[Y,X],[Y,X,L],[Y,X,L,L1],[Y,X,L1],[Y,L],[Y,L,L1],[Y,L1],[L2],[L2,X],[L2,X,L],[L2,X,L,L1],[L2,X,L1],[L2,L],[L2,L,L1],[L2,L1],[X],[X,L],[X,L,L1],[X,L1],[L],[L,L1],[L1]]);mshare([[Y],[Y,L2],[Y,L2,X],[Y,L2,X,L],[Y,L2,X,L,L1],[Y,L2,X,L1],[Y,L2,L],[Y,X],[Y,X,L],[Y,X,L,L1],[Y,X,L1],[Y,L],[L2],[L2,X],[L2,X,L],[L2,X,L,L1],[L2,X,L1],[L2,L],[X],[X,L],[X,L,L1],[X,L1],[L],[L1]]);mshare([[Y],[Y,X],[Y,X,L],[Y,X,L,L1],[Y,X,L1],[Y,L],[Y,L,L1],[Y,L1],[L2],[X],[X,L],[X,L,L1],[X,L1],[L],[L,L1],[L1]]);mshare([[Y],[Y,X],[Y,X,L],[Y,X,L,L1],[Y,X,L1],[Y,L],[L2],[X],[X,L],[X,L,L1],[X,L1],[L],[L1]]);mshare([[Y],[Y,X],[Y,X,L],[Y,L],[L2],[X],[X,L],[L],[L1]]))),
    split(L,Y,L1,L2),
    true(mshare([[Y],[Y,L2,X,L],[Y,L2,X,L,L1],[Y,L2,L],[Y,L2,L,L1],[Y,X],[Y,X,L],[Y,X,L,L1],[Y,L],[Y,L,L1],[L2,X,L],[L2,X,L,L1],[L2,L],[L2,L,L1],[X],[X,L,L1],[L,L1]])).
split([X|L],Y,L1,[X|L2]) :-
    true((mshare([[Y],[Y,L1],[Y,L1,X],[Y,L1,X,L],[Y,L1,X,L,L2],[Y,L1,X,L2],[Y,L1,L],[Y,L1,L,L2],[Y,L1,L2],[Y,X],[Y,X,L],[Y,X,L,L2],[Y,X,L2],[Y,L],[Y,L,L2],[Y,L2],[L1],[L1,X],[L1,X,L],[L1,X,L,L2],[L1,X,L2],[L1,L],[L1,L,L2],[L1,L2],[X],[X,L],[X,L,L2],[X,L2],[L],[L,L2],[L2]]);mshare([[Y],[Y,L1],[Y,L1,X],[Y,L1,X,L],[Y,L1,X,L,L2],[Y,L1,X,L2],[Y,L1,L],[Y,X],[Y,X,L],[Y,X,L,L2],[Y,X,L2],[Y,L],[L1],[L1,X],[L1,X,L],[L1,X,L,L2],[L1,X,L2],[L1,L],[X],[X,L],[X,L,L2],[X,L2],[L],[L2]]);mshare([[Y],[Y,X],[Y,X,L],[Y,X,L,L2],[Y,X,L2],[Y,L],[Y,L,L2],[Y,L2],[L1],[X],[X,L],[X,L,L2],[X,L2],[L],[L,L2],[L2]]);mshare([[Y],[Y,X],[Y,X,L],[Y,X,L,L2],[Y,X,L2],[Y,L],[L1],[X],[X,L],[X,L,L2],[X,L2],[L],[L2]]);mshare([[Y],[Y,X],[Y,X,L],[Y,L],[L1],[X],[X,L],[L],[L2]]),linear(L1),linear(L2))),
    before(Y,X),
    !,
    true((mshare([[Y],[Y,L1],[Y,L1,X],[Y,L1,X,L],[Y,L1,X,L,L2],[Y,L1,X,L2],[Y,L1,L],[Y,L1,L,L2],[Y,L1,L2],[Y,X],[Y,X,L],[Y,X,L,L2],[Y,X,L2],[Y,L],[Y,L,L2],[Y,L2],[L1],[L1,X],[L1,X,L],[L1,X,L,L2],[L1,X,L2],[L1,L],[L1,L,L2],[L1,L2],[X],[X,L],[X,L,L2],[X,L2],[L],[L,L2],[L2]]);mshare([[Y],[Y,L1],[Y,L1,X],[Y,L1,X,L],[Y,L1,X,L,L2],[Y,L1,X,L2],[Y,L1,L],[Y,X],[Y,X,L],[Y,X,L,L2],[Y,X,L2],[Y,L],[L1],[L1,X],[L1,X,L],[L1,X,L,L2],[L1,X,L2],[L1,L],[X],[X,L],[X,L,L2],[X,L2],[L],[L2]]);mshare([[Y],[Y,X],[Y,X,L],[Y,X,L,L2],[Y,X,L2],[Y,L],[Y,L,L2],[Y,L2],[L1],[X],[X,L],[X,L,L2],[X,L2],[L],[L,L2],[L2]]);mshare([[Y],[Y,X],[Y,X,L],[Y,X,L,L2],[Y,X,L2],[Y,L],[L1],[X],[X,L],[X,L,L2],[X,L2],[L],[L2]]);mshare([[Y],[Y,X],[Y,X,L],[Y,L],[L1],[X],[X,L],[L],[L2]]))),
    split(L,Y,L1,L2),
    true(mshare([[Y],[Y,L1,X,L],[Y,L1,X,L,L2],[Y,L1,L],[Y,L1,L,L2],[Y,X],[Y,X,L],[Y,X,L,L2],[Y,L],[Y,L,L2],[L1,X,L],[L1,X,L,L2],[L1,L],[L1,L,L2],[X],[X,L,L2],[L,L2]])).
split([],_1,[],[]).

:- true pred before(_A,_B)
   : mshare([[_A],[_A,_B],[_B]])
   => mshare([[_A],[_A,_B],[_B]]).

before(pair(X1,_1),pair(X2,_2)) :-
    true(mshare([[X1],[X1,_1],[X1,_1,X2],[X1,_1,X2,_2],[X1,_1,_2],[X1,X2],[X1,X2,_2],[X1,_2],[_1],[_1,X2],[_1,X2,_2],[_1,_2],[X2],[X2,_2],[_2]])),
    X1<X2,
    true((
        mshare([[_1],[_1,_2],[_2]]),
        ground([X1,X2])
    )).

:- true pred numbered(_A,N0,N)
   : ( (N0=1),
       mshare([[_A],[N]]) )
   => ( mshare([[_A]]),
        ground([N]) ).

:- true pred numbered(_A,N0,N)
   : ( mshare([[_A],[N]]),
       ground([N0]) )
   => ( mshare([[_A]]),
        ground([N0,N]) ).

:- true pred numbered(_A,N0,N)
   : ( mshare([[_A],[_A,N],[N]]),
       ground([N0]) )
   => ( mshare([[_A]]),
        ground([N0,N]) ).

numbered(tree(T1,pair(_1,N1),T2),N0,N) :-
    true((mshare([[N],[N,T1],[N,T1,T2],[N,T1,T2,_1],[N,T1,T2,_1,N1],[N,T1,T2,N1],[N,T1,_1],[N,T1,_1,N1],[N,T1,N1],[N,T2],[N,T2,_1],[N,T2,_1,N1],[N,T2,N1],[N,_1],[N,_1,N1],[N,N1],[T1],[T1,T2],[T1,T2,_1],[T1,T2,_1,N1],[T1,T2,N1],[T1,_1],[T1,_1,N1],[T1,N1],[T2],[T2,_1],[T2,_1,N1],[T2,N1],[_1],[_1,N1],[N1],[N2]]),ground([N0]),linear(N2);mshare([[N],[T1],[T1,T2],[T1,T2,_1],[T1,T2,_1,N1],[T1,T2,N1],[T1,_1],[T1,_1,N1],[T1,N1],[T2],[T2,_1],[T2,_1,N1],[T2,N1],[_1],[_1,N1],[N1],[N2]]),ground([N0]),linear(N2))),
    numbered(T1,N0,N1),
    true((mshare([[N],[N,T1],[N,T1,T2],[N,T1,T2,_1],[N,T1,_1],[N,T2],[N,T2,_1],[N,_1],[T1],[T1,T2],[T1,T2,_1],[T1,_1],[T2],[T2,_1],[_1],[N2]]),ground([N0,N1]);mshare([[N],[T1],[T1,T2],[T1,T2,_1],[T1,_1],[T2],[T2,_1],[_1],[N2]]),ground([N0,N1]))),
    N2 is N1+1,
    true((mshare([[N],[N,T1],[N,T1,T2],[N,T1,T2,_1],[N,T1,_1],[N,T2],[N,T2,_1],[N,_1],[T1],[T1,T2],[T1,T2,_1],[T1,_1],[T2],[T2,_1],[_1]]),ground([N0,N1,N2]);mshare([[N],[T1],[T1,T2],[T1,T2,_1],[T1,_1],[T2],[T2,_1],[_1]]),ground([N0,N1,N2]))),
    numbered(T2,N2,N),
    true((
        mshare([[T1],[T1,T2],[T1,T2,_1],[T1,_1],[T2],[T2,_1],[_1]]),
        ground([N0,N,N1,N2])
    )).
numbered(void,N,N).

