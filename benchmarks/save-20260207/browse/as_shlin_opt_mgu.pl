:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(browse,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true((
        mshare([[Symbols],[RSymbols],[SA],[B],[SB],[_1],[_2],[_3],[_4],[_5],[_6]]),
        linear(Symbols),
        linear(RSymbols),
        linear(SA),
        linear(B),
        linear(SB),
        linear(_1),
        linear(_2),
        linear(_3),
        linear(_4),
        linear(_5),
        linear(_6)
    )),
    init(100,10,4,[[a,a,a,b,b,b,b,a,a,a,a,a,b,b,a,a,a],[a,a,b,b,b,b,a,a,[a,a],[b,b]],[a,a,a,b,[b,a],b,a,b,a]],Symbols),
    true(mshare([[Symbols],[RSymbols],[SA],[B],[SB],[_1],[_2],[_3],[_4],[_5],[_6]])),
    randomize(Symbols,RSymbols,21),
    !,
    true(mshare([[Symbols,RSymbols],[SA],[B],[SB],[_1],[_2],[_3],[_4],[_5],[_6]])),
    investigate(RSymbols,[[star(SA),B,star(SB),B,a,star(SA),a,star(SB),star(SA)],[star(SA),star(SB),star(SB),star(SA),[star(SA)],[star(SB)]],[_1,_2,star(_3),[b,a],star(_4),_5,_6]]),
    true(mshare([[Symbols,RSymbols],[SA],[SA,B],[SA,B,SB],[SA,B,SB,_1],[SA,B,SB,_1,_2],[SA,B,SB,_1,_2,_3],[SA,B,SB,_1,_2,_3,_4],[SA,B,SB,_1,_2,_3,_4,_5],[SA,B,SB,_1,_2,_3,_4,_5,_6],[SA,B,SB,_1,_2,_3,_4,_6],[SA,B,SB,_1,_2,_3,_5],[SA,B,SB,_1,_2,_3,_5,_6],[SA,B,SB,_1,_2,_3,_6],[SA,B,SB,_1,_2,_4],[SA,B,SB,_1,_2,_4,_5],[SA,B,SB,_1,_2,_4,_5,_6],[SA,B,SB,_1,_2,_4,_6],[SA,B,SB,_1,_2,_5],[SA,B,SB,_1,_2,_5,_6],[SA,B,SB,_1,_2,_6],[SA,B,SB,_1,_3],[SA,B,SB,_1,_3,_4],[SA,B,SB,_1,_3,_4,_5],[SA,B,SB,_1,_3,_4,_5,_6],[SA,B,SB,_1,_3,_4,_6],[SA,B,SB,_1,_3,_5],[SA,B,SB,_1,_3,_5,_6],[SA,B,SB,_1,_3,_6],[SA,B,SB,_1,_4],[SA,B,SB,_1,_4,_5],[SA,B,SB,_1,_4,_5,_6],[SA,B,SB,_1,_4,_6],[SA,B,SB,_1,_5],[SA,B,SB,_1,_5,_6],[SA,B,SB,_1,_6],[SA,B,SB,_2],[SA,B,SB,_2,_3],[SA,B,SB,_2,_3,_4],[SA,B,SB,_2,_3,_4,_5],[SA,B,SB,_2,_3,_4,_5,_6],[SA,B,SB,_2,_3,_4,_6],[SA,B,SB,_2,_3,_5],[SA,B,SB,_2,_3,_5,_6],[SA,B,SB,_2,_3,_6],[SA,B,SB,_2,_4],[SA,B,SB,_2,_4,_5],[SA,B,SB,_2,_4,_5,_6],[SA,B,SB,_2,_4,_6],[SA,B,SB,_2,_5],[SA,B,SB,_2,_5,_6],[SA,B,SB,_2,_6],[SA,B,SB,_3],[SA,B,SB,_3,_4],[SA,B,SB,_3,_4,_5],[SA,B,SB,_3,_4,_5,_6],[SA,B,SB,_3,_4,_6],[SA,B,SB,_3,_5],[SA,B,SB,_3,_5,_6],[SA,B,SB,_3,_6],[SA,B,SB,_4],[SA,B,SB,_4,_5],[SA,B,SB,_4,_5,_6],[SA,B,SB,_4,_6],[SA,B,SB,_5],[SA,B,SB,_5,_6],[SA,B,SB,_6],[SA,B,_1],[SA,B,_1,_2],[SA,B,_1,_2,_3],[SA,B,_1,_2,_3,_4],[SA,B,_1,_2,_3,_4,_5],[SA,B,_1,_2,_3,_4,_5,_6],[SA,B,_1,_2,_3,_4,_6],[SA,B,_1,_2,_3,_5],[SA,B,_1,_2,_3,_5,_6],[SA,B,_1,_2,_3,_6],[SA,B,_1,_2,_4],[SA,B,_1,_2,_4,_5],[SA,B,_1,_2,_4,_5,_6],[SA,B,_1,_2,_4,_6],[SA,B,_1,_2,_5],[SA,B,_1,_2,_5,_6],[SA,B,_1,_2,_6],[SA,B,_1,_3],[SA,B,_1,_3,_4],[SA,B,_1,_3,_4,_5],[SA,B,_1,_3,_4,_5,_6],[SA,B,_1,_3,_4,_6],[SA,B,_1,_3,_5],[SA,B,_1,_3,_5,_6],[SA,B,_1,_3,_6],[SA,B,_1,_4],[SA,B,_1,_4,_5],[SA,B,_1,_4,_5,_6],[SA,B,_1,_4,_6],[SA,B,_1,_5],[SA,B,_1,_5,_6],[SA,B,_1,_6],[SA,B,_2],[SA,B,_2,_3],[SA,B,_2,_3,_4],[SA,B,_2,_3,_4,_5],[SA,B,_2,_3,_4,_5,_6],[SA,B,_2,_3,_4,_6],[SA,B,_2,_3,_5],[SA,B,_2,_3,_5,_6],[SA,B,_2,_3,_6],[SA,B,_2,_4],[SA,B,_2,_4,_5],[SA,B,_2,_4,_5,_6],[SA,B,_2,_4,_6],[SA,B,_2,_5],[SA,B,_2,_5,_6],[SA,B,_2,_6],[SA,B,_3],[SA,B,_3,_4],[SA,B,_3,_4,_5],[SA,B,_3,_4,_5,_6],[SA,B,_3,_4,_6],[SA,B,_3,_5],[SA,B,_3,_5,_6],[SA,B,_3,_6],[SA,B,_4],[SA,B,_4,_5],[SA,B,_4,_5,_6],[SA,B,_4,_6],[SA,B,_5],[SA,B,_5,_6],[SA,B,_6],[SA,SB],[SA,SB,_1],[SA,SB,_1,_2],[SA,SB,_1,_2,_3],[SA,SB,_1,_2,_3,_4],[SA,SB,_1,_2,_3,_4,_5],[SA,SB,_1,_2,_3,_4,_5,_6],[SA,SB,_1,_2,_3,_4,_6],[SA,SB,_1,_2,_3,_5],[SA,SB,_1,_2,_3,_5,_6],[SA,SB,_1,_2,_3,_6],[SA,SB,_1,_2,_4],[SA,SB,_1,_2,_4,_5],[SA,SB,_1,_2,_4,_5,_6],[SA,SB,_1,_2,_4,_6],[SA,SB,_1,_2,_5],[SA,SB,_1,_2,_5,_6],[SA,SB,_1,_2,_6],[SA,SB,_1,_3],[SA,SB,_1,_3,_4],[SA,SB,_1,_3,_4,_5],[SA,SB,_1,_3,_4,_5,_6],[SA,SB,_1,_3,_4,_6],[SA,SB,_1,_3,_5],[SA,SB,_1,_3,_5,_6],[SA,SB,_1,_3,_6],[SA,SB,_1,_4],[SA,SB,_1,_4,_5],[SA,SB,_1,_4,_5,_6],[SA,SB,_1,_4,_6],[SA,SB,_1,_5],[SA,SB,_1,_5,_6],[SA,SB,_1,_6],[SA,SB,_2],[SA,SB,_2,_3],[SA,SB,_2,_3,_4],[SA,SB,_2,_3,_4,_5],[SA,SB,_2,_3,_4,_5,_6],[SA,SB,_2,_3,_4,_6],[SA,SB,_2,_3,_5],[SA,SB,_2,_3,_5,_6],[SA,SB,_2,_3,_6],[SA,SB,_2,_4],[SA,SB,_2,_4,_5],[SA,SB,_2,_4,_5,_6],[SA,SB,_2,_4,_6],[SA,SB,_2,_5],[SA,SB,_2,_5,_6],[SA,SB,_2,_6],[SA,SB,_3],[SA,SB,_3,_4],[SA,SB,_3,_4,_5],[SA,SB,_3,_4,_5,_6],[SA,SB,_3,_4,_6],[SA,SB,_3,_5],[SA,SB,_3,_5,_6],[SA,SB,_3,_6],[SA,SB,_4],[SA,SB,_4,_5],[SA,SB,_4,_5,_6],[SA,SB,_4,_6],[SA,SB,_5],[SA,SB,_5,_6],[SA,SB,_6],[SA,_1],[SA,_1,_2],[SA,_1,_2,_3],[SA,_1,_2,_3,_4],[SA,_1,_2,_3,_4,_5],[SA,_1,_2,_3,_4,_5,_6],[SA,_1,_2,_3,_4,_6],[SA,_1,_2,_3,_5],[SA,_1,_2,_3,_5,_6],[SA,_1,_2,_3,_6],[SA,_1,_2,_4],[SA,_1,_2,_4,_5],[SA,_1,_2,_4,_5,_6],[SA,_1,_2,_4,_6],[SA,_1,_2,_5],[SA,_1,_2,_5,_6],[SA,_1,_2,_6],[SA,_1,_3],[SA,_1,_3,_4],[SA,_1,_3,_4,_5],[SA,_1,_3,_4,_5,_6],[SA,_1,_3,_4,_6],[SA,_1,_3,_5],[SA,_1,_3,_5,_6],[SA,_1,_3,_6],[SA,_1,_4],[SA,_1,_4,_5],[SA,_1,_4,_5,_6],[SA,_1,_4,_6],[SA,_1,_5],[SA,_1,_5,_6],[SA,_1,_6],[SA,_2],[SA,_2,_3],[SA,_2,_3,_4],[SA,_2,_3,_4,_5],[SA,_2,_3,_4,_5,_6],[SA,_2,_3,_4,_6],[SA,_2,_3,_5],[SA,_2,_3,_5,_6],[SA,_2,_3,_6],[SA,_2,_4],[SA,_2,_4,_5],[SA,_2,_4,_5,_6],[SA,_2,_4,_6],[SA,_2,_5],[SA,_2,_5,_6],[SA,_2,_6],[SA,_3],[SA,_3,_4],[SA,_3,_4,_5],[SA,_3,_4,_5,_6],[SA,_3,_4,_6],[SA,_3,_5],[SA,_3,_5,_6],[SA,_3,_6],[SA,_4],[SA,_4,_5],[SA,_4,_5,_6],[SA,_4,_6],[SA,_5],[SA,_5,_6],[SA,_6],[B],[B,SB],[B,SB,_1],[B,SB,_1,_2],[B,SB,_1,_2,_3],[B,SB,_1,_2,_3,_4],[B,SB,_1,_2,_3,_4,_5],[B,SB,_1,_2,_3,_4,_5,_6],[B,SB,_1,_2,_3,_4,_6],[B,SB,_1,_2,_3,_5],[B,SB,_1,_2,_3,_5,_6],[B,SB,_1,_2,_3,_6],[B,SB,_1,_2,_4],[B,SB,_1,_2,_4,_5],[B,SB,_1,_2,_4,_5,_6],[B,SB,_1,_2,_4,_6],[B,SB,_1,_2,_5],[B,SB,_1,_2,_5,_6],[B,SB,_1,_2,_6],[B,SB,_1,_3],[B,SB,_1,_3,_4],[B,SB,_1,_3,_4,_5],[B,SB,_1,_3,_4,_5,_6],[B,SB,_1,_3,_4,_6],[B,SB,_1,_3,_5],[B,SB,_1,_3,_5,_6],[B,SB,_1,_3,_6],[B,SB,_1,_4],[B,SB,_1,_4,_5],[B,SB,_1,_4,_5,_6],[B,SB,_1,_4,_6],[B,SB,_1,_5],[B,SB,_1,_5,_6],[B,SB,_1,_6],[B,SB,_2],[B,SB,_2,_3],[B,SB,_2,_3,_4],[B,SB,_2,_3,_4,_5],[B,SB,_2,_3,_4,_5,_6],[B,SB,_2,_3,_4,_6],[B,SB,_2,_3,_5],[B,SB,_2,_3,_5,_6],[B,SB,_2,_3,_6],[B,SB,_2,_4],[B,SB,_2,_4,_5],[B,SB,_2,_4,_5,_6],[B,SB,_2,_4,_6],[B,SB,_2,_5],[B,SB,_2,_5,_6],[B,SB,_2,_6],[B,SB,_3],[B,SB,_3,_4],[B,SB,_3,_4,_5],[B,SB,_3,_4,_5,_6],[B,SB,_3,_4,_6],[B,SB,_3,_5],[B,SB,_3,_5,_6],[B,SB,_3,_6],[B,SB,_4],[B,SB,_4,_5],[B,SB,_4,_5,_6],[B,SB,_4,_6],[B,SB,_5],[B,SB,_5,_6],[B,SB,_6],[B,_1],[B,_1,_2],[B,_1,_2,_3],[B,_1,_2,_3,_4],[B,_1,_2,_3,_4,_5],[B,_1,_2,_3,_4,_5,_6],[B,_1,_2,_3,_4,_6],[B,_1,_2,_3,_5],[B,_1,_2,_3,_5,_6],[B,_1,_2,_3,_6],[B,_1,_2,_4],[B,_1,_2,_4,_5],[B,_1,_2,_4,_5,_6],[B,_1,_2,_4,_6],[B,_1,_2,_5],[B,_1,_2,_5,_6],[B,_1,_2,_6],[B,_1,_3],[B,_1,_3,_4],[B,_1,_3,_4,_5],[B,_1,_3,_4,_5,_6],[B,_1,_3,_4,_6],[B,_1,_3,_5],[B,_1,_3,_5,_6],[B,_1,_3,_6],[B,_1,_4],[B,_1,_4,_5],[B,_1,_4,_5,_6],[B,_1,_4,_6],[B,_1,_5],[B,_1,_5,_6],[B,_1,_6],[B,_2],[B,_2,_3],[B,_2,_3,_4],[B,_2,_3,_4,_5],[B,_2,_3,_4,_5,_6],[B,_2,_3,_4,_6],[B,_2,_3,_5],[B,_2,_3,_5,_6],[B,_2,_3,_6],[B,_2,_4],[B,_2,_4,_5],[B,_2,_4,_5,_6],[B,_2,_4,_6],[B,_2,_5],[B,_2,_5,_6],[B,_2,_6],[B,_3],[B,_3,_4],[B,_3,_4,_5],[B,_3,_4,_5,_6],[B,_3,_4,_6],[B,_3,_5],[B,_3,_5,_6],[B,_3,_6],[B,_4],[B,_4,_5],[B,_4,_5,_6],[B,_4,_6],[B,_5],[B,_5,_6],[B,_6],[SB],[SB,_1],[SB,_1,_2],[SB,_1,_2,_3],[SB,_1,_2,_3,_4],[SB,_1,_2,_3,_4,_5],[SB,_1,_2,_3,_4,_5,_6],[SB,_1,_2,_3,_4,_6],[SB,_1,_2,_3,_5],[SB,_1,_2,_3,_5,_6],[SB,_1,_2,_3,_6],[SB,_1,_2,_4],[SB,_1,_2,_4,_5],[SB,_1,_2,_4,_5,_6],[SB,_1,_2,_4,_6],[SB,_1,_2,_5],[SB,_1,_2,_5,_6],[SB,_1,_2,_6],[SB,_1,_3],[SB,_1,_3,_4],[SB,_1,_3,_4,_5],[SB,_1,_3,_4,_5,_6],[SB,_1,_3,_4,_6],[SB,_1,_3,_5],[SB,_1,_3,_5,_6],[SB,_1,_3,_6],[SB,_1,_4],[SB,_1,_4,_5],[SB,_1,_4,_5,_6],[SB,_1,_4,_6],[SB,_1,_5],[SB,_1,_5,_6],[SB,_1,_6],[SB,_2],[SB,_2,_3],[SB,_2,_3,_4],[SB,_2,_3,_4,_5],[SB,_2,_3,_4,_5,_6],[SB,_2,_3,_4,_6],[SB,_2,_3,_5],[SB,_2,_3,_5,_6],[SB,_2,_3,_6],[SB,_2,_4],[SB,_2,_4,_5],[SB,_2,_4,_5,_6],[SB,_2,_4,_6],[SB,_2,_5],[SB,_2,_5,_6],[SB,_2,_6],[SB,_3],[SB,_3,_4],[SB,_3,_4,_5],[SB,_3,_4,_5,_6],[SB,_3,_4,_6],[SB,_3,_5],[SB,_3,_5,_6],[SB,_3,_6],[SB,_4],[SB,_4,_5],[SB,_4,_5,_6],[SB,_4,_6],[SB,_5],[SB,_5,_6],[SB,_6],[_1],[_1,_2],[_1,_2,_3],[_1,_2,_3,_4],[_1,_2,_3,_4,_5],[_1,_2,_3,_4,_5,_6],[_1,_2,_3,_4,_6],[_1,_2,_3,_5],[_1,_2,_3,_5,_6],[_1,_2,_3,_6],[_1,_2,_4],[_1,_2,_4,_5],[_1,_2,_4,_5,_6],[_1,_2,_4,_6],[_1,_2,_5],[_1,_2,_5,_6],[_1,_2,_6],[_1,_3],[_1,_3,_4],[_1,_3,_4,_5],[_1,_3,_4,_5,_6],[_1,_3,_4,_6],[_1,_3,_5],[_1,_3,_5,_6],[_1,_3,_6],[_1,_4],[_1,_4,_5],[_1,_4,_5,_6],[_1,_4,_6],[_1,_5],[_1,_5,_6],[_1,_6],[_2],[_2,_3],[_2,_3,_4],[_2,_3,_4,_5],[_2,_3,_4,_5,_6],[_2,_3,_4,_6],[_2,_3,_5],[_2,_3,_5,_6],[_2,_3,_6],[_2,_4],[_2,_4,_5],[_2,_4,_5,_6],[_2,_4,_6],[_2,_5],[_2,_5,_6],[_2,_6],[_3],[_3,_4],[_3,_4,_5],[_3,_4,_5,_6],[_3,_4,_6],[_3,_5],[_3,_5,_6],[_3,_6],[_4],[_4,_5],[_4,_5,_6],[_4,_6],[_5],[_5,_6],[_6]])).

:- true pred init(N,M,Npats,Ipats,Result)
   : ( (N=100), (M=10), (Npats=4), (Ipats=[[a,a,a,b,b,b,b,a,a,a,a,a,b,b,a,a,a],[a,a,b,b,b,b,a,a,[a,a],[b,b]],[a,a,a,b,[b,a],b,a,b,a]]),
       mshare([[Result]]),
       linear(Result) )
   => mshare([[Result]]).

init(N,M,Npats,Ipats,Result) :-
    true((
        mshare([[Result]]),
        ground([N,M,Npats,Ipats]),
        linear(Result)
    )),
    init(N,M,M,Npats,Ipats,Result),
    true((
        mshare([[Result]]),
        ground([N,M,Npats,Ipats])
    )).

:- true pred init(N,_1,_2,_3,_4,_5)
   : ( (_1=_2),
       mshare([[_5]]),
       ground([N,_1,_3,_4]), linear(_5) )
   => ( mshare([[_5]]),
        ground([N,_1,_3,_4]) ).

:- true pred init(N,_1,_2,_3,_4,_5)
   : ( mshare([[_5]]),
       ground([N,_1,_2,_3,_4]) )
   => ( mshare([[_5]]),
        ground([N,_1,_2,_3,_4]) ).

init(0,_1,_2,_3,_4,_5) :-
    !,
    true((mshare([[_5]]),ground([_1,_2,_3,_4]);mshare([[_5]]),ground([_1,_2,_3,_4]),linear(_5))).
init(N,I,M,Npats,Ipats,[Symb|Rest]) :-
    true((mshare([[Symb],[Symb,Rest],[Rest],[L],[Ppats],[J],[N1],[I1]]),ground([N,I,M,Npats,Ipats]),linear(L),linear(Ppats),linear(J),linear(N1),linear(I1);mshare([[Symb],[Rest],[L],[Ppats],[J],[N1],[I1]]),ground([N,I,M,Npats,Ipats]),linear(Symb),linear(Rest),linear(L),linear(Ppats),linear(J),linear(N1),linear(I1))),
    fill(I,[],L),
    true((mshare([[Symb],[Symb,Rest],[Rest],[Ppats],[J],[N1],[I1]]),ground([N,I,M,Npats,Ipats,L]);mshare([[Symb],[Rest],[Ppats],[J],[N1],[I1]]),ground([N,I,M,Npats,Ipats,L]))),
    get_pats(Npats,Ipats,Ppats),
    true((mshare([[Symb],[Symb,Rest],[Rest],[J],[N1],[I1]]),ground([N,I,M,Npats,Ipats,L,Ppats]);mshare([[Symb],[Rest],[J],[N1],[I1]]),ground([N,I,M,Npats,Ipats,L,Ppats]))),
    J is M-I,
    true((mshare([[Symb],[Symb,Rest],[Rest],[N1],[I1]]),ground([N,I,M,Npats,Ipats,L,Ppats,J]);mshare([[Symb],[Rest],[N1],[I1]]),ground([N,I,M,Npats,Ipats,L,Ppats,J]))),
    fill(J,[pattern(Ppats)|L],Symb),
    true((
        mshare([[Rest],[N1],[I1]]),
        ground([N,I,M,Npats,Ipats,Symb,L,Ppats,J])
    )),
    N1 is N-1,
    true((
        mshare([[Rest],[I1]]),
        ground([N,I,M,Npats,Ipats,Symb,L,Ppats,J,N1])
    )),
    'init/6/2/$disj/1'(I,M,I1),
    true((
        mshare([[Rest]]),
        ground([N,I,M,Npats,Ipats,Symb,L,Ppats,J,N1,I1])
    )),
    init(N1,I1,M,Npats,Ipats,Rest),
    true((
        mshare([[Rest]]),
        ground([N,I,M,Npats,Ipats,Symb,L,Ppats,J,N1,I1])
    )).

:- true pred 'init/6/2/$disj/1'(I,M,I1)
   : ( mshare([[I1]]),
       ground([I,M]) )
   => ground([I,M,I1]).

'init/6/2/$disj/1'(I,M,I1) :-
    true((
        mshare([[I1]]),
        ground([I,M])
    )),
    I=:=0,
    !,
    true((
        mshare([[I1]]),
        ground([I,M])
    )),
    I1 is M,
    true(ground([I,M,I1])).
'init/6/2/$disj/1'(I,M,I1) :-
    true((
        mshare([[I1]]),
        ground([I,M])
    )),
    I1 is I-1,
    true(ground([I,M,I1])).

:- true pred fill(N,L,_A)
   : ( (L=[pattern(_C)|_B]),
       mshare([[_A]]),
       ground([N,_B,_C]) )
   => ground([N,_A,_B,_C]).

:- true pred fill(N,L,_A)
   : ( (L=[]),
       mshare([[_A]]),
       ground([N]), linear(_A) )
   => ground([N,_A]).

:- true pred fill(N,L,_A)
   : ( mshare([[_A]]),
       ground([N,L]) )
   => ground([N,L,_A]).

:- true pred fill(N,L,_A)
   : ( mshare([[_A]]),
       ground([N,L]), linear(_A) )
   => ground([N,L,_A]).

fill(0,L,L) :-
    !,
    true(ground([L])).
fill(N,L,[dummy([])|Rest]) :-
    true((mshare([[Rest],[N1]]),ground([N,L]),linear(Rest),linear(N1);mshare([[Rest],[N1]]),ground([N,L]),linear(N1))),
    N1 is N-1,
    true((mshare([[Rest]]),ground([N,L,N1]);mshare([[Rest]]),ground([N,L,N1]),linear(Rest))),
    fill(N1,L,Rest),
    true(ground([N,L,Rest,N1])).

:- true pred randomize(In,_A,_1)
   : ( (_1=21),
       mshare([[In],[_A]]) )
   => mshare([[In,_A]]).

:- true pred randomize(In,_A,_1)
   : ( mshare([[In],[In,_A],[_A]]),
       ground([_1]) )
   => ( mshare([[In,_A]]),
        ground([_1]) ).

randomize([],[],_1) :-
    !,
    true(ground([_1])).
randomize(In,[X|Out],Rand) :-
    true((mshare([[In],[In,X],[In,X,Out],[In,Out],[X],[X,Out],[Out],[Lin],[Rand1],[N],[In1]]),ground([Rand]),linear(Lin),linear(Rand1),linear(N),linear(In1);mshare([[In],[X],[X,Out],[Out],[Lin],[Rand1],[N],[In1]]),ground([Rand]),linear(Lin),linear(Rand1),linear(N),linear(In1))),
    list_to_length(In,Lin),
    true((mshare([[In],[In,X],[In,X,Out],[In,Out],[X],[X,Out],[Out],[Rand1],[N],[In1]]),ground([Rand,Lin]);mshare([[In],[X],[X,Out],[Out],[Rand1],[N],[In1]]),ground([Rand,Lin]))),
    Rand1 is Rand*17 mod 251,
    true((mshare([[In],[In,X],[In,X,Out],[In,Out],[X],[X,Out],[Out],[N],[In1]]),ground([Rand,Lin,Rand1]);mshare([[In],[X],[X,Out],[Out],[N],[In1]]),ground([Rand,Lin,Rand1]))),
    N is Rand1 mod Lin,
    true((mshare([[In],[In,X],[In,X,Out],[In,Out],[X],[X,Out],[Out],[In1]]),ground([Rand,Lin,Rand1,N]);mshare([[In],[X],[X,Out],[Out],[In1]]),ground([Rand,Lin,Rand1,N]))),
    split(N,In,X,In1),
    true((mshare([[In,X],[In,X,Out],[In,X,Out,In1],[In,X,In1],[In,Out,In1],[In,In1],[Out]]),ground([Rand,Lin,Rand1,N]);mshare([[In,X],[In,X,Out],[In,X,Out,In1],[In,X,In1],[In,In1],[Out]]),ground([Rand,Lin,Rand1,N]))),
    randomize(In1,Out,Rand1),
    true((
        mshare([[In,X],[In,X,Out,In1],[In,Out,In1]]),
        ground([Rand,Lin,Rand1,N])
    )).

:- true pred list_to_length(List,Len)
   : ( mshare([[List],[Len]]),
       linear(Len) )
   => ( mshare([[List]]),
        ground([Len]) ).

list_to_length(List,Len) :-
    true((
        mshare([[List],[Len]]),
        linear(Len)
    )),
    list_to_length(List,0,Len),
    true((
        mshare([[List]]),
        ground([Len])
    )).

:- true pred list_to_length(_A,L,_B)
   : ( (L=0),
       mshare([[_A],[_B]]),
       linear(_B) )
   => ( mshare([[_A]]),
        ground([_B]) ).

:- true pred list_to_length(_A,L,_B)
   : ( mshare([[_A],[_B]]),
       ground([L]), linear(_B) )
   => ( mshare([[_A]]),
        ground([L,_B]) ).

list_to_length([],L,L) :-
    !,
    true(ground([L])).
list_to_length([_1|T],L0,L) :-
    true((
        mshare([[L],[_1],[_1,T],[T],[L1]]),
        ground([L0]),
        linear(L),
        linear(L1)
    )),
    L1 is L0+1,
    true((
        mshare([[L],[_1],[_1,T],[T]]),
        ground([L0,L1]),
        linear(L)
    )),
    list_to_length(T,L1,L),
    true((
        mshare([[_1],[_1,T],[T]]),
        ground([L0,L,L1])
    )).

:- true pred split(N,_A,X,Xs)
   : ( mshare([[_A],[_A,X],[X],[Xs]]),
       ground([N]) )
   => ( mshare([[_A,X],[_A,X,Xs],[_A,Xs]]),
        ground([N]) ).

:- true pred split(N,_A,X,Xs)
   : ( mshare([[_A],[_A,X],[_A,X,Xs],[_A,Xs],[X],[X,Xs],[Xs]]),
       ground([N]) )
   => ( mshare([[_A,X],[_A,X,Xs],[_A,Xs]]),
        ground([N]) ).

:- true pred split(N,_A,X,Xs)
   : ( mshare([[_A],[X],[Xs]]),
       ground([N]) )
   => ( mshare([[_A,X],[_A,X,Xs],[_A,Xs]]),
        ground([N]) ).

:- true pred split(N,_A,X,Xs)
   : ( mshare([[_A],[_A,Xs],[X],[Xs]]),
       ground([N]) )
   => ( mshare([[_A,X],[_A,X,Xs],[_A,Xs]]),
        ground([N]) ).

split(0,[X|Xs],X,Xs) :-
    !,
    true(mshare([[X],[X,Xs],[Xs]])).
split(N,[X|Xs],RemovedElt,[X|Ys]) :-
    true((mshare([[RemovedElt],[RemovedElt,X],[RemovedElt,X,Xs],[RemovedElt,X,Xs,Ys],[RemovedElt,X,Ys],[RemovedElt,Xs],[RemovedElt,Xs,Ys],[RemovedElt,Ys],[X],[X,Xs],[X,Xs,Ys],[X,Ys],[Xs],[Xs,Ys],[Ys],[N1]]),ground([N]),linear(N1);mshare([[RemovedElt],[RemovedElt,X],[RemovedElt,X,Xs],[RemovedElt,X,Xs,Ys],[RemovedElt,X,Ys],[RemovedElt,Xs],[X],[X,Xs],[X,Xs,Ys],[X,Ys],[Xs],[Ys],[N1]]),ground([N]),linear(N1);mshare([[RemovedElt],[X],[X,Xs],[X,Xs,Ys],[X,Ys],[Xs],[Xs,Ys],[Ys],[N1]]),ground([N]),linear(N1);mshare([[RemovedElt],[X],[X,Xs],[X,Xs,Ys],[X,Ys],[Xs],[Ys],[N1]]),ground([N]),linear(N1))),
    N1 is N-1,
    true((mshare([[RemovedElt],[RemovedElt,X],[RemovedElt,X,Xs],[RemovedElt,X,Xs,Ys],[RemovedElt,X,Ys],[RemovedElt,Xs],[RemovedElt,Xs,Ys],[RemovedElt,Ys],[X],[X,Xs],[X,Xs,Ys],[X,Ys],[Xs],[Xs,Ys],[Ys]]),ground([N,N1]);mshare([[RemovedElt],[RemovedElt,X],[RemovedElt,X,Xs],[RemovedElt,X,Xs,Ys],[RemovedElt,X,Ys],[RemovedElt,Xs],[X],[X,Xs],[X,Xs,Ys],[X,Ys],[Xs],[Ys]]),ground([N,N1]);mshare([[RemovedElt],[X],[X,Xs],[X,Xs,Ys],[X,Ys],[Xs],[Xs,Ys],[Ys]]),ground([N,N1]);mshare([[RemovedElt],[X],[X,Xs],[X,Xs,Ys],[X,Ys],[Xs],[Ys]]),ground([N,N1]))),
    split(N1,Xs,RemovedElt,Ys),
    true((
        mshare([[RemovedElt,X,Xs],[RemovedElt,X,Xs,Ys],[RemovedElt,Xs],[RemovedElt,Xs,Ys],[X],[X,Xs,Ys],[Xs,Ys]]),
        ground([N,N1])
    )).

:- true pred investigate(_A,_1)
   : ( (_1=[[star(_B),_C,star(_D),_C,a,star(_B),a,star(_D),star(_B)],[star(_B),star(_D),star(_D),star(_B),[star(_B)],[star(_D)]],[_E,_F,star(_G),[b,a],star(_H),_I,_J]]),
       mshare([[_A],[_B],[_C],[_D],[_E],[_F],[_G],[_H],[_I],[_J]]) )
   => mshare([[_A],[_B],[_B,_C],[_B,_C,_D],[_B,_C,_D,_E],[_B,_C,_D,_E,_F],[_B,_C,_D,_E,_F,_G],[_B,_C,_D,_E,_F,_G,_H],[_B,_C,_D,_E,_F,_G,_H,_I],[_B,_C,_D,_E,_F,_G,_H,_I,_J],[_B,_C,_D,_E,_F,_G,_H,_J],[_B,_C,_D,_E,_F,_G,_I],[_B,_C,_D,_E,_F,_G,_I,_J],[_B,_C,_D,_E,_F,_G,_J],[_B,_C,_D,_E,_F,_H],[_B,_C,_D,_E,_F,_H,_I],[_B,_C,_D,_E,_F,_H,_I,_J],[_B,_C,_D,_E,_F,_H,_J],[_B,_C,_D,_E,_F,_I],[_B,_C,_D,_E,_F,_I,_J],[_B,_C,_D,_E,_F,_J],[_B,_C,_D,_E,_G],[_B,_C,_D,_E,_G,_H],[_B,_C,_D,_E,_G,_H,_I],[_B,_C,_D,_E,_G,_H,_I,_J],[_B,_C,_D,_E,_G,_H,_J],[_B,_C,_D,_E,_G,_I],[_B,_C,_D,_E,_G,_I,_J],[_B,_C,_D,_E,_G,_J],[_B,_C,_D,_E,_H],[_B,_C,_D,_E,_H,_I],[_B,_C,_D,_E,_H,_I,_J],[_B,_C,_D,_E,_H,_J],[_B,_C,_D,_E,_I],[_B,_C,_D,_E,_I,_J],[_B,_C,_D,_E,_J],[_B,_C,_D,_F],[_B,_C,_D,_F,_G],[_B,_C,_D,_F,_G,_H],[_B,_C,_D,_F,_G,_H,_I],[_B,_C,_D,_F,_G,_H,_I,_J],[_B,_C,_D,_F,_G,_H,_J],[_B,_C,_D,_F,_G,_I],[_B,_C,_D,_F,_G,_I,_J],[_B,_C,_D,_F,_G,_J],[_B,_C,_D,_F,_H],[_B,_C,_D,_F,_H,_I],[_B,_C,_D,_F,_H,_I,_J],[_B,_C,_D,_F,_H,_J],[_B,_C,_D,_F,_I],[_B,_C,_D,_F,_I,_J],[_B,_C,_D,_F,_J],[_B,_C,_D,_G],[_B,_C,_D,_G,_H],[_B,_C,_D,_G,_H,_I],[_B,_C,_D,_G,_H,_I,_J],[_B,_C,_D,_G,_H,_J],[_B,_C,_D,_G,_I],[_B,_C,_D,_G,_I,_J],[_B,_C,_D,_G,_J],[_B,_C,_D,_H],[_B,_C,_D,_H,_I],[_B,_C,_D,_H,_I,_J],[_B,_C,_D,_H,_J],[_B,_C,_D,_I],[_B,_C,_D,_I,_J],[_B,_C,_D,_J],[_B,_C,_E],[_B,_C,_E,_F],[_B,_C,_E,_F,_G],[_B,_C,_E,_F,_G,_H],[_B,_C,_E,_F,_G,_H,_I],[_B,_C,_E,_F,_G,_H,_I,_J],[_B,_C,_E,_F,_G,_H,_J],[_B,_C,_E,_F,_G,_I],[_B,_C,_E,_F,_G,_I,_J],[_B,_C,_E,_F,_G,_J],[_B,_C,_E,_F,_H],[_B,_C,_E,_F,_H,_I],[_B,_C,_E,_F,_H,_I,_J],[_B,_C,_E,_F,_H,_J],[_B,_C,_E,_F,_I],[_B,_C,_E,_F,_I,_J],[_B,_C,_E,_F,_J],[_B,_C,_E,_G],[_B,_C,_E,_G,_H],[_B,_C,_E,_G,_H,_I],[_B,_C,_E,_G,_H,_I,_J],[_B,_C,_E,_G,_H,_J],[_B,_C,_E,_G,_I],[_B,_C,_E,_G,_I,_J],[_B,_C,_E,_G,_J],[_B,_C,_E,_H],[_B,_C,_E,_H,_I],[_B,_C,_E,_H,_I,_J],[_B,_C,_E,_H,_J],[_B,_C,_E,_I],[_B,_C,_E,_I,_J],[_B,_C,_E,_J],[_B,_C,_F],[_B,_C,_F,_G],[_B,_C,_F,_G,_H],[_B,_C,_F,_G,_H,_I],[_B,_C,_F,_G,_H,_I,_J],[_B,_C,_F,_G,_H,_J],[_B,_C,_F,_G,_I],[_B,_C,_F,_G,_I,_J],[_B,_C,_F,_G,_J],[_B,_C,_F,_H],[_B,_C,_F,_H,_I],[_B,_C,_F,_H,_I,_J],[_B,_C,_F,_H,_J],[_B,_C,_F,_I],[_B,_C,_F,_I,_J],[_B,_C,_F,_J],[_B,_C,_G],[_B,_C,_G,_H],[_B,_C,_G,_H,_I],[_B,_C,_G,_H,_I,_J],[_B,_C,_G,_H,_J],[_B,_C,_G,_I],[_B,_C,_G,_I,_J],[_B,_C,_G,_J],[_B,_C,_H],[_B,_C,_H,_I],[_B,_C,_H,_I,_J],[_B,_C,_H,_J],[_B,_C,_I],[_B,_C,_I,_J],[_B,_C,_J],[_B,_D],[_B,_D,_E],[_B,_D,_E,_F],[_B,_D,_E,_F,_G],[_B,_D,_E,_F,_G,_H],[_B,_D,_E,_F,_G,_H,_I],[_B,_D,_E,_F,_G,_H,_I,_J],[_B,_D,_E,_F,_G,_H,_J],[_B,_D,_E,_F,_G,_I],[_B,_D,_E,_F,_G,_I,_J],[_B,_D,_E,_F,_G,_J],[_B,_D,_E,_F,_H],[_B,_D,_E,_F,_H,_I],[_B,_D,_E,_F,_H,_I,_J],[_B,_D,_E,_F,_H,_J],[_B,_D,_E,_F,_I],[_B,_D,_E,_F,_I,_J],[_B,_D,_E,_F,_J],[_B,_D,_E,_G],[_B,_D,_E,_G,_H],[_B,_D,_E,_G,_H,_I],[_B,_D,_E,_G,_H,_I,_J],[_B,_D,_E,_G,_H,_J],[_B,_D,_E,_G,_I],[_B,_D,_E,_G,_I,_J],[_B,_D,_E,_G,_J],[_B,_D,_E,_H],[_B,_D,_E,_H,_I],[_B,_D,_E,_H,_I,_J],[_B,_D,_E,_H,_J],[_B,_D,_E,_I],[_B,_D,_E,_I,_J],[_B,_D,_E,_J],[_B,_D,_F],[_B,_D,_F,_G],[_B,_D,_F,_G,_H],[_B,_D,_F,_G,_H,_I],[_B,_D,_F,_G,_H,_I,_J],[_B,_D,_F,_G,_H,_J],[_B,_D,_F,_G,_I],[_B,_D,_F,_G,_I,_J],[_B,_D,_F,_G,_J],[_B,_D,_F,_H],[_B,_D,_F,_H,_I],[_B,_D,_F,_H,_I,_J],[_B,_D,_F,_H,_J],[_B,_D,_F,_I],[_B,_D,_F,_I,_J],[_B,_D,_F,_J],[_B,_D,_G],[_B,_D,_G,_H],[_B,_D,_G,_H,_I],[_B,_D,_G,_H,_I,_J],[_B,_D,_G,_H,_J],[_B,_D,_G,_I],[_B,_D,_G,_I,_J],[_B,_D,_G,_J],[_B,_D,_H],[_B,_D,_H,_I],[_B,_D,_H,_I,_J],[_B,_D,_H,_J],[_B,_D,_I],[_B,_D,_I,_J],[_B,_D,_J],[_B,_E],[_B,_E,_F],[_B,_E,_F,_G],[_B,_E,_F,_G,_H],[_B,_E,_F,_G,_H,_I],[_B,_E,_F,_G,_H,_I,_J],[_B,_E,_F,_G,_H,_J],[_B,_E,_F,_G,_I],[_B,_E,_F,_G,_I,_J],[_B,_E,_F,_G,_J],[_B,_E,_F,_H],[_B,_E,_F,_H,_I],[_B,_E,_F,_H,_I,_J],[_B,_E,_F,_H,_J],[_B,_E,_F,_I],[_B,_E,_F,_I,_J],[_B,_E,_F,_J],[_B,_E,_G],[_B,_E,_G,_H],[_B,_E,_G,_H,_I],[_B,_E,_G,_H,_I,_J],[_B,_E,_G,_H,_J],[_B,_E,_G,_I],[_B,_E,_G,_I,_J],[_B,_E,_G,_J],[_B,_E,_H],[_B,_E,_H,_I],[_B,_E,_H,_I,_J],[_B,_E,_H,_J],[_B,_E,_I],[_B,_E,_I,_J],[_B,_E,_J],[_B,_F],[_B,_F,_G],[_B,_F,_G,_H],[_B,_F,_G,_H,_I],[_B,_F,_G,_H,_I,_J],[_B,_F,_G,_H,_J],[_B,_F,_G,_I],[_B,_F,_G,_I,_J],[_B,_F,_G,_J],[_B,_F,_H],[_B,_F,_H,_I],[_B,_F,_H,_I,_J],[_B,_F,_H,_J],[_B,_F,_I],[_B,_F,_I,_J],[_B,_F,_J],[_B,_G],[_B,_G,_H],[_B,_G,_H,_I],[_B,_G,_H,_I,_J],[_B,_G,_H,_J],[_B,_G,_I],[_B,_G,_I,_J],[_B,_G,_J],[_B,_H],[_B,_H,_I],[_B,_H,_I,_J],[_B,_H,_J],[_B,_I],[_B,_I,_J],[_B,_J],[_C],[_C,_D],[_C,_D,_E],[_C,_D,_E,_F],[_C,_D,_E,_F,_G],[_C,_D,_E,_F,_G,_H],[_C,_D,_E,_F,_G,_H,_I],[_C,_D,_E,_F,_G,_H,_I,_J],[_C,_D,_E,_F,_G,_H,_J],[_C,_D,_E,_F,_G,_I],[_C,_D,_E,_F,_G,_I,_J],[_C,_D,_E,_F,_G,_J],[_C,_D,_E,_F,_H],[_C,_D,_E,_F,_H,_I],[_C,_D,_E,_F,_H,_I,_J],[_C,_D,_E,_F,_H,_J],[_C,_D,_E,_F,_I],[_C,_D,_E,_F,_I,_J],[_C,_D,_E,_F,_J],[_C,_D,_E,_G],[_C,_D,_E,_G,_H],[_C,_D,_E,_G,_H,_I],[_C,_D,_E,_G,_H,_I,_J],[_C,_D,_E,_G,_H,_J],[_C,_D,_E,_G,_I],[_C,_D,_E,_G,_I,_J],[_C,_D,_E,_G,_J],[_C,_D,_E,_H],[_C,_D,_E,_H,_I],[_C,_D,_E,_H,_I,_J],[_C,_D,_E,_H,_J],[_C,_D,_E,_I],[_C,_D,_E,_I,_J],[_C,_D,_E,_J],[_C,_D,_F],[_C,_D,_F,_G],[_C,_D,_F,_G,_H],[_C,_D,_F,_G,_H,_I],[_C,_D,_F,_G,_H,_I,_J],[_C,_D,_F,_G,_H,_J],[_C,_D,_F,_G,_I],[_C,_D,_F,_G,_I,_J],[_C,_D,_F,_G,_J],[_C,_D,_F,_H],[_C,_D,_F,_H,_I],[_C,_D,_F,_H,_I,_J],[_C,_D,_F,_H,_J],[_C,_D,_F,_I],[_C,_D,_F,_I,_J],[_C,_D,_F,_J],[_C,_D,_G],[_C,_D,_G,_H],[_C,_D,_G,_H,_I],[_C,_D,_G,_H,_I,_J],[_C,_D,_G,_H,_J],[_C,_D,_G,_I],[_C,_D,_G,_I,_J],[_C,_D,_G,_J],[_C,_D,_H],[_C,_D,_H,_I],[_C,_D,_H,_I,_J],[_C,_D,_H,_J],[_C,_D,_I],[_C,_D,_I,_J],[_C,_D,_J],[_C,_E],[_C,_E,_F],[_C,_E,_F,_G],[_C,_E,_F,_G,_H],[_C,_E,_F,_G,_H,_I],[_C,_E,_F,_G,_H,_I,_J],[_C,_E,_F,_G,_H,_J],[_C,_E,_F,_G,_I],[_C,_E,_F,_G,_I,_J],[_C,_E,_F,_G,_J],[_C,_E,_F,_H],[_C,_E,_F,_H,_I],[_C,_E,_F,_H,_I,_J],[_C,_E,_F,_H,_J],[_C,_E,_F,_I],[_C,_E,_F,_I,_J],[_C,_E,_F,_J],[_C,_E,_G],[_C,_E,_G,_H],[_C,_E,_G,_H,_I],[_C,_E,_G,_H,_I,_J],[_C,_E,_G,_H,_J],[_C,_E,_G,_I],[_C,_E,_G,_I,_J],[_C,_E,_G,_J],[_C,_E,_H],[_C,_E,_H,_I],[_C,_E,_H,_I,_J],[_C,_E,_H,_J],[_C,_E,_I],[_C,_E,_I,_J],[_C,_E,_J],[_C,_F],[_C,_F,_G],[_C,_F,_G,_H],[_C,_F,_G,_H,_I],[_C,_F,_G,_H,_I,_J],[_C,_F,_G,_H,_J],[_C,_F,_G,_I],[_C,_F,_G,_I,_J],[_C,_F,_G,_J],[_C,_F,_H],[_C,_F,_H,_I],[_C,_F,_H,_I,_J],[_C,_F,_H,_J],[_C,_F,_I],[_C,_F,_I,_J],[_C,_F,_J],[_C,_G],[_C,_G,_H],[_C,_G,_H,_I],[_C,_G,_H,_I,_J],[_C,_G,_H,_J],[_C,_G,_I],[_C,_G,_I,_J],[_C,_G,_J],[_C,_H],[_C,_H,_I],[_C,_H,_I,_J],[_C,_H,_J],[_C,_I],[_C,_I,_J],[_C,_J],[_D],[_D,_E],[_D,_E,_F],[_D,_E,_F,_G],[_D,_E,_F,_G,_H],[_D,_E,_F,_G,_H,_I],[_D,_E,_F,_G,_H,_I,_J],[_D,_E,_F,_G,_H,_J],[_D,_E,_F,_G,_I],[_D,_E,_F,_G,_I,_J],[_D,_E,_F,_G,_J],[_D,_E,_F,_H],[_D,_E,_F,_H,_I],[_D,_E,_F,_H,_I,_J],[_D,_E,_F,_H,_J],[_D,_E,_F,_I],[_D,_E,_F,_I,_J],[_D,_E,_F,_J],[_D,_E,_G],[_D,_E,_G,_H],[_D,_E,_G,_H,_I],[_D,_E,_G,_H,_I,_J],[_D,_E,_G,_H,_J],[_D,_E,_G,_I],[_D,_E,_G,_I,_J],[_D,_E,_G,_J],[_D,_E,_H],[_D,_E,_H,_I],[_D,_E,_H,_I,_J],[_D,_E,_H,_J],[_D,_E,_I],[_D,_E,_I,_J],[_D,_E,_J],[_D,_F],[_D,_F,_G],[_D,_F,_G,_H],[_D,_F,_G,_H,_I],[_D,_F,_G,_H,_I,_J],[_D,_F,_G,_H,_J],[_D,_F,_G,_I],[_D,_F,_G,_I,_J],[_D,_F,_G,_J],[_D,_F,_H],[_D,_F,_H,_I],[_D,_F,_H,_I,_J],[_D,_F,_H,_J],[_D,_F,_I],[_D,_F,_I,_J],[_D,_F,_J],[_D,_G],[_D,_G,_H],[_D,_G,_H,_I],[_D,_G,_H,_I,_J],[_D,_G,_H,_J],[_D,_G,_I],[_D,_G,_I,_J],[_D,_G,_J],[_D,_H],[_D,_H,_I],[_D,_H,_I,_J],[_D,_H,_J],[_D,_I],[_D,_I,_J],[_D,_J],[_E],[_E,_F],[_E,_F,_G],[_E,_F,_G,_H],[_E,_F,_G,_H,_I],[_E,_F,_G,_H,_I,_J],[_E,_F,_G,_H,_J],[_E,_F,_G,_I],[_E,_F,_G,_I,_J],[_E,_F,_G,_J],[_E,_F,_H],[_E,_F,_H,_I],[_E,_F,_H,_I,_J],[_E,_F,_H,_J],[_E,_F,_I],[_E,_F,_I,_J],[_E,_F,_J],[_E,_G],[_E,_G,_H],[_E,_G,_H,_I],[_E,_G,_H,_I,_J],[_E,_G,_H,_J],[_E,_G,_I],[_E,_G,_I,_J],[_E,_G,_J],[_E,_H],[_E,_H,_I],[_E,_H,_I,_J],[_E,_H,_J],[_E,_I],[_E,_I,_J],[_E,_J],[_F],[_F,_G],[_F,_G,_H],[_F,_G,_H,_I],[_F,_G,_H,_I,_J],[_F,_G,_H,_J],[_F,_G,_I],[_F,_G,_I,_J],[_F,_G,_J],[_F,_H],[_F,_H,_I],[_F,_H,_I,_J],[_F,_H,_J],[_F,_I],[_F,_I,_J],[_F,_J],[_G],[_G,_H],[_G,_H,_I],[_G,_H,_I,_J],[_G,_H,_J],[_G,_I],[_G,_I,_J],[_G,_J],[_H],[_H,_I],[_H,_I,_J],[_H,_J],[_I],[_I,_J],[_J]]).

:- true pred investigate(_A,_1)
   : mshare([[_A],[_1]])
   => mshare([[_A],[_1]]).

investigate([],_1) :-
    !,
    true(mshare([[_1]])).
investigate([U|Units],Patterns) :-
    true((
        mshare([[Patterns],[U],[U,Units],[Units],[Data]]),
        linear(Data)
    )),
    property(U,pattern,Data),
    true(mshare([[Patterns],[U],[U,Units],[U,Units,Data],[U,Data],[Units]])),
    p_investigate(Data,Patterns),
    true(mshare([[Patterns],[U],[U,Units],[U,Units,Data],[U,Data],[Units]])),
    investigate(Units,Patterns),
    true(mshare([[Patterns],[U],[U,Units],[U,Units,Data],[U,Data],[Units]])).

:- true pred get_pats(Npats,Ipats,Result)
   : ( mshare([[Result]]),
       ground([Npats,Ipats]) )
   => ground([Npats,Ipats,Result]).

get_pats(Npats,Ipats,Result) :-
    true((
        mshare([[Result]]),
        ground([Npats,Ipats])
    )),
    get_pats(Npats,Ipats,Result,Ipats),
    true(ground([Npats,Ipats,Result])).

:- true pred get_pats(N,_1,Ys,_2)
   : ( mshare([[Ys]]),
       ground([N,_1,_2]) )
   => ground([N,_1,Ys,_2]).

:- true pred get_pats(N,_1,Ys,_2)
   : ( (_1=_2),
       mshare([[Ys]]),
       ground([N,_1]) )
   => ground([N,_1,Ys]).

get_pats(0,_1,[],_2) :-
    !,
    true(ground([_1,_2])).
get_pats(N,[X|Xs],[X|Ys],Ipats) :-
    true((
        mshare([[Ys],[N1]]),
        ground([N,Ipats,X,Xs]),
        linear(N1)
    )),
    N1 is N-1,
    true((
        mshare([[Ys]]),
        ground([N,Ipats,X,Xs,N1])
    )),
    get_pats(N1,Xs,Ys,Ipats),
    true(ground([N,Ipats,X,Xs,Ys,N1])).
get_pats(N,[],Ys,Ipats) :-
    true((
        mshare([[Ys]]),
        ground([N,Ipats])
    )),
    get_pats(N,Ipats,Ys,Ipats),
    true(ground([N,Ys,Ipats])).

:- true pred property(_A,_1,_2)
   : ( (_1=pattern),
       mshare([[_A],[_2]]),
       linear(_2) )
   => mshare([[_A],[_A,_2]]).

:- true pred property(_A,_1,_2)
   : ( mshare([[_A],[_2]]),
       ground([_1]), linear(_2) )
   => ( mshare([[_A],[_A,_2]]),
        ground([_1]) ).

property([],_1,_2) :-
    true((
        mshare([[_2]]),
        ground([_1]),
        linear(_2)
    )),
    fail,
    true(fails(_)).
property([Prop|_1],P,Val) :-
    true((
        mshare([[Val],[Prop],[Prop,_1],[_1],[_2]]),
        ground([P]),
        linear(Val),
        linear(_2)
    )),
    functor(Prop,P,_2),
    !,
    true((
        mshare([[Val],[Prop],[Prop,_1],[_1]]),
        ground([P,_2]),
        linear(Val)
    )),
    arg(1,Prop,Val),
    true((
        mshare([[Val,Prop],[Val,Prop,_1],[_1]]),
        ground([P,_2])
    )).
property([_1|RProps],P,Val) :-
    true((
        mshare([[Val],[_1],[_1,RProps],[RProps]]),
        ground([P]),
        linear(Val)
    )),
    property(RProps,P,Val),
    true((
        mshare([[Val,_1,RProps],[Val,RProps],[_1],[_1,RProps],[RProps]]),
        ground([P])
    )).

:- true pred p_investigate(_A,_1)
   : mshare([[_A],[_1]])
   => mshare([[_A],[_1]]).

p_investigate([],_1).
p_investigate([D|Data],Patterns) :-
    true(mshare([[Patterns],[D],[D,Data],[Data]])),
    p_match(Patterns,D),
    true(mshare([[Patterns],[D],[D,Data],[Data]])),
    p_investigate(Data,Patterns),
    true(mshare([[Patterns],[D],[D,Data],[Data]])).

:- true pred p_match(_A,_1)
   : mshare([[_A],[_1]])
   => mshare([[_A],[_1]]).

p_match([],_1).
p_match([P|Patterns],D) :-
    true(mshare([[D],[P],[P,Patterns],[Patterns]])),
    'p_match/2/2/$disj/1'(D,P),
    true(mshare([[D],[P],[P,Patterns],[Patterns]])),
    p_match(Patterns,D),
    true(mshare([[D],[P],[P,Patterns],[Patterns]])).

:- true pred 'p_match/2/2/$disj/1'(D,P)
   : mshare([[D],[P]])
   => mshare([[D],[P]]).

'p_match/2/2/$disj/1'(D,P) :-
    true(mshare([[D],[P]])),
    match(D,P),
    true(mshare([[D,P]])),
    fail,
    true(fails(_)).
'p_match/2/2/$disj/1'(D,P).

:- true pred match(List,_A)
   : mshare([[List],[_A]])
   => mshare([[List,_A]]).

:- true pred match(List,_A)
   : mshare([[List],[List,_A],[_A]])
   => mshare([[List,_A]]).

match([],[]) :-
    !,
    true(true).
match([X|PRest],[Y|SRest]) :-
    true((mshare([[X],[X,PRest],[X,PRest,Y],[X,PRest,Y,SRest],[X,PRest,SRest],[X,Y],[X,Y,SRest],[X,SRest],[PRest],[PRest,Y],[PRest,Y,SRest],[PRest,SRest],[Y],[Y,SRest],[SRest]]);mshare([[X],[X,PRest],[PRest],[Y],[Y,SRest],[SRest]]))),
    var(Y),
    !,
    true((mshare([[X],[X,PRest],[X,PRest,Y],[X,PRest,Y,SRest],[X,PRest,SRest],[X,Y],[X,Y,SRest],[X,SRest],[PRest],[PRest,Y],[PRest,Y,SRest],[PRest,SRest],[Y],[Y,SRest],[SRest]]),linear(Y);mshare([[X],[X,PRest],[PRest],[Y],[Y,SRest],[SRest]]),linear(Y))),
    X=Y,
    true((mshare([[X,PRest,Y],[X,PRest,Y,SRest],[X,Y],[X,Y,SRest],[PRest],[PRest,SRest],[SRest]]);mshare([[X,PRest,Y],[X,PRest,Y,SRest],[X,Y],[X,Y,SRest],[PRest],[SRest]]))),
    match(PRest,SRest),
    true(mshare([[X,PRest,Y,SRest],[X,Y],[PRest,SRest]])).
match(List,[Y|Rest]) :-
    true((mshare([[List],[List,Y],[List,Y,Rest],[List,Rest],[Y],[Y,Rest],[Rest],[X],[SRest]]),linear(X),linear(SRest);mshare([[List],[Y],[Y,Rest],[Rest],[X],[SRest]]),linear(X),linear(SRest))),
    nonvar(Y),
    true((mshare([[List],[List,Y],[List,Y,Rest],[List,Rest],[Y],[Y,Rest],[Rest],[X],[SRest]]),linear(X),linear(SRest);mshare([[List],[Y],[Y,Rest],[Rest],[X],[SRest]]),linear(X),linear(SRest))),
    Y=star(X),
    !,
    true((mshare([[List],[List,Y,Rest,X],[List,Y,X],[List,Rest],[Y,Rest,X],[Y,X],[Rest],[SRest]]),linear(SRest);mshare([[List],[Y,Rest,X],[Y,X],[Rest],[SRest]]),linear(SRest))),
    '$concat'(X,SRest,List),
    true((mshare([[List,Y,Rest,X],[List,Y,Rest,X,SRest],[List,Y,X],[List,Y,X,SRest],[List,Rest,SRest],[List,SRest],[Rest]]);mshare([[List,Y,Rest,X],[List,Y,Rest,X,SRest],[List,Y,X],[List,Y,X,SRest],[List,SRest],[Rest]]))),
    match(SRest,Rest),
    true(mshare([[List,Y,Rest,X,SRest],[List,Y,X],[List,Rest,SRest]])).
match([X|PRest],[Y|SRest]) :-
    true((mshare([[X],[X,PRest],[X,PRest,Y],[X,PRest,Y,SRest],[X,PRest,SRest],[X,Y],[X,Y,SRest],[X,SRest],[PRest],[PRest,Y],[PRest,Y,SRest],[PRest,SRest],[Y],[Y,SRest],[SRest]]);mshare([[X],[X,PRest],[PRest],[Y],[Y,SRest],[SRest]]))),
    'match/2/4/$disj/1'(X,Y),
    true((mshare([[X,PRest,Y],[X,PRest,Y,SRest],[X,Y],[X,Y,SRest],[PRest],[PRest,SRest],[SRest]]);mshare([[X,PRest,Y],[X,PRest,Y,SRest],[X,Y],[X,Y,SRest],[PRest],[SRest]]))),
    match(PRest,SRest),
    true(mshare([[X,PRest,Y,SRest],[X,Y],[PRest,SRest]])).

:- true pred 'match/2/4/$disj/1'(X,Y)
   : mshare([[X],[X,Y],[Y]])
   => mshare([[X,Y]]).

:- true pred 'match/2/4/$disj/1'(X,Y)
   : mshare([[X],[Y]])
   => mshare([[X,Y]]).

'match/2/4/$disj/1'(X,Y) :-
    true((mshare([[X],[X,Y],[Y]]);mshare([[X],[Y]]))),
    atom(X),
    !,
    true((
        mshare([[Y]]),
        ground([X])
    )),
    X=Y,
    true(ground([X,Y])).
'match/2/4/$disj/1'(X,Y) :-
    true((mshare([[X],[X,Y],[Y]]);mshare([[X],[Y]]))),
    match(X,Y),
    true(mshare([[X,Y]])).

:- true pred '$concat'(_A,L,_B)
   : ( mshare([[_A],[L],[_B]]),
       linear(L) )
   => mshare([[_A,L,_B],[_A,_B],[L,_B]]).

:- true pred '$concat'(_A,L,_B)
   : ( mshare([[_A],[_A,_B],[L],[_B]]),
       linear(L) )
   => mshare([[_A,L,_B],[_A,_B],[L,_B]]).

'$concat'([],L,L).
'$concat'([X|L1],L2,[X|L3]) :-
    true((mshare([[L2],[X],[X,L1],[X,L1,L3],[X,L3],[L1],[L1,L3],[L3]]),linear(L2);mshare([[L2],[X],[X,L1],[X,L1,L3],[X,L3],[L1],[L3]]),linear(L2))),
    '$concat'(L1,L2,L3),
    true(mshare([[L2,X,L1,L3],[L2,X,L3],[L2,L1,L3],[L2,L3],[X],[X,L1,L3],[L1,L3]])).


