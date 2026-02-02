:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(fast_mu,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    theorem([m,u,i,i,u]),
    true(true).

:- true pred theorem(G)
   : (G=[m,u,i,i,u]).

theorem(G) :-
    true((
        mshare([[GL1],[GL],[_Derivation]]),
        ground([G]),
        linear(GL1),
        linear(GL),
        linear(_Derivation),
        shlin2([([GL1],[GL1]),([GL],[GL]),([_Derivation],[_Derivation])])
    )),
    list_to_length(G,GL1),
    true((
        mshare([[GL],[_Derivation]]),
        ground([G,GL1]),
        linear(GL),
        linear(_Derivation),
        shlin2([([GL],[GL]),([_Derivation],[_Derivation])])
    )),
    GL is GL1-1,
    true((
        mshare([[_Derivation]]),
        ground([G,GL1,GL]),
        linear(_Derivation),
        shlin2([([_Derivation],[_Derivation])])
    )),
    derive([m,i],G,1,GL,_Derivation,0),
    true(ground([G,GL1,GL,_Derivation])).

:- true pred list_to_length(List,Len)
   : ( mshare([[Len]]),
       ground([List]), linear(Len), shlin2([([Len],[Len])]) )
   => ground([List,Len]).

list_to_length(List,Len) :-
    true((
        mshare([[Len]]),
        ground([List]),
        linear(Len),
        shlin2([([Len],[Len])])
    )),
    list_to_length(List,0,Len),
    true(ground([List,Len])).

:- true pred list_to_length(_A,L,_B)
   : ( (L=0),
       mshare([[_B]]),
       ground([_A]), linear(_B), shlin2([([_B],[_B])]) )
   => ground([_A,_B]).

:- true pred list_to_length(_A,L,_B)
   : ( mshare([[_B]]),
       ground([_A,L]), linear(_B), shlin2([([_B],[_B])]) )
   => ground([_A,L,_B]).

list_to_length([],L,L) :-
    !,
    true(ground([L])).
list_to_length([_1|T],L0,L) :-
    true((
        mshare([[L],[L1]]),
        ground([L0,_1,T]),
        linear(L),
        linear(L1),
        shlin2([([L],[L]),([L1],[L1])])
    )),
    L1 is L0+1,
    true((
        mshare([[L]]),
        ground([L0,_1,T,L1]),
        linear(L),
        shlin2([([L],[L])])
    )),
    list_to_length(T,L1,L),
    true(ground([L0,L,_1,T,L1])).

:- true pred derive(S,G,SL,GL,D,B)
   : ( (S=[m,i]), (SL=1), (B=0),
       mshare([[D]]),
       ground([G,GL]), linear(D), shlin2([([D],[D])]) )
   => ground([G,GL,D]).

:- true pred derive(S,G,SL,GL,D,B)
   : ( mshare([[D]]),
       ground([S,G,SL,GL,B]), linear(D), shlin2([([D],[D])]) )
   => ground([S,G,SL,GL,D,B]).

derive(S,G,SL,GL,D,B) :-
    true((
        mshare([[D]]),
        ground([S,G,SL,GL,B]),
        linear(D),
        shlin2([([D],[D])])
    )),
    derive2(S,G,SL,GL,1,D,B),
    true(ground([S,G,SL,GL,D,B])).
derive(S,G,SL,GL,D,B) :-
    true((
        mshare([[D],[B1]]),
        ground([S,G,SL,GL,B]),
        linear(D),
        linear(B1),
        shlin2([([D],[D]),([B1],[B1])])
    )),
    B1 is B+1,
    true((
        mshare([[D]]),
        ground([S,G,SL,GL,B,B1]),
        linear(D),
        shlin2([([D],[D])])
    )),
    derive(S,G,SL,GL,D,B1),
    true(ground([S,G,SL,GL,D,B,B1])).

:- true pred derive2(S,G,SL,GL,_1,_A,_2)
   : ( (_1=1),
       mshare([[_A]]),
       ground([S,G,SL,GL,_2]), linear(_A), shlin2([([_A],[_A])]) )
   => ground([S,G,SL,GL,_A,_2]).

:- true pred derive2(S,G,SL,GL,_1,_A,_2)
   : ( mshare([[_A]]),
       ground([S,G,SL,GL,_1,_2]), linear(_A), shlin2([([_A],[_A])]) )
   => ground([S,G,SL,GL,_1,_A,_2]).

derive2(S,S,SL,SL,_1,[],_2).
derive2(S,G,SL,GL,Pin,[rule(N,I)|D],R) :-
    true((
        mshare([[D],[N],[I],[B],[R1],[IL],[Pout]]),
        ground([S,G,SL,GL,Pin,R]),
        linear(D),
        linear(N),
        linear(I),
        linear(B),
        linear(R1),
        linear(IL),
        linear(Pout),
        shlin2([([D],[D]),([N],[N]),([I],[I]),([B],[B]),([R1],[R1]),([IL],[IL]),([Pout],[Pout])])
    )),
    lower_bound(SL,GL,B),
    true((
        mshare([[D],[N],[I],[R1],[IL],[Pout]]),
        ground([S,G,SL,GL,Pin,R,B]),
        linear(D),
        linear(N),
        linear(I),
        linear(R1),
        linear(IL),
        linear(Pout),
        shlin2([([D],[D]),([N],[N]),([I],[I]),([R1],[R1]),([IL],[IL]),([Pout],[Pout])])
    )),
    R>=B,
    true((
        mshare([[D],[N],[I],[R1],[IL],[Pout]]),
        ground([S,G,SL,GL,Pin,R,B]),
        linear(D),
        linear(N),
        linear(I),
        linear(R1),
        linear(IL),
        linear(Pout),
        shlin2([([D],[D]),([N],[N]),([I],[I]),([R1],[R1]),([IL],[IL]),([Pout],[Pout])])
    )),
    R1 is R-1,
    true((
        mshare([[D],[N],[I],[IL],[Pout]]),
        ground([S,G,SL,GL,Pin,R,B,R1]),
        linear(D),
        linear(N),
        linear(I),
        linear(IL),
        linear(Pout),
        shlin2([([D],[D]),([N],[N]),([I],[I]),([IL],[IL]),([Pout],[Pout])])
    )),
    rule(S,I,SL,IL,Pin,Pout,N),
    true((
        mshare([[D]]),
        ground([S,G,SL,GL,Pin,R,N,I,B,R1,IL,Pout]),
        linear(D),
        shlin2([([D],[D])])
    )),
    derive2(I,G,IL,GL,Pout,D,R1),
    true(ground([S,G,SL,GL,Pin,R,D,N,I,B,R1,IL,Pout])).

:- true pred rule(_A,_B,L1,L2,Pin,Pout,N)
   : ( mshare([[_B],[L2],[Pout],[N]]),
       ground([_A,L1,Pin]), linear(_B), linear(L2), linear(Pout), linear(N), shlin2([([_B],[_B]),([L2],[L2]),([Pout],[Pout]),([N],[N])]) )
   => ground([_A,_B,L1,L2,Pin,Pout,N]).

rule([m|T1],[m|T2],L1,L2,Pin,Pout,N) :-
    true((
        mshare([[L2],[Pout],[N],[T2],[X]]),
        ground([L1,Pin,T1]),
        linear(L2),
        linear(Pout),
        linear(N),
        linear(T2),
        linear(X),
        shlin2([([L2],[L2]),([Pout],[Pout]),([N],[N]),([T2],[T2]),([X],[X])])
    )),
    rule(T1,T2,L1,L2,Pin,Pout,1,i,N,X,X),
    true((
        mshare([[X]]),
        ground([L1,L2,Pin,Pout,N,T1,T2]),
        shlin2([([X],[])])
    )).

:- true pred rule(_A,L,L1,L2,Pin,Pout,Pos,_1,N,_2,_3)
   : ( (Pos=1), (_1=i), (_2=_3),
       mshare([[L],[L2],[Pout],[N],[_2]]),
       ground([_A,L1,Pin]), linear(L), linear(L2), linear(Pout), linear(N), linear(_2), shlin2([([L],[L]),([L2],[L2]),([Pout],[Pout]),([N],[N]),([_2],[_2])]) )
   => ( mshare([[_2]]),
        ground([_A,L,L1,L2,Pin,Pout,N]), shlin2([([_2],[])]) ).

:- true pred rule(_A,L,L1,L2,Pin,Pout,Pos,_1,N,_2,_3)
   : ( mshare([[L],[L2],[Pout],[N],[_2,_3]]),
       ground([_A,L1,Pin,Pos,_1]), linear(L), linear(L2), linear(Pout), linear(N), linear(_2), linear(_3), shlin2([([L],[L]),([L2],[L2]),([Pout],[Pout]),([N],[N]),([_2,_3],[_2,_3])]) )
   => ( mshare([[_2,_3]]),
        ground([_A,L,L1,L2,Pin,Pout,Pos,_1,N]), shlin2([([_2,_3],[])]) ).

rule([i],[i,u],L1,L2,Pin,Pout,Pos,_1,1,_2,_3) :-
    true((
        mshare([[L2],[Pout],[_2,_3]]),
        ground([L1,Pin,Pos,_1]),
        linear(L2),
        linear(Pout),
        linear(_2),
        linear(_3),
        shlin2([([L2],[L2]),([Pout],[Pout]),([_2,_3],[_2,_3])])
    )),
    Pos>=Pin,
    true((
        mshare([[L2],[Pout],[_2,_3]]),
        ground([L1,Pin,Pos,_1]),
        linear(L2),
        linear(Pout),
        linear(_2),
        linear(_3),
        shlin2([([L2],[L2]),([Pout],[Pout]),([_2,_3],[_2,_3])])
    )),
    Pout is Pos-2,
    true((
        mshare([[L2],[_2,_3]]),
        ground([L1,Pin,Pout,Pos,_1]),
        linear(L2),
        linear(_2),
        linear(_3),
        shlin2([([L2],[L2]),([_2,_3],[_2,_3])])
    )),
    L2 is L1+1,
    true((
        mshare([[_2,_3]]),
        ground([L1,L2,Pin,Pout,Pos,_1]),
        linear(_2),
        linear(_3),
        shlin2([([_2,_3],[_2,_3])])
    )).
rule([],L,L1,L2,_1,1,_2,_3,2,L,[]) :-
    true((
        mshare([[L2]]),
        ground([L,L1,_1,_2,_3]),
        linear(L2),
        shlin2([([L2],[L2])])
    )),
    L2 is L1+L1,
    true(ground([L,L1,L2,_1,_2,_3])).
rule([i,i,i|T],[u|T],L1,L2,Pin,Pout,Pos,_1,3,_2,_3) :-
    true((
        mshare([[L2],[Pout],[_2,_3]]),
        ground([L1,Pin,Pos,_1,T]),
        linear(L2),
        linear(Pout),
        linear(_2),
        linear(_3),
        shlin2([([L2],[L2]),([Pout],[Pout]),([_2,_3],[_2,_3])])
    )),
    Pos>=Pin,
    true((
        mshare([[L2],[Pout],[_2,_3]]),
        ground([L1,Pin,Pos,_1,T]),
        linear(L2),
        linear(Pout),
        linear(_2),
        linear(_3),
        shlin2([([L2],[L2]),([Pout],[Pout]),([_2,_3],[_2,_3])])
    )),
    Pout is Pos-1,
    true((
        mshare([[L2],[_2,_3]]),
        ground([L1,Pin,Pout,Pos,_1,T]),
        linear(L2),
        linear(_2),
        linear(_3),
        shlin2([([L2],[L2]),([_2,_3],[_2,_3])])
    )),
    L2 is L1-2,
    true((
        mshare([[_2,_3]]),
        ground([L1,L2,Pin,Pout,Pos,_1,T]),
        linear(_2),
        linear(_3),
        shlin2([([_2,_3],[_2,_3])])
    )).
rule([u,u|T],T,L1,L2,Pin,Pout,Pos,i,4,_1,_2) :-
    true((
        mshare([[L2],[Pout],[_1,_2]]),
        ground([T,L1,Pin,Pos]),
        linear(L2),
        linear(Pout),
        linear(_1),
        linear(_2),
        shlin2([([L2],[L2]),([Pout],[Pout]),([_1,_2],[_1,_2])])
    )),
    Pos>=Pin,
    true((
        mshare([[L2],[Pout],[_1,_2]]),
        ground([T,L1,Pin,Pos]),
        linear(L2),
        linear(Pout),
        linear(_1),
        linear(_2),
        shlin2([([L2],[L2]),([Pout],[Pout]),([_1,_2],[_1,_2])])
    )),
    Pout is Pos-2,
    true((
        mshare([[L2],[_1,_2]]),
        ground([T,L1,Pin,Pout,Pos]),
        linear(L2),
        linear(_1),
        linear(_2),
        shlin2([([L2],[L2]),([_1,_2],[_1,_2])])
    )),
    L2 is L1-2,
    true((
        mshare([[_1,_2]]),
        ground([T,L1,L2,Pin,Pout,Pos]),
        linear(_1),
        linear(_2),
        shlin2([([_1,_2],[_1,_2])])
    )).
rule([H|T1],[H|T2],L1,L2,Pin,Pout,Pos,_1,N,L,[H|X]) :-
    true((
        mshare([[L2],[Pout],[N],[L,X],[T2],[Pos1]]),
        ground([L1,Pin,Pos,_1,H,T1]),
        linear(L2),
        linear(Pout),
        linear(N),
        linear(L),
        linear(T2),
        linear(X),
        linear(Pos1),
        shlin2([([L2],[L2]),([Pout],[Pout]),([N],[N]),([L,X],[L,X]),([T2],[T2]),([Pos1],[Pos1])])
    )),
    Pos1 is Pos+1,
    true((
        mshare([[L2],[Pout],[N],[L,X],[T2]]),
        ground([L1,Pin,Pos,_1,H,T1,Pos1]),
        linear(L2),
        linear(Pout),
        linear(N),
        linear(L),
        linear(T2),
        linear(X),
        shlin2([([L2],[L2]),([Pout],[Pout]),([N],[N]),([L,X],[L,X]),([T2],[T2])])
    )),
    rule(T1,T2,L1,L2,Pin,Pout,Pos1,H,N,L,X),
    true((
        mshare([[L,X]]),
        ground([L1,L2,Pin,Pout,Pos,_1,N,H,T1,T2,Pos1]),
        shlin2([([L,X],[])])
    )).

:- true pred lower_bound(N,M,B)
   : ( mshare([[B]]),
       ground([N,M]), linear(B), shlin2([([B],[B])]) )
   => ground([N,M,B]).

lower_bound(N,M,1) :-
    true(ground([N,M])),
    N<M,
    true(ground([N,M])).
lower_bound(N,N,2).
lower_bound(N,M,B) :-
    true((
        mshare([[B],[Diff],[P]]),
        ground([N,M]),
        linear(B),
        linear(Diff),
        linear(P),
        shlin2([([B],[B]),([Diff],[Diff]),([P],[P])])
    )),
    N>M,
    true((
        mshare([[B],[Diff],[P]]),
        ground([N,M]),
        linear(B),
        linear(Diff),
        linear(P),
        shlin2([([B],[B]),([Diff],[Diff]),([P],[P])])
    )),
    Diff is N-M,
    true((
        mshare([[B],[P]]),
        ground([N,M,Diff]),
        linear(B),
        linear(P),
        shlin2([([B],[B]),([P],[P])])
    )),
    P is Diff/\1,
    true((
        mshare([[B]]),
        ground([N,M,Diff,P]),
        linear(B),
        shlin2([([B],[B])])
    )),
    'lower_bound/3/3/$disj/1'(B,Diff,P),
    true(ground([N,M,B,Diff,P])).

:- true pred 'lower_bound/3/3/$disj/1'(B,Diff,P)
   : ( mshare([[B]]),
       ground([Diff,P]), linear(B), shlin2([([B],[B])]) )
   => ground([B,Diff,P]).

'lower_bound/3/3/$disj/1'(B,Diff,P) :-
    true((
        mshare([[B]]),
        ground([Diff,P]),
        linear(B),
        shlin2([([B],[B])])
    )),
    P=:=0,
    !,
    true((
        mshare([[B]]),
        ground([Diff,P]),
        linear(B),
        shlin2([([B],[B])])
    )),
    B is Diff>>1,
    true(ground([B,Diff,P])).
'lower_bound/3/3/$disj/1'(B,Diff,P) :-
    true((
        mshare([[B]]),
        ground([Diff,P]),
        linear(B),
        shlin2([([B],[B])])
    )),
    B is(Diff+1)>>1+1,
    true(ground([B,Diff,P])).


