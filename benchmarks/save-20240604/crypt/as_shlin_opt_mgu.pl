:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(crypt,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true((
        mshare([[A],[B],[C],[E],[I],[H],[G],[F],[X],[D],[L],[K],[J],[Y],[P],[O],[N],[M],[Z]]),
        linear(A),
        linear(B),
        linear(C),
        linear(E),
        linear(I),
        linear(H),
        linear(G),
        linear(F),
        linear(X),
        linear(D),
        linear(L),
        linear(K),
        linear(J),
        linear(Y),
        linear(P),
        linear(O),
        linear(N),
        linear(M),
        linear(Z)
    )),
    odd(A),
    true((
        mshare([[B],[C],[E],[I],[H],[G],[F],[X],[D],[L],[K],[J],[Y],[P],[O],[N],[M],[Z]]),
        ground([A])
    )),
    even(B),
    true((
        mshare([[C],[E],[I],[H],[G],[F],[X],[D],[L],[K],[J],[Y],[P],[O],[N],[M],[Z]]),
        ground([A,B])
    )),
    even(C),
    true((
        mshare([[E],[I],[H],[G],[F],[X],[D],[L],[K],[J],[Y],[P],[O],[N],[M],[Z]]),
        ground([A,B,C])
    )),
    even(E),
    true((
        mshare([[I],[H],[G],[F],[X],[D],[L],[K],[J],[Y],[P],[O],[N],[M],[Z]]),
        ground([A,B,C,E])
    )),
    mult([C,B,A],E,[I,H,G,F|X]),
    true((
        mshare([[D],[L],[K],[J],[Y],[P],[O],[N],[M],[Z]]),
        ground([A,B,C,E,I,H,G,F,X])
    )),
    lefteven(F),
    true((
        mshare([[D],[L],[K],[J],[Y],[P],[O],[N],[M],[Z]]),
        ground([A,B,C,E,I,H,G,F,X])
    )),
    odd(G),
    true((
        mshare([[D],[L],[K],[J],[Y],[P],[O],[N],[M],[Z]]),
        ground([A,B,C,E,I,H,G,F,X])
    )),
    even(H),
    true((
        mshare([[D],[L],[K],[J],[Y],[P],[O],[N],[M],[Z]]),
        ground([A,B,C,E,I,H,G,F,X])
    )),
    even(I),
    true((
        mshare([[D],[L],[K],[J],[Y],[P],[O],[N],[M],[Z]]),
        ground([A,B,C,E,I,H,G,F,X])
    )),
    zero(X),
    true((
        mshare([[D],[L],[K],[J],[Y],[P],[O],[N],[M],[Z]]),
        ground([A,B,C,E,I,H,G,F,X])
    )),
    lefteven(D),
    true((
        mshare([[L],[K],[J],[Y],[P],[O],[N],[M],[Z]]),
        ground([A,B,C,E,I,H,G,F,X,D])
    )),
    mult([C,B,A],D,[L,K,J|Y]),
    true((
        mshare([[P],[O],[N],[M],[Z]]),
        ground([A,B,C,E,I,H,G,F,X,D,L,K,J,Y])
    )),
    lefteven(J),
    true((
        mshare([[P],[O],[N],[M],[Z]]),
        ground([A,B,C,E,I,H,G,F,X,D,L,K,J,Y])
    )),
    odd(K),
    true((
        mshare([[P],[O],[N],[M],[Z]]),
        ground([A,B,C,E,I,H,G,F,X,D,L,K,J,Y])
    )),
    even(L),
    true((
        mshare([[P],[O],[N],[M],[Z]]),
        ground([A,B,C,E,I,H,G,F,X,D,L,K,J,Y])
    )),
    zero(Y),
    true((
        mshare([[P],[O],[N],[M],[Z]]),
        ground([A,B,C,E,I,H,G,F,X,D,L,K,J,Y])
    )),
    sum([I,H,G,F],[0,L,K,J],[P,O,N,M|Z]),
    true(ground([A,B,C,E,I,H,G,F,X,D,L,K,J,Y,P,O,N,M,Z])),
    odd(M),
    true(ground([A,B,C,E,I,H,G,F,X,D,L,K,J,Y,P,O,N,M,Z])),
    odd(N),
    true(ground([A,B,C,E,I,H,G,F,X,D,L,K,J,Y,P,O,N,M,Z])),
    even(O),
    true(ground([A,B,C,E,I,H,G,F,X,D,L,K,J,Y,P,O,N,M,Z])),
    even(P),
    true(ground([A,B,C,E,I,H,G,F,X,D,L,K,J,Y,P,O,N,M,Z])),
    zero(Z),
    true(ground([A,B,C,E,I,H,G,F,X,D,L,K,J,Y,P,O,N,M,Z])).

:- true pred sum(AL,BL,CL)
   : ( (AL=[_A,_B,_C,_D]), (BL=[0,_E,_F,_G]), (CL=[_H,_I,_J,_K|_L]),
       mshare([[_H],[_I],[_J],[_K],[_L]]),
       ground([_A,_B,_C,_D,_E,_F,_G]) )
   => ground([_A,_B,_C,_D,_E,_F,_G,_H,_I,_J,_K,_L]).

sum(AL,BL,CL) :-
    true((
        mshare([[CL]]),
        ground([AL,BL])
    )),
    sum(AL,BL,0,CL),
    true(ground([AL,BL,CL])).

:- true pred sum(AL,BL,Carry,_A)
   : ( (Carry=0),
       mshare([[_A]]),
       ground([AL,BL]) )
   => ground([AL,BL,_A]).

:- true pred sum(AL,BL,Carry,_A)
   : ( (AL=[]),
       mshare([[_A]]),
       ground([BL,Carry]) )
   => ground([BL,Carry,_A]).

:- true pred sum(AL,BL,Carry,_A)
   : ( mshare([[_A]]),
       ground([AL,BL,Carry]) )
   => ground([AL,BL,Carry,_A]).

sum([A|AL],[B|BL],Carry,[C|CL]) :-
    !,
    true((
        mshare([[C],[C,CL],[CL],[X],[NewCarry]]),
        ground([Carry,A,AL,B,BL]),
        linear(X),
        linear(NewCarry)
    )),
    X is A+B+Carry,
    true((
        mshare([[C],[C,CL],[CL],[NewCarry]]),
        ground([Carry,A,AL,B,BL,X]),
        linear(NewCarry)
    )),
    C is X mod 10,
    true((
        mshare([[CL],[NewCarry]]),
        ground([Carry,A,AL,B,BL,C,X]),
        linear(NewCarry)
    )),
    NewCarry is X//10,
    true((
        mshare([[CL]]),
        ground([Carry,A,AL,B,BL,C,X,NewCarry])
    )),
    sum(AL,BL,NewCarry,CL),
    true(ground([Carry,A,AL,B,BL,C,CL,X,NewCarry])).
sum([],BL,0,BL) :-
    !,
    true(ground([BL])).
sum(AL,[],0,AL) :-
    !,
    true(ground([AL])).
sum([],[B|BL],Carry,[C|CL]) :-
    !,
    true((
        mshare([[C],[C,CL],[CL],[X],[NewCarry]]),
        ground([Carry,B,BL]),
        linear(X),
        linear(NewCarry)
    )),
    X is B+Carry,
    true((
        mshare([[C],[C,CL],[CL],[NewCarry]]),
        ground([Carry,B,BL,X]),
        linear(NewCarry)
    )),
    NewCarry is X//10,
    true((
        mshare([[C],[C,CL],[CL]]),
        ground([Carry,B,BL,X,NewCarry])
    )),
    C is X mod 10,
    true((
        mshare([[CL]]),
        ground([Carry,B,BL,C,X,NewCarry])
    )),
    sum([],BL,NewCarry,CL),
    true(ground([Carry,B,BL,C,CL,X,NewCarry])).
sum([A|AL],[],Carry,[C|CL]) :-
    !,
    true((
        mshare([[C],[C,CL],[CL],[X],[NewCarry]]),
        ground([Carry,A,AL]),
        linear(X),
        linear(NewCarry)
    )),
    X is A+Carry,
    true((
        mshare([[C],[C,CL],[CL],[NewCarry]]),
        ground([Carry,A,AL,X]),
        linear(NewCarry)
    )),
    NewCarry is X//10,
    true((
        mshare([[C],[C,CL],[CL]]),
        ground([Carry,A,AL,X,NewCarry])
    )),
    C is X mod 10,
    true((
        mshare([[CL]]),
        ground([Carry,A,AL,C,X,NewCarry])
    )),
    sum([],AL,NewCarry,CL),
    true(ground([Carry,A,AL,C,CL,X,NewCarry])).
sum([],[],Carry,[Carry]).

:- true pred mult(AL,D,BL)
   : ( (AL=[_A,_B,_C]), (BL=[_D,_E,_F|_G]),
       mshare([[_D],[_E],[_F],[_G]]),
       ground([D,_A,_B,_C]) )
   => ground([D,_A,_B,_C,_D,_E,_F,_G]).

:- true pred mult(AL,D,BL)
   : ( (AL=[_A,_B,_C]), (BL=[_D,_E,_F,_G|_H]),
       mshare([[_D],[_E],[_F],[_G],[_H]]),
       ground([D,_A,_B,_C]) )
   => ground([D,_A,_B,_C,_D,_E,_F,_G,_H]).

mult(AL,D,BL) :-
    true((
        mshare([[BL]]),
        ground([AL,D])
    )),
    mult(AL,D,0,BL),
    true(ground([AL,D,BL])).

:- true pred mult(_A,D,Carry,_B)
   : ( (Carry=0),
       mshare([[_B]]),
       ground([_A,D]) )
   => ground([_A,D,_B]).

:- true pred mult(_A,D,Carry,_B)
   : ( mshare([[_B]]),
       ground([_A,D,Carry]) )
   => ground([_A,D,Carry,_B]).

mult([A|AL],D,Carry,[B|BL]) :-
    true((
        mshare([[B],[B,BL],[BL],[X],[NewCarry]]),
        ground([D,Carry,A,AL]),
        linear(X),
        linear(NewCarry)
    )),
    X is A*D+Carry,
    true((
        mshare([[B],[B,BL],[BL],[NewCarry]]),
        ground([D,Carry,A,AL,X]),
        linear(NewCarry)
    )),
    B is X mod 10,
    true((
        mshare([[BL],[NewCarry]]),
        ground([D,Carry,A,AL,B,X]),
        linear(NewCarry)
    )),
    NewCarry is X//10,
    true((
        mshare([[BL]]),
        ground([D,Carry,A,AL,B,X,NewCarry])
    )),
    mult(AL,D,NewCarry,BL),
    true(ground([D,Carry,A,AL,B,BL,X,NewCarry])).
mult([],_1,Carry,[C,Cend]) :-
    true((
        mshare([[C],[C,Cend],[Cend]]),
        ground([_1,Carry])
    )),
    C is Carry mod 10,
    true((
        mshare([[Cend]]),
        ground([_1,Carry,C])
    )),
    Cend is Carry//10,
    true(ground([_1,Carry,C,Cend])).

:- true pred zero(_A)
   : ground([_A])
   => ground([_A]).

zero([]).
zero([0|L]) :-
    true(ground([L])),
    zero(L),
    true(ground([L])).

:- true pred odd(_A)
   : ground([_A])
   => ground([_A]).

:- true pred odd(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ground([_A]).

odd(1).
odd(3).
odd(5).
odd(7).
odd(9).

:- true pred even(_A)
   : ground([_A])
   => ground([_A]).

:- true pred even(_A)
   : mshare([[_A]])
   => ground([_A]).

even(0).
even(2).
even(4).
even(6).
even(8).

:- true pred lefteven(_A)
   : ground([_A])
   => ground([_A]).

:- true pred lefteven(_A)
   : mshare([[_A]])
   => ground([_A]).

lefteven(2).
lefteven(4).
lefteven(6).
lefteven(8).


