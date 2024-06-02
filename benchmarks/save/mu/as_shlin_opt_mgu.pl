:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(mu,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    mu,
    true(true).

:- true pred mu.

mu :-
    true((
        mshare([[_1]]),
        linear(_1)
    )),
    theorem([m,u,i,i,u],5,_1),
    !,
    true(ground([_1])).

:- true pred theorem(R,_1,_A)
   : ( (R=[m,u,i,i,u]), (_1=5),
       mshare([[_A]]),
       linear(_A) )
   => ground([_A]).

:- true pred theorem(R,_1,_A)
   : ( mshare([[R],[_A]]),
       ground([_1]), linear(R), linear(_A) )
   => ground([R,_1,_A]).

theorem([m,i],_1,[[a,m,i]]).
theorem(R,Depth,[[N|R]|P]) :-
    true((mshare([[R],[P],[N],[D],[S]]),ground([Depth]),linear(R),linear(P),linear(N),linear(D),linear(S);mshare([[P],[N],[D],[S]]),ground([R,Depth]),linear(P),linear(N),linear(D),linear(S))),
    Depth>0,
    true((mshare([[R],[P],[N],[D],[S]]),ground([Depth]),linear(R),linear(P),linear(N),linear(D),linear(S);mshare([[P],[N],[D],[S]]),ground([R,Depth]),linear(P),linear(N),linear(D),linear(S))),
    D is Depth-1,
    true((mshare([[R],[P],[N],[S]]),ground([Depth,D]),linear(R),linear(P),linear(N),linear(S);mshare([[P],[N],[S]]),ground([R,Depth,D]),linear(P),linear(N),linear(S))),
    theorem(S,D,P),
    true((mshare([[R],[N]]),ground([Depth,P,D,S]);mshare([[N]]),ground([R,Depth,P,D,S]))),
    rule(N,S,R),
    true(ground([R,Depth,P,N,D,S])).

:- true pred rule(_A,S,R)
   : ( mshare([[_A]]),
       ground([S,R]) )
   => ground([_A,S,R]).

:- true pred rule(_A,S,R)
   : ( mshare([[_A],[R]]),
       ground([S]) )
   => ground([_A,S,R]).

rule(1,S,R) :-
    true((mshare([[R]]),ground([S]);ground([S,R]))),
    rule1(S,R),
    true(ground([S,R])).
rule(2,S,R) :-
    true((mshare([[R]]),ground([S]);ground([S,R]))),
    rule2(S,R),
    true(ground([S,R])).
rule(3,S,R) :-
    true((mshare([[R]]),ground([S]);ground([S,R]))),
    rule3(S,R),
    true(ground([S,R])).
rule(4,S,R) :-
    true((mshare([[R]]),ground([S]);ground([S,R]))),
    rule4(S,R),
    true(ground([S,R])).

:- true pred rule1(_A,_B)
   : ground([_A,_B])
   => ground([_A,_B]).

:- true pred rule1(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]) )
   => ground([_A,_B]).

rule1([i],[i,u]).
rule1([H|X],[H|Y]) :-
    true((mshare([[Y]]),ground([H,X]);ground([H,X,Y]))),
    rule1(X,Y),
    true(ground([H,X,Y])).

:- true pred rule2(_A,_B)
   : ground([_A,_B])
   => ground([_A,_B]).

:- true pred rule2(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]) )
   => ground([_A,_B]).

rule2([m|X],[m|Y]) :-
    true((mshare([[Y]]),ground([X]);ground([X,Y]))),
    my_append(X,X,Y),
    true(ground([X,Y])).

:- true pred rule3(_A,_B)
   : ground([_A,_B])
   => ground([_A,_B]).

:- true pred rule3(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]) )
   => ground([_A,_B]).

rule3([i,i,i|X],[u|X]).
rule3([H|X],[H|Y]) :-
    true((mshare([[Y]]),ground([H,X]);ground([H,X,Y]))),
    rule3(X,Y),
    true(ground([H,X,Y])).

:- true pred rule4(_A,X)
   : ground([_A,X])
   => ground([_A,X]).

:- true pred rule4(_A,X)
   : ( mshare([[X]]),
       ground([_A]) )
   => ground([_A,X]).

rule4([u,u|X],X).
rule4([H|X],[H|Y]) :-
    true((mshare([[Y]]),ground([H,X]);ground([H,X,Y]))),
    rule4(X,Y),
    true(ground([H,X,Y])).

:- true pred my_append(_A,X,_B)
   : ( (_A=X), ground([_A,_B]) )
   => ground([_A,_B]).

:- true pred my_append(_A,X,_B)
   : ground([_A,X,_B])
   => ground([_A,X,_B]).

:- true pred my_append(_A,X,_B)
   : ( (_A=X),
       mshare([[_B]]),
       ground([_A]) )
   => ground([_A,_B]).

:- true pred my_append(_A,X,_B)
   : ( mshare([[_B]]),
       ground([_A,X]) )
   => ground([_A,X,_B]).

my_append([],X,X).
my_append([A|B],X,[A|B1]) :-
    true((mshare([[B1]]),ground([X,A,B]);ground([X,A,B,B1]))),
    my_append(B,X,B1),
    true(ground([X,A,B,B1])).


