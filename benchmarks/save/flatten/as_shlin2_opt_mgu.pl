:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(flatten,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true((
        mshare([[X],[Y],[A],[B],[C]]),
        linear(X),
        linear(Y),
        linear(A),
        linear(B),
        linear(C),
        shlin2([([X],[X]),([Y],[Y]),([A],[A]),([B],[B]),([C],[C])])
    )),
    eliminate_disjunctions([(a(A,B,C):-b(A);c(C))],X,Y,[]),
    true((
        mshare([[X],[X,Y],[X,Y,A],[X,Y,A,B],[X,Y,A,B,C],[X,Y,A,C],[X,Y,B],[X,Y,B,C],[X,Y,C],[X,A],[X,A,B],[X,A,B,C],[X,A,C],[X,B],[X,B,C],[X,C],[Y],[Y,A],[Y,A,B],[Y,A,B,C],[Y,A,C],[Y,B],[Y,B,C],[Y,C],[A],[A,B],[A,B,C],[A,C],[B],[B,C],[C]]),
        shlin2([([X],[]),([X,Y],[]),([X,Y,A],[]),([X,Y,A,B],[]),([X,Y,A,B,C],[]),([X,Y,A,C],[]),([X,Y,B],[]),([X,Y,B,C],[]),([X,Y,C],[]),([X,A],[]),([X,A,B],[]),([X,A,B,C],[]),([X,A,C],[]),([X,B],[]),([X,B,C],[]),([X,C],[]),([Y],[]),([Y,A],[]),([Y,A,B],[]),([Y,A,B,C],[]),([Y,A,C],[]),([Y,B],[]),([Y,B,C],[]),([Y,C],[]),([A],[]),([A,B],[]),([A,B,C],[]),([A,C],[]),([B],[]),([B,C],[]),([C],[])])
    )),
    inst_vars((X,Y)),
    true((
        mshare([[X],[X,Y],[X,Y,A],[X,Y,A,B],[X,Y,A,B,C],[X,Y,A,C],[X,Y,B],[X,Y,B,C],[X,Y,C],[X,A],[X,A,B],[X,A,B,C],[X,A,C],[X,B],[X,B,C],[X,C],[Y],[Y,A],[Y,A,B],[Y,A,B,C],[Y,A,C],[Y,B],[Y,B,C],[Y,C],[A],[A,B],[A,B,C],[A,C],[B],[B,C],[C]]),
        shlin2([([X],[]),([X,Y],[]),([X,Y,A],[]),([X,Y,A,B],[]),([X,Y,A,B,C],[]),([X,Y,A,C],[]),([X,Y,B],[]),([X,Y,B,C],[]),([X,Y,C],[]),([X,A],[]),([X,A,B],[]),([X,A,B,C],[]),([X,A,C],[]),([X,B],[]),([X,B,C],[]),([X,C],[]),([Y],[]),([Y,A],[]),([Y,A,B],[]),([Y,A,B,C],[]),([Y,A,C],[]),([Y,B],[]),([Y,B,C],[]),([Y,C],[]),([A],[]),([A,B],[]),([A,B,C],[]),([A,C],[]),([B],[]),([B,C],[]),([C],[])])
    )).
top.

:- true pred eliminate_disjunctions(OneProc,NewProc,NewClauses,Link)
   : ( (OneProc=[(a(_A,_B,_C):-b(_A);c(_C))]), (Link=[]),
       mshare([[NewProc],[NewClauses],[_A],[_B],[_C]]),
       linear(NewProc), linear(NewClauses), linear(_A), linear(_B), linear(_C), shlin2([([NewProc],[NewProc]),([NewClauses],[NewClauses]),([_A],[_A]),([_B],[_B]),([_C],[_C])]) )
   => ( mshare([[NewProc],[NewProc,NewClauses],[NewProc,NewClauses,_A],[NewProc,NewClauses,_A,_B],[NewProc,NewClauses,_A,_B,_C],[NewProc,NewClauses,_A,_C],[NewProc,NewClauses,_B],[NewProc,NewClauses,_B,_C],[NewProc,NewClauses,_C],[NewProc,_A],[NewProc,_A,_B],[NewProc,_A,_B,_C],[NewProc,_A,_C],[NewProc,_B],[NewProc,_B,_C],[NewProc,_C],[NewClauses],[NewClauses,_A],[NewClauses,_A,_B],[NewClauses,_A,_B,_C],[NewClauses,_A,_C],[NewClauses,_B],[NewClauses,_B,_C],[NewClauses,_C],[_A],[_A,_B],[_A,_B,_C],[_A,_C],[_B],[_B,_C],[_C]]),
        shlin2([([NewProc],[]),([NewProc,NewClauses],[]),([NewProc,NewClauses,_A],[]),([NewProc,NewClauses,_A,_B],[]),([NewProc,NewClauses,_A,_B,_C],[]),([NewProc,NewClauses,_A,_C],[]),([NewProc,NewClauses,_B],[]),([NewProc,NewClauses,_B,_C],[]),([NewProc,NewClauses,_C],[]),([NewProc,_A],[]),([NewProc,_A,_B],[]),([NewProc,_A,_B,_C],[]),([NewProc,_A,_C],[]),([NewProc,_B],[]),([NewProc,_B,_C],[]),([NewProc,_C],[]),([NewClauses],[]),([NewClauses,_A],[]),([NewClauses,_A,_B],[]),([NewClauses,_A,_B,_C],[]),([NewClauses,_A,_C],[]),([NewClauses,_B],[]),([NewClauses,_B,_C],[]),([NewClauses,_C],[]),([_A],[]),([_A,_B],[]),([_A,_B,_C],[]),([_A,_C],[]),([_B],[]),([_B,_C],[]),([_C],[])]) ).

eliminate_disjunctions(OneProc,NewProc,NewClauses,Link) :-
    true((
        mshare([[OneProc],[NewProc],[NewClauses],[Disj]]),
        ground([Link]),
        linear(NewProc),
        linear(NewClauses),
        linear(Disj),
        shlin2([([OneProc],[]),([NewProc],[NewProc]),([NewClauses],[NewClauses]),([Disj],[Disj])])
    )),
    gather_disj(OneProc,NewProc,Disj,[]),
    true((
        mshare([[OneProc,NewProc],[OneProc,NewProc,Disj],[OneProc,Disj],[NewProc,Disj],[NewClauses]]),
        ground([Link]),
        linear(NewClauses),
        shlin2([([OneProc,NewProc],[]),([OneProc,NewProc,Disj],[]),([OneProc,Disj],[]),([NewProc,Disj],[NewProc,Disj]),([NewClauses],[NewClauses])])
    )),
    treat_disj(Disj,NewClauses,Link),
    true((
        mshare([[OneProc,NewProc],[OneProc,NewProc,NewClauses,Disj],[OneProc,NewProc,Disj],[OneProc,NewClauses,Disj],[OneProc,Disj],[NewProc,NewClauses,Disj],[NewProc,Disj],[NewClauses]]),
        ground([Link]),
        shlin2([([OneProc,NewProc],[]),([OneProc,NewProc,NewClauses,Disj],[]),([OneProc,NewProc,Disj],[]),([OneProc,NewClauses,Disj],[]),([OneProc,Disj],[]),([NewProc,NewClauses,Disj],[]),([NewProc,Disj],[]),([NewClauses],[])])
    )).

:- true pred gather_disj(_A,NewProc,Link,_B)
   : ( (_B=[]),
       mshare([[_A],[NewProc],[Link]]),
       linear(NewProc), linear(Link), shlin2([([_A],[]),([NewProc],[NewProc]),([Link],[Link])]) )
   => ( mshare([[_A,NewProc],[_A,NewProc,Link],[_A,Link],[NewProc,Link]]),
        shlin2([([_A,NewProc],[]),([_A,NewProc,Link],[]),([_A,Link],[]),([NewProc,Link],[NewProc,Link])]) ).

:- true pred gather_disj(_A,NewProc,Link,_B)
   : ( mshare([[_A],[NewProc],[Link]]),
       ground([_B]), linear(NewProc), linear(Link), shlin2([([_A],[]),([NewProc],[NewProc]),([Link],[Link])]) )
   => ( mshare([[_A,NewProc],[_A,NewProc,Link],[_A,Link],[NewProc,Link]]),
        ground([_B]), shlin2([([_A,NewProc],[]),([_A,NewProc,Link],[]),([_A,Link],[]),([NewProc,Link],[NewProc,Link])]) ).

gather_disj([],[],Link,Link).
gather_disj([C|Cs],NewProc,Disj,Link) :-
    true((
        mshare([[NewProc],[Disj],[C],[C,Cs],[Cs],[NewC],[Rest],[NewCs]]),
        ground([Link]),
        linear(NewProc),
        linear(Disj),
        linear(NewC),
        linear(Rest),
        linear(NewCs),
        shlin2([([NewProc],[NewProc]),([Disj],[Disj]),([C],[]),([C,Cs],[]),([Cs],[]),([NewC],[NewC]),([Rest],[Rest]),([NewCs],[NewCs])])
    )),
    extract_disj(C,NewC,Disj,Rest),
    true((
        mshare([[NewProc],[Disj,C],[Disj,C,Cs],[Disj,C,Cs,NewC],[Disj,C,NewC],[Disj,NewC],[Disj,Rest],[C,Cs,NewC],[C,NewC],[Cs],[NewCs]]),
        ground([Link]),
        linear(NewProc),
        linear(Rest),
        linear(NewCs),
        shlin2([([NewProc],[NewProc]),([Disj,C],[]),([Disj,C,Cs],[]),([Disj,C,Cs,NewC],[]),([Disj,C,NewC],[]),([Disj,NewC],[Disj,NewC]),([Disj,Rest],[Disj,Rest]),([C,Cs,NewC],[]),([C,NewC],[]),([Cs],[]),([NewCs],[NewCs])])
    )),
    NewProc=[NewC|NewCs],
    true((
        mshare([[NewProc,Disj,C,Cs,NewC],[NewProc,Disj,C,NewC],[NewProc,Disj,NewC],[NewProc,C,Cs,NewC],[NewProc,C,NewC],[NewProc,NewCs],[Disj,C],[Disj,C,Cs],[Disj,Rest],[Cs]]),
        ground([Link]),
        linear(Rest),
        linear(NewCs),
        shlin2([([NewProc,Disj,C,Cs,NewC],[]),([NewProc,Disj,C,NewC],[]),([NewProc,Disj,NewC],[NewProc,Disj,NewC]),([NewProc,C,Cs,NewC],[]),([NewProc,C,NewC],[]),([NewProc,NewCs],[NewProc,NewCs]),([Disj,C],[]),([Disj,C,Cs],[]),([Disj,Rest],[Disj,Rest]),([Cs],[])])
    )),
    gather_disj(Cs,NewCs,Rest,Link),
    true((
        mshare([[NewProc,Disj,C,Cs,NewC,Rest],[NewProc,Disj,C,Cs,NewC,Rest,NewCs],[NewProc,Disj,C,Cs,NewC,NewCs],[NewProc,Disj,C,Cs,Rest,NewCs],[NewProc,Disj,C,Cs,NewCs],[NewProc,Disj,C,NewC],[NewProc,Disj,Cs,Rest,NewCs],[NewProc,Disj,NewC],[NewProc,Disj,Rest,NewCs],[NewProc,C,Cs,NewC,NewCs],[NewProc,C,NewC],[NewProc,Cs,NewCs],[Disj,C],[Disj,C,Cs,Rest],[Disj,Cs,Rest]]),
        ground([Link]),
        shlin2([([NewProc,Disj,C,Cs,NewC,Rest],[]),([NewProc,Disj,C,Cs,NewC,Rest,NewCs],[]),([NewProc,Disj,C,Cs,NewC,NewCs],[]),([NewProc,Disj,C,Cs,Rest,NewCs],[]),([NewProc,Disj,C,Cs,NewCs],[]),([NewProc,Disj,C,NewC],[]),([NewProc,Disj,Cs,Rest,NewCs],[]),([NewProc,Disj,NewC],[NewProc,Disj,NewC]),([NewProc,Disj,Rest,NewCs],[NewProc,Disj,Rest,NewCs]),([NewProc,C,Cs,NewC,NewCs],[]),([NewProc,C,NewC],[]),([NewProc,Cs,NewCs],[]),([Disj,C],[]),([Disj,C,Cs,Rest],[]),([Disj,Cs,Rest],[])])
    )).

:- true pred extract_disj(C,Head,Disj,Link)
   : ( mshare([[C],[Head],[Disj],[Link]]),
       linear(Head), linear(Disj), linear(Link), shlin2([([C],[]),([Head],[Head]),([Disj],[Disj]),([Link],[Link])]) )
   => ( mshare([[C,Head],[C,Head,Disj],[C,Disj],[Head,Disj],[Disj,Link]]),
        linear(Link), shlin2([([C,Head],[]),([C,Head,Disj],[]),([C,Disj],[]),([Head,Disj],[Head,Disj]),([Disj,Link],[Disj,Link])]) ).

extract_disj(C,(Head:-NewBody),Disj,Link) :-
    true((
        mshare([[C],[Disj],[Link],[Head],[NewBody],[Body],[CtrIn],[CtrOut]]),
        linear(Disj),
        linear(Link),
        linear(Head),
        linear(NewBody),
        linear(Body),
        linear(CtrIn),
        linear(CtrOut),
        shlin2([([C],[]),([Disj],[Disj]),([Link],[Link]),([Head],[Head]),([NewBody],[NewBody]),([Body],[Body]),([CtrIn],[CtrIn]),([CtrOut],[CtrOut])])
    )),
    C=(Head:-Body),
    !,
    true((
        mshare([[C,Head],[C,Head,Body],[C,Body],[Disj],[Link],[NewBody],[CtrIn],[CtrOut]]),
        linear(Disj),
        linear(Link),
        linear(NewBody),
        linear(CtrIn),
        linear(CtrOut),
        shlin2([([C,Head],[]),([C,Head,Body],[]),([C,Body],[]),([Disj],[Disj]),([Link],[Link]),([NewBody],[NewBody]),([CtrIn],[CtrIn]),([CtrOut],[CtrOut])])
    )),
    CtrIn=0,
    true((
        mshare([[C,Head],[C,Head,Body],[C,Body],[Disj],[Link],[NewBody],[CtrOut]]),
        ground([CtrIn]),
        linear(Disj),
        linear(Link),
        linear(NewBody),
        linear(CtrOut),
        shlin2([([C,Head],[]),([C,Head,Body],[]),([C,Body],[]),([Disj],[Disj]),([Link],[Link]),([NewBody],[NewBody]),([CtrOut],[CtrOut])])
    )),
    extract_disj(Body,NewBody,Disj,Link,C,CtrIn,CtrOut),
    true((
        mshare([[C,Disj,Head],[C,Disj,Head,NewBody,Body],[C,Disj,Head,Body],[C,Disj,NewBody,Body],[C,Disj,Body],[C,Head],[C,Head,NewBody,Body],[C,NewBody,Body],[Disj,Link],[Disj,NewBody]]),
        ground([CtrIn,CtrOut]),
        linear(Link),
        shlin2([([C,Disj,Head],[]),([C,Disj,Head,NewBody,Body],[]),([C,Disj,Head,Body],[]),([C,Disj,NewBody,Body],[]),([C,Disj,Body],[]),([C,Head],[]),([C,Head,NewBody,Body],[]),([C,NewBody,Body],[]),([Disj,Link],[Disj,Link]),([Disj,NewBody],[Disj,NewBody])])
    )).
extract_disj(Head,Head,Link,Link).

:- true pred extract_disj(Goal,X,Disj,Link,C,CtrIn,CtrOut)
   : ( mshare([[Goal,C],[X],[Disj],[Link],[C],[CtrOut]]),
       ground([CtrIn]), linear(X), linear(Disj), linear(Link), linear(CtrOut), shlin2([([Goal,C],[]),([X],[X]),([Disj],[Disj]),([Link],[Link]),([C],[]),([CtrOut],[CtrOut])]) )
   => ( mshare([[Goal,X,Disj,C],[Goal,X,C],[Goal,Disj,C],[X,Disj],[Disj,Link],[Disj,C],[C]]),
        ground([CtrIn,CtrOut]), linear(Link), shlin2([([Goal,X,Disj,C],[]),([Goal,X,C],[]),([Goal,Disj,C],[]),([X,Disj],[X,Disj]),([Disj,Link],[Disj,Link]),([Disj,C],[]),([C],[])]) ).

extract_disj((C1,C2),(NewC1,NewC2),Disj,Link,C,CtrIn,CtrOut) :-
    true((
        mshare([[Disj],[Link],[C],[C,C1],[C,C1,C2],[C,C2],[CtrOut],[NewC1],[NewC2],[Link1],[Ctr]]),
        ground([CtrIn]),
        linear(Disj),
        linear(Link),
        linear(CtrOut),
        linear(NewC1),
        linear(NewC2),
        linear(Link1),
        linear(Ctr),
        shlin2([([Disj],[Disj]),([Link],[Link]),([C],[]),([C,C1],[]),([C,C1,C2],[]),([C,C2],[]),([CtrOut],[CtrOut]),([NewC1],[NewC1]),([NewC2],[NewC2]),([Link1],[Link1]),([Ctr],[Ctr])])
    )),
    extract_disj(C1,NewC1,Disj,Link1,C,CtrIn,Ctr),
    true((
        mshare([[Disj,C],[Disj,C,C1],[Disj,C,C1,C2],[Disj,C,C1,C2,NewC1],[Disj,C,C1,NewC1],[Disj,C,C2],[Disj,NewC1],[Disj,Link1],[Link],[C],[C,C1,C2,NewC1],[C,C1,NewC1],[C,C2],[CtrOut],[NewC2]]),
        ground([CtrIn,Ctr]),
        linear(Link),
        linear(CtrOut),
        linear(NewC2),
        linear(Link1),
        shlin2([([Disj,C],[]),([Disj,C,C1],[]),([Disj,C,C1,C2],[]),([Disj,C,C1,C2,NewC1],[]),([Disj,C,C1,NewC1],[]),([Disj,C,C2],[]),([Disj,NewC1],[Disj,NewC1]),([Disj,Link1],[Disj,Link1]),([Link],[Link]),([C],[]),([C,C1,C2,NewC1],[]),([C,C1,NewC1],[]),([C,C2],[]),([CtrOut],[CtrOut]),([NewC2],[NewC2])])
    )),
    extract_disj(C2,NewC2,Link1,Link,C,Ctr,CtrOut),
    true((
        mshare([[Disj,Link,Link1],[Disj,C],[Disj,C,C1],[Disj,C,C1,C2,NewC1,NewC2],[Disj,C,C1,C2,NewC1,NewC2,Link1],[Disj,C,C1,C2,NewC1,Link1],[Disj,C,C1,C2,NewC2],[Disj,C,C1,C2,NewC2,Link1],[Disj,C,C1,C2,Link1],[Disj,C,C1,NewC1],[Disj,C,C1,NewC1,Link1],[Disj,C,C1,Link1],[Disj,C,C2,NewC2],[Disj,C,C2,NewC2,Link1],[Disj,C,C2,Link1],[Disj,C,Link1],[Disj,NewC1],[Disj,NewC2,Link1],[C],[C,C1,C2,NewC1,NewC2],[C,C1,NewC1],[C,C2,NewC2]]),
        ground([CtrIn,CtrOut,Ctr]),
        linear(Link),
        shlin2([([Disj,Link,Link1],[Disj,Link,Link1]),([Disj,C],[]),([Disj,C,C1],[]),([Disj,C,C1,C2,NewC1,NewC2],[]),([Disj,C,C1,C2,NewC1,NewC2,Link1],[]),([Disj,C,C1,C2,NewC1,Link1],[]),([Disj,C,C1,C2,NewC2],[]),([Disj,C,C1,C2,NewC2,Link1],[]),([Disj,C,C1,C2,Link1],[]),([Disj,C,C1,NewC1],[]),([Disj,C,C1,NewC1,Link1],[]),([Disj,C,C1,Link1],[]),([Disj,C,C2,NewC2],[]),([Disj,C,C2,NewC2,Link1],[]),([Disj,C,C2,Link1],[]),([Disj,C,Link1],[]),([Disj,NewC1],[Disj,NewC1]),([Disj,NewC2,Link1],[Disj,NewC2,Link1]),([C],[]),([C,C1,C2,NewC1,NewC2],[]),([C,C1,NewC1],[]),([C,C2,NewC2],[])])
    )).
extract_disj(Goal,X,Disj,Link,C,CtrIn,CtrOut) :-
    true((
        mshare([[Goal,C],[X],[Disj],[Link],[C],[CtrOut],[NewGoal]]),
        ground([CtrIn]),
        linear(X),
        linear(Disj),
        linear(Link),
        linear(CtrOut),
        linear(NewGoal),
        shlin2([([Goal,C],[]),([X],[X]),([Disj],[Disj]),([Link],[Link]),([C],[]),([CtrOut],[CtrOut]),([NewGoal],[NewGoal])])
    )),
    is_disj(Goal,NewGoal),
    !,
    true((
        mshare([[Goal,C,NewGoal],[X],[Disj],[Link],[C],[CtrOut]]),
        ground([CtrIn]),
        linear(X),
        linear(Disj),
        linear(Link),
        linear(CtrOut),
        shlin2([([Goal,C,NewGoal],[]),([X],[X]),([Disj],[Disj]),([Link],[Link]),([C],[]),([CtrOut],[CtrOut])])
    )),
    Disj=[disj(NewGoal,CtrIn,X,C)|Link],
    true((
        mshare([[Goal,Disj,C,NewGoal],[X,Disj],[Disj,Link],[Disj,C],[CtrOut]]),
        ground([CtrIn]),
        linear(X),
        linear(Link),
        linear(CtrOut),
        shlin2([([Goal,Disj,C,NewGoal],[]),([X,Disj],[X,Disj]),([Disj,Link],[Disj,Link]),([Disj,C],[]),([CtrOut],[CtrOut])])
    )),
    CtrOut is CtrIn+1,
    true((
        mshare([[Goal,Disj,C,NewGoal],[X,Disj],[Disj,Link],[Disj,C]]),
        ground([CtrIn,CtrOut]),
        linear(X),
        linear(Link),
        shlin2([([Goal,Disj,C,NewGoal],[]),([X,Disj],[X,Disj]),([Disj,Link],[Disj,Link]),([Disj,C],[])])
    )).
extract_disj(Goal,Goal,Link,Link,_1,CtrIn,CtrIn).

:- true pred is_disj(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_B), shlin2([([_A],[]),([_B],[_B])]) )
   => ( mshare([[_A,_B]]),
        shlin2([([_A,_B],[])]) ).

is_disj((C1->C2;C3),(C1,!,C2;C3)) :-
    !,
    true((
        mshare([[C3],[C3,C1],[C3,C1,C2],[C3,C2],[C1],[C1,C2],[C2]]),
        shlin2([([C3],[]),([C3,C1],[]),([C3,C1,C2],[]),([C3,C2],[]),([C1],[]),([C1,C2],[]),([C2],[])])
    )).
is_disj((C1;C2),(C1;C2)).
is_disj(not(C),(C,!,fail;true)).
is_disj(\+C,(C,!,fail;true)).
is_disj(C1\=C2,(C1=C2,!,fail;true)).

:- true pred treat_disj(_A,Link,_B)
   : ( mshare([[_A],[Link]]),
       ground([_B]), linear(Link), shlin2([([_A],[]),([Link],[Link])]) )
   => ( mshare([[_A],[_A,Link],[Link]]),
        ground([_B]), shlin2([([_A],[]),([_A,Link],[]),([Link],[])]) ).

treat_disj([],Link,Link).
treat_disj([disj((A;B),N,X,C)|Disjs],DummyClauses,Link) :-
    true((
        mshare([[DummyClauses],[Disjs],[Disjs,N],[Disjs,N,X],[Disjs,N,X,C],[Disjs,N,X,C,A],[Disjs,N,X,C,A,B],[Disjs,N,X,C,B],[Disjs,N,X,A],[Disjs,N,X,A,B],[Disjs,N,X,B],[Disjs,N,C],[Disjs,N,C,A],[Disjs,N,C,A,B],[Disjs,N,C,B],[Disjs,N,A],[Disjs,N,A,B],[Disjs,N,B],[Disjs,X],[Disjs,X,C],[Disjs,X,C,A],[Disjs,X,C,A,B],[Disjs,X,C,B],[Disjs,X,A],[Disjs,X,A,B],[Disjs,X,B],[Disjs,C],[Disjs,C,A],[Disjs,C,A,B],[Disjs,C,B],[Disjs,A],[Disjs,A,B],[Disjs,B],[N],[N,X],[N,X,C],[N,X,C,A],[N,X,C,A,B],[N,X,C,B],[N,X,A],[N,X,A,B],[N,X,B],[N,C],[N,C,A],[N,C,A,B],[N,C,B],[N,A],[N,A,B],[N,B],[X],[X,C],[X,C,A],[X,C,A,B],[X,C,B],[X,A],[X,A,B],[X,B],[C],[C,A],[C,A,B],[C,B],[A],[A,B],[B],[Vars],[CVars],[Args],[Name],[Rest]]),
        ground([Link]),
        linear(DummyClauses),
        linear(Vars),
        linear(CVars),
        linear(Args),
        linear(Name),
        linear(Rest),
        shlin2([([DummyClauses],[DummyClauses]),([Disjs],[]),([Disjs,N],[]),([Disjs,N,X],[]),([Disjs,N,X,C],[]),([Disjs,N,X,C,A],[]),([Disjs,N,X,C,A,B],[]),([Disjs,N,X,C,B],[]),([Disjs,N,X,A],[]),([Disjs,N,X,A,B],[]),([Disjs,N,X,B],[]),([Disjs,N,C],[]),([Disjs,N,C,A],[]),([Disjs,N,C,A,B],[]),([Disjs,N,C,B],[]),([Disjs,N,A],[]),([Disjs,N,A,B],[]),([Disjs,N,B],[]),([Disjs,X],[]),([Disjs,X,C],[]),([Disjs,X,C,A],[]),([Disjs,X,C,A,B],[]),([Disjs,X,C,B],[]),([Disjs,X,A],[]),([Disjs,X,A,B],[]),([Disjs,X,B],[]),([Disjs,C],[]),([Disjs,C,A],[]),([Disjs,C,A,B],[]),([Disjs,C,B],[]),([Disjs,A],[]),([Disjs,A,B],[]),([Disjs,B],[]),([N],[]),([N,X],[]),([N,X,C],[]),([N,X,C,A],[]),([N,X,C,A,B],[]),([N,X,C,B],[]),([N,X,A],[]),([N,X,A,B],[]),([N,X,B],[]),([N,C],[]),([N,C,A],[]),([N,C,A,B],[]),([N,C,B],[]),([N,A],[]),([N,A,B],[]),([N,B],[]),([X],[]),([X,C],[]),([X,C,A],[]),([X,C,A,B],[]),([X,C,B],[]),([X,A],[]),([X,A,B],[]),([X,B],[]),([C],[]),([C,A],[]),([C,A,B],[]),([C,B],[]),([A],[]),([A,B],[]),([B],[]),([Vars],[Vars]),([CVars],[CVars]),([Args],[Args]),([Name],[Name]),([Rest],[Rest])])
    )),
    find_vars((A;B),Vars),
    true((
        mshare([[DummyClauses],[Disjs],[Disjs,N],[Disjs,N,X],[Disjs,N,X,C],[Disjs,N,X,C,A],[Disjs,N,X,C,A,B],[Disjs,N,X,C,A,B,Vars],[Disjs,N,X,C,A,Vars],[Disjs,N,X,C,B],[Disjs,N,X,C,B,Vars],[Disjs,N,X,A],[Disjs,N,X,A,B],[Disjs,N,X,A,B,Vars],[Disjs,N,X,A,Vars],[Disjs,N,X,B],[Disjs,N,X,B,Vars],[Disjs,N,C],[Disjs,N,C,A],[Disjs,N,C,A,B],[Disjs,N,C,A,B,Vars],[Disjs,N,C,A,Vars],[Disjs,N,C,B],[Disjs,N,C,B,Vars],[Disjs,N,A],[Disjs,N,A,B],[Disjs,N,A,B,Vars],[Disjs,N,A,Vars],[Disjs,N,B],[Disjs,N,B,Vars],[Disjs,X],[Disjs,X,C],[Disjs,X,C,A],[Disjs,X,C,A,B],[Disjs,X,C,A,B,Vars],[Disjs,X,C,A,Vars],[Disjs,X,C,B],[Disjs,X,C,B,Vars],[Disjs,X,A],[Disjs,X,A,B],[Disjs,X,A,B,Vars],[Disjs,X,A,Vars],[Disjs,X,B],[Disjs,X,B,Vars],[Disjs,C],[Disjs,C,A],[Disjs,C,A,B],[Disjs,C,A,B,Vars],[Disjs,C,A,Vars],[Disjs,C,B],[Disjs,C,B,Vars],[Disjs,A],[Disjs,A,B],[Disjs,A,B,Vars],[Disjs,A,Vars],[Disjs,B],[Disjs,B,Vars],[N],[N,X],[N,X,C],[N,X,C,A],[N,X,C,A,B],[N,X,C,A,B,Vars],[N,X,C,A,Vars],[N,X,C,B],[N,X,C,B,Vars],[N,X,A],[N,X,A,B],[N,X,A,B,Vars],[N,X,A,Vars],[N,X,B],[N,X,B,Vars],[N,C],[N,C,A],[N,C,A,B],[N,C,A,B,Vars],[N,C,A,Vars],[N,C,B],[N,C,B,Vars],[N,A],[N,A,B],[N,A,B,Vars],[N,A,Vars],[N,B],[N,B,Vars],[X],[X,C],[X,C,A],[X,C,A,B],[X,C,A,B,Vars],[X,C,A,Vars],[X,C,B],[X,C,B,Vars],[X,A],[X,A,B],[X,A,B,Vars],[X,A,Vars],[X,B],[X,B,Vars],[C],[C,A],[C,A,B],[C,A,B,Vars],[C,A,Vars],[C,B],[C,B,Vars],[A],[A,B],[A,B,Vars],[A,Vars],[B],[B,Vars],[CVars],[Args],[Name],[Rest]]),
        ground([Link]),
        linear(DummyClauses),
        linear(CVars),
        linear(Args),
        linear(Name),
        linear(Rest),
        shlin2([([DummyClauses],[DummyClauses]),([Disjs],[]),([Disjs,N],[]),([Disjs,N,X],[]),([Disjs,N,X,C],[]),([Disjs,N,X,C,A],[]),([Disjs,N,X,C,A,B],[]),([Disjs,N,X,C,A,B,Vars],[]),([Disjs,N,X,C,A,Vars],[]),([Disjs,N,X,C,B],[]),([Disjs,N,X,C,B,Vars],[]),([Disjs,N,X,A],[]),([Disjs,N,X,A,B],[]),([Disjs,N,X,A,B,Vars],[]),([Disjs,N,X,A,Vars],[]),([Disjs,N,X,B],[]),([Disjs,N,X,B,Vars],[]),([Disjs,N,C],[]),([Disjs,N,C,A],[]),([Disjs,N,C,A,B],[]),([Disjs,N,C,A,B,Vars],[]),([Disjs,N,C,A,Vars],[]),([Disjs,N,C,B],[]),([Disjs,N,C,B,Vars],[]),([Disjs,N,A],[]),([Disjs,N,A,B],[]),([Disjs,N,A,B,Vars],[]),([Disjs,N,A,Vars],[]),([Disjs,N,B],[]),([Disjs,N,B,Vars],[]),([Disjs,X],[]),([Disjs,X,C],[]),([Disjs,X,C,A],[]),([Disjs,X,C,A,B],[]),([Disjs,X,C,A,B,Vars],[]),([Disjs,X,C,A,Vars],[]),([Disjs,X,C,B],[]),([Disjs,X,C,B,Vars],[]),([Disjs,X,A],[]),([Disjs,X,A,B],[]),([Disjs,X,A,B,Vars],[]),([Disjs,X,A,Vars],[]),([Disjs,X,B],[]),([Disjs,X,B,Vars],[]),([Disjs,C],[]),([Disjs,C,A],[]),([Disjs,C,A,B],[]),([Disjs,C,A,B,Vars],[]),([Disjs,C,A,Vars],[]),([Disjs,C,B],[]),([Disjs,C,B,Vars],[]),([Disjs,A],[]),([Disjs,A,B],[]),([Disjs,A,B,Vars],[]),([Disjs,A,Vars],[]),([Disjs,B],[]),([Disjs,B,Vars],[]),([N],[]),([N,X],[]),([N,X,C],[]),([N,X,C,A],[]),([N,X,C,A,B],[]),([N,X,C,A,B,Vars],[]),([N,X,C,A,Vars],[]),([N,X,C,B],[]),([N,X,C,B,Vars],[]),([N,X,A],[]),([N,X,A,B],[]),([N,X,A,B,Vars],[]),([N,X,A,Vars],[]),([N,X,B],[]),([N,X,B,Vars],[]),([N,C],[]),([N,C,A],[]),([N,C,A,B],[]),([N,C,A,B,Vars],[]),([N,C,A,Vars],[]),([N,C,B],[]),([N,C,B,Vars],[]),([N,A],[]),([N,A,B],[]),([N,A,B,Vars],[]),([N,A,Vars],[]),([N,B],[]),([N,B,Vars],[]),([X],[]),([X,C],[]),([X,C,A],[]),([X,C,A,B],[]),([X,C,A,B,Vars],[]),([X,C,A,Vars],[]),([X,C,B],[]),([X,C,B,Vars],[]),([X,A],[]),([X,A,B],[]),([X,A,B,Vars],[]),([X,A,Vars],[]),([X,B],[]),([X,B,Vars],[]),([C],[]),([C,A],[]),([C,A,B],[]),([C,A,B,Vars],[]),([C,A,Vars],[]),([C,B],[]),([C,B,Vars],[]),([A],[]),([A,B],[]),([A,B,Vars],[]),([A,Vars],[]),([B],[]),([B,Vars],[]),([CVars],[CVars]),([Args],[Args]),([Name],[Name]),([Rest],[Rest])])
    )),
    find_vars(C,CVars),
    true((
        mshare([[DummyClauses],[Disjs],[Disjs,N],[Disjs,N,X],[Disjs,N,X,C],[Disjs,N,X,C,A],[Disjs,N,X,C,A,B],[Disjs,N,X,C,A,B,Vars],[Disjs,N,X,C,A,B,Vars,CVars],[Disjs,N,X,C,A,B,CVars],[Disjs,N,X,C,A,Vars],[Disjs,N,X,C,A,Vars,CVars],[Disjs,N,X,C,A,CVars],[Disjs,N,X,C,B],[Disjs,N,X,C,B,Vars],[Disjs,N,X,C,B,Vars,CVars],[Disjs,N,X,C,B,CVars],[Disjs,N,X,C,CVars],[Disjs,N,X,A],[Disjs,N,X,A,B],[Disjs,N,X,A,B,Vars],[Disjs,N,X,A,Vars],[Disjs,N,X,B],[Disjs,N,X,B,Vars],[Disjs,N,C],[Disjs,N,C,A],[Disjs,N,C,A,B],[Disjs,N,C,A,B,Vars],[Disjs,N,C,A,B,Vars,CVars],[Disjs,N,C,A,B,CVars],[Disjs,N,C,A,Vars],[Disjs,N,C,A,Vars,CVars],[Disjs,N,C,A,CVars],[Disjs,N,C,B],[Disjs,N,C,B,Vars],[Disjs,N,C,B,Vars,CVars],[Disjs,N,C,B,CVars],[Disjs,N,C,CVars],[Disjs,N,A],[Disjs,N,A,B],[Disjs,N,A,B,Vars],[Disjs,N,A,Vars],[Disjs,N,B],[Disjs,N,B,Vars],[Disjs,X],[Disjs,X,C],[Disjs,X,C,A],[Disjs,X,C,A,B],[Disjs,X,C,A,B,Vars],[Disjs,X,C,A,B,Vars,CVars],[Disjs,X,C,A,B,CVars],[Disjs,X,C,A,Vars],[Disjs,X,C,A,Vars,CVars],[Disjs,X,C,A,CVars],[Disjs,X,C,B],[Disjs,X,C,B,Vars],[Disjs,X,C,B,Vars,CVars],[Disjs,X,C,B,CVars],[Disjs,X,C,CVars],[Disjs,X,A],[Disjs,X,A,B],[Disjs,X,A,B,Vars],[Disjs,X,A,Vars],[Disjs,X,B],[Disjs,X,B,Vars],[Disjs,C],[Disjs,C,A],[Disjs,C,A,B],[Disjs,C,A,B,Vars],[Disjs,C,A,B,Vars,CVars],[Disjs,C,A,B,CVars],[Disjs,C,A,Vars],[Disjs,C,A,Vars,CVars],[Disjs,C,A,CVars],[Disjs,C,B],[Disjs,C,B,Vars],[Disjs,C,B,Vars,CVars],[Disjs,C,B,CVars],[Disjs,C,CVars],[Disjs,A],[Disjs,A,B],[Disjs,A,B,Vars],[Disjs,A,Vars],[Disjs,B],[Disjs,B,Vars],[N],[N,X],[N,X,C],[N,X,C,A],[N,X,C,A,B],[N,X,C,A,B,Vars],[N,X,C,A,B,Vars,CVars],[N,X,C,A,B,CVars],[N,X,C,A,Vars],[N,X,C,A,Vars,CVars],[N,X,C,A,CVars],[N,X,C,B],[N,X,C,B,Vars],[N,X,C,B,Vars,CVars],[N,X,C,B,CVars],[N,X,C,CVars],[N,X,A],[N,X,A,B],[N,X,A,B,Vars],[N,X,A,Vars],[N,X,B],[N,X,B,Vars],[N,C],[N,C,A],[N,C,A,B],[N,C,A,B,Vars],[N,C,A,B,Vars,CVars],[N,C,A,B,CVars],[N,C,A,Vars],[N,C,A,Vars,CVars],[N,C,A,CVars],[N,C,B],[N,C,B,Vars],[N,C,B,Vars,CVars],[N,C,B,CVars],[N,C,CVars],[N,A],[N,A,B],[N,A,B,Vars],[N,A,Vars],[N,B],[N,B,Vars],[X],[X,C],[X,C,A],[X,C,A,B],[X,C,A,B,Vars],[X,C,A,B,Vars,CVars],[X,C,A,B,CVars],[X,C,A,Vars],[X,C,A,Vars,CVars],[X,C,A,CVars],[X,C,B],[X,C,B,Vars],[X,C,B,Vars,CVars],[X,C,B,CVars],[X,C,CVars],[X,A],[X,A,B],[X,A,B,Vars],[X,A,Vars],[X,B],[X,B,Vars],[C],[C,A],[C,A,B],[C,A,B,Vars],[C,A,B,Vars,CVars],[C,A,B,CVars],[C,A,Vars],[C,A,Vars,CVars],[C,A,CVars],[C,B],[C,B,Vars],[C,B,Vars,CVars],[C,B,CVars],[C,CVars],[A],[A,B],[A,B,Vars],[A,Vars],[B],[B,Vars],[Args],[Name],[Rest]]),
        ground([Link]),
        linear(DummyClauses),
        linear(Args),
        linear(Name),
        linear(Rest),
        shlin2([([DummyClauses],[DummyClauses]),([Disjs],[]),([Disjs,N],[]),([Disjs,N,X],[]),([Disjs,N,X,C],[]),([Disjs,N,X,C,A],[]),([Disjs,N,X,C,A,B],[]),([Disjs,N,X,C,A,B,Vars],[]),([Disjs,N,X,C,A,B,Vars,CVars],[]),([Disjs,N,X,C,A,B,CVars],[]),([Disjs,N,X,C,A,Vars],[]),([Disjs,N,X,C,A,Vars,CVars],[]),([Disjs,N,X,C,A,CVars],[]),([Disjs,N,X,C,B],[]),([Disjs,N,X,C,B,Vars],[]),([Disjs,N,X,C,B,Vars,CVars],[]),([Disjs,N,X,C,B,CVars],[]),([Disjs,N,X,C,CVars],[]),([Disjs,N,X,A],[]),([Disjs,N,X,A,B],[]),([Disjs,N,X,A,B,Vars],[]),([Disjs,N,X,A,Vars],[]),([Disjs,N,X,B],[]),([Disjs,N,X,B,Vars],[]),([Disjs,N,C],[]),([Disjs,N,C,A],[]),([Disjs,N,C,A,B],[]),([Disjs,N,C,A,B,Vars],[]),([Disjs,N,C,A,B,Vars,CVars],[]),([Disjs,N,C,A,B,CVars],[]),([Disjs,N,C,A,Vars],[]),([Disjs,N,C,A,Vars,CVars],[]),([Disjs,N,C,A,CVars],[]),([Disjs,N,C,B],[]),([Disjs,N,C,B,Vars],[]),([Disjs,N,C,B,Vars,CVars],[]),([Disjs,N,C,B,CVars],[]),([Disjs,N,C,CVars],[]),([Disjs,N,A],[]),([Disjs,N,A,B],[]),([Disjs,N,A,B,Vars],[]),([Disjs,N,A,Vars],[]),([Disjs,N,B],[]),([Disjs,N,B,Vars],[]),([Disjs,X],[]),([Disjs,X,C],[]),([Disjs,X,C,A],[]),([Disjs,X,C,A,B],[]),([Disjs,X,C,A,B,Vars],[]),([Disjs,X,C,A,B,Vars,CVars],[]),([Disjs,X,C,A,B,CVars],[]),([Disjs,X,C,A,Vars],[]),([Disjs,X,C,A,Vars,CVars],[]),([Disjs,X,C,A,CVars],[]),([Disjs,X,C,B],[]),([Disjs,X,C,B,Vars],[]),([Disjs,X,C,B,Vars,CVars],[]),([Disjs,X,C,B,CVars],[]),([Disjs,X,C,CVars],[]),([Disjs,X,A],[]),([Disjs,X,A,B],[]),([Disjs,X,A,B,Vars],[]),([Disjs,X,A,Vars],[]),([Disjs,X,B],[]),([Disjs,X,B,Vars],[]),([Disjs,C],[]),([Disjs,C,A],[]),([Disjs,C,A,B],[]),([Disjs,C,A,B,Vars],[]),([Disjs,C,A,B,Vars,CVars],[]),([Disjs,C,A,B,CVars],[]),([Disjs,C,A,Vars],[]),([Disjs,C,A,Vars,CVars],[]),([Disjs,C,A,CVars],[]),([Disjs,C,B],[]),([Disjs,C,B,Vars],[]),([Disjs,C,B,Vars,CVars],[]),([Disjs,C,B,CVars],[]),([Disjs,C,CVars],[]),([Disjs,A],[]),([Disjs,A,B],[]),([Disjs,A,B,Vars],[]),([Disjs,A,Vars],[]),([Disjs,B],[]),([Disjs,B,Vars],[]),([N],[]),([N,X],[]),([N,X,C],[]),([N,X,C,A],[]),([N,X,C,A,B],[]),([N,X,C,A,B,Vars],[]),([N,X,C,A,B,Vars,CVars],[]),([N,X,C,A,B,CVars],[]),([N,X,C,A,Vars],[]),([N,X,C,A,Vars,CVars],[]),([N,X,C,A,CVars],[]),([N,X,C,B],[]),([N,X,C,B,Vars],[]),([N,X,C,B,Vars,CVars],[]),([N,X,C,B,CVars],[]),([N,X,C,CVars],[]),([N,X,A],[]),([N,X,A,B],[]),([N,X,A,B,Vars],[]),([N,X,A,Vars],[]),([N,X,B],[]),([N,X,B,Vars],[]),([N,C],[]),([N,C,A],[]),([N,C,A,B],[]),([N,C,A,B,Vars],[]),([N,C,A,B,Vars,CVars],[]),([N,C,A,B,CVars],[]),([N,C,A,Vars],[]),([N,C,A,Vars,CVars],[]),([N,C,A,CVars],[]),([N,C,B],[]),([N,C,B,Vars],[]),([N,C,B,Vars,CVars],[]),([N,C,B,CVars],[]),([N,C,CVars],[]),([N,A],[]),([N,A,B],[]),([N,A,B,Vars],[]),([N,A,Vars],[]),([N,B],[]),([N,B,Vars],[]),([X],[]),([X,C],[]),([X,C,A],[]),([X,C,A,B],[]),([X,C,A,B,Vars],[]),([X,C,A,B,Vars,CVars],[]),([X,C,A,B,CVars],[]),([X,C,A,Vars],[]),([X,C,A,Vars,CVars],[]),([X,C,A,CVars],[]),([X,C,B],[]),([X,C,B,Vars],[]),([X,C,B,Vars,CVars],[]),([X,C,B,CVars],[]),([X,C,CVars],[]),([X,A],[]),([X,A,B],[]),([X,A,B,Vars],[]),([X,A,Vars],[]),([X,B],[]),([X,B,Vars],[]),([C],[]),([C,A],[]),([C,A,B],[]),([C,A,B,Vars],[]),([C,A,B,Vars,CVars],[]),([C,A,B,CVars],[]),([C,A,Vars],[]),([C,A,Vars,CVars],[]),([C,A,CVars],[]),([C,B],[]),([C,B,Vars],[]),([C,B,Vars,CVars],[]),([C,B,CVars],[]),([C,CVars],[]),([A],[]),([A,B],[]),([A,B,Vars],[]),([A,Vars],[]),([B],[]),([B,Vars],[]),([Args],[Args]),([Name],[Name]),([Rest],[Rest])])
    )),
    intersect_vars(Vars,CVars,Args),
    true((
        mshare([[DummyClauses],[Disjs],[Disjs,N],[Disjs,N,X],[Disjs,N,X,C],[Disjs,N,X,C,A],[Disjs,N,X,C,A,B],[Disjs,N,X,C,A,B,Vars],[Disjs,N,X,C,A,B,Vars,CVars],[Disjs,N,X,C,A,B,Vars,CVars,Args],[Disjs,N,X,C,A,B,CVars],[Disjs,N,X,C,A,Vars],[Disjs,N,X,C,A,Vars,CVars],[Disjs,N,X,C,A,Vars,CVars,Args],[Disjs,N,X,C,A,CVars],[Disjs,N,X,C,B],[Disjs,N,X,C,B,Vars],[Disjs,N,X,C,B,Vars,CVars],[Disjs,N,X,C,B,Vars,CVars,Args],[Disjs,N,X,C,B,CVars],[Disjs,N,X,C,CVars],[Disjs,N,X,A],[Disjs,N,X,A,B],[Disjs,N,X,A,B,Vars],[Disjs,N,X,A,Vars],[Disjs,N,X,B],[Disjs,N,X,B,Vars],[Disjs,N,C],[Disjs,N,C,A],[Disjs,N,C,A,B],[Disjs,N,C,A,B,Vars],[Disjs,N,C,A,B,Vars,CVars],[Disjs,N,C,A,B,Vars,CVars,Args],[Disjs,N,C,A,B,CVars],[Disjs,N,C,A,Vars],[Disjs,N,C,A,Vars,CVars],[Disjs,N,C,A,Vars,CVars,Args],[Disjs,N,C,A,CVars],[Disjs,N,C,B],[Disjs,N,C,B,Vars],[Disjs,N,C,B,Vars,CVars],[Disjs,N,C,B,Vars,CVars,Args],[Disjs,N,C,B,CVars],[Disjs,N,C,CVars],[Disjs,N,A],[Disjs,N,A,B],[Disjs,N,A,B,Vars],[Disjs,N,A,Vars],[Disjs,N,B],[Disjs,N,B,Vars],[Disjs,X],[Disjs,X,C],[Disjs,X,C,A],[Disjs,X,C,A,B],[Disjs,X,C,A,B,Vars],[Disjs,X,C,A,B,Vars,CVars],[Disjs,X,C,A,B,Vars,CVars,Args],[Disjs,X,C,A,B,CVars],[Disjs,X,C,A,Vars],[Disjs,X,C,A,Vars,CVars],[Disjs,X,C,A,Vars,CVars,Args],[Disjs,X,C,A,CVars],[Disjs,X,C,B],[Disjs,X,C,B,Vars],[Disjs,X,C,B,Vars,CVars],[Disjs,X,C,B,Vars,CVars,Args],[Disjs,X,C,B,CVars],[Disjs,X,C,CVars],[Disjs,X,A],[Disjs,X,A,B],[Disjs,X,A,B,Vars],[Disjs,X,A,Vars],[Disjs,X,B],[Disjs,X,B,Vars],[Disjs,C],[Disjs,C,A],[Disjs,C,A,B],[Disjs,C,A,B,Vars],[Disjs,C,A,B,Vars,CVars],[Disjs,C,A,B,Vars,CVars,Args],[Disjs,C,A,B,CVars],[Disjs,C,A,Vars],[Disjs,C,A,Vars,CVars],[Disjs,C,A,Vars,CVars,Args],[Disjs,C,A,CVars],[Disjs,C,B],[Disjs,C,B,Vars],[Disjs,C,B,Vars,CVars],[Disjs,C,B,Vars,CVars,Args],[Disjs,C,B,CVars],[Disjs,C,CVars],[Disjs,A],[Disjs,A,B],[Disjs,A,B,Vars],[Disjs,A,Vars],[Disjs,B],[Disjs,B,Vars],[N],[N,X],[N,X,C],[N,X,C,A],[N,X,C,A,B],[N,X,C,A,B,Vars],[N,X,C,A,B,Vars,CVars],[N,X,C,A,B,Vars,CVars,Args],[N,X,C,A,B,CVars],[N,X,C,A,Vars],[N,X,C,A,Vars,CVars],[N,X,C,A,Vars,CVars,Args],[N,X,C,A,CVars],[N,X,C,B],[N,X,C,B,Vars],[N,X,C,B,Vars,CVars],[N,X,C,B,Vars,CVars,Args],[N,X,C,B,CVars],[N,X,C,CVars],[N,X,A],[N,X,A,B],[N,X,A,B,Vars],[N,X,A,Vars],[N,X,B],[N,X,B,Vars],[N,C],[N,C,A],[N,C,A,B],[N,C,A,B,Vars],[N,C,A,B,Vars,CVars],[N,C,A,B,Vars,CVars,Args],[N,C,A,B,CVars],[N,C,A,Vars],[N,C,A,Vars,CVars],[N,C,A,Vars,CVars,Args],[N,C,A,CVars],[N,C,B],[N,C,B,Vars],[N,C,B,Vars,CVars],[N,C,B,Vars,CVars,Args],[N,C,B,CVars],[N,C,CVars],[N,A],[N,A,B],[N,A,B,Vars],[N,A,Vars],[N,B],[N,B,Vars],[X],[X,C],[X,C,A],[X,C,A,B],[X,C,A,B,Vars],[X,C,A,B,Vars,CVars],[X,C,A,B,Vars,CVars,Args],[X,C,A,B,CVars],[X,C,A,Vars],[X,C,A,Vars,CVars],[X,C,A,Vars,CVars,Args],[X,C,A,CVars],[X,C,B],[X,C,B,Vars],[X,C,B,Vars,CVars],[X,C,B,Vars,CVars,Args],[X,C,B,CVars],[X,C,CVars],[X,A],[X,A,B],[X,A,B,Vars],[X,A,Vars],[X,B],[X,B,Vars],[C],[C,A],[C,A,B],[C,A,B,Vars],[C,A,B,Vars,CVars],[C,A,B,Vars,CVars,Args],[C,A,B,CVars],[C,A,Vars],[C,A,Vars,CVars],[C,A,Vars,CVars,Args],[C,A,CVars],[C,B],[C,B,Vars],[C,B,Vars,CVars],[C,B,Vars,CVars,Args],[C,B,CVars],[C,CVars],[A],[A,B],[A,B,Vars],[A,Vars],[B],[B,Vars],[Name],[Rest]]),
        ground([Link]),
        linear(DummyClauses),
        linear(Name),
        linear(Rest),
        shlin2([([DummyClauses],[DummyClauses]),([Disjs],[]),([Disjs,N],[]),([Disjs,N,X],[]),([Disjs,N,X,C],[]),([Disjs,N,X,C,A],[]),([Disjs,N,X,C,A,B],[]),([Disjs,N,X,C,A,B,Vars],[]),([Disjs,N,X,C,A,B,Vars,CVars],[]),([Disjs,N,X,C,A,B,Vars,CVars,Args],[]),([Disjs,N,X,C,A,B,CVars],[]),([Disjs,N,X,C,A,Vars],[]),([Disjs,N,X,C,A,Vars,CVars],[]),([Disjs,N,X,C,A,Vars,CVars,Args],[]),([Disjs,N,X,C,A,CVars],[]),([Disjs,N,X,C,B],[]),([Disjs,N,X,C,B,Vars],[]),([Disjs,N,X,C,B,Vars,CVars],[]),([Disjs,N,X,C,B,Vars,CVars,Args],[]),([Disjs,N,X,C,B,CVars],[]),([Disjs,N,X,C,CVars],[]),([Disjs,N,X,A],[]),([Disjs,N,X,A,B],[]),([Disjs,N,X,A,B,Vars],[]),([Disjs,N,X,A,Vars],[]),([Disjs,N,X,B],[]),([Disjs,N,X,B,Vars],[]),([Disjs,N,C],[]),([Disjs,N,C,A],[]),([Disjs,N,C,A,B],[]),([Disjs,N,C,A,B,Vars],[]),([Disjs,N,C,A,B,Vars,CVars],[]),([Disjs,N,C,A,B,Vars,CVars,Args],[]),([Disjs,N,C,A,B,CVars],[]),([Disjs,N,C,A,Vars],[]),([Disjs,N,C,A,Vars,CVars],[]),([Disjs,N,C,A,Vars,CVars,Args],[]),([Disjs,N,C,A,CVars],[]),([Disjs,N,C,B],[]),([Disjs,N,C,B,Vars],[]),([Disjs,N,C,B,Vars,CVars],[]),([Disjs,N,C,B,Vars,CVars,Args],[]),([Disjs,N,C,B,CVars],[]),([Disjs,N,C,CVars],[]),([Disjs,N,A],[]),([Disjs,N,A,B],[]),([Disjs,N,A,B,Vars],[]),([Disjs,N,A,Vars],[]),([Disjs,N,B],[]),([Disjs,N,B,Vars],[]),([Disjs,X],[]),([Disjs,X,C],[]),([Disjs,X,C,A],[]),([Disjs,X,C,A,B],[]),([Disjs,X,C,A,B,Vars],[]),([Disjs,X,C,A,B,Vars,CVars],[]),([Disjs,X,C,A,B,Vars,CVars,Args],[]),([Disjs,X,C,A,B,CVars],[]),([Disjs,X,C,A,Vars],[]),([Disjs,X,C,A,Vars,CVars],[]),([Disjs,X,C,A,Vars,CVars,Args],[]),([Disjs,X,C,A,CVars],[]),([Disjs,X,C,B],[]),([Disjs,X,C,B,Vars],[]),([Disjs,X,C,B,Vars,CVars],[]),([Disjs,X,C,B,Vars,CVars,Args],[]),([Disjs,X,C,B,CVars],[]),([Disjs,X,C,CVars],[]),([Disjs,X,A],[]),([Disjs,X,A,B],[]),([Disjs,X,A,B,Vars],[]),([Disjs,X,A,Vars],[]),([Disjs,X,B],[]),([Disjs,X,B,Vars],[]),([Disjs,C],[]),([Disjs,C,A],[]),([Disjs,C,A,B],[]),([Disjs,C,A,B,Vars],[]),([Disjs,C,A,B,Vars,CVars],[]),([Disjs,C,A,B,Vars,CVars,Args],[]),([Disjs,C,A,B,CVars],[]),([Disjs,C,A,Vars],[]),([Disjs,C,A,Vars,CVars],[]),([Disjs,C,A,Vars,CVars,Args],[]),([Disjs,C,A,CVars],[]),([Disjs,C,B],[]),([Disjs,C,B,Vars],[]),([Disjs,C,B,Vars,CVars],[]),([Disjs,C,B,Vars,CVars,Args],[]),([Disjs,C,B,CVars],[]),([Disjs,C,CVars],[]),([Disjs,A],[]),([Disjs,A,B],[]),([Disjs,A,B,Vars],[]),([Disjs,A,Vars],[]),([Disjs,B],[]),([Disjs,B,Vars],[]),([N],[]),([N,X],[]),([N,X,C],[]),([N,X,C,A],[]),([N,X,C,A,B],[]),([N,X,C,A,B,Vars],[]),([N,X,C,A,B,Vars,CVars],[]),([N,X,C,A,B,Vars,CVars,Args],[]),([N,X,C,A,B,CVars],[]),([N,X,C,A,Vars],[]),([N,X,C,A,Vars,CVars],[]),([N,X,C,A,Vars,CVars,Args],[]),([N,X,C,A,CVars],[]),([N,X,C,B],[]),([N,X,C,B,Vars],[]),([N,X,C,B,Vars,CVars],[]),([N,X,C,B,Vars,CVars,Args],[]),([N,X,C,B,CVars],[]),([N,X,C,CVars],[]),([N,X,A],[]),([N,X,A,B],[]),([N,X,A,B,Vars],[]),([N,X,A,Vars],[]),([N,X,B],[]),([N,X,B,Vars],[]),([N,C],[]),([N,C,A],[]),([N,C,A,B],[]),([N,C,A,B,Vars],[]),([N,C,A,B,Vars,CVars],[]),([N,C,A,B,Vars,CVars,Args],[]),([N,C,A,B,CVars],[]),([N,C,A,Vars],[]),([N,C,A,Vars,CVars],[]),([N,C,A,Vars,CVars,Args],[]),([N,C,A,CVars],[]),([N,C,B],[]),([N,C,B,Vars],[]),([N,C,B,Vars,CVars],[]),([N,C,B,Vars,CVars,Args],[]),([N,C,B,CVars],[]),([N,C,CVars],[]),([N,A],[]),([N,A,B],[]),([N,A,B,Vars],[]),([N,A,Vars],[]),([N,B],[]),([N,B,Vars],[]),([X],[]),([X,C],[]),([X,C,A],[]),([X,C,A,B],[]),([X,C,A,B,Vars],[]),([X,C,A,B,Vars,CVars],[]),([X,C,A,B,Vars,CVars,Args],[]),([X,C,A,B,CVars],[]),([X,C,A,Vars],[]),([X,C,A,Vars,CVars],[]),([X,C,A,Vars,CVars,Args],[]),([X,C,A,CVars],[]),([X,C,B],[]),([X,C,B,Vars],[]),([X,C,B,Vars,CVars],[]),([X,C,B,Vars,CVars,Args],[]),([X,C,B,CVars],[]),([X,C,CVars],[]),([X,A],[]),([X,A,B],[]),([X,A,B,Vars],[]),([X,A,Vars],[]),([X,B],[]),([X,B,Vars],[]),([C],[]),([C,A],[]),([C,A,B],[]),([C,A,B,Vars],[]),([C,A,B,Vars,CVars],[]),([C,A,B,Vars,CVars,Args],[]),([C,A,B,CVars],[]),([C,A,Vars],[]),([C,A,Vars,CVars],[]),([C,A,Vars,CVars,Args],[]),([C,A,CVars],[]),([C,B],[]),([C,B,Vars],[]),([C,B,Vars,CVars],[]),([C,B,Vars,CVars,Args],[]),([C,B,CVars],[]),([C,CVars],[]),([A],[]),([A,B],[]),([A,B,Vars],[]),([A,Vars],[]),([B],[]),([B,Vars],[]),([Name],[Name]),([Rest],[Rest])])
    )),
    make_dummy_name(N,Name),
    true((
        mshare([[DummyClauses],[Disjs],[Disjs,X],[Disjs,X,C],[Disjs,X,C,A],[Disjs,X,C,A,B],[Disjs,X,C,A,B,Vars],[Disjs,X,C,A,B,Vars,CVars],[Disjs,X,C,A,B,Vars,CVars,Args],[Disjs,X,C,A,B,CVars],[Disjs,X,C,A,Vars],[Disjs,X,C,A,Vars,CVars],[Disjs,X,C,A,Vars,CVars,Args],[Disjs,X,C,A,CVars],[Disjs,X,C,B],[Disjs,X,C,B,Vars],[Disjs,X,C,B,Vars,CVars],[Disjs,X,C,B,Vars,CVars,Args],[Disjs,X,C,B,CVars],[Disjs,X,C,CVars],[Disjs,X,A],[Disjs,X,A,B],[Disjs,X,A,B,Vars],[Disjs,X,A,Vars],[Disjs,X,B],[Disjs,X,B,Vars],[Disjs,C],[Disjs,C,A],[Disjs,C,A,B],[Disjs,C,A,B,Vars],[Disjs,C,A,B,Vars,CVars],[Disjs,C,A,B,Vars,CVars,Args],[Disjs,C,A,B,CVars],[Disjs,C,A,Vars],[Disjs,C,A,Vars,CVars],[Disjs,C,A,Vars,CVars,Args],[Disjs,C,A,CVars],[Disjs,C,B],[Disjs,C,B,Vars],[Disjs,C,B,Vars,CVars],[Disjs,C,B,Vars,CVars,Args],[Disjs,C,B,CVars],[Disjs,C,CVars],[Disjs,A],[Disjs,A,B],[Disjs,A,B,Vars],[Disjs,A,Vars],[Disjs,B],[Disjs,B,Vars],[X],[X,C],[X,C,A],[X,C,A,B],[X,C,A,B,Vars],[X,C,A,B,Vars,CVars],[X,C,A,B,Vars,CVars,Args],[X,C,A,B,CVars],[X,C,A,Vars],[X,C,A,Vars,CVars],[X,C,A,Vars,CVars,Args],[X,C,A,CVars],[X,C,B],[X,C,B,Vars],[X,C,B,Vars,CVars],[X,C,B,Vars,CVars,Args],[X,C,B,CVars],[X,C,CVars],[X,A],[X,A,B],[X,A,B,Vars],[X,A,Vars],[X,B],[X,B,Vars],[C],[C,A],[C,A,B],[C,A,B,Vars],[C,A,B,Vars,CVars],[C,A,B,Vars,CVars,Args],[C,A,B,CVars],[C,A,Vars],[C,A,Vars,CVars],[C,A,Vars,CVars,Args],[C,A,CVars],[C,B],[C,B,Vars],[C,B,Vars,CVars],[C,B,Vars,CVars,Args],[C,B,CVars],[C,CVars],[A],[A,B],[A,B,Vars],[A,Vars],[B],[B,Vars],[Rest]]),
        ground([Link,N,Name]),
        linear(DummyClauses),
        linear(Rest),
        shlin2([([DummyClauses],[DummyClauses]),([Disjs],[]),([Disjs,X],[]),([Disjs,X,C],[]),([Disjs,X,C,A],[]),([Disjs,X,C,A,B],[]),([Disjs,X,C,A,B,Vars],[]),([Disjs,X,C,A,B,Vars,CVars],[]),([Disjs,X,C,A,B,Vars,CVars,Args],[]),([Disjs,X,C,A,B,CVars],[]),([Disjs,X,C,A,Vars],[]),([Disjs,X,C,A,Vars,CVars],[]),([Disjs,X,C,A,Vars,CVars,Args],[]),([Disjs,X,C,A,CVars],[]),([Disjs,X,C,B],[]),([Disjs,X,C,B,Vars],[]),([Disjs,X,C,B,Vars,CVars],[]),([Disjs,X,C,B,Vars,CVars,Args],[]),([Disjs,X,C,B,CVars],[]),([Disjs,X,C,CVars],[]),([Disjs,X,A],[]),([Disjs,X,A,B],[]),([Disjs,X,A,B,Vars],[]),([Disjs,X,A,Vars],[]),([Disjs,X,B],[]),([Disjs,X,B,Vars],[]),([Disjs,C],[]),([Disjs,C,A],[]),([Disjs,C,A,B],[]),([Disjs,C,A,B,Vars],[]),([Disjs,C,A,B,Vars,CVars],[]),([Disjs,C,A,B,Vars,CVars,Args],[]),([Disjs,C,A,B,CVars],[]),([Disjs,C,A,Vars],[]),([Disjs,C,A,Vars,CVars],[]),([Disjs,C,A,Vars,CVars,Args],[]),([Disjs,C,A,CVars],[]),([Disjs,C,B],[]),([Disjs,C,B,Vars],[]),([Disjs,C,B,Vars,CVars],[]),([Disjs,C,B,Vars,CVars,Args],[]),([Disjs,C,B,CVars],[]),([Disjs,C,CVars],[]),([Disjs,A],[]),([Disjs,A,B],[]),([Disjs,A,B,Vars],[]),([Disjs,A,Vars],[]),([Disjs,B],[]),([Disjs,B,Vars],[]),([X],[]),([X,C],[]),([X,C,A],[]),([X,C,A,B],[]),([X,C,A,B,Vars],[]),([X,C,A,B,Vars,CVars],[]),([X,C,A,B,Vars,CVars,Args],[]),([X,C,A,B,CVars],[]),([X,C,A,Vars],[]),([X,C,A,Vars,CVars],[]),([X,C,A,Vars,CVars,Args],[]),([X,C,A,CVars],[]),([X,C,B],[]),([X,C,B,Vars],[]),([X,C,B,Vars,CVars],[]),([X,C,B,Vars,CVars,Args],[]),([X,C,B,CVars],[]),([X,C,CVars],[]),([X,A],[]),([X,A,B],[]),([X,A,B,Vars],[]),([X,A,Vars],[]),([X,B],[]),([X,B,Vars],[]),([C],[]),([C,A],[]),([C,A,B],[]),([C,A,B,Vars],[]),([C,A,B,Vars,CVars],[]),([C,A,B,Vars,CVars,Args],[]),([C,A,B,CVars],[]),([C,A,Vars],[]),([C,A,Vars,CVars],[]),([C,A,Vars,CVars,Args],[]),([C,A,CVars],[]),([C,B],[]),([C,B,Vars],[]),([C,B,Vars,CVars],[]),([C,B,Vars,CVars,Args],[]),([C,B,CVars],[]),([C,CVars],[]),([A],[]),([A,B],[]),([A,B,Vars],[]),([A,Vars],[]),([B],[]),([B,Vars],[]),([Rest],[Rest])])
    )),
    X=..[Name|Args],
    true((
        mshare([[DummyClauses],[Disjs],[Disjs,X,C,A,B,Vars,CVars,Args],[Disjs,X,C,A,Vars,CVars,Args],[Disjs,X,C,B,Vars,CVars,Args],[Disjs,C],[Disjs,C,A],[Disjs,C,A,B],[Disjs,C,A,B,Vars],[Disjs,C,A,B,Vars,CVars],[Disjs,C,A,B,CVars],[Disjs,C,A,Vars],[Disjs,C,A,Vars,CVars],[Disjs,C,A,CVars],[Disjs,C,B],[Disjs,C,B,Vars],[Disjs,C,B,Vars,CVars],[Disjs,C,B,CVars],[Disjs,C,CVars],[Disjs,A],[Disjs,A,B],[Disjs,A,B,Vars],[Disjs,A,Vars],[Disjs,B],[Disjs,B,Vars],[X,C,A,B,Vars,CVars,Args],[X,C,A,Vars,CVars,Args],[X,C,B,Vars,CVars,Args],[C],[C,A],[C,A,B],[C,A,B,Vars],[C,A,B,Vars,CVars],[C,A,B,CVars],[C,A,Vars],[C,A,Vars,CVars],[C,A,CVars],[C,B],[C,B,Vars],[C,B,Vars,CVars],[C,B,CVars],[C,CVars],[A],[A,B],[A,B,Vars],[A,Vars],[B],[B,Vars],[Rest]]),
        ground([Link,N,Name]),
        linear(DummyClauses),
        linear(Rest),
        shlin2([([DummyClauses],[DummyClauses]),([Disjs],[]),([Disjs,X,C,A,B,Vars,CVars,Args],[]),([Disjs,X,C,A,Vars,CVars,Args],[]),([Disjs,X,C,B,Vars,CVars,Args],[]),([Disjs,C],[]),([Disjs,C,A],[]),([Disjs,C,A,B],[]),([Disjs,C,A,B,Vars],[]),([Disjs,C,A,B,Vars,CVars],[]),([Disjs,C,A,B,CVars],[]),([Disjs,C,A,Vars],[]),([Disjs,C,A,Vars,CVars],[]),([Disjs,C,A,CVars],[]),([Disjs,C,B],[]),([Disjs,C,B,Vars],[]),([Disjs,C,B,Vars,CVars],[]),([Disjs,C,B,CVars],[]),([Disjs,C,CVars],[]),([Disjs,A],[]),([Disjs,A,B],[]),([Disjs,A,B,Vars],[]),([Disjs,A,Vars],[]),([Disjs,B],[]),([Disjs,B,Vars],[]),([X,C,A,B,Vars,CVars,Args],[]),([X,C,A,Vars,CVars,Args],[]),([X,C,B,Vars,CVars,Args],[]),([C],[]),([C,A],[]),([C,A,B],[]),([C,A,B,Vars],[]),([C,A,B,Vars,CVars],[]),([C,A,B,CVars],[]),([C,A,Vars],[]),([C,A,Vars,CVars],[]),([C,A,CVars],[]),([C,B],[]),([C,B,Vars],[]),([C,B,Vars,CVars],[]),([C,B,CVars],[]),([C,CVars],[]),([A],[]),([A,B],[]),([A,B,Vars],[]),([A,Vars],[]),([B],[]),([B,Vars],[]),([Rest],[Rest])])
    )),
    make_dummy_clauses((A;B),X,DummyClauses,Rest),
    true((
        mshare([[DummyClauses],[DummyClauses,Disjs,X,C,A,B,Vars,CVars,Args],[DummyClauses,Disjs,X,C,A,Vars,CVars,Args],[DummyClauses,Disjs,X,C,B,Vars,CVars,Args],[DummyClauses,Disjs,C,A],[DummyClauses,Disjs,C,A,B],[DummyClauses,Disjs,C,A,B,Vars],[DummyClauses,Disjs,C,A,B,Vars,CVars],[DummyClauses,Disjs,C,A,B,CVars],[DummyClauses,Disjs,C,A,Vars],[DummyClauses,Disjs,C,A,Vars,CVars],[DummyClauses,Disjs,C,A,CVars],[DummyClauses,Disjs,C,B],[DummyClauses,Disjs,C,B,Vars],[DummyClauses,Disjs,C,B,Vars,CVars],[DummyClauses,Disjs,C,B,CVars],[DummyClauses,Disjs,A],[DummyClauses,Disjs,A,B],[DummyClauses,Disjs,A,B,Vars],[DummyClauses,Disjs,A,Vars],[DummyClauses,Disjs,B],[DummyClauses,Disjs,B,Vars],[DummyClauses,X,C,A,B,Vars,CVars,Args],[DummyClauses,X,C,A,Vars,CVars,Args],[DummyClauses,X,C,B,Vars,CVars,Args],[DummyClauses,C,A],[DummyClauses,C,A,B],[DummyClauses,C,A,B,Vars],[DummyClauses,C,A,B,Vars,CVars],[DummyClauses,C,A,B,CVars],[DummyClauses,C,A,Vars],[DummyClauses,C,A,Vars,CVars],[DummyClauses,C,A,CVars],[DummyClauses,C,B],[DummyClauses,C,B,Vars],[DummyClauses,C,B,Vars,CVars],[DummyClauses,C,B,CVars],[DummyClauses,A],[DummyClauses,A,B],[DummyClauses,A,B,Vars],[DummyClauses,A,Vars],[DummyClauses,B],[DummyClauses,B,Vars],[DummyClauses,Rest],[Disjs],[Disjs,X,C,A,B,Vars,CVars,Args],[Disjs,X,C,A,Vars,CVars,Args],[Disjs,X,C,B,Vars,CVars,Args],[Disjs,C],[Disjs,C,A],[Disjs,C,A,B],[Disjs,C,A,B,Vars],[Disjs,C,A,B,Vars,CVars],[Disjs,C,A,B,CVars],[Disjs,C,A,Vars],[Disjs,C,A,Vars,CVars],[Disjs,C,A,CVars],[Disjs,C,B],[Disjs,C,B,Vars],[Disjs,C,B,Vars,CVars],[Disjs,C,B,CVars],[Disjs,C,CVars],[Disjs,A],[Disjs,A,B],[Disjs,A,B,Vars],[Disjs,A,Vars],[Disjs,B],[Disjs,B,Vars],[X,C,A,B,Vars,CVars,Args],[X,C,A,Vars,CVars,Args],[X,C,B,Vars,CVars,Args],[C],[C,A],[C,A,B],[C,A,B,Vars],[C,A,B,Vars,CVars],[C,A,B,CVars],[C,A,Vars],[C,A,Vars,CVars],[C,A,CVars],[C,B],[C,B,Vars],[C,B,Vars,CVars],[C,B,CVars],[C,CVars],[A],[A,B],[A,B,Vars],[A,Vars],[B],[B,Vars]]),
        ground([Link,N,Name]),
        linear(Rest),
        shlin2([([DummyClauses],[]),([DummyClauses,Disjs,X,C,A,B,Vars,CVars,Args],[]),([DummyClauses,Disjs,X,C,A,Vars,CVars,Args],[]),([DummyClauses,Disjs,X,C,B,Vars,CVars,Args],[]),([DummyClauses,Disjs,C,A],[]),([DummyClauses,Disjs,C,A,B],[]),([DummyClauses,Disjs,C,A,B,Vars],[]),([DummyClauses,Disjs,C,A,B,Vars,CVars],[]),([DummyClauses,Disjs,C,A,B,CVars],[]),([DummyClauses,Disjs,C,A,Vars],[]),([DummyClauses,Disjs,C,A,Vars,CVars],[]),([DummyClauses,Disjs,C,A,CVars],[]),([DummyClauses,Disjs,C,B],[]),([DummyClauses,Disjs,C,B,Vars],[]),([DummyClauses,Disjs,C,B,Vars,CVars],[]),([DummyClauses,Disjs,C,B,CVars],[]),([DummyClauses,Disjs,A],[]),([DummyClauses,Disjs,A,B],[]),([DummyClauses,Disjs,A,B,Vars],[]),([DummyClauses,Disjs,A,Vars],[]),([DummyClauses,Disjs,B],[]),([DummyClauses,Disjs,B,Vars],[]),([DummyClauses,X,C,A,B,Vars,CVars,Args],[]),([DummyClauses,X,C,A,Vars,CVars,Args],[]),([DummyClauses,X,C,B,Vars,CVars,Args],[]),([DummyClauses,C,A],[]),([DummyClauses,C,A,B],[]),([DummyClauses,C,A,B,Vars],[]),([DummyClauses,C,A,B,Vars,CVars],[]),([DummyClauses,C,A,B,CVars],[]),([DummyClauses,C,A,Vars],[]),([DummyClauses,C,A,Vars,CVars],[]),([DummyClauses,C,A,CVars],[]),([DummyClauses,C,B],[]),([DummyClauses,C,B,Vars],[]),([DummyClauses,C,B,Vars,CVars],[]),([DummyClauses,C,B,CVars],[]),([DummyClauses,A],[]),([DummyClauses,A,B],[]),([DummyClauses,A,B,Vars],[]),([DummyClauses,A,Vars],[]),([DummyClauses,B],[]),([DummyClauses,B,Vars],[]),([DummyClauses,Rest],[DummyClauses,Rest]),([Disjs],[]),([Disjs,X,C,A,B,Vars,CVars,Args],[]),([Disjs,X,C,A,Vars,CVars,Args],[]),([Disjs,X,C,B,Vars,CVars,Args],[]),([Disjs,C],[]),([Disjs,C,A],[]),([Disjs,C,A,B],[]),([Disjs,C,A,B,Vars],[]),([Disjs,C,A,B,Vars,CVars],[]),([Disjs,C,A,B,CVars],[]),([Disjs,C,A,Vars],[]),([Disjs,C,A,Vars,CVars],[]),([Disjs,C,A,CVars],[]),([Disjs,C,B],[]),([Disjs,C,B,Vars],[]),([Disjs,C,B,Vars,CVars],[]),([Disjs,C,B,CVars],[]),([Disjs,C,CVars],[]),([Disjs,A],[]),([Disjs,A,B],[]),([Disjs,A,B,Vars],[]),([Disjs,A,Vars],[]),([Disjs,B],[]),([Disjs,B,Vars],[]),([X,C,A,B,Vars,CVars,Args],[]),([X,C,A,Vars,CVars,Args],[]),([X,C,B,Vars,CVars,Args],[]),([C],[]),([C,A],[]),([C,A,B],[]),([C,A,B,Vars],[]),([C,A,B,Vars,CVars],[]),([C,A,B,CVars],[]),([C,A,Vars],[]),([C,A,Vars,CVars],[]),([C,A,CVars],[]),([C,B],[]),([C,B,Vars],[]),([C,B,Vars,CVars],[]),([C,B,CVars],[]),([C,CVars],[]),([A],[]),([A,B],[]),([A,B,Vars],[]),([A,Vars],[]),([B],[]),([B,Vars],[])])
    )),
    treat_disj(Disjs,Rest,Link),
    true((
        mshare([[DummyClauses],[DummyClauses,Disjs,X,C,A,B,Vars,CVars,Args],[DummyClauses,Disjs,X,C,A,B,Vars,CVars,Args,Rest],[DummyClauses,Disjs,X,C,A,Vars,CVars,Args],[DummyClauses,Disjs,X,C,A,Vars,CVars,Args,Rest],[DummyClauses,Disjs,X,C,B,Vars,CVars,Args],[DummyClauses,Disjs,X,C,B,Vars,CVars,Args,Rest],[DummyClauses,Disjs,C,A],[DummyClauses,Disjs,C,A,B],[DummyClauses,Disjs,C,A,B,Vars],[DummyClauses,Disjs,C,A,B,Vars,CVars],[DummyClauses,Disjs,C,A,B,Vars,CVars,Rest],[DummyClauses,Disjs,C,A,B,Vars,Rest],[DummyClauses,Disjs,C,A,B,CVars],[DummyClauses,Disjs,C,A,B,CVars,Rest],[DummyClauses,Disjs,C,A,B,Rest],[DummyClauses,Disjs,C,A,Vars],[DummyClauses,Disjs,C,A,Vars,CVars],[DummyClauses,Disjs,C,A,Vars,CVars,Rest],[DummyClauses,Disjs,C,A,Vars,Rest],[DummyClauses,Disjs,C,A,CVars],[DummyClauses,Disjs,C,A,CVars,Rest],[DummyClauses,Disjs,C,A,Rest],[DummyClauses,Disjs,C,B],[DummyClauses,Disjs,C,B,Vars],[DummyClauses,Disjs,C,B,Vars,CVars],[DummyClauses,Disjs,C,B,Vars,CVars,Rest],[DummyClauses,Disjs,C,B,Vars,Rest],[DummyClauses,Disjs,C,B,CVars],[DummyClauses,Disjs,C,B,CVars,Rest],[DummyClauses,Disjs,C,B,Rest],[DummyClauses,Disjs,C,CVars,Rest],[DummyClauses,Disjs,C,Rest],[DummyClauses,Disjs,A],[DummyClauses,Disjs,A,B],[DummyClauses,Disjs,A,B,Vars],[DummyClauses,Disjs,A,B,Vars,Rest],[DummyClauses,Disjs,A,B,Rest],[DummyClauses,Disjs,A,Vars],[DummyClauses,Disjs,A,Vars,Rest],[DummyClauses,Disjs,A,Rest],[DummyClauses,Disjs,B],[DummyClauses,Disjs,B,Vars],[DummyClauses,Disjs,B,Vars,Rest],[DummyClauses,Disjs,B,Rest],[DummyClauses,Disjs,Rest],[DummyClauses,X,C,A,B,Vars,CVars,Args],[DummyClauses,X,C,A,Vars,CVars,Args],[DummyClauses,X,C,B,Vars,CVars,Args],[DummyClauses,C,A],[DummyClauses,C,A,B],[DummyClauses,C,A,B,Vars],[DummyClauses,C,A,B,Vars,CVars],[DummyClauses,C,A,B,CVars],[DummyClauses,C,A,Vars],[DummyClauses,C,A,Vars,CVars],[DummyClauses,C,A,CVars],[DummyClauses,C,B],[DummyClauses,C,B,Vars],[DummyClauses,C,B,Vars,CVars],[DummyClauses,C,B,CVars],[DummyClauses,A],[DummyClauses,A,B],[DummyClauses,A,B,Vars],[DummyClauses,A,Vars],[DummyClauses,B],[DummyClauses,B,Vars],[DummyClauses,Rest],[Disjs],[Disjs,X,C,A,B,Vars,CVars,Args],[Disjs,X,C,A,Vars,CVars,Args],[Disjs,X,C,B,Vars,CVars,Args],[Disjs,C],[Disjs,C,A],[Disjs,C,A,B],[Disjs,C,A,B,Vars],[Disjs,C,A,B,Vars,CVars],[Disjs,C,A,B,CVars],[Disjs,C,A,Vars],[Disjs,C,A,Vars,CVars],[Disjs,C,A,CVars],[Disjs,C,B],[Disjs,C,B,Vars],[Disjs,C,B,Vars,CVars],[Disjs,C,B,CVars],[Disjs,C,CVars],[Disjs,A],[Disjs,A,B],[Disjs,A,B,Vars],[Disjs,A,Vars],[Disjs,B],[Disjs,B,Vars],[X,C,A,B,Vars,CVars,Args],[X,C,A,Vars,CVars,Args],[X,C,B,Vars,CVars,Args],[C],[C,A],[C,A,B],[C,A,B,Vars],[C,A,B,Vars,CVars],[C,A,B,CVars],[C,A,Vars],[C,A,Vars,CVars],[C,A,CVars],[C,B],[C,B,Vars],[C,B,Vars,CVars],[C,B,CVars],[C,CVars],[A],[A,B],[A,B,Vars],[A,Vars],[B],[B,Vars]]),
        ground([Link,N,Name]),
        shlin2([([DummyClauses],[]),([DummyClauses,Disjs,X,C,A,B,Vars,CVars,Args],[]),([DummyClauses,Disjs,X,C,A,B,Vars,CVars,Args,Rest],[]),([DummyClauses,Disjs,X,C,A,Vars,CVars,Args],[]),([DummyClauses,Disjs,X,C,A,Vars,CVars,Args,Rest],[]),([DummyClauses,Disjs,X,C,B,Vars,CVars,Args],[]),([DummyClauses,Disjs,X,C,B,Vars,CVars,Args,Rest],[]),([DummyClauses,Disjs,C,A],[]),([DummyClauses,Disjs,C,A,B],[]),([DummyClauses,Disjs,C,A,B,Vars],[]),([DummyClauses,Disjs,C,A,B,Vars,CVars],[]),([DummyClauses,Disjs,C,A,B,Vars,CVars,Rest],[]),([DummyClauses,Disjs,C,A,B,Vars,Rest],[]),([DummyClauses,Disjs,C,A,B,CVars],[]),([DummyClauses,Disjs,C,A,B,CVars,Rest],[]),([DummyClauses,Disjs,C,A,B,Rest],[]),([DummyClauses,Disjs,C,A,Vars],[]),([DummyClauses,Disjs,C,A,Vars,CVars],[]),([DummyClauses,Disjs,C,A,Vars,CVars,Rest],[]),([DummyClauses,Disjs,C,A,Vars,Rest],[]),([DummyClauses,Disjs,C,A,CVars],[]),([DummyClauses,Disjs,C,A,CVars,Rest],[]),([DummyClauses,Disjs,C,A,Rest],[]),([DummyClauses,Disjs,C,B],[]),([DummyClauses,Disjs,C,B,Vars],[]),([DummyClauses,Disjs,C,B,Vars,CVars],[]),([DummyClauses,Disjs,C,B,Vars,CVars,Rest],[]),([DummyClauses,Disjs,C,B,Vars,Rest],[]),([DummyClauses,Disjs,C,B,CVars],[]),([DummyClauses,Disjs,C,B,CVars,Rest],[]),([DummyClauses,Disjs,C,B,Rest],[]),([DummyClauses,Disjs,C,CVars,Rest],[]),([DummyClauses,Disjs,C,Rest],[]),([DummyClauses,Disjs,A],[]),([DummyClauses,Disjs,A,B],[]),([DummyClauses,Disjs,A,B,Vars],[]),([DummyClauses,Disjs,A,B,Vars,Rest],[]),([DummyClauses,Disjs,A,B,Rest],[]),([DummyClauses,Disjs,A,Vars],[]),([DummyClauses,Disjs,A,Vars,Rest],[]),([DummyClauses,Disjs,A,Rest],[]),([DummyClauses,Disjs,B],[]),([DummyClauses,Disjs,B,Vars],[]),([DummyClauses,Disjs,B,Vars,Rest],[]),([DummyClauses,Disjs,B,Rest],[]),([DummyClauses,Disjs,Rest],[]),([DummyClauses,X,C,A,B,Vars,CVars,Args],[]),([DummyClauses,X,C,A,Vars,CVars,Args],[]),([DummyClauses,X,C,B,Vars,CVars,Args],[]),([DummyClauses,C,A],[]),([DummyClauses,C,A,B],[]),([DummyClauses,C,A,B,Vars],[]),([DummyClauses,C,A,B,Vars,CVars],[]),([DummyClauses,C,A,B,CVars],[]),([DummyClauses,C,A,Vars],[]),([DummyClauses,C,A,Vars,CVars],[]),([DummyClauses,C,A,CVars],[]),([DummyClauses,C,B],[]),([DummyClauses,C,B,Vars],[]),([DummyClauses,C,B,Vars,CVars],[]),([DummyClauses,C,B,CVars],[]),([DummyClauses,A],[]),([DummyClauses,A,B],[]),([DummyClauses,A,B,Vars],[]),([DummyClauses,A,Vars],[]),([DummyClauses,B],[]),([DummyClauses,B,Vars],[]),([DummyClauses,Rest],[]),([Disjs],[]),([Disjs,X,C,A,B,Vars,CVars,Args],[]),([Disjs,X,C,A,Vars,CVars,Args],[]),([Disjs,X,C,B,Vars,CVars,Args],[]),([Disjs,C],[]),([Disjs,C,A],[]),([Disjs,C,A,B],[]),([Disjs,C,A,B,Vars],[]),([Disjs,C,A,B,Vars,CVars],[]),([Disjs,C,A,B,CVars],[]),([Disjs,C,A,Vars],[]),([Disjs,C,A,Vars,CVars],[]),([Disjs,C,A,CVars],[]),([Disjs,C,B],[]),([Disjs,C,B,Vars],[]),([Disjs,C,B,Vars,CVars],[]),([Disjs,C,B,CVars],[]),([Disjs,C,CVars],[]),([Disjs,A],[]),([Disjs,A,B],[]),([Disjs,A,B,Vars],[]),([Disjs,A,Vars],[]),([Disjs,B],[]),([Disjs,B,Vars],[]),([X,C,A,B,Vars,CVars,Args],[]),([X,C,A,Vars,CVars,Args],[]),([X,C,B,Vars,CVars,Args],[]),([C],[]),([C,A],[]),([C,A,B],[]),([C,A,B,Vars],[]),([C,A,B,Vars,CVars],[]),([C,A,B,CVars],[]),([C,A,Vars],[]),([C,A,Vars,CVars],[]),([C,A,CVars],[]),([C,B],[]),([C,B,Vars],[]),([C,B,Vars,CVars],[]),([C,B,CVars],[]),([C,CVars],[]),([A],[]),([A,B],[]),([A,B,Vars],[]),([A,Vars],[]),([B],[]),([B,Vars],[])])
    )).

:- true pred make_dummy_clauses(A,X,_A,Link)
   : ( (A=(_B;_C)),
       mshare([[X,_B],[X,_B,_C],[X,_C],[_A],[Link],[_B],[_B,_C],[_C]]),
       linear(_A), linear(Link), shlin2([([X,_B],[]),([X,_B,_C],[]),([X,_C],[]),([_A],[_A]),([Link],[Link]),([_B],[]),([_B,_C],[]),([_C],[])]) )
   => ( mshare([[X,_A,_B],[X,_A,_B,_C],[X,_A,_C],[X,_B],[X,_B,_C],[X,_C],[_A],[_A,Link],[_A,_B],[_A,_B,_C],[_A,_C],[_B],[_B,_C],[_C]]),
        linear(Link), shlin2([([X,_A,_B],[]),([X,_A,_B,_C],[]),([X,_A,_C],[]),([X,_B],[]),([X,_B,_C],[]),([X,_C],[]),([_A],[]),([_A,Link],[_A,Link]),([_A,_B],[]),([_A,_B,_C],[]),([_A,_C],[]),([_B],[]),([_B,_C],[]),([_C],[])]) ).

:- true pred make_dummy_clauses(A,X,_A,Link)
   : ( mshare([[A],[A,X],[X],[_A],[Link]]),
       linear(_A), linear(Link), shlin2([([A],[]),([A,X],[]),([X],[]),([_A],[_A]),([Link],[Link])]) )
   => ( mshare([[A],[A,X],[A,X,_A],[A,_A],[X],[X,_A],[_A],[_A,Link]]),
        linear(Link), shlin2([([A],[]),([A,X],[]),([A,X,_A],[]),([A,_A],[]),([X],[]),([X,_A],[]),([_A],[]),([_A,Link],[_A,Link])]) ).

make_dummy_clauses((A;B),X,[NewC|Cs],Link) :-
    !,
    true((mshare([[X],[X,A],[X,A,B],[X,B],[Link],[A],[A,B],[B],[NewC],[Cs]]),linear(Link),linear(NewC),linear(Cs),shlin2([([X],[]),([X,A],[]),([X,A,B],[]),([X,B],[]),([Link],[Link]),([A],[]),([A,B],[]),([B],[]),([NewC],[NewC]),([Cs],[Cs])]);mshare([[X,A],[X,A,B],[X,B],[Link],[A],[A,B],[B],[NewC],[Cs]]),linear(Link),linear(NewC),linear(Cs),shlin2([([X,A],[]),([X,A,B],[]),([X,B],[]),([Link],[Link]),([A],[]),([A,B],[]),([B],[]),([NewC],[NewC]),([Cs],[Cs])]))),
    copy((X:-A),NewC),
    true((mshare([[X],[X,A],[X,A,B],[X,A,B,NewC],[X,A,NewC],[X,B],[X,B,NewC],[X,NewC],[Link],[A],[A,B],[A,B,NewC],[A,NewC],[B],[NewC],[Cs]]),linear(Link),linear(Cs),shlin2([([X],[]),([X,A],[]),([X,A,B],[]),([X,A,B,NewC],[]),([X,A,NewC],[]),([X,B],[]),([X,B,NewC],[]),([X,NewC],[]),([Link],[Link]),([A],[]),([A,B],[]),([A,B,NewC],[]),([A,NewC],[]),([B],[]),([NewC],[]),([Cs],[Cs])]);mshare([[X,A],[X,A,B],[X,A,B,NewC],[X,A,NewC],[X,B],[X,B,NewC],[Link],[A],[A,B],[A,B,NewC],[A,NewC],[B],[NewC],[Cs]]),linear(Link),linear(Cs),shlin2([([X,A],[]),([X,A,B],[]),([X,A,B,NewC],[]),([X,A,NewC],[]),([X,B],[]),([X,B,NewC],[]),([Link],[Link]),([A],[]),([A,B],[]),([A,B,NewC],[]),([A,NewC],[]),([B],[]),([NewC],[]),([Cs],[Cs])]))),
    make_dummy_clauses(B,X,Cs,Link),
    true((mshare([[X],[X,A],[X,A,B],[X,A,B,NewC],[X,A,B,NewC,Cs],[X,A,B,Cs],[X,A,NewC],[X,A,NewC,Cs],[X,A,Cs],[X,B],[X,B,NewC],[X,B,NewC,Cs],[X,B,Cs],[X,NewC],[X,NewC,Cs],[X,Cs],[Link,Cs],[A],[A,B],[A,B,NewC],[A,B,NewC,Cs],[A,B,Cs],[A,NewC],[B],[B,Cs],[NewC],[Cs]]),linear(Link),shlin2([([X],[]),([X,A],[]),([X,A,B],[]),([X,A,B,NewC],[]),([X,A,B,NewC,Cs],[]),([X,A,B,Cs],[]),([X,A,NewC],[]),([X,A,NewC,Cs],[]),([X,A,Cs],[]),([X,B],[]),([X,B,NewC],[]),([X,B,NewC,Cs],[]),([X,B,Cs],[]),([X,NewC],[]),([X,NewC,Cs],[]),([X,Cs],[]),([Link,Cs],[Link,Cs]),([A],[]),([A,B],[]),([A,B,NewC],[]),([A,B,NewC,Cs],[]),([A,B,Cs],[]),([A,NewC],[]),([B],[]),([B,Cs],[]),([NewC],[]),([Cs],[])]);mshare([[X,A],[X,A,B],[X,A,B,NewC],[X,A,B,NewC,Cs],[X,A,B,Cs],[X,A,NewC],[X,A,NewC,Cs],[X,A,Cs],[X,B],[X,B,NewC],[X,B,NewC,Cs],[X,B,Cs],[Link,Cs],[A],[A,B],[A,B,NewC],[A,B,NewC,Cs],[A,B,Cs],[A,NewC],[B],[B,Cs],[NewC],[Cs]]),linear(Link),shlin2([([X,A],[]),([X,A,B],[]),([X,A,B,NewC],[]),([X,A,B,NewC,Cs],[]),([X,A,B,Cs],[]),([X,A,NewC],[]),([X,A,NewC,Cs],[]),([X,A,Cs],[]),([X,B],[]),([X,B,NewC],[]),([X,B,NewC,Cs],[]),([X,B,Cs],[]),([Link,Cs],[Link,Cs]),([A],[]),([A,B],[]),([A,B,NewC],[]),([A,B,NewC,Cs],[]),([A,B,Cs],[]),([A,NewC],[]),([B],[]),([B,Cs],[]),([NewC],[]),([Cs],[])]))).
make_dummy_clauses(A,X,[NewC|Link],Link) :-
    true((mshare([[A],[A,X],[X],[Link],[NewC]]),linear(Link),linear(NewC),shlin2([([A],[]),([A,X],[]),([X],[]),([Link],[Link]),([NewC],[NewC])]);mshare([[A],[A,X],[Link],[NewC]]),linear(Link),linear(NewC),shlin2([([A],[]),([A,X],[]),([Link],[Link]),([NewC],[NewC])]))),
    copy((X:-A),NewC),
    true((mshare([[A],[A,X],[A,X,NewC],[A,NewC],[X],[X,NewC],[Link],[NewC]]),linear(Link),shlin2([([A],[]),([A,X],[]),([A,X,NewC],[]),([A,NewC],[]),([X],[]),([X,NewC],[]),([Link],[Link]),([NewC],[])]);mshare([[A],[A,X],[A,X,NewC],[A,NewC],[Link],[NewC]]),linear(Link),shlin2([([A],[]),([A,X],[]),([A,X,NewC],[]),([A,NewC],[]),([Link],[Link]),([NewC],[])]))).

:- true pred find_vars(X,Y)
   : ( mshare([[X],[Y]]),
       linear(Y), shlin2([([X],[]),([Y],[Y])]) )
   => ( mshare([[X],[X,Y]]),
        shlin2([([X],[]),([X,Y],[])]) ).

:- true pred find_vars(X,Y)
   : ( (X=(_A;_B)),
       mshare([[Y],[_A],[_A,_B],[_B]]),
       linear(Y), shlin2([([Y],[Y]),([_A],[]),([_A,_B],[]),([_B],[])]) )
   => ( mshare([[Y,_A],[Y,_A,_B],[Y,_B],[_A],[_A,_B],[_B]]),
        shlin2([([Y,_A],[]),([Y,_A,_B],[]),([Y,_B],[]),([_A],[]),([_A,_B],[]),([_B],[])]) ).

find_vars(X,Y) :-
    true((
        mshare([[X],[Y],[Link]]),
        linear(Y),
        linear(Link),
        shlin2([([X],[]),([Y],[Y]),([Link],[Link])])
    )),
    find_vars(X,Y,Link),
    true((
        mshare([[X],[X,Y],[Y,Link]]),
        linear(Link),
        shlin2([([X],[]),([X,Y],[]),([Y,Link],[Y,Link])])
    )),
    Link=[],
    true((
        mshare([[X],[X,Y]]),
        ground([Link]),
        shlin2([([X],[]),([X,Y],[])])
    )).

:- true pred find_vars(Var,Vars,Link)
   : ( mshare([[Var],[Vars],[Link]]),
       linear(Vars), linear(Link), shlin2([([Var],[]),([Vars],[Vars]),([Link],[Link])]) )
   => ( mshare([[Var],[Var,Vars],[Vars,Link]]),
        linear(Link), shlin2([([Var],[]),([Var,Vars],[]),([Vars,Link],[Vars,Link])]) ).

find_vars(Var,[Var|Link],Link) :-
    true((
        mshare([[Var],[Link]]),
        linear(Link),
        shlin2([([Var],[]),([Link],[Link])])
    )),
    var(Var),
    !,
    true((
        mshare([[Var],[Link]]),
        linear(Var),
        linear(Link),
        shlin2([([Var],[Var]),([Link],[Var,Link])])
    )).
find_vars(Cst,Link,Link) :-
    true((
        mshare([[Cst],[Link]]),
        linear(Link),
        shlin2([([Cst],[]),([Link],[Link])])
    )),
    atomic(Cst),
    !,
    true((
        mshare([[Link]]),
        ground([Cst]),
        linear(Link),
        shlin2([([Link],[Link])])
    )).
find_vars([T|Ts],Vars,NewLink) :-
    !,
    true((
        mshare([[Vars],[NewLink],[T],[T,Ts],[Ts],[Link]]),
        linear(Vars),
        linear(NewLink),
        linear(Link),
        shlin2([([Vars],[Vars]),([NewLink],[NewLink]),([T],[]),([T,Ts],[]),([Ts],[]),([Link],[Link])])
    )),
    find_vars(T,Vars,Link),
    true((
        mshare([[Vars,T],[Vars,T,Ts],[Vars,Link],[NewLink],[T],[T,Ts],[Ts]]),
        linear(NewLink),
        linear(Link),
        shlin2([([Vars,T],[]),([Vars,T,Ts],[]),([Vars,Link],[Vars,Link]),([NewLink],[NewLink]),([T],[]),([T,Ts],[]),([Ts],[])])
    )),
    find_vars(Ts,Link,NewLink),
    true((
        mshare([[Vars,NewLink,Link],[Vars,T],[Vars,T,Ts],[Vars,T,Ts,Link],[Vars,Ts,Link],[T],[T,Ts],[Ts]]),
        linear(NewLink),
        shlin2([([Vars,NewLink,Link],[Vars,NewLink,Link]),([Vars,T],[]),([Vars,T,Ts],[]),([Vars,T,Ts,Link],[]),([Vars,Ts,Link],[]),([T],[]),([T,Ts],[]),([Ts],[])])
    )).
find_vars(Term,Vars,Link) :-
    true((
        mshare([[Term],[Vars],[Link],[_1],[Args]]),
        linear(Vars),
        linear(Link),
        linear(_1),
        linear(Args),
        shlin2([([Term],[]),([Vars],[Vars]),([Link],[Link]),([_1],[_1]),([Args],[Args])])
    )),
    Term=..[_1|Args],
    true((
        mshare([[Term,_1],[Term,_1,Args],[Term,Args],[Vars],[Link]]),
        linear(Vars),
        linear(Link),
        shlin2([([Term,_1],[]),([Term,_1,Args],[]),([Term,Args],[]),([Vars],[Vars]),([Link],[Link])])
    )),
    find_vars(Args,Vars,Link),
    true((
        mshare([[Term,Vars,_1,Args],[Term,Vars,Args],[Term,_1],[Term,_1,Args],[Term,Args],[Vars,Link]]),
        linear(Link),
        shlin2([([Term,Vars,_1,Args],[]),([Term,Vars,Args],[]),([Term,_1],[]),([Term,_1,Args],[]),([Term,Args],[]),([Vars,Link],[Vars,Link])])
    )).

:- true pred intersect_vars(V1,V2,Out)
   : ( mshare([[V1],[V1,V2],[V2],[Out]]),
       linear(Out), shlin2([([V1],[]),([V1,V2],[]),([V2],[]),([Out],[Out])]) )
   => ( mshare([[V1],[V1,V2],[V1,V2,Out],[V2]]),
        shlin2([([V1],[]),([V1,V2],[]),([V1,V2,Out],[]),([V2],[])]) ).

intersect_vars(V1,V2,Out) :-
    true((
        mshare([[V1],[V1,V2],[V2],[Out],[Sorted1],[Sorted2]]),
        linear(Out),
        linear(Sorted1),
        linear(Sorted2),
        shlin2([([V1],[]),([V1,V2],[]),([V2],[]),([Out],[Out]),([Sorted1],[Sorted1]),([Sorted2],[Sorted2])])
    )),
    sort_vars(V1,Sorted1),
    true((
        mshare([[V1,V2,Sorted1],[V1,Sorted1],[V2],[Out],[Sorted2]]),
        linear(Out),
        linear(Sorted2),
        shlin2([([V1,V2,Sorted1],[]),([V1,Sorted1],[]),([V2],[]),([Out],[Out]),([Sorted2],[Sorted2])])
    )),
    sort_vars(V2,Sorted2),
    true((
        mshare([[V1,V2,Sorted1,Sorted2],[V1,Sorted1],[V2,Sorted2],[Out]]),
        linear(Out),
        shlin2([([V1,V2,Sorted1,Sorted2],[]),([V1,Sorted1],[]),([V2,Sorted2],[]),([Out],[Out])])
    )),
    intersect_sorted_vars(Sorted1,Sorted2,Out),
    true((
        mshare([[V1,V2,Out,Sorted1,Sorted2],[V1,V2,Sorted1,Sorted2],[V1,Sorted1],[V2,Sorted2]]),
        shlin2([([V1,V2,Out,Sorted1,Sorted2],[]),([V1,V2,Sorted1,Sorted2],[]),([V1,Sorted1],[]),([V2,Sorted2],[])])
    )).

:- true pred make_dummy_name(N,Name)
   : ( mshare([[N],[Name]]),
       linear(Name), shlin2([([N],[]),([Name],[Name])]) )
   => ground([N,Name]).

make_dummy_name(N,Name) :-
    true((
        mshare([[N],[Name],[L1],[L2],[L]]),
        linear(Name),
        linear(L1),
        linear(L2),
        linear(L),
        shlin2([([N],[]),([Name],[Name]),([L1],[L1]),([L2],[L2]),([L],[L])])
    )),
    atom_codes('_dummy_',L1),
    true((
        mshare([[N],[Name],[L2],[L]]),
        ground([L1]),
        linear(Name),
        linear(L2),
        linear(L),
        shlin2([([N],[]),([Name],[Name]),([L2],[L2]),([L],[L])])
    )),
    number_codes(N,L2),
    true((
        mshare([[Name],[L]]),
        ground([N,L1,L2]),
        linear(Name),
        linear(L),
        shlin2([([Name],[Name]),([L],[L])])
    )),
    my_append(L1,L2,L),
    true((
        mshare([[Name]]),
        ground([N,L1,L2,L]),
        linear(Name),
        shlin2([([Name],[Name])])
    )),
    atom_codes(Name,L),
    true(ground([N,Name,L1,L2,L])).

:- true pred my_append(_A,L,_B)
   : ( mshare([[_B]]),
       ground([_A,L]), linear(_B), shlin2([([_B],[_B])]) )
   => ground([_A,L,_B]).

my_append([],L,L).
my_append([H|L1],L2,[H|Res]) :-
    true((
        mshare([[Res]]),
        ground([L2,H,L1]),
        linear(Res),
        shlin2([([Res],[Res])])
    )),
    my_append(L1,L2,Res),
    true(ground([L2,H,L1,Res])).

:- true pred copy(Term1,Term2)
   : ( (Term1=(_A:-_B)),
       mshare([[Term2],[_A],[_A,_B],[_B]]),
       linear(Term2), shlin2([([Term2],[Term2]),([_A],[]),([_A,_B],[]),([_B],[])]) )
   => ( mshare([[Term2],[Term2,_A],[Term2,_A,_B],[Term2,_B],[_A],[_A,_B],[_B]]),
        shlin2([([Term2],[]),([Term2,_A],[]),([Term2,_A,_B],[]),([Term2,_B],[]),([_A],[]),([_A,_B],[]),([_B],[])]) ).

:- true pred copy(Term1,Term2)
   : ( (Term1=(_A:-_B)),
       mshare([[Term2],[_A,_B],[_B]]),
       linear(Term2), shlin2([([Term2],[Term2]),([_A,_B],[]),([_B],[])]) )
   => ( mshare([[Term2],[Term2,_A],[Term2,_A,_B],[Term2,_B],[_A],[_A,_B],[_B]]),
        shlin2([([Term2],[]),([Term2,_A],[]),([Term2,_A,_B],[]),([Term2,_B],[]),([_A],[]),([_A,_B],[]),([_B],[])]) ).

copy(Term1,Term2) :-
    true((
        mshare([[Term1],[Term2],[Set],[Sym]]),
        linear(Term2),
        linear(Set),
        linear(Sym),
        shlin2([([Term1],[]),([Term2],[Term2]),([Set],[Set]),([Sym],[Sym])])
    )),
    varset(Term1,Set),
    true((
        mshare([[Term1],[Term1,Set],[Term2],[Sym]]),
        linear(Term2),
        linear(Sym),
        shlin2([([Term1],[]),([Term1,Set],[]),([Term2],[Term2]),([Sym],[Sym])])
    )),
    make_sym(Set,Sym),
    true((
        mshare([[Term1],[Term1,Set,Sym],[Term2],[Sym]]),
        linear(Term2),
        shlin2([([Term1],[]),([Term1,Set,Sym],[]),([Term2],[Term2]),([Sym],[Sym])])
    )),
    copy2(Term1,Term2,Sym),
    !,
    true((
        mshare([[Term1],[Term1,Term2,Set,Sym],[Term1,Term2,Sym],[Term1,Set,Sym],[Term1,Sym],[Term2],[Term2,Sym],[Sym]]),
        shlin2([([Term1],[]),([Term1,Term2,Set,Sym],[]),([Term1,Term2,Sym],[]),([Term1,Set,Sym],[]),([Term1,Sym],[]),([Term2],[Term2]),([Term2,Sym],[]),([Sym],[Sym])])
    )).

:- true pred copy2(V1,V2,Sym)
   : ( mshare([[V1,V2,Sym],[V1,Sym],[V2,Sym],[Sym]]),
       shlin2([([V1,V2,Sym],[]),([V1,Sym],[]),([V2,Sym],[]),([Sym],[Sym])]) )
   => ( mshare([[V1,V2,Sym],[V1,Sym],[V2,Sym],[Sym]]),
        shlin2([([V1,V2,Sym],[]),([V1,Sym],[]),([V2,Sym],[]),([Sym],[Sym])]) ).

:- true pred copy2(V1,V2,Sym)
   : ( mshare([[V1],[V1,V2,Sym],[V1,Sym],[V2],[V2,Sym],[Sym]]),
       shlin2([([V1],[]),([V1,V2,Sym],[]),([V1,Sym],[]),([V2],[V2]),([V2,Sym],[]),([Sym],[Sym])]) )
   => ( mshare([[V1],[V1,V2,Sym],[V1,Sym],[V2],[V2,Sym],[Sym]]),
        shlin2([([V1],[]),([V1,V2,Sym],[]),([V1,Sym],[]),([V2],[V2]),([V2,Sym],[]),([Sym],[Sym])]) ).

:- true pred copy2(V1,V2,Sym)
   : ( mshare([[V1],[V1,Sym],[V2],[Sym]]),
       linear(V2), shlin2([([V1],[]),([V1,Sym],[]),([V2],[V2]),([Sym],[Sym])]) )
   => ( mshare([[V1],[V1,V2,Sym],[V1,Sym],[V2],[V2,Sym],[Sym]]),
        shlin2([([V1],[]),([V1,V2,Sym],[]),([V1,Sym],[]),([V2],[V2]),([V2,Sym],[]),([Sym],[Sym])]) ).

:- true pred copy2(V1,V2,Sym)
   : ( mshare([[V1,V2,Sym],[V1,Sym],[V2,Sym],[Sym]]),
       shlin2([([V1,V2,Sym],[]),([V1,Sym],[]),([V2,Sym],[V2,Sym]),([Sym],[Sym])]) )
   => ( mshare([[V1,V2,Sym],[V1,Sym],[V2,Sym],[Sym]]),
        shlin2([([V1,V2,Sym],[]),([V1,Sym],[]),([V2,Sym],[]),([Sym],[Sym])]) ).

copy2(V1,V2,Sym) :-
    true((mshare([[V1],[V1,V2,Sym],[V1,Sym],[V2],[V2,Sym],[Sym]]),shlin2([([V1],[]),([V1,V2,Sym],[]),([V1,Sym],[]),([V2],[V2]),([V2,Sym],[]),([Sym],[Sym])]);mshare([[V1],[V1,Sym],[V2],[Sym]]),linear(V2),shlin2([([V1],[]),([V1,Sym],[]),([V2],[V2]),([Sym],[Sym])]);mshare([[V1,V2,Sym],[V1,Sym],[V2,Sym],[Sym]]),shlin2([([V1,V2,Sym],[]),([V1,Sym],[]),([V2,Sym],[]),([Sym],[Sym])]);mshare([[V1,V2,Sym],[V1,Sym],[V2,Sym],[Sym]]),shlin2([([V1,V2,Sym],[]),([V1,Sym],[]),([V2,Sym],[V2,Sym]),([Sym],[Sym])]))),
    var(V1),
    !,
    true((mshare([[V1],[V1,V2,Sym],[V1,Sym],[V2],[V2,Sym],[Sym]]),linear(V1),shlin2([([V1],[V1]),([V1,V2,Sym],[V1]),([V1,Sym],[V1]),([V2],[V1,V2]),([V2,Sym],[V1]),([Sym],[V1,Sym])]);mshare([[V1],[V1,Sym],[V2],[Sym]]),linear(V1),linear(V2),shlin2([([V1],[V1]),([V1,Sym],[V1]),([V2],[V1,V2]),([Sym],[V1,Sym])]);mshare([[V1,V2,Sym],[V1,Sym],[V2,Sym],[Sym]]),linear(V1),shlin2([([V1,V2,Sym],[V1]),([V1,Sym],[V1]),([V2,Sym],[V1]),([Sym],[V1,Sym])]);mshare([[V1,V2,Sym],[V1,Sym],[V2,Sym],[Sym]]),linear(V1),shlin2([([V1,V2,Sym],[V1]),([V1,Sym],[V1]),([V2,Sym],[V1,V2,Sym]),([Sym],[V1,Sym])]))),
    retrieve_sym(V1,Sym,V2),
    true((mshare([[V1,V2,Sym],[V1,Sym],[V2,Sym],[Sym]]),shlin2([([V1,V2,Sym],[]),([V1,Sym],[]),([V2,Sym],[]),([Sym],[V1,Sym])]);mshare([[V1,V2,Sym],[V1,Sym],[V2,Sym],[Sym]]),shlin2([([V1,V2,Sym],[]),([V1,Sym],[]),([V2,Sym],[V1,V2,Sym]),([Sym],[V1,Sym])]))).
copy2(X1,X2,Sym) :-
    true((mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym],[Name],[Arity]]),linear(Name),linear(Arity),shlin2([([X1],[]),([X1,X2,Sym],[]),([X1,Sym],[]),([X2],[X2]),([X2,Sym],[]),([Sym],[Sym]),([Name],[Name]),([Arity],[Arity])]);mshare([[X1],[X1,Sym],[X2],[Sym],[Name],[Arity]]),linear(X2),linear(Name),linear(Arity),shlin2([([X1],[]),([X1,Sym],[]),([X2],[X2]),([Sym],[Sym]),([Name],[Name]),([Arity],[Arity])]);mshare([[X1,X2,Sym],[X1,Sym],[X2,Sym],[Sym],[Name],[Arity]]),linear(Name),linear(Arity),shlin2([([X1,X2,Sym],[]),([X1,Sym],[]),([X2,Sym],[]),([Sym],[Sym]),([Name],[Name]),([Arity],[Arity])]);mshare([[X1,X2,Sym],[X1,Sym],[X2,Sym],[Sym],[Name],[Arity]]),linear(Name),linear(Arity),shlin2([([X1,X2,Sym],[]),([X1,Sym],[]),([X2,Sym],[X2,Sym]),([Sym],[Sym]),([Name],[Name]),([Arity],[Arity])]))),
    nonvar(X1),
    !,
    true((mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym],[Name],[Arity]]),linear(Name),linear(Arity),shlin2([([X1],[]),([X1,X2,Sym],[]),([X1,Sym],[]),([X2],[X2]),([X2,Sym],[]),([Sym],[Sym]),([Name],[Name]),([Arity],[Arity])]);mshare([[X1],[X1,Sym],[X2],[Sym],[Name],[Arity]]),linear(X2),linear(Name),linear(Arity),shlin2([([X1],[]),([X1,Sym],[]),([X2],[X2]),([Sym],[Sym]),([Name],[Name]),([Arity],[Arity])]);mshare([[X1,X2,Sym],[X1,Sym],[X2,Sym],[Sym],[Name],[Arity]]),linear(Name),linear(Arity),shlin2([([X1,X2,Sym],[]),([X1,Sym],[]),([X2,Sym],[]),([Sym],[Sym]),([Name],[Name]),([Arity],[Arity])]);mshare([[X1,X2,Sym],[X1,Sym],[X2,Sym],[Sym],[Name],[Arity]]),linear(Name),linear(Arity),shlin2([([X1,X2,Sym],[]),([X1,Sym],[]),([X2,Sym],[X2,Sym]),([Sym],[Sym]),([Name],[Name]),([Arity],[Arity])]))),
    functor(X1,Name,Arity),
    true((mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym]]),ground([Name,Arity]),shlin2([([X1],[]),([X1,X2,Sym],[]),([X1,Sym],[]),([X2],[X2]),([X2,Sym],[]),([Sym],[Sym])]);mshare([[X1],[X1,Sym],[X2],[Sym]]),ground([Name,Arity]),linear(X2),shlin2([([X1],[]),([X1,Sym],[]),([X2],[X2]),([Sym],[Sym])]);mshare([[X1,X2,Sym],[X1,Sym],[X2,Sym],[Sym]]),ground([Name,Arity]),shlin2([([X1,X2,Sym],[]),([X1,Sym],[]),([X2,Sym],[]),([Sym],[Sym])]);mshare([[X1,X2,Sym],[X1,Sym],[X2,Sym],[Sym]]),ground([Name,Arity]),shlin2([([X1,X2,Sym],[]),([X1,Sym],[]),([X2,Sym],[X2,Sym]),([Sym],[Sym])]))),
    functor(X2,Name,Arity),
    true((mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym]]),ground([Name,Arity]),shlin2([([X1],[]),([X1,X2,Sym],[]),([X1,Sym],[]),([X2],[X2]),([X2,Sym],[]),([Sym],[Sym])]);mshare([[X1],[X1,Sym],[X2],[Sym]]),ground([Name,Arity]),linear(X2),shlin2([([X1],[]),([X1,Sym],[]),([X2],[X2]),([Sym],[Sym])]);mshare([[X1,X2,Sym],[X1,Sym],[X2,Sym],[Sym]]),ground([Name,Arity]),shlin2([([X1,X2,Sym],[]),([X1,Sym],[]),([X2,Sym],[]),([Sym],[Sym])]);mshare([[X1,X2,Sym],[X1,Sym],[X2,Sym],[Sym]]),ground([Name,Arity]),shlin2([([X1,X2,Sym],[]),([X1,Sym],[]),([X2,Sym],[X2,Sym]),([Sym],[Sym])]))),
    copy2(X1,X2,Sym,1,Arity),
    true((mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym]]),ground([Name,Arity]),shlin2([([X1],[]),([X1,X2,Sym],[]),([X1,Sym],[]),([X2],[X2]),([X2,Sym],[]),([Sym],[Sym])]);mshare([[X1,X2,Sym],[X1,Sym],[X2,Sym],[Sym]]),ground([Name,Arity]),shlin2([([X1,X2,Sym],[]),([X1,Sym],[]),([X2,Sym],[]),([Sym],[Sym])]))).

:- true pred copy2(_X1,_X2,_Sym,N,Arity)
   : ( (N=1),
       mshare([[_X1,_X2,_Sym],[_X1,_Sym],[_X2,_Sym],[_Sym]]),
       ground([Arity]), shlin2([([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2,_Sym],[]),([_Sym],[_Sym])]) )
   => ( mshare([[_X1,_X2,_Sym],[_X1,_Sym],[_X2,_Sym],[_Sym]]),
        ground([Arity]), shlin2([([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2,_Sym],[]),([_Sym],[_Sym])]) ).

:- true pred copy2(_X1,_X2,_Sym,N,Arity)
   : ( (N=1),
       mshare([[_X1,_X2,_Sym],[_X1,_Sym],[_X2,_Sym],[_Sym]]),
       ground([Arity]), shlin2([([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2,_Sym],[_X2,_Sym]),([_Sym],[_Sym])]) )
   => ( mshare([[_X1,_X2,_Sym],[_X1,_Sym],[_X2,_Sym],[_Sym]]),
        ground([Arity]), shlin2([([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2,_Sym],[]),([_Sym],[_Sym])]) ).

:- true pred copy2(_X1,_X2,_Sym,N,Arity)
   : ( (N=1),
       mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),
       ground([Arity]), shlin2([([_X1],[]),([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2],[_X2]),([_X2,_Sym],[]),([_Sym],[_Sym])]) )
   => ( mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),
        ground([Arity]), shlin2([([_X1],[]),([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2],[_X2]),([_X2,_Sym],[]),([_Sym],[_Sym])]) ).

:- true pred copy2(_X1,_X2,_Sym,N,Arity)
   : ( (N=1),
       mshare([[_X1],[_X1,_Sym],[_X2],[_Sym]]),
       ground([Arity]), linear(_X2), shlin2([([_X1],[]),([_X1,_Sym],[]),([_X2],[_X2]),([_Sym],[_Sym])]) )
   => ( mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),
        ground([Arity]), shlin2([([_X1],[]),([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2],[_X2]),([_X2,_Sym],[]),([_Sym],[_Sym])]) ).

:- true pred copy2(_X1,_X2,_Sym,N,Arity)
   : ( mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),
       ground([N,Arity]), shlin2([([_X1],[]),([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2],[_X2]),([_X2,_Sym],[]),([_Sym],[_Sym])]) )
   => ( mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),
        ground([N,Arity]), shlin2([([_X1],[]),([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2],[_X2]),([_X2,_Sym],[]),([_Sym],[_Sym])]) ).

:- true pred copy2(_X1,_X2,_Sym,N,Arity)
   : ( mshare([[_X1,_X2,_Sym],[_X1,_Sym],[_X2,_Sym],[_Sym]]),
       ground([N,Arity]), shlin2([([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2,_Sym],[]),([_Sym],[_Sym])]) )
   => ( mshare([[_X1,_X2,_Sym],[_X1,_Sym],[_X2,_Sym],[_Sym]]),
        ground([N,Arity]), shlin2([([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2,_Sym],[]),([_Sym],[_Sym])]) ).

:- true pred copy2(_X1,_X2,_Sym,N,Arity)
   : ( mshare([[_X1,_X2,_Sym],[_X1,_Sym],[_X2,_Sym],[_Sym]]),
       ground([N,Arity]), shlin2([([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2,_Sym],[_X2,_Sym]),([_Sym],[_Sym])]) )
   => ( mshare([[_X1,_X2,_Sym],[_X1,_Sym],[_X2,_Sym],[_Sym]]),
        ground([N,Arity]), shlin2([([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2,_Sym],[]),([_Sym],[_Sym])]) ).

copy2(_X1,_X2,_Sym,N,Arity) :-
    true((mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),ground([N,Arity]),shlin2([([_X1],[]),([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2],[_X2]),([_X2,_Sym],[]),([_Sym],[_Sym])]);mshare([[_X1],[_X1,_Sym],[_X2],[_Sym]]),ground([N,Arity]),linear(_X2),shlin2([([_X1],[]),([_X1,_Sym],[]),([_X2],[_X2]),([_Sym],[_Sym])]);mshare([[_X1,_X2,_Sym],[_X1,_Sym],[_X2,_Sym],[_Sym]]),ground([N,Arity]),shlin2([([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2,_Sym],[]),([_Sym],[_Sym])]);mshare([[_X1,_X2,_Sym],[_X1,_Sym],[_X2,_Sym],[_Sym]]),ground([N,Arity]),shlin2([([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2,_Sym],[_X2,_Sym]),([_Sym],[_Sym])]))),
    N>Arity,
    !,
    true((mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),ground([N,Arity]),shlin2([([_X1],[]),([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2],[_X2]),([_X2,_Sym],[]),([_Sym],[_Sym])]);mshare([[_X1],[_X1,_Sym],[_X2],[_Sym]]),ground([N,Arity]),linear(_X2),shlin2([([_X1],[]),([_X1,_Sym],[]),([_X2],[_X2]),([_Sym],[_Sym])]);mshare([[_X1,_X2,_Sym],[_X1,_Sym],[_X2,_Sym],[_Sym]]),ground([N,Arity]),shlin2([([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2,_Sym],[]),([_Sym],[_Sym])]);mshare([[_X1,_X2,_Sym],[_X1,_Sym],[_X2,_Sym],[_Sym]]),ground([N,Arity]),shlin2([([_X1,_X2,_Sym],[]),([_X1,_Sym],[]),([_X2,_Sym],[_X2,_Sym]),([_Sym],[_Sym])]))).
copy2(X1,X2,Sym,N,Arity) :-
    true((mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym],[Arg1],[Arg2],[N1]]),ground([N,Arity]),linear(Arg1),linear(Arg2),linear(N1),shlin2([([X1],[]),([X1,X2,Sym],[]),([X1,Sym],[]),([X2],[X2]),([X2,Sym],[]),([Sym],[Sym]),([Arg1],[Arg1]),([Arg2],[Arg2]),([N1],[N1])]);mshare([[X1],[X1,Sym],[X2],[Sym],[Arg1],[Arg2],[N1]]),ground([N,Arity]),linear(X2),linear(Arg1),linear(Arg2),linear(N1),shlin2([([X1],[]),([X1,Sym],[]),([X2],[X2]),([Sym],[Sym]),([Arg1],[Arg1]),([Arg2],[Arg2]),([N1],[N1])]);mshare([[X1,X2,Sym],[X1,Sym],[X2,Sym],[Sym],[Arg1],[Arg2],[N1]]),ground([N,Arity]),linear(Arg1),linear(Arg2),linear(N1),shlin2([([X1,X2,Sym],[]),([X1,Sym],[]),([X2,Sym],[]),([Sym],[Sym]),([Arg1],[Arg1]),([Arg2],[Arg2]),([N1],[N1])]);mshare([[X1,X2,Sym],[X1,Sym],[X2,Sym],[Sym],[Arg1],[Arg2],[N1]]),ground([N,Arity]),linear(Arg1),linear(Arg2),linear(N1),shlin2([([X1,X2,Sym],[]),([X1,Sym],[]),([X2,Sym],[X2,Sym]),([Sym],[Sym]),([Arg1],[Arg1]),([Arg2],[Arg2]),([N1],[N1])]))),
    N=<Arity,
    !,
    true((mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym],[Arg1],[Arg2],[N1]]),ground([N,Arity]),linear(Arg1),linear(Arg2),linear(N1),shlin2([([X1],[]),([X1,X2,Sym],[]),([X1,Sym],[]),([X2],[X2]),([X2,Sym],[]),([Sym],[Sym]),([Arg1],[Arg1]),([Arg2],[Arg2]),([N1],[N1])]);mshare([[X1],[X1,Sym],[X2],[Sym],[Arg1],[Arg2],[N1]]),ground([N,Arity]),linear(X2),linear(Arg1),linear(Arg2),linear(N1),shlin2([([X1],[]),([X1,Sym],[]),([X2],[X2]),([Sym],[Sym]),([Arg1],[Arg1]),([Arg2],[Arg2]),([N1],[N1])]);mshare([[X1,X2,Sym],[X1,Sym],[X2,Sym],[Sym],[Arg1],[Arg2],[N1]]),ground([N,Arity]),linear(Arg1),linear(Arg2),linear(N1),shlin2([([X1,X2,Sym],[]),([X1,Sym],[]),([X2,Sym],[]),([Sym],[Sym]),([Arg1],[Arg1]),([Arg2],[Arg2]),([N1],[N1])]);mshare([[X1,X2,Sym],[X1,Sym],[X2,Sym],[Sym],[Arg1],[Arg2],[N1]]),ground([N,Arity]),linear(Arg1),linear(Arg2),linear(N1),shlin2([([X1,X2,Sym],[]),([X1,Sym],[]),([X2,Sym],[X2,Sym]),([Sym],[Sym]),([Arg1],[Arg1]),([Arg2],[Arg2]),([N1],[N1])]))),
    arg(N,X1,Arg1),
    true((mshare([[X1,X2,Sym,Arg1],[X1,Sym,Arg1],[X1,Arg1],[X2],[X2,Sym],[Sym],[Arg2],[N1]]),ground([N,Arity]),linear(Arg2),linear(N1),shlin2([([X1,X2,Sym,Arg1],[]),([X1,Sym,Arg1],[]),([X1,Arg1],[]),([X2],[X2]),([X2,Sym],[]),([Sym],[Sym]),([Arg2],[Arg2]),([N1],[N1])]);mshare([[X1,X2,Sym,Arg1],[X1,Sym,Arg1],[X2,Sym],[Sym],[Arg2],[N1]]),ground([N,Arity]),linear(Arg2),linear(N1),shlin2([([X1,X2,Sym,Arg1],[]),([X1,Sym,Arg1],[]),([X2,Sym],[]),([Sym],[Sym]),([Arg2],[Arg2]),([N1],[N1])]);mshare([[X1,X2,Sym,Arg1],[X1,Sym,Arg1],[X2,Sym],[Sym],[Arg2],[N1]]),ground([N,Arity]),linear(Arg2),linear(N1),shlin2([([X1,X2,Sym,Arg1],[]),([X1,Sym,Arg1],[]),([X2,Sym],[X2,Sym]),([Sym],[Sym]),([Arg2],[Arg2]),([N1],[N1])]);mshare([[X1,Sym,Arg1],[X1,Arg1],[X2],[Sym],[Arg2],[N1]]),ground([N,Arity]),linear(X2),linear(Arg2),linear(N1),shlin2([([X1,Sym,Arg1],[]),([X1,Arg1],[]),([X2],[X2]),([Sym],[Sym]),([Arg2],[Arg2]),([N1],[N1])]))),
    arg(N,X2,Arg2),
    true((mshare([[X1,X2,Sym,Arg1,Arg2],[X1,Sym,Arg1],[X1,Arg1],[X2,Sym,Arg2],[X2,Arg2],[Sym],[N1]]),ground([N,Arity]),linear(N1),shlin2([([X1,X2,Sym,Arg1,Arg2],[]),([X1,Sym,Arg1],[]),([X1,Arg1],[]),([X2,Sym,Arg2],[]),([X2,Arg2],[X2,Arg2]),([Sym],[Sym]),([N1],[N1])]);mshare([[X1,X2,Sym,Arg1,Arg2],[X1,Sym,Arg1],[X2,Sym,Arg2],[Sym],[N1]]),ground([N,Arity]),linear(N1),shlin2([([X1,X2,Sym,Arg1,Arg2],[]),([X1,Sym,Arg1],[]),([X2,Sym,Arg2],[]),([Sym],[Sym]),([N1],[N1])]);mshare([[X1,X2,Sym,Arg1,Arg2],[X1,Sym,Arg1],[X2,Sym,Arg2],[Sym],[N1]]),ground([N,Arity]),linear(N1),shlin2([([X1,X2,Sym,Arg1,Arg2],[]),([X1,Sym,Arg1],[]),([X2,Sym,Arg2],[X2,Sym,Arg2]),([Sym],[Sym]),([N1],[N1])]);mshare([[X1,Sym,Arg1],[X1,Arg1],[X2,Arg2],[Sym],[N1]]),ground([N,Arity]),linear(X2),linear(Arg2),linear(N1),shlin2([([X1,Sym,Arg1],[]),([X1,Arg1],[]),([X2,Arg2],[X2,Arg2]),([Sym],[Sym]),([N1],[N1])]))),
    copy2(Arg1,Arg2,Sym),
    true((mshare([[X1,X2,Sym,Arg1,Arg2],[X1,Sym,Arg1],[X1,Arg1],[X2,Sym,Arg2],[X2,Arg2],[Sym],[N1]]),ground([N,Arity]),linear(N1),shlin2([([X1,X2,Sym,Arg1,Arg2],[]),([X1,Sym,Arg1],[]),([X1,Arg1],[]),([X2,Sym,Arg2],[]),([X2,Arg2],[X2,Arg2]),([Sym],[Sym]),([N1],[N1])]);mshare([[X1,X2,Sym,Arg1,Arg2],[X1,Sym,Arg1],[X2,Sym,Arg2],[Sym],[N1]]),ground([N,Arity]),linear(N1),shlin2([([X1,X2,Sym,Arg1,Arg2],[]),([X1,Sym,Arg1],[]),([X2,Sym,Arg2],[]),([Sym],[Sym]),([N1],[N1])]))),
    N1 is N+1,
    true((mshare([[X1,X2,Sym,Arg1,Arg2],[X1,Sym,Arg1],[X1,Arg1],[X2,Sym,Arg2],[X2,Arg2],[Sym]]),ground([N,Arity,N1]),shlin2([([X1,X2,Sym,Arg1,Arg2],[]),([X1,Sym,Arg1],[]),([X1,Arg1],[]),([X2,Sym,Arg2],[]),([X2,Arg2],[X2,Arg2]),([Sym],[Sym])]);mshare([[X1,X2,Sym,Arg1,Arg2],[X1,Sym,Arg1],[X2,Sym,Arg2],[Sym]]),ground([N,Arity,N1]),shlin2([([X1,X2,Sym,Arg1,Arg2],[]),([X1,Sym,Arg1],[]),([X2,Sym,Arg2],[]),([Sym],[Sym])]))),
    copy2(X1,X2,Sym,N1,Arity),
    true((mshare([[X1,X2,Sym,Arg1,Arg2],[X1,Sym,Arg1],[X1,Arg1],[X2,Sym,Arg2],[X2,Arg2],[Sym]]),ground([N,Arity,N1]),shlin2([([X1,X2,Sym,Arg1,Arg2],[]),([X1,Sym,Arg1],[]),([X1,Arg1],[]),([X2,Sym,Arg2],[]),([X2,Arg2],[X2,Arg2]),([Sym],[Sym])]);mshare([[X1,X2,Sym,Arg1,Arg2],[X1,Sym,Arg1],[X2,Sym,Arg2],[Sym]]),ground([N,Arity,N1]),shlin2([([X1,X2,Sym,Arg1,Arg2],[]),([X1,Sym,Arg1],[]),([X2,Sym,Arg2],[]),([Sym],[Sym])]))).

:- true pred retrieve_sym(V,_A,X)
   : ( mshare([[V],[V,_A],[V,_A,X],[_A],[_A,X],[X]]),
       linear(V), shlin2([([V],[V]),([V,_A],[V]),([V,_A,X],[V]),([_A],[V,_A]),([_A,X],[V]),([X],[V,X])]) )
   => ( mshare([[V,_A],[V,_A,X],[_A],[_A,X]]),
        shlin2([([V,_A],[]),([V,_A,X],[]),([_A],[_A]),([_A,X],[])]) ).

:- true pred retrieve_sym(V,_A,X)
   : ( mshare([[V],[V,_A],[V,_A,X],[V,X],[_A],[_A,X],[X]]),
       linear(V), shlin2([([V],[V]),([V,_A],[V]),([V,_A,X],[V]),([V,X],[V]),([_A],[_A]),([_A,X],[]),([X],[])]) )
   => ( mshare([[V,_A],[V,_A,X],[_A],[_A,X]]),
        shlin2([([V,_A],[]),([V,_A,X],[]),([_A],[_A]),([_A,X],[])]) ).

:- true pred retrieve_sym(V,_A,X)
   : ( mshare([[V,_A],[V,_A,X],[_A],[_A,X]]),
       linear(V), shlin2([([V,_A],[V]),([V,_A,X],[V]),([_A],[V,_A]),([_A,X],[V])]) )
   => ( mshare([[V,_A],[V,_A,X],[_A],[_A,X]]),
        shlin2([([V,_A],[]),([V,_A,X],[]),([_A],[_A]),([_A,X],[])]) ).

:- true pred retrieve_sym(V,_A,X)
   : ( mshare([[V,_A],[V,_A,X],[_A],[_A,X]]),
       linear(V), shlin2([([V,_A],[V]),([V,_A,X],[V]),([_A],[V,_A]),([_A,X],[V,_A,X])]) )
   => ( mshare([[V,_A],[V,_A,X],[_A],[_A,X]]),
        shlin2([([V,_A],[]),([V,_A,X],[]),([_A],[_A]),([_A,X],[])]) ).

:- true pred retrieve_sym(V,_A,X)
   : ( mshare([[V],[V,_A],[V,_A,X],[V,X],[_A],[_A,X],[X]]),
       linear(V), shlin2([([V],[V]),([V,_A],[V]),([V,_A,X],[V]),([V,X],[V]),([_A],[_A]),([_A,X],[_A,X]),([X],[X])]) )
   => ( mshare([[V,_A],[V,_A,X],[_A],[_A,X]]),
        shlin2([([V,_A],[]),([V,_A,X],[]),([_A],[_A]),([_A,X],[])]) ).

:- true pred retrieve_sym(V,_A,X)
   : ( mshare([[V],[V,_A],[_A],[X]]),
       linear(V), linear(X), shlin2([([V],[V]),([V,_A],[V]),([_A],[V,_A]),([X],[V,X])]) )
   => ( mshare([[V,_A],[V,_A,X],[_A],[_A,X]]),
        shlin2([([V,_A],[]),([V,_A,X],[]),([_A],[_A]),([_A,X],[_A,X])]) ).

:- true pred retrieve_sym(V,_A,X)
   : ( mshare([[V],[V,_A],[_A],[X]]),
       linear(V), linear(X), shlin2([([V],[V]),([V,_A],[V]),([_A],[_A]),([X],[X])]) )
   => ( mshare([[V,_A],[V,_A,X],[_A],[_A,X]]),
        shlin2([([V,_A],[]),([V,_A,X],[]),([_A],[_A]),([_A,X],[_A,X])]) ).

retrieve_sym(V,[p(W,X)|_Sym],X) :-
    true((mshare([[V],[V,X],[V,X,_Sym],[V,X,_Sym,W],[V,X,W],[V,_Sym],[V,_Sym,W],[V,W],[X],[X,_Sym],[X,_Sym,W],[X,W],[_Sym],[W]]),shlin2([([V],[V]),([V,X],[]),([V,X,_Sym],[]),([V,X,_Sym,W],[]),([V,X,W],[]),([V,_Sym],[V]),([V,_Sym,W],[V]),([V,W],[V]),([X],[]),([X,_Sym],[]),([X,_Sym,W],[]),([X,W],[]),([_Sym],[_Sym]),([W],[W])]);mshare([[V],[V,X],[V,X,_Sym],[V,X,_Sym,W],[V,X,W],[V,_Sym],[V,_Sym,W],[V,W],[X],[X,_Sym],[X,W],[_Sym],[W]]),shlin2([([V],[V]),([V,X],[]),([V,X,_Sym],[]),([V,X,_Sym,W],[]),([V,X,W],[]),([V,_Sym],[V]),([V,_Sym,W],[V]),([V,W],[V]),([X],[]),([X,_Sym],[_Sym]),([X,W],[W]),([_Sym],[_Sym]),([W],[W])]);mshare([[V],[V,X],[V,X,_Sym],[V,X,_Sym,W],[V,X,W],[V,_Sym],[V,_Sym,W],[V,W],[X],[_Sym],[W]]),linear(V),shlin2([([V],[V]),([V,X],[V]),([V,X,_Sym],[V]),([V,X,_Sym,W],[V]),([V,X,W],[V]),([V,_Sym],[V]),([V,_Sym,W],[V]),([V,W],[V]),([X],[X]),([_Sym],[_Sym]),([W],[W])]);mshare([[V,X],[V,X,_Sym],[V,X,_Sym,W],[V,X,W],[V,_Sym],[V,_Sym,W],[V,W],[X],[X,_Sym],[X,_Sym,W],[X,W],[_Sym],[W]]),shlin2([([V,X],[]),([V,X,_Sym],[]),([V,X,_Sym,W],[]),([V,X,W],[]),([V,_Sym],[V]),([V,_Sym,W],[V]),([V,W],[V]),([X],[]),([X,_Sym],[]),([X,_Sym,W],[]),([X,W],[]),([_Sym],[_Sym]),([W],[W])]);mshare([[V,X],[V,X,_Sym],[V,X,_Sym,W],[V,X,W],[V,_Sym],[V,_Sym,W],[V,W],[X,_Sym],[X,W],[_Sym],[W]]),shlin2([([V,X],[]),([V,X,_Sym],[]),([V,X,_Sym,W],[]),([V,X,W],[]),([V,_Sym],[V]),([V,_Sym,W],[V]),([V,W],[V]),([X,_Sym],[_Sym]),([X,W],[W]),([_Sym],[_Sym]),([W],[W])]))),
    V==W,
    !,
    true((mshare([[V,X,_Sym,W],[V,X,W],[V,_Sym,W],[V,W],[X],[X,_Sym],[_Sym]]),shlin2([([V,X,_Sym,W],[]),([V,X,W],[]),([V,_Sym,W],[V,W]),([V,W],[V,W]),([X],[]),([X,_Sym],[]),([_Sym],[_Sym])]);mshare([[V,X,_Sym,W],[V,X,W],[V,_Sym,W],[V,W],[X],[X,_Sym],[_Sym]]),shlin2([([V,X,_Sym,W],[]),([V,X,W],[]),([V,_Sym,W],[V,W]),([V,W],[V,W]),([X],[]),([X,_Sym],[_Sym]),([_Sym],[_Sym])]);mshare([[V,X,_Sym,W],[V,X,W],[V,_Sym,W],[V,W],[X],[_Sym]]),linear(V),linear(W),shlin2([([V,X,_Sym,W],[V,W]),([V,X,W],[V,W]),([V,_Sym,W],[V,W]),([V,W],[V,W]),([X],[X]),([_Sym],[_Sym])]);mshare([[V,X,_Sym,W],[V,X,W],[V,_Sym,W],[V,W],[X,_Sym],[_Sym]]),shlin2([([V,X,_Sym,W],[]),([V,X,W],[]),([V,_Sym,W],[V,W]),([V,W],[V,W]),([X,_Sym],[_Sym]),([_Sym],[_Sym])]))).
retrieve_sym(V,[_1|Sym],X) :-
    true((mshare([[V],[V,X],[V,X,_1],[V,X,_1,Sym],[V,X,Sym],[V,_1],[V,_1,Sym],[V,Sym],[X],[X,_1],[X,_1,Sym],[X,Sym],[_1],[Sym]]),linear(V),shlin2([([V],[V]),([V,X],[V]),([V,X,_1],[V]),([V,X,_1,Sym],[V]),([V,X,Sym],[V]),([V,_1],[V]),([V,_1,Sym],[V]),([V,Sym],[V]),([X],[]),([X,_1],[]),([X,_1,Sym],[]),([X,Sym],[]),([_1],[_1]),([Sym],[Sym])]);mshare([[V],[V,X],[V,X,_1],[V,X,_1,Sym],[V,X,Sym],[V,_1],[V,_1,Sym],[V,Sym],[X],[X,_1],[X,Sym],[_1],[Sym]]),linear(V),shlin2([([V],[V]),([V,X],[V]),([V,X,_1],[V]),([V,X,_1,Sym],[V]),([V,X,Sym],[V]),([V,_1],[V]),([V,_1,Sym],[V]),([V,Sym],[V]),([X],[X]),([X,_1],[X,_1]),([X,Sym],[X,Sym]),([_1],[_1]),([Sym],[Sym])]);mshare([[V],[V,X,_1],[V,X,_1,Sym],[V,X,Sym],[V,_1],[V,_1,Sym],[V,Sym],[X],[X,_1],[X,_1,Sym],[X,Sym],[_1],[Sym]]),linear(V),shlin2([([V],[V]),([V,X,_1],[V]),([V,X,_1,Sym],[V]),([V,X,Sym],[V]),([V,_1],[V]),([V,_1,Sym],[V]),([V,Sym],[V]),([X],[X]),([X,_1],[]),([X,_1,Sym],[]),([X,Sym],[]),([_1],[_1]),([Sym],[Sym])]);mshare([[V],[V,_1],[V,_1,Sym],[V,Sym],[X],[_1],[Sym]]),linear(V),linear(X),shlin2([([V],[V]),([V,_1],[V]),([V,_1,Sym],[V]),([V,Sym],[V]),([X],[X]),([_1],[_1]),([Sym],[Sym])]);mshare([[V,X,_1],[V,X,_1,Sym],[V,X,Sym],[V,_1],[V,_1,Sym],[V,Sym],[X,_1],[X,_1,Sym],[X,Sym],[_1],[Sym]]),linear(V),shlin2([([V,X,_1],[V]),([V,X,_1,Sym],[V]),([V,X,Sym],[V]),([V,_1],[V]),([V,_1,Sym],[V]),([V,Sym],[V]),([X,_1],[]),([X,_1,Sym],[]),([X,Sym],[]),([_1],[_1]),([Sym],[Sym])]);mshare([[V,X,_1],[V,X,_1,Sym],[V,X,Sym],[V,_1],[V,_1,Sym],[V,Sym],[X,_1],[X,Sym],[_1],[Sym]]),linear(V),shlin2([([V,X,_1],[V]),([V,X,_1,Sym],[V]),([V,X,Sym],[V]),([V,_1],[V]),([V,_1,Sym],[V]),([V,Sym],[V]),([X,_1],[X,_1]),([X,Sym],[X,Sym]),([_1],[_1]),([Sym],[Sym])]))),
    retrieve_sym(V,Sym,X),
    true((mshare([[V,X,_1,Sym],[V,X,Sym],[V,_1,Sym],[V,Sym],[X,_1,Sym],[X,Sym],[_1],[Sym]]),shlin2([([V,X,_1,Sym],[]),([V,X,Sym],[]),([V,_1,Sym],[]),([V,Sym],[]),([X,_1,Sym],[]),([X,Sym],[]),([_1],[_1]),([Sym],[Sym])]);mshare([[V,X,_1,Sym],[V,X,Sym],[V,_1,Sym],[V,Sym],[X,Sym],[_1],[Sym]]),shlin2([([V,X,_1,Sym],[]),([V,X,Sym],[]),([V,_1,Sym],[]),([V,Sym],[]),([X,Sym],[X,Sym]),([_1],[_1]),([Sym],[Sym])]))).

:- true pred make_sym(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_B), shlin2([([_A],[]),([_B],[_B])]) )
   => ( mshare([[_A,_B],[_B]]),
        shlin2([([_A,_B],[]),([_B],[_B])]) ).

make_sym([],[]).
make_sym([V|L],[p(V,_1)|S]) :-
    true((
        mshare([[V],[V,L],[L],[S],[_1]]),
        linear(S),
        linear(_1),
        shlin2([([V],[]),([V,L],[]),([L],[]),([S],[S]),([_1],[_1])])
    )),
    make_sym(L,S),
    true((
        mshare([[V],[V,L,S],[L,S],[S],[_1]]),
        linear(_1),
        shlin2([([V],[]),([V,L,S],[]),([L,S],[]),([S],[S]),([_1],[_1])])
    )).

:- true pred varset(Term,VarSet)
   : ( mshare([[Term],[VarSet]]),
       linear(VarSet), shlin2([([Term],[]),([VarSet],[VarSet])]) )
   => ( mshare([[Term],[Term,VarSet]]),
        shlin2([([Term],[]),([Term,VarSet],[])]) ).

varset(Term,VarSet) :-
    true((
        mshare([[Term],[VarSet],[VB]]),
        linear(VarSet),
        linear(VB),
        shlin2([([Term],[]),([VarSet],[VarSet]),([VB],[VB])])
    )),
    varbag(Term,VB),
    true((
        mshare([[Term],[Term,VB],[VarSet]]),
        linear(VarSet),
        shlin2([([Term],[]),([Term,VB],[]),([VarSet],[VarSet])])
    )),
    sort(VB,VarSet),
    true((
        mshare([[Term],[Term,VarSet,VB]]),
        shlin2([([Term],[]),([Term,VarSet,VB],[])])
    )).

:- true pred varbag(Term,VarBag)
   : ( mshare([[Term],[VarBag]]),
       linear(VarBag), shlin2([([Term],[]),([VarBag],[VarBag])]) )
   => ( mshare([[Term],[Term,VarBag]]),
        shlin2([([Term],[]),([Term,VarBag],[])]) ).

varbag(Term,VarBag) :-
    true((
        mshare([[Term],[VarBag]]),
        linear(VarBag),
        shlin2([([Term],[]),([VarBag],[VarBag])])
    )),
    varbag(Term,VarBag,[]),
    true((
        mshare([[Term],[Term,VarBag]]),
        shlin2([([Term],[]),([Term,VarBag],[])])
    )).

:- true pred varbag(Var,_1,_2)
   : ( (_2=[]),
       mshare([[Var],[_1]]),
       linear(_1), shlin2([([Var],[]),([_1],[_1])]) )
   => ( mshare([[Var],[Var,_1]]),
        shlin2([([Var],[]),([Var,_1],[])]) ).

:- true pred varbag(Var,_1,_2)
   : ( mshare([[Var],[_1],[_2]]),
       linear(_1), linear(_2), shlin2([([Var],[]),([_1],[_1]),([_2],[_2])]) )
   => ( mshare([[Var],[Var,_1],[_1,_2]]),
        linear(_2), shlin2([([Var],[]),([Var,_1],[]),([_1,_2],[_1,_2])]) ).

varbag(Var,_1,_2) :-
    true((mshare([[Var],[_1]]),ground([_2]),linear(_1),shlin2([([Var],[]),([_1],[_1])]);mshare([[Var],[_1],[_2]]),linear(_1),linear(_2),shlin2([([Var],[]),([_1],[_1]),([_2],[_2])]))),
    var(Var),
    !,
    true((mshare([[Var],[_1]]),ground([_2]),linear(Var),linear(_1),shlin2([([Var],[Var]),([_1],[Var,_1])]);mshare([[Var],[_1],[_2]]),linear(Var),linear(_1),linear(_2),shlin2([([Var],[Var]),([_1],[Var,_1]),([_2],[Var,_2])]))),
    'C'(_1,Var,_2),
    true((mshare([[Var,_1]]),ground([_2]),linear(Var),linear(_1),shlin2([([Var,_1],[Var,_1])]);mshare([[Var,_1],[_1,_2]]),linear(Var),linear(_1),linear(_2),shlin2([([Var,_1],[Var,_1]),([_1,_2],[Var,_1,_2])]))).
varbag(Str,_1,_2) :-
    true((mshare([[Str],[_1],[_2],[_3],[Arity]]),linear(_1),linear(_2),linear(_3),linear(Arity),shlin2([([Str],[]),([_1],[_1]),([_2],[_2]),([_3],[_3]),([Arity],[Arity])]);mshare([[Str],[_1],[_3],[Arity]]),ground([_2]),linear(_1),linear(_3),linear(Arity),shlin2([([Str],[]),([_1],[_1]),([_3],[_3]),([Arity],[Arity])]))),
    nonvar(Str),
    !,
    true((mshare([[Str],[_1],[_2],[_3],[Arity]]),linear(_1),linear(_2),linear(_3),linear(Arity),shlin2([([Str],[]),([_1],[_1]),([_2],[_2]),([_3],[_3]),([Arity],[Arity])]);mshare([[Str],[_1],[_3],[Arity]]),ground([_2]),linear(_1),linear(_3),linear(Arity),shlin2([([Str],[]),([_1],[_1]),([_3],[_3]),([Arity],[Arity])]))),
    functor(Str,_3,Arity),
    true((mshare([[Str],[_1]]),ground([_2,_3,Arity]),linear(_1),shlin2([([Str],[]),([_1],[_1])]);mshare([[Str],[_1],[_2]]),ground([_3,Arity]),linear(_1),linear(_2),shlin2([([Str],[]),([_1],[_1]),([_2],[_2])]))),
    varbag(Str,1,Arity,_1,_2),
    true((mshare([[Str],[Str,_1]]),ground([_2,_3,Arity]),shlin2([([Str],[]),([Str,_1],[])]);mshare([[Str],[Str,_1],[_1,_2]]),ground([_3,Arity]),linear(_2),shlin2([([Str],[]),([Str,_1],[]),([_1,_2],[_1,_2])]))).

:- true pred varbag(_Str,N,Arity,_1,_2)
   : ( mshare([[_Str],[_1],[_2]]),
       ground([N,Arity]), linear(_1), linear(_2), shlin2([([_Str],[]),([_1],[_1]),([_2],[_2])]) )
   => ( mshare([[_Str],[_Str,_1],[_1,_2]]),
        ground([N,Arity]), linear(_2), shlin2([([_Str],[]),([_Str,_1],[]),([_1,_2],[_1,_2])]) ).

:- true pred varbag(_Str,N,Arity,_1,_2)
   : ( (N=1),
       mshare([[_Str],[_1],[_2]]),
       ground([Arity]), linear(_1), linear(_2), shlin2([([_Str],[]),([_1],[_1]),([_2],[_2])]) )
   => ( mshare([[_Str],[_Str,_1],[_1,_2]]),
        ground([Arity]), linear(_2), shlin2([([_Str],[]),([_Str,_1],[]),([_1,_2],[_1,_2])]) ).

:- true pred varbag(_Str,N,Arity,_1,_2)
   : ( (N=1),
       mshare([[_Str],[_1]]),
       ground([Arity,_2]), linear(_1), shlin2([([_Str],[]),([_1],[_1])]) )
   => ( mshare([[_Str],[_Str,_1]]),
        ground([Arity,_2]), shlin2([([_Str],[]),([_Str,_1],[])]) ).

:- true pred varbag(_Str,N,Arity,_1,_2)
   : ( mshare([[_Str],[_1]]),
       ground([N,Arity,_2]), linear(_1), shlin2([([_Str],[]),([_1],[_1])]) )
   => ( mshare([[_Str],[_Str,_1]]),
        ground([N,Arity,_2]), shlin2([([_Str],[]),([_Str,_1],[])]) ).

varbag(_Str,N,Arity,_1,_2) :-
    true((mshare([[_Str],[_1]]),ground([N,Arity,_2]),linear(_1),shlin2([([_Str],[]),([_1],[_1])]);mshare([[_Str],[_1],[_2]]),ground([N,Arity]),linear(_1),linear(_2),shlin2([([_Str],[]),([_1],[_1]),([_2],[_2])]))),
    N>Arity,
    !,
    true((mshare([[_Str],[_1]]),ground([N,Arity,_2]),linear(_1),shlin2([([_Str],[]),([_1],[_1])]);mshare([[_Str],[_1],[_2]]),ground([N,Arity]),linear(_1),linear(_2),shlin2([([_Str],[]),([_1],[_1]),([_2],[_2])]))),
    _2=_1,
    true((mshare([[_Str]]),ground([N,Arity,_1,_2]),shlin2([([_Str],[])]);mshare([[_Str],[_1,_2]]),ground([N,Arity]),linear(_1),linear(_2),shlin2([([_Str],[]),([_1,_2],[_1,_2])]))).
varbag(Str,N,Arity,_1,_2) :-
    true((mshare([[Str],[_1],[_2],[Arg],[_3],[N1]]),ground([N,Arity]),linear(_1),linear(_2),linear(Arg),linear(_3),linear(N1),shlin2([([Str],[]),([_1],[_1]),([_2],[_2]),([Arg],[Arg]),([_3],[_3]),([N1],[N1])]);mshare([[Str],[_1],[Arg],[_3],[N1]]),ground([N,Arity,_2]),linear(_1),linear(Arg),linear(_3),linear(N1),shlin2([([Str],[]),([_1],[_1]),([Arg],[Arg]),([_3],[_3]),([N1],[N1])]))),
    N=<Arity,
    !,
    true((mshare([[Str],[_1],[_2],[Arg],[_3],[N1]]),ground([N,Arity]),linear(_1),linear(_2),linear(Arg),linear(_3),linear(N1),shlin2([([Str],[]),([_1],[_1]),([_2],[_2]),([Arg],[Arg]),([_3],[_3]),([N1],[N1])]);mshare([[Str],[_1],[Arg],[_3],[N1]]),ground([N,Arity,_2]),linear(_1),linear(Arg),linear(_3),linear(N1),shlin2([([Str],[]),([_1],[_1]),([Arg],[Arg]),([_3],[_3]),([N1],[N1])]))),
    arg(N,Str,Arg),
    true((mshare([[Str,Arg],[_1],[_2],[_3],[N1]]),ground([N,Arity]),linear(_1),linear(_2),linear(_3),linear(N1),shlin2([([Str,Arg],[]),([_1],[_1]),([_2],[_2]),([_3],[_3]),([N1],[N1])]);mshare([[Str,Arg],[_1],[_3],[N1]]),ground([N,Arity,_2]),linear(_1),linear(_3),linear(N1),shlin2([([Str,Arg],[]),([_1],[_1]),([_3],[_3]),([N1],[N1])]))),
    varbag(Arg,_1,_3),
    true((mshare([[Str,_1,Arg],[Str,Arg],[_1,_3],[_2],[N1]]),ground([N,Arity]),linear(_2),linear(_3),linear(N1),shlin2([([Str,_1,Arg],[]),([Str,Arg],[]),([_1,_3],[_1,_3]),([_2],[_2]),([N1],[N1])]);mshare([[Str,_1,Arg],[Str,Arg],[_1,_3],[N1]]),ground([N,Arity,_2]),linear(_3),linear(N1),shlin2([([Str,_1,Arg],[]),([Str,Arg],[]),([_1,_3],[_1,_3]),([N1],[N1])]))),
    N1 is N+1,
    true((mshare([[Str,_1,Arg],[Str,Arg],[_1,_3]]),ground([N,Arity,_2,N1]),linear(_3),shlin2([([Str,_1,Arg],[]),([Str,Arg],[]),([_1,_3],[_1,_3])]);mshare([[Str,_1,Arg],[Str,Arg],[_1,_3],[_2]]),ground([N,Arity,N1]),linear(_2),linear(_3),shlin2([([Str,_1,Arg],[]),([Str,Arg],[]),([_1,_3],[_1,_3]),([_2],[_2])]))),
    varbag(Str,N1,Arity,_3,_2),
    true((mshare([[Str,_1,Arg],[Str,_1,Arg,_3],[Str,Arg]]),ground([N,Arity,_2,N1]),shlin2([([Str,_1,Arg],[]),([Str,_1,Arg,_3],[]),([Str,Arg],[])]);mshare([[Str,_1,Arg],[Str,_1,Arg,_3],[Str,Arg],[_1,_2,_3]]),ground([N,Arity,N1]),linear(_2),shlin2([([Str,_1,Arg],[]),([Str,_1,Arg,_3],[]),([Str,Arg],[]),([_1,_2,_3],[_1,_2,_3])]))).

:- true pred inst_vars(Term)
   : ( (Term=(_A,_B)),
       mshare([[_A],[_A,_B],[_B]]),
       shlin2([([_A],[]),([_A,_B],[]),([_B],[])]) )
   => ( mshare([[_A],[_A,_B],[_B]]),
        shlin2([([_A],[]),([_A,_B],[]),([_B],[])]) ).

inst_vars(Term) :-
    true((
        mshare([[Term],[Vars]]),
        linear(Vars),
        shlin2([([Term],[]),([Vars],[Vars])])
    )),
    varset(Term,Vars),
    true((
        mshare([[Term],[Term,Vars]]),
        shlin2([([Term],[]),([Term,Vars],[])])
    )),
    inst_vars_list(Vars,65),
    true((
        mshare([[Term]]),
        ground([Vars]),
        shlin2([([Term],[])])
    )).

:- true pred inst_vars_list(_A,_1)
   : ( (_1=65),
       mshare([[_A]]),
       shlin2([([_A],[])]) )
   => ground([_A]).

:- true pred inst_vars_list(_A,_1)
   : ( mshare([[_A]]),
       ground([_1]), shlin2([([_A],[])]) )
   => ground([_A,_1]).

inst_vars_list([],_1).
inst_vars_list([T|L],N) :-
    true((
        mshare([[T],[T,L],[L],[N1]]),
        ground([N]),
        linear(N1),
        shlin2([([T],[]),([T,L],[]),([L],[]),([N1],[N1])])
    )),
    atom_codes(T,[N]),
    true((
        mshare([[L],[N1]]),
        ground([N,T]),
        linear(N1),
        shlin2([([L],[]),([N1],[N1])])
    )),
    N1 is N+1,
    true((
        mshare([[L]]),
        ground([N,T,N1]),
        shlin2([([L],[])])
    )),
    inst_vars_list(L,N1),
    true(ground([N,T,L,N1])).

:- true pred sort_vars(V,Out)
   : ( mshare([[V],[Out]]),
       linear(Out), shlin2([([V],[]),([Out],[Out])]) )
   => ( mshare([[V,Out]]),
        shlin2([([V,Out],[])]) ).

sort_vars(V,Out) :-
    true((
        mshare([[V],[Out]]),
        linear(Out),
        shlin2([([V],[]),([Out],[Out])])
    )),
    sort_vars(V,Out,[]),
    true((
        mshare([[V,Out]]),
        shlin2([([V,Out],[])])
    )).

:- true pred sort_vars(_A,Link,_B)
   : ( mshare([[_A],[_A,_B],[Link],[_B]]),
       linear(Link), shlin2([([_A],[]),([_A,_B],[]),([Link],[Link]),([_B],[])]) )
   => ( mshare([[_A,Link],[_A,Link,_B],[Link,_B]]),
        shlin2([([_A,Link],[]),([_A,Link,_B],[]),([Link,_B],[])]) ).

:- true pred sort_vars(_A,Link,_B)
   : ( (_B=[]),
       mshare([[_A],[Link]]),
       linear(Link), shlin2([([_A],[]),([Link],[Link])]) )
   => ( mshare([[_A,Link]]),
        shlin2([([_A,Link],[])]) ).

:- true pred sort_vars(_A,Link,_B)
   : ( mshare([[_A],[_A,Link],[Link]]),
       ground([_B]), shlin2([([_A],[]),([_A,Link],[]),([Link],[])]) )
   => ( mshare([[_A,Link]]),
        ground([_B]), shlin2([([_A,Link],[])]) ).

:- true pred sort_vars(_A,Link,_B)
   : ( (_B=[_C|_D]),
       mshare([[_A],[_A,Link],[_A,Link,_C],[_A,_C],[Link],[Link,_C],[_C],[_D]]),
       linear(_D), shlin2([([_A],[]),([_A,Link],[]),([_A,Link,_C],[]),([_A,_C],[]),([Link],[]),([Link,_C],[]),([_C],[]),([_D],[_D])]) )
   => ( mshare([[_A,Link],[_A,Link,_C],[_A,Link,_C,_D],[_A,Link,_D],[Link,_C],[Link,_C,_D],[Link,_D]]),
        shlin2([([_A,Link],[]),([_A,Link,_C],[]),([_A,Link,_C,_D],[]),([_A,Link,_D],[]),([Link,_C],[]),([Link,_C,_D],[]),([Link,_D],[])]) ).

:- true pred sort_vars(_A,Link,_B)
   : ( mshare([[_A],[_A,Link],[_A,Link,_B],[_A,_B],[Link],[Link,_B],[_B]]),
       shlin2([([_A],[]),([_A,Link],[]),([_A,Link,_B],[]),([_A,_B],[]),([Link],[]),([Link,_B],[]),([_B],[])]) )
   => ( mshare([[_A,Link],[_A,Link,_B],[Link,_B]]),
        shlin2([([_A,Link],[]),([_A,Link,_B],[]),([Link,_B],[])]) ).

:- true pred sort_vars(_A,Link,_B)
   : ( (_B=[_C|_D]),
       mshare([[_A],[_A,_C],[Link],[_C],[_D]]),
       linear(Link), linear(_D), shlin2([([_A],[]),([_A,_C],[]),([Link],[Link]),([_C],[]),([_D],[_D])]) )
   => ( mshare([[_A,Link],[_A,Link,_C],[_A,Link,_C,_D],[_A,Link,_D],[Link,_C],[Link,_C,_D],[Link,_D]]),
        shlin2([([_A,Link],[]),([_A,Link,_C],[]),([_A,Link,_C,_D],[]),([_A,Link,_D],[]),([Link,_C],[]),([Link,_C,_D],[]),([Link,_D],[])]) ).

sort_vars([],Link,Link).
sort_vars([V|Vs],Result,Link) :-
    true((mshare([[Result],[Result,Link],[Result,Link,V],[Result,Link,V,Vs],[Result,Link,Vs],[Result,V],[Result,V,Vs],[Result,Vs],[Link],[Link,V],[Link,V,Vs],[Link,Vs],[V],[V,Vs],[Vs],[Smaller],[Bigger],[SLink]]),linear(Smaller),linear(Bigger),linear(SLink),shlin2([([Result],[]),([Result,Link],[]),([Result,Link,V],[]),([Result,Link,V,Vs],[]),([Result,Link,Vs],[]),([Result,V],[]),([Result,V,Vs],[]),([Result,Vs],[]),([Link],[]),([Link,V],[]),([Link,V,Vs],[]),([Link,Vs],[]),([V],[]),([V,Vs],[]),([Vs],[]),([Smaller],[Smaller]),([Bigger],[Bigger]),([SLink],[SLink])]);mshare([[Result],[Result,V],[Result,V,Vs],[Result,Vs],[V],[V,Vs],[Vs],[Smaller],[Bigger],[SLink]]),ground([Link]),linear(Smaller),linear(Bigger),linear(SLink),shlin2([([Result],[]),([Result,V],[]),([Result,V,Vs],[]),([Result,Vs],[]),([V],[]),([V,Vs],[]),([Vs],[]),([Smaller],[Smaller]),([Bigger],[Bigger]),([SLink],[SLink])]);mshare([[Result],[Link],[Link,V],[Link,V,Vs],[Link,Vs],[V],[V,Vs],[Vs],[Smaller],[Bigger],[SLink]]),linear(Result),linear(Smaller),linear(Bigger),linear(SLink),shlin2([([Result],[Result]),([Link],[]),([Link,V],[]),([Link,V,Vs],[]),([Link,Vs],[]),([V],[]),([V,Vs],[]),([Vs],[]),([Smaller],[Smaller]),([Bigger],[Bigger]),([SLink],[SLink])]);mshare([[Result],[V],[V,Vs],[Vs],[Smaller],[Bigger],[SLink]]),ground([Link]),linear(Result),linear(Smaller),linear(Bigger),linear(SLink),shlin2([([Result],[Result]),([V],[]),([V,Vs],[]),([Vs],[]),([Smaller],[Smaller]),([Bigger],[Bigger]),([SLink],[SLink])]))),
    split_vars(Vs,V,Smaller,Bigger),
    true((mshare([[Result],[Result,Link],[Result,Link,V],[Result,Link,V,Vs],[Result,Link,V,Vs,Smaller],[Result,Link,V,Vs,Smaller,Bigger],[Result,Link,V,Vs,Bigger],[Result,Link,Vs,Smaller],[Result,Link,Vs,Smaller,Bigger],[Result,Link,Vs,Bigger],[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Bigger],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Bigger],[Link],[Link,V],[Link,V,Vs],[Link,V,Vs,Smaller],[Link,V,Vs,Smaller,Bigger],[Link,V,Vs,Bigger],[Link,Vs,Smaller],[Link,Vs,Smaller,Bigger],[Link,Vs,Bigger],[V],[V,Vs],[V,Vs,Smaller],[V,Vs,Smaller,Bigger],[V,Vs,Bigger],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger],[SLink]]),linear(SLink),shlin2([([Result],[]),([Result,Link],[]),([Result,Link,V],[]),([Result,Link,V,Vs],[]),([Result,Link,V,Vs,Smaller],[]),([Result,Link,V,Vs,Smaller,Bigger],[]),([Result,Link,V,Vs,Bigger],[]),([Result,Link,Vs,Smaller],[]),([Result,Link,Vs,Smaller,Bigger],[]),([Result,Link,Vs,Bigger],[]),([Result,V],[]),([Result,V,Vs],[]),([Result,V,Vs,Smaller],[]),([Result,V,Vs,Smaller,Bigger],[]),([Result,V,Vs,Bigger],[]),([Result,Vs,Smaller],[]),([Result,Vs,Smaller,Bigger],[]),([Result,Vs,Bigger],[]),([Link],[]),([Link,V],[]),([Link,V,Vs],[]),([Link,V,Vs,Smaller],[]),([Link,V,Vs,Smaller,Bigger],[]),([Link,V,Vs,Bigger],[]),([Link,Vs,Smaller],[]),([Link,Vs,Smaller,Bigger],[]),([Link,Vs,Bigger],[]),([V],[]),([V,Vs],[]),([V,Vs,Smaller],[]),([V,Vs,Smaller,Bigger],[]),([V,Vs,Bigger],[]),([Vs,Smaller],[]),([Vs,Smaller,Bigger],[]),([Vs,Bigger],[]),([SLink],[SLink])]);mshare([[Result],[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Bigger],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Bigger],[V],[V,Vs],[V,Vs,Smaller],[V,Vs,Smaller,Bigger],[V,Vs,Bigger],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger],[SLink]]),ground([Link]),linear(SLink),shlin2([([Result],[]),([Result,V],[]),([Result,V,Vs],[]),([Result,V,Vs,Smaller],[]),([Result,V,Vs,Smaller,Bigger],[]),([Result,V,Vs,Bigger],[]),([Result,Vs,Smaller],[]),([Result,Vs,Smaller,Bigger],[]),([Result,Vs,Bigger],[]),([V],[]),([V,Vs],[]),([V,Vs,Smaller],[]),([V,Vs,Smaller,Bigger],[]),([V,Vs,Bigger],[]),([Vs,Smaller],[]),([Vs,Smaller,Bigger],[]),([Vs,Bigger],[]),([SLink],[SLink])]);mshare([[Result],[Link],[Link,V],[Link,V,Vs],[Link,V,Vs,Smaller],[Link,V,Vs,Smaller,Bigger],[Link,V,Vs,Bigger],[Link,Vs,Smaller],[Link,Vs,Smaller,Bigger],[Link,Vs,Bigger],[V],[V,Vs],[V,Vs,Smaller],[V,Vs,Smaller,Bigger],[V,Vs,Bigger],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger],[SLink]]),linear(Result),linear(SLink),shlin2([([Result],[Result]),([Link],[]),([Link,V],[]),([Link,V,Vs],[]),([Link,V,Vs,Smaller],[]),([Link,V,Vs,Smaller,Bigger],[]),([Link,V,Vs,Bigger],[]),([Link,Vs,Smaller],[]),([Link,Vs,Smaller,Bigger],[]),([Link,Vs,Bigger],[]),([V],[]),([V,Vs],[]),([V,Vs,Smaller],[]),([V,Vs,Smaller,Bigger],[]),([V,Vs,Bigger],[]),([Vs,Smaller],[]),([Vs,Smaller,Bigger],[]),([Vs,Bigger],[]),([SLink],[SLink])]);mshare([[Result],[V],[V,Vs],[V,Vs,Smaller],[V,Vs,Smaller,Bigger],[V,Vs,Bigger],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger],[SLink]]),ground([Link]),linear(Result),linear(SLink),shlin2([([Result],[Result]),([V],[]),([V,Vs],[]),([V,Vs,Smaller],[]),([V,Vs,Smaller,Bigger],[]),([V,Vs,Bigger],[]),([Vs,Smaller],[]),([Vs,Smaller,Bigger],[]),([Vs,Bigger],[]),([SLink],[SLink])]))),
    sort_vars(Smaller,Result,[V|SLink]),
    true((mshare([[Result,Link,V],[Result,Link,V,Vs],[Result,Link,V,Vs,Smaller],[Result,Link,V,Vs,Smaller,Bigger],[Result,Link,V,Vs,Smaller,Bigger,SLink],[Result,Link,V,Vs,Smaller,SLink],[Result,Link,V,Vs,Bigger],[Result,Link,V,Vs,Bigger,SLink],[Result,Link,V,Vs,SLink],[Result,Link,V,SLink],[Result,Link,Vs,Smaller],[Result,Link,Vs,Smaller,Bigger],[Result,Link,Vs,Smaller,Bigger,SLink],[Result,Link,Vs,Smaller,SLink],[Result,Link,Vs,Bigger,SLink],[Result,Link,SLink],[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Smaller,Bigger,SLink],[Result,V,Vs,Smaller,SLink],[Result,V,Vs,Bigger],[Result,V,Vs,Bigger,SLink],[Result,V,Vs,SLink],[Result,V,SLink],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Smaller,Bigger,SLink],[Result,Vs,Smaller,SLink],[Result,Vs,Bigger,SLink],[Result,SLink],[Link],[Link,Vs,Bigger],[Vs,Bigger]]),shlin2([([Result,Link,V],[]),([Result,Link,V,Vs],[]),([Result,Link,V,Vs,Smaller],[]),([Result,Link,V,Vs,Smaller,Bigger],[]),([Result,Link,V,Vs,Smaller,Bigger,SLink],[]),([Result,Link,V,Vs,Smaller,SLink],[]),([Result,Link,V,Vs,Bigger],[]),([Result,Link,V,Vs,Bigger,SLink],[]),([Result,Link,V,Vs,SLink],[]),([Result,Link,V,SLink],[]),([Result,Link,Vs,Smaller],[]),([Result,Link,Vs,Smaller,Bigger],[]),([Result,Link,Vs,Smaller,Bigger,SLink],[]),([Result,Link,Vs,Smaller,SLink],[]),([Result,Link,Vs,Bigger,SLink],[]),([Result,Link,SLink],[]),([Result,V],[]),([Result,V,Vs],[]),([Result,V,Vs,Smaller],[]),([Result,V,Vs,Smaller,Bigger],[]),([Result,V,Vs,Smaller,Bigger,SLink],[]),([Result,V,Vs,Smaller,SLink],[]),([Result,V,Vs,Bigger],[]),([Result,V,Vs,Bigger,SLink],[]),([Result,V,Vs,SLink],[]),([Result,V,SLink],[]),([Result,Vs,Smaller],[]),([Result,Vs,Smaller,Bigger],[]),([Result,Vs,Smaller,Bigger,SLink],[]),([Result,Vs,Smaller,SLink],[]),([Result,Vs,Bigger,SLink],[]),([Result,SLink],[]),([Link],[]),([Link,Vs,Bigger],[]),([Vs,Bigger],[])]);mshare([[Result,Link,V],[Result,Link,V,Vs],[Result,Link,V,Vs,Smaller],[Result,Link,V,Vs,Smaller,Bigger],[Result,Link,V,Vs,Smaller,Bigger,SLink],[Result,Link,V,Vs,Smaller,SLink],[Result,Link,V,Vs,Bigger],[Result,Link,V,Vs,Bigger,SLink],[Result,Link,V,Vs,SLink],[Result,Link,V,SLink],[Result,Link,Vs,Smaller],[Result,Link,Vs,Smaller,Bigger],[Result,Link,Vs,Smaller,Bigger,SLink],[Result,Link,Vs,Smaller,SLink],[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Smaller,Bigger,SLink],[Result,V,Vs,Smaller,SLink],[Result,V,Vs,Bigger],[Result,V,Vs,Bigger,SLink],[Result,V,Vs,SLink],[Result,V,SLink],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Smaller,Bigger,SLink],[Result,Vs,Smaller,SLink],[Result,SLink],[Link],[Link,Vs,Bigger],[Vs,Bigger]]),shlin2([([Result,Link,V],[]),([Result,Link,V,Vs],[]),([Result,Link,V,Vs,Smaller],[]),([Result,Link,V,Vs,Smaller,Bigger],[]),([Result,Link,V,Vs,Smaller,Bigger,SLink],[]),([Result,Link,V,Vs,Smaller,SLink],[]),([Result,Link,V,Vs,Bigger],[]),([Result,Link,V,Vs,Bigger,SLink],[]),([Result,Link,V,Vs,SLink],[]),([Result,Link,V,SLink],[]),([Result,Link,Vs,Smaller],[]),([Result,Link,Vs,Smaller,Bigger],[]),([Result,Link,Vs,Smaller,Bigger,SLink],[]),([Result,Link,Vs,Smaller,SLink],[]),([Result,V],[]),([Result,V,Vs],[]),([Result,V,Vs,Smaller],[]),([Result,V,Vs,Smaller,Bigger],[]),([Result,V,Vs,Smaller,Bigger,SLink],[]),([Result,V,Vs,Smaller,SLink],[]),([Result,V,Vs,Bigger],[]),([Result,V,Vs,Bigger,SLink],[]),([Result,V,Vs,SLink],[]),([Result,V,SLink],[]),([Result,Vs,Smaller],[]),([Result,Vs,Smaller,Bigger],[]),([Result,Vs,Smaller,Bigger,SLink],[]),([Result,Vs,Smaller,SLink],[]),([Result,SLink],[]),([Link],[]),([Link,Vs,Bigger],[]),([Vs,Bigger],[])]);mshare([[Result,Link,V],[Result,Link,V,Vs],[Result,Link,V,Vs,Bigger],[Result,V],[Result,V,Vs],[Result,V,Vs,Bigger],[Result,SLink],[Link],[Link,Vs,Bigger],[Vs,Bigger]]),ground([Smaller]),linear(SLink),shlin2([([Result,Link,V],[]),([Result,Link,V,Vs],[]),([Result,Link,V,Vs,Bigger],[]),([Result,V],[]),([Result,V,Vs],[]),([Result,V,Vs,Bigger],[]),([Result,SLink],[Result,SLink]),([Link],[]),([Link,Vs,Bigger],[]),([Vs,Bigger],[])]);mshare([[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Smaller,Bigger,SLink],[Result,V,Vs,Smaller,SLink],[Result,V,Vs,Bigger],[Result,V,Vs,Bigger,SLink],[Result,V,Vs,SLink],[Result,V,SLink],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Smaller,Bigger,SLink],[Result,Vs,Smaller,SLink],[Result,Vs,Bigger,SLink],[Result,SLink],[Vs,Bigger]]),ground([Link]),shlin2([([Result,V],[]),([Result,V,Vs],[]),([Result,V,Vs,Smaller],[]),([Result,V,Vs,Smaller,Bigger],[]),([Result,V,Vs,Smaller,Bigger,SLink],[]),([Result,V,Vs,Smaller,SLink],[]),([Result,V,Vs,Bigger],[]),([Result,V,Vs,Bigger,SLink],[]),([Result,V,Vs,SLink],[]),([Result,V,SLink],[]),([Result,Vs,Smaller],[]),([Result,Vs,Smaller,Bigger],[]),([Result,Vs,Smaller,Bigger,SLink],[]),([Result,Vs,Smaller,SLink],[]),([Result,Vs,Bigger,SLink],[]),([Result,SLink],[]),([Vs,Bigger],[])]);mshare([[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Smaller,Bigger,SLink],[Result,V,Vs,Smaller,SLink],[Result,V,Vs,Bigger],[Result,V,Vs,Bigger,SLink],[Result,V,Vs,SLink],[Result,V,SLink],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Smaller,Bigger,SLink],[Result,Vs,Smaller,SLink],[Result,SLink],[Vs,Bigger]]),ground([Link]),shlin2([([Result,V],[]),([Result,V,Vs],[]),([Result,V,Vs,Smaller],[]),([Result,V,Vs,Smaller,Bigger],[]),([Result,V,Vs,Smaller,Bigger,SLink],[]),([Result,V,Vs,Smaller,SLink],[]),([Result,V,Vs,Bigger],[]),([Result,V,Vs,Bigger,SLink],[]),([Result,V,Vs,SLink],[]),([Result,V,SLink],[]),([Result,Vs,Smaller],[]),([Result,Vs,Smaller,Bigger],[]),([Result,Vs,Smaller,Bigger,SLink],[]),([Result,Vs,Smaller,SLink],[]),([Result,SLink],[]),([Vs,Bigger],[])]))),
    sort_vars(Bigger,SLink,Link),
    true((mshare([[Result,Link,V,Vs,Smaller,Bigger,SLink],[Result,Link,V,Vs,Smaller,SLink],[Result,Link,V,Vs,Bigger,SLink],[Result,Link,V,Vs,SLink],[Result,Link,V,SLink],[Result,Link,Vs,Smaller,Bigger,SLink],[Result,Link,Vs,Smaller,SLink],[Result,Link,Vs,Bigger,SLink],[Result,Link,SLink],[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger,SLink],[Result,V,Vs,Bigger,SLink],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger,SLink],[Result,Vs,Bigger,SLink]]),shlin2([([Result,Link,V,Vs,Smaller,Bigger,SLink],[]),([Result,Link,V,Vs,Smaller,SLink],[]),([Result,Link,V,Vs,Bigger,SLink],[]),([Result,Link,V,Vs,SLink],[]),([Result,Link,V,SLink],[]),([Result,Link,Vs,Smaller,Bigger,SLink],[]),([Result,Link,Vs,Smaller,SLink],[]),([Result,Link,Vs,Bigger,SLink],[]),([Result,Link,SLink],[]),([Result,V],[]),([Result,V,Vs],[]),([Result,V,Vs,Smaller],[]),([Result,V,Vs,Smaller,Bigger,SLink],[]),([Result,V,Vs,Bigger,SLink],[]),([Result,Vs,Smaller],[]),([Result,Vs,Smaller,Bigger,SLink],[]),([Result,Vs,Bigger,SLink],[])]);mshare([[Result,Link,V,Vs,Bigger,SLink],[Result,Link,V,Vs,SLink],[Result,Link,V,SLink],[Result,Link,Vs,Bigger,SLink],[Result,Link,SLink],[Result,V],[Result,V,Vs],[Result,V,Vs,Bigger,SLink],[Result,Vs,Bigger,SLink]]),ground([Smaller]),shlin2([([Result,Link,V,Vs,Bigger,SLink],[]),([Result,Link,V,Vs,SLink],[]),([Result,Link,V,SLink],[]),([Result,Link,Vs,Bigger,SLink],[]),([Result,Link,SLink],[]),([Result,V],[]),([Result,V,Vs],[]),([Result,V,Vs,Bigger,SLink],[]),([Result,Vs,Bigger,SLink],[])]);mshare([[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger,SLink],[Result,V,Vs,Bigger,SLink],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger,SLink],[Result,Vs,Bigger,SLink]]),ground([Link]),shlin2([([Result,V],[]),([Result,V,Vs],[]),([Result,V,Vs,Smaller],[]),([Result,V,Vs,Smaller,Bigger,SLink],[]),([Result,V,Vs,Bigger,SLink],[]),([Result,Vs,Smaller],[]),([Result,Vs,Smaller,Bigger,SLink],[]),([Result,Vs,Bigger,SLink],[])]))).

:- true pred intersect_sorted_vars(_A,_1,Rs)
   : ( (_1=[_B|_C]),
       mshare([[_A],[_A,_B],[_A,_B,_C],[_A,_C],[Rs],[_B],[_B,_C],[_C]]),
       linear(Rs), shlin2([([_A],[]),([_A,_B],[]),([_A,_B,_C],[]),([_A,_C],[]),([Rs],[Rs]),([_B],[]),([_B,_C],[]),([_C],[])]) )
   => ( mshare([[_A],[_A,Rs,_B],[_A,Rs,_B,_C],[_A,Rs,_C],[_A,_B],[_A,_B,_C],[_A,_C],[_B],[_B,_C],[_C]]),
        shlin2([([_A],[]),([_A,Rs,_B],[]),([_A,Rs,_B,_C],[]),([_A,Rs,_C],[]),([_A,_B],[]),([_A,_B,_C],[]),([_A,_C],[]),([_B],[]),([_B,_C],[]),([_C],[])]) ).

:- true pred intersect_sorted_vars(_A,_1,Rs)
   : ( (_A=[_B|_C]),
       mshare([[_1],[_1,_B],[_1,_B,_C],[_1,_C],[Rs],[_B],[_B,_C],[_C]]),
       linear(Rs), shlin2([([_1],[]),([_1,_B],[]),([_1,_B,_C],[]),([_1,_C],[]),([Rs],[Rs]),([_B],[]),([_B,_C],[]),([_C],[])]) )
   => ( mshare([[_1],[_1,Rs,_B],[_1,Rs,_B,_C],[_1,Rs,_C],[_1,_B],[_1,_B,_C],[_1,_C],[_B],[_B,_C],[_C]]),
        shlin2([([_1],[]),([_1,Rs,_B],[]),([_1,Rs,_B,_C],[]),([_1,Rs,_C],[]),([_1,_B],[]),([_1,_B,_C],[]),([_1,_C],[]),([_B],[]),([_B,_C],[]),([_C],[])]) ).

:- true pred intersect_sorted_vars(_A,_1,Rs)
   : ( mshare([[_A],[_A,_1],[_1],[Rs]]),
       linear(Rs), shlin2([([_A],[]),([_A,_1],[]),([_1],[]),([Rs],[Rs])]) )
   => ( mshare([[_A],[_A,_1],[_A,_1,Rs],[_1]]),
        shlin2([([_A],[]),([_A,_1],[]),([_A,_1,Rs],[]),([_1],[])]) ).

intersect_sorted_vars([],_1,[]) :-
    !,
    true((
        mshare([[_1]]),
        shlin2([([_1],[])])
    )).
intersect_sorted_vars(_1,[],[]).
intersect_sorted_vars([X|Xs],[Y|Ys],[X|Rs]) :-
    true((
        mshare([[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys],[Rs]]),
        linear(Rs),
        shlin2([([X],[]),([X,Xs],[]),([X,Xs,Y],[]),([X,Xs,Y,Ys],[]),([X,Xs,Ys],[]),([X,Y],[]),([X,Y,Ys],[]),([X,Ys],[]),([Xs],[]),([Xs,Y],[]),([Xs,Y,Ys],[]),([Xs,Ys],[]),([Y],[]),([Y,Ys],[]),([Ys],[]),([Rs],[Rs])])
    )),
    X==Y,
    !,
    true((
        mshare([[X,Xs,Y],[X,Xs,Y,Ys],[X,Y],[X,Y,Ys],[Xs],[Xs,Ys],[Ys],[Rs]]),
        linear(Rs),
        shlin2([([X,Xs,Y],[]),([X,Xs,Y,Ys],[]),([X,Y],[]),([X,Y,Ys],[]),([Xs],[]),([Xs,Ys],[]),([Ys],[]),([Rs],[Rs])])
    )),
    intersect_sorted_vars(Xs,Ys,Rs),
    true((
        mshare([[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Y,Ys,Rs],[X,Y],[X,Y,Ys],[Xs],[Xs,Ys],[Xs,Ys,Rs],[Ys]]),
        shlin2([([X,Xs,Y],[]),([X,Xs,Y,Ys],[]),([X,Xs,Y,Ys,Rs],[]),([X,Y],[]),([X,Y,Ys],[]),([Xs],[]),([Xs,Ys],[]),([Xs,Ys,Rs],[]),([Ys],[])])
    )).
intersect_sorted_vars([X|Xs],[Y|Ys],Rs) :-
    true((
        mshare([[Rs],[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys]]),
        linear(Rs),
        shlin2([([Rs],[Rs]),([X],[]),([X,Xs],[]),([X,Xs,Y],[]),([X,Xs,Y,Ys],[]),([X,Xs,Ys],[]),([X,Y],[]),([X,Y,Ys],[]),([X,Ys],[]),([Xs],[]),([Xs,Y],[]),([Xs,Y,Ys],[]),([Xs,Ys],[]),([Y],[]),([Y,Ys],[]),([Ys],[])])
    )),
    X@<Y,
    !,
    true((
        mshare([[Rs],[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys]]),
        linear(Rs),
        shlin2([([Rs],[Rs]),([X],[]),([X,Xs],[]),([X,Xs,Y],[]),([X,Xs,Y,Ys],[]),([X,Xs,Ys],[]),([X,Y],[]),([X,Y,Ys],[]),([X,Ys],[]),([Xs],[]),([Xs,Y],[]),([Xs,Y,Ys],[]),([Xs,Ys],[]),([Y],[]),([Y,Ys],[]),([Ys],[])])
    )),
    intersect_sorted_vars(Xs,[Y|Ys],Rs),
    true((
        mshare([[Rs,X,Xs,Y],[Rs,X,Xs,Y,Ys],[Rs,X,Xs,Ys],[Rs,Xs,Y],[Rs,Xs,Y,Ys],[Rs,Xs,Ys],[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys]]),
        shlin2([([Rs,X,Xs,Y],[]),([Rs,X,Xs,Y,Ys],[]),([Rs,X,Xs,Ys],[]),([Rs,Xs,Y],[]),([Rs,Xs,Y,Ys],[]),([Rs,Xs,Ys],[]),([X],[]),([X,Xs],[]),([X,Xs,Y],[]),([X,Xs,Y,Ys],[]),([X,Xs,Ys],[]),([X,Y],[]),([X,Y,Ys],[]),([X,Ys],[]),([Xs],[]),([Xs,Y],[]),([Xs,Y,Ys],[]),([Xs,Ys],[]),([Y],[]),([Y,Ys],[]),([Ys],[])])
    )).
intersect_sorted_vars([X|Xs],[Y|Ys],Rs) :-
    true((
        mshare([[Rs],[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys]]),
        linear(Rs),
        shlin2([([Rs],[Rs]),([X],[]),([X,Xs],[]),([X,Xs,Y],[]),([X,Xs,Y,Ys],[]),([X,Xs,Ys],[]),([X,Y],[]),([X,Y,Ys],[]),([X,Ys],[]),([Xs],[]),([Xs,Y],[]),([Xs,Y,Ys],[]),([Xs,Ys],[]),([Y],[]),([Y,Ys],[]),([Ys],[])])
    )),
    X@>Y,
    !,
    true((
        mshare([[Rs],[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys]]),
        linear(Rs),
        shlin2([([Rs],[Rs]),([X],[]),([X,Xs],[]),([X,Xs,Y],[]),([X,Xs,Y,Ys],[]),([X,Xs,Ys],[]),([X,Y],[]),([X,Y,Ys],[]),([X,Ys],[]),([Xs],[]),([Xs,Y],[]),([Xs,Y,Ys],[]),([Xs,Ys],[]),([Y],[]),([Y,Ys],[]),([Ys],[])])
    )),
    intersect_sorted_vars([X|Xs],Ys,Rs),
    true((
        mshare([[Rs,X,Xs,Y,Ys],[Rs,X,Xs,Ys],[Rs,X,Y,Ys],[Rs,X,Ys],[Rs,Xs,Y,Ys],[Rs,Xs,Ys],[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys]]),
        shlin2([([Rs,X,Xs,Y,Ys],[]),([Rs,X,Xs,Ys],[]),([Rs,X,Y,Ys],[]),([Rs,X,Ys],[]),([Rs,Xs,Y,Ys],[]),([Rs,Xs,Ys],[]),([X],[]),([X,Xs],[]),([X,Xs,Y],[]),([X,Xs,Y,Ys],[]),([X,Xs,Ys],[]),([X,Y],[]),([X,Y,Ys],[]),([X,Ys],[]),([Xs],[]),([Xs,Y],[]),([Xs,Y,Ys],[]),([Xs,Ys],[]),([Y],[]),([Y,Ys],[]),([Ys],[])])
    )).

:- true pred split_vars(_A,_1,Ss,Bs)
   : ( mshare([[_A],[_A,_1],[_1],[Ss],[Bs]]),
       linear(Ss), linear(Bs), shlin2([([_A],[]),([_A,_1],[]),([_1],[]),([Ss],[Ss]),([Bs],[Bs])]) )
   => ( mshare([[_A,_1],[_A,_1,Ss],[_A,_1,Ss,Bs],[_A,_1,Bs],[_A,Ss],[_A,Ss,Bs],[_A,Bs],[_1]]),
        shlin2([([_A,_1],[]),([_A,_1,Ss],[]),([_A,_1,Ss,Bs],[]),([_A,_1,Bs],[]),([_A,Ss],[]),([_A,Ss,Bs],[]),([_A,Bs],[]),([_1],[])]) ).

split_vars([],_1,[],[]).
split_vars([V|Vs],A,[V|Ss],Bs) :-
    true((
        mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Bs],[V],[V,Vs],[Vs],[Ss]]),
        linear(Bs),
        linear(Ss),
        shlin2([([A],[]),([A,V],[]),([A,V,Vs],[]),([A,Vs],[]),([Bs],[Bs]),([V],[]),([V,Vs],[]),([Vs],[]),([Ss],[Ss])])
    )),
    V@<A,
    !,
    true((
        mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Bs],[V],[V,Vs],[Vs],[Ss]]),
        linear(Bs),
        linear(Ss),
        shlin2([([A],[]),([A,V],[]),([A,V,Vs],[]),([A,Vs],[]),([Bs],[Bs]),([V],[]),([V,Vs],[]),([Vs],[]),([Ss],[Ss])])
    )),
    split_vars(Vs,A,Ss,Bs),
    true((
        mshare([[A],[A,Bs,V,Vs],[A,Bs,V,Vs,Ss],[A,Bs,Vs],[A,Bs,Vs,Ss],[A,V],[A,V,Vs],[A,V,Vs,Ss],[A,Vs],[A,Vs,Ss],[Bs,V,Vs],[Bs,V,Vs,Ss],[Bs,Vs],[Bs,Vs,Ss],[V],[V,Vs,Ss],[Vs,Ss]]),
        shlin2([([A],[]),([A,Bs,V,Vs],[]),([A,Bs,V,Vs,Ss],[]),([A,Bs,Vs],[]),([A,Bs,Vs,Ss],[]),([A,V],[]),([A,V,Vs],[]),([A,V,Vs,Ss],[]),([A,Vs],[]),([A,Vs,Ss],[]),([Bs,V,Vs],[]),([Bs,V,Vs,Ss],[]),([Bs,Vs],[]),([Bs,Vs,Ss],[]),([V],[]),([V,Vs,Ss],[]),([Vs,Ss],[])])
    )).
split_vars([V|Vs],A,Ss,Bs) :-
    true((
        mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Ss],[Bs],[V],[V,Vs],[Vs]]),
        linear(Ss),
        linear(Bs),
        shlin2([([A],[]),([A,V],[]),([A,V,Vs],[]),([A,Vs],[]),([Ss],[Ss]),([Bs],[Bs]),([V],[]),([V,Vs],[]),([Vs],[])])
    )),
    V==A,
    !,
    true((
        mshare([[A,V],[A,V,Vs],[Ss],[Bs],[Vs]]),
        linear(Ss),
        linear(Bs),
        shlin2([([A,V],[]),([A,V,Vs],[]),([Ss],[Ss]),([Bs],[Bs]),([Vs],[])])
    )),
    split_vars(Vs,A,Ss,Bs),
    true((
        mshare([[A,Ss,Bs,V,Vs],[A,Ss,V,Vs],[A,Bs,V,Vs],[A,V],[A,V,Vs],[Ss,Bs,Vs],[Ss,Vs],[Bs,Vs]]),
        shlin2([([A,Ss,Bs,V,Vs],[]),([A,Ss,V,Vs],[]),([A,Bs,V,Vs],[]),([A,V],[]),([A,V,Vs],[]),([Ss,Bs,Vs],[]),([Ss,Vs],[]),([Bs,Vs],[])])
    )).
split_vars([V|Vs],A,Ss,[V|Bs]) :-
    true((
        mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Ss],[V],[V,Vs],[Vs],[Bs]]),
        linear(Ss),
        linear(Bs),
        shlin2([([A],[]),([A,V],[]),([A,V,Vs],[]),([A,Vs],[]),([Ss],[Ss]),([V],[]),([V,Vs],[]),([Vs],[]),([Bs],[Bs])])
    )),
    V@>A,
    !,
    true((
        mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Ss],[V],[V,Vs],[Vs],[Bs]]),
        linear(Ss),
        linear(Bs),
        shlin2([([A],[]),([A,V],[]),([A,V,Vs],[]),([A,Vs],[]),([Ss],[Ss]),([V],[]),([V,Vs],[]),([Vs],[]),([Bs],[Bs])])
    )),
    split_vars(Vs,A,Ss,Bs),
    true((
        mshare([[A],[A,Ss,V,Vs],[A,Ss,V,Vs,Bs],[A,Ss,Vs],[A,Ss,Vs,Bs],[A,V],[A,V,Vs],[A,V,Vs,Bs],[A,Vs],[A,Vs,Bs],[Ss,V,Vs],[Ss,V,Vs,Bs],[Ss,Vs],[Ss,Vs,Bs],[V],[V,Vs,Bs],[Vs,Bs]]),
        shlin2([([A],[]),([A,Ss,V,Vs],[]),([A,Ss,V,Vs,Bs],[]),([A,Ss,Vs],[]),([A,Ss,Vs,Bs],[]),([A,V],[]),([A,V,Vs],[]),([A,V,Vs,Bs],[]),([A,Vs],[]),([A,Vs,Bs],[]),([Ss,V,Vs],[]),([Ss,V,Vs,Bs],[]),([Ss,Vs],[]),([Ss,Vs,Bs],[]),([V],[]),([V,Vs,Bs],[]),([Vs,Bs],[])])
    )).

