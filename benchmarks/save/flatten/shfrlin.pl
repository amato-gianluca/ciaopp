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
        var(X),
        var(Y),
        var(A),
        var(B),
        var(C),
        linear(X),
        linear(Y),
        linear(A),
        linear(B),
        linear(C)
    )),
    eliminate_disjunctions([(a(A,B,C):-b(A);c(C))],X,Y,[]),
    true(mshare([[X],[X,Y],[X,Y,A],[X,Y,A,B],[X,Y,A,B,C],[X,Y,A,C],[X,Y,B],[X,Y,B,C],[X,Y,C],[X,A],[X,A,B],[X,A,B,C],[X,A,C],[X,B],[X,B,C],[X,C],[Y],[Y,A],[Y,A,B],[Y,A,B,C],[Y,A,C],[Y,B],[Y,B,C],[Y,C],[A],[A,B],[A,B,C],[A,C],[B],[B,C],[C]])),
    inst_vars((X,Y)),
    true(mshare([[X],[X,Y],[X,Y,A],[X,Y,A,B],[X,Y,A,B,C],[X,Y,A,C],[X,Y,B],[X,Y,B,C],[X,Y,C],[X,A],[X,A,B],[X,A,B,C],[X,A,C],[X,B],[X,B,C],[X,C],[Y],[Y,A],[Y,A,B],[Y,A,B,C],[Y,A,C],[Y,B],[Y,B,C],[Y,C],[A],[A,B],[A,B,C],[A,C],[B],[B,C],[C]])).
top.

:- true pred eliminate_disjunctions(OneProc,NewProc,NewClauses,Link)
   : ( (OneProc=[(a(_A,_B,_C):-b(_A);c(_C))]), (Link=[]),
       mshare([[NewProc],[NewClauses],[_A],[_B],[_C]]),
       var(NewProc), var(NewClauses), var(_A), var(_B), var(_C), linear(NewProc), linear(NewClauses), linear(_A), linear(_B), linear(_C) )
   => mshare([[NewProc],[NewProc,NewClauses],[NewProc,NewClauses,_A],[NewProc,NewClauses,_A,_B],[NewProc,NewClauses,_A,_B,_C],[NewProc,NewClauses,_A,_C],[NewProc,NewClauses,_B],[NewProc,NewClauses,_B,_C],[NewProc,NewClauses,_C],[NewProc,_A],[NewProc,_A,_B],[NewProc,_A,_B,_C],[NewProc,_A,_C],[NewProc,_B],[NewProc,_B,_C],[NewProc,_C],[NewClauses],[NewClauses,_A],[NewClauses,_A,_B],[NewClauses,_A,_B,_C],[NewClauses,_A,_C],[NewClauses,_B],[NewClauses,_B,_C],[NewClauses,_C],[_A],[_A,_B],[_A,_B,_C],[_A,_C],[_B],[_B,_C],[_C]]).

eliminate_disjunctions(OneProc,NewProc,NewClauses,Link) :-
    true((
        mshare([[OneProc],[NewProc],[NewClauses],[Disj]]),
        var(NewProc),
        var(NewClauses),
        var(Disj),
        ground([Link]),
        linear(NewProc),
        linear(NewClauses),
        linear(Disj)
    )),
    gather_disj(OneProc,NewProc,Disj,[]),
    true((
        mshare([[OneProc,NewProc],[OneProc,NewProc,Disj],[OneProc,Disj],[NewProc,Disj],[NewClauses]]),
        var(NewClauses),
        ground([Link]),
        linear(NewClauses)
    )),
    treat_disj(Disj,NewClauses,Link),
    true((
        mshare([[OneProc,NewProc],[OneProc,NewProc,NewClauses,Disj],[OneProc,NewProc,Disj],[OneProc,NewClauses,Disj],[OneProc,Disj],[NewProc,NewClauses,Disj],[NewProc,Disj],[NewClauses]]),
        ground([Link])
    )).

:- true pred gather_disj(_A,NewProc,Link,_B)
   : ( (_B=[]),
       mshare([[_A],[NewProc],[Link]]),
       var(NewProc), var(Link), linear(NewProc), linear(Link) )
   => mshare([[_A,NewProc],[_A,NewProc,Link],[_A,Link],[NewProc,Link]]).

:- true pred gather_disj(_A,NewProc,Link,_B)
   : ( mshare([[_A],[NewProc],[Link]]),
       var(NewProc), var(Link), ground([_B]), linear(NewProc), linear(Link) )
   => ( mshare([[_A,NewProc],[_A,NewProc,Link],[_A,Link],[NewProc,Link]]),
        ground([_B]) ).

gather_disj([],[],Link,Link).
gather_disj([C|Cs],NewProc,Disj,Link) :-
    true((
        mshare([[NewProc],[Disj],[C],[C,Cs],[Cs],[NewC],[Rest],[NewCs]]),
        var(NewProc),
        var(Disj),
        var(NewC),
        var(Rest),
        var(NewCs),
        ground([Link]),
        linear(NewProc),
        linear(Disj),
        linear(NewC),
        linear(Rest),
        linear(NewCs)
    )),
    extract_disj(C,NewC,Disj,Rest),
    true((
        mshare([[NewProc],[Disj,C],[Disj,C,Cs],[Disj,C,Cs,NewC],[Disj,C,NewC],[Disj,NewC],[Disj,Rest],[C,Cs,NewC],[C,NewC],[Cs],[NewCs]]),
        var(NewProc),
        var(Rest),
        var(NewCs),
        ground([Link]),
        linear(NewProc),
        linear(Rest),
        linear(NewCs)
    )),
    NewProc=[NewC|NewCs],
    true((
        mshare([[NewProc,Disj,C,Cs,NewC],[NewProc,Disj,C,NewC],[NewProc,Disj,NewC],[NewProc,C,Cs,NewC],[NewProc,C,NewC],[NewProc,NewCs],[Disj,C],[Disj,C,Cs],[Disj,Rest],[Cs]]),
        var(Rest),
        var(NewCs),
        ground([Link]),
        linear(Rest),
        linear(NewCs)
    )),
    gather_disj(Cs,NewCs,Rest,Link),
    true((
        mshare([[NewProc,Disj,C,Cs,NewC,Rest],[NewProc,Disj,C,Cs,NewC,Rest,NewCs],[NewProc,Disj,C,Cs,NewC,NewCs],[NewProc,Disj,C,Cs,Rest,NewCs],[NewProc,Disj,C,Cs,NewCs],[NewProc,Disj,C,NewC],[NewProc,Disj,Cs,Rest,NewCs],[NewProc,Disj,NewC],[NewProc,Disj,Rest,NewCs],[NewProc,C,Cs,NewC,NewCs],[NewProc,C,NewC],[NewProc,Cs,NewCs],[Disj,C],[Disj,C,Cs,Rest],[Disj,Cs,Rest]]),
        ground([Link])
    )).

:- true pred extract_disj(C,Head,Disj,Link)
   : ( mshare([[C],[Head],[Disj],[Link]]),
       var(Head), var(Disj), var(Link), linear(Head), linear(Disj), linear(Link) )
   => ( mshare([[C,Head],[C,Head,Disj],[C,Disj],[Head,Disj],[Disj,Link]]),
        var(Link), linear(Link) ).

extract_disj(C,(Head:-NewBody),Disj,Link) :-
    true((
        mshare([[C],[Disj],[Link],[Head],[NewBody],[Body],[CtrIn],[CtrOut]]),
        var(Disj),
        var(Link),
        var(Head),
        var(NewBody),
        var(Body),
        var(CtrIn),
        var(CtrOut),
        linear(Disj),
        linear(Link),
        linear(Head),
        linear(NewBody),
        linear(Body),
        linear(CtrIn),
        linear(CtrOut)
    )),
    C=(Head:-Body),
    !,
    true((
        mshare([[C,Head],[C,Head,Body],[C,Body],[Disj],[Link],[NewBody],[CtrIn],[CtrOut]]),
        var(Disj),
        var(Link),
        var(NewBody),
        var(CtrIn),
        var(CtrOut),
        linear(Disj),
        linear(Link),
        linear(NewBody),
        linear(CtrIn),
        linear(CtrOut)
    )),
    CtrIn=0,
    true((
        mshare([[C,Head],[C,Head,Body],[C,Body],[Disj],[Link],[NewBody],[CtrOut]]),
        var(Disj),
        var(Link),
        var(NewBody),
        var(CtrOut),
        ground([CtrIn]),
        linear(Disj),
        linear(Link),
        linear(NewBody),
        linear(CtrOut)
    )),
    extract_disj(Body,NewBody,Disj,Link,C,CtrIn,CtrOut),
    true((
        mshare([[C,Disj,Head],[C,Disj,Head,NewBody,Body],[C,Disj,Head,Body],[C,Disj,NewBody,Body],[C,Disj,Body],[C,Head],[C,Head,NewBody,Body],[C,NewBody,Body],[Disj,Link],[Disj,NewBody]]),
        var(Link),
        ground([CtrIn,CtrOut]),
        linear(Link)
    )).
extract_disj(Head,Head,Link,Link).

:- true pred extract_disj(Goal,X,Disj,Link,C,CtrIn,CtrOut)
   : ( mshare([[Goal,C],[X],[Disj],[Link],[C],[CtrOut]]),
       var(X), var(Disj), var(Link), var(CtrOut), ground([CtrIn]), linear(X), linear(Disj), linear(Link), linear(CtrOut) )
   => ( mshare([[Goal,X,Disj,C],[Goal,X,C],[Goal,Disj,C],[X,Disj],[Disj,Link],[Disj,C],[C]]),
        var(Link), ground([CtrIn,CtrOut]), linear(Link) ).

extract_disj((C1,C2),(NewC1,NewC2),Disj,Link,C,CtrIn,CtrOut) :-
    true((
        mshare([[Disj],[Link],[C],[C,C1],[C,C1,C2],[C,C2],[CtrOut],[NewC1],[NewC2],[Link1],[Ctr]]),
        var(Disj),
        var(Link),
        var(CtrOut),
        var(NewC1),
        var(NewC2),
        var(Link1),
        var(Ctr),
        ground([CtrIn]),
        linear(Disj),
        linear(Link),
        linear(CtrOut),
        linear(NewC1),
        linear(NewC2),
        linear(Link1),
        linear(Ctr)
    )),
    extract_disj(C1,NewC1,Disj,Link1,C,CtrIn,Ctr),
    true((
        mshare([[Disj,C],[Disj,C,C1],[Disj,C,C1,C2],[Disj,C,C1,C2,NewC1],[Disj,C,C1,NewC1],[Disj,C,C2],[Disj,NewC1],[Disj,Link1],[Link],[C],[C,C1,C2,NewC1],[C,C1,NewC1],[C,C2],[CtrOut],[NewC2]]),
        var(Link),
        var(CtrOut),
        var(NewC2),
        var(Link1),
        ground([CtrIn,Ctr]),
        linear(Link),
        linear(CtrOut),
        linear(NewC2),
        linear(Link1)
    )),
    extract_disj(C2,NewC2,Link1,Link,C,Ctr,CtrOut),
    true((
        mshare([[Disj,Link,Link1],[Disj,C],[Disj,C,C1],[Disj,C,C1,C2,NewC1,NewC2],[Disj,C,C1,C2,NewC1,NewC2,Link1],[Disj,C,C1,C2,NewC1,Link1],[Disj,C,C1,C2,NewC2],[Disj,C,C1,C2,NewC2,Link1],[Disj,C,C1,C2,Link1],[Disj,C,C1,NewC1],[Disj,C,C1,NewC1,Link1],[Disj,C,C1,Link1],[Disj,C,C2,NewC2],[Disj,C,C2,NewC2,Link1],[Disj,C,C2,Link1],[Disj,C,Link1],[Disj,NewC1],[Disj,NewC2,Link1],[C],[C,C1,C2,NewC1,NewC2],[C,C1,NewC1],[C,C2,NewC2]]),
        var(Link),
        ground([CtrIn,CtrOut,Ctr]),
        linear(Link)
    )).
extract_disj(Goal,X,Disj,Link,C,CtrIn,CtrOut) :-
    true((
        mshare([[Goal,C],[X],[Disj],[Link],[C],[CtrOut],[NewGoal]]),
        var(X),
        var(Disj),
        var(Link),
        var(CtrOut),
        var(NewGoal),
        ground([CtrIn]),
        linear(X),
        linear(Disj),
        linear(Link),
        linear(CtrOut),
        linear(NewGoal)
    )),
    is_disj(Goal,NewGoal),
    !,
    true((
        mshare([[Goal,C,NewGoal],[X],[Disj],[Link],[C],[CtrOut]]),
        var(X),
        var(Disj),
        var(Link),
        var(CtrOut),
        ground([CtrIn]),
        linear(X),
        linear(Disj),
        linear(Link),
        linear(CtrOut)
    )),
    Disj=[disj(NewGoal,CtrIn,X,C)|Link],
    true((
        mshare([[Goal,Disj,C,NewGoal],[X,Disj],[Disj,Link],[Disj,C],[CtrOut]]),
        var(X),
        var(Link),
        var(CtrOut),
        ground([CtrIn]),
        linear(X),
        linear(Link),
        linear(CtrOut)
    )),
    CtrOut is CtrIn+1,
    true((
        mshare([[Goal,Disj,C,NewGoal],[X,Disj],[Disj,Link],[Disj,C]]),
        var(X),
        var(Link),
        ground([CtrIn,CtrOut]),
        linear(X),
        linear(Link)
    )).
extract_disj(Goal,Goal,Link,Link,_1,CtrIn,CtrIn).

:- true pred is_disj(_A,_B)
   : ( mshare([[_A],[_B]]),
       var(_B), linear(_B) )
   => mshare([[_A,_B]]).

is_disj((C1->C2;C3),(C1,!,C2;C3)) :-
    !,
    true(mshare([[C3],[C3,C1],[C3,C1,C2],[C3,C2],[C1],[C1,C2],[C2]])).
is_disj((C1;C2),(C1;C2)).
is_disj(not(C),(C,!,fail;true)).
is_disj(\+C,(C,!,fail;true)).
is_disj(C1\=C2,(C1=C2,!,fail;true)).

:- true pred treat_disj(_A,Link,_B)
   : ( mshare([[_A],[Link]]),
       var(Link), ground([_B]), linear(Link) )
   => ( mshare([[_A],[_A,Link],[Link]]),
        ground([_B]) ).

treat_disj([],Link,Link).
treat_disj([disj((A;B),N,X,C)|Disjs],DummyClauses,Link) :-
    true((
        mshare([[DummyClauses],[Disjs],[Disjs,N],[Disjs,N,X],[Disjs,N,X,C],[Disjs,N,X,C,A],[Disjs,N,X,C,A,B],[Disjs,N,X,C,B],[Disjs,N,X,A],[Disjs,N,X,A,B],[Disjs,N,X,B],[Disjs,N,C],[Disjs,N,C,A],[Disjs,N,C,A,B],[Disjs,N,C,B],[Disjs,N,A],[Disjs,N,A,B],[Disjs,N,B],[Disjs,X],[Disjs,X,C],[Disjs,X,C,A],[Disjs,X,C,A,B],[Disjs,X,C,B],[Disjs,X,A],[Disjs,X,A,B],[Disjs,X,B],[Disjs,C],[Disjs,C,A],[Disjs,C,A,B],[Disjs,C,B],[Disjs,A],[Disjs,A,B],[Disjs,B],[N],[N,X],[N,X,C],[N,X,C,A],[N,X,C,A,B],[N,X,C,B],[N,X,A],[N,X,A,B],[N,X,B],[N,C],[N,C,A],[N,C,A,B],[N,C,B],[N,A],[N,A,B],[N,B],[X],[X,C],[X,C,A],[X,C,A,B],[X,C,B],[X,A],[X,A,B],[X,B],[C],[C,A],[C,A,B],[C,B],[A],[A,B],[B],[Vars],[CVars],[Args],[Name],[Rest]]),
        var(DummyClauses),
        var(Vars),
        var(CVars),
        var(Args),
        var(Name),
        var(Rest),
        ground([Link]),
        linear(DummyClauses),
        linear(Vars),
        linear(CVars),
        linear(Args),
        linear(Name),
        linear(Rest)
    )),
    find_vars((A;B),Vars),
    true((
        mshare([[DummyClauses],[Disjs],[Disjs,N],[Disjs,N,X],[Disjs,N,X,C],[Disjs,N,X,C,A,B,Vars],[Disjs,N,X,C,A,Vars],[Disjs,N,X,C,B,Vars],[Disjs,N,X,A,B,Vars],[Disjs,N,X,A,Vars],[Disjs,N,X,B,Vars],[Disjs,N,C],[Disjs,N,C,A,B,Vars],[Disjs,N,C,A,Vars],[Disjs,N,C,B,Vars],[Disjs,N,A,B,Vars],[Disjs,N,A,Vars],[Disjs,N,B,Vars],[Disjs,X],[Disjs,X,C],[Disjs,X,C,A,B,Vars],[Disjs,X,C,A,Vars],[Disjs,X,C,B,Vars],[Disjs,X,A,B,Vars],[Disjs,X,A,Vars],[Disjs,X,B,Vars],[Disjs,C],[Disjs,C,A,B,Vars],[Disjs,C,A,Vars],[Disjs,C,B,Vars],[Disjs,A,B,Vars],[Disjs,A,Vars],[Disjs,B,Vars],[N],[N,X],[N,X,C],[N,X,C,A,B,Vars],[N,X,C,A,Vars],[N,X,C,B,Vars],[N,X,A,B,Vars],[N,X,A,Vars],[N,X,B,Vars],[N,C],[N,C,A,B,Vars],[N,C,A,Vars],[N,C,B,Vars],[N,A,B,Vars],[N,A,Vars],[N,B,Vars],[X],[X,C],[X,C,A,B,Vars],[X,C,A,Vars],[X,C,B,Vars],[X,A,B,Vars],[X,A,Vars],[X,B,Vars],[C],[C,A,B,Vars],[C,A,Vars],[C,B,Vars],[A,B,Vars],[A,Vars],[B,Vars],[CVars],[Args],[Name],[Rest]]),
        var(DummyClauses),
        var(CVars),
        var(Args),
        var(Name),
        var(Rest),
        ground([Link]),
        linear(DummyClauses),
        linear(Vars),
        linear(CVars),
        linear(Args),
        linear(Name),
        linear(Rest)
    )),
    find_vars(C,CVars),
    true((
        mshare([[DummyClauses],[Disjs],[Disjs,N],[Disjs,N,X],[Disjs,N,X,C,A,B,Vars,CVars],[Disjs,N,X,C,A,Vars,CVars],[Disjs,N,X,C,B,Vars,CVars],[Disjs,N,X,C,CVars],[Disjs,N,X,A,B,Vars],[Disjs,N,X,A,Vars],[Disjs,N,X,B,Vars],[Disjs,N,C,A,B,Vars,CVars],[Disjs,N,C,A,Vars,CVars],[Disjs,N,C,B,Vars,CVars],[Disjs,N,C,CVars],[Disjs,N,A,B,Vars],[Disjs,N,A,Vars],[Disjs,N,B,Vars],[Disjs,X],[Disjs,X,C,A,B,Vars,CVars],[Disjs,X,C,A,Vars,CVars],[Disjs,X,C,B,Vars,CVars],[Disjs,X,C,CVars],[Disjs,X,A,B,Vars],[Disjs,X,A,Vars],[Disjs,X,B,Vars],[Disjs,C,A,B,Vars,CVars],[Disjs,C,A,Vars,CVars],[Disjs,C,B,Vars,CVars],[Disjs,C,CVars],[Disjs,A,B,Vars],[Disjs,A,Vars],[Disjs,B,Vars],[N],[N,X],[N,X,C,A,B,Vars,CVars],[N,X,C,A,Vars,CVars],[N,X,C,B,Vars,CVars],[N,X,C,CVars],[N,X,A,B,Vars],[N,X,A,Vars],[N,X,B,Vars],[N,C,A,B,Vars,CVars],[N,C,A,Vars,CVars],[N,C,B,Vars,CVars],[N,C,CVars],[N,A,B,Vars],[N,A,Vars],[N,B,Vars],[X],[X,C,A,B,Vars,CVars],[X,C,A,Vars,CVars],[X,C,B,Vars,CVars],[X,C,CVars],[X,A,B,Vars],[X,A,Vars],[X,B,Vars],[C,A,B,Vars,CVars],[C,A,Vars,CVars],[C,B,Vars,CVars],[C,CVars],[A,B,Vars],[A,Vars],[B,Vars],[Args],[Name],[Rest]]),
        var(DummyClauses),
        var(Args),
        var(Name),
        var(Rest),
        ground([Link]),
        linear(DummyClauses),
        linear(Vars),
        linear(CVars),
        linear(Args),
        linear(Name),
        linear(Rest)
    )),
    intersect_vars(Vars,CVars,Args),
    true((
        mshare([[DummyClauses],[Disjs],[Disjs,N],[Disjs,N,X],[Disjs,N,X,C,A,B,Vars,CVars],[Disjs,N,X,C,A,B,Vars,CVars,Args],[Disjs,N,X,C,A,Vars,CVars],[Disjs,N,X,C,A,Vars,CVars,Args],[Disjs,N,X,C,B,Vars,CVars],[Disjs,N,X,C,B,Vars,CVars,Args],[Disjs,N,X,C,CVars],[Disjs,N,X,A,B,Vars],[Disjs,N,X,A,B,Vars,Args],[Disjs,N,X,A,Vars],[Disjs,N,X,A,Vars,Args],[Disjs,N,X,B,Vars],[Disjs,N,X,B,Vars,Args],[Disjs,N,C,A,B,Vars,CVars],[Disjs,N,C,A,B,Vars,CVars,Args],[Disjs,N,C,A,Vars,CVars],[Disjs,N,C,A,Vars,CVars,Args],[Disjs,N,C,B,Vars,CVars],[Disjs,N,C,B,Vars,CVars,Args],[Disjs,N,C,CVars],[Disjs,N,A,B,Vars],[Disjs,N,A,B,Vars,Args],[Disjs,N,A,Vars],[Disjs,N,A,Vars,Args],[Disjs,N,B,Vars],[Disjs,N,B,Vars,Args],[Disjs,X],[Disjs,X,C,A,B,Vars,CVars],[Disjs,X,C,A,B,Vars,CVars,Args],[Disjs,X,C,A,Vars,CVars],[Disjs,X,C,A,Vars,CVars,Args],[Disjs,X,C,B,Vars,CVars],[Disjs,X,C,B,Vars,CVars,Args],[Disjs,X,C,CVars],[Disjs,X,A,B,Vars],[Disjs,X,A,B,Vars,Args],[Disjs,X,A,Vars],[Disjs,X,A,Vars,Args],[Disjs,X,B,Vars],[Disjs,X,B,Vars,Args],[Disjs,C,A,B,Vars,CVars],[Disjs,C,A,B,Vars,CVars,Args],[Disjs,C,A,Vars,CVars],[Disjs,C,A,Vars,CVars,Args],[Disjs,C,B,Vars,CVars],[Disjs,C,B,Vars,CVars,Args],[Disjs,C,CVars],[Disjs,A,B,Vars],[Disjs,A,B,Vars,Args],[Disjs,A,Vars],[Disjs,A,Vars,Args],[Disjs,B,Vars],[Disjs,B,Vars,Args],[N],[N,X],[N,X,C,A,B,Vars,CVars],[N,X,C,A,B,Vars,CVars,Args],[N,X,C,A,Vars,CVars],[N,X,C,A,Vars,CVars,Args],[N,X,C,B,Vars,CVars],[N,X,C,B,Vars,CVars,Args],[N,X,C,CVars],[N,X,A,B,Vars],[N,X,A,B,Vars,Args],[N,X,A,Vars],[N,X,A,Vars,Args],[N,X,B,Vars],[N,X,B,Vars,Args],[N,C,A,B,Vars,CVars],[N,C,A,B,Vars,CVars,Args],[N,C,A,Vars,CVars],[N,C,A,Vars,CVars,Args],[N,C,B,Vars,CVars],[N,C,B,Vars,CVars,Args],[N,C,CVars],[N,A,B,Vars],[N,A,B,Vars,Args],[N,A,Vars],[N,A,Vars,Args],[N,B,Vars],[N,B,Vars,Args],[X],[X,C,A,B,Vars,CVars],[X,C,A,B,Vars,CVars,Args],[X,C,A,Vars,CVars],[X,C,A,Vars,CVars,Args],[X,C,B,Vars,CVars],[X,C,B,Vars,CVars,Args],[X,C,CVars],[X,A,B,Vars],[X,A,B,Vars,Args],[X,A,Vars],[X,A,Vars,Args],[X,B,Vars],[X,B,Vars,Args],[C,A,B,Vars,CVars],[C,A,B,Vars,CVars,Args],[C,A,Vars,CVars],[C,A,Vars,CVars,Args],[C,B,Vars,CVars],[C,B,Vars,CVars,Args],[C,CVars],[A,B,Vars],[A,B,Vars,Args],[A,Vars],[A,Vars,Args],[B,Vars],[B,Vars,Args],[Name],[Rest]]),
        var(DummyClauses),
        var(Name),
        var(Rest),
        ground([Link]),
        linear(DummyClauses),
        linear(Name),
        linear(Rest)
    )),
    make_dummy_name(N,Name),
    true((
        mshare([[DummyClauses],[Disjs],[Disjs,N],[Disjs,N,X],[Disjs,N,X,C,A,B,Vars,CVars],[Disjs,N,X,C,A,B,Vars,CVars,Args],[Disjs,N,X,C,A,B,Vars,CVars,Args,Name],[Disjs,N,X,C,A,B,Vars,CVars,Name],[Disjs,N,X,C,A,Vars,CVars],[Disjs,N,X,C,A,Vars,CVars,Args],[Disjs,N,X,C,A,Vars,CVars,Args,Name],[Disjs,N,X,C,A,Vars,CVars,Name],[Disjs,N,X,C,B,Vars,CVars],[Disjs,N,X,C,B,Vars,CVars,Args],[Disjs,N,X,C,B,Vars,CVars,Args,Name],[Disjs,N,X,C,B,Vars,CVars,Name],[Disjs,N,X,C,CVars],[Disjs,N,X,C,CVars,Name],[Disjs,N,X,A,B,Vars],[Disjs,N,X,A,B,Vars,Args],[Disjs,N,X,A,B,Vars,Args,Name],[Disjs,N,X,A,B,Vars,Name],[Disjs,N,X,A,Vars],[Disjs,N,X,A,Vars,Args],[Disjs,N,X,A,Vars,Args,Name],[Disjs,N,X,A,Vars,Name],[Disjs,N,X,B,Vars],[Disjs,N,X,B,Vars,Args],[Disjs,N,X,B,Vars,Args,Name],[Disjs,N,X,B,Vars,Name],[Disjs,N,X,Name],[Disjs,N,C,A,B,Vars,CVars],[Disjs,N,C,A,B,Vars,CVars,Args],[Disjs,N,C,A,B,Vars,CVars,Args,Name],[Disjs,N,C,A,B,Vars,CVars,Name],[Disjs,N,C,A,Vars,CVars],[Disjs,N,C,A,Vars,CVars,Args],[Disjs,N,C,A,Vars,CVars,Args,Name],[Disjs,N,C,A,Vars,CVars,Name],[Disjs,N,C,B,Vars,CVars],[Disjs,N,C,B,Vars,CVars,Args],[Disjs,N,C,B,Vars,CVars,Args,Name],[Disjs,N,C,B,Vars,CVars,Name],[Disjs,N,C,CVars],[Disjs,N,C,CVars,Name],[Disjs,N,A,B,Vars],[Disjs,N,A,B,Vars,Args],[Disjs,N,A,B,Vars,Args,Name],[Disjs,N,A,B,Vars,Name],[Disjs,N,A,Vars],[Disjs,N,A,Vars,Args],[Disjs,N,A,Vars,Args,Name],[Disjs,N,A,Vars,Name],[Disjs,N,B,Vars],[Disjs,N,B,Vars,Args],[Disjs,N,B,Vars,Args,Name],[Disjs,N,B,Vars,Name],[Disjs,N,Name],[Disjs,X],[Disjs,X,C,A,B,Vars,CVars],[Disjs,X,C,A,B,Vars,CVars,Args],[Disjs,X,C,A,Vars,CVars],[Disjs,X,C,A,Vars,CVars,Args],[Disjs,X,C,B,Vars,CVars],[Disjs,X,C,B,Vars,CVars,Args],[Disjs,X,C,CVars],[Disjs,X,A,B,Vars],[Disjs,X,A,B,Vars,Args],[Disjs,X,A,Vars],[Disjs,X,A,Vars,Args],[Disjs,X,B,Vars],[Disjs,X,B,Vars,Args],[Disjs,C,A,B,Vars,CVars],[Disjs,C,A,B,Vars,CVars,Args],[Disjs,C,A,Vars,CVars],[Disjs,C,A,Vars,CVars,Args],[Disjs,C,B,Vars,CVars],[Disjs,C,B,Vars,CVars,Args],[Disjs,C,CVars],[Disjs,A,B,Vars],[Disjs,A,B,Vars,Args],[Disjs,A,Vars],[Disjs,A,Vars,Args],[Disjs,B,Vars],[Disjs,B,Vars,Args],[N],[N,X],[N,X,C,A,B,Vars,CVars],[N,X,C,A,B,Vars,CVars,Args],[N,X,C,A,B,Vars,CVars,Args,Name],[N,X,C,A,B,Vars,CVars,Name],[N,X,C,A,Vars,CVars],[N,X,C,A,Vars,CVars,Args],[N,X,C,A,Vars,CVars,Args,Name],[N,X,C,A,Vars,CVars,Name],[N,X,C,B,Vars,CVars],[N,X,C,B,Vars,CVars,Args],[N,X,C,B,Vars,CVars,Args,Name],[N,X,C,B,Vars,CVars,Name],[N,X,C,CVars],[N,X,C,CVars,Name],[N,X,A,B,Vars],[N,X,A,B,Vars,Args],[N,X,A,B,Vars,Args,Name],[N,X,A,B,Vars,Name],[N,X,A,Vars],[N,X,A,Vars,Args],[N,X,A,Vars,Args,Name],[N,X,A,Vars,Name],[N,X,B,Vars],[N,X,B,Vars,Args],[N,X,B,Vars,Args,Name],[N,X,B,Vars,Name],[N,X,Name],[N,C,A,B,Vars,CVars],[N,C,A,B,Vars,CVars,Args],[N,C,A,B,Vars,CVars,Args,Name],[N,C,A,B,Vars,CVars,Name],[N,C,A,Vars,CVars],[N,C,A,Vars,CVars,Args],[N,C,A,Vars,CVars,Args,Name],[N,C,A,Vars,CVars,Name],[N,C,B,Vars,CVars],[N,C,B,Vars,CVars,Args],[N,C,B,Vars,CVars,Args,Name],[N,C,B,Vars,CVars,Name],[N,C,CVars],[N,C,CVars,Name],[N,A,B,Vars],[N,A,B,Vars,Args],[N,A,B,Vars,Args,Name],[N,A,B,Vars,Name],[N,A,Vars],[N,A,Vars,Args],[N,A,Vars,Args,Name],[N,A,Vars,Name],[N,B,Vars],[N,B,Vars,Args],[N,B,Vars,Args,Name],[N,B,Vars,Name],[N,Name],[X],[X,C,A,B,Vars,CVars],[X,C,A,B,Vars,CVars,Args],[X,C,A,Vars,CVars],[X,C,A,Vars,CVars,Args],[X,C,B,Vars,CVars],[X,C,B,Vars,CVars,Args],[X,C,CVars],[X,A,B,Vars],[X,A,B,Vars,Args],[X,A,Vars],[X,A,Vars,Args],[X,B,Vars],[X,B,Vars,Args],[C,A,B,Vars,CVars],[C,A,B,Vars,CVars,Args],[C,A,Vars,CVars],[C,A,Vars,CVars,Args],[C,B,Vars,CVars],[C,B,Vars,CVars,Args],[C,CVars],[A,B,Vars],[A,B,Vars,Args],[A,Vars],[A,Vars,Args],[B,Vars],[B,Vars,Args],[Name],[Rest]]),
        var(DummyClauses),
        var(Rest),
        ground([Link]),
        linear(DummyClauses),
        linear(Rest)
    )),
    X=..[Name|Args],
    true((
        mshare([[DummyClauses],[Disjs],[Disjs,N],[Disjs,N,X,C,A,B,Vars,CVars,Args],[Disjs,N,X,C,A,Vars,CVars,Args],[Disjs,N,X,C,B,Vars,CVars,Args],[Disjs,N,X,A,B,Vars,Args],[Disjs,N,X,A,Vars,Args],[Disjs,N,X,B,Vars,Args],[Disjs,N,C,A,B,Vars,CVars],[Disjs,N,C,A,Vars,CVars],[Disjs,N,C,B,Vars,CVars],[Disjs,N,C,CVars],[Disjs,N,A,B,Vars],[Disjs,N,A,Vars],[Disjs,N,B,Vars],[Disjs,X,C,A,B,Vars,CVars,Args],[Disjs,X,C,A,Vars,CVars,Args],[Disjs,X,C,B,Vars,CVars,Args],[Disjs,X,A,B,Vars,Args],[Disjs,X,A,Vars,Args],[Disjs,X,B,Vars,Args],[Disjs,C,A,B,Vars,CVars],[Disjs,C,A,Vars,CVars],[Disjs,C,B,Vars,CVars],[Disjs,C,CVars],[Disjs,A,B,Vars],[Disjs,A,Vars],[Disjs,B,Vars],[N],[N,X,C,A,B,Vars,CVars,Args],[N,X,C,A,Vars,CVars,Args],[N,X,C,B,Vars,CVars,Args],[N,X,A,B,Vars,Args],[N,X,A,Vars,Args],[N,X,B,Vars,Args],[N,C,A,B,Vars,CVars],[N,C,A,Vars,CVars],[N,C,B,Vars,CVars],[N,C,CVars],[N,A,B,Vars],[N,A,Vars],[N,B,Vars],[X,C,A,B,Vars,CVars,Args],[X,C,A,Vars,CVars,Args],[X,C,B,Vars,CVars,Args],[X,A,B,Vars,Args],[X,A,Vars,Args],[X,B,Vars,Args],[C,A,B,Vars,CVars],[C,A,Vars,CVars],[C,B,Vars,CVars],[C,CVars],[A,B,Vars],[A,Vars],[B,Vars],[Rest]]),
        var(DummyClauses),
        var(Rest),
        ground([Link,Name]),
        linear(DummyClauses),
        linear(Rest)
    )),
    make_dummy_clauses((A;B),X,DummyClauses,Rest),
    true((
        mshare([[DummyClauses],[DummyClauses,Disjs,N,X,C,A,B,Vars,CVars,Args],[DummyClauses,Disjs,N,X,C,A,Vars,CVars,Args],[DummyClauses,Disjs,N,X,C,B,Vars,CVars,Args],[DummyClauses,Disjs,N,X,A,B,Vars,Args],[DummyClauses,Disjs,N,X,A,Vars,Args],[DummyClauses,Disjs,N,X,B,Vars,Args],[DummyClauses,Disjs,N,C,A,B,Vars,CVars],[DummyClauses,Disjs,N,C,A,Vars,CVars],[DummyClauses,Disjs,N,C,B,Vars,CVars],[DummyClauses,Disjs,N,A,B,Vars],[DummyClauses,Disjs,N,A,Vars],[DummyClauses,Disjs,N,B,Vars],[DummyClauses,Disjs,X,C,A,B,Vars,CVars,Args],[DummyClauses,Disjs,X,C,A,Vars,CVars,Args],[DummyClauses,Disjs,X,C,B,Vars,CVars,Args],[DummyClauses,Disjs,X,A,B,Vars,Args],[DummyClauses,Disjs,X,A,Vars,Args],[DummyClauses,Disjs,X,B,Vars,Args],[DummyClauses,Disjs,C,A,B,Vars,CVars],[DummyClauses,Disjs,C,A,Vars,CVars],[DummyClauses,Disjs,C,B,Vars,CVars],[DummyClauses,Disjs,A,B,Vars],[DummyClauses,Disjs,A,Vars],[DummyClauses,Disjs,B,Vars],[DummyClauses,N,X,C,A,B,Vars,CVars,Args],[DummyClauses,N,X,C,A,Vars,CVars,Args],[DummyClauses,N,X,C,B,Vars,CVars,Args],[DummyClauses,N,X,A,B,Vars,Args],[DummyClauses,N,X,A,Vars,Args],[DummyClauses,N,X,B,Vars,Args],[DummyClauses,N,C,A,B,Vars,CVars],[DummyClauses,N,C,A,Vars,CVars],[DummyClauses,N,C,B,Vars,CVars],[DummyClauses,N,A,B,Vars],[DummyClauses,N,A,Vars],[DummyClauses,N,B,Vars],[DummyClauses,X,C,A,B,Vars,CVars,Args],[DummyClauses,X,C,A,Vars,CVars,Args],[DummyClauses,X,C,B,Vars,CVars,Args],[DummyClauses,X,A,B,Vars,Args],[DummyClauses,X,A,Vars,Args],[DummyClauses,X,B,Vars,Args],[DummyClauses,C,A,B,Vars,CVars],[DummyClauses,C,A,Vars,CVars],[DummyClauses,C,B,Vars,CVars],[DummyClauses,A,B,Vars],[DummyClauses,A,Vars],[DummyClauses,B,Vars],[DummyClauses,Rest],[Disjs],[Disjs,N],[Disjs,N,X,C,A,B,Vars,CVars,Args],[Disjs,N,X,C,A,Vars,CVars,Args],[Disjs,N,X,C,B,Vars,CVars,Args],[Disjs,N,X,A,B,Vars,Args],[Disjs,N,X,A,Vars,Args],[Disjs,N,X,B,Vars,Args],[Disjs,N,C,A,B,Vars,CVars],[Disjs,N,C,A,Vars,CVars],[Disjs,N,C,B,Vars,CVars],[Disjs,N,C,CVars],[Disjs,N,A,B,Vars],[Disjs,N,A,Vars],[Disjs,N,B,Vars],[Disjs,X,C,A,B,Vars,CVars,Args],[Disjs,X,C,A,Vars,CVars,Args],[Disjs,X,C,B,Vars,CVars,Args],[Disjs,X,A,B,Vars,Args],[Disjs,X,A,Vars,Args],[Disjs,X,B,Vars,Args],[Disjs,C,A,B,Vars,CVars],[Disjs,C,A,Vars,CVars],[Disjs,C,B,Vars,CVars],[Disjs,C,CVars],[Disjs,A,B,Vars],[Disjs,A,Vars],[Disjs,B,Vars],[N],[N,X,C,A,B,Vars,CVars,Args],[N,X,C,A,Vars,CVars,Args],[N,X,C,B,Vars,CVars,Args],[N,X,A,B,Vars,Args],[N,X,A,Vars,Args],[N,X,B,Vars,Args],[N,C,A,B,Vars,CVars],[N,C,A,Vars,CVars],[N,C,B,Vars,CVars],[N,C,CVars],[N,A,B,Vars],[N,A,Vars],[N,B,Vars],[X,C,A,B,Vars,CVars,Args],[X,C,A,Vars,CVars,Args],[X,C,B,Vars,CVars,Args],[X,A,B,Vars,Args],[X,A,Vars,Args],[X,B,Vars,Args],[C,A,B,Vars,CVars],[C,A,Vars,CVars],[C,B,Vars,CVars],[C,CVars],[A,B,Vars],[A,Vars],[B,Vars]]),
        var(Rest),
        ground([Link,Name]),
        linear(Rest)
    )),
    treat_disj(Disjs,Rest,Link),
    true((
        mshare([[DummyClauses],[DummyClauses,Disjs,N,X,C,A,B,Vars,CVars,Args],[DummyClauses,Disjs,N,X,C,A,B,Vars,CVars,Args,Rest],[DummyClauses,Disjs,N,X,C,A,Vars,CVars,Args],[DummyClauses,Disjs,N,X,C,A,Vars,CVars,Args,Rest],[DummyClauses,Disjs,N,X,C,B,Vars,CVars,Args],[DummyClauses,Disjs,N,X,C,B,Vars,CVars,Args,Rest],[DummyClauses,Disjs,N,X,A,B,Vars,Args],[DummyClauses,Disjs,N,X,A,B,Vars,Args,Rest],[DummyClauses,Disjs,N,X,A,Vars,Args],[DummyClauses,Disjs,N,X,A,Vars,Args,Rest],[DummyClauses,Disjs,N,X,B,Vars,Args],[DummyClauses,Disjs,N,X,B,Vars,Args,Rest],[DummyClauses,Disjs,N,C,A,B,Vars,CVars],[DummyClauses,Disjs,N,C,A,B,Vars,CVars,Rest],[DummyClauses,Disjs,N,C,A,Vars,CVars],[DummyClauses,Disjs,N,C,A,Vars,CVars,Rest],[DummyClauses,Disjs,N,C,B,Vars,CVars],[DummyClauses,Disjs,N,C,B,Vars,CVars,Rest],[DummyClauses,Disjs,N,C,CVars,Rest],[DummyClauses,Disjs,N,A,B,Vars],[DummyClauses,Disjs,N,A,B,Vars,Rest],[DummyClauses,Disjs,N,A,Vars],[DummyClauses,Disjs,N,A,Vars,Rest],[DummyClauses,Disjs,N,B,Vars],[DummyClauses,Disjs,N,B,Vars,Rest],[DummyClauses,Disjs,N,Rest],[DummyClauses,Disjs,X,C,A,B,Vars,CVars,Args],[DummyClauses,Disjs,X,C,A,B,Vars,CVars,Args,Rest],[DummyClauses,Disjs,X,C,A,Vars,CVars,Args],[DummyClauses,Disjs,X,C,A,Vars,CVars,Args,Rest],[DummyClauses,Disjs,X,C,B,Vars,CVars,Args],[DummyClauses,Disjs,X,C,B,Vars,CVars,Args,Rest],[DummyClauses,Disjs,X,A,B,Vars,Args],[DummyClauses,Disjs,X,A,B,Vars,Args,Rest],[DummyClauses,Disjs,X,A,Vars,Args],[DummyClauses,Disjs,X,A,Vars,Args,Rest],[DummyClauses,Disjs,X,B,Vars,Args],[DummyClauses,Disjs,X,B,Vars,Args,Rest],[DummyClauses,Disjs,C,A,B,Vars,CVars],[DummyClauses,Disjs,C,A,B,Vars,CVars,Rest],[DummyClauses,Disjs,C,A,Vars,CVars],[DummyClauses,Disjs,C,A,Vars,CVars,Rest],[DummyClauses,Disjs,C,B,Vars,CVars],[DummyClauses,Disjs,C,B,Vars,CVars,Rest],[DummyClauses,Disjs,C,CVars,Rest],[DummyClauses,Disjs,A,B,Vars],[DummyClauses,Disjs,A,B,Vars,Rest],[DummyClauses,Disjs,A,Vars],[DummyClauses,Disjs,A,Vars,Rest],[DummyClauses,Disjs,B,Vars],[DummyClauses,Disjs,B,Vars,Rest],[DummyClauses,Disjs,Rest],[DummyClauses,N,X,C,A,B,Vars,CVars,Args],[DummyClauses,N,X,C,A,Vars,CVars,Args],[DummyClauses,N,X,C,B,Vars,CVars,Args],[DummyClauses,N,X,A,B,Vars,Args],[DummyClauses,N,X,A,Vars,Args],[DummyClauses,N,X,B,Vars,Args],[DummyClauses,N,C,A,B,Vars,CVars],[DummyClauses,N,C,A,Vars,CVars],[DummyClauses,N,C,B,Vars,CVars],[DummyClauses,N,A,B,Vars],[DummyClauses,N,A,Vars],[DummyClauses,N,B,Vars],[DummyClauses,X,C,A,B,Vars,CVars,Args],[DummyClauses,X,C,A,Vars,CVars,Args],[DummyClauses,X,C,B,Vars,CVars,Args],[DummyClauses,X,A,B,Vars,Args],[DummyClauses,X,A,Vars,Args],[DummyClauses,X,B,Vars,Args],[DummyClauses,C,A,B,Vars,CVars],[DummyClauses,C,A,Vars,CVars],[DummyClauses,C,B,Vars,CVars],[DummyClauses,A,B,Vars],[DummyClauses,A,Vars],[DummyClauses,B,Vars],[DummyClauses,Rest],[Disjs],[Disjs,N],[Disjs,N,X,C,A,B,Vars,CVars,Args],[Disjs,N,X,C,A,Vars,CVars,Args],[Disjs,N,X,C,B,Vars,CVars,Args],[Disjs,N,X,A,B,Vars,Args],[Disjs,N,X,A,Vars,Args],[Disjs,N,X,B,Vars,Args],[Disjs,N,C,A,B,Vars,CVars],[Disjs,N,C,A,Vars,CVars],[Disjs,N,C,B,Vars,CVars],[Disjs,N,C,CVars],[Disjs,N,A,B,Vars],[Disjs,N,A,Vars],[Disjs,N,B,Vars],[Disjs,X,C,A,B,Vars,CVars,Args],[Disjs,X,C,A,Vars,CVars,Args],[Disjs,X,C,B,Vars,CVars,Args],[Disjs,X,A,B,Vars,Args],[Disjs,X,A,Vars,Args],[Disjs,X,B,Vars,Args],[Disjs,C,A,B,Vars,CVars],[Disjs,C,A,Vars,CVars],[Disjs,C,B,Vars,CVars],[Disjs,C,CVars],[Disjs,A,B,Vars],[Disjs,A,Vars],[Disjs,B,Vars],[N],[N,X,C,A,B,Vars,CVars,Args],[N,X,C,A,Vars,CVars,Args],[N,X,C,B,Vars,CVars,Args],[N,X,A,B,Vars,Args],[N,X,A,Vars,Args],[N,X,B,Vars,Args],[N,C,A,B,Vars,CVars],[N,C,A,Vars,CVars],[N,C,B,Vars,CVars],[N,C,CVars],[N,A,B,Vars],[N,A,Vars],[N,B,Vars],[X,C,A,B,Vars,CVars,Args],[X,C,A,Vars,CVars,Args],[X,C,B,Vars,CVars,Args],[X,A,B,Vars,Args],[X,A,Vars,Args],[X,B,Vars,Args],[C,A,B,Vars,CVars],[C,A,Vars,CVars],[C,B,Vars,CVars],[C,CVars],[A,B,Vars],[A,Vars],[B,Vars]]),
        ground([Link,Name])
    )).

:- true pred make_dummy_clauses(A,X,_A,Link)
   : ( (A=(_B;_C)),
       mshare([[X,_B],[X,_B,_C],[X,_C],[_A],[Link],[_B],[_B,_C],[_C]]),
       var(_A), var(Link), linear(_A), linear(Link) )
   => ( mshare([[X,_A,_B],[X,_A,_B,_C],[X,_A,_C],[X,_B],[X,_B,_C],[X,_C],[_A],[_A,Link],[_A,_B],[_A,_B,_C],[_A,_C],[_B],[_B,_C],[_C]]),
        var(Link), linear(Link) ).

:- true pred make_dummy_clauses(A,X,_A,Link)
   : ( mshare([[A],[A,X],[X],[_A],[Link]]),
       var(_A), var(Link), linear(_A), linear(Link) )
   => ( mshare([[A],[A,X],[A,X,_A],[A,_A],[X],[X,_A],[_A],[_A,Link]]),
        var(Link), linear(Link) ).

make_dummy_clauses((A;B),X,[NewC|Cs],Link) :-
    !,
    true((mshare([[X],[X,A],[X,A,B],[X,B],[Link],[A],[A,B],[B],[NewC],[Cs]]),var(Link),var(NewC),var(Cs),linear(Link),linear(NewC),linear(Cs);mshare([[X,A],[X,A,B],[X,B],[Link],[A],[A,B],[B],[NewC],[Cs]]),var(Link),var(NewC),var(Cs),linear(Link),linear(NewC),linear(Cs))),
    copy((X:-A),NewC),
    true((mshare([[X],[X,A],[X,A,B],[X,A,B,NewC],[X,A,NewC],[X,B],[X,B,NewC],[X,NewC],[Link],[A],[A,B],[A,B,NewC],[A,NewC],[B],[NewC],[Cs]]),var(Link),var(Cs),linear(Link),linear(Cs);mshare([[X,A],[X,A,B],[X,A,B,NewC],[X,A,NewC],[X,B],[X,B,NewC],[Link],[A],[A,B],[A,B,NewC],[A,NewC],[B],[NewC],[Cs]]),var(Link),var(Cs),linear(Link),linear(Cs))),
    make_dummy_clauses(B,X,Cs,Link),
    true((mshare([[X],[X,A],[X,A,B],[X,A,B,NewC],[X,A,B,NewC,Cs],[X,A,B,Cs],[X,A,NewC],[X,A,NewC,Cs],[X,A,Cs],[X,B],[X,B,NewC],[X,B,NewC,Cs],[X,B,Cs],[X,NewC],[X,NewC,Cs],[X,Cs],[Link,Cs],[A],[A,B],[A,B,NewC],[A,B,NewC,Cs],[A,B,Cs],[A,NewC],[B],[B,Cs],[NewC],[Cs]]),var(Link),linear(Link);mshare([[X,A],[X,A,B],[X,A,B,NewC],[X,A,B,NewC,Cs],[X,A,B,Cs],[X,A,NewC],[X,A,NewC,Cs],[X,A,Cs],[X,B],[X,B,NewC],[X,B,NewC,Cs],[X,B,Cs],[Link,Cs],[A],[A,B],[A,B,NewC],[A,B,NewC,Cs],[A,B,Cs],[A,NewC],[B],[B,Cs],[NewC],[Cs]]),var(Link),linear(Link))).
make_dummy_clauses(A,X,[NewC|Link],Link) :-
    true((mshare([[A],[A,X],[X],[Link],[NewC]]),var(Link),var(NewC),linear(Link),linear(NewC);mshare([[A],[A,X],[Link],[NewC]]),var(Link),var(NewC),linear(Link),linear(NewC))),
    copy((X:-A),NewC),
    true((mshare([[A],[A,X],[A,X,NewC],[A,NewC],[X],[X,NewC],[Link],[NewC]]),var(Link),linear(Link);mshare([[A],[A,X],[A,X,NewC],[A,NewC],[Link],[NewC]]),var(Link),linear(Link))).

:- true pred find_vars(X,Y)
   : ( mshare([[X],[Y]]),
       var(Y), linear(Y) )
   => ( mshare([[X,Y]]),
        linear(Y) ).

:- true pred find_vars(X,Y)
   : ( (X=(_A;_B)),
       mshare([[Y],[_A],[_A,_B],[_B]]),
       var(Y), linear(Y) )
   => ( mshare([[Y,_A],[Y,_A,_B],[Y,_B]]),
        linear(Y) ).

find_vars(X,Y) :-
    true((
        mshare([[X],[Y],[Link]]),
        var(Y),
        var(Link),
        linear(Y),
        linear(Link)
    )),
    find_vars(X,Y,Link),
    true((
        mshare([[X,Y],[Y,Link]]),
        var(Link),
        linear(Y),
        linear(Link)
    )),
    Link=[],
    true((
        mshare([[X,Y]]),
        ground([Link]),
        linear(Y)
    )).

:- true pred find_vars(Var,Vars,Link)
   : ( mshare([[Var],[Vars],[Link]]),
       var(Vars), var(Link), linear(Vars), linear(Link) )
   => ( mshare([[Var,Vars],[Vars,Link]]),
        var(Link), linear(Vars), linear(Link) ).

find_vars(Var,[Var|Link],Link) :-
    true((
        mshare([[Var],[Link]]),
        var(Link),
        linear(Link)
    )),
    var(Var),
    !,
    true((
        mshare([[Var],[Link]]),
        var(Var),
        var(Link),
        linear(Var),
        linear(Link)
    )).
find_vars(Cst,Link,Link) :-
    true((
        mshare([[Cst],[Link]]),
        var(Link),
        linear(Link)
    )),
    atomic(Cst),
    !,
    true((
        mshare([[Link]]),
        var(Link),
        ground([Cst]),
        linear(Link)
    )).
find_vars([T|Ts],Vars,NewLink) :-
    !,
    true((
        mshare([[Vars],[NewLink],[T],[T,Ts],[Ts],[Link]]),
        var(Vars),
        var(NewLink),
        var(Link),
        linear(Vars),
        linear(NewLink),
        linear(Link)
    )),
    find_vars(T,Vars,Link),
    true((
        mshare([[Vars,T],[Vars,T,Ts],[Vars,Link],[NewLink],[Ts]]),
        var(NewLink),
        var(Link),
        linear(Vars),
        linear(NewLink),
        linear(Link)
    )),
    find_vars(Ts,Link,NewLink),
    true((
        mshare([[Vars,NewLink,Link],[Vars,T],[Vars,T,Ts,Link],[Vars,Ts,Link]]),
        var(NewLink),
        linear(Vars),
        linear(NewLink),
        linear(Link)
    )).
find_vars(Term,Vars,Link) :-
    true((
        mshare([[Term],[Vars],[Link],[_1],[Args]]),
        var(Vars),
        var(Link),
        var(_1),
        var(Args),
        linear(Vars),
        linear(Link),
        linear(_1),
        linear(Args)
    )),
    Term=..[_1|Args],
    true((
        mshare([[Term,Args],[Vars],[Link]]),
        var(Vars),
        var(Link),
        ground([_1]),
        linear(Vars),
        linear(Link)
    )),
    find_vars(Args,Vars,Link),
    true((
        mshare([[Term,Vars,Args],[Vars,Link]]),
        var(Link),
        ground([_1]),
        linear(Vars),
        linear(Link)
    )).

:- true pred intersect_vars(V1,V2,Out)
   : ( mshare([[V1],[V1,V2],[V2],[Out]]),
       var(Out), linear(V1), linear(V2), linear(Out) )
   => mshare([[V1],[V1,V2],[V1,V2,Out],[V1,Out],[V2]]).

intersect_vars(V1,V2,Out) :-
    true((
        mshare([[V1],[V1,V2],[V2],[Out],[Sorted1],[Sorted2]]),
        var(Out),
        var(Sorted1),
        var(Sorted2),
        linear(V1),
        linear(V2),
        linear(Out),
        linear(Sorted1),
        linear(Sorted2)
    )),
    sort_vars(V1,Sorted1),
    true((
        mshare([[V1],[V1,V2],[V1,V2,Sorted1],[V1,Sorted1],[V2],[Out],[Sorted2]]),
        var(Out),
        var(Sorted2),
        linear(V2),
        linear(Out),
        linear(Sorted2)
    )),
    sort_vars(V2,Sorted2),
    true((
        mshare([[V1],[V1,V2],[V1,V2,Sorted1],[V1,V2,Sorted1,Sorted2],[V1,V2,Sorted2],[V1,Sorted1],[V2],[V2,Sorted2],[Out]]),
        var(Out),
        linear(Out)
    )),
    intersect_sorted_vars(Sorted1,Sorted2,Out),
    true(mshare([[V1],[V1,V2],[V1,V2,Out,Sorted1],[V1,V2,Out,Sorted1,Sorted2],[V1,V2,Sorted1],[V1,V2,Sorted1,Sorted2],[V1,V2,Sorted2],[V1,Out,Sorted1],[V1,Sorted1],[V2],[V2,Sorted2]])).

:- true pred make_dummy_name(N,Name)
   : ( mshare([[N],[Name]]),
       var(Name), linear(Name) )
   => mshare([[N],[N,Name],[Name]]).

make_dummy_name(N,Name) :-
    true((
        mshare([[N],[Name],[L1],[L2],[L]]),
        var(Name),
        var(L1),
        var(L2),
        var(L),
        linear(Name),
        linear(L1),
        linear(L2),
        linear(L)
    )),
    atom_codes('_dummy_',L1),
    true((
        mshare([[N],[Name],[L1],[L2],[L]]),
        var(Name),
        var(L2),
        var(L),
        linear(Name),
        linear(L2),
        linear(L)
    )),
    number_codes(N,L2),
    true((
        mshare([[N],[N,L2],[Name],[L1],[L2],[L]]),
        var(Name),
        var(L),
        linear(Name),
        linear(L)
    )),
    my_append(L1,L2,L),
    true((
        mshare([[N],[N,L2,L],[Name],[L1,L],[L2,L]]),
        var(Name),
        linear(Name)
    )),
    atom_codes(Name,L),
    true(mshare([[N],[N,Name,L1,L2,L],[N,Name,L2,L],[N,L1,L2,L],[N,L2,L],[Name],[Name,L1,L2,L],[Name,L1,L],[Name,L2,L],[L1,L2,L],[L1,L],[L2,L]])).

:- true pred my_append(_A,L,_B)
   : ( mshare([[_A],[L],[_B]]),
       var(_B), linear(_B) )
   => mshare([[_A,_B],[L,_B]]).

my_append([],L,L).
my_append([H|L1],L2,[H|Res]) :-
    true((
        mshare([[L2],[H],[H,L1],[L1],[Res]]),
        var(Res),
        linear(Res)
    )),
    my_append(L1,L2,Res),
    true(mshare([[L2,Res],[H],[H,L1,Res],[L1,Res]])).

:- true pred copy(Term1,Term2)
   : ( (Term1=(_A:-_B)),
       mshare([[Term2],[_A],[_A,_B],[_B]]),
       var(Term2), linear(Term2) )
   => mshare([[Term2],[Term2,_A],[Term2,_A,_B],[Term2,_B],[_A],[_A,_B],[_B]]).

:- true pred copy(Term1,Term2)
   : ( (Term1=(_A:-_B)),
       mshare([[Term2],[_A,_B],[_B]]),
       var(Term2), linear(Term2) )
   => mshare([[Term2],[Term2,_A],[Term2,_A,_B],[Term2,_B],[_A],[_A,_B],[_B]]).

copy(Term1,Term2) :-
    true((
        mshare([[Term1],[Term2],[Set],[Sym]]),
        var(Term2),
        var(Set),
        var(Sym),
        linear(Term2),
        linear(Set),
        linear(Sym)
    )),
    varset(Term1,Set),
    true((
        mshare([[Term1],[Term1,Set],[Term2],[Sym]]),
        var(Term2),
        var(Sym),
        linear(Term2),
        linear(Sym)
    )),
    make_sym(Set,Sym),
    true((
        mshare([[Term1],[Term1,Set,Sym],[Term2],[Sym]]),
        var(Term2),
        linear(Term2)
    )),
    copy2(Term1,Term2,Sym),
    !,
    true(mshare([[Term1],[Term1,Term2,Set,Sym],[Term1,Term2,Sym],[Term1,Set,Sym],[Term1,Sym],[Term2],[Term2,Sym],[Sym]])).

:- true pred copy2(V1,V2,Sym)
   : mshare([[V1],[V1,V2,Sym],[V1,Sym],[V2],[V2,Sym],[Sym]])
   => mshare([[V1],[V1,V2,Sym],[V1,Sym],[V2],[V2,Sym],[Sym]]).

:- true pred copy2(V1,V2,Sym)
   : mshare([[V1],[V1,Sym],[V2],[Sym]])
   => mshare([[V1],[V1,V2,Sym],[V1,Sym],[V2],[V2,Sym],[Sym]]).

:- true pred copy2(V1,V2,Sym)
   : ( mshare([[V1],[V1,Sym],[V2],[Sym]]),
       var(V2), linear(V2) )
   => mshare([[V1],[V1,V2,Sym],[V1,Sym],[V2],[V2,Sym],[Sym]]).

copy2(V1,V2,Sym) :-
    true((mshare([[V1],[V1,V2,Sym],[V1,Sym],[V2],[V2,Sym],[Sym]]);mshare([[V1],[V1,Sym],[V2],[Sym]]);mshare([[V1],[V1,Sym],[V2],[Sym]]),var(V2),linear(V2))),
    var(V1),
    !,
    true((mshare([[V1],[V1,V2,Sym],[V1,Sym],[V2],[V2,Sym],[Sym]]),var(V1),linear(V1);mshare([[V1],[V1,Sym],[V2],[Sym]]),var(V1),linear(V1);mshare([[V1],[V1,Sym],[V2],[Sym]]),var(V1),var(V2),linear(V1),linear(V2))),
    retrieve_sym(V1,Sym,V2),
    true(mshare([[V1],[V1,V2,Sym],[V1,Sym],[V2,Sym],[Sym]])).
copy2(X1,X2,Sym) :-
    true((mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym],[Name],[Arity]]),var(Name),var(Arity),linear(Name),linear(Arity);mshare([[X1],[X1,Sym],[X2],[Sym],[Name],[Arity]]),var(X2),var(Name),var(Arity),linear(X2),linear(Name),linear(Arity);mshare([[X1],[X1,Sym],[X2],[Sym],[Name],[Arity]]),var(Name),var(Arity),linear(Name),linear(Arity))),
    nonvar(X1),
    !,
    true((mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym],[Name],[Arity]]),var(Name),var(Arity),linear(Name),linear(Arity);mshare([[X1],[X1,Sym],[X2],[Sym],[Name],[Arity]]),var(X2),var(Name),var(Arity),linear(X2),linear(Name),linear(Arity);mshare([[X1],[X1,Sym],[X2],[Sym],[Name],[Arity]]),var(Name),var(Arity),linear(Name),linear(Arity))),
    functor(X1,Name,Arity),
    true((mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym]]),ground([Name,Arity]);mshare([[X1],[X1,Sym],[X2],[Sym]]),ground([Name,Arity]);mshare([[X1],[X1,Sym],[X2],[Sym]]),var(X2),ground([Name,Arity]),linear(X2))),
    functor(X2,Name,Arity),
    true((mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym]]),ground([Name,Arity]);mshare([[X1],[X1,Sym],[X2],[Sym]]),ground([Name,Arity]))),
    copy2(X1,X2,Sym,1,Arity),
    true((
        mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym]]),
        ground([Name,Arity])
    )).

:- true pred copy2(_X1,_X2,_Sym,N,Arity)
   : ( (N=1),
       mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),
       ground([Arity]) )
   => ( mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),
        ground([Arity]) ).

:- true pred copy2(_X1,_X2,_Sym,N,Arity)
   : ( (N=1),
       mshare([[_X1],[_X1,_Sym],[_X2],[_Sym]]),
       ground([Arity]) )
   => ( mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),
        ground([Arity]) ).

:- true pred copy2(_X1,_X2,_Sym,N,Arity)
   : ( mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),
       ground([N,Arity]) )
   => ( mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),
        ground([N,Arity]) ).

copy2(_X1,_X2,_Sym,N,Arity) :-
    true((mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),ground([N,Arity]);mshare([[_X1],[_X1,_Sym],[_X2],[_Sym]]),ground([N,Arity]))),
    N>Arity,
    !,
    true((mshare([[_X1],[_X1,_X2,_Sym],[_X1,_Sym],[_X2],[_X2,_Sym],[_Sym]]),ground([N,Arity]);mshare([[_X1],[_X1,_Sym],[_X2],[_Sym]]),ground([N,Arity]))).
copy2(X1,X2,Sym,N,Arity) :-
    true((mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym],[Arg1],[Arg2],[N1]]),var(Arg1),var(Arg2),var(N1),ground([N,Arity]),linear(Arg1),linear(Arg2),linear(N1);mshare([[X1],[X1,Sym],[X2],[Sym],[Arg1],[Arg2],[N1]]),var(Arg1),var(Arg2),var(N1),ground([N,Arity]),linear(Arg1),linear(Arg2),linear(N1))),
    N=<Arity,
    !,
    true((mshare([[X1],[X1,X2,Sym],[X1,Sym],[X2],[X2,Sym],[Sym],[Arg1],[Arg2],[N1]]),var(Arg1),var(Arg2),var(N1),ground([N,Arity]),linear(Arg1),linear(Arg2),linear(N1);mshare([[X1],[X1,Sym],[X2],[Sym],[Arg1],[Arg2],[N1]]),var(Arg1),var(Arg2),var(N1),ground([N,Arity]),linear(Arg1),linear(Arg2),linear(N1))),
    arg(N,X1,Arg1),
    true((mshare([[X1],[X1,X2,Sym],[X1,X2,Sym,Arg1],[X1,Sym],[X1,Sym,Arg1],[X1,Arg1],[X2],[X2,Sym],[Sym],[Arg2],[N1]]),var(Arg2),var(N1),ground([N,Arity]),linear(Arg2),linear(N1);mshare([[X1],[X1,Sym],[X1,Sym,Arg1],[X1,Arg1],[X2],[Sym],[Arg2],[N1]]),var(Arg2),var(N1),ground([N,Arity]),linear(Arg2),linear(N1))),
    arg(N,X2,Arg2),
    true((mshare([[X1],[X1,X2,Sym],[X1,X2,Sym,Arg1],[X1,X2,Sym,Arg1,Arg2],[X1,X2,Sym,Arg2],[X1,Sym],[X1,Sym,Arg1],[X1,Arg1],[X2],[X2,Sym],[X2,Sym,Arg2],[X2,Arg2],[Sym],[N1]]),var(N1),ground([N,Arity]),linear(N1);mshare([[X1],[X1,Sym],[X1,Sym,Arg1],[X1,Arg1],[X2],[X2,Arg2],[Sym],[N1]]),var(N1),ground([N,Arity]),linear(N1))),
    copy2(Arg1,Arg2,Sym),
    true((mshare([[X1],[X1,X2,Sym],[X1,X2,Sym,Arg1],[X1,X2,Sym,Arg1,Arg2],[X1,X2,Sym,Arg2],[X1,Sym],[X1,Sym,Arg1],[X1,Arg1],[X2],[X2,Sym],[X2,Sym,Arg2],[X2,Arg2],[Sym],[N1]]),var(N1),ground([N,Arity]),linear(N1);mshare([[X1],[X1,X2,Sym,Arg1,Arg2],[X1,X2,Sym,Arg2],[X1,Sym],[X1,Sym,Arg1],[X1,Arg1],[X2],[X2,Sym,Arg2],[X2,Arg2],[Sym],[N1]]),var(N1),ground([N,Arity]),linear(N1))),
    N1 is N+1,
    true((mshare([[X1],[X1,X2,Sym],[X1,X2,Sym,Arg1],[X1,X2,Sym,Arg1,Arg2],[X1,X2,Sym,Arg2],[X1,Sym],[X1,Sym,Arg1],[X1,Arg1],[X2],[X2,Sym],[X2,Sym,Arg2],[X2,Arg2],[Sym]]),ground([N,Arity,N1]);mshare([[X1],[X1,X2,Sym,Arg1,Arg2],[X1,X2,Sym,Arg2],[X1,Sym],[X1,Sym,Arg1],[X1,Arg1],[X2],[X2,Sym,Arg2],[X2,Arg2],[Sym]]),ground([N,Arity,N1]))),
    copy2(X1,X2,Sym,N1,Arity),
    true((
        mshare([[X1],[X1,X2,Sym],[X1,X2,Sym,Arg1],[X1,X2,Sym,Arg1,Arg2],[X1,X2,Sym,Arg2],[X1,Sym],[X1,Sym,Arg1],[X1,Arg1],[X2],[X2,Sym],[X2,Sym,Arg2],[X2,Arg2],[Sym]]),
        ground([N,Arity,N1])
    )).

:- true pred retrieve_sym(V,_A,X)
   : ( mshare([[V],[V,_A],[V,_A,X],[_A],[_A,X],[X]]),
       var(V), linear(V) )
   => mshare([[V],[V,_A],[V,_A,X],[_A],[_A,X]]).

:- true pred retrieve_sym(V,_A,X)
   : ( mshare([[V],[V,_A],[V,_A,X],[V,X],[_A],[_A,X],[X]]),
       linear(V) )
   => mshare([[V],[V,_A],[V,_A,X],[_A],[_A,X]]).

:- true pred retrieve_sym(V,_A,X)
   : ( mshare([[V],[V,_A],[_A],[X]]),
       var(V), linear(V) )
   => mshare([[V],[V,_A],[V,_A,X],[_A],[_A,X]]).

:- true pred retrieve_sym(V,_A,X)
   : ( mshare([[V],[V,_A],[_A],[X]]),
       linear(V) )
   => mshare([[V],[V,_A],[V,_A,X],[_A],[_A,X]]).

:- true pred retrieve_sym(V,_A,X)
   : ( mshare([[V],[V,_A],[_A],[X]]),
       var(V), var(X), linear(V), linear(X) )
   => mshare([[V],[V,_A],[V,_A,X],[_A],[_A,X]]).

:- true pred retrieve_sym(V,_A,X)
   : ( mshare([[V],[V,_A],[_A],[X]]),
       var(X), linear(V), linear(X) )
   => mshare([[V],[V,_A],[V,_A,X],[_A],[_A,X]]).

retrieve_sym(V,[p(W,X)|_Sym],X) :-
    true((mshare([[V],[V,X],[V,X,_Sym],[V,X,_Sym,W],[V,X,W],[V,_Sym],[V,_Sym,W],[V,W],[X],[X,_Sym],[X,_Sym,W],[X,W],[_Sym],[_Sym,W],[W]]);mshare([[V],[V,X],[V,X,_Sym],[V,X,_Sym,W],[V,X,W],[V,_Sym],[V,_Sym,W],[V,W],[X],[X,_Sym],[X,_Sym,W],[X,W],[_Sym],[_Sym,W],[W]]),linear(V))),
    V==W,
    !,
    true(mshare([[V],[V,X],[V,X,_Sym],[V,X,_Sym,W],[V,X,W],[V,_Sym],[V,_Sym,W],[V,W],[X],[X,_Sym],[X,_Sym,W],[X,W],[_Sym],[_Sym,W],[W]])).
retrieve_sym(V,[_1|Sym],X) :-
    true((mshare([[V],[V,X],[V,X,_1],[V,X,_1,Sym],[V,X,Sym],[V,_1],[V,_1,Sym],[V,Sym],[X],[X,_1],[X,_1,Sym],[X,Sym],[_1],[_1,Sym],[Sym]]),linear(V);mshare([[V],[V,X,_1],[V,X,_1,Sym],[V,X,Sym],[V,_1],[V,_1,Sym],[V,Sym],[X],[X,_1],[X,_1,Sym],[X,Sym],[_1],[_1,Sym],[Sym]]),linear(V);mshare([[V],[V,_1],[V,_1,Sym],[V,Sym],[X],[_1],[_1,Sym],[Sym]]),linear(V);mshare([[V],[V,_1],[V,_1,Sym],[V,Sym],[X],[_1],[_1,Sym],[Sym]]),var(X),linear(V),linear(X))),
    retrieve_sym(V,Sym,X),
    true(mshare([[V],[V,X,_1,Sym],[V,X,Sym],[V,_1],[V,_1,Sym],[V,Sym],[X,_1,Sym],[X,Sym],[_1],[_1,Sym],[Sym]])).

:- true pred make_sym(_A,_B)
   : ( mshare([[_A],[_B]]),
       var(_B), linear(_B) )
   => mshare([[_A,_B],[_B]]).

make_sym([],[]).
make_sym([V|L],[p(V,_1)|S]) :-
    true((
        mshare([[V],[V,L],[L],[S],[_1]]),
        var(S),
        var(_1),
        linear(S),
        linear(_1)
    )),
    make_sym(L,S),
    true((
        mshare([[V],[V,L,S],[L,S],[S],[_1]]),
        var(_1),
        linear(_1)
    )).

:- true pred varset(Term,VarSet)
   : ( mshare([[Term],[VarSet]]),
       var(VarSet), linear(VarSet) )
   => mshare([[Term],[Term,VarSet]]).

varset(Term,VarSet) :-
    true((
        mshare([[Term],[VarSet],[VB]]),
        var(VarSet),
        var(VB),
        linear(VarSet),
        linear(VB)
    )),
    varbag(Term,VB),
    true((
        mshare([[Term],[Term,VB],[VarSet]]),
        var(VarSet),
        linear(VarSet)
    )),
    sort(VB,VarSet),
    true(mshare([[Term],[Term,VarSet,VB]])).

:- true pred varbag(Term,VarBag)
   : ( mshare([[Term],[VarBag]]),
       var(VarBag), linear(VarBag) )
   => mshare([[Term],[Term,VarBag]]).

varbag(Term,VarBag) :-
    true((
        mshare([[Term],[VarBag]]),
        var(VarBag),
        linear(VarBag)
    )),
    varbag(Term,VarBag,[]),
    true(mshare([[Term],[Term,VarBag]])).

:- true pred varbag(Var,_1,_2)
   : ( (_2=[]),
       mshare([[Var],[_1]]),
       var(_1), linear(_1) )
   => mshare([[Var],[Var,_1]]).

:- true pred varbag(Var,_1,_2)
   : ( mshare([[Var],[_1],[_2]]),
       var(_1), var(_2), linear(_1), linear(_2) )
   => ( mshare([[Var],[Var,_1],[_1,_2]]),
        var(_2), linear(_1), linear(_2) ).

varbag(Var,_1,_2) :-
    true((mshare([[Var],[_1]]),var(_1),ground([_2]),linear(_1);mshare([[Var],[_1],[_2]]),var(_1),var(_2),linear(_1),linear(_2))),
    var(Var),
    !,
    true((mshare([[Var],[_1]]),var(Var),var(_1),ground([_2]),linear(Var),linear(_1);mshare([[Var],[_1],[_2]]),var(Var),var(_1),var(_2),linear(Var),linear(_1),linear(_2))),
    'C'(_1,Var,_2),
    true((mshare([[Var,_1]]),var(Var),ground([_2]),linear(Var);mshare([[Var,_1],[_1,_2]]),var(Var),var(_2),linear(Var),linear(_1),linear(_2))).
varbag(Str,_1,_2) :-
    true((mshare([[Str],[_1],[_2],[_3],[Arity]]),var(_1),var(_2),var(_3),var(Arity),linear(_1),linear(_2),linear(_3),linear(Arity);mshare([[Str],[_1],[_3],[Arity]]),var(_1),var(_3),var(Arity),ground([_2]),linear(_1),linear(_3),linear(Arity))),
    nonvar(Str),
    !,
    true((mshare([[Str],[_1],[_2],[_3],[Arity]]),var(_1),var(_2),var(_3),var(Arity),linear(_1),linear(_2),linear(_3),linear(Arity);mshare([[Str],[_1],[_3],[Arity]]),var(_1),var(_3),var(Arity),ground([_2]),linear(_1),linear(_3),linear(Arity))),
    functor(Str,_3,Arity),
    true((mshare([[Str],[_1]]),var(_1),ground([_2,_3,Arity]),linear(_1);mshare([[Str],[_1],[_2]]),var(_1),var(_2),ground([_3,Arity]),linear(_1),linear(_2))),
    varbag(Str,1,Arity,_1,_2),
    true((mshare([[Str],[Str,_1]]),ground([_2,_3,Arity]);mshare([[Str],[Str,_1],[_1,_2]]),var(_2),ground([_3,Arity]),linear(_1),linear(_2))).

:- true pred varbag(_Str,N,Arity,_1,_2)
   : ( mshare([[_Str],[_1],[_2]]),
       var(_1), var(_2), ground([N,Arity]), linear(_1), linear(_2) )
   => ( mshare([[_Str],[_Str,_1],[_1,_2]]),
        var(_2), ground([N,Arity]), linear(_1), linear(_2) ).

:- true pred varbag(_Str,N,Arity,_1,_2)
   : ( (N=1),
       mshare([[_Str],[_1],[_2]]),
       var(_1), var(_2), ground([Arity]), linear(_1), linear(_2) )
   => ( mshare([[_Str],[_Str,_1],[_1,_2]]),
        var(_2), ground([Arity]), linear(_1), linear(_2) ).

:- true pred varbag(_Str,N,Arity,_1,_2)
   : ( (N=1),
       mshare([[_Str],[_1]]),
       var(_1), ground([Arity,_2]), linear(_1) )
   => ( mshare([[_Str],[_Str,_1]]),
        ground([Arity,_2]) ).

:- true pred varbag(_Str,N,Arity,_1,_2)
   : ( mshare([[_Str],[_1]]),
       var(_1), ground([N,Arity,_2]), linear(_1) )
   => ( mshare([[_Str],[_Str,_1]]),
        ground([N,Arity,_2]) ).

varbag(_Str,N,Arity,_1,_2) :-
    true((mshare([[_Str],[_1]]),var(_1),ground([N,Arity,_2]),linear(_1);mshare([[_Str],[_1],[_2]]),var(_1),var(_2),ground([N,Arity]),linear(_1),linear(_2))),
    N>Arity,
    !,
    true((mshare([[_Str],[_1]]),var(_1),ground([N,Arity,_2]),linear(_1);mshare([[_Str],[_1],[_2]]),var(_1),var(_2),ground([N,Arity]),linear(_1),linear(_2))),
    _2=_1,
    true((mshare([[_Str]]),ground([N,Arity,_1,_2]);mshare([[_Str],[_1,_2]]),var(_1),var(_2),ground([N,Arity]),linear(_1),linear(_2))).
varbag(Str,N,Arity,_1,_2) :-
    true((mshare([[Str],[_1],[_2],[Arg],[_3],[N1]]),var(_1),var(_2),var(Arg),var(_3),var(N1),ground([N,Arity]),linear(_1),linear(_2),linear(Arg),linear(_3),linear(N1);mshare([[Str],[_1],[Arg],[_3],[N1]]),var(_1),var(Arg),var(_3),var(N1),ground([N,Arity,_2]),linear(_1),linear(Arg),linear(_3),linear(N1))),
    N=<Arity,
    !,
    true((mshare([[Str],[_1],[_2],[Arg],[_3],[N1]]),var(_1),var(_2),var(Arg),var(_3),var(N1),ground([N,Arity]),linear(_1),linear(_2),linear(Arg),linear(_3),linear(N1);mshare([[Str],[_1],[Arg],[_3],[N1]]),var(_1),var(Arg),var(_3),var(N1),ground([N,Arity,_2]),linear(_1),linear(Arg),linear(_3),linear(N1))),
    arg(N,Str,Arg),
    true((mshare([[Str],[Str,Arg],[_1],[_2],[_3],[N1]]),var(_1),var(_2),var(_3),var(N1),ground([N,Arity]),linear(_1),linear(_2),linear(_3),linear(N1);mshare([[Str],[Str,Arg],[_1],[_3],[N1]]),var(_1),var(_3),var(N1),ground([N,Arity,_2]),linear(_1),linear(_3),linear(N1))),
    varbag(Arg,_1,_3),
    true((mshare([[Str],[Str,_1,Arg],[Str,Arg],[_1,_3],[_2],[N1]]),var(_2),var(_3),var(N1),ground([N,Arity]),linear(_1),linear(_2),linear(_3),linear(N1);mshare([[Str],[Str,_1,Arg],[Str,Arg],[_1,_3],[N1]]),var(_3),var(N1),ground([N,Arity,_2]),linear(_1),linear(_3),linear(N1))),
    N1 is N+1,
    true((mshare([[Str],[Str,_1,Arg],[Str,Arg],[_1,_3]]),var(_3),ground([N,Arity,_2,N1]),linear(_1),linear(_3);mshare([[Str],[Str,_1,Arg],[Str,Arg],[_1,_3],[_2]]),var(_2),var(_3),ground([N,Arity,N1]),linear(_1),linear(_2),linear(_3))),
    varbag(Str,N1,Arity,_3,_2),
    true((mshare([[Str],[Str,_1,Arg],[Str,_1,Arg,_3],[Str,_1,_3],[Str,Arg]]),ground([N,Arity,_2,N1]),linear(_1);mshare([[Str],[Str,_1,Arg],[Str,_1,Arg,_3],[Str,_1,_3],[Str,Arg],[_1,_2,_3]]),var(_2),ground([N,Arity,N1]),linear(_1),linear(_2),linear(_3))).

:- true pred inst_vars(Term)
   : ( (Term=(_A,_B)),
       mshare([[_A],[_A,_B],[_B]]) )
   => mshare([[_A],[_A,_B],[_B]]).

inst_vars(Term) :-
    true((
        mshare([[Term],[Vars]]),
        var(Vars),
        linear(Vars)
    )),
    varset(Term,Vars),
    true(mshare([[Term],[Term,Vars]])),
    inst_vars_list(Vars,65),
    true(mshare([[Term],[Term,Vars]])).

:- true pred inst_vars_list(_A,_1)
   : ( (_1=65),
       mshare([[_A]]) )
   => mshare([[_A]]).

:- true pred inst_vars_list(_A,_1)
   : ( mshare([[_A]]),
       ground([_1]) )
   => ( mshare([[_A]]),
        ground([_1]) ).

inst_vars_list([],_1).
inst_vars_list([T|L],N) :-
    true((
        mshare([[T],[T,L],[L],[N1]]),
        var(N1),
        ground([N]),
        linear(N1)
    )),
    atom_codes(T,[N]),
    true((
        mshare([[T],[T,L],[L],[N1]]),
        var(N1),
        ground([N]),
        linear(N1)
    )),
    N1 is N+1,
    true((
        mshare([[T],[T,L],[L]]),
        ground([N,N1])
    )),
    inst_vars_list(L,N1),
    true((
        mshare([[T],[T,L],[L]]),
        ground([N,N1])
    )).

:- true pred sort_vars(V,Out)
   : ( mshare([[V],[Out]]),
       var(Out), linear(V), linear(Out) )
   => mshare([[V],[V,Out]]).

sort_vars(V,Out) :-
    true((
        mshare([[V],[Out]]),
        var(Out),
        linear(V),
        linear(Out)
    )),
    sort_vars(V,Out,[]),
    true(mshare([[V],[V,Out]])).

:- true pred sort_vars(_A,Link,_B)
   : ( mshare([[_A],[_A,_B],[Link],[_B]]),
       var(Link), linear(Link) )
   => mshare([[_A],[_A,Link],[_A,Link,_B],[Link,_B]]).

:- true pred sort_vars(_A,Link,_B)
   : ( (_B=[]),
       mshare([[_A],[Link]]),
       var(Link), linear(_A), linear(Link) )
   => mshare([[_A],[_A,Link]]).

:- true pred sort_vars(_A,Link,_B)
   : ( mshare([[_A],[_A,Link],[Link]]),
       ground([_B]) )
   => ( mshare([[_A],[_A,Link]]),
        ground([_B]) ).

:- true pred sort_vars(_A,Link,_B)
   : ( (_B=[_C|_D]),
       mshare([[_A],[_A,Link],[_A,Link,_C],[_A,_C],[Link],[Link,_C],[_C],[_D]]),
       var(_D), linear(_D) )
   => mshare([[_A],[_A,Link],[_A,Link,_C],[_A,Link,_C,_D],[_A,Link,_D],[Link,_C],[Link,_C,_D],[Link,_D]]).

:- true pred sort_vars(_A,Link,_B)
   : mshare([[_A],[_A,Link],[_A,Link,_B],[_A,_B],[Link],[Link,_B],[_B]])
   => mshare([[_A],[_A,Link],[_A,Link,_B],[Link,_B]]).

:- true pred sort_vars(_A,Link,_B)
   : ( (_B=[_C|_D]),
       mshare([[_A],[_A,_C],[Link],[_C],[_D]]),
       var(Link), var(_D), linear(Link), linear(_D) )
   => mshare([[_A],[_A,Link],[_A,Link,_C],[_A,Link,_C,_D],[_A,Link,_D],[Link,_C],[Link,_C,_D],[Link,_D]]).

sort_vars([],Link,Link).
sort_vars([V|Vs],Result,Link) :-
    true((mshare([[Result],[Result,Link],[Result,Link,V],[Result,Link,V,Vs],[Result,Link,Vs],[Result,V],[Result,V,Vs],[Result,Vs],[Link],[Link,V],[Link,V,Vs],[Link,Vs],[V],[V,Vs],[Vs],[Smaller],[Bigger],[SLink]]),var(Smaller),var(Bigger),var(SLink),linear(Smaller),linear(Bigger),linear(SLink);mshare([[Result],[Result,V],[Result,V,Vs],[Result,Vs],[V],[V,Vs],[Vs],[Smaller],[Bigger],[SLink]]),var(Smaller),var(Bigger),var(SLink),ground([Link]),linear(Smaller),linear(Bigger),linear(SLink);mshare([[Result],[Link],[Link,V],[Link,V,Vs],[Link,Vs],[V],[V,Vs],[Vs],[Smaller],[Bigger],[SLink]]),var(Result),var(Smaller),var(Bigger),var(SLink),linear(Result),linear(Smaller),linear(Bigger),linear(SLink);mshare([[Result],[V],[V,Vs],[Vs],[Smaller],[Bigger],[SLink]]),var(Result),var(Smaller),var(Bigger),var(SLink),ground([Link]),linear(Result),linear(V),linear(Vs),linear(Smaller),linear(Bigger),linear(SLink))),
    split_vars(Vs,V,Smaller,Bigger),
    true((mshare([[Result],[Result,Link],[Result,Link,V],[Result,Link,V,Vs],[Result,Link,V,Vs,Smaller],[Result,Link,V,Vs,Smaller,Bigger],[Result,Link,V,Vs,Bigger],[Result,Link,Vs],[Result,Link,Vs,Smaller],[Result,Link,Vs,Smaller,Bigger],[Result,Link,Vs,Bigger],[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Bigger],[Result,Vs],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Bigger],[Link],[Link,V],[Link,V,Vs],[Link,V,Vs,Smaller],[Link,V,Vs,Smaller,Bigger],[Link,V,Vs,Bigger],[Link,Vs],[Link,Vs,Smaller],[Link,Vs,Smaller,Bigger],[Link,Vs,Bigger],[V],[V,Vs],[V,Vs,Smaller],[V,Vs,Smaller,Bigger],[V,Vs,Bigger],[Vs],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger],[SLink]]),var(SLink),linear(SLink);mshare([[Result],[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Bigger],[Result,Vs],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Bigger],[V],[V,Vs],[V,Vs,Smaller],[V,Vs,Smaller,Bigger],[V,Vs,Bigger],[Vs],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger],[SLink]]),var(SLink),ground([Link]),linear(SLink);mshare([[Result],[Link],[Link,V],[Link,V,Vs],[Link,V,Vs,Smaller],[Link,V,Vs,Smaller,Bigger],[Link,V,Vs,Bigger],[Link,Vs],[Link,Vs,Smaller],[Link,Vs,Smaller,Bigger],[Link,Vs,Bigger],[V],[V,Vs],[V,Vs,Smaller],[V,Vs,Smaller,Bigger],[V,Vs,Bigger],[Vs],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger],[SLink]]),var(Result),var(SLink),linear(Result),linear(SLink);mshare([[Result],[V],[V,Vs],[V,Vs,Smaller],[V,Vs,Smaller,Bigger],[V,Vs,Bigger],[Vs],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger],[SLink]]),var(Result),var(SLink),ground([Link]),linear(Result),linear(SLink))),
    sort_vars(Smaller,Result,[V|SLink]),
    true((mshare([[Result,Link,V],[Result,Link,V,Vs],[Result,Link,V,Vs,Smaller],[Result,Link,V,Vs,Smaller,Bigger],[Result,Link,V,Vs,Smaller,Bigger,SLink],[Result,Link,V,Vs,Smaller,SLink],[Result,Link,V,Vs,Bigger],[Result,Link,V,Vs,Bigger,SLink],[Result,Link,V,Vs,SLink],[Result,Link,V,SLink],[Result,Link,Vs,Smaller],[Result,Link,Vs,Smaller,Bigger],[Result,Link,Vs,Smaller,Bigger,SLink],[Result,Link,Vs,Smaller,SLink],[Result,Link,Vs,Bigger,SLink],[Result,Link,Vs,SLink],[Result,Link,SLink],[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Smaller,Bigger,SLink],[Result,V,Vs,Smaller,SLink],[Result,V,Vs,Bigger],[Result,V,Vs,Bigger,SLink],[Result,V,Vs,SLink],[Result,V,SLink],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Smaller,Bigger,SLink],[Result,Vs,Smaller,SLink],[Result,Vs,Bigger,SLink],[Result,Vs,SLink],[Result,SLink],[Link],[Link,Vs],[Link,Vs,Smaller],[Link,Vs,Smaller,Bigger],[Link,Vs,Bigger],[Vs],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger]]);mshare([[Result,Link,V],[Result,Link,V,Vs],[Result,Link,V,Vs,Smaller],[Result,Link,V,Vs,Smaller,Bigger],[Result,Link,V,Vs,Smaller,Bigger,SLink],[Result,Link,V,Vs,Smaller,SLink],[Result,Link,V,Vs,Bigger],[Result,Link,V,Vs,Bigger,SLink],[Result,Link,V,Vs,SLink],[Result,Link,V,SLink],[Result,Link,Vs,Smaller],[Result,Link,Vs,Smaller,Bigger],[Result,Link,Vs,Smaller,Bigger,SLink],[Result,Link,Vs,Smaller,SLink],[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Smaller,Bigger,SLink],[Result,V,Vs,Smaller,SLink],[Result,V,Vs,Bigger],[Result,V,Vs,Bigger,SLink],[Result,V,Vs,SLink],[Result,V,SLink],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Smaller,Bigger,SLink],[Result,Vs,Smaller,SLink],[Result,SLink],[Link],[Link,Vs],[Link,Vs,Smaller],[Link,Vs,Smaller,Bigger],[Link,Vs,Bigger],[Vs],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger]]);mshare([[Result,Link,V],[Result,Link,V,Vs],[Result,Link,V,Vs,Bigger],[Result,V],[Result,V,Vs],[Result,V,Vs,Bigger],[Result,SLink],[Link],[Link,Vs],[Link,Vs,Bigger],[Vs],[Vs,Bigger]]),var(SLink),ground([Smaller]),linear(SLink);mshare([[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Smaller,Bigger,SLink],[Result,V,Vs,Smaller,SLink],[Result,V,Vs,Bigger],[Result,V,Vs,Bigger,SLink],[Result,V,Vs,SLink],[Result,V,SLink],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Smaller,Bigger,SLink],[Result,Vs,Smaller,SLink],[Result,Vs,Bigger,SLink],[Result,Vs,SLink],[Result,SLink],[Vs],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger]]),ground([Link]);mshare([[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Smaller,Bigger,SLink],[Result,V,Vs,Smaller,SLink],[Result,V,Vs,Bigger],[Result,V,Vs,Bigger,SLink],[Result,V,Vs,SLink],[Result,V,SLink],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Smaller,Bigger,SLink],[Result,Vs,Smaller,SLink],[Result,SLink],[Vs],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger]]),ground([Link]))),
    sort_vars(Bigger,SLink,Link),
    true((mshare([[Result,Link,V,Vs,Smaller,Bigger,SLink],[Result,Link,V,Vs,Smaller,SLink],[Result,Link,V,Vs,Bigger,SLink],[Result,Link,V,Vs,SLink],[Result,Link,V,SLink],[Result,Link,Vs,Smaller,Bigger,SLink],[Result,Link,Vs,Smaller,SLink],[Result,Link,Vs,Bigger,SLink],[Result,Link,Vs,SLink],[Result,Link,SLink],[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Smaller,Bigger,SLink],[Result,V,Vs,Bigger],[Result,V,Vs,Bigger,SLink],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Smaller,Bigger,SLink],[Result,Vs,Bigger,SLink],[Vs],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger]]);mshare([[Result,Link,V,Vs,Bigger,SLink],[Result,Link,V,Vs,SLink],[Result,Link,V,SLink],[Result,Link,Vs,Bigger,SLink],[Result,Link,Vs,SLink],[Result,Link,SLink],[Result,V],[Result,V,Vs],[Result,V,Vs,Bigger],[Result,V,Vs,Bigger,SLink],[Result,Vs,Bigger,SLink],[Vs],[Vs,Bigger]]),ground([Smaller]);mshare([[Result,V],[Result,V,Vs],[Result,V,Vs,Smaller],[Result,V,Vs,Smaller,Bigger],[Result,V,Vs,Smaller,Bigger,SLink],[Result,V,Vs,Bigger],[Result,V,Vs,Bigger,SLink],[Result,Vs,Smaller],[Result,Vs,Smaller,Bigger],[Result,Vs,Smaller,Bigger,SLink],[Result,Vs,Bigger,SLink],[Vs],[Vs,Smaller],[Vs,Smaller,Bigger],[Vs,Bigger]]),ground([Link]))).

:- true pred intersect_sorted_vars(_A,_1,Rs)
   : ( (_1=[_B|_C]),
       mshare([[_A],[_A,_B],[_A,_B,_C],[_A,_C],[Rs],[_B],[_B,_C],[_C]]),
       var(Rs), linear(Rs) )
   => mshare([[_A],[_A,Rs],[_A,Rs,_B],[_A,Rs,_B,_C],[_A,Rs,_C],[_A,_B],[_A,_B,_C],[_A,_C],[_B],[_B,_C],[_C]]).

:- true pred intersect_sorted_vars(_A,_1,Rs)
   : ( (_A=[_B|_C]),
       mshare([[_1],[_1,_B],[_1,_B,_C],[_1,_C],[Rs],[_B],[_B,_C],[_C]]),
       var(Rs), linear(Rs) )
   => mshare([[_1],[_1,Rs,_B],[_1,Rs,_B,_C],[_1,Rs,_C],[_1,_B],[_1,_B,_C],[_1,_C],[Rs,_B],[Rs,_B,_C],[Rs,_C],[_B],[_B,_C],[_C]]).

:- true pred intersect_sorted_vars(_A,_1,Rs)
   : ( mshare([[_A],[_A,_1],[_1],[Rs]]),
       var(Rs), linear(Rs) )
   => mshare([[_A],[_A,_1],[_A,_1,Rs],[_A,Rs],[_1]]).

intersect_sorted_vars([],_1,[]) :-
    !,
    true(mshare([[_1]])).
intersect_sorted_vars(_1,[],[]).
intersect_sorted_vars([X|Xs],[Y|Ys],[X|Rs]) :-
    true((
        mshare([[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys],[Rs]]),
        var(Rs),
        linear(Rs)
    )),
    X==Y,
    !,
    true((
        mshare([[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys],[Rs]]),
        var(Rs),
        linear(Rs)
    )),
    intersect_sorted_vars(Xs,Ys,Rs),
    true(mshare([[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Y,Ys,Rs],[X,Xs,Y,Rs],[X,Xs,Ys],[X,Xs,Ys,Rs],[X,Xs,Rs],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Y,Ys,Rs],[Xs,Y,Rs],[Xs,Ys],[Xs,Ys,Rs],[Xs,Rs],[Y],[Y,Ys],[Ys]])).
intersect_sorted_vars([X|Xs],[Y|Ys],Rs) :-
    true((
        mshare([[Rs],[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys]]),
        var(Rs),
        linear(Rs)
    )),
    X@<Y,
    !,
    true((
        mshare([[Rs],[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys]]),
        var(Rs),
        linear(Rs)
    )),
    intersect_sorted_vars(Xs,[Y|Ys],Rs),
    true(mshare([[Rs,X,Xs],[Rs,X,Xs,Y],[Rs,X,Xs,Y,Ys],[Rs,X,Xs,Ys],[Rs,Xs],[Rs,Xs,Y],[Rs,Xs,Y,Ys],[Rs,Xs,Ys],[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys]])).
intersect_sorted_vars([X|Xs],[Y|Ys],Rs) :-
    true((
        mshare([[Rs],[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys]]),
        var(Rs),
        linear(Rs)
    )),
    X@>Y,
    !,
    true((
        mshare([[Rs],[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys]]),
        var(Rs),
        linear(Rs)
    )),
    intersect_sorted_vars([X|Xs],Ys,Rs),
    true(mshare([[Rs,X],[Rs,X,Xs],[Rs,X,Xs,Y],[Rs,X,Xs,Y,Ys],[Rs,X,Xs,Ys],[Rs,X,Y],[Rs,X,Y,Ys],[Rs,X,Ys],[Rs,Xs],[Rs,Xs,Y],[Rs,Xs,Y,Ys],[Rs,Xs,Ys],[X],[X,Xs],[X,Xs,Y],[X,Xs,Y,Ys],[X,Xs,Ys],[X,Y],[X,Y,Ys],[X,Ys],[Xs],[Xs,Y],[Xs,Y,Ys],[Xs,Ys],[Y],[Y,Ys],[Ys]])).

:- true pred split_vars(_A,_1,Ss,Bs)
   : ( mshare([[_A],[_A,_1],[_1],[Ss],[Bs]]),
       var(Ss), var(Bs), linear(Ss), linear(Bs) )
   => mshare([[_A],[_A,_1],[_A,_1,Ss],[_A,_1,Ss,Bs],[_A,_1,Bs],[_A,Ss],[_A,Ss,Bs],[_A,Bs],[_1]]).

:- true pred split_vars(_A,_1,Ss,Bs)
   : ( mshare([[_A],[_A,_1],[_1],[Ss],[Bs]]),
       var(Ss), var(Bs), linear(_A), linear(_1), linear(Ss), linear(Bs) )
   => mshare([[_A],[_A,_1],[_A,_1,Ss],[_A,_1,Ss,Bs],[_A,_1,Bs],[_A,Ss],[_A,Ss,Bs],[_A,Bs],[_1]]).

:- true pred split_vars(_A,_1,Ss,Bs)
   : ( mshare([[_A],[_A,_1],[_1],[Ss],[Bs]]),
       var(Ss), var(Bs), linear(_A), linear(Ss), linear(Bs) )
   => mshare([[_A],[_A,_1],[_A,_1,Ss],[_A,_1,Ss,Bs],[_A,_1,Bs],[_A,Ss],[_A,Ss,Bs],[_A,Bs],[_1]]).

split_vars([],_1,[],[]).
split_vars([V|Vs],A,[V|Ss],Bs) :-
    true((mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Bs],[V],[V,Vs],[Vs],[Ss]]),var(Bs),var(Ss),linear(A),linear(Bs),linear(V),linear(Vs),linear(Ss);mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Bs],[V],[V,Vs],[Vs],[Ss]]),var(Bs),var(Ss),linear(Bs),linear(V),linear(Vs),linear(Ss);mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Bs],[V],[V,Vs],[Vs],[Ss]]),var(Bs),var(Ss),linear(Bs),linear(Ss))),
    V@<A,
    !,
    true((mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Bs],[V],[V,Vs],[Vs],[Ss]]),var(Bs),var(Ss),linear(Bs),linear(Vs),linear(Ss);mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Bs],[V],[V,Vs],[Vs],[Ss]]),var(Bs),var(Ss),linear(Bs),linear(Ss))),
    split_vars(Vs,A,Ss,Bs),
    true(mshare([[A],[A,Bs,V,Vs],[A,Bs,V,Vs,Ss],[A,Bs,Vs],[A,Bs,Vs,Ss],[A,V],[A,V,Vs],[A,V,Vs,Ss],[A,Vs],[A,Vs,Ss],[Bs,V,Vs],[Bs,V,Vs,Ss],[Bs,Vs],[Bs,Vs,Ss],[V],[V,Vs],[V,Vs,Ss],[Vs],[Vs,Ss]])).
split_vars([V|Vs],A,Ss,Bs) :-
    true((mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Ss],[Bs],[V],[V,Vs],[Vs]]),var(Ss),var(Bs),linear(A),linear(Ss),linear(Bs),linear(V),linear(Vs);mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Ss],[Bs],[V],[V,Vs],[Vs]]),var(Ss),var(Bs),linear(Ss),linear(Bs);mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Ss],[Bs],[V],[V,Vs],[Vs]]),var(Ss),var(Bs),linear(Ss),linear(Bs),linear(V),linear(Vs))),
    V==A,
    !,
    true((mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Ss],[Bs],[V],[V,Vs],[Vs]]),var(Ss),var(Bs),linear(Ss),linear(Bs);mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Ss],[Bs],[V],[V,Vs],[Vs]]),var(Ss),var(Bs),linear(Ss),linear(Bs),linear(Vs))),
    split_vars(Vs,A,Ss,Bs),
    true(mshare([[A],[A,Ss,Bs,V,Vs],[A,Ss,Bs,Vs],[A,Ss,V,Vs],[A,Ss,Vs],[A,Bs,V,Vs],[A,Bs,Vs],[A,V],[A,V,Vs],[A,Vs],[Ss,Bs,V,Vs],[Ss,Bs,Vs],[Ss,V,Vs],[Ss,Vs],[Bs,V,Vs],[Bs,Vs],[V],[V,Vs],[Vs]])).
split_vars([V|Vs],A,Ss,[V|Bs]) :-
    true((mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Ss],[V],[V,Vs],[Vs],[Bs]]),var(Ss),var(Bs),linear(A),linear(Ss),linear(V),linear(Vs),linear(Bs);mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Ss],[V],[V,Vs],[Vs],[Bs]]),var(Ss),var(Bs),linear(Ss),linear(V),linear(Vs),linear(Bs);mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Ss],[V],[V,Vs],[Vs],[Bs]]),var(Ss),var(Bs),linear(Ss),linear(Bs))),
    V@>A,
    !,
    true((mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Ss],[V],[V,Vs],[Vs],[Bs]]),var(Ss),var(Bs),linear(Ss),linear(Vs),linear(Bs);mshare([[A],[A,V],[A,V,Vs],[A,Vs],[Ss],[V],[V,Vs],[Vs],[Bs]]),var(Ss),var(Bs),linear(Ss),linear(Bs))),
    split_vars(Vs,A,Ss,Bs),
    true(mshare([[A],[A,Ss,V,Vs],[A,Ss,V,Vs,Bs],[A,Ss,Vs],[A,Ss,Vs,Bs],[A,V],[A,V,Vs],[A,V,Vs,Bs],[A,Vs],[A,Vs,Bs],[Ss,V,Vs],[Ss,V,Vs,Bs],[Ss,Vs],[Ss,Vs,Bs],[V],[V,Vs],[V,Vs,Bs],[Vs],[Vs,Bs]])).


