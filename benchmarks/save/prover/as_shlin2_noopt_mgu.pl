:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

:- op(950,xfy,#).

:- initialization(op(950,xfy,#)).

:- op(850,xfy,&).

:- initialization(op(850,xfy,&)).

:- op(500,fx,+).

:- initialization(op(500,fx,+)).

:- op(500,fx,-).

:- initialization(op(500,fx,-)).

'\006\call_in_module'(prover,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    prover,
    true(true).

:- true pred prover.

prover :-
    true((
        mshare([[_1],[P],[C]]),
        linear(_1),
        linear(P),
        linear(C),
        shlin2([([_1],[_1]),([P],[P]),([C],[C])])
    )),
    problem(_1,P,C),
    true(ground([_1,P,C])),
    implies(P,C),
    true(ground([_1,P,C])),
    fail,
    true(fails(_)).
prover.

:- true pred problem(_A,_B,_C)
   : ( mshare([[_A],[_B],[_C]]),
       linear(_A), linear(_B), linear(_C), shlin2([([_A],[_A]),([_B],[_B]),([_C],[_C])]) )
   => ground([_A,_B,_C]).

problem(1,-a,+a).
problem(2,+a,-a& -a).
problem(3,-a,+to_be# -to_be).
problem(4,-a& -a,-a).
problem(5,-a,+b# -a).
problem(6,-a& -b,-b& -a).
problem(7,-a,-b#(+b& -a)).
problem(8,-a#(-b# +c),-b#(-a# +c)).
problem(9,-a# +b,(+b& -c)#(-a# +c)).
problem(10,-a# +c& -b# +c,(-a& -b)# +c).

:- true pred implies(Premise,Conclusion)
   : ground([Premise,Conclusion])
   => ground([Premise,Conclusion]).

implies(Premise,Conclusion) :-
    true((
        mshare([[Denial]]),
        ground([Premise,Conclusion]),
        linear(Denial),
        shlin2([([Denial],[Denial])])
    )),
    opposite(Conclusion,Denial),
    true(ground([Premise,Conclusion,Denial])),
    add_conjunction(Premise,Denial,fs([],[],[],[])),
    true(ground([Premise,Conclusion,Denial])).

:- true pred opposite(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]), linear(_B), shlin2([([_B],[_B])]) )
   => ground([_A,_B]).

:- true pred opposite(_A,_B)
   : ( (_A=_C#_D),
       mshare([[_B]]),
       ground([_C,_D]), linear(_B), shlin2([([_B],[_B])]) )
   => ground([_B,_C,_D]).

opposite(F0&G0,F1#G1) :-
    !,
    true((
        mshare([[F1],[G1]]),
        ground([F0,G0]),
        linear(F1),
        linear(G1),
        shlin2([([F1],[F1]),([G1],[G1])])
    )),
    opposite(F0,F1),
    true((
        mshare([[G1]]),
        ground([F0,G0,F1]),
        linear(G1),
        shlin2([([G1],[G1])])
    )),
    opposite(G0,G1),
    true(ground([F0,G0,F1,G1])).
opposite(F1#G1,F0&G0) :-
    !,
    true((
        mshare([[F0],[G0]]),
        ground([F1,G1]),
        linear(F0),
        linear(G0),
        shlin2([([F0],[F0]),([G0],[G0])])
    )),
    opposite(F1,F0),
    true((
        mshare([[G0]]),
        ground([F1,G1,F0]),
        linear(G0),
        shlin2([([G0],[G0])])
    )),
    opposite(G1,G0),
    true(ground([F1,G1,F0,G0])).
opposite(+Atom,-Atom) :-
    !,
    true(ground([Atom])).
opposite(-Atom,+Atom).

:- true pred add_conjunction(F,G,Set)
   : ground([F,G,Set])
   => ground([F,G,Set]).

:- true pred add_conjunction(F,G,Set)
   : ( (Set=fs([],[],[],[])), ground([F,G]) )
   => ground([F,G]).

add_conjunction(F,G,Set) :-
    true((
        mshare([[Mid],[New]]),
        ground([F,G,Set]),
        linear(Mid),
        linear(New),
        shlin2([([Mid],[Mid]),([New],[New])])
    )),
    expand(F,Set,Mid),
    true((
        mshare([[New]]),
        ground([F,G,Set,Mid]),
        linear(New),
        shlin2([([New],[New])])
    )),
    expand(G,Mid,New),
    true(ground([F,G,Set,Mid,New])),
    refute(New),
    true(ground([F,G,Set,Mid,New])).

:- true pred expand(_1,_A,New)
   : ( (_A=fs(_B,[_1&_F|_E],_C,_D)),
       mshare([[New]]),
       ground([_1,_B,_C,_D,_E,_F]), linear(New), shlin2([([New],[New])]) )
   => ground([_1,New,_B,_C,_D,_E,_F]).

:- true pred expand(_1,_A,New)
   : ( mshare([[New]]),
       ground([_1,_A]), linear(New), shlin2([([New],[New])]) )
   => ground([_1,_A,New]).

expand(_1,refuted,refuted) :-
    !,
    true(ground([_1])).
expand(F&G,fs(D,_1,_2,_3),refuted) :-
    true(ground([F,G,D,_1,_2,_3])),
    includes(D,F&G),
    !,
    true(ground([F,G,D,_1,_2,_3])).
expand(F&G,fs(D,C,P,N),fs(D,C,P,N)) :-
    true(ground([F,G,D,C,P,N])),
    includes(C,F&G),
    !,
    true(ground([F,G,D,C,P,N])).
expand(F&G,fs(D,C,P,N),New) :-
    !,
    true((
        mshare([[New],[Mid]]),
        ground([F,G,D,C,P,N]),
        linear(New),
        linear(Mid),
        shlin2([([New],[New]),([Mid],[Mid])])
    )),
    expand(F,fs(D,[F&G|C],P,N),Mid),
    true((
        mshare([[New]]),
        ground([F,G,D,C,P,N,Mid]),
        linear(New),
        shlin2([([New],[New])])
    )),
    expand(G,Mid,New),
    true(ground([New,F,G,D,C,P,N,Mid])).
expand(F#G,fs(D,C,P,N),Set) :-
    !,
    true((
        mshare([[Set],[Conj],[D1]]),
        ground([F,G,D,C,P,N]),
        linear(Set),
        linear(Conj),
        linear(D1),
        shlin2([([Set],[Set]),([Conj],[Conj]),([D1],[D1])])
    )),
    opposite(F#G,Conj),
    true((
        mshare([[Set],[D1]]),
        ground([F,G,D,C,P,N,Conj]),
        linear(Set),
        linear(D1),
        shlin2([([Set],[Set]),([D1],[D1])])
    )),
    extend(Conj,D,C,D1,fs(D1,C,P,N),Set),
    true((
        mshare([[D1]]),
        ground([Set,F,G,D,C,P,N,Conj]),
        shlin2([([D1],[])])
    )).
expand(+Atom,fs(D,C,P,N),Set) :-
    !,
    true((
        mshare([[Set],[P1]]),
        ground([Atom,D,C,P,N]),
        linear(Set),
        linear(P1),
        shlin2([([Set],[Set]),([P1],[P1])])
    )),
    extend(Atom,P,N,P1,fs(D,C,P1,N),Set),
    true((
        mshare([[P1]]),
        ground([Set,Atom,D,C,P,N]),
        shlin2([([P1],[])])
    )).
expand(-Atom,fs(D,C,P,N),Set) :-
    true((
        mshare([[Set],[N1]]),
        ground([Atom,D,C,P,N]),
        linear(Set),
        linear(N1),
        shlin2([([Set],[Set]),([N1],[N1])])
    )),
    extend(Atom,N,P,N1,fs(D,C,P,N1),Set),
    true((
        mshare([[N1]]),
        ground([Set,Atom,D,C,P,N]),
        shlin2([([N1],[])])
    )).

:- true pred includes(_A,Head)
   : ( (Head=(_B&_C)), ground([_A,_B,_C]) )
   => ground([_A,_B,_C]).

:- true pred includes(_A,Head)
   : ground([_A,Head])
   => ground([_A,Head]).

includes([Head|_1],Head) :-
    !,
    true(ground([Head,_1])).
includes([_1|Tail],This) :-
    true(ground([This,_1,Tail])),
    includes(Tail,This),
    true(ground([This,_1,Tail])).

:- true pred extend(Exp,_1,Neg,_2,_3,Set)
   : ( (_3=fs(_A,_B,Neg,_2)),
       mshare([[_2],[Set]]),
       ground([Exp,_1,Neg,_A,_B]), linear(_2), linear(Set), shlin2([([_2],[_2]),([Set],[Set])]) )
   => ( mshare([[_2],[_2,_A],[_2,_A,_B],[_2,_B]]),
        ground([Exp,_1,Neg,Set]), shlin2([([_2],[]),([_2,_A],[]),([_2,_A,_B],[]),([_2,_B],[])]) ).

:- true pred extend(Exp,_1,Neg,_2,_3,Set)
   : ( (_3=fs(_A,_B,_2,Neg)),
       mshare([[_2],[Set]]),
       ground([Exp,_1,Neg,_A,_B]), linear(_2), linear(Set), shlin2([([_2],[_2]),([Set],[Set])]) )
   => ( mshare([[_2],[_2,_A],[_2,_A,_B],[_2,_B]]),
        ground([Exp,_1,Neg,Set]), shlin2([([_2],[]),([_2,_A],[]),([_2,_A,_B],[]),([_2,_B],[])]) ).

:- true pred extend(Exp,_1,Neg,_2,_3,Set)
   : ( (_3=fs(_2,Neg,_A,_B)),
       mshare([[_2],[Set]]),
       ground([Exp,_1,Neg,_A,_B]), linear(_2), linear(Set), shlin2([([_2],[_2]),([Set],[Set])]) )
   => ( mshare([[_2],[_2,_A],[_2,_A,_B],[_2,_B]]),
        ground([Exp,_1,Neg,Set]), shlin2([([_2],[]),([_2,_A],[]),([_2,_A,_B],[]),([_2,_B],[])]) ).

extend(Exp,_1,Neg,_2,_3,refuted) :-
    true((
        mshare([[_2,_3]]),
        ground([Exp,_1,Neg]),
        linear(_2),
        linear(_3),
        shlin2([([_2,_3],[_2,_3])])
    )),
    includes(Neg,Exp),
    !,
    true((
        mshare([[_2,_3]]),
        ground([Exp,_1,Neg]),
        linear(_2),
        linear(_3),
        shlin2([([_2,_3],[_2,_3])])
    )).
extend(Exp,Pos,_1,Pos,Set,Set) :-
    true(ground([Exp,Pos,_1,Set])),
    includes(Pos,Exp),
    !,
    true(ground([Exp,Pos,_1,Set])).
extend(Exp,Pos,_1,[Exp|Pos],Set,Set).

:- true pred refute(_A)
   : ground([_A])
   => ground([_A]).

refute(refuted) :-
    !,
    true(true).
refute(fs([F1&G1|D],C,P,N)) :-
    true((
        mshare([[F0],[G0],[Set]]),
        ground([C,P,N,D,F1,G1]),
        linear(F0),
        linear(G0),
        linear(Set),
        shlin2([([F0],[F0]),([G0],[G0]),([Set],[Set])])
    )),
    opposite(F1,F0),
    true((
        mshare([[G0],[Set]]),
        ground([C,P,N,D,F1,G1,F0]),
        linear(G0),
        linear(Set),
        shlin2([([G0],[G0]),([Set],[Set])])
    )),
    opposite(G1,G0),
    true((
        mshare([[Set]]),
        ground([C,P,N,D,F1,G1,F0,G0]),
        linear(Set),
        shlin2([([Set],[Set])])
    )),
    Set=fs(D,C,P,N),
    true(ground([C,P,N,D,F1,G1,F0,G0,Set])),
    add_conjunction(F0,G1,Set),
    true(ground([C,P,N,D,F1,G1,F0,G0,Set])),
    add_conjunction(F0,G0,Set),
    true(ground([C,P,N,D,F1,G1,F0,G0,Set])),
    add_conjunction(F1,G0,Set),
    true(ground([C,P,N,D,F1,G1,F0,G0,Set])).


