:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(meta_qsort,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    meta_qsort,
    true(true).

:- true pred meta_qsort.

meta_qsort :-
    true(true),
    interpret(qsort),
    true(true).

:- true pred interpret(Goal)
   : ( mshare([[Goal]]),
       linear(Goal), shlin2([([Goal],[Goal])]) )
   => ( mshare([[Goal]]),
        shlin2([([Goal],[])]) ).

:- true pred interpret(Goal)
   : (Goal=qsort).

:- true pred interpret(Goal)
   : ( mshare([[Goal]]),
       shlin2([([Goal],[])]) )
   => ( mshare([[Goal]]),
        shlin2([([Goal],[])]) ).

interpret(Goal) :-
    true((mshare([[Goal],[Rest]]),linear(Goal),linear(Rest),shlin2([([Goal],[Goal]),([Rest],[Rest])]);mshare([[Goal],[Rest]]),linear(Rest),shlin2([([Goal],[]),([Rest],[Rest])]);mshare([[Rest]]),ground([Goal]),linear(Rest),shlin2([([Rest],[Rest])]))),
    interpret(Goal,Rest),
    true((mshare([[Goal],[Goal,Rest],[Rest]]),linear(Rest),shlin2([([Goal],[]),([Goal,Rest],[Goal,Rest]),([Rest],[Rest])]);mshare([[Goal],[Goal,Rest],[Rest]]),shlin2([([Goal],[]),([Goal,Rest],[]),([Rest],[])]);mshare([[Rest]]),ground([Goal]),linear(Rest),shlin2([([Rest],[Rest])]))),
    'interpret/1/1/$disj/1'(Rest),
    true((mshare([[Goal],[Goal,Rest],[Rest]]),shlin2([([Goal],[]),([Goal,Rest],[]),([Rest],[])]);mshare([[Rest]]),ground([Goal]),shlin2([([Rest],[])]))).

:- true pred 'interpret/1/1/$disj/1'(Rest)
   : ( mshare([[Rest]]),
       shlin2([([Rest],[])]) )
   => ( mshare([[Rest]]),
        shlin2([([Rest],[])]) ).

:- true pred 'interpret/1/1/$disj/1'(Rest)
   : ( mshare([[Rest]]),
       linear(Rest), shlin2([([Rest],[Rest])]) )
   => ( mshare([[Rest]]),
        shlin2([([Rest],[])]) ).

'interpret/1/1/$disj/1'(Rest) :-
    true((mshare([[Rest]]),linear(Rest),shlin2([([Rest],[Rest])]);mshare([[Rest]]),shlin2([([Rest],[])]))),
    nonvar(Rest),
    !,
    true((mshare([[Rest]]),linear(Rest),shlin2([([Rest],[Rest])]);mshare([[Rest]]),shlin2([([Rest],[])]))),
    interpret(Rest),
    true((
        mshare([[Rest]]),
        shlin2([([Rest],[])])
    )).
'interpret/1/1/$disj/1'(Rest).

:- true pred interpret(G,_1)
   : ( mshare([[G],[_1]]),
       linear(_1), shlin2([([G],[]),([_1],[_1])]) )
   => ( mshare([[G],[G,_1],[_1]]),
        shlin2([([G],[]),([G,_1],[]),([_1],[])]) ).

:- true pred interpret(G,_1)
   : ( mshare([[G],[_1]]),
       linear(G), linear(_1), shlin2([([G],[G]),([_1],[_1])]) )
   => ( mshare([[G],[G,_1],[_1]]),
        linear(_1), shlin2([([G],[]),([G,_1],[G,_1]),([_1],[_1])]) ).

:- true pred interpret(G,_1)
   : ( mshare([[_1]]),
       ground([G]), linear(_1), shlin2([([_1],[_1])]) )
   => ( mshare([[_1]]),
        ground([G]), linear(_1), shlin2([([_1],[_1])]) ).

interpret(G,_1) :-
    true((mshare([[G],[_1]]),linear(G),linear(_1),shlin2([([G],[G]),([_1],[_1])]);mshare([[G],[_1]]),linear(_1),shlin2([([G],[]),([_1],[_1])]);mshare([[_1]]),ground([G]),linear(_1),shlin2([([_1],[_1])]))),
    var(G),
    !,
    true((fails(_);mshare([[G],[_1]]),linear(G),linear(_1),shlin2([([G],[G]),([_1],[G,_1])]))),
    fail,
    true(fails(_)).
interpret((A,B),Rest) :-
    !,
    true((mshare([[Rest],[A],[A,B],[B],[Rest0]]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([A],[]),([A,B],[]),([B],[]),([Rest0],[Rest0])]);mshare([[Rest],[A],[B],[Rest0]]),linear(Rest),linear(A),linear(B),linear(Rest0),shlin2([([Rest],[Rest]),([A],[A]),([B],[B]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([A,B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest0],[Rest0])]))),
    interpret(A,Rest0),
    true((mshare([[Rest],[A],[A,B],[A,B,Rest0],[A,Rest0],[B],[Rest0]]),linear(Rest),shlin2([([Rest],[Rest]),([A],[]),([A,B],[]),([A,B,Rest0],[]),([A,Rest0],[]),([B],[]),([Rest0],[])]);mshare([[Rest],[A],[A,Rest0],[B],[Rest0]]),linear(Rest),linear(B),linear(Rest0),shlin2([([Rest],[Rest]),([A],[]),([A,Rest0],[A,Rest0]),([B],[B]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([A,B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest0],[Rest0])]))),
    'interpret/2/2/$disj/1'(Rest,B,Rest0),
    true((mshare([[Rest],[Rest,A,B],[Rest,A,B,Rest0],[Rest,A,Rest0],[Rest,B],[Rest,B,Rest0],[Rest,Rest0],[A],[A,B],[A,B,Rest0],[A,Rest0],[B],[B,Rest0],[Rest0]]),shlin2([([Rest],[]),([Rest,A,B],[]),([Rest,A,B,Rest0],[]),([Rest,A,Rest0],[]),([Rest,B],[]),([Rest,B,Rest0],[]),([Rest,Rest0],[]),([A],[]),([A,B],[]),([A,B,Rest0],[]),([A,Rest0],[]),([B],[]),([B,Rest0],[]),([Rest0],[])]);mshare([[Rest],[Rest,A,Rest0],[Rest,B],[Rest,Rest0],[A],[A,Rest0],[B],[Rest0]]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest,A,Rest0],[Rest,A,Rest0]),([Rest,B],[Rest,B]),([Rest,Rest0],[Rest,Rest0]),([A],[]),([A,Rest0],[A,Rest0]),([B],[]),([Rest0],[Rest0])]);mshare([[Rest],[Rest,Rest0],[Rest0]]),ground([A,B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest,Rest0],[Rest,Rest0]),([Rest0],[Rest0])]))).
interpret((A;B),Rest) :-
    !,
    true((mshare([[Rest]]),ground([A,B]),linear(Rest),shlin2([([Rest],[Rest])]);mshare([[Rest],[A],[A,B],[B]]),linear(Rest),shlin2([([Rest],[Rest]),([A],[]),([A,B],[]),([B],[])]);mshare([[Rest],[A],[B]]),linear(Rest),linear(A),linear(B),shlin2([([Rest],[Rest]),([A],[A]),([B],[B])]))),
    interpret_disjunction(A,B,Rest),
    true((mshare([[Rest]]),ground([A,B]),linear(Rest),shlin2([([Rest],[Rest])]);mshare([[Rest],[Rest,A],[Rest,A,B],[Rest,B],[A],[A,B],[B]]),shlin2([([Rest],[]),([Rest,A],[]),([Rest,A,B],[]),([Rest,B],[]),([A],[]),([A,B],[]),([B],[])]);mshare([[Rest],[Rest,A],[Rest,B],[A],[B]]),linear(Rest),shlin2([([Rest],[Rest]),([Rest,A],[Rest,A]),([Rest,B],[Rest,B]),([A],[]),([B],[])]))).
interpret((A->B),Rest) :-
    !,
    true((mshare([[Rest]]),ground([A,B]),linear(Rest),shlin2([([Rest],[Rest])]);mshare([[Rest],[A],[A,B],[B]]),linear(Rest),shlin2([([Rest],[Rest]),([A],[]),([A,B],[]),([B],[])]);mshare([[Rest],[A],[B]]),linear(Rest),linear(A),linear(B),shlin2([([Rest],[Rest]),([A],[A]),([B],[B])]))),
    interpret_disjunction((A->B),fail,Rest),
    true((mshare([[Rest]]),ground([A,B]),linear(Rest),shlin2([([Rest],[Rest])]);mshare([[Rest],[Rest,A],[Rest,A,B],[Rest,B],[A],[A,B],[B]]),shlin2([([Rest],[]),([Rest,A],[]),([Rest,A,B],[]),([Rest,B],[]),([A],[]),([A,B],[]),([B],[])]);mshare([[Rest],[Rest,A],[Rest,B],[A],[A,B],[B]]),linear(Rest),shlin2([([Rest],[Rest]),([Rest,A],[Rest,A]),([Rest,B],[Rest,B]),([A],[]),([A,B],[]),([B],[])]))).
interpret(\+A,Rest) :-
    !,
    true((mshare([[Rest]]),ground([A]),linear(Rest),shlin2([([Rest],[Rest])]);mshare([[Rest],[A]]),linear(Rest),linear(A),shlin2([([Rest],[Rest]),([A],[A])]);mshare([[Rest],[A]]),linear(Rest),shlin2([([Rest],[Rest]),([A],[])]))),
    interpret_disjunction((A->fail),true,Rest),
    true((mshare([[Rest]]),ground([A]),linear(Rest),shlin2([([Rest],[Rest])]);mshare([[Rest],[Rest,A],[A]]),linear(Rest),shlin2([([Rest],[Rest]),([Rest,A],[Rest,A]),([A],[])]);mshare([[Rest],[Rest,A],[A]]),shlin2([([Rest],[]),([Rest,A],[]),([A],[])]))).
interpret(!,true) :-
    !,
    true(true).
interpret(G,_1) :-
    true((mshare([[G],[_1]]),linear(G),linear(_1),shlin2([([G],[G]),([_1],[_1])]);mshare([[G],[_1]]),linear(_1),shlin2([([G],[]),([_1],[_1])]);mshare([[_1]]),ground([G]),linear(_1),shlin2([([_1],[_1])]))),
    number(G),
    !,
    true((
        mshare([[_1]]),
        ground([G]),
        linear(_1),
        shlin2([([_1],[_1])])
    )),
    fail,
    true(fails(_)).
interpret(G,_1) :-
    true((mshare([[G],[_1]]),linear(G),linear(_1),shlin2([([G],[G]),([_1],[_1])]);mshare([[G],[_1]]),linear(_1),shlin2([([G],[]),([_1],[_1])]);mshare([[_1]]),ground([G]),linear(_1),shlin2([([_1],[_1])]))),
    is_built_in(G),
    !,
    true((mshare([[G],[_1]]),linear(G),linear(_1),shlin2([([G],[G]),([_1],[_1])]);mshare([[G],[_1]]),linear(_1),shlin2([([G],[]),([_1],[_1])]);mshare([[_1]]),ground([G]),linear(_1),shlin2([([_1],[_1])]))),
    interpret_built_in(G),
    true((
        mshare([[_1]]),
        ground([G]),
        linear(_1),
        shlin2([([_1],[_1])])
    )).
interpret(G,_1) :-
    true((mshare([[G],[_1],[Body]]),linear(G),linear(_1),linear(Body),shlin2([([G],[G]),([_1],[_1]),([Body],[Body])]);mshare([[G],[_1],[Body]]),linear(_1),linear(Body),shlin2([([G],[]),([_1],[_1]),([Body],[Body])]);mshare([[_1],[Body]]),ground([G]),linear(_1),linear(Body),shlin2([([_1],[_1]),([Body],[Body])]))),
    define(G,Body),
    true((mshare([[G],[G,Body],[_1],[Body]]),linear(_1),shlin2([([G],[]),([G,Body],[]),([_1],[_1]),([Body],[])]);mshare([[G],[G,Body],[_1],[Body]]),linear(_1),shlin2([([G],[]),([G,Body],[G]),([G,Body],[Body]),([_1],[_1]),([Body],[])]);mshare([[_1],[Body]]),ground([G]),linear(_1),shlin2([([_1],[_1]),([Body],[])]))),
    interpret(Body),
    true((mshare([[G],[G,Body],[_1],[Body]]),linear(_1),shlin2([([G],[]),([G,Body],[]),([_1],[_1]),([Body],[])]);mshare([[_1],[Body]]),ground([G]),linear(_1),shlin2([([_1],[_1]),([Body],[])]))).

:- true pred 'interpret/2/2/$disj/1'(Rest,B,Rest0)
   : ( mshare([[Rest],[Rest0]]),
       ground([B]), linear(Rest), linear(Rest0), shlin2([([Rest],[Rest]),([Rest0],[Rest0])]) )
   => ( mshare([[Rest],[Rest,Rest0],[Rest0]]),
        ground([B]), linear(Rest), linear(Rest0), shlin2([([Rest],[Rest]),([Rest,Rest0],[Rest,Rest0]),([Rest0],[Rest0])]) ).

:- true pred 'interpret/2/2/$disj/1'(Rest,B,Rest0)
   : ( mshare([[Rest],[B],[Rest0]]),
       linear(Rest), linear(Rest0), shlin2([([Rest],[Rest]),([B],[]),([Rest0],[Rest0])]) )
   => ( mshare([[Rest],[Rest,B],[Rest,Rest0],[Rest0]]),
        linear(Rest0), shlin2([([Rest],[Rest]),([Rest,B],[]),([Rest,Rest0],[Rest,Rest0]),([Rest0],[Rest0])]) ).

:- true pred 'interpret/2/2/$disj/1'(Rest,B,Rest0)
   : ( mshare([[Rest],[B],[B,Rest0],[Rest0]]),
       linear(Rest), shlin2([([Rest],[Rest]),([B],[]),([B,Rest0],[]),([Rest0],[])]) )
   => ( mshare([[Rest],[Rest,B],[Rest,B,Rest0],[Rest,Rest0],[B],[B,Rest0],[Rest0]]),
        shlin2([([Rest],[]),([Rest,B],[]),([Rest,B,Rest0],[]),([Rest,Rest0],[]),([B],[]),([B,Rest0],[]),([Rest0],[])]) ).

:- true pred 'interpret/2/2/$disj/1'(Rest,B,Rest0)
   : ( mshare([[Rest],[B],[Rest0]]),
       linear(Rest), linear(B), linear(Rest0), shlin2([([Rest],[Rest]),([B],[B]),([Rest0],[Rest0])]) )
   => ( mshare([[Rest],[Rest,B],[Rest,Rest0],[B],[Rest0]]),
        linear(Rest), linear(Rest0), shlin2([([Rest],[Rest]),([Rest,B],[Rest,B]),([Rest,Rest0],[Rest,Rest0]),([B],[]),([Rest0],[Rest0])]) ).

'interpret/2/2/$disj/1'(Rest,B,Rest0) :-
    true((mshare([[Rest],[B],[B,Rest0],[Rest0]]),linear(Rest),shlin2([([Rest],[Rest]),([B],[]),([B,Rest0],[]),([Rest0],[])]);mshare([[Rest],[B],[Rest0]]),linear(Rest),linear(B),linear(Rest0),shlin2([([Rest],[Rest]),([B],[B]),([Rest0],[Rest0])]);mshare([[Rest],[B],[Rest0]]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([B],[]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest0],[Rest0])]))),
    nonvar(Rest0),
    !,
    true((mshare([[Rest],[B],[B,Rest0],[Rest0]]),linear(Rest),shlin2([([Rest],[Rest]),([B],[]),([B,Rest0],[]),([Rest0],[])]);mshare([[Rest],[B],[Rest0]]),linear(Rest),linear(B),linear(Rest0),shlin2([([Rest],[Rest]),([B],[B]),([Rest0],[Rest0])]);mshare([[Rest],[B],[Rest0]]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([B],[]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest0],[Rest0])]))),
    Rest=(Rest0,B),
    true((mshare([[Rest,B],[Rest,B,Rest0],[Rest,Rest0]]),shlin2([([Rest,B],[]),([Rest,B,Rest0],[]),([Rest,Rest0],[])]);mshare([[Rest,B],[Rest,Rest0]]),linear(Rest),linear(B),linear(Rest0),shlin2([([Rest,B],[Rest,B]),([Rest,Rest0],[Rest,Rest0])]);mshare([[Rest,B],[Rest,Rest0]]),linear(Rest0),shlin2([([Rest,B],[]),([Rest,Rest0],[Rest,Rest0])]);mshare([[Rest,Rest0]]),ground([B]),linear(Rest),linear(Rest0),shlin2([([Rest,Rest0],[Rest,Rest0])]))).
'interpret/2/2/$disj/1'(Rest,B,Rest0) :-
    true((mshare([[Rest],[B],[B,Rest0],[Rest0]]),linear(Rest),shlin2([([Rest],[Rest]),([B],[]),([B,Rest0],[]),([Rest0],[])]);mshare([[Rest],[B],[Rest0]]),linear(Rest),linear(B),linear(Rest0),shlin2([([Rest],[Rest]),([B],[B]),([Rest0],[Rest0])]);mshare([[Rest],[B],[Rest0]]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([B],[]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest0],[Rest0])]))),
    interpret(B,Rest),
    true((mshare([[Rest],[Rest,B],[Rest,B,Rest0],[B],[B,Rest0],[Rest0]]),shlin2([([Rest],[]),([Rest,B],[]),([Rest,B,Rest0],[]),([B],[]),([B,Rest0],[]),([Rest0],[])]);mshare([[Rest],[Rest,B],[B],[Rest0]]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest,B],[Rest,B]),([B],[]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest0],[Rest0])]))).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( mshare([[Rest]]),
       ground([A,_1]), linear(Rest), shlin2([([Rest],[Rest])]) )
   => ( mshare([[Rest]]),
        ground([A,_1]), linear(Rest), shlin2([([Rest],[Rest])]) ).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( (A=(_A->_B)), (_1=fail),
       mshare([[Rest]]),
       ground([_A,_B]), linear(Rest), shlin2([([Rest],[Rest])]) )
   => ( mshare([[Rest]]),
        ground([_A,_B]), linear(Rest), shlin2([([Rest],[Rest])]) ).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( (A=(_A->fail)), (_1=true),
       mshare([[Rest]]),
       ground([_A]), linear(Rest), shlin2([([Rest],[Rest])]) )
   => ( mshare([[Rest]]),
        ground([_A]), linear(Rest), shlin2([([Rest],[Rest])]) ).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( mshare([[A],[A,_1],[_1],[Rest]]),
       linear(Rest), shlin2([([A],[]),([A,_1],[]),([_1],[]),([Rest],[Rest])]) )
   => ( mshare([[A],[A,_1],[A,_1,Rest],[A,Rest],[_1],[_1,Rest],[Rest]]),
        shlin2([([A],[]),([A,_1],[]),([A,_1,Rest],[]),([A,Rest],[]),([_1],[]),([_1,Rest],[]),([Rest],[])]) ).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( (A=(_A->_B)), (_1=fail),
       mshare([[Rest],[_A],[_A,_B],[_B]]),
       linear(Rest), shlin2([([Rest],[Rest]),([_A],[]),([_A,_B],[]),([_B],[])]) )
   => ( mshare([[Rest],[Rest,_A],[Rest,_A,_B],[Rest,_B],[_A],[_A,_B],[_B]]),
        shlin2([([Rest],[]),([Rest,_A],[]),([Rest,_A,_B],[]),([Rest,_B],[]),([_A],[]),([_A,_B],[]),([_B],[])]) ).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( (A=(_A->fail)), (_1=true),
       mshare([[Rest],[_A]]),
       linear(Rest), shlin2([([Rest],[Rest]),([_A],[])]) )
   => ( mshare([[Rest],[Rest,_A],[_A]]),
        shlin2([([Rest],[]),([Rest,_A],[]),([_A],[])]) ).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( mshare([[A],[_1],[Rest]]),
       linear(A), linear(_1), linear(Rest), shlin2([([A],[A]),([_1],[_1]),([Rest],[Rest])]) )
   => ( mshare([[A],[A,Rest],[_1],[_1,Rest],[Rest]]),
        linear(Rest), shlin2([([A],[]),([A,Rest],[A,Rest]),([_1],[]),([_1,Rest],[_1,Rest]),([Rest],[Rest])]) ).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( (A=(_A->_B)), (_1=fail),
       mshare([[Rest],[_A],[_B]]),
       linear(Rest), linear(_A), linear(_B), shlin2([([Rest],[Rest]),([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[Rest],[Rest,_A],[Rest,_B],[_A],[_A,_B],[_B]]),
        linear(Rest), shlin2([([Rest],[Rest]),([Rest,_A],[Rest,_A]),([Rest,_B],[Rest,_B]),([_A],[]),([_A,_B],[]),([_B],[])]) ).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( (A=(_A->fail)), (_1=true),
       mshare([[Rest],[_A]]),
       linear(Rest), linear(_A), shlin2([([Rest],[Rest]),([_A],[_A])]) )
   => ( mshare([[Rest],[Rest,_A],[_A]]),
        linear(Rest), shlin2([([Rest],[Rest]),([Rest,_A],[Rest,_A]),([_A],[])]) ).

interpret_disjunction((A->B),_1,Rest) :-
    true((mshare([[_1],[_1,A],[_1,A,B],[_1,B],[Rest],[A],[A,B],[B],[Rest0]]),linear(Rest),linear(Rest0),shlin2([([_1],[]),([_1,A],[]),([_1,A,B],[]),([_1,B],[]),([Rest],[Rest]),([A],[]),([A,B],[]),([B],[]),([Rest0],[Rest0])]);mshare([[_1],[Rest],[A],[B],[Rest0]]),linear(_1),linear(Rest),linear(A),linear(B),linear(Rest0),shlin2([([_1],[_1]),([Rest],[Rest]),([A],[A]),([B],[B]),([Rest0],[Rest0])]);mshare([[Rest],[A],[A,B],[B],[Rest0]]),ground([_1]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([A],[]),([A,B],[]),([B],[]),([Rest0],[Rest0])]);mshare([[Rest],[A],[B],[Rest0]]),ground([_1]),linear(Rest),linear(A),linear(B),linear(Rest0),shlin2([([Rest],[Rest]),([A],[A]),([B],[B]),([Rest0],[Rest0])]);mshare([[Rest],[A],[Rest0]]),ground([_1,B]),linear(Rest),linear(A),linear(Rest0),shlin2([([Rest],[Rest]),([A],[A]),([Rest0],[Rest0])]);mshare([[Rest],[A],[Rest0]]),ground([_1,B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([A],[]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([_1,A,B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest0],[Rest0])]))),
    interpret(A,Rest0),
    !,
    true((mshare([[_1],[_1,A],[_1,A,B],[_1,A,B,Rest0],[_1,A,Rest0],[_1,B],[Rest],[A],[A,B],[A,B,Rest0],[A,Rest0],[B],[Rest0]]),linear(Rest),shlin2([([_1],[]),([_1,A],[]),([_1,A,B],[]),([_1,A,B,Rest0],[]),([_1,A,Rest0],[]),([_1,B],[]),([Rest],[Rest]),([A],[]),([A,B],[]),([A,B,Rest0],[]),([A,Rest0],[]),([B],[]),([Rest0],[])]);mshare([[_1],[Rest],[A],[A,Rest0],[B],[Rest0]]),linear(_1),linear(Rest),linear(B),linear(Rest0),shlin2([([_1],[_1]),([Rest],[Rest]),([A],[]),([A,Rest0],[A,Rest0]),([B],[B]),([Rest0],[Rest0])]);mshare([[Rest],[A],[A,B],[A,B,Rest0],[A,Rest0],[B],[Rest0]]),ground([_1]),linear(Rest),shlin2([([Rest],[Rest]),([A],[]),([A,B],[]),([A,B,Rest0],[]),([A,Rest0],[]),([B],[]),([Rest0],[])]);mshare([[Rest],[A],[A,Rest0],[B],[Rest0]]),ground([_1]),linear(Rest),linear(B),linear(Rest0),shlin2([([Rest],[Rest]),([A],[]),([A,Rest0],[A,Rest0]),([B],[B]),([Rest0],[Rest0])]);mshare([[Rest],[A],[A,Rest0],[Rest0]]),ground([_1,B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([A],[]),([A,Rest0],[A,Rest0]),([Rest0],[Rest0])]);mshare([[Rest],[A],[A,Rest0],[Rest0]]),ground([_1,B]),linear(Rest),shlin2([([Rest],[Rest]),([A],[]),([A,Rest0],[]),([Rest0],[])]);mshare([[Rest],[Rest0]]),ground([_1,A,B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest0],[Rest0])]))),
    'interpret_disjunction/3/1/$disj/1'(Rest,B,Rest0),
    true((mshare([[_1],[_1,Rest,A,B],[_1,Rest,A,B,Rest0],[_1,Rest,A,Rest0],[_1,Rest,B],[_1,Rest,B,Rest0],[_1,A],[_1,A,B],[_1,A,B,Rest0],[_1,A,Rest0],[_1,B],[_1,B,Rest0],[Rest],[Rest,A,B],[Rest,A,B,Rest0],[Rest,A,Rest0],[Rest,B],[Rest,B,Rest0],[Rest,Rest0],[A],[A,B],[A,B,Rest0],[A,Rest0],[B],[B,Rest0],[Rest0]]),shlin2([([_1],[]),([_1,Rest,A,B],[]),([_1,Rest,A,B,Rest0],[]),([_1,Rest,A,Rest0],[]),([_1,Rest,B],[]),([_1,Rest,B,Rest0],[]),([_1,A],[]),([_1,A,B],[]),([_1,A,B,Rest0],[]),([_1,A,Rest0],[]),([_1,B],[]),([_1,B,Rest0],[]),([Rest],[]),([Rest,A,B],[]),([Rest,A,B,Rest0],[]),([Rest,A,Rest0],[]),([Rest,B],[]),([Rest,B,Rest0],[]),([Rest,Rest0],[]),([A],[]),([A,B],[]),([A,B,Rest0],[]),([A,Rest0],[]),([B],[]),([B,Rest0],[]),([Rest0],[])]);mshare([[_1],[Rest],[Rest,A,Rest0],[Rest,B],[Rest,Rest0],[A],[A,Rest0],[B],[Rest0]]),linear(_1),linear(Rest),linear(Rest0),shlin2([([_1],[_1]),([Rest],[Rest]),([Rest,A,Rest0],[Rest,A,Rest0]),([Rest,B],[Rest,B]),([Rest,Rest0],[Rest,Rest0]),([A],[]),([A,Rest0],[A,Rest0]),([B],[]),([Rest0],[Rest0])]);mshare([[Rest],[Rest,A,B],[Rest,A,B,Rest0],[Rest,A,Rest0],[Rest,B],[Rest,B,Rest0],[Rest,Rest0],[A],[A,B],[A,B,Rest0],[A,Rest0],[B],[B,Rest0],[Rest0]]),ground([_1]),shlin2([([Rest],[]),([Rest,A,B],[]),([Rest,A,B,Rest0],[]),([Rest,A,Rest0],[]),([Rest,B],[]),([Rest,B,Rest0],[]),([Rest,Rest0],[]),([A],[]),([A,B],[]),([A,B,Rest0],[]),([A,Rest0],[]),([B],[]),([B,Rest0],[]),([Rest0],[])]);mshare([[Rest],[Rest,A,Rest0],[Rest,B],[Rest,Rest0],[A],[A,Rest0],[B],[Rest0]]),ground([_1]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest,A,Rest0],[Rest,A,Rest0]),([Rest,B],[Rest,B]),([Rest,Rest0],[Rest,Rest0]),([A],[]),([A,Rest0],[A,Rest0]),([B],[]),([Rest0],[Rest0])]);mshare([[Rest],[Rest,A,Rest0],[Rest,Rest0],[A],[A,Rest0],[Rest0]]),ground([_1,B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest,A,Rest0],[Rest,A,Rest0]),([Rest,Rest0],[Rest,Rest0]),([A],[]),([A,Rest0],[A,Rest0]),([Rest0],[Rest0])]);mshare([[Rest],[Rest,A,Rest0],[Rest,Rest0],[A],[A,Rest0],[Rest0]]),ground([_1,B]),shlin2([([Rest],[Rest]),([Rest,A,Rest0],[]),([Rest,Rest0],[]),([A],[]),([A,Rest0],[]),([Rest0],[])]);mshare([[Rest],[Rest,Rest0],[Rest0]]),ground([_1,A,B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest,Rest0],[Rest,Rest0]),([Rest0],[Rest0])]))).
interpret_disjunction((_1->_2),C,Rest) :-
    !,
    true((mshare([[C],[C,_1],[C,_1,_2],[C,_2],[Rest],[_1],[_1,_2],[_2]]),linear(Rest),shlin2([([C],[]),([C,_1],[]),([C,_1,_2],[]),([C,_2],[]),([Rest],[Rest]),([_1],[]),([_1,_2],[]),([_2],[])]);mshare([[C],[Rest],[_1],[_2]]),linear(C),linear(Rest),linear(_1),linear(_2),shlin2([([C],[C]),([Rest],[Rest]),([_1],[_1]),([_2],[_2])]);mshare([[Rest]]),ground([C,_1,_2]),linear(Rest),shlin2([([Rest],[Rest])]);mshare([[Rest],[_1]]),ground([C,_2]),linear(Rest),linear(_1),shlin2([([Rest],[Rest]),([_1],[_1])]);mshare([[Rest],[_1]]),ground([C,_2]),linear(Rest),shlin2([([Rest],[Rest]),([_1],[])]);mshare([[Rest],[_1],[_1,_2],[_2]]),ground([C]),linear(Rest),shlin2([([Rest],[Rest]),([_1],[]),([_1,_2],[]),([_2],[])]);mshare([[Rest],[_1],[_2]]),ground([C]),linear(Rest),linear(_1),linear(_2),shlin2([([Rest],[Rest]),([_1],[_1]),([_2],[_2])]))),
    interpret(C,Rest),
    true((mshare([[C],[C,Rest],[C,Rest,_1],[C,Rest,_1,_2],[C,Rest,_2],[C,_1],[C,_1,_2],[C,_2],[Rest],[_1],[_1,_2],[_2]]),shlin2([([C],[]),([C,Rest],[]),([C,Rest,_1],[]),([C,Rest,_1,_2],[]),([C,Rest,_2],[]),([C,_1],[]),([C,_1,_2],[]),([C,_2],[]),([Rest],[]),([_1],[]),([_1,_2],[]),([_2],[])]);mshare([[C],[C,Rest],[Rest],[_1],[_2]]),linear(Rest),linear(_1),linear(_2),shlin2([([C],[]),([C,Rest],[C,Rest]),([Rest],[Rest]),([_1],[_1]),([_2],[_2])]);mshare([[Rest]]),ground([C,_1,_2]),linear(Rest),shlin2([([Rest],[Rest])]);mshare([[Rest],[_1]]),ground([C,_2]),linear(Rest),linear(_1),shlin2([([Rest],[Rest]),([_1],[_1])]);mshare([[Rest],[_1]]),ground([C,_2]),linear(Rest),shlin2([([Rest],[Rest]),([_1],[])]);mshare([[Rest],[_1],[_1,_2],[_2]]),ground([C]),linear(Rest),shlin2([([Rest],[Rest]),([_1],[]),([_1,_2],[]),([_2],[])]);mshare([[Rest],[_1],[_2]]),ground([C]),linear(Rest),linear(_1),linear(_2),shlin2([([Rest],[Rest]),([_1],[_1]),([_2],[_2])]))).
interpret_disjunction(A,_1,Rest) :-
    true((mshare([[A],[A,_1],[_1],[Rest]]),linear(Rest),shlin2([([A],[]),([A,_1],[]),([_1],[]),([Rest],[Rest])]);mshare([[A],[_1],[Rest]]),linear(A),linear(_1),linear(Rest),shlin2([([A],[A]),([_1],[_1]),([Rest],[Rest])]);mshare([[A],[Rest]]),ground([_1]),linear(A),linear(Rest),shlin2([([A],[A]),([Rest],[Rest])]);mshare([[A],[Rest]]),ground([_1]),linear(Rest),shlin2([([A],[]),([Rest],[Rest])]);mshare([[Rest]]),ground([A,_1]),linear(Rest),shlin2([([Rest],[Rest])]))),
    interpret(A,Rest),
    true((mshare([[A],[A,_1],[A,_1,Rest],[A,Rest],[_1],[Rest]]),shlin2([([A],[]),([A,_1],[]),([A,_1,Rest],[]),([A,Rest],[]),([_1],[]),([Rest],[])]);mshare([[A],[A,Rest],[_1],[Rest]]),linear(_1),linear(Rest),shlin2([([A],[]),([A,Rest],[A,Rest]),([_1],[_1]),([Rest],[Rest])]);mshare([[A],[A,Rest],[Rest]]),ground([_1]),linear(Rest),shlin2([([A],[]),([A,Rest],[A,Rest]),([Rest],[Rest])]);mshare([[A],[A,Rest],[Rest]]),ground([_1]),shlin2([([A],[]),([A,Rest],[]),([Rest],[])]);mshare([[Rest]]),ground([A,_1]),linear(Rest),shlin2([([Rest],[Rest])]))).
interpret_disjunction(_1,B,Rest) :-
    true((mshare([[_1],[_1,B],[B],[Rest]]),linear(Rest),shlin2([([_1],[]),([_1,B],[]),([B],[]),([Rest],[Rest])]);mshare([[_1],[B],[Rest]]),linear(_1),linear(B),linear(Rest),shlin2([([_1],[_1]),([B],[B]),([Rest],[Rest])]);mshare([[_1],[Rest]]),ground([B]),linear(_1),linear(Rest),shlin2([([_1],[_1]),([Rest],[Rest])]);mshare([[_1],[Rest]]),ground([B]),linear(Rest),shlin2([([_1],[]),([Rest],[Rest])]);mshare([[Rest]]),ground([_1,B]),linear(Rest),shlin2([([Rest],[Rest])]))),
    interpret(B,Rest),
    true((mshare([[_1],[_1,B],[_1,B,Rest],[B],[B,Rest],[Rest]]),shlin2([([_1],[]),([_1,B],[]),([_1,B,Rest],[]),([B],[]),([B,Rest],[]),([Rest],[])]);mshare([[_1],[B],[B,Rest],[Rest]]),linear(_1),linear(Rest),shlin2([([_1],[_1]),([B],[]),([B,Rest],[B,Rest]),([Rest],[Rest])]);mshare([[_1],[Rest]]),ground([B]),linear(_1),linear(Rest),shlin2([([_1],[_1]),([Rest],[Rest])]);mshare([[_1],[Rest]]),ground([B]),linear(Rest),shlin2([([_1],[]),([Rest],[Rest])]);mshare([[Rest]]),ground([_1,B]),linear(Rest),shlin2([([Rest],[Rest])]))).

:- true pred 'interpret_disjunction/3/1/$disj/1'(Rest,B,Rest0)
   : ( mshare([[Rest],[B],[B,Rest0],[Rest0]]),
       linear(Rest), shlin2([([Rest],[Rest]),([B],[]),([B,Rest0],[]),([Rest0],[])]) )
   => ( mshare([[Rest],[Rest,B],[Rest,B,Rest0],[Rest,Rest0],[B],[B,Rest0],[Rest0]]),
        shlin2([([Rest],[]),([Rest,B],[]),([Rest,B,Rest0],[]),([Rest,Rest0],[]),([B],[]),([B,Rest0],[]),([Rest0],[])]) ).

:- true pred 'interpret_disjunction/3/1/$disj/1'(Rest,B,Rest0)
   : ( mshare([[Rest],[B],[Rest0]]),
       linear(Rest), linear(B), linear(Rest0), shlin2([([Rest],[Rest]),([B],[B]),([Rest0],[Rest0])]) )
   => ( mshare([[Rest],[Rest,B],[Rest,Rest0],[B],[Rest0]]),
        linear(Rest), linear(Rest0), shlin2([([Rest],[Rest]),([Rest,B],[Rest,B]),([Rest,Rest0],[Rest,Rest0]),([B],[]),([Rest0],[Rest0])]) ).

:- true pred 'interpret_disjunction/3/1/$disj/1'(Rest,B,Rest0)
   : ( mshare([[Rest],[Rest0]]),
       ground([B]), linear(Rest), linear(Rest0), shlin2([([Rest],[Rest]),([Rest0],[Rest0])]) )
   => ( mshare([[Rest],[Rest,Rest0],[Rest0]]),
        ground([B]), linear(Rest), linear(Rest0), shlin2([([Rest],[Rest]),([Rest,Rest0],[Rest,Rest0]),([Rest0],[Rest0])]) ).

:- true pred 'interpret_disjunction/3/1/$disj/1'(Rest,B,Rest0)
   : ( mshare([[Rest],[Rest0]]),
       ground([B]), linear(Rest), shlin2([([Rest],[Rest]),([Rest0],[])]) )
   => ( mshare([[Rest],[Rest,Rest0],[Rest0]]),
        ground([B]), shlin2([([Rest],[Rest]),([Rest,Rest0],[]),([Rest0],[])]) ).

'interpret_disjunction/3/1/$disj/1'(Rest,B,Rest0) :-
    true((mshare([[Rest],[B],[B,Rest0],[Rest0]]),linear(Rest),shlin2([([Rest],[Rest]),([B],[]),([B,Rest0],[]),([Rest0],[])]);mshare([[Rest],[B],[Rest0]]),linear(Rest),linear(B),linear(Rest0),shlin2([([Rest],[Rest]),([B],[B]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest),shlin2([([Rest],[Rest]),([Rest0],[])]))),
    nonvar(Rest0),
    !,
    true((mshare([[Rest],[B],[B,Rest0],[Rest0]]),linear(Rest),shlin2([([Rest],[Rest]),([B],[]),([B,Rest0],[]),([Rest0],[])]);mshare([[Rest],[B],[Rest0]]),linear(Rest),linear(B),linear(Rest0),shlin2([([Rest],[Rest]),([B],[B]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest),shlin2([([Rest],[Rest]),([Rest0],[])]))),
    Rest=(Rest0->B),
    true((mshare([[Rest,B],[Rest,B,Rest0],[Rest,Rest0]]),shlin2([([Rest,B],[]),([Rest,B,Rest0],[]),([Rest,Rest0],[])]);mshare([[Rest,B],[Rest,Rest0]]),linear(Rest),linear(B),linear(Rest0),shlin2([([Rest,B],[Rest,B]),([Rest,Rest0],[Rest,Rest0])]);mshare([[Rest,Rest0]]),ground([B]),linear(Rest),linear(Rest0),shlin2([([Rest,Rest0],[Rest,Rest0])]);mshare([[Rest,Rest0]]),ground([B]),shlin2([([Rest,Rest0],[])]))).
'interpret_disjunction/3/1/$disj/1'(Rest,B,Rest0) :-
    true((mshare([[Rest],[B],[B,Rest0],[Rest0]]),linear(Rest),shlin2([([Rest],[Rest]),([B],[]),([B,Rest0],[]),([Rest0],[])]);mshare([[Rest],[B],[Rest0]]),linear(Rest),linear(B),linear(Rest0),shlin2([([Rest],[Rest]),([B],[B]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest),shlin2([([Rest],[Rest]),([Rest0],[])]))),
    interpret(B,Rest),
    true((mshare([[Rest],[Rest,B],[Rest,B,Rest0],[B],[B,Rest0],[Rest0]]),shlin2([([Rest],[]),([Rest,B],[]),([Rest,B,Rest0],[]),([B],[]),([B,Rest0],[]),([Rest0],[])]);mshare([[Rest],[Rest,B],[B],[Rest0]]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest,B],[Rest,B]),([B],[]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest),linear(Rest0),shlin2([([Rest],[Rest]),([Rest0],[Rest0])]);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest),shlin2([([Rest],[Rest]),([Rest0],[])]))).

:- true pred is_built_in(_A)
   : ( mshare([[_A]]),
       linear(_A), shlin2([([_A],[_A])]) )
   => ( mshare([[_A]]),
        linear(_A), shlin2([([_A],[_A])]) ).

:- true pred is_built_in(_A)
   : ( mshare([[_A]]),
       shlin2([([_A],[])]) )
   => ( mshare([[_A]]),
        shlin2([([_A],[])]) ).

:- true pred is_built_in(_A)
   : ground([_A])
   => ground([_A]).

is_built_in(true).
is_built_in(_1=<_2).

:- true pred interpret_built_in(_A)
   : ( mshare([[_A]]),
       linear(_A), shlin2([([_A],[_A])]) )
   => ground([_A]).

:- true pred interpret_built_in(_A)
   : ( mshare([[_A]]),
       shlin2([([_A],[])]) )
   => ground([_A]).

:- true pred interpret_built_in(_A)
   : ground([_A])
   => ground([_A]).

interpret_built_in(true).
interpret_built_in(X=<Y) :-
    true((mshare([[X],[X,Y],[Y]]),shlin2([([X],[]),([X,Y],[]),([Y],[])]);mshare([[X],[Y]]),linear(X),linear(Y),shlin2([([X],[X]),([Y],[Y])]);ground([X,Y]))),
    X=<Y,
    true(ground([X,Y])).

:- true pred define(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_A), linear(_B), shlin2([([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[_A],[_A,_B],[_B]]),
        shlin2([([_A],[]),([_A,_B],[_A]),([_A,_B],[_B]),([_B],[])]) ).

:- true pred define(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_B), shlin2([([_A],[]),([_B],[_B])]) )
   => ( mshare([[_A],[_A,_B],[_B]]),
        shlin2([([_A],[]),([_A,_B],[]),([_B],[])]) ).

:- true pred define(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]), linear(_B), shlin2([([_B],[_B])]) )
   => ( mshare([[_B]]),
        ground([_A]), shlin2([([_B],[])]) ).

define(qsort,qsort([27,74,17,33,94,18,46,83,65,2,32,53,28,85,99,47,28,82,6,11,55,29,39,81,90,37,10,0,66,51,7,21,85,27,31,63,75,4,95,99,11,28,61,74,18,92,40,53,59,8],_1,[])).
define(qsort([X|L],R,R0),(partition(L,X,L1,L2),qsort(L2,R1,R0),qsort(L1,R,[X|R1]))).
define(qsort([],R,R),true).
define(partition([X|L],Y,[X|L1],L2),(X=<Y,!,partition(L,Y,L1,L2))).
define(partition([X|L],Y,L1,[X|L2]),partition(L,Y,L1,L2)).
define(partition([],_1,[],[]),true).


