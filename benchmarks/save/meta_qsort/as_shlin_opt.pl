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
   : mshare([[Goal]])
   => mshare([[Goal]]).

:- true pred interpret(Goal)
   : (Goal=qsort).

interpret(Goal) :-
    true((mshare([[Goal],[Rest]]),linear(Rest);mshare([[Rest]]),ground([Goal]),linear(Rest))),
    interpret(Goal,Rest),
    true((mshare([[Goal],[Goal,Rest],[Rest]]);mshare([[Rest]]),ground([Goal]))),
    'interpret/1/1/$disj/1'(Rest),
    true((mshare([[Goal],[Goal,Rest],[Rest]]);mshare([[Rest]]),ground([Goal]))).

:- true pred 'interpret/1/1/$disj/1'(Rest)
   : mshare([[Rest]])
   => mshare([[Rest]]).

'interpret/1/1/$disj/1'(Rest) :-
    true(mshare([[Rest]])),
    nonvar(Rest),
    !,
    true(mshare([[Rest]])),
    interpret(Rest),
    true(mshare([[Rest]])).
'interpret/1/1/$disj/1'(Rest).

:- true pred interpret(G,_1)
   : ( mshare([[G],[_1]]),
       linear(_1) )
   => mshare([[G],[G,_1],[_1]]).

:- true pred interpret(G,_1)
   : ( mshare([[_1]]),
       ground([G]), linear(_1) )
   => ( mshare([[_1]]),
        ground([G]) ).

interpret(G,_1) :-
    true((mshare([[G],[_1]]),linear(_1);mshare([[_1]]),ground([G]),linear(_1))),
    var(G),
    !,
    true((fails(_);mshare([[G],[_1]]),linear(G),linear(_1))),
    fail,
    true(fails(_)).
interpret((A,B),Rest) :-
    !,
    true((mshare([[Rest],[A],[A,B],[B],[Rest0]]),linear(Rest),linear(Rest0);mshare([[Rest],[Rest0]]),ground([A,B]),linear(Rest),linear(Rest0))),
    interpret(A,Rest0),
    true((mshare([[Rest],[A],[A,B],[A,B,Rest0],[A,Rest0],[B],[Rest0]]),linear(Rest);mshare([[Rest],[Rest0]]),ground([A,B]),linear(Rest))),
    'interpret/2/2/$disj/1'(Rest,B,Rest0),
    true((mshare([[Rest],[Rest,A,B],[Rest,A,B,Rest0],[Rest,A,Rest0],[Rest,B],[Rest,B,Rest0],[Rest,Rest0],[A],[A,B],[A,B,Rest0],[A,Rest0],[B],[B,Rest0],[Rest0]]);mshare([[Rest],[Rest,Rest0],[Rest0]]),ground([A,B]))).
interpret((A;B),Rest) :-
    !,
    true((mshare([[Rest]]),ground([A,B]),linear(Rest);mshare([[Rest],[A],[A,B],[B]]),linear(Rest))),
    interpret_disjunction(A,B,Rest),
    true((mshare([[Rest]]),ground([A,B]);mshare([[Rest],[Rest,A],[Rest,A,B],[Rest,B],[A],[A,B],[B]]))).
interpret((A->B),Rest) :-
    !,
    true((mshare([[Rest]]),ground([A,B]),linear(Rest);mshare([[Rest],[A],[A,B],[B]]),linear(Rest))),
    interpret_disjunction((A->B),fail,Rest),
    true((mshare([[Rest]]),ground([A,B]);mshare([[Rest],[Rest,A],[Rest,A,B],[Rest,B],[A],[A,B],[B]]))).
interpret(\+A,Rest) :-
    !,
    true((mshare([[Rest]]),ground([A]),linear(Rest);mshare([[Rest],[A]]),linear(Rest))),
    interpret_disjunction((A->fail),true,Rest),
    true((mshare([[Rest]]),ground([A]);mshare([[Rest],[Rest,A],[A]]))).
interpret(!,true) :-
    !,
    true(true).
interpret(G,_1) :-
    true((mshare([[G],[_1]]),linear(_1);mshare([[_1]]),ground([G]),linear(_1))),
    number(G),
    !,
    true((
        mshare([[_1]]),
        ground([G]),
        linear(_1)
    )),
    fail,
    true(fails(_)).
interpret(G,_1) :-
    true((mshare([[G],[_1]]),linear(_1);mshare([[_1]]),ground([G]),linear(_1))),
    is_built_in(G),
    !,
    true((mshare([[G],[_1]]),linear(_1);mshare([[_1]]),ground([G]),linear(_1))),
    interpret_built_in(G),
    true((
        mshare([[_1]]),
        ground([G]),
        linear(_1)
    )).
interpret(G,_1) :-
    true((mshare([[G],[_1],[Body]]),linear(_1),linear(Body);mshare([[_1],[Body]]),ground([G]),linear(_1),linear(Body))),
    define(G,Body),
    true((mshare([[G],[G,Body],[_1],[Body]]),linear(_1);mshare([[_1],[Body]]),ground([G]),linear(_1))),
    interpret(Body),
    true((mshare([[G],[G,Body],[_1],[Body]]),linear(_1);mshare([[_1],[Body]]),ground([G]),linear(_1))).

:- true pred 'interpret/2/2/$disj/1'(Rest,B,Rest0)
   : ( mshare([[Rest],[Rest0]]),
       ground([B]), linear(Rest) )
   => ( mshare([[Rest],[Rest,Rest0],[Rest0]]),
        ground([B]) ).

:- true pred 'interpret/2/2/$disj/1'(Rest,B,Rest0)
   : ( mshare([[Rest],[B],[Rest0]]),
       linear(Rest) )
   => mshare([[Rest],[Rest,B],[Rest,Rest0],[Rest0]]).

:- true pred 'interpret/2/2/$disj/1'(Rest,B,Rest0)
   : ( mshare([[Rest],[B],[B,Rest0],[Rest0]]),
       linear(Rest) )
   => mshare([[Rest],[Rest,B],[Rest,B,Rest0],[Rest,Rest0],[B],[B,Rest0],[Rest0]]).

'interpret/2/2/$disj/1'(Rest,B,Rest0) :-
    true((mshare([[Rest],[B],[B,Rest0],[Rest0]]),linear(Rest);mshare([[Rest],[B],[Rest0]]),linear(Rest);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest))),
    nonvar(Rest0),
    !,
    true((mshare([[Rest],[B],[B,Rest0],[Rest0]]),linear(Rest);mshare([[Rest],[B],[Rest0]]),linear(Rest);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest))),
    Rest=(Rest0,B),
    true((mshare([[Rest,B],[Rest,B,Rest0],[Rest,Rest0]]);mshare([[Rest,B],[Rest,Rest0]]);mshare([[Rest,Rest0]]),ground([B]))).
'interpret/2/2/$disj/1'(Rest,B,Rest0) :-
    true((mshare([[Rest],[B],[B,Rest0],[Rest0]]),linear(Rest);mshare([[Rest],[B],[Rest0]]),linear(Rest);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest))),
    interpret(B,Rest),
    true((mshare([[Rest],[Rest,B],[Rest,B,Rest0],[B],[B,Rest0],[Rest0]]);mshare([[Rest],[Rest0]]),ground([B]))).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( mshare([[Rest]]),
       ground([A,_1]), linear(Rest) )
   => ( mshare([[Rest]]),
        ground([A,_1]) ).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( (A=(_A->_B)), (_1=fail),
       mshare([[Rest]]),
       ground([_A,_B]), linear(Rest) )
   => ( mshare([[Rest]]),
        ground([_A,_B]) ).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( (A=(_A->fail)), (_1=true),
       mshare([[Rest]]),
       ground([_A]), linear(Rest) )
   => ( mshare([[Rest]]),
        ground([_A]) ).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( (A=(_A->_B)), (_1=fail),
       mshare([[Rest],[_A],[_A,_B],[_B]]),
       linear(Rest) )
   => mshare([[Rest],[Rest,_A],[Rest,_A,_B],[Rest,_B],[_A],[_A,_B],[_B]]).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( (A=(_A->fail)), (_1=true),
       mshare([[Rest],[_A]]),
       linear(Rest) )
   => mshare([[Rest],[Rest,_A],[_A]]).

:- true pred interpret_disjunction(A,_1,Rest)
   : ( mshare([[A],[A,_1],[_1],[Rest]]),
       linear(Rest) )
   => mshare([[A],[A,_1],[A,_1,Rest],[A,Rest],[_1],[_1,Rest],[Rest]]).

interpret_disjunction((A->B),_1,Rest) :-
    true((mshare([[_1],[_1,A],[_1,A,B],[_1,B],[Rest],[A],[A,B],[B],[Rest0]]),linear(Rest),linear(Rest0);mshare([[Rest],[A],[A,B],[B],[Rest0]]),ground([_1]),linear(Rest),linear(Rest0);mshare([[Rest],[A],[Rest0]]),ground([_1,B]),linear(Rest),linear(Rest0);mshare([[Rest],[Rest0]]),ground([_1,A,B]),linear(Rest),linear(Rest0))),
    interpret(A,Rest0),
    !,
    true((mshare([[_1],[_1,A],[_1,A,B],[_1,A,B,Rest0],[_1,A,Rest0],[_1,B],[Rest],[A],[A,B],[A,B,Rest0],[A,Rest0],[B],[Rest0]]),linear(Rest);mshare([[Rest],[A],[A,B],[A,B,Rest0],[A,Rest0],[B],[Rest0]]),ground([_1]),linear(Rest);mshare([[Rest],[A],[A,Rest0],[Rest0]]),ground([_1,B]),linear(Rest);mshare([[Rest],[Rest0]]),ground([_1,A,B]),linear(Rest))),
    'interpret_disjunction/3/1/$disj/1'(Rest,B,Rest0),
    true((mshare([[_1],[_1,Rest,A,B],[_1,Rest,A,B,Rest0],[_1,Rest,A,Rest0],[_1,Rest,B],[_1,Rest,B,Rest0],[_1,A],[_1,A,B],[_1,A,B,Rest0],[_1,A,Rest0],[_1,B],[_1,B,Rest0],[Rest],[Rest,A,B],[Rest,A,B,Rest0],[Rest,A,Rest0],[Rest,B],[Rest,B,Rest0],[Rest,Rest0],[A],[A,B],[A,B,Rest0],[A,Rest0],[B],[B,Rest0],[Rest0]]);mshare([[Rest],[Rest,A,B],[Rest,A,B,Rest0],[Rest,A,Rest0],[Rest,B],[Rest,B,Rest0],[Rest,Rest0],[A],[A,B],[A,B,Rest0],[A,Rest0],[B],[B,Rest0],[Rest0]]),ground([_1]);mshare([[Rest],[Rest,A,Rest0],[Rest,Rest0],[A],[A,Rest0],[Rest0]]),ground([_1,B]);mshare([[Rest],[Rest,Rest0],[Rest0]]),ground([_1,A,B]))).
interpret_disjunction((_1->_2),C,Rest) :-
    !,
    true((mshare([[C],[C,_1],[C,_1,_2],[C,_2],[Rest],[_1],[_1,_2],[_2]]),linear(Rest);mshare([[Rest]]),ground([C,_1,_2]),linear(Rest);mshare([[Rest],[_1]]),ground([C,_2]),linear(Rest);mshare([[Rest],[_1],[_1,_2],[_2]]),ground([C]),linear(Rest))),
    interpret(C,Rest),
    true((mshare([[C],[C,Rest],[C,Rest,_1],[C,Rest,_1,_2],[C,Rest,_2],[C,_1],[C,_1,_2],[C,_2],[Rest],[_1],[_1,_2],[_2]]);mshare([[Rest]]),ground([C,_1,_2]);mshare([[Rest],[_1]]),ground([C,_2]);mshare([[Rest],[_1],[_1,_2],[_2]]),ground([C]))).
interpret_disjunction(A,_1,Rest) :-
    true((mshare([[A],[A,_1],[_1],[Rest]]),linear(Rest);mshare([[A],[Rest]]),ground([_1]),linear(Rest);mshare([[Rest]]),ground([A,_1]),linear(Rest))),
    interpret(A,Rest),
    true((mshare([[A],[A,_1],[A,_1,Rest],[A,Rest],[_1],[Rest]]);mshare([[A],[A,Rest],[Rest]]),ground([_1]);mshare([[Rest]]),ground([A,_1]))).
interpret_disjunction(_1,B,Rest) :-
    true((mshare([[_1],[_1,B],[B],[Rest]]),linear(Rest);mshare([[_1],[Rest]]),ground([B]),linear(Rest);mshare([[Rest]]),ground([_1,B]),linear(Rest))),
    interpret(B,Rest),
    true((mshare([[_1],[_1,B],[_1,B,Rest],[B],[B,Rest],[Rest]]);mshare([[_1],[Rest]]),ground([B]);mshare([[Rest]]),ground([_1,B]))).

:- true pred 'interpret_disjunction/3/1/$disj/1'(Rest,B,Rest0)
   : ( mshare([[Rest],[B],[B,Rest0],[Rest0]]),
       linear(Rest) )
   => mshare([[Rest],[Rest,B],[Rest,B,Rest0],[Rest,Rest0],[B],[B,Rest0],[Rest0]]).

:- true pred 'interpret_disjunction/3/1/$disj/1'(Rest,B,Rest0)
   : ( mshare([[Rest],[Rest0]]),
       ground([B]), linear(Rest) )
   => ( mshare([[Rest],[Rest,Rest0],[Rest0]]),
        ground([B]) ).

'interpret_disjunction/3/1/$disj/1'(Rest,B,Rest0) :-
    true((mshare([[Rest],[B],[B,Rest0],[Rest0]]),linear(Rest);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest))),
    nonvar(Rest0),
    !,
    true((mshare([[Rest],[B],[B,Rest0],[Rest0]]),linear(Rest);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest))),
    Rest=(Rest0->B),
    true((mshare([[Rest,B],[Rest,B,Rest0],[Rest,Rest0]]);mshare([[Rest,Rest0]]),ground([B]))).
'interpret_disjunction/3/1/$disj/1'(Rest,B,Rest0) :-
    true((mshare([[Rest],[B],[B,Rest0],[Rest0]]),linear(Rest);mshare([[Rest],[Rest0]]),ground([B]),linear(Rest))),
    interpret(B,Rest),
    true((mshare([[Rest],[Rest,B],[Rest,B,Rest0],[B],[B,Rest0],[Rest0]]);mshare([[Rest],[Rest0]]),ground([B]))).

:- true pred is_built_in(_A)
   : mshare([[_A]])
   => mshare([[_A]]).

:- true pred is_built_in(_A)
   : ground([_A])
   => ground([_A]).

is_built_in(true).
is_built_in(_1=<_2).

:- true pred interpret_built_in(_A)
   : mshare([[_A]])
   => ground([_A]).

:- true pred interpret_built_in(_A)
   : ground([_A])
   => ground([_A]).

interpret_built_in(true).
interpret_built_in(X=<Y) :-
    true((mshare([[X],[X,Y],[Y]]);ground([X,Y]))),
    X=<Y,
    true(ground([X,Y])).

:- true pred define(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_B) )
   => mshare([[_A],[_A,_B],[_B]]).

:- true pred define(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]), linear(_B) )
   => ( mshare([[_B]]),
        ground([_A]) ).

define(qsort,qsort([27,74,17,33,94,18,46,83,65,2,32,53,28,85,99,47,28,82,6,11,55,29,39,81,90,37,10,0,66,51,7,21,85,27,31,63,75,4,95,99,11,28,61,74,18,92,40,53,59,8],_1,[])).
define(qsort([X|L],R,R0),(partition(L,X,L1,L2),qsort(L2,R1,R0),qsort(L1,R,[X|R1]))).
define(qsort([],R,R),true).
define(partition([X|L],Y,[X|L1],L2),(X=<Y,!,partition(L,Y,L1,L2))).
define(partition([X|L],Y,L1,[X|L2]),partition(L,Y,L1,L2)).
define(partition([],_1,[],[]),true).


