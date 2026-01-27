:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(boyer,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(mshare([[Wff],[NewWff]])),
    wff(Wff),
    true((
        mshare([[NewWff]]),
        ground([Wff])
    )),
    rewrite(Wff,NewWff),
    true((
        mshare([[NewWff]]),
        ground([Wff])
    )),
    tautology(NewWff,[],[]),
    true((
        mshare([[NewWff]]),
        ground([Wff])
    )).

:- true pred wff(_A)
   : mshare([[_A]])
   => ground([_A]).

wff(implies(and(implies(X,Y),and(implies(Y,Z),and(implies(Z,U),implies(U,W)))),implies(X,W))) :-
    true(mshare([[X],[X,Y],[X,Y,Z],[X,Y,Z,U],[X,Y,Z,U,W],[X,Y,Z,W],[X,Y,U],[X,Y,U,W],[X,Y,W],[X,Z],[X,Z,U],[X,Z,U,W],[X,Z,W],[X,U],[X,U,W],[X,W],[Y],[Y,Z],[Y,Z,U],[Y,Z,U,W],[Y,Z,W],[Y,U],[Y,U,W],[Y,W],[Z],[Z,U],[Z,U,W],[Z,W],[U],[U,W],[W]])),
    X=f(myplus(myplus(a,b),myplus(c,zero))),
    true((
        mshare([[Y],[Y,Z],[Y,Z,U],[Y,Z,U,W],[Y,Z,W],[Y,U],[Y,U,W],[Y,W],[Z],[Z,U],[Z,U,W],[Z,W],[U],[U,W],[W]]),
        ground([X])
    )),
    Y=f(times(times(a,b),myplus(c,d))),
    true((
        mshare([[Z],[Z,U],[Z,U,W],[Z,W],[U],[U,W],[W]]),
        ground([X,Y])
    )),
    Z=f(reverse(append(append(a,b),[]))),
    true((
        mshare([[U],[U,W],[W]]),
        ground([X,Y,Z])
    )),
    U=equal(myplus(a,b),boyer_difference(x,y)),
    true((
        mshare([[W]]),
        ground([X,Y,Z,U])
    )),
    W=lessp(remainder(a,b),boyer_member(a,length(b))),
    true(ground([X,Y,Z,U,W])).

tautology(Wff) :-
    rewrite(Wff,NewWff),
    tautology(NewWff,[],[]).

:- true pred tautology(Wff,Tlist,Flist)
   : mshare([[Wff],[Wff,Tlist],[Wff,Tlist,Flist],[Wff,Flist],[Tlist],[Tlist,Flist],[Flist]])
   => mshare([[Wff],[Wff,Tlist],[Wff,Tlist,Flist],[Wff,Flist],[Tlist],[Tlist,Flist],[Flist]]).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Tlist=[_A|_B]),
       mshare([[Wff],[Wff,Flist],[Wff,Flist,_A],[Wff,Flist,_A,_B],[Wff,Flist,_B],[Wff,_A],[Wff,_A,_B],[Wff,_B],[Flist],[Flist,_A],[Flist,_A,_B],[Flist,_B],[_A],[_A,_B],[_B]]) )
   => mshare([[Wff],[Wff,Flist],[Wff,Flist,_A],[Wff,Flist,_A,_B],[Wff,Flist,_B],[Wff,_A],[Wff,_A,_B],[Wff,_B],[Flist],[Flist,_A],[Flist,_A,_B],[Flist,_B],[_A],[_A,_B],[_B]]).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Flist=[_A|_B]),
       mshare([[Wff],[Wff,Tlist],[Wff,Tlist,_A],[Wff,Tlist,_A,_B],[Wff,Tlist,_B],[Wff,_A],[Wff,_A,_B],[Wff,_B],[Tlist],[Tlist,_A],[Tlist,_A,_B],[Tlist,_B],[_A],[_A,_B],[_B]]) )
   => mshare([[Wff],[Wff,Tlist],[Wff,Tlist,_A],[Wff,Tlist,_A,_B],[Wff,Tlist,_B],[Wff,_A],[Wff,_A,_B],[Wff,_B],[Tlist],[Tlist,_A],[Tlist,_A,_B],[Tlist,_B],[_A],[_A,_B],[_B]]).

:- true pred tautology(Wff,Tlist,Flist)
   : ( mshare([[Wff],[Wff,Tlist],[Tlist]]),
       ground([Flist]) )
   => ( mshare([[Wff],[Wff,Tlist],[Tlist]]),
        ground([Flist]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Tlist=[_A|_B]),
       mshare([[Wff],[Wff,_A],[Wff,_A,_B],[Wff,_B],[_A],[_A,_B],[_B]]),
       ground([Flist]) )
   => ( mshare([[Wff],[Wff,_A],[Wff,_A,_B],[Wff,_B],[_A],[_A,_B],[_B]]),
        ground([Flist]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( mshare([[Wff],[Wff,Flist],[Flist]]),
       ground([Tlist]) )
   => ( mshare([[Wff],[Wff,Flist],[Flist]]),
        ground([Tlist]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Flist=[_A|_B]),
       mshare([[Wff],[Wff,_A],[Wff,_A,_B],[Wff,_B],[_A],[_A,_B],[_B]]),
       ground([Tlist]) )
   => ( mshare([[Wff],[Wff,_A],[Wff,_A,_B],[Wff,_B],[_A],[_A,_B],[_B]]),
        ground([Tlist]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( mshare([[Wff]]),
       ground([Tlist,Flist]) )
   => ( mshare([[Wff]]),
        ground([Tlist,Flist]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Tlist=[]), (Flist=[]),
       mshare([[Wff]]) )
   => mshare([[Wff]]).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Flist=[_A|_B]),
       mshare([[Wff],[Wff,_A],[_A]]),
       ground([Tlist,_B]) )
   => ( mshare([[Wff],[Wff,_A],[_A]]),
        ground([Tlist,_B]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Tlist=[_A|_B]),
       mshare([[Wff],[Wff,_A],[_A]]),
       ground([Flist,_B]) )
   => ( mshare([[Wff],[Wff,_A],[_A]]),
        ground([Flist,_B]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Tlist=[_A|_B]),
       mshare([[Wff],[Wff,Flist],[Wff,Flist,_A],[Wff,_A],[Flist],[Flist,_A],[_A]]),
       ground([_B]) )
   => ( mshare([[Wff],[Wff,Flist],[Wff,Flist,_A],[Wff,_A],[Flist],[Flist,_A],[_A]]),
        ground([_B]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Flist=[_A|_B]),
       mshare([[Wff],[Wff,Tlist],[Wff,Tlist,_A],[Wff,_A],[Tlist],[Tlist,_A],[_A]]),
       ground([_B]) )
   => ( mshare([[Wff],[Wff,Tlist],[Wff,Tlist,_A],[Wff,_A],[Tlist],[Tlist,_A],[_A]]),
        ground([_B]) ).

tautology(Wff,Tlist,Flist) :-
    true((mshare([[Wff]]),ground([Tlist,Flist]);mshare([[Wff],[Wff,Tlist],[Wff,Tlist,Flist],[Wff,Flist],[Tlist],[Tlist,Flist],[Flist]]);mshare([[Wff],[Wff,Tlist],[Tlist]]),ground([Flist]);mshare([[Wff],[Wff,Flist],[Flist]]),ground([Tlist]))),
    'tautology/3/1/$disj/1'(Wff,Tlist,Flist),
    !,
    true((mshare([[Wff]]),ground([Tlist,Flist]);mshare([[Wff],[Wff,Tlist],[Wff,Tlist,Flist],[Wff,Flist],[Tlist],[Tlist,Flist],[Flist]]);mshare([[Wff],[Wff,Tlist],[Tlist]]),ground([Flist]);mshare([[Wff],[Wff,Flist],[Flist]]),ground([Tlist]))).

:- true pred 'tautology/3/1/$disj/1'(Wff,Tlist,Flist)
   : ( mshare([[Wff]]),
       ground([Tlist,Flist]) )
   => ( mshare([[Wff]]),
        ground([Tlist,Flist]) ).

:- true pred 'tautology/3/1/$disj/1'(Wff,Tlist,Flist)
   : ( mshare([[Wff],[Wff,Flist],[Flist]]),
       ground([Tlist]) )
   => ( mshare([[Wff],[Wff,Flist],[Flist]]),
        ground([Tlist]) ).

:- true pred 'tautology/3/1/$disj/1'(Wff,Tlist,Flist)
   : mshare([[Wff],[Wff,Tlist],[Wff,Tlist,Flist],[Wff,Flist],[Tlist],[Tlist,Flist],[Flist]])
   => mshare([[Wff],[Wff,Tlist],[Wff,Tlist,Flist],[Wff,Flist],[Tlist],[Tlist,Flist],[Flist]]).

:- true pred 'tautology/3/1/$disj/1'(Wff,Tlist,Flist)
   : ( mshare([[Wff],[Wff,Tlist],[Tlist]]),
       ground([Flist]) )
   => ( mshare([[Wff],[Wff,Tlist],[Tlist]]),
        ground([Flist]) ).

'tautology/3/1/$disj/1'(Wff,Tlist,Flist) :-
    true((mshare([[Wff]]),ground([Tlist,Flist]);mshare([[Wff],[Wff,Tlist],[Wff,Tlist,Flist],[Wff,Flist],[Tlist],[Tlist,Flist],[Flist]]);mshare([[Wff],[Wff,Tlist],[Tlist]]),ground([Flist]);mshare([[Wff],[Wff,Flist],[Flist]]),ground([Tlist]))),
    truep(Wff,Tlist),
    !,
    true((mshare([[Wff,Tlist],[Wff,Tlist,Flist],[Tlist],[Tlist,Flist],[Flist]]);mshare([[Wff,Tlist],[Tlist]]),ground([Flist]);mshare([[Flist]]),ground([Wff,Tlist]);ground([Wff,Tlist,Flist]))),
    true,
    true((mshare([[Wff,Tlist],[Wff,Tlist,Flist],[Tlist],[Tlist,Flist],[Flist]]);mshare([[Wff,Tlist],[Tlist]]),ground([Flist]);mshare([[Flist]]),ground([Wff,Tlist]);ground([Wff,Tlist,Flist]))).
'tautology/3/1/$disj/1'(Wff,Tlist,Flist) :-
    true((mshare([[Wff]]),ground([Tlist,Flist]);mshare([[Wff],[Wff,Tlist],[Wff,Tlist,Flist],[Wff,Flist],[Tlist],[Tlist,Flist],[Flist]]);mshare([[Wff],[Wff,Tlist],[Tlist]]),ground([Flist]);mshare([[Wff],[Wff,Flist],[Flist]]),ground([Tlist]))),
    falsep(Wff,Flist),
    !,
    true((mshare([[Wff,Tlist,Flist],[Wff,Flist],[Tlist],[Tlist,Flist],[Flist]]);mshare([[Wff,Flist],[Flist]]),ground([Tlist]);mshare([[Tlist]]),ground([Wff,Flist]);ground([Wff,Tlist,Flist]))),
    fail,
    true(fails(_)).
'tautology/3/1/$disj/1'(Wff,Tlist,Flist) :-
    true((mshare([[Wff],[Wff,Tlist],[Wff,Tlist,Flist],[Wff,Flist],[Tlist],[Tlist,Flist],[Flist],[If],[Then],[Else]]);mshare([[Wff],[Wff,Tlist],[Tlist],[If],[Then],[Else]]),ground([Flist]);mshare([[Wff],[Wff,Flist],[Flist],[If],[Then],[Else]]),ground([Tlist]);mshare([[Wff],[If],[Then],[Else]]),ground([Tlist,Flist]))),
    Wff=if(If,Then,Else),
    !,
    true((mshare([[Wff,Tlist,Flist,If],[Wff,Tlist,Flist,If,Then],[Wff,Tlist,Flist,If,Then,Else],[Wff,Tlist,Flist,If,Else],[Wff,Tlist,Flist,Then],[Wff,Tlist,Flist,Then,Else],[Wff,Tlist,Flist,Else],[Wff,Tlist,If],[Wff,Tlist,If,Then],[Wff,Tlist,If,Then,Else],[Wff,Tlist,If,Else],[Wff,Tlist,Then],[Wff,Tlist,Then,Else],[Wff,Tlist,Else],[Wff,Flist,If],[Wff,Flist,If,Then],[Wff,Flist,If,Then,Else],[Wff,Flist,If,Else],[Wff,Flist,Then],[Wff,Flist,Then,Else],[Wff,Flist,Else],[Wff,If],[Wff,If,Then],[Wff,If,Then,Else],[Wff,If,Else],[Wff,Then],[Wff,Then,Else],[Wff,Else],[Tlist],[Tlist,Flist],[Flist]]);mshare([[Wff,Tlist,If],[Wff,Tlist,If,Then],[Wff,Tlist,If,Then,Else],[Wff,Tlist,If,Else],[Wff,Tlist,Then],[Wff,Tlist,Then,Else],[Wff,Tlist,Else],[Wff,If],[Wff,If,Then],[Wff,If,Then,Else],[Wff,If,Else],[Wff,Then],[Wff,Then,Else],[Wff,Else],[Tlist]]),ground([Flist]);mshare([[Wff,Flist,If],[Wff,Flist,If,Then],[Wff,Flist,If,Then,Else],[Wff,Flist,If,Else],[Wff,Flist,Then],[Wff,Flist,Then,Else],[Wff,Flist,Else],[Wff,If],[Wff,If,Then],[Wff,If,Then,Else],[Wff,If,Else],[Wff,Then],[Wff,Then,Else],[Wff,Else],[Flist]]),ground([Tlist]);mshare([[Wff,If],[Wff,If,Then],[Wff,If,Then,Else],[Wff,If,Else],[Wff,Then],[Wff,Then,Else],[Wff,Else]]),ground([Tlist,Flist]))),
    'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else),
    true((mshare([[Wff,Tlist,Flist,If],[Wff,Tlist,Flist,If,Then],[Wff,Tlist,Flist,If,Then,Else],[Wff,Tlist,Flist,If,Else],[Wff,Tlist,Flist,Then],[Wff,Tlist,Flist,Then,Else],[Wff,Tlist,Flist,Else],[Wff,Tlist,If],[Wff,Tlist,If,Then],[Wff,Tlist,If,Then,Else],[Wff,Tlist,If,Else],[Wff,Tlist,Then],[Wff,Tlist,Then,Else],[Wff,Tlist,Else],[Wff,Flist,If],[Wff,Flist,If,Then],[Wff,Flist,If,Then,Else],[Wff,Flist,If,Else],[Wff,Flist,Then],[Wff,Flist,Then,Else],[Wff,Flist,Else],[Wff,If],[Wff,If,Then],[Wff,If,Then,Else],[Wff,If,Else],[Wff,Then],[Wff,Then,Else],[Wff,Else],[Tlist],[Tlist,Flist],[Flist]]);mshare([[Wff,Tlist,If],[Wff,Tlist,If,Then],[Wff,Tlist,If,Then,Else],[Wff,Tlist,If,Else],[Wff,Tlist,Then],[Wff,Tlist,Then,Else],[Wff,Tlist,Else],[Wff,If],[Wff,If,Then],[Wff,If,Then,Else],[Wff,If,Else],[Wff,Then],[Wff,Then,Else],[Wff,Else],[Tlist]]),ground([Flist]);mshare([[Wff,Flist,If],[Wff,Flist,If,Then],[Wff,Flist,If,Then,Else],[Wff,Flist,If,Else],[Wff,Flist,Then],[Wff,Flist,Then,Else],[Wff,Flist,Else],[Wff,If],[Wff,If,Then],[Wff,If,Then,Else],[Wff,If,Else],[Wff,Then],[Wff,Then,Else],[Wff,Else],[Flist]]),ground([Tlist]);mshare([[Wff,If],[Wff,If,Then],[Wff,If,Then,Else],[Wff,If,Else],[Wff,Then],[Wff,Then,Else],[Wff,Else]]),ground([Tlist,Flist]))).

:- true pred 'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else)
   : mshare([[Tlist],[Tlist,Flist],[Tlist,Flist,If],[Tlist,Flist,If,Then],[Tlist,Flist,If,Then,Else],[Tlist,Flist,If,Else],[Tlist,Flist,Then],[Tlist,Flist,Then,Else],[Tlist,Flist,Else],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]])
   => mshare([[Tlist],[Tlist,Flist],[Tlist,Flist,If],[Tlist,Flist,If,Then],[Tlist,Flist,If,Then,Else],[Tlist,Flist,If,Else],[Tlist,Flist,Then],[Tlist,Flist,Then,Else],[Tlist,Flist,Else],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]).

:- true pred 'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else)
   : ( mshare([[Tlist],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),
       ground([Flist]) )
   => ( mshare([[Tlist],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),
        ground([Flist]) ).

:- true pred 'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else)
   : ( mshare([[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),
       ground([Tlist]) )
   => ( mshare([[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),
        ground([Tlist]) ).

:- true pred 'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else)
   : ( mshare([[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),
       ground([Tlist,Flist]) )
   => ( mshare([[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),
        ground([Tlist,Flist]) ).

'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else) :-
    true((mshare([[Tlist],[Tlist,Flist],[Tlist,Flist,If],[Tlist,Flist,If,Then],[Tlist,Flist,If,Then,Else],[Tlist,Flist,If,Else],[Tlist,Flist,Then],[Tlist,Flist,Then,Else],[Tlist,Flist,Else],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]);mshare([[Tlist],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Flist]);mshare([[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Tlist]);mshare([[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Tlist,Flist]))),
    truep(If,Tlist),
    !,
    true((mshare([[Tlist],[Tlist,Flist],[Tlist,Flist,If],[Tlist,Flist,If,Then],[Tlist,Flist,If,Then,Else],[Tlist,Flist,If,Else],[Tlist,Flist,Then],[Tlist,Flist,Then,Else],[Tlist,Flist,Else],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Flist],[Flist,Then],[Flist,Then,Else],[Flist,Else],[Then],[Then,Else],[Else]]);mshare([[Tlist],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Then],[Then,Else],[Else]]),ground([Flist]);mshare([[Flist],[Flist,Then],[Flist,Then,Else],[Flist,Else],[Then],[Then,Else],[Else]]),ground([Tlist,If]);mshare([[Then],[Then,Else],[Else]]),ground([Tlist,Flist,If]))),
    tautology(Then,Tlist,Flist),
    true((mshare([[Tlist],[Tlist,Flist],[Tlist,Flist,If],[Tlist,Flist,If,Then],[Tlist,Flist,If,Then,Else],[Tlist,Flist,If,Else],[Tlist,Flist,Then],[Tlist,Flist,Then,Else],[Tlist,Flist,Else],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Flist],[Flist,Then],[Flist,Then,Else],[Flist,Else],[Then],[Then,Else],[Else]]);mshare([[Tlist],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Then],[Then,Else],[Else]]),ground([Flist]);mshare([[Flist],[Flist,Then],[Flist,Then,Else],[Flist,Else],[Then],[Then,Else],[Else]]),ground([Tlist,If]);mshare([[Then],[Then,Else],[Else]]),ground([Tlist,Flist,If]))).
'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else) :-
    true((mshare([[Tlist],[Tlist,Flist],[Tlist,Flist,If],[Tlist,Flist,If,Then],[Tlist,Flist,If,Then,Else],[Tlist,Flist,If,Else],[Tlist,Flist,Then],[Tlist,Flist,Then,Else],[Tlist,Flist,Else],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]);mshare([[Tlist],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Flist]);mshare([[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Tlist]);mshare([[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Tlist,Flist]))),
    falsep(If,Flist),
    !,
    true((mshare([[Tlist],[Tlist,Flist],[Tlist,Flist,If],[Tlist,Flist,If,Then],[Tlist,Flist,If,Then,Else],[Tlist,Flist,If,Else],[Tlist,Flist,Then],[Tlist,Flist,Then,Else],[Tlist,Flist,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[Then],[Then,Else],[Else]]);mshare([[Tlist],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Then],[Then,Else],[Else]]),ground([Flist,If]);mshare([[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[Then],[Then,Else],[Else]]),ground([Tlist]);mshare([[Then],[Then,Else],[Else]]),ground([Tlist,Flist,If]))),
    tautology(Else,Tlist,Flist),
    true((mshare([[Tlist],[Tlist,Flist],[Tlist,Flist,If],[Tlist,Flist,If,Then],[Tlist,Flist,If,Then,Else],[Tlist,Flist,If,Else],[Tlist,Flist,Then],[Tlist,Flist,Then,Else],[Tlist,Flist,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[Then],[Then,Else],[Else]]);mshare([[Tlist],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Then],[Then,Else],[Else]]),ground([Flist,If]);mshare([[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[Then],[Then,Else],[Else]]),ground([Tlist]);mshare([[Then],[Then,Else],[Else]]),ground([Tlist,Flist,If]))).
'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else) :-
    true((mshare([[Tlist],[Tlist,Flist],[Tlist,Flist,If],[Tlist,Flist,If,Then],[Tlist,Flist,If,Then,Else],[Tlist,Flist,If,Else],[Tlist,Flist,Then],[Tlist,Flist,Then,Else],[Tlist,Flist,Else],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]);mshare([[Tlist],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Flist]);mshare([[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Tlist]);mshare([[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Tlist,Flist]))),
    tautology(Then,[If|Tlist],Flist),
    true((mshare([[Tlist],[Tlist,Flist],[Tlist,Flist,If],[Tlist,Flist,If,Then],[Tlist,Flist,If,Then,Else],[Tlist,Flist,If,Else],[Tlist,Flist,Then],[Tlist,Flist,Then,Else],[Tlist,Flist,Else],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]);mshare([[Tlist],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Flist]);mshare([[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Tlist]);mshare([[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Tlist,Flist]))),
    tautology(Else,Tlist,[If|Flist]),
    true((mshare([[Tlist],[Tlist,Flist],[Tlist,Flist,If],[Tlist,Flist,If,Then],[Tlist,Flist,If,Then,Else],[Tlist,Flist,If,Else],[Tlist,Flist,Then],[Tlist,Flist,Then,Else],[Tlist,Flist,Else],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]);mshare([[Tlist],[Tlist,If],[Tlist,If,Then],[Tlist,If,Then,Else],[Tlist,If,Else],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Flist]);mshare([[Flist],[Flist,If],[Flist,If,Then],[Flist,If,Then,Else],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Tlist]);mshare([[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Then,Else],[Else]]),ground([Tlist,Flist]))).

:- true pred rewrite(Atom,New)
   : mshare([[Atom],[New]])
   => mshare([[Atom],[New]]).

:- true pred rewrite(Atom,New)
   : ( mshare([[Atom]]),
       ground([New]) )
   => ( mshare([[Atom]]),
        ground([New]) ).

:- true pred rewrite(Atom,New)
   : ground([Atom,New])
   => ground([Atom,New]).

:- true pred rewrite(Atom,New)
   : ( mshare([[New]]),
       ground([Atom]) )
   => ( mshare([[New]]),
        ground([Atom]) ).

rewrite(Atom,Atom) :-
    true((mshare([[Atom]]);ground([Atom]))),
    atomic(Atom),
    !,
    true(ground([Atom])).
rewrite(Old,New) :-
    true((mshare([[Old],[New],[F],[N],[Mid]]);mshare([[Old],[F],[N],[Mid]]),ground([New]);mshare([[New],[F],[N],[Mid]]),ground([Old]);mshare([[F],[N],[Mid]]),ground([Old,New]))),
    functor(Old,F,N),
    true((mshare([[Old],[New],[Mid]]),ground([F,N]);mshare([[Old],[Mid]]),ground([New,F,N]);mshare([[New],[Mid]]),ground([Old,F,N]);mshare([[Mid]]),ground([Old,New,F,N]))),
    functor(Mid,F,N),
    true((mshare([[Old],[New],[Mid]]),ground([F,N]);mshare([[Old],[Mid]]),ground([New,F,N]);mshare([[New],[Mid]]),ground([Old,F,N]);mshare([[Mid]]),ground([Old,New,F,N]))),
    rewrite_args(N,Old,Mid),
    true((mshare([[Old],[New],[Mid]]),ground([F,N]);mshare([[Old],[Mid]]),ground([New,F,N]);mshare([[New],[Mid]]),ground([Old,F,N]);mshare([[Mid]]),ground([Old,New,F,N]))),
    'rewrite/2/2/$disj/1'(New,Mid),
    !,
    true((mshare([[Old],[New],[New,Mid],[Mid]]),ground([F,N]);mshare([[Old],[Mid]]),ground([New,F,N]);mshare([[New],[New,Mid],[Mid]]),ground([Old,F,N]);mshare([[Mid]]),ground([Old,New,F,N]))).

:- true pred 'rewrite/2/2/$disj/1'(New,Mid)
   : mshare([[New],[Mid]])
   => mshare([[New],[New,Mid],[Mid]]).

:- true pred 'rewrite/2/2/$disj/1'(New,Mid)
   : ( mshare([[Mid]]),
       ground([New]) )
   => ( mshare([[Mid]]),
        ground([New]) ).

'rewrite/2/2/$disj/1'(New,Mid) :-
    true((mshare([[New],[Mid],[Next]]);mshare([[Mid],[Next]]),ground([New]))),
    equal(Mid,Next),
    true((mshare([[New],[Mid],[Mid,Next]]);mshare([[Mid],[Mid,Next]]),ground([New]))),
    rewrite(Next,New),
    true((mshare([[New],[Mid],[Mid,Next]]);mshare([[Mid],[Mid,Next]]),ground([New]))).
'rewrite/2/2/$disj/1'(New,Mid) :-
    true((mshare([[New],[Mid]]);mshare([[Mid]]),ground([New]))),
    New=Mid,
    true((mshare([[New,Mid]]);ground([New,Mid]))).

:- true pred rewrite_args(N,_1,_2)
   : ground([N,_1,_2])
   => ground([N,_1,_2]).

:- true pred rewrite_args(N,_1,_2)
   : ( mshare([[_2]]),
       ground([N,_1]) )
   => ( mshare([[_2]]),
        ground([N,_1]) ).

:- true pred rewrite_args(N,_1,_2)
   : ( mshare([[_1],[_2]]),
       ground([N]) )
   => ( mshare([[_1],[_2]]),
        ground([N]) ).

rewrite_args(0,_1,_2) :-
    !,
    true((mshare([[_1],[_2]]);mshare([[_2]]),ground([_1]);ground([_1,_2]))).
rewrite_args(N,Old,Mid) :-
    true((mshare([[Old],[Mid],[OldArg],[MidArg],[N1]]),ground([N]);mshare([[Mid],[OldArg],[MidArg],[N1]]),ground([N,Old]);mshare([[OldArg],[MidArg],[N1]]),ground([N,Old,Mid]))),
    arg(N,Old,OldArg),
    true((mshare([[Old,OldArg],[Mid],[MidArg],[N1]]),ground([N]);mshare([[Mid],[MidArg],[N1]]),ground([N,Old,OldArg]);mshare([[MidArg],[N1]]),ground([N,Old,Mid,OldArg]))),
    arg(N,Mid,MidArg),
    true((mshare([[Old,OldArg],[Mid,MidArg],[N1]]),ground([N]);mshare([[Mid,MidArg],[N1]]),ground([N,Old,OldArg]);mshare([[N1]]),ground([N,Old,Mid,OldArg,MidArg]))),
    rewrite(OldArg,MidArg),
    true((mshare([[Old,OldArg],[Mid,MidArg],[N1]]),ground([N]);mshare([[Mid,MidArg],[N1]]),ground([N,Old,OldArg]);mshare([[N1]]),ground([N,Old,Mid,OldArg,MidArg]))),
    N1 is N-1,
    true((mshare([[Old,OldArg],[Mid,MidArg]]),ground([N,N1]);mshare([[Mid,MidArg]]),ground([N,Old,OldArg,N1]);ground([N,Old,Mid,OldArg,MidArg,N1]))),
    rewrite_args(N1,Old,Mid),
    true((mshare([[Old,OldArg],[Mid,MidArg]]),ground([N,N1]);mshare([[Mid,MidArg]]),ground([N,Old,OldArg,N1]);ground([N,Old,Mid,OldArg,MidArg,N1]))).

:- true pred truep(Wff,_1)
   : ( mshare([[Wff]]),
       ground([_1]) )
   => ground([Wff,_1]).

:- true pred truep(Wff,_1)
   : mshare([[Wff],[Wff,_1],[_1]])
   => mshare([[Wff,_1],[_1]]).

truep(t,_1) :-
    !,
    true((mshare([[_1]]);ground([_1]))).
truep(Wff,Tlist) :-
    true((mshare([[Wff]]),ground([Tlist]);mshare([[Wff],[Wff,Tlist],[Tlist]]))),
    boyer_member(Wff,Tlist),
    true((mshare([[Wff,Tlist],[Tlist]]);ground([Wff,Tlist]))).

:- true pred falsep(Wff,_1)
   : ( mshare([[Wff]]),
       ground([_1]) )
   => ground([Wff,_1]).

:- true pred falsep(Wff,_1)
   : mshare([[Wff],[Wff,_1],[_1]])
   => mshare([[Wff,_1],[_1]]).

falsep(f,_1) :-
    !,
    true((mshare([[_1]]);ground([_1]))).
falsep(Wff,Flist) :-
    true((mshare([[Wff]]),ground([Flist]);mshare([[Wff],[Wff,Flist],[Flist]]))),
    boyer_member(Wff,Flist),
    true((mshare([[Wff,Flist],[Flist]]);ground([Wff,Flist]))).

:- true pred boyer_member(X,_A)
   : mshare([[X],[X,_A],[_A]])
   => mshare([[X,_A],[_A]]).

:- true pred boyer_member(X,_A)
   : ( mshare([[X]]),
       ground([_A]) )
   => ground([X,_A]).

boyer_member(X,[X|_1]) :-
    !,
    true((mshare([[X],[X,_1],[_1]]);ground([X,_1]))).
boyer_member(X,[_1|T]) :-
    true((mshare([[X]]),ground([_1,T]);mshare([[X],[X,_1],[X,_1,T],[X,T],[_1],[_1,T],[T]]))),
    boyer_member(X,T),
    true((mshare([[X,_1,T],[X,T],[_1],[_1,T],[T]]);ground([X,_1,T]))).

:- true pred equal(_A,C)
   : mshare([[_A],[C]])
   => mshare([[_A],[_A,C]]).

equal(and(P,Q),if(P,if(Q,t,f),f)).
equal(append(append(X,Y),Z),append(X,append(Y,Z))).
equal(assignment(X,append(A,B)),if(assignedp(X,A),assignment(X,A),assignment(X,B))).
equal(assume_false(Var,Alist),cons(cons(Var,f),Alist)).
equal(assume_true(Var,Alist),cons(cons(Var,t),Alist)).
equal(boolean(X),or(equal(X,t),equal(X,f))).
equal(car(gopher(X)),if(listp(X),car(flatten(X)),zero)).
equal(compile(Form),reverse(codegen(optimize(Form),[]))).
equal(count_list(Z,sort_lp(X,Y)),myplus(count_list(Z,X),count_list(Z,Y))).
equal(countps_(L,Pred),countps_loop(L,Pred,zero)).
equal(boyer_difference(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    boyer_difference(A,B,C),
    true(mshare([[C,A],[C,A,B],[C,B],[A,B]])).
equal(divides(X,Y),zerop(remainder(Y,X))).
equal(dsort(X),sort2(X)).
equal(eqp(X,Y),equal(fix(X),fix(Y))).
equal(equal(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    eq(A,B,C),
    true(mshare([[C,A],[C,A,B],[C,B],[A],[A,B]])).
equal(even1(X),if(zerop(X),t,odd(decr(X)))).
equal(exec(append(X,Y),Pds,Envrn),exec(Y,exec(X,Pds,Envrn),Envrn)).
equal(exp(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    exp(A,B,C),
    true(mshare([[C,A],[C,A,B],[C,B]])).
equal(fact_(I),fact_loop(I,1)).
equal(falsify(X),falsify1(normalize(X),[])).
equal(fix(X),if(numberp(X),X,zero)).
equal(flatten(cdr(gopher(X))),if(listp(X),cdr(flatten(X)),cons(zero,[]))).
equal(gcd(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    gcd(A,B,C),
    true(mshare([[C,A],[C,A,B],[C,B]])).
equal(get(J,set(I,Val,Mem)),if(eqp(J,I),Val,get(J,Mem))).
equal(greatereqp(X,Y),not(lessp(X,Y))).
equal(greatereqpr(X,Y),not(lessp(X,Y))).
equal(greaterp(X,Y),lessp(Y,X)).
equal(if(if(A,B,C),D,E),if(A,if(B,D,E),if(C,D,E))).
equal(iff(X,Y),and(implies(X,Y),implies(Y,X))).
equal(implies(P,Q),if(P,if(Q,t,f),t)).
equal(last(append(A,B)),if(listp(B),last(B),if(listp(A),cons(car(last(A))),B))).
equal(length(A),B) :-
    true(mshare([[B],[A]])),
    mylength(A,B),
    true(mshare([[B,A],[A]])).
equal(lesseqp(X,Y),not(lessp(Y,X))).
equal(lessp(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    lessp(A,B,C),
    true(mshare([[C,A],[C,A,B],[C,B],[A],[A,B]])).
equal(listp(gopher(X)),listp(X)).
equal(mc_flatten(X,Y),append(flatten(X),Y)).
equal(meaning(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    meaning(A,B,C),
    true(mshare([[C,A],[C,A,B],[C,B]])).
equal(boyer_member(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    myboyer_member(A,B,C),
    true(mshare([[C,A],[C,A,B],[C,B]])).
equal(not(P),if(P,f,t)).
equal(my_nth(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    my_nth(A,B,C),
    true(mshare([[C,A],[C,A,B],[C,B],[B]])).
equal(numberp(greatest_factor(X,Y)),not(and(or(zerop(Y),equal(Y,1)),not(numberp(X))))).
equal(or(P,Q),if(P,t,if(Q,t,f),f)).
equal(myplus(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    myplus(A,B,C),
    true(mshare([[C,A],[C,A,B],[C,B],[A,B]])).
equal(power_eval(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    power_eval(A,B,C),
    true(mshare([[C,A],[C,A,B],[A,B]])).
equal(prime(X),and(not(zerop(X)),and(not(equal(X,add1(zero))),prime1(X,decr(X))))).
equal(prime_list(append(X,Y)),and(prime_list(X),prime_list(Y))).
equal(quotient(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    quotient(A,B,C),
    true(mshare([[C,A],[C,A,B]])).
equal(remainder(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    remainder(A,B,C),
    true((
        mshare([[A],[A,B]]),
        ground([C])
    )).
equal(reverse_(X),reverse_loop(X,[])).
equal(reverse(append(A,B)),append(reverse(B),reverse(A))).
equal(reverse_loop(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    reverse_loop(A,B,C),
    true(mshare([[C,A],[C,A,B],[C,B]])).
equal(samefringe(X,Y),equal(flatten(X),flatten(Y))).
equal(sigma(zero,I),quotient(times(I,add1(I)),2)).
equal(sort2(delete(X,L)),delete(X,sort2(L))).
equal(tautology_checker(X),tautologyp(normalize(X),[])).
equal(times(A,B),C) :-
    true(mshare([[C],[A],[A,B],[B]])),
    times(A,B,C),
    true(mshare([[C,A],[C,A,B],[C,B]])).
equal(times_list(append(X,Y)),times(times_list(X),times_list(Y))).
equal(value(normalize(X),A),value(X,A)).
equal(zerop(X),or(equal(X,zero),not(numberp(X)))).

:- true pred boyer_difference(X,A,_A)
   : mshare([[X],[X,A],[A],[_A]])
   => mshare([[X,A],[X,A,_A],[X,_A],[A,_A]]).

boyer_difference(X,X,zero) :-
    !,
    true(mshare([[X]])).
boyer_difference(myplus(X,Y),X,fix(Y)) :-
    !,
    true(mshare([[X],[X,Y],[Y]])).
boyer_difference(myplus(Y,X),X,fix(Y)) :-
    !,
    true(mshare([[X],[X,Y],[Y]])).
boyer_difference(myplus(X,Y),myplus(X,Z),boyer_difference(Y,Z)) :-
    !,
    true(mshare([[X],[X,Y],[X,Y,Z],[X,Z],[Y],[Y,Z],[Z]])).
boyer_difference(myplus(B,myplus(A,C)),A,myplus(B,C)) :-
    !,
    true(mshare([[A],[A,B],[A,B,C],[A,C],[B],[B,C],[C]])).
boyer_difference(add1(myplus(Y,Z)),Z,add1(Y)) :-
    !,
    true(mshare([[Z],[Z,Y],[Y]])).
boyer_difference(add1(add1(X)),2,fix(X)).

:- true pred eq(X,Z,_A)
   : mshare([[X],[X,Z],[Z],[_A]])
   => mshare([[X],[X,Z],[X,Z,_A],[X,_A],[Z,_A]]).

eq(myplus(A,B),zero,and(zerop(A),zerop(B))) :-
    !,
    true(mshare([[A],[A,B],[B]])).
eq(myplus(A,B),myplus(A,C),equal(fix(B),fix(C))) :-
    !,
    true(mshare([[A],[A,B],[A,B,C],[A,C],[B],[B,C],[C]])).
eq(zero,boyer_difference(X,Y),not(lessp(Y,X))) :-
    !,
    true(mshare([[X],[X,Y],[Y]])).
eq(X,boyer_difference(X,Y),and(numberp(X),and(or(equal(X,zero),zerop(Y))))) :-
    !,
    true(mshare([[X],[X,Y],[Y]])).
eq(times(X,Y),zero,or(zerop(X),zerop(Y))) :-
    !,
    true(mshare([[X],[X,Y],[Y]])).
eq(append(A,B),append(A,C),equal(B,C)) :-
    !,
    true(mshare([[A],[A,B],[A,B,C],[A,C],[B],[B,C],[C]])).
eq(flatten(X),cons(Y,[]),and(nlistp(X),equal(X,Y))) :-
    !,
    true(mshare([[X],[X,Y],[Y]])).
eq(greatest_factor(X,Y),zero,and(or(zerop(Y),equal(Y,1)),equal(X,zero))) :-
    !,
    true(mshare([[X],[X,Y],[Y]])).
eq(greatest_factor(X,_1),1,equal(X,1)) :-
    !,
    true(mshare([[X],[X,_1],[_1]])).
eq(Z,times(W,Z),and(numberp(Z),or(equal(Z,zero),equal(W,1)))) :-
    !,
    true(mshare([[Z],[Z,W],[W]])).
eq(X,times(X,Y),or(equal(X,zero),and(numberp(X),equal(Y,1)))) :-
    !,
    true(mshare([[X],[X,Y],[Y]])).
eq(times(A,B),1,and(not(equal(A,zero)),and(not(equal(B,zero)),and(numberp(A),and(numberp(B),and(equal(decr(A),zero),equal(decr(B),zero))))))) :-
    !,
    true(mshare([[A],[A,B],[B]])).
eq(boyer_difference(X,Y),boyer_difference(Z,Y),if(lessp(X,Y),not(lessp(Y,Z)),if(lessp(Z,Y),not(lessp(Y,X)),equal(fix(X),fix(Z))))) :-
    !,
    true(mshare([[X],[X,Y],[X,Y,Z],[X,Z],[Y],[Y,Z],[Z]])).
eq(lessp(X,Y),Z,if(lessp(X,Y),equal(t,Z),equal(f,Z))).

:- true pred exp(I,_A,_B)
   : mshare([[I],[I,_A],[_A],[_B]])
   => mshare([[I,_A,_B],[I,_B],[_A,_B]]).

exp(I,myplus(J,K),times(exp(I,J),exp(I,K))) :-
    !,
    true(mshare([[I],[I,J],[I,J,K],[I,K],[J],[J,K],[K]])).
exp(I,times(J,K),exp(exp(I,J),K)).

:- true pred gcd(X,Y,_A)
   : mshare([[X],[X,Y],[Y],[_A]])
   => mshare([[X,Y,_A],[X,_A],[Y,_A]]).

gcd(X,Y,gcd(Y,X)) :-
    !,
    true(mshare([[X],[X,Y],[Y]])).
gcd(times(X,Z),times(Y,Z),times(Z,gcd(X,Y))).

:- true pred mylength(_A,_B)
   : mshare([[_A],[_B]])
   => mshare([[_A],[_A,_B]]).

mylength(reverse(X),length(X)).
mylength(cons(_1,cons(_2,cons(_3,cons(_4,cons(_5,cons(_6,X7)))))),myplus(6,length(X7))).

:- true pred lessp(_A,Y,_B)
   : mshare([[_A],[_A,Y],[Y],[_B]])
   => mshare([[_A],[_A,Y],[_A,Y,_B],[_A,_B],[Y,_B]]).

lessp(remainder(_1,Y),Y,not(zerop(Y))) :-
    !,
    true(mshare([[Y],[Y,_1],[_1]])).
lessp(quotient(I,J),I,and(not(zerop(I)),or(zerop(J),not(equal(J,1))))) :-
    !,
    true(mshare([[I],[I,J],[J]])).
lessp(remainder(X,Y),X,and(not(zerop(Y)),and(not(zerop(X)),not(lessp(X,Y))))) :-
    !,
    true(mshare([[X],[X,Y],[Y]])).
lessp(myplus(X,Y),myplus(X,Z),lessp(Y,Z)) :-
    !,
    true(mshare([[X],[X,Y],[X,Y,Z],[X,Z],[Y],[Y,Z],[Z]])).
lessp(times(X,Z),times(Y,Z),and(not(zerop(Z)),lessp(X,Y))) :-
    !,
    true(mshare([[X],[X,Z],[X,Z,Y],[X,Y],[Z],[Z,Y],[Y]])).
lessp(Y,myplus(X,Y),not(zerop(X))) :-
    !,
    true(mshare([[Y],[Y,X],[X]])).
lessp(length(delete(X,L)),length(L),boyer_member(X,L)).

:- true pred meaning(_A,A,_B)
   : mshare([[_A],[_A,A],[A],[_B]])
   => mshare([[_A,A,_B],[_A,_B],[A,_B]]).

meaning(plus_tree(append(X,Y)),A,myplus(meaning(plus_tree(X),A),meaning(plus_tree(Y),A))) :-
    !,
    true(mshare([[A],[A,X],[A,X,Y],[A,Y],[X],[X,Y],[Y]])).
meaning(plus_tree(plus_fringe(X)),A,fix(meaning(X,A))) :-
    !,
    true(mshare([[A],[A,X],[X]])).
meaning(plus_tree(delete(X,Y)),A,if(boyer_member(X,Y),boyer_difference(meaning(plus_tree(Y),A),meaning(X,A)),meaning(plus_tree(Y),A))).

:- true pred myboyer_member(X,_A,_B)
   : mshare([[X],[X,_A],[_A],[_B]])
   => mshare([[X,_A,_B],[X,_B],[_A,_B]]).

myboyer_member(X,append(A,B),or(boyer_member(X,A),boyer_member(X,B))) :-
    !,
    true(mshare([[X],[X,A],[X,A,B],[X,B],[A],[A,B],[B]])).
myboyer_member(X,reverse(Y),boyer_member(X,Y)) :-
    !,
    true(mshare([[X],[X,Y],[Y]])).
myboyer_member(A,intersect(B,C),and(boyer_member(A,B),boyer_member(A,C))).

:- true pred my_nth(_A,_1,_B)
   : mshare([[_A],[_A,_1],[_1],[_B]])
   => mshare([[_A,_1,_B],[_A,_B],[_1],[_1,_B]]).

my_nth(zero,_1,zero).
my_nth([],I,if(zerop(I),[],zero)).
my_nth(append(A,B),I,append(my_nth(A,I),my_nth(B,boyer_difference(I,length(A))))).

:- true pred myplus(X,Z,_A)
   : mshare([[X],[X,Z],[Z],[_A]])
   => mshare([[X,Z],[X,Z,_A],[X,_A],[Z,_A]]).

myplus(myplus(X,Y),Z,myplus(X,myplus(Y,Z))) :-
    !,
    true(mshare([[Z],[Z,X],[Z,X,Y],[Z,Y],[X],[X,Y],[Y]])).
myplus(remainder(X,Y),times(Y,quotient(X,Y)),fix(X)) :-
    !,
    true(mshare([[X],[X,Y],[Y]])).
myplus(X,add1(Y),if(numberp(Y),add1(myplus(X,Y)),add1(X))).

:- true pred power_eval(_A,Base,_B)
   : mshare([[_A],[_A,Base],[Base],[_B]])
   => mshare([[_A,Base],[_A,Base,_B],[_A,_B]]).

power_eval(big_plus1(L,I,Base),Base,myplus(power_eval(L,Base),I)) :-
    !,
    true(mshare([[Base],[Base,L],[Base,L,I],[Base,I],[L],[L,I],[I]])).
power_eval(power_rep(I,Base),Base,fix(I)) :-
    !,
    true(mshare([[Base],[Base,I],[I]])).
power_eval(big_plus(X,Y,I,Base),Base,myplus(I,myplus(power_eval(X,Base),power_eval(Y,Base)))) :-
    !,
    true(mshare([[Base],[Base,X],[Base,X,Y],[Base,X,Y,I],[Base,X,I],[Base,Y],[Base,Y,I],[Base,I],[X],[X,Y],[X,Y,I],[X,I],[Y],[Y,I],[I]])).
power_eval(big_plus(power_rep(I,Base),power_rep(J,Base),zero,Base),Base,myplus(I,J)).

:- true pred quotient(_A,Y,_B)
   : mshare([[_A],[_A,Y],[Y],[_B]])
   => mshare([[_A,Y,_B],[_A,_B]]).

quotient(myplus(X,myplus(X,Y)),2,myplus(X,quotient(Y,2))).
quotient(times(Y,X),Y,if(zerop(Y),zero,fix(X))).

:- true pred remainder(_1,X,_A)
   : mshare([[_1],[_1,X],[X],[_A]])
   => ( mshare([[_1],[_1,X]]),
        ground([_A]) ).

remainder(_1,1,zero) :-
    !,
    true(mshare([[_1]])).
remainder(X,X,zero) :-
    !,
    true(mshare([[X]])).
remainder(times(_1,Z),Z,zero) :-
    !,
    true(mshare([[Z],[Z,_1],[_1]])).
remainder(times(Y,_1),Y,zero).

:- true pred reverse_loop(X,Y,_A)
   : mshare([[X],[X,Y],[Y],[_A]])
   => mshare([[X,Y,_A],[X,_A],[Y,_A]]).

reverse_loop(X,Y,append(reverse(X),Y)) :-
    !,
    true(mshare([[X],[X,Y],[Y]])).
reverse_loop(X,[],reverse(X)).

:- true pred times(X,Z,_A)
   : mshare([[X],[X,Z],[Z],[_A]])
   => mshare([[X,Z,_A],[X,_A],[Z,_A]]).

times(X,myplus(Y,Z),myplus(times(X,Y),times(X,Z))) :-
    !,
    true(mshare([[X],[X,Y],[X,Y,Z],[X,Z],[Y],[Y,Z],[Z]])).
times(times(X,Y),Z,times(X,times(Y,Z))) :-
    !,
    true(mshare([[Z],[Z,X],[Z,X,Y],[Z,Y],[X],[X,Y],[Y]])).
times(X,boyer_difference(C,W),boyer_difference(times(C,X),times(W,X))) :-
    !,
    true(mshare([[X],[X,C],[X,C,W],[X,W],[C],[C,W],[W]])).
times(X,add1(Y),if(numberp(Y),myplus(X,times(X,Y)),fix(X))).


