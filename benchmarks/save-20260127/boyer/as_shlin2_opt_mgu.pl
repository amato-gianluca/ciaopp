:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(boyer,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true((
        mshare([[Wff],[NewWff]]),
        linear(Wff),
        linear(NewWff),
        shlin2([([Wff],[Wff]),([NewWff],[NewWff])])
    )),
    wff(Wff),
    true((
        mshare([[NewWff]]),
        ground([Wff]),
        linear(NewWff),
        shlin2([([NewWff],[NewWff])])
    )),
    rewrite(Wff,NewWff),
    true((
        mshare([[NewWff]]),
        ground([Wff]),
        linear(NewWff),
        shlin2([([NewWff],[NewWff])])
    )),
    tautology(NewWff,[],[]),
    true((
        mshare([[NewWff]]),
        ground([Wff]),
        shlin2([([NewWff],[])])
    )).

:- true pred wff(_A)
   : ( mshare([[_A]]),
       linear(_A), shlin2([([_A],[_A])]) )
   => ground([_A]).

wff(implies(and(implies(X,Y),and(implies(Y,Z),and(implies(Z,U),implies(U,W)))),implies(X,W))) :-
    true((
        mshare([[X],[Y],[Z],[U],[W]]),
        linear(X),
        linear(Y),
        linear(Z),
        linear(U),
        linear(W),
        shlin2([([X],[X]),([Y],[Y]),([Z],[Z]),([U],[U]),([W],[W])])
    )),
    X=f(myplus(myplus(a,b),myplus(c,zero))),
    true((
        mshare([[Y],[Z],[U],[W]]),
        ground([X]),
        linear(Y),
        linear(Z),
        linear(U),
        linear(W),
        shlin2([([Y],[Y]),([Z],[Z]),([U],[U]),([W],[W])])
    )),
    Y=f(times(times(a,b),myplus(c,d))),
    true((
        mshare([[Z],[U],[W]]),
        ground([X,Y]),
        linear(Z),
        linear(U),
        linear(W),
        shlin2([([Z],[Z]),([U],[U]),([W],[W])])
    )),
    Z=f(reverse(append(append(a,b),[]))),
    true((
        mshare([[U],[W]]),
        ground([X,Y,Z]),
        linear(U),
        linear(W),
        shlin2([([U],[U]),([W],[W])])
    )),
    U=equal(myplus(a,b),boyer_difference(x,y)),
    true((
        mshare([[W]]),
        ground([X,Y,Z,U]),
        linear(W),
        shlin2([([W],[W])])
    )),
    W=lessp(remainder(a,b),boyer_member(a,length(b))),
    true(ground([X,Y,Z,U,W])).

tautology(Wff) :-
    rewrite(Wff,NewWff),
    tautology(NewWff,[],[]).

:- true pred tautology(Wff,Tlist,Flist)
   : ( mshare([[Wff],[Tlist],[Flist]]),
       linear(Wff), linear(Tlist), linear(Flist), shlin2([([Wff],[Wff]),([Tlist],[Tlist]),([Flist],[Flist])]) )
   => ( mshare([[Wff],[Wff,Tlist],[Wff,Flist],[Tlist],[Flist]]),
        linear(Tlist), linear(Flist), shlin2([([Wff],[]),([Wff,Tlist],[Tlist]),([Wff,Flist],[Flist]),([Tlist],[Tlist]),([Flist],[Flist])]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Tlist=[_A|_B]),
       mshare([[Wff],[Flist],[_A],[_B]]),
       linear(Wff), linear(Flist), linear(_A), linear(_B), shlin2([([Wff],[Wff]),([Flist],[Flist]),([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[Wff],[Wff,Flist],[Wff,_A],[Wff,_B],[Flist],[_A],[_B]]),
        linear(Flist), linear(_A), linear(_B), shlin2([([Wff],[]),([Wff,Flist],[Flist]),([Wff,_A],[_A]),([Wff,_B],[_B]),([Flist],[Flist]),([_A],[_A]),([_B],[_B])]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Flist=[_A|_B]),
       mshare([[Wff],[Tlist],[_A],[_B]]),
       linear(Wff), linear(Tlist), linear(_A), linear(_B), shlin2([([Wff],[Wff]),([Tlist],[Tlist]),([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[Wff],[Wff,Tlist],[Wff,_A],[Wff,_B],[Tlist],[_A],[_B]]),
        linear(Tlist), linear(_A), linear(_B), shlin2([([Wff],[]),([Wff,Tlist],[Tlist]),([Wff,_A],[_A]),([Wff,_B],[_B]),([Tlist],[Tlist]),([_A],[_A]),([_B],[_B])]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( mshare([[Wff],[Tlist]]),
       ground([Flist]), linear(Wff), linear(Tlist), shlin2([([Wff],[Wff]),([Tlist],[Tlist])]) )
   => ( mshare([[Wff],[Wff,Tlist],[Tlist]]),
        ground([Flist]), linear(Tlist), shlin2([([Wff],[]),([Wff,Tlist],[Tlist]),([Tlist],[Tlist])]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Tlist=[_A|_B]),
       mshare([[Wff],[_A],[_B]]),
       ground([Flist]), linear(Wff), linear(_A), linear(_B), shlin2([([Wff],[Wff]),([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[Wff],[Wff,_A],[Wff,_B],[_A],[_B]]),
        ground([Flist]), linear(_A), linear(_B), shlin2([([Wff],[]),([Wff,_A],[_A]),([Wff,_B],[_B]),([_A],[_A]),([_B],[_B])]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( mshare([[Wff],[Flist]]),
       ground([Tlist]), linear(Wff), linear(Flist), shlin2([([Wff],[Wff]),([Flist],[Flist])]) )
   => ( mshare([[Wff],[Wff,Flist],[Flist]]),
        ground([Tlist]), linear(Flist), shlin2([([Wff],[]),([Wff,Flist],[Flist]),([Flist],[Flist])]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Flist=[_A|_B]),
       mshare([[Wff],[_A],[_B]]),
       ground([Tlist]), linear(Wff), linear(_A), linear(_B), shlin2([([Wff],[Wff]),([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[Wff],[Wff,_A],[Wff,_B],[_A],[_B]]),
        ground([Tlist]), linear(_A), linear(_B), shlin2([([Wff],[]),([Wff,_A],[_A]),([Wff,_B],[_B]),([_A],[_A]),([_B],[_B])]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( mshare([[Wff]]),
       ground([Tlist,Flist]), linear(Wff), shlin2([([Wff],[Wff])]) )
   => ( mshare([[Wff]]),
        ground([Tlist,Flist]), shlin2([([Wff],[])]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Tlist=[]), (Flist=[]),
       mshare([[Wff]]),
       linear(Wff), shlin2([([Wff],[Wff])]) )
   => ( mshare([[Wff]]),
        shlin2([([Wff],[])]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Flist=[_A|_B]),
       mshare([[Wff],[_A]]),
       ground([Tlist,_B]), linear(Wff), linear(_A), shlin2([([Wff],[Wff]),([_A],[_A])]) )
   => ( mshare([[Wff],[Wff,_A],[Wff,_B],[_A],[_B]]),
        ground([Tlist]), linear(_A), linear(_B), shlin2([([Wff],[]),([Wff,_A],[_A]),([Wff,_B],[_B]),([_A],[_A]),([_B],[_B])]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Tlist=[_A|_B]),
       mshare([[Wff],[_A]]),
       ground([Flist,_B]), linear(Wff), linear(_A), shlin2([([Wff],[Wff]),([_A],[_A])]) )
   => ( mshare([[Wff],[Wff,_A],[Wff,_B],[_A],[_B]]),
        ground([Flist]), linear(_A), linear(_B), shlin2([([Wff],[]),([Wff,_A],[_A]),([Wff,_B],[_B]),([_A],[_A]),([_B],[_B])]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Tlist=[_A|_B]),
       mshare([[Wff],[Flist],[_A]]),
       ground([_B]), linear(Wff), linear(Flist), linear(_A), shlin2([([Wff],[Wff]),([Flist],[Flist]),([_A],[_A])]) )
   => ( mshare([[Wff],[Wff,Flist],[Wff,_A],[Wff,_B],[Flist],[_A],[_B]]),
        linear(Flist), linear(_A), linear(_B), shlin2([([Wff],[]),([Wff,Flist],[Flist]),([Wff,_A],[_A]),([Wff,_B],[_B]),([Flist],[Flist]),([_A],[_A]),([_B],[_B])]) ).

:- true pred tautology(Wff,Tlist,Flist)
   : ( (Flist=[_A|_B]),
       mshare([[Wff],[Tlist],[_A]]),
       ground([_B]), linear(Wff), linear(Tlist), linear(_A), shlin2([([Wff],[Wff]),([Tlist],[Tlist]),([_A],[_A])]) )
   => ( mshare([[Wff],[Wff,Tlist],[Wff,_A],[Wff,_B],[Tlist],[_A],[_B]]),
        linear(Tlist), linear(_A), linear(_B), shlin2([([Wff],[]),([Wff,Tlist],[Tlist]),([Wff,_A],[_A]),([Wff,_B],[_B]),([Tlist],[Tlist]),([_A],[_A]),([_B],[_B])]) ).

tautology(Wff,Tlist,Flist) :-
    true((mshare([[Wff]]),ground([Tlist,Flist]),linear(Wff),shlin2([([Wff],[Wff])]);mshare([[Wff],[Tlist]]),ground([Flist]),linear(Wff),linear(Tlist),shlin2([([Wff],[Wff]),([Tlist],[Tlist])]);mshare([[Wff],[Tlist],[Flist]]),linear(Wff),linear(Tlist),linear(Flist),shlin2([([Wff],[Wff]),([Tlist],[Tlist]),([Flist],[Flist])]);mshare([[Wff],[Flist]]),ground([Tlist]),linear(Wff),linear(Flist),shlin2([([Wff],[Wff]),([Flist],[Flist])]))),
    'tautology/3/1/$disj/1'(Wff,Tlist,Flist),
    !,
    true((mshare([[Wff]]),ground([Tlist,Flist]),shlin2([([Wff],[])]);mshare([[Wff],[Wff,Tlist],[Wff,Flist],[Tlist],[Flist]]),linear(Tlist),linear(Flist),shlin2([([Wff],[]),([Wff,Tlist],[Tlist]),([Wff,Flist],[Flist]),([Tlist],[Tlist]),([Flist],[Flist])]);mshare([[Wff],[Wff,Tlist],[Tlist]]),ground([Flist]),linear(Tlist),shlin2([([Wff],[]),([Wff,Tlist],[Tlist]),([Tlist],[Tlist])]);mshare([[Wff],[Wff,Flist],[Flist]]),ground([Tlist]),linear(Flist),shlin2([([Wff],[]),([Wff,Flist],[Flist]),([Flist],[Flist])]))).

:- true pred 'tautology/3/1/$disj/1'(Wff,Tlist,Flist)
   : ( mshare([[Wff]]),
       ground([Tlist,Flist]), linear(Wff), shlin2([([Wff],[Wff])]) )
   => ( mshare([[Wff]]),
        ground([Tlist,Flist]), shlin2([([Wff],[])]) ).

:- true pred 'tautology/3/1/$disj/1'(Wff,Tlist,Flist)
   : ( mshare([[Wff],[Flist]]),
       ground([Tlist]), linear(Wff), linear(Flist), shlin2([([Wff],[Wff]),([Flist],[Flist])]) )
   => ( mshare([[Wff],[Wff,Flist],[Flist]]),
        ground([Tlist]), linear(Flist), shlin2([([Wff],[]),([Wff,Flist],[Flist]),([Flist],[Flist])]) ).

:- true pred 'tautology/3/1/$disj/1'(Wff,Tlist,Flist)
   : ( mshare([[Wff],[Tlist],[Flist]]),
       linear(Wff), linear(Tlist), linear(Flist), shlin2([([Wff],[Wff]),([Tlist],[Tlist]),([Flist],[Flist])]) )
   => ( mshare([[Wff],[Wff,Tlist],[Wff,Flist],[Tlist],[Flist]]),
        linear(Tlist), linear(Flist), shlin2([([Wff],[]),([Wff,Tlist],[Tlist]),([Wff,Flist],[Flist]),([Tlist],[Tlist]),([Flist],[Flist])]) ).

:- true pred 'tautology/3/1/$disj/1'(Wff,Tlist,Flist)
   : ( mshare([[Wff],[Tlist]]),
       ground([Flist]), linear(Wff), linear(Tlist), shlin2([([Wff],[Wff]),([Tlist],[Tlist])]) )
   => ( mshare([[Wff],[Wff,Tlist],[Tlist]]),
        ground([Flist]), linear(Tlist), shlin2([([Wff],[]),([Wff,Tlist],[Tlist]),([Tlist],[Tlist])]) ).

'tautology/3/1/$disj/1'(Wff,Tlist,Flist) :-
    true((mshare([[Wff]]),ground([Tlist,Flist]),linear(Wff),shlin2([([Wff],[Wff])]);mshare([[Wff],[Tlist]]),ground([Flist]),linear(Wff),linear(Tlist),shlin2([([Wff],[Wff]),([Tlist],[Tlist])]);mshare([[Wff],[Tlist],[Flist]]),linear(Wff),linear(Tlist),linear(Flist),shlin2([([Wff],[Wff]),([Tlist],[Tlist]),([Flist],[Flist])]);mshare([[Wff],[Flist]]),ground([Tlist]),linear(Wff),linear(Flist),shlin2([([Wff],[Wff]),([Flist],[Flist])]))),
    truep(Wff,Tlist),
    !,
    true((mshare([[Wff,Tlist],[Tlist]]),ground([Flist]),linear(Wff),linear(Tlist),shlin2([([Wff,Tlist],[Wff,Tlist]),([Tlist],[Tlist])]);mshare([[Wff,Tlist],[Tlist],[Flist]]),linear(Wff),linear(Tlist),linear(Flist),shlin2([([Wff,Tlist],[Wff,Tlist]),([Tlist],[Tlist]),([Flist],[Flist])]);mshare([[Flist]]),ground([Wff,Tlist]),linear(Flist),shlin2([([Flist],[Flist])]);ground([Wff,Tlist,Flist]))),
    true,
    true((mshare([[Wff,Tlist],[Tlist]]),ground([Flist]),linear(Wff),linear(Tlist),shlin2([([Wff,Tlist],[Wff,Tlist]),([Tlist],[Tlist])]);mshare([[Wff,Tlist],[Tlist],[Flist]]),linear(Wff),linear(Tlist),linear(Flist),shlin2([([Wff,Tlist],[Wff,Tlist]),([Tlist],[Tlist]),([Flist],[Flist])]);mshare([[Flist]]),ground([Wff,Tlist]),linear(Flist),shlin2([([Flist],[Flist])]);ground([Wff,Tlist,Flist]))).
'tautology/3/1/$disj/1'(Wff,Tlist,Flist) :-
    true((mshare([[Wff]]),ground([Tlist,Flist]),linear(Wff),shlin2([([Wff],[Wff])]);mshare([[Wff],[Tlist]]),ground([Flist]),linear(Wff),linear(Tlist),shlin2([([Wff],[Wff]),([Tlist],[Tlist])]);mshare([[Wff],[Tlist],[Flist]]),linear(Wff),linear(Tlist),linear(Flist),shlin2([([Wff],[Wff]),([Tlist],[Tlist]),([Flist],[Flist])]);mshare([[Wff],[Flist]]),ground([Tlist]),linear(Wff),linear(Flist),shlin2([([Wff],[Wff]),([Flist],[Flist])]))),
    falsep(Wff,Flist),
    !,
    true((mshare([[Wff,Flist],[Tlist],[Flist]]),linear(Wff),linear(Tlist),linear(Flist),shlin2([([Wff,Flist],[Wff,Flist]),([Tlist],[Tlist]),([Flist],[Flist])]);mshare([[Wff,Flist],[Flist]]),ground([Tlist]),linear(Wff),linear(Flist),shlin2([([Wff,Flist],[Wff,Flist]),([Flist],[Flist])]);mshare([[Tlist]]),ground([Wff,Flist]),linear(Tlist),shlin2([([Tlist],[Tlist])]);ground([Wff,Tlist,Flist]))),
    fail,
    true(fails(_)).
'tautology/3/1/$disj/1'(Wff,Tlist,Flist) :-
    true((mshare([[Wff],[Tlist],[Flist],[If],[Then],[Else]]),linear(Wff),linear(Tlist),linear(Flist),linear(If),linear(Then),linear(Else),shlin2([([Wff],[Wff]),([Tlist],[Tlist]),([Flist],[Flist]),([If],[If]),([Then],[Then]),([Else],[Else])]);mshare([[Wff],[Tlist],[If],[Then],[Else]]),ground([Flist]),linear(Wff),linear(Tlist),linear(If),linear(Then),linear(Else),shlin2([([Wff],[Wff]),([Tlist],[Tlist]),([If],[If]),([Then],[Then]),([Else],[Else])]);mshare([[Wff],[Flist],[If],[Then],[Else]]),ground([Tlist]),linear(Wff),linear(Flist),linear(If),linear(Then),linear(Else),shlin2([([Wff],[Wff]),([Flist],[Flist]),([If],[If]),([Then],[Then]),([Else],[Else])]);mshare([[Wff],[If],[Then],[Else]]),ground([Tlist,Flist]),linear(Wff),linear(If),linear(Then),linear(Else),shlin2([([Wff],[Wff]),([If],[If]),([Then],[Then]),([Else],[Else])]))),
    Wff=if(If,Then,Else),
    !,
    true((mshare([[Wff,If],[Wff,Then],[Wff,Else]]),ground([Tlist,Flist]),linear(Wff),linear(If),linear(Then),linear(Else),shlin2([([Wff,If],[Wff,If]),([Wff,Then],[Wff,Then]),([Wff,Else],[Wff,Else])]);mshare([[Wff,If],[Wff,Then],[Wff,Else],[Tlist]]),ground([Flist]),linear(Wff),linear(Tlist),linear(If),linear(Then),linear(Else),shlin2([([Wff,If],[Wff,If]),([Wff,Then],[Wff,Then]),([Wff,Else],[Wff,Else]),([Tlist],[Tlist])]);mshare([[Wff,If],[Wff,Then],[Wff,Else],[Tlist],[Flist]]),linear(Wff),linear(Tlist),linear(Flist),linear(If),linear(Then),linear(Else),shlin2([([Wff,If],[Wff,If]),([Wff,Then],[Wff,Then]),([Wff,Else],[Wff,Else]),([Tlist],[Tlist]),([Flist],[Flist])]);mshare([[Wff,If],[Wff,Then],[Wff,Else],[Flist]]),ground([Tlist]),linear(Wff),linear(Flist),linear(If),linear(Then),linear(Else),shlin2([([Wff,If],[Wff,If]),([Wff,Then],[Wff,Then]),([Wff,Else],[Wff,Else]),([Flist],[Flist])]))),
    'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else),
    true((mshare([[Wff,Tlist,If],[Wff,Tlist,If,Then],[Wff,Tlist,Then],[Wff,Tlist,Then,Else],[Wff,Tlist,Else],[Wff,Flist,If],[Wff,Flist,If,Else],[Wff,Flist,Then],[Wff,Flist,Then,Else],[Wff,Flist,Else],[Wff,If],[Wff,If,Then],[Wff,If,Then,Else],[Wff,If,Else],[Wff,Then],[Wff,Else],[Tlist],[Flist]]),linear(Tlist),linear(Flist),linear(If),shlin2([([Wff,Tlist,If],[Wff,Tlist,If]),([Wff,Tlist,If,Then],[Tlist,If]),([Wff,Tlist,Then],[Tlist]),([Wff,Tlist,Then,Else],[Tlist]),([Wff,Tlist,Else],[Tlist]),([Wff,Flist,If],[Wff,Flist,If]),([Wff,Flist,If,Else],[Flist,If]),([Wff,Flist,Then],[Flist]),([Wff,Flist,Then,Else],[Flist]),([Wff,Flist,Else],[Flist]),([Wff,If],[Wff,If]),([Wff,If,Then],[If]),([Wff,If,Then,Else],[If]),([Wff,If,Else],[If]),([Wff,Then],[]),([Wff,Else],[]),([Tlist],[Tlist]),([Flist],[Flist])]);mshare([[Wff,Tlist,If],[Wff,Tlist,If,Then],[Wff,Tlist,Then],[Wff,Tlist,Then,Else],[Wff,Tlist,Else],[Wff,If],[Wff,If,Then],[Wff,If,Then,Else],[Wff,If,Else],[Wff,Then],[Wff,Else],[Tlist]]),ground([Flist]),linear(Tlist),linear(If),shlin2([([Wff,Tlist,If],[Wff,Tlist,If]),([Wff,Tlist,If,Then],[Tlist,If]),([Wff,Tlist,Then],[Tlist]),([Wff,Tlist,Then,Else],[Tlist]),([Wff,Tlist,Else],[Tlist]),([Wff,If],[Wff,If]),([Wff,If,Then],[If]),([Wff,If,Then,Else],[If]),([Wff,If,Else],[If]),([Wff,Then],[]),([Wff,Else],[]),([Tlist],[Tlist])]);mshare([[Wff,Flist,If],[Wff,Flist,If,Else],[Wff,Flist,Then],[Wff,Flist,Then,Else],[Wff,Flist,Else],[Wff,If],[Wff,If,Then],[Wff,If,Then,Else],[Wff,If,Else],[Wff,Then],[Wff,Else],[Flist]]),ground([Tlist]),linear(Flist),linear(If),shlin2([([Wff,Flist,If],[Wff,Flist,If]),([Wff,Flist,If,Else],[Flist,If]),([Wff,Flist,Then],[Flist]),([Wff,Flist,Then,Else],[Flist]),([Wff,Flist,Else],[Flist]),([Wff,If],[Wff,If]),([Wff,If,Then],[If]),([Wff,If,Then,Else],[If]),([Wff,If,Else],[If]),([Wff,Then],[]),([Wff,Else],[]),([Flist],[Flist])]);mshare([[Wff,If],[Wff,If,Then],[Wff,If,Then,Else],[Wff,If,Else],[Wff,Then],[Wff,Else]]),ground([Tlist,Flist]),linear(If),shlin2([([Wff,If],[Wff,If]),([Wff,If,Then],[If]),([Wff,If,Then,Else],[If]),([Wff,If,Else],[If]),([Wff,Then],[]),([Wff,Else],[])]))).

:- true pred 'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else)
   : ( mshare([[Tlist],[Flist],[If],[Then],[Else]]),
       linear(Tlist), linear(Flist), linear(If), linear(Then), linear(Else), shlin2([([Tlist],[Tlist]),([Flist],[Flist]),([If],[If]),([Then],[Then]),([Else],[Else])]) )
   => ( mshare([[Tlist],[Tlist,If],[Tlist,If,Then],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Flist],[Flist,If],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Else]]),
        linear(Tlist), linear(Flist), linear(If), shlin2([([Tlist],[Tlist]),([Tlist,If],[Tlist,If]),([Tlist,If,Then],[Tlist,If]),([Tlist,Then],[Tlist]),([Tlist,Then,Else],[Tlist]),([Tlist,Else],[Tlist]),([Flist],[Flist]),([Flist,If],[Flist,If]),([Flist,If,Else],[Flist,If]),([Flist,Then],[Flist]),([Flist,Then,Else],[Flist]),([Flist,Else],[Flist]),([If],[If]),([If,Then],[If]),([If,Then,Else],[If]),([If,Else],[If]),([Then],[]),([Else],[])]) ).

:- true pred 'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else)
   : ( mshare([[Tlist],[If],[Then],[Else]]),
       ground([Flist]), linear(Tlist), linear(If), linear(Then), linear(Else), shlin2([([Tlist],[Tlist]),([If],[If]),([Then],[Then]),([Else],[Else])]) )
   => ( mshare([[Tlist],[Tlist,If],[Tlist,If,Then],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Else]]),
        ground([Flist]), linear(Tlist), linear(If), shlin2([([Tlist],[Tlist]),([Tlist,If],[Tlist,If]),([Tlist,If,Then],[Tlist,If]),([Tlist,Then],[Tlist]),([Tlist,Then,Else],[Tlist]),([Tlist,Else],[Tlist]),([If],[If]),([If,Then],[If]),([If,Then,Else],[If]),([If,Else],[If]),([Then],[]),([Else],[])]) ).

:- true pred 'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else)
   : ( mshare([[Flist],[If],[Then],[Else]]),
       ground([Tlist]), linear(Flist), linear(If), linear(Then), linear(Else), shlin2([([Flist],[Flist]),([If],[If]),([Then],[Then]),([Else],[Else])]) )
   => ( mshare([[Flist],[Flist,If],[Flist,If,Else],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Else]]),
        ground([Tlist]), linear(Flist), linear(If), shlin2([([Flist],[Flist]),([Flist,If],[Flist,If]),([Flist,If,Else],[Flist,If]),([Flist,Then],[Flist]),([Flist,Then,Else],[Flist]),([Flist,Else],[Flist]),([If],[If]),([If,Then],[If]),([If,Then,Else],[If]),([If,Else],[If]),([Then],[]),([Else],[])]) ).

:- true pred 'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else)
   : ( mshare([[If],[Then],[Else]]),
       ground([Tlist,Flist]), linear(If), linear(Then), linear(Else), shlin2([([If],[If]),([Then],[Then]),([Else],[Else])]) )
   => ( mshare([[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Else]]),
        ground([Tlist,Flist]), linear(If), shlin2([([If],[If]),([If,Then],[If]),([If,Then,Else],[If]),([If,Else],[If]),([Then],[]),([Else],[])]) ).

'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else) :-
    true((mshare([[Tlist],[Flist],[If],[Then],[Else]]),linear(Tlist),linear(Flist),linear(If),linear(Then),linear(Else),shlin2([([Tlist],[Tlist]),([Flist],[Flist]),([If],[If]),([Then],[Then]),([Else],[Else])]);mshare([[Tlist],[If],[Then],[Else]]),ground([Flist]),linear(Tlist),linear(If),linear(Then),linear(Else),shlin2([([Tlist],[Tlist]),([If],[If]),([Then],[Then]),([Else],[Else])]);mshare([[Flist],[If],[Then],[Else]]),ground([Tlist]),linear(Flist),linear(If),linear(Then),linear(Else),shlin2([([Flist],[Flist]),([If],[If]),([Then],[Then]),([Else],[Else])]);mshare([[If],[Then],[Else]]),ground([Tlist,Flist]),linear(If),linear(Then),linear(Else),shlin2([([If],[If]),([Then],[Then]),([Else],[Else])]))),
    truep(If,Tlist),
    !,
    true((mshare([[Tlist],[Tlist,If],[Flist],[Then],[Else]]),linear(Tlist),linear(Flist),linear(If),linear(Then),linear(Else),shlin2([([Tlist],[Tlist]),([Tlist,If],[Tlist,If]),([Flist],[Flist]),([Then],[Then]),([Else],[Else])]);mshare([[Tlist],[Tlist,If],[Then],[Else]]),ground([Flist]),linear(Tlist),linear(If),linear(Then),linear(Else),shlin2([([Tlist],[Tlist]),([Tlist,If],[Tlist,If]),([Then],[Then]),([Else],[Else])]);mshare([[Flist],[Then],[Else]]),ground([Tlist,If]),linear(Flist),linear(Then),linear(Else),shlin2([([Flist],[Flist]),([Then],[Then]),([Else],[Else])]);mshare([[Then],[Else]]),ground([Tlist,Flist,If]),linear(Then),linear(Else),shlin2([([Then],[Then]),([Else],[Else])]))),
    tautology(Then,Tlist,Flist),
    true((mshare([[Tlist],[Tlist,If],[Tlist,If,Then],[Tlist,Then],[Flist],[Flist,Then],[Then],[Else]]),linear(Tlist),linear(Flist),linear(If),linear(Else),shlin2([([Tlist],[Tlist]),([Tlist,If],[Tlist,If]),([Tlist,If,Then],[Tlist,If]),([Tlist,Then],[Tlist]),([Flist],[Flist]),([Flist,Then],[Flist]),([Then],[]),([Else],[Else])]);mshare([[Tlist],[Tlist,If],[Tlist,If,Then],[Tlist,Then],[Then],[Else]]),ground([Flist]),linear(Tlist),linear(If),linear(Else),shlin2([([Tlist],[Tlist]),([Tlist,If],[Tlist,If]),([Tlist,If,Then],[Tlist,If]),([Tlist,Then],[Tlist]),([Then],[]),([Else],[Else])]);mshare([[Flist],[Flist,Then],[Then],[Else]]),ground([Tlist,If]),linear(Flist),linear(Else),shlin2([([Flist],[Flist]),([Flist,Then],[Flist]),([Then],[]),([Else],[Else])]);mshare([[Then],[Else]]),ground([Tlist,Flist,If]),linear(Else),shlin2([([Then],[]),([Else],[Else])]))).
'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else) :-
    true((mshare([[Tlist],[Flist],[If],[Then],[Else]]),linear(Tlist),linear(Flist),linear(If),linear(Then),linear(Else),shlin2([([Tlist],[Tlist]),([Flist],[Flist]),([If],[If]),([Then],[Then]),([Else],[Else])]);mshare([[Tlist],[If],[Then],[Else]]),ground([Flist]),linear(Tlist),linear(If),linear(Then),linear(Else),shlin2([([Tlist],[Tlist]),([If],[If]),([Then],[Then]),([Else],[Else])]);mshare([[Flist],[If],[Then],[Else]]),ground([Tlist]),linear(Flist),linear(If),linear(Then),linear(Else),shlin2([([Flist],[Flist]),([If],[If]),([Then],[Then]),([Else],[Else])]);mshare([[If],[Then],[Else]]),ground([Tlist,Flist]),linear(If),linear(Then),linear(Else),shlin2([([If],[If]),([Then],[Then]),([Else],[Else])]))),
    falsep(If,Flist),
    !,
    true((mshare([[Tlist],[Flist],[Flist,If],[Then],[Else]]),linear(Tlist),linear(Flist),linear(If),linear(Then),linear(Else),shlin2([([Tlist],[Tlist]),([Flist],[Flist]),([Flist,If],[Flist,If]),([Then],[Then]),([Else],[Else])]);mshare([[Tlist],[Then],[Else]]),ground([Flist,If]),linear(Tlist),linear(Then),linear(Else),shlin2([([Tlist],[Tlist]),([Then],[Then]),([Else],[Else])]);mshare([[Flist],[Flist,If],[Then],[Else]]),ground([Tlist]),linear(Flist),linear(If),linear(Then),linear(Else),shlin2([([Flist],[Flist]),([Flist,If],[Flist,If]),([Then],[Then]),([Else],[Else])]);mshare([[Then],[Else]]),ground([Tlist,Flist,If]),linear(Then),linear(Else),shlin2([([Then],[Then]),([Else],[Else])]))),
    tautology(Else,Tlist,Flist),
    true((mshare([[Tlist],[Tlist,Else],[Flist],[Flist,If],[Flist,If,Else],[Flist,Else],[Then],[Else]]),linear(Tlist),linear(Flist),linear(If),linear(Then),shlin2([([Tlist],[Tlist]),([Tlist,Else],[Tlist]),([Flist],[Flist]),([Flist,If],[Flist,If]),([Flist,If,Else],[Flist,If]),([Flist,Else],[Flist]),([Then],[Then]),([Else],[])]);mshare([[Tlist],[Tlist,Else],[Then],[Else]]),ground([Flist,If]),linear(Tlist),linear(Then),shlin2([([Tlist],[Tlist]),([Tlist,Else],[Tlist]),([Then],[Then]),([Else],[])]);mshare([[Flist],[Flist,If],[Flist,If,Else],[Flist,Else],[Then],[Else]]),ground([Tlist]),linear(Flist),linear(If),linear(Then),shlin2([([Flist],[Flist]),([Flist,If],[Flist,If]),([Flist,If,Else],[Flist,If]),([Flist,Else],[Flist]),([Then],[Then]),([Else],[])]);mshare([[Then],[Else]]),ground([Tlist,Flist,If]),linear(Then),shlin2([([Then],[Then]),([Else],[])]))).
'tautology/3/1/$disj/1/3/3/$disj/1'(Tlist,Flist,If,Then,Else) :-
    true((mshare([[Tlist],[Flist],[If],[Then],[Else]]),linear(Tlist),linear(Flist),linear(If),linear(Then),linear(Else),shlin2([([Tlist],[Tlist]),([Flist],[Flist]),([If],[If]),([Then],[Then]),([Else],[Else])]);mshare([[Tlist],[If],[Then],[Else]]),ground([Flist]),linear(Tlist),linear(If),linear(Then),linear(Else),shlin2([([Tlist],[Tlist]),([If],[If]),([Then],[Then]),([Else],[Else])]);mshare([[Flist],[If],[Then],[Else]]),ground([Tlist]),linear(Flist),linear(If),linear(Then),linear(Else),shlin2([([Flist],[Flist]),([If],[If]),([Then],[Then]),([Else],[Else])]);mshare([[If],[Then],[Else]]),ground([Tlist,Flist]),linear(If),linear(Then),linear(Else),shlin2([([If],[If]),([Then],[Then]),([Else],[Else])]))),
    tautology(Then,[If|Tlist],Flist),
    true((mshare([[Tlist],[Tlist,Then],[Flist],[Flist,Then],[If],[If,Then],[Then],[Else]]),linear(Tlist),linear(Flist),linear(If),linear(Else),shlin2([([Tlist],[Tlist]),([Tlist,Then],[Tlist]),([Flist],[Flist]),([Flist,Then],[Flist]),([If],[If]),([If,Then],[If]),([Then],[]),([Else],[Else])]);mshare([[Tlist],[Tlist,Then],[If],[If,Then],[Then],[Else]]),ground([Flist]),linear(Tlist),linear(If),linear(Else),shlin2([([Tlist],[Tlist]),([Tlist,Then],[Tlist]),([If],[If]),([If,Then],[If]),([Then],[]),([Else],[Else])]);mshare([[Flist],[Flist,Then],[If],[If,Then],[Then],[Else]]),ground([Tlist]),linear(Flist),linear(If),linear(Else),shlin2([([Flist],[Flist]),([Flist,Then],[Flist]),([If],[If]),([If,Then],[If]),([Then],[]),([Else],[Else])]);mshare([[If],[If,Then],[Then],[Else]]),ground([Tlist,Flist]),linear(If),linear(Else),shlin2([([If],[If]),([If,Then],[If]),([Then],[]),([Else],[Else])]))),
    tautology(Else,Tlist,[If|Flist]),
    true((mshare([[Tlist],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[Flist],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Else]]),linear(Tlist),linear(Flist),linear(If),shlin2([([Tlist],[Tlist]),([Tlist,Then],[Tlist]),([Tlist,Then,Else],[Tlist]),([Tlist,Else],[Tlist]),([Flist],[Flist]),([Flist,Then],[Flist]),([Flist,Then,Else],[Flist]),([Flist,Else],[Flist]),([If],[If]),([If,Then],[If]),([If,Then,Else],[If]),([If,Else],[If]),([Then],[]),([Else],[])]);mshare([[Tlist],[Tlist,Then],[Tlist,Then,Else],[Tlist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Else]]),ground([Flist]),linear(Tlist),linear(If),shlin2([([Tlist],[Tlist]),([Tlist,Then],[Tlist]),([Tlist,Then,Else],[Tlist]),([Tlist,Else],[Tlist]),([If],[If]),([If,Then],[If]),([If,Then,Else],[If]),([If,Else],[If]),([Then],[]),([Else],[])]);mshare([[Flist],[Flist,Then],[Flist,Then,Else],[Flist,Else],[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Else]]),ground([Tlist]),linear(Flist),linear(If),shlin2([([Flist],[Flist]),([Flist,Then],[Flist]),([Flist,Then,Else],[Flist]),([Flist,Else],[Flist]),([If],[If]),([If,Then],[If]),([If,Then,Else],[If]),([If,Else],[If]),([Then],[]),([Else],[])]);mshare([[If],[If,Then],[If,Then,Else],[If,Else],[Then],[Else]]),ground([Tlist,Flist]),linear(If),shlin2([([If],[If]),([If,Then],[If]),([If,Then,Else],[If]),([If,Else],[If]),([Then],[]),([Else],[])]))).

:- true pred rewrite(Atom,New)
   : ( mshare([[Atom],[New]]),
       linear(New), shlin2([([Atom],[]),([New],[New])]) )
   => ( mshare([[Atom],[New]]),
        linear(New), shlin2([([Atom],[]),([New],[New])]) ).

:- true pred rewrite(Atom,New)
   : ( mshare([[Atom]]),
       ground([New]), shlin2([([Atom],[])]) )
   => ( mshare([[Atom]]),
        ground([New]), shlin2([([Atom],[])]) ).

:- true pred rewrite(Atom,New)
   : ground([Atom,New])
   => ground([Atom,New]).

:- true pred rewrite(Atom,New)
   : ( mshare([[New]]),
       ground([Atom]), linear(New), shlin2([([New],[New])]) )
   => ( mshare([[New]]),
        ground([Atom]), linear(New), shlin2([([New],[New])]) ).

rewrite(Atom,Atom) :-
    true((mshare([[Atom]]),shlin2([([Atom],[])]);ground([Atom]))),
    atomic(Atom),
    !,
    true(ground([Atom])).
rewrite(Old,New) :-
    true((mshare([[Old],[New],[F],[N],[Mid]]),linear(New),linear(F),linear(N),linear(Mid),shlin2([([Old],[]),([New],[New]),([F],[F]),([N],[N]),([Mid],[Mid])]);mshare([[Old],[F],[N],[Mid]]),ground([New]),linear(F),linear(N),linear(Mid),shlin2([([Old],[]),([F],[F]),([N],[N]),([Mid],[Mid])]);mshare([[New],[F],[N],[Mid]]),ground([Old]),linear(New),linear(F),linear(N),linear(Mid),shlin2([([New],[New]),([F],[F]),([N],[N]),([Mid],[Mid])]);mshare([[F],[N],[Mid]]),ground([Old,New]),linear(F),linear(N),linear(Mid),shlin2([([F],[F]),([N],[N]),([Mid],[Mid])]))),
    functor(Old,F,N),
    true((mshare([[Old],[New],[Mid]]),ground([F,N]),linear(New),linear(Mid),shlin2([([Old],[]),([New],[New]),([Mid],[Mid])]);mshare([[Old],[Mid]]),ground([New,F,N]),linear(Mid),shlin2([([Old],[]),([Mid],[Mid])]);mshare([[New],[Mid]]),ground([Old,F,N]),linear(New),linear(Mid),shlin2([([New],[New]),([Mid],[Mid])]);mshare([[Mid]]),ground([Old,New,F,N]),linear(Mid),shlin2([([Mid],[Mid])]))),
    functor(Mid,F,N),
    true((mshare([[Old],[New],[Mid]]),ground([F,N]),linear(New),linear(Mid),shlin2([([Old],[]),([New],[New]),([Mid],[Mid])]);mshare([[Old],[Mid]]),ground([New,F,N]),linear(Mid),shlin2([([Old],[]),([Mid],[Mid])]);mshare([[New],[Mid]]),ground([Old,F,N]),linear(New),linear(Mid),shlin2([([New],[New]),([Mid],[Mid])]);mshare([[Mid]]),ground([Old,New,F,N]),linear(Mid),shlin2([([Mid],[Mid])]))),
    rewrite_args(N,Old,Mid),
    true((mshare([[Old],[New],[Mid]]),ground([F,N]),linear(New),linear(Mid),shlin2([([Old],[]),([New],[New]),([Mid],[Mid])]);mshare([[Old],[Mid]]),ground([New,F,N]),linear(Mid),shlin2([([Old],[]),([Mid],[Mid])]);mshare([[New],[Mid]]),ground([Old,F,N]),linear(New),linear(Mid),shlin2([([New],[New]),([Mid],[Mid])]);mshare([[Mid]]),ground([Old,New,F,N]),linear(Mid),shlin2([([Mid],[Mid])]))),
    'rewrite/2/2/$disj/1'(New,Mid),
    !,
    true((mshare([[Old],[New],[New,Mid],[Mid]]),ground([F,N]),linear(New),shlin2([([Old],[]),([New],[New]),([New,Mid],[New,Mid]),([Mid],[])]);mshare([[Old],[Mid]]),ground([New,F,N]),shlin2([([Old],[]),([Mid],[])]);mshare([[New],[New,Mid],[Mid]]),ground([Old,F,N]),linear(New),shlin2([([New],[New]),([New,Mid],[New,Mid]),([Mid],[])]);mshare([[Mid]]),ground([Old,New,F,N]),shlin2([([Mid],[])]))).

:- true pred 'rewrite/2/2/$disj/1'(New,Mid)
   : ( mshare([[New],[Mid]]),
       linear(New), linear(Mid), shlin2([([New],[New]),([Mid],[Mid])]) )
   => ( mshare([[New],[New,Mid],[Mid]]),
        linear(New), shlin2([([New],[New]),([New,Mid],[New,Mid]),([Mid],[])]) ).

:- true pred 'rewrite/2/2/$disj/1'(New,Mid)
   : ( mshare([[Mid]]),
       ground([New]), linear(Mid), shlin2([([Mid],[Mid])]) )
   => ( mshare([[Mid]]),
        ground([New]), shlin2([([Mid],[])]) ).

'rewrite/2/2/$disj/1'(New,Mid) :-
    true((mshare([[New],[Mid],[Next]]),linear(New),linear(Mid),linear(Next),shlin2([([New],[New]),([Mid],[Mid]),([Next],[Next])]);mshare([[Mid],[Next]]),ground([New]),linear(Mid),linear(Next),shlin2([([Mid],[Mid]),([Next],[Next])]))),
    equal(Mid,Next),
    true((mshare([[New],[Mid],[Mid,Next]]),linear(New),shlin2([([New],[New]),([Mid],[]),([Mid,Next],[])]);mshare([[Mid],[Mid,Next]]),ground([New]),shlin2([([Mid],[]),([Mid,Next],[])]))),
    rewrite(Next,New),
    true((mshare([[New],[Mid],[Mid,Next]]),linear(New),shlin2([([New],[New]),([Mid],[]),([Mid,Next],[])]);mshare([[Mid],[Mid,Next]]),ground([New]),shlin2([([Mid],[]),([Mid,Next],[])]))).
'rewrite/2/2/$disj/1'(New,Mid) :-
    true((mshare([[New],[Mid]]),linear(New),linear(Mid),shlin2([([New],[New]),([Mid],[Mid])]);mshare([[Mid]]),ground([New]),linear(Mid),shlin2([([Mid],[Mid])]))),
    New=Mid,
    true((mshare([[New,Mid]]),linear(New),linear(Mid),shlin2([([New,Mid],[New,Mid])]);ground([New,Mid]))).

:- true pred rewrite_args(N,_1,_2)
   : ground([N,_1,_2])
   => ground([N,_1,_2]).

:- true pred rewrite_args(N,_1,_2)
   : ( mshare([[_2]]),
       ground([N,_1]), linear(_2), shlin2([([_2],[_2])]) )
   => ( mshare([[_2]]),
        ground([N,_1]), linear(_2), shlin2([([_2],[_2])]) ).

:- true pred rewrite_args(N,_1,_2)
   : ( mshare([[_1],[_2]]),
       ground([N]), linear(_2), shlin2([([_1],[]),([_2],[_2])]) )
   => ( mshare([[_1],[_2]]),
        ground([N]), linear(_2), shlin2([([_1],[]),([_2],[_2])]) ).

rewrite_args(0,_1,_2) :-
    !,
    true((mshare([[_1],[_2]]),linear(_2),shlin2([([_1],[]),([_2],[_2])]);mshare([[_2]]),ground([_1]),linear(_2),shlin2([([_2],[_2])]);ground([_1,_2]))).
rewrite_args(N,Old,Mid) :-
    true((mshare([[Old],[Mid],[OldArg],[MidArg],[N1]]),ground([N]),linear(Mid),linear(OldArg),linear(MidArg),linear(N1),shlin2([([Old],[]),([Mid],[Mid]),([OldArg],[OldArg]),([MidArg],[MidArg]),([N1],[N1])]);mshare([[Mid],[OldArg],[MidArg],[N1]]),ground([N,Old]),linear(Mid),linear(OldArg),linear(MidArg),linear(N1),shlin2([([Mid],[Mid]),([OldArg],[OldArg]),([MidArg],[MidArg]),([N1],[N1])]);mshare([[OldArg],[MidArg],[N1]]),ground([N,Old,Mid]),linear(OldArg),linear(MidArg),linear(N1),shlin2([([OldArg],[OldArg]),([MidArg],[MidArg]),([N1],[N1])]))),
    arg(N,Old,OldArg),
    true((mshare([[Old,OldArg],[Mid],[MidArg],[N1]]),ground([N]),linear(Mid),linear(MidArg),linear(N1),shlin2([([Old,OldArg],[]),([Mid],[Mid]),([MidArg],[MidArg]),([N1],[N1])]);mshare([[Mid],[MidArg],[N1]]),ground([N,Old,OldArg]),linear(Mid),linear(MidArg),linear(N1),shlin2([([Mid],[Mid]),([MidArg],[MidArg]),([N1],[N1])]);mshare([[MidArg],[N1]]),ground([N,Old,Mid,OldArg]),linear(MidArg),linear(N1),shlin2([([MidArg],[MidArg]),([N1],[N1])]))),
    arg(N,Mid,MidArg),
    true((mshare([[Old,OldArg],[Mid,MidArg],[N1]]),ground([N]),linear(Mid),linear(MidArg),linear(N1),shlin2([([Old,OldArg],[]),([Mid,MidArg],[Mid,MidArg]),([N1],[N1])]);mshare([[Mid,MidArg],[N1]]),ground([N,Old,OldArg]),linear(Mid),linear(MidArg),linear(N1),shlin2([([Mid,MidArg],[Mid,MidArg]),([N1],[N1])]);mshare([[N1]]),ground([N,Old,Mid,OldArg,MidArg]),linear(N1),shlin2([([N1],[N1])]))),
    rewrite(OldArg,MidArg),
    true((mshare([[Old,OldArg],[Mid,MidArg],[N1]]),ground([N]),linear(Mid),linear(MidArg),linear(N1),shlin2([([Old,OldArg],[]),([Mid,MidArg],[Mid,MidArg]),([N1],[N1])]);mshare([[Mid,MidArg],[N1]]),ground([N,Old,OldArg]),linear(Mid),linear(MidArg),linear(N1),shlin2([([Mid,MidArg],[Mid,MidArg]),([N1],[N1])]);mshare([[N1]]),ground([N,Old,Mid,OldArg,MidArg]),linear(N1),shlin2([([N1],[N1])]))),
    N1 is N-1,
    true((mshare([[Old,OldArg],[Mid,MidArg]]),ground([N,N1]),linear(Mid),linear(MidArg),shlin2([([Old,OldArg],[]),([Mid,MidArg],[Mid,MidArg])]);mshare([[Mid,MidArg]]),ground([N,Old,OldArg,N1]),linear(Mid),linear(MidArg),shlin2([([Mid,MidArg],[Mid,MidArg])]);ground([N,Old,Mid,OldArg,MidArg,N1]))),
    rewrite_args(N1,Old,Mid),
    true((mshare([[Old,OldArg],[Mid,MidArg]]),ground([N,N1]),linear(Mid),linear(MidArg),shlin2([([Old,OldArg],[]),([Mid,MidArg],[Mid,MidArg])]);mshare([[Mid,MidArg]]),ground([N,Old,OldArg,N1]),linear(Mid),linear(MidArg),shlin2([([Mid,MidArg],[Mid,MidArg])]);ground([N,Old,Mid,OldArg,MidArg,N1]))).

:- true pred truep(Wff,_1)
   : ( mshare([[Wff]]),
       ground([_1]), linear(Wff), shlin2([([Wff],[Wff])]) )
   => ground([Wff,_1]).

:- true pred truep(Wff,_1)
   : ( mshare([[Wff],[_1]]),
       linear(Wff), linear(_1), shlin2([([Wff],[Wff]),([_1],[_1])]) )
   => ( mshare([[Wff,_1],[_1]]),
        linear(Wff), linear(_1), shlin2([([Wff,_1],[Wff,_1]),([_1],[_1])]) ).

truep(t,_1) :-
    !,
    true((mshare([[_1]]),linear(_1),shlin2([([_1],[_1])]);ground([_1]))).
truep(Wff,Tlist) :-
    true((mshare([[Wff]]),ground([Tlist]),linear(Wff),shlin2([([Wff],[Wff])]);mshare([[Wff],[Tlist]]),linear(Wff),linear(Tlist),shlin2([([Wff],[Wff]),([Tlist],[Tlist])]))),
    boyer_member(Wff,Tlist),
    true((mshare([[Wff,Tlist],[Tlist]]),linear(Wff),linear(Tlist),shlin2([([Wff,Tlist],[Wff,Tlist]),([Tlist],[Tlist])]);ground([Wff,Tlist]))).

:- true pred falsep(Wff,_1)
   : ( mshare([[Wff]]),
       ground([_1]), linear(Wff), shlin2([([Wff],[Wff])]) )
   => ground([Wff,_1]).

:- true pred falsep(Wff,_1)
   : ( mshare([[Wff],[_1]]),
       linear(Wff), linear(_1), shlin2([([Wff],[Wff]),([_1],[_1])]) )
   => ( mshare([[Wff,_1],[_1]]),
        linear(Wff), linear(_1), shlin2([([Wff,_1],[Wff,_1]),([_1],[_1])]) ).

falsep(f,_1) :-
    !,
    true((mshare([[_1]]),linear(_1),shlin2([([_1],[_1])]);ground([_1]))).
falsep(Wff,Flist) :-
    true((mshare([[Wff]]),ground([Flist]),linear(Wff),shlin2([([Wff],[Wff])]);mshare([[Wff],[Flist]]),linear(Wff),linear(Flist),shlin2([([Wff],[Wff]),([Flist],[Flist])]))),
    boyer_member(Wff,Flist),
    true((mshare([[Wff,Flist],[Flist]]),linear(Wff),linear(Flist),shlin2([([Wff,Flist],[Wff,Flist]),([Flist],[Flist])]);ground([Wff,Flist]))).

:- true pred boyer_member(X,_A)
   : ( mshare([[X],[_A]]),
       linear(X), linear(_A), shlin2([([X],[X]),([_A],[_A])]) )
   => ( mshare([[X,_A],[_A]]),
        linear(X), linear(_A), shlin2([([X,_A],[X,_A]),([_A],[_A])]) ).

:- true pred boyer_member(X,_A)
   : ( mshare([[X]]),
       ground([_A]), linear(X), shlin2([([X],[X])]) )
   => ground([X,_A]).

boyer_member(X,[X|_1]) :-
    !,
    true((mshare([[X],[_1]]),linear(X),linear(_1),shlin2([([X],[X]),([_1],[_1])]);ground([X,_1]))).
boyer_member(X,[_1|T]) :-
    true((mshare([[X]]),ground([_1,T]),linear(X),shlin2([([X],[X])]);mshare([[X],[_1],[T]]),linear(X),linear(_1),linear(T),shlin2([([X],[X]),([_1],[_1]),([T],[T])]))),
    boyer_member(X,T),
    true((mshare([[X,T],[_1],[T]]),linear(X),linear(_1),linear(T),shlin2([([X,T],[X,T]),([_1],[_1]),([T],[T])]);ground([X,_1,T]))).

:- true pred equal(_A,C)
   : ( mshare([[_A],[C]]),
       linear(_A), linear(C), shlin2([([_A],[_A]),([C],[C])]) )
   => ( mshare([[_A],[_A,C]]),
        shlin2([([_A],[]),([_A,C],[])]) ).

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
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    boyer_difference(A,B,C),
    true((
        mshare([[C,A],[C,B],[A,B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C,A],[C,A]),([C,B],[C,B]),([A,B],[A,B])])
    )).
equal(divides(X,Y),zerop(remainder(Y,X))).
equal(dsort(X),sort2(X)).
equal(eqp(X,Y),equal(fix(X),fix(Y))).
equal(equal(A,B),C) :-
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    eq(A,B,C),
    true((
        mshare([[C,A],[C,A,B],[C,B],[A],[A,B]]),
        linear(A),
        linear(B),
        shlin2([([C,A],[A]),([C,A,B],[A,B]),([C,B],[B]),([A],[A]),([A,B],[A,B])])
    )).
equal(even1(X),if(zerop(X),t,odd(decr(X)))).
equal(exec(append(X,Y),Pds,Envrn),exec(Y,exec(X,Pds,Envrn),Envrn)).
equal(exp(A,B),C) :-
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    exp(A,B,C),
    true((
        mshare([[C,A],[C,B]]),
        linear(A),
        linear(B),
        shlin2([([C,A],[A]),([C,B],[C,B])])
    )).
equal(fact_(I),fact_loop(I,1)).
equal(falsify(X),falsify1(normalize(X),[])).
equal(fix(X),if(numberp(X),X,zero)).
equal(flatten(cdr(gopher(X))),if(listp(X),cdr(flatten(X)),cons(zero,[]))).
equal(gcd(A,B),C) :-
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    gcd(A,B,C),
    true((
        mshare([[C,A],[C,A,B],[C,B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C,A],[C,A]),([C,A,B],[C,A,B]),([C,B],[C,B])])
    )).
equal(get(J,set(I,Val,Mem)),if(eqp(J,I),Val,get(J,Mem))).
equal(greatereqp(X,Y),not(lessp(X,Y))).
equal(greatereqpr(X,Y),not(lessp(X,Y))).
equal(greaterp(X,Y),lessp(Y,X)).
equal(if(if(A,B,C),D,E),if(A,if(B,D,E),if(C,D,E))).
equal(iff(X,Y),and(implies(X,Y),implies(Y,X))).
equal(implies(P,Q),if(P,if(Q,t,f),t)).
equal(last(append(A,B)),if(listp(B),last(B),if(listp(A),cons(car(last(A))),B))).
equal(length(A),B) :-
    true((
        mshare([[B],[A]]),
        linear(B),
        linear(A),
        shlin2([([B],[B]),([A],[A])])
    )),
    mylength(A,B),
    true((
        mshare([[B,A],[A]]),
        linear(B),
        linear(A),
        shlin2([([B,A],[B,A]),([A],[A])])
    )).
equal(lesseqp(X,Y),not(lessp(Y,X))).
equal(lessp(A,B),C) :-
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    lessp(A,B,C),
    true((
        mshare([[C,A],[C,A,B],[C,B],[A],[A,B]]),
        linear(A),
        linear(B),
        shlin2([([C,A],[A]),([C,A,B],[A,B]),([C,B],[C,B]),([A],[A]),([A,B],[A,B])])
    )).
equal(listp(gopher(X)),listp(X)).
equal(mc_flatten(X,Y),append(flatten(X),Y)).
equal(meaning(A,B),C) :-
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    meaning(A,B,C),
    true((
        mshare([[C,A],[C,B]]),
        linear(A),
        linear(B),
        shlin2([([C,A],[A]),([C,B],[B])])
    )).
equal(boyer_member(A,B),C) :-
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    myboyer_member(A,B,C),
    true((
        mshare([[C,A],[C,B]]),
        linear(A),
        linear(B),
        shlin2([([C,A],[A]),([C,B],[C,B])])
    )).
equal(not(P),if(P,f,t)).
equal(my_nth(A,B),C) :-
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    my_nth(A,B,C),
    true((
        mshare([[C,A],[C,B],[B]]),
        linear(A),
        linear(B),
        shlin2([([C,A],[A]),([C,B],[B]),([B],[B])])
    )).
equal(numberp(greatest_factor(X,Y)),not(and(or(zerop(Y),equal(Y,1)),not(numberp(X))))).
equal(or(P,Q),if(P,t,if(Q,t,f),f)).
equal(myplus(A,B),C) :-
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    myplus(A,B,C),
    true((
        mshare([[C,A],[C,A,B],[C,B],[A,B]]),
        linear(A),
        shlin2([([C,A],[A]),([C,A,B],[C,A,B]),([C,B],[B]),([A,B],[A])])
    )).
equal(power_eval(A,B),C) :-
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    power_eval(A,B,C),
    true((
        mshare([[C,A],[C,A,B],[A,B]]),
        linear(B),
        shlin2([([C,A],[C,A]),([C,A,B],[A,B]),([A,B],[B])])
    )).
equal(prime(X),and(not(zerop(X)),and(not(equal(X,add1(zero))),prime1(X,decr(X))))).
equal(prime_list(append(X,Y)),and(prime_list(X),prime_list(Y))).
equal(quotient(A,B),C) :-
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    quotient(A,B,C),
    true((
        mshare([[C,A],[C,A,B]]),
        linear(C),
        linear(B),
        shlin2([([C,A],[C]),([C,A,B],[C,A,B])])
    )).
equal(remainder(A,B),C) :-
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    remainder(A,B,C),
    true((
        mshare([[A],[A,B]]),
        ground([C]),
        linear(A),
        linear(B),
        shlin2([([A],[A]),([A,B],[A,B])])
    )).
equal(reverse_(X),reverse_loop(X,[])).
equal(reverse(append(A,B)),append(reverse(B),reverse(A))).
equal(reverse_loop(A,B),C) :-
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    reverse_loop(A,B,C),
    true((
        mshare([[C,A],[C,B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C,A],[C,A]),([C,B],[C,B])])
    )).
equal(samefringe(X,Y),equal(flatten(X),flatten(Y))).
equal(sigma(zero,I),quotient(times(I,add1(I)),2)).
equal(sort2(delete(X,L)),delete(X,sort2(L))).
equal(tautology_checker(X),tautologyp(normalize(X),[])).
equal(times(A,B),C) :-
    true((
        mshare([[C],[A],[B]]),
        linear(C),
        linear(A),
        linear(B),
        shlin2([([C],[C]),([A],[A]),([B],[B])])
    )),
    times(A,B,C),
    true((
        mshare([[C,A],[C,B]]),
        linear(A),
        linear(B),
        shlin2([([C,A],[A]),([C,B],[B])])
    )).
equal(times_list(append(X,Y)),times(times_list(X),times_list(Y))).
equal(value(normalize(X),A),value(X,A)).
equal(zerop(X),or(equal(X,zero),not(numberp(X)))).

:- true pred boyer_difference(X,A,_A)
   : ( mshare([[X],[A],[_A]]),
       linear(X), linear(A), linear(_A), shlin2([([X],[X]),([A],[A]),([_A],[_A])]) )
   => ( mshare([[X,A],[X,_A],[A,_A]]),
        linear(X), linear(A), linear(_A), shlin2([([X,A],[X,A]),([X,_A],[X,_A]),([A,_A],[A,_A])]) ).

boyer_difference(X,X,zero) :-
    !,
    true((
        mshare([[X]]),
        linear(X),
        shlin2([([X],[X])])
    )).
boyer_difference(myplus(X,Y),X,fix(Y)) :-
    !,
    true((
        mshare([[X],[Y]]),
        linear(X),
        linear(Y),
        shlin2([([X],[X]),([Y],[Y])])
    )).
boyer_difference(myplus(Y,X),X,fix(Y)) :-
    !,
    true((
        mshare([[X],[Y]]),
        linear(X),
        linear(Y),
        shlin2([([X],[X]),([Y],[Y])])
    )).
boyer_difference(myplus(X,Y),myplus(X,Z),boyer_difference(Y,Z)) :-
    !,
    true((
        mshare([[X],[Y],[Z]]),
        linear(X),
        linear(Y),
        linear(Z),
        shlin2([([X],[X]),([Y],[Y]),([Z],[Z])])
    )).
boyer_difference(myplus(B,myplus(A,C)),A,myplus(B,C)) :-
    !,
    true((
        mshare([[A],[B],[C]]),
        linear(A),
        linear(B),
        linear(C),
        shlin2([([A],[A]),([B],[B]),([C],[C])])
    )).
boyer_difference(add1(myplus(Y,Z)),Z,add1(Y)) :-
    !,
    true((
        mshare([[Z],[Y]]),
        linear(Z),
        linear(Y),
        shlin2([([Z],[Z]),([Y],[Y])])
    )).
boyer_difference(add1(add1(X)),2,fix(X)).

:- true pred eq(X,Z,_A)
   : ( mshare([[X],[Z],[_A]]),
       linear(X), linear(Z), linear(_A), shlin2([([X],[X]),([Z],[Z]),([_A],[_A])]) )
   => ( mshare([[X],[X,Z],[X,Z,_A],[X,_A],[Z,_A]]),
        linear(X), linear(Z), shlin2([([X],[X]),([X,Z],[X,Z]),([X,Z,_A],[X,Z]),([X,_A],[X]),([Z,_A],[Z])]) ).

eq(myplus(A,B),zero,and(zerop(A),zerop(B))) :-
    !,
    true((
        mshare([[A],[B]]),
        linear(A),
        linear(B),
        shlin2([([A],[A]),([B],[B])])
    )).
eq(myplus(A,B),myplus(A,C),equal(fix(B),fix(C))) :-
    !,
    true((
        mshare([[A],[B],[C]]),
        linear(A),
        linear(B),
        linear(C),
        shlin2([([A],[A]),([B],[B]),([C],[C])])
    )).
eq(zero,boyer_difference(X,Y),not(lessp(Y,X))) :-
    !,
    true((
        mshare([[X],[Y]]),
        linear(X),
        linear(Y),
        shlin2([([X],[X]),([Y],[Y])])
    )).
eq(X,boyer_difference(X,Y),and(numberp(X),and(or(equal(X,zero),zerop(Y))))) :-
    !,
    true((
        mshare([[X],[Y]]),
        linear(X),
        linear(Y),
        shlin2([([X],[X]),([Y],[Y])])
    )).
eq(times(X,Y),zero,or(zerop(X),zerop(Y))) :-
    !,
    true((
        mshare([[X],[Y]]),
        linear(X),
        linear(Y),
        shlin2([([X],[X]),([Y],[Y])])
    )).
eq(append(A,B),append(A,C),equal(B,C)) :-
    !,
    true((
        mshare([[A],[B],[C]]),
        linear(A),
        linear(B),
        linear(C),
        shlin2([([A],[A]),([B],[B]),([C],[C])])
    )).
eq(flatten(X),cons(Y,[]),and(nlistp(X),equal(X,Y))) :-
    !,
    true((
        mshare([[X],[Y]]),
        linear(X),
        linear(Y),
        shlin2([([X],[X]),([Y],[Y])])
    )).
eq(greatest_factor(X,Y),zero,and(or(zerop(Y),equal(Y,1)),equal(X,zero))) :-
    !,
    true((
        mshare([[X],[Y]]),
        linear(X),
        linear(Y),
        shlin2([([X],[X]),([Y],[Y])])
    )).
eq(greatest_factor(X,_1),1,equal(X,1)) :-
    !,
    true((
        mshare([[X],[_1]]),
        linear(X),
        linear(_1),
        shlin2([([X],[X]),([_1],[_1])])
    )).
eq(Z,times(W,Z),and(numberp(Z),or(equal(Z,zero),equal(W,1)))) :-
    !,
    true((
        mshare([[Z],[W]]),
        linear(Z),
        linear(W),
        shlin2([([Z],[Z]),([W],[W])])
    )).
eq(X,times(X,Y),or(equal(X,zero),and(numberp(X),equal(Y,1)))) :-
    !,
    true((
        mshare([[X],[Y]]),
        linear(X),
        linear(Y),
        shlin2([([X],[X]),([Y],[Y])])
    )).
eq(times(A,B),1,and(not(equal(A,zero)),and(not(equal(B,zero)),and(numberp(A),and(numberp(B),and(equal(decr(A),zero),equal(decr(B),zero))))))) :-
    !,
    true((
        mshare([[A],[B]]),
        linear(A),
        linear(B),
        shlin2([([A],[A]),([B],[B])])
    )).
eq(boyer_difference(X,Y),boyer_difference(Z,Y),if(lessp(X,Y),not(lessp(Y,Z)),if(lessp(Z,Y),not(lessp(Y,X)),equal(fix(X),fix(Z))))) :-
    !,
    true((
        mshare([[X],[Y],[Z]]),
        linear(X),
        linear(Y),
        linear(Z),
        shlin2([([X],[X]),([Y],[Y]),([Z],[Z])])
    )).
eq(lessp(X,Y),Z,if(lessp(X,Y),equal(t,Z),equal(f,Z))).

:- true pred exp(I,_A,_B)
   : ( mshare([[I],[_A],[_B]]),
       linear(I), linear(_A), linear(_B), shlin2([([I],[I]),([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[I,_B],[_A,_B]]),
        linear(I), linear(_A), shlin2([([I,_B],[I]),([_A,_B],[_A,_B])]) ).

exp(I,myplus(J,K),times(exp(I,J),exp(I,K))) :-
    !,
    true((
        mshare([[I],[J],[K]]),
        linear(I),
        linear(J),
        linear(K),
        shlin2([([I],[I]),([J],[J]),([K],[K])])
    )).
exp(I,times(J,K),exp(exp(I,J),K)).

:- true pred gcd(X,Y,_A)
   : ( mshare([[X],[Y],[_A]]),
       linear(X), linear(Y), linear(_A), shlin2([([X],[X]),([Y],[Y]),([_A],[_A])]) )
   => ( mshare([[X,Y,_A],[X,_A],[Y,_A]]),
        linear(X), linear(Y), linear(_A), shlin2([([X,Y,_A],[X,Y,_A]),([X,_A],[X,_A]),([Y,_A],[Y,_A])]) ).

gcd(X,Y,gcd(Y,X)) :-
    !,
    true((
        mshare([[X],[Y]]),
        linear(X),
        linear(Y),
        shlin2([([X],[X]),([Y],[Y])])
    )).
gcd(times(X,Z),times(Y,Z),times(Z,gcd(X,Y))).

:- true pred mylength(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_A), linear(_B), shlin2([([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[_A],[_A,_B]]),
        linear(_A), linear(_B), shlin2([([_A],[_A]),([_A,_B],[_A,_B])]) ).

mylength(reverse(X),length(X)).
mylength(cons(_1,cons(_2,cons(_3,cons(_4,cons(_5,cons(_6,X7)))))),myplus(6,length(X7))).

:- true pred lessp(_A,Y,_B)
   : ( mshare([[_A],[Y],[_B]]),
       linear(_A), linear(Y), linear(_B), shlin2([([_A],[_A]),([Y],[Y]),([_B],[_B])]) )
   => ( mshare([[_A],[_A,Y],[_A,Y,_B],[_A,_B],[Y,_B]]),
        linear(_A), linear(Y), shlin2([([_A],[_A]),([_A,Y],[_A,Y]),([_A,Y,_B],[_A,Y]),([_A,_B],[_A]),([Y,_B],[Y,_B])]) ).

lessp(remainder(_1,Y),Y,not(zerop(Y))) :-
    !,
    true((
        mshare([[Y],[_1]]),
        linear(Y),
        linear(_1),
        shlin2([([Y],[Y]),([_1],[_1])])
    )).
lessp(quotient(I,J),I,and(not(zerop(I)),or(zerop(J),not(equal(J,1))))) :-
    !,
    true((
        mshare([[I],[J]]),
        linear(I),
        linear(J),
        shlin2([([I],[I]),([J],[J])])
    )).
lessp(remainder(X,Y),X,and(not(zerop(Y)),and(not(zerop(X)),not(lessp(X,Y))))) :-
    !,
    true((
        mshare([[X],[Y]]),
        linear(X),
        linear(Y),
        shlin2([([X],[X]),([Y],[Y])])
    )).
lessp(myplus(X,Y),myplus(X,Z),lessp(Y,Z)) :-
    !,
    true((
        mshare([[X],[Y],[Z]]),
        linear(X),
        linear(Y),
        linear(Z),
        shlin2([([X],[X]),([Y],[Y]),([Z],[Z])])
    )).
lessp(times(X,Z),times(Y,Z),and(not(zerop(Z)),lessp(X,Y))) :-
    !,
    true((
        mshare([[X],[Z],[Y]]),
        linear(X),
        linear(Z),
        linear(Y),
        shlin2([([X],[X]),([Z],[Z]),([Y],[Y])])
    )).
lessp(Y,myplus(X,Y),not(zerop(X))) :-
    !,
    true((
        mshare([[Y],[X]]),
        linear(Y),
        linear(X),
        shlin2([([Y],[Y]),([X],[X])])
    )).
lessp(length(delete(X,L)),length(L),boyer_member(X,L)).

:- true pred meaning(_A,A,_B)
   : ( mshare([[_A],[A],[_B]]),
       linear(_A), linear(A), linear(_B), shlin2([([_A],[_A]),([A],[A]),([_B],[_B])]) )
   => ( mshare([[_A,_B],[A,_B]]),
        linear(_A), linear(A), shlin2([([_A,_B],[_A]),([A,_B],[A])]) ).

meaning(plus_tree(append(X,Y)),A,myplus(meaning(plus_tree(X),A),meaning(plus_tree(Y),A))) :-
    !,
    true((
        mshare([[A],[X],[Y]]),
        linear(A),
        linear(X),
        linear(Y),
        shlin2([([A],[A]),([X],[X]),([Y],[Y])])
    )).
meaning(plus_tree(plus_fringe(X)),A,fix(meaning(X,A))) :-
    !,
    true((
        mshare([[A],[X]]),
        linear(A),
        linear(X),
        shlin2([([A],[A]),([X],[X])])
    )).
meaning(plus_tree(delete(X,Y)),A,if(boyer_member(X,Y),boyer_difference(meaning(plus_tree(Y),A),meaning(X,A)),meaning(plus_tree(Y),A))).

:- true pred myboyer_member(X,_A,_B)
   : ( mshare([[X],[_A],[_B]]),
       linear(X), linear(_A), linear(_B), shlin2([([X],[X]),([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[X,_B],[_A,_B]]),
        linear(X), linear(_A), shlin2([([X,_B],[X]),([_A,_B],[_A,_B])]) ).

myboyer_member(X,append(A,B),or(boyer_member(X,A),boyer_member(X,B))) :-
    !,
    true((
        mshare([[X],[A],[B]]),
        linear(X),
        linear(A),
        linear(B),
        shlin2([([X],[X]),([A],[A]),([B],[B])])
    )).
myboyer_member(X,reverse(Y),boyer_member(X,Y)) :-
    !,
    true((
        mshare([[X],[Y]]),
        linear(X),
        linear(Y),
        shlin2([([X],[X]),([Y],[Y])])
    )).
myboyer_member(A,intersect(B,C),and(boyer_member(A,B),boyer_member(A,C))).

:- true pred my_nth(_A,_1,_B)
   : ( mshare([[_A],[_1],[_B]]),
       linear(_A), linear(_1), linear(_B), shlin2([([_A],[_A]),([_1],[_1]),([_B],[_B])]) )
   => ( mshare([[_A,_B],[_1],[_1,_B]]),
        linear(_A), linear(_1), shlin2([([_A,_B],[_A]),([_1],[_1]),([_1,_B],[_1])]) ).

my_nth(zero,_1,zero).
my_nth([],I,if(zerop(I),[],zero)).
my_nth(append(A,B),I,append(my_nth(A,I),my_nth(B,boyer_difference(I,length(A))))).

:- true pred myplus(X,Z,_A)
   : ( mshare([[X],[Z],[_A]]),
       linear(X), linear(Z), linear(_A), shlin2([([X],[X]),([Z],[Z]),([_A],[_A])]) )
   => ( mshare([[X,Z],[X,Z,_A],[X,_A],[Z,_A]]),
        linear(X), shlin2([([X,Z],[X]),([X,Z,_A],[X,Z,_A]),([X,_A],[X]),([Z,_A],[Z])]) ).

myplus(myplus(X,Y),Z,myplus(X,myplus(Y,Z))) :-
    !,
    true((
        mshare([[Z],[X],[Y]]),
        linear(Z),
        linear(X),
        linear(Y),
        shlin2([([Z],[Z]),([X],[X]),([Y],[Y])])
    )).
myplus(remainder(X,Y),times(Y,quotient(X,Y)),fix(X)) :-
    !,
    true((
        mshare([[X],[Y]]),
        linear(X),
        linear(Y),
        shlin2([([X],[X]),([Y],[Y])])
    )).
myplus(X,add1(Y),if(numberp(Y),add1(myplus(X,Y)),add1(X))).

:- true pred power_eval(_A,Base,_B)
   : ( mshare([[_A],[Base],[_B]]),
       linear(_A), linear(Base), linear(_B), shlin2([([_A],[_A]),([Base],[Base]),([_B],[_B])]) )
   => ( mshare([[_A,Base],[_A,Base,_B],[_A,_B]]),
        linear(Base), shlin2([([_A,Base],[Base]),([_A,Base,_B],[_A,Base]),([_A,_B],[_A,_B])]) ).

power_eval(big_plus1(L,I,Base),Base,myplus(power_eval(L,Base),I)) :-
    !,
    true((
        mshare([[Base],[L],[I]]),
        linear(Base),
        linear(L),
        linear(I),
        shlin2([([Base],[Base]),([L],[L]),([I],[I])])
    )).
power_eval(power_rep(I,Base),Base,fix(I)) :-
    !,
    true((
        mshare([[Base],[I]]),
        linear(Base),
        linear(I),
        shlin2([([Base],[Base]),([I],[I])])
    )).
power_eval(big_plus(X,Y,I,Base),Base,myplus(I,myplus(power_eval(X,Base),power_eval(Y,Base)))) :-
    !,
    true((
        mshare([[Base],[X],[Y],[I]]),
        linear(Base),
        linear(X),
        linear(Y),
        linear(I),
        shlin2([([Base],[Base]),([X],[X]),([Y],[Y]),([I],[I])])
    )).
power_eval(big_plus(power_rep(I,Base),power_rep(J,Base),zero,Base),Base,myplus(I,J)).

:- true pred quotient(_A,Y,_B)
   : ( mshare([[_A],[Y],[_B]]),
       linear(_A), linear(Y), linear(_B), shlin2([([_A],[_A]),([Y],[Y]),([_B],[_B])]) )
   => ( mshare([[_A,Y,_B],[_A,_B]]),
        linear(Y), linear(_B), shlin2([([_A,Y,_B],[_A,Y,_B]),([_A,_B],[_B])]) ).

quotient(myplus(X,myplus(X,Y)),2,myplus(X,quotient(Y,2))).
quotient(times(Y,X),Y,if(zerop(Y),zero,fix(X))).

:- true pred remainder(_1,X,_A)
   : ( mshare([[_1],[X],[_A]]),
       linear(_1), linear(X), linear(_A), shlin2([([_1],[_1]),([X],[X]),([_A],[_A])]) )
   => ( mshare([[_1],[_1,X]]),
        ground([_A]), linear(_1), linear(X), shlin2([([_1],[_1]),([_1,X],[_1,X])]) ).

remainder(_1,1,zero) :-
    !,
    true((
        mshare([[_1]]),
        linear(_1),
        shlin2([([_1],[_1])])
    )).
remainder(X,X,zero) :-
    !,
    true((
        mshare([[X]]),
        linear(X),
        shlin2([([X],[X])])
    )).
remainder(times(_1,Z),Z,zero) :-
    !,
    true((
        mshare([[Z],[_1]]),
        linear(Z),
        linear(_1),
        shlin2([([Z],[Z]),([_1],[_1])])
    )).
remainder(times(Y,_1),Y,zero).

:- true pred reverse_loop(X,Y,_A)
   : ( mshare([[X],[Y],[_A]]),
       linear(X), linear(Y), linear(_A), shlin2([([X],[X]),([Y],[Y]),([_A],[_A])]) )
   => ( mshare([[X,_A],[Y,_A]]),
        linear(X), linear(Y), linear(_A), shlin2([([X,_A],[X,_A]),([Y,_A],[Y,_A])]) ).

reverse_loop(X,Y,append(reverse(X),Y)) :-
    !,
    true((
        mshare([[X],[Y]]),
        linear(X),
        linear(Y),
        shlin2([([X],[X]),([Y],[Y])])
    )).
reverse_loop(X,[],reverse(X)).

:- true pred times(X,Z,_A)
   : ( mshare([[X],[Z],[_A]]),
       linear(X), linear(Z), linear(_A), shlin2([([X],[X]),([Z],[Z]),([_A],[_A])]) )
   => ( mshare([[X,_A],[Z,_A]]),
        linear(X), linear(Z), shlin2([([X,_A],[X]),([Z,_A],[Z])]) ).

times(X,myplus(Y,Z),myplus(times(X,Y),times(X,Z))) :-
    !,
    true((
        mshare([[X],[Y],[Z]]),
        linear(X),
        linear(Y),
        linear(Z),
        shlin2([([X],[X]),([Y],[Y]),([Z],[Z])])
    )).
times(times(X,Y),Z,times(X,times(Y,Z))) :-
    !,
    true((
        mshare([[Z],[X],[Y]]),
        linear(Z),
        linear(X),
        linear(Y),
        shlin2([([Z],[Z]),([X],[X]),([Y],[Y])])
    )).
times(X,boyer_difference(C,W),boyer_difference(times(C,X),times(W,X))) :-
    !,
    true((
        mshare([[X],[C],[W]]),
        linear(X),
        linear(C),
        linear(W),
        shlin2([([X],[X]),([C],[C]),([W],[W])])
    )).
times(X,add1(Y),if(numberp(Y),myplus(X,times(X,Y)),fix(X))).


