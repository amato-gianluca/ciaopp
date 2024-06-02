:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(pingpong,_1) :-
    !,
    call(_1).

enable_tabling.

:- entry top.

:- true pred top.

top :-
    true((
        mshare([[_1]]),
        var(_1),
        linear(_1)
    )),
    d(_1),
    true(ground([_1])),
    fail,
    true(fails(_)).
top.

:- true pred d(X)
   : ( mshare([[X]]),
       var(X), linear(X) )
   => ground([X]).

d(X) :-
    true((
        mshare([[X],[Y]]),
        var(X),
        var(Y),
        linear(X),
        linear(Y)
    )),
    e(Y),
    true((
        mshare([[X]]),
        var(X),
        ground([Y]),
        linear(X)
    )),
    Y<20000,
    true((
        mshare([[X]]),
        var(X),
        ground([Y]),
        linear(X)
    )),
    X is Y+1,
    true(ground([X,Y])).
d(0).

:- true pred e(X)
   : ( mshare([[X]]),
       var(X), linear(X) )
   => ground([X]).

e(X) :-
    true((
        mshare([[X],[Y]]),
        var(X),
        var(Y),
        linear(X),
        linear(Y)
    )),
    d(Y),
    true((
        mshare([[X]]),
        var(X),
        ground([Y]),
        linear(X)
    )),
    Y<20000,
    true((
        mshare([[X]]),
        var(X),
        ground([Y]),
        linear(X)
    )),
    X is Y+1,
    true(ground([X,Y])).
e(0).


