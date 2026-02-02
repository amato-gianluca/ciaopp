:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(moded_path,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    'top/0/1/$disj/1',
    true(true).

:- true pred 'top/0/1/$disj/1'.

'top/0/1/$disj/1' :-
    true(true),
    'top/0/1/$disj/1/0/1/$disj/1',
    !,
    true(true),
    fail,
    true(fails(_)).
'top/0/1/$disj/1'.

:- true pred 'top/0/1/$disj/1/0/1/$disj/1'.

'top/0/1/$disj/1/0/1/$disj/1' :-
    true((
        mshare([[T]]),
        linear(T),
        shlin2([([T],[T])])
    )),
    path(a,e,T),
    true(ground([T])),
    ok_path(T),
    !,
    true(ground([T])),
    fail,
    true(fails(_)).
'top/0/1/$disj/1/0/1/$disj/1'.

:- true pred path(X,Y,C)
   : ( (X=a), (Y=e),
       mshare([[C]]),
       linear(C), shlin2([([C],[C])]) )
   => ground([C]).

:- true pred path(X,Y,C)
   : ( mshare([[X],[C]]),
       ground([Y]), linear(X), linear(C), shlin2([([X],[X]),([C],[C])]) )
   => ( mshare([[X]]),
        ground([Y,C]), linear(X), shlin2([([X],[X])]) ).

path(X,X,one).
path(X,Y,C) :-
    true((mshare([[X],[C],[Z],[A],[B]]),ground([Y]),linear(X),linear(C),linear(Z),linear(A),linear(B),shlin2([([X],[X]),([C],[C]),([Z],[Z]),([A],[A]),([B],[B])]);mshare([[C],[Z],[A],[B]]),ground([X,Y]),linear(C),linear(Z),linear(A),linear(B),shlin2([([C],[C]),([Z],[Z]),([A],[A]),([B],[B])]))),
    edge(X,Z,A),
    true((mshare([[X],[C],[Z],[B]]),ground([Y,A]),linear(X),linear(C),linear(Z),linear(B),shlin2([([X],[X]),([C],[C]),([Z],[Z]),([B],[B])]);mshare([[C],[Z],[B]]),ground([X,Y,A]),linear(C),linear(Z),linear(B),shlin2([([C],[C]),([Z],[Z]),([B],[B])]))),
    path(Z,Y,B),
    true((mshare([[X],[C],[Z]]),ground([Y,A,B]),linear(X),linear(C),linear(Z),shlin2([([X],[X]),([C],[C]),([Z],[Z])]);mshare([[C],[Z]]),ground([X,Y,A,B]),linear(C),linear(Z),shlin2([([C],[C]),([Z],[Z])]))),
    and(A,B,C),
    true((mshare([[X],[Z]]),ground([Y,C,A,B]),linear(X),linear(Z),shlin2([([X],[X]),([Z],[Z])]);mshare([[Z]]),ground([X,Y,C,A,B]),linear(Z),shlin2([([Z],[Z])]))).
path(A,B,zero) :-
    true((mshare([[A]]),ground([B]),linear(A),shlin2([([A],[A])]);ground([A,B]))),
    nonvar(A),
    true((mshare([[A]]),ground([B]),linear(A),shlin2([([A],[A])]);ground([A,B]))),
    nonvar(B),
    true((mshare([[A]]),ground([B]),linear(A),shlin2([([A],[A])]);ground([A,B]))).

:- true pred edge(A,B,_A)
   : ( mshare([[A],[B],[_A]]),
       linear(A), linear(B), linear(_A), shlin2([([A],[A]),([B],[B]),([_A],[_A])]) )
   => ( mshare([[A],[B]]),
        ground([_A]), linear(A), linear(B), shlin2([([A],[A]),([B],[B])]) ).

:- true pred edge(A,B,_A)
   : ( mshare([[B],[_A]]),
       ground([A]), linear(B), linear(_A), shlin2([([B],[B]),([_A],[_A])]) )
   => ( mshare([[B]]),
        ground([A,_A]), linear(B), shlin2([([B],[B])]) ).

edge(a,b,e(a,b)).
edge(b,e,e(b,e)).
edge(a,e,e(a,e)).
edge(A,B,zero) :-
    true((mshare([[A],[B]]),linear(A),linear(B),shlin2([([A],[A]),([B],[B])]);mshare([[B]]),ground([A]),linear(B),shlin2([([B],[B])]))),
    nonvar(A),
    true((mshare([[A],[B]]),linear(A),linear(B),shlin2([([A],[A]),([B],[B])]);mshare([[B]]),ground([A]),linear(B),shlin2([([B],[B])]))),
    nonvar(B),
    true((mshare([[A],[B]]),linear(A),linear(B),shlin2([([A],[A]),([B],[B])]);mshare([[B]]),ground([A]),linear(B),shlin2([([B],[B])]))).

or(zero,B,B) :- !.
or(B,zero,B) :- !.
or(one,one,one) :- !.
or(A,A,A) :- !.
or(A,B,or(A,B)).

:- true pred and(B,_1,_2)
   : ( mshare([[_2]]),
       ground([B,_1]), linear(_2), shlin2([([_2],[_2])]) )
   => ground([B,_1,_2]).

and(zero,_1,_2) :-
    !,
    true((
        mshare([[_2]]),
        ground([_1]),
        linear(_2),
        shlin2([([_2],[_2])])
    )),
    fail,
    true(fails(_)).
and(_1,zero,_2) :-
    !,
    true((
        mshare([[_2]]),
        ground([_1]),
        linear(_2),
        shlin2([([_2],[_2])])
    )),
    fail,
    true(fails(_)).
and(one,B,B) :-
    !,
    true(ground([B])).
and(B,one,B) :-
    !,
    true(ground([B])).
and(A,A,A) :-
    !,
    true(ground([A])).
and(A,B,and(A,B)).

:- true pred ok_path(_A)
   : ground([_A])
   => ground([_A]).

ok_path(or(e(a,e),and(e(a,b),e(b,e)))).
ok_path(or(and(e(a,b),e(b,e)),e(a,e))).


