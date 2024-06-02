:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(fib,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true((
        mshare([[F]]),
        linear(F),
        shlin2([([F],[F])])
    )),
    fib(1000,F),
    true(ground([F])),
    F==70330367711422815821835254877183549770181269836358732742604905087154537118196933579742249494562611733487750449241765991088186363265450223647106012053374121273867339111198139373125598767690091902245245323403501,
    true(ground([F])).

:- true pred fib(N,F)
   : ( (N=1000),
       mshare([[F]]),
       linear(F), shlin2([([F],[F])]) )
   => ground([F]).

:- true pred fib(N,F)
   : ( mshare([[F]]),
       ground([N]), linear(F), shlin2([([F],[F])]) )
   => ground([N,F]).

fib(0,1) :-
    !,
    true(true).
fib(1,1) :-
    !,
    true(true).
fib(N,F) :-
    true((
        mshare([[F],[N1],[N2],[F1],[F2]]),
        ground([N]),
        linear(F),
        linear(N1),
        linear(N2),
        linear(F1),
        linear(F2),
        shlin2([([F],[F]),([N1],[N1]),([N2],[N2]),([F1],[F1]),([F2],[F2])])
    )),
    N>1,
    true((
        mshare([[F],[N1],[N2],[F1],[F2]]),
        ground([N]),
        linear(F),
        linear(N1),
        linear(N2),
        linear(F1),
        linear(F2),
        shlin2([([F],[F]),([N1],[N1]),([N2],[N2]),([F1],[F1]),([F2],[F2])])
    )),
    N1 is N-1,
    true((
        mshare([[F],[N2],[F1],[F2]]),
        ground([N,N1]),
        linear(F),
        linear(N2),
        linear(F1),
        linear(F2),
        shlin2([([F],[F]),([N2],[N2]),([F1],[F1]),([F2],[F2])])
    )),
    N2 is N-2,
    true((
        mshare([[F],[F1],[F2]]),
        ground([N,N1,N2]),
        linear(F),
        linear(F1),
        linear(F2),
        shlin2([([F],[F]),([F1],[F1]),([F2],[F2])])
    )),
    fib(N1,F1),
    true((
        mshare([[F],[F2]]),
        ground([N,N1,N2,F1]),
        linear(F),
        linear(F2),
        shlin2([([F],[F]),([F2],[F2])])
    )),
    fib(N2,F2),
    true((
        mshare([[F]]),
        ground([N,N1,N2,F1,F2]),
        linear(F),
        shlin2([([F],[F])])
    )),
    F is F1+F2,
    true(ground([N,F,N1,N2,F1,F2])).


