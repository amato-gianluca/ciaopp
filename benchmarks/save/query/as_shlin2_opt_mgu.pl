:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(query,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    query,
    true(true).

:- true pred query.

query :-
    true((
        mshare([[_1]]),
        linear(_1),
        shlin2([([_1],[_1])])
    )),
    query(_1),
    true(ground([_1])),
    fail,
    true(fails(_)).
query.

:- true pred query(_A)
   : ( mshare([[_A]]),
       linear(_A), shlin2([([_A],[_A])]) )
   => ground([_A]).

query([C1,D1,C2,D2]) :-
    true((
        mshare([[C1],[D1],[C2],[D2],[T1],[T2]]),
        linear(C1),
        linear(D1),
        linear(C2),
        linear(D2),
        linear(T1),
        linear(T2),
        shlin2([([C1],[C1]),([D1],[D1]),([C2],[C2]),([D2],[D2]),([T1],[T1]),([T2],[T2])])
    )),
    density(C1,D1),
    true((
        mshare([[C2],[D2],[T1],[T2]]),
        ground([C1,D1]),
        linear(C2),
        linear(D2),
        linear(T1),
        linear(T2),
        shlin2([([C2],[C2]),([D2],[D2]),([T1],[T1]),([T2],[T2])])
    )),
    density(C2,D2),
    true((
        mshare([[T1],[T2]]),
        ground([C1,D1,C2,D2]),
        linear(T1),
        linear(T2),
        shlin2([([T1],[T1]),([T2],[T2])])
    )),
    D1>D2,
    true((
        mshare([[T1],[T2]]),
        ground([C1,D1,C2,D2]),
        linear(T1),
        linear(T2),
        shlin2([([T1],[T1]),([T2],[T2])])
    )),
    T1 is 20*D1,
    true((
        mshare([[T2]]),
        ground([C1,D1,C2,D2,T1]),
        linear(T2),
        shlin2([([T2],[T2])])
    )),
    T2 is 21*D2,
    true(ground([C1,D1,C2,D2,T1,T2])),
    T1<T2,
    true(ground([C1,D1,C2,D2,T1,T2])).

:- true pred density(C,D)
   : ( mshare([[C],[D]]),
       linear(C), linear(D), shlin2([([C],[C]),([D],[D])]) )
   => ground([C,D]).

density(C,D) :-
    true((
        mshare([[C],[D],[P],[A]]),
        linear(C),
        linear(D),
        linear(P),
        linear(A),
        shlin2([([C],[C]),([D],[D]),([P],[P]),([A],[A])])
    )),
    pop(C,P),
    true((
        mshare([[D],[A]]),
        ground([C,P]),
        linear(D),
        linear(A),
        shlin2([([D],[D]),([A],[A])])
    )),
    area(C,A),
    true((
        mshare([[D]]),
        ground([C,P,A]),
        linear(D),
        shlin2([([D],[D])])
    )),
    D is P*100//A,
    true(ground([C,D,P,A])).

:- true pred pop(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_A), linear(_B), shlin2([([_A],[_A]),([_B],[_B])]) )
   => ground([_A,_B]).

pop(china,8250).
pop(india,5863).
pop(ussr,2521).
pop(usa,2119).
pop(indonesia,1276).
pop(japan,1097).
pop(brazil,1042).
pop(bangladesh,750).
pop(pakistan,682).
pop(w_germany,620).
pop(nigeria,613).
pop(mexico,581).
pop(uk,559).
pop(italy,554).
pop(france,525).
pop(philippines,415).
pop(thailand,410).
pop(turkey,383).
pop(egypt,364).
pop(spain,352).
pop(poland,337).
pop(s_korea,335).
pop(iran,320).
pop(ethiopia,272).
pop(argentina,251).

:- true pred area(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]), linear(_B), shlin2([([_B],[_B])]) )
   => ground([_A,_B]).

area(china,3380).
area(india,1139).
area(ussr,8708).
area(usa,3609).
area(indonesia,570).
area(japan,148).
area(brazil,3288).
area(bangladesh,55).
area(pakistan,311).
area(w_germany,96).
area(nigeria,373).
area(mexico,764).
area(uk,86).
area(italy,116).
area(france,213).
area(philippines,90).
area(thailand,200).
area(turkey,296).
area(egypt,386).
area(spain,190).
area(poland,121).
area(s_korea,37).
area(iran,628).
area(ethiopia,350).
area(argentina,1080).

