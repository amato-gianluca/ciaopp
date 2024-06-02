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
        var(_1),
        linear(_1)
    )),
    query(_1),
    true(ground([_1])),
    fail,
    true(fails(_)).
query.

:- true pred query(_A)
   : ( mshare([[_A]]),
       var(_A), linear(_A) )
   => ground([_A]).

query([C1,D1,C2,D2]) :-
    true((
        mshare([[C1],[D1],[C2],[D2],[T1],[T2]]),
        var(C1),
        var(D1),
        var(C2),
        var(D2),
        var(T1),
        var(T2),
        linear(C1),
        linear(D1),
        linear(C2),
        linear(D2),
        linear(T1),
        linear(T2)
    )),
    density(C1,D1),
    true((
        mshare([[C2],[D2],[T1],[T2]]),
        var(C2),
        var(D2),
        var(T1),
        var(T2),
        ground([C1,D1]),
        linear(C2),
        linear(D2),
        linear(T1),
        linear(T2)
    )),
    density(C2,D2),
    true((
        mshare([[T1],[T2]]),
        var(T1),
        var(T2),
        ground([C1,D1,C2,D2]),
        linear(T1),
        linear(T2)
    )),
    D1>D2,
    true((
        mshare([[T1],[T2]]),
        var(T1),
        var(T2),
        ground([C1,D1,C2,D2]),
        linear(T1),
        linear(T2)
    )),
    T1 is 20*D1,
    true((
        mshare([[T2]]),
        var(T2),
        ground([C1,D1,C2,D2,T1]),
        linear(T2)
    )),
    T2 is 21*D2,
    true(ground([C1,D1,C2,D2,T1,T2])),
    T1<T2,
    true(ground([C1,D1,C2,D2,T1,T2])).

:- true pred density(C,D)
   : ( mshare([[C],[D]]),
       var(C), var(D), linear(C), linear(D) )
   => ground([C,D]).

density(C,D) :-
    true((
        mshare([[C],[D],[P],[A]]),
        var(C),
        var(D),
        var(P),
        var(A),
        linear(C),
        linear(D),
        linear(P),
        linear(A)
    )),
    pop(C,P),
    true((
        mshare([[D],[A]]),
        var(D),
        var(A),
        ground([C,P]),
        linear(D),
        linear(A)
    )),
    area(C,A),
    true((
        mshare([[D]]),
        var(D),
        ground([C,P,A]),
        linear(D)
    )),
    D is P*100//A,
    true(ground([C,D,P,A])).

:- true pred pop(_A,_B)
   : ( mshare([[_A],[_B]]),
       var(_A), var(_B), linear(_A), linear(_B) )
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
       var(_B), ground([_A]), linear(_B) )
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


