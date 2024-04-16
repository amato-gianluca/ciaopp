:- module(_1,[],[assertions,nativeprops]).

:- set_prolog_flag(single_var_warnings,off).

:- entry p(A)
   : ground(A).

:- true pred p(A)
   : ground([A])
   => ground([A]).

:- true pred p(A)
   : ( (A=[_A|_B]),
       mshare([[_A]]),
       ground([_B]), linear(_A), shlin2([([_A],[_A])]) )
   => ( mshare([[_A]]),
        ground([_B]), linear(_A), shlin2([([_A],[_A])]) ).

:- true pred p(A)
   : ( (A=[_A|_B]),
       mshare([[_A],[_B]]),
       linear(_A), linear(_B), shlin2([([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[_A],[_B]]),
        linear(_A), linear(_B), shlin2([([_A],[_A]),([_B],[_B])]) ).

p(A).
p(A) :-
    true((mshare([[A],[_1]]),linear(A),linear(_1),shlin2([([A],[A]),([_1],[_1])]);mshare([[_1]]),ground([A]),linear(_1),shlin2([([_1],[_1])]))),
    p([_1|A]),
    true((mshare([[A],[_1]]),linear(A),linear(_1),shlin2([([A],[A]),([_1],[_1])]);mshare([[_1]]),ground([A]),linear(_1),shlin2([([_1],[_1])]))).


