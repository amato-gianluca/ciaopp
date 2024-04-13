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
       ground([_B]), linear(_A) )
   => ( mshare([[_A],[_B]]),
        linear(_A), linear(_B) ).

:- true pred p(A)
   : ( (A=[_A|_B]),
       mshare([[_A],[_B]]),
       linear(_A), linear(_B) )
   => ( mshare([[_A],[_B]]),
        linear(_A), linear(_B) ).

p(A).
p(A) :-
    true((mshare([[A],[_1]]),linear(A),linear(_1);mshare([[_1]]),ground([A]),linear(_1))),
    p([_1|A]),
    true((mshare([[A],[_1]]),linear(A),linear(_1);mshare([[_1]]),ground([A]),linear(_1))).


