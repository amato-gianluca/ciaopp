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
       var(_A), ground([_B]), linear(_A) )
   => ( mshare([[_A]]),
        ground([_B]) ).

:- true pred p(A)
   : ( (A=[_A|_B]),
       mshare([[_A],[_B]]),
       var(_A), linear(_A) )
   => mshare([[_A],[_A,_B],[_B]]).

p(A).
p(A) :-
    true((mshare([[A],[_1]]),var(_1),linear(_1);mshare([[_1]]),var(_1),ground([A]),linear(_1))),
    p([_1|A]),
    true((mshare([[A],[A,_1],[_1]]);mshare([[_1]]),ground([A]))).


