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
       ground([_B]) )
   => ( mshare([[_A]]),
        ground([_B]) ).

:- true pred p(A)
   : ( (A=[_A|_B]),
       mshare([[_A],[_B]]) )
   => mshare([[_A],[_A,_B],[_B]]).

p(A).
p(A) :-
    true((mshare([[A],[_1]]);mshare([[_1]]),ground([A]))),
    p([_1|A]),
    true((mshare([[A],[A,_1],[_1]]);mshare([[_1]]),ground([A]))).


