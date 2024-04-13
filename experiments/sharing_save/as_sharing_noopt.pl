:- module(_2,[],[assertions,nativeprops]).

:- set_prolog_flag(single_var_warnings,off).

:- entry example1(X,Y,Z)
   : mshare([X,Y,Z],[[X,Y],[Y,Z]]).

:- true pred example1(X,Y,Z)
   : mshare([[X,Y],[Y,Z]])
   => ground([X,Y,Z]).

example1(t(U),V,W) :-
    true(mshare([[V,W],[V,W,U],[V,U]])),
    nothing,
    true(ground([V,W,U])).

:- entry example2(X,Y,Z)
   : mshare([X,Y,Z],[[X,Y],[X,Z]]).

:- true pred example2(X,Y,Z)
   : mshare([[X,Y],[X,Z]])
   => ground([X,Y,Z]).

example2(t(U,V),H,K) :-
    true(mshare([[H,K,U],[H,K,U,V],[H,K,V],[H,U],[H,U,V],[H,V],[K,U],[K,U,V],[K,V]])),
    nothing,
    true(ground([H,K,U,V])).

:- entry example3(X,Y,Z,W)
   : mshare([X,Y,Z,W],[[X,W],[X,Z],[Y,W],[Y,Z]]).

:- true pred example3(X,Y,Z,W)
   : mshare([[X,Z],[X,W],[Y,Z],[Y,W]])
   => ground([X,Y,Z,W]).

example3(f(U,H),f(U,K),S,T) :-
    true(mshare([[S,T,U],[S,T,U,H],[S,T,U,H,K],[S,T,U,K],[S,T,H],[S,T,H,K],[S,T,K],[S,U],[S,U,H],[S,U,H,K],[S,U,K],[S,H],[S,H,K],[S,K],[T,U],[T,U,H],[T,U,H,K],[T,U,K],[T,H],[T,H,K],[T,K]])),
    nothing,
    true(ground([S,T,U,H,K])).

:- entry example4(X,Y,Z)
   : mshare([X,Y,Z],[[X],[Y],[Z]]).

:- true pred example4(X,Y,Z)
   : mshare([[X],[Y],[Z]])
   => mshare([[X,Y],[X,Y,Z],[Y,Z]]).

example4(X,Y,Z) :-
    true(mshare([[X],[Y],[Z]])),
    example4bis(t(X),t(Y),t(Z)),
    true(mshare([[X,Y],[X,Y,Z],[Y,Z]])).

%% %% :- trust pred example4bis(X,Y,Z)
%% %%    : mshare([X,Y,Z],[[X],[Y],[Z]])
%% %%    => mshare([X,Y,Z],[[X,Y],[Y,Z]]).

:- check calls example4bis(X,Y,Z)
   : mshare([X,Y,Z],[[X],[Y],[Z]]).

:- trust success example4bis(X,Y,Z)
   : mshare([X,Y,Z],[[X],[Y],[Z]])
   => mshare([X,Y,Z],[[X,Y],[Y,Z]]).

:- true pred example4bis(X,Y,Z)
   : ( (X=t(_A)), (Y=t(_B)), (Z=t(_C)),
       mshare([[_A],[_B],[_C]]) )
   => mshare([[_A,_B],[_A,_B,_C],[_B,_C]]).

example4bis(X,Y,Z) :-
    true(mshare([[X],[Y],[Z]])),
    Y=f(X,Z),
    true(mshare([[X,Y],[X,Y,Z],[Y,Z]])).

:- true pred nothing.

nothing.


