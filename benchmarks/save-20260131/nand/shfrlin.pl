:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

:- dynamic state_/2.

'\006\call_in_module'(nand,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    main(0),
    true(true).

:- true pred main(N)
   : (N=0).

main(N) :-
    true((
        mshare([[NumVars],[NumGs],[Gs],[NumGs2],[Gs2]]),
        var(NumVars),
        var(NumGs),
        var(Gs),
        var(NumGs2),
        var(Gs2),
        ground([N]),
        linear(NumVars),
        linear(NumGs),
        linear(Gs),
        linear(NumGs2),
        linear(Gs2)
    )),
    init_state(N,NumVars,NumGs,Gs),
    true((
        mshare([[NumGs2],[Gs2]]),
        var(NumGs2),
        var(Gs2),
        ground([N,NumVars,NumGs,Gs]),
        linear(NumGs2),
        linear(Gs2)
    )),
    add_necessary_functions(NumVars,NumGs,Gs,NumGs2,Gs2),
    true(ground([N,NumVars,NumGs,Gs,NumGs2,Gs2])),
    test_bounds(NumVars,NumGs2,Gs2),
    true(ground([N,NumVars,NumGs,Gs,NumGs2,Gs2])),
    search(NumVars,NumGs2,Gs2),
    true(fails(_)).
main(_1).

:- true pred init_state(_A,_B,_C,_D)
   : ( mshare([[_B],[_C],[_D]]),
       var(_B), var(_C), var(_D), ground([_A]), linear(_B), linear(_C), linear(_D) )
   => ground([_A,_B,_C,_D]).

init_state(0,2,3,[function(2,[1,2],[0,3],[],[],[],[],[]),function(1,[2,3],[0,1],[],[],[],[],[]),function(0,[1,3],[0,2],[],[],[],[],[])]) :-
    true((
        mshare([[_1],[_2]]),
        var(_1),
        var(_2),
        linear(_1),
        linear(_2)
    )),
    update_bounds(_1,100,_2),
    true((
        mshare([[_1],[_2]]),
        var(_1),
        var(_2),
        linear(_1),
        linear(_2)
    )).
init_state(1,3,4,[function(3,[3,5,6,7],[0,1,2,4],[],[],[],[],[]),function(2,[4,5,6,7],[0,1,2,3],[],[],[],[],[]),function(1,[2,3,6,7],[0,1,4,5],[],[],[],[],[]),function(0,[1,3,5,7],[0,2,4,6],[],[],[],[],[])]) :-
    true((
        mshare([[_1],[_2]]),
        var(_1),
        var(_2),
        linear(_1),
        linear(_2)
    )),
    update_bounds(_1,100,_2),
    true((
        mshare([[_1],[_2]]),
        var(_1),
        var(_2),
        linear(_1),
        linear(_2)
    )).
init_state(2,3,4,[function(3,[1,2,4,6,7],[0,3,5],[],[],[],[],[]),function(2,[4,5,6,7],[0,1,2,3],[],[],[],[],[]),function(1,[2,3,6,7],[0,1,4,5],[],[],[],[],[]),function(0,[1,3,5,7],[0,2,4,6],[],[],[],[],[])]) :-
    true((
        mshare([[_1],[_2]]),
        var(_1),
        var(_2),
        linear(_1),
        linear(_2)
    )),
    update_bounds(_1,100,_2),
    true((
        mshare([[_1],[_2]]),
        var(_1),
        var(_2),
        linear(_1),
        linear(_2)
    )).
init_state(3,3,4,[function(3,[1,2,4,7],[0,3,5,6],[],[],[],[],[]),function(2,[4,5,6,7],[0,1,2,3],[],[],[],[],[]),function(1,[2,3,6,7],[0,1,4,5],[],[],[],[],[]),function(0,[1,3,5,7],[0,2,4,6],[],[],[],[],[])]) :-
    true((
        mshare([[_1],[_2]]),
        var(_1),
        var(_2),
        linear(_1),
        linear(_2)
    )),
    update_bounds(_1,100,_2),
    true((
        mshare([[_1],[_2]]),
        var(_1),
        var(_2),
        linear(_1),
        linear(_2)
    )).
init_state(4,3,5,[function(4,[3,5,6,7],[0,1,2,4],[],[],[],[],[]),function(3,[1,2,4,7],[0,3,5,6],[],[],[],[],[]),function(2,[4,5,6,7],[0,1,2,3],[],[],[],[],[]),function(1,[2,3,6,7],[0,1,4,5],[],[],[],[],[]),function(0,[1,3,5,7],[0,2,4,6],[],[],[],[],[])]) :-
    true((
        mshare([[_1],[_2]]),
        var(_1),
        var(_2),
        linear(_1),
        linear(_2)
    )),
    update_bounds(_1,100,_2),
    true((
        mshare([[_1],[_2]]),
        var(_1),
        var(_2),
        linear(_1),
        linear(_2)
    )).
init_state(5,5,8,[function(7,[1,3,4,6,9,11,12,14,16,18,21,23,24,26,29,31],[0,2,5,7,8,10,13,15,17,19,20,22,25,27,28,30],[],[],[],[],[]),function(6,[2,3,5,6,8,9,12,15,17,18,20,21,24,27,30,31],[0,1,4,7,10,11,13,14,16,19,22,23,25,26,28,29],[],[],[],[],[]),function(5,[7,10,11,13,14,15,19,22,23,25,26,27,28,29,30,31],[0,1,2,3,4,5,6,8,9,12,16,17,18,20,21,24],[],[],[],[],[]),function(4,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[],[],[],[]),function(3,[8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31],[0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23],[],[],[],[],[]),function(2,[4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31],[0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27],[],[],[],[],[]),function(1,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31],[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29],[],[],[],[],[]),function(0,[1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31],[0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30],[],[],[],[],[])]) :-
    true((
        mshare([[_1],[_2]]),
        var(_1),
        var(_2),
        linear(_1),
        linear(_2)
    )),
    update_bounds(_1,21,_2),
    true((
        mshare([[_1],[_2]]),
        var(_1),
        var(_2),
        linear(_1),
        linear(_2)
    )).

:- true pred search(NumVars,NumGsIn,GsIn)
   : ground([NumVars,NumGsIn,GsIn])
   + fails.

search(NumVars,NumGsIn,GsIn) :-
    true((
        mshare([[Gj],[Vector],[NumGs],[Gs],[NumGsOut],[GsOut]]),
        var(Gj),
        var(Vector),
        var(NumGs),
        var(Gs),
        var(NumGsOut),
        var(GsOut),
        ground([NumVars,NumGsIn,GsIn]),
        linear(Gj),
        linear(Vector),
        linear(NumGs),
        linear(Gs),
        linear(NumGsOut),
        linear(GsOut)
    )),
    select_vector(NumVars,NumGsIn,GsIn,Gj,Vector),
    !,
    true((
        mshare([[NumGs],[Gs],[NumGsOut],[GsOut]]),
        var(NumGs),
        var(Gs),
        var(NumGsOut),
        var(GsOut),
        ground([NumVars,NumGsIn,GsIn,Gj,Vector]),
        linear(NumGs),
        linear(Gs),
        linear(NumGsOut),
        linear(GsOut)
    )),
    cover_vector(NumVars,NumGsIn,GsIn,Gj,Vector,NumGs,Gs),
    true((
        mshare([[NumGsOut],[GsOut]]),
        var(NumGsOut),
        var(GsOut),
        ground([NumVars,NumGsIn,GsIn,Gj,Vector,NumGs,Gs]),
        linear(NumGsOut),
        linear(GsOut)
    )),
    add_necessary_functions(NumVars,NumGs,Gs,NumGsOut,GsOut),
    true(ground([NumVars,NumGsIn,GsIn,Gj,Vector,NumGs,Gs,NumGsOut,GsOut])),
    test_bounds(NumVars,NumGsOut,GsOut),
    true(ground([NumVars,NumGsIn,GsIn,Gj,Vector,NumGs,Gs,NumGsOut,GsOut])),
    search(NumVars,NumGsOut,GsOut),
    true(fails(_)).
search(NumVars,NumGs,Gs) :-
    true(ground([NumVars,NumGs,Gs])),
    update_bounds(NumVars,NumGs,Gs),
    true(ground([NumVars,NumGs,Gs])),
    fail,
    true(fails(_)).

:- true pred select_vector(NumVars,NumGs,Gs,Gj,Vector)
   : ( mshare([[Gj],[Vector]]),
       var(Gj), var(Vector), ground([NumVars,NumGs,Gs]), linear(Gj), linear(Vector) )
   => ground([NumVars,NumGs,Gs,Gj,Vector]).

select_vector(NumVars,NumGs,Gs,Gj,Vector) :-
    true((
        mshare([[Gj],[Vector],[Type],[_1]]),
        var(Gj),
        var(Vector),
        var(Type),
        var(_1),
        ground([NumVars,NumGs,Gs]),
        linear(Gj),
        linear(Vector),
        linear(Type),
        linear(_1)
    )),
    select_vector(Gs,NumVars,NumGs,Gs,dummy,0,nf,999,Gj,Vector,Type,_1),
    !,
    true(ground([NumVars,NumGs,Gs,Gj,Vector,Type,_1])),
    'select_vector/5/1/$disj/1'(Type),
    true(ground([NumVars,NumGs,Gs,Gj,Vector,Type,_1])),
    'select_vector/5/1/$disj/2'(Type),
    true(ground([NumVars,NumGs,Gs,Gj,Vector,Type,_1])).

:- true pred 'select_vector/5/1/$disj/1'(Type)
   : ground([Type])
   => ground([Type]).

'select_vector/5/1/$disj/1'(Type) :-
    true(ground([Type])),
    Type=cov,
    !,
    true(ground([Type])),
    fail,
    true(fails(_)).
'select_vector/5/1/$disj/1'(Type).

:- true pred 'select_vector/5/1/$disj/2'(Type)
   : ground([Type])
   => ground([Type]).

'select_vector/5/1/$disj/2'(Type) :-
    true(ground([Type])),
    Type=nf,
    !,
    true(ground([Type])),
    fail,
    true(fails(_)).
'select_vector/5/1/$disj/2'(Type).

:- true pred select_vector(_A,NumVars,_1,_2,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout)
   : ( (_A=_2), (Gj=dummy), (V=0), (Type=nf), (N=999),
       mshare([[GjOut],[Vout],[TypeOut],[Nout]]),
       var(GjOut), var(Vout), var(TypeOut), var(Nout), ground([_A,NumVars,_1]), linear(GjOut), linear(Vout), linear(TypeOut), linear(Nout) )
   => ground([_A,NumVars,_1,GjOut,Vout,TypeOut,Nout]).

:- true pred select_vector(_A,NumVars,_1,_2,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout)
   : ( mshare([[GjOut],[Vout],[TypeOut],[Nout]]),
       var(GjOut), var(Vout), var(TypeOut), var(Nout), ground([_A,NumVars,_1,_2,Gj,V,Type,N]), linear(GjOut), linear(Vout), linear(TypeOut), linear(Nout) )
   => ground([_A,NumVars,_1,_2,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout]).

select_vector([Gk|_3],NumVars,_1,_2,Gj,V,Type,N,Gj,V,Type,N) :-
    true((
        mshare([[K]]),
        var(K),
        ground([NumVars,_1,_2,Gj,V,Type,N,Gk,_3]),
        linear(K)
    )),
    function_number(Gk,K),
    true(ground([NumVars,_1,_2,Gj,V,Type,N,Gk,_3,K])),
    K<NumVars,
    true(ground([NumVars,_1,_2,Gj,V,Type,N,Gk,_3,K])).
select_vector([Gk|Gks],NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,GjOut,Vout,TypeOut,Nout) :-
    true((
        mshare([[GjOut],[Vout],[TypeOut],[Nout],[K],[Tk],[Gj],[V],[Type],[N]]),
        var(GjOut),
        var(Vout),
        var(TypeOut),
        var(Nout),
        var(K),
        var(Tk),
        var(Gj),
        var(V),
        var(Type),
        var(N),
        ground([NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,Gk,Gks]),
        linear(GjOut),
        linear(Vout),
        linear(TypeOut),
        linear(Nout),
        linear(K),
        linear(Tk),
        linear(Gj),
        linear(V),
        linear(Type),
        linear(N)
    )),
    function_number(Gk,K),
    true((
        mshare([[GjOut],[Vout],[TypeOut],[Nout],[Tk],[Gj],[V],[Type],[N]]),
        var(GjOut),
        var(Vout),
        var(TypeOut),
        var(Nout),
        var(Tk),
        var(Gj),
        var(V),
        var(Type),
        var(N),
        ground([NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,Gk,Gks,K]),
        linear(GjOut),
        linear(Vout),
        linear(TypeOut),
        linear(Nout),
        linear(Tk),
        linear(Gj),
        linear(V),
        linear(Type),
        linear(N)
    )),
    K>=NumVars,
    true((
        mshare([[GjOut],[Vout],[TypeOut],[Nout],[Tk],[Gj],[V],[Type],[N]]),
        var(GjOut),
        var(Vout),
        var(TypeOut),
        var(Nout),
        var(Tk),
        var(Gj),
        var(V),
        var(Type),
        var(N),
        ground([NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,Gk,Gks,K]),
        linear(GjOut),
        linear(Vout),
        linear(TypeOut),
        linear(Nout),
        linear(Tk),
        linear(Gj),
        linear(V),
        linear(Type),
        linear(N)
    )),
    true_set(Gk,Tk),
    true((
        mshare([[GjOut],[Vout],[TypeOut],[Nout],[Gj],[V],[Type],[N]]),
        var(GjOut),
        var(Vout),
        var(TypeOut),
        var(Nout),
        var(Gj),
        var(V),
        var(Type),
        var(N),
        ground([NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,Gk,Gks,K,Tk]),
        linear(GjOut),
        linear(Vout),
        linear(TypeOut),
        linear(Nout),
        linear(Gj),
        linear(V),
        linear(Type),
        linear(N)
    )),
    select_vector(Tk,Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,Gj,V,Type,N),
    true((
        mshare([[GjOut],[Vout],[TypeOut],[Nout]]),
        var(GjOut),
        var(Vout),
        var(TypeOut),
        var(Nout),
        ground([NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,Gk,Gks,K,Tk,Gj,V,Type,N]),
        linear(GjOut),
        linear(Vout),
        linear(TypeOut),
        linear(Nout)
    )),
    select_vector(Gks,NumVars,NumGs,Gs,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout),
    true(ground([NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,GjOut,Vout,TypeOut,Nout,Gk,Gks,K,Tk,Gj,V,Type,N])).

:- true pred select_vector(_A,_1,_2,_3,_4,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout)
   : ( mshare([[GjOut],[Vout],[TypeOut],[Nout]]),
       var(GjOut), var(Vout), var(TypeOut), var(Nout), ground([_A,_1,_2,_3,_4,Gj,V,Type,N]), linear(GjOut), linear(Vout), linear(TypeOut), linear(Nout) )
   => ground([_A,_1,_2,_3,_4,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout]).

:- true pred select_vector(_A,_1,_2,_3,_4,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout)
   : ( (Gj=dummy), (V=0), (Type=nf), (N=999),
       mshare([[GjOut],[Vout],[Nout]]),
       var(GjOut), var(Vout), var(Nout), ground([_A,_1,_2,_3,_4,TypeOut]), linear(GjOut), linear(Vout), linear(Nout) )
   => ground([_A,_1,_2,_3,_4,GjOut,Vout,TypeOut,Nout]).

:- true pred select_vector(_A,_1,_2,_3,_4,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout)
   : ( mshare([[GjOut],[Vout],[Nout]]),
       var(GjOut), var(Vout), var(Nout), ground([_A,_1,_2,_3,_4,Gj,V,Type,N,TypeOut]), linear(GjOut), linear(Vout), linear(Nout) )
   => ground([_A,_1,_2,_3,_4,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout]).

select_vector([],_1,_2,_3,_4,Gj,V,Type,N,Gj,V,Type,N).
select_vector([V|Vs],Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,GjOut,Vout,TypeOut,Nout) :-
    true((mshare([[GjOut],[Vout],[TypeOut],[Nout],[Type],[N],[Gj2],[V2],[Type2],[N2]]),var(GjOut),var(Vout),var(TypeOut),var(Nout),var(Type),var(N),var(Gj2),var(V2),var(Type2),var(N2),ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,V,Vs]),linear(GjOut),linear(Vout),linear(TypeOut),linear(Nout),linear(Type),linear(N),linear(Gj2),linear(V2),linear(Type2),linear(N2);mshare([[GjOut],[Vout],[Nout],[Type],[N],[Gj2],[V2],[Type2],[N2]]),var(GjOut),var(Vout),var(Nout),var(Type),var(N),var(Gj2),var(V2),var(Type2),var(N2),ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,TypeOut,V,Vs]),linear(GjOut),linear(Vout),linear(Nout),linear(Type),linear(N),linear(Gj2),linear(V2),linear(Type2),linear(N2))),
    vector_cover_type(NumVars,Gs,Gk,V,Type,N),
    true((mshare([[GjOut],[Vout],[TypeOut],[Nout],[Gj2],[V2],[Type2],[N2]]),var(GjOut),var(Vout),var(TypeOut),var(Nout),var(Gj2),var(V2),var(Type2),var(N2),ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,V,Vs,Type,N]),linear(GjOut),linear(Vout),linear(TypeOut),linear(Nout),linear(Gj2),linear(V2),linear(Type2),linear(N2);mshare([[GjOut],[Vout],[Nout],[Gj2],[V2],[Type2],[N2]]),var(GjOut),var(Vout),var(Nout),var(Gj2),var(V2),var(Type2),var(N2),ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,TypeOut,V,Vs,Type,N]),linear(GjOut),linear(Vout),linear(Nout),linear(Gj2),linear(V2),linear(Type2),linear(N2))),
    best_vector(GjIn,Vin,TypeIn,Nin,Gk,V,Type,N,Gj2,V2,Type2,N2),
    true((mshare([[GjOut],[Vout],[TypeOut],[Nout]]),var(GjOut),var(Vout),var(TypeOut),var(Nout),ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,V,Vs,Type,N,Gj2,V2,Type2,N2]),linear(GjOut),linear(Vout),linear(TypeOut),linear(Nout);mshare([[GjOut],[Vout],[Nout]]),var(GjOut),var(Vout),var(Nout),ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,TypeOut,V,Vs,Type,N,Gj2,V2,Type2,N2]),linear(GjOut),linear(Vout),linear(Nout))),
    select_vector(Vs,Gk,NumVars,NumGs,Gs,Gj2,V2,Type2,N2,GjOut,Vout,TypeOut,Nout),
    true(ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,GjOut,Vout,TypeOut,Nout,V,Vs,Type,N,Gj2,V2,Type2,N2])).

:- true pred vector_cover_type(NumVars,Gs,Gj,Vector,Type,NumCovers)
   : ( mshare([[Type],[NumCovers]]),
       var(Type), var(NumCovers), ground([NumVars,Gs,Gj,Vector]), linear(Type), linear(NumCovers) )
   => ground([NumVars,Gs,Gj,Vector,Type,NumCovers]).

vector_cover_type(NumVars,Gs,Gj,Vector,Type,NumCovers) :-
    true((
        mshare([[Type],[NumCovers],[IPs],[CIs],[Fj],[T],[N]]),
        var(Type),
        var(NumCovers),
        var(IPs),
        var(CIs),
        var(Fj),
        var(T),
        var(N),
        ground([NumVars,Gs,Gj,Vector]),
        linear(Type),
        linear(NumCovers),
        linear(IPs),
        linear(CIs),
        linear(Fj),
        linear(T),
        linear(N)
    )),
    immediate_predecessors(Gj,IPs),
    true((
        mshare([[Type],[NumCovers],[CIs],[Fj],[T],[N]]),
        var(Type),
        var(NumCovers),
        var(CIs),
        var(Fj),
        var(T),
        var(N),
        ground([NumVars,Gs,Gj,Vector,IPs]),
        linear(Type),
        linear(NumCovers),
        linear(CIs),
        linear(Fj),
        linear(T),
        linear(N)
    )),
    conceivable_inputs(Gj,CIs),
    true((
        mshare([[Type],[NumCovers],[Fj],[T],[N]]),
        var(Type),
        var(NumCovers),
        var(Fj),
        var(T),
        var(N),
        ground([NumVars,Gs,Gj,Vector,IPs,CIs]),
        linear(Type),
        linear(NumCovers),
        linear(Fj),
        linear(T),
        linear(N)
    )),
    false_set(Gj,Fj),
    true((
        mshare([[Type],[NumCovers],[T],[N]]),
        var(Type),
        var(NumCovers),
        var(T),
        var(N),
        ground([NumVars,Gs,Gj,Vector,IPs,CIs,Fj]),
        linear(Type),
        linear(NumCovers),
        linear(T),
        linear(N)
    )),
    cover_type1(IPs,Gs,Vector,nf,0,T,N),
    true((
        mshare([[Type],[NumCovers]]),
        var(Type),
        var(NumCovers),
        ground([NumVars,Gs,Gj,Vector,IPs,CIs,Fj,T,N]),
        linear(Type),
        linear(NumCovers)
    )),
    cover_type2(CIs,Gs,NumVars,Fj,Vector,T,N,Type,NumCovers),
    true(ground([NumVars,Gs,Gj,Vector,Type,NumCovers,IPs,CIs,Fj,T,N])).

:- true pred cover_type1(_A,_1,_2,T,N,TypeOut,Nout)
   : ( (T=nf), (N=0),
       mshare([[TypeOut],[Nout]]),
       var(TypeOut), var(Nout), ground([_A,_1,_2]), linear(TypeOut), linear(Nout) )
   => ground([_A,_1,_2,TypeOut,Nout]).

:- true pred cover_type1(_A,_1,_2,T,N,TypeOut,Nout)
   : ( mshare([[TypeOut],[Nout]]),
       var(TypeOut), var(Nout), ground([_A,_1,_2,T,N]), linear(TypeOut), linear(Nout) )
   => ground([_A,_1,_2,T,N,TypeOut,Nout]).

cover_type1([],_1,_2,T,N,T,N).
cover_type1([I|IPs],Gs,V,TypeIn,Nin,TypeOut,Nout) :-
    true((
        mshare([[TypeOut],[Nout],[Gi],[Ti],[Fi],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Gi),
        var(Ti),
        var(Fi),
        var(Type),
        var(N),
        ground([Gs,V,TypeIn,Nin,I,IPs]),
        linear(TypeOut),
        linear(Nout),
        linear(Gi),
        linear(Ti),
        linear(Fi),
        linear(Type),
        linear(N)
    )),
    function(I,Gs,Gi),
    true((
        mshare([[TypeOut],[Nout],[Ti],[Fi],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Ti),
        var(Fi),
        var(Type),
        var(N),
        ground([Gs,V,TypeIn,Nin,I,IPs,Gi]),
        linear(TypeOut),
        linear(Nout),
        linear(Ti),
        linear(Fi),
        linear(Type),
        linear(N)
    )),
    true_set(Gi,Ti),
    true((
        mshare([[TypeOut],[Nout],[Fi],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Fi),
        var(Type),
        var(N),
        ground([Gs,V,TypeIn,Nin,I,IPs,Gi,Ti]),
        linear(TypeOut),
        linear(Nout),
        linear(Fi),
        linear(Type),
        linear(N)
    )),
    'cover_type1/7/2/$disj/1'(V,Ti),
    !,
    true((
        mshare([[TypeOut],[Nout],[Fi],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Fi),
        var(Type),
        var(N),
        ground([Gs,V,TypeIn,Nin,I,IPs,Gi,Ti]),
        linear(TypeOut),
        linear(Nout),
        linear(Fi),
        linear(Type),
        linear(N)
    )),
    false_set(Gi,Fi),
    true((
        mshare([[TypeOut],[Nout],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Type),
        var(N),
        ground([Gs,V,TypeIn,Nin,I,IPs,Gi,Ti,Fi]),
        linear(TypeOut),
        linear(Nout),
        linear(Type),
        linear(N)
    )),
    'cover_type1/7/2/$disj/2'(V,TypeIn,Fi,Type),
    true((
        mshare([[TypeOut],[Nout],[N]]),
        var(TypeOut),
        var(Nout),
        var(N),
        ground([Gs,V,TypeIn,Nin,I,IPs,Gi,Ti,Fi,Type]),
        linear(TypeOut),
        linear(Nout),
        linear(N)
    )),
    N is Nin+1,
    true((
        mshare([[TypeOut],[Nout]]),
        var(TypeOut),
        var(Nout),
        ground([Gs,V,TypeIn,Nin,I,IPs,Gi,Ti,Fi,Type,N]),
        linear(TypeOut),
        linear(Nout)
    )),
    cover_type1(IPs,Gs,V,Type,N,TypeOut,Nout),
    true(ground([Gs,V,TypeIn,Nin,TypeOut,Nout,I,IPs,Gi,Ti,Fi,Type,N])).
cover_type1([_1|IPs],Gs,V,TypeIn,Nin,TypeOut,Nout) :-
    true((
        mshare([[TypeOut],[Nout]]),
        var(TypeOut),
        var(Nout),
        ground([Gs,V,TypeIn,Nin,_1,IPs]),
        linear(TypeOut),
        linear(Nout)
    )),
    cover_type1(IPs,Gs,V,TypeIn,Nin,TypeOut,Nout),
    true(ground([Gs,V,TypeIn,Nin,TypeOut,Nout,_1,IPs])).

:- true pred 'cover_type1/7/2/$disj/1'(V,Ti)
   : ground([V,Ti])
   => ground([V,Ti]).

'cover_type1/7/2/$disj/1'(V,Ti) :-
    true(ground([V,Ti])),
    set_member(V,Ti),
    !,
    true(ground([V,Ti])),
    fail,
    true(fails(_)).
'cover_type1/7/2/$disj/1'(V,Ti).

:- true pred 'cover_type1/7/2/$disj/2'(V,TypeIn,Fi,Type)
   : ( mshare([[Type]]),
       var(Type), ground([V,TypeIn,Fi]), linear(Type) )
   => ground([V,TypeIn,Fi,Type]).

'cover_type1/7/2/$disj/2'(V,TypeIn,Fi,Type) :-
    true((
        mshare([[Type]]),
        var(Type),
        ground([V,TypeIn,Fi]),
        linear(Type)
    )),
    set_member(V,Fi),
    !,
    true((
        mshare([[Type]]),
        var(Type),
        ground([V,TypeIn,Fi]),
        linear(Type)
    )),
    max_type(TypeIn,cov,Type),
    true(ground([V,TypeIn,Fi,Type])).
'cover_type1/7/2/$disj/2'(V,TypeIn,Fi,Type) :-
    true((
        mshare([[Type]]),
        var(Type),
        ground([V,TypeIn,Fi]),
        linear(Type)
    )),
    max_type(TypeIn,exp,Type),
    true(ground([V,TypeIn,Fi,Type])).

:- true pred cover_type2(_A,_1,_2,_3,_4,T,N,TypeOut,Nout)
   : ( mshare([[TypeOut],[Nout]]),
       var(TypeOut), var(Nout), ground([_A,_1,_2,_3,_4,T,N]), linear(TypeOut), linear(Nout) )
   => ground([_A,_1,_2,_3,_4,T,N,TypeOut,Nout]).

cover_type2([],_1,_2,_3,_4,T,N,T,N).
cover_type2([I|CIs],Gs,NumVars,Fj,V,TypeIn,Nin,TypeOut,Nout) :-
    true((
        mshare([[TypeOut],[Nout],[Gi],[Fi],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Gi),
        var(Fi),
        var(Type),
        var(N),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs]),
        linear(TypeOut),
        linear(Nout),
        linear(Gi),
        linear(Fi),
        linear(Type),
        linear(N)
    )),
    I<NumVars,
    true((
        mshare([[TypeOut],[Nout],[Gi],[Fi],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Gi),
        var(Fi),
        var(Type),
        var(N),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs]),
        linear(TypeOut),
        linear(Nout),
        linear(Gi),
        linear(Fi),
        linear(Type),
        linear(N)
    )),
    function(I,Gs,Gi),
    true((
        mshare([[TypeOut],[Nout],[Fi],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Fi),
        var(Type),
        var(N),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi]),
        linear(TypeOut),
        linear(Nout),
        linear(Fi),
        linear(Type),
        linear(N)
    )),
    false_set(Gi,Fi),
    true((
        mshare([[TypeOut],[Nout],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Type),
        var(N),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Fi]),
        linear(TypeOut),
        linear(Nout),
        linear(Type),
        linear(N)
    )),
    set_member(V,Fi),
    !,
    true((
        mshare([[TypeOut],[Nout],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Type),
        var(N),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Fi]),
        linear(TypeOut),
        linear(Nout),
        linear(Type),
        linear(N)
    )),
    max_type(TypeIn,var,Type),
    true((
        mshare([[TypeOut],[Nout],[N]]),
        var(TypeOut),
        var(Nout),
        var(N),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Fi,Type]),
        linear(TypeOut),
        linear(Nout),
        linear(N)
    )),
    N is Nin+1,
    true((
        mshare([[TypeOut],[Nout]]),
        var(TypeOut),
        var(Nout),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Fi,Type,N]),
        linear(TypeOut),
        linear(Nout)
    )),
    cover_type2(CIs,Gs,NumVars,Fj,V,Type,N,TypeOut,Nout),
    true(ground([Gs,NumVars,Fj,V,TypeIn,Nin,TypeOut,Nout,I,CIs,Gi,Fi,Type,N])).
cover_type2([I|CIs],Gs,NumVars,Fj,V,TypeIn,Nin,TypeOut,Nout) :-
    true((
        mshare([[TypeOut],[Nout],[Gi],[Ti],[Fi],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Gi),
        var(Ti),
        var(Fi),
        var(Type),
        var(N),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs]),
        linear(TypeOut),
        linear(Nout),
        linear(Gi),
        linear(Ti),
        linear(Fi),
        linear(Type),
        linear(N)
    )),
    I>=NumVars,
    true((
        mshare([[TypeOut],[Nout],[Gi],[Ti],[Fi],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Gi),
        var(Ti),
        var(Fi),
        var(Type),
        var(N),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs]),
        linear(TypeOut),
        linear(Nout),
        linear(Gi),
        linear(Ti),
        linear(Fi),
        linear(Type),
        linear(N)
    )),
    function(I,Gs,Gi),
    true((
        mshare([[TypeOut],[Nout],[Ti],[Fi],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Ti),
        var(Fi),
        var(Type),
        var(N),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi]),
        linear(TypeOut),
        linear(Nout),
        linear(Ti),
        linear(Fi),
        linear(Type),
        linear(N)
    )),
    true_set(Gi,Ti),
    true((
        mshare([[TypeOut],[Nout],[Fi],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Fi),
        var(Type),
        var(N),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Ti]),
        linear(TypeOut),
        linear(Nout),
        linear(Fi),
        linear(Type),
        linear(N)
    )),
    'cover_type2/9/3/$disj/1'(V,Ti),
    !,
    true((
        mshare([[TypeOut],[Nout],[Fi],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Fi),
        var(Type),
        var(N),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Ti]),
        linear(TypeOut),
        linear(Nout),
        linear(Fi),
        linear(Type),
        linear(N)
    )),
    false_set(Gi,Fi),
    true((
        mshare([[TypeOut],[Nout],[Type],[N]]),
        var(TypeOut),
        var(Nout),
        var(Type),
        var(N),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Ti,Fi]),
        linear(TypeOut),
        linear(Nout),
        linear(Type),
        linear(N)
    )),
    'cover_type2/9/3/$disj/2'(Fj,V,TypeIn,Ti,Fi,Type),
    true((
        mshare([[TypeOut],[Nout],[N]]),
        var(TypeOut),
        var(Nout),
        var(N),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Ti,Fi,Type]),
        linear(TypeOut),
        linear(Nout),
        linear(N)
    )),
    N is Nin+1,
    true((
        mshare([[TypeOut],[Nout]]),
        var(TypeOut),
        var(Nout),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Ti,Fi,Type,N]),
        linear(TypeOut),
        linear(Nout)
    )),
    cover_type2(CIs,Gs,NumVars,Fj,V,Type,N,TypeOut,Nout),
    true(ground([Gs,NumVars,Fj,V,TypeIn,Nin,TypeOut,Nout,I,CIs,Gi,Ti,Fi,Type,N])).
cover_type2([_1|CIs],Gs,NumVars,Fj,V,TypeIn,Nin,TypeOut,Nout) :-
    true((
        mshare([[TypeOut],[Nout]]),
        var(TypeOut),
        var(Nout),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,_1,CIs]),
        linear(TypeOut),
        linear(Nout)
    )),
    cover_type2(CIs,Gs,NumVars,Fj,V,TypeIn,Nin,TypeOut,Nout),
    true(ground([Gs,NumVars,Fj,V,TypeIn,Nin,TypeOut,Nout,_1,CIs])).

:- true pred 'cover_type2/9/3/$disj/1'(V,Ti)
   : ground([V,Ti])
   => ground([V,Ti]).

'cover_type2/9/3/$disj/1'(V,Ti) :-
    true(ground([V,Ti])),
    set_member(V,Ti),
    !,
    true(ground([V,Ti])),
    fail,
    true(fails(_)).
'cover_type2/9/3/$disj/1'(V,Ti).

:- true pred 'cover_type2/9/3/$disj/2'(Fj,V,TypeIn,Ti,Fi,Type)
   : ( mshare([[Type]]),
       var(Type), ground([Fj,V,TypeIn,Ti,Fi]), linear(Type) )
   => ground([Fj,V,TypeIn,Ti,Fi,Type]).

'cover_type2/9/3/$disj/2'(Fj,V,TypeIn,Ti,Fi,Type) :-
    true((
        mshare([[Type]]),
        var(Type),
        ground([Fj,V,TypeIn,Ti,Fi]),
        linear(Type)
    )),
    set_member(V,Fi),
    !,
    true((
        mshare([[Type]]),
        var(Type),
        ground([Fj,V,TypeIn,Ti,Fi]),
        linear(Type)
    )),
    'cover_type2/9/3/$disj/2/6/1/$disj/1'(Fj,TypeIn,Ti,Type),
    true(ground([Fj,V,TypeIn,Ti,Fi,Type])).
'cover_type2/9/3/$disj/2'(Fj,V,TypeIn,Ti,Fi,Type) :-
    true((
        mshare([[Type]]),
        var(Type),
        ground([Fj,V,TypeIn,Ti,Fi]),
        linear(Type)
    )),
    set_subset(Fj,Ti),
    !,
    true((
        mshare([[Type]]),
        var(Type),
        ground([Fj,V,TypeIn,Ti,Fi]),
        linear(Type)
    )),
    max_type(TypeIn,exf,Type),
    true(ground([Fj,V,TypeIn,Ti,Fi,Type])).
'cover_type2/9/3/$disj/2'(Fj,V,TypeIn,Ti,Fi,Type) :-
    true((
        mshare([[Type]]),
        var(Type),
        ground([Fj,V,TypeIn,Ti,Fi]),
        linear(Type)
    )),
    max_type(TypeIn,exmcf,Type),
    true(ground([Fj,V,TypeIn,Ti,Fi,Type])).

:- true pred 'cover_type2/9/3/$disj/2/6/1/$disj/1'(Fj,TypeIn,Ti,Type)
   : ( mshare([[Type]]),
       var(Type), ground([Fj,TypeIn,Ti]), linear(Type) )
   => ground([Fj,TypeIn,Ti,Type]).

'cover_type2/9/3/$disj/2/6/1/$disj/1'(Fj,TypeIn,Ti,Type) :-
    true((
        mshare([[Type]]),
        var(Type),
        ground([Fj,TypeIn,Ti]),
        linear(Type)
    )),
    set_subset(Fj,Ti),
    !,
    true((
        mshare([[Type]]),
        var(Type),
        ground([Fj,TypeIn,Ti]),
        linear(Type)
    )),
    max_type(TypeIn,fcn,Type),
    true(ground([Fj,TypeIn,Ti,Type])).
'cover_type2/9/3/$disj/2/6/1/$disj/1'(Fj,TypeIn,Ti,Type) :-
    true((
        mshare([[Type]]),
        var(Type),
        ground([Fj,TypeIn,Ti]),
        linear(Type)
    )),
    max_type(TypeIn,mcf,Type),
    true(ground([Fj,TypeIn,Ti,Type])).

:- true pred best_vector(Gj1,_1,_2,_3,Gj2,V2,Type2,N2,_A,V1,Type1,N1)
   : ( mshare([[_A],[V1],[Type1],[N1]]),
       var(_A), var(V1), var(Type1), var(N1), ground([Gj1,_1,_2,_3,Gj2,V2,Type2,N2]), linear(_A), linear(V1), linear(Type1), linear(N1) )
   => ground([Gj1,_1,_2,_3,Gj2,V2,Type2,N2,_A,V1,Type1,N1]).

best_vector(dummy,_1,_2,_3,Gj2,V2,Type2,N2,Gj2,V2,Type2,N2) :-
    !,
    true(ground([_1,_2,_3,Gj2,V2,Type2,N2])).
best_vector(Gj1,V1,Type1,N1,dummy,_1,_2,_3,Gj1,V1,Type1,N1) :-
    !,
    true(ground([Gj1,V1,Type1,N1,_1,_2,_3])).
best_vector(Gj1,V1,Type,N1,Gj2,_1,Type,N2,Gj1,V1,Type,N1) :-
    true((
        mshare([[J]]),
        var(J),
        ground([Gj1,V1,Type,N1,Gj2,_1,N2]),
        linear(J)
    )),
    function_number(Gj1,J),
    true(ground([Gj1,V1,Type,N1,Gj2,_1,N2,J])),
    function_number(Gj2,J),
    true(ground([Gj1,V1,Type,N1,Gj2,_1,N2,J])),
    N1<N2,
    !,
    true(ground([Gj1,V1,Type,N1,Gj2,_1,N2,J])).
best_vector(Gj1,_1,Type,N1,Gj2,V2,Type,N2,Gj2,V2,Type,N2) :-
    true((
        mshare([[J]]),
        var(J),
        ground([Gj1,_1,Type,N1,Gj2,V2,N2]),
        linear(J)
    )),
    function_number(Gj1,J),
    true(ground([Gj1,_1,Type,N1,Gj2,V2,N2,J])),
    function_number(Gj2,J),
    true(ground([Gj1,_1,Type,N1,Gj2,V2,N2,J])),
    N1>=N2,
    !,
    true(ground([Gj1,_1,Type,N1,Gj2,V2,N2,J])).
best_vector(Gj1,V1,Type,N1,Gj2,_1,Type,_2,Gj1,V1,Type,N1) :-
    true((
        mshare([[J1],[J2]]),
        var(J1),
        var(J2),
        ground([Gj1,V1,Type,N1,Gj2,_1,_2]),
        linear(J1),
        linear(J2)
    )),
    'best_vector/12/5/$disj/1'(Type),
    true((
        mshare([[J1],[J2]]),
        var(J1),
        var(J2),
        ground([Gj1,V1,Type,N1,Gj2,_1,_2]),
        linear(J1),
        linear(J2)
    )),
    function_number(Gj1,J1),
    true((
        mshare([[J2]]),
        var(J2),
        ground([Gj1,V1,Type,N1,Gj2,_1,_2,J1]),
        linear(J2)
    )),
    function_number(Gj2,J2),
    true(ground([Gj1,V1,Type,N1,Gj2,_1,_2,J1,J2])),
    J1>J2,
    !,
    true(ground([Gj1,V1,Type,N1,Gj2,_1,_2,J1,J2])).
best_vector(Gj1,_1,Type,_2,Gj2,V2,Type,N2,Gj2,V2,Type,N2) :-
    true((
        mshare([[J1],[J2]]),
        var(J1),
        var(J2),
        ground([Gj1,_1,Type,_2,Gj2,V2,N2]),
        linear(J1),
        linear(J2)
    )),
    'best_vector/12/6/$disj/1'(Type),
    true((
        mshare([[J1],[J2]]),
        var(J1),
        var(J2),
        ground([Gj1,_1,Type,_2,Gj2,V2,N2]),
        linear(J1),
        linear(J2)
    )),
    function_number(Gj1,J1),
    true((
        mshare([[J2]]),
        var(J2),
        ground([Gj1,_1,Type,_2,Gj2,V2,N2,J1]),
        linear(J2)
    )),
    function_number(Gj2,J2),
    true(ground([Gj1,_1,Type,_2,Gj2,V2,N2,J1,J2])),
    J1<J2,
    !,
    true(ground([Gj1,_1,Type,_2,Gj2,V2,N2,J1,J2])).
best_vector(Gj1,V1,Type,N1,Gj2,_1,Type,_2,Gj1,V1,Type,N1) :-
    true((
        mshare([[J1],[J2]]),
        var(J1),
        var(J2),
        ground([Gj1,V1,Type,N1,Gj2,_1,_2]),
        linear(J1),
        linear(J2)
    )),
    'best_vector/12/7/$disj/1'(Type),
    true((
        mshare([[J1],[J2]]),
        var(J1),
        var(J2),
        ground([Gj1,V1,Type,N1,Gj2,_1,_2]),
        linear(J1),
        linear(J2)
    )),
    function_number(Gj1,J1),
    true((
        mshare([[J2]]),
        var(J2),
        ground([Gj1,V1,Type,N1,Gj2,_1,_2,J1]),
        linear(J2)
    )),
    function_number(Gj2,J2),
    true(ground([Gj1,V1,Type,N1,Gj2,_1,_2,J1,J2])),
    J1<J2,
    !,
    true(ground([Gj1,V1,Type,N1,Gj2,_1,_2,J1,J2])).
best_vector(Gj1,_1,Type,_2,Gj2,V2,Type,N2,Gj2,V2,Type,N2) :-
    true((
        mshare([[J1],[J2]]),
        var(J1),
        var(J2),
        ground([Gj1,_1,Type,_2,Gj2,V2,N2]),
        linear(J1),
        linear(J2)
    )),
    'best_vector/12/8/$disj/1'(Type),
    true((
        mshare([[J1],[J2]]),
        var(J1),
        var(J2),
        ground([Gj1,_1,Type,_2,Gj2,V2,N2]),
        linear(J1),
        linear(J2)
    )),
    function_number(Gj1,J1),
    true((
        mshare([[J2]]),
        var(J2),
        ground([Gj1,_1,Type,_2,Gj2,V2,N2,J1]),
        linear(J2)
    )),
    function_number(Gj2,J2),
    true(ground([Gj1,_1,Type,_2,Gj2,V2,N2,J1,J2])),
    J1>J2,
    !,
    true(ground([Gj1,_1,Type,_2,Gj2,V2,N2,J1,J2])).
best_vector(Gj1,V1,Type1,N1,_1,_2,Type2,_3,Gj1,V1,Type1,N1) :-
    true(ground([Gj1,V1,Type1,N1,_1,_2,Type2,_3])),
    type_order(Type2,Type1),
    !,
    true(ground([Gj1,V1,Type1,N1,_1,_2,Type2,_3])).
best_vector(_1,_2,Type1,_3,Gj2,V2,Type2,N2,Gj2,V2,Type2,N2) :-
    true(ground([_1,_2,Type1,_3,Gj2,V2,Type2,N2])),
    type_order(Type1,Type2),
    !,
    true(ground([_1,_2,Type1,_3,Gj2,V2,Type2,N2])).

:- true pred 'best_vector/12/5/$disj/1'(Type)
   : ground([Type])
   => ground([Type]).

'best_vector/12/5/$disj/1'(Type) :-
    true(ground([Type])),
    Type=exp,
    true(ground([Type])).
'best_vector/12/5/$disj/1'(Type) :-
    true(ground([Type])),
    Type=var,
    true(ground([Type])).

:- true pred 'best_vector/12/6/$disj/1'(Type)
   : ground([Type])
   => ground([Type]).

'best_vector/12/6/$disj/1'(Type) :-
    true(ground([Type])),
    Type=exp,
    true(ground([Type])).
'best_vector/12/6/$disj/1'(Type) :-
    true(ground([Type])),
    Type=var,
    true(ground([Type])).

:- true pred 'best_vector/12/7/$disj/1'(Type)
   : ground([Type])
   => ground([Type]).

'best_vector/12/7/$disj/1'(Type) :-
    true(ground([Type])),
    'best_vector/12/7/$disj/1/1/1/$disj/1'(Type),
    !,
    true(ground([Type])),
    fail,
    true(fails(_)).
'best_vector/12/7/$disj/1'(Type).

:- true pred 'best_vector/12/7/$disj/1/1/1/$disj/1'(Type)
   : ground([Type])
   => ground([Type]).

'best_vector/12/7/$disj/1/1/1/$disj/1'(Type) :-
    true(ground([Type])),
    Type=exp,
    true(ground([Type])).
'best_vector/12/7/$disj/1/1/1/$disj/1'(Type) :-
    true(ground([Type])),
    Type=var,
    true(ground([Type])).

:- true pred 'best_vector/12/8/$disj/1'(Type)
   : ground([Type])
   => ground([Type]).

'best_vector/12/8/$disj/1'(Type) :-
    true(ground([Type])),
    'best_vector/12/8/$disj/1/1/1/$disj/1'(Type),
    !,
    true(ground([Type])),
    fail,
    true(fails(_)).
'best_vector/12/8/$disj/1'(Type).

:- true pred 'best_vector/12/8/$disj/1/1/1/$disj/1'(Type)
   : ground([Type])
   => ground([Type]).

'best_vector/12/8/$disj/1/1/1/$disj/1'(Type) :-
    true(ground([Type])),
    Type=exp,
    true(ground([Type])).
'best_vector/12/8/$disj/1/1/1/$disj/1'(Type) :-
    true(ground([Type])),
    Type=var,
    true(ground([Type])).

:- true pred max_type(T1,T2,_A)
   : ( (T2=exmcf),
       mshare([[_A]]),
       var(_A), ground([T1]), linear(_A) )
   => ground([T1,_A]).

:- true pred max_type(T1,T2,_A)
   : ( (T2=exf),
       mshare([[_A]]),
       var(_A), ground([T1]), linear(_A) )
   => ground([T1,_A]).

:- true pred max_type(T1,T2,_A)
   : ( (T2=mcf),
       mshare([[_A]]),
       var(_A), ground([T1]), linear(_A) )
   => ground([T1,_A]).

:- true pred max_type(T1,T2,_A)
   : ( (T2=fcn),
       mshare([[_A]]),
       var(_A), ground([T1]), linear(_A) )
   => ground([T1,_A]).

:- true pred max_type(T1,T2,_A)
   : ( (T2=var),
       mshare([[_A]]),
       var(_A), ground([T1]), linear(_A) )
   => ground([T1,_A]).

:- true pred max_type(T1,T2,_A)
   : ( (T2=exp),
       mshare([[_A]]),
       var(_A), ground([T1]), linear(_A) )
   => ground([T1,_A]).

:- true pred max_type(T1,T2,_A)
   : ( (T2=cov),
       mshare([[_A]]),
       var(_A), ground([T1]), linear(_A) )
   => ground([T1,_A]).

max_type(T1,T2,T1) :-
    true(ground([T1,T2])),
    type_order(T1,T2),
    !,
    true(ground([T1,T2])).
max_type(T1,T2,T2) :-
    true(ground([T1,T2])),
    'max_type/3/2/$disj/1'(T1,T2),
    !,
    true(ground([T1,T2])).

:- true pred 'max_type/3/2/$disj/1'(T1,T2)
   : ground([T1,T2])
   => ground([T1,T2]).

'max_type/3/2/$disj/1'(T1,T2) :-
    true(ground([T1,T2])),
    type_order(T1,T2),
    !,
    true(ground([T1,T2])),
    fail,
    true(fails(_)).
'max_type/3/2/$disj/1'(T1,T2).

:- true pred type_order(_A,_B)
   : ground([_A,_B])
   => ground([_A,_B]).

type_order(cov,exp).
type_order(cov,var).
type_order(cov,fcn).
type_order(cov,mcf).
type_order(cov,exf).
type_order(cov,exmcf).
type_order(cov,nf).
type_order(exp,var).
type_order(exp,fcn).
type_order(exp,mcf).
type_order(exp,exf).
type_order(exp,exmcf).
type_order(exp,nf).
type_order(var,fcn).
type_order(var,mcf).
type_order(var,exf).
type_order(var,exmcf).
type_order(var,nf).
type_order(fcn,mcf).
type_order(fcn,exf).
type_order(fcn,exmcf).
type_order(fcn,nf).
type_order(mcf,exf).
type_order(mcf,exmcf).
type_order(mcf,nf).
type_order(exf,exmcf).
type_order(exf,nf).
type_order(exmcf,nf).

:- true pred cover_vector(NumVars,NumGsIn,GsIn,Gj,Vector,NumGsOut,GsOut)
   : ( mshare([[NumGsOut],[GsOut]]),
       var(NumGsOut), var(GsOut), ground([NumVars,NumGsIn,GsIn,Gj,Vector]), linear(NumGsOut), linear(GsOut) )
   => ground([NumVars,NumGsIn,GsIn,Gj,Vector,NumGsOut,GsOut]).

cover_vector(NumVars,NumGsIn,GsIn,Gj,Vector,NumGsOut,GsOut) :-
    true((
        mshare([[NumGsOut],[GsOut],[IPs],[CIs],[Type]]),
        var(NumGsOut),
        var(GsOut),
        var(IPs),
        var(CIs),
        var(Type),
        ground([NumVars,NumGsIn,GsIn,Gj,Vector]),
        linear(NumGsOut),
        linear(GsOut),
        linear(IPs),
        linear(CIs),
        linear(Type)
    )),
    immediate_predecessors(Gj,IPs),
    true((
        mshare([[NumGsOut],[GsOut],[CIs],[Type]]),
        var(NumGsOut),
        var(GsOut),
        var(CIs),
        var(Type),
        ground([NumVars,NumGsIn,GsIn,Gj,Vector,IPs]),
        linear(NumGsOut),
        linear(GsOut),
        linear(CIs),
        linear(Type)
    )),
    conceivable_inputs(Gj,CIs),
    true((
        mshare([[NumGsOut],[GsOut],[Type]]),
        var(NumGsOut),
        var(GsOut),
        var(Type),
        ground([NumVars,NumGsIn,GsIn,Gj,Vector,IPs,CIs]),
        linear(NumGsOut),
        linear(GsOut),
        linear(Type)
    )),
    vector_types(Type),
    true((
        mshare([[NumGsOut],[GsOut]]),
        var(NumGsOut),
        var(GsOut),
        ground([NumVars,NumGsIn,GsIn,Gj,Vector,IPs,CIs,Type]),
        linear(NumGsOut),
        linear(GsOut)
    )),
    cover_vector(Type,IPs,CIs,Gj,Vector,NumVars,NumGsIn,GsIn,NumGsOut,GsOut),
    true(ground([NumVars,NumGsIn,GsIn,Gj,Vector,NumGsOut,GsOut,IPs,CIs,Type])).

:- true pred vector_types(_A)
   : ( mshare([[_A]]),
       var(_A), linear(_A) )
   => ground([_A]).

vector_types(var).
vector_types(exp).
vector_types(fcn).
vector_types(mcf).
vector_types(exf).
vector_types(exmcf).
vector_types(nf).

:- true pred cover_vector(_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut)
   : ( mshare([[NumGsOut],[GsOut]]),
       var(NumGsOut), var(GsOut), ground([_A,_B,_1,Gj,V,_2,NumGs,GsIn]), linear(NumGsOut), linear(GsOut) )
   => ground([_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut]).

:- true pred cover_vector(_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut)
   : ( (_A=exmcf), (NumGs=NumGsOut),
       mshare([[_B],[GsOut]]),
       var(_B), var(GsOut), ground([_1,Gj,V,_2,NumGs,GsIn]), linear(_B), linear(GsOut) )
   => ( mshare([[_B]]),
        var(_B), ground([_1,Gj,V,_2,NumGs,GsIn,GsOut]), linear(_B) ).

:- true pred cover_vector(_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut)
   : ( (_A=exf), (NumGs=NumGsOut),
       mshare([[_B],[GsOut]]),
       var(_B), var(GsOut), ground([_1,Gj,V,_2,NumGs,GsIn]), linear(_B), linear(GsOut) )
   => ( mshare([[_B]]),
        var(_B), ground([_1,Gj,V,_2,NumGs,GsIn,GsOut]), linear(_B) ).

:- true pred cover_vector(_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut)
   : ( (_A=mcf), (NumGs=NumGsOut),
       mshare([[_B],[GsOut]]),
       var(_B), var(GsOut), ground([_1,Gj,V,_2,NumGs,GsIn]), linear(_B), linear(GsOut) )
   => ( mshare([[_B]]),
        var(_B), ground([_1,Gj,V,_2,NumGs,GsIn,GsOut]), linear(_B) ).

:- true pred cover_vector(_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut)
   : ( (_A=fcn), (NumGs=NumGsOut),
       mshare([[_B],[GsOut]]),
       var(_B), var(GsOut), ground([_1,Gj,V,_2,NumGs,GsIn]), linear(_B), linear(GsOut) )
   => ( mshare([[_B]]),
        var(_B), ground([_1,Gj,V,_2,NumGs,GsIn,GsOut]), linear(_B) ).

:- true pred cover_vector(_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut)
   : ( (_A=var), (NumGs=NumGsOut),
       mshare([[_B],[GsOut]]),
       var(_B), var(GsOut), ground([_1,Gj,V,_2,NumGs,GsIn]), linear(_B), linear(GsOut) )
   => ( mshare([[_B]]),
        var(_B), ground([_1,Gj,V,_2,NumGs,GsIn,GsOut]), linear(_B) ).

:- true pred cover_vector(_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut)
   : ( (_A=exp), (NumGs=NumGsOut),
       mshare([[_1],[GsOut]]),
       var(_1), var(GsOut), ground([_B,Gj,V,_2,NumGs,GsIn]), linear(_1), linear(GsOut) )
   => ( mshare([[_1]]),
        var(_1), ground([_B,Gj,V,_2,NumGs,GsIn,GsOut]), linear(_1) ).

cover_vector(exp,[I|_3],_1,Gj,V,_2,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[Gi],[Ti]]),var(_1),var(GsOut),var(Gi),var(Ti),ground([Gj,V,_2,NumGs,GsIn,I,_3]),linear(_1),linear(GsOut),linear(Gi),linear(Ti);mshare([[GsOut],[Gi],[Ti]]),var(GsOut),var(Gi),var(Ti),ground([_1,Gj,V,_2,NumGs,GsIn,I,_3]),linear(GsOut),linear(Gi),linear(Ti))),
    function(I,GsIn,Gi),
    true((mshare([[_1],[GsOut],[Ti]]),var(_1),var(GsOut),var(Ti),ground([Gj,V,_2,NumGs,GsIn,I,_3,Gi]),linear(_1),linear(GsOut),linear(Ti);mshare([[GsOut],[Ti]]),var(GsOut),var(Ti),ground([_1,Gj,V,_2,NumGs,GsIn,I,_3,Gi]),linear(GsOut),linear(Ti))),
    true_set(Gi,Ti),
    true((mshare([[_1],[GsOut]]),var(_1),var(GsOut),ground([Gj,V,_2,NumGs,GsIn,I,_3,Gi,Ti]),linear(_1),linear(GsOut);mshare([[GsOut]]),var(GsOut),ground([_1,Gj,V,_2,NumGs,GsIn,I,_3,Gi,Ti]),linear(GsOut))),
    'cover_vector/10/1/$disj/1'(V,Ti),
    true((mshare([[_1],[GsOut]]),var(_1),var(GsOut),ground([Gj,V,_2,NumGs,GsIn,I,_3,Gi,Ti]),linear(_1),linear(GsOut);mshare([[GsOut]]),var(GsOut),ground([_1,Gj,V,_2,NumGs,GsIn,I,_3,Gi,Ti]),linear(GsOut))),
    update_circuit(GsIn,Gi,Gj,V,GsIn,GsOut),
    true((mshare([[_1]]),var(_1),ground([Gj,V,_2,NumGs,GsIn,GsOut,I,_3,Gi,Ti]),linear(_1);ground([_1,Gj,V,_2,NumGs,GsIn,GsOut,I,_3,Gi,Ti]))).
cover_vector(exp,[_2|IPs],_1,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[_3]]),var(_1),var(GsOut),var(_3),ground([Gj,V,NumVars,NumGs,GsIn,_2,IPs]),linear(_1),linear(GsOut),linear(_3);mshare([[GsOut],[_3]]),var(GsOut),var(_3),ground([_1,Gj,V,NumVars,NumGs,GsIn,_2,IPs]),linear(GsOut),linear(_3))),
    cover_vector(exp,IPs,_3,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut),
    true((mshare([[_1],[_3]]),var(_1),var(_3),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,_2,IPs]),linear(_1),linear(_3);mshare([[_3]]),var(_3),ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,_2,IPs]),linear(_3))).
cover_vector(var,_1,[I|_2],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[Gi],[Fi]]),var(_1),var(GsOut),var(Gi),var(Fi),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(_1),linear(GsOut),linear(Gi),linear(Fi);mshare([[GsOut],[Gi],[Fi]]),var(GsOut),var(Gi),var(Fi),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(GsOut),linear(Gi),linear(Fi))),
    I<NumVars,
    true((mshare([[_1],[GsOut],[Gi],[Fi]]),var(_1),var(GsOut),var(Gi),var(Fi),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(_1),linear(GsOut),linear(Gi),linear(Fi);mshare([[GsOut],[Gi],[Fi]]),var(GsOut),var(Gi),var(Fi),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(GsOut),linear(Gi),linear(Fi))),
    function(I,GsIn,Gi),
    true((mshare([[_1],[GsOut],[Fi]]),var(_1),var(GsOut),var(Fi),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]),linear(_1),linear(GsOut),linear(Fi);mshare([[GsOut],[Fi]]),var(GsOut),var(Fi),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]),linear(GsOut),linear(Fi))),
    false_set(Gi,Fi),
    true((mshare([[_1],[GsOut]]),var(_1),var(GsOut),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(_1),linear(GsOut);mshare([[GsOut]]),var(GsOut),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(GsOut))),
    set_member(V,Fi),
    true((mshare([[_1],[GsOut]]),var(_1),var(GsOut),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(_1),linear(GsOut);mshare([[GsOut]]),var(GsOut),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(GsOut))),
    update_circuit(GsIn,Gi,Gj,V,GsIn,GsOut),
    true((mshare([[_1]]),var(_1),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi]),linear(_1);ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi]))).
cover_vector(var,_1,[_2|CIs],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[_3]]),var(_1),var(GsOut),var(_3),ground([Gj,V,NumVars,NumGs,GsIn,_2,CIs]),linear(_1),linear(GsOut),linear(_3);mshare([[GsOut],[_3]]),var(GsOut),var(_3),ground([_1,Gj,V,NumVars,NumGs,GsIn,_2,CIs]),linear(GsOut),linear(_3))),
    cover_vector(var,_3,CIs,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut),
    true((mshare([[_1],[_3]]),var(_1),var(_3),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]),linear(_1),linear(_3);mshare([[_3]]),var(_3),ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]),linear(_3))).
cover_vector(fcn,_1,[I|_2],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(_1),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(_1),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj))),
    I>=NumVars,
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(_1),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(_1),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj))),
    function(I,GsIn,Gi),
    true((mshare([[_1],[GsOut],[Fi],[Ti],[Fj]]),var(_1),var(GsOut),var(Fi),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]),linear(_1),linear(GsOut),linear(Fi),linear(Ti),linear(Fj);mshare([[GsOut],[Fi],[Ti],[Fj]]),var(GsOut),var(Fi),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]),linear(GsOut),linear(Fi),linear(Ti),linear(Fj))),
    false_set(Gi,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),var(_1),var(GsOut),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(_1),linear(GsOut),linear(Ti),linear(Fj);mshare([[GsOut],[Ti],[Fj]]),var(GsOut),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(GsOut),linear(Ti),linear(Fj))),
    set_member(V,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),var(_1),var(GsOut),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(_1),linear(GsOut),linear(Ti),linear(Fj);mshare([[GsOut],[Ti],[Fj]]),var(GsOut),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(GsOut),linear(Ti),linear(Fj))),
    true_set(Gi,Ti),
    true((mshare([[_1],[GsOut],[Fj]]),var(_1),var(GsOut),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]),linear(_1),linear(GsOut),linear(Fj);mshare([[GsOut],[Fj]]),var(GsOut),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]),linear(GsOut),linear(Fj))),
    false_set(Gj,Fj),
    true((mshare([[_1],[GsOut]]),var(_1),var(GsOut),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(_1),linear(GsOut);mshare([[GsOut]]),var(GsOut),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(GsOut))),
    set_subset(Fj,Ti),
    true((mshare([[_1],[GsOut]]),var(_1),var(GsOut),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(_1),linear(GsOut);mshare([[GsOut]]),var(GsOut),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(GsOut))),
    update_circuit(GsIn,Gi,Gj,V,GsIn,GsOut),
    true((mshare([[_1]]),var(_1),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]),linear(_1);ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]))).
cover_vector(fcn,_1,[_2|CIs],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[_3]]),var(_1),var(GsOut),var(_3),ground([Gj,V,NumVars,NumGs,GsIn,_2,CIs]),linear(_1),linear(GsOut),linear(_3);mshare([[GsOut],[_3]]),var(GsOut),var(_3),ground([_1,Gj,V,NumVars,NumGs,GsIn,_2,CIs]),linear(GsOut),linear(_3))),
    cover_vector(fcn,_3,CIs,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut),
    true((mshare([[_1],[_3]]),var(_1),var(_3),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]),linear(_1),linear(_3);mshare([[_3]]),var(_3),ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]),linear(_3))).
cover_vector(mcf,_1,[I|_2],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(_1),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(_1),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj))),
    I>=NumVars,
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(_1),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(_1),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj))),
    function(I,GsIn,Gi),
    true((mshare([[_1],[GsOut],[Fi],[Ti],[Fj]]),var(_1),var(GsOut),var(Fi),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]),linear(_1),linear(GsOut),linear(Fi),linear(Ti),linear(Fj);mshare([[GsOut],[Fi],[Ti],[Fj]]),var(GsOut),var(Fi),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]),linear(GsOut),linear(Fi),linear(Ti),linear(Fj))),
    false_set(Gi,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),var(_1),var(GsOut),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(_1),linear(GsOut),linear(Ti),linear(Fj);mshare([[GsOut],[Ti],[Fj]]),var(GsOut),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(GsOut),linear(Ti),linear(Fj))),
    set_member(V,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),var(_1),var(GsOut),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(_1),linear(GsOut),linear(Ti),linear(Fj);mshare([[GsOut],[Ti],[Fj]]),var(GsOut),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(GsOut),linear(Ti),linear(Fj))),
    true_set(Gi,Ti),
    true((mshare([[_1],[GsOut],[Fj]]),var(_1),var(GsOut),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]),linear(_1),linear(GsOut),linear(Fj);mshare([[GsOut],[Fj]]),var(GsOut),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]),linear(GsOut),linear(Fj))),
    false_set(Gj,Fj),
    true((mshare([[_1],[GsOut]]),var(_1),var(GsOut),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(_1),linear(GsOut);mshare([[GsOut]]),var(GsOut),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(GsOut))),
    'cover_vector/10/7/$disj/1'(Ti,Fj),
    true((mshare([[_1],[GsOut]]),var(_1),var(GsOut),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(_1),linear(GsOut);mshare([[GsOut]]),var(GsOut),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(GsOut))),
    update_circuit(GsIn,Gi,Gj,V,GsIn,GsOut),
    true((mshare([[_1]]),var(_1),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]),linear(_1);ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]))).
cover_vector(mcf,_1,[_2|CIs],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[_3]]),var(_1),var(GsOut),var(_3),ground([Gj,V,NumVars,NumGs,GsIn,_2,CIs]),linear(_1),linear(GsOut),linear(_3);mshare([[GsOut],[_3]]),var(GsOut),var(_3),ground([_1,Gj,V,NumVars,NumGs,GsIn,_2,CIs]),linear(GsOut),linear(_3))),
    cover_vector(mcf,_3,CIs,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut),
    true((mshare([[_1],[_3]]),var(_1),var(_3),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]),linear(_1),linear(_3);mshare([[_3]]),var(_3),ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]),linear(_3))).
cover_vector(exf,_1,[I|_2],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(_1),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(_1),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj))),
    I>=NumVars,
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(_1),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(_1),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj))),
    function(I,GsIn,Gi),
    true((mshare([[_1],[GsOut],[Fi],[Ti],[Fj]]),var(_1),var(GsOut),var(Fi),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]),linear(_1),linear(GsOut),linear(Fi),linear(Ti),linear(Fj);mshare([[GsOut],[Fi],[Ti],[Fj]]),var(GsOut),var(Fi),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]),linear(GsOut),linear(Fi),linear(Ti),linear(Fj))),
    false_set(Gi,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),var(_1),var(GsOut),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(_1),linear(GsOut),linear(Ti),linear(Fj);mshare([[GsOut],[Ti],[Fj]]),var(GsOut),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(GsOut),linear(Ti),linear(Fj))),
    'cover_vector/10/9/$disj/1'(V,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),var(_1),var(GsOut),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(_1),linear(GsOut),linear(Ti),linear(Fj);mshare([[GsOut],[Ti],[Fj]]),var(GsOut),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(GsOut),linear(Ti),linear(Fj))),
    true_set(Gi,Ti),
    true((mshare([[_1],[GsOut],[Fj]]),var(_1),var(GsOut),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]),linear(_1),linear(GsOut),linear(Fj);mshare([[GsOut],[Fj]]),var(GsOut),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]),linear(GsOut),linear(Fj))),
    'cover_vector/10/9/$disj/2'(V,Ti),
    true((mshare([[_1],[GsOut],[Fj]]),var(_1),var(GsOut),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]),linear(_1),linear(GsOut),linear(Fj);mshare([[GsOut],[Fj]]),var(GsOut),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]),linear(GsOut),linear(Fj))),
    false_set(Gj,Fj),
    true((mshare([[_1],[GsOut]]),var(_1),var(GsOut),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(_1),linear(GsOut);mshare([[GsOut]]),var(GsOut),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(GsOut))),
    set_subset(Fj,Ti),
    true((mshare([[_1],[GsOut]]),var(_1),var(GsOut),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(_1),linear(GsOut);mshare([[GsOut]]),var(GsOut),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(GsOut))),
    update_circuit(GsIn,Gi,Gj,V,GsIn,GsOut),
    true((mshare([[_1]]),var(_1),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]),linear(_1);ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]))).
cover_vector(exf,_1,[_2|CIs],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[_3]]),var(_1),var(GsOut),var(_3),ground([Gj,V,NumVars,NumGs,GsIn,_2,CIs]),linear(_1),linear(GsOut),linear(_3);mshare([[GsOut],[_3]]),var(GsOut),var(_3),ground([_1,Gj,V,NumVars,NumGs,GsIn,_2,CIs]),linear(GsOut),linear(_3))),
    cover_vector(exf,_3,CIs,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut),
    true((mshare([[_1],[_3]]),var(_1),var(_3),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]),linear(_1),linear(_3);mshare([[_3]]),var(_3),ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]),linear(_3))).
cover_vector(exmcf,_1,[I|_2],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(_1),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(_1),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj))),
    I>=NumVars,
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(_1),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(_1),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),var(GsOut),var(Gi),var(Fi),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]),linear(GsOut),linear(Gi),linear(Fi),linear(Ti),linear(Fj))),
    function(I,GsIn,Gi),
    true((mshare([[_1],[GsOut],[Fi],[Ti],[Fj]]),var(_1),var(GsOut),var(Fi),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]),linear(_1),linear(GsOut),linear(Fi),linear(Ti),linear(Fj);mshare([[GsOut],[Fi],[Ti],[Fj]]),var(GsOut),var(Fi),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]),linear(GsOut),linear(Fi),linear(Ti),linear(Fj))),
    false_set(Gi,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),var(_1),var(GsOut),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(_1),linear(GsOut),linear(Ti),linear(Fj);mshare([[GsOut],[Ti],[Fj]]),var(GsOut),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(GsOut),linear(Ti),linear(Fj))),
    'cover_vector/10/11/$disj/1'(V,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),var(_1),var(GsOut),var(Ti),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(_1),linear(GsOut),linear(Ti),linear(Fj);mshare([[GsOut],[Ti],[Fj]]),var(GsOut),var(Ti),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]),linear(GsOut),linear(Ti),linear(Fj))),
    true_set(Gi,Ti),
    true((mshare([[_1],[GsOut],[Fj]]),var(_1),var(GsOut),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]),linear(_1),linear(GsOut),linear(Fj);mshare([[GsOut],[Fj]]),var(GsOut),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]),linear(GsOut),linear(Fj))),
    'cover_vector/10/11/$disj/2'(V,Ti),
    true((mshare([[_1],[GsOut],[Fj]]),var(_1),var(GsOut),var(Fj),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]),linear(_1),linear(GsOut),linear(Fj);mshare([[GsOut],[Fj]]),var(GsOut),var(Fj),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]),linear(GsOut),linear(Fj))),
    false_set(Gj,Fj),
    true((mshare([[_1],[GsOut]]),var(_1),var(GsOut),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(_1),linear(GsOut);mshare([[GsOut]]),var(GsOut),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(GsOut))),
    'cover_vector/10/11/$disj/3'(Ti,Fj),
    true((mshare([[_1],[GsOut]]),var(_1),var(GsOut),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(_1),linear(GsOut);mshare([[GsOut]]),var(GsOut),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]),linear(GsOut))),
    update_circuit(GsIn,Gi,Gj,V,GsIn,GsOut),
    true((mshare([[_1]]),var(_1),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]),linear(_1);ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]))).
cover_vector(exmcf,_1,[_2|CIs],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[_3]]),var(_1),var(GsOut),var(_3),ground([Gj,V,NumVars,NumGs,GsIn,_2,CIs]),linear(_1),linear(GsOut),linear(_3);mshare([[GsOut],[_3]]),var(GsOut),var(_3),ground([_1,Gj,V,NumVars,NumGs,GsIn,_2,CIs]),linear(GsOut),linear(_3))),
    cover_vector(exmcf,_3,CIs,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut),
    true((mshare([[_1],[_3]]),var(_1),var(_3),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]),linear(_1),linear(_3);mshare([[_3]]),var(_3),ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]),linear(_3))).
cover_vector(nf,_1,_2,Gj,V,NumVars,NumGsIn,GsIn,NumGsOut,GsOut) :-
    true((
        mshare([[NumGsOut],[GsOut],[Fj],[Gs],[Gi]]),
        var(NumGsOut),
        var(GsOut),
        var(Fj),
        var(Gs),
        var(Gi),
        ground([_1,_2,Gj,V,NumVars,NumGsIn,GsIn]),
        linear(NumGsOut),
        linear(GsOut),
        linear(Fj),
        linear(Gs),
        linear(Gi)
    )),
    NumGsOut is NumGsIn+1,
    true((
        mshare([[GsOut],[Fj],[Gs],[Gi]]),
        var(GsOut),
        var(Fj),
        var(Gs),
        var(Gi),
        ground([_1,_2,Gj,V,NumVars,NumGsIn,GsIn,NumGsOut]),
        linear(GsOut),
        linear(Fj),
        linear(Gs),
        linear(Gi)
    )),
    false_set(Gj,Fj),
    true((
        mshare([[GsOut],[Gs],[Gi]]),
        var(GsOut),
        var(Gs),
        var(Gi),
        ground([_1,_2,Gj,V,NumVars,NumGsIn,GsIn,NumGsOut,Fj]),
        linear(GsOut),
        linear(Gs),
        linear(Gi)
    )),
    new_function_CIs(GsIn,function(NumGsIn,Fj,[V],[],[],[],[],[]),NumVars,Gs,Gi),
    true((
        mshare([[GsOut]]),
        var(GsOut),
        ground([_1,_2,Gj,V,NumVars,NumGsIn,GsIn,NumGsOut,Fj,Gs,Gi]),
        linear(GsOut)
    )),
    update_circuit(Gs,Gi,Gj,V,Gs,GsOut),
    true(ground([_1,_2,Gj,V,NumVars,NumGsIn,GsIn,NumGsOut,GsOut,Fj,Gs,Gi])).

:- true pred 'cover_vector/10/1/$disj/1'(V,Ti)
   : ground([V,Ti])
   => ground([V,Ti]).

'cover_vector/10/1/$disj/1'(V,Ti) :-
    true(ground([V,Ti])),
    set_member(V,Ti),
    !,
    true(ground([V,Ti])),
    fail,
    true(fails(_)).
'cover_vector/10/1/$disj/1'(V,Ti).

:- true pred 'cover_vector/10/7/$disj/1'(Ti,Fj)
   : ground([Ti,Fj])
   => ground([Ti,Fj]).

'cover_vector/10/7/$disj/1'(Ti,Fj) :-
    true(ground([Ti,Fj])),
    set_subset(Fj,Ti),
    !,
    true(ground([Ti,Fj])),
    fail,
    true(fails(_)).
'cover_vector/10/7/$disj/1'(Ti,Fj).

:- true pred 'cover_vector/10/9/$disj/1'(V,Fi)
   : ground([V,Fi])
   => ground([V,Fi]).

'cover_vector/10/9/$disj/1'(V,Fi) :-
    true(ground([V,Fi])),
    set_member(V,Fi),
    !,
    true(ground([V,Fi])),
    fail,
    true(fails(_)).
'cover_vector/10/9/$disj/1'(V,Fi).

:- true pred 'cover_vector/10/9/$disj/2'(V,Ti)
   : ground([V,Ti])
   => ground([V,Ti]).

'cover_vector/10/9/$disj/2'(V,Ti) :-
    true(ground([V,Ti])),
    set_member(V,Ti),
    !,
    true(ground([V,Ti])),
    fail,
    true(fails(_)).
'cover_vector/10/9/$disj/2'(V,Ti).

:- true pred 'cover_vector/10/11/$disj/1'(V,Fi)
   : ground([V,Fi])
   => ground([V,Fi]).

'cover_vector/10/11/$disj/1'(V,Fi) :-
    true(ground([V,Fi])),
    set_member(V,Fi),
    !,
    true(ground([V,Fi])),
    fail,
    true(fails(_)).
'cover_vector/10/11/$disj/1'(V,Fi).

:- true pred 'cover_vector/10/11/$disj/2'(V,Ti)
   : ground([V,Ti])
   => ground([V,Ti]).

'cover_vector/10/11/$disj/2'(V,Ti) :-
    true(ground([V,Ti])),
    set_member(V,Ti),
    !,
    true(ground([V,Ti])),
    fail,
    true(fails(_)).
'cover_vector/10/11/$disj/2'(V,Ti).

:- true pred 'cover_vector/10/11/$disj/3'(Ti,Fj)
   : ground([Ti,Fj])
   => ground([Ti,Fj]).

'cover_vector/10/11/$disj/3'(Ti,Fj) :-
    true(ground([Ti,Fj])),
    set_subset(Fj,Ti),
    !,
    true(ground([Ti,Fj])),
    fail,
    true(fails(_)).
'cover_vector/10/11/$disj/3'(Ti,Fj).

:- true pred update_circuit(_A,_1,_2,_3,_4,_B)
   : ( (_A=_4),
       mshare([[_B]]),
       var(_B), ground([_A,_1,_2,_3]), linear(_B) )
   => ground([_A,_1,_2,_3,_B]).

:- true pred update_circuit(_A,_1,_2,_3,_4,_B)
   : ( mshare([[_B]]),
       var(_B), ground([_A,_1,_2,_3,_4]), linear(_B) )
   => ground([_A,_1,_2,_3,_4,_B]).

update_circuit([],_1,_2,_3,_4,[]).
update_circuit([function(K,Tk,Fk,CIk,IPk,ISk,Pk,Sk)|GsIn],Gi,Gj,V,Gs,[function(K,Tko,Fko,CIko,IPko,ISko,Pko,Sko)|GsOut]) :-
    true((
        mshare([[GsOut],[Tko],[Fko],[CIko],[IPko],[ISko],[Pko],[Sko],[I],[_1],[Fi],[_2],[IPi],[ISi],[Pi],[_3],[J],[_4],[Fj],[_5],[_6],[_7],[_8],[Sj],[PiI],[SjJ],[Tk2],[Tk3],[CIk2],[CIk3],[CIk4]]),
        var(GsOut),
        var(Tko),
        var(Fko),
        var(CIko),
        var(IPko),
        var(ISko),
        var(Pko),
        var(Sko),
        var(I),
        var(_1),
        var(Fi),
        var(_2),
        var(IPi),
        var(ISi),
        var(Pi),
        var(_3),
        var(J),
        var(_4),
        var(Fj),
        var(_5),
        var(_6),
        var(_7),
        var(_8),
        var(Sj),
        var(PiI),
        var(SjJ),
        var(Tk2),
        var(Tk3),
        var(CIk2),
        var(CIk3),
        var(CIk4),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk]),
        linear(GsOut),
        linear(Tko),
        linear(Fko),
        linear(CIko),
        linear(IPko),
        linear(ISko),
        linear(Pko),
        linear(Sko),
        linear(I),
        linear(_1),
        linear(Fi),
        linear(_2),
        linear(IPi),
        linear(ISi),
        linear(Pi),
        linear(_3),
        linear(J),
        linear(_4),
        linear(Fj),
        linear(_5),
        linear(_6),
        linear(_7),
        linear(_8),
        linear(Sj),
        linear(PiI),
        linear(SjJ),
        linear(Tk2),
        linear(Tk3),
        linear(CIk2),
        linear(CIk3),
        linear(CIk4)
    )),
    Gi=function(I,_1,Fi,_2,IPi,ISi,Pi,_3),
    true((
        mshare([[GsOut],[Tko],[Fko],[CIko],[IPko],[ISko],[Pko],[Sko],[J],[_4],[Fj],[_5],[_6],[_7],[_8],[Sj],[PiI],[SjJ],[Tk2],[Tk3],[CIk2],[CIk3],[CIk4]]),
        var(GsOut),
        var(Tko),
        var(Fko),
        var(CIko),
        var(IPko),
        var(ISko),
        var(Pko),
        var(Sko),
        var(J),
        var(_4),
        var(Fj),
        var(_5),
        var(_6),
        var(_7),
        var(_8),
        var(Sj),
        var(PiI),
        var(SjJ),
        var(Tk2),
        var(Tk3),
        var(CIk2),
        var(CIk3),
        var(CIk4),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,I,_1,Fi,_2,IPi,ISi,Pi,_3]),
        linear(GsOut),
        linear(Tko),
        linear(Fko),
        linear(CIko),
        linear(IPko),
        linear(ISko),
        linear(Pko),
        linear(Sko),
        linear(J),
        linear(_4),
        linear(Fj),
        linear(_5),
        linear(_6),
        linear(_7),
        linear(_8),
        linear(Sj),
        linear(PiI),
        linear(SjJ),
        linear(Tk2),
        linear(Tk3),
        linear(CIk2),
        linear(CIk3),
        linear(CIk4)
    )),
    Gj=function(J,_4,Fj,_5,_6,_7,_8,Sj),
    true((
        mshare([[GsOut],[Tko],[Fko],[CIko],[IPko],[ISko],[Pko],[Sko],[PiI],[SjJ],[Tk2],[Tk3],[CIk2],[CIk3],[CIk4]]),
        var(GsOut),
        var(Tko),
        var(Fko),
        var(CIko),
        var(IPko),
        var(ISko),
        var(Pko),
        var(Sko),
        var(PiI),
        var(SjJ),
        var(Tk2),
        var(Tk3),
        var(CIk2),
        var(CIk3),
        var(CIk4),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj]),
        linear(GsOut),
        linear(Tko),
        linear(Fko),
        linear(CIko),
        linear(IPko),
        linear(ISko),
        linear(Pko),
        linear(Sko),
        linear(PiI),
        linear(SjJ),
        linear(Tk2),
        linear(Tk3),
        linear(CIk2),
        linear(CIk3),
        linear(CIk4)
    )),
    set_union([I],Pi,PiI),
    true((
        mshare([[GsOut],[Tko],[Fko],[CIko],[IPko],[ISko],[Pko],[Sko],[SjJ],[Tk2],[Tk3],[CIk2],[CIk3],[CIk4]]),
        var(GsOut),
        var(Tko),
        var(Fko),
        var(CIko),
        var(IPko),
        var(ISko),
        var(Pko),
        var(Sko),
        var(SjJ),
        var(Tk2),
        var(Tk3),
        var(CIk2),
        var(CIk3),
        var(CIk4),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI]),
        linear(GsOut),
        linear(Tko),
        linear(Fko),
        linear(CIko),
        linear(IPko),
        linear(ISko),
        linear(Pko),
        linear(Sko),
        linear(SjJ),
        linear(Tk2),
        linear(Tk3),
        linear(CIk2),
        linear(CIk3),
        linear(CIk4)
    )),
    set_union([J],Sj,SjJ),
    true((
        mshare([[GsOut],[Tko],[Fko],[CIko],[IPko],[ISko],[Pko],[Sko],[Tk2],[Tk3],[CIk2],[CIk3],[CIk4]]),
        var(GsOut),
        var(Tko),
        var(Fko),
        var(CIko),
        var(IPko),
        var(ISko),
        var(Pko),
        var(Sko),
        var(Tk2),
        var(Tk3),
        var(CIk2),
        var(CIk3),
        var(CIk4),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ]),
        linear(GsOut),
        linear(Tko),
        linear(Fko),
        linear(CIko),
        linear(IPko),
        linear(ISko),
        linear(Pko),
        linear(Sko),
        linear(Tk2),
        linear(Tk3),
        linear(CIk2),
        linear(CIk3),
        linear(CIk4)
    )),
    'update_circuit/6/2/$disj/1'(K,Tk,Fi,J,Tk2),
    true((
        mshare([[GsOut],[Tko],[Fko],[CIko],[IPko],[ISko],[Pko],[Sko],[Tk3],[CIk2],[CIk3],[CIk4]]),
        var(GsOut),
        var(Tko),
        var(Fko),
        var(CIko),
        var(IPko),
        var(ISko),
        var(Pko),
        var(Sko),
        var(Tk3),
        var(CIk2),
        var(CIk3),
        var(CIk4),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2]),
        linear(GsOut),
        linear(Tko),
        linear(Fko),
        linear(CIko),
        linear(IPko),
        linear(ISko),
        linear(Pko),
        linear(Sko),
        linear(Tk3),
        linear(CIk2),
        linear(CIk3),
        linear(CIk4)
    )),
    'update_circuit/6/2/$disj/2'(K,I,Fj,Tk2,Tk3),
    true((
        mshare([[GsOut],[Tko],[Fko],[CIko],[IPko],[ISko],[Pko],[Sko],[CIk2],[CIk3],[CIk4]]),
        var(GsOut),
        var(Tko),
        var(Fko),
        var(CIko),
        var(IPko),
        var(ISko),
        var(Pko),
        var(Sko),
        var(CIk2),
        var(CIk3),
        var(CIk4),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3]),
        linear(GsOut),
        linear(Tko),
        linear(Fko),
        linear(CIko),
        linear(IPko),
        linear(ISko),
        linear(Pko),
        linear(Sko),
        linear(CIk2),
        linear(CIk3),
        linear(CIk4)
    )),
    'update_circuit/6/2/$disj/3'(V,K,Tko,IPi,ISi,Tk3),
    true((
        mshare([[GsOut],[Fko],[CIko],[IPko],[ISko],[Pko],[Sko],[CIk2],[CIk3],[CIk4]]),
        var(GsOut),
        var(Fko),
        var(CIko),
        var(IPko),
        var(ISko),
        var(Pko),
        var(Sko),
        var(CIk2),
        var(CIk3),
        var(CIk4),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3]),
        linear(GsOut),
        linear(Fko),
        linear(CIko),
        linear(IPko),
        linear(ISko),
        linear(Pko),
        linear(Sko),
        linear(CIk2),
        linear(CIk3),
        linear(CIk4)
    )),
    'update_circuit/6/2/$disj/4'(V,K,Fk,Fko,I),
    true((
        mshare([[GsOut],[CIko],[IPko],[ISko],[Pko],[Sko],[CIk2],[CIk3],[CIk4]]),
        var(GsOut),
        var(CIko),
        var(IPko),
        var(ISko),
        var(Pko),
        var(Sko),
        var(CIk2),
        var(CIk3),
        var(CIk4),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3]),
        linear(GsOut),
        linear(CIko),
        linear(IPko),
        linear(ISko),
        linear(Pko),
        linear(Sko),
        linear(CIk2),
        linear(CIk3),
        linear(CIk4)
    )),
    'update_circuit/6/2/$disj/5'(K,CIk,I,Pi,SjJ,CIk2),
    true((
        mshare([[GsOut],[CIko],[IPko],[ISko],[Pko],[Sko],[CIk3],[CIk4]]),
        var(GsOut),
        var(CIko),
        var(IPko),
        var(ISko),
        var(Pko),
        var(Sko),
        var(CIk3),
        var(CIk4),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2]),
        linear(GsOut),
        linear(CIko),
        linear(IPko),
        linear(ISko),
        linear(Pko),
        linear(Sko),
        linear(CIk3),
        linear(CIk4)
    )),
    'update_circuit/6/2/$disj/6'(V,Fk,CIk,I,CIk2,CIk3),
    true((
        mshare([[GsOut],[CIko],[IPko],[ISko],[Pko],[Sko],[CIk4]]),
        var(GsOut),
        var(CIko),
        var(IPko),
        var(ISko),
        var(Pko),
        var(Sko),
        var(CIk4),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3]),
        linear(GsOut),
        linear(CIko),
        linear(IPko),
        linear(ISko),
        linear(Pko),
        linear(Sko),
        linear(CIk4)
    )),
    'update_circuit/6/2/$disj/7'(V,Gs,K,I,CIk3,CIk4),
    true((
        mshare([[GsOut],[CIko],[IPko],[ISko],[Pko],[Sko]]),
        var(GsOut),
        var(CIko),
        var(IPko),
        var(ISko),
        var(Pko),
        var(Sko),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4]),
        linear(GsOut),
        linear(CIko),
        linear(IPko),
        linear(ISko),
        linear(Pko),
        linear(Sko)
    )),
    'update_circuit/6/2/$disj/8'(K,CIko,I,J,CIk4),
    true((
        mshare([[GsOut],[IPko],[ISko],[Pko],[Sko]]),
        var(GsOut),
        var(IPko),
        var(ISko),
        var(Pko),
        var(Sko),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,CIko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4]),
        linear(GsOut),
        linear(IPko),
        linear(ISko),
        linear(Pko),
        linear(Sko)
    )),
    'update_circuit/6/2/$disj/9'(K,IPk,IPko,I,J),
    true((
        mshare([[GsOut],[ISko],[Pko],[Sko]]),
        var(GsOut),
        var(ISko),
        var(Pko),
        var(Sko),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,CIko,IPko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4]),
        linear(GsOut),
        linear(ISko),
        linear(Pko),
        linear(Sko)
    )),
    'update_circuit/6/2/$disj/10'(K,ISk,ISko,I,J),
    true((
        mshare([[GsOut],[Pko],[Sko]]),
        var(GsOut),
        var(Pko),
        var(Sko),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,CIko,IPko,ISko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4]),
        linear(GsOut),
        linear(Pko),
        linear(Sko)
    )),
    'update_circuit/6/2/$disj/11'(K,Pk,Pko,PiI,SjJ),
    true((
        mshare([[GsOut],[Sko]]),
        var(GsOut),
        var(Sko),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,CIko,IPko,ISko,Pko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4]),
        linear(GsOut),
        linear(Sko)
    )),
    'update_circuit/6/2/$disj/12'(K,Sk,Sko,PiI,SjJ),
    true((
        mshare([[GsOut]]),
        var(GsOut),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,CIko,IPko,ISko,Pko,Sko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4]),
        linear(GsOut)
    )),
    update_circuit(GsIn,Gi,Gj,V,Gs,GsOut),
    true(ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,GsOut,Tko,Fko,CIko,IPko,ISko,Pko,Sko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4])).

:- true pred 'update_circuit/6/2/$disj/1'(K,Tk,Fi,J,Tk2)
   : ( mshare([[Tk2]]),
       var(Tk2), ground([K,Tk,Fi,J]), linear(Tk2) )
   => ground([K,Tk,Fi,J,Tk2]).

'update_circuit/6/2/$disj/1'(K,Tk,Fi,J,Tk2) :-
    true((
        mshare([[Tk2]]),
        var(Tk2),
        ground([K,Tk,Fi,J]),
        linear(Tk2)
    )),
    K=J,
    !,
    true((
        mshare([[Tk2]]),
        var(Tk2),
        ground([K,Tk,Fi,J]),
        linear(Tk2)
    )),
    set_union(Tk,Fi,Tk2),
    true(ground([K,Tk,Fi,J,Tk2])).
'update_circuit/6/2/$disj/1'(K,Tk,Fi,J,Tk2) :-
    true((
        mshare([[Tk2]]),
        var(Tk2),
        ground([K,Tk,Fi,J]),
        linear(Tk2)
    )),
    Tk2=Tk,
    true(ground([K,Tk,Fi,J,Tk2])).

:- true pred 'update_circuit/6/2/$disj/2'(K,I,Fj,Tk2,Tk3)
   : ( mshare([[Tk3]]),
       var(Tk3), ground([K,I,Fj,Tk2]), linear(Tk3) )
   => ground([K,I,Fj,Tk2,Tk3]).

'update_circuit/6/2/$disj/2'(K,I,Fj,Tk2,Tk3) :-
    true((
        mshare([[Tk3]]),
        var(Tk3),
        ground([K,I,Fj,Tk2]),
        linear(Tk3)
    )),
    K=I,
    !,
    true((
        mshare([[Tk3]]),
        var(Tk3),
        ground([K,I,Fj,Tk2]),
        linear(Tk3)
    )),
    set_union(Tk2,Fj,Tk3),
    true(ground([K,I,Fj,Tk2,Tk3])).
'update_circuit/6/2/$disj/2'(K,I,Fj,Tk2,Tk3) :-
    true((
        mshare([[Tk3]]),
        var(Tk3),
        ground([K,I,Fj,Tk2]),
        linear(Tk3)
    )),
    Tk3=Tk2,
    true(ground([K,I,Fj,Tk2,Tk3])).

:- true pred 'update_circuit/6/2/$disj/3'(V,K,Tko,IPi,ISi,Tk3)
   : ( mshare([[Tko]]),
       var(Tko), ground([V,K,IPi,ISi,Tk3]), linear(Tko) )
   => ground([V,K,Tko,IPi,ISi,Tk3]).

'update_circuit/6/2/$disj/3'(V,K,Tko,IPi,ISi,Tk3) :-
    true((
        mshare([[Tko]]),
        var(Tko),
        ground([V,K,IPi,ISi,Tk3]),
        linear(Tko)
    )),
    'update_circuit/6/2/$disj/3/6/1/$disj/1'(K,IPi,ISi),
    !,
    true((
        mshare([[Tko]]),
        var(Tko),
        ground([V,K,IPi,ISi,Tk3]),
        linear(Tko)
    )),
    set_union(Tk3,[V],Tko),
    true(ground([V,K,Tko,IPi,ISi,Tk3])).
'update_circuit/6/2/$disj/3'(V,K,Tko,IPi,ISi,Tk3) :-
    true((
        mshare([[Tko]]),
        var(Tko),
        ground([V,K,IPi,ISi,Tk3]),
        linear(Tko)
    )),
    Tko=Tk3,
    true(ground([V,K,Tko,IPi,ISi,Tk3])).

:- true pred 'update_circuit/6/2/$disj/3/6/1/$disj/1'(K,IPi,ISi)
   : ground([K,IPi,ISi])
   => ground([K,IPi,ISi]).

'update_circuit/6/2/$disj/3/6/1/$disj/1'(K,IPi,ISi) :-
    true(ground([K,IPi,ISi])),
    set_member(K,IPi),
    true(ground([K,IPi,ISi])).
'update_circuit/6/2/$disj/3/6/1/$disj/1'(K,IPi,ISi) :-
    true(ground([K,IPi,ISi])),
    set_member(K,ISi),
    true(ground([K,IPi,ISi])).

:- true pred 'update_circuit/6/2/$disj/4'(V,K,Fk,Fko,I)
   : ( mshare([[Fko]]),
       var(Fko), ground([V,K,Fk,I]), linear(Fko) )
   => ground([V,K,Fk,Fko,I]).

'update_circuit/6/2/$disj/4'(V,K,Fk,Fko,I) :-
    true((
        mshare([[Fko]]),
        var(Fko),
        ground([V,K,Fk,I]),
        linear(Fko)
    )),
    K=I,
    !,
    true((
        mshare([[Fko]]),
        var(Fko),
        ground([V,K,Fk,I]),
        linear(Fko)
    )),
    set_union(Fk,[V],Fko),
    true(ground([V,K,Fk,Fko,I])).
'update_circuit/6/2/$disj/4'(V,K,Fk,Fko,I) :-
    true((
        mshare([[Fko]]),
        var(Fko),
        ground([V,K,Fk,I]),
        linear(Fko)
    )),
    Fko=Fk,
    true(ground([V,K,Fk,Fko,I])).

:- true pred 'update_circuit/6/2/$disj/5'(K,CIk,I,Pi,SjJ,CIk2)
   : ( mshare([[CIk2]]),
       var(CIk2), ground([K,CIk,I,Pi,SjJ]), linear(CIk2) )
   => ground([K,CIk,I,Pi,SjJ,CIk2]).

'update_circuit/6/2/$disj/5'(K,CIk,I,Pi,SjJ,CIk2) :-
    true((
        mshare([[CIk2]]),
        var(CIk2),
        ground([K,CIk,I,Pi,SjJ]),
        linear(CIk2)
    )),
    'update_circuit/6/2/$disj/5/6/1/$disj/1'(K,I,Pi),
    !,
    true((
        mshare([[CIk2]]),
        var(CIk2),
        ground([K,CIk,I,Pi,SjJ]),
        linear(CIk2)
    )),
    set_difference(CIk,SjJ,CIk2),
    true(ground([K,CIk,I,Pi,SjJ,CIk2])).
'update_circuit/6/2/$disj/5'(K,CIk,I,Pi,SjJ,CIk2) :-
    true((
        mshare([[CIk2]]),
        var(CIk2),
        ground([K,CIk,I,Pi,SjJ]),
        linear(CIk2)
    )),
    CIk2=CIk,
    true(ground([K,CIk,I,Pi,SjJ,CIk2])).

:- true pred 'update_circuit/6/2/$disj/5/6/1/$disj/1'(K,I,Pi)
   : ground([K,I,Pi])
   => ground([K,I,Pi]).

'update_circuit/6/2/$disj/5/6/1/$disj/1'(K,I,Pi) :-
    true(ground([K,I,Pi])),
    set_member(K,Pi),
    true(ground([K,I,Pi])).
'update_circuit/6/2/$disj/5/6/1/$disj/1'(K,I,Pi) :-
    true(ground([K,I,Pi])),
    K=I,
    true(ground([K,I,Pi])).

:- true pred 'update_circuit/6/2/$disj/6'(V,Fk,CIk,I,CIk2,CIk3)
   : ( mshare([[CIk3]]),
       var(CIk3), ground([V,Fk,CIk,I,CIk2]), linear(CIk3) )
   => ground([V,Fk,CIk,I,CIk2,CIk3]).

'update_circuit/6/2/$disj/6'(V,Fk,CIk,I,CIk2,CIk3) :-
    true((
        mshare([[CIk3]]),
        var(CIk3),
        ground([V,Fk,CIk,I,CIk2]),
        linear(CIk3)
    )),
    set_member(I,CIk),
    true((
        mshare([[CIk3]]),
        var(CIk3),
        ground([V,Fk,CIk,I,CIk2]),
        linear(CIk3)
    )),
    set_member(V,Fk),
    !,
    true((
        mshare([[CIk3]]),
        var(CIk3),
        ground([V,Fk,CIk,I,CIk2]),
        linear(CIk3)
    )),
    set_difference(CIk2,[I],CIk3),
    true(ground([V,Fk,CIk,I,CIk2,CIk3])).
'update_circuit/6/2/$disj/6'(V,Fk,CIk,I,CIk2,CIk3) :-
    true((
        mshare([[CIk3]]),
        var(CIk3),
        ground([V,Fk,CIk,I,CIk2]),
        linear(CIk3)
    )),
    CIk3=CIk2,
    true(ground([V,Fk,CIk,I,CIk2,CIk3])).

:- true pred 'update_circuit/6/2/$disj/7'(V,Gs,K,I,CIk3,CIk4)
   : ( mshare([[CIk4]]),
       var(CIk4), ground([V,Gs,K,I,CIk3]), linear(CIk4) )
   => ground([V,Gs,K,I,CIk3,CIk4]).

'update_circuit/6/2/$disj/7'(V,Gs,K,I,CIk3,CIk4) :-
    true((
        mshare([[CIk4]]),
        var(CIk4),
        ground([V,Gs,K,I,CIk3]),
        linear(CIk4)
    )),
    K=I,
    !,
    true((
        mshare([[CIk4]]),
        var(CIk4),
        ground([V,Gs,K,I,CIk3]),
        linear(CIk4)
    )),
    exclude_if_vector_in_false_set(CIk3,Gs,V,CIk4),
    true(ground([V,Gs,K,I,CIk3,CIk4])).
'update_circuit/6/2/$disj/7'(V,Gs,K,I,CIk3,CIk4) :-
    true((
        mshare([[CIk4]]),
        var(CIk4),
        ground([V,Gs,K,I,CIk3]),
        linear(CIk4)
    )),
    CIk4=CIk3,
    true(ground([V,Gs,K,I,CIk3,CIk4])).

:- true pred 'update_circuit/6/2/$disj/8'(K,CIko,I,J,CIk4)
   : ( mshare([[CIko]]),
       var(CIko), ground([K,I,J,CIk4]), linear(CIko) )
   => ground([K,CIko,I,J,CIk4]).

'update_circuit/6/2/$disj/8'(K,CIko,I,J,CIk4) :-
    true((
        mshare([[CIko]]),
        var(CIko),
        ground([K,I,J,CIk4]),
        linear(CIko)
    )),
    K=J,
    !,
    true((
        mshare([[CIko]]),
        var(CIko),
        ground([K,I,J,CIk4]),
        linear(CIko)
    )),
    set_difference(CIk4,[I],CIko),
    true(ground([K,CIko,I,J,CIk4])).
'update_circuit/6/2/$disj/8'(K,CIko,I,J,CIk4) :-
    true((
        mshare([[CIko]]),
        var(CIko),
        ground([K,I,J,CIk4]),
        linear(CIko)
    )),
    CIko=CIk4,
    true(ground([K,CIko,I,J,CIk4])).

:- true pred 'update_circuit/6/2/$disj/9'(K,IPk,IPko,I,J)
   : ( mshare([[IPko]]),
       var(IPko), ground([K,IPk,I,J]), linear(IPko) )
   => ground([K,IPk,IPko,I,J]).

'update_circuit/6/2/$disj/9'(K,IPk,IPko,I,J) :-
    true((
        mshare([[IPko]]),
        var(IPko),
        ground([K,IPk,I,J]),
        linear(IPko)
    )),
    K=J,
    !,
    true((
        mshare([[IPko]]),
        var(IPko),
        ground([K,IPk,I,J]),
        linear(IPko)
    )),
    set_union(IPk,[I],IPko),
    true(ground([K,IPk,IPko,I,J])).
'update_circuit/6/2/$disj/9'(K,IPk,IPko,I,J) :-
    true((
        mshare([[IPko]]),
        var(IPko),
        ground([K,IPk,I,J]),
        linear(IPko)
    )),
    IPko=IPk,
    true(ground([K,IPk,IPko,I,J])).

:- true pred 'update_circuit/6/2/$disj/10'(K,ISk,ISko,I,J)
   : ( mshare([[ISko]]),
       var(ISko), ground([K,ISk,I,J]), linear(ISko) )
   => ground([K,ISk,ISko,I,J]).

'update_circuit/6/2/$disj/10'(K,ISk,ISko,I,J) :-
    true((
        mshare([[ISko]]),
        var(ISko),
        ground([K,ISk,I,J]),
        linear(ISko)
    )),
    K=I,
    !,
    true((
        mshare([[ISko]]),
        var(ISko),
        ground([K,ISk,I,J]),
        linear(ISko)
    )),
    set_union(ISk,[J],ISko),
    true(ground([K,ISk,ISko,I,J])).
'update_circuit/6/2/$disj/10'(K,ISk,ISko,I,J) :-
    true((
        mshare([[ISko]]),
        var(ISko),
        ground([K,ISk,I,J]),
        linear(ISko)
    )),
    ISko=ISk,
    true(ground([K,ISk,ISko,I,J])).

:- true pred 'update_circuit/6/2/$disj/11'(K,Pk,Pko,PiI,SjJ)
   : ( mshare([[Pko]]),
       var(Pko), ground([K,Pk,PiI,SjJ]), linear(Pko) )
   => ground([K,Pk,Pko,PiI,SjJ]).

'update_circuit/6/2/$disj/11'(K,Pk,Pko,PiI,SjJ) :-
    true((
        mshare([[Pko]]),
        var(Pko),
        ground([K,Pk,PiI,SjJ]),
        linear(Pko)
    )),
    set_member(K,SjJ),
    !,
    true((
        mshare([[Pko]]),
        var(Pko),
        ground([K,Pk,PiI,SjJ]),
        linear(Pko)
    )),
    set_union(Pk,PiI,Pko),
    true(ground([K,Pk,Pko,PiI,SjJ])).
'update_circuit/6/2/$disj/11'(K,Pk,Pko,PiI,SjJ) :-
    true((
        mshare([[Pko]]),
        var(Pko),
        ground([K,Pk,PiI,SjJ]),
        linear(Pko)
    )),
    Pko=Pk,
    true(ground([K,Pk,Pko,PiI,SjJ])).

:- true pred 'update_circuit/6/2/$disj/12'(K,Sk,Sko,PiI,SjJ)
   : ( mshare([[Sko]]),
       var(Sko), ground([K,Sk,PiI,SjJ]), linear(Sko) )
   => ground([K,Sk,Sko,PiI,SjJ]).

'update_circuit/6/2/$disj/12'(K,Sk,Sko,PiI,SjJ) :-
    true((
        mshare([[Sko]]),
        var(Sko),
        ground([K,Sk,PiI,SjJ]),
        linear(Sko)
    )),
    set_member(K,PiI),
    !,
    true((
        mshare([[Sko]]),
        var(Sko),
        ground([K,Sk,PiI,SjJ]),
        linear(Sko)
    )),
    set_union(Sk,SjJ,Sko),
    true(ground([K,Sk,Sko,PiI,SjJ])).
'update_circuit/6/2/$disj/12'(K,Sk,Sko,PiI,SjJ) :-
    true((
        mshare([[Sko]]),
        var(Sko),
        ground([K,Sk,PiI,SjJ]),
        linear(Sko)
    )),
    Sko=Sk,
    true(ground([K,Sk,Sko,PiI,SjJ])).

:- true pred exclude_if_vector_in_false_set(_A,_1,_2,CIsOut)
   : ( mshare([[CIsOut]]),
       var(CIsOut), ground([_A,_1,_2]), linear(CIsOut) )
   => ground([_A,_1,_2,CIsOut]).

exclude_if_vector_in_false_set([],_1,_2,[]).
exclude_if_vector_in_false_set([K|CIsIn],Gs,V,CIsOut) :-
    true((
        mshare([[CIsOut],[Gk],[Fk]]),
        var(CIsOut),
        var(Gk),
        var(Fk),
        ground([Gs,V,K,CIsIn]),
        linear(CIsOut),
        linear(Gk),
        linear(Fk)
    )),
    function(K,Gs,Gk),
    true((
        mshare([[CIsOut],[Fk]]),
        var(CIsOut),
        var(Fk),
        ground([Gs,V,K,CIsIn,Gk]),
        linear(CIsOut),
        linear(Fk)
    )),
    false_set(Gk,Fk),
    true((
        mshare([[CIsOut]]),
        var(CIsOut),
        ground([Gs,V,K,CIsIn,Gk,Fk]),
        linear(CIsOut)
    )),
    set_member(V,Fk),
    !,
    true((
        mshare([[CIsOut]]),
        var(CIsOut),
        ground([Gs,V,K,CIsIn,Gk,Fk]),
        linear(CIsOut)
    )),
    exclude_if_vector_in_false_set(CIsIn,Gs,V,CIsOut),
    true(ground([Gs,V,CIsOut,K,CIsIn,Gk,Fk])).
exclude_if_vector_in_false_set([K|CIsIn],Gs,V,[K|CIsOut]) :-
    true((
        mshare([[CIsOut]]),
        var(CIsOut),
        ground([Gs,V,K,CIsIn]),
        linear(CIsOut)
    )),
    exclude_if_vector_in_false_set(CIsIn,Gs,V,CIsOut),
    true(ground([Gs,V,K,CIsIn,CIsOut])).

:- true pred add_necessary_functions(NumVars,NumGsIn,GsIn,NumGsOut,GsOut)
   : ( mshare([[NumGsOut],[GsOut]]),
       var(NumGsOut), var(GsOut), ground([NumVars,NumGsIn,GsIn]), linear(NumGsOut), linear(GsOut) )
   => ground([NumVars,NumGsIn,GsIn,NumGsOut,GsOut]).

add_necessary_functions(NumVars,NumGsIn,GsIn,NumGsOut,GsOut) :-
    true((
        mshare([[NumGsOut],[GsOut]]),
        var(NumGsOut),
        var(GsOut),
        ground([NumVars,NumGsIn,GsIn]),
        linear(NumGsOut),
        linear(GsOut)
    )),
    add_necessary_functions(NumVars,NumVars,NumGsIn,GsIn,NumGsOut,GsOut),
    true(ground([NumVars,NumGsIn,GsIn,NumGsOut,GsOut])).

:- true pred add_necessary_functions(NumGs,_1,NumGsIn,Gs,NumGsOut,GsOut)
   : ( (NumGs=_1),
       mshare([[NumGsOut],[GsOut]]),
       var(NumGsOut), var(GsOut), ground([NumGs,NumGsIn,Gs]), linear(NumGsOut), linear(GsOut) )
   => ground([NumGs,NumGsIn,Gs,NumGsOut,GsOut]).

:- true pred add_necessary_functions(NumGs,_1,NumGsIn,Gs,NumGsOut,GsOut)
   : ( mshare([[NumGsOut],[GsOut]]),
       var(NumGsOut), var(GsOut), ground([NumGs,_1,NumGsIn,Gs]), linear(NumGsOut), linear(GsOut) )
   => ground([NumGs,_1,NumGsIn,Gs,NumGsOut,GsOut]).

add_necessary_functions(NumGs,_1,NumGs,Gs,NumGs,Gs) :-
    !,
    true(ground([NumGs,_1,Gs])).
add_necessary_functions(K,NumVars,NumGsIn,GsIn,NumGsOut,GsOut) :-
    true((
        mshare([[NumGsOut],[GsOut],[Gk],[V],[Fk],[Gs],[Gl],[Gk1],[Gs1],[NumGs1],[K1]]),
        var(NumGsOut),
        var(GsOut),
        var(Gk),
        var(V),
        var(Fk),
        var(Gs),
        var(Gl),
        var(Gk1),
        var(Gs1),
        var(NumGs1),
        var(K1),
        ground([K,NumVars,NumGsIn,GsIn]),
        linear(NumGsOut),
        linear(GsOut),
        linear(Gk),
        linear(V),
        linear(Fk),
        linear(Gs),
        linear(Gl),
        linear(Gk1),
        linear(Gs1),
        linear(NumGs1),
        linear(K1)
    )),
    function(K,GsIn,Gk),
    true((
        mshare([[NumGsOut],[GsOut],[V],[Fk],[Gs],[Gl],[Gk1],[Gs1],[NumGs1],[K1]]),
        var(NumGsOut),
        var(GsOut),
        var(V),
        var(Fk),
        var(Gs),
        var(Gl),
        var(Gk1),
        var(Gs1),
        var(NumGs1),
        var(K1),
        ground([K,NumVars,NumGsIn,GsIn,Gk]),
        linear(NumGsOut),
        linear(GsOut),
        linear(V),
        linear(Fk),
        linear(Gs),
        linear(Gl),
        linear(Gk1),
        linear(Gs1),
        linear(NumGs1),
        linear(K1)
    )),
    function_type(NumVars,NumGsIn,GsIn,Gk,nf,V),
    !,
    true((
        mshare([[NumGsOut],[GsOut],[Fk],[Gs],[Gl],[Gk1],[Gs1],[NumGs1],[K1]]),
        var(NumGsOut),
        var(GsOut),
        var(Fk),
        var(Gs),
        var(Gl),
        var(Gk1),
        var(Gs1),
        var(NumGs1),
        var(K1),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V]),
        linear(NumGsOut),
        linear(GsOut),
        linear(Fk),
        linear(Gs),
        linear(Gl),
        linear(Gk1),
        linear(Gs1),
        linear(NumGs1),
        linear(K1)
    )),
    false_set(Gk,Fk),
    true((
        mshare([[NumGsOut],[GsOut],[Gs],[Gl],[Gk1],[Gs1],[NumGs1],[K1]]),
        var(NumGsOut),
        var(GsOut),
        var(Gs),
        var(Gl),
        var(Gk1),
        var(Gs1),
        var(NumGs1),
        var(K1),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V,Fk]),
        linear(NumGsOut),
        linear(GsOut),
        linear(Gs),
        linear(Gl),
        linear(Gk1),
        linear(Gs1),
        linear(NumGs1),
        linear(K1)
    )),
    new_function_CIs(GsIn,function(NumGsIn,Fk,[V],[],[],[],[],[]),NumVars,Gs,Gl),
    true((
        mshare([[NumGsOut],[GsOut],[Gk1],[Gs1],[NumGs1],[K1]]),
        var(NumGsOut),
        var(GsOut),
        var(Gk1),
        var(Gs1),
        var(NumGs1),
        var(K1),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V,Fk,Gs,Gl]),
        linear(NumGsOut),
        linear(GsOut),
        linear(Gk1),
        linear(Gs1),
        linear(NumGs1),
        linear(K1)
    )),
    function(K,Gs,Gk1),
    true((
        mshare([[NumGsOut],[GsOut],[Gs1],[NumGs1],[K1]]),
        var(NumGsOut),
        var(GsOut),
        var(Gs1),
        var(NumGs1),
        var(K1),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V,Fk,Gs,Gl,Gk1]),
        linear(NumGsOut),
        linear(GsOut),
        linear(Gs1),
        linear(NumGs1),
        linear(K1)
    )),
    update_circuit(Gs,Gl,Gk1,V,Gs,Gs1),
    true((
        mshare([[NumGsOut],[GsOut],[NumGs1],[K1]]),
        var(NumGsOut),
        var(GsOut),
        var(NumGs1),
        var(K1),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V,Fk,Gs,Gl,Gk1,Gs1]),
        linear(NumGsOut),
        linear(GsOut),
        linear(NumGs1),
        linear(K1)
    )),
    NumGs1 is NumGsIn+1,
    true((
        mshare([[NumGsOut],[GsOut],[K1]]),
        var(NumGsOut),
        var(GsOut),
        var(K1),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V,Fk,Gs,Gl,Gk1,Gs1,NumGs1]),
        linear(NumGsOut),
        linear(GsOut),
        linear(K1)
    )),
    K1 is K+1,
    true((
        mshare([[NumGsOut],[GsOut]]),
        var(NumGsOut),
        var(GsOut),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V,Fk,Gs,Gl,Gk1,Gs1,NumGs1,K1]),
        linear(NumGsOut),
        linear(GsOut)
    )),
    add_necessary_functions(K1,NumVars,NumGs1,Gs1,NumGsOut,GsOut),
    true(ground([K,NumVars,NumGsIn,GsIn,NumGsOut,GsOut,Gk,V,Fk,Gs,Gl,Gk1,Gs1,NumGs1,K1])).
add_necessary_functions(K,NumVars,NumGsIn,GsIn,NumGsOut,GsOut) :-
    true((
        mshare([[NumGsOut],[GsOut],[K1]]),
        var(NumGsOut),
        var(GsOut),
        var(K1),
        ground([K,NumVars,NumGsIn,GsIn]),
        linear(NumGsOut),
        linear(GsOut),
        linear(K1)
    )),
    K1 is K+1,
    true((
        mshare([[NumGsOut],[GsOut]]),
        var(NumGsOut),
        var(GsOut),
        ground([K,NumVars,NumGsIn,GsIn,K1]),
        linear(NumGsOut),
        linear(GsOut)
    )),
    add_necessary_functions(K1,NumVars,NumGsIn,GsIn,NumGsOut,GsOut),
    true(ground([K,NumVars,NumGsIn,GsIn,NumGsOut,GsOut,K1])).

:- true pred new_function_CIs(GsIn,_A,NumVars,_B,GlOut)
   : ( (_A=function(_C,_D,[_E],[],[],[],[],[])),
       mshare([[_B],[GlOut]]),
       var(_B), var(GlOut), ground([GsIn,NumVars,_C,_D,_E]), linear(_B), linear(GlOut) )
   => ground([GsIn,NumVars,_B,GlOut,_C,_D,_E]).

new_function_CIs(GsIn,function(L,Tl,Fl,_1,IPl,ISl,Pl,Sl),NumVars,[GlOut|GsOut],GlOut) :-
    true((
        mshare([[GlOut],[GsOut],[CIlo]]),
        var(GlOut),
        var(GsOut),
        var(CIlo),
        ground([GsIn,NumVars,L,Tl,Fl,_1,IPl,ISl,Pl,Sl]),
        linear(GlOut),
        linear(GsOut),
        linear(CIlo)
    )),
    new_function_CIs(GsIn,L,Fl,NumVars,GsOut,[],CIlo),
    true((
        mshare([[GlOut]]),
        var(GlOut),
        ground([GsIn,NumVars,L,Tl,Fl,_1,IPl,ISl,Pl,Sl,GsOut,CIlo]),
        linear(GlOut)
    )),
    GlOut=function(L,Tl,Fl,CIlo,IPl,ISl,Pl,Sl),
    true(ground([GsIn,NumVars,GlOut,L,Tl,Fl,_1,IPl,ISl,Pl,Sl,GsOut,CIlo])).

:- true pred new_function_CIs(_A,_1,_2,_3,_B,CIl,CIlOut)
   : ( (CIl=[]),
       mshare([[_B],[CIlOut]]),
       var(_B), var(CIlOut), ground([_A,_1,_2,_3]), linear(_B), linear(CIlOut) )
   => ground([_A,_1,_2,_3,_B,CIlOut]).

:- true pred new_function_CIs(_A,_1,_2,_3,_B,CIl,CIlOut)
   : ( mshare([[_B],[CIlOut]]),
       var(_B), var(CIlOut), ground([_A,_1,_2,_3,CIl]), linear(_B), linear(CIlOut) )
   => ground([_A,_1,_2,_3,_B,CIl,CIlOut]).

:- true pred new_function_CIs(_A,_1,_2,_3,_B,CIl,CIlOut)
   : ( (CIl=[_C|_D]),
       mshare([[_B],[CIlOut]]),
       var(_B), var(CIlOut), ground([_A,_1,_2,_3,_C,_D]), linear(_B), linear(CIlOut) )
   => ground([_A,_1,_2,_3,_B,CIlOut,_C,_D]).

new_function_CIs([],_1,_2,_3,[],CIl,CIl).
new_function_CIs([function(K,Tk,Fk,CIk,IPk,ISk,Pk,Sk)|GsIn],L,Fl,NumVars,[function(K,Tk,Fk,CIko,IPk,ISk,Pk,Sk)|GsOut],CIlIn,CIlOut) :-
    true((
        mshare([[CIlOut],[GsOut],[CIko]]),
        var(CIlOut),
        var(GsOut),
        var(CIko),
        ground([L,Fl,NumVars,CIlIn,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk]),
        linear(CIlOut),
        linear(GsOut),
        linear(CIko)
    )),
    set_intersection(Fl,Fk,[]),
    !,
    true((
        mshare([[CIlOut],[GsOut],[CIko]]),
        var(CIlOut),
        var(GsOut),
        var(CIko),
        ground([L,Fl,NumVars,CIlIn,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk]),
        linear(CIlOut),
        linear(GsOut),
        linear(CIko)
    )),
    'new_function_CIs/7/2/$disj/1'(L,NumVars,K,CIk,CIko),
    true((
        mshare([[CIlOut],[GsOut]]),
        var(CIlOut),
        var(GsOut),
        ground([L,Fl,NumVars,CIlIn,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,CIko]),
        linear(CIlOut),
        linear(GsOut)
    )),
    new_function_CIs(GsIn,L,Fl,NumVars,GsOut,[K|CIlIn],CIlOut),
    true(ground([L,Fl,NumVars,CIlIn,CIlOut,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,GsOut,CIko])).
new_function_CIs([Gk|GsIn],L,Fl,NumVars,[Gk|GsOut],CIlIn,CIlOut) :-
    true((
        mshare([[CIlOut],[GsOut]]),
        var(CIlOut),
        var(GsOut),
        ground([L,Fl,NumVars,CIlIn,Gk,GsIn]),
        linear(CIlOut),
        linear(GsOut)
    )),
    new_function_CIs(GsIn,L,Fl,NumVars,GsOut,CIlIn,CIlOut),
    true(ground([L,Fl,NumVars,CIlIn,CIlOut,Gk,GsIn,GsOut])).

:- true pred 'new_function_CIs/7/2/$disj/1'(L,NumVars,K,CIk,CIko)
   : ( mshare([[CIko]]),
       var(CIko), ground([L,NumVars,K,CIk]), linear(CIko) )
   => ground([L,NumVars,K,CIk,CIko]).

'new_function_CIs/7/2/$disj/1'(L,NumVars,K,CIk,CIko) :-
    true((
        mshare([[CIko]]),
        var(CIko),
        ground([L,NumVars,K,CIk]),
        linear(CIko)
    )),
    K>=NumVars,
    !,
    true((
        mshare([[CIko]]),
        var(CIko),
        ground([L,NumVars,K,CIk]),
        linear(CIko)
    )),
    set_union(CIk,[L],CIko),
    true(ground([L,NumVars,K,CIk,CIko])).
'new_function_CIs/7/2/$disj/1'(L,NumVars,K,CIk,CIko) :-
    true((
        mshare([[CIko]]),
        var(CIko),
        ground([L,NumVars,K,CIk]),
        linear(CIko)
    )),
    CIko=CIk,
    true(ground([L,NumVars,K,CIk,CIko])).

:- true pred function_type(NumVars,NumGs,Gs,Gk,Type,Vector)
   : ( (Type=nf),
       mshare([[Vector]]),
       var(Vector), ground([NumVars,NumGs,Gs,Gk]), linear(Vector) )
   => ground([NumVars,NumGs,Gs,Gk,Vector]).

function_type(NumVars,NumGs,Gs,Gk,Type,Vector) :-
    true((
        mshare([[Vector],[Tk],[_1],[_2]]),
        var(Vector),
        var(Tk),
        var(_1),
        var(_2),
        ground([NumVars,NumGs,Gs,Gk,Type]),
        linear(Vector),
        linear(Tk),
        linear(_1),
        linear(_2)
    )),
    true_set(Gk,Tk),
    true((
        mshare([[Vector],[_1],[_2]]),
        var(Vector),
        var(_1),
        var(_2),
        ground([NumVars,NumGs,Gs,Gk,Type,Tk]),
        linear(Vector),
        linear(_1),
        linear(_2)
    )),
    select_vector(Tk,Gk,NumVars,NumGs,Gs,dummy,0,nf,999,_1,Vector,Type,_2),
    true(ground([NumVars,NumGs,Gs,Gk,Type,Vector,Tk,_1,_2])).

:- true pred test_bounds(_1,NumGs,_2)
   : ground([_1,NumGs,_2])
   => ground([_1,NumGs,_2]).

test_bounds(_1,NumGs,_2) :-
    true((
        mshare([[Bound]]),
        var(Bound),
        ground([_1,NumGs,_2]),
        linear(Bound)
    )),
    access(bound,Bound),
    true((
        mshare([[Bound]]),
        ground([_1,NumGs,_2])
    )),
    NumGs<Bound,
    true(ground([_1,NumGs,_2,Bound])).

:- true pred update_bounds(_1,NumGs,_2)
   : ground([_1,NumGs,_2])
   => ground([_1,NumGs,_2]).

:- true pred update_bounds(_1,NumGs,_2)
   : ( (NumGs=21),
       mshare([[_1],[_2]]),
       var(_1), var(_2), linear(_1), linear(_2) )
   => ( mshare([[_1],[_2]]),
        var(_1), var(_2), linear(_1), linear(_2) ).

:- true pred update_bounds(_1,NumGs,_2)
   : ( (NumGs=100),
       mshare([[_1],[_2]]),
       var(_1), var(_2), linear(_1), linear(_2) )
   => ( mshare([[_1],[_2]]),
        var(_1), var(_2), linear(_1), linear(_2) ).

update_bounds(_1,NumGs,_2) :-
    true((mshare([[_1],[_2]]),var(_1),var(_2),ground([NumGs]),linear(_1),linear(_2);ground([_1,NumGs,_2]))),
    set(bound,NumGs),
    true((mshare([[_1],[_2]]),var(_1),var(_2),ground([NumGs]),linear(_1),linear(_2);ground([_1,NumGs,_2]))).

:- true pred set(N,A)
   : ( (N=bound), ground([A]) )
   => ground([A]).

set(N,A) :-
    true(ground([N,A])),
    'set/2/1/$disj/1'(N),
    true(ground([N,A])),
    asserta(state_(N,A)),
    true(ground([N,A])).

:- true pred 'set/2/1/$disj/1'(N)
   : ground([N])
   => ground([N]).

'set/2/1/$disj/1'(N) :-
    true((
        mshare([[_1]]),
        var(_1),
        ground([N]),
        linear(_1)
    )),
    retract(state_(N,_1)),
    !,
    true((
        mshare([[_1]]),
        ground([N])
    )),
    true,
    true((
        mshare([[_1]]),
        ground([N])
    )).
'set/2/1/$disj/1'(N).

:- true pred access(N,A)
   : ( (N=bound),
       mshare([[A]]),
       var(A), linear(A) )
   => mshare([[A]]).

access(N,A) :-
    true((
        mshare([[A]]),
        var(A),
        ground([N]),
        linear(A)
    )),
    state_(N,A),
    true((
        mshare([[A]]),
        ground([N])
    )).

write_gates([]).
write_gates([Gi|Gs]) :-
    function_number(Gi,I),
    write('gate #'),
    write(I),
    write(' inputs:   '),
    immediate_predecessors(Gi,IPi),
    write(IPi),
    nl,
    write_gates(Gs).

:- true pred function(I,_A,Gi)
   : ( mshare([[Gi]]),
       var(Gi), ground([I,_A]), linear(Gi) )
   => ground([I,_A,Gi]).

function(I,[Gi|_1],Gi) :-
    true(ground([I,Gi,_1])),
    function_number(Gi,I),
    !,
    true(ground([I,Gi,_1])).
function(I,[_1|Gs],Gi) :-
    true((
        mshare([[Gi]]),
        var(Gi),
        ground([I,_1,Gs]),
        linear(Gi)
    )),
    function(I,Gs,Gi),
    true(ground([I,Gi,_1,Gs])).

:- true pred function_number(_A,I)
   : ( mshare([[I]]),
       var(I), ground([_A]), linear(I) )
   => ground([_A,I]).

:- true pred function_number(_A,I)
   : ground([_A,I])
   => ground([_A,I]).

function_number(function(I,_1,_2,_3,_4,_5,_6,_7),I).

:- true pred true_set(_A,T)
   : ( mshare([[T]]),
       var(T), ground([_A]), linear(T) )
   => ground([_A,T]).

true_set(function(_1,T,_2,_3,_4,_5,_6,_7),T).

:- true pred false_set(_A,F)
   : ( mshare([[F]]),
       var(F), ground([_A]), linear(F) )
   => ground([_A,F]).

false_set(function(_1,_2,F,_3,_4,_5,_6,_7),F).

:- true pred conceivable_inputs(_A,CI)
   : ( mshare([[CI]]),
       var(CI), ground([_A]), linear(CI) )
   => ground([_A,CI]).

conceivable_inputs(function(_1,_2,_3,CI,_4,_5,_6,_7),CI).

:- true pred immediate_predecessors(_A,IP)
   : ( mshare([[IP]]),
       var(IP), ground([_A]), linear(IP) )
   => ground([_A,IP]).

immediate_predecessors(function(_1,_2,_3,_4,IP,_5,_6,_7),IP).

immediate_successors(function(_1,_2,_3,_4,_5,IS,_6,_7),IS).

predecessors(function(_1,_2,_3,_4,_5,_6,P,_7),P).

successors(function(_1,_2,_3,_4,_5,_6,_7,S),S).

:- true pred set_union(_A,_B,_C)
   : ( (_A=[_D]),
       mshare([[_C]]),
       var(_C), ground([_B,_D]), linear(_C) )
   => ground([_B,_C,_D]).

:- true pred set_union(_A,_B,_C)
   : ( mshare([[_C]]),
       var(_C), ground([_A,_B]), linear(_C) )
   => ground([_A,_B,_C]).

:- true pred set_union(_A,_B,_C)
   : ( (_B=[_D]),
       mshare([[_C]]),
       var(_C), ground([_A,_D]), linear(_C) )
   => ground([_A,_C,_D]).

:- true pred set_union(_A,_B,_C)
   : ( (_A=[_D|_E]),
       mshare([[_C]]),
       var(_C), ground([_B,_D,_E]), linear(_C) )
   => ground([_B,_C,_D,_E]).

:- true pred set_union(_A,_B,_C)
   : ( (_B=[_D|_E]),
       mshare([[_C]]),
       var(_C), ground([_A,_D,_E]), linear(_C) )
   => ground([_A,_C,_D,_E]).

set_union([],[],[]).
set_union([],[X|L2],[X|L2]).
set_union([X|L1],[],[X|L1]).
set_union([X|L1],[X|L2],[X|L3]) :-
    true((
        mshare([[L3]]),
        var(L3),
        ground([X,L1,L2]),
        linear(L3)
    )),
    set_union(L1,L2,L3),
    true(ground([X,L1,L2,L3])).
set_union([X|L1],[Y|L2],[X|L3]) :-
    true((
        mshare([[L3]]),
        var(L3),
        ground([X,L1,Y,L2]),
        linear(L3)
    )),
    X<Y,
    true((
        mshare([[L3]]),
        var(L3),
        ground([X,L1,Y,L2]),
        linear(L3)
    )),
    set_union(L1,[Y|L2],L3),
    true(ground([X,L1,Y,L2,L3])).
set_union([X|L1],[Y|L2],[Y|L3]) :-
    true((
        mshare([[L3]]),
        var(L3),
        ground([X,L1,Y,L2]),
        linear(L3)
    )),
    X>Y,
    true((
        mshare([[L3]]),
        var(L3),
        ground([X,L1,Y,L2]),
        linear(L3)
    )),
    set_union([X|L1],L2,L3),
    true(ground([X,L1,Y,L2,L3])).

:- true pred set_intersection(_A,_B,L3)
   : ( (L3=[]), ground([_A,_B]) )
   => ground([_A,_B]).

:- true pred set_intersection(_A,_B,L3)
   : ( (_A=[_C|_D]), ground([_B,L3,_C,_D]) )
   => ground([_B,L3,_C,_D]).

:- true pred set_intersection(_A,_B,L3)
   : ( (_B=[_C|_D]), ground([_A,L3,_C,_D]) )
   => ground([_A,L3,_C,_D]).

:- true pred set_intersection(_A,_B,L3)
   : ground([_A,_B,L3])
   => ground([_A,_B,L3]).

set_intersection([],[],[]).
set_intersection([],[_1|_2],[]).
set_intersection([_1|_2],[],[]).
set_intersection([X|L1],[X|L2],[X|L3]) :-
    true(ground([X,L1,L2,L3])),
    set_intersection(L1,L2,L3),
    true(ground([X,L1,L2,L3])).
set_intersection([X|L1],[Y|L2],L3) :-
    true(ground([L3,X,L1,Y,L2])),
    X<Y,
    true(ground([L3,X,L1,Y,L2])),
    set_intersection(L1,[Y|L2],L3),
    true(ground([L3,X,L1,Y,L2])).
set_intersection([X|L1],[Y|L2],L3) :-
    true(ground([L3,X,L1,Y,L2])),
    X>Y,
    true(ground([L3,X,L1,Y,L2])),
    set_intersection([X|L1],L2,L3),
    true(ground([L3,X,L1,Y,L2])).

:- true pred set_difference(_A,_B,L3)
   : ( (_B=[_C]),
       mshare([[L3]]),
       var(L3), ground([_A,_C]), linear(L3) )
   => ground([_A,L3,_C]).

:- true pred set_difference(_A,_B,L3)
   : ( (_A=[_C|_D]),
       mshare([[L3]]),
       var(L3), ground([_B,_C,_D]), linear(L3) )
   => ground([_B,L3,_C,_D]).

:- true pred set_difference(_A,_B,L3)
   : ( (_B=[_C|_D]),
       mshare([[L3]]),
       var(L3), ground([_A,_C,_D]), linear(L3) )
   => ground([_A,L3,_C,_D]).

:- true pred set_difference(_A,_B,L3)
   : ( mshare([[L3]]),
       var(L3), ground([_A,_B]), linear(L3) )
   => ground([_A,_B,L3]).

set_difference([],[],[]).
set_difference([],[_1|_2],[]).
set_difference([X|L1],[],[X|L1]).
set_difference([X|L1],[X|L2],L3) :-
    true((
        mshare([[L3]]),
        var(L3),
        ground([X,L1,L2]),
        linear(L3)
    )),
    set_difference(L1,L2,L3),
    true(ground([L3,X,L1,L2])).
set_difference([X|L1],[Y|L2],[X|L3]) :-
    true((
        mshare([[L3]]),
        var(L3),
        ground([X,L1,Y,L2]),
        linear(L3)
    )),
    X<Y,
    true((
        mshare([[L3]]),
        var(L3),
        ground([X,L1,Y,L2]),
        linear(L3)
    )),
    set_difference(L1,[Y|L2],L3),
    true(ground([X,L1,Y,L2,L3])).
set_difference([X|L1],[Y|L2],L3) :-
    true((
        mshare([[L3]]),
        var(L3),
        ground([X,L1,Y,L2]),
        linear(L3)
    )),
    X>Y,
    true((
        mshare([[L3]]),
        var(L3),
        ground([X,L1,Y,L2]),
        linear(L3)
    )),
    set_difference([X|L1],L2,L3),
    true(ground([L3,X,L1,Y,L2])).

:- true pred set_subset(_A,_1)
   : ( (_A=[_B|_C]), ground([_1,_B,_C]) )
   => ground([_1,_B,_C]).

:- true pred set_subset(_A,_1)
   : ground([_A,_1])
   => ground([_A,_1]).

set_subset([],_1).
set_subset([X|L1],[X|L2]) :-
    true(ground([X,L1,L2])),
    set_subset(L1,L2),
    true(ground([X,L1,L2])).
set_subset([X|L1],[Y|L2]) :-
    true(ground([X,L1,Y,L2])),
    X>Y,
    true(ground([X,L1,Y,L2])),
    set_subset([X|L1],L2),
    true(ground([X,L1,Y,L2])).

:- true pred set_member(X,_A)
   : ground([X,_A])
   => ground([X,_A]).

set_member(X,[X|_1]).
set_member(X,[Y|T]) :-
    true(ground([X,Y,T])),
    X>Y,
    true(ground([X,Y,T])),
    set_member(X,T),
    true(ground([X,Y,T])).


