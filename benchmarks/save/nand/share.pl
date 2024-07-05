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
        ground([N])
    )),
    init_state(N,NumVars,NumGs,Gs),
    true((
        mshare([[NumGs2],[Gs2]]),
        ground([N,NumVars,NumGs,Gs])
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
       ground([_A]) )
   => ground([_A,_B,_C,_D]).

init_state(0,2,3,[function(2,[1,2],[0,3],[],[],[],[],[]),function(1,[2,3],[0,1],[],[],[],[],[]),function(0,[1,3],[0,2],[],[],[],[],[])]) :-
    true(mshare([[_1],[_2]])),
    update_bounds(_1,100,_2),
    true(mshare([[_1],[_2]])).
init_state(1,3,4,[function(3,[3,5,6,7],[0,1,2,4],[],[],[],[],[]),function(2,[4,5,6,7],[0,1,2,3],[],[],[],[],[]),function(1,[2,3,6,7],[0,1,4,5],[],[],[],[],[]),function(0,[1,3,5,7],[0,2,4,6],[],[],[],[],[])]) :-
    true(mshare([[_1],[_2]])),
    update_bounds(_1,100,_2),
    true(mshare([[_1],[_2]])).
init_state(2,3,4,[function(3,[1,2,4,6,7],[0,3,5],[],[],[],[],[]),function(2,[4,5,6,7],[0,1,2,3],[],[],[],[],[]),function(1,[2,3,6,7],[0,1,4,5],[],[],[],[],[]),function(0,[1,3,5,7],[0,2,4,6],[],[],[],[],[])]) :-
    true(mshare([[_1],[_2]])),
    update_bounds(_1,100,_2),
    true(mshare([[_1],[_2]])).
init_state(3,3,4,[function(3,[1,2,4,7],[0,3,5,6],[],[],[],[],[]),function(2,[4,5,6,7],[0,1,2,3],[],[],[],[],[]),function(1,[2,3,6,7],[0,1,4,5],[],[],[],[],[]),function(0,[1,3,5,7],[0,2,4,6],[],[],[],[],[])]) :-
    true(mshare([[_1],[_2]])),
    update_bounds(_1,100,_2),
    true(mshare([[_1],[_2]])).
init_state(4,3,5,[function(4,[3,5,6,7],[0,1,2,4],[],[],[],[],[]),function(3,[1,2,4,7],[0,3,5,6],[],[],[],[],[]),function(2,[4,5,6,7],[0,1,2,3],[],[],[],[],[]),function(1,[2,3,6,7],[0,1,4,5],[],[],[],[],[]),function(0,[1,3,5,7],[0,2,4,6],[],[],[],[],[])]) :-
    true(mshare([[_1],[_2]])),
    update_bounds(_1,100,_2),
    true(mshare([[_1],[_2]])).
init_state(5,5,8,[function(7,[1,3,4,6,9,11,12,14,16,18,21,23,24,26,29,31],[0,2,5,7,8,10,13,15,17,19,20,22,25,27,28,30],[],[],[],[],[]),function(6,[2,3,5,6,8,9,12,15,17,18,20,21,24,27,30,31],[0,1,4,7,10,11,13,14,16,19,22,23,25,26,28,29],[],[],[],[],[]),function(5,[7,10,11,13,14,15,19,22,23,25,26,27,28,29,30,31],[0,1,2,3,4,5,6,8,9,12,16,17,18,20,21,24],[],[],[],[],[]),function(4,[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[],[],[],[],[]),function(3,[8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31],[0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23],[],[],[],[],[]),function(2,[4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31],[0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27],[],[],[],[],[]),function(1,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31],[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29],[],[],[],[],[]),function(0,[1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31],[0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30],[],[],[],[],[])]) :-
    true(mshare([[_1],[_2]])),
    update_bounds(_1,21,_2),
    true(mshare([[_1],[_2]])).

:- true pred search(NumVars,NumGsIn,GsIn)
   : ground([NumVars,NumGsIn,GsIn])
   + fails.

search(NumVars,NumGsIn,GsIn) :-
    true((
        mshare([[Gj],[Vector],[NumGs],[Gs],[NumGsOut],[GsOut]]),
        ground([NumVars,NumGsIn,GsIn])
    )),
    select_vector(NumVars,NumGsIn,GsIn,Gj,Vector),
    !,
    true((
        mshare([[NumGs],[Gs],[NumGsOut],[GsOut]]),
        ground([NumVars,NumGsIn,GsIn,Gj,Vector])
    )),
    cover_vector(NumVars,NumGsIn,GsIn,Gj,Vector,NumGs,Gs),
    true((
        mshare([[NumGsOut],[GsOut]]),
        ground([NumVars,NumGsIn,GsIn,Gj,Vector,NumGs,Gs])
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
       ground([NumVars,NumGs,Gs]) )
   => ground([NumVars,NumGs,Gs,Gj,Vector]).

select_vector(NumVars,NumGs,Gs,Gj,Vector) :-
    true((
        mshare([[Gj],[Vector],[Type],[_1]]),
        ground([NumVars,NumGs,Gs])
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
       ground([_A,NumVars,_1]) )
   => ground([_A,NumVars,_1,GjOut,Vout,TypeOut,Nout]).

:- true pred select_vector(_A,NumVars,_1,_2,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout)
   : ( mshare([[GjOut],[Vout],[TypeOut],[Nout]]),
       ground([_A,NumVars,_1,_2,Gj,V,Type,N]) )
   => ground([_A,NumVars,_1,_2,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout]).

select_vector([Gk|_3],NumVars,_1,_2,Gj,V,Type,N,Gj,V,Type,N) :-
    true((
        mshare([[K]]),
        ground([NumVars,_1,_2,Gj,V,Type,N,Gk,_3])
    )),
    function_number(Gk,K),
    true(ground([NumVars,_1,_2,Gj,V,Type,N,Gk,_3,K])),
    K<NumVars,
    true(ground([NumVars,_1,_2,Gj,V,Type,N,Gk,_3,K])).
select_vector([Gk|Gks],NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,GjOut,Vout,TypeOut,Nout) :-
    true((
        mshare([[GjOut],[Vout],[TypeOut],[Nout],[K],[Tk],[Gj],[V],[Type],[N]]),
        ground([NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,Gk,Gks])
    )),
    function_number(Gk,K),
    true((
        mshare([[GjOut],[Vout],[TypeOut],[Nout],[Tk],[Gj],[V],[Type],[N]]),
        ground([NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,Gk,Gks,K])
    )),
    K>=NumVars,
    true((
        mshare([[GjOut],[Vout],[TypeOut],[Nout],[Tk],[Gj],[V],[Type],[N]]),
        ground([NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,Gk,Gks,K])
    )),
    true_set(Gk,Tk),
    true((
        mshare([[GjOut],[Vout],[TypeOut],[Nout],[Gj],[V],[Type],[N]]),
        ground([NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,Gk,Gks,K,Tk])
    )),
    select_vector(Tk,Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,Gj,V,Type,N),
    true((
        mshare([[GjOut],[Vout],[TypeOut],[Nout]]),
        ground([NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,Gk,Gks,K,Tk,Gj,V,Type,N])
    )),
    select_vector(Gks,NumVars,NumGs,Gs,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout),
    true(ground([NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,GjOut,Vout,TypeOut,Nout,Gk,Gks,K,Tk,Gj,V,Type,N])).

:- true pred select_vector(_A,_1,_2,_3,_4,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout)
   : ( mshare([[GjOut],[Vout],[TypeOut],[Nout]]),
       ground([_A,_1,_2,_3,_4,Gj,V,Type,N]) )
   => ground([_A,_1,_2,_3,_4,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout]).

:- true pred select_vector(_A,_1,_2,_3,_4,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout)
   : ( (Gj=dummy), (V=0), (Type=nf), (N=999),
       mshare([[GjOut],[Vout],[Nout]]),
       ground([_A,_1,_2,_3,_4,TypeOut]) )
   => ground([_A,_1,_2,_3,_4,GjOut,Vout,TypeOut,Nout]).

:- true pred select_vector(_A,_1,_2,_3,_4,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout)
   : ( mshare([[GjOut],[Vout],[Nout]]),
       ground([_A,_1,_2,_3,_4,Gj,V,Type,N,TypeOut]) )
   => ground([_A,_1,_2,_3,_4,Gj,V,Type,N,GjOut,Vout,TypeOut,Nout]).

select_vector([],_1,_2,_3,_4,Gj,V,Type,N,Gj,V,Type,N).
select_vector([V|Vs],Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,GjOut,Vout,TypeOut,Nout) :-
    true((mshare([[GjOut],[Vout],[TypeOut],[Nout],[Type],[N],[Gj2],[V2],[Type2],[N2]]),ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,V,Vs]);mshare([[GjOut],[Vout],[Nout],[Type],[N],[Gj2],[V2],[Type2],[N2]]),ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,TypeOut,V,Vs]))),
    vector_cover_type(NumVars,Gs,Gk,V,Type,N),
    true((mshare([[GjOut],[Vout],[TypeOut],[Nout],[Gj2],[V2],[Type2],[N2]]),ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,V,Vs,Type,N]);mshare([[GjOut],[Vout],[Nout],[Gj2],[V2],[Type2],[N2]]),ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,TypeOut,V,Vs,Type,N]))),
    best_vector(GjIn,Vin,TypeIn,Nin,Gk,V,Type,N,Gj2,V2,Type2,N2),
    true((mshare([[GjOut],[Vout],[TypeOut],[Nout]]),ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,V,Vs,Type,N,Gj2,V2,Type2,N2]);mshare([[GjOut],[Vout],[Nout]]),ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,TypeOut,V,Vs,Type,N,Gj2,V2,Type2,N2]))),
    select_vector(Vs,Gk,NumVars,NumGs,Gs,Gj2,V2,Type2,N2,GjOut,Vout,TypeOut,Nout),
    true(ground([Gk,NumVars,NumGs,Gs,GjIn,Vin,TypeIn,Nin,GjOut,Vout,TypeOut,Nout,V,Vs,Type,N,Gj2,V2,Type2,N2])).

:- true pred vector_cover_type(NumVars,Gs,Gj,Vector,Type,NumCovers)
   : ( mshare([[Type],[NumCovers]]),
       ground([NumVars,Gs,Gj,Vector]) )
   => ground([NumVars,Gs,Gj,Vector,Type,NumCovers]).

vector_cover_type(NumVars,Gs,Gj,Vector,Type,NumCovers) :-
    true((
        mshare([[Type],[NumCovers],[IPs],[CIs],[Fj],[T],[N]]),
        ground([NumVars,Gs,Gj,Vector])
    )),
    immediate_predecessors(Gj,IPs),
    true((
        mshare([[Type],[NumCovers],[CIs],[Fj],[T],[N]]),
        ground([NumVars,Gs,Gj,Vector,IPs])
    )),
    conceivable_inputs(Gj,CIs),
    true((
        mshare([[Type],[NumCovers],[Fj],[T],[N]]),
        ground([NumVars,Gs,Gj,Vector,IPs,CIs])
    )),
    false_set(Gj,Fj),
    true((
        mshare([[Type],[NumCovers],[T],[N]]),
        ground([NumVars,Gs,Gj,Vector,IPs,CIs,Fj])
    )),
    cover_type1(IPs,Gs,Vector,nf,0,T,N),
    true((
        mshare([[Type],[NumCovers]]),
        ground([NumVars,Gs,Gj,Vector,IPs,CIs,Fj,T,N])
    )),
    cover_type2(CIs,Gs,NumVars,Fj,Vector,T,N,Type,NumCovers),
    true(ground([NumVars,Gs,Gj,Vector,Type,NumCovers,IPs,CIs,Fj,T,N])).

:- true pred cover_type1(_A,_1,_2,T,N,TypeOut,Nout)
   : ( (T=nf), (N=0),
       mshare([[TypeOut],[Nout]]),
       ground([_A,_1,_2]) )
   => ground([_A,_1,_2,TypeOut,Nout]).

:- true pred cover_type1(_A,_1,_2,T,N,TypeOut,Nout)
   : ( mshare([[TypeOut],[Nout]]),
       ground([_A,_1,_2,T,N]) )
   => ground([_A,_1,_2,T,N,TypeOut,Nout]).

cover_type1([],_1,_2,T,N,T,N).
cover_type1([I|IPs],Gs,V,TypeIn,Nin,TypeOut,Nout) :-
    true((
        mshare([[TypeOut],[Nout],[Gi],[Ti],[Fi],[Type],[N]]),
        ground([Gs,V,TypeIn,Nin,I,IPs])
    )),
    function(I,Gs,Gi),
    true((
        mshare([[TypeOut],[Nout],[Ti],[Fi],[Type],[N]]),
        ground([Gs,V,TypeIn,Nin,I,IPs,Gi])
    )),
    true_set(Gi,Ti),
    true((
        mshare([[TypeOut],[Nout],[Fi],[Type],[N]]),
        ground([Gs,V,TypeIn,Nin,I,IPs,Gi,Ti])
    )),
    'cover_type1/7/2/$disj/1'(V,Ti),
    !,
    true((
        mshare([[TypeOut],[Nout],[Fi],[Type],[N]]),
        ground([Gs,V,TypeIn,Nin,I,IPs,Gi,Ti])
    )),
    false_set(Gi,Fi),
    true((
        mshare([[TypeOut],[Nout],[Type],[N]]),
        ground([Gs,V,TypeIn,Nin,I,IPs,Gi,Ti,Fi])
    )),
    'cover_type1/7/2/$disj/2'(V,TypeIn,Fi,Type),
    true((
        mshare([[TypeOut],[Nout],[N]]),
        ground([Gs,V,TypeIn,Nin,I,IPs,Gi,Ti,Fi,Type])
    )),
    N is Nin+1,
    true((
        mshare([[TypeOut],[Nout]]),
        ground([Gs,V,TypeIn,Nin,I,IPs,Gi,Ti,Fi,Type,N])
    )),
    cover_type1(IPs,Gs,V,Type,N,TypeOut,Nout),
    true(ground([Gs,V,TypeIn,Nin,TypeOut,Nout,I,IPs,Gi,Ti,Fi,Type,N])).
cover_type1([_1|IPs],Gs,V,TypeIn,Nin,TypeOut,Nout) :-
    true((
        mshare([[TypeOut],[Nout]]),
        ground([Gs,V,TypeIn,Nin,_1,IPs])
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
       ground([V,TypeIn,Fi]) )
   => ground([V,TypeIn,Fi,Type]).

'cover_type1/7/2/$disj/2'(V,TypeIn,Fi,Type) :-
    true((
        mshare([[Type]]),
        ground([V,TypeIn,Fi])
    )),
    set_member(V,Fi),
    !,
    true((
        mshare([[Type]]),
        ground([V,TypeIn,Fi])
    )),
    max_type(TypeIn,cov,Type),
    true(ground([V,TypeIn,Fi,Type])).
'cover_type1/7/2/$disj/2'(V,TypeIn,Fi,Type) :-
    true((
        mshare([[Type]]),
        ground([V,TypeIn,Fi])
    )),
    max_type(TypeIn,exp,Type),
    true(ground([V,TypeIn,Fi,Type])).

:- true pred cover_type2(_A,_1,_2,_3,_4,T,N,TypeOut,Nout)
   : ( mshare([[TypeOut],[Nout]]),
       ground([_A,_1,_2,_3,_4,T,N]) )
   => ground([_A,_1,_2,_3,_4,T,N,TypeOut,Nout]).

cover_type2([],_1,_2,_3,_4,T,N,T,N).
cover_type2([I|CIs],Gs,NumVars,Fj,V,TypeIn,Nin,TypeOut,Nout) :-
    true((
        mshare([[TypeOut],[Nout],[Gi],[Fi],[Type],[N]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs])
    )),
    I<NumVars,
    true((
        mshare([[TypeOut],[Nout],[Gi],[Fi],[Type],[N]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs])
    )),
    function(I,Gs,Gi),
    true((
        mshare([[TypeOut],[Nout],[Fi],[Type],[N]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi])
    )),
    false_set(Gi,Fi),
    true((
        mshare([[TypeOut],[Nout],[Type],[N]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Fi])
    )),
    set_member(V,Fi),
    !,
    true((
        mshare([[TypeOut],[Nout],[Type],[N]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Fi])
    )),
    max_type(TypeIn,var,Type),
    true((
        mshare([[TypeOut],[Nout],[N]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Fi,Type])
    )),
    N is Nin+1,
    true((
        mshare([[TypeOut],[Nout]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Fi,Type,N])
    )),
    cover_type2(CIs,Gs,NumVars,Fj,V,Type,N,TypeOut,Nout),
    true(ground([Gs,NumVars,Fj,V,TypeIn,Nin,TypeOut,Nout,I,CIs,Gi,Fi,Type,N])).
cover_type2([I|CIs],Gs,NumVars,Fj,V,TypeIn,Nin,TypeOut,Nout) :-
    true((
        mshare([[TypeOut],[Nout],[Gi],[Ti],[Fi],[Type],[N]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs])
    )),
    I>=NumVars,
    true((
        mshare([[TypeOut],[Nout],[Gi],[Ti],[Fi],[Type],[N]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs])
    )),
    function(I,Gs,Gi),
    true((
        mshare([[TypeOut],[Nout],[Ti],[Fi],[Type],[N]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi])
    )),
    true_set(Gi,Ti),
    true((
        mshare([[TypeOut],[Nout],[Fi],[Type],[N]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Ti])
    )),
    'cover_type2/9/3/$disj/1'(V,Ti),
    !,
    true((
        mshare([[TypeOut],[Nout],[Fi],[Type],[N]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Ti])
    )),
    false_set(Gi,Fi),
    true((
        mshare([[TypeOut],[Nout],[Type],[N]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Ti,Fi])
    )),
    'cover_type2/9/3/$disj/2'(Fj,V,TypeIn,Ti,Fi,Type),
    true((
        mshare([[TypeOut],[Nout],[N]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Ti,Fi,Type])
    )),
    N is Nin+1,
    true((
        mshare([[TypeOut],[Nout]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,I,CIs,Gi,Ti,Fi,Type,N])
    )),
    cover_type2(CIs,Gs,NumVars,Fj,V,Type,N,TypeOut,Nout),
    true(ground([Gs,NumVars,Fj,V,TypeIn,Nin,TypeOut,Nout,I,CIs,Gi,Ti,Fi,Type,N])).
cover_type2([_1|CIs],Gs,NumVars,Fj,V,TypeIn,Nin,TypeOut,Nout) :-
    true((
        mshare([[TypeOut],[Nout]]),
        ground([Gs,NumVars,Fj,V,TypeIn,Nin,_1,CIs])
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
       ground([Fj,V,TypeIn,Ti,Fi]) )
   => ground([Fj,V,TypeIn,Ti,Fi,Type]).

'cover_type2/9/3/$disj/2'(Fj,V,TypeIn,Ti,Fi,Type) :-
    true((
        mshare([[Type]]),
        ground([Fj,V,TypeIn,Ti,Fi])
    )),
    set_member(V,Fi),
    !,
    true((
        mshare([[Type]]),
        ground([Fj,V,TypeIn,Ti,Fi])
    )),
    'cover_type2/9/3/$disj/2/6/1/$disj/1'(Fj,TypeIn,Ti,Type),
    true(ground([Fj,V,TypeIn,Ti,Fi,Type])).
'cover_type2/9/3/$disj/2'(Fj,V,TypeIn,Ti,Fi,Type) :-
    true((
        mshare([[Type]]),
        ground([Fj,V,TypeIn,Ti,Fi])
    )),
    set_subset(Fj,Ti),
    !,
    true((
        mshare([[Type]]),
        ground([Fj,V,TypeIn,Ti,Fi])
    )),
    max_type(TypeIn,exf,Type),
    true(ground([Fj,V,TypeIn,Ti,Fi,Type])).
'cover_type2/9/3/$disj/2'(Fj,V,TypeIn,Ti,Fi,Type) :-
    true((
        mshare([[Type]]),
        ground([Fj,V,TypeIn,Ti,Fi])
    )),
    max_type(TypeIn,exmcf,Type),
    true(ground([Fj,V,TypeIn,Ti,Fi,Type])).

:- true pred 'cover_type2/9/3/$disj/2/6/1/$disj/1'(Fj,TypeIn,Ti,Type)
   : ( mshare([[Type]]),
       ground([Fj,TypeIn,Ti]) )
   => ground([Fj,TypeIn,Ti,Type]).

'cover_type2/9/3/$disj/2/6/1/$disj/1'(Fj,TypeIn,Ti,Type) :-
    true((
        mshare([[Type]]),
        ground([Fj,TypeIn,Ti])
    )),
    set_subset(Fj,Ti),
    !,
    true((
        mshare([[Type]]),
        ground([Fj,TypeIn,Ti])
    )),
    max_type(TypeIn,fcn,Type),
    true(ground([Fj,TypeIn,Ti,Type])).
'cover_type2/9/3/$disj/2/6/1/$disj/1'(Fj,TypeIn,Ti,Type) :-
    true((
        mshare([[Type]]),
        ground([Fj,TypeIn,Ti])
    )),
    max_type(TypeIn,mcf,Type),
    true(ground([Fj,TypeIn,Ti,Type])).

:- true pred best_vector(Gj1,_1,_2,_3,Gj2,V2,Type2,N2,_A,V1,Type1,N1)
   : ( mshare([[_A],[V1],[Type1],[N1]]),
       ground([Gj1,_1,_2,_3,Gj2,V2,Type2,N2]) )
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
        ground([Gj1,V1,Type,N1,Gj2,_1,N2])
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
        ground([Gj1,_1,Type,N1,Gj2,V2,N2])
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
        ground([Gj1,V1,Type,N1,Gj2,_1,_2])
    )),
    'best_vector/12/5/$disj/1'(Type),
    true((
        mshare([[J1],[J2]]),
        ground([Gj1,V1,Type,N1,Gj2,_1,_2])
    )),
    function_number(Gj1,J1),
    true((
        mshare([[J2]]),
        ground([Gj1,V1,Type,N1,Gj2,_1,_2,J1])
    )),
    function_number(Gj2,J2),
    true(ground([Gj1,V1,Type,N1,Gj2,_1,_2,J1,J2])),
    J1>J2,
    !,
    true(ground([Gj1,V1,Type,N1,Gj2,_1,_2,J1,J2])).
best_vector(Gj1,_1,Type,_2,Gj2,V2,Type,N2,Gj2,V2,Type,N2) :-
    true((
        mshare([[J1],[J2]]),
        ground([Gj1,_1,Type,_2,Gj2,V2,N2])
    )),
    'best_vector/12/6/$disj/1'(Type),
    true((
        mshare([[J1],[J2]]),
        ground([Gj1,_1,Type,_2,Gj2,V2,N2])
    )),
    function_number(Gj1,J1),
    true((
        mshare([[J2]]),
        ground([Gj1,_1,Type,_2,Gj2,V2,N2,J1])
    )),
    function_number(Gj2,J2),
    true(ground([Gj1,_1,Type,_2,Gj2,V2,N2,J1,J2])),
    J1<J2,
    !,
    true(ground([Gj1,_1,Type,_2,Gj2,V2,N2,J1,J2])).
best_vector(Gj1,V1,Type,N1,Gj2,_1,Type,_2,Gj1,V1,Type,N1) :-
    true((
        mshare([[J1],[J2]]),
        ground([Gj1,V1,Type,N1,Gj2,_1,_2])
    )),
    'best_vector/12/7/$disj/1'(Type),
    true((
        mshare([[J1],[J2]]),
        ground([Gj1,V1,Type,N1,Gj2,_1,_2])
    )),
    function_number(Gj1,J1),
    true((
        mshare([[J2]]),
        ground([Gj1,V1,Type,N1,Gj2,_1,_2,J1])
    )),
    function_number(Gj2,J2),
    true(ground([Gj1,V1,Type,N1,Gj2,_1,_2,J1,J2])),
    J1<J2,
    !,
    true(ground([Gj1,V1,Type,N1,Gj2,_1,_2,J1,J2])).
best_vector(Gj1,_1,Type,_2,Gj2,V2,Type,N2,Gj2,V2,Type,N2) :-
    true((
        mshare([[J1],[J2]]),
        ground([Gj1,_1,Type,_2,Gj2,V2,N2])
    )),
    'best_vector/12/8/$disj/1'(Type),
    true((
        mshare([[J1],[J2]]),
        ground([Gj1,_1,Type,_2,Gj2,V2,N2])
    )),
    function_number(Gj1,J1),
    true((
        mshare([[J2]]),
        ground([Gj1,_1,Type,_2,Gj2,V2,N2,J1])
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
       ground([T1]) )
   => ground([T1,_A]).

:- true pred max_type(T1,T2,_A)
   : ( (T2=exf),
       mshare([[_A]]),
       ground([T1]) )
   => ground([T1,_A]).

:- true pred max_type(T1,T2,_A)
   : ( (T2=mcf),
       mshare([[_A]]),
       ground([T1]) )
   => ground([T1,_A]).

:- true pred max_type(T1,T2,_A)
   : ( (T2=fcn),
       mshare([[_A]]),
       ground([T1]) )
   => ground([T1,_A]).

:- true pred max_type(T1,T2,_A)
   : ( (T2=var),
       mshare([[_A]]),
       ground([T1]) )
   => ground([T1,_A]).

:- true pred max_type(T1,T2,_A)
   : ( (T2=exp),
       mshare([[_A]]),
       ground([T1]) )
   => ground([T1,_A]).

:- true pred max_type(T1,T2,_A)
   : ( (T2=cov),
       mshare([[_A]]),
       ground([T1]) )
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
       ground([NumVars,NumGsIn,GsIn,Gj,Vector]) )
   => ground([NumVars,NumGsIn,GsIn,Gj,Vector,NumGsOut,GsOut]).

cover_vector(NumVars,NumGsIn,GsIn,Gj,Vector,NumGsOut,GsOut) :-
    true((
        mshare([[NumGsOut],[GsOut],[IPs],[CIs],[Type]]),
        ground([NumVars,NumGsIn,GsIn,Gj,Vector])
    )),
    immediate_predecessors(Gj,IPs),
    true((
        mshare([[NumGsOut],[GsOut],[CIs],[Type]]),
        ground([NumVars,NumGsIn,GsIn,Gj,Vector,IPs])
    )),
    conceivable_inputs(Gj,CIs),
    true((
        mshare([[NumGsOut],[GsOut],[Type]]),
        ground([NumVars,NumGsIn,GsIn,Gj,Vector,IPs,CIs])
    )),
    vector_types(Type),
    true((
        mshare([[NumGsOut],[GsOut]]),
        ground([NumVars,NumGsIn,GsIn,Gj,Vector,IPs,CIs,Type])
    )),
    cover_vector(Type,IPs,CIs,Gj,Vector,NumVars,NumGsIn,GsIn,NumGsOut,GsOut),
    true(ground([NumVars,NumGsIn,GsIn,Gj,Vector,NumGsOut,GsOut,IPs,CIs,Type])).

:- true pred vector_types(_A)
   : mshare([[_A]])
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
       ground([_A,_B,_1,Gj,V,_2,NumGs,GsIn]) )
   => ground([_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut]).

:- true pred cover_vector(_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut)
   : ( (_A=exmcf), (NumGs=NumGsOut),
       mshare([[_B],[GsOut]]),
       ground([_1,Gj,V,_2,NumGs,GsIn]) )
   => ( mshare([[_B]]),
        ground([_1,Gj,V,_2,NumGs,GsIn,GsOut]) ).

:- true pred cover_vector(_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut)
   : ( (_A=exf), (NumGs=NumGsOut),
       mshare([[_B],[GsOut]]),
       ground([_1,Gj,V,_2,NumGs,GsIn]) )
   => ( mshare([[_B]]),
        ground([_1,Gj,V,_2,NumGs,GsIn,GsOut]) ).

:- true pred cover_vector(_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut)
   : ( (_A=mcf), (NumGs=NumGsOut),
       mshare([[_B],[GsOut]]),
       ground([_1,Gj,V,_2,NumGs,GsIn]) )
   => ( mshare([[_B]]),
        ground([_1,Gj,V,_2,NumGs,GsIn,GsOut]) ).

:- true pred cover_vector(_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut)
   : ( (_A=fcn), (NumGs=NumGsOut),
       mshare([[_B],[GsOut]]),
       ground([_1,Gj,V,_2,NumGs,GsIn]) )
   => ( mshare([[_B]]),
        ground([_1,Gj,V,_2,NumGs,GsIn,GsOut]) ).

:- true pred cover_vector(_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut)
   : ( (_A=var), (NumGs=NumGsOut),
       mshare([[_B],[GsOut]]),
       ground([_1,Gj,V,_2,NumGs,GsIn]) )
   => ( mshare([[_B]]),
        ground([_1,Gj,V,_2,NumGs,GsIn,GsOut]) ).

:- true pred cover_vector(_A,_B,_1,Gj,V,_2,NumGs,GsIn,NumGsOut,GsOut)
   : ( (_A=exp), (NumGs=NumGsOut),
       mshare([[_1],[GsOut]]),
       ground([_B,Gj,V,_2,NumGs,GsIn]) )
   => ( mshare([[_1]]),
        ground([_B,Gj,V,_2,NumGs,GsIn,GsOut]) ).

cover_vector(exp,[I|_3],_1,Gj,V,_2,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[Gi],[Ti]]),ground([Gj,V,_2,NumGs,GsIn,I,_3]);mshare([[GsOut],[Gi],[Ti]]),ground([_1,Gj,V,_2,NumGs,GsIn,I,_3]))),
    function(I,GsIn,Gi),
    true((mshare([[_1],[GsOut],[Ti]]),ground([Gj,V,_2,NumGs,GsIn,I,_3,Gi]);mshare([[GsOut],[Ti]]),ground([_1,Gj,V,_2,NumGs,GsIn,I,_3,Gi]))),
    true_set(Gi,Ti),
    true((mshare([[_1],[GsOut]]),ground([Gj,V,_2,NumGs,GsIn,I,_3,Gi,Ti]);mshare([[GsOut]]),ground([_1,Gj,V,_2,NumGs,GsIn,I,_3,Gi,Ti]))),
    'cover_vector/10/1/$disj/1'(V,Ti),
    true((mshare([[_1],[GsOut]]),ground([Gj,V,_2,NumGs,GsIn,I,_3,Gi,Ti]);mshare([[GsOut]]),ground([_1,Gj,V,_2,NumGs,GsIn,I,_3,Gi,Ti]))),
    update_circuit(GsIn,Gi,Gj,V,GsIn,GsOut),
    true((mshare([[_1]]),ground([Gj,V,_2,NumGs,GsIn,GsOut,I,_3,Gi,Ti]);ground([_1,Gj,V,_2,NumGs,GsIn,GsOut,I,_3,Gi,Ti]))).
cover_vector(exp,[_2|IPs],_1,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[_3]]),ground([Gj,V,NumVars,NumGs,GsIn,_2,IPs]);mshare([[GsOut],[_3]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,_2,IPs]))),
    cover_vector(exp,IPs,_3,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut),
    true((mshare([[_1],[_3]]),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,_2,IPs]);mshare([[_3]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,_2,IPs]))).
cover_vector(var,_1,[I|_2],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[Gi],[Fi]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]);mshare([[GsOut],[Gi],[Fi]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]))),
    I<NumVars,
    true((mshare([[_1],[GsOut],[Gi],[Fi]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]);mshare([[GsOut],[Gi],[Fi]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]))),
    function(I,GsIn,Gi),
    true((mshare([[_1],[GsOut],[Fi]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]);mshare([[GsOut],[Fi]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]))),
    false_set(Gi,Fi),
    true((mshare([[_1],[GsOut]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]);mshare([[GsOut]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]))),
    set_member(V,Fi),
    true((mshare([[_1],[GsOut]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]);mshare([[GsOut]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]))),
    update_circuit(GsIn,Gi,Gj,V,GsIn,GsOut),
    true((mshare([[_1]]),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi]);ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi]))).
cover_vector(var,_1,[_2|CIs],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[_3]]),ground([Gj,V,NumVars,NumGs,GsIn,_2,CIs]);mshare([[GsOut],[_3]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,_2,CIs]))),
    cover_vector(var,_3,CIs,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut),
    true((mshare([[_1],[_3]]),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]);mshare([[_3]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]))).
cover_vector(fcn,_1,[I|_2],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]))),
    I>=NumVars,
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]))),
    function(I,GsIn,Gi),
    true((mshare([[_1],[GsOut],[Fi],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]);mshare([[GsOut],[Fi],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]))),
    false_set(Gi,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]);mshare([[GsOut],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]))),
    set_member(V,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]);mshare([[GsOut],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]))),
    true_set(Gi,Ti),
    true((mshare([[_1],[GsOut],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]);mshare([[GsOut],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]))),
    false_set(Gj,Fj),
    true((mshare([[_1],[GsOut]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]);mshare([[GsOut]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]))),
    set_subset(Fj,Ti),
    true((mshare([[_1],[GsOut]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]);mshare([[GsOut]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]))),
    update_circuit(GsIn,Gi,Gj,V,GsIn,GsOut),
    true((mshare([[_1]]),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]);ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]))).
cover_vector(fcn,_1,[_2|CIs],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[_3]]),ground([Gj,V,NumVars,NumGs,GsIn,_2,CIs]);mshare([[GsOut],[_3]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,_2,CIs]))),
    cover_vector(fcn,_3,CIs,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut),
    true((mshare([[_1],[_3]]),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]);mshare([[_3]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]))).
cover_vector(mcf,_1,[I|_2],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]))),
    I>=NumVars,
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]))),
    function(I,GsIn,Gi),
    true((mshare([[_1],[GsOut],[Fi],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]);mshare([[GsOut],[Fi],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]))),
    false_set(Gi,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]);mshare([[GsOut],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]))),
    set_member(V,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]);mshare([[GsOut],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]))),
    true_set(Gi,Ti),
    true((mshare([[_1],[GsOut],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]);mshare([[GsOut],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]))),
    false_set(Gj,Fj),
    true((mshare([[_1],[GsOut]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]);mshare([[GsOut]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]))),
    'cover_vector/10/7/$disj/1'(Ti,Fj),
    true((mshare([[_1],[GsOut]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]);mshare([[GsOut]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]))),
    update_circuit(GsIn,Gi,Gj,V,GsIn,GsOut),
    true((mshare([[_1]]),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]);ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]))).
cover_vector(mcf,_1,[_2|CIs],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[_3]]),ground([Gj,V,NumVars,NumGs,GsIn,_2,CIs]);mshare([[GsOut],[_3]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,_2,CIs]))),
    cover_vector(mcf,_3,CIs,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut),
    true((mshare([[_1],[_3]]),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]);mshare([[_3]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]))).
cover_vector(exf,_1,[I|_2],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]))),
    I>=NumVars,
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]))),
    function(I,GsIn,Gi),
    true((mshare([[_1],[GsOut],[Fi],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]);mshare([[GsOut],[Fi],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]))),
    false_set(Gi,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]);mshare([[GsOut],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]))),
    'cover_vector/10/9/$disj/1'(V,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]);mshare([[GsOut],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]))),
    true_set(Gi,Ti),
    true((mshare([[_1],[GsOut],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]);mshare([[GsOut],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]))),
    'cover_vector/10/9/$disj/2'(V,Ti),
    true((mshare([[_1],[GsOut],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]);mshare([[GsOut],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]))),
    false_set(Gj,Fj),
    true((mshare([[_1],[GsOut]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]);mshare([[GsOut]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]))),
    set_subset(Fj,Ti),
    true((mshare([[_1],[GsOut]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]);mshare([[GsOut]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]))),
    update_circuit(GsIn,Gi,Gj,V,GsIn,GsOut),
    true((mshare([[_1]]),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]);ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]))).
cover_vector(exf,_1,[_2|CIs],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[_3]]),ground([Gj,V,NumVars,NumGs,GsIn,_2,CIs]);mshare([[GsOut],[_3]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,_2,CIs]))),
    cover_vector(exf,_3,CIs,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut),
    true((mshare([[_1],[_3]]),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]);mshare([[_3]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]))).
cover_vector(exmcf,_1,[I|_2],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]))),
    I>=NumVars,
    true((mshare([[_1],[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2]);mshare([[GsOut],[Gi],[Fi],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2]))),
    function(I,GsIn,Gi),
    true((mshare([[_1],[GsOut],[Fi],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]);mshare([[GsOut],[Fi],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi]))),
    false_set(Gi,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]);mshare([[GsOut],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]))),
    'cover_vector/10/11/$disj/1'(V,Fi),
    true((mshare([[_1],[GsOut],[Ti],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]);mshare([[GsOut],[Ti],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi]))),
    true_set(Gi,Ti),
    true((mshare([[_1],[GsOut],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]);mshare([[GsOut],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]))),
    'cover_vector/10/11/$disj/2'(V,Ti),
    true((mshare([[_1],[GsOut],[Fj]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]);mshare([[GsOut],[Fj]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti]))),
    false_set(Gj,Fj),
    true((mshare([[_1],[GsOut]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]);mshare([[GsOut]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]))),
    'cover_vector/10/11/$disj/3'(Ti,Fj),
    true((mshare([[_1],[GsOut]]),ground([Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]);mshare([[GsOut]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,I,_2,Gi,Fi,Ti,Fj]))),
    update_circuit(GsIn,Gi,Gj,V,GsIn,GsOut),
    true((mshare([[_1]]),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]);ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,I,_2,Gi,Fi,Ti,Fj]))).
cover_vector(exmcf,_1,[_2|CIs],Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut) :-
    true((mshare([[_1],[GsOut],[_3]]),ground([Gj,V,NumVars,NumGs,GsIn,_2,CIs]);mshare([[GsOut],[_3]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,_2,CIs]))),
    cover_vector(exmcf,_3,CIs,Gj,V,NumVars,NumGs,GsIn,NumGs,GsOut),
    true((mshare([[_1],[_3]]),ground([Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]);mshare([[_3]]),ground([_1,Gj,V,NumVars,NumGs,GsIn,GsOut,_2,CIs]))).
cover_vector(nf,_1,_2,Gj,V,NumVars,NumGsIn,GsIn,NumGsOut,GsOut) :-
    true((
        mshare([[NumGsOut],[GsOut],[Fj],[Gs],[Gi]]),
        ground([_1,_2,Gj,V,NumVars,NumGsIn,GsIn])
    )),
    NumGsOut is NumGsIn+1,
    true((
        mshare([[GsOut],[Fj],[Gs],[Gi]]),
        ground([_1,_2,Gj,V,NumVars,NumGsIn,GsIn,NumGsOut])
    )),
    false_set(Gj,Fj),
    true((
        mshare([[GsOut],[Gs],[Gi]]),
        ground([_1,_2,Gj,V,NumVars,NumGsIn,GsIn,NumGsOut,Fj])
    )),
    new_function_CIs(GsIn,function(NumGsIn,Fj,[V],[],[],[],[],[]),NumVars,Gs,Gi),
    true((
        mshare([[GsOut]]),
        ground([_1,_2,Gj,V,NumVars,NumGsIn,GsIn,NumGsOut,Fj,Gs,Gi])
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
       ground([_A,_1,_2,_3]) )
   => ground([_A,_1,_2,_3,_B]).

:- true pred update_circuit(_A,_1,_2,_3,_4,_B)
   : ( mshare([[_B]]),
       ground([_A,_1,_2,_3,_4]) )
   => ground([_A,_1,_2,_3,_4,_B]).

update_circuit([],_1,_2,_3,_4,[]).
update_circuit([function(K,Tk,Fk,CIk,IPk,ISk,Pk,Sk)|GsIn],Gi,Gj,V,Gs,[function(K,Tko,Fko,CIko,IPko,ISko,Pko,Sko)|GsOut]) :-
    true((
        mshare([[GsOut],[GsOut,Tko],[GsOut,Tko,Fko],[GsOut,Tko,Fko,CIko],[GsOut,Tko,Fko,CIko,IPko],[GsOut,Tko,Fko,CIko,IPko,ISko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,ISko,Sko],[GsOut,Tko,Fko,CIko,IPko,Pko],[GsOut,Tko,Fko,CIko,IPko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,Sko],[GsOut,Tko,Fko,CIko,ISko],[GsOut,Tko,Fko,CIko,ISko,Pko],[GsOut,Tko,Fko,CIko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,ISko,Sko],[GsOut,Tko,Fko,CIko,Pko],[GsOut,Tko,Fko,CIko,Pko,Sko],[GsOut,Tko,Fko,CIko,Sko],[GsOut,Tko,Fko,IPko],[GsOut,Tko,Fko,IPko,ISko],[GsOut,Tko,Fko,IPko,ISko,Pko],[GsOut,Tko,Fko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,IPko,ISko,Sko],[GsOut,Tko,Fko,IPko,Pko],[GsOut,Tko,Fko,IPko,Pko,Sko],[GsOut,Tko,Fko,IPko,Sko],[GsOut,Tko,Fko,ISko],[GsOut,Tko,Fko,ISko,Pko],[GsOut,Tko,Fko,ISko,Pko,Sko],[GsOut,Tko,Fko,ISko,Sko],[GsOut,Tko,Fko,Pko],[GsOut,Tko,Fko,Pko,Sko],[GsOut,Tko,Fko,Sko],[GsOut,Tko,CIko],[GsOut,Tko,CIko,IPko],[GsOut,Tko,CIko,IPko,ISko],[GsOut,Tko,CIko,IPko,ISko,Pko],[GsOut,Tko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,CIko,IPko,ISko,Sko],[GsOut,Tko,CIko,IPko,Pko],[GsOut,Tko,CIko,IPko,Pko,Sko],[GsOut,Tko,CIko,IPko,Sko],[GsOut,Tko,CIko,ISko],[GsOut,Tko,CIko,ISko,Pko],[GsOut,Tko,CIko,ISko,Pko,Sko],[GsOut,Tko,CIko,ISko,Sko],[GsOut,Tko,CIko,Pko],[GsOut,Tko,CIko,Pko,Sko],[GsOut,Tko,CIko,Sko],[GsOut,Tko,IPko],[GsOut,Tko,IPko,ISko],[GsOut,Tko,IPko,ISko,Pko],[GsOut,Tko,IPko,ISko,Pko,Sko],[GsOut,Tko,IPko,ISko,Sko],[GsOut,Tko,IPko,Pko],[GsOut,Tko,IPko,Pko,Sko],[GsOut,Tko,IPko,Sko],[GsOut,Tko,ISko],[GsOut,Tko,ISko,Pko],[GsOut,Tko,ISko,Pko,Sko],[GsOut,Tko,ISko,Sko],[GsOut,Tko,Pko],[GsOut,Tko,Pko,Sko],[GsOut,Tko,Sko],[GsOut,Fko],[GsOut,Fko,CIko],[GsOut,Fko,CIko,IPko],[GsOut,Fko,CIko,IPko,ISko],[GsOut,Fko,CIko,IPko,ISko,Pko],[GsOut,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Fko,CIko,IPko,ISko,Sko],[GsOut,Fko,CIko,IPko,Pko],[GsOut,Fko,CIko,IPko,Pko,Sko],[GsOut,Fko,CIko,IPko,Sko],[GsOut,Fko,CIko,ISko],[GsOut,Fko,CIko,ISko,Pko],[GsOut,Fko,CIko,ISko,Pko,Sko],[GsOut,Fko,CIko,ISko,Sko],[GsOut,Fko,CIko,Pko],[GsOut,Fko,CIko,Pko,Sko],[GsOut,Fko,CIko,Sko],[GsOut,Fko,IPko],[GsOut,Fko,IPko,ISko],[GsOut,Fko,IPko,ISko,Pko],[GsOut,Fko,IPko,ISko,Pko,Sko],[GsOut,Fko,IPko,ISko,Sko],[GsOut,Fko,IPko,Pko],[GsOut,Fko,IPko,Pko,Sko],[GsOut,Fko,IPko,Sko],[GsOut,Fko,ISko],[GsOut,Fko,ISko,Pko],[GsOut,Fko,ISko,Pko,Sko],[GsOut,Fko,ISko,Sko],[GsOut,Fko,Pko],[GsOut,Fko,Pko,Sko],[GsOut,Fko,Sko],[GsOut,CIko],[GsOut,CIko,IPko],[GsOut,CIko,IPko,ISko],[GsOut,CIko,IPko,ISko,Pko],[GsOut,CIko,IPko,ISko,Pko,Sko],[GsOut,CIko,IPko,ISko,Sko],[GsOut,CIko,IPko,Pko],[GsOut,CIko,IPko,Pko,Sko],[GsOut,CIko,IPko,Sko],[GsOut,CIko,ISko],[GsOut,CIko,ISko,Pko],[GsOut,CIko,ISko,Pko,Sko],[GsOut,CIko,ISko,Sko],[GsOut,CIko,Pko],[GsOut,CIko,Pko,Sko],[GsOut,CIko,Sko],[GsOut,IPko],[GsOut,IPko,ISko],[GsOut,IPko,ISko,Pko],[GsOut,IPko,ISko,Pko,Sko],[GsOut,IPko,ISko,Sko],[GsOut,IPko,Pko],[GsOut,IPko,Pko,Sko],[GsOut,IPko,Sko],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[Tko],[Tko,Fko],[Tko,Fko,CIko],[Tko,Fko,CIko,IPko],[Tko,Fko,CIko,IPko,ISko],[Tko,Fko,CIko,IPko,ISko,Pko],[Tko,Fko,CIko,IPko,ISko,Pko,Sko],[Tko,Fko,CIko,IPko,ISko,Sko],[Tko,Fko,CIko,IPko,Pko],[Tko,Fko,CIko,IPko,Pko,Sko],[Tko,Fko,CIko,IPko,Sko],[Tko,Fko,CIko,ISko],[Tko,Fko,CIko,ISko,Pko],[Tko,Fko,CIko,ISko,Pko,Sko],[Tko,Fko,CIko,ISko,Sko],[Tko,Fko,CIko,Pko],[Tko,Fko,CIko,Pko,Sko],[Tko,Fko,CIko,Sko],[Tko,Fko,IPko],[Tko,Fko,IPko,ISko],[Tko,Fko,IPko,ISko,Pko],[Tko,Fko,IPko,ISko,Pko,Sko],[Tko,Fko,IPko,ISko,Sko],[Tko,Fko,IPko,Pko],[Tko,Fko,IPko,Pko,Sko],[Tko,Fko,IPko,Sko],[Tko,Fko,ISko],[Tko,Fko,ISko,Pko],[Tko,Fko,ISko,Pko,Sko],[Tko,Fko,ISko,Sko],[Tko,Fko,Pko],[Tko,Fko,Pko,Sko],[Tko,Fko,Sko],[Tko,CIko],[Tko,CIko,IPko],[Tko,CIko,IPko,ISko],[Tko,CIko,IPko,ISko,Pko],[Tko,CIko,IPko,ISko,Pko,Sko],[Tko,CIko,IPko,ISko,Sko],[Tko,CIko,IPko,Pko],[Tko,CIko,IPko,Pko,Sko],[Tko,CIko,IPko,Sko],[Tko,CIko,ISko],[Tko,CIko,ISko,Pko],[Tko,CIko,ISko,Pko,Sko],[Tko,CIko,ISko,Sko],[Tko,CIko,Pko],[Tko,CIko,Pko,Sko],[Tko,CIko,Sko],[Tko,IPko],[Tko,IPko,ISko],[Tko,IPko,ISko,Pko],[Tko,IPko,ISko,Pko,Sko],[Tko,IPko,ISko,Sko],[Tko,IPko,Pko],[Tko,IPko,Pko,Sko],[Tko,IPko,Sko],[Tko,ISko],[Tko,ISko,Pko],[Tko,ISko,Pko,Sko],[Tko,ISko,Sko],[Tko,Pko],[Tko,Pko,Sko],[Tko,Sko],[Fko],[Fko,CIko],[Fko,CIko,IPko],[Fko,CIko,IPko,ISko],[Fko,CIko,IPko,ISko,Pko],[Fko,CIko,IPko,ISko,Pko,Sko],[Fko,CIko,IPko,ISko,Sko],[Fko,CIko,IPko,Pko],[Fko,CIko,IPko,Pko,Sko],[Fko,CIko,IPko,Sko],[Fko,CIko,ISko],[Fko,CIko,ISko,Pko],[Fko,CIko,ISko,Pko,Sko],[Fko,CIko,ISko,Sko],[Fko,CIko,Pko],[Fko,CIko,Pko,Sko],[Fko,CIko,Sko],[Fko,IPko],[Fko,IPko,ISko],[Fko,IPko,ISko,Pko],[Fko,IPko,ISko,Pko,Sko],[Fko,IPko,ISko,Sko],[Fko,IPko,Pko],[Fko,IPko,Pko,Sko],[Fko,IPko,Sko],[Fko,ISko],[Fko,ISko,Pko],[Fko,ISko,Pko,Sko],[Fko,ISko,Sko],[Fko,Pko],[Fko,Pko,Sko],[Fko,Sko],[CIko],[CIko,IPko],[CIko,IPko,ISko],[CIko,IPko,ISko,Pko],[CIko,IPko,ISko,Pko,Sko],[CIko,IPko,ISko,Sko],[CIko,IPko,Pko],[CIko,IPko,Pko,Sko],[CIko,IPko,Sko],[CIko,ISko],[CIko,ISko,Pko],[CIko,ISko,Pko,Sko],[CIko,ISko,Sko],[CIko,Pko],[CIko,Pko,Sko],[CIko,Sko],[IPko],[IPko,ISko],[IPko,ISko,Pko],[IPko,ISko,Pko,Sko],[IPko,ISko,Sko],[IPko,Pko],[IPko,Pko,Sko],[IPko,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko],[I],[_1],[Fi],[_2],[IPi],[ISi],[Pi],[_3],[J],[_4],[Fj],[_5],[_6],[_7],[_8],[Sj],[PiI],[SjJ],[Tk2],[Tk3],[CIk2],[CIk3],[CIk4]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk])
    )),
    Gi=function(I,_1,Fi,_2,IPi,ISi,Pi,_3),
    true((
        mshare([[GsOut],[GsOut,Tko],[GsOut,Tko,Fko],[GsOut,Tko,Fko,CIko],[GsOut,Tko,Fko,CIko,IPko],[GsOut,Tko,Fko,CIko,IPko,ISko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,ISko,Sko],[GsOut,Tko,Fko,CIko,IPko,Pko],[GsOut,Tko,Fko,CIko,IPko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,Sko],[GsOut,Tko,Fko,CIko,ISko],[GsOut,Tko,Fko,CIko,ISko,Pko],[GsOut,Tko,Fko,CIko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,ISko,Sko],[GsOut,Tko,Fko,CIko,Pko],[GsOut,Tko,Fko,CIko,Pko,Sko],[GsOut,Tko,Fko,CIko,Sko],[GsOut,Tko,Fko,IPko],[GsOut,Tko,Fko,IPko,ISko],[GsOut,Tko,Fko,IPko,ISko,Pko],[GsOut,Tko,Fko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,IPko,ISko,Sko],[GsOut,Tko,Fko,IPko,Pko],[GsOut,Tko,Fko,IPko,Pko,Sko],[GsOut,Tko,Fko,IPko,Sko],[GsOut,Tko,Fko,ISko],[GsOut,Tko,Fko,ISko,Pko],[GsOut,Tko,Fko,ISko,Pko,Sko],[GsOut,Tko,Fko,ISko,Sko],[GsOut,Tko,Fko,Pko],[GsOut,Tko,Fko,Pko,Sko],[GsOut,Tko,Fko,Sko],[GsOut,Tko,CIko],[GsOut,Tko,CIko,IPko],[GsOut,Tko,CIko,IPko,ISko],[GsOut,Tko,CIko,IPko,ISko,Pko],[GsOut,Tko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,CIko,IPko,ISko,Sko],[GsOut,Tko,CIko,IPko,Pko],[GsOut,Tko,CIko,IPko,Pko,Sko],[GsOut,Tko,CIko,IPko,Sko],[GsOut,Tko,CIko,ISko],[GsOut,Tko,CIko,ISko,Pko],[GsOut,Tko,CIko,ISko,Pko,Sko],[GsOut,Tko,CIko,ISko,Sko],[GsOut,Tko,CIko,Pko],[GsOut,Tko,CIko,Pko,Sko],[GsOut,Tko,CIko,Sko],[GsOut,Tko,IPko],[GsOut,Tko,IPko,ISko],[GsOut,Tko,IPko,ISko,Pko],[GsOut,Tko,IPko,ISko,Pko,Sko],[GsOut,Tko,IPko,ISko,Sko],[GsOut,Tko,IPko,Pko],[GsOut,Tko,IPko,Pko,Sko],[GsOut,Tko,IPko,Sko],[GsOut,Tko,ISko],[GsOut,Tko,ISko,Pko],[GsOut,Tko,ISko,Pko,Sko],[GsOut,Tko,ISko,Sko],[GsOut,Tko,Pko],[GsOut,Tko,Pko,Sko],[GsOut,Tko,Sko],[GsOut,Fko],[GsOut,Fko,CIko],[GsOut,Fko,CIko,IPko],[GsOut,Fko,CIko,IPko,ISko],[GsOut,Fko,CIko,IPko,ISko,Pko],[GsOut,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Fko,CIko,IPko,ISko,Sko],[GsOut,Fko,CIko,IPko,Pko],[GsOut,Fko,CIko,IPko,Pko,Sko],[GsOut,Fko,CIko,IPko,Sko],[GsOut,Fko,CIko,ISko],[GsOut,Fko,CIko,ISko,Pko],[GsOut,Fko,CIko,ISko,Pko,Sko],[GsOut,Fko,CIko,ISko,Sko],[GsOut,Fko,CIko,Pko],[GsOut,Fko,CIko,Pko,Sko],[GsOut,Fko,CIko,Sko],[GsOut,Fko,IPko],[GsOut,Fko,IPko,ISko],[GsOut,Fko,IPko,ISko,Pko],[GsOut,Fko,IPko,ISko,Pko,Sko],[GsOut,Fko,IPko,ISko,Sko],[GsOut,Fko,IPko,Pko],[GsOut,Fko,IPko,Pko,Sko],[GsOut,Fko,IPko,Sko],[GsOut,Fko,ISko],[GsOut,Fko,ISko,Pko],[GsOut,Fko,ISko,Pko,Sko],[GsOut,Fko,ISko,Sko],[GsOut,Fko,Pko],[GsOut,Fko,Pko,Sko],[GsOut,Fko,Sko],[GsOut,CIko],[GsOut,CIko,IPko],[GsOut,CIko,IPko,ISko],[GsOut,CIko,IPko,ISko,Pko],[GsOut,CIko,IPko,ISko,Pko,Sko],[GsOut,CIko,IPko,ISko,Sko],[GsOut,CIko,IPko,Pko],[GsOut,CIko,IPko,Pko,Sko],[GsOut,CIko,IPko,Sko],[GsOut,CIko,ISko],[GsOut,CIko,ISko,Pko],[GsOut,CIko,ISko,Pko,Sko],[GsOut,CIko,ISko,Sko],[GsOut,CIko,Pko],[GsOut,CIko,Pko,Sko],[GsOut,CIko,Sko],[GsOut,IPko],[GsOut,IPko,ISko],[GsOut,IPko,ISko,Pko],[GsOut,IPko,ISko,Pko,Sko],[GsOut,IPko,ISko,Sko],[GsOut,IPko,Pko],[GsOut,IPko,Pko,Sko],[GsOut,IPko,Sko],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[Tko],[Tko,Fko],[Tko,Fko,CIko],[Tko,Fko,CIko,IPko],[Tko,Fko,CIko,IPko,ISko],[Tko,Fko,CIko,IPko,ISko,Pko],[Tko,Fko,CIko,IPko,ISko,Pko,Sko],[Tko,Fko,CIko,IPko,ISko,Sko],[Tko,Fko,CIko,IPko,Pko],[Tko,Fko,CIko,IPko,Pko,Sko],[Tko,Fko,CIko,IPko,Sko],[Tko,Fko,CIko,ISko],[Tko,Fko,CIko,ISko,Pko],[Tko,Fko,CIko,ISko,Pko,Sko],[Tko,Fko,CIko,ISko,Sko],[Tko,Fko,CIko,Pko],[Tko,Fko,CIko,Pko,Sko],[Tko,Fko,CIko,Sko],[Tko,Fko,IPko],[Tko,Fko,IPko,ISko],[Tko,Fko,IPko,ISko,Pko],[Tko,Fko,IPko,ISko,Pko,Sko],[Tko,Fko,IPko,ISko,Sko],[Tko,Fko,IPko,Pko],[Tko,Fko,IPko,Pko,Sko],[Tko,Fko,IPko,Sko],[Tko,Fko,ISko],[Tko,Fko,ISko,Pko],[Tko,Fko,ISko,Pko,Sko],[Tko,Fko,ISko,Sko],[Tko,Fko,Pko],[Tko,Fko,Pko,Sko],[Tko,Fko,Sko],[Tko,CIko],[Tko,CIko,IPko],[Tko,CIko,IPko,ISko],[Tko,CIko,IPko,ISko,Pko],[Tko,CIko,IPko,ISko,Pko,Sko],[Tko,CIko,IPko,ISko,Sko],[Tko,CIko,IPko,Pko],[Tko,CIko,IPko,Pko,Sko],[Tko,CIko,IPko,Sko],[Tko,CIko,ISko],[Tko,CIko,ISko,Pko],[Tko,CIko,ISko,Pko,Sko],[Tko,CIko,ISko,Sko],[Tko,CIko,Pko],[Tko,CIko,Pko,Sko],[Tko,CIko,Sko],[Tko,IPko],[Tko,IPko,ISko],[Tko,IPko,ISko,Pko],[Tko,IPko,ISko,Pko,Sko],[Tko,IPko,ISko,Sko],[Tko,IPko,Pko],[Tko,IPko,Pko,Sko],[Tko,IPko,Sko],[Tko,ISko],[Tko,ISko,Pko],[Tko,ISko,Pko,Sko],[Tko,ISko,Sko],[Tko,Pko],[Tko,Pko,Sko],[Tko,Sko],[Fko],[Fko,CIko],[Fko,CIko,IPko],[Fko,CIko,IPko,ISko],[Fko,CIko,IPko,ISko,Pko],[Fko,CIko,IPko,ISko,Pko,Sko],[Fko,CIko,IPko,ISko,Sko],[Fko,CIko,IPko,Pko],[Fko,CIko,IPko,Pko,Sko],[Fko,CIko,IPko,Sko],[Fko,CIko,ISko],[Fko,CIko,ISko,Pko],[Fko,CIko,ISko,Pko,Sko],[Fko,CIko,ISko,Sko],[Fko,CIko,Pko],[Fko,CIko,Pko,Sko],[Fko,CIko,Sko],[Fko,IPko],[Fko,IPko,ISko],[Fko,IPko,ISko,Pko],[Fko,IPko,ISko,Pko,Sko],[Fko,IPko,ISko,Sko],[Fko,IPko,Pko],[Fko,IPko,Pko,Sko],[Fko,IPko,Sko],[Fko,ISko],[Fko,ISko,Pko],[Fko,ISko,Pko,Sko],[Fko,ISko,Sko],[Fko,Pko],[Fko,Pko,Sko],[Fko,Sko],[CIko],[CIko,IPko],[CIko,IPko,ISko],[CIko,IPko,ISko,Pko],[CIko,IPko,ISko,Pko,Sko],[CIko,IPko,ISko,Sko],[CIko,IPko,Pko],[CIko,IPko,Pko,Sko],[CIko,IPko,Sko],[CIko,ISko],[CIko,ISko,Pko],[CIko,ISko,Pko,Sko],[CIko,ISko,Sko],[CIko,Pko],[CIko,Pko,Sko],[CIko,Sko],[IPko],[IPko,ISko],[IPko,ISko,Pko],[IPko,ISko,Pko,Sko],[IPko,ISko,Sko],[IPko,Pko],[IPko,Pko,Sko],[IPko,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko],[J],[_4],[Fj],[_5],[_6],[_7],[_8],[Sj],[PiI],[SjJ],[Tk2],[Tk3],[CIk2],[CIk3],[CIk4]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,I,_1,Fi,_2,IPi,ISi,Pi,_3])
    )),
    Gj=function(J,_4,Fj,_5,_6,_7,_8,Sj),
    true((
        mshare([[GsOut],[GsOut,Tko],[GsOut,Tko,Fko],[GsOut,Tko,Fko,CIko],[GsOut,Tko,Fko,CIko,IPko],[GsOut,Tko,Fko,CIko,IPko,ISko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,ISko,Sko],[GsOut,Tko,Fko,CIko,IPko,Pko],[GsOut,Tko,Fko,CIko,IPko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,Sko],[GsOut,Tko,Fko,CIko,ISko],[GsOut,Tko,Fko,CIko,ISko,Pko],[GsOut,Tko,Fko,CIko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,ISko,Sko],[GsOut,Tko,Fko,CIko,Pko],[GsOut,Tko,Fko,CIko,Pko,Sko],[GsOut,Tko,Fko,CIko,Sko],[GsOut,Tko,Fko,IPko],[GsOut,Tko,Fko,IPko,ISko],[GsOut,Tko,Fko,IPko,ISko,Pko],[GsOut,Tko,Fko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,IPko,ISko,Sko],[GsOut,Tko,Fko,IPko,Pko],[GsOut,Tko,Fko,IPko,Pko,Sko],[GsOut,Tko,Fko,IPko,Sko],[GsOut,Tko,Fko,ISko],[GsOut,Tko,Fko,ISko,Pko],[GsOut,Tko,Fko,ISko,Pko,Sko],[GsOut,Tko,Fko,ISko,Sko],[GsOut,Tko,Fko,Pko],[GsOut,Tko,Fko,Pko,Sko],[GsOut,Tko,Fko,Sko],[GsOut,Tko,CIko],[GsOut,Tko,CIko,IPko],[GsOut,Tko,CIko,IPko,ISko],[GsOut,Tko,CIko,IPko,ISko,Pko],[GsOut,Tko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,CIko,IPko,ISko,Sko],[GsOut,Tko,CIko,IPko,Pko],[GsOut,Tko,CIko,IPko,Pko,Sko],[GsOut,Tko,CIko,IPko,Sko],[GsOut,Tko,CIko,ISko],[GsOut,Tko,CIko,ISko,Pko],[GsOut,Tko,CIko,ISko,Pko,Sko],[GsOut,Tko,CIko,ISko,Sko],[GsOut,Tko,CIko,Pko],[GsOut,Tko,CIko,Pko,Sko],[GsOut,Tko,CIko,Sko],[GsOut,Tko,IPko],[GsOut,Tko,IPko,ISko],[GsOut,Tko,IPko,ISko,Pko],[GsOut,Tko,IPko,ISko,Pko,Sko],[GsOut,Tko,IPko,ISko,Sko],[GsOut,Tko,IPko,Pko],[GsOut,Tko,IPko,Pko,Sko],[GsOut,Tko,IPko,Sko],[GsOut,Tko,ISko],[GsOut,Tko,ISko,Pko],[GsOut,Tko,ISko,Pko,Sko],[GsOut,Tko,ISko,Sko],[GsOut,Tko,Pko],[GsOut,Tko,Pko,Sko],[GsOut,Tko,Sko],[GsOut,Fko],[GsOut,Fko,CIko],[GsOut,Fko,CIko,IPko],[GsOut,Fko,CIko,IPko,ISko],[GsOut,Fko,CIko,IPko,ISko,Pko],[GsOut,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Fko,CIko,IPko,ISko,Sko],[GsOut,Fko,CIko,IPko,Pko],[GsOut,Fko,CIko,IPko,Pko,Sko],[GsOut,Fko,CIko,IPko,Sko],[GsOut,Fko,CIko,ISko],[GsOut,Fko,CIko,ISko,Pko],[GsOut,Fko,CIko,ISko,Pko,Sko],[GsOut,Fko,CIko,ISko,Sko],[GsOut,Fko,CIko,Pko],[GsOut,Fko,CIko,Pko,Sko],[GsOut,Fko,CIko,Sko],[GsOut,Fko,IPko],[GsOut,Fko,IPko,ISko],[GsOut,Fko,IPko,ISko,Pko],[GsOut,Fko,IPko,ISko,Pko,Sko],[GsOut,Fko,IPko,ISko,Sko],[GsOut,Fko,IPko,Pko],[GsOut,Fko,IPko,Pko,Sko],[GsOut,Fko,IPko,Sko],[GsOut,Fko,ISko],[GsOut,Fko,ISko,Pko],[GsOut,Fko,ISko,Pko,Sko],[GsOut,Fko,ISko,Sko],[GsOut,Fko,Pko],[GsOut,Fko,Pko,Sko],[GsOut,Fko,Sko],[GsOut,CIko],[GsOut,CIko,IPko],[GsOut,CIko,IPko,ISko],[GsOut,CIko,IPko,ISko,Pko],[GsOut,CIko,IPko,ISko,Pko,Sko],[GsOut,CIko,IPko,ISko,Sko],[GsOut,CIko,IPko,Pko],[GsOut,CIko,IPko,Pko,Sko],[GsOut,CIko,IPko,Sko],[GsOut,CIko,ISko],[GsOut,CIko,ISko,Pko],[GsOut,CIko,ISko,Pko,Sko],[GsOut,CIko,ISko,Sko],[GsOut,CIko,Pko],[GsOut,CIko,Pko,Sko],[GsOut,CIko,Sko],[GsOut,IPko],[GsOut,IPko,ISko],[GsOut,IPko,ISko,Pko],[GsOut,IPko,ISko,Pko,Sko],[GsOut,IPko,ISko,Sko],[GsOut,IPko,Pko],[GsOut,IPko,Pko,Sko],[GsOut,IPko,Sko],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[Tko],[Tko,Fko],[Tko,Fko,CIko],[Tko,Fko,CIko,IPko],[Tko,Fko,CIko,IPko,ISko],[Tko,Fko,CIko,IPko,ISko,Pko],[Tko,Fko,CIko,IPko,ISko,Pko,Sko],[Tko,Fko,CIko,IPko,ISko,Sko],[Tko,Fko,CIko,IPko,Pko],[Tko,Fko,CIko,IPko,Pko,Sko],[Tko,Fko,CIko,IPko,Sko],[Tko,Fko,CIko,ISko],[Tko,Fko,CIko,ISko,Pko],[Tko,Fko,CIko,ISko,Pko,Sko],[Tko,Fko,CIko,ISko,Sko],[Tko,Fko,CIko,Pko],[Tko,Fko,CIko,Pko,Sko],[Tko,Fko,CIko,Sko],[Tko,Fko,IPko],[Tko,Fko,IPko,ISko],[Tko,Fko,IPko,ISko,Pko],[Tko,Fko,IPko,ISko,Pko,Sko],[Tko,Fko,IPko,ISko,Sko],[Tko,Fko,IPko,Pko],[Tko,Fko,IPko,Pko,Sko],[Tko,Fko,IPko,Sko],[Tko,Fko,ISko],[Tko,Fko,ISko,Pko],[Tko,Fko,ISko,Pko,Sko],[Tko,Fko,ISko,Sko],[Tko,Fko,Pko],[Tko,Fko,Pko,Sko],[Tko,Fko,Sko],[Tko,CIko],[Tko,CIko,IPko],[Tko,CIko,IPko,ISko],[Tko,CIko,IPko,ISko,Pko],[Tko,CIko,IPko,ISko,Pko,Sko],[Tko,CIko,IPko,ISko,Sko],[Tko,CIko,IPko,Pko],[Tko,CIko,IPko,Pko,Sko],[Tko,CIko,IPko,Sko],[Tko,CIko,ISko],[Tko,CIko,ISko,Pko],[Tko,CIko,ISko,Pko,Sko],[Tko,CIko,ISko,Sko],[Tko,CIko,Pko],[Tko,CIko,Pko,Sko],[Tko,CIko,Sko],[Tko,IPko],[Tko,IPko,ISko],[Tko,IPko,ISko,Pko],[Tko,IPko,ISko,Pko,Sko],[Tko,IPko,ISko,Sko],[Tko,IPko,Pko],[Tko,IPko,Pko,Sko],[Tko,IPko,Sko],[Tko,ISko],[Tko,ISko,Pko],[Tko,ISko,Pko,Sko],[Tko,ISko,Sko],[Tko,Pko],[Tko,Pko,Sko],[Tko,Sko],[Fko],[Fko,CIko],[Fko,CIko,IPko],[Fko,CIko,IPko,ISko],[Fko,CIko,IPko,ISko,Pko],[Fko,CIko,IPko,ISko,Pko,Sko],[Fko,CIko,IPko,ISko,Sko],[Fko,CIko,IPko,Pko],[Fko,CIko,IPko,Pko,Sko],[Fko,CIko,IPko,Sko],[Fko,CIko,ISko],[Fko,CIko,ISko,Pko],[Fko,CIko,ISko,Pko,Sko],[Fko,CIko,ISko,Sko],[Fko,CIko,Pko],[Fko,CIko,Pko,Sko],[Fko,CIko,Sko],[Fko,IPko],[Fko,IPko,ISko],[Fko,IPko,ISko,Pko],[Fko,IPko,ISko,Pko,Sko],[Fko,IPko,ISko,Sko],[Fko,IPko,Pko],[Fko,IPko,Pko,Sko],[Fko,IPko,Sko],[Fko,ISko],[Fko,ISko,Pko],[Fko,ISko,Pko,Sko],[Fko,ISko,Sko],[Fko,Pko],[Fko,Pko,Sko],[Fko,Sko],[CIko],[CIko,IPko],[CIko,IPko,ISko],[CIko,IPko,ISko,Pko],[CIko,IPko,ISko,Pko,Sko],[CIko,IPko,ISko,Sko],[CIko,IPko,Pko],[CIko,IPko,Pko,Sko],[CIko,IPko,Sko],[CIko,ISko],[CIko,ISko,Pko],[CIko,ISko,Pko,Sko],[CIko,ISko,Sko],[CIko,Pko],[CIko,Pko,Sko],[CIko,Sko],[IPko],[IPko,ISko],[IPko,ISko,Pko],[IPko,ISko,Pko,Sko],[IPko,ISko,Sko],[IPko,Pko],[IPko,Pko,Sko],[IPko,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko],[PiI],[SjJ],[Tk2],[Tk3],[CIk2],[CIk3],[CIk4]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj])
    )),
    set_union([I],Pi,PiI),
    true((
        mshare([[GsOut],[GsOut,Tko],[GsOut,Tko,Fko],[GsOut,Tko,Fko,CIko],[GsOut,Tko,Fko,CIko,IPko],[GsOut,Tko,Fko,CIko,IPko,ISko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,ISko,Sko],[GsOut,Tko,Fko,CIko,IPko,Pko],[GsOut,Tko,Fko,CIko,IPko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,Sko],[GsOut,Tko,Fko,CIko,ISko],[GsOut,Tko,Fko,CIko,ISko,Pko],[GsOut,Tko,Fko,CIko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,ISko,Sko],[GsOut,Tko,Fko,CIko,Pko],[GsOut,Tko,Fko,CIko,Pko,Sko],[GsOut,Tko,Fko,CIko,Sko],[GsOut,Tko,Fko,IPko],[GsOut,Tko,Fko,IPko,ISko],[GsOut,Tko,Fko,IPko,ISko,Pko],[GsOut,Tko,Fko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,IPko,ISko,Sko],[GsOut,Tko,Fko,IPko,Pko],[GsOut,Tko,Fko,IPko,Pko,Sko],[GsOut,Tko,Fko,IPko,Sko],[GsOut,Tko,Fko,ISko],[GsOut,Tko,Fko,ISko,Pko],[GsOut,Tko,Fko,ISko,Pko,Sko],[GsOut,Tko,Fko,ISko,Sko],[GsOut,Tko,Fko,Pko],[GsOut,Tko,Fko,Pko,Sko],[GsOut,Tko,Fko,Sko],[GsOut,Tko,CIko],[GsOut,Tko,CIko,IPko],[GsOut,Tko,CIko,IPko,ISko],[GsOut,Tko,CIko,IPko,ISko,Pko],[GsOut,Tko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,CIko,IPko,ISko,Sko],[GsOut,Tko,CIko,IPko,Pko],[GsOut,Tko,CIko,IPko,Pko,Sko],[GsOut,Tko,CIko,IPko,Sko],[GsOut,Tko,CIko,ISko],[GsOut,Tko,CIko,ISko,Pko],[GsOut,Tko,CIko,ISko,Pko,Sko],[GsOut,Tko,CIko,ISko,Sko],[GsOut,Tko,CIko,Pko],[GsOut,Tko,CIko,Pko,Sko],[GsOut,Tko,CIko,Sko],[GsOut,Tko,IPko],[GsOut,Tko,IPko,ISko],[GsOut,Tko,IPko,ISko,Pko],[GsOut,Tko,IPko,ISko,Pko,Sko],[GsOut,Tko,IPko,ISko,Sko],[GsOut,Tko,IPko,Pko],[GsOut,Tko,IPko,Pko,Sko],[GsOut,Tko,IPko,Sko],[GsOut,Tko,ISko],[GsOut,Tko,ISko,Pko],[GsOut,Tko,ISko,Pko,Sko],[GsOut,Tko,ISko,Sko],[GsOut,Tko,Pko],[GsOut,Tko,Pko,Sko],[GsOut,Tko,Sko],[GsOut,Fko],[GsOut,Fko,CIko],[GsOut,Fko,CIko,IPko],[GsOut,Fko,CIko,IPko,ISko],[GsOut,Fko,CIko,IPko,ISko,Pko],[GsOut,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Fko,CIko,IPko,ISko,Sko],[GsOut,Fko,CIko,IPko,Pko],[GsOut,Fko,CIko,IPko,Pko,Sko],[GsOut,Fko,CIko,IPko,Sko],[GsOut,Fko,CIko,ISko],[GsOut,Fko,CIko,ISko,Pko],[GsOut,Fko,CIko,ISko,Pko,Sko],[GsOut,Fko,CIko,ISko,Sko],[GsOut,Fko,CIko,Pko],[GsOut,Fko,CIko,Pko,Sko],[GsOut,Fko,CIko,Sko],[GsOut,Fko,IPko],[GsOut,Fko,IPko,ISko],[GsOut,Fko,IPko,ISko,Pko],[GsOut,Fko,IPko,ISko,Pko,Sko],[GsOut,Fko,IPko,ISko,Sko],[GsOut,Fko,IPko,Pko],[GsOut,Fko,IPko,Pko,Sko],[GsOut,Fko,IPko,Sko],[GsOut,Fko,ISko],[GsOut,Fko,ISko,Pko],[GsOut,Fko,ISko,Pko,Sko],[GsOut,Fko,ISko,Sko],[GsOut,Fko,Pko],[GsOut,Fko,Pko,Sko],[GsOut,Fko,Sko],[GsOut,CIko],[GsOut,CIko,IPko],[GsOut,CIko,IPko,ISko],[GsOut,CIko,IPko,ISko,Pko],[GsOut,CIko,IPko,ISko,Pko,Sko],[GsOut,CIko,IPko,ISko,Sko],[GsOut,CIko,IPko,Pko],[GsOut,CIko,IPko,Pko,Sko],[GsOut,CIko,IPko,Sko],[GsOut,CIko,ISko],[GsOut,CIko,ISko,Pko],[GsOut,CIko,ISko,Pko,Sko],[GsOut,CIko,ISko,Sko],[GsOut,CIko,Pko],[GsOut,CIko,Pko,Sko],[GsOut,CIko,Sko],[GsOut,IPko],[GsOut,IPko,ISko],[GsOut,IPko,ISko,Pko],[GsOut,IPko,ISko,Pko,Sko],[GsOut,IPko,ISko,Sko],[GsOut,IPko,Pko],[GsOut,IPko,Pko,Sko],[GsOut,IPko,Sko],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[Tko],[Tko,Fko],[Tko,Fko,CIko],[Tko,Fko,CIko,IPko],[Tko,Fko,CIko,IPko,ISko],[Tko,Fko,CIko,IPko,ISko,Pko],[Tko,Fko,CIko,IPko,ISko,Pko,Sko],[Tko,Fko,CIko,IPko,ISko,Sko],[Tko,Fko,CIko,IPko,Pko],[Tko,Fko,CIko,IPko,Pko,Sko],[Tko,Fko,CIko,IPko,Sko],[Tko,Fko,CIko,ISko],[Tko,Fko,CIko,ISko,Pko],[Tko,Fko,CIko,ISko,Pko,Sko],[Tko,Fko,CIko,ISko,Sko],[Tko,Fko,CIko,Pko],[Tko,Fko,CIko,Pko,Sko],[Tko,Fko,CIko,Sko],[Tko,Fko,IPko],[Tko,Fko,IPko,ISko],[Tko,Fko,IPko,ISko,Pko],[Tko,Fko,IPko,ISko,Pko,Sko],[Tko,Fko,IPko,ISko,Sko],[Tko,Fko,IPko,Pko],[Tko,Fko,IPko,Pko,Sko],[Tko,Fko,IPko,Sko],[Tko,Fko,ISko],[Tko,Fko,ISko,Pko],[Tko,Fko,ISko,Pko,Sko],[Tko,Fko,ISko,Sko],[Tko,Fko,Pko],[Tko,Fko,Pko,Sko],[Tko,Fko,Sko],[Tko,CIko],[Tko,CIko,IPko],[Tko,CIko,IPko,ISko],[Tko,CIko,IPko,ISko,Pko],[Tko,CIko,IPko,ISko,Pko,Sko],[Tko,CIko,IPko,ISko,Sko],[Tko,CIko,IPko,Pko],[Tko,CIko,IPko,Pko,Sko],[Tko,CIko,IPko,Sko],[Tko,CIko,ISko],[Tko,CIko,ISko,Pko],[Tko,CIko,ISko,Pko,Sko],[Tko,CIko,ISko,Sko],[Tko,CIko,Pko],[Tko,CIko,Pko,Sko],[Tko,CIko,Sko],[Tko,IPko],[Tko,IPko,ISko],[Tko,IPko,ISko,Pko],[Tko,IPko,ISko,Pko,Sko],[Tko,IPko,ISko,Sko],[Tko,IPko,Pko],[Tko,IPko,Pko,Sko],[Tko,IPko,Sko],[Tko,ISko],[Tko,ISko,Pko],[Tko,ISko,Pko,Sko],[Tko,ISko,Sko],[Tko,Pko],[Tko,Pko,Sko],[Tko,Sko],[Fko],[Fko,CIko],[Fko,CIko,IPko],[Fko,CIko,IPko,ISko],[Fko,CIko,IPko,ISko,Pko],[Fko,CIko,IPko,ISko,Pko,Sko],[Fko,CIko,IPko,ISko,Sko],[Fko,CIko,IPko,Pko],[Fko,CIko,IPko,Pko,Sko],[Fko,CIko,IPko,Sko],[Fko,CIko,ISko],[Fko,CIko,ISko,Pko],[Fko,CIko,ISko,Pko,Sko],[Fko,CIko,ISko,Sko],[Fko,CIko,Pko],[Fko,CIko,Pko,Sko],[Fko,CIko,Sko],[Fko,IPko],[Fko,IPko,ISko],[Fko,IPko,ISko,Pko],[Fko,IPko,ISko,Pko,Sko],[Fko,IPko,ISko,Sko],[Fko,IPko,Pko],[Fko,IPko,Pko,Sko],[Fko,IPko,Sko],[Fko,ISko],[Fko,ISko,Pko],[Fko,ISko,Pko,Sko],[Fko,ISko,Sko],[Fko,Pko],[Fko,Pko,Sko],[Fko,Sko],[CIko],[CIko,IPko],[CIko,IPko,ISko],[CIko,IPko,ISko,Pko],[CIko,IPko,ISko,Pko,Sko],[CIko,IPko,ISko,Sko],[CIko,IPko,Pko],[CIko,IPko,Pko,Sko],[CIko,IPko,Sko],[CIko,ISko],[CIko,ISko,Pko],[CIko,ISko,Pko,Sko],[CIko,ISko,Sko],[CIko,Pko],[CIko,Pko,Sko],[CIko,Sko],[IPko],[IPko,ISko],[IPko,ISko,Pko],[IPko,ISko,Pko,Sko],[IPko,ISko,Sko],[IPko,Pko],[IPko,Pko,Sko],[IPko,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko],[SjJ],[Tk2],[Tk3],[CIk2],[CIk3],[CIk4]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI])
    )),
    set_union([J],Sj,SjJ),
    true((
        mshare([[GsOut],[GsOut,Tko],[GsOut,Tko,Fko],[GsOut,Tko,Fko,CIko],[GsOut,Tko,Fko,CIko,IPko],[GsOut,Tko,Fko,CIko,IPko,ISko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,ISko,Sko],[GsOut,Tko,Fko,CIko,IPko,Pko],[GsOut,Tko,Fko,CIko,IPko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,Sko],[GsOut,Tko,Fko,CIko,ISko],[GsOut,Tko,Fko,CIko,ISko,Pko],[GsOut,Tko,Fko,CIko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,ISko,Sko],[GsOut,Tko,Fko,CIko,Pko],[GsOut,Tko,Fko,CIko,Pko,Sko],[GsOut,Tko,Fko,CIko,Sko],[GsOut,Tko,Fko,IPko],[GsOut,Tko,Fko,IPko,ISko],[GsOut,Tko,Fko,IPko,ISko,Pko],[GsOut,Tko,Fko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,IPko,ISko,Sko],[GsOut,Tko,Fko,IPko,Pko],[GsOut,Tko,Fko,IPko,Pko,Sko],[GsOut,Tko,Fko,IPko,Sko],[GsOut,Tko,Fko,ISko],[GsOut,Tko,Fko,ISko,Pko],[GsOut,Tko,Fko,ISko,Pko,Sko],[GsOut,Tko,Fko,ISko,Sko],[GsOut,Tko,Fko,Pko],[GsOut,Tko,Fko,Pko,Sko],[GsOut,Tko,Fko,Sko],[GsOut,Tko,CIko],[GsOut,Tko,CIko,IPko],[GsOut,Tko,CIko,IPko,ISko],[GsOut,Tko,CIko,IPko,ISko,Pko],[GsOut,Tko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,CIko,IPko,ISko,Sko],[GsOut,Tko,CIko,IPko,Pko],[GsOut,Tko,CIko,IPko,Pko,Sko],[GsOut,Tko,CIko,IPko,Sko],[GsOut,Tko,CIko,ISko],[GsOut,Tko,CIko,ISko,Pko],[GsOut,Tko,CIko,ISko,Pko,Sko],[GsOut,Tko,CIko,ISko,Sko],[GsOut,Tko,CIko,Pko],[GsOut,Tko,CIko,Pko,Sko],[GsOut,Tko,CIko,Sko],[GsOut,Tko,IPko],[GsOut,Tko,IPko,ISko],[GsOut,Tko,IPko,ISko,Pko],[GsOut,Tko,IPko,ISko,Pko,Sko],[GsOut,Tko,IPko,ISko,Sko],[GsOut,Tko,IPko,Pko],[GsOut,Tko,IPko,Pko,Sko],[GsOut,Tko,IPko,Sko],[GsOut,Tko,ISko],[GsOut,Tko,ISko,Pko],[GsOut,Tko,ISko,Pko,Sko],[GsOut,Tko,ISko,Sko],[GsOut,Tko,Pko],[GsOut,Tko,Pko,Sko],[GsOut,Tko,Sko],[GsOut,Fko],[GsOut,Fko,CIko],[GsOut,Fko,CIko,IPko],[GsOut,Fko,CIko,IPko,ISko],[GsOut,Fko,CIko,IPko,ISko,Pko],[GsOut,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Fko,CIko,IPko,ISko,Sko],[GsOut,Fko,CIko,IPko,Pko],[GsOut,Fko,CIko,IPko,Pko,Sko],[GsOut,Fko,CIko,IPko,Sko],[GsOut,Fko,CIko,ISko],[GsOut,Fko,CIko,ISko,Pko],[GsOut,Fko,CIko,ISko,Pko,Sko],[GsOut,Fko,CIko,ISko,Sko],[GsOut,Fko,CIko,Pko],[GsOut,Fko,CIko,Pko,Sko],[GsOut,Fko,CIko,Sko],[GsOut,Fko,IPko],[GsOut,Fko,IPko,ISko],[GsOut,Fko,IPko,ISko,Pko],[GsOut,Fko,IPko,ISko,Pko,Sko],[GsOut,Fko,IPko,ISko,Sko],[GsOut,Fko,IPko,Pko],[GsOut,Fko,IPko,Pko,Sko],[GsOut,Fko,IPko,Sko],[GsOut,Fko,ISko],[GsOut,Fko,ISko,Pko],[GsOut,Fko,ISko,Pko,Sko],[GsOut,Fko,ISko,Sko],[GsOut,Fko,Pko],[GsOut,Fko,Pko,Sko],[GsOut,Fko,Sko],[GsOut,CIko],[GsOut,CIko,IPko],[GsOut,CIko,IPko,ISko],[GsOut,CIko,IPko,ISko,Pko],[GsOut,CIko,IPko,ISko,Pko,Sko],[GsOut,CIko,IPko,ISko,Sko],[GsOut,CIko,IPko,Pko],[GsOut,CIko,IPko,Pko,Sko],[GsOut,CIko,IPko,Sko],[GsOut,CIko,ISko],[GsOut,CIko,ISko,Pko],[GsOut,CIko,ISko,Pko,Sko],[GsOut,CIko,ISko,Sko],[GsOut,CIko,Pko],[GsOut,CIko,Pko,Sko],[GsOut,CIko,Sko],[GsOut,IPko],[GsOut,IPko,ISko],[GsOut,IPko,ISko,Pko],[GsOut,IPko,ISko,Pko,Sko],[GsOut,IPko,ISko,Sko],[GsOut,IPko,Pko],[GsOut,IPko,Pko,Sko],[GsOut,IPko,Sko],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[Tko],[Tko,Fko],[Tko,Fko,CIko],[Tko,Fko,CIko,IPko],[Tko,Fko,CIko,IPko,ISko],[Tko,Fko,CIko,IPko,ISko,Pko],[Tko,Fko,CIko,IPko,ISko,Pko,Sko],[Tko,Fko,CIko,IPko,ISko,Sko],[Tko,Fko,CIko,IPko,Pko],[Tko,Fko,CIko,IPko,Pko,Sko],[Tko,Fko,CIko,IPko,Sko],[Tko,Fko,CIko,ISko],[Tko,Fko,CIko,ISko,Pko],[Tko,Fko,CIko,ISko,Pko,Sko],[Tko,Fko,CIko,ISko,Sko],[Tko,Fko,CIko,Pko],[Tko,Fko,CIko,Pko,Sko],[Tko,Fko,CIko,Sko],[Tko,Fko,IPko],[Tko,Fko,IPko,ISko],[Tko,Fko,IPko,ISko,Pko],[Tko,Fko,IPko,ISko,Pko,Sko],[Tko,Fko,IPko,ISko,Sko],[Tko,Fko,IPko,Pko],[Tko,Fko,IPko,Pko,Sko],[Tko,Fko,IPko,Sko],[Tko,Fko,ISko],[Tko,Fko,ISko,Pko],[Tko,Fko,ISko,Pko,Sko],[Tko,Fko,ISko,Sko],[Tko,Fko,Pko],[Tko,Fko,Pko,Sko],[Tko,Fko,Sko],[Tko,CIko],[Tko,CIko,IPko],[Tko,CIko,IPko,ISko],[Tko,CIko,IPko,ISko,Pko],[Tko,CIko,IPko,ISko,Pko,Sko],[Tko,CIko,IPko,ISko,Sko],[Tko,CIko,IPko,Pko],[Tko,CIko,IPko,Pko,Sko],[Tko,CIko,IPko,Sko],[Tko,CIko,ISko],[Tko,CIko,ISko,Pko],[Tko,CIko,ISko,Pko,Sko],[Tko,CIko,ISko,Sko],[Tko,CIko,Pko],[Tko,CIko,Pko,Sko],[Tko,CIko,Sko],[Tko,IPko],[Tko,IPko,ISko],[Tko,IPko,ISko,Pko],[Tko,IPko,ISko,Pko,Sko],[Tko,IPko,ISko,Sko],[Tko,IPko,Pko],[Tko,IPko,Pko,Sko],[Tko,IPko,Sko],[Tko,ISko],[Tko,ISko,Pko],[Tko,ISko,Pko,Sko],[Tko,ISko,Sko],[Tko,Pko],[Tko,Pko,Sko],[Tko,Sko],[Fko],[Fko,CIko],[Fko,CIko,IPko],[Fko,CIko,IPko,ISko],[Fko,CIko,IPko,ISko,Pko],[Fko,CIko,IPko,ISko,Pko,Sko],[Fko,CIko,IPko,ISko,Sko],[Fko,CIko,IPko,Pko],[Fko,CIko,IPko,Pko,Sko],[Fko,CIko,IPko,Sko],[Fko,CIko,ISko],[Fko,CIko,ISko,Pko],[Fko,CIko,ISko,Pko,Sko],[Fko,CIko,ISko,Sko],[Fko,CIko,Pko],[Fko,CIko,Pko,Sko],[Fko,CIko,Sko],[Fko,IPko],[Fko,IPko,ISko],[Fko,IPko,ISko,Pko],[Fko,IPko,ISko,Pko,Sko],[Fko,IPko,ISko,Sko],[Fko,IPko,Pko],[Fko,IPko,Pko,Sko],[Fko,IPko,Sko],[Fko,ISko],[Fko,ISko,Pko],[Fko,ISko,Pko,Sko],[Fko,ISko,Sko],[Fko,Pko],[Fko,Pko,Sko],[Fko,Sko],[CIko],[CIko,IPko],[CIko,IPko,ISko],[CIko,IPko,ISko,Pko],[CIko,IPko,ISko,Pko,Sko],[CIko,IPko,ISko,Sko],[CIko,IPko,Pko],[CIko,IPko,Pko,Sko],[CIko,IPko,Sko],[CIko,ISko],[CIko,ISko,Pko],[CIko,ISko,Pko,Sko],[CIko,ISko,Sko],[CIko,Pko],[CIko,Pko,Sko],[CIko,Sko],[IPko],[IPko,ISko],[IPko,ISko,Pko],[IPko,ISko,Pko,Sko],[IPko,ISko,Sko],[IPko,Pko],[IPko,Pko,Sko],[IPko,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko],[Tk2],[Tk3],[CIk2],[CIk3],[CIk4]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ])
    )),
    'update_circuit/6/2/$disj/1'(K,Tk,Fi,J,Tk2),
    true((
        mshare([[GsOut],[GsOut,Tko],[GsOut,Tko,Fko],[GsOut,Tko,Fko,CIko],[GsOut,Tko,Fko,CIko,IPko],[GsOut,Tko,Fko,CIko,IPko,ISko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,ISko,Sko],[GsOut,Tko,Fko,CIko,IPko,Pko],[GsOut,Tko,Fko,CIko,IPko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,Sko],[GsOut,Tko,Fko,CIko,ISko],[GsOut,Tko,Fko,CIko,ISko,Pko],[GsOut,Tko,Fko,CIko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,ISko,Sko],[GsOut,Tko,Fko,CIko,Pko],[GsOut,Tko,Fko,CIko,Pko,Sko],[GsOut,Tko,Fko,CIko,Sko],[GsOut,Tko,Fko,IPko],[GsOut,Tko,Fko,IPko,ISko],[GsOut,Tko,Fko,IPko,ISko,Pko],[GsOut,Tko,Fko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,IPko,ISko,Sko],[GsOut,Tko,Fko,IPko,Pko],[GsOut,Tko,Fko,IPko,Pko,Sko],[GsOut,Tko,Fko,IPko,Sko],[GsOut,Tko,Fko,ISko],[GsOut,Tko,Fko,ISko,Pko],[GsOut,Tko,Fko,ISko,Pko,Sko],[GsOut,Tko,Fko,ISko,Sko],[GsOut,Tko,Fko,Pko],[GsOut,Tko,Fko,Pko,Sko],[GsOut,Tko,Fko,Sko],[GsOut,Tko,CIko],[GsOut,Tko,CIko,IPko],[GsOut,Tko,CIko,IPko,ISko],[GsOut,Tko,CIko,IPko,ISko,Pko],[GsOut,Tko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,CIko,IPko,ISko,Sko],[GsOut,Tko,CIko,IPko,Pko],[GsOut,Tko,CIko,IPko,Pko,Sko],[GsOut,Tko,CIko,IPko,Sko],[GsOut,Tko,CIko,ISko],[GsOut,Tko,CIko,ISko,Pko],[GsOut,Tko,CIko,ISko,Pko,Sko],[GsOut,Tko,CIko,ISko,Sko],[GsOut,Tko,CIko,Pko],[GsOut,Tko,CIko,Pko,Sko],[GsOut,Tko,CIko,Sko],[GsOut,Tko,IPko],[GsOut,Tko,IPko,ISko],[GsOut,Tko,IPko,ISko,Pko],[GsOut,Tko,IPko,ISko,Pko,Sko],[GsOut,Tko,IPko,ISko,Sko],[GsOut,Tko,IPko,Pko],[GsOut,Tko,IPko,Pko,Sko],[GsOut,Tko,IPko,Sko],[GsOut,Tko,ISko],[GsOut,Tko,ISko,Pko],[GsOut,Tko,ISko,Pko,Sko],[GsOut,Tko,ISko,Sko],[GsOut,Tko,Pko],[GsOut,Tko,Pko,Sko],[GsOut,Tko,Sko],[GsOut,Fko],[GsOut,Fko,CIko],[GsOut,Fko,CIko,IPko],[GsOut,Fko,CIko,IPko,ISko],[GsOut,Fko,CIko,IPko,ISko,Pko],[GsOut,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Fko,CIko,IPko,ISko,Sko],[GsOut,Fko,CIko,IPko,Pko],[GsOut,Fko,CIko,IPko,Pko,Sko],[GsOut,Fko,CIko,IPko,Sko],[GsOut,Fko,CIko,ISko],[GsOut,Fko,CIko,ISko,Pko],[GsOut,Fko,CIko,ISko,Pko,Sko],[GsOut,Fko,CIko,ISko,Sko],[GsOut,Fko,CIko,Pko],[GsOut,Fko,CIko,Pko,Sko],[GsOut,Fko,CIko,Sko],[GsOut,Fko,IPko],[GsOut,Fko,IPko,ISko],[GsOut,Fko,IPko,ISko,Pko],[GsOut,Fko,IPko,ISko,Pko,Sko],[GsOut,Fko,IPko,ISko,Sko],[GsOut,Fko,IPko,Pko],[GsOut,Fko,IPko,Pko,Sko],[GsOut,Fko,IPko,Sko],[GsOut,Fko,ISko],[GsOut,Fko,ISko,Pko],[GsOut,Fko,ISko,Pko,Sko],[GsOut,Fko,ISko,Sko],[GsOut,Fko,Pko],[GsOut,Fko,Pko,Sko],[GsOut,Fko,Sko],[GsOut,CIko],[GsOut,CIko,IPko],[GsOut,CIko,IPko,ISko],[GsOut,CIko,IPko,ISko,Pko],[GsOut,CIko,IPko,ISko,Pko,Sko],[GsOut,CIko,IPko,ISko,Sko],[GsOut,CIko,IPko,Pko],[GsOut,CIko,IPko,Pko,Sko],[GsOut,CIko,IPko,Sko],[GsOut,CIko,ISko],[GsOut,CIko,ISko,Pko],[GsOut,CIko,ISko,Pko,Sko],[GsOut,CIko,ISko,Sko],[GsOut,CIko,Pko],[GsOut,CIko,Pko,Sko],[GsOut,CIko,Sko],[GsOut,IPko],[GsOut,IPko,ISko],[GsOut,IPko,ISko,Pko],[GsOut,IPko,ISko,Pko,Sko],[GsOut,IPko,ISko,Sko],[GsOut,IPko,Pko],[GsOut,IPko,Pko,Sko],[GsOut,IPko,Sko],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[Tko],[Tko,Fko],[Tko,Fko,CIko],[Tko,Fko,CIko,IPko],[Tko,Fko,CIko,IPko,ISko],[Tko,Fko,CIko,IPko,ISko,Pko],[Tko,Fko,CIko,IPko,ISko,Pko,Sko],[Tko,Fko,CIko,IPko,ISko,Sko],[Tko,Fko,CIko,IPko,Pko],[Tko,Fko,CIko,IPko,Pko,Sko],[Tko,Fko,CIko,IPko,Sko],[Tko,Fko,CIko,ISko],[Tko,Fko,CIko,ISko,Pko],[Tko,Fko,CIko,ISko,Pko,Sko],[Tko,Fko,CIko,ISko,Sko],[Tko,Fko,CIko,Pko],[Tko,Fko,CIko,Pko,Sko],[Tko,Fko,CIko,Sko],[Tko,Fko,IPko],[Tko,Fko,IPko,ISko],[Tko,Fko,IPko,ISko,Pko],[Tko,Fko,IPko,ISko,Pko,Sko],[Tko,Fko,IPko,ISko,Sko],[Tko,Fko,IPko,Pko],[Tko,Fko,IPko,Pko,Sko],[Tko,Fko,IPko,Sko],[Tko,Fko,ISko],[Tko,Fko,ISko,Pko],[Tko,Fko,ISko,Pko,Sko],[Tko,Fko,ISko,Sko],[Tko,Fko,Pko],[Tko,Fko,Pko,Sko],[Tko,Fko,Sko],[Tko,CIko],[Tko,CIko,IPko],[Tko,CIko,IPko,ISko],[Tko,CIko,IPko,ISko,Pko],[Tko,CIko,IPko,ISko,Pko,Sko],[Tko,CIko,IPko,ISko,Sko],[Tko,CIko,IPko,Pko],[Tko,CIko,IPko,Pko,Sko],[Tko,CIko,IPko,Sko],[Tko,CIko,ISko],[Tko,CIko,ISko,Pko],[Tko,CIko,ISko,Pko,Sko],[Tko,CIko,ISko,Sko],[Tko,CIko,Pko],[Tko,CIko,Pko,Sko],[Tko,CIko,Sko],[Tko,IPko],[Tko,IPko,ISko],[Tko,IPko,ISko,Pko],[Tko,IPko,ISko,Pko,Sko],[Tko,IPko,ISko,Sko],[Tko,IPko,Pko],[Tko,IPko,Pko,Sko],[Tko,IPko,Sko],[Tko,ISko],[Tko,ISko,Pko],[Tko,ISko,Pko,Sko],[Tko,ISko,Sko],[Tko,Pko],[Tko,Pko,Sko],[Tko,Sko],[Fko],[Fko,CIko],[Fko,CIko,IPko],[Fko,CIko,IPko,ISko],[Fko,CIko,IPko,ISko,Pko],[Fko,CIko,IPko,ISko,Pko,Sko],[Fko,CIko,IPko,ISko,Sko],[Fko,CIko,IPko,Pko],[Fko,CIko,IPko,Pko,Sko],[Fko,CIko,IPko,Sko],[Fko,CIko,ISko],[Fko,CIko,ISko,Pko],[Fko,CIko,ISko,Pko,Sko],[Fko,CIko,ISko,Sko],[Fko,CIko,Pko],[Fko,CIko,Pko,Sko],[Fko,CIko,Sko],[Fko,IPko],[Fko,IPko,ISko],[Fko,IPko,ISko,Pko],[Fko,IPko,ISko,Pko,Sko],[Fko,IPko,ISko,Sko],[Fko,IPko,Pko],[Fko,IPko,Pko,Sko],[Fko,IPko,Sko],[Fko,ISko],[Fko,ISko,Pko],[Fko,ISko,Pko,Sko],[Fko,ISko,Sko],[Fko,Pko],[Fko,Pko,Sko],[Fko,Sko],[CIko],[CIko,IPko],[CIko,IPko,ISko],[CIko,IPko,ISko,Pko],[CIko,IPko,ISko,Pko,Sko],[CIko,IPko,ISko,Sko],[CIko,IPko,Pko],[CIko,IPko,Pko,Sko],[CIko,IPko,Sko],[CIko,ISko],[CIko,ISko,Pko],[CIko,ISko,Pko,Sko],[CIko,ISko,Sko],[CIko,Pko],[CIko,Pko,Sko],[CIko,Sko],[IPko],[IPko,ISko],[IPko,ISko,Pko],[IPko,ISko,Pko,Sko],[IPko,ISko,Sko],[IPko,Pko],[IPko,Pko,Sko],[IPko,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko],[Tk3],[CIk2],[CIk3],[CIk4]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2])
    )),
    'update_circuit/6/2/$disj/2'(K,I,Fj,Tk2,Tk3),
    true((
        mshare([[GsOut],[GsOut,Tko],[GsOut,Tko,Fko],[GsOut,Tko,Fko,CIko],[GsOut,Tko,Fko,CIko,IPko],[GsOut,Tko,Fko,CIko,IPko,ISko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko],[GsOut,Tko,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,ISko,Sko],[GsOut,Tko,Fko,CIko,IPko,Pko],[GsOut,Tko,Fko,CIko,IPko,Pko,Sko],[GsOut,Tko,Fko,CIko,IPko,Sko],[GsOut,Tko,Fko,CIko,ISko],[GsOut,Tko,Fko,CIko,ISko,Pko],[GsOut,Tko,Fko,CIko,ISko,Pko,Sko],[GsOut,Tko,Fko,CIko,ISko,Sko],[GsOut,Tko,Fko,CIko,Pko],[GsOut,Tko,Fko,CIko,Pko,Sko],[GsOut,Tko,Fko,CIko,Sko],[GsOut,Tko,Fko,IPko],[GsOut,Tko,Fko,IPko,ISko],[GsOut,Tko,Fko,IPko,ISko,Pko],[GsOut,Tko,Fko,IPko,ISko,Pko,Sko],[GsOut,Tko,Fko,IPko,ISko,Sko],[GsOut,Tko,Fko,IPko,Pko],[GsOut,Tko,Fko,IPko,Pko,Sko],[GsOut,Tko,Fko,IPko,Sko],[GsOut,Tko,Fko,ISko],[GsOut,Tko,Fko,ISko,Pko],[GsOut,Tko,Fko,ISko,Pko,Sko],[GsOut,Tko,Fko,ISko,Sko],[GsOut,Tko,Fko,Pko],[GsOut,Tko,Fko,Pko,Sko],[GsOut,Tko,Fko,Sko],[GsOut,Tko,CIko],[GsOut,Tko,CIko,IPko],[GsOut,Tko,CIko,IPko,ISko],[GsOut,Tko,CIko,IPko,ISko,Pko],[GsOut,Tko,CIko,IPko,ISko,Pko,Sko],[GsOut,Tko,CIko,IPko,ISko,Sko],[GsOut,Tko,CIko,IPko,Pko],[GsOut,Tko,CIko,IPko,Pko,Sko],[GsOut,Tko,CIko,IPko,Sko],[GsOut,Tko,CIko,ISko],[GsOut,Tko,CIko,ISko,Pko],[GsOut,Tko,CIko,ISko,Pko,Sko],[GsOut,Tko,CIko,ISko,Sko],[GsOut,Tko,CIko,Pko],[GsOut,Tko,CIko,Pko,Sko],[GsOut,Tko,CIko,Sko],[GsOut,Tko,IPko],[GsOut,Tko,IPko,ISko],[GsOut,Tko,IPko,ISko,Pko],[GsOut,Tko,IPko,ISko,Pko,Sko],[GsOut,Tko,IPko,ISko,Sko],[GsOut,Tko,IPko,Pko],[GsOut,Tko,IPko,Pko,Sko],[GsOut,Tko,IPko,Sko],[GsOut,Tko,ISko],[GsOut,Tko,ISko,Pko],[GsOut,Tko,ISko,Pko,Sko],[GsOut,Tko,ISko,Sko],[GsOut,Tko,Pko],[GsOut,Tko,Pko,Sko],[GsOut,Tko,Sko],[GsOut,Fko],[GsOut,Fko,CIko],[GsOut,Fko,CIko,IPko],[GsOut,Fko,CIko,IPko,ISko],[GsOut,Fko,CIko,IPko,ISko,Pko],[GsOut,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Fko,CIko,IPko,ISko,Sko],[GsOut,Fko,CIko,IPko,Pko],[GsOut,Fko,CIko,IPko,Pko,Sko],[GsOut,Fko,CIko,IPko,Sko],[GsOut,Fko,CIko,ISko],[GsOut,Fko,CIko,ISko,Pko],[GsOut,Fko,CIko,ISko,Pko,Sko],[GsOut,Fko,CIko,ISko,Sko],[GsOut,Fko,CIko,Pko],[GsOut,Fko,CIko,Pko,Sko],[GsOut,Fko,CIko,Sko],[GsOut,Fko,IPko],[GsOut,Fko,IPko,ISko],[GsOut,Fko,IPko,ISko,Pko],[GsOut,Fko,IPko,ISko,Pko,Sko],[GsOut,Fko,IPko,ISko,Sko],[GsOut,Fko,IPko,Pko],[GsOut,Fko,IPko,Pko,Sko],[GsOut,Fko,IPko,Sko],[GsOut,Fko,ISko],[GsOut,Fko,ISko,Pko],[GsOut,Fko,ISko,Pko,Sko],[GsOut,Fko,ISko,Sko],[GsOut,Fko,Pko],[GsOut,Fko,Pko,Sko],[GsOut,Fko,Sko],[GsOut,CIko],[GsOut,CIko,IPko],[GsOut,CIko,IPko,ISko],[GsOut,CIko,IPko,ISko,Pko],[GsOut,CIko,IPko,ISko,Pko,Sko],[GsOut,CIko,IPko,ISko,Sko],[GsOut,CIko,IPko,Pko],[GsOut,CIko,IPko,Pko,Sko],[GsOut,CIko,IPko,Sko],[GsOut,CIko,ISko],[GsOut,CIko,ISko,Pko],[GsOut,CIko,ISko,Pko,Sko],[GsOut,CIko,ISko,Sko],[GsOut,CIko,Pko],[GsOut,CIko,Pko,Sko],[GsOut,CIko,Sko],[GsOut,IPko],[GsOut,IPko,ISko],[GsOut,IPko,ISko,Pko],[GsOut,IPko,ISko,Pko,Sko],[GsOut,IPko,ISko,Sko],[GsOut,IPko,Pko],[GsOut,IPko,Pko,Sko],[GsOut,IPko,Sko],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[Tko],[Tko,Fko],[Tko,Fko,CIko],[Tko,Fko,CIko,IPko],[Tko,Fko,CIko,IPko,ISko],[Tko,Fko,CIko,IPko,ISko,Pko],[Tko,Fko,CIko,IPko,ISko,Pko,Sko],[Tko,Fko,CIko,IPko,ISko,Sko],[Tko,Fko,CIko,IPko,Pko],[Tko,Fko,CIko,IPko,Pko,Sko],[Tko,Fko,CIko,IPko,Sko],[Tko,Fko,CIko,ISko],[Tko,Fko,CIko,ISko,Pko],[Tko,Fko,CIko,ISko,Pko,Sko],[Tko,Fko,CIko,ISko,Sko],[Tko,Fko,CIko,Pko],[Tko,Fko,CIko,Pko,Sko],[Tko,Fko,CIko,Sko],[Tko,Fko,IPko],[Tko,Fko,IPko,ISko],[Tko,Fko,IPko,ISko,Pko],[Tko,Fko,IPko,ISko,Pko,Sko],[Tko,Fko,IPko,ISko,Sko],[Tko,Fko,IPko,Pko],[Tko,Fko,IPko,Pko,Sko],[Tko,Fko,IPko,Sko],[Tko,Fko,ISko],[Tko,Fko,ISko,Pko],[Tko,Fko,ISko,Pko,Sko],[Tko,Fko,ISko,Sko],[Tko,Fko,Pko],[Tko,Fko,Pko,Sko],[Tko,Fko,Sko],[Tko,CIko],[Tko,CIko,IPko],[Tko,CIko,IPko,ISko],[Tko,CIko,IPko,ISko,Pko],[Tko,CIko,IPko,ISko,Pko,Sko],[Tko,CIko,IPko,ISko,Sko],[Tko,CIko,IPko,Pko],[Tko,CIko,IPko,Pko,Sko],[Tko,CIko,IPko,Sko],[Tko,CIko,ISko],[Tko,CIko,ISko,Pko],[Tko,CIko,ISko,Pko,Sko],[Tko,CIko,ISko,Sko],[Tko,CIko,Pko],[Tko,CIko,Pko,Sko],[Tko,CIko,Sko],[Tko,IPko],[Tko,IPko,ISko],[Tko,IPko,ISko,Pko],[Tko,IPko,ISko,Pko,Sko],[Tko,IPko,ISko,Sko],[Tko,IPko,Pko],[Tko,IPko,Pko,Sko],[Tko,IPko,Sko],[Tko,ISko],[Tko,ISko,Pko],[Tko,ISko,Pko,Sko],[Tko,ISko,Sko],[Tko,Pko],[Tko,Pko,Sko],[Tko,Sko],[Fko],[Fko,CIko],[Fko,CIko,IPko],[Fko,CIko,IPko,ISko],[Fko,CIko,IPko,ISko,Pko],[Fko,CIko,IPko,ISko,Pko,Sko],[Fko,CIko,IPko,ISko,Sko],[Fko,CIko,IPko,Pko],[Fko,CIko,IPko,Pko,Sko],[Fko,CIko,IPko,Sko],[Fko,CIko,ISko],[Fko,CIko,ISko,Pko],[Fko,CIko,ISko,Pko,Sko],[Fko,CIko,ISko,Sko],[Fko,CIko,Pko],[Fko,CIko,Pko,Sko],[Fko,CIko,Sko],[Fko,IPko],[Fko,IPko,ISko],[Fko,IPko,ISko,Pko],[Fko,IPko,ISko,Pko,Sko],[Fko,IPko,ISko,Sko],[Fko,IPko,Pko],[Fko,IPko,Pko,Sko],[Fko,IPko,Sko],[Fko,ISko],[Fko,ISko,Pko],[Fko,ISko,Pko,Sko],[Fko,ISko,Sko],[Fko,Pko],[Fko,Pko,Sko],[Fko,Sko],[CIko],[CIko,IPko],[CIko,IPko,ISko],[CIko,IPko,ISko,Pko],[CIko,IPko,ISko,Pko,Sko],[CIko,IPko,ISko,Sko],[CIko,IPko,Pko],[CIko,IPko,Pko,Sko],[CIko,IPko,Sko],[CIko,ISko],[CIko,ISko,Pko],[CIko,ISko,Pko,Sko],[CIko,ISko,Sko],[CIko,Pko],[CIko,Pko,Sko],[CIko,Sko],[IPko],[IPko,ISko],[IPko,ISko,Pko],[IPko,ISko,Pko,Sko],[IPko,ISko,Sko],[IPko,Pko],[IPko,Pko,Sko],[IPko,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko],[CIk2],[CIk3],[CIk4]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3])
    )),
    'update_circuit/6/2/$disj/3'(V,K,Tko,IPi,ISi,Tk3),
    true((
        mshare([[GsOut],[GsOut,Fko],[GsOut,Fko,CIko],[GsOut,Fko,CIko,IPko],[GsOut,Fko,CIko,IPko,ISko],[GsOut,Fko,CIko,IPko,ISko,Pko],[GsOut,Fko,CIko,IPko,ISko,Pko,Sko],[GsOut,Fko,CIko,IPko,ISko,Sko],[GsOut,Fko,CIko,IPko,Pko],[GsOut,Fko,CIko,IPko,Pko,Sko],[GsOut,Fko,CIko,IPko,Sko],[GsOut,Fko,CIko,ISko],[GsOut,Fko,CIko,ISko,Pko],[GsOut,Fko,CIko,ISko,Pko,Sko],[GsOut,Fko,CIko,ISko,Sko],[GsOut,Fko,CIko,Pko],[GsOut,Fko,CIko,Pko,Sko],[GsOut,Fko,CIko,Sko],[GsOut,Fko,IPko],[GsOut,Fko,IPko,ISko],[GsOut,Fko,IPko,ISko,Pko],[GsOut,Fko,IPko,ISko,Pko,Sko],[GsOut,Fko,IPko,ISko,Sko],[GsOut,Fko,IPko,Pko],[GsOut,Fko,IPko,Pko,Sko],[GsOut,Fko,IPko,Sko],[GsOut,Fko,ISko],[GsOut,Fko,ISko,Pko],[GsOut,Fko,ISko,Pko,Sko],[GsOut,Fko,ISko,Sko],[GsOut,Fko,Pko],[GsOut,Fko,Pko,Sko],[GsOut,Fko,Sko],[GsOut,CIko],[GsOut,CIko,IPko],[GsOut,CIko,IPko,ISko],[GsOut,CIko,IPko,ISko,Pko],[GsOut,CIko,IPko,ISko,Pko,Sko],[GsOut,CIko,IPko,ISko,Sko],[GsOut,CIko,IPko,Pko],[GsOut,CIko,IPko,Pko,Sko],[GsOut,CIko,IPko,Sko],[GsOut,CIko,ISko],[GsOut,CIko,ISko,Pko],[GsOut,CIko,ISko,Pko,Sko],[GsOut,CIko,ISko,Sko],[GsOut,CIko,Pko],[GsOut,CIko,Pko,Sko],[GsOut,CIko,Sko],[GsOut,IPko],[GsOut,IPko,ISko],[GsOut,IPko,ISko,Pko],[GsOut,IPko,ISko,Pko,Sko],[GsOut,IPko,ISko,Sko],[GsOut,IPko,Pko],[GsOut,IPko,Pko,Sko],[GsOut,IPko,Sko],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[Fko],[Fko,CIko],[Fko,CIko,IPko],[Fko,CIko,IPko,ISko],[Fko,CIko,IPko,ISko,Pko],[Fko,CIko,IPko,ISko,Pko,Sko],[Fko,CIko,IPko,ISko,Sko],[Fko,CIko,IPko,Pko],[Fko,CIko,IPko,Pko,Sko],[Fko,CIko,IPko,Sko],[Fko,CIko,ISko],[Fko,CIko,ISko,Pko],[Fko,CIko,ISko,Pko,Sko],[Fko,CIko,ISko,Sko],[Fko,CIko,Pko],[Fko,CIko,Pko,Sko],[Fko,CIko,Sko],[Fko,IPko],[Fko,IPko,ISko],[Fko,IPko,ISko,Pko],[Fko,IPko,ISko,Pko,Sko],[Fko,IPko,ISko,Sko],[Fko,IPko,Pko],[Fko,IPko,Pko,Sko],[Fko,IPko,Sko],[Fko,ISko],[Fko,ISko,Pko],[Fko,ISko,Pko,Sko],[Fko,ISko,Sko],[Fko,Pko],[Fko,Pko,Sko],[Fko,Sko],[CIko],[CIko,IPko],[CIko,IPko,ISko],[CIko,IPko,ISko,Pko],[CIko,IPko,ISko,Pko,Sko],[CIko,IPko,ISko,Sko],[CIko,IPko,Pko],[CIko,IPko,Pko,Sko],[CIko,IPko,Sko],[CIko,ISko],[CIko,ISko,Pko],[CIko,ISko,Pko,Sko],[CIko,ISko,Sko],[CIko,Pko],[CIko,Pko,Sko],[CIko,Sko],[IPko],[IPko,ISko],[IPko,ISko,Pko],[IPko,ISko,Pko,Sko],[IPko,ISko,Sko],[IPko,Pko],[IPko,Pko,Sko],[IPko,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko],[CIk2],[CIk3],[CIk4]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3])
    )),
    'update_circuit/6/2/$disj/4'(V,K,Fk,Fko,I),
    true((
        mshare([[GsOut],[GsOut,CIko],[GsOut,CIko,IPko],[GsOut,CIko,IPko,ISko],[GsOut,CIko,IPko,ISko,Pko],[GsOut,CIko,IPko,ISko,Pko,Sko],[GsOut,CIko,IPko,ISko,Sko],[GsOut,CIko,IPko,Pko],[GsOut,CIko,IPko,Pko,Sko],[GsOut,CIko,IPko,Sko],[GsOut,CIko,ISko],[GsOut,CIko,ISko,Pko],[GsOut,CIko,ISko,Pko,Sko],[GsOut,CIko,ISko,Sko],[GsOut,CIko,Pko],[GsOut,CIko,Pko,Sko],[GsOut,CIko,Sko],[GsOut,IPko],[GsOut,IPko,ISko],[GsOut,IPko,ISko,Pko],[GsOut,IPko,ISko,Pko,Sko],[GsOut,IPko,ISko,Sko],[GsOut,IPko,Pko],[GsOut,IPko,Pko,Sko],[GsOut,IPko,Sko],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[CIko],[CIko,IPko],[CIko,IPko,ISko],[CIko,IPko,ISko,Pko],[CIko,IPko,ISko,Pko,Sko],[CIko,IPko,ISko,Sko],[CIko,IPko,Pko],[CIko,IPko,Pko,Sko],[CIko,IPko,Sko],[CIko,ISko],[CIko,ISko,Pko],[CIko,ISko,Pko,Sko],[CIko,ISko,Sko],[CIko,Pko],[CIko,Pko,Sko],[CIko,Sko],[IPko],[IPko,ISko],[IPko,ISko,Pko],[IPko,ISko,Pko,Sko],[IPko,ISko,Sko],[IPko,Pko],[IPko,Pko,Sko],[IPko,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko],[CIk2],[CIk3],[CIk4]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3])
    )),
    'update_circuit/6/2/$disj/5'(K,CIk,I,Pi,SjJ,CIk2),
    true((
        mshare([[GsOut],[GsOut,CIko],[GsOut,CIko,IPko],[GsOut,CIko,IPko,ISko],[GsOut,CIko,IPko,ISko,Pko],[GsOut,CIko,IPko,ISko,Pko,Sko],[GsOut,CIko,IPko,ISko,Sko],[GsOut,CIko,IPko,Pko],[GsOut,CIko,IPko,Pko,Sko],[GsOut,CIko,IPko,Sko],[GsOut,CIko,ISko],[GsOut,CIko,ISko,Pko],[GsOut,CIko,ISko,Pko,Sko],[GsOut,CIko,ISko,Sko],[GsOut,CIko,Pko],[GsOut,CIko,Pko,Sko],[GsOut,CIko,Sko],[GsOut,IPko],[GsOut,IPko,ISko],[GsOut,IPko,ISko,Pko],[GsOut,IPko,ISko,Pko,Sko],[GsOut,IPko,ISko,Sko],[GsOut,IPko,Pko],[GsOut,IPko,Pko,Sko],[GsOut,IPko,Sko],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[CIko],[CIko,IPko],[CIko,IPko,ISko],[CIko,IPko,ISko,Pko],[CIko,IPko,ISko,Pko,Sko],[CIko,IPko,ISko,Sko],[CIko,IPko,Pko],[CIko,IPko,Pko,Sko],[CIko,IPko,Sko],[CIko,ISko],[CIko,ISko,Pko],[CIko,ISko,Pko,Sko],[CIko,ISko,Sko],[CIko,Pko],[CIko,Pko,Sko],[CIko,Sko],[IPko],[IPko,ISko],[IPko,ISko,Pko],[IPko,ISko,Pko,Sko],[IPko,ISko,Sko],[IPko,Pko],[IPko,Pko,Sko],[IPko,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko],[CIk3],[CIk4]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2])
    )),
    'update_circuit/6/2/$disj/6'(V,Fk,CIk,I,CIk2,CIk3),
    true((
        mshare([[GsOut],[GsOut,CIko],[GsOut,CIko,IPko],[GsOut,CIko,IPko,ISko],[GsOut,CIko,IPko,ISko,Pko],[GsOut,CIko,IPko,ISko,Pko,Sko],[GsOut,CIko,IPko,ISko,Sko],[GsOut,CIko,IPko,Pko],[GsOut,CIko,IPko,Pko,Sko],[GsOut,CIko,IPko,Sko],[GsOut,CIko,ISko],[GsOut,CIko,ISko,Pko],[GsOut,CIko,ISko,Pko,Sko],[GsOut,CIko,ISko,Sko],[GsOut,CIko,Pko],[GsOut,CIko,Pko,Sko],[GsOut,CIko,Sko],[GsOut,IPko],[GsOut,IPko,ISko],[GsOut,IPko,ISko,Pko],[GsOut,IPko,ISko,Pko,Sko],[GsOut,IPko,ISko,Sko],[GsOut,IPko,Pko],[GsOut,IPko,Pko,Sko],[GsOut,IPko,Sko],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[CIko],[CIko,IPko],[CIko,IPko,ISko],[CIko,IPko,ISko,Pko],[CIko,IPko,ISko,Pko,Sko],[CIko,IPko,ISko,Sko],[CIko,IPko,Pko],[CIko,IPko,Pko,Sko],[CIko,IPko,Sko],[CIko,ISko],[CIko,ISko,Pko],[CIko,ISko,Pko,Sko],[CIko,ISko,Sko],[CIko,Pko],[CIko,Pko,Sko],[CIko,Sko],[IPko],[IPko,ISko],[IPko,ISko,Pko],[IPko,ISko,Pko,Sko],[IPko,ISko,Sko],[IPko,Pko],[IPko,Pko,Sko],[IPko,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko],[CIk4]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3])
    )),
    'update_circuit/6/2/$disj/7'(V,Gs,K,I,CIk3,CIk4),
    true((
        mshare([[GsOut],[GsOut,CIko],[GsOut,CIko,IPko],[GsOut,CIko,IPko,ISko],[GsOut,CIko,IPko,ISko,Pko],[GsOut,CIko,IPko,ISko,Pko,Sko],[GsOut,CIko,IPko,ISko,Sko],[GsOut,CIko,IPko,Pko],[GsOut,CIko,IPko,Pko,Sko],[GsOut,CIko,IPko,Sko],[GsOut,CIko,ISko],[GsOut,CIko,ISko,Pko],[GsOut,CIko,ISko,Pko,Sko],[GsOut,CIko,ISko,Sko],[GsOut,CIko,Pko],[GsOut,CIko,Pko,Sko],[GsOut,CIko,Sko],[GsOut,IPko],[GsOut,IPko,ISko],[GsOut,IPko,ISko,Pko],[GsOut,IPko,ISko,Pko,Sko],[GsOut,IPko,ISko,Sko],[GsOut,IPko,Pko],[GsOut,IPko,Pko,Sko],[GsOut,IPko,Sko],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[CIko],[CIko,IPko],[CIko,IPko,ISko],[CIko,IPko,ISko,Pko],[CIko,IPko,ISko,Pko,Sko],[CIko,IPko,ISko,Sko],[CIko,IPko,Pko],[CIko,IPko,Pko,Sko],[CIko,IPko,Sko],[CIko,ISko],[CIko,ISko,Pko],[CIko,ISko,Pko,Sko],[CIko,ISko,Sko],[CIko,Pko],[CIko,Pko,Sko],[CIko,Sko],[IPko],[IPko,ISko],[IPko,ISko,Pko],[IPko,ISko,Pko,Sko],[IPko,ISko,Sko],[IPko,Pko],[IPko,Pko,Sko],[IPko,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4])
    )),
    'update_circuit/6/2/$disj/8'(K,CIko,I,J,CIk4),
    true((
        mshare([[GsOut],[GsOut,IPko],[GsOut,IPko,ISko],[GsOut,IPko,ISko,Pko],[GsOut,IPko,ISko,Pko,Sko],[GsOut,IPko,ISko,Sko],[GsOut,IPko,Pko],[GsOut,IPko,Pko,Sko],[GsOut,IPko,Sko],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[IPko],[IPko,ISko],[IPko,ISko,Pko],[IPko,ISko,Pko,Sko],[IPko,ISko,Sko],[IPko,Pko],[IPko,Pko,Sko],[IPko,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,CIko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4])
    )),
    'update_circuit/6/2/$disj/9'(K,IPk,IPko,I,J),
    true((
        mshare([[GsOut],[GsOut,ISko],[GsOut,ISko,Pko],[GsOut,ISko,Pko,Sko],[GsOut,ISko,Sko],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[ISko],[ISko,Pko],[ISko,Pko,Sko],[ISko,Sko],[Pko],[Pko,Sko],[Sko]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,CIko,IPko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4])
    )),
    'update_circuit/6/2/$disj/10'(K,ISk,ISko,I,J),
    true((
        mshare([[GsOut],[GsOut,Pko],[GsOut,Pko,Sko],[GsOut,Sko],[Pko],[Pko,Sko],[Sko]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,CIko,IPko,ISko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4])
    )),
    'update_circuit/6/2/$disj/11'(K,Pk,Pko,PiI,SjJ),
    true((
        mshare([[GsOut],[GsOut,Sko],[Sko]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,CIko,IPko,ISko,Pko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4])
    )),
    'update_circuit/6/2/$disj/12'(K,Sk,Sko,PiI,SjJ),
    true((
        mshare([[GsOut]]),
        ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,Tko,Fko,CIko,IPko,ISko,Pko,Sko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4])
    )),
    update_circuit(GsIn,Gi,Gj,V,Gs,GsOut),
    true(ground([Gi,Gj,V,Gs,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,GsOut,Tko,Fko,CIko,IPko,ISko,Pko,Sko,I,_1,Fi,_2,IPi,ISi,Pi,_3,J,_4,Fj,_5,_6,_7,_8,Sj,PiI,SjJ,Tk2,Tk3,CIk2,CIk3,CIk4])).

:- true pred 'update_circuit/6/2/$disj/1'(K,Tk,Fi,J,Tk2)
   : ( mshare([[Tk2]]),
       ground([K,Tk,Fi,J]) )
   => ground([K,Tk,Fi,J,Tk2]).

'update_circuit/6/2/$disj/1'(K,Tk,Fi,J,Tk2) :-
    true((
        mshare([[Tk2]]),
        ground([K,Tk,Fi,J])
    )),
    K=J,
    !,
    true((
        mshare([[Tk2]]),
        ground([K,Tk,Fi,J])
    )),
    set_union(Tk,Fi,Tk2),
    true(ground([K,Tk,Fi,J,Tk2])).
'update_circuit/6/2/$disj/1'(K,Tk,Fi,J,Tk2) :-
    true((
        mshare([[Tk2]]),
        ground([K,Tk,Fi,J])
    )),
    Tk2=Tk,
    true(ground([K,Tk,Fi,J,Tk2])).

:- true pred 'update_circuit/6/2/$disj/2'(K,I,Fj,Tk2,Tk3)
   : ( mshare([[Tk3]]),
       ground([K,I,Fj,Tk2]) )
   => ground([K,I,Fj,Tk2,Tk3]).

'update_circuit/6/2/$disj/2'(K,I,Fj,Tk2,Tk3) :-
    true((
        mshare([[Tk3]]),
        ground([K,I,Fj,Tk2])
    )),
    K=I,
    !,
    true((
        mshare([[Tk3]]),
        ground([K,I,Fj,Tk2])
    )),
    set_union(Tk2,Fj,Tk3),
    true(ground([K,I,Fj,Tk2,Tk3])).
'update_circuit/6/2/$disj/2'(K,I,Fj,Tk2,Tk3) :-
    true((
        mshare([[Tk3]]),
        ground([K,I,Fj,Tk2])
    )),
    Tk3=Tk2,
    true(ground([K,I,Fj,Tk2,Tk3])).

:- true pred 'update_circuit/6/2/$disj/3'(V,K,Tko,IPi,ISi,Tk3)
   : ( mshare([[Tko]]),
       ground([V,K,IPi,ISi,Tk3]) )
   => ground([V,K,Tko,IPi,ISi,Tk3]).

'update_circuit/6/2/$disj/3'(V,K,Tko,IPi,ISi,Tk3) :-
    true((
        mshare([[Tko]]),
        ground([V,K,IPi,ISi,Tk3])
    )),
    'update_circuit/6/2/$disj/3/6/1/$disj/1'(K,IPi,ISi),
    !,
    true((
        mshare([[Tko]]),
        ground([V,K,IPi,ISi,Tk3])
    )),
    set_union(Tk3,[V],Tko),
    true(ground([V,K,Tko,IPi,ISi,Tk3])).
'update_circuit/6/2/$disj/3'(V,K,Tko,IPi,ISi,Tk3) :-
    true((
        mshare([[Tko]]),
        ground([V,K,IPi,ISi,Tk3])
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
       ground([V,K,Fk,I]) )
   => ground([V,K,Fk,Fko,I]).

'update_circuit/6/2/$disj/4'(V,K,Fk,Fko,I) :-
    true((
        mshare([[Fko]]),
        ground([V,K,Fk,I])
    )),
    K=I,
    !,
    true((
        mshare([[Fko]]),
        ground([V,K,Fk,I])
    )),
    set_union(Fk,[V],Fko),
    true(ground([V,K,Fk,Fko,I])).
'update_circuit/6/2/$disj/4'(V,K,Fk,Fko,I) :-
    true((
        mshare([[Fko]]),
        ground([V,K,Fk,I])
    )),
    Fko=Fk,
    true(ground([V,K,Fk,Fko,I])).

:- true pred 'update_circuit/6/2/$disj/5'(K,CIk,I,Pi,SjJ,CIk2)
   : ( mshare([[CIk2]]),
       ground([K,CIk,I,Pi,SjJ]) )
   => ground([K,CIk,I,Pi,SjJ,CIk2]).

'update_circuit/6/2/$disj/5'(K,CIk,I,Pi,SjJ,CIk2) :-
    true((
        mshare([[CIk2]]),
        ground([K,CIk,I,Pi,SjJ])
    )),
    'update_circuit/6/2/$disj/5/6/1/$disj/1'(K,I,Pi),
    !,
    true((
        mshare([[CIk2]]),
        ground([K,CIk,I,Pi,SjJ])
    )),
    set_difference(CIk,SjJ,CIk2),
    true(ground([K,CIk,I,Pi,SjJ,CIk2])).
'update_circuit/6/2/$disj/5'(K,CIk,I,Pi,SjJ,CIk2) :-
    true((
        mshare([[CIk2]]),
        ground([K,CIk,I,Pi,SjJ])
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
       ground([V,Fk,CIk,I,CIk2]) )
   => ground([V,Fk,CIk,I,CIk2,CIk3]).

'update_circuit/6/2/$disj/6'(V,Fk,CIk,I,CIk2,CIk3) :-
    true((
        mshare([[CIk3]]),
        ground([V,Fk,CIk,I,CIk2])
    )),
    set_member(I,CIk),
    true((
        mshare([[CIk3]]),
        ground([V,Fk,CIk,I,CIk2])
    )),
    set_member(V,Fk),
    !,
    true((
        mshare([[CIk3]]),
        ground([V,Fk,CIk,I,CIk2])
    )),
    set_difference(CIk2,[I],CIk3),
    true(ground([V,Fk,CIk,I,CIk2,CIk3])).
'update_circuit/6/2/$disj/6'(V,Fk,CIk,I,CIk2,CIk3) :-
    true((
        mshare([[CIk3]]),
        ground([V,Fk,CIk,I,CIk2])
    )),
    CIk3=CIk2,
    true(ground([V,Fk,CIk,I,CIk2,CIk3])).

:- true pred 'update_circuit/6/2/$disj/7'(V,Gs,K,I,CIk3,CIk4)
   : ( mshare([[CIk4]]),
       ground([V,Gs,K,I,CIk3]) )
   => ground([V,Gs,K,I,CIk3,CIk4]).

'update_circuit/6/2/$disj/7'(V,Gs,K,I,CIk3,CIk4) :-
    true((
        mshare([[CIk4]]),
        ground([V,Gs,K,I,CIk3])
    )),
    K=I,
    !,
    true((
        mshare([[CIk4]]),
        ground([V,Gs,K,I,CIk3])
    )),
    exclude_if_vector_in_false_set(CIk3,Gs,V,CIk4),
    true(ground([V,Gs,K,I,CIk3,CIk4])).
'update_circuit/6/2/$disj/7'(V,Gs,K,I,CIk3,CIk4) :-
    true((
        mshare([[CIk4]]),
        ground([V,Gs,K,I,CIk3])
    )),
    CIk4=CIk3,
    true(ground([V,Gs,K,I,CIk3,CIk4])).

:- true pred 'update_circuit/6/2/$disj/8'(K,CIko,I,J,CIk4)
   : ( mshare([[CIko]]),
       ground([K,I,J,CIk4]) )
   => ground([K,CIko,I,J,CIk4]).

'update_circuit/6/2/$disj/8'(K,CIko,I,J,CIk4) :-
    true((
        mshare([[CIko]]),
        ground([K,I,J,CIk4])
    )),
    K=J,
    !,
    true((
        mshare([[CIko]]),
        ground([K,I,J,CIk4])
    )),
    set_difference(CIk4,[I],CIko),
    true(ground([K,CIko,I,J,CIk4])).
'update_circuit/6/2/$disj/8'(K,CIko,I,J,CIk4) :-
    true((
        mshare([[CIko]]),
        ground([K,I,J,CIk4])
    )),
    CIko=CIk4,
    true(ground([K,CIko,I,J,CIk4])).

:- true pred 'update_circuit/6/2/$disj/9'(K,IPk,IPko,I,J)
   : ( mshare([[IPko]]),
       ground([K,IPk,I,J]) )
   => ground([K,IPk,IPko,I,J]).

'update_circuit/6/2/$disj/9'(K,IPk,IPko,I,J) :-
    true((
        mshare([[IPko]]),
        ground([K,IPk,I,J])
    )),
    K=J,
    !,
    true((
        mshare([[IPko]]),
        ground([K,IPk,I,J])
    )),
    set_union(IPk,[I],IPko),
    true(ground([K,IPk,IPko,I,J])).
'update_circuit/6/2/$disj/9'(K,IPk,IPko,I,J) :-
    true((
        mshare([[IPko]]),
        ground([K,IPk,I,J])
    )),
    IPko=IPk,
    true(ground([K,IPk,IPko,I,J])).

:- true pred 'update_circuit/6/2/$disj/10'(K,ISk,ISko,I,J)
   : ( mshare([[ISko]]),
       ground([K,ISk,I,J]) )
   => ground([K,ISk,ISko,I,J]).

'update_circuit/6/2/$disj/10'(K,ISk,ISko,I,J) :-
    true((
        mshare([[ISko]]),
        ground([K,ISk,I,J])
    )),
    K=I,
    !,
    true((
        mshare([[ISko]]),
        ground([K,ISk,I,J])
    )),
    set_union(ISk,[J],ISko),
    true(ground([K,ISk,ISko,I,J])).
'update_circuit/6/2/$disj/10'(K,ISk,ISko,I,J) :-
    true((
        mshare([[ISko]]),
        ground([K,ISk,I,J])
    )),
    ISko=ISk,
    true(ground([K,ISk,ISko,I,J])).

:- true pred 'update_circuit/6/2/$disj/11'(K,Pk,Pko,PiI,SjJ)
   : ( mshare([[Pko]]),
       ground([K,Pk,PiI,SjJ]) )
   => ground([K,Pk,Pko,PiI,SjJ]).

'update_circuit/6/2/$disj/11'(K,Pk,Pko,PiI,SjJ) :-
    true((
        mshare([[Pko]]),
        ground([K,Pk,PiI,SjJ])
    )),
    set_member(K,SjJ),
    !,
    true((
        mshare([[Pko]]),
        ground([K,Pk,PiI,SjJ])
    )),
    set_union(Pk,PiI,Pko),
    true(ground([K,Pk,Pko,PiI,SjJ])).
'update_circuit/6/2/$disj/11'(K,Pk,Pko,PiI,SjJ) :-
    true((
        mshare([[Pko]]),
        ground([K,Pk,PiI,SjJ])
    )),
    Pko=Pk,
    true(ground([K,Pk,Pko,PiI,SjJ])).

:- true pred 'update_circuit/6/2/$disj/12'(K,Sk,Sko,PiI,SjJ)
   : ( mshare([[Sko]]),
       ground([K,Sk,PiI,SjJ]) )
   => ground([K,Sk,Sko,PiI,SjJ]).

'update_circuit/6/2/$disj/12'(K,Sk,Sko,PiI,SjJ) :-
    true((
        mshare([[Sko]]),
        ground([K,Sk,PiI,SjJ])
    )),
    set_member(K,PiI),
    !,
    true((
        mshare([[Sko]]),
        ground([K,Sk,PiI,SjJ])
    )),
    set_union(Sk,SjJ,Sko),
    true(ground([K,Sk,Sko,PiI,SjJ])).
'update_circuit/6/2/$disj/12'(K,Sk,Sko,PiI,SjJ) :-
    true((
        mshare([[Sko]]),
        ground([K,Sk,PiI,SjJ])
    )),
    Sko=Sk,
    true(ground([K,Sk,Sko,PiI,SjJ])).

:- true pred exclude_if_vector_in_false_set(_A,_1,_2,CIsOut)
   : ( mshare([[CIsOut]]),
       ground([_A,_1,_2]) )
   => ground([_A,_1,_2,CIsOut]).

exclude_if_vector_in_false_set([],_1,_2,[]).
exclude_if_vector_in_false_set([K|CIsIn],Gs,V,CIsOut) :-
    true((
        mshare([[CIsOut],[Gk],[Fk]]),
        ground([Gs,V,K,CIsIn])
    )),
    function(K,Gs,Gk),
    true((
        mshare([[CIsOut],[Fk]]),
        ground([Gs,V,K,CIsIn,Gk])
    )),
    false_set(Gk,Fk),
    true((
        mshare([[CIsOut]]),
        ground([Gs,V,K,CIsIn,Gk,Fk])
    )),
    set_member(V,Fk),
    !,
    true((
        mshare([[CIsOut]]),
        ground([Gs,V,K,CIsIn,Gk,Fk])
    )),
    exclude_if_vector_in_false_set(CIsIn,Gs,V,CIsOut),
    true(ground([Gs,V,CIsOut,K,CIsIn,Gk,Fk])).
exclude_if_vector_in_false_set([K|CIsIn],Gs,V,[K|CIsOut]) :-
    true((
        mshare([[CIsOut]]),
        ground([Gs,V,K,CIsIn])
    )),
    exclude_if_vector_in_false_set(CIsIn,Gs,V,CIsOut),
    true(ground([Gs,V,K,CIsIn,CIsOut])).

:- true pred add_necessary_functions(NumVars,NumGsIn,GsIn,NumGsOut,GsOut)
   : ( mshare([[NumGsOut],[GsOut]]),
       ground([NumVars,NumGsIn,GsIn]) )
   => ground([NumVars,NumGsIn,GsIn,NumGsOut,GsOut]).

add_necessary_functions(NumVars,NumGsIn,GsIn,NumGsOut,GsOut) :-
    true((
        mshare([[NumGsOut],[GsOut]]),
        ground([NumVars,NumGsIn,GsIn])
    )),
    add_necessary_functions(NumVars,NumVars,NumGsIn,GsIn,NumGsOut,GsOut),
    true(ground([NumVars,NumGsIn,GsIn,NumGsOut,GsOut])).

:- true pred add_necessary_functions(NumGs,_1,NumGsIn,Gs,NumGsOut,GsOut)
   : ( (NumGs=_1),
       mshare([[NumGsOut],[GsOut]]),
       ground([NumGs,NumGsIn,Gs]) )
   => ground([NumGs,NumGsIn,Gs,NumGsOut,GsOut]).

:- true pred add_necessary_functions(NumGs,_1,NumGsIn,Gs,NumGsOut,GsOut)
   : ( mshare([[NumGsOut],[GsOut]]),
       ground([NumGs,_1,NumGsIn,Gs]) )
   => ground([NumGs,_1,NumGsIn,Gs,NumGsOut,GsOut]).

add_necessary_functions(NumGs,_1,NumGs,Gs,NumGs,Gs) :-
    !,
    true(ground([NumGs,_1,Gs])).
add_necessary_functions(K,NumVars,NumGsIn,GsIn,NumGsOut,GsOut) :-
    true((
        mshare([[NumGsOut],[GsOut],[Gk],[V],[Fk],[Gs],[Gl],[Gk1],[Gs1],[NumGs1],[K1]]),
        ground([K,NumVars,NumGsIn,GsIn])
    )),
    function(K,GsIn,Gk),
    true((
        mshare([[NumGsOut],[GsOut],[V],[Fk],[Gs],[Gl],[Gk1],[Gs1],[NumGs1],[K1]]),
        ground([K,NumVars,NumGsIn,GsIn,Gk])
    )),
    function_type(NumVars,NumGsIn,GsIn,Gk,nf,V),
    !,
    true((
        mshare([[NumGsOut],[GsOut],[Fk],[Gs],[Gl],[Gk1],[Gs1],[NumGs1],[K1]]),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V])
    )),
    false_set(Gk,Fk),
    true((
        mshare([[NumGsOut],[GsOut],[Gs],[Gl],[Gk1],[Gs1],[NumGs1],[K1]]),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V,Fk])
    )),
    new_function_CIs(GsIn,function(NumGsIn,Fk,[V],[],[],[],[],[]),NumVars,Gs,Gl),
    true((
        mshare([[NumGsOut],[GsOut],[Gk1],[Gs1],[NumGs1],[K1]]),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V,Fk,Gs,Gl])
    )),
    function(K,Gs,Gk1),
    true((
        mshare([[NumGsOut],[GsOut],[Gs1],[NumGs1],[K1]]),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V,Fk,Gs,Gl,Gk1])
    )),
    update_circuit(Gs,Gl,Gk1,V,Gs,Gs1),
    true((
        mshare([[NumGsOut],[GsOut],[NumGs1],[K1]]),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V,Fk,Gs,Gl,Gk1,Gs1])
    )),
    NumGs1 is NumGsIn+1,
    true((
        mshare([[NumGsOut],[GsOut],[K1]]),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V,Fk,Gs,Gl,Gk1,Gs1,NumGs1])
    )),
    K1 is K+1,
    true((
        mshare([[NumGsOut],[GsOut]]),
        ground([K,NumVars,NumGsIn,GsIn,Gk,V,Fk,Gs,Gl,Gk1,Gs1,NumGs1,K1])
    )),
    add_necessary_functions(K1,NumVars,NumGs1,Gs1,NumGsOut,GsOut),
    true(ground([K,NumVars,NumGsIn,GsIn,NumGsOut,GsOut,Gk,V,Fk,Gs,Gl,Gk1,Gs1,NumGs1,K1])).
add_necessary_functions(K,NumVars,NumGsIn,GsIn,NumGsOut,GsOut) :-
    true((
        mshare([[NumGsOut],[GsOut],[K1]]),
        ground([K,NumVars,NumGsIn,GsIn])
    )),
    K1 is K+1,
    true((
        mshare([[NumGsOut],[GsOut]]),
        ground([K,NumVars,NumGsIn,GsIn,K1])
    )),
    add_necessary_functions(K1,NumVars,NumGsIn,GsIn,NumGsOut,GsOut),
    true(ground([K,NumVars,NumGsIn,GsIn,NumGsOut,GsOut,K1])).

:- true pred new_function_CIs(GsIn,_A,NumVars,_B,GlOut)
   : ( (_A=function(_C,_D,[_E],[],[],[],[],[])),
       mshare([[_B],[GlOut]]),
       ground([GsIn,NumVars,_C,_D,_E]) )
   => ground([GsIn,NumVars,_B,GlOut,_C,_D,_E]).

new_function_CIs(GsIn,function(L,Tl,Fl,_1,IPl,ISl,Pl,Sl),NumVars,[GlOut|GsOut],GlOut) :-
    true((
        mshare([[GlOut],[GlOut,GsOut],[GsOut],[CIlo]]),
        ground([GsIn,NumVars,L,Tl,Fl,_1,IPl,ISl,Pl,Sl])
    )),
    new_function_CIs(GsIn,L,Fl,NumVars,GsOut,[],CIlo),
    true((
        mshare([[GlOut]]),
        ground([GsIn,NumVars,L,Tl,Fl,_1,IPl,ISl,Pl,Sl,GsOut,CIlo])
    )),
    GlOut=function(L,Tl,Fl,CIlo,IPl,ISl,Pl,Sl),
    true(ground([GsIn,NumVars,GlOut,L,Tl,Fl,_1,IPl,ISl,Pl,Sl,GsOut,CIlo])).

:- true pred new_function_CIs(_A,_1,_2,_3,_B,CIl,CIlOut)
   : ( (CIl=[]),
       mshare([[_B],[CIlOut]]),
       ground([_A,_1,_2,_3]) )
   => ground([_A,_1,_2,_3,_B,CIlOut]).

:- true pred new_function_CIs(_A,_1,_2,_3,_B,CIl,CIlOut)
   : ( mshare([[_B],[CIlOut]]),
       ground([_A,_1,_2,_3,CIl]) )
   => ground([_A,_1,_2,_3,_B,CIl,CIlOut]).

:- true pred new_function_CIs(_A,_1,_2,_3,_B,CIl,CIlOut)
   : ( (CIl=[_C|_D]),
       mshare([[_B],[CIlOut]]),
       ground([_A,_1,_2,_3,_C,_D]) )
   => ground([_A,_1,_2,_3,_B,CIlOut,_C,_D]).

new_function_CIs([],_1,_2,_3,[],CIl,CIl).
new_function_CIs([function(K,Tk,Fk,CIk,IPk,ISk,Pk,Sk)|GsIn],L,Fl,NumVars,[function(K,Tk,Fk,CIko,IPk,ISk,Pk,Sk)|GsOut],CIlIn,CIlOut) :-
    true((
        mshare([[CIlOut],[GsOut],[GsOut,CIko],[CIko]]),
        ground([L,Fl,NumVars,CIlIn,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk])
    )),
    set_intersection(Fl,Fk,[]),
    !,
    true((
        mshare([[CIlOut],[GsOut],[GsOut,CIko],[CIko]]),
        ground([L,Fl,NumVars,CIlIn,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk])
    )),
    'new_function_CIs/7/2/$disj/1'(L,NumVars,K,CIk,CIko),
    true((
        mshare([[CIlOut],[GsOut]]),
        ground([L,Fl,NumVars,CIlIn,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,CIko])
    )),
    new_function_CIs(GsIn,L,Fl,NumVars,GsOut,[K|CIlIn],CIlOut),
    true(ground([L,Fl,NumVars,CIlIn,CIlOut,GsIn,K,Tk,Fk,CIk,IPk,ISk,Pk,Sk,GsOut,CIko])).
new_function_CIs([Gk|GsIn],L,Fl,NumVars,[Gk|GsOut],CIlIn,CIlOut) :-
    true((
        mshare([[CIlOut],[GsOut]]),
        ground([L,Fl,NumVars,CIlIn,Gk,GsIn])
    )),
    new_function_CIs(GsIn,L,Fl,NumVars,GsOut,CIlIn,CIlOut),
    true(ground([L,Fl,NumVars,CIlIn,CIlOut,Gk,GsIn,GsOut])).

:- true pred 'new_function_CIs/7/2/$disj/1'(L,NumVars,K,CIk,CIko)
   : ( mshare([[CIko]]),
       ground([L,NumVars,K,CIk]) )
   => ground([L,NumVars,K,CIk,CIko]).

'new_function_CIs/7/2/$disj/1'(L,NumVars,K,CIk,CIko) :-
    true((
        mshare([[CIko]]),
        ground([L,NumVars,K,CIk])
    )),
    K>=NumVars,
    !,
    true((
        mshare([[CIko]]),
        ground([L,NumVars,K,CIk])
    )),
    set_union(CIk,[L],CIko),
    true(ground([L,NumVars,K,CIk,CIko])).
'new_function_CIs/7/2/$disj/1'(L,NumVars,K,CIk,CIko) :-
    true((
        mshare([[CIko]]),
        ground([L,NumVars,K,CIk])
    )),
    CIko=CIk,
    true(ground([L,NumVars,K,CIk,CIko])).

:- true pred function_type(NumVars,NumGs,Gs,Gk,Type,Vector)
   : ( (Type=nf),
       mshare([[Vector]]),
       ground([NumVars,NumGs,Gs,Gk]) )
   => ground([NumVars,NumGs,Gs,Gk,Vector]).

function_type(NumVars,NumGs,Gs,Gk,Type,Vector) :-
    true((
        mshare([[Vector],[Tk],[_1],[_2]]),
        ground([NumVars,NumGs,Gs,Gk,Type])
    )),
    true_set(Gk,Tk),
    true((
        mshare([[Vector],[_1],[_2]]),
        ground([NumVars,NumGs,Gs,Gk,Type,Tk])
    )),
    select_vector(Tk,Gk,NumVars,NumGs,Gs,dummy,0,nf,999,_1,Vector,Type,_2),
    true(ground([NumVars,NumGs,Gs,Gk,Type,Vector,Tk,_1,_2])).

:- true pred test_bounds(_1,NumGs,_2)
   : ground([_1,NumGs,_2])
   => ground([_1,NumGs,_2]).

test_bounds(_1,NumGs,_2) :-
    true((
        mshare([[Bound]]),
        ground([_1,NumGs,_2])
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
       mshare([[_1],[_2]]) )
   => mshare([[_1],[_2]]).

:- true pred update_bounds(_1,NumGs,_2)
   : ( (NumGs=100),
       mshare([[_1],[_2]]) )
   => mshare([[_1],[_2]]).

update_bounds(_1,NumGs,_2) :-
    true((mshare([[_1],[_2]]),ground([NumGs]);ground([_1,NumGs,_2]))),
    set(bound,NumGs),
    true((mshare([[_1],[_2]]),ground([NumGs]);ground([_1,NumGs,_2]))).

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
        ground([N])
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
       mshare([[A]]) )
   => mshare([[A]]).

access(N,A) :-
    true((
        mshare([[A]]),
        ground([N])
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
       ground([I,_A]) )
   => ground([I,_A,Gi]).

function(I,[Gi|_1],Gi) :-
    true(ground([I,Gi,_1])),
    function_number(Gi,I),
    !,
    true(ground([I,Gi,_1])).
function(I,[_1|Gs],Gi) :-
    true((
        mshare([[Gi]]),
        ground([I,_1,Gs])
    )),
    function(I,Gs,Gi),
    true(ground([I,Gi,_1,Gs])).

:- true pred function_number(_A,I)
   : ( mshare([[I]]),
       ground([_A]) )
   => ground([_A,I]).

:- true pred function_number(_A,I)
   : ground([_A,I])
   => ground([_A,I]).

function_number(function(I,_1,_2,_3,_4,_5,_6,_7),I).

:- true pred true_set(_A,T)
   : ( mshare([[T]]),
       ground([_A]) )
   => ground([_A,T]).

true_set(function(_1,T,_2,_3,_4,_5,_6,_7),T).

:- true pred false_set(_A,F)
   : ( mshare([[F]]),
       ground([_A]) )
   => ground([_A,F]).

false_set(function(_1,_2,F,_3,_4,_5,_6,_7),F).

:- true pred conceivable_inputs(_A,CI)
   : ( mshare([[CI]]),
       ground([_A]) )
   => ground([_A,CI]).

conceivable_inputs(function(_1,_2,_3,CI,_4,_5,_6,_7),CI).

:- true pred immediate_predecessors(_A,IP)
   : ( mshare([[IP]]),
       ground([_A]) )
   => ground([_A,IP]).

immediate_predecessors(function(_1,_2,_3,_4,IP,_5,_6,_7),IP).

immediate_successors(function(_1,_2,_3,_4,_5,IS,_6,_7),IS).

predecessors(function(_1,_2,_3,_4,_5,_6,P,_7),P).

successors(function(_1,_2,_3,_4,_5,_6,_7,S),S).

:- true pred set_union(_A,_B,_C)
   : ( (_A=[_D]),
       mshare([[_C]]),
       ground([_B,_D]) )
   => ground([_B,_C,_D]).

:- true pred set_union(_A,_B,_C)
   : ( mshare([[_C]]),
       ground([_A,_B]) )
   => ground([_A,_B,_C]).

:- true pred set_union(_A,_B,_C)
   : ( (_B=[_D]),
       mshare([[_C]]),
       ground([_A,_D]) )
   => ground([_A,_C,_D]).

:- true pred set_union(_A,_B,_C)
   : ( (_A=[_D|_E]),
       mshare([[_C]]),
       ground([_B,_D,_E]) )
   => ground([_B,_C,_D,_E]).

:- true pred set_union(_A,_B,_C)
   : ( (_B=[_D|_E]),
       mshare([[_C]]),
       ground([_A,_D,_E]) )
   => ground([_A,_C,_D,_E]).

set_union([],[],[]).
set_union([],[X|L2],[X|L2]).
set_union([X|L1],[],[X|L1]).
set_union([X|L1],[X|L2],[X|L3]) :-
    true((
        mshare([[L3]]),
        ground([X,L1,L2])
    )),
    set_union(L1,L2,L3),
    true(ground([X,L1,L2,L3])).
set_union([X|L1],[Y|L2],[X|L3]) :-
    true((
        mshare([[L3]]),
        ground([X,L1,Y,L2])
    )),
    X<Y,
    true((
        mshare([[L3]]),
        ground([X,L1,Y,L2])
    )),
    set_union(L1,[Y|L2],L3),
    true(ground([X,L1,Y,L2,L3])).
set_union([X|L1],[Y|L2],[Y|L3]) :-
    true((
        mshare([[L3]]),
        ground([X,L1,Y,L2])
    )),
    X>Y,
    true((
        mshare([[L3]]),
        ground([X,L1,Y,L2])
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
       ground([_A,_C]) )
   => ground([_A,L3,_C]).

:- true pred set_difference(_A,_B,L3)
   : ( (_A=[_C|_D]),
       mshare([[L3]]),
       ground([_B,_C,_D]) )
   => ground([_B,L3,_C,_D]).

:- true pred set_difference(_A,_B,L3)
   : ( (_B=[_C|_D]),
       mshare([[L3]]),
       ground([_A,_C,_D]) )
   => ground([_A,L3,_C,_D]).

:- true pred set_difference(_A,_B,L3)
   : ( mshare([[L3]]),
       ground([_A,_B]) )
   => ground([_A,_B,L3]).

set_difference([],[],[]).
set_difference([],[_1|_2],[]).
set_difference([X|L1],[],[X|L1]).
set_difference([X|L1],[X|L2],L3) :-
    true((
        mshare([[L3]]),
        ground([X,L1,L2])
    )),
    set_difference(L1,L2,L3),
    true(ground([L3,X,L1,L2])).
set_difference([X|L1],[Y|L2],[X|L3]) :-
    true((
        mshare([[L3]]),
        ground([X,L1,Y,L2])
    )),
    X<Y,
    true((
        mshare([[L3]]),
        ground([X,L1,Y,L2])
    )),
    set_difference(L1,[Y|L2],L3),
    true(ground([X,L1,Y,L2,L3])).
set_difference([X|L1],[Y|L2],L3) :-
    true((
        mshare([[L3]]),
        ground([X,L1,Y,L2])
    )),
    X>Y,
    true((
        mshare([[L3]]),
        ground([X,L1,Y,L2])
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

