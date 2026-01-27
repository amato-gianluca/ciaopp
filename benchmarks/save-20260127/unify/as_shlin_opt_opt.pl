:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(unify,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true((
        mshare([[_X]]),
        linear(_X)
    )),
    main(_X),
    true(ground([_X])).

:- true pred main(Size)
   : ( mshare([[Size]]),
       linear(Size) )
   => ground([Size]).

main(Size) :-
    true((
        mshare([[Size],[X],[Code],[_Y]]),
        linear(Size),
        linear(X),
        linear(Code),
        linear(_Y)
    )),
    u(X,[1,_Y],[X],Code),
    true((
        mshare([[Size],[X,Code],[X,Code,_Y],[Code],[Code,_Y],[_Y]]),
        linear(Size)
    )),
    unify:size(Code,0,Size),
    true((
        mshare([[X,Code],[X,Code,_Y],[Code],[Code,_Y],[_Y]]),
        ground([Size])
    )).

:- true pred u(X,T,In,Code)
   : ( (T=[1,_A]), (In=[X]),
       mshare([[X],[Code],[_A]]),
       linear(X), linear(Code), linear(_A) )
   => mshare([[X,Code],[X,Code,_A],[Code],[Code,_A],[_A]]).

u(X,T,In,Code) :-
    true((
        mshare([[X,In],[T],[Code],[_1]]),
        linear(X),
        linear(T),
        linear(In),
        linear(Code),
        linear(_1)
    )),
    unify(X,T,In,_1,Code,[]),
    true(mshare([[X,T,In,Code,_1],[X,In,Code,_1],[T],[T,Code],[T,Code,_1],[T,_1],[Code],[Code,_1]])).

:- true pred unify(X,T,In,Out,_1,_2)
   : ( (_2=[]),
       mshare([[X,In],[T],[Out],[_1]]),
       linear(X), linear(T), linear(In), linear(Out), linear(_1) )
   => mshare([[X,T,In,Out,_1],[X,In,Out,_1],[T],[T,Out],[T,Out,_1],[T,_1],[Out,_1],[_1]]).

unify(X,T,In,Out,_1,_2) :-
    true((
        mshare([[X,In],[T],[Out],[_1]]),
        ground([_2]),
        linear(X),
        linear(T),
        linear(In),
        linear(Out),
        linear(_1)
    )),
    'unify/6/1/$disj/1'(X,In),
    !,
    true((
        mshare([[X,In],[T],[Out],[_1]]),
        ground([_2]),
        linear(X),
        linear(T),
        linear(In),
        linear(Out),
        linear(_1)
    )),
    uninit(X,T,In,Out,_1,_2),
    true((
        mshare([[X,T,In,Out,_1],[X,In,Out,_1],[T],[T,Out],[T,Out,_1],[T,_1],[_1]]),
        ground([_2])
    )).
unify(X,T,In,Out,_1,_2) :-
    true((
        mshare([[X,In],[T],[Out],[_1],[_3]]),
        ground([_2]),
        linear(X),
        linear(T),
        linear(In),
        linear(Out),
        linear(_1),
        linear(_3)
    )),
    myin(X,In),
    !,
    true((
        mshare([[X,In],[T],[Out],[_1],[_3]]),
        ground([_2]),
        linear(X),
        linear(T),
        linear(In),
        linear(Out),
        linear(_1),
        linear(_3)
    )),
    init(X,T,In,Out,nonlast,_3,_1,_2),
    true((
        mshare([[X,T,In,Out,_1],[X,In,Out,_1],[T],[T,Out,_1],[T,_1],[Out,_1],[_1],[_1,_3],[_3]]),
        ground([_2])
    )).

:- true pred 'unify/6/1/$disj/1'(X,In)
   : ( mshare([[X,In]]),
       linear(X), linear(In) )
   => ( mshare([[X,In]]),
        linear(X), linear(In) ).

'unify/6/1/$disj/1'(X,In) :-
    true((
        mshare([[X,In]]),
        linear(X),
        linear(In)
    )),
    myin(X,In),
    !,
    true((
        mshare([[X,In]]),
        linear(X),
        linear(In)
    )),
    fail,
    true(fails(_)).
'unify/6/1/$disj/1'(X,In).

:- true pred uninit(X,T,In,Out,_1,_2)
   : ( mshare([[X,In],[T],[Out],[_1]]),
       ground([_2]), linear(X), linear(T), linear(In), linear(Out), linear(_1) )
   => ( mshare([[X,T,In,Out,_1],[X,In,Out,_1],[T],[T,Out],[T,Out,_1],[T,_1],[_1]]),
        ground([_2]) ).

uninit(X,T,In,Out,_1,_2) :-
    true((
        mshare([[X,In],[T],[Out],[_1],[_3],[Tag],[_4],[Mid],[_5]]),
        ground([_2]),
        linear(X),
        linear(T),
        linear(In),
        linear(Out),
        linear(_1),
        linear(_3),
        linear(Tag),
        linear(_4),
        linear(Mid),
        linear(_5)
    )),
    my_compound(T),
    !,
    true((
        mshare([[X,In],[T],[Out],[_1],[_3],[Tag],[_4],[Mid],[_5]]),
        ground([_2]),
        linear(X),
        linear(T),
        linear(In),
        linear(Out),
        linear(_1),
        linear(_3),
        linear(Tag),
        linear(_4),
        linear(Mid),
        linear(_5)
    )),
    'C'(_1,move(Tag^h,X),_3),
    true((
        mshare([[X,In,_1],[T],[Out],[_1,_3],[_1,Tag],[_4],[Mid],[_5]]),
        ground([_2]),
        linear(X),
        linear(T),
        linear(In),
        linear(Out),
        linear(_1),
        linear(_3),
        linear(Tag),
        linear(_4),
        linear(Mid),
        linear(_5)
    )),
    termtag(T,Tag),
    true((
        mshare([[X,In,_1],[T],[Out],[_1,_3],[_4],[Mid],[_5]]),
        ground([_2,Tag]),
        linear(X),
        linear(In),
        linear(Out),
        linear(_1),
        linear(_3),
        linear(_4),
        linear(Mid),
        linear(_5)
    )),
    unify_block(nonlast,T,_4,In,Mid,_5,_3,_2),
    true((
        mshare([[X,T,In,_1,_3,Mid],[X,T,In,_1,Mid],[X,In,_1,Mid],[T],[T,_1,_3],[T,_1,_3,Mid],[T,Mid],[Out],[_1,_3],[_1,_3,_5],[_5]]),
        ground([_2,Tag,_4]),
        linear(Out)
    )),
    incl(X,Mid,Out),
    true((
        mshare([[X,T,In,Out,_1,_3,Mid],[X,T,In,Out,_1,Mid],[X,In,Out,_1,Mid],[T],[T,Out,_1,_3,Mid],[T,Out,Mid],[T,_1,_3],[_1,_3],[_1,_3,_5],[_5]]),
        ground([_2,Tag,_4])
    )).
uninit(X,T,In,Out,_1,_2) :-
    true((
        mshare([[X,In],[T],[Out],[_1]]),
        ground([_2]),
        linear(X),
        linear(T),
        linear(In),
        linear(Out),
        linear(_1)
    )),
    atomic(T),
    !,
    true((
        mshare([[X,In],[Out],[_1]]),
        ground([T,_2]),
        linear(X),
        linear(In),
        linear(Out),
        linear(_1)
    )),
    'C'(_1,move(tatm^T,X),_2),
    true((
        mshare([[X,In,_1],[Out]]),
        ground([T,_2]),
        linear(X),
        linear(In),
        linear(Out),
        linear(_1)
    )),
    incl(X,In,Out),
    true((
        mshare([[X,In,Out,_1]]),
        ground([T,_2])
    )).
uninit(X,T,In,Out,_1,_2) :-
    true((
        mshare([[X,In],[T],[Out],[_1]]),
        ground([_2]),
        linear(X),
        linear(T),
        linear(In),
        linear(Out),
        linear(_1)
    )),
    var(T),
    !,
    true((
        mshare([[X,In],[T],[Out],[_1]]),
        ground([_2]),
        linear(X),
        linear(T),
        linear(In),
        linear(Out),
        linear(_1)
    )),
    unify_var(X,T,In,Out,_1,_2),
    true((
        mshare([[X,In,Out,_1],[T,Out,_1],[T,_1]]),
        ground([_2]),
        linear(T)
    )).

:- true pred init(X,T,In,Out,Last,LLbls,_1,_2)
   : ( mshare([[X],[X,In],[T],[T,In],[In],[Out],[LLbls],[_1],[_2]]),
       ground([Last]), linear(X), linear(Out), linear(LLbls), linear(_1), linear(_2) )
   => ( mshare([[X,T,In,Out,_1],[X,T,Out,_1],[X,In,Out,_1],[X,Out,_1],[X,_1],[T],[T,In,Out],[T,In,Out,_1],[T,Out,_1],[T,_1],[In,Out],[In,Out,_1],[Out,_1],[LLbls],[LLbls,_1],[_1],[_1,_2]]),
        ground([Last]), linear(_2) ).

:- true pred init(X,T,In,Out,Last,LLbls,_1,_2)
   : ( (Last=nonlast),
       mshare([[X,In],[T],[Out],[LLbls],[_1]]),
       ground([_2]), linear(X), linear(T), linear(In), linear(Out), linear(LLbls), linear(_1) )
   => ( mshare([[X,T,In,Out,_1],[X,In,Out,_1],[T],[T,Out,_1],[T,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([_2]) ).

:- true pred init(X,T,In,Out,Last,LLbls,_1,_2)
   : ( mshare([[X],[X,In],[T],[T,In],[In],[Out],[LLbls],[_1]]),
       ground([Last,_2]), linear(X), linear(Out), linear(_1) )
   => ( mshare([[X,T,In,Out,_1],[X,T,Out,_1],[X,In,Out,_1],[X,Out,_1],[X,_1],[T],[T,In,Out],[T,In,Out,_1],[T,Out,_1],[T,_1],[In,Out],[In,Out,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([Last,_2]) ).

init(X,T,In,Out,Last,LLbls,_1,_2) :-
    true((mshare([[X],[X,In],[T],[T,In],[In],[Out],[LLbls],[_1],[_2],[Tag],[_3],[Read],[Write]]),ground([Last]),linear(X),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(Tag),linear(_3),linear(Read),linear(Write);mshare([[X],[X,In],[T],[T,In],[In],[Out],[LLbls],[_1],[Tag],[_3],[Read],[Write]]),ground([Last,_2]),linear(X),linear(Out),linear(_1),linear(Tag),linear(_3),linear(Read),linear(Write);mshare([[X,In],[T],[Out],[LLbls],[_1],[Tag],[_3],[Read],[Write]]),ground([Last,_2]),linear(X),linear(T),linear(In),linear(Out),linear(LLbls),linear(_1),linear(Tag),linear(_3),linear(Read),linear(Write))),
    nonvar(T),
    !,
    true((mshare([[X],[X,In],[T],[T,In],[In],[Out],[LLbls],[_1],[_2],[Tag],[_3],[Read],[Write]]),ground([Last]),linear(X),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(Tag),linear(_3),linear(Read),linear(Write);mshare([[X],[X,In],[T],[T,In],[In],[Out],[LLbls],[_1],[Tag],[_3],[Read],[Write]]),ground([Last,_2]),linear(X),linear(Out),linear(_1),linear(Tag),linear(_3),linear(Read),linear(Write);mshare([[X,In],[T],[Out],[LLbls],[_1],[Tag],[_3],[Read],[Write]]),ground([Last,_2]),linear(X),linear(T),linear(In),linear(Out),linear(LLbls),linear(_1),linear(Tag),linear(_3),linear(Read),linear(Write))),
    termtag(T,Tag),
    true((mshare([[X],[X,In],[T],[T,In],[In],[Out],[LLbls],[_1],[_2],[_3],[Read],[Write]]),ground([Last,Tag]),linear(X),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(_3),linear(Read),linear(Write);mshare([[X],[X,In],[T],[T,In],[In],[Out],[LLbls],[_1],[_3],[Read],[Write]]),ground([Last,_2,Tag]),linear(X),linear(Out),linear(_1),linear(_3),linear(Read),linear(Write);mshare([[X,In],[T],[Out],[LLbls],[_1],[_3],[Read],[Write]]),ground([Last,_2,Tag]),linear(X),linear(In),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(Read),linear(Write))),
    'C'(_1,deref(X),_3),
    true((mshare([[X,In,_1],[X,_1],[T],[T,In],[In],[Out],[LLbls],[_1,_3],[_2],[Read],[Write]]),ground([Last,Tag]),linear(X),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(_3),linear(Read),linear(Write);mshare([[X,In,_1],[X,_1],[T],[T,In],[In],[Out],[LLbls],[_1,_3],[Read],[Write]]),ground([Last,_2,Tag]),linear(X),linear(Out),linear(_1),linear(_3),linear(Read),linear(Write);mshare([[X,In,_1],[T],[Out],[LLbls],[_1,_3],[Read],[Write]]),ground([Last,_2,Tag]),linear(X),linear(In),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(Read),linear(Write))),
    'C'(_3,switch(Tag,X,[trail(X)|Write],Read,fail),_2),
    true((mshare([[X,In,_1,_3],[X,_1,_3],[T],[T,In],[In],[Out],[LLbls],[_1,_2,_3],[_1,_3,Read],[_1,_3,Write]]),ground([Last,Tag]),linear(X),linear(Out),linear(LLbls),linear(_2),linear(Read),linear(Write);mshare([[X,In,_1,_3],[X,_1,_3],[T],[T,In],[In],[Out],[LLbls],[_1,_3,Read],[_1,_3,Write]]),ground([Last,_2,Tag]),linear(X),linear(Out),linear(Read),linear(Write);mshare([[X,In,_1,_3],[T],[Out],[LLbls],[_1,_3,Read],[_1,_3,Write]]),ground([Last,_2,Tag]),linear(X),linear(In),linear(Out),linear(LLbls),linear(Read),linear(Write))),
    unify_writemode(X,T,In,Last,LLbls,Write,[]),
    true((mshare([[X,T,In,_1,_3,Write],[X,In,_1,_3,Write],[X,_1,_3,Write],[T],[T,In],[T,In,_1,_3,Write],[T,_1,_3,Write],[In],[Out],[LLbls],[LLbls,_1,_3,Write],[_1,_2,_3],[_1,_3,Read],[_1,_3,Write]]),ground([Last,Tag]),linear(Out),linear(_2),linear(Read);mshare([[X,T,In,_1,_3,Write],[X,In,_1,_3,Write],[X,_1,_3,Write],[T],[T,In],[T,In,_1,_3,Write],[T,_1,_3,Write],[In],[Out],[LLbls],[LLbls,_1,_3,Write],[_1,_3,Read],[_1,_3,Write]]),ground([Last,_2,Tag]),linear(Out),linear(Read);mshare([[X,T,In,_1,_3,Write],[X,In,_1,_3,Write],[T],[T,_1,_3,Write],[Out],[LLbls],[LLbls,_1,_3,Write],[_1,_3,Read],[_1,_3,Write]]),ground([Last,_2,Tag]),linear(Out),linear(Read))),
    unify_readmode(X,T,In,Out,LLbls,Read,[]),
    true((mshare([[X,T,In,Out,_1,_3,Read,Write],[X,T,In,Out,_1,_3,Write],[X,T,Out,_1,_3,Read,Write],[X,In,Out,_1,_3,Read,Write],[X,In,Out,_1,_3,Write],[X,Out,_1,_3,Read,Write],[X,_1,_3,Read,Write],[X,_1,_3,Write],[T],[T,In,Out],[T,In,Out,_1,_3,Read],[T,In,Out,_1,_3,Read,Write],[T,In,Out,_1,_3,Write],[T,Out,_1,_3,Read],[T,Out,_1,_3,Read,Write],[T,_1,_3,Read],[T,_1,_3,Read,Write],[T,_1,_3,Write],[In,Out],[In,Out,_1,_3,Read],[Out,_1,_3,Read],[LLbls],[LLbls,_1,_3,Read],[LLbls,_1,_3,Read,Write],[LLbls,_1,_3,Write],[_1,_2,_3],[_1,_3,Read],[_1,_3,Write]]),ground([Last,Tag]),linear(_2);mshare([[X,T,In,Out,_1,_3,Read,Write],[X,T,In,Out,_1,_3,Write],[X,T,Out,_1,_3,Read,Write],[X,In,Out,_1,_3,Read,Write],[X,In,Out,_1,_3,Write],[X,Out,_1,_3,Read,Write],[X,_1,_3,Read,Write],[X,_1,_3,Write],[T],[T,In,Out],[T,In,Out,_1,_3,Read],[T,In,Out,_1,_3,Read,Write],[T,In,Out,_1,_3,Write],[T,Out,_1,_3,Read],[T,Out,_1,_3,Read,Write],[T,_1,_3,Read],[T,_1,_3,Read,Write],[T,_1,_3,Write],[In,Out],[In,Out,_1,_3,Read],[Out,_1,_3,Read],[LLbls],[LLbls,_1,_3,Read],[LLbls,_1,_3,Read,Write],[LLbls,_1,_3,Write],[_1,_3,Read],[_1,_3,Write]]),ground([Last,_2,Tag]);mshare([[X,T,In,Out,_1,_3,Read,Write],[X,T,In,Out,_1,_3,Write],[X,In,Out,_1,_3,Read,Write],[X,In,Out,_1,_3,Write],[T],[T,Out,_1,_3,Read],[T,Out,_1,_3,Read,Write],[T,_1,_3,Read],[T,_1,_3,Read,Write],[T,_1,_3,Write],[Out,_1,_3,Read],[LLbls],[LLbls,_1,_3,Read],[LLbls,_1,_3,Read,Write],[LLbls,_1,_3,Write],[_1,_3,Read],[_1,_3,Write]]),ground([Last,_2,Tag]))).
init(X,T,In,Out,_1,_2,_3,_4) :-
    true((mshare([[X],[X,In],[T],[T,In],[In],[Out],[_2],[_3]]),ground([_1,_4]),linear(X),linear(Out),linear(_3);mshare([[X],[X,In],[T],[T,In],[In],[Out],[_2],[_3],[_4]]),ground([_1]),linear(X),linear(Out),linear(_2),linear(_3),linear(_4);mshare([[X,In],[T],[Out],[_2],[_3]]),ground([_1,_4]),linear(X),linear(T),linear(In),linear(Out),linear(_2),linear(_3))),
    var(T),
    !,
    true((mshare([[X],[X,In],[T],[T,In],[In],[Out],[_2],[_3]]),ground([_1,_4]),linear(X),linear(T),linear(Out),linear(_3);mshare([[X],[X,In],[T],[T,In],[In],[Out],[_2],[_3],[_4]]),ground([_1]),linear(X),linear(T),linear(Out),linear(_2),linear(_3),linear(_4);mshare([[X,In],[T],[Out],[_2],[_3]]),ground([_1,_4]),linear(X),linear(T),linear(In),linear(Out),linear(_2),linear(_3))),
    unify_var(X,T,In,Out,_3,_4),
    true((mshare([[X,T,In,Out,_3],[X,T,Out,_3],[X,In,Out,_3],[X,Out,_3],[X,_3],[T,In,Out,_3],[T,Out,_3],[T,_3],[In,Out],[_2]]),ground([_1,_4]);mshare([[X,T,In,Out,_3],[X,T,Out,_3],[X,In,Out,_3],[X,Out,_3],[X,_3],[T,In,Out,_3],[T,Out,_3],[T,_3],[In,Out],[_2],[_3,_4]]),ground([_1]),linear(_2),linear(_4);mshare([[X,In,Out,_3],[T,Out,_3],[T,_3],[_2]]),ground([_1,_4]),linear(T),linear(_2))).

:- true pred unify_var(X,Y,In,Out,_1,_2)
   : ( mshare([[X],[X,In],[Y],[Y,In],[In],[Out],[_1],[_2]]),
       linear(X), linear(Y), linear(Out), linear(_1), linear(_2) )
   => ( mshare([[X,Y,In,Out,_1],[X,Y,Out,_1],[X,In,Out,_1],[X,Out,_1],[X,_1],[Y,In,Out,_1],[Y,Out,_1],[Y,_1],[In,Out],[_1,_2]]),
        linear(_2) ).

:- true pred unify_var(X,Y,In,Out,_1,_2)
   : ( mshare([[X],[X,In],[Y],[Y,In],[In],[Out],[_1]]),
       ground([_2]), linear(X), linear(Y), linear(Out), linear(_1) )
   => ( mshare([[X,Y,In,Out,_1],[X,Y,Out,_1],[X,In,Out,_1],[X,Out,_1],[X,_1],[Y,In,Out,_1],[Y,Out,_1],[Y,_1],[In,Out]]),
        ground([_2]) ).

:- true pred unify_var(X,Y,In,Out,_1,_2)
   : ( mshare([[X,In],[Y],[Out],[_1]]),
       ground([_2]), linear(X), linear(Y), linear(In), linear(Out), linear(_1) )
   => ( mshare([[X,In,Out,_1],[Y,Out,_1],[Y,_1]]),
        ground([_2]), linear(Y) ).

unify_var(X,Y,In,In,_1,_2) :-
    true((mshare([[X],[X,In],[Y],[Y,In],[In],[_1]]),ground([_2]),linear(X),linear(Y),linear(_1);mshare([[X],[X,In],[Y],[Y,In],[In],[_1],[_2]]),linear(X),linear(Y),linear(_1),linear(_2);mshare([[X,In],[Y],[_1]]),ground([_2]),linear(X),linear(Y),linear(In),linear(_1))),
    myin(X,In),
    true((mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[_1]]),ground([_2]),linear(X),linear(_1);mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[_1],[_2]]),linear(X),linear(_1),linear(_2);mshare([[X,In],[Y],[_1]]),ground([_2]),linear(X),linear(Y),linear(In),linear(_1))),
    myin(Y,In),
    !,
    true((mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[_1]]),ground([_2]),linear(_1);mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[_1],[_2]]),linear(_1),linear(_2);mshare([[X,In],[Y],[_1]]),ground([_2]),linear(X),linear(Y),linear(In),linear(_1))),
    'C'(_1,unify(X,Y,fail),_2),
    true((mshare([[X,Y,In,_1],[X,In,_1],[X,_1],[Y,In,_1],[Y,_1],[In]]),ground([_2]);mshare([[X,Y,In,_1],[X,In,_1],[X,_1],[Y,In,_1],[Y,_1],[In],[_1,_2]]),linear(_2);mshare([[X,In,_1],[Y,_1]]),ground([_2]),linear(X),linear(Y),linear(In),linear(_1))).
unify_var(X,Y,In,Out,_1,_2) :-
    true((mshare([[X],[X,In],[Y],[Y,In],[In],[Out],[_1]]),ground([_2]),linear(X),linear(Y),linear(Out),linear(_1);mshare([[X],[X,In],[Y],[Y,In],[In],[Out],[_1],[_2]]),linear(X),linear(Y),linear(Out),linear(_1),linear(_2);mshare([[X,In],[Y],[Out],[_1]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1))),
    myin(X,In),
    true((mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[Out],[_1]]),ground([_2]),linear(X),linear(Out),linear(_1);mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[Out],[_1],[_2]]),linear(X),linear(Out),linear(_1),linear(_2);mshare([[X,In],[Y],[Out],[_1]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1))),
    'unify_var/6/2/$disj/1'(Y,In),
    !,
    true((mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[Out],[_1]]),ground([_2]),linear(Out),linear(_1);mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[Out],[_1],[_2]]),linear(Out),linear(_1),linear(_2);mshare([[X,In],[Y],[Out],[_1]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1))),
    'C'(_1,move(X,Y),_2),
    true((mshare([[X,Y,In,_1],[X,In,_1],[X,_1],[Y,In,_1],[Y,_1],[In],[Out]]),ground([_2]),linear(Out);mshare([[X,Y,In,_1],[X,In,_1],[X,_1],[Y,In,_1],[Y,_1],[In],[Out],[_1,_2]]),linear(Out),linear(_2);mshare([[X,In,_1],[Y,_1],[Out]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1))),
    incl(Y,In,Out),
    true((mshare([[X,Y,In,Out,_1],[X,In,Out,_1],[X,_1],[Y,In,Out,_1],[Y,Out,_1],[Y,_1],[In,Out]]),ground([_2]);mshare([[X,Y,In,Out,_1],[X,In,Out,_1],[X,_1],[Y,In,Out,_1],[Y,Out,_1],[Y,_1],[In,Out],[_1,_2]]),linear(_2);mshare([[X,In,Out,_1],[Y,Out,_1],[Y,_1]]),ground([_2]),linear(Y),linear(Out))).
unify_var(X,Y,In,Out,_1,_2) :-
    true((mshare([[X],[X,In],[Y],[Y,In],[In],[Out],[_1]]),ground([_2]),linear(X),linear(Y),linear(Out),linear(_1);mshare([[X],[X,In],[Y],[Y,In],[In],[Out],[_1],[_2]]),linear(X),linear(Y),linear(Out),linear(_1),linear(_2);mshare([[X,In],[Y],[Out],[_1]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1))),
    'unify_var/6/3/$disj/1'(X,In),
    true((mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[Out],[_1]]),ground([_2]),linear(X),linear(Out),linear(_1);mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[Out],[_1],[_2]]),linear(X),linear(Out),linear(_1),linear(_2);mshare([[X,In],[Y],[Out],[_1]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1))),
    myin(Y,In),
    !,
    true((mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[Out],[_1]]),ground([_2]),linear(Out),linear(_1);mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[Out],[_1],[_2]]),linear(Out),linear(_1),linear(_2);mshare([[X,In],[Y],[Out],[_1]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1))),
    'C'(_1,move(Y,X),_2),
    true((mshare([[X,Y,In,_1],[X,In,_1],[X,_1],[Y,In,_1],[Y,_1],[In],[Out]]),ground([_2]),linear(Out);mshare([[X,Y,In,_1],[X,In,_1],[X,_1],[Y,In,_1],[Y,_1],[In],[Out],[_1,_2]]),linear(Out),linear(_2);mshare([[X,In,_1],[Y,_1],[Out]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1))),
    incl(X,In,Out),
    true((mshare([[X,Y,In,Out,_1],[X,In,Out,_1],[X,Out,_1],[X,_1],[Y,In,Out,_1],[Y,_1],[In,Out]]),ground([_2]);mshare([[X,Y,In,Out,_1],[X,In,Out,_1],[X,Out,_1],[X,_1],[Y,In,Out,_1],[Y,_1],[In,Out],[_1,_2]]),linear(_2);mshare([[X,In,Out,_1],[Y,_1]]),ground([_2]),linear(Y))).
unify_var(X,Y,In,Out,_1,_2) :-
    true((mshare([[X],[X,In],[Y],[Y,In],[In],[Out],[_1],[_2],[_3],[_4],[_5],[Mid]]),linear(X),linear(Y),linear(Out),linear(_1),linear(_2),linear(_3),linear(_4),linear(_5),linear(Mid);mshare([[X],[X,In],[Y],[Y,In],[In],[Out],[_1],[_3],[_4],[_5],[Mid]]),ground([_2]),linear(X),linear(Y),linear(Out),linear(_1),linear(_3),linear(_4),linear(_5),linear(Mid);mshare([[X,In],[Y],[Out],[_1],[_3],[_4],[_5],[Mid]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1),linear(_3),linear(_4),linear(_5),linear(Mid))),
    'unify_var/6/4/$disj/1'(X,In),
    true((mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[Out],[_1],[_2],[_3],[_4],[_5],[Mid]]),linear(X),linear(Out),linear(_1),linear(_2),linear(_3),linear(_4),linear(_5),linear(Mid);mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[Out],[_1],[_3],[_4],[_5],[Mid]]),ground([_2]),linear(X),linear(Out),linear(_1),linear(_3),linear(_4),linear(_5),linear(Mid);mshare([[X,In],[Y],[Out],[_1],[_3],[_4],[_5],[Mid]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1),linear(_3),linear(_4),linear(_5),linear(Mid))),
    'unify_var/6/4/$disj/2'(Y,In),
    !,
    true((mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[Out],[_1],[_2],[_3],[_4],[_5],[Mid]]),linear(Out),linear(_1),linear(_2),linear(_3),linear(_4),linear(_5),linear(Mid);mshare([[X],[X,Y,In],[X,In],[Y],[Y,In],[In],[Out],[_1],[_3],[_4],[_5],[Mid]]),ground([_2]),linear(Out),linear(_1),linear(_3),linear(_4),linear(_5),linear(Mid);mshare([[X,In],[Y],[Out],[_1],[_3],[_4],[_5],[Mid]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1),linear(_3),linear(_4),linear(_5),linear(Mid))),
    'C'(_1,move(tvar^h,X),_3),
    true((mshare([[X,Y,In,_1],[X,In,_1],[X,_1],[Y],[Y,In],[In],[Out],[_1,_3],[_2],[_4],[_5],[Mid]]),linear(Out),linear(_2),linear(_3),linear(_4),linear(_5),linear(Mid);mshare([[X,Y,In,_1],[X,In,_1],[X,_1],[Y],[Y,In],[In],[Out],[_1,_3],[_4],[_5],[Mid]]),ground([_2]),linear(Out),linear(_3),linear(_4),linear(_5),linear(Mid);mshare([[X,In,_1],[Y],[Out],[_1,_3],[_4],[_5],[Mid]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1),linear(_3),linear(_4),linear(_5),linear(Mid))),
    'C'(_3,move(tvar^h,Y),_4),
    true((mshare([[X,Y,In,_1,_3],[X,In,_1],[X,_1],[Y,In,_1,_3],[Y,_1,_3],[In],[Out],[_1,_3,_4],[_2],[_5],[Mid]]),linear(Out),linear(_2),linear(_4),linear(_5),linear(Mid);mshare([[X,Y,In,_1,_3],[X,In,_1],[X,_1],[Y,In,_1,_3],[Y,_1,_3],[In],[Out],[_1,_3,_4],[_5],[Mid]]),ground([_2]),linear(Out),linear(_4),linear(_5),linear(Mid);mshare([[X,In,_1],[Y,_1,_3],[Out],[_1,_3,_4],[_5],[Mid]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1),linear(_3),linear(_4),linear(_5),linear(Mid))),
    'C'(_4,add(1,h),_5),
    true((mshare([[X,Y,In,_1,_3],[X,In,_1],[X,_1],[Y,In,_1,_3],[Y,_1,_3],[In],[Out],[_1,_3,_4,_5],[_2],[Mid]]),linear(Out),linear(_2),linear(_4),linear(_5),linear(Mid);mshare([[X,Y,In,_1,_3],[X,In,_1],[X,_1],[Y,In,_1,_3],[Y,_1,_3],[In],[Out],[_1,_3,_4,_5],[Mid]]),ground([_2]),linear(Out),linear(_4),linear(_5),linear(Mid);mshare([[X,In,_1],[Y,_1,_3],[Out],[_1,_3,_4,_5],[Mid]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_1),linear(_3),linear(_4),linear(_5),linear(Mid))),
    'C'(_5,move(Y,[h-1]),_2),
    true((mshare([[X,Y,In,_1,_3,_4,_5],[X,In,_1],[X,_1],[Y,In,_1,_3,_4,_5],[Y,_1,_3,_4,_5],[In],[Out],[_1,_2,_3,_4,_5],[Mid]]),linear(Out),linear(_2),linear(Mid);mshare([[X,Y,In,_1,_3,_4,_5],[X,In,_1],[X,_1],[Y,In,_1,_3,_4,_5],[Y,_1,_3,_4,_5],[In],[Out],[Mid]]),ground([_2]),linear(Out),linear(Mid);mshare([[X,In,_1],[Y,_1,_3,_4,_5],[Out],[Mid]]),ground([_2]),linear(X),linear(Y),linear(In),linear(Out),linear(_4),linear(_5),linear(Mid))),
    incl(X,In,Mid),
    true((mshare([[X,Y,In,_1,_3,_4,_5,Mid],[X,In,_1,Mid],[X,_1],[X,_1,Mid],[Y,In,_1,_3,_4,_5,Mid],[Y,_1,_3,_4,_5],[In,Mid],[Out]]),ground([_2]),linear(Out);mshare([[X,Y,In,_1,_3,_4,_5,Mid],[X,In,_1,Mid],[X,_1],[X,_1,Mid],[Y,In,_1,_3,_4,_5,Mid],[Y,_1,_3,_4,_5],[In,Mid],[Out],[_1,_2,_3,_4,_5]]),linear(Out),linear(_2);mshare([[X,In,_1,Mid],[Y,_1,_3,_4,_5],[Out]]),ground([_2]),linear(Y),linear(Out),linear(_4),linear(_5))),
    incl(Y,Mid,Out),
    true((mshare([[X,Y,In,Out,_1,_3,_4,_5,Mid],[X,Y,Out,_1,_3,_4,_5,Mid],[X,In,Out,_1,Mid],[X,Out,_1,Mid],[X,_1],[Y,In,Out,_1,_3,_4,_5,Mid],[Y,Out,_1,_3,_4,_5],[Y,_1,_3,_4,_5],[In,Out,Mid]]),ground([_2]);mshare([[X,Y,In,Out,_1,_3,_4,_5,Mid],[X,Y,Out,_1,_3,_4,_5,Mid],[X,In,Out,_1,Mid],[X,Out,_1,Mid],[X,_1],[Y,In,Out,_1,_3,_4,_5,Mid],[Y,Out,_1,_3,_4,_5],[Y,_1,_3,_4,_5],[In,Out,Mid],[_1,_2,_3,_4,_5]]),linear(_2);mshare([[X,In,Out,_1,Mid],[Y,Out,_1,_3,_4,_5],[Y,_1,_3,_4,_5]]),ground([_2]),linear(Y),linear(_4),linear(_5))).

:- true pred 'unify_var/6/2/$disj/1'(Y,In)
   : mshare([[Y],[Y,In],[In]])
   => mshare([[Y],[Y,In],[In]]).

:- true pred 'unify_var/6/2/$disj/1'(Y,In)
   : ( mshare([[Y],[In]]),
       linear(Y), linear(In) )
   => ( mshare([[Y],[In]]),
        linear(Y), linear(In) ).

'unify_var/6/2/$disj/1'(Y,In) :-
    true((mshare([[Y],[Y,In],[In]]);mshare([[Y],[In]]),linear(Y),linear(In))),
    myin(Y,In),
    !,
    true((mshare([[Y],[Y,In],[In]]);mshare([[Y],[In]]),linear(Y),linear(In))),
    fail,
    true(fails(_)).
'unify_var/6/2/$disj/1'(Y,In).

:- true pred 'unify_var/6/3/$disj/1'(X,In)
   : ( mshare([[X],[X,In],[In]]),
       linear(X) )
   => ( mshare([[X],[X,In],[In]]),
        linear(X) ).

:- true pred 'unify_var/6/3/$disj/1'(X,In)
   : ( mshare([[X,In]]),
       linear(X), linear(In) )
   => ( mshare([[X,In]]),
        linear(X), linear(In) ).

'unify_var/6/3/$disj/1'(X,In) :-
    true((mshare([[X],[X,In],[In]]),linear(X);mshare([[X,In]]),linear(X),linear(In))),
    myin(X,In),
    !,
    true((mshare([[X],[X,In],[In]]),linear(X);mshare([[X,In]]),linear(X),linear(In))),
    fail,
    true(fails(_)).
'unify_var/6/3/$disj/1'(X,In).

:- true pred 'unify_var/6/4/$disj/1'(X,In)
   : ( mshare([[X],[X,In],[In]]),
       linear(X) )
   => ( mshare([[X],[X,In],[In]]),
        linear(X) ).

:- true pred 'unify_var/6/4/$disj/1'(X,In)
   : ( mshare([[X,In]]),
       linear(X), linear(In) )
   => ( mshare([[X,In]]),
        linear(X), linear(In) ).

'unify_var/6/4/$disj/1'(X,In) :-
    true((mshare([[X],[X,In],[In]]),linear(X);mshare([[X,In]]),linear(X),linear(In))),
    myin(X,In),
    !,
    true((mshare([[X],[X,In],[In]]),linear(X);mshare([[X,In]]),linear(X),linear(In))),
    fail,
    true(fails(_)).
'unify_var/6/4/$disj/1'(X,In).

:- true pred 'unify_var/6/4/$disj/2'(Y,In)
   : mshare([[Y],[Y,In],[In]])
   => mshare([[Y],[Y,In],[In]]).

:- true pred 'unify_var/6/4/$disj/2'(Y,In)
   : ( mshare([[Y],[In]]),
       linear(Y), linear(In) )
   => ( mshare([[Y],[In]]),
        linear(Y), linear(In) ).

'unify_var/6/4/$disj/2'(Y,In) :-
    true((mshare([[Y],[Y,In],[In]]);mshare([[Y],[In]]),linear(Y),linear(In))),
    myin(Y,In),
    !,
    true((mshare([[Y],[Y,In],[In]]);mshare([[Y],[In]]),linear(Y),linear(In))),
    fail,
    true(fails(_)).
'unify_var/6/4/$disj/2'(Y,In).

:- true pred unify_readmode(X,T,In,Out,LLbls,_1,_2)
   : ( (_2=[]),
       mshare([[X],[X,T,In],[X,In],[T],[T,In],[In],[Out],[LLbls],[_1]]),
       linear(Out), linear(_1) )
   => mshare([[X],[X,T,In,Out],[X,T,In,Out,_1],[X,T,Out,_1],[X,In,Out],[X,In,Out,_1],[X,Out,_1],[X,_1],[T],[T,In,Out],[T,In,Out,_1],[T,Out,_1],[T,_1],[In,Out],[In,Out,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]).

:- true pred unify_readmode(X,T,In,Out,LLbls,_1,_2)
   : ( (_2=[]),
       mshare([[X,T,In],[X,In],[T],[Out],[LLbls],[_1]]),
       linear(Out), linear(_1) )
   => mshare([[X,T,In,Out],[X,T,In,Out,_1],[X,In,Out],[X,In,Out,_1],[T],[T,Out,_1],[T,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]).

unify_readmode(X,T,In,Out,LLbls,_1,_2) :-
    true((mshare([[X],[X,T,In],[X,In],[T],[T,In],[In],[Out],[LLbls],[_1],[_3],[F],[N]]),ground([_2]),linear(Out),linear(_1),linear(_3),linear(F),linear(N);mshare([[X,T,In],[X,In],[T],[Out],[LLbls],[_1],[_3],[F],[N]]),ground([_2]),linear(Out),linear(_1),linear(_3),linear(F),linear(N))),
    structure(T),
    !,
    true((mshare([[X],[X,T,In],[X,In],[T],[T,In],[In],[Out],[LLbls],[_1],[_3],[F],[N]]),ground([_2]),linear(Out),linear(_1),linear(_3),linear(F),linear(N);mshare([[X,T,In],[X,In],[T],[Out],[LLbls],[_1],[_3],[F],[N]]),ground([_2]),linear(Out),linear(_1),linear(_3),linear(F),linear(N))),
    'C'(_1,equal([X],tatm^(F/N),fail),_3),
    true((mshare([[X,T,In,_1],[X,In,_1],[X,_1],[T],[T,In],[In],[Out],[LLbls],[_1,_3],[_1,F],[_1,N]]),ground([_2]),linear(Out),linear(_3),linear(F),linear(N);mshare([[X,T,In,_1],[X,In,_1],[T],[Out],[LLbls],[_1,_3],[_1,F],[_1,N]]),ground([_2]),linear(Out),linear(_3),linear(F),linear(N))),
    functor(T,F,N),
    true((mshare([[X,T,In,_1],[X,In,_1],[X,_1],[T],[T,In],[In],[Out],[LLbls],[_1,_3]]),ground([_2,F,N]),linear(Out),linear(_3);mshare([[X,T,In,_1],[X,In,_1],[T],[Out],[LLbls],[_1,_3]]),ground([_2,F,N]),linear(Out),linear(_3))),
    unify_args(1,N,T,In,Out,0,X,LLbls,_3,_2),
    true((mshare([[X,T,In,Out,_1],[X,T,In,Out,_1,_3],[X,T,Out,_1,_3],[X,In,Out,_1],[X,In,Out,_1,_3],[X,Out,_1,_3],[X,_1],[X,_1,_3],[T],[T,In,Out],[T,In,Out,_1,_3],[T,Out,_1,_3],[T,_1,_3],[In,Out],[In,Out,_1,_3],[Out,_1,_3],[LLbls],[LLbls,_1,_3],[_1,_3]]),ground([_2,F,N]);mshare([[X,T,In,Out,_1],[X,T,In,Out,_1,_3],[X,In,Out,_1],[X,In,Out,_1,_3],[T],[T,Out,_1,_3],[T,_1,_3],[Out,_1,_3],[LLbls],[LLbls,_1,_3],[_1,_3]]),ground([_2,F,N]))).
unify_readmode(X,T,In,Out,LLbls,_1,_2) :-
    true((mshare([[X],[X,T,In],[X,In],[T],[T,In],[In],[Out],[LLbls],[_1]]),ground([_2]),linear(Out),linear(_1);mshare([[X,T,In],[X,In],[T],[Out],[LLbls],[_1]]),ground([_2]),linear(Out),linear(_1))),
    cons(T),
    !,
    true((mshare([[X],[X,T,In],[X,In],[T],[T,In],[In],[Out],[LLbls],[_1]]),ground([_2]),linear(Out),linear(_1);mshare([[X,T,In],[X,In],[T],[Out],[LLbls],[_1]]),ground([_2]),linear(Out),linear(_1))),
    unify_args(1,2,T,In,Out,-1,X,LLbls,_1,_2),
    true((mshare([[X],[X,T,In,Out],[X,T,In,Out,_1],[X,T,Out,_1],[X,In,Out],[X,In,Out,_1],[X,Out,_1],[X,_1],[T],[T,In,Out],[T,In,Out,_1],[T,Out,_1],[T,_1],[In,Out],[In,Out,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]),ground([_2]);mshare([[X,T,In,Out],[X,T,In,Out,_1],[X,In,Out],[X,In,Out,_1],[T],[T,Out,_1],[T,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]),ground([_2]))).
unify_readmode(X,T,In,In,_1,_2,_3) :-
    true((mshare([[X],[X,T,In],[X,In],[T],[T,In],[In],[_1],[_2]]),ground([_3]),linear(_2);mshare([[X,T,In],[X,In],[T],[_1],[_2]]),ground([_3]),linear(_2))),
    atomic(T),
    !,
    true((mshare([[X],[X,In],[In],[_1],[_2]]),ground([T,_3]),linear(_2);mshare([[X,In],[_1],[_2]]),ground([T,_3]),linear(_2))),
    'C'(_2,equal(X,tatm^T,fail),_3),
    true((mshare([[X,In,_2],[X,_2],[In],[_1]]),ground([T,_3]);mshare([[X,In,_2],[_1]]),ground([T,_3]))).

:- true pred unify_args(I,N,_1,In,Out,_2,_3,_4,_5,_6)
   : ( mshare([[_1],[_1,In],[_1,In,_3],[In],[In,_3],[Out],[_3],[_4],[_5]]),
       ground([I,N,_2,_6]), linear(Out), linear(_5) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_3],[_1,In,Out,_3,_5],[_1,In,Out,_5],[_1,Out,_3,_5],[_1,Out,_5],[_1,_5],[In,Out],[In,Out,_3],[In,Out,_3,_5],[In,Out,_5],[Out,_3,_5],[Out,_5],[_3],[_3,_5],[_4],[_4,_5],[_5]]),
        ground([I,N,_2,_6]) ).

:- true pred unify_args(I,N,_1,In,Out,_2,_3,_4,_5,_6)
   : ( (I=1), (N=2), (_2= -1),
       mshare([[_1],[_1,In],[_1,In,_3],[In],[In,_3],[Out],[_3],[_4],[_5]]),
       ground([_6]), linear(Out), linear(_5) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_3],[_1,In,Out,_3,_5],[_1,In,Out,_5],[_1,Out,_3,_5],[_1,Out,_5],[_1,_5],[In,Out],[In,Out,_3],[In,Out,_3,_5],[In,Out,_5],[Out,_3,_5],[Out,_5],[_3],[_3,_5],[_4],[_4,_5],[_5]]),
        ground([_6]) ).

:- true pred unify_args(I,N,_1,In,Out,_2,_3,_4,_5,_6)
   : ( (I=1), (_2=0),
       mshare([[_1],[_1,In],[_1,In,_3],[In],[In,_3],[Out],[_3],[_4],[_5]]),
       ground([N,_6]), linear(Out), linear(_5) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_3],[_1,In,Out,_3,_5],[_1,In,Out,_5],[_1,Out,_3,_5],[_1,Out,_5],[_1,_5],[In,Out],[In,Out,_3],[In,Out,_3,_5],[In,Out,_5],[Out,_3,_5],[Out,_5],[_3],[_3,_5],[_4],[_4,_5],[_5]]),
        ground([N,_6]) ).

:- true pred unify_args(I,N,_1,In,Out,_2,_3,_4,_5,_6)
   : ( mshare([[_1],[_1,In],[_1,In,_3],[In],[In,_3],[Out],[_4],[_5]]),
       ground([I,N,_2,_6]), linear(Out), linear(_5) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_3],[_1,In,Out,_3,_5],[_1,In,Out,_5],[_1,Out,_5],[_1,_5],[In,Out],[In,Out,_3],[In,Out,_3,_5],[In,Out,_5],[Out,_5],[_4],[_4,_5],[_5]]),
        ground([I,N,_2,_6]) ).

:- true pred unify_args(I,N,_1,In,Out,_2,_3,_4,_5,_6)
   : ( (I=1), (N=2), (_2= -1),
       mshare([[_1],[_1,In,_3],[In,_3],[Out],[_4],[_5]]),
       ground([_6]), linear(Out), linear(_5) )
   => ( mshare([[_1],[_1,In,Out,_3],[_1,In,Out,_3,_5],[_1,Out,_5],[_1,_5],[In,Out,_3],[In,Out,_3,_5],[Out,_5],[_4],[_4,_5],[_5]]),
        ground([_6]) ).

:- true pred unify_args(I,N,_1,In,Out,_2,_3,_4,_5,_6)
   : ( (I=1), (_2=0),
       mshare([[_1],[_1,In,_3],[In,_3],[Out],[_4],[_5]]),
       ground([N,_6]), linear(Out), linear(_5) )
   => ( mshare([[_1],[_1,In,Out,_3],[_1,In,Out,_3,_5],[_1,Out,_5],[_1,_5],[In,Out,_3],[In,Out,_3,_5],[Out,_5],[_4],[_4,_5],[_5]]),
        ground([N,_6]) ).

unify_args(I,N,_1,In,In,_2,_3,_4,_5,_6) :-
    true((mshare([[_1],[_1,In],[_1,In,_3],[In],[In,_3],[_3],[_4],[_5]]),ground([I,N,_2,_6]),linear(_5);mshare([[_1],[_1,In],[_1,In,_3],[In],[In,_3],[_4],[_5]]),ground([I,N,_2,_6]),linear(_5);mshare([[_1],[_1,In,_3],[In,_3],[_4],[_5]]),ground([I,N,_2,_6]),linear(_5))),
    I>N,
    !,
    true((mshare([[_1],[_1,In],[_1,In,_3],[In],[In,_3],[_3],[_4],[_5]]),ground([I,N,_2,_6]),linear(_5);mshare([[_1],[_1,In],[_1,In,_3],[In],[In,_3],[_4],[_5]]),ground([I,N,_2,_6]),linear(_5);mshare([[_1],[_1,In,_3],[In,_3],[_4],[_5]]),ground([I,N,_2,_6]),linear(_5))),
    _6=_5,
    true((mshare([[_1],[_1,In],[_1,In,_3],[In],[In,_3],[_3],[_4]]),ground([I,N,_2,_5,_6]);mshare([[_1],[_1,In],[_1,In,_3],[In],[In,_3],[_4]]),ground([I,N,_2,_5,_6]);mshare([[_1],[_1,In,_3],[In,_3],[_4]]),ground([I,N,_2,_5,_6]))).
unify_args(I,N,T,In,Out,D,X,[_3|LLbls],_1,_2) :-
    true((mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[X],[_1],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]),linear(Out),linear(_1);mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[_1],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]),linear(Out),linear(_1);mshare([[T],[T,In,X],[In,X],[Out],[_1],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]),linear(Out),linear(_1))),
    I=N,
    !,
    true((mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[X],[_1],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]),linear(Out),linear(_1);mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[_1],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]),linear(Out),linear(_1);mshare([[T],[T,In,X],[In,X],[Out],[_1],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]),linear(Out),linear(_1))),
    unify_arg(I,T,In,Out,D,X,last,LLbls,_1,_2),
    true((mshare([[T],[T,In,Out],[T,In,Out,X,_1],[T,In,Out,_1],[T,Out,_1],[T,_1],[In,Out],[In,Out,X,_1],[In,Out,_1],[Out,_1],[X,_1],[_1],[_1,_3,LLbls],[_1,LLbls],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]);mshare([[T],[T,In,Out],[T,In,Out,X,_1],[T,In,Out,_1],[T,Out,_1],[T,_1],[In,Out],[In,Out,X,_1],[In,Out,_1],[Out,_1],[_1],[_1,_3,LLbls],[_1,LLbls],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]);mshare([[T],[T,In,Out,X,_1],[T,Out,_1],[T,_1],[In,Out,X,_1],[Out,_1],[_1],[_1,_3,LLbls],[_1,LLbls],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]))).
unify_args(I,N,T,In,Out,D,X,LLbls,_1,_2) :-
    true((mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[X],[LLbls],[_1],[Mid],[_3],[_4],[I1]]),ground([I,N,D,_2]),linear(Out),linear(_1),linear(Mid),linear(_3),linear(_4),linear(I1);mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[LLbls],[_1],[Mid],[_3],[_4],[I1]]),ground([I,N,D,_2]),linear(Out),linear(_1),linear(Mid),linear(_3),linear(_4),linear(I1);mshare([[T],[T,In,X],[In,X],[Out],[LLbls],[_1],[Mid],[_3],[_4],[I1]]),ground([I,N,D,_2]),linear(Out),linear(_1),linear(Mid),linear(_3),linear(_4),linear(I1))),
    I<N,
    !,
    true((mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[X],[LLbls],[_1],[Mid],[_3],[_4],[I1]]),ground([I,N,D,_2]),linear(Out),linear(_1),linear(Mid),linear(_3),linear(_4),linear(I1);mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[LLbls],[_1],[Mid],[_3],[_4],[I1]]),ground([I,N,D,_2]),linear(Out),linear(_1),linear(Mid),linear(_3),linear(_4),linear(I1);mshare([[T],[T,In,X],[In,X],[Out],[LLbls],[_1],[Mid],[_3],[_4],[I1]]),ground([I,N,D,_2]),linear(Out),linear(_1),linear(Mid),linear(_3),linear(_4),linear(I1))),
    unify_arg(I,T,In,Mid,D,X,nonlast,_3,_1,_4),
    true((mshare([[T],[T,In,X,_1,Mid],[T,In,_1,Mid],[T,In,Mid],[T,_1],[T,_1,Mid],[In,X,_1,Mid],[In,_1,Mid],[In,Mid],[Out],[X,_1],[LLbls],[_1],[_1,Mid],[_1,_3],[_1,_4],[_3],[I1]]),ground([I,N,D,_2]),linear(Out),linear(_4),linear(I1);mshare([[T],[T,In,X,_1,Mid],[T,In,_1,Mid],[T,In,Mid],[T,_1],[T,_1,Mid],[In,X,_1,Mid],[In,_1,Mid],[In,Mid],[Out],[LLbls],[_1],[_1,Mid],[_1,_3],[_1,_4],[_3],[I1]]),ground([I,N,D,_2]),linear(Out),linear(_4),linear(I1);mshare([[T],[T,In,X,_1,Mid],[T,_1],[T,_1,Mid],[In,X,_1,Mid],[Out],[LLbls],[_1],[_1,Mid],[_1,_3],[_1,_4],[_3],[I1]]),ground([I,N,D,_2]),linear(Out),linear(_4),linear(I1))),
    I1 is I+1,
    true((mshare([[T],[T,In,X,_1,Mid],[T,In,_1,Mid],[T,In,Mid],[T,_1],[T,_1,Mid],[In,X,_1,Mid],[In,_1,Mid],[In,Mid],[Out],[X,_1],[LLbls],[_1],[_1,Mid],[_1,_3],[_1,_4],[_3]]),ground([I,N,D,_2,I1]),linear(Out),linear(_4);mshare([[T],[T,In,X,_1,Mid],[T,In,_1,Mid],[T,In,Mid],[T,_1],[T,_1,Mid],[In,X,_1,Mid],[In,_1,Mid],[In,Mid],[Out],[LLbls],[_1],[_1,Mid],[_1,_3],[_1,_4],[_3]]),ground([I,N,D,_2,I1]),linear(Out),linear(_4);mshare([[T],[T,In,X,_1,Mid],[T,_1],[T,_1,Mid],[In,X,_1,Mid],[Out],[LLbls],[_1],[_1,Mid],[_1,_3],[_1,_4],[_3]]),ground([I,N,D,_2,I1]),linear(Out),linear(_4))),
    unify_args(I1,N,T,Mid,Out,D,X,LLbls,_4,_2),
    true((mshare([[T],[T,In,Out,X,_1,Mid],[T,In,Out,X,_1,Mid,_4],[T,In,Out,_1,Mid],[T,In,Out,_1,Mid,_4],[T,In,Out,Mid],[T,Out,X,_1,Mid],[T,Out,X,_1,Mid,_4],[T,Out,X,_1,_4],[T,Out,_1,Mid],[T,Out,_1,Mid,_4],[T,Out,_1,_4],[T,_1],[T,_1,_4],[In,Out,X,_1,Mid],[In,Out,X,_1,Mid,_4],[In,Out,_1,Mid],[In,Out,_1,Mid,_4],[In,Out,Mid],[Out,X,_1,Mid],[Out,X,_1,Mid,_4],[Out,X,_1,_4],[Out,_1,Mid],[Out,_1,Mid,_4],[Out,_1,_4],[X,_1],[X,_1,_4],[LLbls],[LLbls,_1,_4],[_1],[_1,_3],[_1,_4],[_3]]),ground([I,N,D,_2,I1]);mshare([[T],[T,In,Out,X,_1,Mid],[T,In,Out,X,_1,Mid,_4],[T,In,Out,_1,Mid],[T,In,Out,_1,Mid,_4],[T,In,Out,Mid],[T,Out,_1,Mid],[T,Out,_1,Mid,_4],[T,Out,_1,_4],[T,_1],[T,_1,_4],[In,Out,X,_1,Mid],[In,Out,X,_1,Mid,_4],[In,Out,_1,Mid],[In,Out,_1,Mid,_4],[In,Out,Mid],[Out,_1,Mid],[Out,_1,Mid,_4],[Out,_1,_4],[LLbls],[LLbls,_1,_4],[_1],[_1,_3],[_1,_4],[_3]]),ground([I,N,D,_2,I1]);mshare([[T],[T,In,Out,X,_1,Mid],[T,In,Out,X,_1,Mid,_4],[T,Out,_1,Mid],[T,Out,_1,Mid,_4],[T,Out,_1,_4],[T,_1],[T,_1,_4],[In,Out,X,_1,Mid],[In,Out,X,_1,Mid,_4],[Out,_1,Mid],[Out,_1,Mid,_4],[Out,_1,_4],[LLbls],[LLbls,_1,_4],[_1],[_1,_3],[_1,_4],[_3]]),ground([I,N,D,_2,I1]))).

:- true pred unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2)
   : ( (Last=last),
       mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[X],[LLbls],[_1]]),
       ground([I,D,_2]), linear(Out), linear(_1) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,X,_1],[T,In,Out,_1],[T,Out,_1],[T,_1],[In,Out],[In,Out,X,_1],[In,Out,_1],[Out,_1],[X,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([I,D,_2]) ).

:- true pred unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2)
   : ( (Last=nonlast),
       mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[X],[LLbls],[_1],[_2]]),
       ground([I,D]), linear(Out), linear(LLbls), linear(_1), linear(_2) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,X,_1],[T,In,Out,_1],[T,Out,_1],[T,_1],[In,Out],[In,Out,X,_1],[In,Out,_1],[Out,_1],[X,_1],[LLbls],[LLbls,_1],[_1],[_1,_2]]),
        ground([I,D]), linear(_2) ).

:- true pred unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2)
   : ( (Last=nonlast),
       mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[LLbls],[_1],[_2]]),
       ground([I,D]), linear(Out), linear(LLbls), linear(_1), linear(_2) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,X,_1],[T,In,Out,_1],[T,Out,_1],[T,_1],[In,Out],[In,Out,X,_1],[In,Out,_1],[Out,_1],[LLbls],[LLbls,_1],[_1],[_1,_2]]),
        ground([I,D]), linear(_2) ).

:- true pred unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2)
   : ( (Last=nonlast),
       mshare([[T],[T,In,X],[In,X],[Out],[LLbls],[_1],[_2]]),
       ground([I,D]), linear(Out), linear(LLbls), linear(_1), linear(_2) )
   => ( mshare([[T],[T,In,Out,X,_1],[T,Out,_1],[T,_1],[In,Out,X,_1],[Out,_1],[LLbls],[LLbls,_1],[_1],[_1,_2]]),
        ground([I,D]), linear(_2) ).

:- true pred unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2)
   : ( (Last=last),
       mshare([[T],[T,In,X],[In,X],[Out],[LLbls],[_1]]),
       ground([I,D,_2]), linear(Out), linear(_1) )
   => ( mshare([[T],[T,In,Out,X,_1],[T,Out,_1],[T,_1],[In,Out,X,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([I,D,_2]) ).

:- true pred unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2)
   : ( (Last=last),
       mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[LLbls],[_1]]),
       ground([I,D,_2]), linear(Out), linear(_1) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,X,_1],[T,In,Out,_1],[T,Out,_1],[T,_1],[In,Out],[In,Out,X,_1],[In,Out,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([I,D,_2]) ).

unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2) :-
    true((mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[X],[LLbls],[_1],[_2],[_3],[Y],[ID],[Mid],[A]]),ground([I,D,Last]),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(_3),linear(Y),linear(ID),linear(Mid),linear(A);mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[X],[LLbls],[_1],[_3],[Y],[ID],[Mid],[A]]),ground([I,D,Last,_2]),linear(Out),linear(_1),linear(_3),linear(Y),linear(ID),linear(Mid),linear(A);mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[LLbls],[_1],[_2],[_3],[Y],[ID],[Mid],[A]]),ground([I,D,Last]),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(_3),linear(Y),linear(ID),linear(Mid),linear(A);mshare([[T],[T,In],[T,In,X],[In],[In,X],[Out],[LLbls],[_1],[_3],[Y],[ID],[Mid],[A]]),ground([I,D,Last,_2]),linear(Out),linear(_1),linear(_3),linear(Y),linear(ID),linear(Mid),linear(A);mshare([[T],[T,In,X],[In,X],[Out],[LLbls],[_1],[_2],[_3],[Y],[ID],[Mid],[A]]),ground([I,D,Last]),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(_3),linear(Y),linear(ID),linear(Mid),linear(A);mshare([[T],[T,In,X],[In,X],[Out],[LLbls],[_1],[_3],[Y],[ID],[Mid],[A]]),ground([I,D,Last,_2]),linear(Out),linear(_1),linear(_3),linear(Y),linear(ID),linear(Mid),linear(A))),
    'C'(_1,move([X+ID],Y),_3),
    true((mshare([[T],[T,In],[T,In,X,_1],[In],[In,X,_1],[Out],[X,_1],[LLbls],[_1,_3],[_1,Y],[_1,ID],[_2],[Mid],[A]]),ground([I,D,Last]),linear(Out),linear(LLbls),linear(_2),linear(_3),linear(Y),linear(ID),linear(Mid),linear(A);mshare([[T],[T,In],[T,In,X,_1],[In],[In,X,_1],[Out],[X,_1],[LLbls],[_1,_3],[_1,Y],[_1,ID],[Mid],[A]]),ground([I,D,Last,_2]),linear(Out),linear(_3),linear(Y),linear(ID),linear(Mid),linear(A);mshare([[T],[T,In],[T,In,X,_1],[In],[In,X,_1],[Out],[LLbls],[_1,_3],[_1,Y],[_1,ID],[_2],[Mid],[A]]),ground([I,D,Last]),linear(Out),linear(LLbls),linear(_2),linear(_3),linear(Y),linear(ID),linear(Mid),linear(A);mshare([[T],[T,In],[T,In,X,_1],[In],[In,X,_1],[Out],[LLbls],[_1,_3],[_1,Y],[_1,ID],[Mid],[A]]),ground([I,D,Last,_2]),linear(Out),linear(_3),linear(Y),linear(ID),linear(Mid),linear(A);mshare([[T],[T,In,X,_1],[In,X,_1],[Out],[LLbls],[_1,_3],[_1,Y],[_1,ID],[_2],[Mid],[A]]),ground([I,D,Last]),linear(Out),linear(LLbls),linear(_2),linear(_3),linear(Y),linear(ID),linear(Mid),linear(A);mshare([[T],[T,In,X,_1],[In,X,_1],[Out],[LLbls],[_1,_3],[_1,Y],[_1,ID],[Mid],[A]]),ground([I,D,Last,_2]),linear(Out),linear(_3),linear(Y),linear(ID),linear(Mid),linear(A))),
    ID is I+D,
    true((mshare([[T],[T,In],[T,In,X,_1],[In],[In,X,_1],[Out],[X,_1],[LLbls],[_1,_3],[_1,Y],[_2],[Mid],[A]]),ground([I,D,Last,ID]),linear(Out),linear(LLbls),linear(_2),linear(_3),linear(Y),linear(Mid),linear(A);mshare([[T],[T,In],[T,In,X,_1],[In],[In,X,_1],[Out],[X,_1],[LLbls],[_1,_3],[_1,Y],[Mid],[A]]),ground([I,D,Last,_2,ID]),linear(Out),linear(_3),linear(Y),linear(Mid),linear(A);mshare([[T],[T,In],[T,In,X,_1],[In],[In,X,_1],[Out],[LLbls],[_1,_3],[_1,Y],[_2],[Mid],[A]]),ground([I,D,Last,ID]),linear(Out),linear(LLbls),linear(_2),linear(_3),linear(Y),linear(Mid),linear(A);mshare([[T],[T,In],[T,In,X,_1],[In],[In,X,_1],[Out],[LLbls],[_1,_3],[_1,Y],[Mid],[A]]),ground([I,D,Last,_2,ID]),linear(Out),linear(_3),linear(Y),linear(Mid),linear(A);mshare([[T],[T,In,X,_1],[In,X,_1],[Out],[LLbls],[_1,_3],[_1,Y],[_2],[Mid],[A]]),ground([I,D,Last,ID]),linear(Out),linear(LLbls),linear(_2),linear(_3),linear(Y),linear(Mid),linear(A);mshare([[T],[T,In,X,_1],[In,X,_1],[Out],[LLbls],[_1,_3],[_1,Y],[Mid],[A]]),ground([I,D,Last,_2,ID]),linear(Out),linear(_3),linear(Y),linear(Mid),linear(A))),
    incl(Y,In,Mid),
    true((mshare([[T],[T,In,X,_1,Mid],[T,In,Mid],[In,X,_1,Mid],[In,Mid],[Out],[X,_1],[LLbls],[_1,_3],[_1,Y],[_1,Y,Mid],[_2],[A]]),ground([I,D,Last,ID]),linear(Out),linear(LLbls),linear(_2),linear(_3),linear(Y),linear(A);mshare([[T],[T,In,X,_1,Mid],[T,In,Mid],[In,X,_1,Mid],[In,Mid],[Out],[X,_1],[LLbls],[_1,_3],[_1,Y],[_1,Y,Mid],[A]]),ground([I,D,Last,_2,ID]),linear(Out),linear(_3),linear(Y),linear(A);mshare([[T],[T,In,X,_1,Mid],[T,In,Mid],[In,X,_1,Mid],[In,Mid],[Out],[LLbls],[_1,_3],[_1,Y],[_1,Y,Mid],[_2],[A]]),ground([I,D,Last,ID]),linear(Out),linear(LLbls),linear(_2),linear(_3),linear(Y),linear(A);mshare([[T],[T,In,X,_1,Mid],[T,In,Mid],[In,X,_1,Mid],[In,Mid],[Out],[LLbls],[_1,_3],[_1,Y],[_1,Y,Mid],[A]]),ground([I,D,Last,_2,ID]),linear(Out),linear(_3),linear(Y),linear(A);mshare([[T],[T,In,X,_1,Mid],[In,X,_1,Mid],[Out],[LLbls],[_1,_3],[_1,Y],[_1,Y,Mid],[_2],[A]]),ground([I,D,Last,ID]),linear(Out),linear(LLbls),linear(_2),linear(_3),linear(Y),linear(A);mshare([[T],[T,In,X,_1,Mid],[In,X,_1,Mid],[Out],[LLbls],[_1,_3],[_1,Y],[_1,Y,Mid],[A]]),ground([I,D,Last,_2,ID]),linear(Out),linear(_3),linear(Y),linear(A))),
    arg(I,T,A),
    true((mshare([[T,In,X,_1,Mid,A],[T,In,Mid,A],[T,A],[In,X,_1,Mid],[In,Mid],[Out],[X,_1],[LLbls],[_1,_3],[_1,Y],[_1,Y,Mid]]),ground([I,D,Last,_2,ID]),linear(Out),linear(_3),linear(Y);mshare([[T,In,X,_1,Mid,A],[T,In,Mid,A],[T,A],[In,X,_1,Mid],[In,Mid],[Out],[X,_1],[LLbls],[_1,_3],[_1,Y],[_1,Y,Mid],[_2]]),ground([I,D,Last,ID]),linear(Out),linear(LLbls),linear(_2),linear(_3),linear(Y);mshare([[T,In,X,_1,Mid,A],[T,In,Mid,A],[T,A],[In,X,_1,Mid],[In,Mid],[Out],[LLbls],[_1,_3],[_1,Y],[_1,Y,Mid]]),ground([I,D,Last,_2,ID]),linear(Out),linear(_3),linear(Y);mshare([[T,In,X,_1,Mid,A],[T,In,Mid,A],[T,A],[In,X,_1,Mid],[In,Mid],[Out],[LLbls],[_1,_3],[_1,Y],[_1,Y,Mid],[_2]]),ground([I,D,Last,ID]),linear(Out),linear(LLbls),linear(_2),linear(_3),linear(Y);mshare([[T,In,X,_1,Mid,A],[T,A],[In,X,_1,Mid],[Out],[LLbls],[_1,_3],[_1,Y],[_1,Y,Mid]]),ground([I,D,Last,_2,ID]),linear(Out),linear(_3),linear(Y);mshare([[T,In,X,_1,Mid,A],[T,A],[In,X,_1,Mid],[Out],[LLbls],[_1,_3],[_1,Y],[_1,Y,Mid],[_2]]),ground([I,D,Last,ID]),linear(Out),linear(LLbls),linear(_2),linear(_3),linear(Y))),
    init(Y,A,Mid,Out,Last,LLbls,_3,_2),
    true((mshare([[T,In,Out,X,_1,_3,Y,Mid,A],[T,In,Out,X,_1,_3,Mid,A],[T,In,Out,X,_1,Mid,A],[T,In,Out,_1,_3,Y,Mid,A],[T,In,Out,_1,_3,Mid,A],[T,In,Out,Mid,A],[T,Out,_1,_3,Y,Mid,A],[T,Out,_1,_3,Y,A],[T,Out,_1,_3,A],[T,_1,_3,A],[T,A],[In,Out,X,_1,_3,Y,Mid],[In,Out,X,_1,_3,Mid],[In,Out,X,_1,Mid],[In,Out,_1,_3,Y,Mid],[In,Out,_1,_3,Mid],[In,Out,Mid],[Out,_1,_3],[Out,_1,_3,Y],[Out,_1,_3,Y,Mid],[X,_1],[LLbls],[LLbls,_1,_3],[_1,_2,_3],[_1,_3],[_1,_3,Y]]),ground([I,D,Last,ID]),linear(_2);mshare([[T,In,Out,X,_1,_3,Y,Mid,A],[T,In,Out,X,_1,_3,Mid,A],[T,In,Out,X,_1,Mid,A],[T,In,Out,_1,_3,Y,Mid,A],[T,In,Out,_1,_3,Mid,A],[T,In,Out,Mid,A],[T,Out,_1,_3,Y,Mid,A],[T,Out,_1,_3,Y,A],[T,Out,_1,_3,A],[T,_1,_3,A],[T,A],[In,Out,X,_1,_3,Y,Mid],[In,Out,X,_1,_3,Mid],[In,Out,X,_1,Mid],[In,Out,_1,_3,Y,Mid],[In,Out,_1,_3,Mid],[In,Out,Mid],[Out,_1,_3],[Out,_1,_3,Y],[Out,_1,_3,Y,Mid],[X,_1],[LLbls],[LLbls,_1,_3],[_1,_3],[_1,_3,Y]]),ground([I,D,Last,_2,ID]);mshare([[T,In,Out,X,_1,_3,Y,Mid,A],[T,In,Out,X,_1,_3,Mid,A],[T,In,Out,X,_1,Mid,A],[T,In,Out,_1,_3,Y,Mid,A],[T,In,Out,_1,_3,Mid,A],[T,In,Out,Mid,A],[T,Out,_1,_3,Y,Mid,A],[T,Out,_1,_3,Y,A],[T,Out,_1,_3,A],[T,_1,_3,A],[T,A],[In,Out,X,_1,_3,Y,Mid],[In,Out,X,_1,_3,Mid],[In,Out,X,_1,Mid],[In,Out,_1,_3,Y,Mid],[In,Out,_1,_3,Mid],[In,Out,Mid],[Out,_1,_3],[Out,_1,_3,Y],[Out,_1,_3,Y,Mid],[LLbls],[LLbls,_1,_3],[_1,_2,_3],[_1,_3],[_1,_3,Y]]),ground([I,D,Last,ID]),linear(_2);mshare([[T,In,Out,X,_1,_3,Y,Mid,A],[T,In,Out,X,_1,_3,Mid,A],[T,In,Out,X,_1,Mid,A],[T,In,Out,_1,_3,Y,Mid,A],[T,In,Out,_1,_3,Mid,A],[T,In,Out,Mid,A],[T,Out,_1,_3,Y,Mid,A],[T,Out,_1,_3,Y,A],[T,Out,_1,_3,A],[T,_1,_3,A],[T,A],[In,Out,X,_1,_3,Y,Mid],[In,Out,X,_1,_3,Mid],[In,Out,X,_1,Mid],[In,Out,_1,_3,Y,Mid],[In,Out,_1,_3,Mid],[In,Out,Mid],[Out,_1,_3],[Out,_1,_3,Y],[Out,_1,_3,Y,Mid],[LLbls],[LLbls,_1,_3],[_1,_3],[_1,_3,Y]]),ground([I,D,Last,_2,ID]);mshare([[T,In,Out,X,_1,_3,Y,Mid,A],[T,In,Out,X,_1,_3,Mid,A],[T,In,Out,X,_1,Mid,A],[T,Out,_1,_3,Y,Mid,A],[T,Out,_1,_3,Y,A],[T,Out,_1,_3,A],[T,_1,_3,A],[T,A],[In,Out,X,_1,_3,Y,Mid],[In,Out,X,_1,_3,Mid],[In,Out,X,_1,Mid],[Out,_1,_3],[Out,_1,_3,Y],[Out,_1,_3,Y,Mid],[LLbls],[LLbls,_1,_3],[_1,_2,_3],[_1,_3],[_1,_3,Y]]),ground([I,D,Last,ID]),linear(_2);mshare([[T,In,Out,X,_1,_3,Y,Mid,A],[T,In,Out,X,_1,_3,Mid,A],[T,In,Out,X,_1,Mid,A],[T,Out,_1,_3,Y,Mid,A],[T,Out,_1,_3,Y,A],[T,Out,_1,_3,A],[T,_1,_3,A],[T,A],[In,Out,X,_1,_3,Y,Mid],[In,Out,X,_1,_3,Mid],[In,Out,X,_1,Mid],[Out,_1,_3],[Out,_1,_3,Y],[Out,_1,_3,Y,Mid],[LLbls],[LLbls,_1,_3],[_1,_3],[_1,_3,Y]]),ground([I,D,Last,_2,ID]))).

:- true pred unify_writemode(X,T,In,Last,LLbls,_1,_2)
   : ( (_2=[]),
       mshare([[X],[X,In],[T],[T,In],[In],[LLbls],[_1]]),
       ground([Last]), linear(X), linear(LLbls), linear(_1) )
   => ( mshare([[X,T,In,_1],[X,In,_1],[X,_1],[T],[T,In],[T,In,_1],[T,_1],[In],[LLbls],[LLbls,_1],[_1]]),
        ground([Last]) ).

:- true pred unify_writemode(X,T,In,Last,LLbls,_1,_2)
   : ( (_2=[]),
       mshare([[X],[X,In],[T],[T,In],[In],[LLbls],[_1]]),
       ground([Last]), linear(X), linear(_1) )
   => ( mshare([[X,T,In,_1],[X,In,_1],[X,_1],[T],[T,In],[T,In,_1],[T,_1],[In],[LLbls],[LLbls,_1],[_1]]),
        ground([Last]) ).

:- true pred unify_writemode(X,T,In,Last,LLbls,_1,_2)
   : ( (_2=[]),
       mshare([[X,In],[T],[LLbls],[_1]]),
       ground([Last]), linear(X), linear(In), linear(LLbls), linear(_1) )
   => ( mshare([[X,T,In,_1],[X,In,_1],[T],[T,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([Last]) ).

unify_writemode(X,T,In,Last,LLbls,_1,_2) :-
    true((mshare([[X],[X,In],[T],[T,In],[In],[LLbls],[_1],[_3],[Tag],[_4],[_5]]),ground([Last,_2]),linear(X),linear(LLbls),linear(_1),linear(_3),linear(Tag),linear(_4),linear(_5);mshare([[X],[X,In],[T],[T,In],[In],[LLbls],[_1],[_3],[Tag],[_4],[_5]]),ground([Last,_2]),linear(X),linear(_1),linear(_3),linear(Tag),linear(_4),linear(_5);mshare([[X,In],[T],[LLbls],[_1],[_3],[Tag],[_4],[_5]]),ground([Last,_2]),linear(X),linear(In),linear(LLbls),linear(_1),linear(_3),linear(Tag),linear(_4),linear(_5))),
    my_compound(T),
    !,
    true((mshare([[X],[X,In],[T],[T,In],[In],[LLbls],[_1],[_3],[Tag],[_4],[_5]]),ground([Last,_2]),linear(X),linear(LLbls),linear(_1),linear(_3),linear(Tag),linear(_4),linear(_5);mshare([[X],[X,In],[T],[T,In],[In],[LLbls],[_1],[_3],[Tag],[_4],[_5]]),ground([Last,_2]),linear(X),linear(_1),linear(_3),linear(Tag),linear(_4),linear(_5);mshare([[X,In],[T],[LLbls],[_1],[_3],[Tag],[_4],[_5]]),ground([Last,_2]),linear(X),linear(In),linear(LLbls),linear(_1),linear(_3),linear(Tag),linear(_4),linear(_5))),
    'C'(_1,move(Tag^h,[X]),_3),
    true((mshare([[X,In,_1],[X,_1],[T],[T,In],[In],[LLbls],[_1,_3],[_1,Tag],[_4],[_5]]),ground([Last,_2]),linear(X),linear(LLbls),linear(_1),linear(_3),linear(Tag),linear(_4),linear(_5);mshare([[X,In,_1],[X,_1],[T],[T,In],[In],[LLbls],[_1,_3],[_1,Tag],[_4],[_5]]),ground([Last,_2]),linear(X),linear(_1),linear(_3),linear(Tag),linear(_4),linear(_5);mshare([[X,In,_1],[T],[LLbls],[_1,_3],[_1,Tag],[_4],[_5]]),ground([Last,_2]),linear(X),linear(In),linear(LLbls),linear(_1),linear(_3),linear(Tag),linear(_4),linear(_5))),
    termtag(T,Tag),
    true((mshare([[X,In,_1],[X,_1],[T],[T,In],[In],[LLbls],[_1,_3],[_4],[_5]]),ground([Last,_2,Tag]),linear(X),linear(LLbls),linear(_1),linear(_3),linear(_4),linear(_5);mshare([[X,In,_1],[X,_1],[T],[T,In],[In],[LLbls],[_1,_3],[_4],[_5]]),ground([Last,_2,Tag]),linear(X),linear(_1),linear(_3),linear(_4),linear(_5);mshare([[X,In,_1],[T],[LLbls],[_1,_3],[_4],[_5]]),ground([Last,_2,Tag]),linear(X),linear(In),linear(LLbls),linear(_1),linear(_3),linear(_4),linear(_5))),
    unify_block(Last,T,_4,In,_5,LLbls,_3,_2),
    true((mshare([[X,T,In,_1,_3,_5],[X,T,In,_1,_5],[X,In,_1,_5],[X,_1],[T],[T,In,_1,_3,_5],[T,In,_5],[T,_1,_3],[T,_1,_3,_5],[T,_5],[In,_5],[LLbls],[LLbls,_1,_3],[_1,_3]]),ground([Last,_2,Tag,_4]);mshare([[X,T,In,_1,_3,_5],[X,T,In,_1,_5],[X,In,_1,_5],[T],[T,_1,_3],[T,_1,_3,_5],[T,_5],[LLbls],[LLbls,_1,_3],[_1,_3]]),ground([Last,_2,Tag,_4]))).
unify_writemode(X,T,_1,_2,_3,_4,_5) :-
    true((mshare([[X],[X,_1],[T],[T,_1],[_1],[_3],[_4]]),ground([_2,_5]),linear(X),linear(_3),linear(_4);mshare([[X],[X,_1],[T],[T,_1],[_1],[_3],[_4]]),ground([_2,_5]),linear(X),linear(_4);mshare([[X,_1],[T],[_3],[_4]]),ground([_2,_5]),linear(X),linear(_1),linear(_3),linear(_4))),
    atomic(T),
    !,
    true((mshare([[X],[X,_1],[_1],[_3],[_4]]),ground([T,_2,_5]),linear(X),linear(_3),linear(_4);mshare([[X],[X,_1],[_1],[_3],[_4]]),ground([T,_2,_5]),linear(X),linear(_4);mshare([[X,_1],[_3],[_4]]),ground([T,_2,_5]),linear(X),linear(_1),linear(_3),linear(_4))),
    'C'(_4,move(tatm^T,[X]),_5),
    true((mshare([[X,_1,_4],[X,_4],[_1],[_3]]),ground([T,_2,_5]),linear(X),linear(_3),linear(_4);mshare([[X,_1,_4],[X,_4],[_1],[_3]]),ground([T,_2,_5]),linear(X),linear(_4);mshare([[X,_1,_4],[_3]]),ground([T,_2,_5]),linear(X),linear(_1),linear(_3),linear(_4))).

:- true pred unify_block(_A,T,Size,In,Out,_B,_1,_2)
   : ( mshare([[T],[T,In],[Size],[In],[Out],[_B],[_1]]),
       ground([_A,_2]), linear(Size), linear(Out), linear(_B), linear(_1) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_1],[T,Out],[T,Out,_1],[T,_1],[In,Out],[_B],[_B,_1],[_1]]),
        ground([_A,Size,_2]) ).

:- true pred unify_block(_A,T,Size,In,Out,_B,_1,_2)
   : ( mshare([[T],[T,In],[Size],[In],[Out],[_B],[_1]]),
       ground([_A,_2]), linear(Size), linear(Out), linear(_1) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_1],[T,Out],[T,Out,_1],[T,_1],[In,Out],[_B],[_B,_1],[_1]]),
        ground([_A,Size,_2]) ).

:- true pred unify_block(_A,T,Size,In,Out,_B,_1,_2)
   : ( mshare([[T],[Size],[In],[Out],[_B],[_1]]),
       ground([_A,_2]), linear(Size), linear(In), linear(Out), linear(_B), linear(_1) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_1],[T,Out],[T,Out,_1],[T,_1],[In,Out],[_B],[_B,_1],[_1]]),
        ground([_A,Size,_2]) ).

:- true pred unify_block(_A,T,Size,In,Out,_B,_1,_2)
   : ( (_A=nonlast),
       mshare([[T],[Size],[In],[Out],[_B],[_1]]),
       ground([_2]), linear(Size), linear(In), linear(Out), linear(_B), linear(_1) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_1],[T,Out],[T,Out,_1],[T,_1],[In,Out],[_B],[_B,_1],[_1]]),
        ground([Size,_2]) ).

unify_block(last,T,Size,In,In,[Lbl|_3],_1,_2) :-
    !,
    true((mshare([[T],[T,In],[Size],[In],[_1],[Lbl],[Lbl,_3],[_3],[_4]]),ground([_2]),linear(Size),linear(_1),linear(_4);mshare([[T],[T,In],[Size],[In],[_1],[Lbl],[_3],[_4]]),ground([_2]),linear(Size),linear(_1),linear(Lbl),linear(_3),linear(_4);mshare([[T],[Size],[In],[_1],[Lbl],[_3],[_4]]),ground([_2]),linear(Size),linear(In),linear(_1),linear(Lbl),linear(_3),linear(_4))),
    'C'(_1,add(Size,h),_4),
    true((mshare([[T],[T,In],[Size,_1],[In],[_1,_4],[Lbl],[Lbl,_3],[_3]]),ground([_2]),linear(Size),linear(_1),linear(_4);mshare([[T],[T,In],[Size,_1],[In],[_1,_4],[Lbl],[_3]]),ground([_2]),linear(Size),linear(_1),linear(Lbl),linear(_3),linear(_4);mshare([[T],[Size,_1],[In],[_1,_4],[Lbl],[_3]]),ground([_2]),linear(Size),linear(In),linear(_1),linear(Lbl),linear(_3),linear(_4))),
    'C'(_4,jump(Lbl),_2),
    true((mshare([[T],[T,In],[Size,_1],[In],[_1,Lbl,_3,_4],[_1,Lbl,_4],[_3]]),ground([_2]),linear(Size);mshare([[T],[T,In],[Size,_1],[In],[_1,Lbl,_4],[_3]]),ground([_2]),linear(Size),linear(_1),linear(Lbl),linear(_3),linear(_4);mshare([[T],[Size,_1],[In],[_1,Lbl,_4],[_3]]),ground([_2]),linear(Size),linear(In),linear(_1),linear(Lbl),linear(_3),linear(_4))),
    unify:size(T,0,Size),
    true((mshare([[T],[T,In],[In],[_1,Lbl,_3,_4],[_1,Lbl,_4],[_3]]),ground([Size,_2]);mshare([[T],[T,In],[In],[_1,Lbl,_4],[_3]]),ground([Size,_2]),linear(_1),linear(Lbl),linear(_3),linear(_4);mshare([[T],[In],[_1,Lbl,_4],[_3]]),ground([Size,_2]),linear(In),linear(_1),linear(Lbl),linear(_3),linear(_4))).
unify_block(nonlast,T,Size,In,Out,[_3|LLbls],_1,_2) :-
    !,
    true((mshare([[T],[T,In],[Size],[In],[Out],[_1],[_3],[_3,LLbls],[LLbls],[_4],[Offset]]),ground([_2]),linear(Size),linear(Out),linear(_1),linear(_4),linear(Offset);mshare([[T],[T,In],[Size],[In],[Out],[_1],[_3],[LLbls],[_4],[Offset]]),ground([_2]),linear(Size),linear(Out),linear(_1),linear(_3),linear(LLbls),linear(_4),linear(Offset);mshare([[T],[Size],[In],[Out],[_1],[_3],[LLbls],[_4],[Offset]]),ground([_2]),linear(Size),linear(In),linear(Out),linear(_1),linear(_3),linear(LLbls),linear(_4),linear(Offset))),
    'C'(_1,add(Size,h),_4),
    true((mshare([[T],[T,In],[Size,_1],[In],[Out],[_1,_4],[_3],[_3,LLbls],[LLbls],[Offset]]),ground([_2]),linear(Size),linear(Out),linear(_1),linear(_4),linear(Offset);mshare([[T],[T,In],[Size,_1],[In],[Out],[_1,_4],[_3],[LLbls],[Offset]]),ground([_2]),linear(Size),linear(Out),linear(_1),linear(_3),linear(LLbls),linear(_4),linear(Offset);mshare([[T],[Size,_1],[In],[Out],[_1,_4],[_3],[LLbls],[Offset]]),ground([_2]),linear(Size),linear(In),linear(Out),linear(_1),linear(_3),linear(LLbls),linear(_4),linear(Offset))),
    unify:size(T,0,Size),
    true((mshare([[T],[T,In],[In],[Out],[_1,_4],[_3],[_3,LLbls],[LLbls],[Offset]]),ground([Size,_2]),linear(Out),linear(_1),linear(_4),linear(Offset);mshare([[T],[T,In],[In],[Out],[_1,_4],[_3],[LLbls],[Offset]]),ground([Size,_2]),linear(Out),linear(_1),linear(_3),linear(LLbls),linear(_4),linear(Offset);mshare([[T],[In],[Out],[_1,_4],[_3],[LLbls],[Offset]]),ground([Size,_2]),linear(In),linear(Out),linear(_1),linear(_3),linear(LLbls),linear(_4),linear(Offset))),
    Offset is-Size,
    true((mshare([[T],[T,In],[In],[Out],[_1,_4],[_3],[_3,LLbls],[LLbls]]),ground([Size,_2,Offset]),linear(Out),linear(_1),linear(_4);mshare([[T],[T,In],[In],[Out],[_1,_4],[_3],[LLbls]]),ground([Size,_2,Offset]),linear(Out),linear(_1),linear(_3),linear(LLbls),linear(_4);mshare([[T],[In],[Out],[_1,_4],[_3],[LLbls]]),ground([Size,_2,Offset]),linear(In),linear(Out),linear(_1),linear(_3),linear(LLbls),linear(_4))),
    block(T,Offset,0,In,Out,LLbls,_4,_2),
    true((mshare([[T],[T,In,Out],[T,In,Out,_1,_4],[T,Out],[T,Out,_1,_4],[T,_1,_4],[In,Out],[_1,_3,LLbls,_4],[_1,LLbls,_4],[_1,_4],[_3]]),ground([Size,_2,Offset]);mshare([[T],[T,In,Out],[T,In,Out,_1,_4],[T,Out],[T,Out,_1,_4],[T,_1,_4],[In,Out],[_1,LLbls,_4],[_1,_4],[_3]]),ground([Size,_2,Offset]),linear(_3))).

:- true pred block(T,Inf,Outf,In,Out,LLbls,_1,_2)
   : ( mshare([[T],[T,In],[In],[Out],[LLbls],[_1]]),
       ground([Inf,Outf,_2]), linear(Out), linear(LLbls), linear(_1) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_1],[T,Out],[T,Out,_1],[T,_1],[In,Out],[LLbls,_1],[_1]]),
        ground([Inf,Outf,_2]) ).

:- true pred block(T,Inf,Outf,In,Out,LLbls,_1,_2)
   : ( mshare([[T],[T,In],[In],[Out],[LLbls],[_1]]),
       ground([Inf,Outf,_2]), linear(Out), linear(_1) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_1],[T,Out],[T,Out,_1],[T,_1],[In,Out],[LLbls,_1],[_1]]),
        ground([Inf,Outf,_2]) ).

:- true pred block(T,Inf,Outf,In,Out,LLbls,_1,_2)
   : ( (Outf=0),
       mshare([[T],[T,In],[In],[Out],[LLbls],[_1]]),
       ground([Inf,_2]), linear(Out), linear(LLbls), linear(_1) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_1],[T,Out],[T,Out,_1],[T,_1],[In,Out],[LLbls,_1],[_1]]),
        ground([Inf,_2]) ).

:- true pred block(T,Inf,Outf,In,Out,LLbls,_1,_2)
   : ( (Outf=0),
       mshare([[T],[T,In],[In],[Out],[LLbls],[_1]]),
       ground([Inf,_2]), linear(Out), linear(_1) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_1],[T,Out],[T,Out,_1],[T,_1],[In,Out],[LLbls,_1],[_1]]),
        ground([Inf,_2]) ).

:- true pred block(T,Inf,Outf,In,Out,LLbls,_1,_2)
   : ( mshare([[T],[T,In],[Outf],[In],[Out],[LLbls],[_1],[_2]]),
       ground([Inf]), linear(Outf), linear(Out), linear(LLbls), linear(_1), linear(_2) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_1],[T,Out],[T,Out,_1],[T,_1],[In,Out],[LLbls,_1],[_1],[_1,_2]]),
        ground([Inf,Outf]), linear(_2) ).

:- true pred block(T,Inf,Outf,In,Out,LLbls,_1,_2)
   : ( (Outf=0),
       mshare([[T],[In],[Out],[LLbls],[_1]]),
       ground([Inf,_2]), linear(In), linear(Out), linear(LLbls), linear(_1) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_1],[T,Out],[T,Out,_1],[T,_1],[In,Out],[LLbls,_1],[_1]]),
        ground([Inf,_2]) ).

block(T,Inf,Outf,In,Out,LLbls,_1,_2) :-
    true((mshare([[T],[T,In],[Outf],[In],[Out],[LLbls],[_1],[_2],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf]),linear(Outf),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(_3),linear(F),linear(N),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(F),linear(N),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]),linear(Out),linear(_1),linear(_3),linear(F),linear(N),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[In],[Out],[LLbls],[_1],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]),linear(In),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(F),linear(N),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4))),
    structure(T),
    !,
    true((mshare([[T],[T,In],[Outf],[In],[Out],[LLbls],[_1],[_2],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf]),linear(Outf),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(_3),linear(F),linear(N),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(F),linear(N),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]),linear(Out),linear(_1),linear(_3),linear(F),linear(N),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[In],[Out],[LLbls],[_1],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]),linear(In),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(F),linear(N),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4))),
    'C'(_1,move(tatm^(F/N),[h+Inf]),_3),
    true((mshare([[T],[T,In],[Outf],[In],[Out],[LLbls],[_1,_3],[_1,F],[_1,N],[_2],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf]),linear(Outf),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(_3),linear(F),linear(N),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[T,In],[In],[Out],[LLbls],[_1,_3],[_1,F],[_1,N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(F),linear(N),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[T,In],[In],[Out],[LLbls],[_1,_3],[_1,F],[_1,N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]),linear(Out),linear(_1),linear(_3),linear(F),linear(N),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[In],[Out],[LLbls],[_1,_3],[_1,F],[_1,N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]),linear(In),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(F),linear(N),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4))),
    functor(T,F,N),
    true((mshare([[T],[T,In],[Outf],[In],[Out],[LLbls],[_1,_3],[_2],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,F,N]),linear(Outf),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(_3),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[T,In],[In],[Out],[LLbls],[_1,_3],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N]),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[T,In],[In],[Out],[LLbls],[_1,_3],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N]),linear(Out),linear(_1),linear(_3),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[In],[Out],[LLbls],[_1,_3],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N]),linear(In),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(Midf),linear(S),linear(Offsets),linear(Mid),linear(_4))),
    Midf is Inf+N+1,
    true((mshare([[T],[T,In],[Outf],[In],[Out],[LLbls],[_1,_3],[_2],[S],[Offsets],[Mid],[_4]]),ground([Inf,F,N,Midf]),linear(Outf),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(_3),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[T,In],[In],[Out],[LLbls],[_1,_3],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N,Midf]),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[T,In],[In],[Out],[LLbls],[_1,_3],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N,Midf]),linear(Out),linear(_1),linear(_3),linear(S),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[In],[Out],[LLbls],[_1,_3],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N,Midf]),linear(In),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(S),linear(Offsets),linear(Mid),linear(_4))),
    S is Inf+1,
    true((mshare([[T],[T,In],[Outf],[In],[Out],[LLbls],[_1,_3],[_2],[Offsets],[Mid],[_4]]),ground([Inf,F,N,Midf,S]),linear(Outf),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(_3),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[T,In],[In],[Out],[LLbls],[_1,_3],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N,Midf,S]),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[T,In],[In],[Out],[LLbls],[_1,_3],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N,Midf,S]),linear(Out),linear(_1),linear(_3),linear(Offsets),linear(Mid),linear(_4);mshare([[T],[In],[Out],[LLbls],[_1,_3],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N,Midf,S]),linear(In),linear(Out),linear(LLbls),linear(_1),linear(_3),linear(Offsets),linear(Mid),linear(_4))),
    make_slots(1,N,T,S,Offsets,In,Mid,_3,_4),
    true((mshare([[T],[T,In,_1,_3,Mid],[T,In,Mid],[T,_1,_3],[T,_1,_3,Mid],[T,Mid],[Outf],[In,Mid],[Out],[LLbls],[_1,_3,Offsets],[_1,_3,_4],[_2],[Offsets]]),ground([Inf,F,N,Midf,S]),linear(Outf),linear(Out),linear(LLbls),linear(_2),linear(_4);mshare([[T],[T,In,_1,_3,Mid],[T,In,Mid],[T,_1,_3],[T,_1,_3,Mid],[T,Mid],[In,Mid],[Out],[LLbls],[_1,_3,Offsets],[_1,_3,_4],[Offsets]]),ground([Inf,Outf,_2,F,N,Midf,S]),linear(Out),linear(LLbls),linear(_4);mshare([[T],[T,In,_1,_3,Mid],[T,In,Mid],[T,_1,_3],[T,_1,_3,Mid],[T,Mid],[In,Mid],[Out],[LLbls],[_1,_3,Offsets],[_1,_3,_4],[Offsets]]),ground([Inf,Outf,_2,F,N,Midf,S]),linear(Out),linear(_4))),
    block_args(1,N,T,Midf,Outf,Offsets,Mid,Out,LLbls,_4,_2),
    true((mshare([[T],[T,In,Out,_1,_3,Mid],[T,In,Out,_1,_3,Mid,_4],[T,In,Out,Mid],[T,Out],[T,Out,_1,_3],[T,Out,_1,_3,Mid],[T,Out,_1,_3,Mid,_4],[T,Out,_1,_3,_4],[T,Out,Mid],[T,_1,_3],[T,_1,_3,_4],[In,Out,Mid],[LLbls,_1,_3,_4],[_1,_2,_3,_4],[_1,_3,_4]]),ground([Inf,Outf,F,N,Midf,S,Offsets]),linear(_2);mshare([[T],[T,In,Out,_1,_3,Mid],[T,In,Out,_1,_3,Mid,_4],[T,In,Out,Mid],[T,Out],[T,Out,_1,_3],[T,Out,_1,_3,Mid],[T,Out,_1,_3,Mid,_4],[T,Out,_1,_3,_4],[T,Out,Mid],[T,_1,_3],[T,_1,_3,_4],[In,Out,Mid],[LLbls,_1,_3,_4],[_1,_3,_4]]),ground([Inf,Outf,_2,F,N,Midf,S,Offsets]))).
block(T,Inf,Outf,In,Out,LLbls,_1,_2) :-
    true((mshare([[T],[T,In],[Outf],[In],[Out],[LLbls],[_1],[_2],[Midf],[Offsets],[Mid],[_3]]),ground([Inf]),linear(Outf),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(Midf),linear(Offsets),linear(Mid),linear(_3);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[Midf],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2]),linear(Out),linear(LLbls),linear(_1),linear(Midf),linear(Offsets),linear(Mid),linear(_3);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[Midf],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2]),linear(Out),linear(_1),linear(Midf),linear(Offsets),linear(Mid),linear(_3);mshare([[T],[In],[Out],[LLbls],[_1],[Midf],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2]),linear(In),linear(Out),linear(LLbls),linear(_1),linear(Midf),linear(Offsets),linear(Mid),linear(_3))),
    cons(T),
    !,
    true((mshare([[T],[T,In],[Outf],[In],[Out],[LLbls],[_1],[_2],[Midf],[Offsets],[Mid],[_3]]),ground([Inf]),linear(Outf),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(Midf),linear(Offsets),linear(Mid),linear(_3);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[Midf],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2]),linear(Out),linear(LLbls),linear(_1),linear(Midf),linear(Offsets),linear(Mid),linear(_3);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[Midf],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2]),linear(Out),linear(_1),linear(Midf),linear(Offsets),linear(Mid),linear(_3);mshare([[T],[In],[Out],[LLbls],[_1],[Midf],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2]),linear(In),linear(Out),linear(LLbls),linear(_1),linear(Midf),linear(Offsets),linear(Mid),linear(_3))),
    Midf is Inf+2,
    true((mshare([[T],[T,In],[Outf],[In],[Out],[LLbls],[_1],[_2],[Offsets],[Mid],[_3]]),ground([Inf,Midf]),linear(Outf),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(Offsets),linear(Mid),linear(_3);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2,Midf]),linear(Out),linear(LLbls),linear(_1),linear(Offsets),linear(Mid),linear(_3);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2,Midf]),linear(Out),linear(_1),linear(Offsets),linear(Mid),linear(_3);mshare([[T],[In],[Out],[LLbls],[_1],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2,Midf]),linear(In),linear(Out),linear(LLbls),linear(_1),linear(Offsets),linear(Mid),linear(_3))),
    make_slots(1,2,T,Inf,Offsets,In,Mid,_1,_3),
    true((mshare([[T],[T,In,_1,Mid],[T,In,Mid],[T,_1],[T,_1,Mid],[T,Mid],[Outf],[In,Mid],[Out],[LLbls],[_1,Offsets],[_1,_3],[_2],[Offsets]]),ground([Inf,Midf]),linear(Outf),linear(Out),linear(LLbls),linear(_2),linear(_3);mshare([[T],[T,In,_1,Mid],[T,In,Mid],[T,_1],[T,_1,Mid],[T,Mid],[In,Mid],[Out],[LLbls],[_1,Offsets],[_1,_3],[Offsets]]),ground([Inf,Outf,_2,Midf]),linear(Out),linear(LLbls),linear(_3);mshare([[T],[T,In,_1,Mid],[T,In,Mid],[T,_1],[T,_1,Mid],[T,Mid],[In,Mid],[Out],[LLbls],[_1,Offsets],[_1,_3],[Offsets]]),ground([Inf,Outf,_2,Midf]),linear(Out),linear(_3))),
    block_args(1,2,T,Midf,Outf,Offsets,Mid,Out,LLbls,_3,_2),
    true((mshare([[T],[T,In,Out,_1,Mid],[T,In,Out,_1,Mid,_3],[T,In,Out,Mid],[T,Out],[T,Out,_1],[T,Out,_1,Mid],[T,Out,_1,Mid,_3],[T,Out,_1,_3],[T,Out,Mid],[T,_1],[T,_1,_3],[In,Out,Mid],[LLbls,_1,_3],[_1,_2,_3],[_1,_3]]),ground([Inf,Outf,Midf,Offsets]),linear(_2);mshare([[T],[T,In,Out,_1,Mid],[T,In,Out,_1,Mid,_3],[T,In,Out,Mid],[T,Out],[T,Out,_1],[T,Out,_1,Mid],[T,Out,_1,Mid,_3],[T,Out,_1,_3],[T,Out,Mid],[T,_1],[T,_1,_3],[In,Out,Mid],[LLbls,_1,_3],[_1,_3]]),ground([Inf,Outf,_2,Midf,Offsets]))).
block(T,Inf,Inf,In,In,[],_1,_2) :-
    true((mshare([[T],[T,In],[In],[_1]]),ground([Inf,_2]),linear(_1);mshare([[T],[T,In],[In],[_1],[_2]]),ground([Inf]),linear(_1),linear(_2);mshare([[T],[In],[_1]]),ground([Inf,_2]),linear(In),linear(_1))),
    atomic(T),
    !,
    true((mshare([[In],[_1]]),ground([T,Inf,_2]),linear(In),linear(_1);mshare([[In],[_1]]),ground([T,Inf,_2]),linear(_1);mshare([[In],[_1],[_2]]),ground([T,Inf]),linear(_1),linear(_2))),
    _2=_1,
    true((mshare([[In]]),ground([T,Inf,_1,_2]);mshare([[In]]),ground([T,Inf,_1,_2]),linear(In);mshare([[In],[_1,_2]]),ground([T,Inf]),linear(_1),linear(_2))).
block(T,Inf,Inf,In,In,[],_1,_2) :-
    true((mshare([[T],[T,In],[In],[_1]]),ground([Inf,_2]),linear(_1);mshare([[T],[T,In],[In],[_1],[_2]]),ground([Inf]),linear(_1),linear(_2);mshare([[T],[In],[_1]]),ground([Inf,_2]),linear(In),linear(_1))),
    var(T),
    !,
    true((mshare([[T],[T,In],[In],[_1]]),ground([Inf,_2]),linear(T),linear(_1);mshare([[T],[T,In],[In],[_1],[_2]]),ground([Inf]),linear(T),linear(_1),linear(_2);mshare([[T],[In],[_1]]),ground([Inf,_2]),linear(T),linear(In),linear(_1))),
    _2=_1,
    true((mshare([[T],[T,In],[In]]),ground([Inf,_1,_2]),linear(T);mshare([[T],[T,In],[In],[_1,_2]]),ground([Inf]),linear(T),linear(_1),linear(_2);mshare([[T],[In]]),ground([Inf,_1,_2]),linear(T),linear(In))).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( mshare([[_1],[_1,In],[Outf],[_A],[In],[Out],[LLbls],[_2],[_3]]),
       ground([I,N,Inf]), linear(Outf), linear(Out), linear(LLbls), linear(_2), linear(_3) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_2],[_1,Out],[_1,Out,_2],[_1,_2],[In,Out],[LLbls,_2],[_2],[_2,_3]]),
        ground([I,N,Inf,Outf,_A]), linear(_3) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1),
       mshare([[_1],[_1,In],[Outf],[_A],[In],[Out],[LLbls],[_2],[_3]]),
       ground([N,Inf]), linear(Outf), linear(Out), linear(LLbls), linear(_2), linear(_3) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_2],[_1,Out],[_1,Out,_2],[_1,_2],[In,Out],[LLbls,_2],[_2],[_2,_3]]),
        ground([N,Inf,Outf,_A]), linear(_3) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1), (N=2),
       mshare([[_1],[_1,In],[Outf],[_A],[In],[Out],[LLbls],[_2],[_3]]),
       ground([Inf]), linear(Outf), linear(Out), linear(LLbls), linear(_2), linear(_3) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_2],[_1,Out],[_1,Out,_2],[_1,_2],[In,Out],[LLbls,_2],[_2],[_2,_3]]),
        ground([Inf,Outf,_A]), linear(_3) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( mshare([[_1],[_1,In],[_A],[In],[Out],[LLbls],[_2]]),
       ground([I,N,Inf,Outf,_3]), linear(Out), linear(LLbls), linear(_2) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_2],[_1,Out],[_1,Out,_2],[_1,_2],[In,Out],[LLbls,_2],[_2]]),
        ground([I,N,Inf,Outf,_A,_3]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( mshare([[_1],[_1,In],[_A],[In],[Out],[LLbls],[_2]]),
       ground([I,N,Inf,Outf,_3]), linear(Out), linear(_2) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_2],[_1,Out],[_1,Out,_2],[_1,_2],[In,Out],[LLbls,_2],[_2]]),
        ground([I,N,Inf,Outf,_A,_3]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1), (N=2),
       mshare([[_1],[_1,In],[_A],[In],[Out],[LLbls],[_2]]),
       ground([Inf,Outf,_3]), linear(Out), linear(_2) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_2],[_1,Out],[_1,Out,_2],[_1,_2],[In,Out],[LLbls,_2],[_2]]),
        ground([Inf,Outf,_A,_3]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1), (N=2),
       mshare([[_1],[_1,In],[_A],[In],[Out],[LLbls],[_2]]),
       ground([Inf,Outf,_3]), linear(Out), linear(LLbls), linear(_2) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_2],[_1,Out],[_1,Out,_2],[_1,_2],[In,Out],[LLbls,_2],[_2]]),
        ground([Inf,Outf,_A,_3]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1),
       mshare([[_1],[_1,In],[_A],[In],[Out],[LLbls],[_2]]),
       ground([N,Inf,Outf,_3]), linear(Out), linear(LLbls), linear(_2) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_2],[_1,Out],[_1,Out,_2],[_1,_2],[In,Out],[LLbls,_2],[_2]]),
        ground([N,Inf,Outf,_A,_3]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1),
       mshare([[_1],[_1,In],[_A],[In],[Out],[LLbls],[_2]]),
       ground([N,Inf,Outf,_3]), linear(Out), linear(_2) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_2],[_1,Out],[_1,Out,_2],[_1,_2],[In,Out],[LLbls,_2],[_2]]),
        ground([N,Inf,Outf,_A,_3]) ).

block_args(I,N,_1,Inf,Inf,[],In,In,[],_2,_3) :-
    true((mshare([[_1],[_1,In],[In],[_2]]),ground([I,N,Inf,_3]),linear(_2);mshare([[_1],[_1,In],[In],[_2],[_3]]),ground([I,N,Inf]),linear(_2),linear(_3))),
    I>N,
    !,
    true((mshare([[_1],[_1,In],[In],[_2]]),ground([I,N,Inf,_3]),linear(_2);mshare([[_1],[_1,In],[In],[_2],[_3]]),ground([I,N,Inf]),linear(_2),linear(_3))),
    _3=_2,
    true((mshare([[_1],[_1,In],[In]]),ground([I,N,Inf,_2,_3]);mshare([[_1],[_1,In],[In],[_2,_3]]),ground([I,N,Inf]),linear(_2),linear(_3))).
block_args(I,N,T,Inf,Outf,[Inf],In,Out,[Lbl|LLbls],_1,_2) :-
    true((mshare([[T],[T,In],[Outf],[In],[Out],[_1],[_2],[Lbl],[LLbls],[_3],[A]]),ground([I,N,Inf]),linear(Outf),linear(Out),linear(_1),linear(_2),linear(Lbl),linear(LLbls),linear(_3),linear(A);mshare([[T],[T,In],[In],[Out],[_1],[Lbl],[Lbl,LLbls],[LLbls],[_3],[A]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(_1),linear(_3),linear(A);mshare([[T],[T,In],[In],[Out],[_1],[Lbl],[LLbls],[_3],[A]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(_1),linear(Lbl),linear(LLbls),linear(_3),linear(A))),
    I=N,
    !,
    true((mshare([[T],[T,In],[Outf],[In],[Out],[_1],[_2],[Lbl],[LLbls],[_3],[A]]),ground([I,N,Inf]),linear(Outf),linear(Out),linear(_1),linear(_2),linear(Lbl),linear(LLbls),linear(_3),linear(A);mshare([[T],[T,In],[In],[Out],[_1],[Lbl],[Lbl,LLbls],[LLbls],[_3],[A]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(_1),linear(_3),linear(A);mshare([[T],[T,In],[In],[Out],[_1],[Lbl],[LLbls],[_3],[A]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(_1),linear(Lbl),linear(LLbls),linear(_3),linear(A))),
    'C'(_1,label(Lbl),_3),
    true((mshare([[T],[T,In],[Outf],[In],[Out],[_1,Lbl],[_1,_3],[_2],[LLbls],[A]]),ground([I,N,Inf]),linear(Outf),linear(Out),linear(_1),linear(_2),linear(Lbl),linear(LLbls),linear(_3),linear(A);mshare([[T],[T,In],[In],[Out],[_1,Lbl],[_1,Lbl,LLbls],[_1,_3],[LLbls],[A]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(_3),linear(A);mshare([[T],[T,In],[In],[Out],[_1,Lbl],[_1,_3],[LLbls],[A]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(_1),linear(Lbl),linear(LLbls),linear(_3),linear(A))),
    arg(I,T,A),
    true((mshare([[T,In,A],[T,A],[Outf],[In],[Out],[_1,Lbl],[_1,_3],[_2],[LLbls]]),ground([I,N,Inf]),linear(Outf),linear(Out),linear(_1),linear(_2),linear(Lbl),linear(LLbls),linear(_3);mshare([[T,In,A],[T,A],[In],[Out],[_1,Lbl],[_1,Lbl,LLbls],[_1,_3],[LLbls]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(_3);mshare([[T,In,A],[T,A],[In],[Out],[_1,Lbl],[_1,_3],[LLbls]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(_1),linear(Lbl),linear(LLbls),linear(_3))),
    block(A,Inf,Outf,In,Out,LLbls,_3,_2),
    true((mshare([[T,In,Out,_1,_3,A],[T,In,Out,A],[T,Out,_1,_3,A],[T,Out,A],[T,_1,_3,A],[T,A],[In,Out],[_1,_2,_3],[_1,Lbl],[_1,LLbls,_3],[_1,_3]]),ground([I,N,Inf,Outf]),linear(_2),linear(Lbl);mshare([[T,In,Out,_1,_3,A],[T,In,Out,A],[T,Out,_1,_3,A],[T,Out,A],[T,_1,_3,A],[T,A],[In,Out],[_1,Lbl],[_1,Lbl,LLbls,_3],[_1,LLbls,_3],[_1,_3]]),ground([I,N,Inf,Outf,_2]);mshare([[T,In,Out,_1,_3,A],[T,In,Out,A],[T,Out,_1,_3,A],[T,Out,A],[T,_1,_3,A],[T,A],[In,Out],[_1,Lbl],[_1,LLbls,_3],[_1,_3]]),ground([I,N,Inf,Outf,_2]),linear(Lbl))).
block_args(I,N,T,Inf,Outf,[Inf|Offsets],In,Out,LLbls,_1,_2) :-
    true((mshare([[T],[T,In],[Outf],[In],[Out],[LLbls],[_1],[_2],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf]),linear(Outf),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(A),linear(Midf),linear(Mid),linear(_3),linear(_4),linear(I1);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(LLbls),linear(_1),linear(A),linear(Midf),linear(Mid),linear(_3),linear(_4),linear(I1);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(_1),linear(A),linear(Midf),linear(Mid),linear(_3),linear(_4),linear(I1))),
    I<N,
    !,
    true((mshare([[T],[T,In],[Outf],[In],[Out],[LLbls],[_1],[_2],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf]),linear(Outf),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(A),linear(Midf),linear(Mid),linear(_3),linear(_4),linear(I1);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(LLbls),linear(_1),linear(A),linear(Midf),linear(Mid),linear(_3),linear(_4),linear(I1);mshare([[T],[T,In],[In],[Out],[LLbls],[_1],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(_1),linear(A),linear(Midf),linear(Mid),linear(_3),linear(_4),linear(I1))),
    arg(I,T,A),
    true((mshare([[T,In,A],[T,A],[Outf],[In],[Out],[LLbls],[_1],[_2],[Offsets],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf]),linear(Outf),linear(Out),linear(LLbls),linear(_1),linear(_2),linear(Midf),linear(Mid),linear(_3),linear(_4),linear(I1);mshare([[T,In,A],[T,A],[In],[Out],[LLbls],[_1],[Offsets],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(LLbls),linear(_1),linear(Midf),linear(Mid),linear(_3),linear(_4),linear(I1);mshare([[T,In,A],[T,A],[In],[Out],[LLbls],[_1],[Offsets],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf,Outf,_2]),linear(Out),linear(_1),linear(Midf),linear(Mid),linear(_3),linear(_4),linear(I1))),
    block(A,Inf,Midf,In,Mid,_3,_1,_4),
    true((mshare([[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,A],[T,_1,A,Mid],[T,A],[T,A,Mid],[Outf],[In,Mid],[Out],[LLbls],[_1],[_1,_3],[_1,_4],[_2],[Offsets],[I1]]),ground([I,N,Inf,Midf]),linear(Outf),linear(Out),linear(LLbls),linear(_2),linear(_4),linear(I1);mshare([[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,A],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,Mid],[Out],[LLbls],[_1],[_1,_3],[_1,_4],[Offsets],[I1]]),ground([I,N,Inf,Outf,_2,Midf]),linear(Out),linear(LLbls),linear(_4),linear(I1);mshare([[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,A],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,Mid],[Out],[LLbls],[_1],[_1,_3],[_1,_4],[Offsets],[I1]]),ground([I,N,Inf,Outf,_2,Midf]),linear(Out),linear(_4),linear(I1))),
    I1 is I+1,
    true((mshare([[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,A],[T,_1,A,Mid],[T,A],[T,A,Mid],[Outf],[In,Mid],[Out],[LLbls],[_1],[_1,_3],[_1,_4],[_2],[Offsets]]),ground([I,N,Inf,Midf,I1]),linear(Outf),linear(Out),linear(LLbls),linear(_2),linear(_4);mshare([[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,A],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,Mid],[Out],[LLbls],[_1],[_1,_3],[_1,_4],[Offsets]]),ground([I,N,Inf,Outf,_2,Midf,I1]),linear(Out),linear(LLbls),linear(_4);mshare([[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,A],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,Mid],[Out],[LLbls],[_1],[_1,_3],[_1,_4],[Offsets]]),ground([I,N,Inf,Outf,_2,Midf,I1]),linear(Out),linear(_4))),
    block_args(I1,N,T,Midf,Outf,Offsets,Mid,Out,LLbls,_4,_2),
    true((mshare([[T,In,Out,_1,A,Mid],[T,In,Out,_1,A,Mid,_4],[T,In,Out,A,Mid],[T,Out,_1,A],[T,Out,_1,A,Mid],[T,Out,_1,A,Mid,_4],[T,Out,_1,A,_4],[T,Out,A],[T,Out,A,Mid],[T,_1,A],[T,_1,A,_4],[T,A],[In,Out,Mid],[LLbls,_1,_4],[_1],[_1,_2,_4],[_1,_3],[_1,_4]]),ground([I,N,Inf,Outf,Offsets,Midf,I1]),linear(_2);mshare([[T,In,Out,_1,A,Mid],[T,In,Out,_1,A,Mid,_4],[T,In,Out,A,Mid],[T,Out,_1,A],[T,Out,_1,A,Mid],[T,Out,_1,A,Mid,_4],[T,Out,_1,A,_4],[T,Out,A],[T,Out,A,Mid],[T,_1,A],[T,_1,A,_4],[T,A],[In,Out,Mid],[LLbls,_1,_4],[_1],[_1,_3],[_1,_4]]),ground([I,N,Inf,Outf,_2,Offsets,Midf,I1]))).

:- true pred make_slots(I,N,_1,_2,_A,In,Out,_3,_4)
   : ( (I=1), (N=2),
       mshare([[_1],[_1,In],[_A],[In],[Out],[_3],[_4]]),
       ground([_2]), linear(_A), linear(Out), linear(_3), linear(_4) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_3],[_1,Out],[_1,Out,_3],[_1,_3],[_A],[_A,_3],[In,Out],[_3,_4]]),
        ground([_2]), linear(_4) ).

:- true pred make_slots(I,N,_1,_2,_A,In,Out,_3,_4)
   : ( (I=1),
       mshare([[_1],[_1,In],[_A],[In],[Out],[_3],[_4]]),
       ground([N,_2]), linear(_A), linear(Out), linear(_3), linear(_4) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_3],[_1,Out],[_1,Out,_3],[_1,_3],[_A],[_A,_3],[In,Out],[_3,_4]]),
        ground([N,_2]), linear(_4) ).

:- true pred make_slots(I,N,_1,_2,_A,In,Out,_3,_4)
   : ( (I=1), (N=2),
       mshare([[_1],[_A],[In],[Out],[_3],[_4]]),
       ground([_2]), linear(_A), linear(In), linear(Out), linear(_3), linear(_4) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_3],[_1,Out],[_1,Out,_3],[_1,_3],[_A],[_A,_3],[In,Out],[_3,_4]]),
        ground([_2]), linear(_4) ).

:- true pred make_slots(I,N,_1,_2,_A,In,Out,_3,_4)
   : ( (I=1),
       mshare([[_1],[_A],[In],[Out],[_3],[_4]]),
       ground([N,_2]), linear(_A), linear(In), linear(Out), linear(_3), linear(_4) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_3],[_1,Out],[_1,Out,_3],[_1,_3],[_A],[_A,_3],[In,Out],[_3,_4]]),
        ground([N,_2]), linear(_4) ).

:- true pred make_slots(I,N,_1,_2,_A,In,Out,_3,_4)
   : ( mshare([[_1],[_1,In],[_A],[In],[Out],[_3],[_4]]),
       ground([I,N,_2]), linear(_A), linear(Out), linear(_3), linear(_4) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_3],[_1,Out],[_1,Out,_3],[_1,_3],[_A],[_A,_3],[In,Out],[_3,_4]]),
        ground([I,N,_2]), linear(_4) ).

make_slots(I,N,_1,_2,[],In,In,_3,_4) :-
    true((mshare([[_1],[_1,In],[In],[_3],[_4]]),ground([I,N,_2]),linear(_3),linear(_4);mshare([[_1],[In],[_3],[_4]]),ground([I,N,_2]),linear(In),linear(_3),linear(_4))),
    I>N,
    !,
    true((mshare([[_1],[_1,In],[In],[_3],[_4]]),ground([I,N,_2]),linear(_3),linear(_4);mshare([[_1],[In],[_3],[_4]]),ground([I,N,_2]),linear(In),linear(_3),linear(_4))),
    _4=_3,
    true((mshare([[_1],[_1,In],[In],[_3,_4]]),ground([I,N,_2]),linear(_3),linear(_4);mshare([[_1],[In],[_3,_4]]),ground([I,N,_2]),linear(In),linear(_3),linear(_4))).
make_slots(I,N,T,S,[Off|Offsets],In,Out,_1,_2) :-
    true((mshare([[T],[T,In],[In],[Out],[_1],[_2],[Off],[Offsets],[A],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]),linear(Out),linear(_1),linear(_2),linear(Off),linear(Offsets),linear(A),linear(_3),linear(Mid),linear(Word),linear(_4),linear(S1),linear(I1);mshare([[T],[In],[Out],[_1],[_2],[Off],[Offsets],[A],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]),linear(In),linear(Out),linear(_1),linear(_2),linear(Off),linear(Offsets),linear(A),linear(_3),linear(Mid),linear(Word),linear(_4),linear(S1),linear(I1))),
    I=<N,
    !,
    true((mshare([[T],[T,In],[In],[Out],[_1],[_2],[Off],[Offsets],[A],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]),linear(Out),linear(_1),linear(_2),linear(Off),linear(Offsets),linear(A),linear(_3),linear(Mid),linear(Word),linear(_4),linear(S1),linear(I1);mshare([[T],[In],[Out],[_1],[_2],[Off],[Offsets],[A],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]),linear(In),linear(Out),linear(_1),linear(_2),linear(Off),linear(Offsets),linear(A),linear(_3),linear(Mid),linear(Word),linear(_4),linear(S1),linear(I1))),
    arg(I,T,A),
    true((mshare([[T,In,A],[T,A],[In],[Out],[_1],[_2],[Off],[Offsets],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]),linear(Out),linear(_1),linear(_2),linear(Off),linear(Offsets),linear(_3),linear(Mid),linear(Word),linear(_4),linear(S1),linear(I1);mshare([[T,A],[In],[Out],[_1],[_2],[Off],[Offsets],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]),linear(In),linear(Out),linear(_1),linear(_2),linear(Off),linear(Offsets),linear(_3),linear(Mid),linear(Word),linear(_4),linear(S1),linear(I1))),
    init_var(A,S,In,_1,_3),
    true((mshare([[T,In,_1,A],[T,In,A],[T,_1,A],[T,A],[In],[Out],[_1,_3],[_2],[Off],[Offsets],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]),linear(Out),linear(_1),linear(_2),linear(Off),linear(Offsets),linear(_3),linear(Mid),linear(Word),linear(_4),linear(S1),linear(I1);mshare([[T,_1,A],[T,A],[In],[Out],[_1,_3],[_2],[Off],[Offsets],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]),linear(In),linear(Out),linear(_1),linear(_2),linear(Off),linear(Offsets),linear(_3),linear(Mid),linear(Word),linear(_4),linear(S1),linear(I1))),
    incl(A,In,Mid),
    true((mshare([[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,A],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,Mid],[Out],[_1,_3],[_2],[Off],[Offsets],[Word],[_4],[S1],[I1]]),ground([I,N,S]),linear(Out),linear(_2),linear(Off),linear(Offsets),linear(_3),linear(Word),linear(_4),linear(S1),linear(I1);mshare([[T,_1,A],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,Mid],[Out],[_1,_3],[_2],[Off],[Offsets],[Word],[_4],[S1],[I1]]),ground([I,N,S]),linear(Out),linear(_2),linear(Off),linear(Offsets),linear(_3),linear(Word),linear(_4),linear(S1),linear(I1))),
    make_word(A,Off,Word),
    true((mshare([[T,In,_1,A,Mid],[T,In,_1,A,Mid,Word],[T,In,A,Mid],[T,In,A,Mid,Word],[T,_1,A],[T,_1,A,Mid],[T,_1,A,Mid,Word],[T,_1,A,Word],[T,A],[T,A,Mid],[T,A,Mid,Word],[T,A,Word],[In,Mid],[Out],[_1,_3],[_2],[Off],[Off,Word],[Offsets],[_4],[S1],[I1]]),ground([I,N,S]),linear(Out),linear(_2),linear(Off),linear(Offsets),linear(_3),linear(_4),linear(S1),linear(I1);mshare([[T,_1,A],[T,_1,A,Mid],[T,_1,A,Mid,Word],[T,_1,A,Word],[T,A],[T,A,Mid],[T,A,Mid,Word],[T,A,Word],[In,Mid],[Out],[_1,_3],[_2],[Off],[Off,Word],[Offsets],[_4],[S1],[I1]]),ground([I,N,S]),linear(Out),linear(_2),linear(Off),linear(Offsets),linear(_3),linear(_4),linear(S1),linear(I1))),
    'C'(_3,move(Word,[h+S]),_4),
    true((mshare([[T,In,_1,A,_3,Mid,Word],[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,A],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Word],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,Mid],[Out],[_1,Off,_3,Word],[_1,_3,_4],[_2],[Off],[Offsets],[S1],[I1]]),ground([I,N,S]),linear(Out),linear(_2),linear(Off),linear(Offsets),linear(_4),linear(S1),linear(I1);mshare([[T,_1,A],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Word],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,Mid],[Out],[_1,Off,_3,Word],[_1,_3,_4],[_2],[Off],[Offsets],[S1],[I1]]),ground([I,N,S]),linear(Out),linear(_2),linear(Off),linear(Offsets),linear(_4),linear(S1),linear(I1))),
    S1 is S+1,
    true((mshare([[T,In,_1,A,_3,Mid,Word],[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,A],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Word],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,Mid],[Out],[_1,Off,_3,Word],[_1,_3,_4],[_2],[Off],[Offsets],[I1]]),ground([I,N,S,S1]),linear(Out),linear(_2),linear(Off),linear(Offsets),linear(_4),linear(I1);mshare([[T,_1,A],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Word],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,Mid],[Out],[_1,Off,_3,Word],[_1,_3,_4],[_2],[Off],[Offsets],[I1]]),ground([I,N,S,S1]),linear(Out),linear(_2),linear(Off),linear(Offsets),linear(_4),linear(I1))),
    I1 is I+1,
    true((mshare([[T,In,_1,A,_3,Mid,Word],[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,A],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Word],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,Mid],[Out],[_1,Off,_3,Word],[_1,_3,_4],[_2],[Off],[Offsets]]),ground([I,N,S,S1,I1]),linear(Out),linear(_2),linear(Off),linear(Offsets),linear(_4);mshare([[T,_1,A],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Word],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,Mid],[Out],[_1,Off,_3,Word],[_1,_3,_4],[_2],[Off],[Offsets]]),ground([I,N,S,S1,I1]),linear(Out),linear(_2),linear(Off),linear(Offsets),linear(_4))),
    make_slots(I1,N,T,S1,Offsets,Mid,Out,_4,_2),
    true((
        mshare([[T,In,Out,_1,A,_3,Mid,Word],[T,In,Out,_1,A,_3,Mid,Word,_4],[T,In,Out,_1,A,_3,Mid,_4],[T,In,Out,_1,A,Mid],[T,In,Out,A,Mid],[T,Out,_1,A],[T,Out,_1,A,_3,Mid,Word],[T,Out,_1,A,_3,Mid,Word,_4],[T,Out,_1,A,_3,Mid,_4],[T,Out,_1,A,_3,Word],[T,Out,_1,A,_3,Word,_4],[T,Out,_1,A,_3,_4],[T,Out,_1,A,Mid],[T,Out,A],[T,Out,A,Mid],[T,_1,A],[T,_1,A,_3,Word],[T,_1,A,_3,Word,_4],[T,_1,A,_3,_4],[T,A],[In,Out,Mid],[_1,_2,_3,_4],[_1,Off,_3,Word],[_1,Offsets,_3,_4],[Off],[Offsets]]),
        ground([I,N,S,S1,I1]),
        linear(_2),
        linear(Off)
    )).

:- true pred init_var(V,I,In,_1,_2)
   : ( mshare([[V],[In],[_1],[_2]]),
       ground([I]), linear(In), linear(_1), linear(_2) )
   => ( mshare([[V],[V,_1],[In],[_1,_2]]),
        ground([I]), linear(In), linear(_1), linear(_2) ).

:- true pred init_var(V,I,In,_1,_2)
   : ( mshare([[V],[V,In],[In],[_1],[_2]]),
       ground([I]), linear(_1), linear(_2) )
   => ( mshare([[V],[V,In],[V,In,_1],[V,_1],[In],[_1,_2]]),
        ground([I]), linear(_1), linear(_2) ).

init_var(V,I,In,_1,_2) :-
    true((mshare([[V],[V,In],[In],[_1],[_2]]),ground([I]),linear(_1),linear(_2);mshare([[V],[In],[_1],[_2]]),ground([I]),linear(In),linear(_1),linear(_2))),
    var(V),
    true((mshare([[V],[V,In],[In],[_1],[_2]]),ground([I]),linear(V),linear(_1),linear(_2);mshare([[V],[In],[_1],[_2]]),ground([I]),linear(V),linear(In),linear(_1),linear(_2))),
    'init_var/5/1/$disj/1'(V,In),
    !,
    true((mshare([[V],[V,In],[In],[_1],[_2]]),ground([I]),linear(V),linear(_1),linear(_2);mshare([[V],[In],[_1],[_2]]),ground([I]),linear(V),linear(In),linear(_1),linear(_2))),
    'C'(_1,move(tvar^(h+I),V),_2),
    true((mshare([[V,In,_1],[V,_1],[In],[_1,_2]]),ground([I]),linear(V),linear(_1),linear(_2);mshare([[V,_1],[In],[_1,_2]]),ground([I]),linear(V),linear(In),linear(_1),linear(_2))).
init_var(V,_1,In,_2,_3) :-
    true((mshare([[V],[V,In],[In],[_2],[_3]]),ground([_1]),linear(_2),linear(_3);mshare([[V],[In],[_2],[_3]]),ground([_1]),linear(In),linear(_2),linear(_3))),
    var(V),
    true((mshare([[V],[V,In],[In],[_2],[_3]]),ground([_1]),linear(V),linear(_2),linear(_3);mshare([[V],[In],[_2],[_3]]),ground([_1]),linear(V),linear(In),linear(_2),linear(_3))),
    myin(V,In),
    !,
    true((mshare([[V],[V,In],[In],[_2],[_3]]),ground([_1]),linear(V),linear(_2),linear(_3);mshare([[V],[In],[_2],[_3]]),ground([_1]),linear(V),linear(In),linear(_2),linear(_3))),
    _3=_2,
    true((mshare([[V],[V,In],[In],[_2,_3]]),ground([_1]),linear(V),linear(_2),linear(_3);mshare([[V],[In],[_2,_3]]),ground([_1]),linear(V),linear(In),linear(_2),linear(_3))).
init_var(V,_1,_2,_3,_4) :-
    true((mshare([[V],[V,_2],[_2],[_3],[_4]]),ground([_1]),linear(_3),linear(_4);mshare([[V],[_2],[_3],[_4]]),ground([_1]),linear(_2),linear(_3),linear(_4))),
    nonvar(V),
    !,
    true((mshare([[V],[V,_2],[_2],[_3],[_4]]),ground([_1]),linear(_3),linear(_4);mshare([[V],[_2],[_3],[_4]]),ground([_1]),linear(_2),linear(_3),linear(_4))),
    _4=_3,
    true((mshare([[V],[V,_2],[_2],[_3,_4]]),ground([_1]),linear(_3),linear(_4);mshare([[V],[_2],[_3,_4]]),ground([_1]),linear(_2),linear(_3),linear(_4))).

:- true pred 'init_var/5/1/$disj/1'(V,In)
   : ( mshare([[V],[V,In],[In]]),
       linear(V) )
   => ( mshare([[V],[V,In],[In]]),
        linear(V) ).

:- true pred 'init_var/5/1/$disj/1'(V,In)
   : ( mshare([[V],[In]]),
       linear(V), linear(In) )
   => ( mshare([[V],[In]]),
        linear(V), linear(In) ).

'init_var/5/1/$disj/1'(V,In) :-
    true((mshare([[V],[V,In],[In]]),linear(V);mshare([[V],[In]]),linear(V),linear(In))),
    myin(V,In),
    !,
    true((mshare([[V],[V,In],[In]]),linear(V);mshare([[V],[In]]),linear(V),linear(In))),
    fail,
    true(fails(_)).
'init_var/5/1/$disj/1'(V,In).

:- true pred make_word(C,Off,V)
   : ( mshare([[C],[Off],[V]]),
       linear(Off), linear(V) )
   => ( mshare([[C],[C,V],[Off],[Off,V]]),
        linear(Off) ).

make_word(C,Off,Tag^(h+Off)) :-
    true((
        mshare([[C],[Off],[Tag]]),
        linear(Off),
        linear(Tag)
    )),
    my_compound(C),
    !,
    true((
        mshare([[C],[Off],[Tag]]),
        linear(Off),
        linear(Tag)
    )),
    termtag(C,Tag),
    true((
        mshare([[C],[Off]]),
        ground([Tag]),
        linear(Off)
    )).
make_word(V,_1,V) :-
    true((
        mshare([[V],[_1]]),
        linear(_1)
    )),
    var(V),
    !,
    true((
        mshare([[V],[_1]]),
        linear(V),
        linear(_1)
    )).
make_word(A,_1,tatm^A) :-
    true((
        mshare([[A],[_1]]),
        linear(_1)
    )),
    atomic(A),
    !,
    true((
        mshare([[_1]]),
        ground([A]),
        linear(_1)
    )).

:- true pred size(T,_1,_2)
   : ( mshare([[T],[_2]]),
       ground([_1]), linear(_2) )
   => ( mshare([[T]]),
        ground([_1,_2]) ).

:- true pred size(T,_1,_2)
   : ( (_1=0),
       mshare([[T],[_2]]),
       linear(_2) )
   => ( mshare([[T]]),
        ground([_2]) ).

size(T,_1,_2) :-
    true((
        mshare([[T],[_2],[_3],[N],[_4],[_5]]),
        ground([_1]),
        linear(_2),
        linear(_3),
        linear(N),
        linear(_4),
        linear(_5)
    )),
    structure(T),
    !,
    true((
        mshare([[T],[_2],[_3],[N],[_4],[_5]]),
        ground([_1]),
        linear(_2),
        linear(_3),
        linear(N),
        linear(_4),
        linear(_5)
    )),
    functor(T,_3,N),
    true((
        mshare([[T],[_2],[_4],[_5]]),
        ground([_1,_3,N]),
        linear(_2),
        linear(_4),
        linear(_5)
    )),
    add(1,_1,_4),
    true((
        mshare([[T],[_2],[_5]]),
        ground([_1,_3,N,_4]),
        linear(_2),
        linear(_5)
    )),
    add(N,_4,_5),
    true((
        mshare([[T],[_2]]),
        ground([_1,_3,N,_4,_5]),
        linear(_2)
    )),
    size_args(1,N,T,_5,_2),
    true((
        mshare([[T]]),
        ground([_1,_2,_3,N,_4,_5])
    )).
size(T,_1,_2) :-
    true((
        mshare([[T],[_2],[_3]]),
        ground([_1]),
        linear(_2),
        linear(_3)
    )),
    cons(T),
    !,
    true((
        mshare([[T],[_2],[_3]]),
        ground([_1]),
        linear(_2),
        linear(_3)
    )),
    add(2,_1,_3),
    true((
        mshare([[T],[_2]]),
        ground([_1,_3]),
        linear(_2)
    )),
    size_args(1,2,T,_3,_2),
    true((
        mshare([[T]]),
        ground([_1,_2,_3])
    )).
size(T,_1,_2) :-
    true((
        mshare([[T],[_2]]),
        ground([_1]),
        linear(_2)
    )),
    atomic(T),
    !,
    true((
        mshare([[_2]]),
        ground([T,_1]),
        linear(_2)
    )),
    _2=_1,
    true(ground([T,_1,_2])).
size(T,_1,_2) :-
    true((
        mshare([[T],[_2]]),
        ground([_1]),
        linear(_2)
    )),
    var(T),
    !,
    true((
        mshare([[T],[_2]]),
        ground([_1]),
        linear(T),
        linear(_2)
    )),
    _2=_1,
    true((
        mshare([[T]]),
        ground([_1,_2]),
        linear(T)
    )).

:- true pred size_args(I,N,_1,_2,_3)
   : ( mshare([[_1],[_3]]),
       ground([I,N,_2]), linear(_3) )
   => ( mshare([[_1]]),
        ground([I,N,_2,_3]) ).

:- true pred size_args(I,N,_1,_2,_3)
   : ( (I=1), (N=2),
       mshare([[_1],[_3]]),
       ground([_2]), linear(_3) )
   => ( mshare([[_1]]),
        ground([_2,_3]) ).

:- true pred size_args(I,N,_1,_2,_3)
   : ( (I=1),
       mshare([[_1],[_3]]),
       ground([N,_2]), linear(_3) )
   => ( mshare([[_1]]),
        ground([N,_2,_3]) ).

size_args(I,N,_1,_2,_3) :-
    true((
        mshare([[_1],[_3]]),
        ground([I,N,_2]),
        linear(_3)
    )),
    I>N,
    !,
    true((
        mshare([[_1],[_3]]),
        ground([I,N,_2]),
        linear(_3)
    )),
    _3=_2,
    true((
        mshare([[_1]]),
        ground([I,N,_2,_3])
    )).
size_args(I,N,T,_1,_2) :-
    true((
        mshare([[T],[_2],[A],[_3],[I1]]),
        ground([I,N,_1]),
        linear(_2),
        linear(A),
        linear(_3),
        linear(I1)
    )),
    I=<N,
    !,
    true((
        mshare([[T],[_2],[A],[_3],[I1]]),
        ground([I,N,_1]),
        linear(_2),
        linear(A),
        linear(_3),
        linear(I1)
    )),
    arg(I,T,A),
    true((
        mshare([[T,A],[_2],[_3],[I1]]),
        ground([I,N,_1]),
        linear(_2),
        linear(_3),
        linear(I1)
    )),
    unify:size(A,_1,_3),
    true((
        mshare([[T,A],[_2],[I1]]),
        ground([I,N,_1,_3]),
        linear(_2),
        linear(I1)
    )),
    I1 is I+1,
    true((
        mshare([[T,A],[_2]]),
        ground([I,N,_1,_3,I1]),
        linear(_2)
    )),
    size_args(I1,N,T,_3,_2),
    true((
        mshare([[T,A]]),
        ground([I,N,_1,_2,_3,I1])
    )).

:- true pred add(I,X,Y)
   : ( (I=2),
       mshare([[Y]]),
       ground([X]), linear(Y) )
   => ground([X,Y]).

:- true pred add(I,X,Y)
   : ( mshare([[Y]]),
       ground([I,X]), linear(Y) )
   => ground([I,X,Y]).

:- true pred add(I,X,Y)
   : ( (I=1),
       mshare([[Y]]),
       ground([X]), linear(Y) )
   => ground([X,Y]).

add(I,X,Y) :-
    true((
        mshare([[Y]]),
        ground([I,X]),
        linear(Y)
    )),
    Y is X+I,
    true(ground([I,X,Y])).

:- true pred myin(A,_A)
   : ( mshare([[A],[A,_A]]),
       linear(A), linear(_A) )
   => ( mshare([[A],[A,_A]]),
        linear(A), linear(_A) ).

:- true pred myin(A,_A)
   : mshare([[A],[A,_A],[_A]])
   => mshare([[A],[A,_A],[_A]]).

:- true pred myin(A,_A)
   : ( mshare([[A],[A,_A],[_A]]),
       linear(A) )
   => ( mshare([[A],[A,_A],[_A]]),
        linear(A) ).

:- true pred myin(A,_A)
   : ( mshare([[A,_A]]),
       linear(A), linear(_A) )
   => ( mshare([[A,_A]]),
        linear(A), linear(_A) ).

:- true pred myin(A,_A)
   : ( mshare([[A],[_A]]),
       linear(A), linear(_A) )
   => ( mshare([[A],[_A]]),
        linear(A), linear(_A) ).

myin(A,[B|S]) :-
    true((mshare([[A],[A,B],[A,B,S],[A,S],[B],[B,S],[S],[Order]]),linear(A),linear(Order);mshare([[A],[A,B],[A,B,S],[A,S],[B],[B,S],[S],[Order]]),linear(Order);mshare([[A],[A,B],[A,S],[Order]]),linear(A),linear(B),linear(S),linear(Order);mshare([[A],[B],[S],[Order]]),linear(A),linear(B),linear(S),linear(Order);mshare([[A,B],[A,S],[Order]]),linear(A),linear(B),linear(S),linear(Order))),
    compare(Order,A,B),
    true((mshare([[A],[A,B],[A,B,S],[A,S],[B],[B,S],[S]]),ground([Order]);mshare([[A],[A,B],[A,B,S],[A,S],[B],[B,S],[S]]),ground([Order]),linear(A);mshare([[A],[A,B],[A,S]]),ground([Order]),linear(A),linear(B),linear(S);mshare([[A],[B],[S]]),ground([Order]),linear(A),linear(B),linear(S);mshare([[A,B],[A,S]]),ground([Order]),linear(A),linear(B),linear(S))),
    in_2(Order,A,S),
    true((mshare([[A],[A,B],[A,B,S],[A,S],[B],[B,S],[S]]),ground([Order]);mshare([[A],[A,B],[A,B,S],[A,S],[B],[B,S],[S]]),ground([Order]),linear(A);mshare([[A],[A,B],[A,S]]),ground([Order]),linear(A),linear(B),linear(S);mshare([[A],[B],[S]]),ground([Order]),linear(A),linear(B),linear(S);mshare([[A,B],[A,S]]),ground([Order]),linear(A),linear(B),linear(S))).

:- true pred in_2(_A,_1,_2)
   : ( mshare([[_1],[_2]]),
       ground([_A]), linear(_1), linear(_2) )
   => ( mshare([[_1],[_2]]),
        ground([_A]), linear(_1), linear(_2) ).

:- true pred in_2(_A,_1,_2)
   : ( mshare([[_1],[_1,_2],[_2]]),
       ground([_A]), linear(_1) )
   => ( mshare([[_1],[_1,_2],[_2]]),
        ground([_A]), linear(_1) ).

:- true pred in_2(_A,_1,_2)
   : ( mshare([[_1],[_1,_2],[_2]]),
       ground([_A]) )
   => ( mshare([[_1],[_1,_2],[_2]]),
        ground([_A]) ).

:- true pred in_2(_A,_1,_2)
   : ( mshare([[_1],[_1,_2]]),
       ground([_A]), linear(_1), linear(_2) )
   => ( mshare([[_1],[_1,_2]]),
        ground([_A]), linear(_1), linear(_2) ).

in_2(=,_1,_2).
in_2(>,A,S) :-
    true((mshare([[A],[A,S]]),linear(A),linear(S);mshare([[A],[A,S],[S]]);mshare([[A],[A,S],[S]]),linear(A);mshare([[A],[S]]),linear(A),linear(S))),
    myin(A,S),
    true((mshare([[A],[A,S]]),linear(A),linear(S);mshare([[A],[A,S],[S]]);mshare([[A],[A,S],[S]]),linear(A);mshare([[A],[S]]),linear(A),linear(S))).

:- true pred incl(A,S1,S)
   : ( mshare([[A],[S1],[S]]),
       linear(A), linear(S) )
   => ( mshare([[A],[A,S],[S1,S]]),
        linear(A) ).

:- true pred incl(A,S1,S)
   : ( mshare([[A],[A,S1],[S1],[S]]),
       linear(S) )
   => mshare([[A],[A,S1,S],[A,S],[S1,S]]).

:- true pred incl(A,S1,S)
   : ( mshare([[A,S1],[S]]),
       linear(A), linear(S1), linear(S) )
   => mshare([[A,S1,S]]).

:- true pred incl(A,S1,S)
   : ( mshare([[A],[S1],[S]]),
       linear(A), linear(S1), linear(S) )
   => ( mshare([[A],[A,S],[S1,S]]),
        linear(A), linear(S) ).

:- true pred incl(A,S1,S)
   : ( mshare([[A,S1],[S1],[S]]),
       linear(S) )
   => mshare([[A,S1,S],[S1,S]]).

:- true pred incl(A,S1,S)
   : ( mshare([[A],[S1],[S]]),
       linear(S1), linear(S) )
   => mshare([[A],[A,S],[S1,S]]).

incl(A,S1,S) :-
    true((mshare([[A],[A,S1],[S1],[S]]),linear(S);mshare([[A],[S1],[S]]),linear(A),linear(S1),linear(S);mshare([[A],[S1],[S]]),linear(A),linear(S);mshare([[A],[S1],[S]]),linear(S1),linear(S);mshare([[A,S1],[S1],[S]]),linear(S);mshare([[A,S1],[S]]),linear(A),linear(S1),linear(S))),
    incl_2(S1,A,S),
    true((mshare([[A],[A,S1,S],[A,S],[S1,S]]);mshare([[A],[A,S],[S1,S]]);mshare([[A],[A,S],[S1,S]]),linear(A);mshare([[A],[A,S],[S1,S]]),linear(A),linear(S);mshare([[A,S1,S]]);mshare([[A,S1,S],[S1,S]]))).

:- true pred incl_2(_A,A,S)
   : ( mshare([[_A],[A],[S]]),
       linear(A), linear(S) )
   => ( mshare([[_A,S],[A],[A,S]]),
        linear(A) ).

:- true pred incl_2(_A,A,S)
   : ( mshare([[_A],[A],[S]]),
       linear(_A), linear(A), linear(S) )
   => ( mshare([[_A,S],[A],[A,S]]),
        linear(A), linear(S) ).

:- true pred incl_2(_A,A,S)
   : ( mshare([[_A,A],[S]]),
       linear(_A), linear(A), linear(S) )
   => mshare([[_A,A,S]]).

:- true pred incl_2(_A,A,S)
   : ( mshare([[_A,A],[A],[S]]),
       linear(_A), linear(A), linear(S) )
   => ( mshare([[_A,A,S],[A],[A,S]]),
        linear(A) ).

:- true pred incl_2(_A,A,S)
   : ( mshare([[_A],[_A,A],[S]]),
       linear(S) )
   => mshare([[_A,A,S],[_A,S]]).

:- true pred incl_2(_A,A,S)
   : ( mshare([[_A],[_A,A],[A],[S]]),
       linear(S) )
   => mshare([[_A,A,S],[_A,S],[A],[A,S]]).

:- true pred incl_2(_A,A,S)
   : ( mshare([[_A],[A],[S]]),
       linear(_A), linear(S) )
   => mshare([[_A,S],[A],[A,S]]).

incl_2([],A,[A]).
incl_2([B|S1],A,S) :-
    true((mshare([[A],[A,B],[A,B,S1],[A,S1],[S],[B],[B,S1],[S1],[Order]]),linear(S),linear(Order);mshare([[A],[A,B],[A,S1],[S],[Order]]),linear(A),linear(S),linear(B),linear(S1),linear(Order);mshare([[A],[S],[B],[B,S1],[S1],[Order]]),linear(A),linear(S),linear(Order);mshare([[A],[S],[B],[S1],[Order]]),linear(A),linear(S),linear(B),linear(S1),linear(Order);mshare([[A],[S],[B],[S1],[Order]]),linear(S),linear(B),linear(S1),linear(Order);mshare([[A,B],[A,B,S1],[A,S1],[S],[B],[B,S1],[S1],[Order]]),linear(S),linear(Order);mshare([[A,B],[A,S1],[S],[Order]]),linear(A),linear(S),linear(B),linear(S1),linear(Order))),
    compare(Order,A,B),
    true((mshare([[A],[A,B],[A,B,S1],[A,S1],[S],[B],[B,S1],[S1]]),ground([Order]),linear(S);mshare([[A],[A,B],[A,S1],[S]]),ground([Order]),linear(A),linear(S),linear(B),linear(S1);mshare([[A],[S],[B],[B,S1],[S1]]),ground([Order]),linear(A),linear(S);mshare([[A],[S],[B],[S1]]),ground([Order]),linear(A),linear(S),linear(B),linear(S1);mshare([[A],[S],[B],[S1]]),ground([Order]),linear(S),linear(B),linear(S1);mshare([[A,B],[A,B,S1],[A,S1],[S],[B],[B,S1],[S1]]),ground([Order]),linear(S);mshare([[A,B],[A,S1],[S]]),ground([Order]),linear(A),linear(S),linear(B),linear(S1))),
    incl_3(Order,A,B,S1,S),
    true((mshare([[A],[A,S],[A,S,B],[A,S,B,S1],[A,S,S1],[S,B],[S,B,S1],[S,S1]]),ground([Order]);mshare([[A],[A,S],[A,S,B],[A,S,S1]]),ground([Order]),linear(A),linear(B),linear(S1);mshare([[A],[A,S],[S,B],[S,B,S1],[S,S1]]),ground([Order]),linear(A);mshare([[A],[A,S],[S,B],[S,S1]]),ground([Order]),linear(A),linear(S),linear(B);mshare([[A],[A,S],[S,B],[S,S1]]),ground([Order]),linear(B);mshare([[A,S,B],[A,S,B,S1],[A,S,S1],[S,B],[S,B,S1],[S,S1]]),ground([Order]);mshare([[A,S,B],[A,S,S1]]),ground([Order]),linear(A),linear(B),linear(S1))).

:- true pred incl_3(_A,A,B,S1,_B)
   : ( mshare([[A],[B],[S1],[_B]]),
       ground([_A]), linear(B), linear(S1), linear(_B) )
   => ( mshare([[A],[A,_B],[B,_B],[S1,_B]]),
        ground([_A]), linear(B) ).

:- true pred incl_3(_A,A,B,S1,_B)
   : ( mshare([[A],[A,B],[A,B,S1],[A,S1],[B],[B,S1],[S1],[_B]]),
       ground([_A]), linear(_B) )
   => ( mshare([[A],[A,B,S1,_B],[A,B,_B],[A,S1,_B],[A,_B],[B,S1,_B],[B,_B],[S1,_B]]),
        ground([_A]) ).

:- true pred incl_3(_A,A,B,S1,_B)
   : ( mshare([[A],[A,B],[A,S1],[_B]]),
       ground([_A]), linear(A), linear(B), linear(S1), linear(_B) )
   => ( mshare([[A],[A,B,_B],[A,S1,_B],[A,_B]]),
        ground([_A]), linear(A), linear(B) ).

:- true pred incl_3(_A,A,B,S1,_B)
   : ( mshare([[A],[B],[S1],[_B]]),
       ground([_A]), linear(A), linear(B), linear(S1), linear(_B) )
   => ( mshare([[A],[A,_B],[B,_B],[S1,_B]]),
        ground([_A]), linear(A), linear(B), linear(_B) ).

:- true pred incl_3(_A,A,B,S1,_B)
   : ( mshare([[A],[B],[B,S1],[S1],[_B]]),
       ground([_A]), linear(A), linear(_B) )
   => ( mshare([[A],[A,_B],[B,S1,_B],[B,_B],[S1,_B]]),
        ground([_A]), linear(A) ).

:- true pred incl_3(_A,A,B,S1,_B)
   : ( mshare([[A,B],[A,S1],[_B]]),
       ground([_A]), linear(A), linear(B), linear(S1), linear(_B) )
   => ( mshare([[A,B,_B],[A,S1,_B]]),
        ground([_A]), linear(A), linear(B), linear(S1) ).

:- true pred incl_3(_A,A,B,S1,_B)
   : ( mshare([[A,B],[A,B,S1],[A,S1],[B],[B,S1],[S1],[_B]]),
       ground([_A]), linear(_B) )
   => ( mshare([[A,B,S1,_B],[A,B,_B],[A,S1,_B],[B,S1,_B],[B,_B],[S1,_B]]),
        ground([_A]) ).

incl_3(<,A,B,S1,[A,B|S1]).
incl_3(=,_1,B,S1,[B|S1]).
incl_3(>,A,B,S1,[B|S]) :-
    true((mshare([[A],[A,B],[A,B,S1],[A,S1],[B],[B,S1],[S1],[S]]),linear(S);mshare([[A],[A,B],[A,S1],[S]]),linear(A),linear(B),linear(S1),linear(S);mshare([[A],[B],[B,S1],[S1],[S]]),linear(A),linear(S);mshare([[A],[B],[S1],[S]]),linear(A),linear(B),linear(S1),linear(S);mshare([[A],[B],[S1],[S]]),linear(B),linear(S1),linear(S);mshare([[A,B],[A,B,S1],[A,S1],[B],[B,S1],[S1],[S]]),linear(S);mshare([[A,B],[A,S1],[S]]),linear(A),linear(B),linear(S1),linear(S))),
    incl_2(S1,A,S),
    true((mshare([[A],[A,B],[A,B,S1,S],[A,B,S],[A,S1,S],[A,S],[B],[B,S1,S],[S1,S]]);mshare([[A],[A,B],[A,B,S],[A,S1,S],[A,S]]),linear(A),linear(B),linear(S1);mshare([[A],[A,S],[B],[B,S1,S],[S1,S]]),linear(A);mshare([[A],[A,S],[B],[S1,S]]),linear(A),linear(B),linear(S);mshare([[A],[A,S],[B],[S1,S]]),linear(B);mshare([[A,B],[A,B,S1,S],[A,B,S],[A,S1,S],[B],[B,S1,S],[S1,S]]);mshare([[A,B],[A,B,S],[A,S1,S]]),linear(A),linear(B),linear(S1))).

:- true pred my_compound(X)
   : mshare([[X]])
   => mshare([[X]]).

:- true pred my_compound(X)
   : ( mshare([[X]]),
       linear(X) )
   => ( mshare([[X]]),
        linear(X) ).

my_compound(X) :-
    true((mshare([[X]]);mshare([[X]]),linear(X))),
    nonvar(X),
    true((mshare([[X]]);mshare([[X]]),linear(X))),
    'my_compound/1/1/$disj/1'(X),
    true((mshare([[X]]);mshare([[X]]),linear(X))).

:- true pred 'my_compound/1/1/$disj/1'(X)
   : mshare([[X]])
   => mshare([[X]]).

:- true pred 'my_compound/1/1/$disj/1'(X)
   : ( mshare([[X]]),
       linear(X) )
   => ( mshare([[X]]),
        linear(X) ).

'my_compound/1/1/$disj/1'(X) :-
    true((mshare([[X]]);mshare([[X]]),linear(X))),
    atomic(X),
    !,
    true(ground([X])),
    fail,
    true(fails(_)).
'my_compound/1/1/$disj/1'(X).

:- true pred cons(X)
   : mshare([[X]])
   => mshare([[X]]).

:- true pred cons(X)
   : ( mshare([[X]]),
       linear(X) )
   => ( mshare([[X]]),
        linear(X) ).

cons(X) :-
    true((mshare([[X],[_1],[_2]]),linear(X),linear(_1),linear(_2);mshare([[X],[_1],[_2]]),linear(_1),linear(_2))),
    nonvar(X),
    true((mshare([[X],[_1],[_2]]),linear(X),linear(_1),linear(_2);mshare([[X],[_1],[_2]]),linear(_1),linear(_2))),
    X=[_1|_2],
    true((mshare([[X,_1],[X,_1,_2],[X,_2]]);mshare([[X,_1],[X,_2]]),linear(X),linear(_1),linear(_2))).

:- true pred structure(X)
   : mshare([[X]])
   => mshare([[X]]).

:- true pred structure(X)
   : ( mshare([[X]]),
       linear(X) )
   => ( mshare([[X]]),
        linear(X) ).

structure(X) :-
    true((mshare([[X]]);mshare([[X]]),linear(X))),
    my_compound(X),
    true((mshare([[X]]);mshare([[X]]),linear(X))),
    'structure/1/1/$disj/1'(X),
    true((mshare([[X]]);mshare([[X]]),linear(X))).

:- true pred 'structure/1/1/$disj/1'(X)
   : mshare([[X]])
   => mshare([[X]]).

:- true pred 'structure/1/1/$disj/1'(X)
   : ( mshare([[X]]),
       linear(X) )
   => ( mshare([[X]]),
        linear(X) ).

'structure/1/1/$disj/1'(X) :-
    true((mshare([[X],[_1],[_2]]),linear(X),linear(_1),linear(_2);mshare([[X],[_1],[_2]]),linear(_1),linear(_2))),
    X=[_1|_2],
    !,
    true((mshare([[X,_1],[X,_1,_2],[X,_2]]);mshare([[X,_1],[X,_2]]),linear(X),linear(_1),linear(_2))),
    fail,
    true(fails(_)).
'structure/1/1/$disj/1'(X).

:- true pred termtag(T,_A)
   : ( mshare([[T],[_A]]),
       linear(_A) )
   => ( mshare([[T]]),
        ground([_A]) ).

:- true pred termtag(T,_A)
   : ( mshare([[T],[_A]]),
       linear(T), linear(_A) )
   => ( mshare([[T]]),
        ground([_A]) ).

termtag(T,tstr) :-
    true((mshare([[T]]);mshare([[T]]),linear(T))),
    structure(T),
    true((mshare([[T]]);mshare([[T]]),linear(T))).
termtag(T,tlst) :-
    true((mshare([[T]]);mshare([[T]]),linear(T))),
    cons(T),
    true((mshare([[T]]);mshare([[T]]),linear(T))).
termtag(T,tatm) :-
    true((mshare([[T]]);mshare([[T]]),linear(T))),
    atomic(T),
    true(ground([T])).
termtag(T,tvar) :-
    true((mshare([[T]]);mshare([[T]]),linear(T))),
    var(T),
    true((
        mshare([[T]]),
        linear(T)
    )).


