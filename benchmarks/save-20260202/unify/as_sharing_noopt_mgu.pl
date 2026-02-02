:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(unify,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(mshare([[_X]])),
    main(_X),
    true(ground([_X])).

:- true pred main(Size)
   : mshare([[Size]])
   => ground([Size]).

main(Size) :-
    true(mshare([[Size],[X],[Code],[_Y]])),
    u(X,[1,_Y],[X],Code),
    true(mshare([[Size],[X,Code],[X,Code,_Y],[Code],[Code,_Y],[_Y]])),
    unify:size(Code,0,Size),
    true((
        mshare([[X,Code],[X,Code,_Y],[Code],[Code,_Y],[_Y]]),
        ground([Size])
    )).

:- true pred u(X,T,In,Code)
   : ( (T=[1,_A]), (In=[X]),
       mshare([[X],[Code],[_A]]) )
   => mshare([[X,Code],[X,Code,_A],[Code],[Code,_A],[_A]]).

u(X,T,In,Code) :-
    true(mshare([[X,In],[T],[Code],[_1]])),
    unify(X,T,In,_1,Code,[]),
    true(mshare([[X,T,In,Code,_1],[X,In,Code,_1],[T],[T,Code],[T,Code,_1],[T,_1],[Code],[Code,_1]])).

:- true pred unify(X,T,In,Out,_1,_2)
   : ( (_2=[]),
       mshare([[X,In],[T],[Out],[_1]]) )
   => mshare([[X,T,In,Out,_1],[X,In,Out,_1],[T],[T,Out],[T,Out,_1],[T,_1],[Out,_1],[_1]]).

unify(X,T,In,Out,_1,_2) :-
    true((
        mshare([[X,In],[T],[Out],[_1]]),
        ground([_2])
    )),
    'unify/6/1/$disj/1'(X,In),
    !,
    true((
        mshare([[X,In],[T],[Out],[_1]]),
        ground([_2])
    )),
    uninit(X,T,In,Out,_1,_2),
    true((
        mshare([[X,T,In,Out,_1],[X,In,Out,_1],[T],[T,Out],[T,Out,_1],[T,_1],[_1]]),
        ground([_2])
    )).
unify(X,T,In,Out,_1,_2) :-
    true((
        mshare([[X,In],[T],[Out],[_1],[_3]]),
        ground([_2])
    )),
    myin(X,In),
    !,
    true((
        mshare([[X,In],[T],[Out],[_1],[_3]]),
        ground([_2])
    )),
    init(X,T,In,Out,nonlast,_3,_1,_2),
    true((
        mshare([[X,T,In,Out,_1],[X,T,In,Out,_1,_3],[X,In,Out,_1],[X,In,Out,_1,_3],[T],[T,Out,_1],[T,Out,_1,_3],[T,_1],[T,_1,_3],[T,_3],[Out,_1],[Out,_1,_3],[_1],[_1,_3],[_3]]),
        ground([_2])
    )).

:- true pred 'unify/6/1/$disj/1'(X,In)
   : mshare([[X,In]])
   => mshare([[X,In]]).

'unify/6/1/$disj/1'(X,In) :-
    true(mshare([[X,In]])),
    myin(X,In),
    !,
    true(mshare([[X,In]])),
    fail,
    true(fails(_)).
'unify/6/1/$disj/1'(X,In).

:- true pred uninit(X,T,In,Out,_1,_2)
   : ( mshare([[X,In],[T],[Out],[_1]]),
       ground([_2]) )
   => ( mshare([[X,T,In,Out,_1],[X,In,Out,_1],[T],[T,Out],[T,Out,_1],[T,_1],[_1]]),
        ground([_2]) ).

uninit(X,T,In,Out,_1,_2) :-
    true((
        mshare([[X,In],[T],[Out],[_1],[_3],[Tag],[_4],[Mid],[_5]]),
        ground([_2])
    )),
    my_compound(T),
    !,
    true((
        mshare([[X,In],[T],[Out],[_1],[_3],[Tag],[_4],[Mid],[_5]]),
        ground([_2])
    )),
    'C'(_1,move(Tag^h,X),_3),
    true((
        mshare([[X,In,_1],[X,In,_1,_3],[X,In,_1,_3,Tag],[X,In,_1,Tag],[T],[Out],[_1,_3],[_1,_3,Tag],[_1,Tag],[_4],[Mid],[_5]]),
        ground([_2])
    )),
    termtag(T,Tag),
    true((
        mshare([[X,In,_1],[X,In,_1,_3],[T],[Out],[_1,_3],[_4],[Mid],[_5]]),
        ground([_2,Tag])
    )),
    unify_block(nonlast,T,_4,In,Mid,_5,_3,_2),
    true((
        mshare([[X,T,In,_1,_3,Mid],[X,T,In,_1,_3,Mid,_5],[X,T,In,_1,Mid],[X,In,_1,_3,Mid],[X,In,_1,_3,Mid,_5],[X,In,_1,Mid],[T],[T,_1,_3],[T,_1,_3,Mid],[T,_1,_3,Mid,_5],[T,_1,_3,_5],[T,Mid],[Out],[_1,_3],[_1,_3,_5],[_5]]),
        ground([_2,Tag,_4])
    )),
    incl(X,Mid,Out),
    true((
        mshare([[X,T,In,Out,_1,_3,Mid],[X,T,In,Out,_1,_3,Mid,_5],[X,T,In,Out,_1,Mid],[X,In,Out,_1,_3,Mid],[X,In,Out,_1,_3,Mid,_5],[X,In,Out,_1,Mid],[T],[T,Out,_1,_3,Mid],[T,Out,_1,_3,Mid,_5],[T,Out,Mid],[T,_1,_3],[T,_1,_3,_5],[_1,_3],[_1,_3,_5],[_5]]),
        ground([_2,Tag,_4])
    )).
uninit(X,T,In,Out,_1,_2) :-
    true((
        mshare([[X,In],[T],[Out],[_1]]),
        ground([_2])
    )),
    atomic(T),
    !,
    true((
        mshare([[X,In],[Out],[_1]]),
        ground([T,_2])
    )),
    'C'(_1,move(tatm^T,X),_2),
    true((
        mshare([[X,In,_1],[Out]]),
        ground([T,_2])
    )),
    incl(X,In,Out),
    true((
        mshare([[X,In,Out,_1]]),
        ground([T,_2])
    )).
uninit(X,T,In,Out,_1,_2) :-
    true((
        mshare([[X,In],[T],[Out],[_1]]),
        ground([_2])
    )),
    var(T),
    !,
    true((
        mshare([[X,In],[T],[Out],[_1]]),
        ground([_2])
    )),
    unify_var(X,T,In,Out,_1,_2),
    true((
        mshare([[X,T,In,Out,_1],[X,In,Out,_1],[T,Out,_1],[T,_1]]),
        ground([_2])
    )).

:- true pred init(X,T,In,Out,Last,LLbls,_1,_2)
   : ( mshare([[X],[X,T],[X,T,In],[X,T,In,_1],[X,T,_1],[X,In],[X,In,_1],[X,_1],[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[LLbls],[_1],[_2]]),
       ground([Last]) )
   => ( mshare([[X,T,In,Out,LLbls,_1],[X,T,In,Out,LLbls,_1,_2],[X,T,In,Out,_1],[X,T,In,Out,_1,_2],[X,T,Out,LLbls,_1],[X,T,Out,LLbls,_1,_2],[X,T,Out,_1],[X,T,Out,_1,_2],[X,T,LLbls,_1],[X,T,LLbls,_1,_2],[X,T,_1],[X,T,_1,_2],[X,In,Out,LLbls,_1],[X,In,Out,LLbls,_1,_2],[X,In,Out,_1],[X,In,Out,_1,_2],[X,Out,LLbls,_1],[X,Out,LLbls,_1,_2],[X,Out,_1],[X,Out,_1,_2],[X,LLbls,_1],[X,LLbls,_1,_2],[X,_1],[X,_1,_2],[T],[T,In,Out],[T,In,Out,LLbls],[T,In,Out,LLbls,_1],[T,In,Out,LLbls,_1,_2],[T,In,Out,_1],[T,In,Out,_1,_2],[T,Out,LLbls,_1],[T,Out,LLbls,_1,_2],[T,Out,_1],[T,Out,_1,_2],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,_2],[T,_1],[T,_1,_2],[In,Out],[In,Out,LLbls],[In,Out,LLbls,_1],[In,Out,LLbls,_1,_2],[In,Out,_1],[In,Out,_1,_2],[Out,LLbls,_1],[Out,LLbls,_1,_2],[Out,_1],[Out,_1,_2],[LLbls],[LLbls,_1],[LLbls,_1,_2],[_1],[_1,_2]]),
        ground([Last]) ).

:- true pred init(X,T,In,Out,Last,LLbls,_1,_2)
   : ( (Last=nonlast),
       mshare([[X,In],[T],[Out],[LLbls],[_1]]),
       ground([_2]) )
   => ( mshare([[X,T,In,Out,LLbls,_1],[X,T,In,Out,_1],[X,In,Out,LLbls,_1],[X,In,Out,_1],[T],[T,Out,LLbls,_1],[T,Out,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[Out,LLbls,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([_2]) ).

:- true pred init(X,T,In,Out,Last,LLbls,_1,_2)
   : ( mshare([[X],[X,T],[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1]]),
       ground([Last,_2]) )
   => ( mshare([[X,T,In,Out,LLbls,_1],[X,T,In,Out,_1],[X,T,Out,LLbls,_1],[X,T,Out,_1],[X,T,LLbls,_1],[X,T,_1],[X,In,Out,LLbls,_1],[X,In,Out,_1],[X,Out,LLbls,_1],[X,Out,_1],[X,LLbls,_1],[X,_1],[T],[T,In,Out],[T,In,Out,LLbls],[T,In,Out,LLbls,_1],[T,In,Out,_1],[T,Out,LLbls,_1],[T,Out,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In,Out],[In,Out,LLbls],[In,Out,LLbls,_1],[In,Out,_1],[Out,LLbls,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([Last,_2]) ).

init(X,T,In,Out,Last,LLbls,_1,_2) :-
    true((mshare([[X],[X,T],[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[Tag],[_3],[Read],[Write]]),ground([Last,_2]);mshare([[X],[X,T],[X,T,In],[X,T,In,_1],[X,T,_1],[X,In],[X,In,_1],[X,_1],[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[LLbls],[_1],[_2],[Tag],[_3],[Read],[Write]]),ground([Last]);mshare([[X,In],[T],[Out],[LLbls],[_1],[Tag],[_3],[Read],[Write]]),ground([Last,_2]))),
    nonvar(T),
    !,
    true((mshare([[X],[X,T],[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[Tag],[_3],[Read],[Write]]),ground([Last,_2]);mshare([[X],[X,T],[X,T,In],[X,T,In,_1],[X,T,_1],[X,In],[X,In,_1],[X,_1],[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[LLbls],[_1],[_2],[Tag],[_3],[Read],[Write]]),ground([Last]);mshare([[X,In],[T],[Out],[LLbls],[_1],[Tag],[_3],[Read],[Write]]),ground([Last,_2]))),
    termtag(T,Tag),
    true((mshare([[X],[X,T],[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[_3],[Read],[Write]]),ground([Last,_2,Tag]);mshare([[X],[X,T],[X,T,In],[X,T,In,_1],[X,T,_1],[X,In],[X,In,_1],[X,_1],[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[LLbls],[_1],[_2],[_3],[Read],[Write]]),ground([Last,Tag]);mshare([[X,In],[T],[Out],[LLbls],[_1],[_3],[Read],[Write]]),ground([Last,_2,Tag]))),
    'C'(_1,deref(X),_3),
    true((mshare([[X,T,In,LLbls,_1],[X,T,In,LLbls,_1,_3],[X,T,In,_1],[X,T,In,_1,_3],[X,T,LLbls,_1],[X,T,LLbls,_1,_3],[X,T,_1],[X,T,_1,_3],[X,In,LLbls,_1],[X,In,LLbls,_1,_3],[X,In,_1],[X,In,_1,_3],[X,LLbls,_1],[X,LLbls,_1,_3],[X,_1],[X,_1,_3],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,_1,_3],[T,LLbls],[T,LLbls,_1,_3],[T,_1,_3],[In],[In,LLbls],[In,LLbls,_1,_3],[In,_1,_3],[Out],[LLbls],[LLbls,_1,_3],[_1,_3],[Read],[Write]]),ground([Last,_2,Tag]);mshare([[X,T,In,_1],[X,T,In,_1,_3],[X,T,_1],[X,T,_1,_3],[X,In,_1],[X,In,_1,_3],[X,_1],[X,_1,_3],[T],[T,In],[T,In,_1,_3],[T,_1,_3],[In],[In,_1,_3],[Out],[LLbls],[_1,_3],[_2],[Read],[Write]]),ground([Last,Tag]);mshare([[X,In,_1],[X,In,_1,_3],[T],[Out],[LLbls],[_1,_3],[Read],[Write]]),ground([Last,_2,Tag]))),
    'C'(_3,switch(Tag,X,[trail(X)|Write],Read,fail),_2),
    true((mshare([[X,T,In,LLbls,_1,_3],[X,T,In,LLbls,_1,_3,Read],[X,T,In,LLbls,_1,_3,Read,Write],[X,T,In,LLbls,_1,_3,Write],[X,T,In,_1,_3],[X,T,In,_1,_3,Read],[X,T,In,_1,_3,Read,Write],[X,T,In,_1,_3,Write],[X,T,LLbls,_1,_3],[X,T,LLbls,_1,_3,Read],[X,T,LLbls,_1,_3,Read,Write],[X,T,LLbls,_1,_3,Write],[X,T,_1,_3],[X,T,_1,_3,Read],[X,T,_1,_3,Read,Write],[X,T,_1,_3,Write],[X,In,LLbls,_1,_3],[X,In,LLbls,_1,_3,Read],[X,In,LLbls,_1,_3,Read,Write],[X,In,LLbls,_1,_3,Write],[X,In,_1,_3],[X,In,_1,_3,Read],[X,In,_1,_3,Read,Write],[X,In,_1,_3,Write],[X,LLbls,_1,_3],[X,LLbls,_1,_3,Read],[X,LLbls,_1,_3,Read,Write],[X,LLbls,_1,_3,Write],[X,_1,_3],[X,_1,_3,Read],[X,_1,_3,Read,Write],[X,_1,_3,Write],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3,Read],[T,In,LLbls,_1,_3,Read,Write],[T,In,LLbls,_1,_3,Write],[T,In,_1,_3,Read],[T,In,_1,_3,Read,Write],[T,In,_1,_3,Write],[T,LLbls],[T,LLbls,_1,_3,Read],[T,LLbls,_1,_3,Read,Write],[T,LLbls,_1,_3,Write],[T,_1,_3,Read],[T,_1,_3,Read,Write],[T,_1,_3,Write],[In],[In,LLbls],[In,LLbls,_1,_3,Read],[In,LLbls,_1,_3,Read,Write],[In,LLbls,_1,_3,Write],[In,_1,_3,Read],[In,_1,_3,Read,Write],[In,_1,_3,Write],[Out],[LLbls],[LLbls,_1,_3,Read],[LLbls,_1,_3,Read,Write],[LLbls,_1,_3,Write],[_1,_3,Read],[_1,_3,Read,Write],[_1,_3,Write]]),ground([Last,_2,Tag]);mshare([[X,T,In,_1,_2,_3],[X,T,In,_1,_2,_3,Read],[X,T,In,_1,_2,_3,Read,Write],[X,T,In,_1,_2,_3,Write],[X,T,In,_1,_3],[X,T,In,_1,_3,Read],[X,T,In,_1,_3,Read,Write],[X,T,In,_1,_3,Write],[X,T,_1,_2,_3],[X,T,_1,_2,_3,Read],[X,T,_1,_2,_3,Read,Write],[X,T,_1,_2,_3,Write],[X,T,_1,_3],[X,T,_1,_3,Read],[X,T,_1,_3,Read,Write],[X,T,_1,_3,Write],[X,In,_1,_2,_3],[X,In,_1,_2,_3,Read],[X,In,_1,_2,_3,Read,Write],[X,In,_1,_2,_3,Write],[X,In,_1,_3],[X,In,_1,_3,Read],[X,In,_1,_3,Read,Write],[X,In,_1,_3,Write],[X,_1,_2,_3],[X,_1,_2,_3,Read],[X,_1,_2,_3,Read,Write],[X,_1,_2,_3,Write],[X,_1,_3],[X,_1,_3,Read],[X,_1,_3,Read,Write],[X,_1,_3,Write],[T],[T,In],[T,In,_1,_2,_3],[T,In,_1,_2,_3,Read],[T,In,_1,_2,_3,Read,Write],[T,In,_1,_2,_3,Write],[T,In,_1,_3,Read],[T,In,_1,_3,Read,Write],[T,In,_1,_3,Write],[T,_1,_2,_3],[T,_1,_2,_3,Read],[T,_1,_2,_3,Read,Write],[T,_1,_2,_3,Write],[T,_1,_3,Read],[T,_1,_3,Read,Write],[T,_1,_3,Write],[In],[In,_1,_2,_3],[In,_1,_2,_3,Read],[In,_1,_2,_3,Read,Write],[In,_1,_2,_3,Write],[In,_1,_3,Read],[In,_1,_3,Read,Write],[In,_1,_3,Write],[Out],[LLbls],[_1,_2,_3],[_1,_2,_3,Read],[_1,_2,_3,Read,Write],[_1,_2,_3,Write],[_1,_3,Read],[_1,_3,Read,Write],[_1,_3,Write]]),ground([Last,Tag]);mshare([[X,In,_1,_3],[X,In,_1,_3,Read],[X,In,_1,_3,Read,Write],[X,In,_1,_3,Write],[T],[Out],[LLbls],[_1,_3,Read],[_1,_3,Read,Write],[_1,_3,Write]]),ground([Last,_2,Tag]))),
    unify_writemode(X,T,In,Last,LLbls,Write,[]),
    true((mshare([[X,T,In,LLbls,_1,_2,_3,Read,Write],[X,T,In,LLbls,_1,_2,_3,Write],[X,T,In,LLbls,_1,_3,Read,Write],[X,T,In,LLbls,_1,_3,Write],[X,T,In,_1,_2,_3,Read,Write],[X,T,In,_1,_2,_3,Write],[X,T,In,_1,_3,Read,Write],[X,T,In,_1,_3,Write],[X,T,LLbls,_1,_2,_3,Read,Write],[X,T,LLbls,_1,_2,_3,Write],[X,T,LLbls,_1,_3,Read,Write],[X,T,LLbls,_1,_3,Write],[X,T,_1,_2,_3,Read,Write],[X,T,_1,_2,_3,Write],[X,T,_1,_3,Read,Write],[X,T,_1,_3,Write],[X,In,LLbls,_1,_2,_3,Read,Write],[X,In,LLbls,_1,_2,_3,Write],[X,In,LLbls,_1,_3,Read,Write],[X,In,LLbls,_1,_3,Write],[X,In,_1,_2,_3,Read,Write],[X,In,_1,_2,_3,Write],[X,In,_1,_3,Read,Write],[X,In,_1,_3,Write],[X,LLbls,_1,_2,_3,Read,Write],[X,LLbls,_1,_2,_3,Write],[X,LLbls,_1,_3,Read,Write],[X,LLbls,_1,_3,Write],[X,_1,_2,_3,Read,Write],[X,_1,_2,_3,Write],[X,_1,_3,Read,Write],[X,_1,_3,Write],[T],[T,In],[T,In,LLbls,_1,_2,_3,Read,Write],[T,In,LLbls,_1,_2,_3,Write],[T,In,LLbls,_1,_3,Read,Write],[T,In,LLbls,_1,_3,Write],[T,In,_1,_2,_3],[T,In,_1,_2,_3,Read],[T,In,_1,_2,_3,Read,Write],[T,In,_1,_2,_3,Write],[T,In,_1,_3,Read],[T,In,_1,_3,Read,Write],[T,In,_1,_3,Write],[T,LLbls,_1,_2,_3,Read,Write],[T,LLbls,_1,_2,_3,Write],[T,LLbls,_1,_3,Read,Write],[T,LLbls,_1,_3,Write],[T,_1,_2,_3],[T,_1,_2,_3,Read],[T,_1,_2,_3,Read,Write],[T,_1,_2,_3,Write],[T,_1,_3,Read],[T,_1,_3,Read,Write],[T,_1,_3,Write],[In],[In,LLbls,_1,_2,_3,Read,Write],[In,LLbls,_1,_2,_3,Write],[In,LLbls,_1,_3,Read,Write],[In,LLbls,_1,_3,Write],[In,_1,_2,_3],[In,_1,_2,_3,Read],[In,_1,_2,_3,Read,Write],[In,_1,_2,_3,Write],[In,_1,_3,Read],[In,_1,_3,Read,Write],[In,_1,_3,Write],[Out],[LLbls],[LLbls,_1,_2,_3,Read,Write],[LLbls,_1,_2,_3,Write],[LLbls,_1,_3,Read,Write],[LLbls,_1,_3,Write],[_1,_2,_3],[_1,_2,_3,Read],[_1,_2,_3,Read,Write],[_1,_2,_3,Write],[_1,_3,Read],[_1,_3,Read,Write],[_1,_3,Write]]),ground([Last,Tag]);mshare([[X,T,In,LLbls,_1,_3,Read,Write],[X,T,In,LLbls,_1,_3,Write],[X,T,In,_1,_3,Read,Write],[X,T,In,_1,_3,Write],[X,T,LLbls,_1,_3,Read,Write],[X,T,LLbls,_1,_3,Write],[X,T,_1,_3,Read,Write],[X,T,_1,_3,Write],[X,In,LLbls,_1,_3,Read,Write],[X,In,LLbls,_1,_3,Write],[X,In,_1,_3,Read,Write],[X,In,_1,_3,Write],[X,LLbls,_1,_3,Read,Write],[X,LLbls,_1,_3,Write],[X,_1,_3,Read,Write],[X,_1,_3,Write],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3,Read],[T,In,LLbls,_1,_3,Read,Write],[T,In,LLbls,_1,_3,Write],[T,In,_1,_3,Read],[T,In,_1,_3,Read,Write],[T,In,_1,_3,Write],[T,LLbls],[T,LLbls,_1,_3,Read],[T,LLbls,_1,_3,Read,Write],[T,LLbls,_1,_3,Write],[T,_1,_3,Read],[T,_1,_3,Read,Write],[T,_1,_3,Write],[In],[In,LLbls],[In,LLbls,_1,_3,Read],[In,LLbls,_1,_3,Read,Write],[In,LLbls,_1,_3,Write],[In,_1,_3,Read],[In,_1,_3,Read,Write],[In,_1,_3,Write],[Out],[LLbls],[LLbls,_1,_3,Read],[LLbls,_1,_3,Read,Write],[LLbls,_1,_3,Write],[_1,_3,Read],[_1,_3,Read,Write],[_1,_3,Write]]),ground([Last,_2,Tag]);mshare([[X,T,In,LLbls,_1,_3,Read,Write],[X,T,In,LLbls,_1,_3,Write],[X,T,In,_1,_3,Read,Write],[X,T,In,_1,_3,Write],[X,In,LLbls,_1,_3,Read,Write],[X,In,LLbls,_1,_3,Write],[X,In,_1,_3,Read,Write],[X,In,_1,_3,Write],[T],[T,LLbls,_1,_3,Read,Write],[T,LLbls,_1,_3,Write],[T,_1,_3,Read,Write],[T,_1,_3,Write],[Out],[LLbls],[LLbls,_1,_3,Read,Write],[LLbls,_1,_3,Write],[_1,_3,Read],[_1,_3,Read,Write],[_1,_3,Write]]),ground([Last,_2,Tag]))),
    unify_readmode(X,T,In,Out,LLbls,Read,[]),
    true((mshare([[X,T,In,Out,LLbls,_1,_2,_3,Read,Write],[X,T,In,Out,LLbls,_1,_2,_3,Write],[X,T,In,Out,LLbls,_1,_3,Read,Write],[X,T,In,Out,LLbls,_1,_3,Write],[X,T,In,Out,_1,_2,_3,Read,Write],[X,T,In,Out,_1,_2,_3,Write],[X,T,In,Out,_1,_3,Read,Write],[X,T,In,Out,_1,_3,Write],[X,T,Out,LLbls,_1,_2,_3,Read,Write],[X,T,Out,LLbls,_1,_3,Read,Write],[X,T,Out,_1,_2,_3,Read,Write],[X,T,Out,_1,_3,Read,Write],[X,T,LLbls,_1,_2,_3,Read,Write],[X,T,LLbls,_1,_2,_3,Write],[X,T,LLbls,_1,_3,Read,Write],[X,T,LLbls,_1,_3,Write],[X,T,_1,_2,_3,Read,Write],[X,T,_1,_2,_3,Write],[X,T,_1,_3,Read,Write],[X,T,_1,_3,Write],[X,In,Out,LLbls,_1,_2,_3,Read,Write],[X,In,Out,LLbls,_1,_2,_3,Write],[X,In,Out,LLbls,_1,_3,Read,Write],[X,In,Out,LLbls,_1,_3,Write],[X,In,Out,_1,_2,_3,Read,Write],[X,In,Out,_1,_2,_3,Write],[X,In,Out,_1,_3,Read,Write],[X,In,Out,_1,_3,Write],[X,Out,LLbls,_1,_2,_3,Read,Write],[X,Out,LLbls,_1,_3,Read,Write],[X,Out,_1,_2,_3,Read,Write],[X,Out,_1,_3,Read,Write],[X,LLbls,_1,_2,_3,Read,Write],[X,LLbls,_1,_2,_3,Write],[X,LLbls,_1,_3,Read,Write],[X,LLbls,_1,_3,Write],[X,_1,_2,_3,Read,Write],[X,_1,_2,_3,Write],[X,_1,_3,Read,Write],[X,_1,_3,Write],[T],[T,In,Out],[T,In,Out,LLbls],[T,In,Out,LLbls,_1,_2,_3],[T,In,Out,LLbls,_1,_2,_3,Read],[T,In,Out,LLbls,_1,_2,_3,Read,Write],[T,In,Out,LLbls,_1,_2,_3,Write],[T,In,Out,LLbls,_1,_3,Read],[T,In,Out,LLbls,_1,_3,Read,Write],[T,In,Out,LLbls,_1,_3,Write],[T,In,Out,_1,_2,_3],[T,In,Out,_1,_2,_3,Read],[T,In,Out,_1,_2,_3,Read,Write],[T,In,Out,_1,_2,_3,Write],[T,In,Out,_1,_3,Read],[T,In,Out,_1,_3,Read,Write],[T,In,Out,_1,_3,Write],[T,Out,LLbls,_1,_2,_3,Read],[T,Out,LLbls,_1,_2,_3,Read,Write],[T,Out,LLbls,_1,_3,Read],[T,Out,LLbls,_1,_3,Read,Write],[T,Out,_1,_2,_3,Read],[T,Out,_1,_2,_3,Read,Write],[T,Out,_1,_3,Read],[T,Out,_1,_3,Read,Write],[T,LLbls],[T,LLbls,_1,_2,_3],[T,LLbls,_1,_2,_3,Read],[T,LLbls,_1,_2,_3,Read,Write],[T,LLbls,_1,_2,_3,Write],[T,LLbls,_1,_3,Read],[T,LLbls,_1,_3,Read,Write],[T,LLbls,_1,_3,Write],[T,_1,_2,_3],[T,_1,_2,_3,Read],[T,_1,_2,_3,Read,Write],[T,_1,_2,_3,Write],[T,_1,_3,Read],[T,_1,_3,Read,Write],[T,_1,_3,Write],[In,Out],[In,Out,LLbls],[In,Out,LLbls,_1,_2,_3],[In,Out,LLbls,_1,_2,_3,Read],[In,Out,LLbls,_1,_2,_3,Read,Write],[In,Out,LLbls,_1,_2,_3,Write],[In,Out,LLbls,_1,_3,Read],[In,Out,LLbls,_1,_3,Read,Write],[In,Out,LLbls,_1,_3,Write],[In,Out,_1,_2,_3],[In,Out,_1,_2,_3,Read],[In,Out,_1,_2,_3,Read,Write],[In,Out,_1,_2,_3,Write],[In,Out,_1,_3,Read],[In,Out,_1,_3,Read,Write],[In,Out,_1,_3,Write],[Out,LLbls,_1,_2,_3,Read],[Out,LLbls,_1,_2,_3,Read,Write],[Out,LLbls,_1,_3,Read],[Out,LLbls,_1,_3,Read,Write],[Out,_1,_2,_3,Read],[Out,_1,_2,_3,Read,Write],[Out,_1,_3,Read],[Out,_1,_3,Read,Write],[LLbls],[LLbls,_1,_2,_3,Read],[LLbls,_1,_2,_3,Read,Write],[LLbls,_1,_2,_3,Write],[LLbls,_1,_3,Read],[LLbls,_1,_3,Read,Write],[LLbls,_1,_3,Write],[_1,_2,_3],[_1,_2,_3,Read],[_1,_2,_3,Read,Write],[_1,_2,_3,Write],[_1,_3,Read],[_1,_3,Read,Write],[_1,_3,Write]]),ground([Last,Tag]);mshare([[X,T,In,Out,LLbls,_1,_3,Read,Write],[X,T,In,Out,LLbls,_1,_3,Write],[X,T,In,Out,_1,_3,Read,Write],[X,T,In,Out,_1,_3,Write],[X,T,Out,LLbls,_1,_3,Read,Write],[X,T,Out,_1,_3,Read,Write],[X,T,LLbls,_1,_3,Read,Write],[X,T,LLbls,_1,_3,Write],[X,T,_1,_3,Read,Write],[X,T,_1,_3,Write],[X,In,Out,LLbls,_1,_3,Read,Write],[X,In,Out,LLbls,_1,_3,Write],[X,In,Out,_1,_3,Read,Write],[X,In,Out,_1,_3,Write],[X,Out,LLbls,_1,_3,Read,Write],[X,Out,_1,_3,Read,Write],[X,LLbls,_1,_3,Read,Write],[X,LLbls,_1,_3,Write],[X,_1,_3,Read,Write],[X,_1,_3,Write],[T],[T,In,Out],[T,In,Out,LLbls],[T,In,Out,LLbls,_1,_3,Read],[T,In,Out,LLbls,_1,_3,Read,Write],[T,In,Out,LLbls,_1,_3,Write],[T,In,Out,_1,_3,Read],[T,In,Out,_1,_3,Read,Write],[T,In,Out,_1,_3,Write],[T,Out,LLbls,_1,_3,Read],[T,Out,LLbls,_1,_3,Read,Write],[T,Out,_1,_3,Read],[T,Out,_1,_3,Read,Write],[T,LLbls],[T,LLbls,_1,_3,Read],[T,LLbls,_1,_3,Read,Write],[T,LLbls,_1,_3,Write],[T,_1,_3,Read],[T,_1,_3,Read,Write],[T,_1,_3,Write],[In,Out],[In,Out,LLbls],[In,Out,LLbls,_1,_3,Read],[In,Out,LLbls,_1,_3,Read,Write],[In,Out,LLbls,_1,_3,Write],[In,Out,_1,_3,Read],[In,Out,_1,_3,Read,Write],[In,Out,_1,_3,Write],[Out,LLbls,_1,_3,Read],[Out,LLbls,_1,_3,Read,Write],[Out,_1,_3,Read],[Out,_1,_3,Read,Write],[LLbls],[LLbls,_1,_3,Read],[LLbls,_1,_3,Read,Write],[LLbls,_1,_3,Write],[_1,_3,Read],[_1,_3,Read,Write],[_1,_3,Write]]),ground([Last,_2,Tag]);mshare([[X,T,In,Out,LLbls,_1,_3,Read,Write],[X,T,In,Out,LLbls,_1,_3,Write],[X,T,In,Out,_1,_3,Read,Write],[X,T,In,Out,_1,_3,Write],[X,In,Out,LLbls,_1,_3,Read,Write],[X,In,Out,LLbls,_1,_3,Write],[X,In,Out,_1,_3,Read,Write],[X,In,Out,_1,_3,Write],[T],[T,Out,LLbls,_1,_3,Read],[T,Out,LLbls,_1,_3,Read,Write],[T,Out,_1,_3,Read],[T,Out,_1,_3,Read,Write],[T,LLbls],[T,LLbls,_1,_3,Read],[T,LLbls,_1,_3,Read,Write],[T,LLbls,_1,_3,Write],[T,_1,_3,Read],[T,_1,_3,Read,Write],[T,_1,_3,Write],[Out,LLbls,_1,_3,Read],[Out,LLbls,_1,_3,Read,Write],[Out,_1,_3,Read],[Out,_1,_3,Read,Write],[LLbls],[LLbls,_1,_3,Read],[LLbls,_1,_3,Read,Write],[LLbls,_1,_3,Write],[_1,_3,Read],[_1,_3,Read,Write],[_1,_3,Write]]),ground([Last,_2,Tag]))).
init(X,T,In,Out,_1,_2,_3,_4) :-
    true((mshare([[X],[X,T],[X,T,In],[X,T,In,_2],[X,T,In,_2,_3],[X,T,In,_3],[X,T,_2],[X,T,_2,_3],[X,T,_3],[X,In],[X,In,_2],[X,In,_2,_3],[X,In,_3],[X,_2],[X,_2,_3],[X,_3],[T],[T,In],[T,In,_2],[T,In,_2,_3],[T,In,_3],[T,_2],[T,_2,_3],[T,_3],[In],[In,_2],[In,_2,_3],[In,_3],[Out],[_2],[_2,_3],[_3]]),ground([_1,_4]);mshare([[X],[X,T],[X,T,In],[X,T,In,_3],[X,T,_3],[X,In],[X,In,_3],[X,_3],[T],[T,In],[T,In,_3],[T,_3],[In],[In,_3],[Out],[_2],[_3],[_4]]),ground([_1]);mshare([[X,In],[T],[Out],[_2],[_3]]),ground([_1,_4]))),
    var(T),
    !,
    true((mshare([[X],[X,T],[X,T,In],[X,T,In,_2],[X,T,In,_2,_3],[X,T,In,_3],[X,T,_2],[X,T,_2,_3],[X,T,_3],[X,In],[X,In,_2],[X,In,_2,_3],[X,In,_3],[X,_2],[X,_2,_3],[X,_3],[T],[T,In],[T,In,_2],[T,In,_2,_3],[T,In,_3],[T,_2],[T,_2,_3],[T,_3],[In],[In,_2],[In,_2,_3],[In,_3],[Out],[_2],[_2,_3],[_3]]),ground([_1,_4]);mshare([[X],[X,T],[X,T,In],[X,T,In,_3],[X,T,_3],[X,In],[X,In,_3],[X,_3],[T],[T,In],[T,In,_3],[T,_3],[In],[In,_3],[Out],[_2],[_3],[_4]]),ground([_1]);mshare([[X,In],[T],[Out],[_2],[_3]]),ground([_1,_4]))),
    unify_var(X,T,In,Out,_3,_4),
    true((mshare([[X,T,In,Out,_2,_3],[X,T,In,Out,_3],[X,T,Out,_2,_3],[X,T,Out,_3],[X,T,_2,_3],[X,T,_3],[X,In,Out,_2,_3],[X,In,Out,_3],[X,Out,_2,_3],[X,Out,_3],[X,_2,_3],[X,_3],[T,In,Out,_2,_3],[T,In,Out,_3],[T,Out,_2,_3],[T,Out,_3],[T,_2,_3],[T,_3],[In,Out],[In,Out,_2],[_2]]),ground([_1,_4]);mshare([[X,T,In,Out,_3],[X,T,In,Out,_3,_4],[X,T,Out,_3],[X,T,Out,_3,_4],[X,T,_3],[X,T,_3,_4],[X,In,Out,_3],[X,In,Out,_3,_4],[X,Out,_3],[X,Out,_3,_4],[X,_3],[X,_3,_4],[T,In,Out,_3],[T,In,Out,_3,_4],[T,Out,_3],[T,Out,_3,_4],[T,_3],[T,_3,_4],[In,Out],[In,Out,_3,_4],[_2],[_3,_4]]),ground([_1]);mshare([[X,T,In,Out,_3],[X,In,Out,_3],[T,Out,_3],[T,_3],[_2]]),ground([_1,_4]))).

:- true pred unify_var(X,Y,In,Out,_1,_2)
   : mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1],[_2]])
   => mshare([[X,Y,In,Out,_1],[X,Y,In,Out,_1,_2],[X,Y,Out,_1],[X,Y,Out,_1,_2],[X,Y,_1],[X,Y,_1,_2],[X,In,Out,_1],[X,In,Out,_1,_2],[X,Out,_1],[X,Out,_1,_2],[X,_1],[X,_1,_2],[Y,In,Out,_1],[Y,In,Out,_1,_2],[Y,Out,_1],[Y,Out,_1,_2],[Y,_1],[Y,_1,_2],[In,Out],[In,Out,_1,_2],[_1,_2]]).

:- true pred unify_var(X,Y,In,Out,_1,_2)
   : ( mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1]]),
       ground([_2]) )
   => ( mshare([[X,Y,In,Out,_1],[X,Y,Out,_1],[X,Y,_1],[X,In,Out,_1],[X,Out,_1],[X,_1],[Y,In,Out,_1],[Y,Out,_1],[Y,_1],[In,Out]]),
        ground([_2]) ).

:- true pred unify_var(X,Y,In,Out,_1,_2)
   : ( mshare([[X,In],[Y],[Out],[_1]]),
       ground([_2]) )
   => ( mshare([[X,Y,In,Out,_1],[X,In,Out,_1],[Y,Out,_1],[Y,_1]]),
        ground([_2]) ).

unify_var(X,Y,In,In,_1,_2) :-
    true((mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[_1]]),ground([_2]);mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[_1],[_2]]);mshare([[X,In],[Y],[_1]]),ground([_2]))),
    myin(X,In),
    true((mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[_1]]),ground([_2]);mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[_1],[_2]]);mshare([[X,In],[Y],[_1]]),ground([_2]))),
    myin(Y,In),
    !,
    true((mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[_1]]),ground([_2]);mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[_1],[_2]]);mshare([[X,In],[Y],[_1]]),ground([_2]))),
    'C'(_1,unify(X,Y,fail),_2),
    true((mshare([[X,Y,In,_1],[X,Y,In,_1,_2],[X,Y,_1],[X,Y,_1,_2],[X,In,_1],[X,In,_1,_2],[X,_1],[X,_1,_2],[Y,In,_1],[Y,In,_1,_2],[Y,_1],[Y,_1,_2],[In],[In,_1,_2],[_1,_2]]);mshare([[X,Y,In,_1],[X,Y,_1],[X,In,_1],[X,_1],[Y,In,_1],[Y,_1],[In]]),ground([_2]);mshare([[X,Y,In,_1],[X,In,_1],[Y,_1]]),ground([_2]))).
unify_var(X,Y,In,Out,_1,_2) :-
    true((mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1]]),ground([_2]);mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1],[_2]]);mshare([[X,In],[Y],[Out],[_1]]),ground([_2]))),
    myin(X,In),
    true((mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1]]),ground([_2]);mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1],[_2]]);mshare([[X,In],[Y],[Out],[_1]]),ground([_2]))),
    'unify_var/6/2/$disj/1'(Y,In),
    !,
    true((mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1]]),ground([_2]);mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1],[_2]]);mshare([[X,In],[Y],[Out],[_1]]),ground([_2]))),
    'C'(_1,move(X,Y),_2),
    true((mshare([[X,Y,In,_1],[X,Y,In,_1,_2],[X,Y,_1],[X,Y,_1,_2],[X,In,_1],[X,In,_1,_2],[X,_1],[X,_1,_2],[Y,In,_1],[Y,In,_1,_2],[Y,_1],[Y,_1,_2],[In],[In,_1,_2],[Out],[_1,_2]]);mshare([[X,Y,In,_1],[X,Y,_1],[X,In,_1],[X,_1],[Y,In,_1],[Y,_1],[In],[Out]]),ground([_2]);mshare([[X,Y,In,_1],[X,In,_1],[Y,_1],[Out]]),ground([_2]))),
    incl(Y,In,Out),
    true((mshare([[X,Y,In,Out,_1],[X,Y,In,Out,_1,_2],[X,Y,Out,_1],[X,Y,Out,_1,_2],[X,Y,_1],[X,Y,_1,_2],[X,In,Out,_1],[X,In,Out,_1,_2],[X,_1],[X,_1,_2],[Y,In,Out,_1],[Y,In,Out,_1,_2],[Y,Out,_1],[Y,Out,_1,_2],[Y,_1],[Y,_1,_2],[In,Out],[In,Out,_1,_2],[_1,_2]]);mshare([[X,Y,In,Out,_1],[X,Y,Out,_1],[X,Y,_1],[X,In,Out,_1],[X,_1],[Y,In,Out,_1],[Y,Out,_1],[Y,_1],[In,Out]]),ground([_2]);mshare([[X,Y,In,Out,_1],[X,In,Out,_1],[Y,Out,_1],[Y,_1]]),ground([_2]))).
unify_var(X,Y,In,Out,_1,_2) :-
    true((mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1]]),ground([_2]);mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1],[_2]]);mshare([[X,In],[Y],[Out],[_1]]),ground([_2]))),
    'unify_var/6/3/$disj/1'(X,In),
    true((mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1]]),ground([_2]);mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1],[_2]]);mshare([[X,In],[Y],[Out],[_1]]),ground([_2]))),
    myin(Y,In),
    !,
    true((mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1]]),ground([_2]);mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1],[_2]]);mshare([[X,In],[Y],[Out],[_1]]),ground([_2]))),
    'C'(_1,move(Y,X),_2),
    true((mshare([[X,Y,In,_1],[X,Y,In,_1,_2],[X,Y,_1],[X,Y,_1,_2],[X,In,_1],[X,In,_1,_2],[X,_1],[X,_1,_2],[Y,In,_1],[Y,In,_1,_2],[Y,_1],[Y,_1,_2],[In],[In,_1,_2],[Out],[_1,_2]]);mshare([[X,Y,In,_1],[X,Y,_1],[X,In,_1],[X,_1],[Y,In,_1],[Y,_1],[In],[Out]]),ground([_2]);mshare([[X,Y,In,_1],[X,In,_1],[Y,_1],[Out]]),ground([_2]))),
    incl(X,In,Out),
    true((mshare([[X,Y,In,Out,_1],[X,Y,In,Out,_1,_2],[X,Y,Out,_1],[X,Y,Out,_1,_2],[X,Y,_1],[X,Y,_1,_2],[X,In,Out,_1],[X,In,Out,_1,_2],[X,Out,_1],[X,Out,_1,_2],[X,_1],[X,_1,_2],[Y,In,Out,_1],[Y,In,Out,_1,_2],[Y,_1],[Y,_1,_2],[In,Out],[In,Out,_1,_2],[_1,_2]]);mshare([[X,Y,In,Out,_1],[X,Y,Out,_1],[X,Y,_1],[X,In,Out,_1],[X,Out,_1],[X,_1],[Y,In,Out,_1],[Y,_1],[In,Out]]),ground([_2]);mshare([[X,Y,In,Out,_1],[X,In,Out,_1],[Y,_1]]),ground([_2]))).
unify_var(X,Y,In,Out,_1,_2) :-
    true((mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1],[_2],[_3],[_4],[_5],[Mid]]);mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1],[_3],[_4],[_5],[Mid]]),ground([_2]);mshare([[X,In],[Y],[Out],[_1],[_3],[_4],[_5],[Mid]]),ground([_2]))),
    'unify_var/6/4/$disj/1'(X,In),
    true((mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1],[_2],[_3],[_4],[_5],[Mid]]);mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1],[_3],[_4],[_5],[Mid]]),ground([_2]);mshare([[X,In],[Y],[Out],[_1],[_3],[_4],[_5],[Mid]]),ground([_2]))),
    'unify_var/6/4/$disj/2'(Y,In),
    !,
    true((mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1],[_2],[_3],[_4],[_5],[Mid]]);mshare([[X],[X,Y],[X,Y,In],[X,Y,In,_1],[X,Y,_1],[X,In],[X,In,_1],[X,_1],[Y],[Y,In],[Y,In,_1],[Y,_1],[In],[In,_1],[Out],[_1],[_3],[_4],[_5],[Mid]]),ground([_2]);mshare([[X,In],[Y],[Out],[_1],[_3],[_4],[_5],[Mid]]),ground([_2]))),
    'C'(_1,move(tvar^h,X),_3),
    true((mshare([[X,Y,In,_1],[X,Y,In,_1,_3],[X,Y,_1],[X,Y,_1,_3],[X,In,_1],[X,In,_1,_3],[X,_1],[X,_1,_3],[Y],[Y,In],[Y,In,_1,_3],[Y,_1,_3],[In],[In,_1,_3],[Out],[_1,_3],[_2],[_4],[_5],[Mid]]);mshare([[X,Y,In,_1],[X,Y,In,_1,_3],[X,Y,_1],[X,Y,_1,_3],[X,In,_1],[X,In,_1,_3],[X,_1],[X,_1,_3],[Y],[Y,In],[Y,In,_1,_3],[Y,_1,_3],[In],[In,_1,_3],[Out],[_1,_3],[_4],[_5],[Mid]]),ground([_2]);mshare([[X,In,_1],[X,In,_1,_3],[Y],[Out],[_1,_3],[_4],[_5],[Mid]]),ground([_2]))),
    'C'(_3,move(tvar^h,Y),_4),
    true((mshare([[X,Y,In,_1,_3],[X,Y,In,_1,_3,_4],[X,Y,_1,_3],[X,Y,_1,_3,_4],[X,In,_1],[X,In,_1,_3,_4],[X,_1],[X,_1,_3,_4],[Y,In,_1,_3],[Y,In,_1,_3,_4],[Y,_1,_3],[Y,_1,_3,_4],[In],[In,_1,_3,_4],[Out],[_1,_3,_4],[_2],[_5],[Mid]]);mshare([[X,Y,In,_1,_3],[X,Y,In,_1,_3,_4],[X,Y,_1,_3],[X,Y,_1,_3,_4],[X,In,_1],[X,In,_1,_3,_4],[X,_1],[X,_1,_3,_4],[Y,In,_1,_3],[Y,In,_1,_3,_4],[Y,_1,_3],[Y,_1,_3,_4],[In],[In,_1,_3,_4],[Out],[_1,_3,_4],[_5],[Mid]]),ground([_2]);mshare([[X,Y,In,_1,_3],[X,Y,In,_1,_3,_4],[X,In,_1],[X,In,_1,_3,_4],[Y,_1,_3],[Y,_1,_3,_4],[Out],[_1,_3,_4],[_5],[Mid]]),ground([_2]))),
    'C'(_4,add(1,h),_5),
    true((mshare([[X,Y,In,_1,_3],[X,Y,In,_1,_3,_4,_5],[X,Y,_1,_3],[X,Y,_1,_3,_4,_5],[X,In,_1],[X,In,_1,_3,_4,_5],[X,_1],[X,_1,_3,_4,_5],[Y,In,_1,_3],[Y,In,_1,_3,_4,_5],[Y,_1,_3],[Y,_1,_3,_4,_5],[In],[In,_1,_3,_4,_5],[Out],[_1,_3,_4,_5],[_2],[Mid]]);mshare([[X,Y,In,_1,_3],[X,Y,In,_1,_3,_4,_5],[X,Y,_1,_3],[X,Y,_1,_3,_4,_5],[X,In,_1],[X,In,_1,_3,_4,_5],[X,_1],[X,_1,_3,_4,_5],[Y,In,_1,_3],[Y,In,_1,_3,_4,_5],[Y,_1,_3],[Y,_1,_3,_4,_5],[In],[In,_1,_3,_4,_5],[Out],[_1,_3,_4,_5],[Mid]]),ground([_2]);mshare([[X,Y,In,_1,_3],[X,Y,In,_1,_3,_4,_5],[X,In,_1],[X,In,_1,_3,_4,_5],[Y,_1,_3],[Y,_1,_3,_4,_5],[Out],[_1,_3,_4,_5],[Mid]]),ground([_2]))),
    'C'(_5,move(Y,[h-1]),_2),
    true((mshare([[X,Y,In,_1,_2,_3,_4,_5],[X,Y,In,_1,_3,_4,_5],[X,Y,_1,_2,_3,_4,_5],[X,Y,_1,_3,_4,_5],[X,In,_1],[X,In,_1,_2,_3,_4,_5],[X,_1],[X,_1,_2,_3,_4,_5],[Y,In,_1,_2,_3,_4,_5],[Y,In,_1,_3,_4,_5],[Y,_1,_2,_3,_4,_5],[Y,_1,_3,_4,_5],[In],[In,_1,_2,_3,_4,_5],[Out],[_1,_2,_3,_4,_5],[Mid]]);mshare([[X,Y,In,_1,_3,_4,_5],[X,Y,_1,_3,_4,_5],[X,In,_1],[X,_1],[Y,In,_1,_3,_4,_5],[Y,_1,_3,_4,_5],[In],[Out],[Mid]]),ground([_2]);mshare([[X,Y,In,_1,_3,_4,_5],[X,In,_1],[Y,_1,_3,_4,_5],[Out],[Mid]]),ground([_2]))),
    incl(X,In,Mid),
    true((mshare([[X,Y,In,_1,_2,_3,_4,_5,Mid],[X,Y,In,_1,_3,_4,_5,Mid],[X,Y,_1,_2,_3,_4,_5],[X,Y,_1,_2,_3,_4,_5,Mid],[X,Y,_1,_3,_4,_5],[X,Y,_1,_3,_4,_5,Mid],[X,In,_1,_2,_3,_4,_5,Mid],[X,In,_1,Mid],[X,_1],[X,_1,_2,_3,_4,_5],[X,_1,_2,_3,_4,_5,Mid],[X,_1,Mid],[Y,In,_1,_2,_3,_4,_5,Mid],[Y,In,_1,_3,_4,_5,Mid],[Y,_1,_2,_3,_4,_5],[Y,_1,_3,_4,_5],[In,_1,_2,_3,_4,_5,Mid],[In,Mid],[Out],[_1,_2,_3,_4,_5]]);mshare([[X,Y,In,_1,_3,_4,_5,Mid],[X,Y,_1,_3,_4,_5],[X,Y,_1,_3,_4,_5,Mid],[X,In,_1,Mid],[X,_1],[X,_1,Mid],[Y,In,_1,_3,_4,_5,Mid],[Y,_1,_3,_4,_5],[In,Mid],[Out]]),ground([_2]);mshare([[X,Y,In,_1,_3,_4,_5,Mid],[X,In,_1,Mid],[Y,_1,_3,_4,_5],[Out]]),ground([_2]))),
    incl(Y,Mid,Out),
    true((mshare([[X,Y,In,Out,_1,_2,_3,_4,_5,Mid],[X,Y,In,Out,_1,_3,_4,_5,Mid],[X,Y,Out,_1,_2,_3,_4,_5],[X,Y,Out,_1,_2,_3,_4,_5,Mid],[X,Y,Out,_1,_3,_4,_5],[X,Y,Out,_1,_3,_4,_5,Mid],[X,Y,_1,_2,_3,_4,_5],[X,Y,_1,_3,_4,_5],[X,In,Out,_1,_2,_3,_4,_5,Mid],[X,In,Out,_1,Mid],[X,Out,_1,_2,_3,_4,_5,Mid],[X,Out,_1,Mid],[X,_1],[X,_1,_2,_3,_4,_5],[Y,In,Out,_1,_2,_3,_4,_5,Mid],[Y,In,Out,_1,_3,_4,_5,Mid],[Y,Out,_1,_2,_3,_4,_5],[Y,Out,_1,_3,_4,_5],[Y,_1,_2,_3,_4,_5],[Y,_1,_3,_4,_5],[In,Out,_1,_2,_3,_4,_5,Mid],[In,Out,Mid],[_1,_2,_3,_4,_5]]);mshare([[X,Y,In,Out,_1,_3,_4,_5,Mid],[X,Y,Out,_1,_3,_4,_5],[X,Y,Out,_1,_3,_4,_5,Mid],[X,Y,_1,_3,_4,_5],[X,In,Out,_1,Mid],[X,Out,_1,Mid],[X,_1],[Y,In,Out,_1,_3,_4,_5,Mid],[Y,Out,_1,_3,_4,_5],[Y,_1,_3,_4,_5],[In,Out,Mid]]),ground([_2]);mshare([[X,Y,In,Out,_1,_3,_4,_5,Mid],[X,In,Out,_1,Mid],[Y,Out,_1,_3,_4,_5],[Y,_1,_3,_4,_5]]),ground([_2]))).

:- true pred 'unify_var/6/2/$disj/1'(Y,In)
   : mshare([[Y],[Y,In],[In]])
   => mshare([[Y],[Y,In],[In]]).

:- true pred 'unify_var/6/2/$disj/1'(Y,In)
   : mshare([[Y],[In]])
   => mshare([[Y],[In]]).

'unify_var/6/2/$disj/1'(Y,In) :-
    true((mshare([[Y],[Y,In],[In]]);mshare([[Y],[In]]))),
    myin(Y,In),
    !,
    true((mshare([[Y],[Y,In],[In]]);mshare([[Y],[In]]))),
    fail,
    true(fails(_)).
'unify_var/6/2/$disj/1'(Y,In).

:- true pred 'unify_var/6/3/$disj/1'(X,In)
   : mshare([[X],[X,In],[In]])
   => mshare([[X],[X,In],[In]]).

:- true pred 'unify_var/6/3/$disj/1'(X,In)
   : mshare([[X,In]])
   => mshare([[X,In]]).

'unify_var/6/3/$disj/1'(X,In) :-
    true((mshare([[X],[X,In],[In]]);mshare([[X,In]]))),
    myin(X,In),
    !,
    true((mshare([[X],[X,In],[In]]);mshare([[X,In]]))),
    fail,
    true(fails(_)).
'unify_var/6/3/$disj/1'(X,In).

:- true pred 'unify_var/6/4/$disj/1'(X,In)
   : mshare([[X],[X,In],[In]])
   => mshare([[X],[X,In],[In]]).

:- true pred 'unify_var/6/4/$disj/1'(X,In)
   : mshare([[X,In]])
   => mshare([[X,In]]).

'unify_var/6/4/$disj/1'(X,In) :-
    true((mshare([[X],[X,In],[In]]);mshare([[X,In]]))),
    myin(X,In),
    !,
    true((mshare([[X],[X,In],[In]]);mshare([[X,In]]))),
    fail,
    true(fails(_)).
'unify_var/6/4/$disj/1'(X,In).

:- true pred 'unify_var/6/4/$disj/2'(Y,In)
   : mshare([[Y],[Y,In],[In]])
   => mshare([[Y],[Y,In],[In]]).

:- true pred 'unify_var/6/4/$disj/2'(Y,In)
   : mshare([[Y],[In]])
   => mshare([[Y],[In]]).

'unify_var/6/4/$disj/2'(Y,In) :-
    true((mshare([[Y],[Y,In],[In]]);mshare([[Y],[In]]))),
    myin(Y,In),
    !,
    true((mshare([[Y],[Y,In],[In]]);mshare([[Y],[In]]))),
    fail,
    true(fails(_)).
'unify_var/6/4/$disj/2'(Y,In).

:- true pred unify_readmode(X,T,In,Out,LLbls,_1,_2)
   : ( (_2=[]),
       mshare([[X],[X,T],[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1]]) )
   => mshare([[X],[X,T],[X,T,In,Out],[X,T,In,Out,LLbls],[X,T,In,Out,LLbls,_1],[X,T,In,Out,_1],[X,T,Out,LLbls,_1],[X,T,Out,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In,Out],[X,In,Out,LLbls],[X,In,Out,LLbls,_1],[X,In,Out,_1],[X,Out,LLbls,_1],[X,Out,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In,Out],[T,In,Out,LLbls],[T,In,Out,LLbls,_1],[T,In,Out,_1],[T,Out,LLbls,_1],[T,Out,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In,Out],[In,Out,LLbls],[In,Out,LLbls,_1],[In,Out,_1],[Out,LLbls,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]).

:- true pred unify_readmode(X,T,In,Out,LLbls,_1,_2)
   : ( (_2=[]),
       mshare([[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[T],[T,LLbls],[T,LLbls,_1],[T,_1],[Out],[LLbls],[LLbls,_1],[_1]]) )
   => mshare([[X,T,In,Out],[X,T,In,Out,LLbls],[X,T,In,Out,LLbls,_1],[X,T,In,Out,_1],[X,In,Out],[X,In,Out,LLbls],[X,In,Out,LLbls,_1],[X,In,Out,_1],[T],[T,Out,LLbls,_1],[T,Out,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[Out,LLbls,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]).

unify_readmode(X,T,In,Out,LLbls,_1,_2) :-
    true((mshare([[X],[X,T],[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[_3],[F],[N]]),ground([_2]);mshare([[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[T],[T,LLbls],[T,LLbls,_1],[T,_1],[Out],[LLbls],[LLbls,_1],[_1],[_3],[F],[N]]),ground([_2]))),
    structure(T),
    !,
    true((mshare([[X],[X,T],[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[_3],[F],[N]]),ground([_2]);mshare([[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[T],[T,LLbls],[T,LLbls,_1],[T,_1],[Out],[LLbls],[LLbls,_1],[_1],[_3],[F],[N]]),ground([_2]))),
    'C'(_1,equal([X],tatm^(F/N),fail),_3),
    true((mshare([[X,T,In,LLbls,_1],[X,T,In,LLbls,_1,_3],[X,T,In,LLbls,_1,_3,F],[X,T,In,LLbls,_1,_3,F,N],[X,T,In,LLbls,_1,_3,N],[X,T,In,LLbls,_1,F],[X,T,In,LLbls,_1,F,N],[X,T,In,LLbls,_1,N],[X,T,In,_1],[X,T,In,_1,_3],[X,T,In,_1,_3,F],[X,T,In,_1,_3,F,N],[X,T,In,_1,_3,N],[X,T,In,_1,F],[X,T,In,_1,F,N],[X,T,In,_1,N],[X,T,LLbls,_1],[X,T,LLbls,_1,_3],[X,T,LLbls,_1,_3,F],[X,T,LLbls,_1,_3,F,N],[X,T,LLbls,_1,_3,N],[X,T,LLbls,_1,F],[X,T,LLbls,_1,F,N],[X,T,LLbls,_1,N],[X,T,_1],[X,T,_1,_3],[X,T,_1,_3,F],[X,T,_1,_3,F,N],[X,T,_1,_3,N],[X,T,_1,F],[X,T,_1,F,N],[X,T,_1,N],[X,In,LLbls,_1],[X,In,LLbls,_1,_3],[X,In,LLbls,_1,_3,F],[X,In,LLbls,_1,_3,F,N],[X,In,LLbls,_1,_3,N],[X,In,LLbls,_1,F],[X,In,LLbls,_1,F,N],[X,In,LLbls,_1,N],[X,In,_1],[X,In,_1,_3],[X,In,_1,_3,F],[X,In,_1,_3,F,N],[X,In,_1,_3,N],[X,In,_1,F],[X,In,_1,F,N],[X,In,_1,N],[X,LLbls,_1],[X,LLbls,_1,_3],[X,LLbls,_1,_3,F],[X,LLbls,_1,_3,F,N],[X,LLbls,_1,_3,N],[X,LLbls,_1,F],[X,LLbls,_1,F,N],[X,LLbls,_1,N],[X,_1],[X,_1,_3],[X,_1,_3,F],[X,_1,_3,F,N],[X,_1,_3,N],[X,_1,F],[X,_1,F,N],[X,_1,N],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,LLbls,_1,_3,F],[T,In,LLbls,_1,_3,F,N],[T,In,LLbls,_1,_3,N],[T,In,LLbls,_1,F],[T,In,LLbls,_1,F,N],[T,In,LLbls,_1,N],[T,In,_1,_3],[T,In,_1,_3,F],[T,In,_1,_3,F,N],[T,In,_1,_3,N],[T,In,_1,F],[T,In,_1,F,N],[T,In,_1,N],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,F],[T,LLbls,_1,_3,F,N],[T,LLbls,_1,_3,N],[T,LLbls,_1,F],[T,LLbls,_1,F,N],[T,LLbls,_1,N],[T,_1,_3],[T,_1,_3,F],[T,_1,_3,F,N],[T,_1,_3,N],[T,_1,F],[T,_1,F,N],[T,_1,N],[In],[In,LLbls],[In,LLbls,_1,_3],[In,LLbls,_1,_3,F],[In,LLbls,_1,_3,F,N],[In,LLbls,_1,_3,N],[In,LLbls,_1,F],[In,LLbls,_1,F,N],[In,LLbls,_1,N],[In,_1,_3],[In,_1,_3,F],[In,_1,_3,F,N],[In,_1,_3,N],[In,_1,F],[In,_1,F,N],[In,_1,N],[Out],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,F],[LLbls,_1,_3,F,N],[LLbls,_1,_3,N],[LLbls,_1,F],[LLbls,_1,F,N],[LLbls,_1,N],[_1,_3],[_1,_3,F],[_1,_3,F,N],[_1,_3,N],[_1,F],[_1,F,N],[_1,N]]),ground([_2]);mshare([[X,T,In,LLbls,_1],[X,T,In,LLbls,_1,_3],[X,T,In,LLbls,_1,_3,F],[X,T,In,LLbls,_1,_3,F,N],[X,T,In,LLbls,_1,_3,N],[X,T,In,LLbls,_1,F],[X,T,In,LLbls,_1,F,N],[X,T,In,LLbls,_1,N],[X,T,In,_1],[X,T,In,_1,_3],[X,T,In,_1,_3,F],[X,T,In,_1,_3,F,N],[X,T,In,_1,_3,N],[X,T,In,_1,F],[X,T,In,_1,F,N],[X,T,In,_1,N],[X,In,LLbls,_1],[X,In,LLbls,_1,_3],[X,In,LLbls,_1,_3,F],[X,In,LLbls,_1,_3,F,N],[X,In,LLbls,_1,_3,N],[X,In,LLbls,_1,F],[X,In,LLbls,_1,F,N],[X,In,LLbls,_1,N],[X,In,_1],[X,In,_1,_3],[X,In,_1,_3,F],[X,In,_1,_3,F,N],[X,In,_1,_3,N],[X,In,_1,F],[X,In,_1,F,N],[X,In,_1,N],[T],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,F],[T,LLbls,_1,_3,F,N],[T,LLbls,_1,_3,N],[T,LLbls,_1,F],[T,LLbls,_1,F,N],[T,LLbls,_1,N],[T,_1,_3],[T,_1,_3,F],[T,_1,_3,F,N],[T,_1,_3,N],[T,_1,F],[T,_1,F,N],[T,_1,N],[Out],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,F],[LLbls,_1,_3,F,N],[LLbls,_1,_3,N],[LLbls,_1,F],[LLbls,_1,F,N],[LLbls,_1,N],[_1,_3],[_1,_3,F],[_1,_3,F,N],[_1,_3,N],[_1,F],[_1,F,N],[_1,N]]),ground([_2]))),
    functor(T,F,N),
    true((mshare([[X,T,In,LLbls,_1],[X,T,In,LLbls,_1,_3],[X,T,In,_1],[X,T,In,_1,_3],[X,T,LLbls,_1],[X,T,LLbls,_1,_3],[X,T,_1],[X,T,_1,_3],[X,In,LLbls,_1],[X,In,LLbls,_1,_3],[X,In,_1],[X,In,_1,_3],[X,LLbls,_1],[X,LLbls,_1,_3],[X,_1],[X,_1,_3],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,_1,_3],[T,LLbls],[T,LLbls,_1,_3],[T,_1,_3],[In],[In,LLbls],[In,LLbls,_1,_3],[In,_1,_3],[Out],[LLbls],[LLbls,_1,_3],[_1,_3]]),ground([_2,F,N]);mshare([[X,T,In,LLbls,_1],[X,T,In,LLbls,_1,_3],[X,T,In,_1],[X,T,In,_1,_3],[X,In,LLbls,_1],[X,In,LLbls,_1,_3],[X,In,_1],[X,In,_1,_3],[T],[T,LLbls],[T,LLbls,_1,_3],[T,_1,_3],[Out],[LLbls],[LLbls,_1,_3],[_1,_3]]),ground([_2,F,N]))),
    unify_args(1,N,T,In,Out,0,X,LLbls,_3,_2),
    true((mshare([[X,T,In,Out,LLbls,_1],[X,T,In,Out,LLbls,_1,_3],[X,T,In,Out,_1],[X,T,In,Out,_1,_3],[X,T,Out,LLbls,_1,_3],[X,T,Out,_1,_3],[X,T,LLbls,_1],[X,T,LLbls,_1,_3],[X,T,_1],[X,T,_1,_3],[X,In,Out,LLbls,_1],[X,In,Out,LLbls,_1,_3],[X,In,Out,_1],[X,In,Out,_1,_3],[X,Out,LLbls,_1,_3],[X,Out,_1,_3],[X,LLbls,_1],[X,LLbls,_1,_3],[X,_1],[X,_1,_3],[T],[T,In,Out],[T,In,Out,LLbls],[T,In,Out,LLbls,_1,_3],[T,In,Out,_1,_3],[T,Out,LLbls,_1,_3],[T,Out,_1,_3],[T,LLbls],[T,LLbls,_1,_3],[T,_1,_3],[In,Out],[In,Out,LLbls],[In,Out,LLbls,_1,_3],[In,Out,_1,_3],[Out,LLbls,_1,_3],[Out,_1,_3],[LLbls],[LLbls,_1,_3],[_1,_3]]),ground([_2,F,N]);mshare([[X,T,In,Out,LLbls,_1],[X,T,In,Out,LLbls,_1,_3],[X,T,In,Out,_1],[X,T,In,Out,_1,_3],[X,In,Out,LLbls,_1],[X,In,Out,LLbls,_1,_3],[X,In,Out,_1],[X,In,Out,_1,_3],[T],[T,Out,LLbls,_1,_3],[T,Out,_1,_3],[T,LLbls],[T,LLbls,_1,_3],[T,_1,_3],[Out,LLbls,_1,_3],[Out,_1,_3],[LLbls],[LLbls,_1,_3],[_1,_3]]),ground([_2,F,N]))).
unify_readmode(X,T,In,Out,LLbls,_1,_2) :-
    true((mshare([[X],[X,T],[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1]]),ground([_2]);mshare([[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[T],[T,LLbls],[T,LLbls,_1],[T,_1],[Out],[LLbls],[LLbls,_1],[_1]]),ground([_2]))),
    cons(T),
    !,
    true((mshare([[X],[X,T],[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1]]),ground([_2]);mshare([[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[T],[T,LLbls],[T,LLbls,_1],[T,_1],[Out],[LLbls],[LLbls,_1],[_1]]),ground([_2]))),
    unify_args(1,2,T,In,Out,-1,X,LLbls,_1,_2),
    true((mshare([[X],[X,T],[X,T,In,Out],[X,T,In,Out,LLbls],[X,T,In,Out,LLbls,_1],[X,T,In,Out,_1],[X,T,Out,LLbls,_1],[X,T,Out,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In,Out],[X,In,Out,LLbls],[X,In,Out,LLbls,_1],[X,In,Out,_1],[X,Out,LLbls,_1],[X,Out,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In,Out],[T,In,Out,LLbls],[T,In,Out,LLbls,_1],[T,In,Out,_1],[T,Out,LLbls,_1],[T,Out,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In,Out],[In,Out,LLbls],[In,Out,LLbls,_1],[In,Out,_1],[Out,LLbls,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]),ground([_2]);mshare([[X,T,In,Out],[X,T,In,Out,LLbls],[X,T,In,Out,LLbls,_1],[X,T,In,Out,_1],[X,In,Out],[X,In,Out,LLbls],[X,In,Out,LLbls,_1],[X,In,Out,_1],[T],[T,Out,LLbls,_1],[T,Out,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[Out,LLbls,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]),ground([_2]))).
unify_readmode(X,T,In,In,_1,_2,_3) :-
    true((mshare([[X],[X,T],[X,T,In],[X,T,In,_1],[X,T,In,_1,_2],[X,T,In,_2],[X,T,_1],[X,T,_1,_2],[X,T,_2],[X,In],[X,In,_1],[X,In,_1,_2],[X,In,_2],[X,_1],[X,_1,_2],[X,_2],[T],[T,In],[T,In,_1],[T,In,_1,_2],[T,In,_2],[T,_1],[T,_1,_2],[T,_2],[In],[In,_1],[In,_1,_2],[In,_2],[_1],[_1,_2],[_2]]),ground([_3]);mshare([[X,T,In],[X,T,In,_1],[X,T,In,_1,_2],[X,T,In,_2],[X,In],[X,In,_1],[X,In,_1,_2],[X,In,_2],[T],[T,_1],[T,_1,_2],[T,_2],[_1],[_1,_2],[_2]]),ground([_3]))),
    atomic(T),
    !,
    true((mshare([[X],[X,In],[X,In,_1],[X,In,_1,_2],[X,In,_2],[X,_1],[X,_1,_2],[X,_2],[In],[In,_1],[In,_1,_2],[In,_2],[_1],[_1,_2],[_2]]),ground([T,_3]);mshare([[X,In],[X,In,_1],[X,In,_1,_2],[X,In,_2],[_1],[_1,_2],[_2]]),ground([T,_3]))),
    'C'(_2,equal(X,tatm^T,fail),_3),
    true((mshare([[X,In,_1,_2],[X,In,_2],[X,_1,_2],[X,_2],[In],[In,_1],[_1]]),ground([T,_3]);mshare([[X,In,_1,_2],[X,In,_2],[_1]]),ground([T,_3]))).

:- true pred unify_args(I,N,_1,In,Out,_2,_3,_4,_5,_6)
   : ( mshare([[_1],[_1,In],[_1,In,_3],[_1,In,_3,_4],[_1,In,_3,_4,_5],[_1,In,_3,_5],[_1,In,_4],[_1,In,_4,_5],[_1,In,_5],[_1,_3],[_1,_3,_4],[_1,_3,_4,_5],[_1,_3,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In],[In,_3],[In,_3,_4],[In,_3,_4,_5],[In,_3,_5],[In,_4],[In,_4,_5],[In,_5],[Out],[_3],[_3,_4],[_3,_4,_5],[_3,_5],[_4],[_4,_5],[_5]]),
       ground([I,N,_2,_6]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_3],[_1,In,Out,_3,_4],[_1,In,Out,_3,_4,_5],[_1,In,Out,_3,_5],[_1,In,Out,_4],[_1,In,Out,_4,_5],[_1,In,Out,_5],[_1,Out,_3,_4,_5],[_1,Out,_3,_5],[_1,Out,_4,_5],[_1,Out,_5],[_1,_3],[_1,_3,_4],[_1,_3,_4,_5],[_1,_3,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In,Out],[In,Out,_3],[In,Out,_3,_4],[In,Out,_3,_4,_5],[In,Out,_3,_5],[In,Out,_4],[In,Out,_4,_5],[In,Out,_5],[Out,_3,_4,_5],[Out,_3,_5],[Out,_4,_5],[Out,_5],[_3],[_3,_4],[_3,_4,_5],[_3,_5],[_4],[_4,_5],[_5]]),
        ground([I,N,_2,_6]) ).

:- true pred unify_args(I,N,_1,In,Out,_2,_3,_4,_5,_6)
   : ( (I=1), (_2=0),
       mshare([[_1],[_1,In],[_1,In,_3],[_1,In,_3,_4],[_1,In,_3,_4,_5],[_1,In,_3,_5],[_1,In,_4],[_1,In,_4,_5],[_1,In,_5],[_1,_3],[_1,_3,_4],[_1,_3,_4,_5],[_1,_3,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In],[In,_3],[In,_3,_4],[In,_3,_4,_5],[In,_3,_5],[In,_4],[In,_4,_5],[In,_5],[Out],[_3],[_3,_4],[_3,_4,_5],[_3,_5],[_4],[_4,_5],[_5]]),
       ground([N,_6]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_3],[_1,In,Out,_3,_4],[_1,In,Out,_3,_4,_5],[_1,In,Out,_3,_5],[_1,In,Out,_4],[_1,In,Out,_4,_5],[_1,In,Out,_5],[_1,Out,_3,_4,_5],[_1,Out,_3,_5],[_1,Out,_4,_5],[_1,Out,_5],[_1,_3],[_1,_3,_4],[_1,_3,_4,_5],[_1,_3,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In,Out],[In,Out,_3],[In,Out,_3,_4],[In,Out,_3,_4,_5],[In,Out,_3,_5],[In,Out,_4],[In,Out,_4,_5],[In,Out,_5],[Out,_3,_4,_5],[Out,_3,_5],[Out,_4,_5],[Out,_5],[_3],[_3,_4],[_3,_4,_5],[_3,_5],[_4],[_4,_5],[_5]]),
        ground([N,_6]) ).

:- true pred unify_args(I,N,_1,In,Out,_2,_3,_4,_5,_6)
   : ( (I=1), (N=2), (_2= -1),
       mshare([[_1],[_1,In],[_1,In,_3],[_1,In,_3,_4],[_1,In,_3,_4,_5],[_1,In,_3,_5],[_1,In,_4],[_1,In,_4,_5],[_1,In,_5],[_1,_3],[_1,_3,_4],[_1,_3,_4,_5],[_1,_3,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In],[In,_3],[In,_3,_4],[In,_3,_4,_5],[In,_3,_5],[In,_4],[In,_4,_5],[In,_5],[Out],[_3],[_3,_4],[_3,_4,_5],[_3,_5],[_4],[_4,_5],[_5]]),
       ground([_6]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_3],[_1,In,Out,_3,_4],[_1,In,Out,_3,_4,_5],[_1,In,Out,_3,_5],[_1,In,Out,_4],[_1,In,Out,_4,_5],[_1,In,Out,_5],[_1,Out,_3,_4,_5],[_1,Out,_3,_5],[_1,Out,_4,_5],[_1,Out,_5],[_1,_3],[_1,_3,_4],[_1,_3,_4,_5],[_1,_3,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In,Out],[In,Out,_3],[In,Out,_3,_4],[In,Out,_3,_4,_5],[In,Out,_3,_5],[In,Out,_4],[In,Out,_4,_5],[In,Out,_5],[Out,_3,_4,_5],[Out,_3,_5],[Out,_4,_5],[Out,_5],[_3],[_3,_4],[_3,_4,_5],[_3,_5],[_4],[_4,_5],[_5]]),
        ground([_6]) ).

:- true pred unify_args(I,N,_1,In,Out,_2,_3,_4,_5,_6)
   : ( mshare([[_1],[_1,In],[_1,In,_3],[_1,In,_3,_4],[_1,In,_3,_4,_5],[_1,In,_3,_5],[_1,In,_4],[_1,In,_4,_5],[_1,In,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In],[In,_3],[In,_3,_4],[In,_3,_4,_5],[In,_3,_5],[In,_4],[In,_4,_5],[In,_5],[Out],[_4],[_4,_5],[_5]]),
       ground([I,N,_2,_6]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,_3],[_1,In,Out,_3,_4],[_1,In,Out,_3,_4,_5],[_1,In,Out,_3,_5],[_1,In,Out,_4],[_1,In,Out,_4,_5],[_1,In,Out,_5],[_1,Out,_4,_5],[_1,Out,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In,Out],[In,Out,_3],[In,Out,_3,_4],[In,Out,_3,_4,_5],[In,Out,_3,_5],[In,Out,_4],[In,Out,_4,_5],[In,Out,_5],[Out,_4,_5],[Out,_5],[_4],[_4,_5],[_5]]),
        ground([I,N,_2,_6]) ).

:- true pred unify_args(I,N,_1,In,Out,_2,_3,_4,_5,_6)
   : ( (I=1), (N=2), (_2= -1),
       mshare([[_1],[_1,In,_3],[_1,In,_3,_4],[_1,In,_3,_4,_5],[_1,In,_3,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In,_3],[In,_3,_4],[In,_3,_4,_5],[In,_3,_5],[Out],[_4],[_4,_5],[_5]]),
       ground([_6]) )
   => ( mshare([[_1],[_1,In,Out,_3],[_1,In,Out,_3,_4],[_1,In,Out,_3,_4,_5],[_1,In,Out,_3,_5],[_1,Out,_4,_5],[_1,Out,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In,Out,_3],[In,Out,_3,_4],[In,Out,_3,_4,_5],[In,Out,_3,_5],[Out,_4,_5],[Out,_5],[_4],[_4,_5],[_5]]),
        ground([_6]) ).

:- true pred unify_args(I,N,_1,In,Out,_2,_3,_4,_5,_6)
   : ( (I=1), (_2=0),
       mshare([[_1],[_1,In,_3],[_1,In,_3,_4],[_1,In,_3,_4,_5],[_1,In,_3,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In,_3],[In,_3,_4],[In,_3,_4,_5],[In,_3,_5],[Out],[_4],[_4,_5],[_5]]),
       ground([N,_6]) )
   => ( mshare([[_1],[_1,In,Out,_3],[_1,In,Out,_3,_4],[_1,In,Out,_3,_4,_5],[_1,In,Out,_3,_5],[_1,Out,_4,_5],[_1,Out,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In,Out,_3],[In,Out,_3,_4],[In,Out,_3,_4,_5],[In,Out,_3,_5],[Out,_4,_5],[Out,_5],[_4],[_4,_5],[_5]]),
        ground([N,_6]) ).

unify_args(I,N,_1,In,In,_2,_3,_4,_5,_6) :-
    true((mshare([[_1],[_1,In],[_1,In,_3],[_1,In,_3,_4],[_1,In,_3,_4,_5],[_1,In,_3,_5],[_1,In,_4],[_1,In,_4,_5],[_1,In,_5],[_1,_3],[_1,_3,_4],[_1,_3,_4,_5],[_1,_3,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In],[In,_3],[In,_3,_4],[In,_3,_4,_5],[In,_3,_5],[In,_4],[In,_4,_5],[In,_5],[_3],[_3,_4],[_3,_4,_5],[_3,_5],[_4],[_4,_5],[_5]]),ground([I,N,_2,_6]);mshare([[_1],[_1,In],[_1,In,_3],[_1,In,_3,_4],[_1,In,_3,_4,_5],[_1,In,_3,_5],[_1,In,_4],[_1,In,_4,_5],[_1,In,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In],[In,_3],[In,_3,_4],[In,_3,_4,_5],[In,_3,_5],[In,_4],[In,_4,_5],[In,_5],[_4],[_4,_5],[_5]]),ground([I,N,_2,_6]);mshare([[_1],[_1,In,_3],[_1,In,_3,_4],[_1,In,_3,_4,_5],[_1,In,_3,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In,_3],[In,_3,_4],[In,_3,_4,_5],[In,_3,_5],[_4],[_4,_5],[_5]]),ground([I,N,_2,_6]))),
    I>N,
    !,
    true((mshare([[_1],[_1,In],[_1,In,_3],[_1,In,_3,_4],[_1,In,_3,_4,_5],[_1,In,_3,_5],[_1,In,_4],[_1,In,_4,_5],[_1,In,_5],[_1,_3],[_1,_3,_4],[_1,_3,_4,_5],[_1,_3,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In],[In,_3],[In,_3,_4],[In,_3,_4,_5],[In,_3,_5],[In,_4],[In,_4,_5],[In,_5],[_3],[_3,_4],[_3,_4,_5],[_3,_5],[_4],[_4,_5],[_5]]),ground([I,N,_2,_6]);mshare([[_1],[_1,In],[_1,In,_3],[_1,In,_3,_4],[_1,In,_3,_4,_5],[_1,In,_3,_5],[_1,In,_4],[_1,In,_4,_5],[_1,In,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In],[In,_3],[In,_3,_4],[In,_3,_4,_5],[In,_3,_5],[In,_4],[In,_4,_5],[In,_5],[_4],[_4,_5],[_5]]),ground([I,N,_2,_6]);mshare([[_1],[_1,In,_3],[_1,In,_3,_4],[_1,In,_3,_4,_5],[_1,In,_3,_5],[_1,_4],[_1,_4,_5],[_1,_5],[In,_3],[In,_3,_4],[In,_3,_4,_5],[In,_3,_5],[_4],[_4,_5],[_5]]),ground([I,N,_2,_6]))),
    _6=_5,
    true((mshare([[_1],[_1,In],[_1,In,_3],[_1,In,_3,_4],[_1,In,_4],[_1,_3],[_1,_3,_4],[_1,_4],[In],[In,_3],[In,_3,_4],[In,_4],[_3],[_3,_4],[_4]]),ground([I,N,_2,_5,_6]);mshare([[_1],[_1,In],[_1,In,_3],[_1,In,_3,_4],[_1,In,_4],[_1,_4],[In],[In,_3],[In,_3,_4],[In,_4],[_4]]),ground([I,N,_2,_5,_6]);mshare([[_1],[_1,In,_3],[_1,In,_3,_4],[_1,_4],[In,_3],[In,_3,_4],[_4]]),ground([I,N,_2,_5,_6]))).
unify_args(I,N,T,In,Out,D,X,[_3|LLbls],_1,_2) :-
    true((mshare([[T],[T,In],[T,In,X],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,LLbls],[T,In,X,_1,LLbls],[T,In,X,_3],[T,In,X,_3,LLbls],[T,In,X,LLbls],[T,In,_1],[T,In,_1,_3],[T,In,_1,_3,LLbls],[T,In,_1,LLbls],[T,In,_3],[T,In,_3,LLbls],[T,In,LLbls],[T,X],[T,X,_1],[T,X,_1,_3],[T,X,_1,_3,LLbls],[T,X,_1,LLbls],[T,X,_3],[T,X,_3,LLbls],[T,X,LLbls],[T,_1],[T,_1,_3],[T,_1,_3,LLbls],[T,_1,LLbls],[T,_3],[T,_3,LLbls],[T,LLbls],[In],[In,X],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,LLbls],[In,X,_1,LLbls],[In,X,_3],[In,X,_3,LLbls],[In,X,LLbls],[In,_1],[In,_1,_3],[In,_1,_3,LLbls],[In,_1,LLbls],[In,_3],[In,_3,LLbls],[In,LLbls],[Out],[X],[X,_1],[X,_1,_3],[X,_1,_3,LLbls],[X,_1,LLbls],[X,_3],[X,_3,LLbls],[X,LLbls],[_1],[_1,_3],[_1,_3,LLbls],[_1,LLbls],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]);mshare([[T],[T,In],[T,In,X],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,LLbls],[T,In,X,_1,LLbls],[T,In,X,_3],[T,In,X,_3,LLbls],[T,In,X,LLbls],[T,In,_1],[T,In,_1,_3],[T,In,_1,_3,LLbls],[T,In,_1,LLbls],[T,In,_3],[T,In,_3,LLbls],[T,In,LLbls],[T,_1],[T,_1,_3],[T,_1,_3,LLbls],[T,_1,LLbls],[T,_3],[T,_3,LLbls],[T,LLbls],[In],[In,X],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,LLbls],[In,X,_1,LLbls],[In,X,_3],[In,X,_3,LLbls],[In,X,LLbls],[In,_1],[In,_1,_3],[In,_1,_3,LLbls],[In,_1,LLbls],[In,_3],[In,_3,LLbls],[In,LLbls],[Out],[_1],[_1,_3],[_1,_3,LLbls],[_1,LLbls],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]);mshare([[T],[T,In,X],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,LLbls],[T,In,X,_1,LLbls],[T,In,X,_3],[T,In,X,_3,LLbls],[T,In,X,LLbls],[T,_1],[T,_1,_3],[T,_1,_3,LLbls],[T,_1,LLbls],[T,_3],[T,_3,LLbls],[T,LLbls],[In,X],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,LLbls],[In,X,_1,LLbls],[In,X,_3],[In,X,_3,LLbls],[In,X,LLbls],[Out],[_1],[_1,_3],[_1,_3,LLbls],[_1,LLbls],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]))),
    I=N,
    !,
    true((mshare([[T],[T,In],[T,In,X],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,LLbls],[T,In,X,_1,LLbls],[T,In,X,_3],[T,In,X,_3,LLbls],[T,In,X,LLbls],[T,In,_1],[T,In,_1,_3],[T,In,_1,_3,LLbls],[T,In,_1,LLbls],[T,In,_3],[T,In,_3,LLbls],[T,In,LLbls],[T,X],[T,X,_1],[T,X,_1,_3],[T,X,_1,_3,LLbls],[T,X,_1,LLbls],[T,X,_3],[T,X,_3,LLbls],[T,X,LLbls],[T,_1],[T,_1,_3],[T,_1,_3,LLbls],[T,_1,LLbls],[T,_3],[T,_3,LLbls],[T,LLbls],[In],[In,X],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,LLbls],[In,X,_1,LLbls],[In,X,_3],[In,X,_3,LLbls],[In,X,LLbls],[In,_1],[In,_1,_3],[In,_1,_3,LLbls],[In,_1,LLbls],[In,_3],[In,_3,LLbls],[In,LLbls],[Out],[X],[X,_1],[X,_1,_3],[X,_1,_3,LLbls],[X,_1,LLbls],[X,_3],[X,_3,LLbls],[X,LLbls],[_1],[_1,_3],[_1,_3,LLbls],[_1,LLbls],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]);mshare([[T],[T,In],[T,In,X],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,LLbls],[T,In,X,_1,LLbls],[T,In,X,_3],[T,In,X,_3,LLbls],[T,In,X,LLbls],[T,In,_1],[T,In,_1,_3],[T,In,_1,_3,LLbls],[T,In,_1,LLbls],[T,In,_3],[T,In,_3,LLbls],[T,In,LLbls],[T,_1],[T,_1,_3],[T,_1,_3,LLbls],[T,_1,LLbls],[T,_3],[T,_3,LLbls],[T,LLbls],[In],[In,X],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,LLbls],[In,X,_1,LLbls],[In,X,_3],[In,X,_3,LLbls],[In,X,LLbls],[In,_1],[In,_1,_3],[In,_1,_3,LLbls],[In,_1,LLbls],[In,_3],[In,_3,LLbls],[In,LLbls],[Out],[_1],[_1,_3],[_1,_3,LLbls],[_1,LLbls],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]);mshare([[T],[T,In,X],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,LLbls],[T,In,X,_1,LLbls],[T,In,X,_3],[T,In,X,_3,LLbls],[T,In,X,LLbls],[T,_1],[T,_1,_3],[T,_1,_3,LLbls],[T,_1,LLbls],[T,_3],[T,_3,LLbls],[T,LLbls],[In,X],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,LLbls],[In,X,_1,LLbls],[In,X,_3],[In,X,_3,LLbls],[In,X,LLbls],[Out],[_1],[_1,_3],[_1,_3,LLbls],[_1,LLbls],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]))),
    unify_arg(I,T,In,Out,D,X,last,LLbls,_1,_2),
    true((mshare([[T],[T,In,Out],[T,In,Out,X,_1],[T,In,Out,X,_1,_3],[T,In,Out,X,_1,_3,LLbls],[T,In,Out,X,_1,LLbls],[T,In,Out,_1],[T,In,Out,_1,_3],[T,In,Out,_1,_3,LLbls],[T,In,Out,_1,LLbls],[T,In,Out,_3],[T,In,Out,_3,LLbls],[T,In,Out,LLbls],[T,Out,X,_1],[T,Out,X,_1,_3],[T,Out,X,_1,_3,LLbls],[T,Out,X,_1,LLbls],[T,Out,_1],[T,Out,_1,_3],[T,Out,_1,_3,LLbls],[T,Out,_1,LLbls],[T,X,_1],[T,X,_1,_3],[T,X,_1,_3,LLbls],[T,X,_1,LLbls],[T,_1],[T,_1,_3],[T,_1,_3,LLbls],[T,_1,LLbls],[T,_3],[T,_3,LLbls],[T,LLbls],[In,Out],[In,Out,X,_1],[In,Out,X,_1,_3],[In,Out,X,_1,_3,LLbls],[In,Out,X,_1,LLbls],[In,Out,_1],[In,Out,_1,_3],[In,Out,_1,_3,LLbls],[In,Out,_1,LLbls],[In,Out,_3],[In,Out,_3,LLbls],[In,Out,LLbls],[Out,X,_1],[Out,X,_1,_3],[Out,X,_1,_3,LLbls],[Out,X,_1,LLbls],[Out,_1],[Out,_1,_3],[Out,_1,_3,LLbls],[Out,_1,LLbls],[X,_1],[X,_1,_3],[X,_1,_3,LLbls],[X,_1,LLbls],[_1],[_1,_3],[_1,_3,LLbls],[_1,LLbls],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]);mshare([[T],[T,In,Out],[T,In,Out,X,_1],[T,In,Out,X,_1,_3],[T,In,Out,X,_1,_3,LLbls],[T,In,Out,X,_1,LLbls],[T,In,Out,_1],[T,In,Out,_1,_3],[T,In,Out,_1,_3,LLbls],[T,In,Out,_1,LLbls],[T,In,Out,_3],[T,In,Out,_3,LLbls],[T,In,Out,LLbls],[T,Out,_1],[T,Out,_1,_3],[T,Out,_1,_3,LLbls],[T,Out,_1,LLbls],[T,_1],[T,_1,_3],[T,_1,_3,LLbls],[T,_1,LLbls],[T,_3],[T,_3,LLbls],[T,LLbls],[In,Out],[In,Out,X,_1],[In,Out,X,_1,_3],[In,Out,X,_1,_3,LLbls],[In,Out,X,_1,LLbls],[In,Out,_1],[In,Out,_1,_3],[In,Out,_1,_3,LLbls],[In,Out,_1,LLbls],[In,Out,_3],[In,Out,_3,LLbls],[In,Out,LLbls],[Out,_1],[Out,_1,_3],[Out,_1,_3,LLbls],[Out,_1,LLbls],[_1],[_1,_3],[_1,_3,LLbls],[_1,LLbls],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]);mshare([[T],[T,In,Out,X,_1],[T,In,Out,X,_1,_3],[T,In,Out,X,_1,_3,LLbls],[T,In,Out,X,_1,LLbls],[T,Out,_1],[T,Out,_1,_3],[T,Out,_1,_3,LLbls],[T,Out,_1,LLbls],[T,_1],[T,_1,_3],[T,_1,_3,LLbls],[T,_1,LLbls],[T,_3],[T,_3,LLbls],[T,LLbls],[In,Out,X,_1],[In,Out,X,_1,_3],[In,Out,X,_1,_3,LLbls],[In,Out,X,_1,LLbls],[Out,_1],[Out,_1,_3],[Out,_1,_3,LLbls],[Out,_1,LLbls],[_1],[_1,_3],[_1,_3,LLbls],[_1,LLbls],[_3],[_3,LLbls],[LLbls]]),ground([I,N,D,_2]))).
unify_args(I,N,T,In,Out,D,X,LLbls,_1,_2) :-
    true((mshare([[T],[T,In],[T,In,X],[T,In,X,LLbls],[T,In,X,LLbls,_1],[T,In,X,_1],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,X],[T,X,LLbls],[T,X,LLbls,_1],[T,X,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,X],[In,X,LLbls],[In,X,LLbls,_1],[In,X,_1],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[X],[X,LLbls],[X,LLbls,_1],[X,_1],[LLbls],[LLbls,_1],[_1],[Mid],[_3],[_4],[I1]]),ground([I,N,D,_2]);mshare([[T],[T,In],[T,In,X],[T,In,X,LLbls],[T,In,X,LLbls,_1],[T,In,X,_1],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,X],[In,X,LLbls],[In,X,LLbls,_1],[In,X,_1],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[Mid],[_3],[_4],[I1]]),ground([I,N,D,_2]);mshare([[T],[T,In,X],[T,In,X,LLbls],[T,In,X,LLbls,_1],[T,In,X,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In,X],[In,X,LLbls],[In,X,LLbls,_1],[In,X,_1],[Out],[LLbls],[LLbls,_1],[_1],[Mid],[_3],[_4],[I1]]),ground([I,N,D,_2]))),
    I<N,
    !,
    true((mshare([[T],[T,In],[T,In,X],[T,In,X,LLbls],[T,In,X,LLbls,_1],[T,In,X,_1],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,X],[T,X,LLbls],[T,X,LLbls,_1],[T,X,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,X],[In,X,LLbls],[In,X,LLbls,_1],[In,X,_1],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[X],[X,LLbls],[X,LLbls,_1],[X,_1],[LLbls],[LLbls,_1],[_1],[Mid],[_3],[_4],[I1]]),ground([I,N,D,_2]);mshare([[T],[T,In],[T,In,X],[T,In,X,LLbls],[T,In,X,LLbls,_1],[T,In,X,_1],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,X],[In,X,LLbls],[In,X,LLbls,_1],[In,X,_1],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[Mid],[_3],[_4],[I1]]),ground([I,N,D,_2]);mshare([[T],[T,In,X],[T,In,X,LLbls],[T,In,X,LLbls,_1],[T,In,X,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In,X],[In,X,LLbls],[In,X,LLbls,_1],[In,X,_1],[Out],[LLbls],[LLbls,_1],[_1],[Mid],[_3],[_4],[I1]]),ground([I,N,D,_2]))),
    unify_arg(I,T,In,Mid,D,X,nonlast,_3,_1,_4),
    true((mshare([[T],[T,In,X,LLbls,_1,Mid],[T,In,X,LLbls,_1,Mid,_3],[T,In,X,LLbls,_1,Mid,_3,_4],[T,In,X,LLbls,_1,Mid,_4],[T,In,X,_1,Mid],[T,In,X,_1,Mid,_3],[T,In,X,_1,Mid,_3,_4],[T,In,X,_1,Mid,_4],[T,In,LLbls,_1,Mid],[T,In,LLbls,_1,Mid,_3],[T,In,LLbls,_1,Mid,_3,_4],[T,In,LLbls,_1,Mid,_4],[T,In,LLbls,Mid],[T,In,LLbls,Mid,_3],[T,In,_1,Mid],[T,In,_1,Mid,_3],[T,In,_1,Mid,_3,_4],[T,In,_1,Mid,_4],[T,In,Mid],[T,In,Mid,_3],[T,X,LLbls,_1],[T,X,LLbls,_1,Mid],[T,X,LLbls,_1,Mid,_3],[T,X,LLbls,_1,Mid,_3,_4],[T,X,LLbls,_1,Mid,_4],[T,X,LLbls,_1,_3],[T,X,LLbls,_1,_3,_4],[T,X,LLbls,_1,_4],[T,X,_1],[T,X,_1,Mid],[T,X,_1,Mid,_3],[T,X,_1,Mid,_3,_4],[T,X,_1,Mid,_4],[T,X,_1,_3],[T,X,_1,_3,_4],[T,X,_1,_4],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,Mid],[T,LLbls,_1,Mid,_3],[T,LLbls,_1,Mid,_3,_4],[T,LLbls,_1,Mid,_4],[T,LLbls,_1,_3],[T,LLbls,_1,_3,_4],[T,LLbls,_1,_4],[T,LLbls,_3],[T,_1],[T,_1,Mid],[T,_1,Mid,_3],[T,_1,Mid,_3,_4],[T,_1,Mid,_4],[T,_1,_3],[T,_1,_3,_4],[T,_1,_4],[T,_3],[In,X,LLbls,_1,Mid],[In,X,LLbls,_1,Mid,_3],[In,X,LLbls,_1,Mid,_3,_4],[In,X,LLbls,_1,Mid,_4],[In,X,_1,Mid],[In,X,_1,Mid,_3],[In,X,_1,Mid,_3,_4],[In,X,_1,Mid,_4],[In,LLbls,_1,Mid],[In,LLbls,_1,Mid,_3],[In,LLbls,_1,Mid,_3,_4],[In,LLbls,_1,Mid,_4],[In,LLbls,Mid],[In,LLbls,Mid,_3],[In,_1,Mid],[In,_1,Mid,_3],[In,_1,Mid,_3,_4],[In,_1,Mid,_4],[In,Mid],[In,Mid,_3],[Out],[X,LLbls,_1],[X,LLbls,_1,Mid],[X,LLbls,_1,Mid,_3],[X,LLbls,_1,Mid,_3,_4],[X,LLbls,_1,Mid,_4],[X,LLbls,_1,_3],[X,LLbls,_1,_3,_4],[X,LLbls,_1,_4],[X,_1],[X,_1,Mid],[X,_1,Mid,_3],[X,_1,Mid,_3,_4],[X,_1,Mid,_4],[X,_1,_3],[X,_1,_3,_4],[X,_1,_4],[LLbls],[LLbls,_1],[LLbls,_1,Mid],[LLbls,_1,Mid,_3],[LLbls,_1,Mid,_3,_4],[LLbls,_1,Mid,_4],[LLbls,_1,_3],[LLbls,_1,_3,_4],[LLbls,_1,_4],[_1],[_1,Mid],[_1,Mid,_3],[_1,Mid,_3,_4],[_1,Mid,_4],[_1,_3],[_1,_3,_4],[_1,_4],[_3],[I1]]),ground([I,N,D,_2]);mshare([[T],[T,In,X,LLbls,_1,Mid],[T,In,X,LLbls,_1,Mid,_3],[T,In,X,LLbls,_1,Mid,_3,_4],[T,In,X,LLbls,_1,Mid,_4],[T,In,X,_1,Mid],[T,In,X,_1,Mid,_3],[T,In,X,_1,Mid,_3,_4],[T,In,X,_1,Mid,_4],[T,In,LLbls,_1,Mid],[T,In,LLbls,_1,Mid,_3],[T,In,LLbls,_1,Mid,_3,_4],[T,In,LLbls,_1,Mid,_4],[T,In,LLbls,Mid],[T,In,LLbls,Mid,_3],[T,In,_1,Mid],[T,In,_1,Mid,_3],[T,In,_1,Mid,_3,_4],[T,In,_1,Mid,_4],[T,In,Mid],[T,In,Mid,_3],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,Mid],[T,LLbls,_1,Mid,_3],[T,LLbls,_1,Mid,_3,_4],[T,LLbls,_1,Mid,_4],[T,LLbls,_1,_3],[T,LLbls,_1,_3,_4],[T,LLbls,_1,_4],[T,LLbls,_3],[T,_1],[T,_1,Mid],[T,_1,Mid,_3],[T,_1,Mid,_3,_4],[T,_1,Mid,_4],[T,_1,_3],[T,_1,_3,_4],[T,_1,_4],[T,_3],[In,X,LLbls,_1,Mid],[In,X,LLbls,_1,Mid,_3],[In,X,LLbls,_1,Mid,_3,_4],[In,X,LLbls,_1,Mid,_4],[In,X,_1,Mid],[In,X,_1,Mid,_3],[In,X,_1,Mid,_3,_4],[In,X,_1,Mid,_4],[In,LLbls,_1,Mid],[In,LLbls,_1,Mid,_3],[In,LLbls,_1,Mid,_3,_4],[In,LLbls,_1,Mid,_4],[In,LLbls,Mid],[In,LLbls,Mid,_3],[In,_1,Mid],[In,_1,Mid,_3],[In,_1,Mid,_3,_4],[In,_1,Mid,_4],[In,Mid],[In,Mid,_3],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Mid],[LLbls,_1,Mid,_3],[LLbls,_1,Mid,_3,_4],[LLbls,_1,Mid,_4],[LLbls,_1,_3],[LLbls,_1,_3,_4],[LLbls,_1,_4],[_1],[_1,Mid],[_1,Mid,_3],[_1,Mid,_3,_4],[_1,Mid,_4],[_1,_3],[_1,_3,_4],[_1,_4],[_3],[I1]]),ground([I,N,D,_2]);mshare([[T],[T,In,X,LLbls,_1,Mid],[T,In,X,LLbls,_1,Mid,_3],[T,In,X,LLbls,_1,Mid,_3,_4],[T,In,X,LLbls,_1,Mid,_4],[T,In,X,_1,Mid],[T,In,X,_1,Mid,_3],[T,In,X,_1,Mid,_3,_4],[T,In,X,_1,Mid,_4],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,Mid],[T,LLbls,_1,Mid,_3],[T,LLbls,_1,Mid,_3,_4],[T,LLbls,_1,Mid,_4],[T,LLbls,_1,_3],[T,LLbls,_1,_3,_4],[T,LLbls,_1,_4],[T,LLbls,_3],[T,_1],[T,_1,Mid],[T,_1,Mid,_3],[T,_1,Mid,_3,_4],[T,_1,Mid,_4],[T,_1,_3],[T,_1,_3,_4],[T,_1,_4],[T,_3],[In,X,LLbls,_1,Mid],[In,X,LLbls,_1,Mid,_3],[In,X,LLbls,_1,Mid,_3,_4],[In,X,LLbls,_1,Mid,_4],[In,X,_1,Mid],[In,X,_1,Mid,_3],[In,X,_1,Mid,_3,_4],[In,X,_1,Mid,_4],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Mid],[LLbls,_1,Mid,_3],[LLbls,_1,Mid,_3,_4],[LLbls,_1,Mid,_4],[LLbls,_1,_3],[LLbls,_1,_3,_4],[LLbls,_1,_4],[_1],[_1,Mid],[_1,Mid,_3],[_1,Mid,_3,_4],[_1,Mid,_4],[_1,_3],[_1,_3,_4],[_1,_4],[_3],[I1]]),ground([I,N,D,_2]))),
    I1 is I+1,
    true((mshare([[T],[T,In,X,LLbls,_1,Mid],[T,In,X,LLbls,_1,Mid,_3],[T,In,X,LLbls,_1,Mid,_3,_4],[T,In,X,LLbls,_1,Mid,_4],[T,In,X,_1,Mid],[T,In,X,_1,Mid,_3],[T,In,X,_1,Mid,_3,_4],[T,In,X,_1,Mid,_4],[T,In,LLbls,_1,Mid],[T,In,LLbls,_1,Mid,_3],[T,In,LLbls,_1,Mid,_3,_4],[T,In,LLbls,_1,Mid,_4],[T,In,LLbls,Mid],[T,In,LLbls,Mid,_3],[T,In,_1,Mid],[T,In,_1,Mid,_3],[T,In,_1,Mid,_3,_4],[T,In,_1,Mid,_4],[T,In,Mid],[T,In,Mid,_3],[T,X,LLbls,_1],[T,X,LLbls,_1,Mid],[T,X,LLbls,_1,Mid,_3],[T,X,LLbls,_1,Mid,_3,_4],[T,X,LLbls,_1,Mid,_4],[T,X,LLbls,_1,_3],[T,X,LLbls,_1,_3,_4],[T,X,LLbls,_1,_4],[T,X,_1],[T,X,_1,Mid],[T,X,_1,Mid,_3],[T,X,_1,Mid,_3,_4],[T,X,_1,Mid,_4],[T,X,_1,_3],[T,X,_1,_3,_4],[T,X,_1,_4],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,Mid],[T,LLbls,_1,Mid,_3],[T,LLbls,_1,Mid,_3,_4],[T,LLbls,_1,Mid,_4],[T,LLbls,_1,_3],[T,LLbls,_1,_3,_4],[T,LLbls,_1,_4],[T,LLbls,_3],[T,_1],[T,_1,Mid],[T,_1,Mid,_3],[T,_1,Mid,_3,_4],[T,_1,Mid,_4],[T,_1,_3],[T,_1,_3,_4],[T,_1,_4],[T,_3],[In,X,LLbls,_1,Mid],[In,X,LLbls,_1,Mid,_3],[In,X,LLbls,_1,Mid,_3,_4],[In,X,LLbls,_1,Mid,_4],[In,X,_1,Mid],[In,X,_1,Mid,_3],[In,X,_1,Mid,_3,_4],[In,X,_1,Mid,_4],[In,LLbls,_1,Mid],[In,LLbls,_1,Mid,_3],[In,LLbls,_1,Mid,_3,_4],[In,LLbls,_1,Mid,_4],[In,LLbls,Mid],[In,LLbls,Mid,_3],[In,_1,Mid],[In,_1,Mid,_3],[In,_1,Mid,_3,_4],[In,_1,Mid,_4],[In,Mid],[In,Mid,_3],[Out],[X,LLbls,_1],[X,LLbls,_1,Mid],[X,LLbls,_1,Mid,_3],[X,LLbls,_1,Mid,_3,_4],[X,LLbls,_1,Mid,_4],[X,LLbls,_1,_3],[X,LLbls,_1,_3,_4],[X,LLbls,_1,_4],[X,_1],[X,_1,Mid],[X,_1,Mid,_3],[X,_1,Mid,_3,_4],[X,_1,Mid,_4],[X,_1,_3],[X,_1,_3,_4],[X,_1,_4],[LLbls],[LLbls,_1],[LLbls,_1,Mid],[LLbls,_1,Mid,_3],[LLbls,_1,Mid,_3,_4],[LLbls,_1,Mid,_4],[LLbls,_1,_3],[LLbls,_1,_3,_4],[LLbls,_1,_4],[_1],[_1,Mid],[_1,Mid,_3],[_1,Mid,_3,_4],[_1,Mid,_4],[_1,_3],[_1,_3,_4],[_1,_4],[_3]]),ground([I,N,D,_2,I1]);mshare([[T],[T,In,X,LLbls,_1,Mid],[T,In,X,LLbls,_1,Mid,_3],[T,In,X,LLbls,_1,Mid,_3,_4],[T,In,X,LLbls,_1,Mid,_4],[T,In,X,_1,Mid],[T,In,X,_1,Mid,_3],[T,In,X,_1,Mid,_3,_4],[T,In,X,_1,Mid,_4],[T,In,LLbls,_1,Mid],[T,In,LLbls,_1,Mid,_3],[T,In,LLbls,_1,Mid,_3,_4],[T,In,LLbls,_1,Mid,_4],[T,In,LLbls,Mid],[T,In,LLbls,Mid,_3],[T,In,_1,Mid],[T,In,_1,Mid,_3],[T,In,_1,Mid,_3,_4],[T,In,_1,Mid,_4],[T,In,Mid],[T,In,Mid,_3],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,Mid],[T,LLbls,_1,Mid,_3],[T,LLbls,_1,Mid,_3,_4],[T,LLbls,_1,Mid,_4],[T,LLbls,_1,_3],[T,LLbls,_1,_3,_4],[T,LLbls,_1,_4],[T,LLbls,_3],[T,_1],[T,_1,Mid],[T,_1,Mid,_3],[T,_1,Mid,_3,_4],[T,_1,Mid,_4],[T,_1,_3],[T,_1,_3,_4],[T,_1,_4],[T,_3],[In,X,LLbls,_1,Mid],[In,X,LLbls,_1,Mid,_3],[In,X,LLbls,_1,Mid,_3,_4],[In,X,LLbls,_1,Mid,_4],[In,X,_1,Mid],[In,X,_1,Mid,_3],[In,X,_1,Mid,_3,_4],[In,X,_1,Mid,_4],[In,LLbls,_1,Mid],[In,LLbls,_1,Mid,_3],[In,LLbls,_1,Mid,_3,_4],[In,LLbls,_1,Mid,_4],[In,LLbls,Mid],[In,LLbls,Mid,_3],[In,_1,Mid],[In,_1,Mid,_3],[In,_1,Mid,_3,_4],[In,_1,Mid,_4],[In,Mid],[In,Mid,_3],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Mid],[LLbls,_1,Mid,_3],[LLbls,_1,Mid,_3,_4],[LLbls,_1,Mid,_4],[LLbls,_1,_3],[LLbls,_1,_3,_4],[LLbls,_1,_4],[_1],[_1,Mid],[_1,Mid,_3],[_1,Mid,_3,_4],[_1,Mid,_4],[_1,_3],[_1,_3,_4],[_1,_4],[_3]]),ground([I,N,D,_2,I1]);mshare([[T],[T,In,X,LLbls,_1,Mid],[T,In,X,LLbls,_1,Mid,_3],[T,In,X,LLbls,_1,Mid,_3,_4],[T,In,X,LLbls,_1,Mid,_4],[T,In,X,_1,Mid],[T,In,X,_1,Mid,_3],[T,In,X,_1,Mid,_3,_4],[T,In,X,_1,Mid,_4],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,Mid],[T,LLbls,_1,Mid,_3],[T,LLbls,_1,Mid,_3,_4],[T,LLbls,_1,Mid,_4],[T,LLbls,_1,_3],[T,LLbls,_1,_3,_4],[T,LLbls,_1,_4],[T,LLbls,_3],[T,_1],[T,_1,Mid],[T,_1,Mid,_3],[T,_1,Mid,_3,_4],[T,_1,Mid,_4],[T,_1,_3],[T,_1,_3,_4],[T,_1,_4],[T,_3],[In,X,LLbls,_1,Mid],[In,X,LLbls,_1,Mid,_3],[In,X,LLbls,_1,Mid,_3,_4],[In,X,LLbls,_1,Mid,_4],[In,X,_1,Mid],[In,X,_1,Mid,_3],[In,X,_1,Mid,_3,_4],[In,X,_1,Mid,_4],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Mid],[LLbls,_1,Mid,_3],[LLbls,_1,Mid,_3,_4],[LLbls,_1,Mid,_4],[LLbls,_1,_3],[LLbls,_1,_3,_4],[LLbls,_1,_4],[_1],[_1,Mid],[_1,Mid,_3],[_1,Mid,_3,_4],[_1,Mid,_4],[_1,_3],[_1,_3,_4],[_1,_4],[_3]]),ground([I,N,D,_2,I1]))),
    unify_args(I1,N,T,Mid,Out,D,X,LLbls,_4,_2),
    true((mshare([[T],[T,In,Out,X,LLbls,_1,Mid],[T,In,Out,X,LLbls,_1,Mid,_3],[T,In,Out,X,LLbls,_1,Mid,_3,_4],[T,In,Out,X,LLbls,_1,Mid,_4],[T,In,Out,X,_1,Mid],[T,In,Out,X,_1,Mid,_3],[T,In,Out,X,_1,Mid,_3,_4],[T,In,Out,X,_1,Mid,_4],[T,In,Out,LLbls,_1,Mid],[T,In,Out,LLbls,_1,Mid,_3],[T,In,Out,LLbls,_1,Mid,_3,_4],[T,In,Out,LLbls,_1,Mid,_4],[T,In,Out,LLbls,Mid],[T,In,Out,LLbls,Mid,_3],[T,In,Out,_1,Mid],[T,In,Out,_1,Mid,_3],[T,In,Out,_1,Mid,_3,_4],[T,In,Out,_1,Mid,_4],[T,In,Out,Mid],[T,In,Out,Mid,_3],[T,Out,X,LLbls,_1,Mid],[T,Out,X,LLbls,_1,Mid,_3],[T,Out,X,LLbls,_1,Mid,_3,_4],[T,Out,X,LLbls,_1,Mid,_4],[T,Out,X,LLbls,_1,_3,_4],[T,Out,X,LLbls,_1,_4],[T,Out,X,_1,Mid],[T,Out,X,_1,Mid,_3],[T,Out,X,_1,Mid,_3,_4],[T,Out,X,_1,Mid,_4],[T,Out,X,_1,_3,_4],[T,Out,X,_1,_4],[T,Out,LLbls,_1,Mid],[T,Out,LLbls,_1,Mid,_3],[T,Out,LLbls,_1,Mid,_3,_4],[T,Out,LLbls,_1,Mid,_4],[T,Out,LLbls,_1,_3,_4],[T,Out,LLbls,_1,_4],[T,Out,_1,Mid],[T,Out,_1,Mid,_3],[T,Out,_1,Mid,_3,_4],[T,Out,_1,Mid,_4],[T,Out,_1,_3,_4],[T,Out,_1,_4],[T,X,LLbls,_1],[T,X,LLbls,_1,_3],[T,X,LLbls,_1,_3,_4],[T,X,LLbls,_1,_4],[T,X,_1],[T,X,_1,_3],[T,X,_1,_3,_4],[T,X,_1,_4],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,_3],[T,LLbls,_1,_3,_4],[T,LLbls,_1,_4],[T,LLbls,_3],[T,_1],[T,_1,_3],[T,_1,_3,_4],[T,_1,_4],[T,_3],[In,Out,X,LLbls,_1,Mid],[In,Out,X,LLbls,_1,Mid,_3],[In,Out,X,LLbls,_1,Mid,_3,_4],[In,Out,X,LLbls,_1,Mid,_4],[In,Out,X,_1,Mid],[In,Out,X,_1,Mid,_3],[In,Out,X,_1,Mid,_3,_4],[In,Out,X,_1,Mid,_4],[In,Out,LLbls,_1,Mid],[In,Out,LLbls,_1,Mid,_3],[In,Out,LLbls,_1,Mid,_3,_4],[In,Out,LLbls,_1,Mid,_4],[In,Out,LLbls,Mid],[In,Out,LLbls,Mid,_3],[In,Out,_1,Mid],[In,Out,_1,Mid,_3],[In,Out,_1,Mid,_3,_4],[In,Out,_1,Mid,_4],[In,Out,Mid],[In,Out,Mid,_3],[Out,X,LLbls,_1,Mid],[Out,X,LLbls,_1,Mid,_3],[Out,X,LLbls,_1,Mid,_3,_4],[Out,X,LLbls,_1,Mid,_4],[Out,X,LLbls,_1,_3,_4],[Out,X,LLbls,_1,_4],[Out,X,_1,Mid],[Out,X,_1,Mid,_3],[Out,X,_1,Mid,_3,_4],[Out,X,_1,Mid,_4],[Out,X,_1,_3,_4],[Out,X,_1,_4],[Out,LLbls,_1,Mid],[Out,LLbls,_1,Mid,_3],[Out,LLbls,_1,Mid,_3,_4],[Out,LLbls,_1,Mid,_4],[Out,LLbls,_1,_3,_4],[Out,LLbls,_1,_4],[Out,_1,Mid],[Out,_1,Mid,_3],[Out,_1,Mid,_3,_4],[Out,_1,Mid,_4],[Out,_1,_3,_4],[Out,_1,_4],[X,LLbls,_1],[X,LLbls,_1,_3],[X,LLbls,_1,_3,_4],[X,LLbls,_1,_4],[X,_1],[X,_1,_3],[X,_1,_3,_4],[X,_1,_4],[LLbls],[LLbls,_1],[LLbls,_1,_3],[LLbls,_1,_3,_4],[LLbls,_1,_4],[_1],[_1,_3],[_1,_3,_4],[_1,_4],[_3]]),ground([I,N,D,_2,I1]);mshare([[T],[T,In,Out,X,LLbls,_1,Mid],[T,In,Out,X,LLbls,_1,Mid,_3],[T,In,Out,X,LLbls,_1,Mid,_3,_4],[T,In,Out,X,LLbls,_1,Mid,_4],[T,In,Out,X,_1,Mid],[T,In,Out,X,_1,Mid,_3],[T,In,Out,X,_1,Mid,_3,_4],[T,In,Out,X,_1,Mid,_4],[T,In,Out,LLbls,_1,Mid],[T,In,Out,LLbls,_1,Mid,_3],[T,In,Out,LLbls,_1,Mid,_3,_4],[T,In,Out,LLbls,_1,Mid,_4],[T,In,Out,LLbls,Mid],[T,In,Out,LLbls,Mid,_3],[T,In,Out,_1,Mid],[T,In,Out,_1,Mid,_3],[T,In,Out,_1,Mid,_3,_4],[T,In,Out,_1,Mid,_4],[T,In,Out,Mid],[T,In,Out,Mid,_3],[T,Out,LLbls,_1,Mid],[T,Out,LLbls,_1,Mid,_3],[T,Out,LLbls,_1,Mid,_3,_4],[T,Out,LLbls,_1,Mid,_4],[T,Out,LLbls,_1,_3,_4],[T,Out,LLbls,_1,_4],[T,Out,_1,Mid],[T,Out,_1,Mid,_3],[T,Out,_1,Mid,_3,_4],[T,Out,_1,Mid,_4],[T,Out,_1,_3,_4],[T,Out,_1,_4],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,_3],[T,LLbls,_1,_3,_4],[T,LLbls,_1,_4],[T,LLbls,_3],[T,_1],[T,_1,_3],[T,_1,_3,_4],[T,_1,_4],[T,_3],[In,Out,X,LLbls,_1,Mid],[In,Out,X,LLbls,_1,Mid,_3],[In,Out,X,LLbls,_1,Mid,_3,_4],[In,Out,X,LLbls,_1,Mid,_4],[In,Out,X,_1,Mid],[In,Out,X,_1,Mid,_3],[In,Out,X,_1,Mid,_3,_4],[In,Out,X,_1,Mid,_4],[In,Out,LLbls,_1,Mid],[In,Out,LLbls,_1,Mid,_3],[In,Out,LLbls,_1,Mid,_3,_4],[In,Out,LLbls,_1,Mid,_4],[In,Out,LLbls,Mid],[In,Out,LLbls,Mid,_3],[In,Out,_1,Mid],[In,Out,_1,Mid,_3],[In,Out,_1,Mid,_3,_4],[In,Out,_1,Mid,_4],[In,Out,Mid],[In,Out,Mid,_3],[Out,LLbls,_1,Mid],[Out,LLbls,_1,Mid,_3],[Out,LLbls,_1,Mid,_3,_4],[Out,LLbls,_1,Mid,_4],[Out,LLbls,_1,_3,_4],[Out,LLbls,_1,_4],[Out,_1,Mid],[Out,_1,Mid,_3],[Out,_1,Mid,_3,_4],[Out,_1,Mid,_4],[Out,_1,_3,_4],[Out,_1,_4],[LLbls],[LLbls,_1],[LLbls,_1,_3],[LLbls,_1,_3,_4],[LLbls,_1,_4],[_1],[_1,_3],[_1,_3,_4],[_1,_4],[_3]]),ground([I,N,D,_2,I1]);mshare([[T],[T,In,Out,X,LLbls,_1,Mid],[T,In,Out,X,LLbls,_1,Mid,_3],[T,In,Out,X,LLbls,_1,Mid,_3,_4],[T,In,Out,X,LLbls,_1,Mid,_4],[T,In,Out,X,_1,Mid],[T,In,Out,X,_1,Mid,_3],[T,In,Out,X,_1,Mid,_3,_4],[T,In,Out,X,_1,Mid,_4],[T,Out,LLbls,_1,Mid],[T,Out,LLbls,_1,Mid,_3],[T,Out,LLbls,_1,Mid,_3,_4],[T,Out,LLbls,_1,Mid,_4],[T,Out,LLbls,_1,_3,_4],[T,Out,LLbls,_1,_4],[T,Out,_1,Mid],[T,Out,_1,Mid,_3],[T,Out,_1,Mid,_3,_4],[T,Out,_1,Mid,_4],[T,Out,_1,_3,_4],[T,Out,_1,_4],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,_3],[T,LLbls,_1,_3,_4],[T,LLbls,_1,_4],[T,LLbls,_3],[T,_1],[T,_1,_3],[T,_1,_3,_4],[T,_1,_4],[T,_3],[In,Out,X,LLbls,_1,Mid],[In,Out,X,LLbls,_1,Mid,_3],[In,Out,X,LLbls,_1,Mid,_3,_4],[In,Out,X,LLbls,_1,Mid,_4],[In,Out,X,_1,Mid],[In,Out,X,_1,Mid,_3],[In,Out,X,_1,Mid,_3,_4],[In,Out,X,_1,Mid,_4],[Out,LLbls,_1,Mid],[Out,LLbls,_1,Mid,_3],[Out,LLbls,_1,Mid,_3,_4],[Out,LLbls,_1,Mid,_4],[Out,LLbls,_1,_3,_4],[Out,LLbls,_1,_4],[Out,_1,Mid],[Out,_1,Mid,_3],[Out,_1,Mid,_3,_4],[Out,_1,Mid,_4],[Out,_1,_3,_4],[Out,_1,_4],[LLbls],[LLbls,_1],[LLbls,_1,_3],[LLbls,_1,_3,_4],[LLbls,_1,_4],[_1],[_1,_3],[_1,_3,_4],[_1,_4],[_3]]),ground([I,N,D,_2,I1]))).

:- true pred unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2)
   : ( (Last=nonlast),
       mshare([[T],[T,In],[T,In,X],[T,In,X,_1],[T,In,_1],[T,X],[T,X,_1],[T,_1],[In],[In,X],[In,X,_1],[In,_1],[Out],[X],[X,_1],[LLbls],[_1],[_2]]),
       ground([I,D]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,X,LLbls,_1],[T,In,Out,X,LLbls,_1,_2],[T,In,Out,X,_1],[T,In,Out,X,_1,_2],[T,In,Out,LLbls],[T,In,Out,LLbls,_1],[T,In,Out,LLbls,_1,_2],[T,In,Out,_1],[T,In,Out,_1,_2],[T,Out,X,LLbls,_1],[T,Out,X,LLbls,_1,_2],[T,Out,X,_1],[T,Out,X,_1,_2],[T,Out,LLbls,_1],[T,Out,LLbls,_1,_2],[T,Out,_1],[T,Out,_1,_2],[T,X,LLbls,_1],[T,X,LLbls,_1,_2],[T,X,_1],[T,X,_1,_2],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,_2],[T,_1],[T,_1,_2],[In,Out],[In,Out,X,LLbls,_1],[In,Out,X,LLbls,_1,_2],[In,Out,X,_1],[In,Out,X,_1,_2],[In,Out,LLbls],[In,Out,LLbls,_1],[In,Out,LLbls,_1,_2],[In,Out,_1],[In,Out,_1,_2],[Out,X,LLbls,_1],[Out,X,LLbls,_1,_2],[Out,X,_1],[Out,X,_1,_2],[Out,LLbls,_1],[Out,LLbls,_1,_2],[Out,_1],[Out,_1,_2],[X,LLbls,_1],[X,LLbls,_1,_2],[X,_1],[X,_1,_2],[LLbls],[LLbls,_1],[LLbls,_1,_2],[_1],[_1,_2]]),
        ground([I,D]) ).

:- true pred unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2)
   : ( (Last=last),
       mshare([[T],[T,In],[T,In,X],[T,In,X,LLbls],[T,In,X,LLbls,_1],[T,In,X,_1],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,X],[T,X,LLbls],[T,X,LLbls,_1],[T,X,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,X],[In,X,LLbls],[In,X,LLbls,_1],[In,X,_1],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[X],[X,LLbls],[X,LLbls,_1],[X,_1],[LLbls],[LLbls,_1],[_1]]),
       ground([I,D,_2]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,X,LLbls,_1],[T,In,Out,X,_1],[T,In,Out,LLbls],[T,In,Out,LLbls,_1],[T,In,Out,_1],[T,Out,X,LLbls,_1],[T,Out,X,_1],[T,Out,LLbls,_1],[T,Out,_1],[T,X,LLbls,_1],[T,X,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In,Out],[In,Out,X,LLbls,_1],[In,Out,X,_1],[In,Out,LLbls],[In,Out,LLbls,_1],[In,Out,_1],[Out,X,LLbls,_1],[Out,X,_1],[Out,LLbls,_1],[Out,_1],[X,LLbls,_1],[X,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([I,D,_2]) ).

:- true pred unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2)
   : ( (Last=nonlast),
       mshare([[T],[T,In],[T,In,X],[T,In,X,_1],[T,In,_1],[T,_1],[In],[In,X],[In,X,_1],[In,_1],[Out],[LLbls],[_1],[_2]]),
       ground([I,D]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,X,LLbls,_1],[T,In,Out,X,LLbls,_1,_2],[T,In,Out,X,_1],[T,In,Out,X,_1,_2],[T,In,Out,LLbls],[T,In,Out,LLbls,_1],[T,In,Out,LLbls,_1,_2],[T,In,Out,_1],[T,In,Out,_1,_2],[T,Out,LLbls,_1],[T,Out,LLbls,_1,_2],[T,Out,_1],[T,Out,_1,_2],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,_2],[T,_1],[T,_1,_2],[In,Out],[In,Out,X,LLbls,_1],[In,Out,X,LLbls,_1,_2],[In,Out,X,_1],[In,Out,X,_1,_2],[In,Out,LLbls],[In,Out,LLbls,_1],[In,Out,LLbls,_1,_2],[In,Out,_1],[In,Out,_1,_2],[Out,LLbls,_1],[Out,LLbls,_1,_2],[Out,_1],[Out,_1,_2],[LLbls],[LLbls,_1],[LLbls,_1,_2],[_1],[_1,_2]]),
        ground([I,D]) ).

:- true pred unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2)
   : ( (Last=nonlast),
       mshare([[T],[T,In,X],[T,In,X,_1],[T,_1],[In,X],[In,X,_1],[Out],[LLbls],[_1],[_2]]),
       ground([I,D]) )
   => ( mshare([[T],[T,In,Out,X,LLbls,_1],[T,In,Out,X,LLbls,_1,_2],[T,In,Out,X,_1],[T,In,Out,X,_1,_2],[T,Out,LLbls,_1],[T,Out,LLbls,_1,_2],[T,Out,_1],[T,Out,_1,_2],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,_2],[T,_1],[T,_1,_2],[In,Out,X,LLbls,_1],[In,Out,X,LLbls,_1,_2],[In,Out,X,_1],[In,Out,X,_1,_2],[Out,LLbls,_1],[Out,LLbls,_1,_2],[Out,_1],[Out,_1,_2],[LLbls],[LLbls,_1],[LLbls,_1,_2],[_1],[_1,_2]]),
        ground([I,D]) ).

:- true pred unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2)
   : ( (Last=last),
       mshare([[T],[T,In,X],[T,In,X,LLbls],[T,In,X,LLbls,_1],[T,In,X,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In,X],[In,X,LLbls],[In,X,LLbls,_1],[In,X,_1],[Out],[LLbls],[LLbls,_1],[_1]]),
       ground([I,D,_2]) )
   => ( mshare([[T],[T,In,Out,X,LLbls,_1],[T,In,Out,X,_1],[T,Out,LLbls,_1],[T,Out,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In,Out,X,LLbls,_1],[In,Out,X,_1],[Out,LLbls,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([I,D,_2]) ).

:- true pred unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2)
   : ( (Last=last),
       mshare([[T],[T,In],[T,In,X],[T,In,X,LLbls],[T,In,X,LLbls,_1],[T,In,X,_1],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,X],[In,X,LLbls],[In,X,LLbls,_1],[In,X,_1],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1]]),
       ground([I,D,_2]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,X,LLbls,_1],[T,In,Out,X,_1],[T,In,Out,LLbls],[T,In,Out,LLbls,_1],[T,In,Out,_1],[T,Out,LLbls,_1],[T,Out,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In,Out],[In,Out,X,LLbls,_1],[In,Out,X,_1],[In,Out,LLbls],[In,Out,LLbls,_1],[In,Out,_1],[Out,LLbls,_1],[Out,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([I,D,_2]) ).

unify_arg(I,T,In,Out,D,X,Last,LLbls,_1,_2) :-
    true((mshare([[T],[T,In],[T,In,X],[T,In,X,LLbls],[T,In,X,LLbls,_1],[T,In,X,_1],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,X],[T,X,LLbls],[T,X,LLbls,_1],[T,X,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,X],[In,X,LLbls],[In,X,LLbls,_1],[In,X,_1],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[X],[X,LLbls],[X,LLbls,_1],[X,_1],[LLbls],[LLbls,_1],[_1],[_3],[Y],[ID],[Mid],[A]]),ground([I,D,Last,_2]);mshare([[T],[T,In],[T,In,X],[T,In,X,LLbls],[T,In,X,LLbls,_1],[T,In,X,_1],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,X],[In,X,LLbls],[In,X,LLbls,_1],[In,X,_1],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[_3],[Y],[ID],[Mid],[A]]),ground([I,D,Last,_2]);mshare([[T],[T,In],[T,In,X],[T,In,X,_1],[T,In,_1],[T,X],[T,X,_1],[T,_1],[In],[In,X],[In,X,_1],[In,_1],[Out],[X],[X,_1],[LLbls],[_1],[_2],[_3],[Y],[ID],[Mid],[A]]),ground([I,D,Last]);mshare([[T],[T,In],[T,In,X],[T,In,X,_1],[T,In,_1],[T,_1],[In],[In,X],[In,X,_1],[In,_1],[Out],[LLbls],[_1],[_2],[_3],[Y],[ID],[Mid],[A]]),ground([I,D,Last]);mshare([[T],[T,In,X],[T,In,X,LLbls],[T,In,X,LLbls,_1],[T,In,X,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In,X],[In,X,LLbls],[In,X,LLbls,_1],[In,X,_1],[Out],[LLbls],[LLbls,_1],[_1],[_3],[Y],[ID],[Mid],[A]]),ground([I,D,Last,_2]);mshare([[T],[T,In,X],[T,In,X,_1],[T,_1],[In,X],[In,X,_1],[Out],[LLbls],[_1],[_2],[_3],[Y],[ID],[Mid],[A]]),ground([I,D,Last]))),
    'C'(_1,move([X+ID],Y),_3),
    true((mshare([[T],[T,In],[T,In,X,LLbls,_1],[T,In,X,LLbls,_1,_3],[T,In,X,LLbls,_1,_3,Y],[T,In,X,LLbls,_1,_3,Y,ID],[T,In,X,LLbls,_1,_3,ID],[T,In,X,LLbls,_1,Y],[T,In,X,LLbls,_1,Y,ID],[T,In,X,LLbls,_1,ID],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,Y],[T,In,X,_1,_3,Y,ID],[T,In,X,_1,_3,ID],[T,In,X,_1,Y],[T,In,X,_1,Y,ID],[T,In,X,_1,ID],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,LLbls,_1,_3,Y],[T,In,LLbls,_1,_3,Y,ID],[T,In,LLbls,_1,_3,ID],[T,In,LLbls,_1,Y],[T,In,LLbls,_1,Y,ID],[T,In,LLbls,_1,ID],[T,In,_1,_3],[T,In,_1,_3,Y],[T,In,_1,_3,Y,ID],[T,In,_1,_3,ID],[T,In,_1,Y],[T,In,_1,Y,ID],[T,In,_1,ID],[T,X,LLbls,_1],[T,X,LLbls,_1,_3],[T,X,LLbls,_1,_3,Y],[T,X,LLbls,_1,_3,Y,ID],[T,X,LLbls,_1,_3,ID],[T,X,LLbls,_1,Y],[T,X,LLbls,_1,Y,ID],[T,X,LLbls,_1,ID],[T,X,_1],[T,X,_1,_3],[T,X,_1,_3,Y],[T,X,_1,_3,Y,ID],[T,X,_1,_3,ID],[T,X,_1,Y],[T,X,_1,Y,ID],[T,X,_1,ID],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,Y],[T,LLbls,_1,_3,Y,ID],[T,LLbls,_1,_3,ID],[T,LLbls,_1,Y],[T,LLbls,_1,Y,ID],[T,LLbls,_1,ID],[T,_1,_3],[T,_1,_3,Y],[T,_1,_3,Y,ID],[T,_1,_3,ID],[T,_1,Y],[T,_1,Y,ID],[T,_1,ID],[In],[In,X,LLbls,_1],[In,X,LLbls,_1,_3],[In,X,LLbls,_1,_3,Y],[In,X,LLbls,_1,_3,Y,ID],[In,X,LLbls,_1,_3,ID],[In,X,LLbls,_1,Y],[In,X,LLbls,_1,Y,ID],[In,X,LLbls,_1,ID],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,Y],[In,X,_1,_3,Y,ID],[In,X,_1,_3,ID],[In,X,_1,Y],[In,X,_1,Y,ID],[In,X,_1,ID],[In,LLbls],[In,LLbls,_1,_3],[In,LLbls,_1,_3,Y],[In,LLbls,_1,_3,Y,ID],[In,LLbls,_1,_3,ID],[In,LLbls,_1,Y],[In,LLbls,_1,Y,ID],[In,LLbls,_1,ID],[In,_1,_3],[In,_1,_3,Y],[In,_1,_3,Y,ID],[In,_1,_3,ID],[In,_1,Y],[In,_1,Y,ID],[In,_1,ID],[Out],[X,LLbls,_1],[X,LLbls,_1,_3],[X,LLbls,_1,_3,Y],[X,LLbls,_1,_3,Y,ID],[X,LLbls,_1,_3,ID],[X,LLbls,_1,Y],[X,LLbls,_1,Y,ID],[X,LLbls,_1,ID],[X,_1],[X,_1,_3],[X,_1,_3,Y],[X,_1,_3,Y,ID],[X,_1,_3,ID],[X,_1,Y],[X,_1,Y,ID],[X,_1,ID],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[LLbls,_1,_3,Y,ID],[LLbls,_1,_3,ID],[LLbls,_1,Y],[LLbls,_1,Y,ID],[LLbls,_1,ID],[_1,_3],[_1,_3,Y],[_1,_3,Y,ID],[_1,_3,ID],[_1,Y],[_1,Y,ID],[_1,ID],[Mid],[A]]),ground([I,D,Last,_2]);mshare([[T],[T,In],[T,In,X,LLbls,_1],[T,In,X,LLbls,_1,_3],[T,In,X,LLbls,_1,_3,Y],[T,In,X,LLbls,_1,_3,Y,ID],[T,In,X,LLbls,_1,_3,ID],[T,In,X,LLbls,_1,Y],[T,In,X,LLbls,_1,Y,ID],[T,In,X,LLbls,_1,ID],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,Y],[T,In,X,_1,_3,Y,ID],[T,In,X,_1,_3,ID],[T,In,X,_1,Y],[T,In,X,_1,Y,ID],[T,In,X,_1,ID],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,LLbls,_1,_3,Y],[T,In,LLbls,_1,_3,Y,ID],[T,In,LLbls,_1,_3,ID],[T,In,LLbls,_1,Y],[T,In,LLbls,_1,Y,ID],[T,In,LLbls,_1,ID],[T,In,_1,_3],[T,In,_1,_3,Y],[T,In,_1,_3,Y,ID],[T,In,_1,_3,ID],[T,In,_1,Y],[T,In,_1,Y,ID],[T,In,_1,ID],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,Y],[T,LLbls,_1,_3,Y,ID],[T,LLbls,_1,_3,ID],[T,LLbls,_1,Y],[T,LLbls,_1,Y,ID],[T,LLbls,_1,ID],[T,_1,_3],[T,_1,_3,Y],[T,_1,_3,Y,ID],[T,_1,_3,ID],[T,_1,Y],[T,_1,Y,ID],[T,_1,ID],[In],[In,X,LLbls,_1],[In,X,LLbls,_1,_3],[In,X,LLbls,_1,_3,Y],[In,X,LLbls,_1,_3,Y,ID],[In,X,LLbls,_1,_3,ID],[In,X,LLbls,_1,Y],[In,X,LLbls,_1,Y,ID],[In,X,LLbls,_1,ID],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,Y],[In,X,_1,_3,Y,ID],[In,X,_1,_3,ID],[In,X,_1,Y],[In,X,_1,Y,ID],[In,X,_1,ID],[In,LLbls],[In,LLbls,_1,_3],[In,LLbls,_1,_3,Y],[In,LLbls,_1,_3,Y,ID],[In,LLbls,_1,_3,ID],[In,LLbls,_1,Y],[In,LLbls,_1,Y,ID],[In,LLbls,_1,ID],[In,_1,_3],[In,_1,_3,Y],[In,_1,_3,Y,ID],[In,_1,_3,ID],[In,_1,Y],[In,_1,Y,ID],[In,_1,ID],[Out],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[LLbls,_1,_3,Y,ID],[LLbls,_1,_3,ID],[LLbls,_1,Y],[LLbls,_1,Y,ID],[LLbls,_1,ID],[_1,_3],[_1,_3,Y],[_1,_3,Y,ID],[_1,_3,ID],[_1,Y],[_1,Y,ID],[_1,ID],[Mid],[A]]),ground([I,D,Last,_2]);mshare([[T],[T,In],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,Y],[T,In,X,_1,_3,Y,ID],[T,In,X,_1,_3,ID],[T,In,X,_1,Y],[T,In,X,_1,Y,ID],[T,In,X,_1,ID],[T,In,_1,_3],[T,In,_1,_3,Y],[T,In,_1,_3,Y,ID],[T,In,_1,_3,ID],[T,In,_1,Y],[T,In,_1,Y,ID],[T,In,_1,ID],[T,X,_1],[T,X,_1,_3],[T,X,_1,_3,Y],[T,X,_1,_3,Y,ID],[T,X,_1,_3,ID],[T,X,_1,Y],[T,X,_1,Y,ID],[T,X,_1,ID],[T,_1,_3],[T,_1,_3,Y],[T,_1,_3,Y,ID],[T,_1,_3,ID],[T,_1,Y],[T,_1,Y,ID],[T,_1,ID],[In],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,Y],[In,X,_1,_3,Y,ID],[In,X,_1,_3,ID],[In,X,_1,Y],[In,X,_1,Y,ID],[In,X,_1,ID],[In,_1,_3],[In,_1,_3,Y],[In,_1,_3,Y,ID],[In,_1,_3,ID],[In,_1,Y],[In,_1,Y,ID],[In,_1,ID],[Out],[X,_1],[X,_1,_3],[X,_1,_3,Y],[X,_1,_3,Y,ID],[X,_1,_3,ID],[X,_1,Y],[X,_1,Y,ID],[X,_1,ID],[LLbls],[_1,_3],[_1,_3,Y],[_1,_3,Y,ID],[_1,_3,ID],[_1,Y],[_1,Y,ID],[_1,ID],[_2],[Mid],[A]]),ground([I,D,Last]);mshare([[T],[T,In],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,Y],[T,In,X,_1,_3,Y,ID],[T,In,X,_1,_3,ID],[T,In,X,_1,Y],[T,In,X,_1,Y,ID],[T,In,X,_1,ID],[T,In,_1,_3],[T,In,_1,_3,Y],[T,In,_1,_3,Y,ID],[T,In,_1,_3,ID],[T,In,_1,Y],[T,In,_1,Y,ID],[T,In,_1,ID],[T,_1,_3],[T,_1,_3,Y],[T,_1,_3,Y,ID],[T,_1,_3,ID],[T,_1,Y],[T,_1,Y,ID],[T,_1,ID],[In],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,Y],[In,X,_1,_3,Y,ID],[In,X,_1,_3,ID],[In,X,_1,Y],[In,X,_1,Y,ID],[In,X,_1,ID],[In,_1,_3],[In,_1,_3,Y],[In,_1,_3,Y,ID],[In,_1,_3,ID],[In,_1,Y],[In,_1,Y,ID],[In,_1,ID],[Out],[LLbls],[_1,_3],[_1,_3,Y],[_1,_3,Y,ID],[_1,_3,ID],[_1,Y],[_1,Y,ID],[_1,ID],[_2],[Mid],[A]]),ground([I,D,Last]);mshare([[T],[T,In,X,LLbls,_1],[T,In,X,LLbls,_1,_3],[T,In,X,LLbls,_1,_3,Y],[T,In,X,LLbls,_1,_3,Y,ID],[T,In,X,LLbls,_1,_3,ID],[T,In,X,LLbls,_1,Y],[T,In,X,LLbls,_1,Y,ID],[T,In,X,LLbls,_1,ID],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,Y],[T,In,X,_1,_3,Y,ID],[T,In,X,_1,_3,ID],[T,In,X,_1,Y],[T,In,X,_1,Y,ID],[T,In,X,_1,ID],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,Y],[T,LLbls,_1,_3,Y,ID],[T,LLbls,_1,_3,ID],[T,LLbls,_1,Y],[T,LLbls,_1,Y,ID],[T,LLbls,_1,ID],[T,_1,_3],[T,_1,_3,Y],[T,_1,_3,Y,ID],[T,_1,_3,ID],[T,_1,Y],[T,_1,Y,ID],[T,_1,ID],[In,X,LLbls,_1],[In,X,LLbls,_1,_3],[In,X,LLbls,_1,_3,Y],[In,X,LLbls,_1,_3,Y,ID],[In,X,LLbls,_1,_3,ID],[In,X,LLbls,_1,Y],[In,X,LLbls,_1,Y,ID],[In,X,LLbls,_1,ID],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,Y],[In,X,_1,_3,Y,ID],[In,X,_1,_3,ID],[In,X,_1,Y],[In,X,_1,Y,ID],[In,X,_1,ID],[Out],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[LLbls,_1,_3,Y,ID],[LLbls,_1,_3,ID],[LLbls,_1,Y],[LLbls,_1,Y,ID],[LLbls,_1,ID],[_1,_3],[_1,_3,Y],[_1,_3,Y,ID],[_1,_3,ID],[_1,Y],[_1,Y,ID],[_1,ID],[Mid],[A]]),ground([I,D,Last,_2]);mshare([[T],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,Y],[T,In,X,_1,_3,Y,ID],[T,In,X,_1,_3,ID],[T,In,X,_1,Y],[T,In,X,_1,Y,ID],[T,In,X,_1,ID],[T,_1,_3],[T,_1,_3,Y],[T,_1,_3,Y,ID],[T,_1,_3,ID],[T,_1,Y],[T,_1,Y,ID],[T,_1,ID],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,Y],[In,X,_1,_3,Y,ID],[In,X,_1,_3,ID],[In,X,_1,Y],[In,X,_1,Y,ID],[In,X,_1,ID],[Out],[LLbls],[_1,_3],[_1,_3,Y],[_1,_3,Y,ID],[_1,_3,ID],[_1,Y],[_1,Y,ID],[_1,ID],[_2],[Mid],[A]]),ground([I,D,Last]))),
    ID is I+D,
    true((mshare([[T],[T,In],[T,In,X,LLbls,_1],[T,In,X,LLbls,_1,_3],[T,In,X,LLbls,_1,_3,Y],[T,In,X,LLbls,_1,Y],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,Y],[T,In,X,_1,Y],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,LLbls,_1,_3,Y],[T,In,LLbls,_1,Y],[T,In,_1,_3],[T,In,_1,_3,Y],[T,In,_1,Y],[T,X,LLbls,_1],[T,X,LLbls,_1,_3],[T,X,LLbls,_1,_3,Y],[T,X,LLbls,_1,Y],[T,X,_1],[T,X,_1,_3],[T,X,_1,_3,Y],[T,X,_1,Y],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,Y],[T,LLbls,_1,Y],[T,_1,_3],[T,_1,_3,Y],[T,_1,Y],[In],[In,X,LLbls,_1],[In,X,LLbls,_1,_3],[In,X,LLbls,_1,_3,Y],[In,X,LLbls,_1,Y],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,Y],[In,X,_1,Y],[In,LLbls],[In,LLbls,_1,_3],[In,LLbls,_1,_3,Y],[In,LLbls,_1,Y],[In,_1,_3],[In,_1,_3,Y],[In,_1,Y],[Out],[X,LLbls,_1],[X,LLbls,_1,_3],[X,LLbls,_1,_3,Y],[X,LLbls,_1,Y],[X,_1],[X,_1,_3],[X,_1,_3,Y],[X,_1,Y],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[LLbls,_1,Y],[_1,_3],[_1,_3,Y],[_1,Y],[Mid],[A]]),ground([I,D,Last,_2,ID]);mshare([[T],[T,In],[T,In,X,LLbls,_1],[T,In,X,LLbls,_1,_3],[T,In,X,LLbls,_1,_3,Y],[T,In,X,LLbls,_1,Y],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,Y],[T,In,X,_1,Y],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,LLbls,_1,_3,Y],[T,In,LLbls,_1,Y],[T,In,_1,_3],[T,In,_1,_3,Y],[T,In,_1,Y],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,Y],[T,LLbls,_1,Y],[T,_1,_3],[T,_1,_3,Y],[T,_1,Y],[In],[In,X,LLbls,_1],[In,X,LLbls,_1,_3],[In,X,LLbls,_1,_3,Y],[In,X,LLbls,_1,Y],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,Y],[In,X,_1,Y],[In,LLbls],[In,LLbls,_1,_3],[In,LLbls,_1,_3,Y],[In,LLbls,_1,Y],[In,_1,_3],[In,_1,_3,Y],[In,_1,Y],[Out],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[LLbls,_1,Y],[_1,_3],[_1,_3,Y],[_1,Y],[Mid],[A]]),ground([I,D,Last,_2,ID]);mshare([[T],[T,In],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,Y],[T,In,X,_1,Y],[T,In,_1,_3],[T,In,_1,_3,Y],[T,In,_1,Y],[T,X,_1],[T,X,_1,_3],[T,X,_1,_3,Y],[T,X,_1,Y],[T,_1,_3],[T,_1,_3,Y],[T,_1,Y],[In],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,Y],[In,X,_1,Y],[In,_1,_3],[In,_1,_3,Y],[In,_1,Y],[Out],[X,_1],[X,_1,_3],[X,_1,_3,Y],[X,_1,Y],[LLbls],[_1,_3],[_1,_3,Y],[_1,Y],[_2],[Mid],[A]]),ground([I,D,Last,ID]);mshare([[T],[T,In],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,Y],[T,In,X,_1,Y],[T,In,_1,_3],[T,In,_1,_3,Y],[T,In,_1,Y],[T,_1,_3],[T,_1,_3,Y],[T,_1,Y],[In],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,Y],[In,X,_1,Y],[In,_1,_3],[In,_1,_3,Y],[In,_1,Y],[Out],[LLbls],[_1,_3],[_1,_3,Y],[_1,Y],[_2],[Mid],[A]]),ground([I,D,Last,ID]);mshare([[T],[T,In,X,LLbls,_1],[T,In,X,LLbls,_1,_3],[T,In,X,LLbls,_1,_3,Y],[T,In,X,LLbls,_1,Y],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,Y],[T,In,X,_1,Y],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,Y],[T,LLbls,_1,Y],[T,_1,_3],[T,_1,_3,Y],[T,_1,Y],[In,X,LLbls,_1],[In,X,LLbls,_1,_3],[In,X,LLbls,_1,_3,Y],[In,X,LLbls,_1,Y],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,Y],[In,X,_1,Y],[Out],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[LLbls,_1,Y],[_1,_3],[_1,_3,Y],[_1,Y],[Mid],[A]]),ground([I,D,Last,_2,ID]);mshare([[T],[T,In,X,_1],[T,In,X,_1,_3],[T,In,X,_1,_3,Y],[T,In,X,_1,Y],[T,_1,_3],[T,_1,_3,Y],[T,_1,Y],[In,X,_1],[In,X,_1,_3],[In,X,_1,_3,Y],[In,X,_1,Y],[Out],[LLbls],[_1,_3],[_1,_3,Y],[_1,Y],[_2],[Mid],[A]]),ground([I,D,Last,ID]))),
    incl(Y,In,Mid),
    true((mshare([[T],[T,In,X,LLbls,_1,_3,Y,Mid],[T,In,X,LLbls,_1,_3,Mid],[T,In,X,LLbls,_1,Y,Mid],[T,In,X,LLbls,_1,Mid],[T,In,X,_1,_3,Y,Mid],[T,In,X,_1,_3,Mid],[T,In,X,_1,Y,Mid],[T,In,X,_1,Mid],[T,In,LLbls,_1,_3,Y,Mid],[T,In,LLbls,_1,_3,Mid],[T,In,LLbls,_1,Y,Mid],[T,In,LLbls,Mid],[T,In,_1,_3,Y,Mid],[T,In,_1,_3,Mid],[T,In,_1,Y,Mid],[T,In,Mid],[T,X,LLbls,_1],[T,X,LLbls,_1,_3],[T,X,LLbls,_1,_3,Y],[T,X,LLbls,_1,_3,Y,Mid],[T,X,LLbls,_1,Y],[T,X,LLbls,_1,Y,Mid],[T,X,_1],[T,X,_1,_3],[T,X,_1,_3,Y],[T,X,_1,_3,Y,Mid],[T,X,_1,Y],[T,X,_1,Y,Mid],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,Y],[T,LLbls,_1,_3,Y,Mid],[T,LLbls,_1,Y],[T,LLbls,_1,Y,Mid],[T,_1,_3],[T,_1,_3,Y],[T,_1,_3,Y,Mid],[T,_1,Y],[T,_1,Y,Mid],[In,X,LLbls,_1,_3,Y,Mid],[In,X,LLbls,_1,_3,Mid],[In,X,LLbls,_1,Y,Mid],[In,X,LLbls,_1,Mid],[In,X,_1,_3,Y,Mid],[In,X,_1,_3,Mid],[In,X,_1,Y,Mid],[In,X,_1,Mid],[In,LLbls,_1,_3,Y,Mid],[In,LLbls,_1,_3,Mid],[In,LLbls,_1,Y,Mid],[In,LLbls,Mid],[In,_1,_3,Y,Mid],[In,_1,_3,Mid],[In,_1,Y,Mid],[In,Mid],[Out],[X,LLbls,_1],[X,LLbls,_1,_3],[X,LLbls,_1,_3,Y],[X,LLbls,_1,_3,Y,Mid],[X,LLbls,_1,Y],[X,LLbls,_1,Y,Mid],[X,_1],[X,_1,_3],[X,_1,_3,Y],[X,_1,_3,Y,Mid],[X,_1,Y],[X,_1,Y,Mid],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[LLbls,_1,_3,Y,Mid],[LLbls,_1,Y],[LLbls,_1,Y,Mid],[_1,_3],[_1,_3,Y],[_1,_3,Y,Mid],[_1,Y],[_1,Y,Mid],[A]]),ground([I,D,Last,_2,ID]);mshare([[T],[T,In,X,LLbls,_1,_3,Y,Mid],[T,In,X,LLbls,_1,_3,Mid],[T,In,X,LLbls,_1,Y,Mid],[T,In,X,LLbls,_1,Mid],[T,In,X,_1,_3,Y,Mid],[T,In,X,_1,_3,Mid],[T,In,X,_1,Y,Mid],[T,In,X,_1,Mid],[T,In,LLbls,_1,_3,Y,Mid],[T,In,LLbls,_1,_3,Mid],[T,In,LLbls,_1,Y,Mid],[T,In,LLbls,Mid],[T,In,_1,_3,Y,Mid],[T,In,_1,_3,Mid],[T,In,_1,Y,Mid],[T,In,Mid],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,Y],[T,LLbls,_1,_3,Y,Mid],[T,LLbls,_1,Y],[T,LLbls,_1,Y,Mid],[T,_1,_3],[T,_1,_3,Y],[T,_1,_3,Y,Mid],[T,_1,Y],[T,_1,Y,Mid],[In,X,LLbls,_1,_3,Y,Mid],[In,X,LLbls,_1,_3,Mid],[In,X,LLbls,_1,Y,Mid],[In,X,LLbls,_1,Mid],[In,X,_1,_3,Y,Mid],[In,X,_1,_3,Mid],[In,X,_1,Y,Mid],[In,X,_1,Mid],[In,LLbls,_1,_3,Y,Mid],[In,LLbls,_1,_3,Mid],[In,LLbls,_1,Y,Mid],[In,LLbls,Mid],[In,_1,_3,Y,Mid],[In,_1,_3,Mid],[In,_1,Y,Mid],[In,Mid],[Out],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[LLbls,_1,_3,Y,Mid],[LLbls,_1,Y],[LLbls,_1,Y,Mid],[_1,_3],[_1,_3,Y],[_1,_3,Y,Mid],[_1,Y],[_1,Y,Mid],[A]]),ground([I,D,Last,_2,ID]);mshare([[T],[T,In,X,LLbls,_1,_3,Y,Mid],[T,In,X,LLbls,_1,_3,Mid],[T,In,X,LLbls,_1,Y,Mid],[T,In,X,LLbls,_1,Mid],[T,In,X,_1,_3,Y,Mid],[T,In,X,_1,_3,Mid],[T,In,X,_1,Y,Mid],[T,In,X,_1,Mid],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,Y],[T,LLbls,_1,_3,Y,Mid],[T,LLbls,_1,Y],[T,LLbls,_1,Y,Mid],[T,_1,_3],[T,_1,_3,Y],[T,_1,_3,Y,Mid],[T,_1,Y],[T,_1,Y,Mid],[In,X,LLbls,_1,_3,Y,Mid],[In,X,LLbls,_1,_3,Mid],[In,X,LLbls,_1,Y,Mid],[In,X,LLbls,_1,Mid],[In,X,_1,_3,Y,Mid],[In,X,_1,_3,Mid],[In,X,_1,Y,Mid],[In,X,_1,Mid],[Out],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[LLbls,_1,_3,Y,Mid],[LLbls,_1,Y],[LLbls,_1,Y,Mid],[_1,_3],[_1,_3,Y],[_1,_3,Y,Mid],[_1,Y],[_1,Y,Mid],[A]]),ground([I,D,Last,_2,ID]);mshare([[T],[T,In,X,_1,_3,Y,Mid],[T,In,X,_1,_3,Mid],[T,In,X,_1,Y,Mid],[T,In,X,_1,Mid],[T,In,_1,_3,Y,Mid],[T,In,_1,_3,Mid],[T,In,_1,Y,Mid],[T,In,Mid],[T,X,_1],[T,X,_1,_3],[T,X,_1,_3,Y],[T,X,_1,_3,Y,Mid],[T,X,_1,Y],[T,X,_1,Y,Mid],[T,_1,_3],[T,_1,_3,Y],[T,_1,_3,Y,Mid],[T,_1,Y],[T,_1,Y,Mid],[In,X,_1,_3,Y,Mid],[In,X,_1,_3,Mid],[In,X,_1,Y,Mid],[In,X,_1,Mid],[In,_1,_3,Y,Mid],[In,_1,_3,Mid],[In,_1,Y,Mid],[In,Mid],[Out],[X,_1],[X,_1,_3],[X,_1,_3,Y],[X,_1,_3,Y,Mid],[X,_1,Y],[X,_1,Y,Mid],[LLbls],[_1,_3],[_1,_3,Y],[_1,_3,Y,Mid],[_1,Y],[_1,Y,Mid],[_2],[A]]),ground([I,D,Last,ID]);mshare([[T],[T,In,X,_1,_3,Y,Mid],[T,In,X,_1,_3,Mid],[T,In,X,_1,Y,Mid],[T,In,X,_1,Mid],[T,In,_1,_3,Y,Mid],[T,In,_1,_3,Mid],[T,In,_1,Y,Mid],[T,In,Mid],[T,_1,_3],[T,_1,_3,Y],[T,_1,_3,Y,Mid],[T,_1,Y],[T,_1,Y,Mid],[In,X,_1,_3,Y,Mid],[In,X,_1,_3,Mid],[In,X,_1,Y,Mid],[In,X,_1,Mid],[In,_1,_3,Y,Mid],[In,_1,_3,Mid],[In,_1,Y,Mid],[In,Mid],[Out],[LLbls],[_1,_3],[_1,_3,Y],[_1,_3,Y,Mid],[_1,Y],[_1,Y,Mid],[_2],[A]]),ground([I,D,Last,ID]);mshare([[T],[T,In,X,_1,_3,Y,Mid],[T,In,X,_1,_3,Mid],[T,In,X,_1,Y,Mid],[T,In,X,_1,Mid],[T,_1,_3],[T,_1,_3,Y],[T,_1,_3,Y,Mid],[T,_1,Y],[T,_1,Y,Mid],[In,X,_1,_3,Y,Mid],[In,X,_1,_3,Mid],[In,X,_1,Y,Mid],[In,X,_1,Mid],[Out],[LLbls],[_1,_3],[_1,_3,Y],[_1,_3,Y,Mid],[_1,Y],[_1,Y,Mid],[_2],[A]]),ground([I,D,Last,ID]))),
    arg(I,T,A),
    true((mshare([[T,In,X,LLbls,_1,_3,Y,Mid,A],[T,In,X,LLbls,_1,_3,Mid,A],[T,In,X,LLbls,_1,Y,Mid,A],[T,In,X,LLbls,_1,Mid,A],[T,In,X,_1,_3,Y,Mid,A],[T,In,X,_1,_3,Mid,A],[T,In,X,_1,Y,Mid,A],[T,In,X,_1,Mid,A],[T,In,LLbls,_1,_3,Y,Mid,A],[T,In,LLbls,_1,_3,Mid,A],[T,In,LLbls,_1,Y,Mid,A],[T,In,LLbls,Mid,A],[T,In,_1,_3,Y,Mid,A],[T,In,_1,_3,Mid,A],[T,In,_1,Y,Mid,A],[T,In,Mid,A],[T,X,LLbls,_1,_3,Y,Mid,A],[T,X,LLbls,_1,_3,Y,A],[T,X,LLbls,_1,_3,A],[T,X,LLbls,_1,Y,Mid,A],[T,X,LLbls,_1,Y,A],[T,X,LLbls,_1,A],[T,X,_1,_3,Y,Mid,A],[T,X,_1,_3,Y,A],[T,X,_1,_3,A],[T,X,_1,Y,Mid,A],[T,X,_1,Y,A],[T,X,_1,A],[T,LLbls,_1,_3,Y,Mid,A],[T,LLbls,_1,_3,Y,A],[T,LLbls,_1,_3,A],[T,LLbls,_1,Y,Mid,A],[T,LLbls,_1,Y,A],[T,LLbls,A],[T,_1,_3,Y,Mid,A],[T,_1,_3,Y,A],[T,_1,_3,A],[T,_1,Y,Mid,A],[T,_1,Y,A],[T,A],[In,X,LLbls,_1,_3,Y,Mid],[In,X,LLbls,_1,_3,Mid],[In,X,LLbls,_1,Y,Mid],[In,X,LLbls,_1,Mid],[In,X,_1,_3,Y,Mid],[In,X,_1,_3,Mid],[In,X,_1,Y,Mid],[In,X,_1,Mid],[In,LLbls,_1,_3,Y,Mid],[In,LLbls,_1,_3,Mid],[In,LLbls,_1,Y,Mid],[In,LLbls,Mid],[In,_1,_3,Y,Mid],[In,_1,_3,Mid],[In,_1,Y,Mid],[In,Mid],[Out],[X,LLbls,_1],[X,LLbls,_1,_3],[X,LLbls,_1,_3,Y],[X,LLbls,_1,_3,Y,Mid],[X,LLbls,_1,Y],[X,LLbls,_1,Y,Mid],[X,_1],[X,_1,_3],[X,_1,_3,Y],[X,_1,_3,Y,Mid],[X,_1,Y],[X,_1,Y,Mid],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[LLbls,_1,_3,Y,Mid],[LLbls,_1,Y],[LLbls,_1,Y,Mid],[_1,_3],[_1,_3,Y],[_1,_3,Y,Mid],[_1,Y],[_1,Y,Mid]]),ground([I,D,Last,_2,ID]);mshare([[T,In,X,LLbls,_1,_3,Y,Mid,A],[T,In,X,LLbls,_1,_3,Mid,A],[T,In,X,LLbls,_1,Y,Mid,A],[T,In,X,LLbls,_1,Mid,A],[T,In,X,_1,_3,Y,Mid,A],[T,In,X,_1,_3,Mid,A],[T,In,X,_1,Y,Mid,A],[T,In,X,_1,Mid,A],[T,In,LLbls,_1,_3,Y,Mid,A],[T,In,LLbls,_1,_3,Mid,A],[T,In,LLbls,_1,Y,Mid,A],[T,In,LLbls,Mid,A],[T,In,_1,_3,Y,Mid,A],[T,In,_1,_3,Mid,A],[T,In,_1,Y,Mid,A],[T,In,Mid,A],[T,LLbls,_1,_3,Y,Mid,A],[T,LLbls,_1,_3,Y,A],[T,LLbls,_1,_3,A],[T,LLbls,_1,Y,Mid,A],[T,LLbls,_1,Y,A],[T,LLbls,A],[T,_1,_3,Y,Mid,A],[T,_1,_3,Y,A],[T,_1,_3,A],[T,_1,Y,Mid,A],[T,_1,Y,A],[T,A],[In,X,LLbls,_1,_3,Y,Mid],[In,X,LLbls,_1,_3,Mid],[In,X,LLbls,_1,Y,Mid],[In,X,LLbls,_1,Mid],[In,X,_1,_3,Y,Mid],[In,X,_1,_3,Mid],[In,X,_1,Y,Mid],[In,X,_1,Mid],[In,LLbls,_1,_3,Y,Mid],[In,LLbls,_1,_3,Mid],[In,LLbls,_1,Y,Mid],[In,LLbls,Mid],[In,_1,_3,Y,Mid],[In,_1,_3,Mid],[In,_1,Y,Mid],[In,Mid],[Out],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[LLbls,_1,_3,Y,Mid],[LLbls,_1,Y],[LLbls,_1,Y,Mid],[_1,_3],[_1,_3,Y],[_1,_3,Y,Mid],[_1,Y],[_1,Y,Mid]]),ground([I,D,Last,_2,ID]);mshare([[T,In,X,LLbls,_1,_3,Y,Mid,A],[T,In,X,LLbls,_1,_3,Mid,A],[T,In,X,LLbls,_1,Y,Mid,A],[T,In,X,LLbls,_1,Mid,A],[T,In,X,_1,_3,Y,Mid,A],[T,In,X,_1,_3,Mid,A],[T,In,X,_1,Y,Mid,A],[T,In,X,_1,Mid,A],[T,LLbls,_1,_3,Y,Mid,A],[T,LLbls,_1,_3,Y,A],[T,LLbls,_1,_3,A],[T,LLbls,_1,Y,Mid,A],[T,LLbls,_1,Y,A],[T,LLbls,A],[T,_1,_3,Y,Mid,A],[T,_1,_3,Y,A],[T,_1,_3,A],[T,_1,Y,Mid,A],[T,_1,Y,A],[T,A],[In,X,LLbls,_1,_3,Y,Mid],[In,X,LLbls,_1,_3,Mid],[In,X,LLbls,_1,Y,Mid],[In,X,LLbls,_1,Mid],[In,X,_1,_3,Y,Mid],[In,X,_1,_3,Mid],[In,X,_1,Y,Mid],[In,X,_1,Mid],[Out],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[LLbls,_1,_3,Y,Mid],[LLbls,_1,Y],[LLbls,_1,Y,Mid],[_1,_3],[_1,_3,Y],[_1,_3,Y,Mid],[_1,Y],[_1,Y,Mid]]),ground([I,D,Last,_2,ID]);mshare([[T,In,X,_1,_3,Y,Mid,A],[T,In,X,_1,_3,Mid,A],[T,In,X,_1,Y,Mid,A],[T,In,X,_1,Mid,A],[T,In,_1,_3,Y,Mid,A],[T,In,_1,_3,Mid,A],[T,In,_1,Y,Mid,A],[T,In,Mid,A],[T,X,_1,_3,Y,Mid,A],[T,X,_1,_3,Y,A],[T,X,_1,_3,A],[T,X,_1,Y,Mid,A],[T,X,_1,Y,A],[T,X,_1,A],[T,_1,_3,Y,Mid,A],[T,_1,_3,Y,A],[T,_1,_3,A],[T,_1,Y,Mid,A],[T,_1,Y,A],[T,A],[In,X,_1,_3,Y,Mid],[In,X,_1,_3,Mid],[In,X,_1,Y,Mid],[In,X,_1,Mid],[In,_1,_3,Y,Mid],[In,_1,_3,Mid],[In,_1,Y,Mid],[In,Mid],[Out],[X,_1],[X,_1,_3],[X,_1,_3,Y],[X,_1,_3,Y,Mid],[X,_1,Y],[X,_1,Y,Mid],[LLbls],[_1,_3],[_1,_3,Y],[_1,_3,Y,Mid],[_1,Y],[_1,Y,Mid],[_2]]),ground([I,D,Last,ID]);mshare([[T,In,X,_1,_3,Y,Mid,A],[T,In,X,_1,_3,Mid,A],[T,In,X,_1,Y,Mid,A],[T,In,X,_1,Mid,A],[T,In,_1,_3,Y,Mid,A],[T,In,_1,_3,Mid,A],[T,In,_1,Y,Mid,A],[T,In,Mid,A],[T,_1,_3,Y,Mid,A],[T,_1,_3,Y,A],[T,_1,_3,A],[T,_1,Y,Mid,A],[T,_1,Y,A],[T,A],[In,X,_1,_3,Y,Mid],[In,X,_1,_3,Mid],[In,X,_1,Y,Mid],[In,X,_1,Mid],[In,_1,_3,Y,Mid],[In,_1,_3,Mid],[In,_1,Y,Mid],[In,Mid],[Out],[LLbls],[_1,_3],[_1,_3,Y],[_1,_3,Y,Mid],[_1,Y],[_1,Y,Mid],[_2]]),ground([I,D,Last,ID]);mshare([[T,In,X,_1,_3,Y,Mid,A],[T,In,X,_1,_3,Mid,A],[T,In,X,_1,Y,Mid,A],[T,In,X,_1,Mid,A],[T,_1,_3,Y,Mid,A],[T,_1,_3,Y,A],[T,_1,_3,A],[T,_1,Y,Mid,A],[T,_1,Y,A],[T,A],[In,X,_1,_3,Y,Mid],[In,X,_1,_3,Mid],[In,X,_1,Y,Mid],[In,X,_1,Mid],[Out],[LLbls],[_1,_3],[_1,_3,Y],[_1,_3,Y,Mid],[_1,Y],[_1,Y,Mid],[_2]]),ground([I,D,Last,ID]))),
    init(Y,A,Mid,Out,Last,LLbls,_3,_2),
    true((mshare([[T,In,Out,X,LLbls,_1,_2,_3,Y,Mid,A],[T,In,Out,X,LLbls,_1,_2,_3,Mid,A],[T,In,Out,X,LLbls,_1,_3,Y,Mid,A],[T,In,Out,X,LLbls,_1,_3,Mid,A],[T,In,Out,X,LLbls,_1,Mid,A],[T,In,Out,X,_1,_2,_3,Y,Mid,A],[T,In,Out,X,_1,_2,_3,Mid,A],[T,In,Out,X,_1,_3,Y,Mid,A],[T,In,Out,X,_1,_3,Mid,A],[T,In,Out,X,_1,Mid,A],[T,In,Out,LLbls,_1,_2,_3,Y,Mid,A],[T,In,Out,LLbls,_1,_2,_3,Mid,A],[T,In,Out,LLbls,_1,_3,Y,Mid,A],[T,In,Out,LLbls,_1,_3,Mid,A],[T,In,Out,LLbls,Mid,A],[T,In,Out,_1,_2,_3,Y,Mid,A],[T,In,Out,_1,_2,_3,Mid,A],[T,In,Out,_1,_3,Y,Mid,A],[T,In,Out,_1,_3,Mid,A],[T,In,Out,Mid,A],[T,Out,X,LLbls,_1,_2,_3,Y,Mid,A],[T,Out,X,LLbls,_1,_2,_3,Y,A],[T,Out,X,LLbls,_1,_2,_3,A],[T,Out,X,LLbls,_1,_3,Y,Mid,A],[T,Out,X,LLbls,_1,_3,Y,A],[T,Out,X,LLbls,_1,_3,A],[T,Out,X,_1,_2,_3,Y,Mid,A],[T,Out,X,_1,_2,_3,Y,A],[T,Out,X,_1,_2,_3,A],[T,Out,X,_1,_3,Y,Mid,A],[T,Out,X,_1,_3,Y,A],[T,Out,X,_1,_3,A],[T,Out,LLbls,_1,_2,_3,Y,Mid,A],[T,Out,LLbls,_1,_2,_3,Y,A],[T,Out,LLbls,_1,_2,_3,A],[T,Out,LLbls,_1,_3,Y,Mid,A],[T,Out,LLbls,_1,_3,Y,A],[T,Out,LLbls,_1,_3,A],[T,Out,_1,_2,_3,Y,Mid,A],[T,Out,_1,_2,_3,Y,A],[T,Out,_1,_2,_3,A],[T,Out,_1,_3,Y,Mid,A],[T,Out,_1,_3,Y,A],[T,Out,_1,_3,A],[T,X,LLbls,_1,_2,_3,Y,A],[T,X,LLbls,_1,_2,_3,A],[T,X,LLbls,_1,_3,Y,A],[T,X,LLbls,_1,_3,A],[T,X,LLbls,_1,A],[T,X,_1,_2,_3,Y,A],[T,X,_1,_2,_3,A],[T,X,_1,_3,Y,A],[T,X,_1,_3,A],[T,X,_1,A],[T,LLbls,_1,_2,_3,Y,A],[T,LLbls,_1,_2,_3,A],[T,LLbls,_1,_3,Y,A],[T,LLbls,_1,_3,A],[T,LLbls,A],[T,_1,_2,_3,Y,A],[T,_1,_2,_3,A],[T,_1,_3,Y,A],[T,_1,_3,A],[T,A],[In,Out,X,LLbls,_1,_2,_3,Y,Mid],[In,Out,X,LLbls,_1,_2,_3,Mid],[In,Out,X,LLbls,_1,_3,Y,Mid],[In,Out,X,LLbls,_1,_3,Mid],[In,Out,X,LLbls,_1,Mid],[In,Out,X,_1,_2,_3,Y,Mid],[In,Out,X,_1,_2,_3,Mid],[In,Out,X,_1,_3,Y,Mid],[In,Out,X,_1,_3,Mid],[In,Out,X,_1,Mid],[In,Out,LLbls,_1,_2,_3,Y,Mid],[In,Out,LLbls,_1,_2,_3,Mid],[In,Out,LLbls,_1,_3,Y,Mid],[In,Out,LLbls,_1,_3,Mid],[In,Out,LLbls,Mid],[In,Out,_1,_2,_3,Y,Mid],[In,Out,_1,_2,_3,Mid],[In,Out,_1,_3,Y,Mid],[In,Out,_1,_3,Mid],[In,Out,Mid],[Out,X,LLbls,_1,_2,_3],[Out,X,LLbls,_1,_2,_3,Y],[Out,X,LLbls,_1,_2,_3,Y,Mid],[Out,X,LLbls,_1,_3],[Out,X,LLbls,_1,_3,Y],[Out,X,LLbls,_1,_3,Y,Mid],[Out,X,_1,_2,_3],[Out,X,_1,_2,_3,Y],[Out,X,_1,_2,_3,Y,Mid],[Out,X,_1,_3],[Out,X,_1,_3,Y],[Out,X,_1,_3,Y,Mid],[Out,LLbls,_1,_2,_3],[Out,LLbls,_1,_2,_3,Y],[Out,LLbls,_1,_2,_3,Y,Mid],[Out,LLbls,_1,_3],[Out,LLbls,_1,_3,Y],[Out,LLbls,_1,_3,Y,Mid],[Out,_1,_2,_3],[Out,_1,_2,_3,Y],[Out,_1,_2,_3,Y,Mid],[Out,_1,_3],[Out,_1,_3,Y],[Out,_1,_3,Y,Mid],[X,LLbls,_1,_2,_3],[X,LLbls,_1,_2,_3,Y],[X,LLbls,_1,_3],[X,LLbls,_1,_3,Y],[X,_1],[X,_1,_2,_3],[X,_1,_2,_3,Y],[X,_1,_3],[X,_1,_3,Y],[LLbls],[LLbls,_1,_2,_3],[LLbls,_1,_2,_3,Y],[LLbls,_1,_3],[LLbls,_1,_3,Y],[_1,_2,_3],[_1,_2,_3,Y],[_1,_3],[_1,_3,Y]]),ground([I,D,Last,ID]);mshare([[T,In,Out,X,LLbls,_1,_2,_3,Y,Mid,A],[T,In,Out,X,LLbls,_1,_2,_3,Mid,A],[T,In,Out,X,LLbls,_1,_3,Y,Mid,A],[T,In,Out,X,LLbls,_1,_3,Mid,A],[T,In,Out,X,LLbls,_1,Mid,A],[T,In,Out,X,_1,_2,_3,Y,Mid,A],[T,In,Out,X,_1,_2,_3,Mid,A],[T,In,Out,X,_1,_3,Y,Mid,A],[T,In,Out,X,_1,_3,Mid,A],[T,In,Out,X,_1,Mid,A],[T,In,Out,LLbls,_1,_2,_3,Y,Mid,A],[T,In,Out,LLbls,_1,_2,_3,Mid,A],[T,In,Out,LLbls,_1,_3,Y,Mid,A],[T,In,Out,LLbls,_1,_3,Mid,A],[T,In,Out,LLbls,Mid,A],[T,In,Out,_1,_2,_3,Y,Mid,A],[T,In,Out,_1,_2,_3,Mid,A],[T,In,Out,_1,_3,Y,Mid,A],[T,In,Out,_1,_3,Mid,A],[T,In,Out,Mid,A],[T,Out,LLbls,_1,_2,_3,Y,Mid,A],[T,Out,LLbls,_1,_2,_3,Y,A],[T,Out,LLbls,_1,_2,_3,A],[T,Out,LLbls,_1,_3,Y,Mid,A],[T,Out,LLbls,_1,_3,Y,A],[T,Out,LLbls,_1,_3,A],[T,Out,_1,_2,_3,Y,Mid,A],[T,Out,_1,_2,_3,Y,A],[T,Out,_1,_2,_3,A],[T,Out,_1,_3,Y,Mid,A],[T,Out,_1,_3,Y,A],[T,Out,_1,_3,A],[T,LLbls,_1,_2,_3,Y,A],[T,LLbls,_1,_2,_3,A],[T,LLbls,_1,_3,Y,A],[T,LLbls,_1,_3,A],[T,LLbls,A],[T,_1,_2,_3,Y,A],[T,_1,_2,_3,A],[T,_1,_3,Y,A],[T,_1,_3,A],[T,A],[In,Out,X,LLbls,_1,_2,_3,Y,Mid],[In,Out,X,LLbls,_1,_2,_3,Mid],[In,Out,X,LLbls,_1,_3,Y,Mid],[In,Out,X,LLbls,_1,_3,Mid],[In,Out,X,LLbls,_1,Mid],[In,Out,X,_1,_2,_3,Y,Mid],[In,Out,X,_1,_2,_3,Mid],[In,Out,X,_1,_3,Y,Mid],[In,Out,X,_1,_3,Mid],[In,Out,X,_1,Mid],[In,Out,LLbls,_1,_2,_3,Y,Mid],[In,Out,LLbls,_1,_2,_3,Mid],[In,Out,LLbls,_1,_3,Y,Mid],[In,Out,LLbls,_1,_3,Mid],[In,Out,LLbls,Mid],[In,Out,_1,_2,_3,Y,Mid],[In,Out,_1,_2,_3,Mid],[In,Out,_1,_3,Y,Mid],[In,Out,_1,_3,Mid],[In,Out,Mid],[Out,LLbls,_1,_2,_3],[Out,LLbls,_1,_2,_3,Y],[Out,LLbls,_1,_2,_3,Y,Mid],[Out,LLbls,_1,_3],[Out,LLbls,_1,_3,Y],[Out,LLbls,_1,_3,Y,Mid],[Out,_1,_2,_3],[Out,_1,_2,_3,Y],[Out,_1,_2,_3,Y,Mid],[Out,_1,_3],[Out,_1,_3,Y],[Out,_1,_3,Y,Mid],[LLbls],[LLbls,_1,_2,_3],[LLbls,_1,_2,_3,Y],[LLbls,_1,_3],[LLbls,_1,_3,Y],[_1,_2,_3],[_1,_2,_3,Y],[_1,_3],[_1,_3,Y]]),ground([I,D,Last,ID]);mshare([[T,In,Out,X,LLbls,_1,_2,_3,Y,Mid,A],[T,In,Out,X,LLbls,_1,_2,_3,Mid,A],[T,In,Out,X,LLbls,_1,_3,Y,Mid,A],[T,In,Out,X,LLbls,_1,_3,Mid,A],[T,In,Out,X,LLbls,_1,Mid,A],[T,In,Out,X,_1,_2,_3,Y,Mid,A],[T,In,Out,X,_1,_2,_3,Mid,A],[T,In,Out,X,_1,_3,Y,Mid,A],[T,In,Out,X,_1,_3,Mid,A],[T,In,Out,X,_1,Mid,A],[T,Out,LLbls,_1,_2,_3,Y,Mid,A],[T,Out,LLbls,_1,_2,_3,Y,A],[T,Out,LLbls,_1,_2,_3,A],[T,Out,LLbls,_1,_3,Y,Mid,A],[T,Out,LLbls,_1,_3,Y,A],[T,Out,LLbls,_1,_3,A],[T,Out,_1,_2,_3,Y,Mid,A],[T,Out,_1,_2,_3,Y,A],[T,Out,_1,_2,_3,A],[T,Out,_1,_3,Y,Mid,A],[T,Out,_1,_3,Y,A],[T,Out,_1,_3,A],[T,LLbls,_1,_2,_3,Y,A],[T,LLbls,_1,_2,_3,A],[T,LLbls,_1,_3,Y,A],[T,LLbls,_1,_3,A],[T,LLbls,A],[T,_1,_2,_3,Y,A],[T,_1,_2,_3,A],[T,_1,_3,Y,A],[T,_1,_3,A],[T,A],[In,Out,X,LLbls,_1,_2,_3,Y,Mid],[In,Out,X,LLbls,_1,_2,_3,Mid],[In,Out,X,LLbls,_1,_3,Y,Mid],[In,Out,X,LLbls,_1,_3,Mid],[In,Out,X,LLbls,_1,Mid],[In,Out,X,_1,_2,_3,Y,Mid],[In,Out,X,_1,_2,_3,Mid],[In,Out,X,_1,_3,Y,Mid],[In,Out,X,_1,_3,Mid],[In,Out,X,_1,Mid],[Out,LLbls,_1,_2,_3],[Out,LLbls,_1,_2,_3,Y],[Out,LLbls,_1,_2,_3,Y,Mid],[Out,LLbls,_1,_3],[Out,LLbls,_1,_3,Y],[Out,LLbls,_1,_3,Y,Mid],[Out,_1,_2,_3],[Out,_1,_2,_3,Y],[Out,_1,_2,_3,Y,Mid],[Out,_1,_3],[Out,_1,_3,Y],[Out,_1,_3,Y,Mid],[LLbls],[LLbls,_1,_2,_3],[LLbls,_1,_2,_3,Y],[LLbls,_1,_3],[LLbls,_1,_3,Y],[_1,_2,_3],[_1,_2,_3,Y],[_1,_3],[_1,_3,Y]]),ground([I,D,Last,ID]);mshare([[T,In,Out,X,LLbls,_1,_3,Y,Mid,A],[T,In,Out,X,LLbls,_1,_3,Mid,A],[T,In,Out,X,LLbls,_1,Mid,A],[T,In,Out,X,_1,_3,Y,Mid,A],[T,In,Out,X,_1,_3,Mid,A],[T,In,Out,X,_1,Mid,A],[T,In,Out,LLbls,_1,_3,Y,Mid,A],[T,In,Out,LLbls,_1,_3,Mid,A],[T,In,Out,LLbls,Mid,A],[T,In,Out,_1,_3,Y,Mid,A],[T,In,Out,_1,_3,Mid,A],[T,In,Out,Mid,A],[T,Out,X,LLbls,_1,_3,Y,Mid,A],[T,Out,X,LLbls,_1,_3,Y,A],[T,Out,X,LLbls,_1,_3,A],[T,Out,X,_1,_3,Y,Mid,A],[T,Out,X,_1,_3,Y,A],[T,Out,X,_1,_3,A],[T,Out,LLbls,_1,_3,Y,Mid,A],[T,Out,LLbls,_1,_3,Y,A],[T,Out,LLbls,_1,_3,A],[T,Out,_1,_3,Y,Mid,A],[T,Out,_1,_3,Y,A],[T,Out,_1,_3,A],[T,X,LLbls,_1,_3,Y,A],[T,X,LLbls,_1,_3,A],[T,X,LLbls,_1,A],[T,X,_1,_3,Y,A],[T,X,_1,_3,A],[T,X,_1,A],[T,LLbls,_1,_3,Y,A],[T,LLbls,_1,_3,A],[T,LLbls,A],[T,_1,_3,Y,A],[T,_1,_3,A],[T,A],[In,Out,X,LLbls,_1,_3,Y,Mid],[In,Out,X,LLbls,_1,_3,Mid],[In,Out,X,LLbls,_1,Mid],[In,Out,X,_1,_3,Y,Mid],[In,Out,X,_1,_3,Mid],[In,Out,X,_1,Mid],[In,Out,LLbls,_1,_3,Y,Mid],[In,Out,LLbls,_1,_3,Mid],[In,Out,LLbls,Mid],[In,Out,_1,_3,Y,Mid],[In,Out,_1,_3,Mid],[In,Out,Mid],[Out,X,LLbls,_1,_3],[Out,X,LLbls,_1,_3,Y],[Out,X,LLbls,_1,_3,Y,Mid],[Out,X,_1,_3],[Out,X,_1,_3,Y],[Out,X,_1,_3,Y,Mid],[Out,LLbls,_1,_3],[Out,LLbls,_1,_3,Y],[Out,LLbls,_1,_3,Y,Mid],[Out,_1,_3],[Out,_1,_3,Y],[Out,_1,_3,Y,Mid],[X,LLbls,_1],[X,LLbls,_1,_3],[X,LLbls,_1,_3,Y],[X,_1],[X,_1,_3],[X,_1,_3,Y],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[_1,_3],[_1,_3,Y]]),ground([I,D,Last,_2,ID]);mshare([[T,In,Out,X,LLbls,_1,_3,Y,Mid,A],[T,In,Out,X,LLbls,_1,_3,Mid,A],[T,In,Out,X,LLbls,_1,Mid,A],[T,In,Out,X,_1,_3,Y,Mid,A],[T,In,Out,X,_1,_3,Mid,A],[T,In,Out,X,_1,Mid,A],[T,In,Out,LLbls,_1,_3,Y,Mid,A],[T,In,Out,LLbls,_1,_3,Mid,A],[T,In,Out,LLbls,Mid,A],[T,In,Out,_1,_3,Y,Mid,A],[T,In,Out,_1,_3,Mid,A],[T,In,Out,Mid,A],[T,Out,LLbls,_1,_3,Y,Mid,A],[T,Out,LLbls,_1,_3,Y,A],[T,Out,LLbls,_1,_3,A],[T,Out,_1,_3,Y,Mid,A],[T,Out,_1,_3,Y,A],[T,Out,_1,_3,A],[T,LLbls,_1,_3,Y,A],[T,LLbls,_1,_3,A],[T,LLbls,A],[T,_1,_3,Y,A],[T,_1,_3,A],[T,A],[In,Out,X,LLbls,_1,_3,Y,Mid],[In,Out,X,LLbls,_1,_3,Mid],[In,Out,X,LLbls,_1,Mid],[In,Out,X,_1,_3,Y,Mid],[In,Out,X,_1,_3,Mid],[In,Out,X,_1,Mid],[In,Out,LLbls,_1,_3,Y,Mid],[In,Out,LLbls,_1,_3,Mid],[In,Out,LLbls,Mid],[In,Out,_1,_3,Y,Mid],[In,Out,_1,_3,Mid],[In,Out,Mid],[Out,LLbls,_1,_3],[Out,LLbls,_1,_3,Y],[Out,LLbls,_1,_3,Y,Mid],[Out,_1,_3],[Out,_1,_3,Y],[Out,_1,_3,Y,Mid],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[_1,_3],[_1,_3,Y]]),ground([I,D,Last,_2,ID]);mshare([[T,In,Out,X,LLbls,_1,_3,Y,Mid,A],[T,In,Out,X,LLbls,_1,_3,Mid,A],[T,In,Out,X,LLbls,_1,Mid,A],[T,In,Out,X,_1,_3,Y,Mid,A],[T,In,Out,X,_1,_3,Mid,A],[T,In,Out,X,_1,Mid,A],[T,Out,LLbls,_1,_3,Y,Mid,A],[T,Out,LLbls,_1,_3,Y,A],[T,Out,LLbls,_1,_3,A],[T,Out,_1,_3,Y,Mid,A],[T,Out,_1,_3,Y,A],[T,Out,_1,_3,A],[T,LLbls,_1,_3,Y,A],[T,LLbls,_1,_3,A],[T,LLbls,A],[T,_1,_3,Y,A],[T,_1,_3,A],[T,A],[In,Out,X,LLbls,_1,_3,Y,Mid],[In,Out,X,LLbls,_1,_3,Mid],[In,Out,X,LLbls,_1,Mid],[In,Out,X,_1,_3,Y,Mid],[In,Out,X,_1,_3,Mid],[In,Out,X,_1,Mid],[Out,LLbls,_1,_3],[Out,LLbls,_1,_3,Y],[Out,LLbls,_1,_3,Y,Mid],[Out,_1,_3],[Out,_1,_3,Y],[Out,_1,_3,Y,Mid],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Y],[_1,_3],[_1,_3,Y]]),ground([I,D,Last,_2,ID]))).

:- true pred unify_writemode(X,T,In,Last,LLbls,_1,_2)
   : ( (_2=[]),
       mshare([[X],[X,T],[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[LLbls],[LLbls,_1],[_1]]),
       ground([Last]) )
   => ( mshare([[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls,_1],[X,T,_1],[X,In,LLbls,_1],[X,In,_1],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([Last]) ).

:- true pred unify_writemode(X,T,In,Last,LLbls,_1,_2)
   : ( (_2=[]),
       mshare([[X],[X,T],[X,T,In],[X,T,In,_1],[X,T,_1],[X,In],[X,In,_1],[X,_1],[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[LLbls],[_1]]),
       ground([Last]) )
   => ( mshare([[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls,_1],[X,T,_1],[X,In,LLbls,_1],[X,In,_1],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls,_1],[T,In,_1],[T,LLbls,_1],[T,_1],[In],[In,LLbls,_1],[In,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([Last]) ).

:- true pred unify_writemode(X,T,In,Last,LLbls,_1,_2)
   : ( (_2=[]),
       mshare([[X,In],[X,In,_1],[T],[LLbls],[_1]]),
       ground([Last]) )
   => ( mshare([[X,T,In,LLbls,_1],[X,T,In,_1],[X,In,LLbls,_1],[X,In,_1],[T],[T,LLbls,_1],[T,_1],[LLbls],[LLbls,_1],[_1]]),
        ground([Last]) ).

unify_writemode(X,T,In,Last,LLbls,_1,_2) :-
    true((mshare([[X],[X,T],[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[LLbls],[LLbls,_1],[_1],[_3],[Tag],[_4],[_5]]),ground([Last,_2]);mshare([[X],[X,T],[X,T,In],[X,T,In,_1],[X,T,_1],[X,In],[X,In,_1],[X,_1],[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[LLbls],[_1],[_3],[Tag],[_4],[_5]]),ground([Last,_2]);mshare([[X,In],[X,In,_1],[T],[LLbls],[_1],[_3],[Tag],[_4],[_5]]),ground([Last,_2]))),
    my_compound(T),
    !,
    true((mshare([[X],[X,T],[X,T,In],[X,T,In,LLbls],[X,T,In,LLbls,_1],[X,T,In,_1],[X,T,LLbls],[X,T,LLbls,_1],[X,T,_1],[X,In],[X,In,LLbls],[X,In,LLbls,_1],[X,In,_1],[X,LLbls],[X,LLbls,_1],[X,_1],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[LLbls],[LLbls,_1],[_1],[_3],[Tag],[_4],[_5]]),ground([Last,_2]);mshare([[X],[X,T],[X,T,In],[X,T,In,_1],[X,T,_1],[X,In],[X,In,_1],[X,_1],[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[LLbls],[_1],[_3],[Tag],[_4],[_5]]),ground([Last,_2]);mshare([[X,In],[X,In,_1],[T],[LLbls],[_1],[_3],[Tag],[_4],[_5]]),ground([Last,_2]))),
    'C'(_1,move(Tag^h,[X]),_3),
    true((mshare([[X,T,In,LLbls,_1],[X,T,In,LLbls,_1,_3],[X,T,In,LLbls,_1,_3,Tag],[X,T,In,LLbls,_1,Tag],[X,T,In,_1],[X,T,In,_1,_3],[X,T,In,_1,_3,Tag],[X,T,In,_1,Tag],[X,T,LLbls,_1],[X,T,LLbls,_1,_3],[X,T,LLbls,_1,_3,Tag],[X,T,LLbls,_1,Tag],[X,T,_1],[X,T,_1,_3],[X,T,_1,_3,Tag],[X,T,_1,Tag],[X,In,LLbls,_1],[X,In,LLbls,_1,_3],[X,In,LLbls,_1,_3,Tag],[X,In,LLbls,_1,Tag],[X,In,_1],[X,In,_1,_3],[X,In,_1,_3,Tag],[X,In,_1,Tag],[X,LLbls,_1],[X,LLbls,_1,_3],[X,LLbls,_1,_3,Tag],[X,LLbls,_1,Tag],[X,_1],[X,_1,_3],[X,_1,_3,Tag],[X,_1,Tag],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,LLbls,_1,_3,Tag],[T,In,LLbls,_1,Tag],[T,In,_1,_3],[T,In,_1,_3,Tag],[T,In,_1,Tag],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,Tag],[T,LLbls,_1,Tag],[T,_1,_3],[T,_1,_3,Tag],[T,_1,Tag],[In],[In,LLbls],[In,LLbls,_1,_3],[In,LLbls,_1,_3,Tag],[In,LLbls,_1,Tag],[In,_1,_3],[In,_1,_3,Tag],[In,_1,Tag],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,Tag],[LLbls,_1,Tag],[_1,_3],[_1,_3,Tag],[_1,Tag],[_4],[_5]]),ground([Last,_2]);mshare([[X,T,In,_1],[X,T,In,_1,_3],[X,T,In,_1,_3,Tag],[X,T,In,_1,Tag],[X,T,_1],[X,T,_1,_3],[X,T,_1,_3,Tag],[X,T,_1,Tag],[X,In,_1],[X,In,_1,_3],[X,In,_1,_3,Tag],[X,In,_1,Tag],[X,_1],[X,_1,_3],[X,_1,_3,Tag],[X,_1,Tag],[T],[T,In],[T,In,_1,_3],[T,In,_1,_3,Tag],[T,In,_1,Tag],[T,_1,_3],[T,_1,_3,Tag],[T,_1,Tag],[In],[In,_1,_3],[In,_1,_3,Tag],[In,_1,Tag],[LLbls],[_1,_3],[_1,_3,Tag],[_1,Tag],[_4],[_5]]),ground([Last,_2]);mshare([[X,In,_1],[X,In,_1,_3],[X,In,_1,_3,Tag],[X,In,_1,Tag],[T],[LLbls],[_1,_3],[_1,_3,Tag],[_1,Tag],[_4],[_5]]),ground([Last,_2]))),
    termtag(T,Tag),
    true((mshare([[X,T,In,LLbls,_1],[X,T,In,LLbls,_1,_3],[X,T,In,_1],[X,T,In,_1,_3],[X,T,LLbls,_1],[X,T,LLbls,_1,_3],[X,T,_1],[X,T,_1,_3],[X,In,LLbls,_1],[X,In,LLbls,_1,_3],[X,In,_1],[X,In,_1,_3],[X,LLbls,_1],[X,LLbls,_1,_3],[X,_1],[X,_1,_3],[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,_1,_3],[T,LLbls],[T,LLbls,_1,_3],[T,_1,_3],[In],[In,LLbls],[In,LLbls,_1,_3],[In,_1,_3],[LLbls],[LLbls,_1,_3],[_1,_3],[_4],[_5]]),ground([Last,_2,Tag]);mshare([[X,T,In,_1],[X,T,In,_1,_3],[X,T,_1],[X,T,_1,_3],[X,In,_1],[X,In,_1,_3],[X,_1],[X,_1,_3],[T],[T,In],[T,In,_1,_3],[T,_1,_3],[In],[In,_1,_3],[LLbls],[_1,_3],[_4],[_5]]),ground([Last,_2,Tag]);mshare([[X,In,_1],[X,In,_1,_3],[T],[LLbls],[_1,_3],[_4],[_5]]),ground([Last,_2,Tag]))),
    unify_block(Last,T,_4,In,_5,LLbls,_3,_2),
    true((mshare([[X,T,In,LLbls,_1,_3,_5],[X,T,In,LLbls,_1,_5],[X,T,In,_1,_3,_5],[X,T,In,_1,_5],[X,T,LLbls,_1],[X,T,LLbls,_1,_3],[X,T,LLbls,_1,_3,_5],[X,T,LLbls,_1,_5],[X,T,_1],[X,T,_1,_3],[X,T,_1,_3,_5],[X,T,_1,_5],[X,In,LLbls,_1,_3,_5],[X,In,LLbls,_1,_5],[X,In,_1,_3,_5],[X,In,_1,_5],[X,LLbls,_1],[X,LLbls,_1,_3],[X,_1],[X,_1,_3],[T],[T,In,LLbls,_1,_3,_5],[T,In,LLbls,_5],[T,In,_1,_3,_5],[T,In,_5],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,_5],[T,LLbls,_5],[T,_1,_3],[T,_1,_3,_5],[T,_5],[In,LLbls,_1,_3,_5],[In,LLbls,_5],[In,_1,_3,_5],[In,_5],[LLbls],[LLbls,_1,_3],[_1,_3]]),ground([Last,_2,Tag,_4]);mshare([[X,T,In,LLbls,_1,_3,_5],[X,T,In,_1,_3,_5],[X,T,In,_1,_5],[X,T,LLbls,_1,_3],[X,T,LLbls,_1,_3,_5],[X,T,_1],[X,T,_1,_3],[X,T,_1,_3,_5],[X,T,_1,_5],[X,In,LLbls,_1,_3,_5],[X,In,_1,_3,_5],[X,In,_1,_5],[X,LLbls,_1,_3],[X,_1],[X,_1,_3],[T],[T,In,LLbls,_1,_3,_5],[T,In,_1,_3,_5],[T,In,_5],[T,LLbls,_1,_3],[T,LLbls,_1,_3,_5],[T,_1,_3],[T,_1,_3,_5],[T,_5],[In,LLbls,_1,_3,_5],[In,_1,_3,_5],[In,_5],[LLbls],[LLbls,_1,_3],[_1,_3]]),ground([Last,_2,Tag,_4]);mshare([[X,T,In,LLbls,_1,_3,_5],[X,T,In,_1,_3,_5],[X,T,In,_1,_5],[X,In,LLbls,_1,_3,_5],[X,In,_1,_3,_5],[X,In,_1,_5],[T],[T,LLbls,_1,_3],[T,LLbls,_1,_3,_5],[T,_1,_3],[T,_1,_3,_5],[T,_5],[LLbls],[LLbls,_1,_3],[_1,_3]]),ground([Last,_2,Tag,_4]))).
unify_writemode(X,T,_1,_2,_3,_4,_5) :-
    true((mshare([[X],[X,T],[X,T,_1],[X,T,_1,_3],[X,T,_1,_3,_4],[X,T,_1,_4],[X,T,_3],[X,T,_3,_4],[X,T,_4],[X,_1],[X,_1,_3],[X,_1,_3,_4],[X,_1,_4],[X,_3],[X,_3,_4],[X,_4],[T],[T,_1],[T,_1,_3],[T,_1,_3,_4],[T,_1,_4],[T,_3],[T,_3,_4],[T,_4],[_1],[_1,_3],[_1,_3,_4],[_1,_4],[_3],[_3,_4],[_4]]),ground([_2,_5]);mshare([[X],[X,T],[X,T,_1],[X,T,_1,_4],[X,T,_4],[X,_1],[X,_1,_4],[X,_4],[T],[T,_1],[T,_1,_4],[T,_4],[_1],[_1,_4],[_3],[_4]]),ground([_2,_5]);mshare([[X,_1],[X,_1,_4],[T],[_3],[_4]]),ground([_2,_5]))),
    atomic(T),
    !,
    true((mshare([[X],[X,_1],[X,_1,_3],[X,_1,_3,_4],[X,_1,_4],[X,_3],[X,_3,_4],[X,_4],[_1],[_1,_3],[_1,_3,_4],[_1,_4],[_3],[_3,_4],[_4]]),ground([T,_2,_5]);mshare([[X],[X,_1],[X,_1,_4],[X,_4],[_1],[_1,_4],[_3],[_4]]),ground([T,_2,_5]);mshare([[X,_1],[X,_1,_4],[_3],[_4]]),ground([T,_2,_5]))),
    'C'(_4,move(tatm^T,[X]),_5),
    true((mshare([[X,_1,_3,_4],[X,_1,_4],[X,_3,_4],[X,_4],[_1],[_1,_3],[_3]]),ground([T,_2,_5]);mshare([[X,_1,_4],[X,_4],[_1],[_3]]),ground([T,_2,_5]);mshare([[X,_1,_4],[_3]]),ground([T,_2,_5]))).

:- true pred unify_block(_A,T,Size,In,Out,_B,_1,_2)
   : ( mshare([[T],[T,In],[T,In,_1],[T,_1],[Size],[In],[In,_1],[Out],[_B],[_1]]),
       ground([_A,_2]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_B,_1],[T,In,Out,_1],[T,Out],[T,Out,_B,_1],[T,Out,_1],[T,_B,_1],[T,_1],[In,Out],[In,Out,_B,_1],[In,Out,_1],[_B],[_B,_1],[_1]]),
        ground([_A,Size,_2]) ).

:- true pred unify_block(_A,T,Size,In,Out,_B,_1,_2)
   : ( mshare([[T],[T,In],[T,In,_B],[T,In,_B,_1],[T,In,_1],[T,_B],[T,_B,_1],[T,_1],[Size],[In],[In,_B],[In,_B,_1],[In,_1],[Out],[_B],[_B,_1],[_1]]),
       ground([_A,_2]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_B],[T,In,Out,_B,_1],[T,In,Out,_1],[T,Out],[T,Out,_B],[T,Out,_B,_1],[T,Out,_1],[T,_B],[T,_B,_1],[T,_1],[In,Out],[In,Out,_B],[In,Out,_B,_1],[In,Out,_1],[_B],[_B,_1],[_1]]),
        ground([_A,Size,_2]) ).

:- true pred unify_block(_A,T,Size,In,Out,_B,_1,_2)
   : ( mshare([[T],[Size],[In],[In,_1],[Out],[_B],[_1]]),
       ground([_A,_2]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_B,_1],[T,In,Out,_1],[T,Out],[T,Out,_B,_1],[T,Out,_1],[T,_B,_1],[T,_1],[In,Out],[In,Out,_B,_1],[In,Out,_1],[_B],[_B,_1],[_1]]),
        ground([_A,Size,_2]) ).

:- true pred unify_block(_A,T,Size,In,Out,_B,_1,_2)
   : ( (_A=nonlast),
       mshare([[T],[Size],[In],[In,_1],[Out],[_B],[_1]]),
       ground([_2]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,_B,_1],[T,In,Out,_1],[T,Out],[T,Out,_B,_1],[T,Out,_1],[T,_B,_1],[T,_1],[In,Out],[In,Out,_B,_1],[In,Out,_1],[_B],[_B,_1],[_1]]),
        ground([Size,_2]) ).

unify_block(last,T,Size,In,In,[Lbl|_3],_1,_2) :-
    !,
    true((mshare([[T],[T,In],[T,In,_1],[T,In,_1,Lbl],[T,In,_1,Lbl,_3],[T,In,_1,_3],[T,In,Lbl],[T,In,Lbl,_3],[T,In,_3],[T,_1],[T,_1,Lbl],[T,_1,Lbl,_3],[T,_1,_3],[T,Lbl],[T,Lbl,_3],[T,_3],[Size],[In],[In,_1],[In,_1,Lbl],[In,_1,Lbl,_3],[In,_1,_3],[In,Lbl],[In,Lbl,_3],[In,_3],[_1],[_1,Lbl],[_1,Lbl,_3],[_1,_3],[Lbl],[Lbl,_3],[_3],[_4]]),ground([_2]);mshare([[T],[T,In],[T,In,_1],[T,_1],[Size],[In],[In,_1],[_1],[Lbl],[Lbl,_3],[_3],[_4]]),ground([_2]);mshare([[T],[Size],[In],[In,_1],[_1],[Lbl],[Lbl,_3],[_3],[_4]]),ground([_2]))),
    'C'(_1,add(Size,h),_4),
    true((mshare([[T],[T,Size,In,_1],[T,Size,In,_1,Lbl],[T,Size,In,_1,Lbl,_3],[T,Size,In,_1,Lbl,_3,_4],[T,Size,In,_1,Lbl,_4],[T,Size,In,_1,_3],[T,Size,In,_1,_3,_4],[T,Size,In,_1,_4],[T,Size,_1],[T,Size,_1,Lbl],[T,Size,_1,Lbl,_3],[T,Size,_1,Lbl,_3,_4],[T,Size,_1,Lbl,_4],[T,Size,_1,_3],[T,Size,_1,_3,_4],[T,Size,_1,_4],[T,In],[T,In,_1,Lbl,_3,_4],[T,In,_1,Lbl,_4],[T,In,_1,_3,_4],[T,In,_1,_4],[T,In,Lbl],[T,In,Lbl,_3],[T,In,_3],[T,_1,Lbl,_3,_4],[T,_1,Lbl,_4],[T,_1,_3,_4],[T,_1,_4],[T,Lbl],[T,Lbl,_3],[T,_3],[Size,In,_1],[Size,In,_1,Lbl],[Size,In,_1,Lbl,_3],[Size,In,_1,Lbl,_3,_4],[Size,In,_1,Lbl,_4],[Size,In,_1,_3],[Size,In,_1,_3,_4],[Size,In,_1,_4],[Size,_1],[Size,_1,Lbl],[Size,_1,Lbl,_3],[Size,_1,Lbl,_3,_4],[Size,_1,Lbl,_4],[Size,_1,_3],[Size,_1,_3,_4],[Size,_1,_4],[In],[In,_1,Lbl,_3,_4],[In,_1,Lbl,_4],[In,_1,_3,_4],[In,_1,_4],[In,Lbl],[In,Lbl,_3],[In,_3],[_1,Lbl,_3,_4],[_1,Lbl,_4],[_1,_3,_4],[_1,_4],[Lbl],[Lbl,_3],[_3]]),ground([_2]);mshare([[T],[T,Size,In,_1],[T,Size,In,_1,_4],[T,Size,_1],[T,Size,_1,_4],[T,In],[T,In,_1,_4],[T,_1,_4],[Size,In,_1],[Size,In,_1,_4],[Size,_1],[Size,_1,_4],[In],[In,_1,_4],[_1,_4],[Lbl],[Lbl,_3],[_3]]),ground([_2]);mshare([[T],[Size,In,_1],[Size,In,_1,_4],[Size,_1],[Size,_1,_4],[In],[In,_1,_4],[_1,_4],[Lbl],[Lbl,_3],[_3]]),ground([_2]))),
    'C'(_4,jump(Lbl),_2),
    true((mshare([[T],[T,Size,In,_1],[T,Size,In,_1,Lbl,_3,_4],[T,Size,In,_1,Lbl,_4],[T,Size,In,_1,_3],[T,Size,_1],[T,Size,_1,Lbl,_3,_4],[T,Size,_1,Lbl,_4],[T,Size,_1,_3],[T,In],[T,In,_1,Lbl,_3,_4],[T,In,_1,Lbl,_4],[T,In,_3],[T,_1,Lbl,_3,_4],[T,_1,Lbl,_4],[T,_3],[Size,In,_1],[Size,In,_1,Lbl,_3,_4],[Size,In,_1,Lbl,_4],[Size,In,_1,_3],[Size,_1],[Size,_1,Lbl,_3,_4],[Size,_1,Lbl,_4],[Size,_1,_3],[In],[In,_1,Lbl,_3,_4],[In,_1,Lbl,_4],[In,_3],[_1,Lbl,_3,_4],[_1,Lbl,_4],[_3]]),ground([_2]);mshare([[T],[T,Size,In,_1],[T,Size,In,_1,Lbl,_3,_4],[T,Size,In,_1,Lbl,_4],[T,Size,_1],[T,Size,_1,Lbl,_3,_4],[T,Size,_1,Lbl,_4],[T,In],[T,In,_1,Lbl,_3,_4],[T,In,_1,Lbl,_4],[T,_1,Lbl,_3,_4],[T,_1,Lbl,_4],[Size,In,_1],[Size,In,_1,Lbl,_3,_4],[Size,In,_1,Lbl,_4],[Size,_1],[Size,_1,Lbl,_3,_4],[Size,_1,Lbl,_4],[In],[In,_1,Lbl,_3,_4],[In,_1,Lbl,_4],[_1,Lbl,_3,_4],[_1,Lbl,_4],[_3]]),ground([_2]);mshare([[T],[Size,In,_1],[Size,In,_1,Lbl,_3,_4],[Size,In,_1,Lbl,_4],[Size,_1],[Size,_1,Lbl,_3,_4],[Size,_1,Lbl,_4],[In],[In,_1,Lbl,_3,_4],[In,_1,Lbl,_4],[_1,Lbl,_3,_4],[_1,Lbl,_4],[_3]]),ground([_2]))),
    unify:size(T,0,Size),
    true((mshare([[T],[T,In],[T,In,_1,Lbl,_3,_4],[T,In,_1,Lbl,_4],[T,In,_3],[T,_1,Lbl,_3,_4],[T,_1,Lbl,_4],[T,_3],[In],[In,_1,Lbl,_3,_4],[In,_1,Lbl,_4],[In,_3],[_1,Lbl,_3,_4],[_1,Lbl,_4],[_3]]),ground([Size,_2]);mshare([[T],[T,In],[T,In,_1,Lbl,_3,_4],[T,In,_1,Lbl,_4],[T,_1,Lbl,_3,_4],[T,_1,Lbl,_4],[In],[In,_1,Lbl,_3,_4],[In,_1,Lbl,_4],[_1,Lbl,_3,_4],[_1,Lbl,_4],[_3]]),ground([Size,_2]);mshare([[T],[In],[In,_1,Lbl,_3,_4],[In,_1,Lbl,_4],[_1,Lbl,_3,_4],[_1,Lbl,_4],[_3]]),ground([Size,_2]))).
unify_block(nonlast,T,Size,In,Out,[_3|LLbls],_1,_2) :-
    !,
    true((mshare([[T],[T,In],[T,In,_1],[T,In,_1,_3],[T,In,_1,_3,LLbls],[T,In,_1,LLbls],[T,In,_3],[T,In,_3,LLbls],[T,In,LLbls],[T,_1],[T,_1,_3],[T,_1,_3,LLbls],[T,_1,LLbls],[T,_3],[T,_3,LLbls],[T,LLbls],[Size],[In],[In,_1],[In,_1,_3],[In,_1,_3,LLbls],[In,_1,LLbls],[In,_3],[In,_3,LLbls],[In,LLbls],[Out],[_1],[_1,_3],[_1,_3,LLbls],[_1,LLbls],[_3],[_3,LLbls],[LLbls],[_4],[Offset]]),ground([_2]);mshare([[T],[T,In],[T,In,_1],[T,_1],[Size],[In],[In,_1],[Out],[_1],[_3],[_3,LLbls],[LLbls],[_4],[Offset]]),ground([_2]);mshare([[T],[Size],[In],[In,_1],[Out],[_1],[_3],[_3,LLbls],[LLbls],[_4],[Offset]]),ground([_2]))),
    'C'(_1,add(Size,h),_4),
    true((mshare([[T],[T,Size,In,_1],[T,Size,In,_1,_3],[T,Size,In,_1,_3,LLbls],[T,Size,In,_1,_3,LLbls,_4],[T,Size,In,_1,_3,_4],[T,Size,In,_1,LLbls],[T,Size,In,_1,LLbls,_4],[T,Size,In,_1,_4],[T,Size,_1],[T,Size,_1,_3],[T,Size,_1,_3,LLbls],[T,Size,_1,_3,LLbls,_4],[T,Size,_1,_3,_4],[T,Size,_1,LLbls],[T,Size,_1,LLbls,_4],[T,Size,_1,_4],[T,In],[T,In,_1,_3,LLbls,_4],[T,In,_1,_3,_4],[T,In,_1,LLbls,_4],[T,In,_1,_4],[T,In,_3],[T,In,_3,LLbls],[T,In,LLbls],[T,_1,_3,LLbls,_4],[T,_1,_3,_4],[T,_1,LLbls,_4],[T,_1,_4],[T,_3],[T,_3,LLbls],[T,LLbls],[Size,In,_1],[Size,In,_1,_3],[Size,In,_1,_3,LLbls],[Size,In,_1,_3,LLbls,_4],[Size,In,_1,_3,_4],[Size,In,_1,LLbls],[Size,In,_1,LLbls,_4],[Size,In,_1,_4],[Size,_1],[Size,_1,_3],[Size,_1,_3,LLbls],[Size,_1,_3,LLbls,_4],[Size,_1,_3,_4],[Size,_1,LLbls],[Size,_1,LLbls,_4],[Size,_1,_4],[In],[In,_1,_3,LLbls,_4],[In,_1,_3,_4],[In,_1,LLbls,_4],[In,_1,_4],[In,_3],[In,_3,LLbls],[In,LLbls],[Out],[_1,_3,LLbls,_4],[_1,_3,_4],[_1,LLbls,_4],[_1,_4],[_3],[_3,LLbls],[LLbls],[Offset]]),ground([_2]);mshare([[T],[T,Size,In,_1],[T,Size,In,_1,_4],[T,Size,_1],[T,Size,_1,_4],[T,In],[T,In,_1,_4],[T,_1,_4],[Size,In,_1],[Size,In,_1,_4],[Size,_1],[Size,_1,_4],[In],[In,_1,_4],[Out],[_1,_4],[_3],[_3,LLbls],[LLbls],[Offset]]),ground([_2]);mshare([[T],[Size,In,_1],[Size,In,_1,_4],[Size,_1],[Size,_1,_4],[In],[In,_1,_4],[Out],[_1,_4],[_3],[_3,LLbls],[LLbls],[Offset]]),ground([_2]))),
    unify:size(T,0,Size),
    true((mshare([[T],[T,In],[T,In,_1,_3,LLbls,_4],[T,In,_1,_3,_4],[T,In,_1,LLbls,_4],[T,In,_1,_4],[T,In,_3],[T,In,_3,LLbls],[T,In,LLbls],[T,_1,_3,LLbls,_4],[T,_1,_3,_4],[T,_1,LLbls,_4],[T,_1,_4],[T,_3],[T,_3,LLbls],[T,LLbls],[In],[In,_1,_3,LLbls,_4],[In,_1,_3,_4],[In,_1,LLbls,_4],[In,_1,_4],[In,_3],[In,_3,LLbls],[In,LLbls],[Out],[_1,_3,LLbls,_4],[_1,_3,_4],[_1,LLbls,_4],[_1,_4],[_3],[_3,LLbls],[LLbls],[Offset]]),ground([Size,_2]);mshare([[T],[T,In],[T,In,_1,_4],[T,_1,_4],[In],[In,_1,_4],[Out],[_1,_4],[_3],[_3,LLbls],[LLbls],[Offset]]),ground([Size,_2]);mshare([[T],[In],[In,_1,_4],[Out],[_1,_4],[_3],[_3,LLbls],[LLbls],[Offset]]),ground([Size,_2]))),
    Offset is-Size,
    true((mshare([[T],[T,In],[T,In,_1,_3,LLbls,_4],[T,In,_1,_3,_4],[T,In,_1,LLbls,_4],[T,In,_1,_4],[T,In,_3],[T,In,_3,LLbls],[T,In,LLbls],[T,_1,_3,LLbls,_4],[T,_1,_3,_4],[T,_1,LLbls,_4],[T,_1,_4],[T,_3],[T,_3,LLbls],[T,LLbls],[In],[In,_1,_3,LLbls,_4],[In,_1,_3,_4],[In,_1,LLbls,_4],[In,_1,_4],[In,_3],[In,_3,LLbls],[In,LLbls],[Out],[_1,_3,LLbls,_4],[_1,_3,_4],[_1,LLbls,_4],[_1,_4],[_3],[_3,LLbls],[LLbls]]),ground([Size,_2,Offset]);mshare([[T],[T,In],[T,In,_1,_4],[T,_1,_4],[In],[In,_1,_4],[Out],[_1,_4],[_3],[_3,LLbls],[LLbls]]),ground([Size,_2,Offset]);mshare([[T],[In],[In,_1,_4],[Out],[_1,_4],[_3],[_3,LLbls],[LLbls]]),ground([Size,_2,Offset]))),
    block(T,Offset,0,In,Out,LLbls,_4,_2),
    true((mshare([[T],[T,In,Out],[T,In,Out,_1,_3,LLbls,_4],[T,In,Out,_1,_3,_4],[T,In,Out,_1,LLbls,_4],[T,In,Out,_1,_4],[T,In,Out,_3],[T,Out],[T,Out,_1,_3,LLbls,_4],[T,Out,_1,_3,_4],[T,Out,_1,LLbls,_4],[T,Out,_1,_4],[T,Out,_3],[T,_1,_3,LLbls,_4],[T,_1,_3,_4],[T,_1,LLbls,_4],[T,_1,_4],[T,_3],[In,Out],[In,Out,_1,_3,LLbls,_4],[In,Out,_1,_3,_4],[In,Out,_1,LLbls,_4],[In,Out,_1,_4],[In,Out,_3],[_1,_3,LLbls,_4],[_1,_3,_4],[_1,LLbls,_4],[_1,_4],[_3]]),ground([Size,_2,Offset]);mshare([[T],[T,In,Out],[T,In,Out,_1,_3,LLbls,_4],[T,In,Out,_1,LLbls,_4],[T,In,Out,_1,_4],[T,Out],[T,Out,_1,_3,LLbls,_4],[T,Out,_1,LLbls,_4],[T,Out,_1,_4],[T,_1,_3,LLbls,_4],[T,_1,LLbls,_4],[T,_1,_4],[In,Out],[In,Out,_1,_3,LLbls,_4],[In,Out,_1,LLbls,_4],[In,Out,_1,_4],[_1,_3,LLbls,_4],[_1,LLbls,_4],[_1,_4],[_3]]),ground([Size,_2,Offset]))).

:- true pred block(T,Inf,Outf,In,Out,LLbls,_1,_2)
   : ( mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[Outf],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[_2]]),
       ground([Inf]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,LLbls,_1],[T,In,Out,LLbls,_1,_2],[T,In,Out,_1],[T,In,Out,_1,_2],[T,Out],[T,Out,LLbls,_1],[T,Out,LLbls,_1,_2],[T,Out,_1],[T,Out,_1,_2],[T,LLbls,_1],[T,LLbls,_1,_2],[T,_1],[T,_1,_2],[In,Out],[In,Out,LLbls,_1],[In,Out,LLbls,_1,_2],[In,Out,_1],[In,Out,_1,_2],[LLbls,_1],[LLbls,_1,_2],[_1],[_1,_2]]),
        ground([Inf,Outf]) ).

:- true pred block(T,Inf,Outf,In,Out,LLbls,_1,_2)
   : ( (Outf=0),
       mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[LLbls],[_1]]),
       ground([Inf,_2]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,LLbls,_1],[T,In,Out,_1],[T,Out],[T,Out,LLbls,_1],[T,Out,_1],[T,LLbls,_1],[T,_1],[In,Out],[In,Out,LLbls,_1],[In,Out,_1],[LLbls,_1],[_1]]),
        ground([Inf,_2]) ).

:- true pred block(T,Inf,Outf,In,Out,LLbls,_1,_2)
   : ( (Outf=0),
       mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1]]),
       ground([Inf,_2]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,LLbls,_1],[T,In,Out,_1],[T,Out],[T,Out,LLbls,_1],[T,Out,_1],[T,LLbls,_1],[T,_1],[In,Out],[In,Out,LLbls,_1],[In,Out,_1],[LLbls,_1],[_1]]),
        ground([Inf,_2]) ).

:- true pred block(T,Inf,Outf,In,Out,LLbls,_1,_2)
   : ( mshare([[T],[T,In],[T,In,_1],[T,_1],[Outf],[In],[In,_1],[Out],[LLbls],[_1],[_2]]),
       ground([Inf]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,LLbls,_1],[T,In,Out,LLbls,_1,_2],[T,In,Out,_1],[T,In,Out,_1,_2],[T,Out],[T,Out,LLbls,_1],[T,Out,LLbls,_1,_2],[T,Out,_1],[T,Out,_1,_2],[T,LLbls,_1],[T,LLbls,_1,_2],[T,_1],[T,_1,_2],[In,Out],[In,Out,LLbls,_1],[In,Out,LLbls,_1,_2],[In,Out,_1],[In,Out,_1,_2],[LLbls,_1],[LLbls,_1,_2],[_1],[_1,_2]]),
        ground([Inf,Outf]) ).

:- true pred block(T,Inf,Outf,In,Out,LLbls,_1,_2)
   : ( mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1]]),
       ground([Inf,Outf,_2]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,LLbls,_1],[T,In,Out,_1],[T,Out],[T,Out,LLbls,_1],[T,Out,_1],[T,LLbls,_1],[T,_1],[In,Out],[In,Out,LLbls,_1],[In,Out,_1],[LLbls,_1],[_1]]),
        ground([Inf,Outf,_2]) ).

:- true pred block(T,Inf,Outf,In,Out,LLbls,_1,_2)
   : ( (Outf=0),
       mshare([[T],[In],[In,_1],[Out],[LLbls],[_1]]),
       ground([Inf,_2]) )
   => ( mshare([[T],[T,In,Out],[T,In,Out,LLbls,_1],[T,In,Out,_1],[T,Out],[T,Out,LLbls,_1],[T,Out,_1],[T,LLbls,_1],[T,_1],[In,Out],[In,Out,LLbls,_1],[In,Out,_1],[LLbls,_1],[_1]]),
        ground([Inf,_2]) ).

block(T,Inf,Outf,In,Out,LLbls,_1,_2) :-
    true((mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[Outf],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[_2],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf]);mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]);mshare([[T],[T,In],[T,In,_1],[T,_1],[Outf],[In],[In,_1],[Out],[LLbls],[_1],[_2],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf]);mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[LLbls],[_1],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]);mshare([[T],[In],[In,_1],[Out],[LLbls],[_1],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]))),
    structure(T),
    !,
    true((mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[Outf],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[_2],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf]);mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]);mshare([[T],[T,In],[T,In,_1],[T,_1],[Outf],[In],[In,_1],[Out],[LLbls],[_1],[_2],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf]);mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[LLbls],[_1],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]);mshare([[T],[In],[In,_1],[Out],[LLbls],[_1],[_3],[F],[N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]))),
    'C'(_1,move(tatm^(F/N),[h+Inf]),_3),
    true((mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,LLbls,_1,_3,F],[T,In,LLbls,_1,_3,F,N],[T,In,LLbls,_1,_3,N],[T,In,LLbls,_1,F],[T,In,LLbls,_1,F,N],[T,In,LLbls,_1,N],[T,In,_1,_3],[T,In,_1,_3,F],[T,In,_1,_3,F,N],[T,In,_1,_3,N],[T,In,_1,F],[T,In,_1,F,N],[T,In,_1,N],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,F],[T,LLbls,_1,_3,F,N],[T,LLbls,_1,_3,N],[T,LLbls,_1,F],[T,LLbls,_1,F,N],[T,LLbls,_1,N],[T,_1,_3],[T,_1,_3,F],[T,_1,_3,F,N],[T,_1,_3,N],[T,_1,F],[T,_1,F,N],[T,_1,N],[Outf],[In],[In,LLbls],[In,LLbls,_1,_3],[In,LLbls,_1,_3,F],[In,LLbls,_1,_3,F,N],[In,LLbls,_1,_3,N],[In,LLbls,_1,F],[In,LLbls,_1,F,N],[In,LLbls,_1,N],[In,_1,_3],[In,_1,_3,F],[In,_1,_3,F,N],[In,_1,_3,N],[In,_1,F],[In,_1,F,N],[In,_1,N],[Out],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,F],[LLbls,_1,_3,F,N],[LLbls,_1,_3,N],[LLbls,_1,F],[LLbls,_1,F,N],[LLbls,_1,N],[_1,_3],[_1,_3,F],[_1,_3,F,N],[_1,_3,N],[_1,F],[_1,F,N],[_1,N],[_2],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf]);mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,LLbls,_1,_3,F],[T,In,LLbls,_1,_3,F,N],[T,In,LLbls,_1,_3,N],[T,In,LLbls,_1,F],[T,In,LLbls,_1,F,N],[T,In,LLbls,_1,N],[T,In,_1,_3],[T,In,_1,_3,F],[T,In,_1,_3,F,N],[T,In,_1,_3,N],[T,In,_1,F],[T,In,_1,F,N],[T,In,_1,N],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,F],[T,LLbls,_1,_3,F,N],[T,LLbls,_1,_3,N],[T,LLbls,_1,F],[T,LLbls,_1,F,N],[T,LLbls,_1,N],[T,_1,_3],[T,_1,_3,F],[T,_1,_3,F,N],[T,_1,_3,N],[T,_1,F],[T,_1,F,N],[T,_1,N],[In],[In,LLbls],[In,LLbls,_1,_3],[In,LLbls,_1,_3,F],[In,LLbls,_1,_3,F,N],[In,LLbls,_1,_3,N],[In,LLbls,_1,F],[In,LLbls,_1,F,N],[In,LLbls,_1,N],[In,_1,_3],[In,_1,_3,F],[In,_1,_3,F,N],[In,_1,_3,N],[In,_1,F],[In,_1,F,N],[In,_1,N],[Out],[LLbls],[LLbls,_1,_3],[LLbls,_1,_3,F],[LLbls,_1,_3,F,N],[LLbls,_1,_3,N],[LLbls,_1,F],[LLbls,_1,F,N],[LLbls,_1,N],[_1,_3],[_1,_3,F],[_1,_3,F,N],[_1,_3,N],[_1,F],[_1,F,N],[_1,N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]);mshare([[T],[T,In],[T,In,_1,_3],[T,In,_1,_3,F],[T,In,_1,_3,F,N],[T,In,_1,_3,N],[T,In,_1,F],[T,In,_1,F,N],[T,In,_1,N],[T,_1,_3],[T,_1,_3,F],[T,_1,_3,F,N],[T,_1,_3,N],[T,_1,F],[T,_1,F,N],[T,_1,N],[Outf],[In],[In,_1,_3],[In,_1,_3,F],[In,_1,_3,F,N],[In,_1,_3,N],[In,_1,F],[In,_1,F,N],[In,_1,N],[Out],[LLbls],[_1,_3],[_1,_3,F],[_1,_3,F,N],[_1,_3,N],[_1,F],[_1,F,N],[_1,N],[_2],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf]);mshare([[T],[T,In],[T,In,_1,_3],[T,In,_1,_3,F],[T,In,_1,_3,F,N],[T,In,_1,_3,N],[T,In,_1,F],[T,In,_1,F,N],[T,In,_1,N],[T,_1,_3],[T,_1,_3,F],[T,_1,_3,F,N],[T,_1,_3,N],[T,_1,F],[T,_1,F,N],[T,_1,N],[In],[In,_1,_3],[In,_1,_3,F],[In,_1,_3,F,N],[In,_1,_3,N],[In,_1,F],[In,_1,F,N],[In,_1,N],[Out],[LLbls],[_1,_3],[_1,_3,F],[_1,_3,F,N],[_1,_3,N],[_1,F],[_1,F,N],[_1,N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]);mshare([[T],[In],[In,_1,_3],[In,_1,_3,F],[In,_1,_3,F,N],[In,_1,_3,N],[In,_1,F],[In,_1,F,N],[In,_1,N],[Out],[LLbls],[_1,_3],[_1,_3,F],[_1,_3,F,N],[_1,_3,N],[_1,F],[_1,F,N],[_1,N],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2]))),
    functor(T,F,N),
    true((mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,_1,_3],[T,LLbls],[T,LLbls,_1,_3],[T,_1,_3],[Outf],[In],[In,LLbls],[In,LLbls,_1,_3],[In,_1,_3],[Out],[LLbls],[LLbls,_1,_3],[_1,_3],[_2],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,F,N]);mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,_1,_3],[T,LLbls],[T,LLbls,_1,_3],[T,_1,_3],[In],[In,LLbls],[In,LLbls,_1,_3],[In,_1,_3],[Out],[LLbls],[LLbls,_1,_3],[_1,_3],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N]);mshare([[T],[T,In],[T,In,_1,_3],[T,_1,_3],[Outf],[In],[In,_1,_3],[Out],[LLbls],[_1,_3],[_2],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,F,N]);mshare([[T],[T,In],[T,In,_1,_3],[T,_1,_3],[In],[In,_1,_3],[Out],[LLbls],[_1,_3],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N]);mshare([[T],[In],[In,_1,_3],[Out],[LLbls],[_1,_3],[Midf],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N]))),
    Midf is Inf+N+1,
    true((mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,_1,_3],[T,LLbls],[T,LLbls,_1,_3],[T,_1,_3],[Outf],[In],[In,LLbls],[In,LLbls,_1,_3],[In,_1,_3],[Out],[LLbls],[LLbls,_1,_3],[_1,_3],[_2],[S],[Offsets],[Mid],[_4]]),ground([Inf,F,N,Midf]);mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,_1,_3],[T,LLbls],[T,LLbls,_1,_3],[T,_1,_3],[In],[In,LLbls],[In,LLbls,_1,_3],[In,_1,_3],[Out],[LLbls],[LLbls,_1,_3],[_1,_3],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N,Midf]);mshare([[T],[T,In],[T,In,_1,_3],[T,_1,_3],[Outf],[In],[In,_1,_3],[Out],[LLbls],[_1,_3],[_2],[S],[Offsets],[Mid],[_4]]),ground([Inf,F,N,Midf]);mshare([[T],[T,In],[T,In,_1,_3],[T,_1,_3],[In],[In,_1,_3],[Out],[LLbls],[_1,_3],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N,Midf]);mshare([[T],[In],[In,_1,_3],[Out],[LLbls],[_1,_3],[S],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N,Midf]))),
    S is Inf+1,
    true((mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,_1,_3],[T,LLbls],[T,LLbls,_1,_3],[T,_1,_3],[Outf],[In],[In,LLbls],[In,LLbls,_1,_3],[In,_1,_3],[Out],[LLbls],[LLbls,_1,_3],[_1,_3],[_2],[Offsets],[Mid],[_4]]),ground([Inf,F,N,Midf,S]);mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1,_3],[T,In,_1,_3],[T,LLbls],[T,LLbls,_1,_3],[T,_1,_3],[In],[In,LLbls],[In,LLbls,_1,_3],[In,_1,_3],[Out],[LLbls],[LLbls,_1,_3],[_1,_3],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N,Midf,S]);mshare([[T],[T,In],[T,In,_1,_3],[T,_1,_3],[Outf],[In],[In,_1,_3],[Out],[LLbls],[_1,_3],[_2],[Offsets],[Mid],[_4]]),ground([Inf,F,N,Midf,S]);mshare([[T],[T,In],[T,In,_1,_3],[T,_1,_3],[In],[In,_1,_3],[Out],[LLbls],[_1,_3],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N,Midf,S]);mshare([[T],[In],[In,_1,_3],[Out],[LLbls],[_1,_3],[Offsets],[Mid],[_4]]),ground([Inf,Outf,_2,F,N,Midf,S]))),
    make_slots(1,N,T,S,Offsets,In,Mid,_3,_4),
    true((mshare([[T],[T,In,LLbls,_1,_3,Offsets,Mid],[T,In,LLbls,_1,_3,Offsets,Mid,_4],[T,In,LLbls,_1,_3,Mid],[T,In,LLbls,_1,_3,Mid,_4],[T,In,LLbls,Offsets,Mid],[T,In,LLbls,Mid],[T,In,_1,_3,Offsets,Mid],[T,In,_1,_3,Offsets,Mid,_4],[T,In,_1,_3,Mid],[T,In,_1,_3,Mid,_4],[T,In,Offsets,Mid],[T,In,Mid],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,Offsets],[T,LLbls,_1,_3,Offsets,Mid],[T,LLbls,_1,_3,Offsets,Mid,_4],[T,LLbls,_1,_3,Offsets,_4],[T,LLbls,_1,_3,Mid],[T,LLbls,_1,_3,Mid,_4],[T,LLbls,_1,_3,_4],[T,LLbls,Offsets],[T,LLbls,Offsets,Mid],[T,LLbls,Mid],[T,_1,_3],[T,_1,_3,Offsets],[T,_1,_3,Offsets,Mid],[T,_1,_3,Offsets,Mid,_4],[T,_1,_3,Offsets,_4],[T,_1,_3,Mid],[T,_1,_3,Mid,_4],[T,_1,_3,_4],[T,Offsets],[T,Offsets,Mid],[T,Mid],[Outf],[In,LLbls,_1,_3,Offsets,Mid],[In,LLbls,_1,_3,Offsets,Mid,_4],[In,LLbls,_1,_3,Mid,_4],[In,LLbls,Offsets,Mid],[In,LLbls,Mid],[In,_1,_3,Offsets,Mid],[In,_1,_3,Offsets,Mid,_4],[In,_1,_3,Mid,_4],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[LLbls,_1,_3,Offsets],[LLbls,_1,_3,Offsets,_4],[LLbls,_1,_3,_4],[_1,_3,Offsets],[_1,_3,Offsets,_4],[_1,_3,_4],[_2],[Offsets]]),ground([Inf,F,N,Midf,S]);mshare([[T],[T,In,LLbls,_1,_3,Offsets,Mid],[T,In,LLbls,_1,_3,Offsets,Mid,_4],[T,In,LLbls,_1,_3,Mid],[T,In,LLbls,_1,_3,Mid,_4],[T,In,LLbls,Offsets,Mid],[T,In,LLbls,Mid],[T,In,_1,_3,Offsets,Mid],[T,In,_1,_3,Offsets,Mid,_4],[T,In,_1,_3,Mid],[T,In,_1,_3,Mid,_4],[T,In,Offsets,Mid],[T,In,Mid],[T,LLbls],[T,LLbls,_1,_3],[T,LLbls,_1,_3,Offsets],[T,LLbls,_1,_3,Offsets,Mid],[T,LLbls,_1,_3,Offsets,Mid,_4],[T,LLbls,_1,_3,Offsets,_4],[T,LLbls,_1,_3,Mid],[T,LLbls,_1,_3,Mid,_4],[T,LLbls,_1,_3,_4],[T,LLbls,Offsets],[T,LLbls,Offsets,Mid],[T,LLbls,Mid],[T,_1,_3],[T,_1,_3,Offsets],[T,_1,_3,Offsets,Mid],[T,_1,_3,Offsets,Mid,_4],[T,_1,_3,Offsets,_4],[T,_1,_3,Mid],[T,_1,_3,Mid,_4],[T,_1,_3,_4],[T,Offsets],[T,Offsets,Mid],[T,Mid],[In,LLbls,_1,_3,Offsets,Mid],[In,LLbls,_1,_3,Offsets,Mid,_4],[In,LLbls,_1,_3,Mid,_4],[In,LLbls,Offsets,Mid],[In,LLbls,Mid],[In,_1,_3,Offsets,Mid],[In,_1,_3,Offsets,Mid,_4],[In,_1,_3,Mid,_4],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[LLbls,_1,_3,Offsets],[LLbls,_1,_3,Offsets,_4],[LLbls,_1,_3,_4],[_1,_3,Offsets],[_1,_3,Offsets,_4],[_1,_3,_4],[Offsets]]),ground([Inf,Outf,_2,F,N,Midf,S]);mshare([[T],[T,In,_1,_3,Offsets,Mid],[T,In,_1,_3,Offsets,Mid,_4],[T,In,_1,_3,Mid],[T,In,_1,_3,Mid,_4],[T,In,Offsets,Mid],[T,In,Mid],[T,_1,_3],[T,_1,_3,Offsets],[T,_1,_3,Offsets,Mid],[T,_1,_3,Offsets,Mid,_4],[T,_1,_3,Offsets,_4],[T,_1,_3,Mid],[T,_1,_3,Mid,_4],[T,_1,_3,_4],[T,Offsets],[T,Offsets,Mid],[T,Mid],[Outf],[In,_1,_3,Offsets,Mid],[In,_1,_3,Offsets,Mid,_4],[In,_1,_3,Mid,_4],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[_1,_3,Offsets],[_1,_3,Offsets,_4],[_1,_3,_4],[_2],[Offsets]]),ground([Inf,F,N,Midf,S]);mshare([[T],[T,In,_1,_3,Offsets,Mid],[T,In,_1,_3,Offsets,Mid,_4],[T,In,_1,_3,Mid],[T,In,_1,_3,Mid,_4],[T,In,Offsets,Mid],[T,In,Mid],[T,_1,_3],[T,_1,_3,Offsets],[T,_1,_3,Offsets,Mid],[T,_1,_3,Offsets,Mid,_4],[T,_1,_3,Offsets,_4],[T,_1,_3,Mid],[T,_1,_3,Mid,_4],[T,_1,_3,_4],[T,Offsets],[T,Offsets,Mid],[T,Mid],[In,_1,_3,Offsets,Mid],[In,_1,_3,Offsets,Mid,_4],[In,_1,_3,Mid,_4],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[_1,_3,Offsets],[_1,_3,Offsets,_4],[_1,_3,_4],[Offsets]]),ground([Inf,Outf,_2,F,N,Midf,S]))),
    block_args(1,N,T,Midf,Outf,Offsets,Mid,Out,LLbls,_4,_2),
    true((mshare([[T],[T,In,Out,LLbls,_1,_2,_3,Mid,_4],[T,In,Out,LLbls,_1,_3,Mid,_4],[T,In,Out,_1,_2,_3,Mid,_4],[T,In,Out,_1,_3,Mid],[T,In,Out,_1,_3,Mid,_4],[T,In,Out,Mid],[T,Out],[T,Out,LLbls,_1,_2,_3,Mid,_4],[T,Out,LLbls,_1,_2,_3,_4],[T,Out,LLbls,_1,_3,Mid,_4],[T,Out,LLbls,_1,_3,_4],[T,Out,_1,_2,_3,Mid,_4],[T,Out,_1,_2,_3,_4],[T,Out,_1,_3],[T,Out,_1,_3,Mid],[T,Out,_1,_3,Mid,_4],[T,Out,_1,_3,_4],[T,Out,Mid],[T,LLbls,_1,_2,_3,_4],[T,LLbls,_1,_3,_4],[T,_1,_2,_3,_4],[T,_1,_3],[T,_1,_3,_4],[In,Out,LLbls,_1,_2,_3,Mid,_4],[In,Out,LLbls,_1,_3,Mid,_4],[In,Out,_1,_2,_3,Mid,_4],[In,Out,_1,_3,Mid,_4],[In,Out,Mid],[LLbls,_1,_2,_3,_4],[LLbls,_1,_3,_4],[_1,_2,_3,_4],[_1,_3,_4]]),ground([Inf,Outf,F,N,Midf,S,Offsets]);mshare([[T],[T,In,Out,LLbls,_1,_3,Mid,_4],[T,In,Out,_1,_3,Mid],[T,In,Out,_1,_3,Mid,_4],[T,In,Out,Mid],[T,Out],[T,Out,LLbls,_1,_3,Mid,_4],[T,Out,LLbls,_1,_3,_4],[T,Out,_1,_3],[T,Out,_1,_3,Mid],[T,Out,_1,_3,Mid,_4],[T,Out,_1,_3,_4],[T,Out,Mid],[T,LLbls,_1,_3,_4],[T,_1,_3],[T,_1,_3,_4],[In,Out,LLbls,_1,_3,Mid,_4],[In,Out,_1,_3,Mid,_4],[In,Out,Mid],[LLbls,_1,_3,_4],[_1,_3,_4]]),ground([Inf,Outf,_2,F,N,Midf,S,Offsets]))).
block(T,Inf,Outf,In,Out,LLbls,_1,_2) :-
    true((mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[Outf],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[_2],[Midf],[Offsets],[Mid],[_3]]),ground([Inf]);mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[Midf],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2]);mshare([[T],[T,In],[T,In,_1],[T,_1],[Outf],[In],[In,_1],[Out],[LLbls],[_1],[_2],[Midf],[Offsets],[Mid],[_3]]),ground([Inf]);mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[LLbls],[_1],[Midf],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2]);mshare([[T],[In],[In,_1],[Out],[LLbls],[_1],[Midf],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2]))),
    cons(T),
    !,
    true((mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[Outf],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[_2],[Midf],[Offsets],[Mid],[_3]]),ground([Inf]);mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[Midf],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2]);mshare([[T],[T,In],[T,In,_1],[T,_1],[Outf],[In],[In,_1],[Out],[LLbls],[_1],[_2],[Midf],[Offsets],[Mid],[_3]]),ground([Inf]);mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[LLbls],[_1],[Midf],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2]);mshare([[T],[In],[In,_1],[Out],[LLbls],[_1],[Midf],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2]))),
    Midf is Inf+2,
    true((mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[Outf],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[_2],[Offsets],[Mid],[_3]]),ground([Inf,Midf]);mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,_1],[T,LLbls],[T,LLbls,_1],[T,_1],[In],[In,LLbls],[In,LLbls,_1],[In,_1],[Out],[LLbls],[LLbls,_1],[_1],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2,Midf]);mshare([[T],[T,In],[T,In,_1],[T,_1],[Outf],[In],[In,_1],[Out],[LLbls],[_1],[_2],[Offsets],[Mid],[_3]]),ground([Inf,Midf]);mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[LLbls],[_1],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2,Midf]);mshare([[T],[In],[In,_1],[Out],[LLbls],[_1],[Offsets],[Mid],[_3]]),ground([Inf,Outf,_2,Midf]))),
    make_slots(1,2,T,Inf,Offsets,In,Mid,_1,_3),
    true((mshare([[T],[T,In,LLbls,_1,Offsets,Mid],[T,In,LLbls,_1,Offsets,Mid,_3],[T,In,LLbls,_1,Mid],[T,In,LLbls,_1,Mid,_3],[T,In,LLbls,Offsets,Mid],[T,In,LLbls,Mid],[T,In,_1,Offsets,Mid],[T,In,_1,Offsets,Mid,_3],[T,In,_1,Mid],[T,In,_1,Mid,_3],[T,In,Offsets,Mid],[T,In,Mid],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,Offsets],[T,LLbls,_1,Offsets,Mid],[T,LLbls,_1,Offsets,Mid,_3],[T,LLbls,_1,Offsets,_3],[T,LLbls,_1,Mid],[T,LLbls,_1,Mid,_3],[T,LLbls,_1,_3],[T,LLbls,Offsets],[T,LLbls,Offsets,Mid],[T,LLbls,Mid],[T,_1],[T,_1,Offsets],[T,_1,Offsets,Mid],[T,_1,Offsets,Mid,_3],[T,_1,Offsets,_3],[T,_1,Mid],[T,_1,Mid,_3],[T,_1,_3],[T,Offsets],[T,Offsets,Mid],[T,Mid],[Outf],[In,LLbls,_1,Offsets,Mid],[In,LLbls,_1,Offsets,Mid,_3],[In,LLbls,_1,Mid,_3],[In,LLbls,Offsets,Mid],[In,LLbls,Mid],[In,_1,Offsets,Mid],[In,_1,Offsets,Mid,_3],[In,_1,Mid,_3],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[LLbls,_1,Offsets],[LLbls,_1,Offsets,_3],[LLbls,_1,_3],[_1,Offsets],[_1,Offsets,_3],[_1,_3],[_2],[Offsets]]),ground([Inf,Midf]);mshare([[T],[T,In,LLbls,_1,Offsets,Mid],[T,In,LLbls,_1,Offsets,Mid,_3],[T,In,LLbls,_1,Mid],[T,In,LLbls,_1,Mid,_3],[T,In,LLbls,Offsets,Mid],[T,In,LLbls,Mid],[T,In,_1,Offsets,Mid],[T,In,_1,Offsets,Mid,_3],[T,In,_1,Mid],[T,In,_1,Mid,_3],[T,In,Offsets,Mid],[T,In,Mid],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,Offsets],[T,LLbls,_1,Offsets,Mid],[T,LLbls,_1,Offsets,Mid,_3],[T,LLbls,_1,Offsets,_3],[T,LLbls,_1,Mid],[T,LLbls,_1,Mid,_3],[T,LLbls,_1,_3],[T,LLbls,Offsets],[T,LLbls,Offsets,Mid],[T,LLbls,Mid],[T,_1],[T,_1,Offsets],[T,_1,Offsets,Mid],[T,_1,Offsets,Mid,_3],[T,_1,Offsets,_3],[T,_1,Mid],[T,_1,Mid,_3],[T,_1,_3],[T,Offsets],[T,Offsets,Mid],[T,Mid],[In,LLbls,_1,Offsets,Mid],[In,LLbls,_1,Offsets,Mid,_3],[In,LLbls,_1,Mid,_3],[In,LLbls,Offsets,Mid],[In,LLbls,Mid],[In,_1,Offsets,Mid],[In,_1,Offsets,Mid,_3],[In,_1,Mid,_3],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[LLbls,_1,Offsets],[LLbls,_1,Offsets,_3],[LLbls,_1,_3],[_1,Offsets],[_1,Offsets,_3],[_1,_3],[Offsets]]),ground([Inf,Outf,_2,Midf]);mshare([[T],[T,In,_1,Offsets,Mid],[T,In,_1,Offsets,Mid,_3],[T,In,_1,Mid],[T,In,_1,Mid,_3],[T,In,Offsets,Mid],[T,In,Mid],[T,_1],[T,_1,Offsets],[T,_1,Offsets,Mid],[T,_1,Offsets,Mid,_3],[T,_1,Offsets,_3],[T,_1,Mid],[T,_1,Mid,_3],[T,_1,_3],[T,Offsets],[T,Offsets,Mid],[T,Mid],[Outf],[In,_1,Offsets,Mid],[In,_1,Offsets,Mid,_3],[In,_1,Mid,_3],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[_1,Offsets],[_1,Offsets,_3],[_1,_3],[_2],[Offsets]]),ground([Inf,Midf]);mshare([[T],[T,In,_1,Offsets,Mid],[T,In,_1,Offsets,Mid,_3],[T,In,_1,Mid],[T,In,_1,Mid,_3],[T,In,Offsets,Mid],[T,In,Mid],[T,_1],[T,_1,Offsets],[T,_1,Offsets,Mid],[T,_1,Offsets,Mid,_3],[T,_1,Offsets,_3],[T,_1,Mid],[T,_1,Mid,_3],[T,_1,_3],[T,Offsets],[T,Offsets,Mid],[T,Mid],[In,_1,Offsets,Mid],[In,_1,Offsets,Mid,_3],[In,_1,Mid,_3],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[_1,Offsets],[_1,Offsets,_3],[_1,_3],[Offsets]]),ground([Inf,Outf,_2,Midf]))),
    block_args(1,2,T,Midf,Outf,Offsets,Mid,Out,LLbls,_3,_2),
    true((mshare([[T],[T,In,Out,LLbls,_1,_2,Mid,_3],[T,In,Out,LLbls,_1,Mid,_3],[T,In,Out,_1,_2,Mid,_3],[T,In,Out,_1,Mid],[T,In,Out,_1,Mid,_3],[T,In,Out,Mid],[T,Out],[T,Out,LLbls,_1,_2,Mid,_3],[T,Out,LLbls,_1,_2,_3],[T,Out,LLbls,_1,Mid,_3],[T,Out,LLbls,_1,_3],[T,Out,_1],[T,Out,_1,_2,Mid,_3],[T,Out,_1,_2,_3],[T,Out,_1,Mid],[T,Out,_1,Mid,_3],[T,Out,_1,_3],[T,Out,Mid],[T,LLbls,_1,_2,_3],[T,LLbls,_1,_3],[T,_1],[T,_1,_2,_3],[T,_1,_3],[In,Out,LLbls,_1,_2,Mid,_3],[In,Out,LLbls,_1,Mid,_3],[In,Out,_1,_2,Mid,_3],[In,Out,_1,Mid,_3],[In,Out,Mid],[LLbls,_1,_2,_3],[LLbls,_1,_3],[_1,_2,_3],[_1,_3]]),ground([Inf,Outf,Midf,Offsets]);mshare([[T],[T,In,Out,LLbls,_1,Mid,_3],[T,In,Out,_1,Mid],[T,In,Out,_1,Mid,_3],[T,In,Out,Mid],[T,Out],[T,Out,LLbls,_1,Mid,_3],[T,Out,LLbls,_1,_3],[T,Out,_1],[T,Out,_1,Mid],[T,Out,_1,Mid,_3],[T,Out,_1,_3],[T,Out,Mid],[T,LLbls,_1,_3],[T,_1],[T,_1,_3],[In,Out,LLbls,_1,Mid,_3],[In,Out,_1,Mid,_3],[In,Out,Mid],[LLbls,_1,_3],[_1,_3]]),ground([Inf,Outf,_2,Midf,Offsets]))).
block(T,Inf,Inf,In,In,[],_1,_2) :-
    true((mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[_1]]),ground([Inf,_2]);mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[_1],[_2]]),ground([Inf]);mshare([[T],[In],[In,_1],[_1]]),ground([Inf,_2]))),
    atomic(T),
    !,
    true((mshare([[In],[In,_1],[_1]]),ground([T,Inf,_2]);mshare([[In],[In,_1],[_1],[_2]]),ground([T,Inf]))),
    _2=_1,
    true((mshare([[In]]),ground([T,Inf,_1,_2]);mshare([[In],[In,_1,_2],[_1,_2]]),ground([T,Inf]))).
block(T,Inf,Inf,In,In,[],_1,_2) :-
    true((mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[_1]]),ground([Inf,_2]);mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[_1],[_2]]),ground([Inf]);mshare([[T],[In],[In,_1],[_1]]),ground([Inf,_2]))),
    var(T),
    !,
    true((mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[_1]]),ground([Inf,_2]);mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[_1],[_2]]),ground([Inf]);mshare([[T],[In],[In,_1],[_1]]),ground([Inf,_2]))),
    _2=_1,
    true((mshare([[T],[T,In],[T,In,_1,_2],[T,_1,_2],[In],[In,_1,_2],[_1,_2]]),ground([Inf]);mshare([[T],[T,In],[In]]),ground([Inf,_1,_2]);mshare([[T],[In]]),ground([Inf,_1,_2]))).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( mshare([[_1],[_1,_A],[_1,_A,In],[_1,_A,In,LLbls],[_1,_A,In,LLbls,_2],[_1,_A,In,_2],[_1,_A,LLbls],[_1,_A,LLbls,_2],[_1,_A,_2],[_1,In],[_1,In,LLbls],[_1,In,LLbls,_2],[_1,In,_2],[_1,LLbls],[_1,LLbls,_2],[_1,_2],[Outf],[_A],[_A,In],[_A,In,LLbls],[_A,In,LLbls,_2],[_A,In,_2],[_A,LLbls],[_A,LLbls,_2],[_A,_2],[In],[In,LLbls],[In,LLbls,_2],[In,_2],[Out],[LLbls],[LLbls,_2],[_2],[_3]]),
       ground([I,N,Inf]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,LLbls,_2],[_1,In,Out,LLbls,_2,_3],[_1,In,Out,_2],[_1,In,Out,_2,_3],[_1,Out],[_1,Out,LLbls,_2],[_1,Out,LLbls,_2,_3],[_1,Out,_2],[_1,Out,_2,_3],[_1,LLbls,_2],[_1,LLbls,_2,_3],[_1,_2],[_1,_2,_3],[In,Out],[In,Out,LLbls,_2],[In,Out,LLbls,_2,_3],[In,Out,_2],[In,Out,_2,_3],[LLbls,_2],[LLbls,_2,_3],[_2],[_2,_3]]),
        ground([I,N,Inf,Outf,_A]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1),
       mshare([[_1],[_1,_A],[_1,_A,In],[_1,_A,In,LLbls],[_1,_A,In,LLbls,_2],[_1,_A,In,_2],[_1,_A,LLbls],[_1,_A,LLbls,_2],[_1,_A,_2],[_1,In],[_1,In,LLbls],[_1,In,LLbls,_2],[_1,In,_2],[_1,LLbls],[_1,LLbls,_2],[_1,_2],[Outf],[_A],[_A,In],[_A,In,LLbls],[_A,In,LLbls,_2],[_A,In,_2],[_A,LLbls],[_A,LLbls,_2],[_A,_2],[In],[In,LLbls],[In,LLbls,_2],[In,_2],[Out],[LLbls],[LLbls,_2],[_2],[_3]]),
       ground([N,Inf]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,LLbls,_2],[_1,In,Out,LLbls,_2,_3],[_1,In,Out,_2],[_1,In,Out,_2,_3],[_1,Out],[_1,Out,LLbls,_2],[_1,Out,LLbls,_2,_3],[_1,Out,_2],[_1,Out,_2,_3],[_1,LLbls,_2],[_1,LLbls,_2,_3],[_1,_2],[_1,_2,_3],[In,Out],[In,Out,LLbls,_2],[In,Out,LLbls,_2,_3],[In,Out,_2],[In,Out,_2,_3],[LLbls,_2],[LLbls,_2,_3],[_2],[_2,_3]]),
        ground([N,Inf,Outf,_A]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1), (N=2),
       mshare([[_1],[_1,_A],[_1,_A,In],[_1,_A,In,LLbls],[_1,_A,In,LLbls,_2],[_1,_A,In,_2],[_1,_A,LLbls],[_1,_A,LLbls,_2],[_1,_A,_2],[_1,In],[_1,In,LLbls],[_1,In,LLbls,_2],[_1,In,_2],[_1,LLbls],[_1,LLbls,_2],[_1,_2],[Outf],[_A],[_A,In],[_A,In,LLbls],[_A,In,LLbls,_2],[_A,In,_2],[_A,LLbls],[_A,LLbls,_2],[_A,_2],[In],[In,LLbls],[In,LLbls,_2],[In,_2],[Out],[LLbls],[LLbls,_2],[_2],[_3]]),
       ground([Inf]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,LLbls,_2],[_1,In,Out,LLbls,_2,_3],[_1,In,Out,_2],[_1,In,Out,_2,_3],[_1,Out],[_1,Out,LLbls,_2],[_1,Out,LLbls,_2,_3],[_1,Out,_2],[_1,Out,_2,_3],[_1,LLbls,_2],[_1,LLbls,_2,_3],[_1,_2],[_1,_2,_3],[In,Out],[In,Out,LLbls,_2],[In,Out,LLbls,_2,_3],[In,Out,_2],[In,Out,_2,_3],[LLbls,_2],[LLbls,_2,_3],[_2],[_2,_3]]),
        ground([Inf,Outf,_A]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( mshare([[_1],[_1,_A],[_1,_A,In],[_1,_A,In,_2],[_1,_A,_2],[_1,In],[_1,In,_2],[_1,_2],[Outf],[_A],[_A,In],[_A,In,_2],[_A,_2],[In],[In,_2],[Out],[LLbls],[_2],[_3]]),
       ground([I,N,Inf]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,LLbls,_2],[_1,In,Out,LLbls,_2,_3],[_1,In,Out,_2],[_1,In,Out,_2,_3],[_1,Out],[_1,Out,LLbls,_2],[_1,Out,LLbls,_2,_3],[_1,Out,_2],[_1,Out,_2,_3],[_1,LLbls,_2],[_1,LLbls,_2,_3],[_1,_2],[_1,_2,_3],[In,Out],[In,Out,LLbls,_2],[In,Out,LLbls,_2,_3],[In,Out,_2],[In,Out,_2,_3],[LLbls,_2],[LLbls,_2,_3],[_2],[_2,_3]]),
        ground([I,N,Inf,Outf,_A]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1),
       mshare([[_1],[_1,_A],[_1,_A,In],[_1,_A,In,_2],[_1,_A,_2],[_1,In],[_1,In,_2],[_1,_2],[Outf],[_A],[_A,In],[_A,In,_2],[_A,_2],[In],[In,_2],[Out],[LLbls],[_2],[_3]]),
       ground([N,Inf]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,LLbls,_2],[_1,In,Out,LLbls,_2,_3],[_1,In,Out,_2],[_1,In,Out,_2,_3],[_1,Out],[_1,Out,LLbls,_2],[_1,Out,LLbls,_2,_3],[_1,Out,_2],[_1,Out,_2,_3],[_1,LLbls,_2],[_1,LLbls,_2,_3],[_1,_2],[_1,_2,_3],[In,Out],[In,Out,LLbls,_2],[In,Out,LLbls,_2,_3],[In,Out,_2],[In,Out,_2,_3],[LLbls,_2],[LLbls,_2,_3],[_2],[_2,_3]]),
        ground([N,Inf,Outf,_A]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1), (N=2),
       mshare([[_1],[_1,_A],[_1,_A,In],[_1,_A,In,_2],[_1,_A,_2],[_1,In],[_1,In,_2],[_1,_2],[Outf],[_A],[_A,In],[_A,In,_2],[_A,_2],[In],[In,_2],[Out],[LLbls],[_2],[_3]]),
       ground([Inf]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,LLbls,_2],[_1,In,Out,LLbls,_2,_3],[_1,In,Out,_2],[_1,In,Out,_2,_3],[_1,Out],[_1,Out,LLbls,_2],[_1,Out,LLbls,_2,_3],[_1,Out,_2],[_1,Out,_2,_3],[_1,LLbls,_2],[_1,LLbls,_2,_3],[_1,_2],[_1,_2,_3],[In,Out],[In,Out,LLbls,_2],[In,Out,LLbls,_2,_3],[In,Out,_2],[In,Out,_2,_3],[LLbls,_2],[LLbls,_2,_3],[_2],[_2,_3]]),
        ground([Inf,Outf,_A]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1), (N=2),
       mshare([[_1],[_1,_A],[_1,_A,In],[_1,_A,In,_2],[_1,_A,_2],[_1,In],[_1,In,_2],[_1,_2],[_A],[_A,In],[_A,In,_2],[_A,_2],[In],[In,_2],[Out],[LLbls],[_2]]),
       ground([Inf,Outf,_3]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,LLbls,_2],[_1,In,Out,_2],[_1,Out],[_1,Out,LLbls,_2],[_1,Out,_2],[_1,LLbls,_2],[_1,_2],[In,Out],[In,Out,LLbls,_2],[In,Out,_2],[LLbls,_2],[_2]]),
        ground([Inf,Outf,_A,_3]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1),
       mshare([[_1],[_1,_A],[_1,_A,In],[_1,_A,In,_2],[_1,_A,_2],[_1,In],[_1,In,_2],[_1,_2],[_A],[_A,In],[_A,In,_2],[_A,_2],[In],[In,_2],[Out],[LLbls],[_2]]),
       ground([N,Inf,Outf,_3]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,LLbls,_2],[_1,In,Out,_2],[_1,Out],[_1,Out,LLbls,_2],[_1,Out,_2],[_1,LLbls,_2],[_1,_2],[In,Out],[In,Out,LLbls,_2],[In,Out,_2],[LLbls,_2],[_2]]),
        ground([N,Inf,Outf,_A,_3]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1), (N=2),
       mshare([[_1],[_1,_A],[_1,_A,In],[_1,_A,In,LLbls],[_1,_A,In,LLbls,_2],[_1,_A,In,_2],[_1,_A,LLbls],[_1,_A,LLbls,_2],[_1,_A,_2],[_1,In],[_1,In,LLbls],[_1,In,LLbls,_2],[_1,In,_2],[_1,LLbls],[_1,LLbls,_2],[_1,_2],[_A],[_A,In],[_A,In,LLbls],[_A,In,LLbls,_2],[_A,In,_2],[_A,LLbls],[_A,LLbls,_2],[_A,_2],[In],[In,LLbls],[In,LLbls,_2],[In,_2],[Out],[LLbls],[LLbls,_2],[_2]]),
       ground([Inf,Outf,_3]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,LLbls,_2],[_1,In,Out,_2],[_1,Out],[_1,Out,LLbls,_2],[_1,Out,_2],[_1,LLbls,_2],[_1,_2],[In,Out],[In,Out,LLbls,_2],[In,Out,_2],[LLbls,_2],[_2]]),
        ground([Inf,Outf,_A,_3]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( mshare([[_1],[_1,_A],[_1,_A,In],[_1,_A,In,LLbls],[_1,_A,In,LLbls,_2],[_1,_A,In,_2],[_1,_A,LLbls],[_1,_A,LLbls,_2],[_1,_A,_2],[_1,In],[_1,In,LLbls],[_1,In,LLbls,_2],[_1,In,_2],[_1,LLbls],[_1,LLbls,_2],[_1,_2],[_A],[_A,In],[_A,In,LLbls],[_A,In,LLbls,_2],[_A,In,_2],[_A,LLbls],[_A,LLbls,_2],[_A,_2],[In],[In,LLbls],[In,LLbls,_2],[In,_2],[Out],[LLbls],[LLbls,_2],[_2]]),
       ground([I,N,Inf,Outf,_3]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,LLbls,_2],[_1,In,Out,_2],[_1,Out],[_1,Out,LLbls,_2],[_1,Out,_2],[_1,LLbls,_2],[_1,_2],[In,Out],[In,Out,LLbls,_2],[In,Out,_2],[LLbls,_2],[_2]]),
        ground([I,N,Inf,Outf,_A,_3]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( (I=1),
       mshare([[_1],[_1,_A],[_1,_A,In],[_1,_A,In,LLbls],[_1,_A,In,LLbls,_2],[_1,_A,In,_2],[_1,_A,LLbls],[_1,_A,LLbls,_2],[_1,_A,_2],[_1,In],[_1,In,LLbls],[_1,In,LLbls,_2],[_1,In,_2],[_1,LLbls],[_1,LLbls,_2],[_1,_2],[_A],[_A,In],[_A,In,LLbls],[_A,In,LLbls,_2],[_A,In,_2],[_A,LLbls],[_A,LLbls,_2],[_A,_2],[In],[In,LLbls],[In,LLbls,_2],[In,_2],[Out],[LLbls],[LLbls,_2],[_2]]),
       ground([N,Inf,Outf,_3]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,LLbls,_2],[_1,In,Out,_2],[_1,Out],[_1,Out,LLbls,_2],[_1,Out,_2],[_1,LLbls,_2],[_1,_2],[In,Out],[In,Out,LLbls,_2],[In,Out,_2],[LLbls,_2],[_2]]),
        ground([N,Inf,Outf,_A,_3]) ).

:- true pred block_args(I,N,_1,Inf,Outf,_A,In,Out,LLbls,_2,_3)
   : ( mshare([[_1],[_1,_A],[_1,_A,In],[_1,_A,In,_2],[_1,_A,_2],[_1,In],[_1,In,_2],[_1,_2],[_A],[_A,In],[_A,In,_2],[_A,_2],[In],[In,_2],[Out],[LLbls],[_2]]),
       ground([I,N,Inf,Outf,_3]) )
   => ( mshare([[_1],[_1,In,Out],[_1,In,Out,LLbls,_2],[_1,In,Out,_2],[_1,Out],[_1,Out,LLbls,_2],[_1,Out,_2],[_1,LLbls,_2],[_1,_2],[In,Out],[In,Out,LLbls,_2],[In,Out,_2],[LLbls,_2],[_2]]),
        ground([I,N,Inf,Outf,_A,_3]) ).

block_args(I,N,_1,Inf,Inf,[],In,In,[],_2,_3) :-
    true((mshare([[_1],[_1,In],[_1,In,_2],[_1,_2],[In],[In,_2],[_2]]),ground([I,N,Inf,_3]);mshare([[_1],[_1,In],[_1,In,_2],[_1,_2],[In],[In,_2],[_2],[_3]]),ground([I,N,Inf]))),
    I>N,
    !,
    true((mshare([[_1],[_1,In],[_1,In,_2],[_1,_2],[In],[In,_2],[_2]]),ground([I,N,Inf,_3]);mshare([[_1],[_1,In],[_1,In,_2],[_1,_2],[In],[In,_2],[_2],[_3]]),ground([I,N,Inf]))),
    _3=_2,
    true((mshare([[_1],[_1,In],[_1,In,_2,_3],[_1,_2,_3],[In],[In,_2,_3],[_2,_3]]),ground([I,N,Inf]);mshare([[_1],[_1,In],[In]]),ground([I,N,Inf,_2,_3]))).
block_args(I,N,T,Inf,Outf,[Inf],In,Out,[Lbl|LLbls],_1,_2) :-
    true((mshare([[T],[T,In],[T,In,_1],[T,In,_1,Lbl],[T,In,_1,Lbl,LLbls],[T,In,_1,LLbls],[T,In,Lbl],[T,In,Lbl,LLbls],[T,In,LLbls],[T,_1],[T,_1,Lbl],[T,_1,Lbl,LLbls],[T,_1,LLbls],[T,Lbl],[T,Lbl,LLbls],[T,LLbls],[Outf],[In],[In,_1],[In,_1,Lbl],[In,_1,Lbl,LLbls],[In,_1,LLbls],[In,Lbl],[In,Lbl,LLbls],[In,LLbls],[Out],[_1],[_1,Lbl],[_1,Lbl,LLbls],[_1,LLbls],[_2],[Lbl],[Lbl,LLbls],[LLbls],[_3],[A]]),ground([I,N,Inf]);mshare([[T],[T,In],[T,In,_1],[T,In,_1,Lbl],[T,In,_1,Lbl,LLbls],[T,In,_1,LLbls],[T,In,Lbl],[T,In,Lbl,LLbls],[T,In,LLbls],[T,_1],[T,_1,Lbl],[T,_1,Lbl,LLbls],[T,_1,LLbls],[T,Lbl],[T,Lbl,LLbls],[T,LLbls],[In],[In,_1],[In,_1,Lbl],[In,_1,Lbl,LLbls],[In,_1,LLbls],[In,Lbl],[In,Lbl,LLbls],[In,LLbls],[Out],[_1],[_1,Lbl],[_1,Lbl,LLbls],[_1,LLbls],[Lbl],[Lbl,LLbls],[LLbls],[_3],[A]]),ground([I,N,Inf,Outf,_2]);mshare([[T],[T,In],[T,In,_1],[T,_1],[Outf],[In],[In,_1],[Out],[_1],[_2],[Lbl],[Lbl,LLbls],[LLbls],[_3],[A]]),ground([I,N,Inf]);mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[_1],[Lbl],[Lbl,LLbls],[LLbls],[_3],[A]]),ground([I,N,Inf,Outf,_2]))),
    I=N,
    !,
    true((mshare([[T],[T,In],[T,In,_1],[T,In,_1,Lbl],[T,In,_1,Lbl,LLbls],[T,In,_1,LLbls],[T,In,Lbl],[T,In,Lbl,LLbls],[T,In,LLbls],[T,_1],[T,_1,Lbl],[T,_1,Lbl,LLbls],[T,_1,LLbls],[T,Lbl],[T,Lbl,LLbls],[T,LLbls],[Outf],[In],[In,_1],[In,_1,Lbl],[In,_1,Lbl,LLbls],[In,_1,LLbls],[In,Lbl],[In,Lbl,LLbls],[In,LLbls],[Out],[_1],[_1,Lbl],[_1,Lbl,LLbls],[_1,LLbls],[_2],[Lbl],[Lbl,LLbls],[LLbls],[_3],[A]]),ground([I,N,Inf]);mshare([[T],[T,In],[T,In,_1],[T,In,_1,Lbl],[T,In,_1,Lbl,LLbls],[T,In,_1,LLbls],[T,In,Lbl],[T,In,Lbl,LLbls],[T,In,LLbls],[T,_1],[T,_1,Lbl],[T,_1,Lbl,LLbls],[T,_1,LLbls],[T,Lbl],[T,Lbl,LLbls],[T,LLbls],[In],[In,_1],[In,_1,Lbl],[In,_1,Lbl,LLbls],[In,_1,LLbls],[In,Lbl],[In,Lbl,LLbls],[In,LLbls],[Out],[_1],[_1,Lbl],[_1,Lbl,LLbls],[_1,LLbls],[Lbl],[Lbl,LLbls],[LLbls],[_3],[A]]),ground([I,N,Inf,Outf,_2]);mshare([[T],[T,In],[T,In,_1],[T,_1],[Outf],[In],[In,_1],[Out],[_1],[_2],[Lbl],[Lbl,LLbls],[LLbls],[_3],[A]]),ground([I,N,Inf]);mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[_1],[Lbl],[Lbl,LLbls],[LLbls],[_3],[A]]),ground([I,N,Inf,Outf,_2]))),
    'C'(_1,label(Lbl),_3),
    true((mshare([[T],[T,In],[T,In,_1,Lbl],[T,In,_1,Lbl,LLbls],[T,In,_1,Lbl,LLbls,_3],[T,In,_1,Lbl,_3],[T,In,_1,LLbls,_3],[T,In,_1,_3],[T,In,LLbls],[T,_1,Lbl],[T,_1,Lbl,LLbls],[T,_1,Lbl,LLbls,_3],[T,_1,Lbl,_3],[T,_1,LLbls,_3],[T,_1,_3],[T,LLbls],[Outf],[In],[In,_1,Lbl],[In,_1,Lbl,LLbls],[In,_1,Lbl,LLbls,_3],[In,_1,Lbl,_3],[In,_1,LLbls,_3],[In,_1,_3],[In,LLbls],[Out],[_1,Lbl],[_1,Lbl,LLbls],[_1,Lbl,LLbls,_3],[_1,Lbl,_3],[_1,LLbls,_3],[_1,_3],[_2],[LLbls],[A]]),ground([I,N,Inf]);mshare([[T],[T,In],[T,In,_1,Lbl],[T,In,_1,Lbl,LLbls],[T,In,_1,Lbl,LLbls,_3],[T,In,_1,Lbl,_3],[T,In,_1,LLbls,_3],[T,In,_1,_3],[T,In,LLbls],[T,_1,Lbl],[T,_1,Lbl,LLbls],[T,_1,Lbl,LLbls,_3],[T,_1,Lbl,_3],[T,_1,LLbls,_3],[T,_1,_3],[T,LLbls],[In],[In,_1,Lbl],[In,_1,Lbl,LLbls],[In,_1,Lbl,LLbls,_3],[In,_1,Lbl,_3],[In,_1,LLbls,_3],[In,_1,_3],[In,LLbls],[Out],[_1,Lbl],[_1,Lbl,LLbls],[_1,Lbl,LLbls,_3],[_1,Lbl,_3],[_1,LLbls,_3],[_1,_3],[LLbls],[A]]),ground([I,N,Inf,Outf,_2]);mshare([[T],[T,In],[T,In,_1,Lbl],[T,In,_1,Lbl,LLbls],[T,In,_1,Lbl,LLbls,_3],[T,In,_1,Lbl,_3],[T,In,_1,_3],[T,_1,Lbl],[T,_1,Lbl,LLbls],[T,_1,Lbl,LLbls,_3],[T,_1,Lbl,_3],[T,_1,_3],[Outf],[In],[In,_1,Lbl],[In,_1,Lbl,LLbls],[In,_1,Lbl,LLbls,_3],[In,_1,Lbl,_3],[In,_1,_3],[Out],[_1,Lbl],[_1,Lbl,LLbls],[_1,Lbl,LLbls,_3],[_1,Lbl,_3],[_1,_3],[_2],[LLbls],[A]]),ground([I,N,Inf]);mshare([[T],[T,In],[T,In,_1,Lbl],[T,In,_1,Lbl,LLbls],[T,In,_1,Lbl,LLbls,_3],[T,In,_1,Lbl,_3],[T,In,_1,_3],[T,_1,Lbl],[T,_1,Lbl,LLbls],[T,_1,Lbl,LLbls,_3],[T,_1,Lbl,_3],[T,_1,_3],[In],[In,_1,Lbl],[In,_1,Lbl,LLbls],[In,_1,Lbl,LLbls,_3],[In,_1,Lbl,_3],[In,_1,_3],[Out],[_1,Lbl],[_1,Lbl,LLbls],[_1,Lbl,LLbls,_3],[_1,Lbl,_3],[_1,_3],[LLbls],[A]]),ground([I,N,Inf,Outf,_2]))),
    arg(I,T,A),
    true((mshare([[T,In,_1,Lbl,LLbls,_3,A],[T,In,_1,Lbl,LLbls,A],[T,In,_1,Lbl,_3,A],[T,In,_1,Lbl,A],[T,In,_1,LLbls,_3,A],[T,In,_1,_3,A],[T,In,LLbls,A],[T,In,A],[T,_1,Lbl,LLbls,_3,A],[T,_1,Lbl,LLbls,A],[T,_1,Lbl,_3,A],[T,_1,Lbl,A],[T,_1,LLbls,_3,A],[T,_1,_3,A],[T,LLbls,A],[T,A],[Outf],[In],[In,_1,Lbl],[In,_1,Lbl,LLbls],[In,_1,Lbl,LLbls,_3],[In,_1,Lbl,_3],[In,_1,LLbls,_3],[In,_1,_3],[In,LLbls],[Out],[_1,Lbl],[_1,Lbl,LLbls],[_1,Lbl,LLbls,_3],[_1,Lbl,_3],[_1,LLbls,_3],[_1,_3],[_2],[LLbls]]),ground([I,N,Inf]);mshare([[T,In,_1,Lbl,LLbls,_3,A],[T,In,_1,Lbl,LLbls,A],[T,In,_1,Lbl,_3,A],[T,In,_1,Lbl,A],[T,In,_1,LLbls,_3,A],[T,In,_1,_3,A],[T,In,LLbls,A],[T,In,A],[T,_1,Lbl,LLbls,_3,A],[T,_1,Lbl,LLbls,A],[T,_1,Lbl,_3,A],[T,_1,Lbl,A],[T,_1,LLbls,_3,A],[T,_1,_3,A],[T,LLbls,A],[T,A],[In],[In,_1,Lbl],[In,_1,Lbl,LLbls],[In,_1,Lbl,LLbls,_3],[In,_1,Lbl,_3],[In,_1,LLbls,_3],[In,_1,_3],[In,LLbls],[Out],[_1,Lbl],[_1,Lbl,LLbls],[_1,Lbl,LLbls,_3],[_1,Lbl,_3],[_1,LLbls,_3],[_1,_3],[LLbls]]),ground([I,N,Inf,Outf,_2]);mshare([[T,In,_1,Lbl,LLbls,_3,A],[T,In,_1,Lbl,LLbls,A],[T,In,_1,Lbl,_3,A],[T,In,_1,Lbl,A],[T,In,_1,_3,A],[T,In,A],[T,_1,Lbl,LLbls,_3,A],[T,_1,Lbl,LLbls,A],[T,_1,Lbl,_3,A],[T,_1,Lbl,A],[T,_1,_3,A],[T,A],[Outf],[In],[In,_1,Lbl],[In,_1,Lbl,LLbls],[In,_1,Lbl,LLbls,_3],[In,_1,Lbl,_3],[In,_1,_3],[Out],[_1,Lbl],[_1,Lbl,LLbls],[_1,Lbl,LLbls,_3],[_1,Lbl,_3],[_1,_3],[_2],[LLbls]]),ground([I,N,Inf]);mshare([[T,In,_1,Lbl,LLbls,_3,A],[T,In,_1,Lbl,LLbls,A],[T,In,_1,Lbl,_3,A],[T,In,_1,Lbl,A],[T,In,_1,_3,A],[T,In,A],[T,_1,Lbl,LLbls,_3,A],[T,_1,Lbl,LLbls,A],[T,_1,Lbl,_3,A],[T,_1,Lbl,A],[T,_1,_3,A],[T,A],[In],[In,_1,Lbl],[In,_1,Lbl,LLbls],[In,_1,Lbl,LLbls,_3],[In,_1,Lbl,_3],[In,_1,_3],[Out],[_1,Lbl],[_1,Lbl,LLbls],[_1,Lbl,LLbls,_3],[_1,Lbl,_3],[_1,_3],[LLbls]]),ground([I,N,Inf,Outf,_2]))),
    block(A,Inf,Outf,In,Out,LLbls,_3,_2),
    true((mshare([[T,In,Out,_1,_2,Lbl,LLbls,_3,A],[T,In,Out,_1,_2,Lbl,_3,A],[T,In,Out,_1,_2,LLbls,_3,A],[T,In,Out,_1,_2,_3,A],[T,In,Out,_1,Lbl,LLbls,_3,A],[T,In,Out,_1,Lbl,_3,A],[T,In,Out,_1,Lbl,A],[T,In,Out,_1,LLbls,_3,A],[T,In,Out,_1,_3,A],[T,In,Out,A],[T,Out,_1,_2,Lbl,LLbls,_3,A],[T,Out,_1,_2,Lbl,_3,A],[T,Out,_1,_2,LLbls,_3,A],[T,Out,_1,_2,_3,A],[T,Out,_1,Lbl,LLbls,_3,A],[T,Out,_1,Lbl,_3,A],[T,Out,_1,Lbl,A],[T,Out,_1,LLbls,_3,A],[T,Out,_1,_3,A],[T,Out,A],[T,_1,_2,Lbl,LLbls,_3,A],[T,_1,_2,Lbl,_3,A],[T,_1,_2,LLbls,_3,A],[T,_1,_2,_3,A],[T,_1,Lbl,LLbls,_3,A],[T,_1,Lbl,_3,A],[T,_1,Lbl,A],[T,_1,LLbls,_3,A],[T,_1,_3,A],[T,A],[In,Out],[In,Out,_1,_2,Lbl,LLbls,_3],[In,Out,_1,_2,Lbl,_3],[In,Out,_1,_2,LLbls,_3],[In,Out,_1,_2,_3],[In,Out,_1,Lbl],[In,Out,_1,Lbl,LLbls,_3],[In,Out,_1,Lbl,_3],[In,Out,_1,LLbls,_3],[In,Out,_1,_3],[_1,_2,Lbl,LLbls,_3],[_1,_2,Lbl,_3],[_1,_2,LLbls,_3],[_1,_2,_3],[_1,Lbl],[_1,Lbl,LLbls,_3],[_1,Lbl,_3],[_1,LLbls,_3],[_1,_3]]),ground([I,N,Inf,Outf]);mshare([[T,In,Out,_1,Lbl,LLbls,_3,A],[T,In,Out,_1,Lbl,_3,A],[T,In,Out,_1,Lbl,A],[T,In,Out,_1,LLbls,_3,A],[T,In,Out,_1,_3,A],[T,In,Out,A],[T,Out,_1,Lbl,LLbls,_3,A],[T,Out,_1,Lbl,_3,A],[T,Out,_1,Lbl,A],[T,Out,_1,LLbls,_3,A],[T,Out,_1,_3,A],[T,Out,A],[T,_1,Lbl,LLbls,_3,A],[T,_1,Lbl,_3,A],[T,_1,Lbl,A],[T,_1,LLbls,_3,A],[T,_1,_3,A],[T,A],[In,Out],[In,Out,_1,Lbl],[In,Out,_1,Lbl,LLbls,_3],[In,Out,_1,Lbl,_3],[In,Out,_1,LLbls,_3],[In,Out,_1,_3],[_1,Lbl],[_1,Lbl,LLbls,_3],[_1,Lbl,_3],[_1,LLbls,_3],[_1,_3]]),ground([I,N,Inf,Outf,_2]))).
block_args(I,N,T,Inf,Outf,[Inf|Offsets],In,Out,LLbls,_1,_2) :-
    true((mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,LLbls,_1,Offsets],[T,In,LLbls,Offsets],[T,In,_1],[T,In,_1,Offsets],[T,In,Offsets],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,Offsets],[T,LLbls,Offsets],[T,_1],[T,_1,Offsets],[T,Offsets],[Outf],[In],[In,LLbls],[In,LLbls,_1],[In,LLbls,_1,Offsets],[In,LLbls,Offsets],[In,_1],[In,_1,Offsets],[In,Offsets],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Offsets],[LLbls,Offsets],[_1],[_1,Offsets],[_2],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf]);mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,LLbls,_1,Offsets],[T,In,LLbls,Offsets],[T,In,_1],[T,In,_1,Offsets],[T,In,Offsets],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,Offsets],[T,LLbls,Offsets],[T,_1],[T,_1,Offsets],[T,Offsets],[In],[In,LLbls],[In,LLbls,_1],[In,LLbls,_1,Offsets],[In,LLbls,Offsets],[In,_1],[In,_1,Offsets],[In,Offsets],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Offsets],[LLbls,Offsets],[_1],[_1,Offsets],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf,Outf,_2]);mshare([[T],[T,In],[T,In,_1],[T,In,_1,Offsets],[T,In,Offsets],[T,_1],[T,_1,Offsets],[T,Offsets],[Outf],[In],[In,_1],[In,_1,Offsets],[In,Offsets],[Out],[LLbls],[_1],[_1,Offsets],[_2],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf]);mshare([[T],[T,In],[T,In,_1],[T,In,_1,Offsets],[T,In,Offsets],[T,_1],[T,_1,Offsets],[T,Offsets],[In],[In,_1],[In,_1,Offsets],[In,Offsets],[Out],[LLbls],[_1],[_1,Offsets],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf,Outf,_2]))),
    I<N,
    !,
    true((mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,LLbls,_1,Offsets],[T,In,LLbls,Offsets],[T,In,_1],[T,In,_1,Offsets],[T,In,Offsets],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,Offsets],[T,LLbls,Offsets],[T,_1],[T,_1,Offsets],[T,Offsets],[Outf],[In],[In,LLbls],[In,LLbls,_1],[In,LLbls,_1,Offsets],[In,LLbls,Offsets],[In,_1],[In,_1,Offsets],[In,Offsets],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Offsets],[LLbls,Offsets],[_1],[_1,Offsets],[_2],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf]);mshare([[T],[T,In],[T,In,LLbls],[T,In,LLbls,_1],[T,In,LLbls,_1,Offsets],[T,In,LLbls,Offsets],[T,In,_1],[T,In,_1,Offsets],[T,In,Offsets],[T,LLbls],[T,LLbls,_1],[T,LLbls,_1,Offsets],[T,LLbls,Offsets],[T,_1],[T,_1,Offsets],[T,Offsets],[In],[In,LLbls],[In,LLbls,_1],[In,LLbls,_1,Offsets],[In,LLbls,Offsets],[In,_1],[In,_1,Offsets],[In,Offsets],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Offsets],[LLbls,Offsets],[_1],[_1,Offsets],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf,Outf,_2]);mshare([[T],[T,In],[T,In,_1],[T,In,_1,Offsets],[T,In,Offsets],[T,_1],[T,_1,Offsets],[T,Offsets],[Outf],[In],[In,_1],[In,_1,Offsets],[In,Offsets],[Out],[LLbls],[_1],[_1,Offsets],[_2],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf]);mshare([[T],[T,In],[T,In,_1],[T,In,_1,Offsets],[T,In,Offsets],[T,_1],[T,_1,Offsets],[T,Offsets],[In],[In,_1],[In,_1,Offsets],[In,Offsets],[Out],[LLbls],[_1],[_1,Offsets],[Offsets],[A],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf,Outf,_2]))),
    arg(I,T,A),
    true((mshare([[T,In,LLbls,_1,Offsets,A],[T,In,LLbls,_1,A],[T,In,LLbls,Offsets,A],[T,In,LLbls,A],[T,In,_1,Offsets,A],[T,In,_1,A],[T,In,Offsets,A],[T,In,A],[T,LLbls,_1,Offsets,A],[T,LLbls,_1,A],[T,LLbls,Offsets,A],[T,LLbls,A],[T,_1,Offsets,A],[T,_1,A],[T,Offsets,A],[T,A],[Outf],[In],[In,LLbls],[In,LLbls,_1],[In,LLbls,_1,Offsets],[In,LLbls,Offsets],[In,_1],[In,_1,Offsets],[In,Offsets],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Offsets],[LLbls,Offsets],[_1],[_1,Offsets],[_2],[Offsets],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf]);mshare([[T,In,LLbls,_1,Offsets,A],[T,In,LLbls,_1,A],[T,In,LLbls,Offsets,A],[T,In,LLbls,A],[T,In,_1,Offsets,A],[T,In,_1,A],[T,In,Offsets,A],[T,In,A],[T,LLbls,_1,Offsets,A],[T,LLbls,_1,A],[T,LLbls,Offsets,A],[T,LLbls,A],[T,_1,Offsets,A],[T,_1,A],[T,Offsets,A],[T,A],[In],[In,LLbls],[In,LLbls,_1],[In,LLbls,_1,Offsets],[In,LLbls,Offsets],[In,_1],[In,_1,Offsets],[In,Offsets],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Offsets],[LLbls,Offsets],[_1],[_1,Offsets],[Offsets],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf,Outf,_2]);mshare([[T,In,_1,Offsets,A],[T,In,_1,A],[T,In,Offsets,A],[T,In,A],[T,_1,Offsets,A],[T,_1,A],[T,Offsets,A],[T,A],[Outf],[In],[In,_1],[In,_1,Offsets],[In,Offsets],[Out],[LLbls],[_1],[_1,Offsets],[_2],[Offsets],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf]);mshare([[T,In,_1,Offsets,A],[T,In,_1,A],[T,In,Offsets,A],[T,In,A],[T,_1,Offsets,A],[T,_1,A],[T,Offsets,A],[T,A],[In],[In,_1],[In,_1,Offsets],[In,Offsets],[Out],[LLbls],[_1],[_1,Offsets],[Offsets],[Midf],[Mid],[_3],[_4],[I1]]),ground([I,N,Inf,Outf,_2]))),
    block(A,Inf,Midf,In,Mid,_3,_1,_4),
    true((mshare([[T,In,LLbls,_1,Offsets,A,Mid],[T,In,LLbls,_1,Offsets,A,Mid,_3],[T,In,LLbls,_1,Offsets,A,Mid,_3,_4],[T,In,LLbls,_1,Offsets,A,Mid,_4],[T,In,LLbls,_1,A,Mid],[T,In,LLbls,_1,A,Mid,_3],[T,In,LLbls,_1,A,Mid,_3,_4],[T,In,LLbls,_1,A,Mid,_4],[T,In,LLbls,Offsets,A,Mid],[T,In,LLbls,A,Mid],[T,In,_1,Offsets,A,Mid],[T,In,_1,Offsets,A,Mid,_3],[T,In,_1,Offsets,A,Mid,_3,_4],[T,In,_1,Offsets,A,Mid,_4],[T,In,_1,A,Mid],[T,In,_1,A,Mid,_3],[T,In,_1,A,Mid,_3,_4],[T,In,_1,A,Mid,_4],[T,In,Offsets,A,Mid],[T,In,A,Mid],[T,LLbls,_1,Offsets,A],[T,LLbls,_1,Offsets,A,Mid],[T,LLbls,_1,Offsets,A,Mid,_3],[T,LLbls,_1,Offsets,A,Mid,_3,_4],[T,LLbls,_1,Offsets,A,Mid,_4],[T,LLbls,_1,Offsets,A,_3],[T,LLbls,_1,Offsets,A,_3,_4],[T,LLbls,_1,Offsets,A,_4],[T,LLbls,_1,A],[T,LLbls,_1,A,Mid],[T,LLbls,_1,A,Mid,_3],[T,LLbls,_1,A,Mid,_3,_4],[T,LLbls,_1,A,Mid,_4],[T,LLbls,_1,A,_3],[T,LLbls,_1,A,_3,_4],[T,LLbls,_1,A,_4],[T,LLbls,Offsets,A],[T,LLbls,Offsets,A,Mid],[T,LLbls,A],[T,LLbls,A,Mid],[T,_1,Offsets,A],[T,_1,Offsets,A,Mid],[T,_1,Offsets,A,Mid,_3],[T,_1,Offsets,A,Mid,_3,_4],[T,_1,Offsets,A,Mid,_4],[T,_1,Offsets,A,_3],[T,_1,Offsets,A,_3,_4],[T,_1,Offsets,A,_4],[T,_1,A],[T,_1,A,Mid],[T,_1,A,Mid,_3],[T,_1,A,Mid,_3,_4],[T,_1,A,Mid,_4],[T,_1,A,_3],[T,_1,A,_3,_4],[T,_1,A,_4],[T,Offsets,A],[T,Offsets,A,Mid],[T,A],[T,A,Mid],[Outf],[In,LLbls,_1,Offsets,Mid],[In,LLbls,_1,Offsets,Mid,_3],[In,LLbls,_1,Offsets,Mid,_3,_4],[In,LLbls,_1,Offsets,Mid,_4],[In,LLbls,_1,Mid],[In,LLbls,_1,Mid,_3],[In,LLbls,_1,Mid,_3,_4],[In,LLbls,_1,Mid,_4],[In,LLbls,Offsets,Mid],[In,LLbls,Mid],[In,_1,Offsets,Mid],[In,_1,Offsets,Mid,_3],[In,_1,Offsets,Mid,_3,_4],[In,_1,Offsets,Mid,_4],[In,_1,Mid],[In,_1,Mid,_3],[In,_1,Mid,_3,_4],[In,_1,Mid,_4],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Offsets],[LLbls,_1,Offsets,_3],[LLbls,_1,Offsets,_3,_4],[LLbls,_1,Offsets,_4],[LLbls,_1,_3],[LLbls,_1,_3,_4],[LLbls,_1,_4],[LLbls,Offsets],[_1],[_1,Offsets],[_1,Offsets,_3],[_1,Offsets,_3,_4],[_1,Offsets,_4],[_1,_3],[_1,_3,_4],[_1,_4],[_2],[Offsets],[I1]]),ground([I,N,Inf,Midf]);mshare([[T,In,LLbls,_1,Offsets,A,Mid],[T,In,LLbls,_1,Offsets,A,Mid,_3],[T,In,LLbls,_1,Offsets,A,Mid,_3,_4],[T,In,LLbls,_1,Offsets,A,Mid,_4],[T,In,LLbls,_1,A,Mid],[T,In,LLbls,_1,A,Mid,_3],[T,In,LLbls,_1,A,Mid,_3,_4],[T,In,LLbls,_1,A,Mid,_4],[T,In,LLbls,Offsets,A,Mid],[T,In,LLbls,A,Mid],[T,In,_1,Offsets,A,Mid],[T,In,_1,Offsets,A,Mid,_3],[T,In,_1,Offsets,A,Mid,_3,_4],[T,In,_1,Offsets,A,Mid,_4],[T,In,_1,A,Mid],[T,In,_1,A,Mid,_3],[T,In,_1,A,Mid,_3,_4],[T,In,_1,A,Mid,_4],[T,In,Offsets,A,Mid],[T,In,A,Mid],[T,LLbls,_1,Offsets,A],[T,LLbls,_1,Offsets,A,Mid],[T,LLbls,_1,Offsets,A,Mid,_3],[T,LLbls,_1,Offsets,A,Mid,_3,_4],[T,LLbls,_1,Offsets,A,Mid,_4],[T,LLbls,_1,Offsets,A,_3],[T,LLbls,_1,Offsets,A,_3,_4],[T,LLbls,_1,Offsets,A,_4],[T,LLbls,_1,A],[T,LLbls,_1,A,Mid],[T,LLbls,_1,A,Mid,_3],[T,LLbls,_1,A,Mid,_3,_4],[T,LLbls,_1,A,Mid,_4],[T,LLbls,_1,A,_3],[T,LLbls,_1,A,_3,_4],[T,LLbls,_1,A,_4],[T,LLbls,Offsets,A],[T,LLbls,Offsets,A,Mid],[T,LLbls,A],[T,LLbls,A,Mid],[T,_1,Offsets,A],[T,_1,Offsets,A,Mid],[T,_1,Offsets,A,Mid,_3],[T,_1,Offsets,A,Mid,_3,_4],[T,_1,Offsets,A,Mid,_4],[T,_1,Offsets,A,_3],[T,_1,Offsets,A,_3,_4],[T,_1,Offsets,A,_4],[T,_1,A],[T,_1,A,Mid],[T,_1,A,Mid,_3],[T,_1,A,Mid,_3,_4],[T,_1,A,Mid,_4],[T,_1,A,_3],[T,_1,A,_3,_4],[T,_1,A,_4],[T,Offsets,A],[T,Offsets,A,Mid],[T,A],[T,A,Mid],[In,LLbls,_1,Offsets,Mid],[In,LLbls,_1,Offsets,Mid,_3],[In,LLbls,_1,Offsets,Mid,_3,_4],[In,LLbls,_1,Offsets,Mid,_4],[In,LLbls,_1,Mid],[In,LLbls,_1,Mid,_3],[In,LLbls,_1,Mid,_3,_4],[In,LLbls,_1,Mid,_4],[In,LLbls,Offsets,Mid],[In,LLbls,Mid],[In,_1,Offsets,Mid],[In,_1,Offsets,Mid,_3],[In,_1,Offsets,Mid,_3,_4],[In,_1,Offsets,Mid,_4],[In,_1,Mid],[In,_1,Mid,_3],[In,_1,Mid,_3,_4],[In,_1,Mid,_4],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Offsets],[LLbls,_1,Offsets,_3],[LLbls,_1,Offsets,_3,_4],[LLbls,_1,Offsets,_4],[LLbls,_1,_3],[LLbls,_1,_3,_4],[LLbls,_1,_4],[LLbls,Offsets],[_1],[_1,Offsets],[_1,Offsets,_3],[_1,Offsets,_3,_4],[_1,Offsets,_4],[_1,_3],[_1,_3,_4],[_1,_4],[Offsets],[I1]]),ground([I,N,Inf,Outf,_2,Midf]);mshare([[T,In,_1,Offsets,A,Mid],[T,In,_1,Offsets,A,Mid,_3],[T,In,_1,Offsets,A,Mid,_3,_4],[T,In,_1,Offsets,A,Mid,_4],[T,In,_1,A,Mid],[T,In,_1,A,Mid,_3],[T,In,_1,A,Mid,_3,_4],[T,In,_1,A,Mid,_4],[T,In,Offsets,A,Mid],[T,In,A,Mid],[T,_1,Offsets,A],[T,_1,Offsets,A,Mid],[T,_1,Offsets,A,Mid,_3],[T,_1,Offsets,A,Mid,_3,_4],[T,_1,Offsets,A,Mid,_4],[T,_1,Offsets,A,_3],[T,_1,Offsets,A,_3,_4],[T,_1,Offsets,A,_4],[T,_1,A],[T,_1,A,Mid],[T,_1,A,Mid,_3],[T,_1,A,Mid,_3,_4],[T,_1,A,Mid,_4],[T,_1,A,_3],[T,_1,A,_3,_4],[T,_1,A,_4],[T,Offsets,A],[T,Offsets,A,Mid],[T,A],[T,A,Mid],[Outf],[In,_1,Offsets,Mid],[In,_1,Offsets,Mid,_3],[In,_1,Offsets,Mid,_3,_4],[In,_1,Offsets,Mid,_4],[In,_1,Mid],[In,_1,Mid,_3],[In,_1,Mid,_3,_4],[In,_1,Mid,_4],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[_1],[_1,Offsets],[_1,Offsets,_3],[_1,Offsets,_3,_4],[_1,Offsets,_4],[_1,_3],[_1,_3,_4],[_1,_4],[_2],[Offsets],[I1]]),ground([I,N,Inf,Midf]);mshare([[T,In,_1,Offsets,A,Mid],[T,In,_1,Offsets,A,Mid,_3],[T,In,_1,Offsets,A,Mid,_3,_4],[T,In,_1,Offsets,A,Mid,_4],[T,In,_1,A,Mid],[T,In,_1,A,Mid,_3],[T,In,_1,A,Mid,_3,_4],[T,In,_1,A,Mid,_4],[T,In,Offsets,A,Mid],[T,In,A,Mid],[T,_1,Offsets,A],[T,_1,Offsets,A,Mid],[T,_1,Offsets,A,Mid,_3],[T,_1,Offsets,A,Mid,_3,_4],[T,_1,Offsets,A,Mid,_4],[T,_1,Offsets,A,_3],[T,_1,Offsets,A,_3,_4],[T,_1,Offsets,A,_4],[T,_1,A],[T,_1,A,Mid],[T,_1,A,Mid,_3],[T,_1,A,Mid,_3,_4],[T,_1,A,Mid,_4],[T,_1,A,_3],[T,_1,A,_3,_4],[T,_1,A,_4],[T,Offsets,A],[T,Offsets,A,Mid],[T,A],[T,A,Mid],[In,_1,Offsets,Mid],[In,_1,Offsets,Mid,_3],[In,_1,Offsets,Mid,_3,_4],[In,_1,Offsets,Mid,_4],[In,_1,Mid],[In,_1,Mid,_3],[In,_1,Mid,_3,_4],[In,_1,Mid,_4],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[_1],[_1,Offsets],[_1,Offsets,_3],[_1,Offsets,_3,_4],[_1,Offsets,_4],[_1,_3],[_1,_3,_4],[_1,_4],[Offsets],[I1]]),ground([I,N,Inf,Outf,_2,Midf]))),
    I1 is I+1,
    true((mshare([[T,In,LLbls,_1,Offsets,A,Mid],[T,In,LLbls,_1,Offsets,A,Mid,_3],[T,In,LLbls,_1,Offsets,A,Mid,_3,_4],[T,In,LLbls,_1,Offsets,A,Mid,_4],[T,In,LLbls,_1,A,Mid],[T,In,LLbls,_1,A,Mid,_3],[T,In,LLbls,_1,A,Mid,_3,_4],[T,In,LLbls,_1,A,Mid,_4],[T,In,LLbls,Offsets,A,Mid],[T,In,LLbls,A,Mid],[T,In,_1,Offsets,A,Mid],[T,In,_1,Offsets,A,Mid,_3],[T,In,_1,Offsets,A,Mid,_3,_4],[T,In,_1,Offsets,A,Mid,_4],[T,In,_1,A,Mid],[T,In,_1,A,Mid,_3],[T,In,_1,A,Mid,_3,_4],[T,In,_1,A,Mid,_4],[T,In,Offsets,A,Mid],[T,In,A,Mid],[T,LLbls,_1,Offsets,A],[T,LLbls,_1,Offsets,A,Mid],[T,LLbls,_1,Offsets,A,Mid,_3],[T,LLbls,_1,Offsets,A,Mid,_3,_4],[T,LLbls,_1,Offsets,A,Mid,_4],[T,LLbls,_1,Offsets,A,_3],[T,LLbls,_1,Offsets,A,_3,_4],[T,LLbls,_1,Offsets,A,_4],[T,LLbls,_1,A],[T,LLbls,_1,A,Mid],[T,LLbls,_1,A,Mid,_3],[T,LLbls,_1,A,Mid,_3,_4],[T,LLbls,_1,A,Mid,_4],[T,LLbls,_1,A,_3],[T,LLbls,_1,A,_3,_4],[T,LLbls,_1,A,_4],[T,LLbls,Offsets,A],[T,LLbls,Offsets,A,Mid],[T,LLbls,A],[T,LLbls,A,Mid],[T,_1,Offsets,A],[T,_1,Offsets,A,Mid],[T,_1,Offsets,A,Mid,_3],[T,_1,Offsets,A,Mid,_3,_4],[T,_1,Offsets,A,Mid,_4],[T,_1,Offsets,A,_3],[T,_1,Offsets,A,_3,_4],[T,_1,Offsets,A,_4],[T,_1,A],[T,_1,A,Mid],[T,_1,A,Mid,_3],[T,_1,A,Mid,_3,_4],[T,_1,A,Mid,_4],[T,_1,A,_3],[T,_1,A,_3,_4],[T,_1,A,_4],[T,Offsets,A],[T,Offsets,A,Mid],[T,A],[T,A,Mid],[Outf],[In,LLbls,_1,Offsets,Mid],[In,LLbls,_1,Offsets,Mid,_3],[In,LLbls,_1,Offsets,Mid,_3,_4],[In,LLbls,_1,Offsets,Mid,_4],[In,LLbls,_1,Mid],[In,LLbls,_1,Mid,_3],[In,LLbls,_1,Mid,_3,_4],[In,LLbls,_1,Mid,_4],[In,LLbls,Offsets,Mid],[In,LLbls,Mid],[In,_1,Offsets,Mid],[In,_1,Offsets,Mid,_3],[In,_1,Offsets,Mid,_3,_4],[In,_1,Offsets,Mid,_4],[In,_1,Mid],[In,_1,Mid,_3],[In,_1,Mid,_3,_4],[In,_1,Mid,_4],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Offsets],[LLbls,_1,Offsets,_3],[LLbls,_1,Offsets,_3,_4],[LLbls,_1,Offsets,_4],[LLbls,_1,_3],[LLbls,_1,_3,_4],[LLbls,_1,_4],[LLbls,Offsets],[_1],[_1,Offsets],[_1,Offsets,_3],[_1,Offsets,_3,_4],[_1,Offsets,_4],[_1,_3],[_1,_3,_4],[_1,_4],[_2],[Offsets]]),ground([I,N,Inf,Midf,I1]);mshare([[T,In,LLbls,_1,Offsets,A,Mid],[T,In,LLbls,_1,Offsets,A,Mid,_3],[T,In,LLbls,_1,Offsets,A,Mid,_3,_4],[T,In,LLbls,_1,Offsets,A,Mid,_4],[T,In,LLbls,_1,A,Mid],[T,In,LLbls,_1,A,Mid,_3],[T,In,LLbls,_1,A,Mid,_3,_4],[T,In,LLbls,_1,A,Mid,_4],[T,In,LLbls,Offsets,A,Mid],[T,In,LLbls,A,Mid],[T,In,_1,Offsets,A,Mid],[T,In,_1,Offsets,A,Mid,_3],[T,In,_1,Offsets,A,Mid,_3,_4],[T,In,_1,Offsets,A,Mid,_4],[T,In,_1,A,Mid],[T,In,_1,A,Mid,_3],[T,In,_1,A,Mid,_3,_4],[T,In,_1,A,Mid,_4],[T,In,Offsets,A,Mid],[T,In,A,Mid],[T,LLbls,_1,Offsets,A],[T,LLbls,_1,Offsets,A,Mid],[T,LLbls,_1,Offsets,A,Mid,_3],[T,LLbls,_1,Offsets,A,Mid,_3,_4],[T,LLbls,_1,Offsets,A,Mid,_4],[T,LLbls,_1,Offsets,A,_3],[T,LLbls,_1,Offsets,A,_3,_4],[T,LLbls,_1,Offsets,A,_4],[T,LLbls,_1,A],[T,LLbls,_1,A,Mid],[T,LLbls,_1,A,Mid,_3],[T,LLbls,_1,A,Mid,_3,_4],[T,LLbls,_1,A,Mid,_4],[T,LLbls,_1,A,_3],[T,LLbls,_1,A,_3,_4],[T,LLbls,_1,A,_4],[T,LLbls,Offsets,A],[T,LLbls,Offsets,A,Mid],[T,LLbls,A],[T,LLbls,A,Mid],[T,_1,Offsets,A],[T,_1,Offsets,A,Mid],[T,_1,Offsets,A,Mid,_3],[T,_1,Offsets,A,Mid,_3,_4],[T,_1,Offsets,A,Mid,_4],[T,_1,Offsets,A,_3],[T,_1,Offsets,A,_3,_4],[T,_1,Offsets,A,_4],[T,_1,A],[T,_1,A,Mid],[T,_1,A,Mid,_3],[T,_1,A,Mid,_3,_4],[T,_1,A,Mid,_4],[T,_1,A,_3],[T,_1,A,_3,_4],[T,_1,A,_4],[T,Offsets,A],[T,Offsets,A,Mid],[T,A],[T,A,Mid],[In,LLbls,_1,Offsets,Mid],[In,LLbls,_1,Offsets,Mid,_3],[In,LLbls,_1,Offsets,Mid,_3,_4],[In,LLbls,_1,Offsets,Mid,_4],[In,LLbls,_1,Mid],[In,LLbls,_1,Mid,_3],[In,LLbls,_1,Mid,_3,_4],[In,LLbls,_1,Mid,_4],[In,LLbls,Offsets,Mid],[In,LLbls,Mid],[In,_1,Offsets,Mid],[In,_1,Offsets,Mid,_3],[In,_1,Offsets,Mid,_3,_4],[In,_1,Offsets,Mid,_4],[In,_1,Mid],[In,_1,Mid,_3],[In,_1,Mid,_3,_4],[In,_1,Mid,_4],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[LLbls,_1],[LLbls,_1,Offsets],[LLbls,_1,Offsets,_3],[LLbls,_1,Offsets,_3,_4],[LLbls,_1,Offsets,_4],[LLbls,_1,_3],[LLbls,_1,_3,_4],[LLbls,_1,_4],[LLbls,Offsets],[_1],[_1,Offsets],[_1,Offsets,_3],[_1,Offsets,_3,_4],[_1,Offsets,_4],[_1,_3],[_1,_3,_4],[_1,_4],[Offsets]]),ground([I,N,Inf,Outf,_2,Midf,I1]);mshare([[T,In,_1,Offsets,A,Mid],[T,In,_1,Offsets,A,Mid,_3],[T,In,_1,Offsets,A,Mid,_3,_4],[T,In,_1,Offsets,A,Mid,_4],[T,In,_1,A,Mid],[T,In,_1,A,Mid,_3],[T,In,_1,A,Mid,_3,_4],[T,In,_1,A,Mid,_4],[T,In,Offsets,A,Mid],[T,In,A,Mid],[T,_1,Offsets,A],[T,_1,Offsets,A,Mid],[T,_1,Offsets,A,Mid,_3],[T,_1,Offsets,A,Mid,_3,_4],[T,_1,Offsets,A,Mid,_4],[T,_1,Offsets,A,_3],[T,_1,Offsets,A,_3,_4],[T,_1,Offsets,A,_4],[T,_1,A],[T,_1,A,Mid],[T,_1,A,Mid,_3],[T,_1,A,Mid,_3,_4],[T,_1,A,Mid,_4],[T,_1,A,_3],[T,_1,A,_3,_4],[T,_1,A,_4],[T,Offsets,A],[T,Offsets,A,Mid],[T,A],[T,A,Mid],[Outf],[In,_1,Offsets,Mid],[In,_1,Offsets,Mid,_3],[In,_1,Offsets,Mid,_3,_4],[In,_1,Offsets,Mid,_4],[In,_1,Mid],[In,_1,Mid,_3],[In,_1,Mid,_3,_4],[In,_1,Mid,_4],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[_1],[_1,Offsets],[_1,Offsets,_3],[_1,Offsets,_3,_4],[_1,Offsets,_4],[_1,_3],[_1,_3,_4],[_1,_4],[_2],[Offsets]]),ground([I,N,Inf,Midf,I1]);mshare([[T,In,_1,Offsets,A,Mid],[T,In,_1,Offsets,A,Mid,_3],[T,In,_1,Offsets,A,Mid,_3,_4],[T,In,_1,Offsets,A,Mid,_4],[T,In,_1,A,Mid],[T,In,_1,A,Mid,_3],[T,In,_1,A,Mid,_3,_4],[T,In,_1,A,Mid,_4],[T,In,Offsets,A,Mid],[T,In,A,Mid],[T,_1,Offsets,A],[T,_1,Offsets,A,Mid],[T,_1,Offsets,A,Mid,_3],[T,_1,Offsets,A,Mid,_3,_4],[T,_1,Offsets,A,Mid,_4],[T,_1,Offsets,A,_3],[T,_1,Offsets,A,_3,_4],[T,_1,Offsets,A,_4],[T,_1,A],[T,_1,A,Mid],[T,_1,A,Mid,_3],[T,_1,A,Mid,_3,_4],[T,_1,A,Mid,_4],[T,_1,A,_3],[T,_1,A,_3,_4],[T,_1,A,_4],[T,Offsets,A],[T,Offsets,A,Mid],[T,A],[T,A,Mid],[In,_1,Offsets,Mid],[In,_1,Offsets,Mid,_3],[In,_1,Offsets,Mid,_3,_4],[In,_1,Offsets,Mid,_4],[In,_1,Mid],[In,_1,Mid,_3],[In,_1,Mid,_3,_4],[In,_1,Mid,_4],[In,Offsets,Mid],[In,Mid],[Out],[LLbls],[_1],[_1,Offsets],[_1,Offsets,_3],[_1,Offsets,_3,_4],[_1,Offsets,_4],[_1,_3],[_1,_3,_4],[_1,_4],[Offsets]]),ground([I,N,Inf,Outf,_2,Midf,I1]))),
    block_args(I1,N,T,Midf,Outf,Offsets,Mid,Out,LLbls,_4,_2),
    true((mshare([[T,In,Out,LLbls,_1,_2,A,Mid,_3,_4],[T,In,Out,LLbls,_1,_2,A,Mid,_4],[T,In,Out,LLbls,_1,A,Mid,_3,_4],[T,In,Out,LLbls,_1,A,Mid,_4],[T,In,Out,_1,_2,A,Mid,_3,_4],[T,In,Out,_1,_2,A,Mid,_4],[T,In,Out,_1,A,Mid],[T,In,Out,_1,A,Mid,_3],[T,In,Out,_1,A,Mid,_3,_4],[T,In,Out,_1,A,Mid,_4],[T,In,Out,A,Mid],[T,Out,LLbls,_1,_2,A,Mid,_3,_4],[T,Out,LLbls,_1,_2,A,Mid,_4],[T,Out,LLbls,_1,_2,A,_3,_4],[T,Out,LLbls,_1,_2,A,_4],[T,Out,LLbls,_1,A,Mid,_3,_4],[T,Out,LLbls,_1,A,Mid,_4],[T,Out,LLbls,_1,A,_3,_4],[T,Out,LLbls,_1,A,_4],[T,Out,_1,_2,A,Mid,_3,_4],[T,Out,_1,_2,A,Mid,_4],[T,Out,_1,_2,A,_3,_4],[T,Out,_1,_2,A,_4],[T,Out,_1,A],[T,Out,_1,A,Mid],[T,Out,_1,A,Mid,_3],[T,Out,_1,A,Mid,_3,_4],[T,Out,_1,A,Mid,_4],[T,Out,_1,A,_3],[T,Out,_1,A,_3,_4],[T,Out,_1,A,_4],[T,Out,A],[T,Out,A,Mid],[T,LLbls,_1,_2,A,_3,_4],[T,LLbls,_1,_2,A,_4],[T,LLbls,_1,A,_3,_4],[T,LLbls,_1,A,_4],[T,_1,_2,A,_3,_4],[T,_1,_2,A,_4],[T,_1,A],[T,_1,A,_3],[T,_1,A,_3,_4],[T,_1,A,_4],[T,A],[In,Out,LLbls,_1,_2,Mid,_3,_4],[In,Out,LLbls,_1,_2,Mid,_4],[In,Out,LLbls,_1,Mid,_3,_4],[In,Out,LLbls,_1,Mid,_4],[In,Out,_1,_2,Mid,_3,_4],[In,Out,_1,_2,Mid,_4],[In,Out,_1,Mid],[In,Out,_1,Mid,_3],[In,Out,_1,Mid,_3,_4],[In,Out,_1,Mid,_4],[In,Out,Mid],[LLbls,_1,_2,_3,_4],[LLbls,_1,_2,_4],[LLbls,_1,_3,_4],[LLbls,_1,_4],[_1],[_1,_2,_3,_4],[_1,_2,_4],[_1,_3],[_1,_3,_4],[_1,_4]]),ground([I,N,Inf,Outf,Offsets,Midf,I1]);mshare([[T,In,Out,LLbls,_1,A,Mid,_3,_4],[T,In,Out,LLbls,_1,A,Mid,_4],[T,In,Out,_1,A,Mid],[T,In,Out,_1,A,Mid,_3],[T,In,Out,_1,A,Mid,_3,_4],[T,In,Out,_1,A,Mid,_4],[T,In,Out,A,Mid],[T,Out,LLbls,_1,A,Mid,_3,_4],[T,Out,LLbls,_1,A,Mid,_4],[T,Out,LLbls,_1,A,_3,_4],[T,Out,LLbls,_1,A,_4],[T,Out,_1,A],[T,Out,_1,A,Mid],[T,Out,_1,A,Mid,_3],[T,Out,_1,A,Mid,_3,_4],[T,Out,_1,A,Mid,_4],[T,Out,_1,A,_3],[T,Out,_1,A,_3,_4],[T,Out,_1,A,_4],[T,Out,A],[T,Out,A,Mid],[T,LLbls,_1,A,_3,_4],[T,LLbls,_1,A,_4],[T,_1,A],[T,_1,A,_3],[T,_1,A,_3,_4],[T,_1,A,_4],[T,A],[In,Out,LLbls,_1,Mid,_3,_4],[In,Out,LLbls,_1,Mid,_4],[In,Out,_1,Mid],[In,Out,_1,Mid,_3],[In,Out,_1,Mid,_3,_4],[In,Out,_1,Mid,_4],[In,Out,Mid],[LLbls,_1,_3,_4],[LLbls,_1,_4],[_1],[_1,_3],[_1,_3,_4],[_1,_4]]),ground([I,N,Inf,Outf,_2,Offsets,Midf,I1]))).

:- true pred make_slots(I,N,_1,_2,_A,In,Out,_3,_4)
   : ( (I=1), (N=2),
       mshare([[_1],[_1,In],[_1,In,_3],[_1,_3],[_A],[In],[In,_3],[Out],[_3],[_4]]),
       ground([_2]) )
   => ( mshare([[_1],[_1,_A],[_1,_A,In,Out],[_1,_A,In,Out,_3],[_1,_A,In,Out,_3,_4],[_1,_A,Out],[_1,_A,Out,_3],[_1,_A,Out,_3,_4],[_1,_A,_3],[_1,_A,_3,_4],[_1,In,Out],[_1,In,Out,_3],[_1,In,Out,_3,_4],[_1,Out],[_1,Out,_3],[_1,Out,_3,_4],[_1,_3],[_1,_3,_4],[_A],[_A,In,Out],[_A,In,Out,_3],[_A,In,Out,_3,_4],[_A,_3],[_A,_3,_4],[In,Out],[In,Out,_3,_4],[_3,_4]]),
        ground([_2]) ).

:- true pred make_slots(I,N,_1,_2,_A,In,Out,_3,_4)
   : ( (I=1),
       mshare([[_1],[_1,In],[_1,In,_3],[_1,_3],[_A],[In],[In,_3],[Out],[_3],[_4]]),
       ground([N,_2]) )
   => ( mshare([[_1],[_1,_A],[_1,_A,In,Out],[_1,_A,In,Out,_3],[_1,_A,In,Out,_3,_4],[_1,_A,Out],[_1,_A,Out,_3],[_1,_A,Out,_3,_4],[_1,_A,_3],[_1,_A,_3,_4],[_1,In,Out],[_1,In,Out,_3],[_1,In,Out,_3,_4],[_1,Out],[_1,Out,_3],[_1,Out,_3,_4],[_1,_3],[_1,_3,_4],[_A],[_A,In,Out],[_A,In,Out,_3],[_A,In,Out,_3,_4],[_A,_3],[_A,_3,_4],[In,Out],[In,Out,_3,_4],[_3,_4]]),
        ground([N,_2]) ).

:- true pred make_slots(I,N,_1,_2,_A,In,Out,_3,_4)
   : ( (I=1), (N=2),
       mshare([[_1],[_A],[In],[In,_3],[Out],[_3],[_4]]),
       ground([_2]) )
   => ( mshare([[_1],[_1,_A],[_1,_A,In,Out],[_1,_A,In,Out,_3],[_1,_A,In,Out,_3,_4],[_1,_A,Out],[_1,_A,Out,_3],[_1,_A,Out,_3,_4],[_1,_A,_3],[_1,_A,_3,_4],[_1,In,Out],[_1,In,Out,_3],[_1,In,Out,_3,_4],[_1,Out],[_1,Out,_3],[_1,Out,_3,_4],[_1,_3],[_1,_3,_4],[_A],[_A,In,Out],[_A,In,Out,_3],[_A,In,Out,_3,_4],[_A,_3],[_A,_3,_4],[In,Out],[In,Out,_3,_4],[_3,_4]]),
        ground([_2]) ).

:- true pred make_slots(I,N,_1,_2,_A,In,Out,_3,_4)
   : ( mshare([[_1],[_1,_A],[_1,_A,In],[_1,_A,In,_3],[_1,_A,_3],[_1,In],[_1,In,_3],[_1,_3],[_A],[_A,In],[_A,In,_3],[_A,_3],[In],[In,_3],[Out],[_3],[_4]]),
       ground([I,N,_2]) )
   => ( mshare([[_1],[_1,_A],[_1,_A,In,Out],[_1,_A,In,Out,_3],[_1,_A,In,Out,_3,_4],[_1,_A,Out],[_1,_A,Out,_3],[_1,_A,Out,_3,_4],[_1,_A,_3],[_1,_A,_3,_4],[_1,In,Out],[_1,In,Out,_3],[_1,In,Out,_3,_4],[_1,Out],[_1,Out,_3],[_1,Out,_3,_4],[_1,_3],[_1,_3,_4],[_A],[_A,In,Out],[_A,In,Out,_3],[_A,In,Out,_3,_4],[_A,_3],[_A,_3,_4],[In,Out],[In,Out,_3,_4],[_3,_4]]),
        ground([I,N,_2]) ).

:- true pred make_slots(I,N,_1,_2,_A,In,Out,_3,_4)
   : ( (I=1),
       mshare([[_1],[_A],[In],[In,_3],[Out],[_3],[_4]]),
       ground([N,_2]) )
   => ( mshare([[_1],[_1,_A],[_1,_A,In,Out],[_1,_A,In,Out,_3],[_1,_A,In,Out,_3,_4],[_1,_A,Out],[_1,_A,Out,_3],[_1,_A,Out,_3,_4],[_1,_A,_3],[_1,_A,_3,_4],[_1,In,Out],[_1,In,Out,_3],[_1,In,Out,_3,_4],[_1,Out],[_1,Out,_3],[_1,Out,_3,_4],[_1,_3],[_1,_3,_4],[_A],[_A,In,Out],[_A,In,Out,_3],[_A,In,Out,_3,_4],[_A,_3],[_A,_3,_4],[In,Out],[In,Out,_3,_4],[_3,_4]]),
        ground([N,_2]) ).

make_slots(I,N,_1,_2,[],In,In,_3,_4) :-
    true((mshare([[_1],[_1,In],[_1,In,_3],[_1,_3],[In],[In,_3],[_3],[_4]]),ground([I,N,_2]);mshare([[_1],[In],[In,_3],[_3],[_4]]),ground([I,N,_2]))),
    I>N,
    !,
    true((mshare([[_1],[_1,In],[_1,In,_3],[_1,_3],[In],[In,_3],[_3],[_4]]),ground([I,N,_2]);mshare([[_1],[In],[In,_3],[_3],[_4]]),ground([I,N,_2]))),
    _4=_3,
    true((mshare([[_1],[_1,In],[_1,In,_3,_4],[_1,_3,_4],[In],[In,_3,_4],[_3,_4]]),ground([I,N,_2]);mshare([[_1],[In],[In,_3,_4],[_3,_4]]),ground([I,N,_2]))).
make_slots(I,N,T,S,[Off|Offsets],In,Out,_1,_2) :-
    true((mshare([[T],[T,In],[T,In,_1],[T,In,_1,Off],[T,In,_1,Off,Offsets],[T,In,_1,Offsets],[T,In,Off],[T,In,Off,Offsets],[T,In,Offsets],[T,_1],[T,_1,Off],[T,_1,Off,Offsets],[T,_1,Offsets],[T,Off],[T,Off,Offsets],[T,Offsets],[In],[In,_1],[In,_1,Off],[In,_1,Off,Offsets],[In,_1,Offsets],[In,Off],[In,Off,Offsets],[In,Offsets],[Out],[_1],[_1,Off],[_1,Off,Offsets],[_1,Offsets],[_2],[Off],[Off,Offsets],[Offsets],[A],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]);mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[_1],[_2],[Off],[Off,Offsets],[Offsets],[A],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]);mshare([[T],[In],[In,_1],[Out],[_1],[_2],[Off],[Off,Offsets],[Offsets],[A],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]))),
    I=<N,
    !,
    true((mshare([[T],[T,In],[T,In,_1],[T,In,_1,Off],[T,In,_1,Off,Offsets],[T,In,_1,Offsets],[T,In,Off],[T,In,Off,Offsets],[T,In,Offsets],[T,_1],[T,_1,Off],[T,_1,Off,Offsets],[T,_1,Offsets],[T,Off],[T,Off,Offsets],[T,Offsets],[In],[In,_1],[In,_1,Off],[In,_1,Off,Offsets],[In,_1,Offsets],[In,Off],[In,Off,Offsets],[In,Offsets],[Out],[_1],[_1,Off],[_1,Off,Offsets],[_1,Offsets],[_2],[Off],[Off,Offsets],[Offsets],[A],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]);mshare([[T],[T,In],[T,In,_1],[T,_1],[In],[In,_1],[Out],[_1],[_2],[Off],[Off,Offsets],[Offsets],[A],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]);mshare([[T],[In],[In,_1],[Out],[_1],[_2],[Off],[Off,Offsets],[Offsets],[A],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]))),
    arg(I,T,A),
    true((mshare([[T,In,_1,Off,Offsets,A],[T,In,_1,Off,A],[T,In,_1,Offsets,A],[T,In,_1,A],[T,In,Off,Offsets,A],[T,In,Off,A],[T,In,Offsets,A],[T,In,A],[T,_1,Off,Offsets,A],[T,_1,Off,A],[T,_1,Offsets,A],[T,_1,A],[T,Off,Offsets,A],[T,Off,A],[T,Offsets,A],[T,A],[In],[In,_1],[In,_1,Off],[In,_1,Off,Offsets],[In,_1,Offsets],[In,Off],[In,Off,Offsets],[In,Offsets],[Out],[_1],[_1,Off],[_1,Off,Offsets],[_1,Offsets],[_2],[Off],[Off,Offsets],[Offsets],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]);mshare([[T,In,_1,A],[T,In,A],[T,_1,A],[T,A],[In],[In,_1],[Out],[_1],[_2],[Off],[Off,Offsets],[Offsets],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]);mshare([[T,A],[In],[In,_1],[Out],[_1],[_2],[Off],[Off,Offsets],[Offsets],[_3],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]))),
    init_var(A,S,In,_1,_3),
    true((mshare([[T,In,_1,Off,Offsets,A],[T,In,_1,Off,Offsets,A,_3],[T,In,_1,Off,A],[T,In,_1,Off,A,_3],[T,In,_1,Offsets,A],[T,In,_1,Offsets,A,_3],[T,In,_1,A],[T,In,_1,A,_3],[T,In,Off,Offsets,A],[T,In,Off,A],[T,In,Offsets,A],[T,In,A],[T,_1,Off,Offsets,A],[T,_1,Off,Offsets,A,_3],[T,_1,Off,A],[T,_1,Off,A,_3],[T,_1,Offsets,A],[T,_1,Offsets,A,_3],[T,_1,A],[T,_1,A,_3],[T,Off,Offsets,A],[T,Off,A],[T,Offsets,A],[T,A],[In],[In,_1,Off,Offsets,_3],[In,_1,Off,_3],[In,_1,Offsets,_3],[In,_1,_3],[In,Off],[In,Off,Offsets],[In,Offsets],[Out],[_1,Off,Offsets,_3],[_1,Off,_3],[_1,Offsets,_3],[_1,_3],[_2],[Off],[Off,Offsets],[Offsets],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]);mshare([[T,In,_1,A],[T,In,_1,A,_3],[T,In,A],[T,_1,A],[T,_1,A,_3],[T,A],[In],[In,_1,_3],[Out],[_1,_3],[_2],[Off],[Off,Offsets],[Offsets],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]);mshare([[T,In,_1,A],[T,In,_1,A,_3],[T,_1,A],[T,_1,A,_3],[T,A],[In],[In,_1,_3],[Out],[_1,_3],[_2],[Off],[Off,Offsets],[Offsets],[Mid],[Word],[_4],[S1],[I1]]),ground([I,N,S]))),
    incl(A,In,Mid),
    true((mshare([[T,In,_1,Off,Offsets,A,_3,Mid],[T,In,_1,Off,Offsets,A,Mid],[T,In,_1,Off,A,_3,Mid],[T,In,_1,Off,A,Mid],[T,In,_1,Offsets,A,_3,Mid],[T,In,_1,Offsets,A,Mid],[T,In,_1,A,_3,Mid],[T,In,_1,A,Mid],[T,In,Off,Offsets,A,Mid],[T,In,Off,A,Mid],[T,In,Offsets,A,Mid],[T,In,A,Mid],[T,_1,Off,Offsets,A],[T,_1,Off,Offsets,A,_3],[T,_1,Off,Offsets,A,_3,Mid],[T,_1,Off,Offsets,A,Mid],[T,_1,Off,A],[T,_1,Off,A,_3],[T,_1,Off,A,_3,Mid],[T,_1,Off,A,Mid],[T,_1,Offsets,A],[T,_1,Offsets,A,_3],[T,_1,Offsets,A,_3,Mid],[T,_1,Offsets,A,Mid],[T,_1,A],[T,_1,A,_3],[T,_1,A,_3,Mid],[T,_1,A,Mid],[T,Off,Offsets,A],[T,Off,Offsets,A,Mid],[T,Off,A],[T,Off,A,Mid],[T,Offsets,A],[T,Offsets,A,Mid],[T,A],[T,A,Mid],[In,_1,Off,Offsets,_3,Mid],[In,_1,Off,_3,Mid],[In,_1,Offsets,_3,Mid],[In,_1,_3,Mid],[In,Off,Offsets,Mid],[In,Off,Mid],[In,Offsets,Mid],[In,Mid],[Out],[_1,Off,Offsets,_3],[_1,Off,_3],[_1,Offsets,_3],[_1,_3],[_2],[Off],[Off,Offsets],[Offsets],[Word],[_4],[S1],[I1]]),ground([I,N,S]);mshare([[T,In,_1,A,_3,Mid],[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,A],[T,_1,A,_3],[T,_1,A,_3,Mid],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,_1,_3,Mid],[In,Mid],[Out],[_1,_3],[_2],[Off],[Off,Offsets],[Offsets],[Word],[_4],[S1],[I1]]),ground([I,N,S]))),
    make_word(A,Off,Word),
    true((mshare([[T,In,_1,Off,Offsets,A,_3,Mid],[T,In,_1,Off,Offsets,A,_3,Mid,Word],[T,In,_1,Off,Offsets,A,Mid],[T,In,_1,Off,Offsets,A,Mid,Word],[T,In,_1,Off,A,_3,Mid],[T,In,_1,Off,A,_3,Mid,Word],[T,In,_1,Off,A,Mid],[T,In,_1,Off,A,Mid,Word],[T,In,_1,Offsets,A,_3,Mid],[T,In,_1,Offsets,A,_3,Mid,Word],[T,In,_1,Offsets,A,Mid],[T,In,_1,Offsets,A,Mid,Word],[T,In,_1,A,_3,Mid],[T,In,_1,A,_3,Mid,Word],[T,In,_1,A,Mid],[T,In,_1,A,Mid,Word],[T,In,Off,Offsets,A,Mid],[T,In,Off,Offsets,A,Mid,Word],[T,In,Off,A,Mid],[T,In,Off,A,Mid,Word],[T,In,Offsets,A,Mid],[T,In,Offsets,A,Mid,Word],[T,In,A,Mid],[T,In,A,Mid,Word],[T,_1,Off,Offsets,A],[T,_1,Off,Offsets,A,_3],[T,_1,Off,Offsets,A,_3,Mid],[T,_1,Off,Offsets,A,_3,Mid,Word],[T,_1,Off,Offsets,A,_3,Word],[T,_1,Off,Offsets,A,Mid],[T,_1,Off,Offsets,A,Mid,Word],[T,_1,Off,Offsets,A,Word],[T,_1,Off,A],[T,_1,Off,A,_3],[T,_1,Off,A,_3,Mid],[T,_1,Off,A,_3,Mid,Word],[T,_1,Off,A,_3,Word],[T,_1,Off,A,Mid],[T,_1,Off,A,Mid,Word],[T,_1,Off,A,Word],[T,_1,Offsets,A],[T,_1,Offsets,A,_3],[T,_1,Offsets,A,_3,Mid],[T,_1,Offsets,A,_3,Mid,Word],[T,_1,Offsets,A,_3,Word],[T,_1,Offsets,A,Mid],[T,_1,Offsets,A,Mid,Word],[T,_1,Offsets,A,Word],[T,_1,A],[T,_1,A,_3],[T,_1,A,_3,Mid],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Word],[T,_1,A,Mid],[T,_1,A,Mid,Word],[T,_1,A,Word],[T,Off,Offsets,A],[T,Off,Offsets,A,Mid],[T,Off,Offsets,A,Mid,Word],[T,Off,Offsets,A,Word],[T,Off,A],[T,Off,A,Mid],[T,Off,A,Mid,Word],[T,Off,A,Word],[T,Offsets,A],[T,Offsets,A,Mid],[T,Offsets,A,Mid,Word],[T,Offsets,A,Word],[T,A],[T,A,Mid],[T,A,Mid,Word],[T,A,Word],[In,_1,Off,Offsets,_3,Mid],[In,_1,Off,Offsets,_3,Mid,Word],[In,_1,Off,_3,Mid],[In,_1,Off,_3,Mid,Word],[In,_1,Offsets,_3,Mid],[In,_1,_3,Mid],[In,Off,Offsets,Mid],[In,Off,Offsets,Mid,Word],[In,Off,Mid],[In,Off,Mid,Word],[In,Offsets,Mid],[In,Mid],[Out],[_1,Off,Offsets,_3],[_1,Off,Offsets,_3,Word],[_1,Off,_3],[_1,Off,_3,Word],[_1,Offsets,_3],[_1,_3],[_2],[Off],[Off,Offsets],[Off,Offsets,Word],[Off,Word],[Offsets],[_4],[S1],[I1]]),ground([I,N,S]);mshare([[T,In,_1,Off,Offsets,A,_3,Mid,Word],[T,In,_1,Off,Offsets,A,Mid,Word],[T,In,_1,Off,A,_3,Mid,Word],[T,In,_1,Off,A,Mid,Word],[T,In,_1,A,_3,Mid],[T,In,_1,A,_3,Mid,Word],[T,In,_1,A,Mid],[T,In,_1,A,Mid,Word],[T,In,Off,Offsets,A,Mid,Word],[T,In,Off,A,Mid,Word],[T,In,A,Mid],[T,In,A,Mid,Word],[T,_1,Off,Offsets,A,_3,Mid,Word],[T,_1,Off,Offsets,A,_3,Word],[T,_1,Off,Offsets,A,Mid,Word],[T,_1,Off,Offsets,A,Word],[T,_1,Off,A,_3,Mid,Word],[T,_1,Off,A,_3,Word],[T,_1,Off,A,Mid,Word],[T,_1,Off,A,Word],[T,_1,A],[T,_1,A,_3],[T,_1,A,_3,Mid],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Word],[T,_1,A,Mid],[T,_1,A,Mid,Word],[T,_1,A,Word],[T,Off,Offsets,A,Mid,Word],[T,Off,Offsets,A,Word],[T,Off,A,Mid,Word],[T,Off,A,Word],[T,A],[T,A,Mid],[T,A,Mid,Word],[T,A,Word],[In,_1,_3,Mid],[In,Mid],[Out],[_1,_3],[_2],[Off],[Off,Offsets],[Off,Offsets,Word],[Off,Word],[Offsets],[_4],[S1],[I1]]),ground([I,N,S]))),
    'C'(_3,move(Word,[h+S]),_4),
    true((mshare([[T,In,_1,Off,Offsets,A,_3,Mid,Word],[T,In,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,In,_1,Off,Offsets,A,_3,Mid,_4],[T,In,_1,Off,Offsets,A,Mid],[T,In,_1,Off,A,_3,Mid,Word],[T,In,_1,Off,A,_3,Mid,Word,_4],[T,In,_1,Off,A,_3,Mid,_4],[T,In,_1,Off,A,Mid],[T,In,_1,Offsets,A,_3,Mid,Word],[T,In,_1,Offsets,A,_3,Mid,Word,_4],[T,In,_1,Offsets,A,_3,Mid,_4],[T,In,_1,Offsets,A,Mid],[T,In,_1,A,_3,Mid,Word],[T,In,_1,A,_3,Mid,Word,_4],[T,In,_1,A,_3,Mid,_4],[T,In,_1,A,Mid],[T,In,Off,Offsets,A,Mid],[T,In,Off,A,Mid],[T,In,Offsets,A,Mid],[T,In,A,Mid],[T,_1,Off,Offsets,A],[T,_1,Off,Offsets,A,_3,Mid,Word],[T,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,_1,Off,Offsets,A,_3,Mid,_4],[T,_1,Off,Offsets,A,_3,Word],[T,_1,Off,Offsets,A,_3,Word,_4],[T,_1,Off,Offsets,A,_3,_4],[T,_1,Off,Offsets,A,Mid],[T,_1,Off,A],[T,_1,Off,A,_3,Mid,Word],[T,_1,Off,A,_3,Mid,Word,_4],[T,_1,Off,A,_3,Mid,_4],[T,_1,Off,A,_3,Word],[T,_1,Off,A,_3,Word,_4],[T,_1,Off,A,_3,_4],[T,_1,Off,A,Mid],[T,_1,Offsets,A],[T,_1,Offsets,A,_3,Mid,Word],[T,_1,Offsets,A,_3,Mid,Word,_4],[T,_1,Offsets,A,_3,Mid,_4],[T,_1,Offsets,A,_3,Word],[T,_1,Offsets,A,_3,Word,_4],[T,_1,Offsets,A,_3,_4],[T,_1,Offsets,A,Mid],[T,_1,A],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Mid,Word,_4],[T,_1,A,_3,Mid,_4],[T,_1,A,_3,Word],[T,_1,A,_3,Word,_4],[T,_1,A,_3,_4],[T,_1,A,Mid],[T,Off,Offsets,A],[T,Off,Offsets,A,Mid],[T,Off,A],[T,Off,A,Mid],[T,Offsets,A],[T,Offsets,A,Mid],[T,A],[T,A,Mid],[In,_1,Off,Offsets,_3,Mid,Word],[In,_1,Off,Offsets,_3,Mid,Word,_4],[In,_1,Off,Offsets,_3,Mid,_4],[In,_1,Off,_3,Mid,Word],[In,_1,Off,_3,Mid,Word,_4],[In,_1,Off,_3,Mid,_4],[In,_1,Offsets,_3,Mid,_4],[In,_1,_3,Mid,_4],[In,Off,Offsets,Mid],[In,Off,Mid],[In,Offsets,Mid],[In,Mid],[Out],[_1,Off,Offsets,_3,Word],[_1,Off,Offsets,_3,Word,_4],[_1,Off,Offsets,_3,_4],[_1,Off,_3,Word],[_1,Off,_3,Word,_4],[_1,Off,_3,_4],[_1,Offsets,_3,_4],[_1,_3,_4],[_2],[Off],[Off,Offsets],[Offsets],[S1],[I1]]),ground([I,N,S]);mshare([[T,In,_1,Off,Offsets,A,_3,Mid,Word],[T,In,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,In,_1,Off,A,_3,Mid,Word],[T,In,_1,Off,A,_3,Mid,Word,_4],[T,In,_1,A,_3,Mid,Word],[T,In,_1,A,_3,Mid,Word,_4],[T,In,_1,A,_3,Mid,_4],[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,Off,Offsets,A,_3,Mid,Word],[T,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,_1,Off,Offsets,A,_3,Word],[T,_1,Off,Offsets,A,_3,Word,_4],[T,_1,Off,A,_3,Mid,Word],[T,_1,Off,A,_3,Mid,Word,_4],[T,_1,Off,A,_3,Word],[T,_1,Off,A,_3,Word,_4],[T,_1,A],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Mid,Word,_4],[T,_1,A,_3,Mid,_4],[T,_1,A,_3,Word],[T,_1,A,_3,Word,_4],[T,_1,A,_3,_4],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,_1,Off,Offsets,_3,Mid,Word],[In,_1,Off,Offsets,_3,Mid,Word,_4],[In,_1,Off,_3,Mid,Word],[In,_1,Off,_3,Mid,Word,_4],[In,_1,_3,Mid,_4],[In,Mid],[Out],[_1,Off,Offsets,_3,Word],[_1,Off,Offsets,_3,Word,_4],[_1,Off,_3,Word],[_1,Off,_3,Word,_4],[_1,_3,_4],[_2],[Off],[Off,Offsets],[Offsets],[S1],[I1]]),ground([I,N,S]))),
    S1 is S+1,
    true((mshare([[T,In,_1,Off,Offsets,A,_3,Mid,Word],[T,In,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,In,_1,Off,Offsets,A,_3,Mid,_4],[T,In,_1,Off,Offsets,A,Mid],[T,In,_1,Off,A,_3,Mid,Word],[T,In,_1,Off,A,_3,Mid,Word,_4],[T,In,_1,Off,A,_3,Mid,_4],[T,In,_1,Off,A,Mid],[T,In,_1,Offsets,A,_3,Mid,Word],[T,In,_1,Offsets,A,_3,Mid,Word,_4],[T,In,_1,Offsets,A,_3,Mid,_4],[T,In,_1,Offsets,A,Mid],[T,In,_1,A,_3,Mid,Word],[T,In,_1,A,_3,Mid,Word,_4],[T,In,_1,A,_3,Mid,_4],[T,In,_1,A,Mid],[T,In,Off,Offsets,A,Mid],[T,In,Off,A,Mid],[T,In,Offsets,A,Mid],[T,In,A,Mid],[T,_1,Off,Offsets,A],[T,_1,Off,Offsets,A,_3,Mid,Word],[T,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,_1,Off,Offsets,A,_3,Mid,_4],[T,_1,Off,Offsets,A,_3,Word],[T,_1,Off,Offsets,A,_3,Word,_4],[T,_1,Off,Offsets,A,_3,_4],[T,_1,Off,Offsets,A,Mid],[T,_1,Off,A],[T,_1,Off,A,_3,Mid,Word],[T,_1,Off,A,_3,Mid,Word,_4],[T,_1,Off,A,_3,Mid,_4],[T,_1,Off,A,_3,Word],[T,_1,Off,A,_3,Word,_4],[T,_1,Off,A,_3,_4],[T,_1,Off,A,Mid],[T,_1,Offsets,A],[T,_1,Offsets,A,_3,Mid,Word],[T,_1,Offsets,A,_3,Mid,Word,_4],[T,_1,Offsets,A,_3,Mid,_4],[T,_1,Offsets,A,_3,Word],[T,_1,Offsets,A,_3,Word,_4],[T,_1,Offsets,A,_3,_4],[T,_1,Offsets,A,Mid],[T,_1,A],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Mid,Word,_4],[T,_1,A,_3,Mid,_4],[T,_1,A,_3,Word],[T,_1,A,_3,Word,_4],[T,_1,A,_3,_4],[T,_1,A,Mid],[T,Off,Offsets,A],[T,Off,Offsets,A,Mid],[T,Off,A],[T,Off,A,Mid],[T,Offsets,A],[T,Offsets,A,Mid],[T,A],[T,A,Mid],[In,_1,Off,Offsets,_3,Mid,Word],[In,_1,Off,Offsets,_3,Mid,Word,_4],[In,_1,Off,Offsets,_3,Mid,_4],[In,_1,Off,_3,Mid,Word],[In,_1,Off,_3,Mid,Word,_4],[In,_1,Off,_3,Mid,_4],[In,_1,Offsets,_3,Mid,_4],[In,_1,_3,Mid,_4],[In,Off,Offsets,Mid],[In,Off,Mid],[In,Offsets,Mid],[In,Mid],[Out],[_1,Off,Offsets,_3,Word],[_1,Off,Offsets,_3,Word,_4],[_1,Off,Offsets,_3,_4],[_1,Off,_3,Word],[_1,Off,_3,Word,_4],[_1,Off,_3,_4],[_1,Offsets,_3,_4],[_1,_3,_4],[_2],[Off],[Off,Offsets],[Offsets],[I1]]),ground([I,N,S,S1]);mshare([[T,In,_1,Off,Offsets,A,_3,Mid,Word],[T,In,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,In,_1,Off,A,_3,Mid,Word],[T,In,_1,Off,A,_3,Mid,Word,_4],[T,In,_1,A,_3,Mid,Word],[T,In,_1,A,_3,Mid,Word,_4],[T,In,_1,A,_3,Mid,_4],[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,Off,Offsets,A,_3,Mid,Word],[T,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,_1,Off,Offsets,A,_3,Word],[T,_1,Off,Offsets,A,_3,Word,_4],[T,_1,Off,A,_3,Mid,Word],[T,_1,Off,A,_3,Mid,Word,_4],[T,_1,Off,A,_3,Word],[T,_1,Off,A,_3,Word,_4],[T,_1,A],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Mid,Word,_4],[T,_1,A,_3,Mid,_4],[T,_1,A,_3,Word],[T,_1,A,_3,Word,_4],[T,_1,A,_3,_4],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,_1,Off,Offsets,_3,Mid,Word],[In,_1,Off,Offsets,_3,Mid,Word,_4],[In,_1,Off,_3,Mid,Word],[In,_1,Off,_3,Mid,Word,_4],[In,_1,_3,Mid,_4],[In,Mid],[Out],[_1,Off,Offsets,_3,Word],[_1,Off,Offsets,_3,Word,_4],[_1,Off,_3,Word],[_1,Off,_3,Word,_4],[_1,_3,_4],[_2],[Off],[Off,Offsets],[Offsets],[I1]]),ground([I,N,S,S1]))),
    I1 is I+1,
    true((mshare([[T,In,_1,Off,Offsets,A,_3,Mid,Word],[T,In,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,In,_1,Off,Offsets,A,_3,Mid,_4],[T,In,_1,Off,Offsets,A,Mid],[T,In,_1,Off,A,_3,Mid,Word],[T,In,_1,Off,A,_3,Mid,Word,_4],[T,In,_1,Off,A,_3,Mid,_4],[T,In,_1,Off,A,Mid],[T,In,_1,Offsets,A,_3,Mid,Word],[T,In,_1,Offsets,A,_3,Mid,Word,_4],[T,In,_1,Offsets,A,_3,Mid,_4],[T,In,_1,Offsets,A,Mid],[T,In,_1,A,_3,Mid,Word],[T,In,_1,A,_3,Mid,Word,_4],[T,In,_1,A,_3,Mid,_4],[T,In,_1,A,Mid],[T,In,Off,Offsets,A,Mid],[T,In,Off,A,Mid],[T,In,Offsets,A,Mid],[T,In,A,Mid],[T,_1,Off,Offsets,A],[T,_1,Off,Offsets,A,_3,Mid,Word],[T,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,_1,Off,Offsets,A,_3,Mid,_4],[T,_1,Off,Offsets,A,_3,Word],[T,_1,Off,Offsets,A,_3,Word,_4],[T,_1,Off,Offsets,A,_3,_4],[T,_1,Off,Offsets,A,Mid],[T,_1,Off,A],[T,_1,Off,A,_3,Mid,Word],[T,_1,Off,A,_3,Mid,Word,_4],[T,_1,Off,A,_3,Mid,_4],[T,_1,Off,A,_3,Word],[T,_1,Off,A,_3,Word,_4],[T,_1,Off,A,_3,_4],[T,_1,Off,A,Mid],[T,_1,Offsets,A],[T,_1,Offsets,A,_3,Mid,Word],[T,_1,Offsets,A,_3,Mid,Word,_4],[T,_1,Offsets,A,_3,Mid,_4],[T,_1,Offsets,A,_3,Word],[T,_1,Offsets,A,_3,Word,_4],[T,_1,Offsets,A,_3,_4],[T,_1,Offsets,A,Mid],[T,_1,A],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Mid,Word,_4],[T,_1,A,_3,Mid,_4],[T,_1,A,_3,Word],[T,_1,A,_3,Word,_4],[T,_1,A,_3,_4],[T,_1,A,Mid],[T,Off,Offsets,A],[T,Off,Offsets,A,Mid],[T,Off,A],[T,Off,A,Mid],[T,Offsets,A],[T,Offsets,A,Mid],[T,A],[T,A,Mid],[In,_1,Off,Offsets,_3,Mid,Word],[In,_1,Off,Offsets,_3,Mid,Word,_4],[In,_1,Off,Offsets,_3,Mid,_4],[In,_1,Off,_3,Mid,Word],[In,_1,Off,_3,Mid,Word,_4],[In,_1,Off,_3,Mid,_4],[In,_1,Offsets,_3,Mid,_4],[In,_1,_3,Mid,_4],[In,Off,Offsets,Mid],[In,Off,Mid],[In,Offsets,Mid],[In,Mid],[Out],[_1,Off,Offsets,_3,Word],[_1,Off,Offsets,_3,Word,_4],[_1,Off,Offsets,_3,_4],[_1,Off,_3,Word],[_1,Off,_3,Word,_4],[_1,Off,_3,_4],[_1,Offsets,_3,_4],[_1,_3,_4],[_2],[Off],[Off,Offsets],[Offsets]]),ground([I,N,S,S1,I1]);mshare([[T,In,_1,Off,Offsets,A,_3,Mid,Word],[T,In,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,In,_1,Off,A,_3,Mid,Word],[T,In,_1,Off,A,_3,Mid,Word,_4],[T,In,_1,A,_3,Mid,Word],[T,In,_1,A,_3,Mid,Word,_4],[T,In,_1,A,_3,Mid,_4],[T,In,_1,A,Mid],[T,In,A,Mid],[T,_1,Off,Offsets,A,_3,Mid,Word],[T,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,_1,Off,Offsets,A,_3,Word],[T,_1,Off,Offsets,A,_3,Word,_4],[T,_1,Off,A,_3,Mid,Word],[T,_1,Off,A,_3,Mid,Word,_4],[T,_1,Off,A,_3,Word],[T,_1,Off,A,_3,Word,_4],[T,_1,A],[T,_1,A,_3,Mid,Word],[T,_1,A,_3,Mid,Word,_4],[T,_1,A,_3,Mid,_4],[T,_1,A,_3,Word],[T,_1,A,_3,Word,_4],[T,_1,A,_3,_4],[T,_1,A,Mid],[T,A],[T,A,Mid],[In,_1,Off,Offsets,_3,Mid,Word],[In,_1,Off,Offsets,_3,Mid,Word,_4],[In,_1,Off,_3,Mid,Word],[In,_1,Off,_3,Mid,Word,_4],[In,_1,_3,Mid,_4],[In,Mid],[Out],[_1,Off,Offsets,_3,Word],[_1,Off,Offsets,_3,Word,_4],[_1,Off,_3,Word],[_1,Off,_3,Word,_4],[_1,_3,_4],[_2],[Off],[Off,Offsets],[Offsets]]),ground([I,N,S,S1,I1]))),
    make_slots(I1,N,T,S1,Offsets,Mid,Out,_4,_2),
    true((mshare([[T,In,Out,_1,_2,Off,Offsets,A,_3,Mid,Word,_4],[T,In,Out,_1,_2,Off,Offsets,A,_3,Mid,_4],[T,In,Out,_1,_2,Off,A,_3,Mid,Word,_4],[T,In,Out,_1,_2,Off,A,_3,Mid,_4],[T,In,Out,_1,_2,Offsets,A,_3,Mid,Word,_4],[T,In,Out,_1,_2,Offsets,A,_3,Mid,_4],[T,In,Out,_1,_2,A,_3,Mid,Word,_4],[T,In,Out,_1,_2,A,_3,Mid,_4],[T,In,Out,_1,Off,Offsets,A,_3,Mid,Word],[T,In,Out,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,In,Out,_1,Off,Offsets,A,_3,Mid,_4],[T,In,Out,_1,Off,Offsets,A,Mid],[T,In,Out,_1,Off,A,_3,Mid,Word],[T,In,Out,_1,Off,A,_3,Mid,Word,_4],[T,In,Out,_1,Off,A,_3,Mid,_4],[T,In,Out,_1,Off,A,Mid],[T,In,Out,_1,Offsets,A,_3,Mid,Word],[T,In,Out,_1,Offsets,A,_3,Mid,Word,_4],[T,In,Out,_1,Offsets,A,_3,Mid,_4],[T,In,Out,_1,Offsets,A,Mid],[T,In,Out,_1,A,_3,Mid,Word],[T,In,Out,_1,A,_3,Mid,Word,_4],[T,In,Out,_1,A,_3,Mid,_4],[T,In,Out,_1,A,Mid],[T,In,Out,Off,Offsets,A,Mid],[T,In,Out,Off,A,Mid],[T,In,Out,Offsets,A,Mid],[T,In,Out,A,Mid],[T,Out,_1,_2,Off,Offsets,A,_3,Mid,Word,_4],[T,Out,_1,_2,Off,Offsets,A,_3,Mid,_4],[T,Out,_1,_2,Off,Offsets,A,_3,Word,_4],[T,Out,_1,_2,Off,Offsets,A,_3,_4],[T,Out,_1,_2,Off,A,_3,Mid,Word,_4],[T,Out,_1,_2,Off,A,_3,Mid,_4],[T,Out,_1,_2,Off,A,_3,Word,_4],[T,Out,_1,_2,Off,A,_3,_4],[T,Out,_1,_2,Offsets,A,_3,Mid,Word,_4],[T,Out,_1,_2,Offsets,A,_3,Mid,_4],[T,Out,_1,_2,Offsets,A,_3,Word,_4],[T,Out,_1,_2,Offsets,A,_3,_4],[T,Out,_1,_2,A,_3,Mid,Word,_4],[T,Out,_1,_2,A,_3,Mid,_4],[T,Out,_1,_2,A,_3,Word,_4],[T,Out,_1,_2,A,_3,_4],[T,Out,_1,Off,Offsets,A],[T,Out,_1,Off,Offsets,A,_3,Mid,Word],[T,Out,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,Out,_1,Off,Offsets,A,_3,Mid,_4],[T,Out,_1,Off,Offsets,A,_3,Word],[T,Out,_1,Off,Offsets,A,_3,Word,_4],[T,Out,_1,Off,Offsets,A,_3,_4],[T,Out,_1,Off,Offsets,A,Mid],[T,Out,_1,Off,A],[T,Out,_1,Off,A,_3,Mid,Word],[T,Out,_1,Off,A,_3,Mid,Word,_4],[T,Out,_1,Off,A,_3,Mid,_4],[T,Out,_1,Off,A,_3,Word],[T,Out,_1,Off,A,_3,Word,_4],[T,Out,_1,Off,A,_3,_4],[T,Out,_1,Off,A,Mid],[T,Out,_1,Offsets,A],[T,Out,_1,Offsets,A,_3,Mid,Word],[T,Out,_1,Offsets,A,_3,Mid,Word,_4],[T,Out,_1,Offsets,A,_3,Mid,_4],[T,Out,_1,Offsets,A,_3,Word],[T,Out,_1,Offsets,A,_3,Word,_4],[T,Out,_1,Offsets,A,_3,_4],[T,Out,_1,Offsets,A,Mid],[T,Out,_1,A],[T,Out,_1,A,_3,Mid,Word],[T,Out,_1,A,_3,Mid,Word,_4],[T,Out,_1,A,_3,Mid,_4],[T,Out,_1,A,_3,Word],[T,Out,_1,A,_3,Word,_4],[T,Out,_1,A,_3,_4],[T,Out,_1,A,Mid],[T,Out,Off,Offsets,A],[T,Out,Off,Offsets,A,Mid],[T,Out,Off,A],[T,Out,Off,A,Mid],[T,Out,Offsets,A],[T,Out,Offsets,A,Mid],[T,Out,A],[T,Out,A,Mid],[T,_1,_2,Off,Offsets,A,_3,Word,_4],[T,_1,_2,Off,Offsets,A,_3,_4],[T,_1,_2,Off,A,_3,Word,_4],[T,_1,_2,Off,A,_3,_4],[T,_1,_2,Offsets,A,_3,Word,_4],[T,_1,_2,Offsets,A,_3,_4],[T,_1,_2,A,_3,Word,_4],[T,_1,_2,A,_3,_4],[T,_1,Off,Offsets,A],[T,_1,Off,Offsets,A,_3,Word],[T,_1,Off,Offsets,A,_3,Word,_4],[T,_1,Off,Offsets,A,_3,_4],[T,_1,Off,A],[T,_1,Off,A,_3,Word],[T,_1,Off,A,_3,Word,_4],[T,_1,Off,A,_3,_4],[T,_1,Offsets,A],[T,_1,Offsets,A,_3,Word],[T,_1,Offsets,A,_3,Word,_4],[T,_1,Offsets,A,_3,_4],[T,_1,A],[T,_1,A,_3,Word],[T,_1,A,_3,Word,_4],[T,_1,A,_3,_4],[T,Off,Offsets,A],[T,Off,A],[T,Offsets,A],[T,A],[In,Out,_1,_2,Off,Offsets,_3,Mid,Word,_4],[In,Out,_1,_2,Off,Offsets,_3,Mid,_4],[In,Out,_1,_2,Off,_3,Mid,Word,_4],[In,Out,_1,_2,Off,_3,Mid,_4],[In,Out,_1,_2,Offsets,_3,Mid,_4],[In,Out,_1,_2,_3,Mid,_4],[In,Out,_1,Off,Offsets,_3,Mid,Word],[In,Out,_1,Off,Offsets,_3,Mid,Word,_4],[In,Out,_1,Off,Offsets,_3,Mid,_4],[In,Out,_1,Off,_3,Mid,Word],[In,Out,_1,Offsets,_3,Mid,_4],[In,Out,Off,Offsets,Mid],[In,Out,Off,Mid],[In,Out,Offsets,Mid],[In,Out,Mid],[_1,_2,Off,Offsets,_3,Word,_4],[_1,_2,Off,Offsets,_3,_4],[_1,_2,Off,_3,Word,_4],[_1,_2,Off,_3,_4],[_1,_2,Offsets,_3,_4],[_1,_2,_3,_4],[_1,Off,Offsets,_3,Word],[_1,Off,Offsets,_3,Word,_4],[_1,Off,Offsets,_3,_4],[_1,Off,_3,Word],[_1,Offsets,_3,_4],[Off],[Off,Offsets],[Offsets]]),ground([I,N,S,S1,I1]);mshare([[T,In,Out,_1,_2,Off,Offsets,A,_3,Mid,Word,_4],[T,In,Out,_1,_2,Off,Offsets,A,_3,Mid,_4],[T,In,Out,_1,_2,Off,A,_3,Mid,Word,_4],[T,In,Out,_1,_2,Offsets,A,_3,Mid,Word,_4],[T,In,Out,_1,_2,Offsets,A,_3,Mid,_4],[T,In,Out,_1,_2,A,_3,Mid,Word,_4],[T,In,Out,_1,_2,A,_3,Mid,_4],[T,In,Out,_1,Off,Offsets,A,_3,Mid,Word],[T,In,Out,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,In,Out,_1,Off,Offsets,A,_3,Mid,_4],[T,In,Out,_1,Off,Offsets,A,Mid],[T,In,Out,_1,Off,A,_3,Mid,Word],[T,In,Out,_1,Off,A,_3,Mid,Word,_4],[T,In,Out,_1,Offsets,A,_3,Mid,Word],[T,In,Out,_1,Offsets,A,_3,Mid,Word,_4],[T,In,Out,_1,Offsets,A,_3,Mid,_4],[T,In,Out,_1,Offsets,A,Mid],[T,In,Out,_1,A,_3,Mid,Word],[T,In,Out,_1,A,_3,Mid,Word,_4],[T,In,Out,_1,A,_3,Mid,_4],[T,In,Out,_1,A,Mid],[T,In,Out,Off,Offsets,A,Mid],[T,In,Out,Offsets,A,Mid],[T,In,Out,A,Mid],[T,Out,_1,_2,Off,Offsets,A,_3,Mid,Word,_4],[T,Out,_1,_2,Off,Offsets,A,_3,Mid,_4],[T,Out,_1,_2,Off,Offsets,A,_3,Word,_4],[T,Out,_1,_2,Off,Offsets,A,_3,_4],[T,Out,_1,_2,Off,A,_3,Mid,Word,_4],[T,Out,_1,_2,Off,A,_3,Word,_4],[T,Out,_1,_2,Offsets,A,_3,Mid,Word,_4],[T,Out,_1,_2,Offsets,A,_3,Mid,_4],[T,Out,_1,_2,Offsets,A,_3,Word,_4],[T,Out,_1,_2,Offsets,A,_3,_4],[T,Out,_1,_2,A,_3,Mid,Word,_4],[T,Out,_1,_2,A,_3,Mid,_4],[T,Out,_1,_2,A,_3,Word,_4],[T,Out,_1,_2,A,_3,_4],[T,Out,_1,Off,Offsets,A],[T,Out,_1,Off,Offsets,A,_3,Mid,Word],[T,Out,_1,Off,Offsets,A,_3,Mid,Word,_4],[T,Out,_1,Off,Offsets,A,_3,Mid,_4],[T,Out,_1,Off,Offsets,A,_3,Word],[T,Out,_1,Off,Offsets,A,_3,Word,_4],[T,Out,_1,Off,Offsets,A,_3,_4],[T,Out,_1,Off,Offsets,A,Mid],[T,Out,_1,Off,A,_3,Mid,Word],[T,Out,_1,Off,A,_3,Mid,Word,_4],[T,Out,_1,Off,A,_3,Word],[T,Out,_1,Off,A,_3,Word,_4],[T,Out,_1,Offsets,A],[T,Out,_1,Offsets,A,_3,Mid,Word],[T,Out,_1,Offsets,A,_3,Mid,Word,_4],[T,Out,_1,Offsets,A,_3,Mid,_4],[T,Out,_1,Offsets,A,_3,Word],[T,Out,_1,Offsets,A,_3,Word,_4],[T,Out,_1,Offsets,A,_3,_4],[T,Out,_1,Offsets,A,Mid],[T,Out,_1,A],[T,Out,_1,A,_3,Mid,Word],[T,Out,_1,A,_3,Mid,Word,_4],[T,Out,_1,A,_3,Mid,_4],[T,Out,_1,A,_3,Word],[T,Out,_1,A,_3,Word,_4],[T,Out,_1,A,_3,_4],[T,Out,_1,A,Mid],[T,Out,Off,Offsets,A],[T,Out,Off,Offsets,A,Mid],[T,Out,Offsets,A],[T,Out,Offsets,A,Mid],[T,Out,A],[T,Out,A,Mid],[T,_1,_2,Off,Offsets,A,_3,Word,_4],[T,_1,_2,Off,Offsets,A,_3,_4],[T,_1,_2,Off,A,_3,Word,_4],[T,_1,_2,Offsets,A,_3,Word,_4],[T,_1,_2,Offsets,A,_3,_4],[T,_1,_2,A,_3,Word,_4],[T,_1,_2,A,_3,_4],[T,_1,Off,Offsets,A],[T,_1,Off,Offsets,A,_3,Word],[T,_1,Off,Offsets,A,_3,Word,_4],[T,_1,Off,Offsets,A,_3,_4],[T,_1,Off,A,_3,Word],[T,_1,Off,A,_3,Word,_4],[T,_1,Offsets,A],[T,_1,Offsets,A,_3,Word],[T,_1,Offsets,A,_3,Word,_4],[T,_1,Offsets,A,_3,_4],[T,_1,A],[T,_1,A,_3,Word],[T,_1,A,_3,Word,_4],[T,_1,A,_3,_4],[T,Off,Offsets,A],[T,Offsets,A],[T,A],[In,Out,_1,_2,Off,Offsets,_3,Mid,Word,_4],[In,Out,_1,_2,Off,Offsets,_3,Mid,_4],[In,Out,_1,_2,Off,_3,Mid,Word,_4],[In,Out,_1,_2,Offsets,_3,Mid,_4],[In,Out,_1,_2,_3,Mid,_4],[In,Out,_1,Off,Offsets,_3,Mid,Word],[In,Out,_1,Off,Offsets,_3,Mid,Word,_4],[In,Out,_1,Off,Offsets,_3,Mid,_4],[In,Out,_1,Off,_3,Mid,Word],[In,Out,_1,Offsets,_3,Mid,_4],[In,Out,Off,Offsets,Mid],[In,Out,Offsets,Mid],[In,Out,Mid],[_1,_2,Off,Offsets,_3,Word,_4],[_1,_2,Off,Offsets,_3,_4],[_1,_2,Off,_3,Word,_4],[_1,_2,Offsets,_3,_4],[_1,_2,_3,_4],[_1,Off,Offsets,_3,Word],[_1,Off,Offsets,_3,Word,_4],[_1,Off,Offsets,_3,_4],[_1,Off,_3,Word],[_1,Offsets,_3,_4],[Off],[Off,Offsets],[Offsets]]),ground([I,N,S,S1,I1]))).

:- true pred init_var(V,I,In,_1,_2)
   : ( mshare([[V],[In],[In,_1],[_1],[_2]]),
       ground([I]) )
   => ( mshare([[V],[V,In,_1],[V,In,_1,_2],[V,_1],[V,_1,_2],[In],[In,_1,_2],[_1,_2]]),
        ground([I]) ).

:- true pred init_var(V,I,In,_1,_2)
   : ( mshare([[V],[V,In],[V,In,_1],[V,_1],[In],[In,_1],[_1],[_2]]),
       ground([I]) )
   => ( mshare([[V],[V,In],[V,In,_1],[V,In,_1,_2],[V,_1],[V,_1,_2],[In],[In,_1,_2],[_1,_2]]),
        ground([I]) ).

init_var(V,I,In,_1,_2) :-
    true((mshare([[V],[V,In],[V,In,_1],[V,_1],[In],[In,_1],[_1],[_2]]),ground([I]);mshare([[V],[In],[In,_1],[_1],[_2]]),ground([I]))),
    var(V),
    true((mshare([[V],[V,In],[V,In,_1],[V,_1],[In],[In,_1],[_1],[_2]]),ground([I]);mshare([[V],[In],[In,_1],[_1],[_2]]),ground([I]))),
    'init_var/5/1/$disj/1'(V,In),
    !,
    true((mshare([[V],[V,In],[V,In,_1],[V,_1],[In],[In,_1],[_1],[_2]]),ground([I]);mshare([[V],[In],[In,_1],[_1],[_2]]),ground([I]))),
    'C'(_1,move(tvar^(h+I),V),_2),
    true((
        mshare([[V,In,_1],[V,In,_1,_2],[V,_1],[V,_1,_2],[In],[In,_1,_2],[_1,_2]]),
        ground([I])
    )).
init_var(V,_1,In,_2,_3) :-
    true((mshare([[V],[V,In],[V,In,_2],[V,_2],[In],[In,_2],[_2],[_3]]),ground([_1]);mshare([[V],[In],[In,_2],[_2],[_3]]),ground([_1]))),
    var(V),
    true((mshare([[V],[V,In],[V,In,_2],[V,_2],[In],[In,_2],[_2],[_3]]),ground([_1]);mshare([[V],[In],[In,_2],[_2],[_3]]),ground([_1]))),
    myin(V,In),
    !,
    true((mshare([[V],[V,In],[V,In,_2],[V,_2],[In],[In,_2],[_2],[_3]]),ground([_1]);mshare([[V],[In],[In,_2],[_2],[_3]]),ground([_1]))),
    _3=_2,
    true((mshare([[V],[V,In],[V,In,_2,_3],[V,_2,_3],[In],[In,_2,_3],[_2,_3]]),ground([_1]);mshare([[V],[In],[In,_2,_3],[_2,_3]]),ground([_1]))).
init_var(V,_1,_2,_3,_4) :-
    true((mshare([[V],[V,_2],[V,_2,_3],[V,_3],[_2],[_2,_3],[_3],[_4]]),ground([_1]);mshare([[V],[_2],[_2,_3],[_3],[_4]]),ground([_1]))),
    nonvar(V),
    !,
    true((mshare([[V],[V,_2],[V,_2,_3],[V,_3],[_2],[_2,_3],[_3],[_4]]),ground([_1]);mshare([[V],[_2],[_2,_3],[_3],[_4]]),ground([_1]))),
    _4=_3,
    true((mshare([[V],[V,_2],[V,_2,_3,_4],[V,_3,_4],[_2],[_2,_3,_4],[_3,_4]]),ground([_1]);mshare([[V],[_2],[_2,_3,_4],[_3,_4]]),ground([_1]))).

:- true pred 'init_var/5/1/$disj/1'(V,In)
   : mshare([[V],[V,In],[In]])
   => mshare([[V],[V,In],[In]]).

:- true pred 'init_var/5/1/$disj/1'(V,In)
   : mshare([[V],[In]])
   => mshare([[V],[In]]).

'init_var/5/1/$disj/1'(V,In) :-
    true((mshare([[V],[V,In],[In]]);mshare([[V],[In]]))),
    myin(V,In),
    !,
    true((mshare([[V],[V,In],[In]]);mshare([[V],[In]]))),
    fail,
    true(fails(_)).
'init_var/5/1/$disj/1'(V,In).

:- true pred make_word(C,Off,V)
   : mshare([[C],[Off],[V]])
   => mshare([[C],[C,V],[Off],[Off,V]]).

:- true pred make_word(C,Off,V)
   : mshare([[C],[C,Off],[Off],[V]])
   => mshare([[C],[C,Off,V],[C,V],[Off],[Off,V]]).

make_word(C,Off,Tag^(h+Off)) :-
    true((mshare([[C],[C,Off],[C,Off,Tag],[Off],[Off,Tag],[Tag]]);mshare([[C],[Off],[Off,Tag],[Tag]]))),
    my_compound(C),
    !,
    true((mshare([[C],[C,Off],[C,Off,Tag],[Off],[Off,Tag],[Tag]]);mshare([[C],[Off],[Off,Tag],[Tag]]))),
    termtag(C,Tag),
    true((mshare([[C],[C,Off],[Off]]),ground([Tag]);mshare([[C],[Off]]),ground([Tag]))).
make_word(V,_1,V) :-
    true((mshare([[V],[V,_1],[_1]]);mshare([[V],[_1]]))),
    var(V),
    !,
    true((mshare([[V],[V,_1],[_1]]);mshare([[V],[_1]]))).
make_word(A,_1,tatm^A) :-
    true((mshare([[A],[A,_1],[_1]]);mshare([[A],[_1]]))),
    atomic(A),
    !,
    true((
        mshare([[_1]]),
        ground([A])
    )).

:- true pred size(T,_1,_2)
   : ( (_1=0),
       mshare([[T],[_2]]) )
   => ( mshare([[T]]),
        ground([_2]) ).

:- true pred size(T,_1,_2)
   : ( (_1=0),
       mshare([[T],[T,_2],[_2]]) )
   => ( mshare([[T]]),
        ground([_2]) ).

:- true pred size(T,_1,_2)
   : ( mshare([[T],[_2]]),
       ground([_1]) )
   => ( mshare([[T]]),
        ground([_1,_2]) ).

size(T,_1,_2) :-
    true((mshare([[T],[T,_2],[_2],[_3],[N],[_4],[_5]]),ground([_1]);mshare([[T],[_2],[_3],[N],[_4],[_5]]),ground([_1]))),
    structure(T),
    !,
    true((mshare([[T],[T,_2],[_2],[_3],[N],[_4],[_5]]),ground([_1]);mshare([[T],[_2],[_3],[N],[_4],[_5]]),ground([_1]))),
    functor(T,_3,N),
    true((mshare([[T],[T,_2],[_2],[_4],[_5]]),ground([_1,_3,N]);mshare([[T],[_2],[_4],[_5]]),ground([_1,_3,N]))),
    add(1,_1,_4),
    true((mshare([[T],[T,_2],[_2],[_5]]),ground([_1,_3,N,_4]);mshare([[T],[_2],[_5]]),ground([_1,_3,N,_4]))),
    add(N,_4,_5),
    true((mshare([[T],[T,_2],[_2]]),ground([_1,_3,N,_4,_5]);mshare([[T],[_2]]),ground([_1,_3,N,_4,_5]))),
    size_args(1,N,T,_5,_2),
    true((
        mshare([[T]]),
        ground([_1,_2,_3,N,_4,_5])
    )).
size(T,_1,_2) :-
    true((mshare([[T],[T,_2],[_2],[_3]]),ground([_1]);mshare([[T],[_2],[_3]]),ground([_1]))),
    cons(T),
    !,
    true((mshare([[T],[T,_2],[_2],[_3]]),ground([_1]);mshare([[T],[_2],[_3]]),ground([_1]))),
    add(2,_1,_3),
    true((mshare([[T],[T,_2],[_2]]),ground([_1,_3]);mshare([[T],[_2]]),ground([_1,_3]))),
    size_args(1,2,T,_3,_2),
    true((
        mshare([[T]]),
        ground([_1,_2,_3])
    )).
size(T,_1,_2) :-
    true((mshare([[T],[T,_2],[_2]]),ground([_1]);mshare([[T],[_2]]),ground([_1]))),
    atomic(T),
    !,
    true((
        mshare([[_2]]),
        ground([T,_1])
    )),
    _2=_1,
    true(ground([T,_1,_2])).
size(T,_1,_2) :-
    true((mshare([[T],[T,_2],[_2]]),ground([_1]);mshare([[T],[_2]]),ground([_1]))),
    var(T),
    !,
    true((mshare([[T],[T,_2],[_2]]),ground([_1]);mshare([[T],[_2]]),ground([_1]))),
    _2=_1,
    true((
        mshare([[T]]),
        ground([_1,_2])
    )).

:- true pred size_args(I,N,_1,_2,_3)
   : ( mshare([[_1],[_3]]),
       ground([I,N,_2]) )
   => ( mshare([[_1]]),
        ground([I,N,_2,_3]) ).

:- true pred size_args(I,N,_1,_2,_3)
   : ( (I=1), (N=2),
       mshare([[_1],[_3]]),
       ground([_2]) )
   => ( mshare([[_1]]),
        ground([_2,_3]) ).

:- true pred size_args(I,N,_1,_2,_3)
   : ( (I=1), (N=2),
       mshare([[_1],[_1,_3],[_3]]),
       ground([_2]) )
   => ( mshare([[_1]]),
        ground([_2,_3]) ).

:- true pred size_args(I,N,_1,_2,_3)
   : ( mshare([[_1],[_1,_3],[_3]]),
       ground([I,N,_2]) )
   => ( mshare([[_1]]),
        ground([I,N,_2,_3]) ).

:- true pred size_args(I,N,_1,_2,_3)
   : ( (I=1),
       mshare([[_1],[_1,_3],[_3]]),
       ground([N,_2]) )
   => ( mshare([[_1]]),
        ground([N,_2,_3]) ).

:- true pred size_args(I,N,_1,_2,_3)
   : ( (I=1),
       mshare([[_1],[_3]]),
       ground([N,_2]) )
   => ( mshare([[_1]]),
        ground([N,_2,_3]) ).

size_args(I,N,_1,_2,_3) :-
    true((mshare([[_1],[_1,_3],[_3]]),ground([I,N,_2]);mshare([[_1],[_3]]),ground([I,N,_2]))),
    I>N,
    !,
    true((mshare([[_1],[_1,_3],[_3]]),ground([I,N,_2]);mshare([[_1],[_3]]),ground([I,N,_2]))),
    _3=_2,
    true((
        mshare([[_1]]),
        ground([I,N,_2,_3])
    )).
size_args(I,N,T,_1,_2) :-
    true((mshare([[T],[T,_2],[_2],[A],[_3],[I1]]),ground([I,N,_1]);mshare([[T],[_2],[A],[_3],[I1]]),ground([I,N,_1]))),
    I=<N,
    !,
    true((mshare([[T],[T,_2],[_2],[A],[_3],[I1]]),ground([I,N,_1]);mshare([[T],[_2],[A],[_3],[I1]]),ground([I,N,_1]))),
    arg(I,T,A),
    true((mshare([[T,_2,A],[T,A],[_2],[_3],[I1]]),ground([I,N,_1]);mshare([[T,A],[_2],[_3],[I1]]),ground([I,N,_1]))),
    unify:size(A,_1,_3),
    true((mshare([[T,_2,A],[T,A],[_2],[I1]]),ground([I,N,_1,_3]);mshare([[T,A],[_2],[I1]]),ground([I,N,_1,_3]))),
    I1 is I+1,
    true((mshare([[T,_2,A],[T,A],[_2]]),ground([I,N,_1,_3,I1]);mshare([[T,A],[_2]]),ground([I,N,_1,_3,I1]))),
    size_args(I1,N,T,_3,_2),
    true((
        mshare([[T,A]]),
        ground([I,N,_1,_2,_3,I1])
    )).

:- true pred add(I,X,Y)
   : ( (I=2),
       mshare([[Y]]),
       ground([X]) )
   => ground([X,Y]).

:- true pred add(I,X,Y)
   : ( mshare([[Y]]),
       ground([I,X]) )
   => ground([I,X,Y]).

:- true pred add(I,X,Y)
   : ( (I=1),
       mshare([[Y]]),
       ground([X]) )
   => ground([X,Y]).

add(I,X,Y) :-
    true((
        mshare([[Y]]),
        ground([I,X])
    )),
    Y is X+I,
    true(ground([I,X,Y])).

:- true pred myin(A,_A)
   : mshare([[A],[A,_A]])
   => mshare([[A],[A,_A]]).

:- true pred myin(A,_A)
   : mshare([[A],[A,_A],[_A]])
   => mshare([[A],[A,_A],[_A]]).

:- true pred myin(A,_A)
   : mshare([[A,_A]])
   => mshare([[A,_A]]).

:- true pred myin(A,_A)
   : mshare([[A],[_A]])
   => mshare([[A],[_A]]).

myin(A,[B|S]) :-
    true((mshare([[A],[A,B],[A,B,S],[A,S],[B],[B,S],[S],[Order]]);mshare([[A],[A,B],[A,B,S],[A,S],[Order]]);mshare([[A],[B],[B,S],[S],[Order]]);mshare([[A,B],[A,B,S],[A,S],[Order]]))),
    compare(Order,A,B),
    true((mshare([[A],[A,B],[A,B,S],[A,S]]),ground([Order]);mshare([[A],[A,B],[A,B,S],[A,S],[B],[B,S],[S]]),ground([Order]);mshare([[A],[B],[B,S],[S]]),ground([Order]);mshare([[A,B],[A,B,S],[A,S]]),ground([Order]))),
    in_2(Order,A,S),
    true((mshare([[A],[A,B],[A,B,S],[A,S]]),ground([Order]);mshare([[A],[A,B],[A,B,S],[A,S],[B],[B,S],[S]]),ground([Order]);mshare([[A],[B],[B,S],[S]]),ground([Order]);mshare([[A,B],[A,B,S],[A,S]]),ground([Order]))).

:- true pred in_2(_A,_1,_2)
   : ( mshare([[_1],[_2]]),
       ground([_A]) )
   => ( mshare([[_1],[_2]]),
        ground([_A]) ).

:- true pred in_2(_A,_1,_2)
   : ( mshare([[_1],[_1,_2],[_2]]),
       ground([_A]) )
   => ( mshare([[_1],[_1,_2],[_2]]),
        ground([_A]) ).

:- true pred in_2(_A,_1,_2)
   : ( mshare([[_1],[_1,_2]]),
       ground([_A]) )
   => ( mshare([[_1],[_1,_2]]),
        ground([_A]) ).

in_2(=,_1,_2).
in_2(>,A,S) :-
    true((mshare([[A],[A,S]]);mshare([[A],[A,S],[S]]);mshare([[A],[S]]))),
    myin(A,S),
    true((mshare([[A],[A,S]]);mshare([[A],[A,S],[S]]);mshare([[A],[S]]))).

:- true pred incl(A,S1,S)
   : mshare([[A],[A,S1],[S1],[S]])
   => mshare([[A],[A,S1,S],[A,S],[S1,S]]).

:- true pred incl(A,S1,S)
   : mshare([[A,S1],[S]])
   => mshare([[A,S1,S]]).

:- true pred incl(A,S1,S)
   : mshare([[A,S1],[S1],[S]])
   => mshare([[A,S1,S],[S1,S]]).

incl(A,S1,S) :-
    true((mshare([[A],[A,S1],[S1],[S]]);mshare([[A,S1],[S1],[S]]);mshare([[A,S1],[S]]))),
    incl_2(S1,A,S),
    true((mshare([[A],[A,S1,S],[A,S],[S1,S]]);mshare([[A,S1,S]]);mshare([[A,S1,S],[S1,S]]))).

:- true pred incl_2(_A,A,S)
   : mshare([[_A,A],[S]])
   => mshare([[_A,A,S]]).

:- true pred incl_2(_A,A,S)
   : mshare([[_A,A],[_A,A,S],[A],[A,S],[S]])
   => mshare([[_A,A,S],[A],[A,S]]).

:- true pred incl_2(_A,A,S)
   : mshare([[_A],[_A,A],[S]])
   => mshare([[_A,A,S],[_A,S]]).

:- true pred incl_2(_A,A,S)
   : mshare([[_A],[_A,A],[_A,A,S],[_A,S],[A],[A,S],[S]])
   => mshare([[_A,A,S],[_A,S],[A],[A,S]]).

:- true pred incl_2(_A,A,S)
   : mshare([[_A],[_A,A],[A],[S]])
   => mshare([[_A,A,S],[_A,S],[A],[A,S]]).

incl_2([],A,[A]).
incl_2([B|S1],A,S) :-
    true((mshare([[A],[A,S],[A,S,B],[A,S,B,S1],[A,S,S1],[A,B],[A,B,S1],[A,S1],[S],[S,B],[S,B,S1],[S,S1],[B],[B,S1],[S1],[Order]]);mshare([[A],[A,S],[A,S,B],[A,S,B,S1],[A,S,S1],[A,B],[A,B,S1],[A,S1],[S],[Order]]);mshare([[A],[A,B],[A,B,S1],[A,S1],[S],[B],[B,S1],[S1],[Order]]);mshare([[A,B],[A,B,S1],[A,S1],[S],[B],[B,S1],[S1],[Order]]);mshare([[A,B],[A,B,S1],[A,S1],[S],[Order]]))),
    compare(Order,A,B),
    true((mshare([[A],[A,S],[A,S,B],[A,S,B,S1],[A,S,S1],[A,B],[A,B,S1],[A,S1],[S]]),ground([Order]);mshare([[A],[A,S],[A,S,B],[A,S,B,S1],[A,S,S1],[A,B],[A,B,S1],[A,S1],[S],[S,B],[S,B,S1],[S,S1],[B],[B,S1],[S1]]),ground([Order]);mshare([[A],[A,B],[A,B,S1],[A,S1],[S],[B],[B,S1],[S1]]),ground([Order]);mshare([[A,B],[A,B,S1],[A,S1],[S]]),ground([Order]);mshare([[A,B],[A,B,S1],[A,S1],[S],[B],[B,S1],[S1]]),ground([Order]))),
    incl_3(Order,A,B,S1,S),
    true((mshare([[A],[A,S],[A,S,B],[A,S,B,S1],[A,S,S1]]),ground([Order]);mshare([[A],[A,S],[A,S,B],[A,S,B,S1],[A,S,S1],[S,B],[S,B,S1],[S,S1]]),ground([Order]);mshare([[A,S,B],[A,S,B,S1],[A,S,S1]]),ground([Order]);mshare([[A,S,B],[A,S,B,S1],[A,S,S1],[S,B],[S,B,S1],[S,S1]]),ground([Order]))).

:- true pred incl_3(_A,A,B,S1,_B)
   : ( mshare([[A],[A,B],[A,B,S1],[A,B,S1,_B],[A,B,_B],[A,S1],[A,S1,_B],[A,_B],[B],[B,S1],[B,S1,_B],[B,_B],[S1],[S1,_B],[_B]]),
       ground([_A]) )
   => ( mshare([[A],[A,B,S1,_B],[A,B,_B],[A,S1,_B],[A,_B],[B,S1,_B],[B,_B],[S1,_B]]),
        ground([_A]) ).

:- true pred incl_3(_A,A,B,S1,_B)
   : ( mshare([[A],[A,B],[A,B,S1],[A,B,S1,_B],[A,B,_B],[A,S1],[A,S1,_B],[A,_B],[_B]]),
       ground([_A]) )
   => ( mshare([[A],[A,B,S1,_B],[A,B,_B],[A,S1,_B],[A,_B]]),
        ground([_A]) ).

:- true pred incl_3(_A,A,B,S1,_B)
   : ( mshare([[A,B],[A,B,S1],[A,S1],[_B]]),
       ground([_A]) )
   => ( mshare([[A,B,S1,_B],[A,B,_B],[A,S1,_B]]),
        ground([_A]) ).

:- true pred incl_3(_A,A,B,S1,_B)
   : ( mshare([[A,B],[A,B,S1],[A,S1],[B],[B,S1],[S1],[_B]]),
       ground([_A]) )
   => ( mshare([[A,B,S1,_B],[A,B,_B],[A,S1,_B],[B,S1,_B],[B,_B],[S1,_B]]),
        ground([_A]) ).

:- true pred incl_3(_A,A,B,S1,_B)
   : ( mshare([[A],[A,B],[A,B,S1],[A,S1],[B],[B,S1],[S1],[_B]]),
       ground([_A]) )
   => ( mshare([[A],[A,B,S1,_B],[A,B,_B],[A,S1,_B],[A,_B],[B,S1,_B],[B,_B],[S1,_B]]),
        ground([_A]) ).

incl_3(<,A,B,S1,[A,B|S1]).
incl_3(=,_1,B,S1,[B|S1]).
incl_3(>,A,B,S1,[B|S]) :-
    true((mshare([[A],[A,B],[A,B,S1],[A,B,S1,S],[A,B,S],[A,S1],[A,S1,S],[A,S],[B],[B,S1],[B,S1,S],[B,S],[S1],[S1,S],[S]]);mshare([[A],[A,B],[A,B,S1],[A,B,S1,S],[A,B,S],[A,S1],[A,S1,S],[A,S],[S]]);mshare([[A],[A,B],[A,B,S1],[A,B,S1,S],[A,B,S],[A,S1],[B],[B,S1],[B,S1,S],[B,S],[S1],[S]]);mshare([[A,B],[A,B,S1],[A,B,S1,S],[A,B,S],[A,S1],[B],[B,S1],[B,S1,S],[B,S],[S1],[S]]);mshare([[A,B],[A,B,S1],[A,B,S1,S],[A,B,S],[A,S1],[S]]))),
    incl_2(S1,A,S),
    true((mshare([[A],[A,B],[A,B,S1,S],[A,B,S],[A,S1,S],[A,S]]);mshare([[A],[A,B],[A,B,S1,S],[A,B,S],[A,S1,S],[A,S],[B],[B,S1,S],[S1,S]]);mshare([[A,B],[A,B,S1,S],[A,B,S],[A,S1,S]]);mshare([[A,B],[A,B,S1,S],[A,B,S],[A,S1,S],[B],[B,S1,S],[S1,S]]))).

:- true pred my_compound(X)
   : mshare([[X]])
   => mshare([[X]]).

my_compound(X) :-
    true(mshare([[X]])),
    nonvar(X),
    true(mshare([[X]])),
    'my_compound/1/1/$disj/1'(X),
    true(mshare([[X]])).

:- true pred 'my_compound/1/1/$disj/1'(X)
   : mshare([[X]])
   => mshare([[X]]).

'my_compound/1/1/$disj/1'(X) :-
    true(mshare([[X]])),
    atomic(X),
    !,
    true(ground([X])),
    fail,
    true(fails(_)).
'my_compound/1/1/$disj/1'(X).

:- true pred cons(X)
   : mshare([[X]])
   => mshare([[X]]).

cons(X) :-
    true(mshare([[X],[_1],[_2]])),
    nonvar(X),
    true(mshare([[X],[_1],[_2]])),
    X=[_1|_2],
    true(mshare([[X,_1],[X,_1,_2],[X,_2]])).

:- true pred structure(X)
   : mshare([[X]])
   => mshare([[X]]).

structure(X) :-
    true(mshare([[X]])),
    my_compound(X),
    true(mshare([[X]])),
    'structure/1/1/$disj/1'(X),
    true(mshare([[X]])).

:- true pred 'structure/1/1/$disj/1'(X)
   : mshare([[X]])
   => mshare([[X]]).

'structure/1/1/$disj/1'(X) :-
    true(mshare([[X],[_1],[_2]])),
    X=[_1|_2],
    !,
    true(mshare([[X,_1],[X,_1,_2],[X,_2]])),
    fail,
    true(fails(_)).
'structure/1/1/$disj/1'(X).

:- true pred termtag(T,_A)
   : mshare([[T],[_A]])
   => ( mshare([[T]]),
        ground([_A]) ).

:- true pred termtag(T,_A)
   : mshare([[T],[T,_A],[_A]])
   => ( mshare([[T]]),
        ground([_A]) ).

termtag(T,tstr) :-
    true(mshare([[T]])),
    structure(T),
    true(mshare([[T]])).
termtag(T,tlst) :-
    true(mshare([[T]])),
    cons(T),
    true(mshare([[T]])).
termtag(T,tatm) :-
    true(mshare([[T]])),
    atomic(T),
    true(ground([T])).
termtag(T,tvar) :-
    true(mshare([[T]])),
    var(T),
    true(mshare([[T]])).


