:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(chat_parser,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    chat_parser,
    true(true).

go :-
    statistics(runtime,[_1,_2]),
    chat_parser,
    statistics(runtime,[_3,T]),
    write('execution time is '),
    write(T),
    write(milliseconds).

:- true pred chat_parser.

chat_parser :-
    true((
        mshare([[X],[_1]]),
        linear(X),
        linear(_1)
    )),
    my_string(X),
    true((
        mshare([[_1]]),
        ground([X]),
        linear(_1)
    )),
    determinate_say(X,_1),
    true((
        mshare([[_1]]),
        ground([X])
    )),
    fail,
    true(fails(_)).
chat_parser.

:- true pred my_string(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ground([_A]).

my_string([what,rivers,are,there,?]).
my_string([does,afghanistan,border,china,?]).
my_string([what,is,the,capital,of,upper_volta,?]).
my_string([where,is,the,largest,country,?]).
my_string([which,country,~,s,capital,is,london,?]).
my_string([which,countries,are,european,?]).
my_string([how,large,is,the,smallest,american,country,?]).
my_string([what,is,the,ocean,that,borders,african,countries,and,that,borders,asian,countries,?]).
my_string([what,are,the,capitals,of,the,countries,bordering,the,baltic,?]).
my_string([which,countries,are,bordered,by,two,seas,?]).
my_string([how,many,countries,does,the,danube,flow,through,?]).
my_string([what,is,the,total,area,of,countries,south,of,the,equator,and,not,in,australasia,?]).
my_string([what,is,the,average,area,of,the,countries,in,each,continent,?]).
my_string([is,there,more,than,one,country,in,each,continent,?]).
my_string([is,there,some,ocean,that,does,not,border,any,country,?]).
my_string([what,are,the,countries,from,which,a,river,flows,into,the,black_sea,?]).

:- true pred determinate_say(X,Y)
   : ( mshare([[Y]]),
       ground([X]), linear(Y) )
   => ( mshare([[Y]]),
        ground([X]) ).

determinate_say(X,Y) :-
    true((
        mshare([[Y]]),
        ground([X]),
        linear(Y)
    )),
    say(X,Y),
    !,
    true((
        mshare([[Y]]),
        ground([X])
    )).

:- true pred terminal(T,S,_A,_B,X)
   : ( mshare([[T],[_B]]),
       ground([S,_A,X]), linear(T) )
   => ( mshare([[T,_B],[_B]]),
        ground([S,_A,X]) ).

:- true pred terminal(T,S,_A,_B,X)
   : ( mshare([[T],[_A],[X]]),
       ground([S,_B]), linear(T), linear(_A), linear(X) )
   => ground([T,S,_A,_B,X]).

:- true pred terminal(T,S,_A,_B,X)
   : ( mshare([[_A],[_B],[X]]),
       ground([T,S]), linear(_A), linear(X) )
   => ( mshare([[_B],[_B,X]]),
        ground([T,S,_A]) ).

:- true pred terminal(T,S,_A,_B,X)
   : ( mshare([[T],[_A],[_B],[X]]),
       ground([S]), linear(T), linear(_A), linear(X) )
   => ( mshare([[T,_B],[T,_B,X],[_B],[_B,X]]),
        ground([S,_A]) ).

:- true pred terminal(T,S,_A,_B,X)
   : ( mshare([[_A],[X]]),
       ground([T,S,_B]), linear(_A), linear(X) )
   => ground([T,S,_A,_B,X]).

:- true pred terminal(T,S,_A,_B,X)
   : ( mshare([[T],[_A],[_B],[X]]),
       ground([S]), linear(_A), linear(X) )
   => ( mshare([[T,_B],[T,_B,X],[_B],[_B,X]]),
        ground([S,_A]) ).

:- true pred terminal(T,S,_A,_B,X)
   : ( (T=','),
       mshare([[_A],[_B],[X]]),
       ground([S]), linear(_A), linear(X) )
   => ( mshare([[_B],[_B,X]]),
        ground([S,_A]) ).

:- true pred terminal(T,S,_A,_B,X)
   : ( (T=there),
       mshare([[_A],[_B],[X]]),
       ground([S]), linear(_A), linear(X) )
   => ( mshare([[_B],[_B,X]]),
        ground([S,_A]) ).

terminal(T,S,S,x(_1,terminal,T,X),X).
terminal(T,[T|S],S,X,X) :-
    true((mshare([[X]]),ground([T,S]);ground([T,S,X]))),
    gap(X),
    true((mshare([[X]]),ground([T,S]);ground([T,S,X]))).

:- true pred gap(_A)
   : ground([_A])
   => ground([_A]).

:- true pred gap(_A)
   : mshare([[_A]])
   => mshare([[_A]]).

gap(x(gap,_1,_2,_3)).
gap([]).

:- true pred virtual(NT,_A,X)
   : ( (NT=verb_form(_B,_C,_D,_E)),
       mshare([[X],[_B],[_D],[_E]]),
       ground([_A,_C]), linear(X), linear(_B), linear(_D), linear(_E) )
   => ground([_A,X,_B,_C,_D,_E]).

:- true pred virtual(NT,_A,X)
   : ( (NT=np(_B,_C,_D,_E,_F,_G,_H)),
       mshare([[X],[_B],[_C],[_E],[_G],[_H]]),
       ground([_A,_D,_F]), linear(X), linear(_B), linear(_C), linear(_E), linear(_G), linear(_H) )
   => ground([_A,X,_B,_C,_D,_E,_F,_G,_H]).

:- true pred virtual(NT,_A,X)
   : ( (NT=pp(_B,_C,_D,_E)),
       mshare([[X],[_B],[_D],[_E]]),
       ground([_A,_C]), linear(X), linear(_B), linear(_D), linear(_E) )
   => ground([_A,X,_B,_C,_D,_E]).

:- true pred virtual(NT,_A,X)
   : ( (NT=det(_B,_C,_D)),
       mshare([[_A],[_A,_C],[X],[_B]]),
       ground([_D]), linear(X), linear(_B) )
   => ( mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_C],[_A,_B],[_A,_B,_C],[_A,_C]]),
        ground([_D]) ).

:- true pred virtual(NT,_A,X)
   : ( (NT=np(_B,_C,_D,_E,_F,_G,_H)),
       mshare([[_A],[_A,_C],[X],[_B],[_D],[_E],[_H]]),
       ground([_F,_G]), linear(X), linear(_B), linear(_D), linear(_E), linear(_H) )
   => ( mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_B,_C,_D],[_A,X,_B,_C,_D,_E],[_A,X,_B,_C,_D,_E,_H],[_A,X,_B,_C,_D,_H],[_A,X,_B,_C,_E],[_A,X,_B,_C,_E,_H],[_A,X,_B,_C,_H],[_A,X,_B,_D],[_A,X,_B,_D,_E],[_A,X,_B,_D,_E,_H],[_A,X,_B,_D,_H],[_A,X,_B,_E],[_A,X,_B,_E,_H],[_A,X,_B,_H],[_A,X,_C],[_A,X,_C,_D],[_A,X,_C,_D,_E],[_A,X,_C,_D,_E,_H],[_A,X,_C,_D,_H],[_A,X,_C,_E],[_A,X,_C,_E,_H],[_A,X,_C,_H],[_A,X,_D],[_A,X,_D,_E],[_A,X,_D,_E,_H],[_A,X,_D,_H],[_A,X,_E],[_A,X,_E,_H],[_A,X,_H],[_A,_B],[_A,_B,_C],[_A,_B,_C,_D],[_A,_B,_C,_D,_E],[_A,_B,_C,_D,_E,_H],[_A,_B,_C,_D,_H],[_A,_B,_C,_E],[_A,_B,_C,_E,_H],[_A,_B,_C,_H],[_A,_B,_D],[_A,_B,_D,_E],[_A,_B,_D,_E,_H],[_A,_B,_D,_H],[_A,_B,_E],[_A,_B,_E,_H],[_A,_B,_H],[_A,_C],[_A,_C,_D],[_A,_C,_D,_E],[_A,_C,_D,_E,_H],[_A,_C,_D,_H],[_A,_C,_E],[_A,_C,_E,_H],[_A,_C,_H],[_A,_D],[_A,_D,_E],[_A,_D,_E,_H],[_A,_D,_H],[_A,_E],[_A,_E,_H],[_A,_H]]),
        ground([_F,_G]) ).

:- true pred virtual(NT,_A,X)
   : ( (NT=close),
       mshare([[_A],[X]]),
       linear(X) )
   => mshare([[_A],[_A,X]]).

:- true pred virtual(NT,_A,X)
   : ( (NT=predicate(_B,_C,_D)),
       mshare([[_A],[X],[_B],[_C],[_D]]),
       linear(X), linear(_B), linear(_C), linear(_D) )
   => mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_B,_C,_D],[_A,X,_B,_D],[_A,X,_C],[_A,X,_C,_D],[_A,X,_D],[_A,_B],[_A,_B,_C],[_A,_B,_C,_D],[_A,_B,_D],[_A,_C],[_A,_C,_D],[_A,_D]]).

:- true pred virtual(NT,_A,X)
   : ( (NT=verb_form(_B,_C,_D,_E)),
       mshare([[_A],[X],[_B],[_D],[_E]]),
       ground([_C]), linear(X), linear(_B), linear(_D), linear(_E) )
   => ( mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_D],[_A,X,_B,_D,_E],[_A,X,_B,_E],[_A,X,_D],[_A,X,_D,_E],[_A,X,_E],[_A,_B],[_A,_B,_D],[_A,_B,_D,_E],[_A,_B,_E],[_A,_D],[_A,_D,_E],[_A,_E]]),
        ground([_C]) ).

:- true pred virtual(NT,_A,X)
   : ( (NT=neg(_B,_C)),
       mshare([[_A],[X],[_C]]),
       ground([_B]), linear(X), linear(_C) )
   => ( mshare([[_A],[_A,X],[_A,X,_C],[_A,_C]]),
        ground([_B]) ).

:- true pred virtual(NT,_A,X)
   : ( (NT=verb_form(_B,_C,_D,_E)),
       mshare([[_A],[_A,_D],[X],[_B],[_C],[_D],[_E]]),
       linear(X), linear(_B), linear(_C), linear(_E) )
   => mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_B,_C,_D],[_A,X,_B,_C,_D,_E],[_A,X,_B,_C,_E],[_A,X,_B,_D],[_A,X,_B,_D,_E],[_A,X,_B,_E],[_A,X,_C],[_A,X,_C,_D],[_A,X,_C,_D,_E],[_A,X,_C,_E],[_A,X,_D],[_A,X,_D,_E],[_A,X,_E],[_A,_B],[_A,_B,_C],[_A,_B,_C,_D],[_A,_B,_C,_D,_E],[_A,_B,_C,_E],[_A,_B,_D],[_A,_B,_D,_E],[_A,_B,_E],[_A,_C],[_A,_C,_D],[_A,_C,_D,_E],[_A,_C,_E],[_A,_D],[_A,_D,_E],[_A,_E]]).

:- true pred virtual(NT,_A,X)
   : ( (NT=verb(_B,_C,_D,_E)),
       mshare([[_A],[_A,_C],[X],[_B],[_C],[_D],[_E]]),
       linear(X), linear(_B), linear(_D), linear(_E) )
   => mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_B,_C,_D],[_A,X,_B,_C,_D,_E],[_A,X,_B,_C,_E],[_A,X,_B,_D],[_A,X,_B,_D,_E],[_A,X,_B,_E],[_A,X,_C],[_A,X,_C,_D],[_A,X,_C,_D,_E],[_A,X,_C,_E],[_A,X,_D],[_A,X,_D,_E],[_A,X,_E],[_A,_B],[_A,_B,_C],[_A,_B,_C,_D],[_A,_B,_C,_D,_E],[_A,_B,_C,_E],[_A,_B,_D],[_A,_B,_D,_E],[_A,_B,_E],[_A,_C],[_A,_C,_D],[_A,_C,_D,_E],[_A,_C,_E],[_A,_D],[_A,_D,_E],[_A,_E]]).

:- true pred virtual(NT,_A,X)
   : ( (NT=np(_B,_C,_D,_E,_F,_G,_H)),
       mshare([[_A],[X],[_B],[_C],[_D],[_H]]),
       ground([_E,_F,_G]), linear(X), linear(_B), linear(_C), linear(_D), linear(_H) )
   => ( mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_B,_C,_D],[_A,X,_B,_C,_D,_H],[_A,X,_B,_C,_H],[_A,X,_B,_D],[_A,X,_B,_D,_H],[_A,X,_B,_H],[_A,X,_C],[_A,X,_C,_D],[_A,X,_C,_D,_H],[_A,X,_C,_H],[_A,X,_D],[_A,X,_D,_H],[_A,X,_H],[_A,_B],[_A,_B,_C],[_A,_B,_C,_D],[_A,_B,_C,_D,_H],[_A,_B,_C,_H],[_A,_B,_D],[_A,_B,_D,_H],[_A,_B,_H],[_A,_C],[_A,_C,_D],[_A,_C,_D,_H],[_A,_C,_H],[_A,_D],[_A,_D,_H],[_A,_H]]),
        ground([_E,_F,_G]) ).

:- true pred virtual(NT,_A,X)
   : ( (NT=np_head0(_B,_C,_D)),
       mshare([[_A],[X],[_B],[_C],[_D]]),
       linear(X), linear(_B), linear(_C), linear(_D) )
   => mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_B,_C,_D],[_A,X,_B,_D],[_A,X,_C],[_A,X,_C,_D],[_A,X,_D],[_A,_B],[_A,_B,_C],[_A,_B,_C,_D],[_A,_B,_D],[_A,_C],[_A,_C,_D],[_A,_D]]).

:- true pred virtual(NT,_A,X)
   : ( (NT=np(_B,_C,_D,_E,_F,_G,_H)),
       mshare([[_A],[X],[_B],[_C],[_D],[_E],[_H]]),
       ground([_F,_G]), linear(X), linear(_B), linear(_C), linear(_D), linear(_E), linear(_H) )
   => ( mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_B,_C,_D],[_A,X,_B,_C,_D,_E],[_A,X,_B,_C,_D,_E,_H],[_A,X,_B,_C,_D,_H],[_A,X,_B,_C,_E],[_A,X,_B,_C,_E,_H],[_A,X,_B,_C,_H],[_A,X,_B,_D],[_A,X,_B,_D,_E],[_A,X,_B,_D,_E,_H],[_A,X,_B,_D,_H],[_A,X,_B,_E],[_A,X,_B,_E,_H],[_A,X,_B,_H],[_A,X,_C],[_A,X,_C,_D],[_A,X,_C,_D,_E],[_A,X,_C,_D,_E,_H],[_A,X,_C,_D,_H],[_A,X,_C,_E],[_A,X,_C,_E,_H],[_A,X,_C,_H],[_A,X,_D],[_A,X,_D,_E],[_A,X,_D,_E,_H],[_A,X,_D,_H],[_A,X,_E],[_A,X,_E,_H],[_A,X,_H],[_A,_B],[_A,_B,_C],[_A,_B,_C,_D],[_A,_B,_C,_D,_E],[_A,_B,_C,_D,_E,_H],[_A,_B,_C,_D,_H],[_A,_B,_C,_E],[_A,_B,_C,_E,_H],[_A,_B,_C,_H],[_A,_B,_D],[_A,_B,_D,_E],[_A,_B,_D,_E,_H],[_A,_B,_D,_H],[_A,_B,_E],[_A,_B,_E,_H],[_A,_B,_H],[_A,_C],[_A,_C,_D],[_A,_C,_D,_E],[_A,_C,_D,_E,_H],[_A,_C,_D,_H],[_A,_C,_E],[_A,_C,_E,_H],[_A,_C,_H],[_A,_D],[_A,_D,_E],[_A,_D,_E,_H],[_A,_D,_H],[_A,_E],[_A,_E,_H],[_A,_H]]),
        ground([_F,_G]) ).

:- true pred virtual(NT,_A,X)
   : ( (NT=pp(_B,_C,_D,_E)),
       mshare([[_A],[X],[_B],[_E]]),
       ground([_C,_D]), linear(X), linear(_B), linear(_E) )
   => ( mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_E],[_A,X,_E],[_A,_B],[_A,_B,_E],[_A,_E]]),
        ground([_C,_D]) ).

:- true pred virtual(NT,_A,X)
   : ( (NT=adv_phrase(_B,_C,_D)),
       mshare([[_A],[X],[_B],[_D]]),
       ground([_C]), linear(X), linear(_B), linear(_D) )
   => ( mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_D],[_A,X,_D],[_A,_B],[_A,_B,_D],[_A,_D]]),
        ground([_C]) ).

:- true pred virtual(NT,_A,X)
   : ( (NT=np(_B,_C,_D,_E,_F,_G,_H)),
       mshare([[_A],[X],[_B],[_C],[_E],[_H]]),
       ground([_D,_F,_G]), linear(X), linear(_B), linear(_C), linear(_E), linear(_H) )
   => ( mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_B,_C,_E],[_A,X,_B,_C,_E,_H],[_A,X,_B,_C,_H],[_A,X,_B,_E],[_A,X,_B,_E,_H],[_A,X,_B,_H],[_A,X,_C],[_A,X,_C,_E],[_A,X,_C,_E,_H],[_A,X,_C,_H],[_A,X,_E],[_A,X,_E,_H],[_A,X,_H],[_A,_B],[_A,_B,_C],[_A,_B,_C,_E],[_A,_B,_C,_E,_H],[_A,_B,_C,_H],[_A,_B,_E],[_A,_B,_E,_H],[_A,_B,_H],[_A,_C],[_A,_C,_E],[_A,_C,_E,_H],[_A,_C,_H],[_A,_E],[_A,_E,_H],[_A,_H]]),
        ground([_D,_F,_G]) ).

:- true pred virtual(NT,_A,X)
   : ( (NT=predicate(_B,_C,_D)),
       mshare([[_A],[_A,_B],[X],[_B],[_C],[_D]]),
       linear(X), linear(_C), linear(_D) )
   => mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_B,_C,_D],[_A,X,_B,_D],[_A,X,_C],[_A,X,_C,_D],[_A,X,_D],[_A,_B],[_A,_B,_C],[_A,_B,_C,_D],[_A,_B,_D],[_A,_C],[_A,_C,_D],[_A,_D]]).

:- true pred virtual(NT,_A,X)
   : ( (NT=verb_form(_B,_C,_D,_E)),
       mshare([[_A],[X],[_B],[_C],[_D],[_E]]),
       linear(X), linear(_B), linear(_C), linear(_D), linear(_E) )
   => mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_B,_C,_D],[_A,X,_B,_C,_D,_E],[_A,X,_B,_C,_E],[_A,X,_B,_D],[_A,X,_B,_D,_E],[_A,X,_B,_E],[_A,X,_C],[_A,X,_C,_D],[_A,X,_C,_D,_E],[_A,X,_C,_E],[_A,X,_D],[_A,X,_D,_E],[_A,X,_E],[_A,_B],[_A,_B,_C],[_A,_B,_C,_D],[_A,_B,_C,_D,_E],[_A,_B,_C,_E],[_A,_B,_D],[_A,_B,_D,_E],[_A,_B,_E],[_A,_C],[_A,_C,_D],[_A,_C,_D,_E],[_A,_C,_E],[_A,_D],[_A,_D,_E],[_A,_E]]).

:- true pred virtual(NT,_A,X)
   : ( (NT=neg(_B,_C)),
       mshare([[_A],[X],[_B],[_C]]),
       linear(X), linear(_B), linear(_C) )
   => mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_C],[_A,_B],[_A,_B,_C],[_A,_C]]).

:- true pred virtual(NT,_A,X)
   : ( (NT=np(_B,_C,_D,_E,_F,_G,_H)),
       mshare([[_A],[X],[_B],[_H]]),
       ground([_C,_D,_E,_F,_G]), linear(X), linear(_B), linear(_H) )
   => ( mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_H],[_A,X,_H],[_A,_B],[_A,_B,_H],[_A,_H]]),
        ground([_C,_D,_E,_F,_G]) ).

:- true pred virtual(NT,_A,X)
   : ( (NT=det(_B,_C,_D)),
       mshare([[_A],[X],[_B],[_C]]),
       ground([_D]), linear(X), linear(_B), linear(_C) )
   => ( mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_C],[_A,_B],[_A,_B,_C],[_A,_C]]),
        ground([_D]) ).

:- true pred virtual(NT,_A,X)
   : ( (NT=gen_marker),
       mshare([[_A],[X]]),
       linear(X) )
   => mshare([[_A],[_A,X]]).

:- true pred virtual(NT,_A,X)
   : ( (NT=det(_B,_C,_D)),
       mshare([[_A],[X],[_B],[_C],[_D]]),
       linear(X), linear(_B), linear(_C), linear(_D) )
   => mshare([[_A],[_A,X],[_A,X,_B],[_A,X,_B,_C],[_A,X,_B,_C,_D],[_A,X,_B,_D],[_A,X,_C],[_A,X,_C,_D],[_A,X,_D],[_A,_B],[_A,_B,_C],[_A,_B,_C,_D],[_A,_B,_D],[_A,_C],[_A,_C,_D],[_A,_D]]).

:- true pred virtual(NT,_A,X)
   : ( (NT=np(_B,_C,_D,_E,_F,_G,_H)),
       mshare([[X],[_B],[_C],[_D],[_E],[_H]]),
       ground([_A,_F,_G]), linear(X), linear(_B), linear(_C), linear(_D), linear(_E), linear(_H) )
   => ground([_A,X,_B,_C,_D,_E,_F,_G,_H]).

:- true pred virtual(NT,_A,X)
   : ( (NT=pp(_B,_C,_D,_E)),
       mshare([[X],[_B],[_E]]),
       ground([_A,_C,_D]), linear(X), linear(_B), linear(_E) )
   => ground([_A,X,_B,_C,_D,_E]).

:- true pred virtual(NT,_A,X)
   : ( (NT=adv_phrase(_B,_C,_D)),
       mshare([[X],[_B],[_D]]),
       ground([_A,_C]), linear(X), linear(_B), linear(_D) )
   => ground([_A,X,_B,_C,_D]).

:- true pred virtual(NT,_A,X)
   : ( (NT=np(_B,_C,_D,_E,_F,_G,_H)),
       mshare([[X],[_B],[_C],[_E],[_H]]),
       ground([_A,_D,_F,_G]), linear(X), linear(_B), linear(_C), linear(_E), linear(_H) )
   => ground([_A,X,_B,_C,_D,_E,_F,_G,_H]).

:- true pred virtual(NT,_A,X)
   : ( (NT=predicate(_B,_C,_D)),
       mshare([[X],[_C],[_D]]),
       ground([_A,_B]), linear(X), linear(_C), linear(_D) )
   => ground([_A,X,_B,_C,_D]).

:- true pred virtual(NT,_A,X)
   : ( (NT=verb_form(_B,_C,_D,_E)),
       mshare([[X],[_B],[_C],[_D],[_E]]),
       ground([_A]), linear(X), linear(_B), linear(_C), linear(_D), linear(_E) )
   => ground([_A,X,_B,_C,_D,_E]).

:- true pred virtual(NT,_A,X)
   : ( (NT=neg(_B,_C)),
       mshare([[X],[_B],[_C]]),
       ground([_A]), linear(X), linear(_B), linear(_C) )
   => ground([_A,X,_B,_C]).

:- true pred virtual(NT,_A,X)
   : ( (NT=np(_B,_C,_D,_E,_F,_G,_H)),
       mshare([[X],[_B],[_H]]),
       ground([_A,_C,_D,_E,_F,_G]), linear(X), linear(_B), linear(_H) )
   => ground([_A,X,_B,_C,_D,_E,_F,_G,_H]).

:- true pred virtual(NT,_A,X)
   : ( (NT=det(_B,_C,_D)),
       mshare([[X],[_B],[_C]]),
       ground([_A,_D]), linear(X), linear(_B), linear(_C) )
   => ground([_A,X,_B,_C,_D]).

:- true pred virtual(NT,_A,X)
   : ( (NT=gen_marker),
       mshare([[X]]),
       ground([_A]), linear(X) )
   => ground([_A,X]).

:- true pred virtual(NT,_A,X)
   : ( (NT=det(_B,_C,_D)),
       mshare([[X],[_B],[_C],[_D]]),
       ground([_A]), linear(X), linear(_B), linear(_C), linear(_D) )
   => ground([_A,X,_B,_C,_D]).

:- true pred virtual(NT,_A,X)
   : ( (NT=np_head0(_B,_C,_D)),
       mshare([[X],[_B],[_C],[_D]]),
       ground([_A]), linear(X), linear(_B), linear(_C), linear(_D) )
   => ground([_A,X,_B,_C,_D]).

virtual(NT,x(_1,nonterminal,NT,X),X).

:- true pred is_pp(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ( mshare([[_A]]),
        linear(_A) ).

:- true pred is_pp(_A)
   : ground([_A])
   => ground([_A]).

is_pp(#(1,_1,_2,_3)).

:- true pred is_pred(_A)
   : ground([_A])
   => ground([_A]).

is_pred(#(_1,1,_2,_3)).

is_trace(#(_1,_2,1,_3)).

:- true pred is_adv(_A)
   : ground([_A])
   => ground([_A]).

:- true pred is_adv(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ( mshare([[_A]]),
        linear(_A) ).

is_adv(#(_1,_2,_3,1)).

:- true pred trace1(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_A), linear(_B) )
   => ( mshare([[_A]]),
        ground([_B]), linear(_A) ).

trace1(#(_1,_2,1,_3),#(0,0,0,0)).

:- true pred trace1(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ground([_A]).

trace1(#(0,0,1,0)).

:- true pred adv(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ground([_A]).

adv(#(0,0,0,1)).

:- true pred empty(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ground([_A]).

empty(#(0,0,0,0)).

:- true pred np_all(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ground([_A]).

np_all(#(1,1,1,0)).

:- true pred s_all(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ground([_A]).

s_all(#(1,0,1,1)).

:- true pred np_no_trace(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ground([_A]).

np_no_trace(#(1,1,0,0)).

:- true pred myplus(_A,_B,_C)
   : ( mshare([[_A],[_C]]),
       ground([_B]), linear(_C) )
   => ground([_A,_B,_C]).

:- true pred myplus(_A,_B,_C)
   : ( mshare([[_B],[_C]]),
       ground([_A]), linear(_C) )
   => ( mshare([[_B]]),
        ground([_A,_C]) ).

:- true pred myplus(_A,_B,_C)
   : ( mshare([[_C]]),
       ground([_A,_B]), linear(_C) )
   => ground([_A,_B,_C]).

myplus(#(B1,B2,B3,B4),#(C1,C2,C3,C4),#(D1,D2,D3,D4)) :-
    true((mshare([[B1],[B1,B2],[B1,B2,B3],[B1,B2,B3,B4],[B1,B2,B4],[B1,B3],[B1,B3,B4],[B1,B4],[B2],[B2,B3],[B2,B3,B4],[B2,B4],[B3],[B3,B4],[B4],[D1],[D2],[D3],[D4]]),ground([C1,C2,C3,C4]),linear(D1),linear(D2),linear(D3),linear(D4);mshare([[C1],[C1,C2],[C1,C2,C3],[C1,C2,C3,C4],[C1,C2,C4],[C1,C3],[C1,C3,C4],[C1,C4],[C2],[C2,C3],[C2,C3,C4],[C2,C4],[C3],[C3,C4],[C4],[D1],[D2],[D3],[D4]]),ground([B1,B2,B3,B4]),linear(D1),linear(D2),linear(D3),linear(D4);mshare([[D1],[D2],[D3],[D4]]),ground([B1,B2,B3,B4,C1,C2,C3,C4]),linear(D1),linear(D2),linear(D3),linear(D4))),
    or(B1,C1,D1),
    true((mshare([[B2],[B2,B3],[B2,B3,B4],[B2,B4],[B3],[B3,B4],[B4],[D2],[D3],[D4]]),ground([B1,C1,C2,C3,C4,D1]),linear(D2),linear(D3),linear(D4);mshare([[C1],[C1,C2],[C1,C2,C3],[C1,C2,C3,C4],[C1,C2,C4],[C1,C3],[C1,C3,C4],[C1,C4],[C2],[C2,C3],[C2,C3,C4],[C2,C4],[C3],[C3,C4],[C4],[D2],[D3],[D4]]),ground([B1,B2,B3,B4,D1]),linear(D2),linear(D3),linear(D4);mshare([[D2],[D3],[D4]]),ground([B1,B2,B3,B4,C1,C2,C3,C4,D1]),linear(D2),linear(D3),linear(D4))),
    or(B2,C2,D2),
    true((mshare([[B3],[B3,B4],[B4],[D3],[D4]]),ground([B1,B2,C1,C2,C3,C4,D1,D2]),linear(D3),linear(D4);mshare([[C1],[C1,C2],[C1,C2,C3],[C1,C2,C3,C4],[C1,C2,C4],[C1,C3],[C1,C3,C4],[C1,C4],[C2],[C2,C3],[C2,C3,C4],[C2,C4],[C3],[C3,C4],[C4],[D3],[D4]]),ground([B1,B2,B3,B4,D1,D2]),linear(D3),linear(D4);mshare([[D3],[D4]]),ground([B1,B2,B3,B4,C1,C2,C3,C4,D1,D2]),linear(D3),linear(D4))),
    or(B3,C3,D3),
    true((mshare([[B4],[D4]]),ground([B1,B2,B3,C1,C2,C3,C4,D1,D2,D3]),linear(D4);mshare([[C1],[C1,C2],[C1,C2,C3],[C1,C2,C3,C4],[C1,C2,C4],[C1,C3],[C1,C3,C4],[C1,C4],[C2],[C2,C3],[C2,C3,C4],[C2,C4],[C3],[C3,C4],[C4],[D4]]),ground([B1,B2,B3,B4,D1,D2,D3]),linear(D4);mshare([[D4]]),ground([B1,B2,B3,B4,C1,C2,C3,C4,D1,D2,D3]),linear(D4))),
    or(B4,C4,D4),
    true((mshare([[C1],[C1,C2],[C1,C2,C3],[C1,C2,C3,C4],[C1,C2,C4],[C1,C3],[C1,C3,C4],[C1,C4],[C2],[C2,C3],[C2,C3,C4],[C2,C4],[C3],[C3,C4],[C4]]),ground([B1,B2,B3,B4,D1,D2,D3,D4]);ground([B1,B2,B3,B4,C1,C2,C3,C4,D1,D2,D3,D4]))).

:- true pred minus(_A,_B,_C)
   : ( mshare([[_C]]),
       ground([_A,_B]), linear(_C) )
   => ground([_A,_B,_C]).

:- true pred minus(_A,_B,_C)
   : ( mshare([[_B],[_C]]),
       ground([_A]), linear(_C) )
   => ground([_A,_B,_C]).

minus(#(B1,B2,B3,B4),#(C1,C2,C3,C4),#(D1,D2,D3,D4)) :-
    true((mshare([[C1],[C1,C2],[C1,C2,C3],[C1,C2,C3,C4],[C1,C2,C4],[C1,C3],[C1,C3,C4],[C1,C4],[C2],[C2,C3],[C2,C3,C4],[C2,C4],[C3],[C3,C4],[C4],[D1],[D2],[D3],[D4]]),ground([B1,B2,B3,B4]),linear(D1),linear(D2),linear(D3),linear(D4);mshare([[D1],[D2],[D3],[D4]]),ground([B1,B2,B3,B4,C1,C2,C3,C4]),linear(D1),linear(D2),linear(D3),linear(D4))),
    anot(B1,C1,D1),
    true((mshare([[C2],[C2,C3],[C2,C3,C4],[C2,C4],[C3],[C3,C4],[C4],[D2],[D3],[D4]]),ground([B1,B2,B3,B4,C1,D1]),linear(D2),linear(D3),linear(D4);mshare([[D2],[D3],[D4]]),ground([B1,B2,B3,B4,C1,C2,C3,C4,D1]),linear(D2),linear(D3),linear(D4))),
    anot(B2,C2,D2),
    true((mshare([[C3],[C3,C4],[C4],[D3],[D4]]),ground([B1,B2,B3,B4,C1,C2,D1,D2]),linear(D3),linear(D4);mshare([[D3],[D4]]),ground([B1,B2,B3,B4,C1,C2,C3,C4,D1,D2]),linear(D3),linear(D4))),
    anot(B3,C3,D3),
    true((mshare([[C4],[D4]]),ground([B1,B2,B3,B4,C1,C2,C3,D1,D2,D3]),linear(D4);mshare([[D4]]),ground([B1,B2,B3,B4,C1,C2,C3,C4,D1,D2,D3]),linear(D4))),
    anot(B4,C4,D4),
    true(ground([B1,B2,B3,B4,C1,C2,C3,C4,D1,D2,D3,D4])).

:- true pred or(_A,_1,_B)
   : ( mshare([[_B]]),
       ground([_A,_1]), linear(_B) )
   => ground([_A,_1,_B]).

:- true pred or(_A,_1,_B)
   : ( mshare([[_A],[_B]]),
       ground([_1]), linear(_B) )
   => ground([_A,_1,_B]).

:- true pred or(_A,_1,_B)
   : ( mshare([[_1],[_B]]),
       ground([_A]), linear(_B) )
   => ( mshare([[_1]]),
        ground([_A,_B]) ).

or(1,_1,1).
or(0,1,1).
or(0,0,0).

:- true pred anot(X,_A,_B)
   : ( mshare([[_A],[_B]]),
       ground([X]), linear(_B) )
   => ground([X,_A,_B]).

:- true pred anot(X,_A,_B)
   : ( mshare([[_B]]),
       ground([X,_A]), linear(_B) )
   => ground([X,_A,_B]).

anot(X,0,X).
anot(X,1,0).

:- true pred role(_A,_1,_2)
   : ( mshare([[_1],[_2]]),
       ground([_A]), linear(_1), linear(_2) )
   => ( mshare([[_1],[_2]]),
        ground([_A]) ).

:- true pred role(_A,_1,_2)
   : ( (_1=decl),
       mshare([[_A]]),
       ground([_2]) )
   => ground([_A,_2]).

:- true pred role(_A,_1,_2)
   : ( mshare([[_1],[_2]]),
       ground([_A]), linear(_1) )
   => ( mshare([[_1],[_2]]),
        ground([_A]) ).

:- true pred role(_A,_1,_2)
   : ( (_A=subj),
       mshare([[_1],[_2]]),
       linear(_1) )
   => ( mshare([[_1]]),
        ground([_2]), linear(_1) ).

:- true pred role(_A,_1,_2)
   : ( (_1=decl),
       mshare([[_A],[_2]]),
       linear(_2) )
   => ( mshare([[_2]]),
        ground([_A]) ).

:- true pred role(_A,_1,_2)
   : ( (_1=decl),
       mshare([[_2]]),
       ground([_A]), linear(_2) )
   => ( mshare([[_2]]),
        ground([_A]) ).

role(subj,_1,#(1,0,0)).
role(compl,_1,#(0,_2,_3)).
role(undef,main,#(_1,0,_2)).
role(undef,aux,#(0,_1,_2)).
role(undef,decl,_1).
role(nil,_1,_2).

:- true pred subj_case(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ground([_A]).

subj_case(#(1,0,0)).

:- true pred verb_case(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ground([_A]).

verb_case(#(0,1,0)).

:- true pred prep_case(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ground([_A]).

prep_case(#(0,0,1)).

:- true pred compl_case(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => ( mshare([[_A]]),
        linear(_A) ).

:- true pred compl_case(_A)
   : mshare([[_A]])
   => mshare([[_A]]).

compl_case(#(0,_1,_2)).

:- true pred say(X,Y)
   : ( mshare([[Y]]),
       ground([X]), linear(Y) )
   => ( mshare([[Y]]),
        ground([X]) ).

say(X,Y) :-
    true((
        mshare([[Y]]),
        ground([X]),
        linear(Y)
    )),
    sentence(Y,X,[],[],[]),
    true((
        mshare([[Y]]),
        ground([X])
    )).

:- true pred sentence(B,C,D,E,F)
   : ( (D=[]), (E=[]), (F=[]),
       mshare([[B]]),
       ground([C]), linear(B) )
   => ( mshare([[B]]),
        ground([C]) ).

sentence(B,C,D,E,F) :-
    true((
        mshare([[B],[G],[H]]),
        ground([C,D,E,F]),
        linear(B),
        linear(G),
        linear(H)
    )),
    declarative(B,C,G,E,H),
    true((
        mshare([[B],[B,H],[H]]),
        ground([C,D,E,F,G])
    )),
    terminator('.',G,D,H,F),
    true((
        mshare([[B],[B,H],[H]]),
        ground([C,D,E,F,G])
    )).
sentence(B,C,D,E,F) :-
    true((
        mshare([[B],[G],[H]]),
        ground([C,D,E,F]),
        linear(B),
        linear(G),
        linear(H)
    )),
    wh_question(B,C,G,E,H),
    true((
        mshare([[B],[B,H],[H]]),
        ground([C,D,E,F,G])
    )),
    terminator(?,G,D,H,F),
    true((
        mshare([[B],[B,H],[H]]),
        ground([C,D,E,F,G])
    )).
sentence(B,C,D,E,F) :-
    true((
        mshare([[B],[G],[H],[I],[J]]),
        ground([C,D,E,F]),
        linear(B),
        linear(G),
        linear(H),
        linear(I),
        linear(J)
    )),
    topic(C,G,E,H),
    true((
        mshare([[B],[H],[I],[J]]),
        ground([C,D,E,F,G]),
        linear(B),
        linear(I),
        linear(J)
    )),
    wh_question(B,G,I,H,J),
    true((
        mshare([[B],[B,H],[B,H,J],[B,J],[H],[H,J],[J]]),
        ground([C,D,E,F,G,I])
    )),
    terminator(?,I,D,J,F),
    true((
        mshare([[B],[B,H],[B,H,J],[B,J],[H],[H,J],[J]]),
        ground([C,D,E,F,G,I])
    )).
sentence(B,C,D,E,F) :-
    true((
        mshare([[B],[G],[H]]),
        ground([C,D,E,F]),
        linear(B),
        linear(G),
        linear(H)
    )),
    yn_question(B,C,G,E,H),
    true((
        mshare([[B],[B,H],[H]]),
        ground([C,D,E,F,G])
    )),
    terminator(?,G,D,H,F),
    true((
        mshare([[B],[B,H],[H]]),
        ground([C,D,E,F,G])
    )).
sentence(B,C,D,E,F) :-
    true((
        mshare([[B],[G],[H]]),
        ground([C,D,E,F]),
        linear(B),
        linear(G),
        linear(H)
    )),
    imperative(B,C,G,E,H),
    true((
        mshare([[B],[B,H],[H]]),
        ground([C,D,E,F,G])
    )),
    terminator(!,G,D,H,F),
    true((
        mshare([[B],[B,H],[H]]),
        ground([C,D,E,F,G])
    )).

:- true pred pp(B,C,D,E,F,_A,G,H)
   : ( (C=compl),
       mshare([[B],[D],[E],[_A],[H]]),
       ground([F,G]), linear(B), linear(D), linear(E), linear(_A), linear(H) )
   => ( mshare([[B],[B,H],[D],[H]]),
        ground([E,F,_A,G]) ).

:- true pred pp(B,C,D,E,F,_A,G,H)
   : ( (C=compl),
       mshare([[B],[E],[_A],[G],[H]]),
       ground([D,F]), linear(B), linear(E), linear(_A), linear(H) )
   => ( mshare([[B],[B,E,G],[B,E,G,H],[B,G],[B,G,H],[B,H],[E,G],[E,G,H],[G],[G,H],[H]]),
        ground([D,F,_A]) ).

:- true pred pp(B,C,D,E,F,_A,G,H)
   : ( (B=pp(prep(of),_B)), (C=compl),
       mshare([[E],[_A],[H],[_B]]),
       ground([D,F,G]), linear(E), linear(_A), linear(H), linear(_B) )
   => ( mshare([[H],[H,_B],[_B]]),
        ground([D,E,F,_A,G]) ).

:- true pred pp(B,C,D,E,F,_A,G,H)
   : ( (C=compl),
       mshare([[B],[E],[_A],[H]]),
       ground([D,F,G]), linear(B), linear(E), linear(_A), linear(H) )
   => ( mshare([[B],[B,H],[H]]),
        ground([D,E,F,_A,G]) ).

:- true pred pp(B,C,D,E,F,_A,G,H)
   : ( mshare([[B],[E],[_A],[H]]),
       ground([C,D,F,G]), linear(B), linear(E), linear(_A), linear(H) )
   => ( mshare([[B],[B,H],[H]]),
        ground([C,D,E,F,_A,G]) ).

:- true pred pp(B,C,D,E,F,_A,G,H)
   : ( mshare([[B],[E],[_A],[G],[H]]),
       ground([C,D,F]), linear(B), linear(E), linear(_A), linear(H) )
   => ( mshare([[B],[B,E,G],[B,E,G,H],[B,G],[B,G,H],[B,H],[E,G],[E,G,H],[G],[G,H],[H]]),
        ground([C,D,F,_A]) ).

:- true pred pp(B,C,D,E,F,_A,G,H)
   : ( (B=pp(prep(of),_B)), (C=compl),
       mshare([[E],[_A],[G],[H],[_B]]),
       ground([D,F]), linear(E), linear(_A), linear(H), linear(_B) )
   => ( mshare([[E,G],[E,G,H],[E,G,H,_B],[E,G,_B],[G],[G,H],[G,H,_B],[G,_B],[H],[H,_B],[_B]]),
        ground([D,F,_A]) ).

pp(B,C,D,E,F,F,G,H) :-
    true((mshare([[B],[D],[E],[H]]),ground([C,F,G]),linear(B),linear(D),linear(E),linear(H);mshare([[B],[E],[G],[H]]),ground([C,D,F]),linear(B),linear(E),linear(H);mshare([[B],[E],[H]]),ground([C,D,F,G]),linear(B),linear(E),linear(H))),
    virtual(pp(B,C,D,E),G,H),
    true((mshare([[B,E,G],[B,E,G,H],[B,G],[B,G,H],[E,G],[E,G,H],[G],[G,H]]),ground([C,D,F]);ground([B,C,D,E,F,G,H]))).
pp(pp(B,C),D,E,F,G,H,I,J) :-
    true((mshare([[E],[F],[H],[J],[B],[C],[K],[L],[M],[N],[O]]),ground([D,G,I]),linear(E),linear(F),linear(H),linear(J),linear(B),linear(C),linear(K),linear(L),linear(M),linear(N),linear(O);mshare([[F],[H],[I],[J],[B],[C],[K],[L],[M],[N],[O]]),ground([D,E,G]),linear(F),linear(H),linear(J),linear(B),linear(C),linear(K),linear(L),linear(M),linear(N),linear(O);mshare([[F],[H],[I],[J],[C],[K],[L],[M],[N],[O]]),ground([D,E,G,B]),linear(F),linear(H),linear(J),linear(C),linear(K),linear(L),linear(M),linear(N),linear(O);mshare([[F],[H],[J],[B],[C],[K],[L],[M],[N],[O]]),ground([D,E,G,I]),linear(F),linear(H),linear(J),linear(B),linear(C),linear(K),linear(L),linear(M),linear(N),linear(O);mshare([[F],[H],[J],[C],[K],[L],[M],[N],[O]]),ground([D,E,G,I,B]),linear(F),linear(H),linear(J),linear(C),linear(K),linear(L),linear(M),linear(N),linear(O))),
    prep(B,G,K,I,L),
    true((mshare([[E],[F],[H],[J],[C],[M],[N],[O]]),ground([D,G,I,B,K,L]),linear(E),linear(F),linear(H),linear(J),linear(C),linear(M),linear(N),linear(O);mshare([[F],[H],[I],[I,L],[J],[C],[M],[N],[O]]),ground([D,E,G,B,K]),linear(F),linear(H),linear(J),linear(C),linear(M),linear(N),linear(O);mshare([[F],[H],[J],[C],[M],[N],[O]]),ground([D,E,G,I,B,K,L]),linear(F),linear(H),linear(J),linear(C),linear(M),linear(N),linear(O))),
    prep_case(M),
    true((mshare([[E],[F],[H],[J],[C],[N],[O]]),ground([D,G,I,B,K,L,M]),linear(E),linear(F),linear(H),linear(J),linear(C),linear(N),linear(O);mshare([[F],[H],[I],[I,L],[J],[C],[N],[O]]),ground([D,E,G,B,K,M]),linear(F),linear(H),linear(J),linear(C),linear(N),linear(O);mshare([[F],[H],[J],[C],[N],[O]]),ground([D,E,G,I,B,K,L,M]),linear(F),linear(H),linear(J),linear(C),linear(N),linear(O))),
    np(C,N,M,O,D,E,F,K,H,L,J),
    true((mshare([[E],[J],[J,C],[J,C,N],[C],[C,N],[N]]),ground([D,F,G,H,I,B,K,L,M,O]);mshare([[F,I,J,C,L],[F,I,J,C,L,N],[F,I,J,C,L,N,O],[F,I,J,C,L,O],[F,I,J,L],[F,I,J,L,N],[F,I,J,L,N,O],[F,I,J,L,O],[F,I,C,L],[F,I,C,L,N],[F,I,C,L,N,O],[F,I,C,L,O],[F,I,L],[F,I,L,N],[F,I,L,N,O],[F,I,L,O],[I],[I,J,C,L],[I,J,C,L,N],[I,J,C,L,N,O],[I,J,C,L,O],[I,J,L],[I,J,L,N],[I,J,L,N,O],[I,J,L,O],[I,C,L],[I,C,L,N],[I,C,L,N,O],[I,C,L,O],[I,L],[I,L,N],[I,L,N,O],[I,L,O],[J],[J,C],[J,C,N],[C],[C,N],[N]]),ground([D,E,G,H,B,K,M]);mshare([[J],[J,C],[J,C,N],[C],[C,N],[N]]),ground([D,E,F,G,H,I,B,K,L,M,O]))).

:- true pred topic(B,C,D,_A)
   : ( mshare([[C],[_A]]),
       ground([B,D]), linear(C), linear(_A) )
   => ( mshare([[_A]]),
        ground([B,C,D]) ).

topic(B,C,D,x(gap,nonterminal,pp(E,compl,F,G),H)) :-
    true((
        mshare([[C],[H],[E],[F],[G],[I],[J]]),
        ground([B,D]),
        linear(C),
        linear(H),
        linear(E),
        linear(F),
        linear(G),
        linear(I),
        linear(J)
    )),
    pp(E,compl,F,G,B,I,D,J),
    true((
        mshare([[C],[H],[E],[E,J],[F],[J]]),
        ground([B,D,G,I]),
        linear(C),
        linear(H)
    )),
    opt_comma(I,C,J,H),
    true((
        mshare([[H,E,J],[H,J],[E],[E,J],[F],[J]]),
        ground([B,C,D,G,I])
    )).

:- true pred opt_comma(B,C,D,E)
   : ( mshare([[C],[D],[E]]),
       ground([B]), linear(C), linear(E) )
   => ( mshare([[D],[D,E]]),
        ground([B,C]) ).

opt_comma(B,C,D,E) :-
    true((
        mshare([[C],[D],[E]]),
        ground([B]),
        linear(C),
        linear(E)
    )),
    ~(',',B,C,D,E),
    true((
        mshare([[D],[D,E]]),
        ground([B,C])
    )).
opt_comma(B,B,C,C).

:- true pred declarative(_A,C,D,E,F)
   : ( mshare([[_A],[D],[F]]),
       ground([C,E]), linear(_A), linear(D), linear(F) )
   => ( mshare([[_A],[_A,F],[F]]),
        ground([C,D,E]) ).

declarative((decl B),C,D,E,F) :-
    true((
        mshare([[D],[F],[B],[G]]),
        ground([C,E]),
        linear(D),
        linear(F),
        linear(B),
        linear(G)
    )),
    s(B,G,C,D,E,F),
    true((
        mshare([[F],[F,B],[B]]),
        ground([C,D,E,G])
    )).

:- true pred wh_question(_A,D,E,F,G)
   : ( mshare([[_A],[E],[F],[G]]),
       ground([D]), linear(_A), linear(E), linear(G) )
   => ( mshare([[_A],[_A,F],[_A,F,G],[_A,G],[F],[F,G],[G]]),
        ground([D,E]) ).

:- true pred wh_question(_A,D,E,F,G)
   : ( mshare([[_A],[E],[G]]),
       ground([D,F]), linear(_A), linear(E), linear(G) )
   => ( mshare([[_A],[_A,G],[G]]),
        ground([D,E,F]) ).

wh_question(whq(B,C),D,E,F,G) :-
    true((mshare([[E],[F],[G],[B],[C],[H],[I],[J],[K],[L]]),ground([D]),linear(E),linear(G),linear(B),linear(C),linear(H),linear(I),linear(J),linear(K),linear(L);mshare([[E],[G],[B],[C],[H],[I],[J],[K],[L]]),ground([D,F]),linear(E),linear(G),linear(B),linear(C),linear(H),linear(I),linear(J),linear(K),linear(L))),
    variable_q(B,H,I,J,D,K,F,L),
    true((mshare([[E],[F],[F,B],[F,B,H],[F,B,H,L],[F,B,L],[F,H],[F,H,L],[F,L],[G],[B],[B,H],[B,H,L],[B,L],[C],[H],[H,L],[J],[J,L],[L]]),ground([D,I,K]),linear(E),linear(G),linear(C);mshare([[E],[G],[B],[B,H],[B,H,L],[B,L],[C],[H],[H,L],[J],[J,L],[L]]),ground([D,F,I,K]),linear(E),linear(G),linear(C))),
    question(I,J,C,K,E,L,G),
    true((mshare([[F],[F,G,B,C,H,J,L],[F,G,B,C,H,L],[F,G,B,C,J,L],[F,G,B,C,L],[F,G,B,H,J,L],[F,G,B,H,L],[F,G,B,J,L],[F,G,B,L],[F,G,C,H,J,L],[F,G,C,H,L],[F,G,C,J,L],[F,G,C,L],[F,G,H,J,L],[F,G,H,L],[F,G,J,L],[F,G,L],[F,B],[F,B,C,H,J,L],[F,B,C,H,L],[F,B,C,J,L],[F,B,C,L],[F,B,H],[F,B,H,J,L],[F,B,H,L],[F,B,J,L],[F,B,L],[F,C,H,J,L],[F,C,H,L],[F,C,J,L],[F,C,L],[F,H],[F,H,J,L],[F,H,L],[F,J,L],[F,L],[G],[G,B,C,H,J,L],[G,B,C,H,L],[G,B,C,J,L],[G,B,C,L],[G,B,H,J,L],[G,B,H,L],[G,B,J,L],[G,B,L],[G,C],[G,C,H,J,L],[G,C,H,L],[G,C,J,L],[G,C,L],[G,H,J,L],[G,H,L],[G,J,L],[G,L],[B],[B,C,H,J,L],[B,C,H,L],[B,C,J,L],[B,C,L],[B,H],[B,H,J,L],[B,H,L],[B,J,L],[B,L],[C],[C,H,J,L],[C,H,L],[C,J,L],[C,L],[H],[H,J,L],[H,L],[J],[J,L],[L]]),ground([D,E,I,K]);mshare([[G],[G,B,C,H,J,L],[G,B,C,H,L],[G,B,C,J,L],[G,B,C,L],[G,B,H,J,L],[G,B,H,L],[G,B,J,L],[G,B,L],[G,C],[G,C,H,J,L],[G,C,H,L],[G,C,J,L],[G,C,L],[G,H,J,L],[G,H,L],[G,J,L],[G,L],[B],[B,C,H,J,L],[B,C,H,L],[B,C,J,L],[B,C,L],[B,H],[B,H,J,L],[B,H,L],[B,J,L],[B,L],[C],[C,H,J,L],[C,H,L],[C,J,L],[C,L],[H],[H,J,L],[H,L],[J],[J,L],[L]]),ground([D,E,F,I,K]))).

:- true pred np(B,C,D,E,F,G,H,I,_A,J,K)
   : ( (F=subj),
       mshare([[B],[C],[E],[H],[_A],[J],[K]]),
       ground([D,G,I]), linear(B), linear(C), linear(E), linear(H), linear(_A), linear(K) )
   => ( mshare([[B],[B,C],[B,C,E,H,J],[B,C,E,H,J,K],[B,C,E,J],[B,C,E,J,K],[B,C,H,J],[B,C,H,J,K],[B,C,J],[B,C,J,K],[B,C,K],[B,E,H,J],[B,E,H,J,K],[B,E,J],[B,E,J,K],[B,H,J],[B,H,J,K],[B,J],[B,J,K],[B,K],[C],[C,E,H,J],[C,E,H,J,K],[C,E,J],[C,E,J,K],[C,H,J],[C,H,J,K],[C,J],[C,J,K],[E,H,J],[E,H,J,K],[E,J],[E,J,K],[H,J],[H,J,K],[J],[J,K],[K]]),
        ground([D,G,I,_A]) ).

:- true pred np(B,C,D,E,F,G,H,I,_A,J,K)
   : ( (F=compl),
       mshare([[B],[C],[E],[H],[_A],[K]]),
       ground([D,G,I,J]), linear(B), linear(C), linear(E), linear(H), linear(_A), linear(K) )
   => ( mshare([[B],[B,C],[B,C,K],[B,K],[C],[K]]),
        ground([D,E,G,H,I,_A,J]) ).

:- true pred np(B,C,D,E,F,G,H,I,_A,J,K)
   : ( (F=subj),
       mshare([[B],[C],[D],[E],[H],[_A],[K]]),
       ground([G,I,J]), linear(B), linear(C), linear(D), linear(E), linear(H), linear(_A), linear(K) )
   => ( mshare([[B],[B,C],[B,C,K],[B,K],[C],[D],[K]]),
        ground([E,G,H,I,_A,J]) ).

:- true pred np(B,C,D,E,F,G,H,I,_A,J,K)
   : ( (F=subj),
       mshare([[B],[C,J],[D],[E],[H],[_A],[J],[K]]),
       ground([G,I]), linear(B), linear(D), linear(E), linear(H), linear(_A), linear(K) )
   => ( mshare([[B],[B,C,D,E,H,J],[B,C,D,E,H,J,K],[B,C,D,E,J],[B,C,D,E,J,K],[B,C,D,H,J],[B,C,D,H,J,K],[B,C,D,J],[B,C,D,J,K],[B,C,E,H,J],[B,C,E,H,J,K],[B,C,E,J],[B,C,E,J,K],[B,C,H,J],[B,C,H,J,K],[B,C,J],[B,C,J,K],[B,D,E,H,J],[B,D,E,H,J,K],[B,D,E,J],[B,D,E,J,K],[B,D,H,J],[B,D,H,J,K],[B,D,J],[B,D,J,K],[B,E,H,J],[B,E,H,J,K],[B,E,J],[B,E,J,K],[B,H,J],[B,H,J,K],[B,J],[B,J,K],[B,K],[C,D,E,H,J],[C,D,E,H,J,K],[C,D,E,J],[C,D,E,J,K],[C,D,H,J],[C,D,H,J,K],[C,D,J],[C,D,J,K],[C,E,H,J],[C,E,H,J,K],[C,E,J],[C,E,J,K],[C,H,J],[C,H,J,K],[C,J],[C,J,K],[D],[D,E,H,J],[D,E,H,J,K],[D,E,J],[D,E,J,K],[D,H,J],[D,H,J,K],[D,J],[D,J,K],[E,H,J],[E,H,J,K],[E,J],[E,J,K],[H,J],[H,J,K],[J],[J,K],[K]]),
        ground([G,I,_A]) ).

:- true pred np(B,C,D,E,F,G,H,I,_A,J,K)
   : ( mshare([[B],[C],[E],[G],[H],[_A],[K]]),
       ground([D,F,I,J]), linear(B), linear(C), linear(E), linear(G), linear(H), linear(_A), linear(K) )
   => ( mshare([[B],[B,C],[B,C,K],[B,K],[C],[G],[K]]),
        ground([D,E,F,H,I,_A,J]) ).

:- true pred np(B,C,D,E,F,G,H,I,_A,J,K)
   : ( (C=3+plu), (E=def),
       mshare([[B],[H],[_A],[K]]),
       ground([D,F,G,I,J]), linear(B), linear(H), linear(_A), linear(K) )
   => ( mshare([[B],[B,K],[K]]),
        ground([D,F,G,H,I,_A,J]) ).

:- true pred np(B,C,D,E,F,G,H,I,_A,J,K)
   : ( (C=3+plu), (E=def),
       mshare([[B],[H],[_A],[J],[K]]),
       ground([D,F,G,I]), linear(B), linear(H), linear(_A), linear(K) )
   => ( mshare([[B],[B,H,J],[B,H,J,K],[B,J],[B,J,K],[B,K],[H,J],[H,J,K],[J],[J,K],[K]]),
        ground([D,F,G,I,_A]) ).

:- true pred np(B,C,D,E,F,G,H,I,_A,J,K)
   : ( (F=compl),
       mshare([[B],[C],[E],[H],[_A],[J],[K]]),
       ground([D,G,I]), linear(B), linear(C), linear(E), linear(H), linear(_A), linear(K) )
   => ( mshare([[B],[B,C],[B,C,E,H,J],[B,C,E,H,J,K],[B,C,E,J],[B,C,E,J,K],[B,C,H,J],[B,C,H,J,K],[B,C,J],[B,C,J,K],[B,C,K],[B,E,H,J],[B,E,H,J,K],[B,E,J],[B,E,J,K],[B,H,J],[B,H,J,K],[B,J],[B,J,K],[B,K],[C],[C,E,H,J],[C,E,H,J,K],[C,E,J],[C,E,J,K],[C,H,J],[C,H,J,K],[C,J],[C,J,K],[E,H,J],[E,H,J,K],[E,J],[E,J,K],[H,J],[H,J,K],[J],[J,K],[K]]),
        ground([D,G,I,_A]) ).

:- true pred np(B,C,D,E,F,G,H,I,_A,J,K)
   : ( (F=subj),
       mshare([[B],[C],[E],[H],[_A],[K]]),
       ground([D,G,I,J]), linear(B), linear(C), linear(E), linear(H), linear(_A), linear(K) )
   => ( mshare([[B],[B,C],[B,C,K],[B,K],[C],[K]]),
        ground([D,E,G,H,I,_A,J]) ).

:- true pred np(B,C,D,E,F,G,H,I,_A,J,K)
   : ( mshare([[B],[C],[E],[H],[_A],[K]]),
       ground([D,F,G,I,J]), linear(B), linear(C), linear(E), linear(H), linear(_A), linear(K) )
   => ( mshare([[B],[B,C],[B,C,K],[B,K],[C],[K]]),
        ground([D,E,F,G,H,I,_A,J]) ).

:- true pred np(B,C,D,E,F,G,H,I,_A,J,K)
   : ( (E=def), (F=subj),
       mshare([[B],[C],[D],[H],[_A],[J],[K]]),
       ground([G,I]), linear(B), linear(C), linear(D), linear(H), linear(_A), linear(K) )
   => ( mshare([[B],[B,C],[B,C,D,H,J],[B,C,D,H,J,K],[B,C,D,J],[B,C,D,J,K],[B,C,H,J],[B,C,H,J,K],[B,C,J],[B,C,J,K],[B,C,K],[B,D,H,J],[B,D,H,J,K],[B,D,J],[B,D,J,K],[B,H,J],[B,H,J,K],[B,J],[B,J,K],[B,K],[C,D,H,J],[C,D,H,J,K],[C,D,J],[C,D,J,K],[C,H,J],[C,H,J,K],[C,J],[C,J,K],[D],[D,H,J],[D,H,J,K],[D,J],[D,J,K],[H,J],[H,J,K],[J],[J,K],[K]]),
        ground([G,I,_A]) ).

:- true pred np(B,C,D,E,F,G,H,I,_A,J,K)
   : ( (F=subj),
       mshare([[B],[C],[D],[E],[H],[_A],[J],[K]]),
       ground([G,I]), linear(B), linear(C), linear(D), linear(E), linear(H), linear(_A), linear(K) )
   => ( mshare([[B],[B,C],[B,C,D,E,H,J],[B,C,D,E,H,J,K],[B,C,D,E,J],[B,C,D,E,J,K],[B,C,D,H,J],[B,C,D,H,J,K],[B,C,D,J],[B,C,D,J,K],[B,C,E,H,J],[B,C,E,H,J,K],[B,C,E,J],[B,C,E,J,K],[B,C,H,J],[B,C,H,J,K],[B,C,J],[B,C,J,K],[B,C,K],[B,D,E,H,J],[B,D,E,H,J,K],[B,D,E,J],[B,D,E,J,K],[B,D,H,J],[B,D,H,J,K],[B,D,J],[B,D,J,K],[B,E,H,J],[B,E,H,J,K],[B,E,J],[B,E,J,K],[B,H,J],[B,H,J,K],[B,J],[B,J,K],[B,K],[C],[C,D,E,H,J],[C,D,E,H,J,K],[C,D,E,J],[C,D,E,J,K],[C,D,H,J],[C,D,H,J,K],[C,D,J],[C,D,J,K],[C,E,H,J],[C,E,H,J,K],[C,E,J],[C,E,J,K],[C,H,J],[C,H,J,K],[C,J],[C,J,K],[D],[D,E,H,J],[D,E,H,J,K],[D,E,J],[D,E,J,K],[D,H,J],[D,H,J,K],[D,J],[D,J,K],[E,H,J],[E,H,J,K],[E,J],[E,J,K],[H,J],[H,J,K],[J],[J,K],[K]]),
        ground([G,I,_A]) ).

:- true pred np(B,C,D,E,F,G,H,I,_A,J,K)
   : ( mshare([[B],[C],[E],[H],[_A],[J],[K]]),
       ground([D,F,G,I]), linear(B), linear(C), linear(E), linear(H), linear(_A), linear(K) )
   => ( mshare([[B],[B,C],[B,C,E,H,J],[B,C,E,H,J,K],[B,C,E,J],[B,C,E,J,K],[B,C,H,J],[B,C,H,J,K],[B,C,J],[B,C,J,K],[B,C,K],[B,E,H,J],[B,E,H,J,K],[B,E,J],[B,E,J,K],[B,H,J],[B,H,J,K],[B,J],[B,J,K],[B,K],[C],[C,E,H,J],[C,E,H,J,K],[C,E,J],[C,E,J,K],[C,H,J],[C,H,J,K],[C,J],[C,J,K],[E,H,J],[E,H,J,K],[E,J],[E,J,K],[H,J],[H,J,K],[J],[J,K],[K]]),
        ground([D,F,G,I,_A]) ).

np(B,C,D,E,F,G,H,I,I,J,K) :-
    true((mshare([[B],[C],[D],[E],[H],[J],[K]]),ground([F,G,I]),linear(B),linear(C),linear(D),linear(E),linear(H),linear(K);mshare([[B],[C],[D],[E],[H],[K]]),ground([F,G,I,J]),linear(B),linear(C),linear(D),linear(E),linear(H),linear(K);mshare([[B],[C],[D],[H],[J],[K]]),ground([E,F,G,I]),linear(B),linear(C),linear(D),linear(H),linear(K);mshare([[B],[C],[E],[G],[H],[K]]),ground([D,F,I,J]),linear(B),linear(C),linear(E),linear(G),linear(H),linear(K);mshare([[B],[C],[E],[H],[J],[K]]),ground([D,F,G,I]),linear(B),linear(C),linear(E),linear(H),linear(K);mshare([[B],[C],[E],[H],[K]]),ground([D,F,G,I,J]),linear(B),linear(C),linear(E),linear(H),linear(K);mshare([[B],[C,J],[D],[E],[H],[J],[K]]),ground([F,G,I]),linear(B),linear(D),linear(E),linear(H),linear(K);mshare([[B],[H],[J],[K]]),ground([C,D,E,F,G,I]),linear(B),linear(H),linear(K);mshare([[B],[H],[K]]),ground([C,D,E,F,G,I,J]),linear(B),linear(H),linear(K))),
    virtual(np(B,C,D,E,F,G,H),J,K),
    true((mshare([[B,C,D,E,H,J],[B,C,D,E,H,J,K],[B,C,D,E,J],[B,C,D,E,J,K],[B,C,D,H,J],[B,C,D,H,J,K],[B,C,D,J],[B,C,D,J,K],[B,C,E,H,J],[B,C,E,H,J,K],[B,C,E,J],[B,C,E,J,K],[B,C,H,J],[B,C,H,J,K],[B,C,J],[B,C,J,K],[B,D,E,H,J],[B,D,E,H,J,K],[B,D,E,J],[B,D,E,J,K],[B,D,H,J],[B,D,H,J,K],[B,D,J],[B,D,J,K],[B,E,H,J],[B,E,H,J,K],[B,E,J],[B,E,J,K],[B,H,J],[B,H,J,K],[B,J],[B,J,K],[C,D,E,H,J],[C,D,E,H,J,K],[C,D,E,J],[C,D,E,J,K],[C,D,H,J],[C,D,H,J,K],[C,D,J],[C,D,J,K],[C,E,H,J],[C,E,H,J,K],[C,E,J],[C,E,J,K],[C,H,J],[C,H,J,K],[C,J],[C,J,K],[D,E,H,J],[D,E,H,J,K],[D,E,J],[D,E,J,K],[D,H,J],[D,H,J,K],[D,J],[D,J,K],[E,H,J],[E,H,J,K],[E,J],[E,J,K],[H,J],[H,J,K],[J],[J,K]]),ground([F,G,I]);mshare([[B,C,D,H,J],[B,C,D,H,J,K],[B,C,D,J],[B,C,D,J,K],[B,C,H,J],[B,C,H,J,K],[B,C,J],[B,C,J,K],[B,D,H,J],[B,D,H,J,K],[B,D,J],[B,D,J,K],[B,H,J],[B,H,J,K],[B,J],[B,J,K],[C,D,H,J],[C,D,H,J,K],[C,D,J],[C,D,J,K],[C,H,J],[C,H,J,K],[C,J],[C,J,K],[D,H,J],[D,H,J,K],[D,J],[D,J,K],[H,J],[H,J,K],[J],[J,K]]),ground([E,F,G,I]);mshare([[B,C,E,H,J],[B,C,E,H,J,K],[B,C,E,J],[B,C,E,J,K],[B,C,H,J],[B,C,H,J,K],[B,C,J],[B,C,J,K],[B,E,H,J],[B,E,H,J,K],[B,E,J],[B,E,J,K],[B,H,J],[B,H,J,K],[B,J],[B,J,K],[C,E,H,J],[C,E,H,J,K],[C,E,J],[C,E,J,K],[C,H,J],[C,H,J,K],[C,J],[C,J,K],[E,H,J],[E,H,J,K],[E,J],[E,J,K],[H,J],[H,J,K],[J],[J,K]]),ground([D,F,G,I]);mshare([[B,H,J],[B,H,J,K],[B,J],[B,J,K],[H,J],[H,J,K],[J],[J,K]]),ground([C,D,E,F,G,I]);ground([B,C,D,E,F,G,H,I,J,K]))).
np(np(B,C,[]),B,D,def,E,F,G,H,I,J,K) :-
    true((mshare([[B],[D],[G],[I],[J],[K],[C],[L]]),ground([E,F,H]),linear(B),linear(D),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[B],[D],[G],[I],[K],[C],[L]]),ground([E,F,H,J]),linear(B),linear(D),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[B],[F],[G],[I],[K],[C],[L]]),ground([D,E,H,J]),linear(B),linear(F),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[B],[G],[I],[J],[K],[C],[L]]),ground([D,E,F,H]),linear(B),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[B],[G],[I],[K],[C],[L]]),ground([D,E,F,H,J]),linear(B),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[B,J],[D],[G],[I],[J],[K],[C],[L]]),ground([E,F,H]),linear(D),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[G],[I],[J],[K],[C],[L]]),ground([B,D,E,F,H]),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[G],[I],[K],[C],[L]]),ground([B,D,E,F,H,J]),linear(G),linear(I),linear(K),linear(C),linear(L))),
    is_pp(F),
    true((mshare([[B],[D],[G],[I],[J],[K],[C],[L]]),ground([E,F,H]),linear(B),linear(D),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[B],[D],[G],[I],[K],[C],[L]]),ground([E,F,H,J]),linear(B),linear(D),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[B],[F],[G],[I],[K],[C],[L]]),ground([D,E,H,J]),linear(B),linear(F),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[B],[G],[I],[J],[K],[C],[L]]),ground([D,E,F,H]),linear(B),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[B],[G],[I],[K],[C],[L]]),ground([D,E,F,H,J]),linear(B),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[B,J],[D],[G],[I],[J],[K],[C],[L]]),ground([E,F,H]),linear(D),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[G],[I],[J],[K],[C],[L]]),ground([B,D,E,F,H]),linear(G),linear(I),linear(K),linear(C),linear(L);mshare([[G],[I],[K],[C],[L]]),ground([B,D,E,F,H,J]),linear(G),linear(I),linear(K),linear(C),linear(L))),
    pers_pron(C,B,L,H,I,J,K),
    true((mshare([[B],[D],[G],[J],[J,K],[C],[L]]),ground([E,F,H,I]),linear(D),linear(G);mshare([[B],[D],[G],[C],[L]]),ground([E,F,H,I,J,K]),linear(D),linear(G);mshare([[B],[F],[G],[C],[L]]),ground([D,E,H,I,J,K]),linear(F),linear(G);mshare([[B],[G],[J],[J,K],[C],[L]]),ground([D,E,F,H,I]),linear(G);mshare([[B],[G],[C],[L]]),ground([D,E,F,H,I,J,K]),linear(G);mshare([[B,J],[B,J,K],[D],[G],[J],[J,K],[C],[L]]),ground([E,F,H,I]),linear(D),linear(G);mshare([[G],[J],[J,K],[C],[L]]),ground([B,D,E,F,H,I]),linear(G);mshare([[G],[C],[L]]),ground([B,D,E,F,H,I,J,K]),linear(G))),
    empty(G),
    true((mshare([[B],[D],[J],[J,K],[C],[L]]),ground([E,F,G,H,I]),linear(D);mshare([[B],[D],[C],[L]]),ground([E,F,G,H,I,J,K]),linear(D);mshare([[B],[F],[C],[L]]),ground([D,E,G,H,I,J,K]),linear(F);mshare([[B],[J],[J,K],[C],[L]]),ground([D,E,F,G,H,I]);mshare([[B],[C],[L]]),ground([D,E,F,G,H,I,J,K]);mshare([[B,J],[B,J,K],[D],[J],[J,K],[C],[L]]),ground([E,F,G,H,I]),linear(D);mshare([[J],[J,K],[C],[L]]),ground([B,D,E,F,G,H,I]);mshare([[C],[L]]),ground([B,D,E,F,G,H,I,J,K]))),
    role(L,decl,D),
    true((mshare([[B],[D],[J],[J,K],[C]]),ground([E,F,G,H,I,L]);mshare([[B],[D],[C]]),ground([E,F,G,H,I,J,K,L]);mshare([[B],[F],[C]]),ground([D,E,G,H,I,J,K,L]),linear(F);mshare([[B],[J],[J,K],[C]]),ground([D,E,F,G,H,I,L]);mshare([[B],[C]]),ground([D,E,F,G,H,I,J,K,L]);mshare([[B,J],[B,J,K],[D],[J],[J,K],[C]]),ground([E,F,G,H,I,L]);mshare([[J],[J,K],[C]]),ground([B,D,E,F,G,H,I,L]);mshare([[C]]),ground([B,D,E,F,G,H,I,J,K,L]))).
np(np(B,C,D),B,E,F,G,H,I,J,K,L,M) :-
    true((mshare([[B],[E],[F],[I],[K],[L],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([G,H,J]),linear(B),linear(E),linear(F),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[B],[E],[F],[I],[K],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([G,H,J,L]),linear(B),linear(E),linear(F),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[B],[E],[I],[K],[L],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([F,G,H,J]),linear(B),linear(E),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[B],[F],[H],[I],[K],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([E,G,J,L]),linear(B),linear(F),linear(H),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[B],[F],[I],[K],[L],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([E,G,H,J]),linear(B),linear(F),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[B],[F],[I],[K],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([E,G,H,J,L]),linear(B),linear(F),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[B,L],[E],[F],[I],[K],[L],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([G,H,J]),linear(E),linear(F),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[I],[K],[L],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([B,E,F,G,H,J]),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[I],[K],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([B,E,F,G,H,J,L]),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R))),
    is_pp(H),
    true((mshare([[B],[E],[F],[I],[K],[L],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([G,H,J]),linear(B),linear(E),linear(F),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[B],[E],[F],[I],[K],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([G,H,J,L]),linear(B),linear(E),linear(F),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[B],[E],[I],[K],[L],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([F,G,H,J]),linear(B),linear(E),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[B],[F],[H],[I],[K],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([E,G,J,L]),linear(B),linear(F),linear(H),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[B],[F],[I],[K],[L],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([E,G,H,J]),linear(B),linear(F),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[B],[F],[I],[K],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([E,G,H,J,L]),linear(B),linear(F),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[B,L],[E],[F],[I],[K],[L],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([G,H,J]),linear(E),linear(F),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[I],[K],[L],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([B,E,F,G,H,J]),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R);mshare([[I],[K],[M],[C],[D],[O],[P],[Q],[N],[R]]),ground([B,E,F,G,H,J,L]),linear(I),linear(K),linear(M),linear(C),linear(D),linear(O),linear(P),linear(Q),linear(N),linear(R))),
    np_head(C,B,F+N,O,D,J,P,L,Q),
    true((mshare([[B],[B,F,L],[B,F,L,C],[B,F,L,C,D],[B,F,L,C,D,Q],[B,F,L,C,D,Q,N],[B,F,L,C,D,N],[B,F,L,C,Q],[B,F,L,C,Q,N],[B,F,L,C,N],[B,F,L,D],[B,F,L,D,Q],[B,F,L,D,Q,N],[B,F,L,D,N],[B,F,L,Q],[B,F,L,Q,N],[B,F,L,N],[B,L],[B,L,C],[B,L,C,D],[B,L,C,D,Q],[B,L,C,D,Q,N],[B,L,C,D,N],[B,L,C,Q],[B,L,C,Q,N],[B,L,C,N],[B,L,D],[B,L,D,Q],[B,L,D,Q,N],[B,L,D,N],[B,L,Q],[B,L,Q,N],[B,L,N],[B,C],[B,C,D],[B,D],[E],[F,L],[F,L,C],[F,L,C,D],[F,L,C,D,Q],[F,L,C,D,Q,N],[F,L,C,D,N],[F,L,C,Q],[F,L,C,Q,N],[F,L,C,N],[F,L,D],[F,L,D,Q],[F,L,D,Q,N],[F,L,D,N],[F,L,Q],[F,L,Q,N],[F,L,N],[I],[K],[L],[L,C],[L,C,D],[L,C,D,Q],[L,C,D,Q,N],[L,C,D,N],[L,C,Q],[L,C,Q,N],[L,C,N],[L,D],[L,D,Q],[L,D,Q,N],[L,D,N],[L,Q],[L,Q,N],[L,N],[M],[C],[C,D],[D],[D,O],[R]]),ground([G,H,J,P]),linear(E),linear(I),linear(K),linear(M),linear(O),linear(R);mshare([[B],[B,F,L],[B,F,L,C],[B,F,L,C,D],[B,F,L,C,D,Q],[B,F,L,C,D,Q,N],[B,F,L,C,D,N],[B,F,L,C,Q],[B,F,L,C,Q,N],[B,F,L,C,N],[B,F,L,D],[B,F,L,D,Q],[B,F,L,D,Q,N],[B,F,L,D,N],[B,F,L,Q],[B,F,L,Q,N],[B,F,L,N],[B,L],[B,L,C],[B,L,C,D],[B,L,C,D,Q],[B,L,C,D,Q,N],[B,L,C,D,N],[B,L,C,Q],[B,L,C,Q,N],[B,L,C,N],[B,L,D],[B,L,D,Q],[B,L,D,Q,N],[B,L,D,N],[B,L,Q],[B,L,Q,N],[B,L,N],[B,C],[B,C,D],[B,D],[F,L],[F,L,C],[F,L,C,D],[F,L,C,D,Q],[F,L,C,D,Q,N],[F,L,C,D,N],[F,L,C,Q],[F,L,C,Q,N],[F,L,C,N],[F,L,D],[F,L,D,Q],[F,L,D,Q,N],[F,L,D,N],[F,L,Q],[F,L,Q,N],[F,L,N],[I],[K],[L],[L,C],[L,C,D],[L,C,D,Q],[L,C,D,Q,N],[L,C,D,N],[L,C,Q],[L,C,Q,N],[L,C,N],[L,D],[L,D,Q],[L,D,Q,N],[L,D,N],[L,Q],[L,Q,N],[L,N],[M],[C],[C,D],[D],[D,O],[R]]),ground([E,G,H,J,P]),linear(I),linear(K),linear(M),linear(O),linear(R);mshare([[B],[B,L],[B,L,C],[B,L,C,D],[B,L,C,D,Q],[B,L,C,D,Q,N],[B,L,C,D,N],[B,L,C,Q],[B,L,C,Q,N],[B,L,C,N],[B,L,D],[B,L,D,Q],[B,L,D,Q,N],[B,L,D,N],[B,L,Q],[B,L,Q,N],[B,L,N],[B,C],[B,C,D],[B,D],[E],[I],[K],[L],[L,C],[L,C,D],[L,C,D,Q],[L,C,D,Q,N],[L,C,D,N],[L,C,Q],[L,C,Q,N],[L,C,N],[L,D],[L,D,Q],[L,D,Q,N],[L,D,N],[L,Q],[L,Q,N],[L,N],[M],[C],[C,D],[D],[D,O],[R]]),ground([F,G,H,J,P]),linear(E),linear(I),linear(K),linear(M),linear(O),linear(R);mshare([[B],[B,C],[E],[I],[K],[M],[C],[D],[D,O],[R]]),ground([F,G,H,J,L,P,Q,N]),linear(E),linear(I),linear(K),linear(M),linear(O),linear(R);mshare([[B],[B,C],[H],[I],[K],[M],[C],[D],[D,O],[R]]),ground([E,F,G,J,L,P,Q,N]),linear(H),linear(I),linear(K),linear(M),linear(O),linear(R);mshare([[B],[B,C],[I],[K],[M],[C],[D],[D,O],[R]]),ground([E,F,G,H,J,L,P,Q,N]),linear(I),linear(K),linear(M),linear(O),linear(R);mshare([[B,F,L],[B,F,L,C],[B,F,L,C,D],[B,F,L,C,D,Q],[B,F,L,C,D,Q,N],[B,F,L,C,D,N],[B,F,L,C,Q],[B,F,L,C,Q,N],[B,F,L,C,N],[B,F,L,D],[B,F,L,D,Q],[B,F,L,D,Q,N],[B,F,L,D,N],[B,F,L,Q],[B,F,L,Q,N],[B,F,L,N],[B,L],[B,L,C],[B,L,C,D],[B,L,C,D,Q],[B,L,C,D,Q,N],[B,L,C,D,N],[B,L,C,Q],[B,L,C,Q,N],[B,L,C,N],[B,L,D],[B,L,D,Q],[B,L,D,Q,N],[B,L,D,N],[B,L,Q],[B,L,Q,N],[B,L,N],[E],[F,L],[F,L,C],[F,L,C,D],[F,L,C,D,Q],[F,L,C,D,Q,N],[F,L,C,D,N],[F,L,C,Q],[F,L,C,Q,N],[F,L,C,N],[F,L,D],[F,L,D,Q],[F,L,D,Q,N],[F,L,D,N],[F,L,Q],[F,L,Q,N],[F,L,N],[I],[K],[L],[L,C],[L,C,D],[L,C,D,Q],[L,C,D,Q,N],[L,C,D,N],[L,C,Q],[L,C,Q,N],[L,C,N],[L,D],[L,D,Q],[L,D,Q,N],[L,D,N],[L,Q],[L,Q,N],[L,N],[M],[C],[C,D],[D],[D,O],[R]]),ground([G,H,J,P]),linear(E),linear(I),linear(K),linear(M),linear(O),linear(R);mshare([[I],[K],[L],[L,C],[L,C,D],[L,C,D,Q],[L,C,D,Q,N],[L,C,D,N],[L,C,Q],[L,C,Q,N],[L,C,N],[L,D],[L,D,Q],[L,D,Q,N],[L,D,N],[L,Q],[L,Q,N],[L,N],[M],[C],[C,D],[D],[D,O],[R]]),ground([B,E,F,G,H,J,P]),linear(I),linear(K),linear(M),linear(O),linear(R);mshare([[I],[K],[M],[C],[D],[D,O],[R]]),ground([B,E,F,G,H,J,L,P,Q,N]),linear(I),linear(K),linear(M),linear(O),linear(R))),
    np_all(R),
    true((mshare([[B],[B,F,L],[B,F,L,C],[B,F,L,C,D],[B,F,L,C,D,Q],[B,F,L,C,D,Q,N],[B,F,L,C,D,N],[B,F,L,C,Q],[B,F,L,C,Q,N],[B,F,L,C,N],[B,F,L,D],[B,F,L,D,Q],[B,F,L,D,Q,N],[B,F,L,D,N],[B,F,L,Q],[B,F,L,Q,N],[B,F,L,N],[B,L],[B,L,C],[B,L,C,D],[B,L,C,D,Q],[B,L,C,D,Q,N],[B,L,C,D,N],[B,L,C,Q],[B,L,C,Q,N],[B,L,C,N],[B,L,D],[B,L,D,Q],[B,L,D,Q,N],[B,L,D,N],[B,L,Q],[B,L,Q,N],[B,L,N],[B,C],[B,C,D],[B,D],[E],[F,L],[F,L,C],[F,L,C,D],[F,L,C,D,Q],[F,L,C,D,Q,N],[F,L,C,D,N],[F,L,C,Q],[F,L,C,Q,N],[F,L,C,N],[F,L,D],[F,L,D,Q],[F,L,D,Q,N],[F,L,D,N],[F,L,Q],[F,L,Q,N],[F,L,N],[I],[K],[L],[L,C],[L,C,D],[L,C,D,Q],[L,C,D,Q,N],[L,C,D,N],[L,C,Q],[L,C,Q,N],[L,C,N],[L,D],[L,D,Q],[L,D,Q,N],[L,D,N],[L,Q],[L,Q,N],[L,N],[M],[C],[C,D],[D],[D,O]]),ground([G,H,J,P,R]),linear(E),linear(I),linear(K),linear(M),linear(O);mshare([[B],[B,F,L],[B,F,L,C],[B,F,L,C,D],[B,F,L,C,D,Q],[B,F,L,C,D,Q,N],[B,F,L,C,D,N],[B,F,L,C,Q],[B,F,L,C,Q,N],[B,F,L,C,N],[B,F,L,D],[B,F,L,D,Q],[B,F,L,D,Q,N],[B,F,L,D,N],[B,F,L,Q],[B,F,L,Q,N],[B,F,L,N],[B,L],[B,L,C],[B,L,C,D],[B,L,C,D,Q],[B,L,C,D,Q,N],[B,L,C,D,N],[B,L,C,Q],[B,L,C,Q,N],[B,L,C,N],[B,L,D],[B,L,D,Q],[B,L,D,Q,N],[B,L,D,N],[B,L,Q],[B,L,Q,N],[B,L,N],[B,C],[B,C,D],[B,D],[F,L],[F,L,C],[F,L,C,D],[F,L,C,D,Q],[F,L,C,D,Q,N],[F,L,C,D,N],[F,L,C,Q],[F,L,C,Q,N],[F,L,C,N],[F,L,D],[F,L,D,Q],[F,L,D,Q,N],[F,L,D,N],[F,L,Q],[F,L,Q,N],[F,L,N],[I],[K],[L],[L,C],[L,C,D],[L,C,D,Q],[L,C,D,Q,N],[L,C,D,N],[L,C,Q],[L,C,Q,N],[L,C,N],[L,D],[L,D,Q],[L,D,Q,N],[L,D,N],[L,Q],[L,Q,N],[L,N],[M],[C],[C,D],[D],[D,O]]),ground([E,G,H,J,P,R]),linear(I),linear(K),linear(M),linear(O);mshare([[B],[B,L],[B,L,C],[B,L,C,D],[B,L,C,D,Q],[B,L,C,D,Q,N],[B,L,C,D,N],[B,L,C,Q],[B,L,C,Q,N],[B,L,C,N],[B,L,D],[B,L,D,Q],[B,L,D,Q,N],[B,L,D,N],[B,L,Q],[B,L,Q,N],[B,L,N],[B,C],[B,C,D],[B,D],[E],[I],[K],[L],[L,C],[L,C,D],[L,C,D,Q],[L,C,D,Q,N],[L,C,D,N],[L,C,Q],[L,C,Q,N],[L,C,N],[L,D],[L,D,Q],[L,D,Q,N],[L,D,N],[L,Q],[L,Q,N],[L,N],[M],[C],[C,D],[D],[D,O]]),ground([F,G,H,J,P,R]),linear(E),linear(I),linear(K),linear(M),linear(O);mshare([[B],[B,C],[E],[I],[K],[M],[C],[D],[D,O]]),ground([F,G,H,J,L,P,Q,N,R]),linear(E),linear(I),linear(K),linear(M),linear(O);mshare([[B],[B,C],[H],[I],[K],[M],[C],[D],[D,O]]),ground([E,F,G,J,L,P,Q,N,R]),linear(H),linear(I),linear(K),linear(M),linear(O);mshare([[B],[B,C],[I],[K],[M],[C],[D],[D,O]]),ground([E,F,G,H,J,L,P,Q,N,R]),linear(I),linear(K),linear(M),linear(O);mshare([[B,F,L],[B,F,L,C],[B,F,L,C,D],[B,F,L,C,D,Q],[B,F,L,C,D,Q,N],[B,F,L,C,D,N],[B,F,L,C,Q],[B,F,L,C,Q,N],[B,F,L,C,N],[B,F,L,D],[B,F,L,D,Q],[B,F,L,D,Q,N],[B,F,L,D,N],[B,F,L,Q],[B,F,L,Q,N],[B,F,L,N],[B,L],[B,L,C],[B,L,C,D],[B,L,C,D,Q],[B,L,C,D,Q,N],[B,L,C,D,N],[B,L,C,Q],[B,L,C,Q,N],[B,L,C,N],[B,L,D],[B,L,D,Q],[B,L,D,Q,N],[B,L,D,N],[B,L,Q],[B,L,Q,N],[B,L,N],[E],[F,L],[F,L,C],[F,L,C,D],[F,L,C,D,Q],[F,L,C,D,Q,N],[F,L,C,D,N],[F,L,C,Q],[F,L,C,Q,N],[F,L,C,N],[F,L,D],[F,L,D,Q],[F,L,D,Q,N],[F,L,D,N],[F,L,Q],[F,L,Q,N],[F,L,N],[I],[K],[L],[L,C],[L,C,D],[L,C,D,Q],[L,C,D,Q,N],[L,C,D,N],[L,C,Q],[L,C,Q,N],[L,C,N],[L,D],[L,D,Q],[L,D,Q,N],[L,D,N],[L,Q],[L,Q,N],[L,N],[M],[C],[C,D],[D],[D,O]]),ground([G,H,J,P,R]),linear(E),linear(I),linear(K),linear(M),linear(O);mshare([[I],[K],[L],[L,C],[L,C,D],[L,C,D,Q],[L,C,D,Q,N],[L,C,D,N],[L,C,Q],[L,C,Q,N],[L,C,N],[L,D],[L,D,Q],[L,D,Q,N],[L,D,N],[L,Q],[L,Q,N],[L,N],[M],[C],[C,D],[D],[D,O]]),ground([B,E,F,G,H,J,P,R]),linear(I),linear(K),linear(M),linear(O);mshare([[I],[K],[M],[C],[D],[D,O]]),ground([B,E,F,G,H,J,L,P,Q,N,R]),linear(I),linear(K),linear(M),linear(O))),
    np_compls(N,B,G,O,R,I,P,K,Q,M),
    true((mshare([[B],[B,F,L],[B,F,L,M],[B,F,L,M,C],[B,F,L,M,C,D],[B,F,L,M,C,D,O],[B,F,L,M,C,D,O,Q],[B,F,L,M,C,D,Q],[B,F,L,M,C,Q],[B,F,L,M,D],[B,F,L,M,D,O],[B,F,L,M,D,O,Q],[B,F,L,M,D,Q],[B,F,L,M,Q],[B,F,L,C],[B,F,L,C,D],[B,F,L,C,D,O],[B,F,L,C,D,O,Q],[B,F,L,C,D,Q],[B,F,L,C,Q],[B,F,L,D],[B,F,L,D,O],[B,F,L,D,O,Q],[B,F,L,D,Q],[B,F,L,Q],[B,L],[B,L,M],[B,L,M,C],[B,L,M,C,D],[B,L,M,C,D,O],[B,L,M,C,D,O,Q],[B,L,M,C,D,Q],[B,L,M,C,Q],[B,L,M,D],[B,L,M,D,O],[B,L,M,D,O,Q],[B,L,M,D,Q],[B,L,M,Q],[B,L,C],[B,L,C,D],[B,L,C,D,O],[B,L,C,D,O,Q],[B,L,C,D,Q],[B,L,C,Q],[B,L,D],[B,L,D,O],[B,L,D,O,Q],[B,L,D,Q],[B,L,Q],[B,M],[B,M,C],[B,M,C,D],[B,M,C,D,O],[B,M,D],[B,M,D,O],[B,C],[B,C,D],[B,C,D,O],[B,D],[B,D,O],[E],[F,L],[F,L,M,C,D,O,Q],[F,L,M,C,D,Q],[F,L,M,C,Q],[F,L,M,D,O,Q],[F,L,M,D,Q],[F,L,M,Q],[F,L,C],[F,L,C,D],[F,L,C,D,O,Q],[F,L,C,D,Q],[F,L,C,Q],[F,L,D],[F,L,D,O,Q],[F,L,D,Q],[F,L,Q],[L],[L,M,C,D,O,Q],[L,M,C,D,Q],[L,M,C,Q],[L,M,D,O,Q],[L,M,D,Q],[L,M,Q],[L,C],[L,C,D],[L,C,D,O,Q],[L,C,D,Q],[L,C,Q],[L,D],[L,D,O,Q],[L,D,Q],[L,Q],[M],[M,D,O],[C],[C,D],[D],[D,O]]),ground([G,H,I,J,K,P,N,R]),linear(E);mshare([[B],[B,F,L],[B,F,L,M],[B,F,L,M,C],[B,F,L,M,C,D],[B,F,L,M,C,D,O],[B,F,L,M,C,D,O,Q],[B,F,L,M,C,D,Q],[B,F,L,M,C,Q],[B,F,L,M,D],[B,F,L,M,D,O],[B,F,L,M,D,O,Q],[B,F,L,M,D,Q],[B,F,L,M,Q],[B,F,L,C],[B,F,L,C,D],[B,F,L,C,D,O],[B,F,L,C,D,O,Q],[B,F,L,C,D,Q],[B,F,L,C,Q],[B,F,L,D],[B,F,L,D,O],[B,F,L,D,O,Q],[B,F,L,D,Q],[B,F,L,Q],[B,L],[B,L,M],[B,L,M,C],[B,L,M,C,D],[B,L,M,C,D,O],[B,L,M,C,D,O,Q],[B,L,M,C,D,Q],[B,L,M,C,Q],[B,L,M,D],[B,L,M,D,O],[B,L,M,D,O,Q],[B,L,M,D,Q],[B,L,M,Q],[B,L,C],[B,L,C,D],[B,L,C,D,O],[B,L,C,D,O,Q],[B,L,C,D,Q],[B,L,C,Q],[B,L,D],[B,L,D,O],[B,L,D,O,Q],[B,L,D,Q],[B,L,Q],[B,M],[B,M,C],[B,M,C,D],[B,M,C,D,O],[B,M,D],[B,M,D,O],[B,C],[B,C,D],[B,C,D,O],[B,D],[B,D,O],[F,L],[F,L,M,C,D,O,Q],[F,L,M,C,D,Q],[F,L,M,C,Q],[F,L,M,D,O,Q],[F,L,M,D,Q],[F,L,M,Q],[F,L,C],[F,L,C,D],[F,L,C,D,O,Q],[F,L,C,D,Q],[F,L,C,Q],[F,L,D],[F,L,D,O,Q],[F,L,D,Q],[F,L,Q],[L],[L,M,C,D,O,Q],[L,M,C,D,Q],[L,M,C,Q],[L,M,D,O,Q],[L,M,D,Q],[L,M,Q],[L,C],[L,C,D],[L,C,D,O,Q],[L,C,D,Q],[L,C,Q],[L,D],[L,D,O,Q],[L,D,Q],[L,Q],[M],[M,D,O],[C],[C,D],[D],[D,O]]),ground([E,G,H,I,J,K,P,N,R]);mshare([[B],[B,L],[B,L,M],[B,L,M,C],[B,L,M,C,D],[B,L,M,C,D,O],[B,L,M,C,D,O,Q],[B,L,M,C,D,Q],[B,L,M,C,Q],[B,L,M,D],[B,L,M,D,O],[B,L,M,D,O,Q],[B,L,M,D,Q],[B,L,M,Q],[B,L,C],[B,L,C,D],[B,L,C,D,O],[B,L,C,D,O,Q],[B,L,C,D,Q],[B,L,C,Q],[B,L,D],[B,L,D,O],[B,L,D,O,Q],[B,L,D,Q],[B,L,Q],[B,M],[B,M,C],[B,M,C,D],[B,M,C,D,O],[B,M,D],[B,M,D,O],[B,C],[B,C,D],[B,C,D,O],[B,D],[B,D,O],[E],[L],[L,M,C,D,O,Q],[L,M,C,D,Q],[L,M,C,Q],[L,M,D,O,Q],[L,M,D,Q],[L,M,Q],[L,C],[L,C,D],[L,C,D,O,Q],[L,C,D,Q],[L,C,Q],[L,D],[L,D,O,Q],[L,D,Q],[L,Q],[M],[M,D,O],[C],[C,D],[D],[D,O]]),ground([F,G,H,I,J,K,P,N,R]),linear(E);mshare([[B],[B,M],[B,M,C],[B,M,C,D,O],[B,M,D,O],[B,C],[B,C,D,O],[B,D,O],[E],[M],[M,D,O],[C],[D],[D,O]]),ground([F,G,H,I,J,K,L,P,Q,N,R]),linear(E);mshare([[B],[B,M],[B,M,C],[B,M,C,D,O],[B,M,D,O],[B,C],[B,C,D,O],[B,D,O],[H],[M],[M,D,O],[C],[D],[D,O]]),ground([E,F,G,I,J,K,L,P,Q,N,R]),linear(H);mshare([[B],[B,M],[B,M,C],[B,M,C,D,O],[B,M,D,O],[B,C],[B,C,D,O],[B,D,O],[M],[M,D,O],[C],[D],[D,O]]),ground([E,F,G,H,I,J,K,L,P,Q,N,R]);mshare([[B,F,L],[B,F,L,M],[B,F,L,M,C],[B,F,L,M,C,D],[B,F,L,M,C,D,O],[B,F,L,M,C,D,O,Q],[B,F,L,M,C,D,Q],[B,F,L,M,C,Q],[B,F,L,M,D],[B,F,L,M,D,O],[B,F,L,M,D,O,Q],[B,F,L,M,D,Q],[B,F,L,M,Q],[B,F,L,C],[B,F,L,C,D],[B,F,L,C,D,O],[B,F,L,C,D,O,Q],[B,F,L,C,D,Q],[B,F,L,C,Q],[B,F,L,D],[B,F,L,D,O],[B,F,L,D,O,Q],[B,F,L,D,Q],[B,F,L,Q],[B,L],[B,L,M],[B,L,M,C],[B,L,M,C,D],[B,L,M,C,D,O],[B,L,M,C,D,O,Q],[B,L,M,C,D,Q],[B,L,M,C,Q],[B,L,M,D],[B,L,M,D,O],[B,L,M,D,O,Q],[B,L,M,D,Q],[B,L,M,Q],[B,L,C],[B,L,C,D],[B,L,C,D,O],[B,L,C,D,O,Q],[B,L,C,D,Q],[B,L,C,Q],[B,L,D],[B,L,D,O],[B,L,D,O,Q],[B,L,D,Q],[B,L,Q],[E],[F,L],[F,L,M,C,D,O,Q],[F,L,M,C,D,Q],[F,L,M,C,Q],[F,L,M,D,O,Q],[F,L,M,D,Q],[F,L,M,Q],[F,L,C],[F,L,C,D],[F,L,C,D,O,Q],[F,L,C,D,Q],[F,L,C,Q],[F,L,D],[F,L,D,O,Q],[F,L,D,Q],[F,L,Q],[L],[L,M,C,D,O,Q],[L,M,C,D,Q],[L,M,C,Q],[L,M,D,O,Q],[L,M,D,Q],[L,M,Q],[L,C],[L,C,D],[L,C,D,O,Q],[L,C,D,Q],[L,C,Q],[L,D],[L,D,O,Q],[L,D,Q],[L,Q],[M],[M,D,O],[C],[C,D],[D],[D,O]]),ground([G,H,I,J,K,P,N,R]),linear(E);mshare([[L],[L,M,C,D,O,Q],[L,M,C,D,Q],[L,M,C,Q],[L,M,D,O,Q],[L,M,D,Q],[L,M,Q],[L,C],[L,C,D],[L,C,D,O,Q],[L,C,D,Q],[L,C,Q],[L,D],[L,D,O,Q],[L,D,Q],[L,Q],[M],[M,D,O],[C],[C,D],[D],[D,O]]),ground([B,E,F,G,H,I,J,K,P,N,R]);mshare([[M],[M,D,O],[C],[D],[D,O]]),ground([B,E,F,G,H,I,J,K,L,P,Q,N,R]))).
np(part(B,C),3+D,E,indef,F,G,H,I,J,K,L) :-
    true((mshare([[E],[H],[J],[K],[K,D],[L],[B],[C],[M],[N],[O],[P],[Q],[R]]),ground([F,G,I]),linear(E),linear(H),linear(J),linear(L),linear(B),linear(C),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R);mshare([[E],[H],[J],[K],[L],[B],[C],[D],[M],[N],[O],[P],[Q],[R]]),ground([F,G,I]),linear(E),linear(H),linear(J),linear(L),linear(B),linear(C),linear(D),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R);mshare([[E],[H],[J],[L],[B],[C],[D],[M],[N],[O],[P],[Q],[R]]),ground([F,G,I,K]),linear(E),linear(H),linear(J),linear(L),linear(B),linear(C),linear(D),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R);mshare([[G],[H],[J],[L],[B],[C],[D],[M],[N],[O],[P],[Q],[R]]),ground([E,F,I,K]),linear(G),linear(H),linear(J),linear(L),linear(B),linear(C),linear(D),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R);mshare([[H],[J],[K],[L],[B],[C],[D],[M],[N],[O],[P],[Q],[R]]),ground([E,F,G,I]),linear(H),linear(J),linear(L),linear(B),linear(C),linear(D),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R);mshare([[H],[J],[L],[B],[C],[D],[M],[N],[O],[P],[Q],[R]]),ground([E,F,G,I,K]),linear(H),linear(J),linear(L),linear(B),linear(C),linear(D),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R))),
    is_pp(G),
    true((mshare([[E],[H],[J],[K],[K,D],[L],[B],[C],[M],[N],[O],[P],[Q],[R]]),ground([F,G,I]),linear(E),linear(H),linear(J),linear(L),linear(B),linear(C),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R);mshare([[E],[H],[J],[K],[L],[B],[C],[D],[M],[N],[O],[P],[Q],[R]]),ground([F,G,I]),linear(E),linear(H),linear(J),linear(L),linear(B),linear(C),linear(D),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R);mshare([[E],[H],[J],[L],[B],[C],[D],[M],[N],[O],[P],[Q],[R]]),ground([F,G,I,K]),linear(E),linear(H),linear(J),linear(L),linear(B),linear(C),linear(D),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R);mshare([[G],[H],[J],[L],[B],[C],[D],[M],[N],[O],[P],[Q],[R]]),ground([E,F,I,K]),linear(G),linear(H),linear(J),linear(L),linear(B),linear(C),linear(D),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R);mshare([[H],[J],[K],[L],[B],[C],[D],[M],[N],[O],[P],[Q],[R]]),ground([E,F,G,I]),linear(H),linear(J),linear(L),linear(B),linear(C),linear(D),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R);mshare([[H],[J],[L],[B],[C],[D],[M],[N],[O],[P],[Q],[R]]),ground([E,F,G,I,K]),linear(H),linear(J),linear(L),linear(B),linear(C),linear(D),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R))),
    determiner(B,D,indef,I,M,K,N),
    true((mshare([[E],[H],[J],[K],[K,B],[K,B,D],[K,B,D,N],[K,B,N],[K,D],[K,D,N],[K,N],[L],[B,D],[C],[D],[O],[P],[Q],[R]]),ground([F,G,I,M]),linear(E),linear(H),linear(J),linear(L),linear(C),linear(O),linear(P),linear(Q),linear(R);mshare([[E],[H],[J],[K],[K,B],[K,B,D],[K,B,D,N],[K,B,N],[K,D],[K,D,N],[K,N],[L],[C],[O],[P],[Q],[R]]),ground([F,G,I,M]),linear(E),linear(H),linear(J),linear(L),linear(C),linear(O),linear(P),linear(Q),linear(R);mshare([[E],[H],[J],[L],[B,D],[C],[D],[O],[P],[Q],[R]]),ground([F,G,I,K,M,N]),linear(E),linear(H),linear(J),linear(L),linear(C),linear(O),linear(P),linear(Q),linear(R);mshare([[G],[H],[J],[L],[B,D],[C],[D],[O],[P],[Q],[R]]),ground([E,F,I,K,M,N]),linear(G),linear(H),linear(J),linear(L),linear(C),linear(O),linear(P),linear(Q),linear(R);mshare([[H],[J],[K],[K,B],[K,B,D],[K,B,D,N],[K,B,N],[K,D],[K,D,N],[K,N],[L],[B,D],[C],[D],[O],[P],[Q],[R]]),ground([E,F,G,I,M]),linear(H),linear(J),linear(L),linear(C),linear(O),linear(P),linear(Q),linear(R);mshare([[H],[J],[L],[B,D],[C],[D],[O],[P],[Q],[R]]),ground([E,F,G,I,K,M,N]),linear(H),linear(J),linear(L),linear(C),linear(O),linear(P),linear(Q),linear(R))),
    ~(of,M,O,N,P),
    true((mshare([[E],[H],[J],[K],[K,B],[K,B,D],[K,B,D,N],[K,B,D,N,P],[K,B,N],[K,B,N,P],[K,D],[K,D,N],[K,D,N,P],[K,N],[K,N,P],[L],[B,D],[C],[D],[Q],[R]]),ground([F,G,I,M,O]),linear(E),linear(H),linear(J),linear(L),linear(C),linear(Q),linear(R);mshare([[E],[H],[J],[K],[K,B],[K,B,D],[K,B,D,N],[K,B,D,N,P],[K,B,N],[K,B,N,P],[K,D],[K,D,N],[K,D,N,P],[K,N],[K,N,P],[L],[C],[Q],[R]]),ground([F,G,I,M,O]),linear(E),linear(H),linear(J),linear(L),linear(C),linear(Q),linear(R);mshare([[E],[H],[J],[L],[B,D],[C],[D],[Q],[R]]),ground([F,G,I,K,M,N,O,P]),linear(E),linear(H),linear(J),linear(L),linear(C),linear(Q),linear(R);mshare([[G],[H],[J],[L],[B,D],[C],[D],[Q],[R]]),ground([E,F,I,K,M,N,O,P]),linear(G),linear(H),linear(J),linear(L),linear(C),linear(Q),linear(R);mshare([[H],[J],[K],[K,B],[K,B,D],[K,B,D,N],[K,B,D,N,P],[K,B,N],[K,B,N,P],[K,D],[K,D,N],[K,D,N,P],[K,N],[K,N,P],[L],[B,D],[C],[D],[Q],[R]]),ground([E,F,G,I,M,O]),linear(H),linear(J),linear(L),linear(C),linear(Q),linear(R);mshare([[H],[J],[L],[B,D],[C],[D],[Q],[R]]),ground([E,F,G,I,K,M,N,O,P]),linear(H),linear(J),linear(L),linear(C),linear(Q),linear(R))),
    s_all(Q),
    true((mshare([[E],[H],[J],[K],[K,B],[K,B,D],[K,B,D,N],[K,B,D,N,P],[K,B,N],[K,B,N,P],[K,D],[K,D,N],[K,D,N,P],[K,N],[K,N,P],[L],[B,D],[C],[D],[R]]),ground([F,G,I,M,O,Q]),linear(E),linear(H),linear(J),linear(L),linear(C),linear(R);mshare([[E],[H],[J],[K],[K,B],[K,B,D],[K,B,D,N],[K,B,D,N,P],[K,B,N],[K,B,N,P],[K,D],[K,D,N],[K,D,N,P],[K,N],[K,N,P],[L],[C],[R]]),ground([F,G,I,M,O,Q]),linear(E),linear(H),linear(J),linear(L),linear(C),linear(R);mshare([[E],[H],[J],[L],[B,D],[C],[D],[R]]),ground([F,G,I,K,M,N,O,P,Q]),linear(E),linear(H),linear(J),linear(L),linear(C),linear(R);mshare([[G],[H],[J],[L],[B,D],[C],[D],[R]]),ground([E,F,I,K,M,N,O,P,Q]),linear(G),linear(H),linear(J),linear(L),linear(C),linear(R);mshare([[H],[J],[K],[K,B],[K,B,D],[K,B,D,N],[K,B,D,N,P],[K,B,N],[K,B,N,P],[K,D],[K,D,N],[K,D,N,P],[K,N],[K,N,P],[L],[B,D],[C],[D],[R]]),ground([E,F,G,I,M,O,Q]),linear(H),linear(J),linear(L),linear(C),linear(R);mshare([[H],[J],[L],[B,D],[C],[D],[R]]),ground([E,F,G,I,K,M,N,O,P,Q]),linear(H),linear(J),linear(L),linear(C),linear(R))),
    prep_case(R),
    true((mshare([[E],[H],[J],[K],[K,B],[K,B,D],[K,B,D,N],[K,B,D,N,P],[K,B,N],[K,B,N,P],[K,D],[K,D,N],[K,D,N,P],[K,N],[K,N,P],[L],[B,D],[C],[D]]),ground([F,G,I,M,O,Q,R]),linear(E),linear(H),linear(J),linear(L),linear(C);mshare([[E],[H],[J],[K],[K,B],[K,B,D],[K,B,D,N],[K,B,D,N,P],[K,B,N],[K,B,N,P],[K,D],[K,D,N],[K,D,N,P],[K,N],[K,N,P],[L],[C]]),ground([F,G,I,M,O,Q,R]),linear(E),linear(H),linear(J),linear(L),linear(C);mshare([[E],[H],[J],[L],[B,D],[C],[D]]),ground([F,G,I,K,M,N,O,P,Q,R]),linear(E),linear(H),linear(J),linear(L),linear(C);mshare([[G],[H],[J],[L],[B,D],[C],[D]]),ground([E,F,I,K,M,N,O,P,Q,R]),linear(G),linear(H),linear(J),linear(L),linear(C);mshare([[H],[J],[K],[K,B],[K,B,D],[K,B,D,N],[K,B,D,N,P],[K,B,N],[K,B,N,P],[K,D],[K,D,N],[K,D,N,P],[K,N],[K,N,P],[L],[B,D],[C],[D]]),ground([E,F,G,I,M,O,Q,R]),linear(H),linear(J),linear(L),linear(C);mshare([[H],[J],[L],[B,D],[C],[D]]),ground([E,F,G,I,K,M,N,O,P,Q,R]),linear(H),linear(J),linear(L),linear(C))),
    np(C,3+plu,R,def,F,Q,H,O,J,P,L),
    true((mshare([[E],[H,K,L,B,C,D,N,P],[H,K,L,B,C,N,P],[H,K,L,B,D,N,P],[H,K,L,B,N,P],[H,K,L,C,D,N,P],[H,K,L,C,N,P],[H,K,L,D,N,P],[H,K,L,N,P],[H,K,B,C,D,N,P],[H,K,B,C,N,P],[H,K,B,D,N,P],[H,K,B,N,P],[H,K,C,D,N,P],[H,K,C,N,P],[H,K,D,N,P],[H,K,N,P],[K],[K,L,B,C,D,N,P],[K,L,B,C,N,P],[K,L,B,D,N,P],[K,L,B,N,P],[K,L,C,D,N,P],[K,L,C,N,P],[K,L,D,N,P],[K,L,N,P],[K,B],[K,B,C,D,N,P],[K,B,C,N,P],[K,B,D],[K,B,D,N],[K,B,D,N,P],[K,B,N],[K,B,N,P],[K,C,D,N,P],[K,C,N,P],[K,D],[K,D,N],[K,D,N,P],[K,N],[K,N,P],[L],[L,C],[B,D],[C],[D]]),ground([F,G,I,J,M,O,Q,R]),linear(E);mshare([[E],[H,K,L,B,C,D,N,P],[H,K,L,B,C,N,P],[H,K,L,B,D,N,P],[H,K,L,B,N,P],[H,K,L,C,D,N,P],[H,K,L,C,N,P],[H,K,L,D,N,P],[H,K,L,N,P],[H,K,B,C,D,N,P],[H,K,B,C,N,P],[H,K,B,D,N,P],[H,K,B,N,P],[H,K,C,D,N,P],[H,K,C,N,P],[H,K,D,N,P],[H,K,N,P],[K],[K,L,B,C,D,N,P],[K,L,B,C,N,P],[K,L,B,D,N,P],[K,L,B,N,P],[K,L,C,D,N,P],[K,L,C,N,P],[K,L,D,N,P],[K,L,N,P],[K,B],[K,B,C,D,N,P],[K,B,C,N,P],[K,B,D],[K,B,D,N],[K,B,D,N,P],[K,B,N],[K,B,N,P],[K,C,D,N,P],[K,C,N,P],[K,D],[K,D,N],[K,D,N,P],[K,N],[K,N,P],[L],[L,C],[C]]),ground([F,G,I,J,M,O,Q,R]),linear(E);mshare([[E],[L],[L,C],[B,D],[C],[D]]),ground([F,G,H,I,J,K,M,N,O,P,Q,R]),linear(E);mshare([[G],[L],[L,C],[B,D],[C],[D]]),ground([E,F,H,I,J,K,M,N,O,P,Q,R]),linear(G);mshare([[H,K,L,B,C,D,N,P],[H,K,L,B,C,N,P],[H,K,L,B,D,N,P],[H,K,L,B,N,P],[H,K,L,C,D,N,P],[H,K,L,C,N,P],[H,K,L,D,N,P],[H,K,L,N,P],[H,K,B,C,D,N,P],[H,K,B,C,N,P],[H,K,B,D,N,P],[H,K,B,N,P],[H,K,C,D,N,P],[H,K,C,N,P],[H,K,D,N,P],[H,K,N,P],[K],[K,L,B,C,D,N,P],[K,L,B,C,N,P],[K,L,B,D,N,P],[K,L,B,N,P],[K,L,C,D,N,P],[K,L,C,N,P],[K,L,D,N,P],[K,L,N,P],[K,B],[K,B,C,D,N,P],[K,B,C,N,P],[K,B,D],[K,B,D,N],[K,B,D,N,P],[K,B,N],[K,B,N,P],[K,C,D,N,P],[K,C,N,P],[K,D],[K,D,N],[K,D,N,P],[K,N],[K,N,P],[L],[L,C],[B,D],[C],[D]]),ground([E,F,G,I,J,M,O,Q,R]);mshare([[L],[L,C],[B,D],[C],[D]]),ground([E,F,G,H,I,J,K,M,N,O,P,Q,R]))).

:- true pred variable_q(B,C,D,E,F,G,H,_A)
   : ( mshare([[B],[C],[D],[E],[G],[H],[_A]]),
       ground([F]), linear(B), linear(C), linear(D), linear(E), linear(G), linear(_A) )
   => ( mshare([[B],[B,C],[B,C,H],[B,C,H,_A],[B,C,_A],[B,H],[B,H,_A],[B,_A],[C],[C,H],[C,H,_A],[C,_A],[E],[E,_A],[H],[H,_A],[_A]]),
        ground([D,F,G]) ).

:- true pred variable_q(B,C,D,E,F,G,H,_A)
   : ( mshare([[B],[C],[D],[E],[G],[_A]]),
       ground([F,H]), linear(B), linear(C), linear(D), linear(E), linear(G), linear(_A) )
   => ( mshare([[B],[B,C],[B,C,_A],[B,_A],[C],[C,_A],[E],[E,_A],[_A]]),
        ground([D,F,G,H]) ).

variable_q(B,C,D,E,F,G,H,x(gap,nonterminal,np(I,C,E,J,K,L,M),N)) :-
    true((mshare([[B],[C],[D],[E],[G],[H],[N],[I],[J],[K],[L],[M]]),ground([F]),linear(B),linear(C),linear(D),linear(E),linear(G),linear(N),linear(I),linear(J),linear(K),linear(L),linear(M);mshare([[B],[C],[D],[E],[G],[N],[I],[J],[K],[L],[M]]),ground([F,H]),linear(B),linear(C),linear(D),linear(E),linear(G),linear(N),linear(I),linear(J),linear(K),linear(L),linear(M))),
    whq(B,C,I,D,F,G,H,N),
    true((mshare([[B],[B,C],[B,C,H],[B,C,H,N],[B,C,H,N,I],[B,C,H,I],[B,C,N],[B,C,N,I],[B,C,I],[B,H],[B,H,N],[B,H,N,I],[B,H,I],[B,N],[B,N,I],[B,I],[C],[C,H],[C,H,N],[C,H,N,I],[C,H,I],[C,N],[C,N,I],[C,I],[E],[H],[H,N],[H,N,I],[H,I],[N],[N,I],[I],[J],[K],[L],[M]]),ground([D,F,G]),linear(E),linear(J),linear(K),linear(L),linear(M);mshare([[B],[B,C],[B,C,N],[B,C,N,I],[B,C,I],[B,N],[B,N,I],[B,I],[C],[C,N],[C,N,I],[C,I],[E],[N],[N,I],[I],[J],[K],[L],[M]]),ground([D,F,G,H]),linear(E),linear(J),linear(K),linear(L),linear(M))),
    trace1(L,M),
    true((mshare([[B],[B,C],[B,C,H],[B,C,H,N],[B,C,H,N,I],[B,C,H,I],[B,C,N],[B,C,N,I],[B,C,I],[B,H],[B,H,N],[B,H,N,I],[B,H,I],[B,N],[B,N,I],[B,I],[C],[C,H],[C,H,N],[C,H,N,I],[C,H,I],[C,N],[C,N,I],[C,I],[E],[H],[H,N],[H,N,I],[H,I],[N],[N,I],[I],[J],[K],[L]]),ground([D,F,G,M]),linear(E),linear(J),linear(K),linear(L);mshare([[B],[B,C],[B,C,N],[B,C,N,I],[B,C,I],[B,N],[B,N,I],[B,I],[C],[C,N],[C,N,I],[C,I],[E],[N],[N,I],[I],[J],[K],[L]]),ground([D,F,G,H,M]),linear(E),linear(J),linear(K),linear(L))).
variable_q(B,C,compl,D,E,F,G,x(gap,nonterminal,pp(pp(H,I),compl,J,K),L)) :-
    true((mshare([[B],[C],[D],[F],[G],[L],[J],[K],[H],[I],[M],[N],[O]]),ground([E]),linear(B),linear(C),linear(D),linear(F),linear(L),linear(J),linear(K),linear(H),linear(I),linear(M),linear(N),linear(O);mshare([[B],[C],[D],[F],[L],[J],[K],[H],[I],[M],[N],[O]]),ground([E,G]),linear(B),linear(C),linear(D),linear(F),linear(L),linear(J),linear(K),linear(H),linear(I),linear(M),linear(N),linear(O))),
    prep(H,E,M,G,N),
    true((mshare([[B],[C],[D],[F],[G],[G,N],[L],[J],[K],[I],[O]]),ground([E,H,M]),linear(B),linear(C),linear(D),linear(F),linear(L),linear(J),linear(K),linear(I),linear(O);mshare([[B],[C],[D],[F],[L],[J],[K],[I],[O]]),ground([E,G,H,M,N]),linear(B),linear(C),linear(D),linear(F),linear(L),linear(J),linear(K),linear(I),linear(O))),
    whq(B,C,I,O,M,F,N,L),
    true((mshare([[B],[B,C],[B,C,G,L,I,N],[B,C,G,L,N],[B,C,G,I,N],[B,C,G,N],[B,C,L],[B,C,L,I],[B,C,I],[B,G,L,I,N],[B,G,L,N],[B,G,I,N],[B,G,N],[B,L],[B,L,I],[B,I],[C],[C,G,L,I,N],[C,G,L,N],[C,G,I,N],[C,G,N],[C,L],[C,L,I],[C,I],[D],[G],[G,L,I,N],[G,L,N],[G,I,N],[G,N],[L],[L,I],[J],[K],[I]]),ground([E,F,H,M,O]),linear(D),linear(J),linear(K);mshare([[B],[B,C],[B,C,L],[B,C,L,I],[B,C,I],[B,L],[B,L,I],[B,I],[C],[C,L],[C,L,I],[C,I],[D],[L],[L,I],[J],[K],[I]]),ground([E,F,G,H,M,N,O]),linear(D),linear(J),linear(K))),
    trace1(J,K),
    true((mshare([[B],[B,C],[B,C,G,L,I,N],[B,C,G,L,N],[B,C,G,I,N],[B,C,G,N],[B,C,L],[B,C,L,I],[B,C,I],[B,G,L,I,N],[B,G,L,N],[B,G,I,N],[B,G,N],[B,L],[B,L,I],[B,I],[C],[C,G,L,I,N],[C,G,L,N],[C,G,I,N],[C,G,N],[C,L],[C,L,I],[C,I],[D],[G],[G,L,I,N],[G,L,N],[G,I,N],[G,N],[L],[L,I],[J],[I]]),ground([E,F,K,H,M,O]),linear(D),linear(J);mshare([[B],[B,C],[B,C,L],[B,C,L,I],[B,C,I],[B,L],[B,L,I],[B,I],[C],[C,L],[C,L,I],[C,I],[D],[L],[L,I],[J],[I]]),ground([E,F,G,K,H,M,N,O]),linear(D),linear(J))),
    compl_case(D),
    true((mshare([[B],[B,C],[B,C,G,L,I,N],[B,C,G,L,N],[B,C,G,I,N],[B,C,G,N],[B,C,L],[B,C,L,I],[B,C,I],[B,G,L,I,N],[B,G,L,N],[B,G,I,N],[B,G,N],[B,L],[B,L,I],[B,I],[C],[C,G,L,I,N],[C,G,L,N],[C,G,I,N],[C,G,N],[C,L],[C,L,I],[C,I],[D],[G],[G,L,I,N],[G,L,N],[G,I,N],[G,N],[L],[L,I],[J],[I]]),ground([E,F,K,H,M,O]),linear(D),linear(J);mshare([[B],[B,C],[B,C,L],[B,C,L,I],[B,C,I],[B,L],[B,L,I],[B,I],[C],[C,L],[C,L,I],[C,I],[D],[L],[L,I],[J],[I]]),ground([E,F,G,K,H,M,N,O]),linear(D),linear(J))).
variable_q(B,C,compl,D,E,F,G,x(gap,nonterminal,adv_phrase(pp(H,np(C,np_head(int_det(B),[],I),[])),J,K),L)) :-
    true((mshare([[B],[C],[D],[F],[G],[L],[J],[K],[H],[I]]),ground([E]),linear(B),linear(C),linear(D),linear(F),linear(L),linear(J),linear(K),linear(H),linear(I);mshare([[B],[C],[D],[F],[L],[J],[K],[H],[I]]),ground([E,G]),linear(B),linear(C),linear(D),linear(F),linear(L),linear(J),linear(K),linear(H),linear(I))),
    context_pron(H,I,E,F,G,L),
    true((mshare([[B],[C],[D],[G],[G,L],[J],[K]]),ground([E,F,H,I]),linear(B),linear(C),linear(D),linear(J),linear(K);mshare([[B],[C],[D],[J],[K]]),ground([E,F,G,L,H,I]),linear(B),linear(C),linear(D),linear(J),linear(K))),
    trace1(J,K),
    true((mshare([[B],[C],[D],[G],[G,L],[J]]),ground([E,F,K,H,I]),linear(B),linear(C),linear(D),linear(J);mshare([[B],[C],[D],[J]]),ground([E,F,G,L,K,H,I]),linear(B),linear(C),linear(D),linear(J))),
    verb_case(D),
    true((mshare([[B],[C],[G],[G,L],[J]]),ground([D,E,F,K,H,I]),linear(B),linear(C),linear(J);mshare([[B],[C],[J]]),ground([D,E,F,G,L,K,H,I]),linear(B),linear(C),linear(J))).
variable_q(B,C,compl,D,E,F,G,x(gap,nonterminal,predicate(adj,value(H,wh(B)),I),J)) :-
    true((mshare([[B],[C],[D],[F],[G],[J],[I],[H],[K],[L]]),ground([E]),linear(B),linear(C),linear(D),linear(F),linear(J),linear(I),linear(H),linear(K),linear(L);mshare([[B],[C],[D],[F],[J],[I],[H],[K],[L]]),ground([E,G]),linear(B),linear(C),linear(D),linear(F),linear(J),linear(I),linear(H),linear(K),linear(L))),
    ~(how,E,K,G,L),
    true((mshare([[B],[C],[D],[F],[G],[G,L],[J],[I],[H]]),ground([E,K]),linear(B),linear(C),linear(D),linear(F),linear(J),linear(I),linear(H);mshare([[B],[C],[D],[F],[J],[I],[H]]),ground([E,G,K,L]),linear(B),linear(C),linear(D),linear(F),linear(J),linear(I),linear(H))),
    adj(quant,H,K,F,L,J),
    true((mshare([[B],[C],[D],[G],[G,J,L],[G,L],[I]]),ground([E,F,H,K]),linear(B),linear(C),linear(D),linear(I);mshare([[B],[C],[D],[I]]),ground([E,F,G,J,H,K,L]),linear(B),linear(C),linear(D),linear(I))),
    empty(I),
    true((mshare([[B],[C],[D]]),ground([E,F,G,J,I,H,K,L]),linear(B),linear(C),linear(D);mshare([[B],[C],[D],[G],[G,J,L],[G,L]]),ground([E,F,I,H,K]),linear(B),linear(C),linear(D))),
    verb_case(D),
    true((mshare([[B],[C]]),ground([D,E,F,G,J,I,H,K,L]),linear(B),linear(C);mshare([[B],[C],[G],[G,J,L],[G,L]]),ground([D,E,F,I,H,K]),linear(B),linear(C))).

:- true pred adv_phrase(B,C,D,E,_A,F,G)
   : ( mshare([[B],[D],[_A],[F],[G]]),
       ground([C,E]), linear(B), linear(D), linear(_A), linear(G) )
   => ( mshare([[B],[B,D,F],[B,D,F,G],[B,F],[B,F,G],[B,G],[D,F],[D,F,G],[F],[F,G],[G]]),
        ground([C,E,_A]) ).

:- true pred adv_phrase(B,C,D,E,_A,F,G)
   : ( mshare([[B],[D],[_A],[G]]),
       ground([C,E,F]), linear(B), linear(D), linear(_A), linear(G) )
   => ( mshare([[B],[B,G],[G]]),
        ground([C,D,E,_A,F]) ).

adv_phrase(B,C,D,E,E,F,G) :-
    true((mshare([[B],[D],[F],[G]]),ground([C,E]),linear(B),linear(D),linear(G);mshare([[B],[D],[G]]),ground([C,E,F]),linear(B),linear(D),linear(G))),
    virtual(adv_phrase(B,C,D),F,G),
    true((mshare([[B,D,F],[B,D,F,G],[B,F],[B,F,G],[D,F],[D,F,G],[F],[F,G]]),ground([C,E]);ground([B,C,D,E,F,G]))).
adv_phrase(pp(B,C),D,E,F,G,H,I) :-
    true((mshare([[E],[G],[H],[I],[B],[C],[J],[K]]),ground([D,F]),linear(E),linear(G),linear(I),linear(B),linear(C),linear(J),linear(K);mshare([[E],[G],[I],[B],[C],[J],[K]]),ground([D,F,H]),linear(E),linear(G),linear(I),linear(B),linear(C),linear(J),linear(K))),
    loc_pred(B,F,J,H,K),
    true((mshare([[E],[G],[H],[H,K],[I],[C]]),ground([D,F,B,J]),linear(E),linear(G),linear(I),linear(C);mshare([[E],[G],[I],[C]]),ground([D,F,H,B,J,K]),linear(E),linear(G),linear(I),linear(C))),
    pp(pp(prep(of),C),compl,D,E,J,G,K,I),
    true((mshare([[E,H,I,C,K],[E,H,I,K],[E,H,C,K],[E,H,K],[H],[H,I,C,K],[H,I,K],[H,C,K],[H,K],[I],[I,C],[C]]),ground([D,F,G,B,J]);mshare([[I],[I,C],[C]]),ground([D,E,F,G,H,B,J,K]))).

:- true pred predicate(B,C,D,E,_A,F,G)
   : ( mshare([[C],[D],[_A],[G]]),
       ground([B,E,F]), linear(C), linear(D), linear(_A), linear(G) )
   => ( mshare([[C],[C,G],[G]]),
        ground([B,D,E,_A,F]) ).

:- true pred predicate(B,C,D,E,_A,F,G)
   : ( mshare([[B],[C],[D],[_A],[F],[G]]),
       ground([E]), linear(B), linear(C), linear(D), linear(_A), linear(G) )
   => ( mshare([[B],[B,C,D,F],[B,C,D,F,G],[B,C,F],[B,C,F,G],[B,D,F],[B,D,F,G],[B,F],[B,F,G],[C],[C,D,F],[C,D,F,G],[C,F],[C,F,G],[C,G],[D,F],[D,F,G],[F],[F,G],[G]]),
        ground([E,_A]) ).

:- true pred predicate(B,C,D,E,_A,F,G)
   : ( mshare([[B],[B,F],[C],[D],[_A],[F],[G]]),
       ground([E]), linear(C), linear(D), linear(_A), linear(G) )
   => ( mshare([[B],[B,C,D,F],[B,C,D,F,G],[B,C,F],[B,C,F,G],[B,D,F],[B,D,F,G],[B,F],[B,F,G],[C],[C,D,F],[C,D,F,G],[C,F],[C,F,G],[C,G],[D,F],[D,F,G],[F],[F,G],[G]]),
        ground([E,_A]) ).

predicate(B,C,D,E,E,F,G) :-
    true((mshare([[B],[B,F],[C],[D],[F],[G]]),ground([E]),linear(C),linear(D),linear(G);mshare([[B],[C],[D],[F],[G]]),ground([E]),linear(B),linear(C),linear(D),linear(G);mshare([[C],[D],[G]]),ground([B,E,F]),linear(C),linear(D),linear(G))),
    virtual(predicate(B,C,D),F,G),
    true((mshare([[B,C,D,F],[B,C,D,F,G],[B,C,F],[B,C,F,G],[B,D,F],[B,D,F,G],[B,F],[B,F,G],[C,D,F],[C,D,F,G],[C,F],[C,F,G],[D,F],[D,F,G],[F],[F,G]]),ground([E]);ground([B,C,D,E,F,G]))).
predicate(B,C,D,E,F,G,H) :-
    true((mshare([[B],[B,G],[C],[D],[F],[G],[H]]),ground([E]),linear(C),linear(D),linear(F),linear(H);mshare([[B],[C],[D],[F],[G],[H]]),ground([E]),linear(B),linear(C),linear(D),linear(F),linear(H);mshare([[C],[D],[F],[H]]),ground([B,E,G]),linear(C),linear(D),linear(F),linear(H))),
    adj_phrase(C,D,E,F,G,H),
    true((mshare([[B],[B,C,D,G],[B,C,D,G,H],[B,C,G],[B,C,G,H],[B,D,G],[B,D,G,H],[B,G],[B,G,H],[C],[C,D,G],[C,D,G,H],[C,G],[C,G,H],[C,H],[D,G],[D,G,H],[G],[G,H],[H]]),ground([E,F]);mshare([[B],[C],[C,D,G],[C,D,G,H],[C,G],[C,G,H],[C,H],[D,G],[D,G,H],[G],[G,H],[H]]),ground([E,F]),linear(B);mshare([[C],[C,H],[H]]),ground([B,D,E,F,G]))).
predicate(neg,B,C,D,E,F,G) :-
    true((mshare([[B],[C],[E],[F],[G],[H]]),ground([D]),linear(B),linear(C),linear(E),linear(G),linear(H);mshare([[B],[C],[E],[G],[H]]),ground([D,F]),linear(B),linear(C),linear(E),linear(G),linear(H))),
    s_all(H),
    true((mshare([[B],[C],[E],[F],[G]]),ground([D,H]),linear(B),linear(C),linear(E),linear(G);mshare([[B],[C],[E],[G]]),ground([D,F,H]),linear(B),linear(C),linear(E),linear(G))),
    pp(B,compl,H,C,D,E,F,G),
    true((mshare([[B],[B,C,F],[B,C,F,G],[B,F],[B,F,G],[B,G],[C,F],[C,F,G],[F],[F,G],[G]]),ground([D,E,H]);mshare([[B],[B,G],[G]]),ground([C,D,E,F,H]))).
predicate(B,C,D,E,F,G,H) :-
    true((mshare([[B],[B,G],[C],[D],[F],[G],[H],[I]]),ground([E]),linear(C),linear(D),linear(F),linear(H),linear(I);mshare([[B],[C],[D],[F],[G],[H],[I]]),ground([E]),linear(B),linear(C),linear(D),linear(F),linear(H),linear(I);mshare([[C],[D],[F],[H],[I]]),ground([B,E,G]),linear(C),linear(D),linear(F),linear(H),linear(I))),
    s_all(I),
    true((mshare([[B],[B,G],[C],[D],[F],[G],[H]]),ground([E,I]),linear(C),linear(D),linear(F),linear(H);mshare([[B],[C],[D],[F],[G],[H]]),ground([E,I]),linear(B),linear(C),linear(D),linear(F),linear(H);mshare([[C],[D],[F],[H]]),ground([B,E,G,I]),linear(C),linear(D),linear(F),linear(H))),
    adv_phrase(C,I,D,E,F,G,H),
    true((mshare([[B],[B,C,D,G],[B,C,D,G,H],[B,C,G],[B,C,G,H],[B,D,G],[B,D,G,H],[B,G],[B,G,H],[C],[C,D,G],[C,D,G,H],[C,G],[C,G,H],[C,H],[D,G],[D,G,H],[G],[G,H],[H]]),ground([E,F,I]);mshare([[B],[C],[C,D,G],[C,D,G,H],[C,G],[C,G,H],[C,H],[D,G],[D,G,H],[G],[G,H],[H]]),ground([E,F,I]),linear(B);mshare([[C],[C,H],[H]]),ground([B,D,E,F,G,I]))).

:- true pred whq(B,C,D,_A,E,F,G,H)
   : ( mshare([[B],[C],[D],[_A],[F],[G],[H]]),
       ground([E]), linear(B), linear(C), linear(D), linear(_A), linear(F), linear(H) )
   => ( mshare([[B],[B,C],[B,C,D],[B,C,D,G],[B,C,D,G,H],[B,C,D,H],[B,C,G],[B,C,G,H],[B,C,H],[B,D],[B,D,G],[B,D,G,H],[B,D,H],[B,G],[B,G,H],[B,H],[C],[C,D],[C,D,G],[C,D,G,H],[C,D,H],[C,G],[C,G,H],[C,H],[D],[D,G],[D,G,H],[D,H],[G],[G,H],[H]]),
        ground([_A,E,F]) ).

:- true pred whq(B,C,D,_A,E,F,G,H)
   : ( mshare([[B],[C],[D],[_A],[F],[H]]),
       ground([E,G]), linear(B), linear(C), linear(D), linear(_A), linear(F), linear(H) )
   => ( mshare([[B],[B,C],[B,C,D],[B,C,D,H],[B,C,H],[B,D],[B,D,H],[B,H],[C],[C,D],[C,D,H],[C,H],[D],[D,H],[H]]),
        ground([_A,E,F,G]) ).

whq(B,C,D,undef,E,F,G,H) :-
    true((mshare([[B],[C],[D],[F],[G],[H],[I],[J],[K],[L],[M],[N]]),ground([E]),linear(B),linear(C),linear(D),linear(F),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(N);mshare([[B],[C],[D],[F],[H],[I],[J],[K],[L],[M],[N]]),ground([E,G]),linear(B),linear(C),linear(D),linear(F),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(N))),
    int_det(B,C,E,I,G,J),
    true((mshare([[B,J],[C,J],[D],[F],[G],[G,J],[H],[K],[L],[M],[N]]),ground([E,I]),linear(B),linear(D),linear(F),linear(H),linear(K),linear(L),linear(M),linear(N);mshare([[B,J],[C,J],[D],[F],[H],[K],[L],[M],[N]]),ground([E,G,I]),linear(B),linear(D),linear(F),linear(H),linear(K),linear(L),linear(M),linear(N))),
    s_all(K),
    true((mshare([[B,J],[C,J],[D],[F],[G],[G,J],[H],[L],[M],[N]]),ground([E,I,K]),linear(B),linear(D),linear(F),linear(H),linear(L),linear(M),linear(N);mshare([[B,J],[C,J],[D],[F],[H],[L],[M],[N]]),ground([E,G,I,K]),linear(B),linear(D),linear(F),linear(H),linear(L),linear(M),linear(N))),
    np(D,C,L,M,subj,K,N,I,F,J,H),
    true((mshare([[B,C,D,G,H,J],[B,C,D,G,H,J,L],[B,C,D,G,H,J,L,M],[B,C,D,G,H,J,L,M,N],[B,C,D,G,H,J,L,N],[B,C,D,G,H,J,M],[B,C,D,G,H,J,M,N],[B,C,D,G,H,J,N],[B,C,D,G,J],[B,C,D,G,J,L],[B,C,D,G,J,L,M],[B,C,D,G,J,L,M,N],[B,C,D,G,J,L,N],[B,C,D,G,J,M],[B,C,D,G,J,M,N],[B,C,D,G,J,N],[B,C,D,H,J],[B,C,D,H,J,L],[B,C,D,H,J,L,M],[B,C,D,H,J,L,M,N],[B,C,D,H,J,L,N],[B,C,D,H,J,M],[B,C,D,H,J,M,N],[B,C,D,H,J,N],[B,C,D,J],[B,C,D,J,L],[B,C,D,J,L,M],[B,C,D,J,L,M,N],[B,C,D,J,L,N],[B,C,D,J,M],[B,C,D,J,M,N],[B,C,D,J,N],[B,C,G,H,J],[B,C,G,H,J,L],[B,C,G,H,J,L,M],[B,C,G,H,J,L,M,N],[B,C,G,H,J,L,N],[B,C,G,H,J,M],[B,C,G,H,J,M,N],[B,C,G,H,J,N],[B,C,G,J],[B,C,G,J,L],[B,C,G,J,L,M],[B,C,G,J,L,M,N],[B,C,G,J,L,N],[B,C,G,J,M],[B,C,G,J,M,N],[B,C,G,J,N],[B,C,H,J],[B,C,H,J,L],[B,C,H,J,L,M],[B,C,H,J,L,M,N],[B,C,H,J,L,N],[B,C,H,J,M],[B,C,H,J,M,N],[B,C,H,J,N],[B,C,J],[B,C,J,L],[B,C,J,L,M],[B,C,J,L,M,N],[B,C,J,L,N],[B,C,J,M],[B,C,J,M,N],[B,C,J,N],[B,D,G,H,J],[B,D,G,H,J,L],[B,D,G,H,J,L,M],[B,D,G,H,J,L,M,N],[B,D,G,H,J,L,N],[B,D,G,H,J,M],[B,D,G,H,J,M,N],[B,D,G,H,J,N],[B,D,G,J],[B,D,G,J,L],[B,D,G,J,L,M],[B,D,G,J,L,M,N],[B,D,G,J,L,N],[B,D,G,J,M],[B,D,G,J,M,N],[B,D,G,J,N],[B,D,H,J],[B,D,H,J,L],[B,D,H,J,L,M],[B,D,H,J,L,M,N],[B,D,H,J,L,N],[B,D,H,J,M],[B,D,H,J,M,N],[B,D,H,J,N],[B,D,J],[B,D,J,L],[B,D,J,L,M],[B,D,J,L,M,N],[B,D,J,L,N],[B,D,J,M],[B,D,J,M,N],[B,D,J,N],[B,G,H,J],[B,G,H,J,L],[B,G,H,J,L,M],[B,G,H,J,L,M,N],[B,G,H,J,L,N],[B,G,H,J,M],[B,G,H,J,M,N],[B,G,H,J,N],[B,G,J],[B,G,J,L],[B,G,J,L,M],[B,G,J,L,M,N],[B,G,J,L,N],[B,G,J,M],[B,G,J,M,N],[B,G,J,N],[B,H,J],[B,H,J,L],[B,H,J,L,M],[B,H,J,L,M,N],[B,H,J,L,N],[B,H,J,M],[B,H,J,M,N],[B,H,J,N],[B,J],[B,J,L],[B,J,L,M],[B,J,L,M,N],[B,J,L,N],[B,J,M],[B,J,M,N],[B,J,N],[C,D,G,H,J],[C,D,G,H,J,L],[C,D,G,H,J,L,M],[C,D,G,H,J,L,M,N],[C,D,G,H,J,L,N],[C,D,G,H,J,M],[C,D,G,H,J,M,N],[C,D,G,H,J,N],[C,D,G,J],[C,D,G,J,L],[C,D,G,J,L,M],[C,D,G,J,L,M,N],[C,D,G,J,L,N],[C,D,G,J,M],[C,D,G,J,M,N],[C,D,G,J,N],[C,D,H,J],[C,D,H,J,L],[C,D,H,J,L,M],[C,D,H,J,L,M,N],[C,D,H,J,L,N],[C,D,H,J,M],[C,D,H,J,M,N],[C,D,H,J,N],[C,D,J],[C,D,J,L],[C,D,J,L,M],[C,D,J,L,M,N],[C,D,J,L,N],[C,D,J,M],[C,D,J,M,N],[C,D,J,N],[C,G,H,J],[C,G,H,J,L],[C,G,H,J,L,M],[C,G,H,J,L,M,N],[C,G,H,J,L,N],[C,G,H,J,M],[C,G,H,J,M,N],[C,G,H,J,N],[C,G,J],[C,G,J,L],[C,G,J,L,M],[C,G,J,L,M,N],[C,G,J,L,N],[C,G,J,M],[C,G,J,M,N],[C,G,J,N],[C,H,J],[C,H,J,L],[C,H,J,L,M],[C,H,J,L,M,N],[C,H,J,L,N],[C,H,J,M],[C,H,J,M,N],[C,H,J,N],[C,J],[C,J,L],[C,J,L,M],[C,J,L,M,N],[C,J,L,N],[C,J,M],[C,J,M,N],[C,J,N],[D],[D,G,H,J],[D,G,H,J,L],[D,G,H,J,L,M],[D,G,H,J,L,M,N],[D,G,H,J,L,N],[D,G,H,J,M],[D,G,H,J,M,N],[D,G,H,J,N],[D,G,J],[D,G,J,L],[D,G,J,L,M],[D,G,J,L,M,N],[D,G,J,L,N],[D,G,J,M],[D,G,J,M,N],[D,G,J,N],[D,H],[G],[G,H,J],[G,H,J,L],[G,H,J,L,M],[G,H,J,L,M,N],[G,H,J,L,N],[G,H,J,M],[G,H,J,M,N],[G,H,J,N],[G,J],[G,J,L],[G,J,L,M],[G,J,L,M,N],[G,J,L,N],[G,J,M],[G,J,M,N],[G,J,N],[H],[L]]),ground([E,F,I,K]);mshare([[B,C,D,H,J],[B,C,D,H,J,L],[B,C,D,H,J,L,M],[B,C,D,H,J,L,M,N],[B,C,D,H,J,L,N],[B,C,D,H,J,M],[B,C,D,H,J,M,N],[B,C,D,H,J,N],[B,C,D,J],[B,C,D,J,L],[B,C,D,J,L,M],[B,C,D,J,L,M,N],[B,C,D,J,L,N],[B,C,D,J,M],[B,C,D,J,M,N],[B,C,D,J,N],[B,C,H,J],[B,C,H,J,L],[B,C,H,J,L,M],[B,C,H,J,L,M,N],[B,C,H,J,L,N],[B,C,H,J,M],[B,C,H,J,M,N],[B,C,H,J,N],[B,C,J],[B,C,J,L],[B,C,J,L,M],[B,C,J,L,M,N],[B,C,J,L,N],[B,C,J,M],[B,C,J,M,N],[B,C,J,N],[B,D,H,J],[B,D,H,J,L],[B,D,H,J,L,M],[B,D,H,J,L,M,N],[B,D,H,J,L,N],[B,D,H,J,M],[B,D,H,J,M,N],[B,D,H,J,N],[B,D,J],[B,D,J,L],[B,D,J,L,M],[B,D,J,L,M,N],[B,D,J,L,N],[B,D,J,M],[B,D,J,M,N],[B,D,J,N],[B,H,J],[B,H,J,L],[B,H,J,L,M],[B,H,J,L,M,N],[B,H,J,L,N],[B,H,J,M],[B,H,J,M,N],[B,H,J,N],[B,J],[B,J,L],[B,J,L,M],[B,J,L,M,N],[B,J,L,N],[B,J,M],[B,J,M,N],[B,J,N],[C,D,H,J],[C,D,H,J,L],[C,D,H,J,L,M],[C,D,H,J,L,M,N],[C,D,H,J,L,N],[C,D,H,J,M],[C,D,H,J,M,N],[C,D,H,J,N],[C,D,J],[C,D,J,L],[C,D,J,L,M],[C,D,J,L,M,N],[C,D,J,L,N],[C,D,J,M],[C,D,J,M,N],[C,D,J,N],[C,H,J],[C,H,J,L],[C,H,J,L,M],[C,H,J,L,M,N],[C,H,J,L,N],[C,H,J,M],[C,H,J,M,N],[C,H,J,N],[C,J],[C,J,L],[C,J,L,M],[C,J,L,M,N],[C,J,L,N],[C,J,M],[C,J,M,N],[C,J,N],[D],[D,H],[H],[L]]),ground([E,F,G,I,K]))).
whq(B,3+C,np(3+C,wh(B),[]),D,E,F,G,H) :-
    true((mshare([[B],[D],[F],[G],[H],[C]]),ground([E]),linear(B),linear(D),linear(F),linear(H),linear(C);mshare([[B],[D],[F],[H],[C]]),ground([E,G]),linear(B),linear(D),linear(F),linear(H),linear(C))),
    int_pron(D,E,F,G,H),
    true((mshare([[B],[G],[G,H],[C]]),ground([D,E,F]),linear(B),linear(C);mshare([[B],[C]]),ground([D,E,F,G,H]),linear(B),linear(C))).

:- true pred int_det(B,_A,D,E,F,G)
   : ( mshare([[B],[_A],[E],[F],[G]]),
       ground([D]), linear(B), linear(_A), linear(E), linear(G) )
   => ( mshare([[B,G],[_A,G],[F],[F,G]]),
        ground([D,E]), linear(B) ).

:- true pred int_det(B,_A,D,E,F,G)
   : ( mshare([[B],[_A],[E],[G]]),
       ground([D,F]), linear(B), linear(_A), linear(E), linear(G) )
   => ( mshare([[B,G],[_A,G]]),
        ground([D,E,F]), linear(B) ).

int_det(B,3+C,D,E,F,G) :-
    true((mshare([[B],[E],[F],[G],[C]]),ground([D]),linear(B),linear(E),linear(G),linear(C);mshare([[B],[E],[G],[C]]),ground([D,F]),linear(B),linear(E),linear(G),linear(C))),
    whose(B,C,D,E,F,G),
    true((mshare([[B,G],[F],[F,G],[G,C]]),ground([D,E]),linear(B),linear(C);mshare([[B,G],[G,C]]),ground([D,E,F]),linear(B),linear(G),linear(C))).
int_det(B,3+C,D,E,F,G) :-
    true((mshare([[B],[E],[F],[G],[C]]),ground([D]),linear(B),linear(E),linear(G),linear(C);mshare([[B],[E],[G],[C]]),ground([D,F]),linear(B),linear(E),linear(G),linear(C))),
    int_art(B,C,D,E,F,G),
    true((mshare([[B,G],[F],[F,G],[G,C]]),ground([D,E]),linear(B);mshare([[B,G],[G,C]]),ground([D,E,F]),linear(B))).

:- true pred gen_marker(B,_A,C,D)
   : ( mshare([[_A],[C],[D]]),
       ground([B]), linear(_A), linear(D) )
   => ( mshare([[C],[C,D]]),
        ground([B,_A]) ).

:- true pred gen_marker(B,_A,C,D)
   : ( mshare([[_A],[D]]),
       ground([B,C]), linear(_A), linear(D) )
   => ground([B,_A,C,D]).

gen_marker(B,B,C,D) :-
    true((mshare([[C],[D]]),ground([B]),linear(D);mshare([[D]]),ground([B,C]),linear(D))),
    virtual(gen_marker,C,D),
    true((mshare([[C],[C,D]]),ground([B]);ground([B,C,D]))).
gen_marker(B,C,D,E) :-
    true((mshare([[C],[D],[E],[F],[G]]),ground([B]),linear(C),linear(E),linear(F),linear(G);mshare([[C],[E],[F],[G]]),ground([B,D]),linear(C),linear(E),linear(F),linear(G))),
    ~(~,B,F,D,G),
    true((mshare([[C],[D],[D,G],[E]]),ground([B,F]),linear(C),linear(E);mshare([[C],[E]]),ground([B,D,F,G]),linear(C),linear(E))),
    an_s(F,C,G,E),
    true((mshare([[D],[D,E,G],[D,G]]),ground([B,C,F]);ground([B,C,D,E,F,G]))).

:- true pred whose(B,C,D,E,F,_A)
   : ( mshare([[B],[C],[E],[F],[_A]]),
       ground([D]), linear(B), linear(C), linear(E), linear(_A) )
   => ( mshare([[B,_A],[C,_A],[F],[F,_A]]),
        ground([D,E]), linear(B), linear(C) ).

:- true pred whose(B,C,D,E,F,_A)
   : ( mshare([[B],[C],[E],[_A]]),
       ground([D,F]), linear(B), linear(C), linear(E), linear(_A) )
   => ( mshare([[B,_A],[C,_A]]),
        ground([D,E,F]), linear(B), linear(C), linear(_A) ).

:- true pred whose(B,C,D,E,F,_A)
   : ( mshare([[B],[C],[C,F],[E],[F],[_A]]),
       ground([D]), linear(B), linear(E), linear(_A) )
   => ( mshare([[B,_A],[C,F,_A],[C,_A],[F],[F,_A]]),
        ground([D,E]), linear(B) ).

:- true pred whose(B,C,D,E,F,_A)
   : ( mshare([[B],[E],[F],[_A]]),
       ground([C,D]), linear(B), linear(E), linear(_A) )
   => ( mshare([[B,_A],[F],[F,_A]]),
        ground([C,D,E]), linear(B) ).

whose(B,C,D,E,F,x(nogap,nonterminal,np_head0(wh(B),C,proper),x(nogap,nonterminal,gen_marker,G))) :-
    true((mshare([[B],[C],[C,F],[E],[F],[G]]),ground([D]),linear(B),linear(E),linear(G);mshare([[B],[C],[E],[F],[G]]),ground([D]),linear(B),linear(C),linear(E),linear(G);mshare([[B],[C],[E],[G]]),ground([D,F]),linear(B),linear(C),linear(E),linear(G);mshare([[B],[E],[F],[G]]),ground([C,D]),linear(B),linear(E),linear(G))),
    ~(whose,D,E,F,G),
    true((mshare([[B],[C]]),ground([D,E,F,G]),linear(B),linear(C);mshare([[B],[C],[C,F],[C,F,G],[F],[F,G]]),ground([D,E]),linear(B);mshare([[B],[C],[F],[F,G]]),ground([D,E]),linear(B),linear(C);mshare([[B],[F],[F,G]]),ground([C,D,E]),linear(B))).

:- true pred question(B,C,D,E,F,G,H)
   : ( mshare([[C],[C,G],[D],[F],[G],[H]]),
       ground([B,E]), linear(D), linear(F), linear(H) )
   => ( mshare([[C],[C,D,G],[C,D,G,H],[C,G],[C,G,H],[D],[D,G],[D,G,H],[D,H],[G],[G,H],[H]]),
        ground([B,E,F]) ).

question(B,C,D,E,F,G,H) :-
    true((
        mshare([[C],[C,G],[D],[F],[G],[H],[I],[J]]),
        ground([B,E]),
        linear(D),
        linear(F),
        linear(H),
        linear(I),
        linear(J)
    )),
    subj_question(B),
    true((
        mshare([[C],[C,G],[D],[F],[G],[H],[I],[J]]),
        ground([B,E]),
        linear(D),
        linear(F),
        linear(H),
        linear(I),
        linear(J)
    )),
    role(subj,I,C),
    true((
        mshare([[D],[F],[G],[H],[I],[J]]),
        ground([B,C,E]),
        linear(D),
        linear(F),
        linear(H),
        linear(I),
        linear(J)
    )),
    s(D,J,E,F,G,H),
    true((
        mshare([[D],[D,G],[D,G,H],[D,H],[G],[G,H],[H],[I]]),
        ground([B,C,E,F,J]),
        linear(I)
    )).
question(B,C,D,E,F,G,H) :-
    true((
        mshare([[C],[C,G],[D],[F],[G],[H],[I],[J],[K]]),
        ground([B,E]),
        linear(D),
        linear(F),
        linear(H),
        linear(I),
        linear(J),
        linear(K)
    )),
    fronted_verb(B,C,E,I,G,J),
    true((
        mshare([[C],[C,G],[C,G,J],[D],[F],[G],[G,J],[H],[J],[K]]),
        ground([B,E,I]),
        linear(D),
        linear(F),
        linear(H),
        linear(K)
    )),
    s(D,K,I,F,J,H),
    true((
        mshare([[C],[C,D,G,H,J],[C,D,G,J],[C,G],[C,G,H,J],[C,G,J],[D],[D,G,H,J],[D,G,J],[D,H],[D,H,J],[D,J],[G],[G,H,J],[G,J],[H],[H,J],[J]]),
        ground([B,E,F,I,K])
    )).

:- true pred det(B,C,D,E,_A,F,G)
   : ( mshare([[B],[C,F],[_A],[F],[G]]),
       ground([D,E]), linear(B), linear(_A), linear(G) )
   => ( mshare([[B,C,F],[B,C,F,G],[B,F],[B,F,G],[C,F],[C,F,G],[F],[F,G]]),
        ground([D,E,_A]) ).

:- true pred det(B,C,D,E,_A,F,G)
   : ( mshare([[B],[C],[_A],[F],[G]]),
       ground([D,E]), linear(B), linear(C), linear(_A), linear(G) )
   => ( mshare([[B,C],[B,C,F],[B,C,F,G],[B,F],[B,F,G],[C],[C,F],[C,F,G],[F],[F,G]]),
        ground([D,E,_A]) ).

:- true pred det(B,C,D,E,_A,F,G)
   : ( mshare([[B],[C],[D],[_A],[F],[G]]),
       ground([E]), linear(B), linear(C), linear(D), linear(_A), linear(G) )
   => ( mshare([[B,C],[B,C,D,F],[B,C,D,F,G],[B,C,F],[B,C,F,G],[B,D,F],[B,D,F,G],[B,F],[B,F,G],[C],[C,D,F],[C,D,F,G],[C,F],[C,F,G],[D,F],[D,F,G],[F],[F,G]]),
        ground([E,_A]) ).

:- true pred det(B,C,D,E,_A,F,G)
   : ( mshare([[B],[C],[_A],[G]]),
       ground([D,E,F]), linear(B), linear(C), linear(_A), linear(G) )
   => ( mshare([[B,C],[C]]),
        ground([D,E,_A,F,G]) ).

:- true pred det(B,C,D,E,_A,F,G)
   : ( mshare([[B],[C],[D],[_A],[G]]),
       ground([E,F]), linear(B), linear(C), linear(D), linear(_A), linear(G) )
   => ( mshare([[B,C],[C]]),
        ground([D,E,_A,F,G]) ).

det(B,C,D,E,E,F,G) :-
    true((mshare([[B],[C],[D],[F],[G]]),ground([E]),linear(B),linear(C),linear(D),linear(G);mshare([[B],[C],[D],[G]]),ground([E,F]),linear(B),linear(C),linear(D),linear(G);mshare([[B],[C],[F],[G]]),ground([D,E]),linear(B),linear(C),linear(G);mshare([[B],[C],[G]]),ground([D,E,F]),linear(B),linear(C),linear(G);mshare([[B],[C,F],[F],[G]]),ground([D,E]),linear(B),linear(G))),
    virtual(det(B,C,D),F,G),
    true((mshare([[B,C,D,F],[B,C,D,F,G],[B,C,F],[B,C,F,G],[B,D,F],[B,D,F,G],[B,F],[B,F,G],[C,D,F],[C,D,F,G],[C,F],[C,F,G],[D,F],[D,F,G],[F],[F,G]]),ground([E]);mshare([[B,C,F],[B,C,F,G],[B,F],[B,F,G],[C,F],[C,F,G],[F],[F,G]]),ground([D,E]);ground([B,C,D,E,F,G]))).
det(det(B),C,D,E,F,G,H) :-
    true((mshare([[C],[D],[F],[G],[H],[B],[I]]),ground([E]),linear(C),linear(D),linear(F),linear(H),linear(B),linear(I);mshare([[C],[D],[F],[H],[B],[I]]),ground([E,G]),linear(C),linear(D),linear(F),linear(H),linear(B),linear(I);mshare([[C],[F],[G],[H],[B],[I]]),ground([D,E]),linear(C),linear(F),linear(H),linear(B),linear(I);mshare([[C],[F],[H],[B],[I]]),ground([D,E,G]),linear(C),linear(F),linear(H),linear(B),linear(I);mshare([[C,G],[F],[G],[H],[B],[I]]),ground([D,E]),linear(F),linear(H),linear(B),linear(I))),
    terminal(I,E,F,G,H),
    true((mshare([[C],[D],[G],[G,H],[G,H,I],[G,I],[B]]),ground([E,F]),linear(C),linear(D),linear(B);mshare([[C],[D],[B]]),ground([E,F,G,H,I]),linear(C),linear(D),linear(B);mshare([[C],[G],[G,H],[G,H,I],[G,I],[B]]),ground([D,E,F]),linear(C),linear(B);mshare([[C],[B]]),ground([D,E,F,G,H,I]),linear(C),linear(B);mshare([[C,G],[C,G,H],[C,G,H,I],[C,G,I],[G],[G,H],[G,H,I],[G,I],[B]]),ground([D,E,F]),linear(B))),
    det(I,C,B,D),
    true((mshare([[C],[C,B]]),ground([D,E,F,G,H,I]);mshare([[C],[C,B],[G],[G,H]]),ground([D,E,F,I]);mshare([[C,G],[C,G,H],[C,G,H,B],[C,G,B],[G],[G,H]]),ground([D,E,F,I]))).
det(generic,B,generic,C,C,D,D).

:- true pred int_art(B,C,D,E,F,_A)
   : ( mshare([[B],[C],[E],[F],[_A]]),
       ground([D]), linear(B), linear(C), linear(E), linear(_A) )
   => ( mshare([[B,_A],[C,_A],[F],[F,_A]]),
        ground([D,E]), linear(B) ).

:- true pred int_art(B,C,D,E,F,_A)
   : ( mshare([[B],[C],[E],[_A]]),
       ground([D,F]), linear(B), linear(C), linear(E), linear(_A) )
   => ( mshare([[B,_A],[C,_A]]),
        ground([D,E,F]), linear(B) ).

int_art(B,C,D,E,F,x(nogap,nonterminal,det(G,C,def),H)) :-
    true((mshare([[B],[C],[E],[F],[H],[G]]),ground([D]),linear(B),linear(C),linear(E),linear(H),linear(G);mshare([[B],[C],[E],[H],[G]]),ground([D,F]),linear(B),linear(C),linear(E),linear(H),linear(G))),
    int_art(B,C,G,D,E,F,H),
    true((mshare([[B,G],[C]]),ground([D,E,F,H]),linear(B),linear(G);mshare([[B,G],[C],[F],[F,H]]),ground([D,E]),linear(B),linear(G))).

:- true pred subj_question(_A)
   : ground([_A])
   => ground([_A]).

subj_question(subj).
subj_question(undef).

:- true pred yn_question(_A,C,D,E,F)
   : ( mshare([[_A],[D],[F]]),
       ground([C,E]), linear(_A), linear(D), linear(F) )
   => ( mshare([[_A],[_A,F],[F]]),
        ground([C,D,E]) ).

yn_question(q(B),C,D,E,F) :-
    true((
        mshare([[D],[F],[B],[G],[H],[I],[J]]),
        ground([C,E]),
        linear(D),
        linear(F),
        linear(B),
        linear(G),
        linear(H),
        linear(I),
        linear(J)
    )),
    fronted_verb(nil,G,C,H,E,I),
    true((
        mshare([[D],[F],[B],[G],[I],[J]]),
        ground([C,E,H]),
        linear(D),
        linear(F),
        linear(B),
        linear(J)
    )),
    s(B,J,H,D,I,F),
    true((
        mshare([[F],[F,B],[F,B,I],[F,I],[B],[B,I],[G],[I]]),
        ground([C,D,E,H,J])
    )).

:- true pred verb_form(B,C,D,E,F,_A,G,H)
   : ( (C=inf),
       mshare([[B],[D],[E],[_A],[H]]),
       ground([F,G]), linear(B), linear(D), linear(E), linear(_A), linear(H) )
   => ( mshare([[D],[E]]),
        ground([B,F,_A,G,H]) ).

:- true pred verb_form(B,C,D,E,F,_A,G,H)
   : ( mshare([[B],[C],[D],[E],[_A],[H]]),
       ground([F,G]), linear(B), linear(C), linear(D), linear(E), linear(_A), linear(H) )
   => ( mshare([[C],[D],[E]]),
        ground([B,F,_A,G,H]) ).

:- true pred verb_form(B,C,D,E,F,_A,G,H)
   : ( mshare([[B],[C],[D],[E],[_A],[G],[H]]),
       ground([F]), linear(B), linear(C), linear(D), linear(E), linear(_A), linear(H) )
   => ( mshare([[B,C,D,E,G],[B,C,D,E,G,H],[B,C,D,G],[B,C,D,G,H],[B,C,E,G],[B,C,E,G,H],[B,C,G],[B,C,G,H],[B,D,E,G],[B,D,E,G,H],[B,D,G],[B,D,G,H],[B,E,G],[B,E,G,H],[B,G],[B,G,H],[C],[C,D,E,G],[C,D,E,G,H],[C,D,G],[C,D,G,H],[C,E,G],[C,E,G,H],[C,G],[C,G,H],[D],[D,E,G],[D,E,G,H],[D,G],[D,G,H],[E],[E,G],[E,G,H],[G],[G,H]]),
        ground([F,_A]) ).

:- true pred verb_form(B,C,D,E,F,_A,G,H)
   : ( (C=inf),
       mshare([[B],[D],[E],[_A],[G],[H]]),
       ground([F]), linear(B), linear(D), linear(E), linear(_A), linear(H) )
   => ( mshare([[B,D,E,G],[B,D,E,G,H],[B,D,G],[B,D,G,H],[B,E,G],[B,E,G,H],[B,G],[B,G,H],[D],[D,E,G],[D,E,G,H],[D,G],[D,G,H],[E],[E,G],[E,G,H],[G],[G,H]]),
        ground([F,_A]) ).

:- true pred verb_form(B,C,D,E,F,_A,G,H)
   : ( (C=past+part),
       mshare([[B],[D],[E],[_A],[G],[H]]),
       ground([F]), linear(B), linear(D), linear(E), linear(_A), linear(H) )
   => ( mshare([[B,D,E,G],[B,D,E,G,H],[B,D,G],[B,D,G,H],[B,E,G],[B,E,G,H],[B,G],[B,G,H],[D],[D,E,G],[D,E,G,H],[D,G],[D,G,H],[E],[E,G],[E,G,H],[G],[G,H]]),
        ground([F,_A]) ).

:- true pred verb_form(B,C,D,E,F,_A,G,H)
   : ( (C=_B+fin),
       mshare([[B],[D],[D,G],[E],[_A],[G],[H],[_B]]),
       ground([F]), linear(B), linear(E), linear(_A), linear(H), linear(_B) )
   => ( mshare([[B,D,E,G],[B,D,E,G,H],[B,D,E,G,H,_B],[B,D,E,G,_B],[B,D,G],[B,D,G,H],[B,D,G,H,_B],[B,D,G,_B],[B,E,G],[B,E,G,H],[B,E,G,H,_B],[B,E,G,_B],[B,G],[B,G,H],[B,G,H,_B],[B,G,_B],[D],[D,E,G],[D,E,G,H],[D,E,G,H,_B],[D,E,G,_B],[D,G],[D,G,H],[D,G,H,_B],[D,G,_B],[E],[E,G],[E,G,H],[E,G,H,_B],[E,G,_B],[G],[G,H],[G,H,_B],[G,_B],[_B]]),
        ground([F,_A]) ).

verb_form(B,C,D,E,F,F,G,H) :-
    true((mshare([[B],[C],[D],[D,G],[E],[G],[H]]),ground([F]),linear(B),linear(C),linear(E),linear(H);mshare([[B],[C],[D],[E],[G],[H]]),ground([F]),linear(B),linear(C),linear(D),linear(E),linear(H);mshare([[B],[C],[D],[E],[H]]),ground([F,G]),linear(B),linear(C),linear(D),linear(E),linear(H);mshare([[B],[D],[E],[G],[H]]),ground([C,F]),linear(B),linear(D),linear(E),linear(H);mshare([[B],[D],[E],[H]]),ground([C,F,G]),linear(B),linear(D),linear(E),linear(H))),
    virtual(verb_form(B,C,D,E),G,H),
    true((mshare([[B,C,D,E,G],[B,C,D,E,G,H],[B,C,D,G],[B,C,D,G,H],[B,C,E,G],[B,C,E,G,H],[B,C,G],[B,C,G,H],[B,D,E,G],[B,D,E,G,H],[B,D,G],[B,D,G,H],[B,E,G],[B,E,G,H],[B,G],[B,G,H],[C,D,E,G],[C,D,E,G,H],[C,D,G],[C,D,G,H],[C,E,G],[C,E,G,H],[C,G],[C,G,H],[D,E,G],[D,E,G,H],[D,G],[D,G,H],[E,G],[E,G,H],[G],[G,H]]),ground([F]);mshare([[B,D,E,G],[B,D,E,G,H],[B,D,G],[B,D,G,H],[B,E,G],[B,E,G,H],[B,G],[B,G,H],[D,E,G],[D,E,G,H],[D,G],[D,G,H],[E,G],[E,G,H],[G],[G,H]]),ground([C,F]);ground([B,C,D,E,F,G,H]))).
verb_form(B,C,D,E,F,G,H,I) :-
    true((mshare([[B],[C],[D],[D,H],[E],[G],[H],[I],[J]]),ground([F]),linear(B),linear(C),linear(E),linear(G),linear(I),linear(J);mshare([[B],[C],[D],[E],[G],[H],[I],[J]]),ground([F]),linear(B),linear(C),linear(D),linear(E),linear(G),linear(I),linear(J);mshare([[B],[C],[D],[E],[G],[I],[J]]),ground([F,H]),linear(B),linear(C),linear(D),linear(E),linear(G),linear(I),linear(J);mshare([[B],[D],[E],[G],[H],[I],[J]]),ground([C,F]),linear(B),linear(D),linear(E),linear(G),linear(I),linear(J);mshare([[B],[D],[E],[G],[I],[J]]),ground([C,F,H]),linear(B),linear(D),linear(E),linear(G),linear(I),linear(J))),
    terminal(J,F,G,H,I),
    true((mshare([[B],[C],[D],[D,H],[D,H,I],[D,H,I,J],[D,H,J],[E],[H],[H,I],[H,I,J],[H,J]]),ground([F,G]),linear(B),linear(C),linear(E);mshare([[B],[C],[D],[E]]),ground([F,G,H,I,J]),linear(B),linear(C),linear(D),linear(E);mshare([[B],[C],[D],[E],[H],[H,I],[H,I,J],[H,J]]),ground([F,G]),linear(B),linear(C),linear(D),linear(E);mshare([[B],[D],[E]]),ground([C,F,G,H,I,J]),linear(B),linear(D),linear(E);mshare([[B],[D],[E],[H],[H,I],[H,I,J],[H,J]]),ground([C,F,G]),linear(B),linear(D),linear(E))),
    verb_form(J,B,C,D),
    true((mshare([[C],[D],[D,H],[D,H,I],[E],[H],[H,I]]),ground([B,F,G,J]),linear(E);mshare([[C],[D],[E]]),ground([B,F,G,H,I,J]),linear(E);mshare([[C],[D],[E],[H],[H,I]]),ground([B,F,G,J]),linear(E);mshare([[D],[E]]),ground([B,C,F,G,H,I,J]),linear(E);mshare([[D],[E],[H],[H,I]]),ground([B,C,F,G,J]),linear(E))).

:- true pred neg(B,C,D,_A,E,F)
   : ( mshare([[B],[C],[_A],[F]]),
       ground([D,E]), linear(B), linear(C), linear(_A), linear(F) )
   => ( mshare([[B]]),
        ground([C,D,_A,E,F]) ).

:- true pred neg(B,C,D,_A,E,F)
   : ( mshare([[B],[C],[_A],[E],[F]]),
       ground([D]), linear(B), linear(C), linear(_A), linear(F) )
   => ( mshare([[B],[B,C,E],[B,C,E,F],[B,E],[B,E,F],[C,E],[C,E,F],[E],[E,F]]),
        ground([D,_A]) ).

:- true pred neg(B,C,D,_A,E,F)
   : ( mshare([[C],[_A],[E],[F]]),
       ground([B,D]), linear(C), linear(_A), linear(F) )
   => ( mshare([[C,E],[C,E,F],[E],[E,F]]),
        ground([B,D,_A]) ).

neg(B,C,D,D,E,F) :-
    true((mshare([[B],[C],[E],[F]]),ground([D]),linear(B),linear(C),linear(F);mshare([[B],[C],[F]]),ground([D,E]),linear(B),linear(C),linear(F);mshare([[C],[E],[F]]),ground([B,D]),linear(C),linear(F))),
    virtual(neg(B,C),E,F),
    true((mshare([[B,C,E],[B,C,E,F],[B,E],[B,E,F],[C,E],[C,E,F],[E],[E,F]]),ground([D]);mshare([[C,E],[C,E,F],[E],[E,F]]),ground([B,D]);ground([B,C,D,E,F]))).
neg(aux+B,neg,C,D,E,F) :-
    true((mshare([[D],[E],[F]]),ground([C,B]),linear(D),linear(F);mshare([[D],[E],[F],[B]]),ground([C]),linear(D),linear(F),linear(B);mshare([[D],[F],[B]]),ground([C,E]),linear(D),linear(F),linear(B))),
    ~(not,C,D,E,F),
    true((mshare([[E],[E,F]]),ground([C,D,B]);mshare([[E],[E,F],[B]]),ground([C,D]),linear(B);mshare([[B]]),ground([C,D,E,F]),linear(B))).
neg(B,pos,C,C,D,D).

:- true pred fronted_verb(B,C,D,E,F,_A)
   : ( (B=nil),
       mshare([[C],[E],[_A]]),
       ground([D,F]), linear(C), linear(E), linear(_A) )
   => ( mshare([[C],[_A]]),
        ground([D,E,F]) ).

:- true pred fronted_verb(B,C,D,E,F,_A)
   : ( mshare([[C],[C,F],[E],[F],[_A]]),
       ground([B,D]), linear(E), linear(_A) )
   => ( mshare([[C],[C,F],[C,F,_A],[F],[F,_A],[_A]]),
        ground([B,D,E]) ).

fronted_verb(B,C,D,E,F,x(gap,nonterminal,verb_form(G,H,I,J),x(nogap,nonterminal,neg(K,L),M))) :-
    true((mshare([[C],[C,F],[E],[F],[G],[H],[I],[J],[M],[K],[L],[N],[O],[P],[Q],[R]]),ground([B,D]),linear(E),linear(G),linear(H),linear(I),linear(J),linear(M),linear(K),linear(L),linear(N),linear(O),linear(P),linear(Q),linear(R);mshare([[C],[E],[G],[H],[I],[J],[M],[K],[L],[N],[O],[P],[Q],[R]]),ground([B,D,F]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(M),linear(K),linear(L),linear(N),linear(O),linear(P),linear(Q),linear(R))),
    verb_form(G,H,I,N,D,O,F,P),
    true((mshare([[C],[C,F],[C,F,G],[C,F,G,H],[C,F,G,H,I],[C,F,G,H,I,N],[C,F,G,H,I,N,P],[C,F,G,H,I,P],[C,F,G,H,N],[C,F,G,H,N,P],[C,F,G,H,P],[C,F,G,I],[C,F,G,I,N],[C,F,G,I,N,P],[C,F,G,I,P],[C,F,G,N],[C,F,G,N,P],[C,F,G,P],[C,F,H],[C,F,H,I],[C,F,H,I,N],[C,F,H,I,N,P],[C,F,H,I,P],[C,F,H,N],[C,F,H,N,P],[C,F,H,P],[C,F,I],[C,F,I,N],[C,F,I,N,P],[C,F,I,P],[C,F,N],[C,F,N,P],[C,F,P],[E],[F],[F,G],[F,G,H],[F,G,H,I],[F,G,H,I,N],[F,G,H,I,N,P],[F,G,H,I,P],[F,G,H,N],[F,G,H,N,P],[F,G,H,P],[F,G,I],[F,G,I,N],[F,G,I,N,P],[F,G,I,P],[F,G,N],[F,G,N,P],[F,G,P],[F,H],[F,H,I],[F,H,I,N],[F,H,I,N,P],[F,H,I,P],[F,H,N],[F,H,N,P],[F,H,P],[F,I],[F,I,N],[F,I,N,P],[F,I,P],[F,N],[F,N,P],[F,P],[H],[I],[J],[M],[K],[L],[N],[Q],[R]]),ground([B,D,O]),linear(E),linear(J),linear(M),linear(K),linear(L),linear(Q),linear(R);mshare([[C],[E],[H],[I],[J],[M],[K],[L],[N],[Q],[R]]),ground([B,D,F,G,O,P]),linear(C),linear(E),linear(J),linear(M),linear(K),linear(L),linear(Q),linear(R))),
    verb_type(G,aux+Q),
    true((mshare([[C],[C,F],[C,F,H],[C,F,H,I],[C,F,H,I,N],[C,F,H,I,N,P],[C,F,H,I,P],[C,F,H,N],[C,F,H,N,P],[C,F,H,P],[C,F,I],[C,F,I,N],[C,F,I,N,P],[C,F,I,P],[C,F,N],[C,F,N,P],[C,F,P],[E],[F],[F,H],[F,H,I],[F,H,I,N],[F,H,I,N,P],[F,H,I,P],[F,H,N],[F,H,N,P],[F,H,P],[F,I],[F,I,N],[F,I,N,P],[F,I,P],[F,N],[F,N,P],[F,P],[H],[I],[J],[M],[K],[L],[N],[R]]),ground([B,D,G,O,Q]),linear(E),linear(J),linear(M),linear(K),linear(L),linear(R);mshare([[C],[E],[H],[I],[J],[M],[K],[L],[N],[R]]),ground([B,D,F,G,O,P,Q]),linear(C),linear(E),linear(J),linear(M),linear(K),linear(L),linear(R))),
    role(B,J,C),
    true((mshare([[C],[C,F],[C,F,H],[C,F,H,I],[C,F,H,I,N],[C,F,H,I,N,P],[C,F,H,I,P],[C,F,H,N],[C,F,H,N,P],[C,F,H,P],[C,F,I],[C,F,I,N],[C,F,I,N,P],[C,F,I,P],[C,F,N],[C,F,N,P],[C,F,P],[E],[F],[F,H],[F,H,I],[F,H,I,N],[F,H,I,N,P],[F,H,I,P],[F,H,N],[F,H,N,P],[F,H,P],[F,I],[F,I,N],[F,I,N,P],[F,I,P],[F,N],[F,N,P],[F,P],[H],[I],[J],[M],[K],[L],[N],[R]]),ground([B,D,G,O,Q]),linear(E),linear(M),linear(K),linear(L),linear(R);mshare([[C],[E],[H],[I],[J],[M],[K],[L],[N],[R]]),ground([B,D,F,G,O,P,Q]),linear(E),linear(M),linear(K),linear(L),linear(R))),
    neg(R,L,O,E,P,M),
    true((mshare([[C],[C,F],[C,F,H],[C,F,H,I],[C,F,H,I,M,L,N,P],[C,F,H,I,M,L,N,P,R],[C,F,H,I,M,L,P],[C,F,H,I,M,L,P,R],[C,F,H,I,M,N,P],[C,F,H,I,M,N,P,R],[C,F,H,I,M,P],[C,F,H,I,M,P,R],[C,F,H,I,L,N,P],[C,F,H,I,L,N,P,R],[C,F,H,I,L,P],[C,F,H,I,L,P,R],[C,F,H,I,N],[C,F,H,I,N,P],[C,F,H,I,N,P,R],[C,F,H,I,P],[C,F,H,I,P,R],[C,F,H,M,L,N,P],[C,F,H,M,L,N,P,R],[C,F,H,M,L,P],[C,F,H,M,L,P,R],[C,F,H,M,N,P],[C,F,H,M,N,P,R],[C,F,H,M,P],[C,F,H,M,P,R],[C,F,H,L,N,P],[C,F,H,L,N,P,R],[C,F,H,L,P],[C,F,H,L,P,R],[C,F,H,N],[C,F,H,N,P],[C,F,H,N,P,R],[C,F,H,P],[C,F,H,P,R],[C,F,I],[C,F,I,M,L,N,P],[C,F,I,M,L,N,P,R],[C,F,I,M,L,P],[C,F,I,M,L,P,R],[C,F,I,M,N,P],[C,F,I,M,N,P,R],[C,F,I,M,P],[C,F,I,M,P,R],[C,F,I,L,N,P],[C,F,I,L,N,P,R],[C,F,I,L,P],[C,F,I,L,P,R],[C,F,I,N],[C,F,I,N,P],[C,F,I,N,P,R],[C,F,I,P],[C,F,I,P,R],[C,F,M,L,N,P],[C,F,M,L,N,P,R],[C,F,M,L,P],[C,F,M,L,P,R],[C,F,M,N,P],[C,F,M,N,P,R],[C,F,M,P],[C,F,M,P,R],[C,F,L,N,P],[C,F,L,N,P,R],[C,F,L,P],[C,F,L,P,R],[C,F,N],[C,F,N,P],[C,F,N,P,R],[C,F,P],[C,F,P,R],[F],[F,H],[F,H,I],[F,H,I,M,L,N,P],[F,H,I,M,L,N,P,R],[F,H,I,M,L,P],[F,H,I,M,L,P,R],[F,H,I,M,N,P],[F,H,I,M,N,P,R],[F,H,I,M,P],[F,H,I,M,P,R],[F,H,I,L,N,P],[F,H,I,L,N,P,R],[F,H,I,L,P],[F,H,I,L,P,R],[F,H,I,N],[F,H,I,N,P],[F,H,I,N,P,R],[F,H,I,P],[F,H,I,P,R],[F,H,M,L,N,P],[F,H,M,L,N,P,R],[F,H,M,L,P],[F,H,M,L,P,R],[F,H,M,N,P],[F,H,M,N,P,R],[F,H,M,P],[F,H,M,P,R],[F,H,L,N,P],[F,H,L,N,P,R],[F,H,L,P],[F,H,L,P,R],[F,H,N],[F,H,N,P],[F,H,N,P,R],[F,H,P],[F,H,P,R],[F,I],[F,I,M,L,N,P],[F,I,M,L,N,P,R],[F,I,M,L,P],[F,I,M,L,P,R],[F,I,M,N,P],[F,I,M,N,P,R],[F,I,M,P],[F,I,M,P,R],[F,I,L,N,P],[F,I,L,N,P,R],[F,I,L,P],[F,I,L,P,R],[F,I,N],[F,I,N,P],[F,I,N,P,R],[F,I,P],[F,I,P,R],[F,M,L,N,P],[F,M,L,N,P,R],[F,M,L,P],[F,M,L,P,R],[F,M,N,P],[F,M,N,P,R],[F,M,P],[F,M,P,R],[F,L,N,P],[F,L,N,P,R],[F,L,P],[F,L,P,R],[F,N],[F,N,P],[F,N,P,R],[F,P],[F,P,R],[H],[I],[J],[K],[N],[R]]),ground([B,D,E,G,O,Q]),linear(K);mshare([[C],[H],[I],[J],[K],[N],[R]]),ground([B,D,E,F,G,M,L,O,P,Q]),linear(K))).

:- true pred imperative(_A,C,D,E,F)
   : ( mshare([[_A],[D],[F]]),
       ground([C,E]), linear(_A), linear(D), linear(F) )
   => ( mshare([[_A],[_A,F],[F]]),
        ground([C,D,E]) ).

imperative(imp(B),C,D,E,F) :-
    true((
        mshare([[D],[F],[B],[G],[H],[I]]),
        ground([C,E]),
        linear(D),
        linear(F),
        linear(B),
        linear(G),
        linear(H),
        linear(I)
    )),
    imperative_verb(C,G,E,H),
    true((
        mshare([[D],[F],[B],[I]]),
        ground([C,E,G,H]),
        linear(D),
        linear(F),
        linear(B),
        linear(I)
    )),
    s(B,I,G,D,H,F),
    true((
        mshare([[F],[F,B],[B]]),
        ground([C,D,E,G,H,I])
    )).

:- true pred imperative_verb(B,C,D,_A)
   : ( mshare([[C],[_A]]),
       ground([B,D]), linear(C), linear(_A) )
   => ground([B,C,D,_A]).

imperative_verb(B,C,D,x(nogap,terminal,you,x(nogap,nonterminal,verb_form(E,imp+fin,2+sin,main),F))) :-
    true((
        mshare([[C],[F],[E],[G],[H]]),
        ground([B,D]),
        linear(C),
        linear(F),
        linear(E),
        linear(G),
        linear(H)
    )),
    verb_form(E,inf,G,H,B,C,D,F),
    true((
        mshare([[G],[H]]),
        ground([B,C,D,F,E])
    )).

:- true pred s(_A,F,G,H,I,J)
   : ( mshare([[_A],[F],[H],[J]]),
       ground([G,I]), linear(_A), linear(F), linear(H), linear(J) )
   => ( mshare([[_A],[_A,J],[J]]),
        ground([F,G,H,I]) ).

:- true pred s(_A,F,G,H,I,J)
   : ( mshare([[_A],[F],[H],[I],[J]]),
       ground([G]), linear(_A), linear(F), linear(H), linear(J) )
   => ( mshare([[_A],[_A,I],[_A,I,J],[_A,J],[I],[I,J],[J]]),
        ground([F,G,H]) ).

s(s(B,C,D,E),F,G,H,I,J) :-
    true((mshare([[F],[H],[I],[J],[B],[C],[D],[E],[K],[L],[M],[N],[O],[P],[Q],[R],[S],[T],[U],[V],[W],[X]]),ground([G]),linear(F),linear(H),linear(J),linear(B),linear(C),linear(D),linear(E),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V),linear(W),linear(X);mshare([[F],[H],[J],[B],[C],[D],[E],[K],[L],[M],[N],[O],[P],[Q],[R],[S],[T],[U],[V],[W],[X]]),ground([G,I]),linear(F),linear(H),linear(J),linear(B),linear(C),linear(D),linear(E),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V),linear(W),linear(X))),
    subj(B,K,L,G,M,I,N),
    true((mshare([[F],[H],[I],[I,B],[I,B,K],[I,B,K,N],[I,B,N],[I,K],[I,K,N],[I,N],[J],[B],[B,K],[B,K,N],[B,N],[C],[D],[E],[K],[L],[N],[O],[P],[Q],[R],[S],[T],[U],[V],[W],[X]]),ground([G,M]),linear(F),linear(H),linear(J),linear(C),linear(D),linear(E),linear(L),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V),linear(W),linear(X);mshare([[F],[H],[J],[B],[B,K],[B,K,N],[B,N],[C],[D],[E],[K],[L],[N],[O],[P],[Q],[R],[S],[T],[U],[V],[W],[X]]),ground([G,I,M]),linear(F),linear(H),linear(J),linear(C),linear(D),linear(E),linear(L),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V),linear(W),linear(X))),
    verb(C,K,L,O,M,P,N,Q),
    true((mshare([[F],[H],[I],[I,B],[I,B,C,K,L,N],[I,B,C,K,L,N,O],[I,B,C,K,L,N,O,Q],[I,B,C,K,L,N,Q],[I,B,C,K,N],[I,B,C,K,N,O],[I,B,C,K,N,O,Q],[I,B,C,K,N,Q],[I,B,C,L,N],[I,B,C,L,N,O],[I,B,C,L,N,O,Q],[I,B,C,L,N,Q],[I,B,C,N],[I,B,C,N,O],[I,B,C,N,O,Q],[I,B,C,N,Q],[I,B,K],[I,B,K,L,N],[I,B,K,L,N,O],[I,B,K,L,N,O,Q],[I,B,K,L,N,Q],[I,B,K,N],[I,B,K,N,O],[I,B,K,N,O,Q],[I,B,K,N,Q],[I,B,L,N],[I,B,L,N,O],[I,B,L,N,O,Q],[I,B,L,N,Q],[I,B,N],[I,B,N,O],[I,B,N,O,Q],[I,B,N,Q],[I,C,K,L,N],[I,C,K,L,N,O],[I,C,K,L,N,O,Q],[I,C,K,L,N,Q],[I,C,K,N],[I,C,K,N,O],[I,C,K,N,O,Q],[I,C,K,N,Q],[I,C,L,N],[I,C,L,N,O],[I,C,L,N,O,Q],[I,C,L,N,Q],[I,C,N],[I,C,N,O],[I,C,N,O,Q],[I,C,N,Q],[I,K],[I,K,L,N],[I,K,L,N,O],[I,K,L,N,O,Q],[I,K,L,N,Q],[I,K,N],[I,K,N,O],[I,K,N,O,Q],[I,K,N,Q],[I,L,N],[I,L,N,O],[I,L,N,O,Q],[I,L,N,Q],[I,N],[I,N,O],[I,N,O,Q],[I,N,Q],[J],[B],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,Q],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,Q],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,Q],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,Q],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,Q],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,Q],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,Q],[B,N],[B,N,O],[B,N,O,Q],[B,N,Q],[C],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,Q],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,Q],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,Q],[C,N],[C,N,O],[C,N,O,Q],[C,N,Q],[D],[E],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,Q],[K,N],[K,N,O],[K,N,O,Q],[K,N,Q],[L,N],[L,N,O],[L,N,O,Q],[L,N,Q],[N],[N,O],[N,O,Q],[N,Q],[R],[S],[T],[U],[V],[W],[X]]),ground([G,M,P]),linear(F),linear(H),linear(J),linear(D),linear(E),linear(R),linear(S),linear(T),linear(U),linear(V),linear(W),linear(X);mshare([[F],[H],[J],[B],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,Q],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,Q],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,Q],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,Q],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,Q],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,Q],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,Q],[B,N],[B,N,O],[B,N,O,Q],[B,N,Q],[C],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,Q],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,Q],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,Q],[C,N],[C,N,O],[C,N,O,Q],[C,N,Q],[D],[E],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,Q],[K,N],[K,N,O],[K,N,O,Q],[K,N,Q],[L,N],[L,N,O],[L,N,O,Q],[L,N,Q],[N],[N,O],[N,O,Q],[N,Q],[R],[S],[T],[U],[V],[W],[X]]),ground([G,I,M,P]),linear(F),linear(H),linear(J),linear(D),linear(E),linear(R),linear(S),linear(T),linear(U),linear(V),linear(W),linear(X))),
    empty(R),
    true((mshare([[F],[H],[I],[I,B],[I,B,C,K,L,N],[I,B,C,K,L,N,O],[I,B,C,K,L,N,O,Q],[I,B,C,K,L,N,Q],[I,B,C,K,N],[I,B,C,K,N,O],[I,B,C,K,N,O,Q],[I,B,C,K,N,Q],[I,B,C,L,N],[I,B,C,L,N,O],[I,B,C,L,N,O,Q],[I,B,C,L,N,Q],[I,B,C,N],[I,B,C,N,O],[I,B,C,N,O,Q],[I,B,C,N,Q],[I,B,K],[I,B,K,L,N],[I,B,K,L,N,O],[I,B,K,L,N,O,Q],[I,B,K,L,N,Q],[I,B,K,N],[I,B,K,N,O],[I,B,K,N,O,Q],[I,B,K,N,Q],[I,B,L,N],[I,B,L,N,O],[I,B,L,N,O,Q],[I,B,L,N,Q],[I,B,N],[I,B,N,O],[I,B,N,O,Q],[I,B,N,Q],[I,C,K,L,N],[I,C,K,L,N,O],[I,C,K,L,N,O,Q],[I,C,K,L,N,Q],[I,C,K,N],[I,C,K,N,O],[I,C,K,N,O,Q],[I,C,K,N,Q],[I,C,L,N],[I,C,L,N,O],[I,C,L,N,O,Q],[I,C,L,N,Q],[I,C,N],[I,C,N,O],[I,C,N,O,Q],[I,C,N,Q],[I,K],[I,K,L,N],[I,K,L,N,O],[I,K,L,N,O,Q],[I,K,L,N,Q],[I,K,N],[I,K,N,O],[I,K,N,O,Q],[I,K,N,Q],[I,L,N],[I,L,N,O],[I,L,N,O,Q],[I,L,N,Q],[I,N],[I,N,O],[I,N,O,Q],[I,N,Q],[J],[B],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,Q],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,Q],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,Q],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,Q],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,Q],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,Q],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,Q],[B,N],[B,N,O],[B,N,O,Q],[B,N,Q],[C],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,Q],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,Q],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,Q],[C,N],[C,N,O],[C,N,O,Q],[C,N,Q],[D],[E],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,Q],[K,N],[K,N,O],[K,N,O,Q],[K,N,Q],[L,N],[L,N,O],[L,N,O,Q],[L,N,Q],[N],[N,O],[N,O,Q],[N,Q],[S],[T],[U],[V],[W],[X]]),ground([G,M,P,R]),linear(F),linear(H),linear(J),linear(D),linear(E),linear(S),linear(T),linear(U),linear(V),linear(W),linear(X);mshare([[F],[H],[J],[B],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,Q],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,Q],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,Q],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,Q],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,Q],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,Q],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,Q],[B,N],[B,N,O],[B,N,O,Q],[B,N,Q],[C],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,Q],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,Q],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,Q],[C,N],[C,N,O],[C,N,O,Q],[C,N,Q],[D],[E],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,Q],[K,N],[K,N,O],[K,N,O,Q],[K,N,Q],[L,N],[L,N,O],[L,N,O,Q],[L,N,Q],[N],[N,O],[N,O,Q],[N,Q],[S],[T],[U],[V],[W],[X]]),ground([G,I,M,P,R]),linear(F),linear(H),linear(J),linear(D),linear(E),linear(S),linear(T),linear(U),linear(V),linear(W),linear(X))),
    s_all(S),
    true((mshare([[F],[H],[I],[I,B],[I,B,C,K,L,N],[I,B,C,K,L,N,O],[I,B,C,K,L,N,O,Q],[I,B,C,K,L,N,Q],[I,B,C,K,N],[I,B,C,K,N,O],[I,B,C,K,N,O,Q],[I,B,C,K,N,Q],[I,B,C,L,N],[I,B,C,L,N,O],[I,B,C,L,N,O,Q],[I,B,C,L,N,Q],[I,B,C,N],[I,B,C,N,O],[I,B,C,N,O,Q],[I,B,C,N,Q],[I,B,K],[I,B,K,L,N],[I,B,K,L,N,O],[I,B,K,L,N,O,Q],[I,B,K,L,N,Q],[I,B,K,N],[I,B,K,N,O],[I,B,K,N,O,Q],[I,B,K,N,Q],[I,B,L,N],[I,B,L,N,O],[I,B,L,N,O,Q],[I,B,L,N,Q],[I,B,N],[I,B,N,O],[I,B,N,O,Q],[I,B,N,Q],[I,C,K,L,N],[I,C,K,L,N,O],[I,C,K,L,N,O,Q],[I,C,K,L,N,Q],[I,C,K,N],[I,C,K,N,O],[I,C,K,N,O,Q],[I,C,K,N,Q],[I,C,L,N],[I,C,L,N,O],[I,C,L,N,O,Q],[I,C,L,N,Q],[I,C,N],[I,C,N,O],[I,C,N,O,Q],[I,C,N,Q],[I,K],[I,K,L,N],[I,K,L,N,O],[I,K,L,N,O,Q],[I,K,L,N,Q],[I,K,N],[I,K,N,O],[I,K,N,O,Q],[I,K,N,Q],[I,L,N],[I,L,N,O],[I,L,N,O,Q],[I,L,N,Q],[I,N],[I,N,O],[I,N,O,Q],[I,N,Q],[J],[B],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,Q],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,Q],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,Q],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,Q],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,Q],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,Q],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,Q],[B,N],[B,N,O],[B,N,O,Q],[B,N,Q],[C],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,Q],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,Q],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,Q],[C,N],[C,N,O],[C,N,O,Q],[C,N,Q],[D],[E],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,Q],[K,N],[K,N,O],[K,N,O,Q],[K,N,Q],[L,N],[L,N,O],[L,N,O,Q],[L,N,Q],[N],[N,O],[N,O,Q],[N,Q],[T],[U],[V],[W],[X]]),ground([G,M,P,R,S]),linear(F),linear(H),linear(J),linear(D),linear(E),linear(T),linear(U),linear(V),linear(W),linear(X);mshare([[F],[H],[J],[B],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,Q],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,Q],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,Q],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,Q],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,Q],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,Q],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,Q],[B,N],[B,N,O],[B,N,O,Q],[B,N,Q],[C],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,Q],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,Q],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,Q],[C,N],[C,N,O],[C,N,O,Q],[C,N,Q],[D],[E],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,Q],[K,N],[K,N,O],[K,N,O,Q],[K,N,Q],[L,N],[L,N,O],[L,N,O,Q],[L,N,Q],[N],[N,O],[N,O,Q],[N,Q],[T],[U],[V],[W],[X]]),ground([G,I,M,P,R,S]),linear(F),linear(H),linear(J),linear(D),linear(E),linear(T),linear(U),linear(V),linear(W),linear(X))),
    verb_args(L,O,D,R,T,P,U,Q,V),
    true((mshare([[F],[H],[I],[I,B],[I,B,C,D,K,L,N,O,Q],[I,B,C,D,K,L,N,O,Q,T],[I,B,C,D,K,L,N,O,Q,T,V],[I,B,C,D,K,L,N,O,Q,V],[I,B,C,D,K,L,N,Q],[I,B,C,D,K,L,N,Q,T],[I,B,C,D,K,L,N,Q,T,V],[I,B,C,D,K,L,N,Q,V],[I,B,C,D,K,N,O,Q],[I,B,C,D,K,N,O,Q,T],[I,B,C,D,K,N,O,Q,T,V],[I,B,C,D,K,N,O,Q,V],[I,B,C,D,K,N,Q],[I,B,C,D,K,N,Q,T],[I,B,C,D,K,N,Q,T,V],[I,B,C,D,K,N,Q,V],[I,B,C,D,L,N,O,Q],[I,B,C,D,L,N,O,Q,T],[I,B,C,D,L,N,O,Q,T,V],[I,B,C,D,L,N,O,Q,V],[I,B,C,D,L,N,Q],[I,B,C,D,L,N,Q,T],[I,B,C,D,L,N,Q,T,V],[I,B,C,D,L,N,Q,V],[I,B,C,D,N,O,Q],[I,B,C,D,N,O,Q,T],[I,B,C,D,N,O,Q,T,V],[I,B,C,D,N,O,Q,V],[I,B,C,D,N,Q],[I,B,C,D,N,Q,T],[I,B,C,D,N,Q,T,V],[I,B,C,D,N,Q,V],[I,B,C,K,L,N],[I,B,C,K,L,N,O],[I,B,C,K,L,N,O,Q],[I,B,C,K,L,N,O,Q,T],[I,B,C,K,L,N,O,Q,T,V],[I,B,C,K,L,N,O,Q,V],[I,B,C,K,L,N,Q],[I,B,C,K,L,N,Q,T],[I,B,C,K,L,N,Q,T,V],[I,B,C,K,L,N,Q,V],[I,B,C,K,N],[I,B,C,K,N,O],[I,B,C,K,N,O,Q],[I,B,C,K,N,O,Q,T],[I,B,C,K,N,O,Q,T,V],[I,B,C,K,N,O,Q,V],[I,B,C,K,N,Q],[I,B,C,K,N,Q,T],[I,B,C,K,N,Q,T,V],[I,B,C,K,N,Q,V],[I,B,C,L,N],[I,B,C,L,N,O],[I,B,C,L,N,O,Q],[I,B,C,L,N,O,Q,T],[I,B,C,L,N,O,Q,T,V],[I,B,C,L,N,O,Q,V],[I,B,C,L,N,Q],[I,B,C,L,N,Q,T],[I,B,C,L,N,Q,T,V],[I,B,C,L,N,Q,V],[I,B,C,N],[I,B,C,N,O],[I,B,C,N,O,Q],[I,B,C,N,O,Q,T],[I,B,C,N,O,Q,T,V],[I,B,C,N,O,Q,V],[I,B,C,N,Q],[I,B,C,N,Q,T],[I,B,C,N,Q,T,V],[I,B,C,N,Q,V],[I,B,D,K,L,N,O,Q],[I,B,D,K,L,N,O,Q,T],[I,B,D,K,L,N,O,Q,T,V],[I,B,D,K,L,N,O,Q,V],[I,B,D,K,L,N,Q],[I,B,D,K,L,N,Q,T],[I,B,D,K,L,N,Q,T,V],[I,B,D,K,L,N,Q,V],[I,B,D,K,N,O,Q],[I,B,D,K,N,O,Q,T],[I,B,D,K,N,O,Q,T,V],[I,B,D,K,N,O,Q,V],[I,B,D,K,N,Q],[I,B,D,K,N,Q,T],[I,B,D,K,N,Q,T,V],[I,B,D,K,N,Q,V],[I,B,D,L,N,O,Q],[I,B,D,L,N,O,Q,T],[I,B,D,L,N,O,Q,T,V],[I,B,D,L,N,O,Q,V],[I,B,D,L,N,Q],[I,B,D,L,N,Q,T],[I,B,D,L,N,Q,T,V],[I,B,D,L,N,Q,V],[I,B,D,N,O,Q],[I,B,D,N,O,Q,T],[I,B,D,N,O,Q,T,V],[I,B,D,N,O,Q,V],[I,B,D,N,Q],[I,B,D,N,Q,T],[I,B,D,N,Q,T,V],[I,B,D,N,Q,V],[I,B,K],[I,B,K,L,N],[I,B,K,L,N,O],[I,B,K,L,N,O,Q],[I,B,K,L,N,O,Q,T],[I,B,K,L,N,O,Q,T,V],[I,B,K,L,N,O,Q,V],[I,B,K,L,N,Q],[I,B,K,L,N,Q,T],[I,B,K,L,N,Q,T,V],[I,B,K,L,N,Q,V],[I,B,K,N],[I,B,K,N,O],[I,B,K,N,O,Q],[I,B,K,N,O,Q,T],[I,B,K,N,O,Q,T,V],[I,B,K,N,O,Q,V],[I,B,K,N,Q],[I,B,K,N,Q,T],[I,B,K,N,Q,T,V],[I,B,K,N,Q,V],[I,B,L,N],[I,B,L,N,O],[I,B,L,N,O,Q],[I,B,L,N,O,Q,T],[I,B,L,N,O,Q,T,V],[I,B,L,N,O,Q,V],[I,B,L,N,Q],[I,B,L,N,Q,T],[I,B,L,N,Q,T,V],[I,B,L,N,Q,V],[I,B,N],[I,B,N,O],[I,B,N,O,Q],[I,B,N,O,Q,T],[I,B,N,O,Q,T,V],[I,B,N,O,Q,V],[I,B,N,Q],[I,B,N,Q,T],[I,B,N,Q,T,V],[I,B,N,Q,V],[I,C,D,K,L,N,O,Q],[I,C,D,K,L,N,O,Q,T],[I,C,D,K,L,N,O,Q,T,V],[I,C,D,K,L,N,O,Q,V],[I,C,D,K,L,N,Q],[I,C,D,K,L,N,Q,T],[I,C,D,K,L,N,Q,T,V],[I,C,D,K,L,N,Q,V],[I,C,D,K,N,O,Q],[I,C,D,K,N,O,Q,T],[I,C,D,K,N,O,Q,T,V],[I,C,D,K,N,O,Q,V],[I,C,D,K,N,Q],[I,C,D,K,N,Q,T],[I,C,D,K,N,Q,T,V],[I,C,D,K,N,Q,V],[I,C,D,L,N,O,Q],[I,C,D,L,N,O,Q,T],[I,C,D,L,N,O,Q,T,V],[I,C,D,L,N,O,Q,V],[I,C,D,L,N,Q],[I,C,D,L,N,Q,T],[I,C,D,L,N,Q,T,V],[I,C,D,L,N,Q,V],[I,C,D,N,O,Q],[I,C,D,N,O,Q,T],[I,C,D,N,O,Q,T,V],[I,C,D,N,O,Q,V],[I,C,D,N,Q],[I,C,D,N,Q,T],[I,C,D,N,Q,T,V],[I,C,D,N,Q,V],[I,C,K,L,N],[I,C,K,L,N,O],[I,C,K,L,N,O,Q],[I,C,K,L,N,O,Q,T],[I,C,K,L,N,O,Q,T,V],[I,C,K,L,N,O,Q,V],[I,C,K,L,N,Q],[I,C,K,L,N,Q,T],[I,C,K,L,N,Q,T,V],[I,C,K,L,N,Q,V],[I,C,K,N],[I,C,K,N,O],[I,C,K,N,O,Q],[I,C,K,N,O,Q,T],[I,C,K,N,O,Q,T,V],[I,C,K,N,O,Q,V],[I,C,K,N,Q],[I,C,K,N,Q,T],[I,C,K,N,Q,T,V],[I,C,K,N,Q,V],[I,C,L,N],[I,C,L,N,O],[I,C,L,N,O,Q],[I,C,L,N,O,Q,T],[I,C,L,N,O,Q,T,V],[I,C,L,N,O,Q,V],[I,C,L,N,Q],[I,C,L,N,Q,T],[I,C,L,N,Q,T,V],[I,C,L,N,Q,V],[I,C,N],[I,C,N,O],[I,C,N,O,Q],[I,C,N,O,Q,T],[I,C,N,O,Q,T,V],[I,C,N,O,Q,V],[I,C,N,Q],[I,C,N,Q,T],[I,C,N,Q,T,V],[I,C,N,Q,V],[I,D,K,L,N,O,Q],[I,D,K,L,N,O,Q,T],[I,D,K,L,N,O,Q,T,V],[I,D,K,L,N,O,Q,V],[I,D,K,L,N,Q],[I,D,K,L,N,Q,T],[I,D,K,L,N,Q,T,V],[I,D,K,L,N,Q,V],[I,D,K,N,O,Q],[I,D,K,N,O,Q,T],[I,D,K,N,O,Q,T,V],[I,D,K,N,O,Q,V],[I,D,K,N,Q],[I,D,K,N,Q,T],[I,D,K,N,Q,T,V],[I,D,K,N,Q,V],[I,D,L,N,O,Q],[I,D,L,N,O,Q,T],[I,D,L,N,O,Q,T,V],[I,D,L,N,O,Q,V],[I,D,L,N,Q],[I,D,L,N,Q,T],[I,D,L,N,Q,T,V],[I,D,L,N,Q,V],[I,D,N,O,Q],[I,D,N,O,Q,T],[I,D,N,O,Q,T,V],[I,D,N,O,Q,V],[I,D,N,Q],[I,D,N,Q,T],[I,D,N,Q,T,V],[I,D,N,Q,V],[I,K],[I,K,L,N],[I,K,L,N,O],[I,K,L,N,O,Q],[I,K,L,N,O,Q,T],[I,K,L,N,O,Q,T,V],[I,K,L,N,O,Q,V],[I,K,L,N,Q],[I,K,L,N,Q,T],[I,K,L,N,Q,T,V],[I,K,L,N,Q,V],[I,K,N],[I,K,N,O],[I,K,N,O,Q],[I,K,N,O,Q,T],[I,K,N,O,Q,T,V],[I,K,N,O,Q,V],[I,K,N,Q],[I,K,N,Q,T],[I,K,N,Q,T,V],[I,K,N,Q,V],[I,L,N],[I,L,N,O],[I,L,N,O,Q],[I,L,N,O,Q,T],[I,L,N,O,Q,T,V],[I,L,N,O,Q,V],[I,L,N,Q],[I,L,N,Q,T],[I,L,N,Q,T,V],[I,L,N,Q,V],[I,N],[I,N,O],[I,N,O,Q],[I,N,O,Q,T],[I,N,O,Q,T,V],[I,N,O,Q,V],[I,N,Q],[I,N,Q,T],[I,N,Q,T,V],[I,N,Q,V],[J],[B],[B,C,D,K,L,N,O,Q],[B,C,D,K,L,N,O,Q,T],[B,C,D,K,L,N,O,Q,T,V],[B,C,D,K,L,N,O,Q,V],[B,C,D,K,L,N,Q],[B,C,D,K,L,N,Q,T],[B,C,D,K,L,N,Q,T,V],[B,C,D,K,L,N,Q,V],[B,C,D,K,N,O,Q],[B,C,D,K,N,O,Q,T],[B,C,D,K,N,O,Q,T,V],[B,C,D,K,N,O,Q,V],[B,C,D,K,N,Q],[B,C,D,K,N,Q,T],[B,C,D,K,N,Q,T,V],[B,C,D,K,N,Q,V],[B,C,D,L,N,O,Q],[B,C,D,L,N,O,Q,T],[B,C,D,L,N,O,Q,T,V],[B,C,D,L,N,O,Q,V],[B,C,D,L,N,Q],[B,C,D,L,N,Q,T],[B,C,D,L,N,Q,T,V],[B,C,D,L,N,Q,V],[B,C,D,N,O,Q],[B,C,D,N,O,Q,T],[B,C,D,N,O,Q,T,V],[B,C,D,N,O,Q,V],[B,C,D,N,Q],[B,C,D,N,Q,T],[B,C,D,N,Q,T,V],[B,C,D,N,Q,V],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,O,Q,T],[B,C,K,L,N,O,Q,T,V],[B,C,K,L,N,O,Q,V],[B,C,K,L,N,Q],[B,C,K,L,N,Q,T],[B,C,K,L,N,Q,T,V],[B,C,K,L,N,Q,V],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,O,Q,T],[B,C,K,N,O,Q,T,V],[B,C,K,N,O,Q,V],[B,C,K,N,Q],[B,C,K,N,Q,T],[B,C,K,N,Q,T,V],[B,C,K,N,Q,V],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,O,Q,T],[B,C,L,N,O,Q,T,V],[B,C,L,N,O,Q,V],[B,C,L,N,Q],[B,C,L,N,Q,T],[B,C,L,N,Q,T,V],[B,C,L,N,Q,V],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,O,Q,T],[B,C,N,O,Q,T,V],[B,C,N,O,Q,V],[B,C,N,Q],[B,C,N,Q,T],[B,C,N,Q,T,V],[B,C,N,Q,V],[B,D,K,L,N,O,Q],[B,D,K,L,N,O,Q,T],[B,D,K,L,N,O,Q,T,V],[B,D,K,L,N,O,Q,V],[B,D,K,L,N,Q],[B,D,K,L,N,Q,T],[B,D,K,L,N,Q,T,V],[B,D,K,L,N,Q,V],[B,D,K,N,O,Q],[B,D,K,N,O,Q,T],[B,D,K,N,O,Q,T,V],[B,D,K,N,O,Q,V],[B,D,K,N,Q],[B,D,K,N,Q,T],[B,D,K,N,Q,T,V],[B,D,K,N,Q,V],[B,D,L,N,O,Q],[B,D,L,N,O,Q,T],[B,D,L,N,O,Q,T,V],[B,D,L,N,O,Q,V],[B,D,L,N,Q],[B,D,L,N,Q,T],[B,D,L,N,Q,T,V],[B,D,L,N,Q,V],[B,D,N,O,Q],[B,D,N,O,Q,T],[B,D,N,O,Q,T,V],[B,D,N,O,Q,V],[B,D,N,Q],[B,D,N,Q,T],[B,D,N,Q,T,V],[B,D,N,Q,V],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,O,Q,T],[B,K,L,N,O,Q,T,V],[B,K,L,N,O,Q,V],[B,K,L,N,Q],[B,K,L,N,Q,T],[B,K,L,N,Q,T,V],[B,K,L,N,Q,V],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,O,Q,T],[B,K,N,O,Q,T,V],[B,K,N,O,Q,V],[B,K,N,Q],[B,K,N,Q,T],[B,K,N,Q,T,V],[B,K,N,Q,V],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,O,Q,T],[B,L,N,O,Q,T,V],[B,L,N,O,Q,V],[B,L,N,Q],[B,L,N,Q,T],[B,L,N,Q,T,V],[B,L,N,Q,V],[B,N],[B,N,O],[B,N,O,Q],[B,N,O,Q,T],[B,N,O,Q,T,V],[B,N,O,Q,V],[B,N,Q],[B,N,Q,T],[B,N,Q,T,V],[B,N,Q,V],[C],[C,D,K,L,N,O,Q],[C,D,K,L,N,O,Q,T],[C,D,K,L,N,O,Q,T,V],[C,D,K,L,N,O,Q,V],[C,D,K,L,N,Q],[C,D,K,L,N,Q,T],[C,D,K,L,N,Q,T,V],[C,D,K,L,N,Q,V],[C,D,K,N,O,Q],[C,D,K,N,O,Q,T],[C,D,K,N,O,Q,T,V],[C,D,K,N,O,Q,V],[C,D,K,N,Q],[C,D,K,N,Q,T],[C,D,K,N,Q,T,V],[C,D,K,N,Q,V],[C,D,L,N,O,Q],[C,D,L,N,O,Q,T],[C,D,L,N,O,Q,T,V],[C,D,L,N,O,Q,V],[C,D,L,N,Q],[C,D,L,N,Q,T],[C,D,L,N,Q,T,V],[C,D,L,N,Q,V],[C,D,N,O,Q],[C,D,N,O,Q,T],[C,D,N,O,Q,T,V],[C,D,N,O,Q,V],[C,D,N,Q],[C,D,N,Q,T],[C,D,N,Q,T,V],[C,D,N,Q,V],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,O,Q,T],[C,K,L,N,O,Q,T,V],[C,K,L,N,O,Q,V],[C,K,L,N,Q],[C,K,L,N,Q,T],[C,K,L,N,Q,T,V],[C,K,L,N,Q,V],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,O,Q,T],[C,K,N,O,Q,T,V],[C,K,N,O,Q,V],[C,K,N,Q],[C,K,N,Q,T],[C,K,N,Q,T,V],[C,K,N,Q,V],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,O,Q,T],[C,L,N,O,Q,T,V],[C,L,N,O,Q,V],[C,L,N,Q],[C,L,N,Q,T],[C,L,N,Q,T,V],[C,L,N,Q,V],[C,N],[C,N,O],[C,N,O,Q],[C,N,O,Q,T],[C,N,O,Q,T,V],[C,N,O,Q,V],[C,N,Q],[C,N,Q,T],[C,N,Q,T,V],[C,N,Q,V],[D],[D,K,L,N,O,Q],[D,K,L,N,O,Q,T],[D,K,L,N,O,Q,T,V],[D,K,L,N,O,Q,V],[D,K,L,N,Q],[D,K,L,N,Q,T],[D,K,L,N,Q,T,V],[D,K,L,N,Q,V],[D,K,N,O,Q],[D,K,N,O,Q,T],[D,K,N,O,Q,T,V],[D,K,N,O,Q,V],[D,K,N,Q],[D,K,N,Q,T],[D,K,N,Q,T,V],[D,K,N,Q,V],[D,L,N,O,Q],[D,L,N,O,Q,T],[D,L,N,O,Q,T,V],[D,L,N,O,Q,V],[D,L,N,Q],[D,L,N,Q,T],[D,L,N,Q,T,V],[D,L,N,Q,V],[D,N,O,Q],[D,N,O,Q,T],[D,N,O,Q,T,V],[D,N,O,Q,V],[D,N,Q],[D,N,Q,T],[D,N,Q,T,V],[D,N,Q,V],[D,T],[D,T,V],[D,V],[E],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,O,Q,T],[K,L,N,O,Q,T,V],[K,L,N,O,Q,V],[K,L,N,Q],[K,L,N,Q,T],[K,L,N,Q,T,V],[K,L,N,Q,V],[K,N],[K,N,O],[K,N,O,Q],[K,N,O,Q,T],[K,N,O,Q,T,V],[K,N,O,Q,V],[K,N,Q],[K,N,Q,T],[K,N,Q,T,V],[K,N,Q,V],[L,N],[L,N,O],[L,N,O,Q],[L,N,O,Q,T],[L,N,O,Q,T,V],[L,N,O,Q,V],[L,N,Q],[L,N,Q,T],[L,N,Q,T,V],[L,N,Q,V],[N],[N,O],[N,O,Q],[N,O,Q,T],[N,O,Q,T,V],[N,O,Q,V],[N,Q],[N,Q,T],[N,Q,T,V],[N,Q,V],[T],[T,V],[V],[W],[X]]),ground([G,M,P,R,S,U]),linear(F),linear(H),linear(J),linear(E),linear(W),linear(X);mshare([[F],[H],[J],[B],[B,C,D,K,L,N,O,Q],[B,C,D,K,L,N,O,Q,T],[B,C,D,K,L,N,O,Q,T,V],[B,C,D,K,L,N,O,Q,V],[B,C,D,K,L,N,Q],[B,C,D,K,L,N,Q,T],[B,C,D,K,L,N,Q,T,V],[B,C,D,K,L,N,Q,V],[B,C,D,K,N,O,Q],[B,C,D,K,N,O,Q,T],[B,C,D,K,N,O,Q,T,V],[B,C,D,K,N,O,Q,V],[B,C,D,K,N,Q],[B,C,D,K,N,Q,T],[B,C,D,K,N,Q,T,V],[B,C,D,K,N,Q,V],[B,C,D,L,N,O,Q],[B,C,D,L,N,O,Q,T],[B,C,D,L,N,O,Q,T,V],[B,C,D,L,N,O,Q,V],[B,C,D,L,N,Q],[B,C,D,L,N,Q,T],[B,C,D,L,N,Q,T,V],[B,C,D,L,N,Q,V],[B,C,D,N,O,Q],[B,C,D,N,O,Q,T],[B,C,D,N,O,Q,T,V],[B,C,D,N,O,Q,V],[B,C,D,N,Q],[B,C,D,N,Q,T],[B,C,D,N,Q,T,V],[B,C,D,N,Q,V],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,O,Q,T],[B,C,K,L,N,O,Q,T,V],[B,C,K,L,N,O,Q,V],[B,C,K,L,N,Q],[B,C,K,L,N,Q,T],[B,C,K,L,N,Q,T,V],[B,C,K,L,N,Q,V],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,O,Q,T],[B,C,K,N,O,Q,T,V],[B,C,K,N,O,Q,V],[B,C,K,N,Q],[B,C,K,N,Q,T],[B,C,K,N,Q,T,V],[B,C,K,N,Q,V],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,O,Q,T],[B,C,L,N,O,Q,T,V],[B,C,L,N,O,Q,V],[B,C,L,N,Q],[B,C,L,N,Q,T],[B,C,L,N,Q,T,V],[B,C,L,N,Q,V],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,O,Q,T],[B,C,N,O,Q,T,V],[B,C,N,O,Q,V],[B,C,N,Q],[B,C,N,Q,T],[B,C,N,Q,T,V],[B,C,N,Q,V],[B,D,K,L,N,O,Q],[B,D,K,L,N,O,Q,T],[B,D,K,L,N,O,Q,T,V],[B,D,K,L,N,O,Q,V],[B,D,K,L,N,Q],[B,D,K,L,N,Q,T],[B,D,K,L,N,Q,T,V],[B,D,K,L,N,Q,V],[B,D,K,N,O,Q],[B,D,K,N,O,Q,T],[B,D,K,N,O,Q,T,V],[B,D,K,N,O,Q,V],[B,D,K,N,Q],[B,D,K,N,Q,T],[B,D,K,N,Q,T,V],[B,D,K,N,Q,V],[B,D,L,N,O,Q],[B,D,L,N,O,Q,T],[B,D,L,N,O,Q,T,V],[B,D,L,N,O,Q,V],[B,D,L,N,Q],[B,D,L,N,Q,T],[B,D,L,N,Q,T,V],[B,D,L,N,Q,V],[B,D,N,O,Q],[B,D,N,O,Q,T],[B,D,N,O,Q,T,V],[B,D,N,O,Q,V],[B,D,N,Q],[B,D,N,Q,T],[B,D,N,Q,T,V],[B,D,N,Q,V],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,O,Q,T],[B,K,L,N,O,Q,T,V],[B,K,L,N,O,Q,V],[B,K,L,N,Q],[B,K,L,N,Q,T],[B,K,L,N,Q,T,V],[B,K,L,N,Q,V],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,O,Q,T],[B,K,N,O,Q,T,V],[B,K,N,O,Q,V],[B,K,N,Q],[B,K,N,Q,T],[B,K,N,Q,T,V],[B,K,N,Q,V],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,O,Q,T],[B,L,N,O,Q,T,V],[B,L,N,O,Q,V],[B,L,N,Q],[B,L,N,Q,T],[B,L,N,Q,T,V],[B,L,N,Q,V],[B,N],[B,N,O],[B,N,O,Q],[B,N,O,Q,T],[B,N,O,Q,T,V],[B,N,O,Q,V],[B,N,Q],[B,N,Q,T],[B,N,Q,T,V],[B,N,Q,V],[C],[C,D,K,L,N,O,Q],[C,D,K,L,N,O,Q,T],[C,D,K,L,N,O,Q,T,V],[C,D,K,L,N,O,Q,V],[C,D,K,L,N,Q],[C,D,K,L,N,Q,T],[C,D,K,L,N,Q,T,V],[C,D,K,L,N,Q,V],[C,D,K,N,O,Q],[C,D,K,N,O,Q,T],[C,D,K,N,O,Q,T,V],[C,D,K,N,O,Q,V],[C,D,K,N,Q],[C,D,K,N,Q,T],[C,D,K,N,Q,T,V],[C,D,K,N,Q,V],[C,D,L,N,O,Q],[C,D,L,N,O,Q,T],[C,D,L,N,O,Q,T,V],[C,D,L,N,O,Q,V],[C,D,L,N,Q],[C,D,L,N,Q,T],[C,D,L,N,Q,T,V],[C,D,L,N,Q,V],[C,D,N,O,Q],[C,D,N,O,Q,T],[C,D,N,O,Q,T,V],[C,D,N,O,Q,V],[C,D,N,Q],[C,D,N,Q,T],[C,D,N,Q,T,V],[C,D,N,Q,V],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,O,Q,T],[C,K,L,N,O,Q,T,V],[C,K,L,N,O,Q,V],[C,K,L,N,Q],[C,K,L,N,Q,T],[C,K,L,N,Q,T,V],[C,K,L,N,Q,V],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,O,Q,T],[C,K,N,O,Q,T,V],[C,K,N,O,Q,V],[C,K,N,Q],[C,K,N,Q,T],[C,K,N,Q,T,V],[C,K,N,Q,V],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,O,Q,T],[C,L,N,O,Q,T,V],[C,L,N,O,Q,V],[C,L,N,Q],[C,L,N,Q,T],[C,L,N,Q,T,V],[C,L,N,Q,V],[C,N],[C,N,O],[C,N,O,Q],[C,N,O,Q,T],[C,N,O,Q,T,V],[C,N,O,Q,V],[C,N,Q],[C,N,Q,T],[C,N,Q,T,V],[C,N,Q,V],[D],[D,K,L,N,O,Q],[D,K,L,N,O,Q,T],[D,K,L,N,O,Q,T,V],[D,K,L,N,O,Q,V],[D,K,L,N,Q],[D,K,L,N,Q,T],[D,K,L,N,Q,T,V],[D,K,L,N,Q,V],[D,K,N,O,Q],[D,K,N,O,Q,T],[D,K,N,O,Q,T,V],[D,K,N,O,Q,V],[D,K,N,Q],[D,K,N,Q,T],[D,K,N,Q,T,V],[D,K,N,Q,V],[D,L,N,O,Q],[D,L,N,O,Q,T],[D,L,N,O,Q,T,V],[D,L,N,O,Q,V],[D,L,N,Q],[D,L,N,Q,T],[D,L,N,Q,T,V],[D,L,N,Q,V],[D,N,O,Q],[D,N,O,Q,T],[D,N,O,Q,T,V],[D,N,O,Q,V],[D,N,Q],[D,N,Q,T],[D,N,Q,T,V],[D,N,Q,V],[D,T],[D,T,V],[D,V],[E],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,O,Q,T],[K,L,N,O,Q,T,V],[K,L,N,O,Q,V],[K,L,N,Q],[K,L,N,Q,T],[K,L,N,Q,T,V],[K,L,N,Q,V],[K,N],[K,N,O],[K,N,O,Q],[K,N,O,Q,T],[K,N,O,Q,T,V],[K,N,O,Q,V],[K,N,Q],[K,N,Q,T],[K,N,Q,T,V],[K,N,Q,V],[L,N],[L,N,O],[L,N,O,Q],[L,N,O,Q,T],[L,N,O,Q,T,V],[L,N,O,Q,V],[L,N,Q],[L,N,Q,T],[L,N,Q,T,V],[L,N,Q,V],[N],[N,O],[N,O,Q],[N,O,Q,T],[N,O,Q,T,V],[N,O,Q,V],[N,Q],[N,Q,T],[N,Q,T,V],[N,Q,V],[T],[T,V],[V],[W],[X]]),ground([G,I,M,P,R,S,U]),linear(F),linear(H),linear(J),linear(E),linear(W),linear(X))),
    minus(S,T,W),
    true((mshare([[F],[H],[I],[I,B],[I,B,C,D,K,L,N,O,Q],[I,B,C,D,K,L,N,O,Q,V],[I,B,C,D,K,L,N,Q],[I,B,C,D,K,L,N,Q,V],[I,B,C,D,K,N,O,Q],[I,B,C,D,K,N,O,Q,V],[I,B,C,D,K,N,Q],[I,B,C,D,K,N,Q,V],[I,B,C,D,L,N,O,Q],[I,B,C,D,L,N,O,Q,V],[I,B,C,D,L,N,Q],[I,B,C,D,L,N,Q,V],[I,B,C,D,N,O,Q],[I,B,C,D,N,O,Q,V],[I,B,C,D,N,Q],[I,B,C,D,N,Q,V],[I,B,C,K,L,N],[I,B,C,K,L,N,O],[I,B,C,K,L,N,O,Q],[I,B,C,K,L,N,O,Q,V],[I,B,C,K,L,N,Q],[I,B,C,K,L,N,Q,V],[I,B,C,K,N],[I,B,C,K,N,O],[I,B,C,K,N,O,Q],[I,B,C,K,N,O,Q,V],[I,B,C,K,N,Q],[I,B,C,K,N,Q,V],[I,B,C,L,N],[I,B,C,L,N,O],[I,B,C,L,N,O,Q],[I,B,C,L,N,O,Q,V],[I,B,C,L,N,Q],[I,B,C,L,N,Q,V],[I,B,C,N],[I,B,C,N,O],[I,B,C,N,O,Q],[I,B,C,N,O,Q,V],[I,B,C,N,Q],[I,B,C,N,Q,V],[I,B,D,K,L,N,O,Q],[I,B,D,K,L,N,O,Q,V],[I,B,D,K,L,N,Q],[I,B,D,K,L,N,Q,V],[I,B,D,K,N,O,Q],[I,B,D,K,N,O,Q,V],[I,B,D,K,N,Q],[I,B,D,K,N,Q,V],[I,B,D,L,N,O,Q],[I,B,D,L,N,O,Q,V],[I,B,D,L,N,Q],[I,B,D,L,N,Q,V],[I,B,D,N,O,Q],[I,B,D,N,O,Q,V],[I,B,D,N,Q],[I,B,D,N,Q,V],[I,B,K],[I,B,K,L,N],[I,B,K,L,N,O],[I,B,K,L,N,O,Q],[I,B,K,L,N,O,Q,V],[I,B,K,L,N,Q],[I,B,K,L,N,Q,V],[I,B,K,N],[I,B,K,N,O],[I,B,K,N,O,Q],[I,B,K,N,O,Q,V],[I,B,K,N,Q],[I,B,K,N,Q,V],[I,B,L,N],[I,B,L,N,O],[I,B,L,N,O,Q],[I,B,L,N,O,Q,V],[I,B,L,N,Q],[I,B,L,N,Q,V],[I,B,N],[I,B,N,O],[I,B,N,O,Q],[I,B,N,O,Q,V],[I,B,N,Q],[I,B,N,Q,V],[I,C,D,K,L,N,O,Q],[I,C,D,K,L,N,O,Q,V],[I,C,D,K,L,N,Q],[I,C,D,K,L,N,Q,V],[I,C,D,K,N,O,Q],[I,C,D,K,N,O,Q,V],[I,C,D,K,N,Q],[I,C,D,K,N,Q,V],[I,C,D,L,N,O,Q],[I,C,D,L,N,O,Q,V],[I,C,D,L,N,Q],[I,C,D,L,N,Q,V],[I,C,D,N,O,Q],[I,C,D,N,O,Q,V],[I,C,D,N,Q],[I,C,D,N,Q,V],[I,C,K,L,N],[I,C,K,L,N,O],[I,C,K,L,N,O,Q],[I,C,K,L,N,O,Q,V],[I,C,K,L,N,Q],[I,C,K,L,N,Q,V],[I,C,K,N],[I,C,K,N,O],[I,C,K,N,O,Q],[I,C,K,N,O,Q,V],[I,C,K,N,Q],[I,C,K,N,Q,V],[I,C,L,N],[I,C,L,N,O],[I,C,L,N,O,Q],[I,C,L,N,O,Q,V],[I,C,L,N,Q],[I,C,L,N,Q,V],[I,C,N],[I,C,N,O],[I,C,N,O,Q],[I,C,N,O,Q,V],[I,C,N,Q],[I,C,N,Q,V],[I,D,K,L,N,O,Q],[I,D,K,L,N,O,Q,V],[I,D,K,L,N,Q],[I,D,K,L,N,Q,V],[I,D,K,N,O,Q],[I,D,K,N,O,Q,V],[I,D,K,N,Q],[I,D,K,N,Q,V],[I,D,L,N,O,Q],[I,D,L,N,O,Q,V],[I,D,L,N,Q],[I,D,L,N,Q,V],[I,D,N,O,Q],[I,D,N,O,Q,V],[I,D,N,Q],[I,D,N,Q,V],[I,K],[I,K,L,N],[I,K,L,N,O],[I,K,L,N,O,Q],[I,K,L,N,O,Q,V],[I,K,L,N,Q],[I,K,L,N,Q,V],[I,K,N],[I,K,N,O],[I,K,N,O,Q],[I,K,N,O,Q,V],[I,K,N,Q],[I,K,N,Q,V],[I,L,N],[I,L,N,O],[I,L,N,O,Q],[I,L,N,O,Q,V],[I,L,N,Q],[I,L,N,Q,V],[I,N],[I,N,O],[I,N,O,Q],[I,N,O,Q,V],[I,N,Q],[I,N,Q,V],[J],[B],[B,C,D,K,L,N,O,Q],[B,C,D,K,L,N,O,Q,V],[B,C,D,K,L,N,Q],[B,C,D,K,L,N,Q,V],[B,C,D,K,N,O,Q],[B,C,D,K,N,O,Q,V],[B,C,D,K,N,Q],[B,C,D,K,N,Q,V],[B,C,D,L,N,O,Q],[B,C,D,L,N,O,Q,V],[B,C,D,L,N,Q],[B,C,D,L,N,Q,V],[B,C,D,N,O,Q],[B,C,D,N,O,Q,V],[B,C,D,N,Q],[B,C,D,N,Q,V],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,O,Q,V],[B,C,K,L,N,Q],[B,C,K,L,N,Q,V],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,O,Q,V],[B,C,K,N,Q],[B,C,K,N,Q,V],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,O,Q,V],[B,C,L,N,Q],[B,C,L,N,Q,V],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,O,Q,V],[B,C,N,Q],[B,C,N,Q,V],[B,D,K,L,N,O,Q],[B,D,K,L,N,O,Q,V],[B,D,K,L,N,Q],[B,D,K,L,N,Q,V],[B,D,K,N,O,Q],[B,D,K,N,O,Q,V],[B,D,K,N,Q],[B,D,K,N,Q,V],[B,D,L,N,O,Q],[B,D,L,N,O,Q,V],[B,D,L,N,Q],[B,D,L,N,Q,V],[B,D,N,O,Q],[B,D,N,O,Q,V],[B,D,N,Q],[B,D,N,Q,V],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,O,Q,V],[B,K,L,N,Q],[B,K,L,N,Q,V],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,O,Q,V],[B,K,N,Q],[B,K,N,Q,V],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,O,Q,V],[B,L,N,Q],[B,L,N,Q,V],[B,N],[B,N,O],[B,N,O,Q],[B,N,O,Q,V],[B,N,Q],[B,N,Q,V],[C],[C,D,K,L,N,O,Q],[C,D,K,L,N,O,Q,V],[C,D,K,L,N,Q],[C,D,K,L,N,Q,V],[C,D,K,N,O,Q],[C,D,K,N,O,Q,V],[C,D,K,N,Q],[C,D,K,N,Q,V],[C,D,L,N,O,Q],[C,D,L,N,O,Q,V],[C,D,L,N,Q],[C,D,L,N,Q,V],[C,D,N,O,Q],[C,D,N,O,Q,V],[C,D,N,Q],[C,D,N,Q,V],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,O,Q,V],[C,K,L,N,Q],[C,K,L,N,Q,V],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,O,Q,V],[C,K,N,Q],[C,K,N,Q,V],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,O,Q,V],[C,L,N,Q],[C,L,N,Q,V],[C,N],[C,N,O],[C,N,O,Q],[C,N,O,Q,V],[C,N,Q],[C,N,Q,V],[D],[D,K,L,N,O,Q],[D,K,L,N,O,Q,V],[D,K,L,N,Q],[D,K,L,N,Q,V],[D,K,N,O,Q],[D,K,N,O,Q,V],[D,K,N,Q],[D,K,N,Q,V],[D,L,N,O,Q],[D,L,N,O,Q,V],[D,L,N,Q],[D,L,N,Q,V],[D,N,O,Q],[D,N,O,Q,V],[D,N,Q],[D,N,Q,V],[D,V],[E],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,O,Q,V],[K,L,N,Q],[K,L,N,Q,V],[K,N],[K,N,O],[K,N,O,Q],[K,N,O,Q,V],[K,N,Q],[K,N,Q,V],[L,N],[L,N,O],[L,N,O,Q],[L,N,O,Q,V],[L,N,Q],[L,N,Q,V],[N],[N,O],[N,O,Q],[N,O,Q,V],[N,Q],[N,Q,V],[V],[X]]),ground([G,M,P,R,S,T,U,W]),linear(F),linear(H),linear(J),linear(E),linear(X);mshare([[F],[H],[J],[B],[B,C,D,K,L,N,O,Q],[B,C,D,K,L,N,O,Q,V],[B,C,D,K,L,N,Q],[B,C,D,K,L,N,Q,V],[B,C,D,K,N,O,Q],[B,C,D,K,N,O,Q,V],[B,C,D,K,N,Q],[B,C,D,K,N,Q,V],[B,C,D,L,N,O,Q],[B,C,D,L,N,O,Q,V],[B,C,D,L,N,Q],[B,C,D,L,N,Q,V],[B,C,D,N,O,Q],[B,C,D,N,O,Q,V],[B,C,D,N,Q],[B,C,D,N,Q,V],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,O,Q,V],[B,C,K,L,N,Q],[B,C,K,L,N,Q,V],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,O,Q,V],[B,C,K,N,Q],[B,C,K,N,Q,V],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,O,Q,V],[B,C,L,N,Q],[B,C,L,N,Q,V],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,O,Q,V],[B,C,N,Q],[B,C,N,Q,V],[B,D,K,L,N,O,Q],[B,D,K,L,N,O,Q,V],[B,D,K,L,N,Q],[B,D,K,L,N,Q,V],[B,D,K,N,O,Q],[B,D,K,N,O,Q,V],[B,D,K,N,Q],[B,D,K,N,Q,V],[B,D,L,N,O,Q],[B,D,L,N,O,Q,V],[B,D,L,N,Q],[B,D,L,N,Q,V],[B,D,N,O,Q],[B,D,N,O,Q,V],[B,D,N,Q],[B,D,N,Q,V],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,O,Q,V],[B,K,L,N,Q],[B,K,L,N,Q,V],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,O,Q,V],[B,K,N,Q],[B,K,N,Q,V],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,O,Q,V],[B,L,N,Q],[B,L,N,Q,V],[B,N],[B,N,O],[B,N,O,Q],[B,N,O,Q,V],[B,N,Q],[B,N,Q,V],[C],[C,D,K,L,N,O,Q],[C,D,K,L,N,O,Q,V],[C,D,K,L,N,Q],[C,D,K,L,N,Q,V],[C,D,K,N,O,Q],[C,D,K,N,O,Q,V],[C,D,K,N,Q],[C,D,K,N,Q,V],[C,D,L,N,O,Q],[C,D,L,N,O,Q,V],[C,D,L,N,Q],[C,D,L,N,Q,V],[C,D,N,O,Q],[C,D,N,O,Q,V],[C,D,N,Q],[C,D,N,Q,V],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,O,Q,V],[C,K,L,N,Q],[C,K,L,N,Q,V],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,O,Q,V],[C,K,N,Q],[C,K,N,Q,V],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,O,Q,V],[C,L,N,Q],[C,L,N,Q,V],[C,N],[C,N,O],[C,N,O,Q],[C,N,O,Q,V],[C,N,Q],[C,N,Q,V],[D],[D,K,L,N,O,Q],[D,K,L,N,O,Q,V],[D,K,L,N,Q],[D,K,L,N,Q,V],[D,K,N,O,Q],[D,K,N,O,Q,V],[D,K,N,Q],[D,K,N,Q,V],[D,L,N,O,Q],[D,L,N,O,Q,V],[D,L,N,Q],[D,L,N,Q,V],[D,N,O,Q],[D,N,O,Q,V],[D,N,Q],[D,N,Q,V],[D,V],[E],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,O,Q,V],[K,L,N,Q],[K,L,N,Q,V],[K,N],[K,N,O],[K,N,O,Q],[K,N,O,Q,V],[K,N,Q],[K,N,Q,V],[L,N],[L,N,O],[L,N,O,Q],[L,N,O,Q,V],[L,N,Q],[L,N,Q,V],[N],[N,O],[N,O,Q],[N,O,Q,V],[N,Q],[N,Q,V],[V],[X]]),ground([G,I,M,P,R,S,T,U,W]),linear(F),linear(H),linear(J),linear(E),linear(X))),
    myplus(S,T,X),
    true((mshare([[F],[H],[I],[I,B],[I,B,C,D,K,L,N,O,Q],[I,B,C,D,K,L,N,O,Q,V],[I,B,C,D,K,L,N,Q],[I,B,C,D,K,L,N,Q,V],[I,B,C,D,K,N,O,Q],[I,B,C,D,K,N,O,Q,V],[I,B,C,D,K,N,Q],[I,B,C,D,K,N,Q,V],[I,B,C,D,L,N,O,Q],[I,B,C,D,L,N,O,Q,V],[I,B,C,D,L,N,Q],[I,B,C,D,L,N,Q,V],[I,B,C,D,N,O,Q],[I,B,C,D,N,O,Q,V],[I,B,C,D,N,Q],[I,B,C,D,N,Q,V],[I,B,C,K,L,N],[I,B,C,K,L,N,O],[I,B,C,K,L,N,O,Q],[I,B,C,K,L,N,O,Q,V],[I,B,C,K,L,N,Q],[I,B,C,K,L,N,Q,V],[I,B,C,K,N],[I,B,C,K,N,O],[I,B,C,K,N,O,Q],[I,B,C,K,N,O,Q,V],[I,B,C,K,N,Q],[I,B,C,K,N,Q,V],[I,B,C,L,N],[I,B,C,L,N,O],[I,B,C,L,N,O,Q],[I,B,C,L,N,O,Q,V],[I,B,C,L,N,Q],[I,B,C,L,N,Q,V],[I,B,C,N],[I,B,C,N,O],[I,B,C,N,O,Q],[I,B,C,N,O,Q,V],[I,B,C,N,Q],[I,B,C,N,Q,V],[I,B,D,K,L,N,O,Q],[I,B,D,K,L,N,O,Q,V],[I,B,D,K,L,N,Q],[I,B,D,K,L,N,Q,V],[I,B,D,K,N,O,Q],[I,B,D,K,N,O,Q,V],[I,B,D,K,N,Q],[I,B,D,K,N,Q,V],[I,B,D,L,N,O,Q],[I,B,D,L,N,O,Q,V],[I,B,D,L,N,Q],[I,B,D,L,N,Q,V],[I,B,D,N,O,Q],[I,B,D,N,O,Q,V],[I,B,D,N,Q],[I,B,D,N,Q,V],[I,B,K],[I,B,K,L,N],[I,B,K,L,N,O],[I,B,K,L,N,O,Q],[I,B,K,L,N,O,Q,V],[I,B,K,L,N,Q],[I,B,K,L,N,Q,V],[I,B,K,N],[I,B,K,N,O],[I,B,K,N,O,Q],[I,B,K,N,O,Q,V],[I,B,K,N,Q],[I,B,K,N,Q,V],[I,B,L,N],[I,B,L,N,O],[I,B,L,N,O,Q],[I,B,L,N,O,Q,V],[I,B,L,N,Q],[I,B,L,N,Q,V],[I,B,N],[I,B,N,O],[I,B,N,O,Q],[I,B,N,O,Q,V],[I,B,N,Q],[I,B,N,Q,V],[I,C,D,K,L,N,O,Q],[I,C,D,K,L,N,O,Q,V],[I,C,D,K,L,N,Q],[I,C,D,K,L,N,Q,V],[I,C,D,K,N,O,Q],[I,C,D,K,N,O,Q,V],[I,C,D,K,N,Q],[I,C,D,K,N,Q,V],[I,C,D,L,N,O,Q],[I,C,D,L,N,O,Q,V],[I,C,D,L,N,Q],[I,C,D,L,N,Q,V],[I,C,D,N,O,Q],[I,C,D,N,O,Q,V],[I,C,D,N,Q],[I,C,D,N,Q,V],[I,C,K,L,N],[I,C,K,L,N,O],[I,C,K,L,N,O,Q],[I,C,K,L,N,O,Q,V],[I,C,K,L,N,Q],[I,C,K,L,N,Q,V],[I,C,K,N],[I,C,K,N,O],[I,C,K,N,O,Q],[I,C,K,N,O,Q,V],[I,C,K,N,Q],[I,C,K,N,Q,V],[I,C,L,N],[I,C,L,N,O],[I,C,L,N,O,Q],[I,C,L,N,O,Q,V],[I,C,L,N,Q],[I,C,L,N,Q,V],[I,C,N],[I,C,N,O],[I,C,N,O,Q],[I,C,N,O,Q,V],[I,C,N,Q],[I,C,N,Q,V],[I,D,K,L,N,O,Q],[I,D,K,L,N,O,Q,V],[I,D,K,L,N,Q],[I,D,K,L,N,Q,V],[I,D,K,N,O,Q],[I,D,K,N,O,Q,V],[I,D,K,N,Q],[I,D,K,N,Q,V],[I,D,L,N,O,Q],[I,D,L,N,O,Q,V],[I,D,L,N,Q],[I,D,L,N,Q,V],[I,D,N,O,Q],[I,D,N,O,Q,V],[I,D,N,Q],[I,D,N,Q,V],[I,K],[I,K,L,N],[I,K,L,N,O],[I,K,L,N,O,Q],[I,K,L,N,O,Q,V],[I,K,L,N,Q],[I,K,L,N,Q,V],[I,K,N],[I,K,N,O],[I,K,N,O,Q],[I,K,N,O,Q,V],[I,K,N,Q],[I,K,N,Q,V],[I,L,N],[I,L,N,O],[I,L,N,O,Q],[I,L,N,O,Q,V],[I,L,N,Q],[I,L,N,Q,V],[I,N],[I,N,O],[I,N,O,Q],[I,N,O,Q,V],[I,N,Q],[I,N,Q,V],[J],[B],[B,C,D,K,L,N,O,Q],[B,C,D,K,L,N,O,Q,V],[B,C,D,K,L,N,Q],[B,C,D,K,L,N,Q,V],[B,C,D,K,N,O,Q],[B,C,D,K,N,O,Q,V],[B,C,D,K,N,Q],[B,C,D,K,N,Q,V],[B,C,D,L,N,O,Q],[B,C,D,L,N,O,Q,V],[B,C,D,L,N,Q],[B,C,D,L,N,Q,V],[B,C,D,N,O,Q],[B,C,D,N,O,Q,V],[B,C,D,N,Q],[B,C,D,N,Q,V],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,O,Q,V],[B,C,K,L,N,Q],[B,C,K,L,N,Q,V],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,O,Q,V],[B,C,K,N,Q],[B,C,K,N,Q,V],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,O,Q,V],[B,C,L,N,Q],[B,C,L,N,Q,V],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,O,Q,V],[B,C,N,Q],[B,C,N,Q,V],[B,D,K,L,N,O,Q],[B,D,K,L,N,O,Q,V],[B,D,K,L,N,Q],[B,D,K,L,N,Q,V],[B,D,K,N,O,Q],[B,D,K,N,O,Q,V],[B,D,K,N,Q],[B,D,K,N,Q,V],[B,D,L,N,O,Q],[B,D,L,N,O,Q,V],[B,D,L,N,Q],[B,D,L,N,Q,V],[B,D,N,O,Q],[B,D,N,O,Q,V],[B,D,N,Q],[B,D,N,Q,V],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,O,Q,V],[B,K,L,N,Q],[B,K,L,N,Q,V],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,O,Q,V],[B,K,N,Q],[B,K,N,Q,V],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,O,Q,V],[B,L,N,Q],[B,L,N,Q,V],[B,N],[B,N,O],[B,N,O,Q],[B,N,O,Q,V],[B,N,Q],[B,N,Q,V],[C],[C,D,K,L,N,O,Q],[C,D,K,L,N,O,Q,V],[C,D,K,L,N,Q],[C,D,K,L,N,Q,V],[C,D,K,N,O,Q],[C,D,K,N,O,Q,V],[C,D,K,N,Q],[C,D,K,N,Q,V],[C,D,L,N,O,Q],[C,D,L,N,O,Q,V],[C,D,L,N,Q],[C,D,L,N,Q,V],[C,D,N,O,Q],[C,D,N,O,Q,V],[C,D,N,Q],[C,D,N,Q,V],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,O,Q,V],[C,K,L,N,Q],[C,K,L,N,Q,V],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,O,Q,V],[C,K,N,Q],[C,K,N,Q,V],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,O,Q,V],[C,L,N,Q],[C,L,N,Q,V],[C,N],[C,N,O],[C,N,O,Q],[C,N,O,Q,V],[C,N,Q],[C,N,Q,V],[D],[D,K,L,N,O,Q],[D,K,L,N,O,Q,V],[D,K,L,N,Q],[D,K,L,N,Q,V],[D,K,N,O,Q],[D,K,N,O,Q,V],[D,K,N,Q],[D,K,N,Q,V],[D,L,N,O,Q],[D,L,N,O,Q,V],[D,L,N,Q],[D,L,N,Q,V],[D,N,O,Q],[D,N,O,Q,V],[D,N,Q],[D,N,Q,V],[D,V],[E],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,O,Q,V],[K,L,N,Q],[K,L,N,Q,V],[K,N],[K,N,O],[K,N,O,Q],[K,N,O,Q,V],[K,N,Q],[K,N,Q,V],[L,N],[L,N,O],[L,N,O,Q],[L,N,O,Q,V],[L,N,Q],[L,N,Q,V],[N],[N,O],[N,O,Q],[N,O,Q,V],[N,Q],[N,Q,V],[V]]),ground([G,M,P,R,S,T,U,W,X]),linear(F),linear(H),linear(J),linear(E);mshare([[F],[H],[J],[B],[B,C,D,K,L,N,O,Q],[B,C,D,K,L,N,O,Q,V],[B,C,D,K,L,N,Q],[B,C,D,K,L,N,Q,V],[B,C,D,K,N,O,Q],[B,C,D,K,N,O,Q,V],[B,C,D,K,N,Q],[B,C,D,K,N,Q,V],[B,C,D,L,N,O,Q],[B,C,D,L,N,O,Q,V],[B,C,D,L,N,Q],[B,C,D,L,N,Q,V],[B,C,D,N,O,Q],[B,C,D,N,O,Q,V],[B,C,D,N,Q],[B,C,D,N,Q,V],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,O,Q,V],[B,C,K,L,N,Q],[B,C,K,L,N,Q,V],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,O,Q,V],[B,C,K,N,Q],[B,C,K,N,Q,V],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,O,Q,V],[B,C,L,N,Q],[B,C,L,N,Q,V],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,O,Q,V],[B,C,N,Q],[B,C,N,Q,V],[B,D,K,L,N,O,Q],[B,D,K,L,N,O,Q,V],[B,D,K,L,N,Q],[B,D,K,L,N,Q,V],[B,D,K,N,O,Q],[B,D,K,N,O,Q,V],[B,D,K,N,Q],[B,D,K,N,Q,V],[B,D,L,N,O,Q],[B,D,L,N,O,Q,V],[B,D,L,N,Q],[B,D,L,N,Q,V],[B,D,N,O,Q],[B,D,N,O,Q,V],[B,D,N,Q],[B,D,N,Q,V],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,O,Q,V],[B,K,L,N,Q],[B,K,L,N,Q,V],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,O,Q,V],[B,K,N,Q],[B,K,N,Q,V],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,O,Q,V],[B,L,N,Q],[B,L,N,Q,V],[B,N],[B,N,O],[B,N,O,Q],[B,N,O,Q,V],[B,N,Q],[B,N,Q,V],[C],[C,D,K,L,N,O,Q],[C,D,K,L,N,O,Q,V],[C,D,K,L,N,Q],[C,D,K,L,N,Q,V],[C,D,K,N,O,Q],[C,D,K,N,O,Q,V],[C,D,K,N,Q],[C,D,K,N,Q,V],[C,D,L,N,O,Q],[C,D,L,N,O,Q,V],[C,D,L,N,Q],[C,D,L,N,Q,V],[C,D,N,O,Q],[C,D,N,O,Q,V],[C,D,N,Q],[C,D,N,Q,V],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,O,Q,V],[C,K,L,N,Q],[C,K,L,N,Q,V],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,O,Q,V],[C,K,N,Q],[C,K,N,Q,V],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,O,Q,V],[C,L,N,Q],[C,L,N,Q,V],[C,N],[C,N,O],[C,N,O,Q],[C,N,O,Q,V],[C,N,Q],[C,N,Q,V],[D],[D,K,L,N,O,Q],[D,K,L,N,O,Q,V],[D,K,L,N,Q],[D,K,L,N,Q,V],[D,K,N,O,Q],[D,K,N,O,Q,V],[D,K,N,Q],[D,K,N,Q,V],[D,L,N,O,Q],[D,L,N,O,Q,V],[D,L,N,Q],[D,L,N,Q,V],[D,N,O,Q],[D,N,O,Q,V],[D,N,Q],[D,N,Q,V],[D,V],[E],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,O,Q,V],[K,L,N,Q],[K,L,N,Q,V],[K,N],[K,N,O],[K,N,O,Q],[K,N,O,Q,V],[K,N,Q],[K,N,Q,V],[L,N],[L,N,O],[L,N,O,Q],[L,N,O,Q,V],[L,N,Q],[L,N,Q,V],[N],[N,O],[N,O,Q],[N,O,Q,V],[N,Q],[N,Q,V],[V]]),ground([G,I,M,P,R,S,T,U,W,X]),linear(F),linear(H),linear(J),linear(E))),
    verb_mods(E,W,X,F,U,H,V,J),
    true((mshare([[I],[I,J,B,C,D,E,K,L,N,O,Q,V],[I,J,B,C,D,E,K,L,N,Q,V],[I,J,B,C,D,E,K,N,O,Q,V],[I,J,B,C,D,E,K,N,Q,V],[I,J,B,C,D,E,L,N,O,Q,V],[I,J,B,C,D,E,L,N,Q,V],[I,J,B,C,D,E,N,O,Q,V],[I,J,B,C,D,E,N,Q,V],[I,J,B,C,D,K,L,N,O,Q,V],[I,J,B,C,D,K,L,N,Q,V],[I,J,B,C,D,K,N,O,Q,V],[I,J,B,C,D,K,N,Q,V],[I,J,B,C,D,L,N,O,Q,V],[I,J,B,C,D,L,N,Q,V],[I,J,B,C,D,N,O,Q,V],[I,J,B,C,D,N,Q,V],[I,J,B,C,E,K,L,N,O,Q,V],[I,J,B,C,E,K,L,N,Q,V],[I,J,B,C,E,K,N,O,Q,V],[I,J,B,C,E,K,N,Q,V],[I,J,B,C,E,L,N,O,Q,V],[I,J,B,C,E,L,N,Q,V],[I,J,B,C,E,N,O,Q,V],[I,J,B,C,E,N,Q,V],[I,J,B,C,K,L,N,O,Q,V],[I,J,B,C,K,L,N,Q,V],[I,J,B,C,K,N,O,Q,V],[I,J,B,C,K,N,Q,V],[I,J,B,C,L,N,O,Q,V],[I,J,B,C,L,N,Q,V],[I,J,B,C,N,O,Q,V],[I,J,B,C,N,Q,V],[I,J,B,D,E,K,L,N,O,Q,V],[I,J,B,D,E,K,L,N,Q,V],[I,J,B,D,E,K,N,O,Q,V],[I,J,B,D,E,K,N,Q,V],[I,J,B,D,E,L,N,O,Q,V],[I,J,B,D,E,L,N,Q,V],[I,J,B,D,E,N,O,Q,V],[I,J,B,D,E,N,Q,V],[I,J,B,D,K,L,N,O,Q,V],[I,J,B,D,K,L,N,Q,V],[I,J,B,D,K,N,O,Q,V],[I,J,B,D,K,N,Q,V],[I,J,B,D,L,N,O,Q,V],[I,J,B,D,L,N,Q,V],[I,J,B,D,N,O,Q,V],[I,J,B,D,N,Q,V],[I,J,B,E,K,L,N,O,Q,V],[I,J,B,E,K,L,N,Q,V],[I,J,B,E,K,N,O,Q,V],[I,J,B,E,K,N,Q,V],[I,J,B,E,L,N,O,Q,V],[I,J,B,E,L,N,Q,V],[I,J,B,E,N,O,Q,V],[I,J,B,E,N,Q,V],[I,J,B,K,L,N,O,Q,V],[I,J,B,K,L,N,Q,V],[I,J,B,K,N,O,Q,V],[I,J,B,K,N,Q,V],[I,J,B,L,N,O,Q,V],[I,J,B,L,N,Q,V],[I,J,B,N,O,Q,V],[I,J,B,N,Q,V],[I,J,C,D,E,K,L,N,O,Q,V],[I,J,C,D,E,K,L,N,Q,V],[I,J,C,D,E,K,N,O,Q,V],[I,J,C,D,E,K,N,Q,V],[I,J,C,D,E,L,N,O,Q,V],[I,J,C,D,E,L,N,Q,V],[I,J,C,D,E,N,O,Q,V],[I,J,C,D,E,N,Q,V],[I,J,C,D,K,L,N,O,Q,V],[I,J,C,D,K,L,N,Q,V],[I,J,C,D,K,N,O,Q,V],[I,J,C,D,K,N,Q,V],[I,J,C,D,L,N,O,Q,V],[I,J,C,D,L,N,Q,V],[I,J,C,D,N,O,Q,V],[I,J,C,D,N,Q,V],[I,J,C,E,K,L,N,O,Q,V],[I,J,C,E,K,L,N,Q,V],[I,J,C,E,K,N,O,Q,V],[I,J,C,E,K,N,Q,V],[I,J,C,E,L,N,O,Q,V],[I,J,C,E,L,N,Q,V],[I,J,C,E,N,O,Q,V],[I,J,C,E,N,Q,V],[I,J,C,K,L,N,O,Q,V],[I,J,C,K,L,N,Q,V],[I,J,C,K,N,O,Q,V],[I,J,C,K,N,Q,V],[I,J,C,L,N,O,Q,V],[I,J,C,L,N,Q,V],[I,J,C,N,O,Q,V],[I,J,C,N,Q,V],[I,J,D,E,K,L,N,O,Q,V],[I,J,D,E,K,L,N,Q,V],[I,J,D,E,K,N,O,Q,V],[I,J,D,E,K,N,Q,V],[I,J,D,E,L,N,O,Q,V],[I,J,D,E,L,N,Q,V],[I,J,D,E,N,O,Q,V],[I,J,D,E,N,Q,V],[I,J,D,K,L,N,O,Q,V],[I,J,D,K,L,N,Q,V],[I,J,D,K,N,O,Q,V],[I,J,D,K,N,Q,V],[I,J,D,L,N,O,Q,V],[I,J,D,L,N,Q,V],[I,J,D,N,O,Q,V],[I,J,D,N,Q,V],[I,J,E,K,L,N,O,Q,V],[I,J,E,K,L,N,Q,V],[I,J,E,K,N,O,Q,V],[I,J,E,K,N,Q,V],[I,J,E,L,N,O,Q,V],[I,J,E,L,N,Q,V],[I,J,E,N,O,Q,V],[I,J,E,N,Q,V],[I,J,K,L,N,O,Q,V],[I,J,K,L,N,Q,V],[I,J,K,N,O,Q,V],[I,J,K,N,Q,V],[I,J,L,N,O,Q,V],[I,J,L,N,Q,V],[I,J,N,O,Q,V],[I,J,N,Q,V],[I,B],[I,B,C,D,E,K,L,N,O,Q,V],[I,B,C,D,E,K,L,N,Q,V],[I,B,C,D,E,K,N,O,Q,V],[I,B,C,D,E,K,N,Q,V],[I,B,C,D,E,L,N,O,Q,V],[I,B,C,D,E,L,N,Q,V],[I,B,C,D,E,N,O,Q,V],[I,B,C,D,E,N,Q,V],[I,B,C,D,K,L,N,O,Q],[I,B,C,D,K,L,N,O,Q,V],[I,B,C,D,K,L,N,Q],[I,B,C,D,K,L,N,Q,V],[I,B,C,D,K,N,O,Q],[I,B,C,D,K,N,O,Q,V],[I,B,C,D,K,N,Q],[I,B,C,D,K,N,Q,V],[I,B,C,D,L,N,O,Q],[I,B,C,D,L,N,O,Q,V],[I,B,C,D,L,N,Q],[I,B,C,D,L,N,Q,V],[I,B,C,D,N,O,Q],[I,B,C,D,N,O,Q,V],[I,B,C,D,N,Q],[I,B,C,D,N,Q,V],[I,B,C,E,K,L,N,O,Q,V],[I,B,C,E,K,L,N,Q,V],[I,B,C,E,K,N,O,Q,V],[I,B,C,E,K,N,Q,V],[I,B,C,E,L,N,O,Q,V],[I,B,C,E,L,N,Q,V],[I,B,C,E,N,O,Q,V],[I,B,C,E,N,Q,V],[I,B,C,K,L,N],[I,B,C,K,L,N,O],[I,B,C,K,L,N,O,Q],[I,B,C,K,L,N,O,Q,V],[I,B,C,K,L,N,Q],[I,B,C,K,L,N,Q,V],[I,B,C,K,N],[I,B,C,K,N,O],[I,B,C,K,N,O,Q],[I,B,C,K,N,O,Q,V],[I,B,C,K,N,Q],[I,B,C,K,N,Q,V],[I,B,C,L,N],[I,B,C,L,N,O],[I,B,C,L,N,O,Q],[I,B,C,L,N,O,Q,V],[I,B,C,L,N,Q],[I,B,C,L,N,Q,V],[I,B,C,N],[I,B,C,N,O],[I,B,C,N,O,Q],[I,B,C,N,O,Q,V],[I,B,C,N,Q],[I,B,C,N,Q,V],[I,B,D,E,K,L,N,O,Q,V],[I,B,D,E,K,L,N,Q,V],[I,B,D,E,K,N,O,Q,V],[I,B,D,E,K,N,Q,V],[I,B,D,E,L,N,O,Q,V],[I,B,D,E,L,N,Q,V],[I,B,D,E,N,O,Q,V],[I,B,D,E,N,Q,V],[I,B,D,K,L,N,O,Q],[I,B,D,K,L,N,O,Q,V],[I,B,D,K,L,N,Q],[I,B,D,K,L,N,Q,V],[I,B,D,K,N,O,Q],[I,B,D,K,N,O,Q,V],[I,B,D,K,N,Q],[I,B,D,K,N,Q,V],[I,B,D,L,N,O,Q],[I,B,D,L,N,O,Q,V],[I,B,D,L,N,Q],[I,B,D,L,N,Q,V],[I,B,D,N,O,Q],[I,B,D,N,O,Q,V],[I,B,D,N,Q],[I,B,D,N,Q,V],[I,B,E,K,L,N,O,Q,V],[I,B,E,K,L,N,Q,V],[I,B,E,K,N,O,Q,V],[I,B,E,K,N,Q,V],[I,B,E,L,N,O,Q,V],[I,B,E,L,N,Q,V],[I,B,E,N,O,Q,V],[I,B,E,N,Q,V],[I,B,K],[I,B,K,L,N],[I,B,K,L,N,O],[I,B,K,L,N,O,Q],[I,B,K,L,N,O,Q,V],[I,B,K,L,N,Q],[I,B,K,L,N,Q,V],[I,B,K,N],[I,B,K,N,O],[I,B,K,N,O,Q],[I,B,K,N,O,Q,V],[I,B,K,N,Q],[I,B,K,N,Q,V],[I,B,L,N],[I,B,L,N,O],[I,B,L,N,O,Q],[I,B,L,N,O,Q,V],[I,B,L,N,Q],[I,B,L,N,Q,V],[I,B,N],[I,B,N,O],[I,B,N,O,Q],[I,B,N,O,Q,V],[I,B,N,Q],[I,B,N,Q,V],[I,C,D,E,K,L,N,O,Q,V],[I,C,D,E,K,L,N,Q,V],[I,C,D,E,K,N,O,Q,V],[I,C,D,E,K,N,Q,V],[I,C,D,E,L,N,O,Q,V],[I,C,D,E,L,N,Q,V],[I,C,D,E,N,O,Q,V],[I,C,D,E,N,Q,V],[I,C,D,K,L,N,O,Q],[I,C,D,K,L,N,O,Q,V],[I,C,D,K,L,N,Q],[I,C,D,K,L,N,Q,V],[I,C,D,K,N,O,Q],[I,C,D,K,N,O,Q,V],[I,C,D,K,N,Q],[I,C,D,K,N,Q,V],[I,C,D,L,N,O,Q],[I,C,D,L,N,O,Q,V],[I,C,D,L,N,Q],[I,C,D,L,N,Q,V],[I,C,D,N,O,Q],[I,C,D,N,O,Q,V],[I,C,D,N,Q],[I,C,D,N,Q,V],[I,C,E,K,L,N,O,Q,V],[I,C,E,K,L,N,Q,V],[I,C,E,K,N,O,Q,V],[I,C,E,K,N,Q,V],[I,C,E,L,N,O,Q,V],[I,C,E,L,N,Q,V],[I,C,E,N,O,Q,V],[I,C,E,N,Q,V],[I,C,K,L,N],[I,C,K,L,N,O],[I,C,K,L,N,O,Q],[I,C,K,L,N,O,Q,V],[I,C,K,L,N,Q],[I,C,K,L,N,Q,V],[I,C,K,N],[I,C,K,N,O],[I,C,K,N,O,Q],[I,C,K,N,O,Q,V],[I,C,K,N,Q],[I,C,K,N,Q,V],[I,C,L,N],[I,C,L,N,O],[I,C,L,N,O,Q],[I,C,L,N,O,Q,V],[I,C,L,N,Q],[I,C,L,N,Q,V],[I,C,N],[I,C,N,O],[I,C,N,O,Q],[I,C,N,O,Q,V],[I,C,N,Q],[I,C,N,Q,V],[I,D,E,K,L,N,O,Q,V],[I,D,E,K,L,N,Q,V],[I,D,E,K,N,O,Q,V],[I,D,E,K,N,Q,V],[I,D,E,L,N,O,Q,V],[I,D,E,L,N,Q,V],[I,D,E,N,O,Q,V],[I,D,E,N,Q,V],[I,D,K,L,N,O,Q],[I,D,K,L,N,O,Q,V],[I,D,K,L,N,Q],[I,D,K,L,N,Q,V],[I,D,K,N,O,Q],[I,D,K,N,O,Q,V],[I,D,K,N,Q],[I,D,K,N,Q,V],[I,D,L,N,O,Q],[I,D,L,N,O,Q,V],[I,D,L,N,Q],[I,D,L,N,Q,V],[I,D,N,O,Q],[I,D,N,O,Q,V],[I,D,N,Q],[I,D,N,Q,V],[I,E,K,L,N,O,Q,V],[I,E,K,L,N,Q,V],[I,E,K,N,O,Q,V],[I,E,K,N,Q,V],[I,E,L,N,O,Q,V],[I,E,L,N,Q,V],[I,E,N,O,Q,V],[I,E,N,Q,V],[I,K],[I,K,L,N],[I,K,L,N,O],[I,K,L,N,O,Q],[I,K,L,N,O,Q,V],[I,K,L,N,Q],[I,K,L,N,Q,V],[I,K,N],[I,K,N,O],[I,K,N,O,Q],[I,K,N,O,Q,V],[I,K,N,Q],[I,K,N,Q,V],[I,L,N],[I,L,N,O],[I,L,N,O,Q],[I,L,N,O,Q,V],[I,L,N,Q],[I,L,N,Q,V],[I,N],[I,N,O],[I,N,O,Q],[I,N,O,Q,V],[I,N,Q],[I,N,Q,V],[J],[J,B,C,D,E,K,L,N,O,Q,V],[J,B,C,D,E,K,L,N,Q,V],[J,B,C,D,E,K,N,O,Q,V],[J,B,C,D,E,K,N,Q,V],[J,B,C,D,E,L,N,O,Q,V],[J,B,C,D,E,L,N,Q,V],[J,B,C,D,E,N,O,Q,V],[J,B,C,D,E,N,Q,V],[J,B,C,D,K,L,N,O,Q,V],[J,B,C,D,K,L,N,Q,V],[J,B,C,D,K,N,O,Q,V],[J,B,C,D,K,N,Q,V],[J,B,C,D,L,N,O,Q,V],[J,B,C,D,L,N,Q,V],[J,B,C,D,N,O,Q,V],[J,B,C,D,N,Q,V],[J,B,C,E,K,L,N,O,Q,V],[J,B,C,E,K,L,N,Q,V],[J,B,C,E,K,N,O,Q,V],[J,B,C,E,K,N,Q,V],[J,B,C,E,L,N,O,Q,V],[J,B,C,E,L,N,Q,V],[J,B,C,E,N,O,Q,V],[J,B,C,E,N,Q,V],[J,B,C,K,L,N,O,Q,V],[J,B,C,K,L,N,Q,V],[J,B,C,K,N,O,Q,V],[J,B,C,K,N,Q,V],[J,B,C,L,N,O,Q,V],[J,B,C,L,N,Q,V],[J,B,C,N,O,Q,V],[J,B,C,N,Q,V],[J,B,D,E,K,L,N,O,Q,V],[J,B,D,E,K,L,N,Q,V],[J,B,D,E,K,N,O,Q,V],[J,B,D,E,K,N,Q,V],[J,B,D,E,L,N,O,Q,V],[J,B,D,E,L,N,Q,V],[J,B,D,E,N,O,Q,V],[J,B,D,E,N,Q,V],[J,B,D,K,L,N,O,Q,V],[J,B,D,K,L,N,Q,V],[J,B,D,K,N,O,Q,V],[J,B,D,K,N,Q,V],[J,B,D,L,N,O,Q,V],[J,B,D,L,N,Q,V],[J,B,D,N,O,Q,V],[J,B,D,N,Q,V],[J,B,E,K,L,N,O,Q,V],[J,B,E,K,L,N,Q,V],[J,B,E,K,N,O,Q,V],[J,B,E,K,N,Q,V],[J,B,E,L,N,O,Q,V],[J,B,E,L,N,Q,V],[J,B,E,N,O,Q,V],[J,B,E,N,Q,V],[J,B,K,L,N,O,Q,V],[J,B,K,L,N,Q,V],[J,B,K,N,O,Q,V],[J,B,K,N,Q,V],[J,B,L,N,O,Q,V],[J,B,L,N,Q,V],[J,B,N,O,Q,V],[J,B,N,Q,V],[J,C,D,E,K,L,N,O,Q,V],[J,C,D,E,K,L,N,Q,V],[J,C,D,E,K,N,O,Q,V],[J,C,D,E,K,N,Q,V],[J,C,D,E,L,N,O,Q,V],[J,C,D,E,L,N,Q,V],[J,C,D,E,N,O,Q,V],[J,C,D,E,N,Q,V],[J,C,D,K,L,N,O,Q,V],[J,C,D,K,L,N,Q,V],[J,C,D,K,N,O,Q,V],[J,C,D,K,N,Q,V],[J,C,D,L,N,O,Q,V],[J,C,D,L,N,Q,V],[J,C,D,N,O,Q,V],[J,C,D,N,Q,V],[J,C,E,K,L,N,O,Q,V],[J,C,E,K,L,N,Q,V],[J,C,E,K,N,O,Q,V],[J,C,E,K,N,Q,V],[J,C,E,L,N,O,Q,V],[J,C,E,L,N,Q,V],[J,C,E,N,O,Q,V],[J,C,E,N,Q,V],[J,C,K,L,N,O,Q,V],[J,C,K,L,N,Q,V],[J,C,K,N,O,Q,V],[J,C,K,N,Q,V],[J,C,L,N,O,Q,V],[J,C,L,N,Q,V],[J,C,N,O,Q,V],[J,C,N,Q,V],[J,D,E,K,L,N,O,Q,V],[J,D,E,K,L,N,Q,V],[J,D,E,K,N,O,Q,V],[J,D,E,K,N,Q,V],[J,D,E,L,N,O,Q,V],[J,D,E,L,N,Q,V],[J,D,E,N,O,Q,V],[J,D,E,N,Q,V],[J,D,E,V],[J,D,K,L,N,O,Q,V],[J,D,K,L,N,Q,V],[J,D,K,N,O,Q,V],[J,D,K,N,Q,V],[J,D,L,N,O,Q,V],[J,D,L,N,Q,V],[J,D,N,O,Q,V],[J,D,N,Q,V],[J,D,V],[J,E],[J,E,K,L,N,O,Q,V],[J,E,K,L,N,Q,V],[J,E,K,N,O,Q,V],[J,E,K,N,Q,V],[J,E,L,N,O,Q,V],[J,E,L,N,Q,V],[J,E,N,O,Q,V],[J,E,N,Q,V],[J,E,V],[J,K,L,N,O,Q,V],[J,K,L,N,Q,V],[J,K,N,O,Q,V],[J,K,N,Q,V],[J,L,N,O,Q,V],[J,L,N,Q,V],[J,N,O,Q,V],[J,N,Q,V],[J,V],[B],[B,C,D,E,K,L,N,O,Q,V],[B,C,D,E,K,L,N,Q,V],[B,C,D,E,K,N,O,Q,V],[B,C,D,E,K,N,Q,V],[B,C,D,E,L,N,O,Q,V],[B,C,D,E,L,N,Q,V],[B,C,D,E,N,O,Q,V],[B,C,D,E,N,Q,V],[B,C,D,K,L,N,O,Q],[B,C,D,K,L,N,O,Q,V],[B,C,D,K,L,N,Q],[B,C,D,K,L,N,Q,V],[B,C,D,K,N,O,Q],[B,C,D,K,N,O,Q,V],[B,C,D,K,N,Q],[B,C,D,K,N,Q,V],[B,C,D,L,N,O,Q],[B,C,D,L,N,O,Q,V],[B,C,D,L,N,Q],[B,C,D,L,N,Q,V],[B,C,D,N,O,Q],[B,C,D,N,O,Q,V],[B,C,D,N,Q],[B,C,D,N,Q,V],[B,C,E,K,L,N,O,Q,V],[B,C,E,K,L,N,Q,V],[B,C,E,K,N,O,Q,V],[B,C,E,K,N,Q,V],[B,C,E,L,N,O,Q,V],[B,C,E,L,N,Q,V],[B,C,E,N,O,Q,V],[B,C,E,N,Q,V],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,O,Q,V],[B,C,K,L,N,Q],[B,C,K,L,N,Q,V],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,O,Q,V],[B,C,K,N,Q],[B,C,K,N,Q,V],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,O,Q,V],[B,C,L,N,Q],[B,C,L,N,Q,V],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,O,Q,V],[B,C,N,Q],[B,C,N,Q,V],[B,D,E,K,L,N,O,Q,V],[B,D,E,K,L,N,Q,V],[B,D,E,K,N,O,Q,V],[B,D,E,K,N,Q,V],[B,D,E,L,N,O,Q,V],[B,D,E,L,N,Q,V],[B,D,E,N,O,Q,V],[B,D,E,N,Q,V],[B,D,K,L,N,O,Q],[B,D,K,L,N,O,Q,V],[B,D,K,L,N,Q],[B,D,K,L,N,Q,V],[B,D,K,N,O,Q],[B,D,K,N,O,Q,V],[B,D,K,N,Q],[B,D,K,N,Q,V],[B,D,L,N,O,Q],[B,D,L,N,O,Q,V],[B,D,L,N,Q],[B,D,L,N,Q,V],[B,D,N,O,Q],[B,D,N,O,Q,V],[B,D,N,Q],[B,D,N,Q,V],[B,E,K,L,N,O,Q,V],[B,E,K,L,N,Q,V],[B,E,K,N,O,Q,V],[B,E,K,N,Q,V],[B,E,L,N,O,Q,V],[B,E,L,N,Q,V],[B,E,N,O,Q,V],[B,E,N,Q,V],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,O,Q,V],[B,K,L,N,Q],[B,K,L,N,Q,V],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,O,Q,V],[B,K,N,Q],[B,K,N,Q,V],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,O,Q,V],[B,L,N,Q],[B,L,N,Q,V],[B,N],[B,N,O],[B,N,O,Q],[B,N,O,Q,V],[B,N,Q],[B,N,Q,V],[C],[C,D,E,K,L,N,O,Q,V],[C,D,E,K,L,N,Q,V],[C,D,E,K,N,O,Q,V],[C,D,E,K,N,Q,V],[C,D,E,L,N,O,Q,V],[C,D,E,L,N,Q,V],[C,D,E,N,O,Q,V],[C,D,E,N,Q,V],[C,D,K,L,N,O,Q],[C,D,K,L,N,O,Q,V],[C,D,K,L,N,Q],[C,D,K,L,N,Q,V],[C,D,K,N,O,Q],[C,D,K,N,O,Q,V],[C,D,K,N,Q],[C,D,K,N,Q,V],[C,D,L,N,O,Q],[C,D,L,N,O,Q,V],[C,D,L,N,Q],[C,D,L,N,Q,V],[C,D,N,O,Q],[C,D,N,O,Q,V],[C,D,N,Q],[C,D,N,Q,V],[C,E,K,L,N,O,Q,V],[C,E,K,L,N,Q,V],[C,E,K,N,O,Q,V],[C,E,K,N,Q,V],[C,E,L,N,O,Q,V],[C,E,L,N,Q,V],[C,E,N,O,Q,V],[C,E,N,Q,V],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,O,Q,V],[C,K,L,N,Q],[C,K,L,N,Q,V],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,O,Q,V],[C,K,N,Q],[C,K,N,Q,V],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,O,Q,V],[C,L,N,Q],[C,L,N,Q,V],[C,N],[C,N,O],[C,N,O,Q],[C,N,O,Q,V],[C,N,Q],[C,N,Q,V],[D],[D,E,K,L,N,O,Q,V],[D,E,K,L,N,Q,V],[D,E,K,N,O,Q,V],[D,E,K,N,Q,V],[D,E,L,N,O,Q,V],[D,E,L,N,Q,V],[D,E,N,O,Q,V],[D,E,N,Q,V],[D,E,V],[D,K,L,N,O,Q],[D,K,L,N,O,Q,V],[D,K,L,N,Q],[D,K,L,N,Q,V],[D,K,N,O,Q],[D,K,N,O,Q,V],[D,K,N,Q],[D,K,N,Q,V],[D,L,N,O,Q],[D,L,N,O,Q,V],[D,L,N,Q],[D,L,N,Q,V],[D,N,O,Q],[D,N,O,Q,V],[D,N,Q],[D,N,Q,V],[D,V],[E],[E,K,L,N,O,Q,V],[E,K,L,N,Q,V],[E,K,N,O,Q,V],[E,K,N,Q,V],[E,L,N,O,Q,V],[E,L,N,Q,V],[E,N,O,Q,V],[E,N,Q,V],[E,V],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,O,Q,V],[K,L,N,Q],[K,L,N,Q,V],[K,N],[K,N,O],[K,N,O,Q],[K,N,O,Q,V],[K,N,Q],[K,N,Q,V],[L,N],[L,N,O],[L,N,O,Q],[L,N,O,Q,V],[L,N,Q],[L,N,Q,V],[N],[N,O],[N,O,Q],[N,O,Q,V],[N,Q],[N,Q,V],[V]]),ground([F,G,H,M,P,R,S,T,U,W,X]);mshare([[J],[J,B,C,D,E,K,L,N,O,Q,V],[J,B,C,D,E,K,L,N,Q,V],[J,B,C,D,E,K,N,O,Q,V],[J,B,C,D,E,K,N,Q,V],[J,B,C,D,E,L,N,O,Q,V],[J,B,C,D,E,L,N,Q,V],[J,B,C,D,E,N,O,Q,V],[J,B,C,D,E,N,Q,V],[J,B,C,D,K,L,N,O,Q,V],[J,B,C,D,K,L,N,Q,V],[J,B,C,D,K,N,O,Q,V],[J,B,C,D,K,N,Q,V],[J,B,C,D,L,N,O,Q,V],[J,B,C,D,L,N,Q,V],[J,B,C,D,N,O,Q,V],[J,B,C,D,N,Q,V],[J,B,C,E,K,L,N,O,Q,V],[J,B,C,E,K,L,N,Q,V],[J,B,C,E,K,N,O,Q,V],[J,B,C,E,K,N,Q,V],[J,B,C,E,L,N,O,Q,V],[J,B,C,E,L,N,Q,V],[J,B,C,E,N,O,Q,V],[J,B,C,E,N,Q,V],[J,B,C,K,L,N,O,Q,V],[J,B,C,K,L,N,Q,V],[J,B,C,K,N,O,Q,V],[J,B,C,K,N,Q,V],[J,B,C,L,N,O,Q,V],[J,B,C,L,N,Q,V],[J,B,C,N,O,Q,V],[J,B,C,N,Q,V],[J,B,D,E,K,L,N,O,Q,V],[J,B,D,E,K,L,N,Q,V],[J,B,D,E,K,N,O,Q,V],[J,B,D,E,K,N,Q,V],[J,B,D,E,L,N,O,Q,V],[J,B,D,E,L,N,Q,V],[J,B,D,E,N,O,Q,V],[J,B,D,E,N,Q,V],[J,B,D,K,L,N,O,Q,V],[J,B,D,K,L,N,Q,V],[J,B,D,K,N,O,Q,V],[J,B,D,K,N,Q,V],[J,B,D,L,N,O,Q,V],[J,B,D,L,N,Q,V],[J,B,D,N,O,Q,V],[J,B,D,N,Q,V],[J,B,E,K,L,N,O,Q,V],[J,B,E,K,L,N,Q,V],[J,B,E,K,N,O,Q,V],[J,B,E,K,N,Q,V],[J,B,E,L,N,O,Q,V],[J,B,E,L,N,Q,V],[J,B,E,N,O,Q,V],[J,B,E,N,Q,V],[J,B,K,L,N,O,Q,V],[J,B,K,L,N,Q,V],[J,B,K,N,O,Q,V],[J,B,K,N,Q,V],[J,B,L,N,O,Q,V],[J,B,L,N,Q,V],[J,B,N,O,Q,V],[J,B,N,Q,V],[J,C,D,E,K,L,N,O,Q,V],[J,C,D,E,K,L,N,Q,V],[J,C,D,E,K,N,O,Q,V],[J,C,D,E,K,N,Q,V],[J,C,D,E,L,N,O,Q,V],[J,C,D,E,L,N,Q,V],[J,C,D,E,N,O,Q,V],[J,C,D,E,N,Q,V],[J,C,D,K,L,N,O,Q,V],[J,C,D,K,L,N,Q,V],[J,C,D,K,N,O,Q,V],[J,C,D,K,N,Q,V],[J,C,D,L,N,O,Q,V],[J,C,D,L,N,Q,V],[J,C,D,N,O,Q,V],[J,C,D,N,Q,V],[J,C,E,K,L,N,O,Q,V],[J,C,E,K,L,N,Q,V],[J,C,E,K,N,O,Q,V],[J,C,E,K,N,Q,V],[J,C,E,L,N,O,Q,V],[J,C,E,L,N,Q,V],[J,C,E,N,O,Q,V],[J,C,E,N,Q,V],[J,C,K,L,N,O,Q,V],[J,C,K,L,N,Q,V],[J,C,K,N,O,Q,V],[J,C,K,N,Q,V],[J,C,L,N,O,Q,V],[J,C,L,N,Q,V],[J,C,N,O,Q,V],[J,C,N,Q,V],[J,D,E,K,L,N,O,Q,V],[J,D,E,K,L,N,Q,V],[J,D,E,K,N,O,Q,V],[J,D,E,K,N,Q,V],[J,D,E,L,N,O,Q,V],[J,D,E,L,N,Q,V],[J,D,E,N,O,Q,V],[J,D,E,N,Q,V],[J,D,E,V],[J,D,K,L,N,O,Q,V],[J,D,K,L,N,Q,V],[J,D,K,N,O,Q,V],[J,D,K,N,Q,V],[J,D,L,N,O,Q,V],[J,D,L,N,Q,V],[J,D,N,O,Q,V],[J,D,N,Q,V],[J,D,V],[J,E],[J,E,K,L,N,O,Q,V],[J,E,K,L,N,Q,V],[J,E,K,N,O,Q,V],[J,E,K,N,Q,V],[J,E,L,N,O,Q,V],[J,E,L,N,Q,V],[J,E,N,O,Q,V],[J,E,N,Q,V],[J,E,V],[J,K,L,N,O,Q,V],[J,K,L,N,Q,V],[J,K,N,O,Q,V],[J,K,N,Q,V],[J,L,N,O,Q,V],[J,L,N,Q,V],[J,N,O,Q,V],[J,N,Q,V],[J,V],[B],[B,C,D,E,K,L,N,O,Q,V],[B,C,D,E,K,L,N,Q,V],[B,C,D,E,K,N,O,Q,V],[B,C,D,E,K,N,Q,V],[B,C,D,E,L,N,O,Q,V],[B,C,D,E,L,N,Q,V],[B,C,D,E,N,O,Q,V],[B,C,D,E,N,Q,V],[B,C,D,K,L,N,O,Q],[B,C,D,K,L,N,O,Q,V],[B,C,D,K,L,N,Q],[B,C,D,K,L,N,Q,V],[B,C,D,K,N,O,Q],[B,C,D,K,N,O,Q,V],[B,C,D,K,N,Q],[B,C,D,K,N,Q,V],[B,C,D,L,N,O,Q],[B,C,D,L,N,O,Q,V],[B,C,D,L,N,Q],[B,C,D,L,N,Q,V],[B,C,D,N,O,Q],[B,C,D,N,O,Q,V],[B,C,D,N,Q],[B,C,D,N,Q,V],[B,C,E,K,L,N,O,Q,V],[B,C,E,K,L,N,Q,V],[B,C,E,K,N,O,Q,V],[B,C,E,K,N,Q,V],[B,C,E,L,N,O,Q,V],[B,C,E,L,N,Q,V],[B,C,E,N,O,Q,V],[B,C,E,N,Q,V],[B,C,K,L,N],[B,C,K,L,N,O],[B,C,K,L,N,O,Q],[B,C,K,L,N,O,Q,V],[B,C,K,L,N,Q],[B,C,K,L,N,Q,V],[B,C,K,N],[B,C,K,N,O],[B,C,K,N,O,Q],[B,C,K,N,O,Q,V],[B,C,K,N,Q],[B,C,K,N,Q,V],[B,C,L,N],[B,C,L,N,O],[B,C,L,N,O,Q],[B,C,L,N,O,Q,V],[B,C,L,N,Q],[B,C,L,N,Q,V],[B,C,N],[B,C,N,O],[B,C,N,O,Q],[B,C,N,O,Q,V],[B,C,N,Q],[B,C,N,Q,V],[B,D,E,K,L,N,O,Q,V],[B,D,E,K,L,N,Q,V],[B,D,E,K,N,O,Q,V],[B,D,E,K,N,Q,V],[B,D,E,L,N,O,Q,V],[B,D,E,L,N,Q,V],[B,D,E,N,O,Q,V],[B,D,E,N,Q,V],[B,D,K,L,N,O,Q],[B,D,K,L,N,O,Q,V],[B,D,K,L,N,Q],[B,D,K,L,N,Q,V],[B,D,K,N,O,Q],[B,D,K,N,O,Q,V],[B,D,K,N,Q],[B,D,K,N,Q,V],[B,D,L,N,O,Q],[B,D,L,N,O,Q,V],[B,D,L,N,Q],[B,D,L,N,Q,V],[B,D,N,O,Q],[B,D,N,O,Q,V],[B,D,N,Q],[B,D,N,Q,V],[B,E,K,L,N,O,Q,V],[B,E,K,L,N,Q,V],[B,E,K,N,O,Q,V],[B,E,K,N,Q,V],[B,E,L,N,O,Q,V],[B,E,L,N,Q,V],[B,E,N,O,Q,V],[B,E,N,Q,V],[B,K],[B,K,L,N],[B,K,L,N,O],[B,K,L,N,O,Q],[B,K,L,N,O,Q,V],[B,K,L,N,Q],[B,K,L,N,Q,V],[B,K,N],[B,K,N,O],[B,K,N,O,Q],[B,K,N,O,Q,V],[B,K,N,Q],[B,K,N,Q,V],[B,L,N],[B,L,N,O],[B,L,N,O,Q],[B,L,N,O,Q,V],[B,L,N,Q],[B,L,N,Q,V],[B,N],[B,N,O],[B,N,O,Q],[B,N,O,Q,V],[B,N,Q],[B,N,Q,V],[C],[C,D,E,K,L,N,O,Q,V],[C,D,E,K,L,N,Q,V],[C,D,E,K,N,O,Q,V],[C,D,E,K,N,Q,V],[C,D,E,L,N,O,Q,V],[C,D,E,L,N,Q,V],[C,D,E,N,O,Q,V],[C,D,E,N,Q,V],[C,D,K,L,N,O,Q],[C,D,K,L,N,O,Q,V],[C,D,K,L,N,Q],[C,D,K,L,N,Q,V],[C,D,K,N,O,Q],[C,D,K,N,O,Q,V],[C,D,K,N,Q],[C,D,K,N,Q,V],[C,D,L,N,O,Q],[C,D,L,N,O,Q,V],[C,D,L,N,Q],[C,D,L,N,Q,V],[C,D,N,O,Q],[C,D,N,O,Q,V],[C,D,N,Q],[C,D,N,Q,V],[C,E,K,L,N,O,Q,V],[C,E,K,L,N,Q,V],[C,E,K,N,O,Q,V],[C,E,K,N,Q,V],[C,E,L,N,O,Q,V],[C,E,L,N,Q,V],[C,E,N,O,Q,V],[C,E,N,Q,V],[C,K,L,N],[C,K,L,N,O],[C,K,L,N,O,Q],[C,K,L,N,O,Q,V],[C,K,L,N,Q],[C,K,L,N,Q,V],[C,K,N],[C,K,N,O],[C,K,N,O,Q],[C,K,N,O,Q,V],[C,K,N,Q],[C,K,N,Q,V],[C,L,N],[C,L,N,O],[C,L,N,O,Q],[C,L,N,O,Q,V],[C,L,N,Q],[C,L,N,Q,V],[C,N],[C,N,O],[C,N,O,Q],[C,N,O,Q,V],[C,N,Q],[C,N,Q,V],[D],[D,E,K,L,N,O,Q,V],[D,E,K,L,N,Q,V],[D,E,K,N,O,Q,V],[D,E,K,N,Q,V],[D,E,L,N,O,Q,V],[D,E,L,N,Q,V],[D,E,N,O,Q,V],[D,E,N,Q,V],[D,E,V],[D,K,L,N,O,Q],[D,K,L,N,O,Q,V],[D,K,L,N,Q],[D,K,L,N,Q,V],[D,K,N,O,Q],[D,K,N,O,Q,V],[D,K,N,Q],[D,K,N,Q,V],[D,L,N,O,Q],[D,L,N,O,Q,V],[D,L,N,Q],[D,L,N,Q,V],[D,N,O,Q],[D,N,O,Q,V],[D,N,Q],[D,N,Q,V],[D,V],[E],[E,K,L,N,O,Q,V],[E,K,L,N,Q,V],[E,K,N,O,Q,V],[E,K,N,Q,V],[E,L,N,O,Q,V],[E,L,N,Q,V],[E,N,O,Q,V],[E,N,Q,V],[E,V],[K],[K,L,N],[K,L,N,O],[K,L,N,O,Q],[K,L,N,O,Q,V],[K,L,N,Q],[K,L,N,Q,V],[K,N],[K,N,O],[K,N,O,Q],[K,N,O,Q,V],[K,N,Q],[K,N,Q,V],[L,N],[L,N,O],[L,N,O,Q],[L,N,O,Q,V],[L,N,Q],[L,N,Q,V],[N],[N,O],[N,O,Q],[N,O,Q,V],[N,Q],[N,Q,V],[V]]),ground([F,G,H,I,M,P,R,S,T,U,W,X]))).

:- true pred subj(_A,B,_B,D,E,F,G)
   : ( mshare([[_A],[B],[_B],[E],[F],[G]]),
       ground([D]), linear(_A), linear(B), linear(_B), linear(E), linear(G) )
   => ( mshare([[_A],[_A,B],[_A,B,F],[_A,B,F,G],[_A,B,G],[_A,F],[_A,F,G],[_A,G],[B],[B,F],[B,F,G],[_B],[F],[F,G],[G]]),
        ground([D,E]), linear(_B) ).

:- true pred subj(_A,B,_B,D,E,F,G)
   : ( mshare([[_A],[B],[_B],[E],[G]]),
       ground([D,F]), linear(_A), linear(B), linear(_B), linear(E), linear(G) )
   => ( mshare([[_A],[_A,B],[_A,B,G],[_A,G],[B],[_B],[G]]),
        ground([D,E,F]), linear(_B) ).

subj(there,B,C+be,D,E,F,G) :-
    true((mshare([[B],[E],[F],[G],[C]]),ground([D]),linear(B),linear(E),linear(G),linear(C);mshare([[B],[E],[G],[C]]),ground([D,F]),linear(B),linear(E),linear(G),linear(C))),
    ~(there,D,E,F,G),
    true((mshare([[B],[F],[F,G],[C]]),ground([D,E]),linear(B),linear(C);mshare([[B],[C]]),ground([D,E,F,G]),linear(B),linear(C))).
subj(B,C,D,E,F,G,H) :-
    true((mshare([[B],[C],[D],[F],[G],[H],[I],[J],[K],[L]]),ground([E]),linear(B),linear(C),linear(D),linear(F),linear(H),linear(I),linear(J),linear(K),linear(L);mshare([[B],[C],[D],[F],[H],[I],[J],[K],[L]]),ground([E,G]),linear(B),linear(C),linear(D),linear(F),linear(H),linear(I),linear(J),linear(K),linear(L))),
    s_all(I),
    true((mshare([[B],[C],[D],[F],[G],[H],[J],[K],[L]]),ground([E,I]),linear(B),linear(C),linear(D),linear(F),linear(H),linear(J),linear(K),linear(L);mshare([[B],[C],[D],[F],[H],[J],[K],[L]]),ground([E,G,I]),linear(B),linear(C),linear(D),linear(F),linear(H),linear(J),linear(K),linear(L))),
    subj_case(J),
    true((mshare([[B],[C],[D],[F],[G],[H],[K],[L]]),ground([E,I,J]),linear(B),linear(C),linear(D),linear(F),linear(H),linear(K),linear(L);mshare([[B],[C],[D],[F],[H],[K],[L]]),ground([E,G,I,J]),linear(B),linear(C),linear(D),linear(F),linear(H),linear(K),linear(L))),
    np(B,C,J,K,subj,I,L,E,F,G,H),
    true((mshare([[B],[B,C],[B,C,G],[B,C,G,H],[B,C,G,H,K],[B,C,G,H,K,L],[B,C,G,H,L],[B,C,G,K],[B,C,G,K,L],[B,C,G,L],[B,C,H],[B,G],[B,G,H],[B,G,H,K],[B,G,H,K,L],[B,G,H,L],[B,G,K],[B,G,K,L],[B,G,L],[B,H],[C],[C,G],[C,G,H],[C,G,H,K],[C,G,H,K,L],[C,G,H,L],[C,G,K],[C,G,K,L],[C,G,L],[D],[G],[G,H],[G,H,K],[G,H,K,L],[G,H,L],[G,K],[G,K,L],[G,L],[H]]),ground([E,F,I,J]),linear(D);mshare([[B],[B,C],[B,C,H],[B,H],[C],[D],[H]]),ground([E,F,G,I,J,K,L]),linear(D))).

:- true pred np_head(B,C,D,E,F,G,H,I,J)
   : ( (D=_A+_B),
       mshare([[B],[C],[E],[F],[H],[J],[_A],[_B]]),
       ground([G,I]), linear(B), linear(C), linear(E), linear(F), linear(H), linear(J), linear(_A), linear(_B) )
   => ( mshare([[B],[B,C],[C],[E,F],[F]]),
        ground([G,H,I,J,_A,_B]), linear(E) ).

:- true pred np_head(B,C,D,E,F,G,H,I,J)
   : ( (D=_A+_B),
       mshare([[B],[C,I],[E],[F],[H],[I],[J],[_A],[_B]]),
       ground([G]), linear(B), linear(E), linear(F), linear(H), linear(J), linear(_A), linear(_B) )
   => ( mshare([[B],[B,C,F,I],[B,C,F,I,J],[B,C,F,I,J,_A],[B,C,F,I,J,_A,_B],[B,C,F,I,J,_B],[B,C,F,I,_A],[B,C,F,I,_A,_B],[B,C,F,I,_B],[B,C,I],[B,C,I,J],[B,C,I,J,_A],[B,C,I,J,_A,_B],[B,C,I,J,_B],[B,C,I,_A],[B,C,I,_A,_B],[B,C,I,_B],[B,F],[B,F,I],[B,F,I,J],[B,F,I,J,_A],[B,F,I,J,_A,_B],[B,F,I,J,_B],[B,F,I,_A],[B,F,I,_A,_B],[B,F,I,_B],[B,I],[B,I,J],[B,I,J,_A],[B,I,J,_A,_B],[B,I,J,_B],[B,I,_A],[B,I,_A,_B],[B,I,_B],[C,F,I],[C,F,I,J],[C,F,I,J,_A],[C,F,I,J,_A,_B],[C,F,I,J,_B],[C,F,I,_A],[C,F,I,_A,_B],[C,F,I,_B],[C,I],[C,I,J],[C,I,J,_A],[C,I,J,_A,_B],[C,I,J,_B],[C,I,_A],[C,I,_A,_B],[C,I,_B],[E,F],[F],[F,I],[F,I,J],[F,I,J,_A],[F,I,J,_A,_B],[F,I,J,_B],[F,I,_A],[F,I,_A,_B],[F,I,_B],[I],[I,J],[I,J,_A],[I,J,_A,_B],[I,J,_B],[I,_A],[I,_A,_B],[I,_B]]),
        ground([G,H]), linear(E) ).

:- true pred np_head(B,C,D,E,F,G,H,I,J)
   : ( (D=_A+_B),
       mshare([[B],[E],[F],[H],[J],[_B]]),
       ground([C,G,I,_A]), linear(B), linear(E), linear(F), linear(H), linear(J), linear(_B) )
   => ( mshare([[B],[E,F],[F]]),
        ground([C,G,H,I,J,_A,_B]), linear(E) ).

:- true pred np_head(B,C,D,E,F,G,H,I,J)
   : ( (D=_A+_B),
       mshare([[B],[C],[E],[F],[H],[I],[J],[_A],[_B]]),
       ground([G]), linear(B), linear(C), linear(E), linear(F), linear(H), linear(J), linear(_A), linear(_B) )
   => ( mshare([[B],[B,C],[B,C,F],[B,C,F,I],[B,C,F,I,J],[B,C,F,I,J,_A],[B,C,F,I,J,_A,_B],[B,C,F,I,J,_B],[B,C,F,I,_A],[B,C,F,I,_A,_B],[B,C,F,I,_B],[B,C,I],[B,C,I,J],[B,C,I,J,_A],[B,C,I,J,_A,_B],[B,C,I,J,_B],[B,C,I,_A],[B,C,I,_A,_B],[B,C,I,_B],[B,F],[B,F,I],[B,F,I,J],[B,F,I,J,_A],[B,F,I,J,_A,_B],[B,F,I,J,_B],[B,F,I,_A],[B,F,I,_A,_B],[B,F,I,_B],[B,I],[B,I,J],[B,I,J,_A],[B,I,J,_A,_B],[B,I,J,_B],[B,I,_A],[B,I,_A,_B],[B,I,_B],[C],[C,F],[C,F,I],[C,F,I,J],[C,F,I,J,_A],[C,F,I,J,_A,_B],[C,F,I,J,_B],[C,F,I,_A],[C,F,I,_A,_B],[C,F,I,_B],[C,I],[C,I,J],[C,I,J,_A],[C,I,J,_A,_B],[C,I,J,_B],[C,I,_A],[C,I,_A,_B],[C,I,_B],[E,F],[F],[F,I],[F,I,J],[F,I,J,_A],[F,I,J,_A,_B],[F,I,J,_B],[F,I,_A],[F,I,_A,_B],[F,I,_B],[I],[I,J],[I,J,_A],[I,J,_A,_B],[I,J,_B],[I,_A],[I,_A,_B],[I,_B]]),
        ground([G,H]), linear(E) ).

:- true pred np_head(B,C,D,E,F,G,H,I,J)
   : ( (D=_A+_B),
       mshare([[B],[C],[E],[F],[H],[I],[J],[_B]]),
       ground([G,_A]), linear(B), linear(C), linear(E), linear(F), linear(H), linear(J), linear(_B) )
   => ( mshare([[B],[B,C],[B,C,F],[B,C,F,I],[B,C,F,I,J],[B,C,F,I,J,_B],[B,C,F,I,_B],[B,C,I],[B,C,I,J],[B,C,I,J,_B],[B,C,I,_B],[B,F],[B,F,I],[B,F,I,J],[B,F,I,J,_B],[B,F,I,_B],[B,I],[B,I,J],[B,I,J,_B],[B,I,_B],[C],[C,F],[C,F,I],[C,F,I,J],[C,F,I,J,_B],[C,F,I,_B],[C,I],[C,I,J],[C,I,J,_B],[C,I,_B],[E,F],[F],[F,I],[F,I,J],[F,I,J,_B],[F,I,_B],[I],[I,J],[I,J,_B],[I,_B]]),
        ground([G,H,_A]), linear(E) ).

:- true pred np_head(B,C,D,E,F,G,H,I,J)
   : ( (D=_A+_B),
       mshare([[B],[E],[F],[H],[I],[J],[_B]]),
       ground([C,G,_A]), linear(B), linear(E), linear(F), linear(H), linear(J), linear(_B) )
   => ( mshare([[B],[B,F],[B,F,I],[B,F,I,J],[B,F,I,J,_B],[B,F,I,_B],[B,I],[B,I,J],[B,I,J,_B],[B,I,_B],[E,F],[F],[F,I],[F,I,J],[F,I,J,_B],[F,I,_B],[I],[I,J],[I,J,_B],[I,_B]]),
        ground([C,G,H,_A]), linear(E) ).

np_head(B,C,D,E,F,G,H,I,J) :-
    true((mshare([[B],[C],[D],[E],[F],[H],[I],[J],[K],[L],[M],[N],[O],[P]]),ground([G]),linear(B),linear(C),linear(D),linear(E),linear(F),linear(H),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P);mshare([[B],[C],[D],[E],[F],[H],[J],[K],[L],[M],[N],[O],[P]]),ground([G,I]),linear(B),linear(C),linear(D),linear(E),linear(F),linear(H),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P);mshare([[B],[C,I],[D],[E],[F],[H],[I],[J],[K],[L],[M],[N],[O],[P]]),ground([G]),linear(B),linear(D),linear(E),linear(F),linear(H),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P);mshare([[B],[D],[E],[F],[H],[I],[J],[K],[L],[M],[N],[O],[P]]),ground([C,G]),linear(B),linear(D),linear(E),linear(F),linear(H),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P);mshare([[B],[D],[E],[F],[H],[J],[K],[L],[M],[N],[O],[P]]),ground([C,G,I]),linear(B),linear(D),linear(E),linear(F),linear(H),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P))),
    np_head0(K,L,M,G,N,I,O),
    true((mshare([[B],[C],[D],[E],[F],[H],[I],[I,K],[I,K,L],[I,K,L,M],[I,K,L,M,O],[I,K,L,O],[I,K,M],[I,K,M,O],[I,K,O],[I,L],[I,L,M],[I,L,M,O],[I,L,O],[I,M],[I,M,O],[I,O],[J],[K],[K,L],[L],[P]]),ground([G,N]),linear(B),linear(C),linear(D),linear(E),linear(F),linear(H),linear(J),linear(P);mshare([[B],[C],[D],[E],[F],[H],[J],[K],[K,L],[L],[P]]),ground([G,I,M,N,O]),linear(B),linear(C),linear(D),linear(E),linear(F),linear(H),linear(J),linear(P);mshare([[B],[C,I],[C,I,K],[C,I,K,L],[C,I,K,L,M],[C,I,K,L,M,O],[C,I,K,L,O],[C,I,K,M],[C,I,K,M,O],[C,I,K,O],[C,I,L],[C,I,L,M],[C,I,L,M,O],[C,I,L,O],[C,I,M],[C,I,M,O],[C,I,O],[D],[E],[F],[H],[I],[I,K],[I,K,L],[I,K,L,M],[I,K,L,M,O],[I,K,L,O],[I,K,M],[I,K,M,O],[I,K,O],[I,L],[I,L,M],[I,L,M,O],[I,L,O],[I,M],[I,M,O],[I,O],[J],[K],[K,L],[L],[P]]),ground([G,N]),linear(B),linear(D),linear(E),linear(F),linear(H),linear(J),linear(P);mshare([[B],[D],[E],[F],[H],[I],[I,K],[I,K,L],[I,K,L,M],[I,K,L,M,O],[I,K,L,O],[I,K,M],[I,K,M,O],[I,K,O],[I,L],[I,L,M],[I,L,M,O],[I,L,O],[I,M],[I,M,O],[I,O],[J],[K],[K,L],[L],[P]]),ground([C,G,N]),linear(B),linear(D),linear(E),linear(F),linear(H),linear(J),linear(P);mshare([[B],[D],[E],[F],[H],[J],[K],[K,L],[L],[P]]),ground([C,G,I,M,N,O]),linear(B),linear(D),linear(E),linear(F),linear(H),linear(J),linear(P))),
    possessive(K,L,M,P,P,B,C,D,E,F,N,H,O,J),
    true((mshare([[B],[B,C],[B,C,D,F,I,J,K,L,M,O],[B,C,D,F,I,J,K,L,O],[B,C,D,F,I,J,K,M,O],[B,C,D,F,I,J,K,O],[B,C,D,F,I,J,L,M,O],[B,C,D,F,I,J,L,O],[B,C,D,F,I,J,M,O],[B,C,D,F,I,J,O],[B,C,D,F,I,K,L,M,O],[B,C,D,F,I,K,L,O],[B,C,D,F,I,K,M,O],[B,C,D,F,I,K,O],[B,C,D,F,I,L,M,O],[B,C,D,F,I,L,O],[B,C,D,F,I,M,O],[B,C,D,F,I,O],[B,C,D,I,J,K,L,M,O],[B,C,D,I,J,M,O],[B,C,D,I,J,O],[B,C,D,I,K,L,M],[B,C,D,I,M,O],[B,C,D,I,O],[B,C,F],[B,C,F,I,J,K,L,M,O],[B,C,F,I,J,K,L,O],[B,C,F,I,J,K,M,O],[B,C,F,I,J,K,O],[B,C,F,I,J,L,M,O],[B,C,F,I,J,L,O],[B,C,F,I,J,M,O],[B,C,F,I,J,O],[B,C,F,I,K],[B,C,F,I,K,L],[B,C,F,I,K,L,M],[B,C,F,I,K,L,M,O],[B,C,F,I,K,L,O],[B,C,F,I,K,M],[B,C,F,I,K,M,O],[B,C,F,I,K,O],[B,C,F,I,L],[B,C,F,I,L,M],[B,C,F,I,L,M,O],[B,C,F,I,L,O],[B,C,F,I,M,O],[B,C,F,I,O],[B,C,F,K],[B,C,F,K,L],[B,C,F,L],[B,C,I,J,K,L,O],[B,C,I,J,M,O],[B,C,I,J,O],[B,C,I,K,L],[B,C,I,M,O],[B,C,I,O],[B,C,K,L],[B,D,F,I,J,K,L,M,O],[B,D,F,I,J,K,L,O],[B,D,F,I,J,K,M,O],[B,D,F,I,J,K,O],[B,D,F,I,J,L,M,O],[B,D,F,I,J,L,O],[B,D,F,I,J,M,O],[B,D,F,I,J,O],[B,D,F,I,K,L,M,O],[B,D,F,I,K,L,O],[B,D,F,I,K,M,O],[B,D,F,I,K,O],[B,D,F,I,L,M,O],[B,D,F,I,L,O],[B,D,F,I,M,O],[B,D,F,I,O],[B,D,I,J,K,M,O],[B,D,I,J,M,O],[B,D,I,J,O],[B,D,I,K,M],[B,D,I,M,O],[B,D,I,O],[B,F],[B,F,I,J,K,L,M,O],[B,F,I,J,K,L,O],[B,F,I,J,K,M,O],[B,F,I,J,K,O],[B,F,I,J,L,M,O],[B,F,I,J,L,O],[B,F,I,J,M,O],[B,F,I,J,O],[B,F,I,K],[B,F,I,K,L],[B,F,I,K,L,M],[B,F,I,K,L,M,O],[B,F,I,K,L,O],[B,F,I,K,M],[B,F,I,K,M,O],[B,F,I,K,O],[B,F,I,L],[B,F,I,L,M],[B,F,I,L,M,O],[B,F,I,L,O],[B,F,I,M,O],[B,F,I,O],[B,F,K],[B,F,K,L],[B,F,L],[B,I,J,K,O],[B,I,J,M,O],[B,I,J,O],[B,I,K],[B,I,M,O],[B,I,O],[B,K],[C],[C,D,F,I,J,K,L,M,O],[C,D,F,I,J,K,L,O],[C,D,F,I,J,K,M,O],[C,D,F,I,J,K,O],[C,D,F,I,J,L,M,O],[C,D,F,I,J,L,O],[C,D,F,I,J,M,O],[C,D,F,I,J,O],[C,D,F,I,K,L,M,O],[C,D,F,I,K,L,O],[C,D,F,I,K,M,O],[C,D,F,I,K,O],[C,D,F,I,L,M,O],[C,D,F,I,L,O],[C,D,F,I,M,O],[C,D,F,I,O],[C,D,I,J,L,M,O],[C,D,I,J,M,O],[C,D,I,J,O],[C,D,I,L,M],[C,D,I,M,O],[C,D,I,O],[C,F],[C,F,I,J,K,L,M,O],[C,F,I,J,K,L,O],[C,F,I,J,K,M,O],[C,F,I,J,K,O],[C,F,I,J,L,M,O],[C,F,I,J,L,O],[C,F,I,J,M,O],[C,F,I,J,O],[C,F,I,K],[C,F,I,K,L],[C,F,I,K,L,M],[C,F,I,K,L,M,O],[C,F,I,K,L,O],[C,F,I,K,M],[C,F,I,K,M,O],[C,F,I,K,O],[C,F,I,L],[C,F,I,L,M],[C,F,I,L,M,O],[C,F,I,L,O],[C,F,I,M,O],[C,F,I,O],[C,F,K],[C,F,K,L],[C,F,L],[C,I,J,L,O],[C,I,J,M,O],[C,I,J,O],[C,I,L],[C,I,M,O],[C,I,O],[C,L],[D,F,I,J,K,L,M,O],[D,F,I,J,K,L,O],[D,F,I,J,K,M,O],[D,F,I,J,K,O],[D,F,I,J,L,M,O],[D,F,I,J,L,O],[D,F,I,J,M,O],[D,F,I,J,O],[D,F,I,K,L,M,O],[D,F,I,K,L,O],[D,F,I,K,M,O],[D,F,I,K,O],[D,F,I,L,M,O],[D,F,I,L,O],[D,F,I,M,O],[D,F,I,O],[D,I,J,M,O],[D,I,J,O],[D,I,M],[D,I,M,O],[D,I,O],[E,F],[E,F,P],[F],[F,I,J,K,L,M,O],[F,I,J,K,L,O],[F,I,J,K,M,O],[F,I,J,K,O],[F,I,J,L,M,O],[F,I,J,L,O],[F,I,J,M,O],[F,I,J,O],[F,I,K],[F,I,K,L],[F,I,K,L,M],[F,I,K,L,M,O],[F,I,K,L,O],[F,I,K,M],[F,I,K,M,O],[F,I,K,O],[F,I,L],[F,I,L,M],[F,I,L,M,O],[F,I,L,O],[F,I,M,O],[F,I,O],[F,K],[F,K,L],[F,L],[I],[I,J,M,O],[I,J,O],[I,M],[I,M,O],[I,O]]),ground([G,H,N]),linear(E);mshare([[B],[B,C],[B,C,K,L],[B,K],[C],[C,L],[E,F],[E,F,P],[F],[F,K],[F,K,L],[F,L]]),ground([D,G,H,I,J,M,N,O]),linear(E);mshare([[B],[B,C,D,F,I,J,K,L,M,O],[B,C,D,F,I,J,K,L,O],[B,C,D,F,I,J,K,M,O],[B,C,D,F,I,J,K,O],[B,C,D,F,I,J,L,M,O],[B,C,D,F,I,J,L,O],[B,C,D,F,I,J,M,O],[B,C,D,F,I,J,O],[B,C,D,F,I,K,L,M,O],[B,C,D,F,I,K,L,O],[B,C,D,F,I,K,M,O],[B,C,D,F,I,K,O],[B,C,D,F,I,L,M,O],[B,C,D,F,I,L,O],[B,C,D,F,I,M,O],[B,C,D,F,I,O],[B,C,D,I,J,K,L,M,O],[B,C,D,I,J,M,O],[B,C,D,I,J,O],[B,C,D,I,K,L,M],[B,C,D,I,M,O],[B,C,D,I,O],[B,C,F,I],[B,C,F,I,J,K,L,M,O],[B,C,F,I,J,K,L,O],[B,C,F,I,J,K,M,O],[B,C,F,I,J,K,O],[B,C,F,I,J,L,M,O],[B,C,F,I,J,L,O],[B,C,F,I,J,M,O],[B,C,F,I,J,O],[B,C,F,I,K],[B,C,F,I,K,L],[B,C,F,I,K,L,M],[B,C,F,I,K,L,M,O],[B,C,F,I,K,L,O],[B,C,F,I,K,M],[B,C,F,I,K,M,O],[B,C,F,I,K,O],[B,C,F,I,L],[B,C,F,I,L,M],[B,C,F,I,L,M,O],[B,C,F,I,L,O],[B,C,F,I,M],[B,C,F,I,M,O],[B,C,F,I,O],[B,C,I],[B,C,I,J,K,L,O],[B,C,I,J,M,O],[B,C,I,J,O],[B,C,I,K,L],[B,C,I,M],[B,C,I,M,O],[B,C,I,O],[B,D,F,I,J,K,L,M,O],[B,D,F,I,J,K,L,O],[B,D,F,I,J,K,M,O],[B,D,F,I,J,K,O],[B,D,F,I,J,L,M,O],[B,D,F,I,J,L,O],[B,D,F,I,J,M,O],[B,D,F,I,J,O],[B,D,F,I,K,L,M,O],[B,D,F,I,K,L,O],[B,D,F,I,K,M,O],[B,D,F,I,K,O],[B,D,F,I,L,M,O],[B,D,F,I,L,O],[B,D,F,I,M,O],[B,D,F,I,O],[B,D,I,J,K,M,O],[B,D,I,J,M,O],[B,D,I,J,O],[B,D,I,K,M],[B,D,I,M,O],[B,D,I,O],[B,F],[B,F,I,J,K,L,M,O],[B,F,I,J,K,L,O],[B,F,I,J,K,M,O],[B,F,I,J,K,O],[B,F,I,J,L,M,O],[B,F,I,J,L,O],[B,F,I,J,M,O],[B,F,I,J,O],[B,F,I,K],[B,F,I,K,L],[B,F,I,K,L,M],[B,F,I,K,L,M,O],[B,F,I,K,L,O],[B,F,I,K,M],[B,F,I,K,M,O],[B,F,I,K,O],[B,F,I,L],[B,F,I,L,M],[B,F,I,L,M,O],[B,F,I,L,O],[B,F,I,M,O],[B,F,I,O],[B,F,K],[B,F,K,L],[B,F,L],[B,I,J,K,O],[B,I,J,M,O],[B,I,J,O],[B,I,K],[B,I,M,O],[B,I,O],[B,K],[C,D,F,I,J,K,L,M,O],[C,D,F,I,J,K,L,O],[C,D,F,I,J,K,M,O],[C,D,F,I,J,K,O],[C,D,F,I,J,L,M,O],[C,D,F,I,J,L,O],[C,D,F,I,J,M,O],[C,D,F,I,J,O],[C,D,F,I,K,L,M,O],[C,D,F,I,K,L,O],[C,D,F,I,K,M,O],[C,D,F,I,K,O],[C,D,F,I,L,M,O],[C,D,F,I,L,O],[C,D,F,I,M,O],[C,D,F,I,O],[C,D,I,J,L,M,O],[C,D,I,J,M,O],[C,D,I,J,O],[C,D,I,L,M],[C,D,I,M,O],[C,D,I,O],[C,F,I],[C,F,I,J,K,L,M,O],[C,F,I,J,K,L,O],[C,F,I,J,K,M,O],[C,F,I,J,K,O],[C,F,I,J,L,M,O],[C,F,I,J,L,O],[C,F,I,J,M,O],[C,F,I,J,O],[C,F,I,K],[C,F,I,K,L],[C,F,I,K,L,M],[C,F,I,K,L,M,O],[C,F,I,K,L,O],[C,F,I,K,M],[C,F,I,K,M,O],[C,F,I,K,O],[C,F,I,L],[C,F,I,L,M],[C,F,I,L,M,O],[C,F,I,L,O],[C,F,I,M],[C,F,I,M,O],[C,F,I,O],[C,I],[C,I,J,L,O],[C,I,J,M,O],[C,I,J,O],[C,I,L],[C,I,M],[C,I,M,O],[C,I,O],[D,F,I,J,K,L,M,O],[D,F,I,J,K,L,O],[D,F,I,J,K,M,O],[D,F,I,J,K,O],[D,F,I,J,L,M,O],[D,F,I,J,L,O],[D,F,I,J,M,O],[D,F,I,J,O],[D,F,I,K,L,M,O],[D,F,I,K,L,O],[D,F,I,K,M,O],[D,F,I,K,O],[D,F,I,L,M,O],[D,F,I,L,O],[D,F,I,M,O],[D,F,I,O],[D,I,J,M,O],[D,I,J,O],[D,I,M],[D,I,M,O],[D,I,O],[E,F],[E,F,P],[F],[F,I,J,K,L,M,O],[F,I,J,K,L,O],[F,I,J,K,M,O],[F,I,J,K,O],[F,I,J,L,M,O],[F,I,J,L,O],[F,I,J,M,O],[F,I,J,O],[F,I,K],[F,I,K,L],[F,I,K,L,M],[F,I,K,L,M,O],[F,I,K,L,O],[F,I,K,M],[F,I,K,M,O],[F,I,K,O],[F,I,L],[F,I,L,M],[F,I,L,M,O],[F,I,L,O],[F,I,M,O],[F,I,O],[F,K],[F,K,L],[F,L],[I],[I,J,M,O],[I,J,O],[I,M],[I,M,O],[I,O]]),ground([G,H,N]),linear(E);mshare([[B],[B,D,F,I,J,K,L,M,O],[B,D,F,I,J,K,L,O],[B,D,F,I,J,K,M,O],[B,D,F,I,J,K,O],[B,D,F,I,J,L,M,O],[B,D,F,I,J,L,O],[B,D,F,I,J,M,O],[B,D,F,I,J,O],[B,D,F,I,K,L,M,O],[B,D,F,I,K,L,O],[B,D,F,I,K,M,O],[B,D,F,I,K,O],[B,D,F,I,L,M,O],[B,D,F,I,L,O],[B,D,F,I,M,O],[B,D,F,I,O],[B,D,I,J,K,M,O],[B,D,I,J,M,O],[B,D,I,J,O],[B,D,I,K,M],[B,D,I,M,O],[B,D,I,O],[B,F],[B,F,I,J,K,L,M,O],[B,F,I,J,K,L,O],[B,F,I,J,K,M,O],[B,F,I,J,K,O],[B,F,I,J,L,M,O],[B,F,I,J,L,O],[B,F,I,J,M,O],[B,F,I,J,O],[B,F,I,K],[B,F,I,K,L],[B,F,I,K,L,M],[B,F,I,K,L,M,O],[B,F,I,K,L,O],[B,F,I,K,M],[B,F,I,K,M,O],[B,F,I,K,O],[B,F,I,L],[B,F,I,L,M],[B,F,I,L,M,O],[B,F,I,L,O],[B,F,I,M,O],[B,F,I,O],[B,F,K],[B,F,K,L],[B,F,L],[B,I,J,K,O],[B,I,J,M,O],[B,I,J,O],[B,I,K],[B,I,M,O],[B,I,O],[B,K],[D,F,I,J,K,L,M,O],[D,F,I,J,K,L,O],[D,F,I,J,K,M,O],[D,F,I,J,K,O],[D,F,I,J,L,M,O],[D,F,I,J,L,O],[D,F,I,J,M,O],[D,F,I,J,O],[D,F,I,K,L,M,O],[D,F,I,K,L,O],[D,F,I,K,M,O],[D,F,I,K,O],[D,F,I,L,M,O],[D,F,I,L,O],[D,F,I,M,O],[D,F,I,O],[D,I,J,M,O],[D,I,J,O],[D,I,M],[D,I,M,O],[D,I,O],[E,F],[E,F,P],[F],[F,I,J,K,L,M,O],[F,I,J,K,L,O],[F,I,J,K,M,O],[F,I,J,K,O],[F,I,J,L,M,O],[F,I,J,L,O],[F,I,J,M,O],[F,I,J,O],[F,I,K],[F,I,K,L],[F,I,K,L,M],[F,I,K,L,M,O],[F,I,K,L,O],[F,I,K,M],[F,I,K,M,O],[F,I,K,O],[F,I,L],[F,I,L,M],[F,I,L,M,O],[F,I,L,O],[F,I,M,O],[F,I,O],[F,K],[F,K,L],[F,L],[I],[I,J,M,O],[I,J,O],[I,M],[I,M,O],[I,O]]),ground([C,G,H,N]),linear(E);mshare([[B],[B,K],[E,F],[E,F,P],[F],[F,K],[F,K,L],[F,L]]),ground([C,D,G,H,I,J,M,N,O]),linear(E))).

:- true pred np_head0(B,C,D,E,H,F,G)
   : ( mshare([[B],[C],[D],[H],[F],[G]]),
       ground([E]), linear(B), linear(C), linear(D), linear(H), linear(G) )
   => ( mshare([[B],[B,C],[B,C,D,F],[B,C,D,F,G],[B,C,F],[B,C,F,G],[B,D,F],[B,D,F,G],[B,F],[B,F,G],[C],[C,D,F],[C,D,F,G],[C,F],[C,F,G],[D,F],[D,F,G],[F],[F,G]]),
        ground([E,H]) ).

:- true pred np_head0(B,C,D,E,H,F,G)
   : ( (D=_A+common),
       mshare([[B],[C],[H],[F],[G],[_A]]),
       ground([E]), linear(B), linear(C), linear(H), linear(G), linear(_A) )
   => ( mshare([[B,C],[B,C,F],[B,C,F,G],[B,C,F,G,_A],[B,C,F,_A],[B,F],[B,F,G],[B,F,G,_A],[B,F,_A],[C],[C,F],[C,F,G],[C,F,G,_A],[C,F,_A],[F],[F,G],[F,G,_A],[F,_A]]),
        ground([E,H]) ).

:- true pred np_head0(B,C,D,E,H,F,G)
   : ( mshare([[B],[C],[D],[H],[G]]),
       ground([E,F]), linear(B), linear(C), linear(D), linear(H), linear(G) )
   => ( mshare([[B],[B,C],[C]]),
        ground([D,E,H,F,G]) ).

np_head0(B,C,D,E,E,F,G) :-
    true((mshare([[B],[C],[D],[F],[G]]),ground([E]),linear(B),linear(C),linear(D),linear(G);mshare([[B],[C],[D],[G]]),ground([E,F]),linear(B),linear(C),linear(D),linear(G))),
    virtual(np_head0(B,C,D),F,G),
    true((mshare([[B,C,D,F],[B,C,D,F,G],[B,C,F],[B,C,F,G],[B,D,F],[B,D,F,G],[B,F],[B,F,G],[C,D,F],[C,D,F,G],[C,F],[C,F,G],[D,F],[D,F,G],[F],[F,G]]),ground([E]);ground([B,C,D,E,F,G]))).
np_head0(name(B),3+sin,def+proper,C,D,E,F) :-
    true((mshare([[D],[E],[F],[B]]),ground([C]),linear(D),linear(F),linear(B);mshare([[D],[F],[B]]),ground([C,E]),linear(D),linear(F),linear(B))),
    name(B,C,D,E,F),
    true((mshare([[E],[E,F],[E,F,B],[E,B]]),ground([C,D]);ground([C,D,E,F,B]))).
np_head0(np_head(B,C,D),3+E,F+common,G,H,I,J) :-
    true((mshare([[H],[I],[J],[B],[C],[D],[E],[F],[K],[L],[M],[N]]),ground([G]),linear(H),linear(J),linear(B),linear(C),linear(D),linear(E),linear(F),linear(K),linear(L),linear(M),linear(N);mshare([[H],[J],[B],[C],[D],[E],[F],[K],[L],[M],[N]]),ground([G,I]),linear(H),linear(J),linear(B),linear(C),linear(D),linear(E),linear(F),linear(K),linear(L),linear(M),linear(N))),
    determiner(B,E,F,G,K,I,L),
    true((mshare([[H],[I],[I,B],[I,B,E],[I,B,E,F],[I,B,E,F,L],[I,B,E,L],[I,B,F],[I,B,F,L],[I,B,L],[I,E],[I,E,F],[I,E,F,L],[I,E,L],[I,F],[I,F,L],[I,L],[J],[B,E],[C],[D],[E],[M],[N]]),ground([G,K]),linear(H),linear(J),linear(C),linear(D),linear(M),linear(N);mshare([[H],[J],[B,E],[C],[D],[E],[M],[N]]),ground([G,I,F,K,L]),linear(H),linear(J),linear(C),linear(D),linear(M),linear(N))),
    adjs(C,K,M,L,N),
    true((mshare([[H],[I],[I,B],[I,B,E],[I,B,E,F],[I,B,E,F,L],[I,B,E,F,L,N],[I,B,E,L],[I,B,E,L,N],[I,B,F],[I,B,F,L],[I,B,F,L,N],[I,B,L],[I,B,L,N],[I,E],[I,E,F],[I,E,F,L],[I,E,F,L,N],[I,E,L],[I,E,L,N],[I,F],[I,F,L],[I,F,L,N],[I,L],[I,L,N],[J],[B,E],[D],[E]]),ground([G,C,K,M]),linear(H),linear(J),linear(D);mshare([[H],[J],[B,E],[D],[E]]),ground([G,I,C,F,K,L,M,N]),linear(H),linear(J),linear(D))),
    noun(D,E,M,H,N,J),
    true((mshare([[I],[I,J,B,E,F,L,N],[I,J,B,E,L,N],[I,J,B,F,L,N],[I,J,B,L,N],[I,J,E,F,L,N],[I,J,E,L,N],[I,J,F,L,N],[I,J,L,N],[I,B],[I,B,E],[I,B,E,F],[I,B,E,F,L],[I,B,E,F,L,N],[I,B,E,L],[I,B,E,L,N],[I,B,F],[I,B,F,L],[I,B,F,L,N],[I,B,L],[I,B,L,N],[I,E],[I,E,F],[I,E,F,L],[I,E,F,L,N],[I,E,L],[I,E,L,N],[I,F],[I,F,L],[I,F,L,N],[I,L],[I,L,N],[B,E],[E]]),ground([G,H,C,D,K,M]);mshare([[B,E],[E]]),ground([G,H,I,J,C,D,F,K,L,M,N]))).
np_head0(B,C,def+proper,D,E,F,x(nogap,nonterminal,gen_marker,G)) :-
    true((mshare([[B],[C],[E],[F],[G]]),ground([D]),linear(B),linear(C),linear(E),linear(G);mshare([[B],[C],[E],[G]]),ground([D,F]),linear(B),linear(C),linear(E),linear(G))),
    poss_pron(B,C,D,E,F,G),
    true((mshare([[B],[C]]),ground([D,E,F,G]);mshare([[B],[C],[F],[F,G]]),ground([D,E]))).
np_head0(np_head(B,[],C),3+sin,indef+common,D,E,F,G) :-
    true((mshare([[E],[F],[G],[B],[C]]),ground([D]),linear(E),linear(G),linear(B),linear(C);mshare([[E],[G],[B],[C]]),ground([D,F]),linear(E),linear(G),linear(B),linear(C))),
    quantifier_pron(B,C,D,E,F,G),
    true((mshare([[F],[F,G]]),ground([D,E,B,C]);ground([D,E,F,G,B,C]))).

:- true pred np_compls(_A,B,C,_B,D,E,F,H,G,J)
   : ( mshare([[_B],[E],[H],[J]]),
       ground([_A,B,C,D,F,G]), linear(_B), linear(E), linear(H), linear(J) )
   => ( mshare([[_B],[_B,J],[J]]),
        ground([_A,B,C,D,E,F,H,G]) ).

:- true pred np_compls(_A,B,C,_B,D,E,F,H,G,J)
   : ( mshare([[B],[_B],[E],[H],[J]]),
       ground([_A,C,D,F,G]), linear(_B), linear(E), linear(H), linear(J) )
   => ( mshare([[B],[B,_B],[B,_B,J],[B,J],[_B],[_B,J],[J]]),
        ground([_A,C,D,E,F,H,G]) ).

:- true pred np_compls(_A,B,C,_B,D,E,F,H,G,J)
   : ( mshare([[_A],[_A,B],[_A,B,G],[_A,G],[B],[B,G],[_B],[E],[H],[G],[J]]),
       ground([C,D,F]), linear(_B), linear(E), linear(H), linear(J) )
   => ( mshare([[B],[B,_B],[B,_B,G],[B,_B,G,J],[B,_B,J],[B,G],[B,G,J],[B,J],[_B],[_B,G],[_B,G,J],[_B,J],[G],[G,J],[J]]),
        ground([_A,C,D,E,F,H]) ).

:- true pred np_compls(_A,B,C,_B,D,E,F,H,G,J)
   : ( mshare([[_A],[_A,G],[_B],[E],[H],[G],[J]]),
       ground([B,C,D,F]), linear(_B), linear(E), linear(H), linear(J) )
   => ( mshare([[_B],[_B,G],[_B,G,J],[_B,J],[G],[G,J],[J]]),
        ground([_A,B,C,D,E,F,H]) ).

np_compls(proper,B,C,[],D,E,F,F,G,G) :-
    true((mshare([[B],[B,G],[E],[G]]),ground([C,D,F]),linear(E);mshare([[B],[E]]),ground([C,D,F,G]),linear(E);mshare([[E]]),ground([B,C,D,F,G]),linear(E);mshare([[E],[G]]),ground([B,C,D,F]),linear(E))),
    empty(E),
    true((mshare([[B]]),ground([C,D,E,F,G]);mshare([[B],[B,G],[G]]),ground([C,D,E,F]);mshare([[G]]),ground([B,C,D,E,F]);ground([B,C,D,E,F,G]))).
np_compls(common,B,C,D,E,F,G,H,I,J) :-
    true((mshare([[B],[B,I],[D],[F],[H],[I],[J],[K],[L],[M],[N],[O],[P]]),ground([C,E,G]),linear(D),linear(F),linear(H),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P);mshare([[B],[D],[F],[H],[J],[K],[L],[M],[N],[O],[P]]),ground([C,E,G,I]),linear(D),linear(F),linear(H),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P);mshare([[D],[F],[H],[I],[J],[K],[L],[M],[N],[O],[P]]),ground([B,C,E,G]),linear(D),linear(F),linear(H),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P);mshare([[D],[F],[H],[J],[K],[L],[M],[N],[O],[P]]),ground([B,C,E,G,I]),linear(D),linear(F),linear(H),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P))),
    np_all(K),
    true((mshare([[B],[B,I],[D],[F],[H],[I],[J],[L],[M],[N],[O],[P]]),ground([C,E,G,K]),linear(D),linear(F),linear(H),linear(J),linear(L),linear(M),linear(N),linear(O),linear(P);mshare([[B],[D],[F],[H],[J],[L],[M],[N],[O],[P]]),ground([C,E,G,I,K]),linear(D),linear(F),linear(H),linear(J),linear(L),linear(M),linear(N),linear(O),linear(P);mshare([[D],[F],[H],[I],[J],[L],[M],[N],[O],[P]]),ground([B,C,E,G,K]),linear(D),linear(F),linear(H),linear(J),linear(L),linear(M),linear(N),linear(O),linear(P);mshare([[D],[F],[H],[J],[L],[M],[N],[O],[P]]),ground([B,C,E,G,I,K]),linear(D),linear(F),linear(H),linear(J),linear(L),linear(M),linear(N),linear(O),linear(P))),
    np_mods(B,C,L,D,E,M,K,N,G,O,I,P),
    true((mshare([[B],[B,D],[B,D,I],[B,D,I,P],[B,D,P],[B,I],[B,I,P],[B,P],[D],[D,I],[D,I,P],[D,L],[D,P],[F],[H],[I],[I,P],[J],[P]]),ground([C,E,G,K,M,N,O]),linear(F),linear(H),linear(J),linear(L);mshare([[B],[B,D],[B,D,P],[B,P],[D],[D,L],[D,P],[F],[H],[J],[P]]),ground([C,E,G,I,K,M,N,O]),linear(F),linear(H),linear(J),linear(L);mshare([[D],[D,I],[D,I,P],[D,L],[D,P],[F],[H],[I],[I,P],[J],[P]]),ground([B,C,E,G,K,M,N,O]),linear(F),linear(H),linear(J),linear(L);mshare([[D],[D,L],[D,P],[F],[H],[J],[P]]),ground([B,C,E,G,I,K,M,N,O]),linear(F),linear(H),linear(J),linear(L))),
    relative(B,L,M,N,F,O,H,P,J),
    true((mshare([[B],[B,D],[B,D,I],[B,D,I,J],[B,D,I,J,L],[B,D,I,J,L,P],[B,D,I,J,P],[B,D,I,L],[B,D,I,L,P],[B,D,I,P],[B,D,J],[B,D,J,L],[B,D,J,L,P],[B,D,J,P],[B,D,L],[B,D,L,P],[B,D,P],[B,I],[B,I,J],[B,I,J,P],[B,I,P],[B,J],[B,J,P],[B,P],[D],[D,I],[D,I,J,L,P],[D,I,J,P],[D,I,L,P],[D,I,P],[D,J,L],[D,J,L,P],[D,J,P],[D,L],[D,L,P],[D,P],[I],[I,J,P],[I,P],[J],[J,P],[P]]),ground([C,E,F,G,H,K,M,N,O]);mshare([[B],[B,D],[B,D,J],[B,D,J,L],[B,D,J,L,P],[B,D,J,P],[B,D,L],[B,D,L,P],[B,D,P],[B,J],[B,J,P],[B,P],[D],[D,J,L],[D,J,L,P],[D,J,P],[D,L],[D,L,P],[D,P],[J],[J,P],[P]]),ground([C,E,F,G,H,I,K,M,N,O]);mshare([[D],[D,I],[D,I,J,L,P],[D,I,J,P],[D,I,L,P],[D,I,P],[D,J,L],[D,J,L,P],[D,J,P],[D,L],[D,L,P],[D,P],[I],[I,J,P],[I,P],[J],[J,P],[P]]),ground([B,C,E,F,G,H,K,M,N,O]);mshare([[D],[D,J,L],[D,J,L,P],[D,J,P],[D,L],[D,L,P],[D,P],[J],[J,P],[P]]),ground([B,C,E,F,G,H,I,K,M,N,O]))).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (_A=E),
       mshare([[B],[B,C],[B,C,D],[B,C,D,G],[B,C,D,G,M],[B,C,D,M],[B,C,G],[B,C,G,M],[B,C,M],[B,D],[B,D,G],[B,D,G,M],[B,D,M],[B,G],[B,G,M],[B,M],[C],[C,D],[C,D,G],[C,D,G,M],[C,D,M],[C,G],[C,G,M],[C,M],[D],[D,G],[D,G,M],[D,M],[_A],[F],[G],[G,M],[H],[I],[J],[L],[M],[N]]),
       ground([K]), linear(_A), linear(F), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,D,F,G,H],[B,C,D,F,G,H,J,M],[B,C,D,F,G,H,J,M,N],[B,C,D,F,G,H,M,N],[B,C,D,F,G,J],[B,C,D,F,G,J,M],[B,C,D,F,G,J,M,N],[B,C,D,F,H,J,M],[B,C,D,F,H,J,M,N],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N],[B,C,D,G,H,J,M],[B,C,D,G,H,J,M,N],[B,C,D,G,J],[B,C,D,G,J,M],[B,C,D,G,J,M,N],[B,C,D,H,J,M],[B,C,D,H,J,M,N],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N],[B,C,F,G],[B,C,F,G,H,J,M],[B,C,F,G,H,J,M,N],[B,C,F,G,J],[B,C,F,G,J,M],[B,C,F,G,J,M,N],[B,C,F,G,M,N],[B,C,F,H,J,M],[B,C,F,H,J,M,N],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N],[B,C,G,H,J,M],[B,C,G,H,J,M,N],[B,C,G,J],[B,C,G,J,M],[B,C,G,J,M,N],[B,C,H,J,M],[B,C,H,J,M,N],[B,C,J],[B,C,J,M],[B,C,J,M,N],[B,D,F,G,H,J,M],[B,D,F,G,H,J,M,N],[B,D,F,G,J],[B,D,F,G,J,M],[B,D,F,G,J,M,N],[B,D,F,H],[B,D,F,H,J,M],[B,D,F,H,J,M,N],[B,D,F,H,M,N],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N],[B,D,G,H,J,M],[B,D,G,H,J,M,N],[B,D,G,J],[B,D,G,J,M],[B,D,G,J,M,N],[B,D,H,J,M],[B,D,H,J,M,N],[B,D,J],[B,D,J,M],[B,D,J,M,N],[B,F],[B,F,G,H,J,M],[B,F,G,H,J,M,N],[B,F,G,J],[B,F,G,J,M],[B,F,G,J,M,N],[B,F,H,J,M],[B,F,H,J,M,N],[B,F,J],[B,F,J,M],[B,F,J,M,N],[B,F,M,N],[B,G,H,J,M],[B,G,H,J,M,N],[B,G,J],[B,G,J,M],[B,G,J,M,N],[B,H,J,M],[B,H,J,M,N],[B,J],[B,J,M],[B,J,M,N],[C,D,F,G,H,J,M],[C,D,F,G,H,J,M,N],[C,D,F,G,J],[C,D,F,G,J,M],[C,D,F,G,J,M,N],[C,D,F,H,J,M],[C,D,F,H,J,M,N],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N],[C,D,G,H],[C,D,G,H,J,M],[C,D,G,H,J,M,N],[C,D,G,H,M,N],[C,D,G,J],[C,D,G,J,M],[C,D,G,J,M,N],[C,D,H,J,M],[C,D,H,J,M,N],[C,D,J],[C,D,J,M],[C,D,J,M,N],[C,F,G,H,J,M],[C,F,G,H,J,M,N],[C,F,G,J],[C,F,G,J,M],[C,F,G,J,M,N],[C,F,H,J,M],[C,F,H,J,M,N],[C,F,J],[C,F,J,M],[C,F,J,M,N],[C,G],[C,G,H,J,M],[C,G,H,J,M,N],[C,G,J],[C,G,J,M],[C,G,J,M,N],[C,G,M,N],[C,H,J,M],[C,H,J,M,N],[C,J],[C,J,M],[C,J,M,N],[D],[D,F,G],[D,F,G,H,J,M],[D,F,G,H,J,M,N],[D,F,G,H,M],[D,F,G,H,M,N],[D,F,G,J],[D,F,G,J,M],[D,F,G,J,M,N],[D,F,G,M],[D,F,G,M,N],[D,F,H,J,M],[D,F,H,J,M,N],[D,F,H,M],[D,F,H,M,N],[D,F,J,M],[D,F,J,M,N],[D,F,M],[D,F,M,N],[D,G],[D,G,H,J,M],[D,G,H,J,M,N],[D,G,H,M],[D,G,H,M,N],[D,G,J],[D,G,J,M],[D,G,J,M,N],[D,G,M],[D,G,M,N],[D,H],[D,H,J,M],[D,H,J,M,N],[D,H,M],[D,H,M,N],[D,J,M],[D,J,M,N],[D,M],[D,M,N],[_A,I,J],[F],[F,G],[F,G,H,J,M],[F,G,H,J,M,N],[F,G,H,M],[F,G,H,M,N],[F,G,J],[F,G,J,M],[F,G,J,M,N],[F,G,M],[F,G,M,N],[F,H,J,M],[F,H,J,M,N],[F,H,M],[F,H,M,N],[F,J],[F,J,M],[F,J,M,N],[F,M],[F,M,N],[G],[G,H,J,M],[G,H,J,M,N],[G,H,M],[G,H,M,N],[G,J],[G,J,M],[G,J,M,N],[G,M],[G,M,N],[H,J,M],[H,J,M,N],[H,M],[H,M,N],[I,J],[J],[J,M],[J,M,N],[M],[M,N]]),
        ground([K,L]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (E=[pp(poss,np(_B,_C,_D))|_A]),
       mshare([[B],[B,C],[B,C,D],[B,C,D,G],[B,C,D,G,M],[B,C,D,G,M,_B],[B,C,D,G,M,_B,_C],[B,C,D,G,M,_C],[B,C,D,G,_B],[B,C,D,G,_B,_C],[B,C,D,G,_C],[B,C,D,M],[B,C,D,M,_B],[B,C,D,M,_B,_C],[B,C,D,M,_C],[B,C,D,_B],[B,C,D,_B,_C],[B,C,D,_C],[B,C,G],[B,C,G,M],[B,C,G,M,_B],[B,C,G,M,_B,_C],[B,C,G,M,_C],[B,C,G,_B],[B,C,G,_B,_C],[B,C,G,_C],[B,C,M],[B,C,M,_B],[B,C,M,_B,_C],[B,C,M,_C],[B,C,_B],[B,C,_B,_C],[B,C,_C],[B,D],[B,D,G],[B,D,G,M],[B,D,G,M,_B],[B,D,G,M,_B,_C],[B,D,G,M,_C],[B,D,G,_B],[B,D,G,_B,_C],[B,D,G,_C],[B,D,M],[B,D,M,_B],[B,D,M,_B,_C],[B,D,M,_C],[B,D,_B],[B,D,_B,_C],[B,D,_C],[B,G],[B,G,M],[B,G,M,_B],[B,G,M,_B,_C],[B,G,M,_C],[B,G,_B],[B,G,_B,_C],[B,G,_C],[B,M],[B,M,_B],[B,M,_B,_C],[B,M,_C],[B,_B],[B,_B,_C],[B,_C],[C],[C,D],[C,D,G],[C,D,G,M],[C,D,G,M,_B],[C,D,G,M,_B,_C],[C,D,G,M,_C],[C,D,G,_B],[C,D,G,_B,_C],[C,D,G,_C],[C,D,M],[C,D,M,_B],[C,D,M,_B,_C],[C,D,M,_C],[C,D,_B],[C,D,_B,_C],[C,D,_C],[C,G],[C,G,M],[C,G,M,_B],[C,G,M,_B,_C],[C,G,M,_C],[C,G,_B],[C,G,_B,_C],[C,G,_C],[C,M],[C,M,_B],[C,M,_B,_C],[C,M,_C],[C,_B],[C,_B,_C],[C,_C],[D],[D,G],[D,G,M],[D,G,M,_B],[D,G,M,_B,_C],[D,G,M,_C],[D,G,_B],[D,G,_B,_C],[D,G,_C],[D,M],[D,M,_B],[D,M,_B,_C],[D,M,_C],[D,_B],[D,_B,_C],[D,_C],[_A],[F],[G],[G,M],[G,M,_B],[G,M,_B,_C],[G,M,_C],[G,_B],[G,_B,_C],[G,_C],[H],[I],[J],[L],[M],[M,_B],[M,_B,_C],[M,_C],[N],[_B],[_B,_C],[_C]]),
       ground([K,_D]), linear(_A), linear(F), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,D,F,G,H],[B,C,D,F,G,H,J,M],[B,C,D,F,G,H,J,M,N],[B,C,D,F,G,H,J,M,N,_B],[B,C,D,F,G,H,J,M,N,_B,_C],[B,C,D,F,G,H,J,M,N,_C],[B,C,D,F,G,H,J,M,_B],[B,C,D,F,G,H,J,M,_B,_C],[B,C,D,F,G,H,J,M,_C],[B,C,D,F,G,H,J,_B],[B,C,D,F,G,H,J,_B,_C],[B,C,D,F,G,H,J,_C],[B,C,D,F,G,H,M,N],[B,C,D,F,G,J],[B,C,D,F,G,J,M],[B,C,D,F,G,J,M,N],[B,C,D,F,G,J,M,N,_B],[B,C,D,F,G,J,M,N,_B,_C],[B,C,D,F,G,J,M,N,_C],[B,C,D,F,G,J,M,_B],[B,C,D,F,G,J,M,_B,_C],[B,C,D,F,G,J,M,_C],[B,C,D,F,G,J,_B],[B,C,D,F,G,J,_B,_C],[B,C,D,F,G,J,_C],[B,C,D,F,H,J,M],[B,C,D,F,H,J,M,N],[B,C,D,F,H,J,M,N,_B],[B,C,D,F,H,J,M,N,_B,_C],[B,C,D,F,H,J,M,N,_C],[B,C,D,F,H,J,M,_B],[B,C,D,F,H,J,M,_B,_C],[B,C,D,F,H,J,M,_C],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N],[B,C,D,F,J,M,N,_B],[B,C,D,F,J,M,N,_B,_C],[B,C,D,F,J,M,N,_C],[B,C,D,F,J,M,_B],[B,C,D,F,J,M,_B,_C],[B,C,D,F,J,M,_C],[B,C,D,F,J,_B],[B,C,D,F,J,_B,_C],[B,C,D,F,J,_C],[B,C,D,G,H,J,M],[B,C,D,G,H,J,M,N],[B,C,D,G,H,J,M,N,_B],[B,C,D,G,H,J,M,N,_B,_C],[B,C,D,G,H,J,M,N,_C],[B,C,D,G,H,J,M,_B],[B,C,D,G,H,J,M,_B,_C],[B,C,D,G,H,J,M,_C],[B,C,D,G,J],[B,C,D,G,J,M],[B,C,D,G,J,M,N],[B,C,D,G,J,M,N,_B],[B,C,D,G,J,M,N,_B,_C],[B,C,D,G,J,M,N,_C],[B,C,D,G,J,M,_B],[B,C,D,G,J,M,_B,_C],[B,C,D,G,J,M,_C],[B,C,D,G,J,_B],[B,C,D,G,J,_B,_C],[B,C,D,G,J,_C],[B,C,D,H,J,M],[B,C,D,H,J,M,N],[B,C,D,H,J,M,N,_B],[B,C,D,H,J,M,N,_B,_C],[B,C,D,H,J,M,N,_C],[B,C,D,H,J,M,_B],[B,C,D,H,J,M,_B,_C],[B,C,D,H,J,M,_C],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N],[B,C,D,J,M,N,_B],[B,C,D,J,M,N,_B,_C],[B,C,D,J,M,N,_C],[B,C,D,J,M,_B],[B,C,D,J,M,_B,_C],[B,C,D,J,M,_C],[B,C,D,J,_B],[B,C,D,J,_B,_C],[B,C,D,J,_C],[B,C,F,G],[B,C,F,G,H,J,M],[B,C,F,G,H,J,M,N],[B,C,F,G,H,J,M,N,_B],[B,C,F,G,H,J,M,N,_B,_C],[B,C,F,G,H,J,M,N,_C],[B,C,F,G,H,J,M,_B],[B,C,F,G,H,J,M,_B,_C],[B,C,F,G,H,J,M,_C],[B,C,F,G,J],[B,C,F,G,J,M],[B,C,F,G,J,M,N],[B,C,F,G,J,M,N,_B],[B,C,F,G,J,M,N,_B,_C],[B,C,F,G,J,M,N,_C],[B,C,F,G,J,M,_B],[B,C,F,G,J,M,_B,_C],[B,C,F,G,J,M,_C],[B,C,F,G,J,_B],[B,C,F,G,J,_B,_C],[B,C,F,G,J,_C],[B,C,F,G,M,N],[B,C,F,H,J,M],[B,C,F,H,J,M,N],[B,C,F,H,J,M,N,_B],[B,C,F,H,J,M,N,_B,_C],[B,C,F,H,J,M,N,_C],[B,C,F,H,J,M,_B],[B,C,F,H,J,M,_B,_C],[B,C,F,H,J,M,_C],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N],[B,C,F,J,M,N,_B],[B,C,F,J,M,N,_B,_C],[B,C,F,J,M,N,_C],[B,C,F,J,M,_B],[B,C,F,J,M,_B,_C],[B,C,F,J,M,_C],[B,C,F,J,_B],[B,C,F,J,_B,_C],[B,C,F,J,_C],[B,C,G,H,J,M],[B,C,G,H,J,M,N],[B,C,G,H,J,M,N,_B],[B,C,G,H,J,M,N,_B,_C],[B,C,G,H,J,M,N,_C],[B,C,G,H,J,M,_B],[B,C,G,H,J,M,_B,_C],[B,C,G,H,J,M,_C],[B,C,G,J],[B,C,G,J,M],[B,C,G,J,M,N],[B,C,G,J,M,N,_B],[B,C,G,J,M,N,_B,_C],[B,C,G,J,M,N,_C],[B,C,G,J,M,_B],[B,C,G,J,M,_B,_C],[B,C,G,J,M,_C],[B,C,G,J,_B],[B,C,G,J,_B,_C],[B,C,G,J,_C],[B,C,H,J,M],[B,C,H,J,M,N],[B,C,H,J,M,N,_B],[B,C,H,J,M,N,_B,_C],[B,C,H,J,M,N,_C],[B,C,H,J,M,_B],[B,C,H,J,M,_B,_C],[B,C,H,J,M,_C],[B,C,J],[B,C,J,M],[B,C,J,M,N],[B,C,J,M,N,_B],[B,C,J,M,N,_B,_C],[B,C,J,M,N,_C],[B,C,J,M,_B],[B,C,J,M,_B,_C],[B,C,J,M,_C],[B,C,J,_B],[B,C,J,_B,_C],[B,C,J,_C],[B,D,F,G,H,J,M],[B,D,F,G,H,J,M,N],[B,D,F,G,H,J,M,N,_B],[B,D,F,G,H,J,M,N,_B,_C],[B,D,F,G,H,J,M,N,_C],[B,D,F,G,H,J,M,_B],[B,D,F,G,H,J,M,_B,_C],[B,D,F,G,H,J,M,_C],[B,D,F,G,J],[B,D,F,G,J,M],[B,D,F,G,J,M,N],[B,D,F,G,J,M,N,_B],[B,D,F,G,J,M,N,_B,_C],[B,D,F,G,J,M,N,_C],[B,D,F,G,J,M,_B],[B,D,F,G,J,M,_B,_C],[B,D,F,G,J,M,_C],[B,D,F,G,J,_B],[B,D,F,G,J,_B,_C],[B,D,F,G,J,_C],[B,D,F,H],[B,D,F,H,J,M],[B,D,F,H,J,M,N],[B,D,F,H,J,M,N,_B],[B,D,F,H,J,M,N,_B,_C],[B,D,F,H,J,M,N,_C],[B,D,F,H,J,M,_B],[B,D,F,H,J,M,_B,_C],[B,D,F,H,J,M,_C],[B,D,F,H,J,_B],[B,D,F,H,J,_B,_C],[B,D,F,H,J,_C],[B,D,F,H,M,N],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N],[B,D,F,J,M,N,_B],[B,D,F,J,M,N,_B,_C],[B,D,F,J,M,N,_C],[B,D,F,J,M,_B],[B,D,F,J,M,_B,_C],[B,D,F,J,M,_C],[B,D,F,J,_B],[B,D,F,J,_B,_C],[B,D,F,J,_C],[B,D,G,H,J,M],[B,D,G,H,J,M,N],[B,D,G,H,J,M,N,_B],[B,D,G,H,J,M,N,_B,_C],[B,D,G,H,J,M,N,_C],[B,D,G,H,J,M,_B],[B,D,G,H,J,M,_B,_C],[B,D,G,H,J,M,_C],[B,D,G,J],[B,D,G,J,M],[B,D,G,J,M,N],[B,D,G,J,M,N,_B],[B,D,G,J,M,N,_B,_C],[B,D,G,J,M,N,_C],[B,D,G,J,M,_B],[B,D,G,J,M,_B,_C],[B,D,G,J,M,_C],[B,D,G,J,_B],[B,D,G,J,_B,_C],[B,D,G,J,_C],[B,D,H,J,M],[B,D,H,J,M,N],[B,D,H,J,M,N,_B],[B,D,H,J,M,N,_B,_C],[B,D,H,J,M,N,_C],[B,D,H,J,M,_B],[B,D,H,J,M,_B,_C],[B,D,H,J,M,_C],[B,D,J],[B,D,J,M],[B,D,J,M,N],[B,D,J,M,N,_B],[B,D,J,M,N,_B,_C],[B,D,J,M,N,_C],[B,D,J,M,_B],[B,D,J,M,_B,_C],[B,D,J,M,_C],[B,D,J,_B],[B,D,J,_B,_C],[B,D,J,_C],[B,F],[B,F,G,H,J,M],[B,F,G,H,J,M,N],[B,F,G,H,J,M,N,_B],[B,F,G,H,J,M,N,_B,_C],[B,F,G,H,J,M,N,_C],[B,F,G,H,J,M,_B],[B,F,G,H,J,M,_B,_C],[B,F,G,H,J,M,_C],[B,F,G,J],[B,F,G,J,M],[B,F,G,J,M,N],[B,F,G,J,M,N,_B],[B,F,G,J,M,N,_B,_C],[B,F,G,J,M,N,_C],[B,F,G,J,M,_B],[B,F,G,J,M,_B,_C],[B,F,G,J,M,_C],[B,F,G,J,_B],[B,F,G,J,_B,_C],[B,F,G,J,_C],[B,F,H,J,M],[B,F,H,J,M,N],[B,F,H,J,M,N,_B],[B,F,H,J,M,N,_B,_C],[B,F,H,J,M,N,_C],[B,F,H,J,M,_B],[B,F,H,J,M,_B,_C],[B,F,H,J,M,_C],[B,F,J],[B,F,J,M],[B,F,J,M,N],[B,F,J,M,N,_B],[B,F,J,M,N,_B,_C],[B,F,J,M,N,_C],[B,F,J,M,_B],[B,F,J,M,_B,_C],[B,F,J,M,_C],[B,F,J,_B],[B,F,J,_B,_C],[B,F,J,_C],[B,F,M,N],[B,G,H,J,M],[B,G,H,J,M,N],[B,G,H,J,M,N,_B],[B,G,H,J,M,N,_B,_C],[B,G,H,J,M,N,_C],[B,G,H,J,M,_B],[B,G,H,J,M,_B,_C],[B,G,H,J,M,_C],[B,G,J],[B,G,J,M],[B,G,J,M,N],[B,G,J,M,N,_B],[B,G,J,M,N,_B,_C],[B,G,J,M,N,_C],[B,G,J,M,_B],[B,G,J,M,_B,_C],[B,G,J,M,_C],[B,G,J,_B],[B,G,J,_B,_C],[B,G,J,_C],[B,H,J,M],[B,H,J,M,N],[B,H,J,M,N,_B],[B,H,J,M,N,_B,_C],[B,H,J,M,N,_C],[B,H,J,M,_B],[B,H,J,M,_B,_C],[B,H,J,M,_C],[B,J],[B,J,M],[B,J,M,N],[B,J,M,N,_B],[B,J,M,N,_B,_C],[B,J,M,N,_C],[B,J,M,_B],[B,J,M,_B,_C],[B,J,M,_C],[B,J,_B],[B,J,_B,_C],[B,J,_C],[C,D,F,G,H,J,M],[C,D,F,G,H,J,M,N],[C,D,F,G,H,J,M,N,_B],[C,D,F,G,H,J,M,N,_B,_C],[C,D,F,G,H,J,M,N,_C],[C,D,F,G,H,J,M,_B],[C,D,F,G,H,J,M,_B,_C],[C,D,F,G,H,J,M,_C],[C,D,F,G,J],[C,D,F,G,J,M],[C,D,F,G,J,M,N],[C,D,F,G,J,M,N,_B],[C,D,F,G,J,M,N,_B,_C],[C,D,F,G,J,M,N,_C],[C,D,F,G,J,M,_B],[C,D,F,G,J,M,_B,_C],[C,D,F,G,J,M,_C],[C,D,F,G,J,_B],[C,D,F,G,J,_B,_C],[C,D,F,G,J,_C],[C,D,F,H,J,M],[C,D,F,H,J,M,N],[C,D,F,H,J,M,N,_B],[C,D,F,H,J,M,N,_B,_C],[C,D,F,H,J,M,N,_C],[C,D,F,H,J,M,_B],[C,D,F,H,J,M,_B,_C],[C,D,F,H,J,M,_C],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N],[C,D,F,J,M,N,_B],[C,D,F,J,M,N,_B,_C],[C,D,F,J,M,N,_C],[C,D,F,J,M,_B],[C,D,F,J,M,_B,_C],[C,D,F,J,M,_C],[C,D,F,J,_B],[C,D,F,J,_B,_C],[C,D,F,J,_C],[C,D,G,H],[C,D,G,H,J,M],[C,D,G,H,J,M,N],[C,D,G,H,J,M,N,_B],[C,D,G,H,J,M,N,_B,_C],[C,D,G,H,J,M,N,_C],[C,D,G,H,J,M,_B],[C,D,G,H,J,M,_B,_C],[C,D,G,H,J,M,_C],[C,D,G,H,J,_B],[C,D,G,H,J,_B,_C],[C,D,G,H,J,_C],[C,D,G,H,M,N],[C,D,G,J],[C,D,G,J,M],[C,D,G,J,M,N],[C,D,G,J,M,N,_B],[C,D,G,J,M,N,_B,_C],[C,D,G,J,M,N,_C],[C,D,G,J,M,_B],[C,D,G,J,M,_B,_C],[C,D,G,J,M,_C],[C,D,G,J,_B],[C,D,G,J,_B,_C],[C,D,G,J,_C],[C,D,H,J,M],[C,D,H,J,M,N],[C,D,H,J,M,N,_B],[C,D,H,J,M,N,_B,_C],[C,D,H,J,M,N,_C],[C,D,H,J,M,_B],[C,D,H,J,M,_B,_C],[C,D,H,J,M,_C],[C,D,J],[C,D,J,M],[C,D,J,M,N],[C,D,J,M,N,_B],[C,D,J,M,N,_B,_C],[C,D,J,M,N,_C],[C,D,J,M,_B],[C,D,J,M,_B,_C],[C,D,J,M,_C],[C,D,J,_B],[C,D,J,_B,_C],[C,D,J,_C],[C,F,G,H,J,M],[C,F,G,H,J,M,N],[C,F,G,H,J,M,N,_B],[C,F,G,H,J,M,N,_B,_C],[C,F,G,H,J,M,N,_C],[C,F,G,H,J,M,_B],[C,F,G,H,J,M,_B,_C],[C,F,G,H,J,M,_C],[C,F,G,J],[C,F,G,J,M],[C,F,G,J,M,N],[C,F,G,J,M,N,_B],[C,F,G,J,M,N,_B,_C],[C,F,G,J,M,N,_C],[C,F,G,J,M,_B],[C,F,G,J,M,_B,_C],[C,F,G,J,M,_C],[C,F,G,J,_B],[C,F,G,J,_B,_C],[C,F,G,J,_C],[C,F,H,J,M],[C,F,H,J,M,N],[C,F,H,J,M,N,_B],[C,F,H,J,M,N,_B,_C],[C,F,H,J,M,N,_C],[C,F,H,J,M,_B],[C,F,H,J,M,_B,_C],[C,F,H,J,M,_C],[C,F,J],[C,F,J,M],[C,F,J,M,N],[C,F,J,M,N,_B],[C,F,J,M,N,_B,_C],[C,F,J,M,N,_C],[C,F,J,M,_B],[C,F,J,M,_B,_C],[C,F,J,M,_C],[C,F,J,_B],[C,F,J,_B,_C],[C,F,J,_C],[C,G],[C,G,H,J,M],[C,G,H,J,M,N],[C,G,H,J,M,N,_B],[C,G,H,J,M,N,_B,_C],[C,G,H,J,M,N,_C],[C,G,H,J,M,_B],[C,G,H,J,M,_B,_C],[C,G,H,J,M,_C],[C,G,J],[C,G,J,M],[C,G,J,M,N],[C,G,J,M,N,_B],[C,G,J,M,N,_B,_C],[C,G,J,M,N,_C],[C,G,J,M,_B],[C,G,J,M,_B,_C],[C,G,J,M,_C],[C,G,J,_B],[C,G,J,_B,_C],[C,G,J,_C],[C,G,M,N],[C,H,J,M],[C,H,J,M,N],[C,H,J,M,N,_B],[C,H,J,M,N,_B,_C],[C,H,J,M,N,_C],[C,H,J,M,_B],[C,H,J,M,_B,_C],[C,H,J,M,_C],[C,J],[C,J,M],[C,J,M,N],[C,J,M,N,_B],[C,J,M,N,_B,_C],[C,J,M,N,_C],[C,J,M,_B],[C,J,M,_B,_C],[C,J,M,_C],[C,J,_B],[C,J,_B,_C],[C,J,_C],[D],[D,F,G],[D,F,G,H,J,M],[D,F,G,H,J,M,N],[D,F,G,H,J,M,N,_B],[D,F,G,H,J,M,N,_B,_C],[D,F,G,H,J,M,N,_C],[D,F,G,H,J,M,_B],[D,F,G,H,J,M,_B,_C],[D,F,G,H,J,M,_C],[D,F,G,H,M],[D,F,G,H,M,N],[D,F,G,J],[D,F,G,J,M],[D,F,G,J,M,N],[D,F,G,J,M,N,_B],[D,F,G,J,M,N,_B,_C],[D,F,G,J,M,N,_C],[D,F,G,J,M,_B],[D,F,G,J,M,_B,_C],[D,F,G,J,M,_C],[D,F,G,J,_B],[D,F,G,J,_B,_C],[D,F,G,J,_C],[D,F,G,M],[D,F,G,M,N],[D,F,H,J,M],[D,F,H,J,M,N],[D,F,H,J,M,N,_B],[D,F,H,J,M,N,_B,_C],[D,F,H,J,M,N,_C],[D,F,H,J,M,_B],[D,F,H,J,M,_B,_C],[D,F,H,J,M,_C],[D,F,H,M],[D,F,H,M,N],[D,F,J,M],[D,F,J,M,N],[D,F,J,M,N,_B],[D,F,J,M,N,_B,_C],[D,F,J,M,N,_C],[D,F,J,M,_B],[D,F,J,M,_B,_C],[D,F,J,M,_C],[D,F,J,_B],[D,F,J,_B,_C],[D,F,J,_C],[D,F,M],[D,F,M,N],[D,G],[D,G,H,J,M],[D,G,H,J,M,N],[D,G,H,J,M,N,_B],[D,G,H,J,M,N,_B,_C],[D,G,H,J,M,N,_C],[D,G,H,J,M,_B],[D,G,H,J,M,_B,_C],[D,G,H,J,M,_C],[D,G,H,M],[D,G,H,M,N],[D,G,J],[D,G,J,M],[D,G,J,M,N],[D,G,J,M,N,_B],[D,G,J,M,N,_B,_C],[D,G,J,M,N,_C],[D,G,J,M,_B],[D,G,J,M,_B,_C],[D,G,J,M,_C],[D,G,J,_B],[D,G,J,_B,_C],[D,G,J,_C],[D,G,M],[D,G,M,N],[D,H],[D,H,J,M],[D,H,J,M,N],[D,H,J,M,N,_B],[D,H,J,M,N,_B,_C],[D,H,J,M,N,_C],[D,H,J,M,_B],[D,H,J,M,_B,_C],[D,H,J,M,_C],[D,H,J,_B],[D,H,J,_B,_C],[D,H,J,_C],[D,H,M],[D,H,M,N],[D,J,M],[D,J,M,N],[D,J,M,N,_B],[D,J,M,N,_B,_C],[D,J,M,N,_C],[D,J,M,_B],[D,J,M,_B,_C],[D,J,M,_C],[D,J,_B],[D,J,_B,_C],[D,J,_C],[D,M],[D,M,N],[_A,I,J],[F],[F,G],[F,G,H,J,M],[F,G,H,J,M,N],[F,G,H,J,M,N,_B],[F,G,H,J,M,N,_B,_C],[F,G,H,J,M,N,_C],[F,G,H,J,M,_B],[F,G,H,J,M,_B,_C],[F,G,H,J,M,_C],[F,G,H,M],[F,G,H,M,N],[F,G,J],[F,G,J,M],[F,G,J,M,N],[F,G,J,M,N,_B],[F,G,J,M,N,_B,_C],[F,G,J,M,N,_C],[F,G,J,M,_B],[F,G,J,M,_B,_C],[F,G,J,M,_C],[F,G,J,_B],[F,G,J,_B,_C],[F,G,J,_C],[F,G,M],[F,G,M,N],[F,H,J,M],[F,H,J,M,N],[F,H,J,M,N,_B],[F,H,J,M,N,_B,_C],[F,H,J,M,N,_C],[F,H,J,M,_B],[F,H,J,M,_B,_C],[F,H,J,M,_C],[F,H,M],[F,H,M,N],[F,J],[F,J,M],[F,J,M,N],[F,J,M,N,_B],[F,J,M,N,_B,_C],[F,J,M,N,_C],[F,J,M,_B],[F,J,M,_B,_C],[F,J,M,_C],[F,J,_B],[F,J,_B,_C],[F,J,_C],[F,M],[F,M,N],[G],[G,H,J,M],[G,H,J,M,N],[G,H,J,M,N,_B],[G,H,J,M,N,_B,_C],[G,H,J,M,N,_C],[G,H,J,M,_B],[G,H,J,M,_B,_C],[G,H,J,M,_C],[G,H,M],[G,H,M,N],[G,J],[G,J,M],[G,J,M,N],[G,J,M,N,_B],[G,J,M,N,_B,_C],[G,J,M,N,_C],[G,J,M,_B],[G,J,M,_B,_C],[G,J,M,_C],[G,J,_B],[G,J,_B,_C],[G,J,_C],[G,M],[G,M,N],[H,J,M],[H,J,M,N],[H,J,M,N,_B],[H,J,M,N,_B,_C],[H,J,M,N,_C],[H,J,M,_B],[H,J,M,_B,_C],[H,J,M,_C],[H,M],[H,M,N],[I,J],[J],[J,M],[J,M,N],[J,M,N,_B],[J,M,N,_B,_C],[J,M,N,_C],[J,M,_B],[J,M,_B,_C],[J,M,_C],[J,_B],[J,_B,_C],[J,_C],[M],[M,N]]),
        ground([K,L,_D]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (E=[pp(poss,np(_B,_C,_D))|_A]),
       mshare([[B],[B,C],[B,C,D],[B,C,D,G],[B,C,D,G,M],[B,C,D,G,M,_B],[B,C,D,G,M,_B,_C],[B,C,D,G,M,_B,_C,_D],[B,C,D,G,M,_B,_D],[B,C,D,G,M,_C],[B,C,D,G,M,_C,_D],[B,C,D,G,M,_D],[B,C,D,G,_B],[B,C,D,G,_B,_C],[B,C,D,G,_B,_C,_D],[B,C,D,G,_B,_D],[B,C,D,G,_C],[B,C,D,G,_C,_D],[B,C,D,G,_D],[B,C,D,M],[B,C,D,M,_B],[B,C,D,M,_B,_C],[B,C,D,M,_B,_C,_D],[B,C,D,M,_B,_D],[B,C,D,M,_C],[B,C,D,M,_C,_D],[B,C,D,M,_D],[B,C,D,_B],[B,C,D,_B,_C],[B,C,D,_B,_C,_D],[B,C,D,_B,_D],[B,C,D,_C],[B,C,D,_C,_D],[B,C,D,_D],[B,C,G],[B,C,G,M],[B,C,G,M,_B],[B,C,G,M,_B,_C],[B,C,G,M,_B,_C,_D],[B,C,G,M,_B,_D],[B,C,G,M,_C],[B,C,G,M,_C,_D],[B,C,G,M,_D],[B,C,G,_B],[B,C,G,_B,_C],[B,C,G,_B,_C,_D],[B,C,G,_B,_D],[B,C,G,_C],[B,C,G,_C,_D],[B,C,G,_D],[B,C,M],[B,C,M,_B],[B,C,M,_B,_C],[B,C,M,_B,_C,_D],[B,C,M,_B,_D],[B,C,M,_C],[B,C,M,_C,_D],[B,C,M,_D],[B,C,_B],[B,C,_B,_C],[B,C,_B,_C,_D],[B,C,_B,_D],[B,C,_C],[B,C,_C,_D],[B,C,_D],[B,D],[B,D,G],[B,D,G,M],[B,D,G,M,_B],[B,D,G,M,_B,_C],[B,D,G,M,_B,_C,_D],[B,D,G,M,_B,_D],[B,D,G,M,_C],[B,D,G,M,_C,_D],[B,D,G,M,_D],[B,D,G,_B],[B,D,G,_B,_C],[B,D,G,_B,_C,_D],[B,D,G,_B,_D],[B,D,G,_C],[B,D,G,_C,_D],[B,D,G,_D],[B,D,M],[B,D,M,_B],[B,D,M,_B,_C],[B,D,M,_B,_C,_D],[B,D,M,_B,_D],[B,D,M,_C],[B,D,M,_C,_D],[B,D,M,_D],[B,D,_B],[B,D,_B,_C],[B,D,_B,_C,_D],[B,D,_B,_D],[B,D,_C],[B,D,_C,_D],[B,D,_D],[B,G],[B,G,M],[B,G,M,_B],[B,G,M,_B,_C],[B,G,M,_B,_C,_D],[B,G,M,_B,_D],[B,G,M,_C],[B,G,M,_C,_D],[B,G,M,_D],[B,G,_B],[B,G,_B,_C],[B,G,_B,_C,_D],[B,G,_B,_D],[B,G,_C],[B,G,_C,_D],[B,G,_D],[B,M],[B,M,_B],[B,M,_B,_C],[B,M,_B,_C,_D],[B,M,_B,_D],[B,M,_C],[B,M,_C,_D],[B,M,_D],[B,_B],[B,_B,_C],[B,_B,_C,_D],[B,_B,_D],[B,_C],[B,_C,_D],[B,_D],[C],[C,D],[C,D,G],[C,D,G,M],[C,D,G,M,_B],[C,D,G,M,_B,_C],[C,D,G,M,_B,_C,_D],[C,D,G,M,_B,_D],[C,D,G,M,_C],[C,D,G,M,_C,_D],[C,D,G,M,_D],[C,D,G,_B],[C,D,G,_B,_C],[C,D,G,_B,_C,_D],[C,D,G,_B,_D],[C,D,G,_C],[C,D,G,_C,_D],[C,D,G,_D],[C,D,M],[C,D,M,_B],[C,D,M,_B,_C],[C,D,M,_B,_C,_D],[C,D,M,_B,_D],[C,D,M,_C],[C,D,M,_C,_D],[C,D,M,_D],[C,D,_B],[C,D,_B,_C],[C,D,_B,_C,_D],[C,D,_B,_D],[C,D,_C],[C,D,_C,_D],[C,D,_D],[C,G],[C,G,M],[C,G,M,_B],[C,G,M,_B,_C],[C,G,M,_B,_C,_D],[C,G,M,_B,_D],[C,G,M,_C],[C,G,M,_C,_D],[C,G,M,_D],[C,G,_B],[C,G,_B,_C],[C,G,_B,_C,_D],[C,G,_B,_D],[C,G,_C],[C,G,_C,_D],[C,G,_D],[C,M],[C,M,_B],[C,M,_B,_C],[C,M,_B,_C,_D],[C,M,_B,_D],[C,M,_C],[C,M,_C,_D],[C,M,_D],[C,_B],[C,_B,_C],[C,_B,_C,_D],[C,_B,_D],[C,_C],[C,_C,_D],[C,_D],[D],[D,G],[D,G,M],[D,G,M,_B],[D,G,M,_B,_C],[D,G,M,_B,_C,_D],[D,G,M,_B,_D],[D,G,M,_C],[D,G,M,_C,_D],[D,G,M,_D],[D,G,_B],[D,G,_B,_C],[D,G,_B,_C,_D],[D,G,_B,_D],[D,G,_C],[D,G,_C,_D],[D,G,_D],[D,M],[D,M,_B],[D,M,_B,_C],[D,M,_B,_C,_D],[D,M,_B,_D],[D,M,_C],[D,M,_C,_D],[D,M,_D],[D,_B],[D,_B,_C],[D,_B,_C,_D],[D,_B,_D],[D,_C],[D,_C,_D],[D,_D],[_A],[F],[G],[G,M],[G,M,_B],[G,M,_B,_C],[G,M,_B,_C,_D],[G,M,_B,_D],[G,M,_C],[G,M,_C,_D],[G,M,_D],[G,_B],[G,_B,_C],[G,_B,_C,_D],[G,_B,_D],[G,_C],[G,_C,_D],[G,_D],[H],[I],[J],[L],[M],[M,_B],[M,_B,_C],[M,_B,_C,_D],[M,_B,_D],[M,_C],[M,_C,_D],[M,_D],[N],[_B],[_B,_C],[_B,_C,_D],[_B,_D],[_C],[_C,_D],[_D]]),
       ground([K]), linear(_A), linear(F), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,D,F,G,H],[B,C,D,F,G,H,J,M],[B,C,D,F,G,H,J,M,N],[B,C,D,F,G,H,J,M,N,_B],[B,C,D,F,G,H,J,M,N,_B,_C],[B,C,D,F,G,H,J,M,N,_B,_C,_D],[B,C,D,F,G,H,J,M,N,_B,_D],[B,C,D,F,G,H,J,M,N,_C],[B,C,D,F,G,H,J,M,N,_C,_D],[B,C,D,F,G,H,J,M,N,_D],[B,C,D,F,G,H,J,M,_B],[B,C,D,F,G,H,J,M,_B,_C],[B,C,D,F,G,H,J,M,_B,_C,_D],[B,C,D,F,G,H,J,M,_B,_D],[B,C,D,F,G,H,J,M,_C],[B,C,D,F,G,H,J,M,_C,_D],[B,C,D,F,G,H,J,M,_D],[B,C,D,F,G,H,J,_B],[B,C,D,F,G,H,J,_B,_C],[B,C,D,F,G,H,J,_B,_C,_D],[B,C,D,F,G,H,J,_B,_D],[B,C,D,F,G,H,J,_C],[B,C,D,F,G,H,J,_C,_D],[B,C,D,F,G,H,J,_D],[B,C,D,F,G,H,M,N],[B,C,D,F,G,J],[B,C,D,F,G,J,M],[B,C,D,F,G,J,M,N],[B,C,D,F,G,J,M,N,_B],[B,C,D,F,G,J,M,N,_B,_C],[B,C,D,F,G,J,M,N,_B,_C,_D],[B,C,D,F,G,J,M,N,_B,_D],[B,C,D,F,G,J,M,N,_C],[B,C,D,F,G,J,M,N,_C,_D],[B,C,D,F,G,J,M,N,_D],[B,C,D,F,G,J,M,_B],[B,C,D,F,G,J,M,_B,_C],[B,C,D,F,G,J,M,_B,_C,_D],[B,C,D,F,G,J,M,_B,_D],[B,C,D,F,G,J,M,_C],[B,C,D,F,G,J,M,_C,_D],[B,C,D,F,G,J,M,_D],[B,C,D,F,G,J,_B],[B,C,D,F,G,J,_B,_C],[B,C,D,F,G,J,_B,_C,_D],[B,C,D,F,G,J,_B,_D],[B,C,D,F,G,J,_C],[B,C,D,F,G,J,_C,_D],[B,C,D,F,G,J,_D],[B,C,D,F,H,J,M],[B,C,D,F,H,J,M,N],[B,C,D,F,H,J,M,N,_B],[B,C,D,F,H,J,M,N,_B,_C],[B,C,D,F,H,J,M,N,_B,_C,_D],[B,C,D,F,H,J,M,N,_B,_D],[B,C,D,F,H,J,M,N,_C],[B,C,D,F,H,J,M,N,_C,_D],[B,C,D,F,H,J,M,N,_D],[B,C,D,F,H,J,M,_B],[B,C,D,F,H,J,M,_B,_C],[B,C,D,F,H,J,M,_B,_C,_D],[B,C,D,F,H,J,M,_B,_D],[B,C,D,F,H,J,M,_C],[B,C,D,F,H,J,M,_C,_D],[B,C,D,F,H,J,M,_D],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N],[B,C,D,F,J,M,N,_B],[B,C,D,F,J,M,N,_B,_C],[B,C,D,F,J,M,N,_B,_C,_D],[B,C,D,F,J,M,N,_B,_D],[B,C,D,F,J,M,N,_C],[B,C,D,F,J,M,N,_C,_D],[B,C,D,F,J,M,N,_D],[B,C,D,F,J,M,_B],[B,C,D,F,J,M,_B,_C],[B,C,D,F,J,M,_B,_C,_D],[B,C,D,F,J,M,_B,_D],[B,C,D,F,J,M,_C],[B,C,D,F,J,M,_C,_D],[B,C,D,F,J,M,_D],[B,C,D,F,J,_B],[B,C,D,F,J,_B,_C],[B,C,D,F,J,_B,_C,_D],[B,C,D,F,J,_B,_D],[B,C,D,F,J,_C],[B,C,D,F,J,_C,_D],[B,C,D,F,J,_D],[B,C,D,G,H,J,M],[B,C,D,G,H,J,M,N],[B,C,D,G,H,J,M,N,_B],[B,C,D,G,H,J,M,N,_B,_C],[B,C,D,G,H,J,M,N,_B,_C,_D],[B,C,D,G,H,J,M,N,_B,_D],[B,C,D,G,H,J,M,N,_C],[B,C,D,G,H,J,M,N,_C,_D],[B,C,D,G,H,J,M,N,_D],[B,C,D,G,H,J,M,_B],[B,C,D,G,H,J,M,_B,_C],[B,C,D,G,H,J,M,_B,_C,_D],[B,C,D,G,H,J,M,_B,_D],[B,C,D,G,H,J,M,_C],[B,C,D,G,H,J,M,_C,_D],[B,C,D,G,H,J,M,_D],[B,C,D,G,J],[B,C,D,G,J,M],[B,C,D,G,J,M,N],[B,C,D,G,J,M,N,_B],[B,C,D,G,J,M,N,_B,_C],[B,C,D,G,J,M,N,_B,_C,_D],[B,C,D,G,J,M,N,_B,_D],[B,C,D,G,J,M,N,_C],[B,C,D,G,J,M,N,_C,_D],[B,C,D,G,J,M,N,_D],[B,C,D,G,J,M,_B],[B,C,D,G,J,M,_B,_C],[B,C,D,G,J,M,_B,_C,_D],[B,C,D,G,J,M,_B,_D],[B,C,D,G,J,M,_C],[B,C,D,G,J,M,_C,_D],[B,C,D,G,J,M,_D],[B,C,D,G,J,_B],[B,C,D,G,J,_B,_C],[B,C,D,G,J,_B,_C,_D],[B,C,D,G,J,_B,_D],[B,C,D,G,J,_C],[B,C,D,G,J,_C,_D],[B,C,D,G,J,_D],[B,C,D,H,J,M],[B,C,D,H,J,M,N],[B,C,D,H,J,M,N,_B],[B,C,D,H,J,M,N,_B,_C],[B,C,D,H,J,M,N,_B,_C,_D],[B,C,D,H,J,M,N,_B,_D],[B,C,D,H,J,M,N,_C],[B,C,D,H,J,M,N,_C,_D],[B,C,D,H,J,M,N,_D],[B,C,D,H,J,M,_B],[B,C,D,H,J,M,_B,_C],[B,C,D,H,J,M,_B,_C,_D],[B,C,D,H,J,M,_B,_D],[B,C,D,H,J,M,_C],[B,C,D,H,J,M,_C,_D],[B,C,D,H,J,M,_D],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N],[B,C,D,J,M,N,_B],[B,C,D,J,M,N,_B,_C],[B,C,D,J,M,N,_B,_C,_D],[B,C,D,J,M,N,_B,_D],[B,C,D,J,M,N,_C],[B,C,D,J,M,N,_C,_D],[B,C,D,J,M,N,_D],[B,C,D,J,M,_B],[B,C,D,J,M,_B,_C],[B,C,D,J,M,_B,_C,_D],[B,C,D,J,M,_B,_D],[B,C,D,J,M,_C],[B,C,D,J,M,_C,_D],[B,C,D,J,M,_D],[B,C,D,J,_B],[B,C,D,J,_B,_C],[B,C,D,J,_B,_C,_D],[B,C,D,J,_B,_D],[B,C,D,J,_C],[B,C,D,J,_C,_D],[B,C,D,J,_D],[B,C,F,G],[B,C,F,G,H,J,M],[B,C,F,G,H,J,M,N],[B,C,F,G,H,J,M,N,_B],[B,C,F,G,H,J,M,N,_B,_C],[B,C,F,G,H,J,M,N,_B,_C,_D],[B,C,F,G,H,J,M,N,_B,_D],[B,C,F,G,H,J,M,N,_C],[B,C,F,G,H,J,M,N,_C,_D],[B,C,F,G,H,J,M,N,_D],[B,C,F,G,H,J,M,_B],[B,C,F,G,H,J,M,_B,_C],[B,C,F,G,H,J,M,_B,_C,_D],[B,C,F,G,H,J,M,_B,_D],[B,C,F,G,H,J,M,_C],[B,C,F,G,H,J,M,_C,_D],[B,C,F,G,H,J,M,_D],[B,C,F,G,J],[B,C,F,G,J,M],[B,C,F,G,J,M,N],[B,C,F,G,J,M,N,_B],[B,C,F,G,J,M,N,_B,_C],[B,C,F,G,J,M,N,_B,_C,_D],[B,C,F,G,J,M,N,_B,_D],[B,C,F,G,J,M,N,_C],[B,C,F,G,J,M,N,_C,_D],[B,C,F,G,J,M,N,_D],[B,C,F,G,J,M,_B],[B,C,F,G,J,M,_B,_C],[B,C,F,G,J,M,_B,_C,_D],[B,C,F,G,J,M,_B,_D],[B,C,F,G,J,M,_C],[B,C,F,G,J,M,_C,_D],[B,C,F,G,J,M,_D],[B,C,F,G,J,_B],[B,C,F,G,J,_B,_C],[B,C,F,G,J,_B,_C,_D],[B,C,F,G,J,_B,_D],[B,C,F,G,J,_C],[B,C,F,G,J,_C,_D],[B,C,F,G,J,_D],[B,C,F,G,M,N],[B,C,F,H,J,M],[B,C,F,H,J,M,N],[B,C,F,H,J,M,N,_B],[B,C,F,H,J,M,N,_B,_C],[B,C,F,H,J,M,N,_B,_C,_D],[B,C,F,H,J,M,N,_B,_D],[B,C,F,H,J,M,N,_C],[B,C,F,H,J,M,N,_C,_D],[B,C,F,H,J,M,N,_D],[B,C,F,H,J,M,_B],[B,C,F,H,J,M,_B,_C],[B,C,F,H,J,M,_B,_C,_D],[B,C,F,H,J,M,_B,_D],[B,C,F,H,J,M,_C],[B,C,F,H,J,M,_C,_D],[B,C,F,H,J,M,_D],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N],[B,C,F,J,M,N,_B],[B,C,F,J,M,N,_B,_C],[B,C,F,J,M,N,_B,_C,_D],[B,C,F,J,M,N,_B,_D],[B,C,F,J,M,N,_C],[B,C,F,J,M,N,_C,_D],[B,C,F,J,M,N,_D],[B,C,F,J,M,_B],[B,C,F,J,M,_B,_C],[B,C,F,J,M,_B,_C,_D],[B,C,F,J,M,_B,_D],[B,C,F,J,M,_C],[B,C,F,J,M,_C,_D],[B,C,F,J,M,_D],[B,C,F,J,_B],[B,C,F,J,_B,_C],[B,C,F,J,_B,_C,_D],[B,C,F,J,_B,_D],[B,C,F,J,_C],[B,C,F,J,_C,_D],[B,C,F,J,_D],[B,C,G,H,J,M],[B,C,G,H,J,M,N],[B,C,G,H,J,M,N,_B],[B,C,G,H,J,M,N,_B,_C],[B,C,G,H,J,M,N,_B,_C,_D],[B,C,G,H,J,M,N,_B,_D],[B,C,G,H,J,M,N,_C],[B,C,G,H,J,M,N,_C,_D],[B,C,G,H,J,M,N,_D],[B,C,G,H,J,M,_B],[B,C,G,H,J,M,_B,_C],[B,C,G,H,J,M,_B,_C,_D],[B,C,G,H,J,M,_B,_D],[B,C,G,H,J,M,_C],[B,C,G,H,J,M,_C,_D],[B,C,G,H,J,M,_D],[B,C,G,J],[B,C,G,J,M],[B,C,G,J,M,N],[B,C,G,J,M,N,_B],[B,C,G,J,M,N,_B,_C],[B,C,G,J,M,N,_B,_C,_D],[B,C,G,J,M,N,_B,_D],[B,C,G,J,M,N,_C],[B,C,G,J,M,N,_C,_D],[B,C,G,J,M,N,_D],[B,C,G,J,M,_B],[B,C,G,J,M,_B,_C],[B,C,G,J,M,_B,_C,_D],[B,C,G,J,M,_B,_D],[B,C,G,J,M,_C],[B,C,G,J,M,_C,_D],[B,C,G,J,M,_D],[B,C,G,J,_B],[B,C,G,J,_B,_C],[B,C,G,J,_B,_C,_D],[B,C,G,J,_B,_D],[B,C,G,J,_C],[B,C,G,J,_C,_D],[B,C,G,J,_D],[B,C,H,J,M],[B,C,H,J,M,N],[B,C,H,J,M,N,_B],[B,C,H,J,M,N,_B,_C],[B,C,H,J,M,N,_B,_C,_D],[B,C,H,J,M,N,_B,_D],[B,C,H,J,M,N,_C],[B,C,H,J,M,N,_C,_D],[B,C,H,J,M,N,_D],[B,C,H,J,M,_B],[B,C,H,J,M,_B,_C],[B,C,H,J,M,_B,_C,_D],[B,C,H,J,M,_B,_D],[B,C,H,J,M,_C],[B,C,H,J,M,_C,_D],[B,C,H,J,M,_D],[B,C,J],[B,C,J,M],[B,C,J,M,N],[B,C,J,M,N,_B],[B,C,J,M,N,_B,_C],[B,C,J,M,N,_B,_C,_D],[B,C,J,M,N,_B,_D],[B,C,J,M,N,_C],[B,C,J,M,N,_C,_D],[B,C,J,M,N,_D],[B,C,J,M,_B],[B,C,J,M,_B,_C],[B,C,J,M,_B,_C,_D],[B,C,J,M,_B,_D],[B,C,J,M,_C],[B,C,J,M,_C,_D],[B,C,J,M,_D],[B,C,J,_B],[B,C,J,_B,_C],[B,C,J,_B,_C,_D],[B,C,J,_B,_D],[B,C,J,_C],[B,C,J,_C,_D],[B,C,J,_D],[B,D,F,G,H,J,M],[B,D,F,G,H,J,M,N],[B,D,F,G,H,J,M,N,_B],[B,D,F,G,H,J,M,N,_B,_C],[B,D,F,G,H,J,M,N,_B,_C,_D],[B,D,F,G,H,J,M,N,_B,_D],[B,D,F,G,H,J,M,N,_C],[B,D,F,G,H,J,M,N,_C,_D],[B,D,F,G,H,J,M,N,_D],[B,D,F,G,H,J,M,_B],[B,D,F,G,H,J,M,_B,_C],[B,D,F,G,H,J,M,_B,_C,_D],[B,D,F,G,H,J,M,_B,_D],[B,D,F,G,H,J,M,_C],[B,D,F,G,H,J,M,_C,_D],[B,D,F,G,H,J,M,_D],[B,D,F,G,J],[B,D,F,G,J,M],[B,D,F,G,J,M,N],[B,D,F,G,J,M,N,_B],[B,D,F,G,J,M,N,_B,_C],[B,D,F,G,J,M,N,_B,_C,_D],[B,D,F,G,J,M,N,_B,_D],[B,D,F,G,J,M,N,_C],[B,D,F,G,J,M,N,_C,_D],[B,D,F,G,J,M,N,_D],[B,D,F,G,J,M,_B],[B,D,F,G,J,M,_B,_C],[B,D,F,G,J,M,_B,_C,_D],[B,D,F,G,J,M,_B,_D],[B,D,F,G,J,M,_C],[B,D,F,G,J,M,_C,_D],[B,D,F,G,J,M,_D],[B,D,F,G,J,_B],[B,D,F,G,J,_B,_C],[B,D,F,G,J,_B,_C,_D],[B,D,F,G,J,_B,_D],[B,D,F,G,J,_C],[B,D,F,G,J,_C,_D],[B,D,F,G,J,_D],[B,D,F,H],[B,D,F,H,J,M],[B,D,F,H,J,M,N],[B,D,F,H,J,M,N,_B],[B,D,F,H,J,M,N,_B,_C],[B,D,F,H,J,M,N,_B,_C,_D],[B,D,F,H,J,M,N,_B,_D],[B,D,F,H,J,M,N,_C],[B,D,F,H,J,M,N,_C,_D],[B,D,F,H,J,M,N,_D],[B,D,F,H,J,M,_B],[B,D,F,H,J,M,_B,_C],[B,D,F,H,J,M,_B,_C,_D],[B,D,F,H,J,M,_B,_D],[B,D,F,H,J,M,_C],[B,D,F,H,J,M,_C,_D],[B,D,F,H,J,M,_D],[B,D,F,H,J,_B],[B,D,F,H,J,_B,_C],[B,D,F,H,J,_B,_C,_D],[B,D,F,H,J,_B,_D],[B,D,F,H,J,_C],[B,D,F,H,J,_C,_D],[B,D,F,H,J,_D],[B,D,F,H,M,N],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N],[B,D,F,J,M,N,_B],[B,D,F,J,M,N,_B,_C],[B,D,F,J,M,N,_B,_C,_D],[B,D,F,J,M,N,_B,_D],[B,D,F,J,M,N,_C],[B,D,F,J,M,N,_C,_D],[B,D,F,J,M,N,_D],[B,D,F,J,M,_B],[B,D,F,J,M,_B,_C],[B,D,F,J,M,_B,_C,_D],[B,D,F,J,M,_B,_D],[B,D,F,J,M,_C],[B,D,F,J,M,_C,_D],[B,D,F,J,M,_D],[B,D,F,J,_B],[B,D,F,J,_B,_C],[B,D,F,J,_B,_C,_D],[B,D,F,J,_B,_D],[B,D,F,J,_C],[B,D,F,J,_C,_D],[B,D,F,J,_D],[B,D,G,H,J,M],[B,D,G,H,J,M,N],[B,D,G,H,J,M,N,_B],[B,D,G,H,J,M,N,_B,_C],[B,D,G,H,J,M,N,_B,_C,_D],[B,D,G,H,J,M,N,_B,_D],[B,D,G,H,J,M,N,_C],[B,D,G,H,J,M,N,_C,_D],[B,D,G,H,J,M,N,_D],[B,D,G,H,J,M,_B],[B,D,G,H,J,M,_B,_C],[B,D,G,H,J,M,_B,_C,_D],[B,D,G,H,J,M,_B,_D],[B,D,G,H,J,M,_C],[B,D,G,H,J,M,_C,_D],[B,D,G,H,J,M,_D],[B,D,G,J],[B,D,G,J,M],[B,D,G,J,M,N],[B,D,G,J,M,N,_B],[B,D,G,J,M,N,_B,_C],[B,D,G,J,M,N,_B,_C,_D],[B,D,G,J,M,N,_B,_D],[B,D,G,J,M,N,_C],[B,D,G,J,M,N,_C,_D],[B,D,G,J,M,N,_D],[B,D,G,J,M,_B],[B,D,G,J,M,_B,_C],[B,D,G,J,M,_B,_C,_D],[B,D,G,J,M,_B,_D],[B,D,G,J,M,_C],[B,D,G,J,M,_C,_D],[B,D,G,J,M,_D],[B,D,G,J,_B],[B,D,G,J,_B,_C],[B,D,G,J,_B,_C,_D],[B,D,G,J,_B,_D],[B,D,G,J,_C],[B,D,G,J,_C,_D],[B,D,G,J,_D],[B,D,H,J,M],[B,D,H,J,M,N],[B,D,H,J,M,N,_B],[B,D,H,J,M,N,_B,_C],[B,D,H,J,M,N,_B,_C,_D],[B,D,H,J,M,N,_B,_D],[B,D,H,J,M,N,_C],[B,D,H,J,M,N,_C,_D],[B,D,H,J,M,N,_D],[B,D,H,J,M,_B],[B,D,H,J,M,_B,_C],[B,D,H,J,M,_B,_C,_D],[B,D,H,J,M,_B,_D],[B,D,H,J,M,_C],[B,D,H,J,M,_C,_D],[B,D,H,J,M,_D],[B,D,J],[B,D,J,M],[B,D,J,M,N],[B,D,J,M,N,_B],[B,D,J,M,N,_B,_C],[B,D,J,M,N,_B,_C,_D],[B,D,J,M,N,_B,_D],[B,D,J,M,N,_C],[B,D,J,M,N,_C,_D],[B,D,J,M,N,_D],[B,D,J,M,_B],[B,D,J,M,_B,_C],[B,D,J,M,_B,_C,_D],[B,D,J,M,_B,_D],[B,D,J,M,_C],[B,D,J,M,_C,_D],[B,D,J,M,_D],[B,D,J,_B],[B,D,J,_B,_C],[B,D,J,_B,_C,_D],[B,D,J,_B,_D],[B,D,J,_C],[B,D,J,_C,_D],[B,D,J,_D],[B,F],[B,F,G,H,J,M],[B,F,G,H,J,M,N],[B,F,G,H,J,M,N,_B],[B,F,G,H,J,M,N,_B,_C],[B,F,G,H,J,M,N,_B,_C,_D],[B,F,G,H,J,M,N,_B,_D],[B,F,G,H,J,M,N,_C],[B,F,G,H,J,M,N,_C,_D],[B,F,G,H,J,M,N,_D],[B,F,G,H,J,M,_B],[B,F,G,H,J,M,_B,_C],[B,F,G,H,J,M,_B,_C,_D],[B,F,G,H,J,M,_B,_D],[B,F,G,H,J,M,_C],[B,F,G,H,J,M,_C,_D],[B,F,G,H,J,M,_D],[B,F,G,J],[B,F,G,J,M],[B,F,G,J,M,N],[B,F,G,J,M,N,_B],[B,F,G,J,M,N,_B,_C],[B,F,G,J,M,N,_B,_C,_D],[B,F,G,J,M,N,_B,_D],[B,F,G,J,M,N,_C],[B,F,G,J,M,N,_C,_D],[B,F,G,J,M,N,_D],[B,F,G,J,M,_B],[B,F,G,J,M,_B,_C],[B,F,G,J,M,_B,_C,_D],[B,F,G,J,M,_B,_D],[B,F,G,J,M,_C],[B,F,G,J,M,_C,_D],[B,F,G,J,M,_D],[B,F,G,J,_B],[B,F,G,J,_B,_C],[B,F,G,J,_B,_C,_D],[B,F,G,J,_B,_D],[B,F,G,J,_C],[B,F,G,J,_C,_D],[B,F,G,J,_D],[B,F,H,J,M],[B,F,H,J,M,N],[B,F,H,J,M,N,_B],[B,F,H,J,M,N,_B,_C],[B,F,H,J,M,N,_B,_C,_D],[B,F,H,J,M,N,_B,_D],[B,F,H,J,M,N,_C],[B,F,H,J,M,N,_C,_D],[B,F,H,J,M,N,_D],[B,F,H,J,M,_B],[B,F,H,J,M,_B,_C],[B,F,H,J,M,_B,_C,_D],[B,F,H,J,M,_B,_D],[B,F,H,J,M,_C],[B,F,H,J,M,_C,_D],[B,F,H,J,M,_D],[B,F,J],[B,F,J,M],[B,F,J,M,N],[B,F,J,M,N,_B],[B,F,J,M,N,_B,_C],[B,F,J,M,N,_B,_C,_D],[B,F,J,M,N,_B,_D],[B,F,J,M,N,_C],[B,F,J,M,N,_C,_D],[B,F,J,M,N,_D],[B,F,J,M,_B],[B,F,J,M,_B,_C],[B,F,J,M,_B,_C,_D],[B,F,J,M,_B,_D],[B,F,J,M,_C],[B,F,J,M,_C,_D],[B,F,J,M,_D],[B,F,J,_B],[B,F,J,_B,_C],[B,F,J,_B,_C,_D],[B,F,J,_B,_D],[B,F,J,_C],[B,F,J,_C,_D],[B,F,J,_D],[B,F,M,N],[B,G,H,J,M],[B,G,H,J,M,N],[B,G,H,J,M,N,_B],[B,G,H,J,M,N,_B,_C],[B,G,H,J,M,N,_B,_C,_D],[B,G,H,J,M,N,_B,_D],[B,G,H,J,M,N,_C],[B,G,H,J,M,N,_C,_D],[B,G,H,J,M,N,_D],[B,G,H,J,M,_B],[B,G,H,J,M,_B,_C],[B,G,H,J,M,_B,_C,_D],[B,G,H,J,M,_B,_D],[B,G,H,J,M,_C],[B,G,H,J,M,_C,_D],[B,G,H,J,M,_D],[B,G,J],[B,G,J,M],[B,G,J,M,N],[B,G,J,M,N,_B],[B,G,J,M,N,_B,_C],[B,G,J,M,N,_B,_C,_D],[B,G,J,M,N,_B,_D],[B,G,J,M,N,_C],[B,G,J,M,N,_C,_D],[B,G,J,M,N,_D],[B,G,J,M,_B],[B,G,J,M,_B,_C],[B,G,J,M,_B,_C,_D],[B,G,J,M,_B,_D],[B,G,J,M,_C],[B,G,J,M,_C,_D],[B,G,J,M,_D],[B,G,J,_B],[B,G,J,_B,_C],[B,G,J,_B,_C,_D],[B,G,J,_B,_D],[B,G,J,_C],[B,G,J,_C,_D],[B,G,J,_D],[B,H,J,M],[B,H,J,M,N],[B,H,J,M,N,_B],[B,H,J,M,N,_B,_C],[B,H,J,M,N,_B,_C,_D],[B,H,J,M,N,_B,_D],[B,H,J,M,N,_C],[B,H,J,M,N,_C,_D],[B,H,J,M,N,_D],[B,H,J,M,_B],[B,H,J,M,_B,_C],[B,H,J,M,_B,_C,_D],[B,H,J,M,_B,_D],[B,H,J,M,_C],[B,H,J,M,_C,_D],[B,H,J,M,_D],[B,J],[B,J,M],[B,J,M,N],[B,J,M,N,_B],[B,J,M,N,_B,_C],[B,J,M,N,_B,_C,_D],[B,J,M,N,_B,_D],[B,J,M,N,_C],[B,J,M,N,_C,_D],[B,J,M,N,_D],[B,J,M,_B],[B,J,M,_B,_C],[B,J,M,_B,_C,_D],[B,J,M,_B,_D],[B,J,M,_C],[B,J,M,_C,_D],[B,J,M,_D],[B,J,_B],[B,J,_B,_C],[B,J,_B,_C,_D],[B,J,_B,_D],[B,J,_C],[B,J,_C,_D],[B,J,_D],[C,D,F,G,H,J,M],[C,D,F,G,H,J,M,N],[C,D,F,G,H,J,M,N,_B],[C,D,F,G,H,J,M,N,_B,_C],[C,D,F,G,H,J,M,N,_B,_C,_D],[C,D,F,G,H,J,M,N,_B,_D],[C,D,F,G,H,J,M,N,_C],[C,D,F,G,H,J,M,N,_C,_D],[C,D,F,G,H,J,M,N,_D],[C,D,F,G,H,J,M,_B],[C,D,F,G,H,J,M,_B,_C],[C,D,F,G,H,J,M,_B,_C,_D],[C,D,F,G,H,J,M,_B,_D],[C,D,F,G,H,J,M,_C],[C,D,F,G,H,J,M,_C,_D],[C,D,F,G,H,J,M,_D],[C,D,F,G,J],[C,D,F,G,J,M],[C,D,F,G,J,M,N],[C,D,F,G,J,M,N,_B],[C,D,F,G,J,M,N,_B,_C],[C,D,F,G,J,M,N,_B,_C,_D],[C,D,F,G,J,M,N,_B,_D],[C,D,F,G,J,M,N,_C],[C,D,F,G,J,M,N,_C,_D],[C,D,F,G,J,M,N,_D],[C,D,F,G,J,M,_B],[C,D,F,G,J,M,_B,_C],[C,D,F,G,J,M,_B,_C,_D],[C,D,F,G,J,M,_B,_D],[C,D,F,G,J,M,_C],[C,D,F,G,J,M,_C,_D],[C,D,F,G,J,M,_D],[C,D,F,G,J,_B],[C,D,F,G,J,_B,_C],[C,D,F,G,J,_B,_C,_D],[C,D,F,G,J,_B,_D],[C,D,F,G,J,_C],[C,D,F,G,J,_C,_D],[C,D,F,G,J,_D],[C,D,F,H,J,M],[C,D,F,H,J,M,N],[C,D,F,H,J,M,N,_B],[C,D,F,H,J,M,N,_B,_C],[C,D,F,H,J,M,N,_B,_C,_D],[C,D,F,H,J,M,N,_B,_D],[C,D,F,H,J,M,N,_C],[C,D,F,H,J,M,N,_C,_D],[C,D,F,H,J,M,N,_D],[C,D,F,H,J,M,_B],[C,D,F,H,J,M,_B,_C],[C,D,F,H,J,M,_B,_C,_D],[C,D,F,H,J,M,_B,_D],[C,D,F,H,J,M,_C],[C,D,F,H,J,M,_C,_D],[C,D,F,H,J,M,_D],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N],[C,D,F,J,M,N,_B],[C,D,F,J,M,N,_B,_C],[C,D,F,J,M,N,_B,_C,_D],[C,D,F,J,M,N,_B,_D],[C,D,F,J,M,N,_C],[C,D,F,J,M,N,_C,_D],[C,D,F,J,M,N,_D],[C,D,F,J,M,_B],[C,D,F,J,M,_B,_C],[C,D,F,J,M,_B,_C,_D],[C,D,F,J,M,_B,_D],[C,D,F,J,M,_C],[C,D,F,J,M,_C,_D],[C,D,F,J,M,_D],[C,D,F,J,_B],[C,D,F,J,_B,_C],[C,D,F,J,_B,_C,_D],[C,D,F,J,_B,_D],[C,D,F,J,_C],[C,D,F,J,_C,_D],[C,D,F,J,_D],[C,D,G,H],[C,D,G,H,J,M],[C,D,G,H,J,M,N],[C,D,G,H,J,M,N,_B],[C,D,G,H,J,M,N,_B,_C],[C,D,G,H,J,M,N,_B,_C,_D],[C,D,G,H,J,M,N,_B,_D],[C,D,G,H,J,M,N,_C],[C,D,G,H,J,M,N,_C,_D],[C,D,G,H,J,M,N,_D],[C,D,G,H,J,M,_B],[C,D,G,H,J,M,_B,_C],[C,D,G,H,J,M,_B,_C,_D],[C,D,G,H,J,M,_B,_D],[C,D,G,H,J,M,_C],[C,D,G,H,J,M,_C,_D],[C,D,G,H,J,M,_D],[C,D,G,H,J,_B],[C,D,G,H,J,_B,_C],[C,D,G,H,J,_B,_C,_D],[C,D,G,H,J,_B,_D],[C,D,G,H,J,_C],[C,D,G,H,J,_C,_D],[C,D,G,H,J,_D],[C,D,G,H,M,N],[C,D,G,J],[C,D,G,J,M],[C,D,G,J,M,N],[C,D,G,J,M,N,_B],[C,D,G,J,M,N,_B,_C],[C,D,G,J,M,N,_B,_C,_D],[C,D,G,J,M,N,_B,_D],[C,D,G,J,M,N,_C],[C,D,G,J,M,N,_C,_D],[C,D,G,J,M,N,_D],[C,D,G,J,M,_B],[C,D,G,J,M,_B,_C],[C,D,G,J,M,_B,_C,_D],[C,D,G,J,M,_B,_D],[C,D,G,J,M,_C],[C,D,G,J,M,_C,_D],[C,D,G,J,M,_D],[C,D,G,J,_B],[C,D,G,J,_B,_C],[C,D,G,J,_B,_C,_D],[C,D,G,J,_B,_D],[C,D,G,J,_C],[C,D,G,J,_C,_D],[C,D,G,J,_D],[C,D,H,J,M],[C,D,H,J,M,N],[C,D,H,J,M,N,_B],[C,D,H,J,M,N,_B,_C],[C,D,H,J,M,N,_B,_C,_D],[C,D,H,J,M,N,_B,_D],[C,D,H,J,M,N,_C],[C,D,H,J,M,N,_C,_D],[C,D,H,J,M,N,_D],[C,D,H,J,M,_B],[C,D,H,J,M,_B,_C],[C,D,H,J,M,_B,_C,_D],[C,D,H,J,M,_B,_D],[C,D,H,J,M,_C],[C,D,H,J,M,_C,_D],[C,D,H,J,M,_D],[C,D,J],[C,D,J,M],[C,D,J,M,N],[C,D,J,M,N,_B],[C,D,J,M,N,_B,_C],[C,D,J,M,N,_B,_C,_D],[C,D,J,M,N,_B,_D],[C,D,J,M,N,_C],[C,D,J,M,N,_C,_D],[C,D,J,M,N,_D],[C,D,J,M,_B],[C,D,J,M,_B,_C],[C,D,J,M,_B,_C,_D],[C,D,J,M,_B,_D],[C,D,J,M,_C],[C,D,J,M,_C,_D],[C,D,J,M,_D],[C,D,J,_B],[C,D,J,_B,_C],[C,D,J,_B,_C,_D],[C,D,J,_B,_D],[C,D,J,_C],[C,D,J,_C,_D],[C,D,J,_D],[C,F,G,H,J,M],[C,F,G,H,J,M,N],[C,F,G,H,J,M,N,_B],[C,F,G,H,J,M,N,_B,_C],[C,F,G,H,J,M,N,_B,_C,_D],[C,F,G,H,J,M,N,_B,_D],[C,F,G,H,J,M,N,_C],[C,F,G,H,J,M,N,_C,_D],[C,F,G,H,J,M,N,_D],[C,F,G,H,J,M,_B],[C,F,G,H,J,M,_B,_C],[C,F,G,H,J,M,_B,_C,_D],[C,F,G,H,J,M,_B,_D],[C,F,G,H,J,M,_C],[C,F,G,H,J,M,_C,_D],[C,F,G,H,J,M,_D],[C,F,G,J],[C,F,G,J,M],[C,F,G,J,M,N],[C,F,G,J,M,N,_B],[C,F,G,J,M,N,_B,_C],[C,F,G,J,M,N,_B,_C,_D],[C,F,G,J,M,N,_B,_D],[C,F,G,J,M,N,_C],[C,F,G,J,M,N,_C,_D],[C,F,G,J,M,N,_D],[C,F,G,J,M,_B],[C,F,G,J,M,_B,_C],[C,F,G,J,M,_B,_C,_D],[C,F,G,J,M,_B,_D],[C,F,G,J,M,_C],[C,F,G,J,M,_C,_D],[C,F,G,J,M,_D],[C,F,G,J,_B],[C,F,G,J,_B,_C],[C,F,G,J,_B,_C,_D],[C,F,G,J,_B,_D],[C,F,G,J,_C],[C,F,G,J,_C,_D],[C,F,G,J,_D],[C,F,H,J,M],[C,F,H,J,M,N],[C,F,H,J,M,N,_B],[C,F,H,J,M,N,_B,_C],[C,F,H,J,M,N,_B,_C,_D],[C,F,H,J,M,N,_B,_D],[C,F,H,J,M,N,_C],[C,F,H,J,M,N,_C,_D],[C,F,H,J,M,N,_D],[C,F,H,J,M,_B],[C,F,H,J,M,_B,_C],[C,F,H,J,M,_B,_C,_D],[C,F,H,J,M,_B,_D],[C,F,H,J,M,_C],[C,F,H,J,M,_C,_D],[C,F,H,J,M,_D],[C,F,J],[C,F,J,M],[C,F,J,M,N],[C,F,J,M,N,_B],[C,F,J,M,N,_B,_C],[C,F,J,M,N,_B,_C,_D],[C,F,J,M,N,_B,_D],[C,F,J,M,N,_C],[C,F,J,M,N,_C,_D],[C,F,J,M,N,_D],[C,F,J,M,_B],[C,F,J,M,_B,_C],[C,F,J,M,_B,_C,_D],[C,F,J,M,_B,_D],[C,F,J,M,_C],[C,F,J,M,_C,_D],[C,F,J,M,_D],[C,F,J,_B],[C,F,J,_B,_C],[C,F,J,_B,_C,_D],[C,F,J,_B,_D],[C,F,J,_C],[C,F,J,_C,_D],[C,F,J,_D],[C,G],[C,G,H,J,M],[C,G,H,J,M,N],[C,G,H,J,M,N,_B],[C,G,H,J,M,N,_B,_C],[C,G,H,J,M,N,_B,_C,_D],[C,G,H,J,M,N,_B,_D],[C,G,H,J,M,N,_C],[C,G,H,J,M,N,_C,_D],[C,G,H,J,M,N,_D],[C,G,H,J,M,_B],[C,G,H,J,M,_B,_C],[C,G,H,J,M,_B,_C,_D],[C,G,H,J,M,_B,_D],[C,G,H,J,M,_C],[C,G,H,J,M,_C,_D],[C,G,H,J,M,_D],[C,G,J],[C,G,J,M],[C,G,J,M,N],[C,G,J,M,N,_B],[C,G,J,M,N,_B,_C],[C,G,J,M,N,_B,_C,_D],[C,G,J,M,N,_B,_D],[C,G,J,M,N,_C],[C,G,J,M,N,_C,_D],[C,G,J,M,N,_D],[C,G,J,M,_B],[C,G,J,M,_B,_C],[C,G,J,M,_B,_C,_D],[C,G,J,M,_B,_D],[C,G,J,M,_C],[C,G,J,M,_C,_D],[C,G,J,M,_D],[C,G,J,_B],[C,G,J,_B,_C],[C,G,J,_B,_C,_D],[C,G,J,_B,_D],[C,G,J,_C],[C,G,J,_C,_D],[C,G,J,_D],[C,G,M,N],[C,H,J,M],[C,H,J,M,N],[C,H,J,M,N,_B],[C,H,J,M,N,_B,_C],[C,H,J,M,N,_B,_C,_D],[C,H,J,M,N,_B,_D],[C,H,J,M,N,_C],[C,H,J,M,N,_C,_D],[C,H,J,M,N,_D],[C,H,J,M,_B],[C,H,J,M,_B,_C],[C,H,J,M,_B,_C,_D],[C,H,J,M,_B,_D],[C,H,J,M,_C],[C,H,J,M,_C,_D],[C,H,J,M,_D],[C,J],[C,J,M],[C,J,M,N],[C,J,M,N,_B],[C,J,M,N,_B,_C],[C,J,M,N,_B,_C,_D],[C,J,M,N,_B,_D],[C,J,M,N,_C],[C,J,M,N,_C,_D],[C,J,M,N,_D],[C,J,M,_B],[C,J,M,_B,_C],[C,J,M,_B,_C,_D],[C,J,M,_B,_D],[C,J,M,_C],[C,J,M,_C,_D],[C,J,M,_D],[C,J,_B],[C,J,_B,_C],[C,J,_B,_C,_D],[C,J,_B,_D],[C,J,_C],[C,J,_C,_D],[C,J,_D],[D],[D,F,G],[D,F,G,H,J,M],[D,F,G,H,J,M,N],[D,F,G,H,J,M,N,_B],[D,F,G,H,J,M,N,_B,_C],[D,F,G,H,J,M,N,_B,_C,_D],[D,F,G,H,J,M,N,_B,_D],[D,F,G,H,J,M,N,_C],[D,F,G,H,J,M,N,_C,_D],[D,F,G,H,J,M,N,_D],[D,F,G,H,J,M,_B],[D,F,G,H,J,M,_B,_C],[D,F,G,H,J,M,_B,_C,_D],[D,F,G,H,J,M,_B,_D],[D,F,G,H,J,M,_C],[D,F,G,H,J,M,_C,_D],[D,F,G,H,J,M,_D],[D,F,G,H,M],[D,F,G,H,M,N],[D,F,G,J],[D,F,G,J,M],[D,F,G,J,M,N],[D,F,G,J,M,N,_B],[D,F,G,J,M,N,_B,_C],[D,F,G,J,M,N,_B,_C,_D],[D,F,G,J,M,N,_B,_D],[D,F,G,J,M,N,_C],[D,F,G,J,M,N,_C,_D],[D,F,G,J,M,N,_D],[D,F,G,J,M,_B],[D,F,G,J,M,_B,_C],[D,F,G,J,M,_B,_C,_D],[D,F,G,J,M,_B,_D],[D,F,G,J,M,_C],[D,F,G,J,M,_C,_D],[D,F,G,J,M,_D],[D,F,G,J,_B],[D,F,G,J,_B,_C],[D,F,G,J,_B,_C,_D],[D,F,G,J,_B,_D],[D,F,G,J,_C],[D,F,G,J,_C,_D],[D,F,G,J,_D],[D,F,G,M],[D,F,G,M,N],[D,F,H,J,M],[D,F,H,J,M,N],[D,F,H,J,M,N,_B],[D,F,H,J,M,N,_B,_C],[D,F,H,J,M,N,_B,_C,_D],[D,F,H,J,M,N,_B,_D],[D,F,H,J,M,N,_C],[D,F,H,J,M,N,_C,_D],[D,F,H,J,M,N,_D],[D,F,H,J,M,_B],[D,F,H,J,M,_B,_C],[D,F,H,J,M,_B,_C,_D],[D,F,H,J,M,_B,_D],[D,F,H,J,M,_C],[D,F,H,J,M,_C,_D],[D,F,H,J,M,_D],[D,F,H,M],[D,F,H,M,N],[D,F,J,M],[D,F,J,M,N],[D,F,J,M,N,_B],[D,F,J,M,N,_B,_C],[D,F,J,M,N,_B,_C,_D],[D,F,J,M,N,_B,_D],[D,F,J,M,N,_C],[D,F,J,M,N,_C,_D],[D,F,J,M,N,_D],[D,F,J,M,_B],[D,F,J,M,_B,_C],[D,F,J,M,_B,_C,_D],[D,F,J,M,_B,_D],[D,F,J,M,_C],[D,F,J,M,_C,_D],[D,F,J,M,_D],[D,F,J,_B],[D,F,J,_B,_C],[D,F,J,_B,_C,_D],[D,F,J,_B,_D],[D,F,J,_C],[D,F,J,_C,_D],[D,F,J,_D],[D,F,M],[D,F,M,N],[D,G],[D,G,H,J,M],[D,G,H,J,M,N],[D,G,H,J,M,N,_B],[D,G,H,J,M,N,_B,_C],[D,G,H,J,M,N,_B,_C,_D],[D,G,H,J,M,N,_B,_D],[D,G,H,J,M,N,_C],[D,G,H,J,M,N,_C,_D],[D,G,H,J,M,N,_D],[D,G,H,J,M,_B],[D,G,H,J,M,_B,_C],[D,G,H,J,M,_B,_C,_D],[D,G,H,J,M,_B,_D],[D,G,H,J,M,_C],[D,G,H,J,M,_C,_D],[D,G,H,J,M,_D],[D,G,H,M],[D,G,H,M,N],[D,G,J],[D,G,J,M],[D,G,J,M,N],[D,G,J,M,N,_B],[D,G,J,M,N,_B,_C],[D,G,J,M,N,_B,_C,_D],[D,G,J,M,N,_B,_D],[D,G,J,M,N,_C],[D,G,J,M,N,_C,_D],[D,G,J,M,N,_D],[D,G,J,M,_B],[D,G,J,M,_B,_C],[D,G,J,M,_B,_C,_D],[D,G,J,M,_B,_D],[D,G,J,M,_C],[D,G,J,M,_C,_D],[D,G,J,M,_D],[D,G,J,_B],[D,G,J,_B,_C],[D,G,J,_B,_C,_D],[D,G,J,_B,_D],[D,G,J,_C],[D,G,J,_C,_D],[D,G,J,_D],[D,G,M],[D,G,M,N],[D,H],[D,H,J,M],[D,H,J,M,N],[D,H,J,M,N,_B],[D,H,J,M,N,_B,_C],[D,H,J,M,N,_B,_C,_D],[D,H,J,M,N,_B,_D],[D,H,J,M,N,_C],[D,H,J,M,N,_C,_D],[D,H,J,M,N,_D],[D,H,J,M,_B],[D,H,J,M,_B,_C],[D,H,J,M,_B,_C,_D],[D,H,J,M,_B,_D],[D,H,J,M,_C],[D,H,J,M,_C,_D],[D,H,J,M,_D],[D,H,J,_B],[D,H,J,_B,_C],[D,H,J,_B,_C,_D],[D,H,J,_B,_D],[D,H,J,_C],[D,H,J,_C,_D],[D,H,J,_D],[D,H,M],[D,H,M,N],[D,J,M],[D,J,M,N],[D,J,M,N,_B],[D,J,M,N,_B,_C],[D,J,M,N,_B,_C,_D],[D,J,M,N,_B,_D],[D,J,M,N,_C],[D,J,M,N,_C,_D],[D,J,M,N,_D],[D,J,M,_B],[D,J,M,_B,_C],[D,J,M,_B,_C,_D],[D,J,M,_B,_D],[D,J,M,_C],[D,J,M,_C,_D],[D,J,M,_D],[D,J,_B],[D,J,_B,_C],[D,J,_B,_C,_D],[D,J,_B,_D],[D,J,_C],[D,J,_C,_D],[D,J,_D],[D,M],[D,M,N],[_A,I,J],[F],[F,G],[F,G,H,J,M],[F,G,H,J,M,N],[F,G,H,J,M,N,_B],[F,G,H,J,M,N,_B,_C],[F,G,H,J,M,N,_B,_C,_D],[F,G,H,J,M,N,_B,_D],[F,G,H,J,M,N,_C],[F,G,H,J,M,N,_C,_D],[F,G,H,J,M,N,_D],[F,G,H,J,M,_B],[F,G,H,J,M,_B,_C],[F,G,H,J,M,_B,_C,_D],[F,G,H,J,M,_B,_D],[F,G,H,J,M,_C],[F,G,H,J,M,_C,_D],[F,G,H,J,M,_D],[F,G,H,M],[F,G,H,M,N],[F,G,J],[F,G,J,M],[F,G,J,M,N],[F,G,J,M,N,_B],[F,G,J,M,N,_B,_C],[F,G,J,M,N,_B,_C,_D],[F,G,J,M,N,_B,_D],[F,G,J,M,N,_C],[F,G,J,M,N,_C,_D],[F,G,J,M,N,_D],[F,G,J,M,_B],[F,G,J,M,_B,_C],[F,G,J,M,_B,_C,_D],[F,G,J,M,_B,_D],[F,G,J,M,_C],[F,G,J,M,_C,_D],[F,G,J,M,_D],[F,G,J,_B],[F,G,J,_B,_C],[F,G,J,_B,_C,_D],[F,G,J,_B,_D],[F,G,J,_C],[F,G,J,_C,_D],[F,G,J,_D],[F,G,M],[F,G,M,N],[F,H,J,M],[F,H,J,M,N],[F,H,J,M,N,_B],[F,H,J,M,N,_B,_C],[F,H,J,M,N,_B,_C,_D],[F,H,J,M,N,_B,_D],[F,H,J,M,N,_C],[F,H,J,M,N,_C,_D],[F,H,J,M,N,_D],[F,H,J,M,_B],[F,H,J,M,_B,_C],[F,H,J,M,_B,_C,_D],[F,H,J,M,_B,_D],[F,H,J,M,_C],[F,H,J,M,_C,_D],[F,H,J,M,_D],[F,H,M],[F,H,M,N],[F,J],[F,J,M],[F,J,M,N],[F,J,M,N,_B],[F,J,M,N,_B,_C],[F,J,M,N,_B,_C,_D],[F,J,M,N,_B,_D],[F,J,M,N,_C],[F,J,M,N,_C,_D],[F,J,M,N,_D],[F,J,M,_B],[F,J,M,_B,_C],[F,J,M,_B,_C,_D],[F,J,M,_B,_D],[F,J,M,_C],[F,J,M,_C,_D],[F,J,M,_D],[F,J,_B],[F,J,_B,_C],[F,J,_B,_C,_D],[F,J,_B,_D],[F,J,_C],[F,J,_C,_D],[F,J,_D],[F,M],[F,M,N],[G],[G,H,J,M],[G,H,J,M,N],[G,H,J,M,N,_B],[G,H,J,M,N,_B,_C],[G,H,J,M,N,_B,_C,_D],[G,H,J,M,N,_B,_D],[G,H,J,M,N,_C],[G,H,J,M,N,_C,_D],[G,H,J,M,N,_D],[G,H,J,M,_B],[G,H,J,M,_B,_C],[G,H,J,M,_B,_C,_D],[G,H,J,M,_B,_D],[G,H,J,M,_C],[G,H,J,M,_C,_D],[G,H,J,M,_D],[G,H,M],[G,H,M,N],[G,J],[G,J,M],[G,J,M,N],[G,J,M,N,_B],[G,J,M,N,_B,_C],[G,J,M,N,_B,_C,_D],[G,J,M,N,_B,_D],[G,J,M,N,_C],[G,J,M,N,_C,_D],[G,J,M,N,_D],[G,J,M,_B],[G,J,M,_B,_C],[G,J,M,_B,_C,_D],[G,J,M,_B,_D],[G,J,M,_C],[G,J,M,_C,_D],[G,J,M,_D],[G,J,_B],[G,J,_B,_C],[G,J,_B,_C,_D],[G,J,_B,_D],[G,J,_C],[G,J,_C,_D],[G,J,_D],[G,M],[G,M,N],[H,J,M],[H,J,M,N],[H,J,M,N,_B],[H,J,M,N,_B,_C],[H,J,M,N,_B,_C,_D],[H,J,M,N,_B,_D],[H,J,M,N,_C],[H,J,M,N,_C,_D],[H,J,M,N,_D],[H,J,M,_B],[H,J,M,_B,_C],[H,J,M,_B,_C,_D],[H,J,M,_B,_D],[H,J,M,_C],[H,J,M,_C,_D],[H,J,M,_D],[H,M],[H,M,N],[I,J],[J],[J,M],[J,M,N],[J,M,N,_B],[J,M,N,_B,_C],[J,M,N,_B,_C,_D],[J,M,N,_B,_D],[J,M,N,_C],[J,M,N,_C,_D],[J,M,N,_D],[J,M,_B],[J,M,_B,_C],[J,M,_B,_C,_D],[J,M,_B,_D],[J,M,_C],[J,M,_C,_D],[J,M,_D],[J,_B],[J,_B,_C],[J,_B,_C,_D],[J,_B,_D],[J,_C],[J,_C,_D],[J,_D],[M],[M,N]]),
        ground([K,L]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (_A=E),
       mshare([[B],[B,C],[B,C,D],[B,C,D,M],[B,C,M],[B,D],[B,D,M],[B,M],[C],[C,D],[C,D,M],[C,M],[D],[D,M],[_A],[F],[G],[H],[I],[J],[L],[M],[N]]),
       ground([K]), linear(_A), linear(F), linear(G), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,D,F,G,H],[B,C,D,F,G,H,J,M],[B,C,D,F,G,H,J,M,N],[B,C,D,F,G,H,M,N],[B,C,D,F,G,J],[B,C,D,F,G,J,M],[B,C,D,F,G,J,M,N],[B,C,D,F,H,J,M],[B,C,D,F,H,J,M,N],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N],[B,C,D,G,H,J,M],[B,C,D,G,H,J,M,N],[B,C,D,G,J],[B,C,D,G,J,M],[B,C,D,G,J,M,N],[B,C,D,H,J,M],[B,C,D,H,J,M,N],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N],[B,C,F,G],[B,C,F,G,H,J,M],[B,C,F,G,H,J,M,N],[B,C,F,G,J],[B,C,F,G,J,M],[B,C,F,G,J,M,N],[B,C,F,G,M,N],[B,C,F,H,J,M],[B,C,F,H,J,M,N],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N],[B,C,G,H,J,M],[B,C,G,H,J,M,N],[B,C,G,J],[B,C,G,J,M],[B,C,G,J,M,N],[B,C,H,J,M],[B,C,H,J,M,N],[B,C,J],[B,C,J,M],[B,C,J,M,N],[B,D,F,G,H,J,M],[B,D,F,G,H,J,M,N],[B,D,F,G,J],[B,D,F,G,J,M],[B,D,F,G,J,M,N],[B,D,F,H],[B,D,F,H,J,M],[B,D,F,H,J,M,N],[B,D,F,H,M,N],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N],[B,D,G,H,J,M],[B,D,G,H,J,M,N],[B,D,G,J],[B,D,G,J,M],[B,D,G,J,M,N],[B,D,H,J,M],[B,D,H,J,M,N],[B,D,J],[B,D,J,M],[B,D,J,M,N],[B,F],[B,F,G,H,J,M],[B,F,G,H,J,M,N],[B,F,G,J],[B,F,G,J,M],[B,F,G,J,M,N],[B,F,H,J,M],[B,F,H,J,M,N],[B,F,J],[B,F,J,M],[B,F,J,M,N],[B,F,M,N],[B,G,H,J,M],[B,G,H,J,M,N],[B,G,J],[B,G,J,M],[B,G,J,M,N],[B,H,J,M],[B,H,J,M,N],[B,J],[B,J,M],[B,J,M,N],[C,D,F,G,H,J,M],[C,D,F,G,H,J,M,N],[C,D,F,G,J],[C,D,F,G,J,M],[C,D,F,G,J,M,N],[C,D,F,H,J,M],[C,D,F,H,J,M,N],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N],[C,D,G,H],[C,D,G,H,J,M],[C,D,G,H,J,M,N],[C,D,G,H,M,N],[C,D,G,J],[C,D,G,J,M],[C,D,G,J,M,N],[C,D,H,J,M],[C,D,H,J,M,N],[C,D,J],[C,D,J,M],[C,D,J,M,N],[C,F,G,H,J,M],[C,F,G,H,J,M,N],[C,F,G,J],[C,F,G,J,M],[C,F,G,J,M,N],[C,F,H,J,M],[C,F,H,J,M,N],[C,F,J],[C,F,J,M],[C,F,J,M,N],[C,G],[C,G,H,J,M],[C,G,H,J,M,N],[C,G,J],[C,G,J,M],[C,G,J,M,N],[C,G,M,N],[C,H,J,M],[C,H,J,M,N],[C,J],[C,J,M],[C,J,M,N],[D],[D,F,G,H,J,M],[D,F,G,H,J,M,N],[D,F,G,H,M],[D,F,G,H,M,N],[D,F,G,J,M],[D,F,G,J,M,N],[D,F,G,M],[D,F,G,M,N],[D,F,H,J,M],[D,F,H,J,M,N],[D,F,H,M],[D,F,H,M,N],[D,F,J,M],[D,F,J,M,N],[D,F,M],[D,F,M,N],[D,G,H,J,M],[D,G,H,J,M,N],[D,G,H,M],[D,G,H,M,N],[D,G,J,M],[D,G,J,M,N],[D,G,M],[D,G,M,N],[D,H],[D,H,J,M],[D,H,J,M,N],[D,H,M],[D,H,M,N],[D,J,M],[D,J,M,N],[D,M],[D,M,N],[_A,I,J],[F],[F,G],[F,G,H,J,M],[F,G,H,J,M,N],[F,G,H,M],[F,G,H,M,N],[F,G,J],[F,G,J,M],[F,G,J,M,N],[F,G,M],[F,G,M,N],[F,H,J,M],[F,H,J,M,N],[F,H,M],[F,H,M,N],[F,J],[F,J,M],[F,J,M,N],[F,M],[F,M,N],[G],[G,H,J,M],[G,H,J,M,N],[G,H,M],[G,H,M,N],[G,J],[G,J,M],[G,J,M,N],[G,M],[G,M,N],[H,J,M],[H,J,M,N],[H,M],[H,M,N],[I,J],[J],[J,M],[J,M,N],[M],[M,N]]),
        ground([K,L]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (_A=E),
       mshare([[B],[B,C],[B,C,D],[B,C,D,M],[B,C,M],[B,D],[B,D,M],[B,M],[C],[C,D],[C,D,M],[C,M],[D],[D,M],[_A],[F],[H],[I],[J],[L],[M],[N]]),
       ground([G,K]), linear(_A), linear(F), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,D,F,H,J,M],[B,C,D,F,H,J,M,N],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N],[B,C,D,H,J,M],[B,C,D,H,J,M,N],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N],[B,C,F,H,J,M],[B,C,F,H,J,M,N],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N],[B,C,H,J,M],[B,C,H,J,M,N],[B,C,J],[B,C,J,M],[B,C,J,M,N],[B,D,F,H],[B,D,F,H,J,M],[B,D,F,H,J,M,N],[B,D,F,H,M,N],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N],[B,D,H,J,M],[B,D,H,J,M,N],[B,D,J],[B,D,J,M],[B,D,J,M,N],[B,F],[B,F,H,J,M],[B,F,H,J,M,N],[B,F,J],[B,F,J,M],[B,F,J,M,N],[B,F,M,N],[B,H,J,M],[B,H,J,M,N],[B,J],[B,J,M],[B,J,M,N],[C,D,F,H,J,M],[C,D,F,H,J,M,N],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N],[C,D,H,J,M],[C,D,H,J,M,N],[C,D,J],[C,D,J,M],[C,D,J,M,N],[C,F,H,J,M],[C,F,H,J,M,N],[C,F,J],[C,F,J,M],[C,F,J,M,N],[C,H,J,M],[C,H,J,M,N],[C,J],[C,J,M],[C,J,M,N],[D],[D,F,H,J,M],[D,F,H,J,M,N],[D,F,H,M],[D,F,H,M,N],[D,F,J,M],[D,F,J,M,N],[D,F,M],[D,F,M,N],[D,H],[D,H,J,M],[D,H,J,M,N],[D,H,M],[D,H,M,N],[D,J,M],[D,J,M,N],[D,M],[D,M,N],[_A,I,J],[F],[F,H,J,M],[F,H,J,M,N],[F,H,M],[F,H,M,N],[F,J],[F,J,M],[F,J,M,N],[F,M],[F,M,N],[H,J,M],[H,J,M,N],[H,M],[H,M,N],[I,J],[J],[J,M],[J,M,N],[M],[M,N]]),
        ground([G,K,L]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (E=[pp(poss,np(_B,_C,_D))|_A]),
       mshare([[B],[B,C],[B,C,D],[B,C,D,M],[B,C,D,M,_B],[B,C,D,M,_B,_C],[B,C,D,M,_C],[B,C,D,_B],[B,C,D,_B,_C],[B,C,D,_C],[B,C,M],[B,C,M,_B],[B,C,M,_B,_C],[B,C,M,_C],[B,C,_B],[B,C,_B,_C],[B,C,_C],[B,D],[B,D,M],[B,D,M,_B],[B,D,M,_B,_C],[B,D,M,_C],[B,D,_B],[B,D,_B,_C],[B,D,_C],[B,M],[B,M,_B],[B,M,_B,_C],[B,M,_C],[B,_B],[B,_B,_C],[B,_C],[C],[C,D],[C,D,M],[C,D,M,_B],[C,D,M,_B,_C],[C,D,M,_C],[C,D,_B],[C,D,_B,_C],[C,D,_C],[C,M],[C,M,_B],[C,M,_B,_C],[C,M,_C],[C,_B],[C,_B,_C],[C,_C],[D],[D,M],[D,M,_B],[D,M,_B,_C],[D,M,_C],[D,_B],[D,_B,_C],[D,_C],[_A],[F],[H],[I],[J],[L],[M],[M,_B],[M,_B,_C],[M,_C],[N],[_B],[_B,_C],[_C]]),
       ground([G,K,_D]), linear(_A), linear(F), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,D,F,H,J,M],[B,C,D,F,H,J,M,N],[B,C,D,F,H,J,M,N,_B],[B,C,D,F,H,J,M,N,_B,_C],[B,C,D,F,H,J,M,N,_C],[B,C,D,F,H,J,M,_B],[B,C,D,F,H,J,M,_B,_C],[B,C,D,F,H,J,M,_C],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N],[B,C,D,F,J,M,N,_B],[B,C,D,F,J,M,N,_B,_C],[B,C,D,F,J,M,N,_C],[B,C,D,F,J,M,_B],[B,C,D,F,J,M,_B,_C],[B,C,D,F,J,M,_C],[B,C,D,F,J,_B],[B,C,D,F,J,_B,_C],[B,C,D,F,J,_C],[B,C,D,H,J,M],[B,C,D,H,J,M,N],[B,C,D,H,J,M,N,_B],[B,C,D,H,J,M,N,_B,_C],[B,C,D,H,J,M,N,_C],[B,C,D,H,J,M,_B],[B,C,D,H,J,M,_B,_C],[B,C,D,H,J,M,_C],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N],[B,C,D,J,M,N,_B],[B,C,D,J,M,N,_B,_C],[B,C,D,J,M,N,_C],[B,C,D,J,M,_B],[B,C,D,J,M,_B,_C],[B,C,D,J,M,_C],[B,C,D,J,_B],[B,C,D,J,_B,_C],[B,C,D,J,_C],[B,C,F,H,J,M],[B,C,F,H,J,M,N],[B,C,F,H,J,M,N,_B],[B,C,F,H,J,M,N,_B,_C],[B,C,F,H,J,M,N,_C],[B,C,F,H,J,M,_B],[B,C,F,H,J,M,_B,_C],[B,C,F,H,J,M,_C],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N],[B,C,F,J,M,N,_B],[B,C,F,J,M,N,_B,_C],[B,C,F,J,M,N,_C],[B,C,F,J,M,_B],[B,C,F,J,M,_B,_C],[B,C,F,J,M,_C],[B,C,F,J,_B],[B,C,F,J,_B,_C],[B,C,F,J,_C],[B,C,H,J,M],[B,C,H,J,M,N],[B,C,H,J,M,N,_B],[B,C,H,J,M,N,_B,_C],[B,C,H,J,M,N,_C],[B,C,H,J,M,_B],[B,C,H,J,M,_B,_C],[B,C,H,J,M,_C],[B,C,J],[B,C,J,M],[B,C,J,M,N],[B,C,J,M,N,_B],[B,C,J,M,N,_B,_C],[B,C,J,M,N,_C],[B,C,J,M,_B],[B,C,J,M,_B,_C],[B,C,J,M,_C],[B,C,J,_B],[B,C,J,_B,_C],[B,C,J,_C],[B,D,F,H],[B,D,F,H,J,M],[B,D,F,H,J,M,N],[B,D,F,H,J,M,N,_B],[B,D,F,H,J,M,N,_B,_C],[B,D,F,H,J,M,N,_C],[B,D,F,H,J,M,_B],[B,D,F,H,J,M,_B,_C],[B,D,F,H,J,M,_C],[B,D,F,H,J,_B],[B,D,F,H,J,_B,_C],[B,D,F,H,J,_C],[B,D,F,H,M,N],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N],[B,D,F,J,M,N,_B],[B,D,F,J,M,N,_B,_C],[B,D,F,J,M,N,_C],[B,D,F,J,M,_B],[B,D,F,J,M,_B,_C],[B,D,F,J,M,_C],[B,D,F,J,_B],[B,D,F,J,_B,_C],[B,D,F,J,_C],[B,D,H,J,M],[B,D,H,J,M,N],[B,D,H,J,M,N,_B],[B,D,H,J,M,N,_B,_C],[B,D,H,J,M,N,_C],[B,D,H,J,M,_B],[B,D,H,J,M,_B,_C],[B,D,H,J,M,_C],[B,D,J],[B,D,J,M],[B,D,J,M,N],[B,D,J,M,N,_B],[B,D,J,M,N,_B,_C],[B,D,J,M,N,_C],[B,D,J,M,_B],[B,D,J,M,_B,_C],[B,D,J,M,_C],[B,D,J,_B],[B,D,J,_B,_C],[B,D,J,_C],[B,F],[B,F,H,J,M],[B,F,H,J,M,N],[B,F,H,J,M,N,_B],[B,F,H,J,M,N,_B,_C],[B,F,H,J,M,N,_C],[B,F,H,J,M,_B],[B,F,H,J,M,_B,_C],[B,F,H,J,M,_C],[B,F,J],[B,F,J,M],[B,F,J,M,N],[B,F,J,M,N,_B],[B,F,J,M,N,_B,_C],[B,F,J,M,N,_C],[B,F,J,M,_B],[B,F,J,M,_B,_C],[B,F,J,M,_C],[B,F,J,_B],[B,F,J,_B,_C],[B,F,J,_C],[B,F,M,N],[B,H,J,M],[B,H,J,M,N],[B,H,J,M,N,_B],[B,H,J,M,N,_B,_C],[B,H,J,M,N,_C],[B,H,J,M,_B],[B,H,J,M,_B,_C],[B,H,J,M,_C],[B,J],[B,J,M],[B,J,M,N],[B,J,M,N,_B],[B,J,M,N,_B,_C],[B,J,M,N,_C],[B,J,M,_B],[B,J,M,_B,_C],[B,J,M,_C],[B,J,_B],[B,J,_B,_C],[B,J,_C],[C,D,F,H,J,M],[C,D,F,H,J,M,N],[C,D,F,H,J,M,N,_B],[C,D,F,H,J,M,N,_B,_C],[C,D,F,H,J,M,N,_C],[C,D,F,H,J,M,_B],[C,D,F,H,J,M,_B,_C],[C,D,F,H,J,M,_C],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N],[C,D,F,J,M,N,_B],[C,D,F,J,M,N,_B,_C],[C,D,F,J,M,N,_C],[C,D,F,J,M,_B],[C,D,F,J,M,_B,_C],[C,D,F,J,M,_C],[C,D,F,J,_B],[C,D,F,J,_B,_C],[C,D,F,J,_C],[C,D,H,J,M],[C,D,H,J,M,N],[C,D,H,J,M,N,_B],[C,D,H,J,M,N,_B,_C],[C,D,H,J,M,N,_C],[C,D,H,J,M,_B],[C,D,H,J,M,_B,_C],[C,D,H,J,M,_C],[C,D,J],[C,D,J,M],[C,D,J,M,N],[C,D,J,M,N,_B],[C,D,J,M,N,_B,_C],[C,D,J,M,N,_C],[C,D,J,M,_B],[C,D,J,M,_B,_C],[C,D,J,M,_C],[C,D,J,_B],[C,D,J,_B,_C],[C,D,J,_C],[C,F,H,J,M],[C,F,H,J,M,N],[C,F,H,J,M,N,_B],[C,F,H,J,M,N,_B,_C],[C,F,H,J,M,N,_C],[C,F,H,J,M,_B],[C,F,H,J,M,_B,_C],[C,F,H,J,M,_C],[C,F,J],[C,F,J,M],[C,F,J,M,N],[C,F,J,M,N,_B],[C,F,J,M,N,_B,_C],[C,F,J,M,N,_C],[C,F,J,M,_B],[C,F,J,M,_B,_C],[C,F,J,M,_C],[C,F,J,_B],[C,F,J,_B,_C],[C,F,J,_C],[C,H,J,M],[C,H,J,M,N],[C,H,J,M,N,_B],[C,H,J,M,N,_B,_C],[C,H,J,M,N,_C],[C,H,J,M,_B],[C,H,J,M,_B,_C],[C,H,J,M,_C],[C,J],[C,J,M],[C,J,M,N],[C,J,M,N,_B],[C,J,M,N,_B,_C],[C,J,M,N,_C],[C,J,M,_B],[C,J,M,_B,_C],[C,J,M,_C],[C,J,_B],[C,J,_B,_C],[C,J,_C],[D],[D,F,H,J,M],[D,F,H,J,M,N],[D,F,H,J,M,N,_B],[D,F,H,J,M,N,_B,_C],[D,F,H,J,M,N,_C],[D,F,H,J,M,_B],[D,F,H,J,M,_B,_C],[D,F,H,J,M,_C],[D,F,H,M],[D,F,H,M,N],[D,F,J,M],[D,F,J,M,N],[D,F,J,M,N,_B],[D,F,J,M,N,_B,_C],[D,F,J,M,N,_C],[D,F,J,M,_B],[D,F,J,M,_B,_C],[D,F,J,M,_C],[D,F,J,_B],[D,F,J,_B,_C],[D,F,J,_C],[D,F,M],[D,F,M,N],[D,H],[D,H,J,M],[D,H,J,M,N],[D,H,J,M,N,_B],[D,H,J,M,N,_B,_C],[D,H,J,M,N,_C],[D,H,J,M,_B],[D,H,J,M,_B,_C],[D,H,J,M,_C],[D,H,J,_B],[D,H,J,_B,_C],[D,H,J,_C],[D,H,M],[D,H,M,N],[D,J,M],[D,J,M,N],[D,J,M,N,_B],[D,J,M,N,_B,_C],[D,J,M,N,_C],[D,J,M,_B],[D,J,M,_B,_C],[D,J,M,_C],[D,J,_B],[D,J,_B,_C],[D,J,_C],[D,M],[D,M,N],[_A,I,J],[F],[F,H,J,M],[F,H,J,M,N],[F,H,J,M,N,_B],[F,H,J,M,N,_B,_C],[F,H,J,M,N,_C],[F,H,J,M,_B],[F,H,J,M,_B,_C],[F,H,J,M,_C],[F,H,M],[F,H,M,N],[F,J],[F,J,M],[F,J,M,N],[F,J,M,N,_B],[F,J,M,N,_B,_C],[F,J,M,N,_C],[F,J,M,_B],[F,J,M,_B,_C],[F,J,M,_C],[F,J,_B],[F,J,_B,_C],[F,J,_C],[F,M],[F,M,N],[H,J,M],[H,J,M,N],[H,J,M,N,_B],[H,J,M,N,_B,_C],[H,J,M,N,_C],[H,J,M,_B],[H,J,M,_B,_C],[H,J,M,_C],[H,M],[H,M,N],[I,J],[J],[J,M],[J,M,N],[J,M,N,_B],[J,M,N,_B,_C],[J,M,N,_C],[J,M,_B],[J,M,_B,_C],[J,M,_C],[J,_B],[J,_B,_C],[J,_C],[M],[M,N]]),
        ground([G,K,L,_D]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (E=[pp(poss,np(_B,_C,_D))|_A]),
       mshare([[B],[B,C],[B,C,D],[B,C,D,M],[B,C,D,M,_B],[B,C,D,M,_B,_C],[B,C,D,M,_B,_C,_D],[B,C,D,M,_B,_D],[B,C,D,M,_C],[B,C,D,M,_C,_D],[B,C,D,M,_D],[B,C,D,_B],[B,C,D,_B,_C],[B,C,D,_B,_C,_D],[B,C,D,_B,_D],[B,C,D,_C],[B,C,D,_C,_D],[B,C,D,_D],[B,C,M],[B,C,M,_B],[B,C,M,_B,_C],[B,C,M,_B,_C,_D],[B,C,M,_B,_D],[B,C,M,_C],[B,C,M,_C,_D],[B,C,M,_D],[B,C,_B],[B,C,_B,_C],[B,C,_B,_C,_D],[B,C,_B,_D],[B,C,_C],[B,C,_C,_D],[B,C,_D],[B,D],[B,D,M],[B,D,M,_B],[B,D,M,_B,_C],[B,D,M,_B,_C,_D],[B,D,M,_B,_D],[B,D,M,_C],[B,D,M,_C,_D],[B,D,M,_D],[B,D,_B],[B,D,_B,_C],[B,D,_B,_C,_D],[B,D,_B,_D],[B,D,_C],[B,D,_C,_D],[B,D,_D],[B,M],[B,M,_B],[B,M,_B,_C],[B,M,_B,_C,_D],[B,M,_B,_D],[B,M,_C],[B,M,_C,_D],[B,M,_D],[B,_B],[B,_B,_C],[B,_B,_C,_D],[B,_B,_D],[B,_C],[B,_C,_D],[B,_D],[C],[C,D],[C,D,M],[C,D,M,_B],[C,D,M,_B,_C],[C,D,M,_B,_C,_D],[C,D,M,_B,_D],[C,D,M,_C],[C,D,M,_C,_D],[C,D,M,_D],[C,D,_B],[C,D,_B,_C],[C,D,_B,_C,_D],[C,D,_B,_D],[C,D,_C],[C,D,_C,_D],[C,D,_D],[C,M],[C,M,_B],[C,M,_B,_C],[C,M,_B,_C,_D],[C,M,_B,_D],[C,M,_C],[C,M,_C,_D],[C,M,_D],[C,_B],[C,_B,_C],[C,_B,_C,_D],[C,_B,_D],[C,_C],[C,_C,_D],[C,_D],[D],[D,M],[D,M,_B],[D,M,_B,_C],[D,M,_B,_C,_D],[D,M,_B,_D],[D,M,_C],[D,M,_C,_D],[D,M,_D],[D,_B],[D,_B,_C],[D,_B,_C,_D],[D,_B,_D],[D,_C],[D,_C,_D],[D,_D],[_A],[F],[H],[I],[J],[L],[M],[M,_B],[M,_B,_C],[M,_B,_C,_D],[M,_B,_D],[M,_C],[M,_C,_D],[M,_D],[N],[_B],[_B,_C],[_B,_C,_D],[_B,_D],[_C],[_C,_D],[_D]]),
       ground([G,K]), linear(_A), linear(F), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,D,F,H,J,M],[B,C,D,F,H,J,M,N],[B,C,D,F,H,J,M,N,_B],[B,C,D,F,H,J,M,N,_B,_C],[B,C,D,F,H,J,M,N,_B,_C,_D],[B,C,D,F,H,J,M,N,_B,_D],[B,C,D,F,H,J,M,N,_C],[B,C,D,F,H,J,M,N,_C,_D],[B,C,D,F,H,J,M,N,_D],[B,C,D,F,H,J,M,_B],[B,C,D,F,H,J,M,_B,_C],[B,C,D,F,H,J,M,_B,_C,_D],[B,C,D,F,H,J,M,_B,_D],[B,C,D,F,H,J,M,_C],[B,C,D,F,H,J,M,_C,_D],[B,C,D,F,H,J,M,_D],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N],[B,C,D,F,J,M,N,_B],[B,C,D,F,J,M,N,_B,_C],[B,C,D,F,J,M,N,_B,_C,_D],[B,C,D,F,J,M,N,_B,_D],[B,C,D,F,J,M,N,_C],[B,C,D,F,J,M,N,_C,_D],[B,C,D,F,J,M,N,_D],[B,C,D,F,J,M,_B],[B,C,D,F,J,M,_B,_C],[B,C,D,F,J,M,_B,_C,_D],[B,C,D,F,J,M,_B,_D],[B,C,D,F,J,M,_C],[B,C,D,F,J,M,_C,_D],[B,C,D,F,J,M,_D],[B,C,D,F,J,_B],[B,C,D,F,J,_B,_C],[B,C,D,F,J,_B,_C,_D],[B,C,D,F,J,_B,_D],[B,C,D,F,J,_C],[B,C,D,F,J,_C,_D],[B,C,D,F,J,_D],[B,C,D,H,J,M],[B,C,D,H,J,M,N],[B,C,D,H,J,M,N,_B],[B,C,D,H,J,M,N,_B,_C],[B,C,D,H,J,M,N,_B,_C,_D],[B,C,D,H,J,M,N,_B,_D],[B,C,D,H,J,M,N,_C],[B,C,D,H,J,M,N,_C,_D],[B,C,D,H,J,M,N,_D],[B,C,D,H,J,M,_B],[B,C,D,H,J,M,_B,_C],[B,C,D,H,J,M,_B,_C,_D],[B,C,D,H,J,M,_B,_D],[B,C,D,H,J,M,_C],[B,C,D,H,J,M,_C,_D],[B,C,D,H,J,M,_D],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N],[B,C,D,J,M,N,_B],[B,C,D,J,M,N,_B,_C],[B,C,D,J,M,N,_B,_C,_D],[B,C,D,J,M,N,_B,_D],[B,C,D,J,M,N,_C],[B,C,D,J,M,N,_C,_D],[B,C,D,J,M,N,_D],[B,C,D,J,M,_B],[B,C,D,J,M,_B,_C],[B,C,D,J,M,_B,_C,_D],[B,C,D,J,M,_B,_D],[B,C,D,J,M,_C],[B,C,D,J,M,_C,_D],[B,C,D,J,M,_D],[B,C,D,J,_B],[B,C,D,J,_B,_C],[B,C,D,J,_B,_C,_D],[B,C,D,J,_B,_D],[B,C,D,J,_C],[B,C,D,J,_C,_D],[B,C,D,J,_D],[B,C,F,H,J,M],[B,C,F,H,J,M,N],[B,C,F,H,J,M,N,_B],[B,C,F,H,J,M,N,_B,_C],[B,C,F,H,J,M,N,_B,_C,_D],[B,C,F,H,J,M,N,_B,_D],[B,C,F,H,J,M,N,_C],[B,C,F,H,J,M,N,_C,_D],[B,C,F,H,J,M,N,_D],[B,C,F,H,J,M,_B],[B,C,F,H,J,M,_B,_C],[B,C,F,H,J,M,_B,_C,_D],[B,C,F,H,J,M,_B,_D],[B,C,F,H,J,M,_C],[B,C,F,H,J,M,_C,_D],[B,C,F,H,J,M,_D],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N],[B,C,F,J,M,N,_B],[B,C,F,J,M,N,_B,_C],[B,C,F,J,M,N,_B,_C,_D],[B,C,F,J,M,N,_B,_D],[B,C,F,J,M,N,_C],[B,C,F,J,M,N,_C,_D],[B,C,F,J,M,N,_D],[B,C,F,J,M,_B],[B,C,F,J,M,_B,_C],[B,C,F,J,M,_B,_C,_D],[B,C,F,J,M,_B,_D],[B,C,F,J,M,_C],[B,C,F,J,M,_C,_D],[B,C,F,J,M,_D],[B,C,F,J,_B],[B,C,F,J,_B,_C],[B,C,F,J,_B,_C,_D],[B,C,F,J,_B,_D],[B,C,F,J,_C],[B,C,F,J,_C,_D],[B,C,F,J,_D],[B,C,H,J,M],[B,C,H,J,M,N],[B,C,H,J,M,N,_B],[B,C,H,J,M,N,_B,_C],[B,C,H,J,M,N,_B,_C,_D],[B,C,H,J,M,N,_B,_D],[B,C,H,J,M,N,_C],[B,C,H,J,M,N,_C,_D],[B,C,H,J,M,N,_D],[B,C,H,J,M,_B],[B,C,H,J,M,_B,_C],[B,C,H,J,M,_B,_C,_D],[B,C,H,J,M,_B,_D],[B,C,H,J,M,_C],[B,C,H,J,M,_C,_D],[B,C,H,J,M,_D],[B,C,J],[B,C,J,M],[B,C,J,M,N],[B,C,J,M,N,_B],[B,C,J,M,N,_B,_C],[B,C,J,M,N,_B,_C,_D],[B,C,J,M,N,_B,_D],[B,C,J,M,N,_C],[B,C,J,M,N,_C,_D],[B,C,J,M,N,_D],[B,C,J,M,_B],[B,C,J,M,_B,_C],[B,C,J,M,_B,_C,_D],[B,C,J,M,_B,_D],[B,C,J,M,_C],[B,C,J,M,_C,_D],[B,C,J,M,_D],[B,C,J,_B],[B,C,J,_B,_C],[B,C,J,_B,_C,_D],[B,C,J,_B,_D],[B,C,J,_C],[B,C,J,_C,_D],[B,C,J,_D],[B,D,F,H],[B,D,F,H,J,M],[B,D,F,H,J,M,N],[B,D,F,H,J,M,N,_B],[B,D,F,H,J,M,N,_B,_C],[B,D,F,H,J,M,N,_B,_C,_D],[B,D,F,H,J,M,N,_B,_D],[B,D,F,H,J,M,N,_C],[B,D,F,H,J,M,N,_C,_D],[B,D,F,H,J,M,N,_D],[B,D,F,H,J,M,_B],[B,D,F,H,J,M,_B,_C],[B,D,F,H,J,M,_B,_C,_D],[B,D,F,H,J,M,_B,_D],[B,D,F,H,J,M,_C],[B,D,F,H,J,M,_C,_D],[B,D,F,H,J,M,_D],[B,D,F,H,J,_B],[B,D,F,H,J,_B,_C],[B,D,F,H,J,_B,_C,_D],[B,D,F,H,J,_B,_D],[B,D,F,H,J,_C],[B,D,F,H,J,_C,_D],[B,D,F,H,J,_D],[B,D,F,H,M,N],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N],[B,D,F,J,M,N,_B],[B,D,F,J,M,N,_B,_C],[B,D,F,J,M,N,_B,_C,_D],[B,D,F,J,M,N,_B,_D],[B,D,F,J,M,N,_C],[B,D,F,J,M,N,_C,_D],[B,D,F,J,M,N,_D],[B,D,F,J,M,_B],[B,D,F,J,M,_B,_C],[B,D,F,J,M,_B,_C,_D],[B,D,F,J,M,_B,_D],[B,D,F,J,M,_C],[B,D,F,J,M,_C,_D],[B,D,F,J,M,_D],[B,D,F,J,_B],[B,D,F,J,_B,_C],[B,D,F,J,_B,_C,_D],[B,D,F,J,_B,_D],[B,D,F,J,_C],[B,D,F,J,_C,_D],[B,D,F,J,_D],[B,D,H,J,M],[B,D,H,J,M,N],[B,D,H,J,M,N,_B],[B,D,H,J,M,N,_B,_C],[B,D,H,J,M,N,_B,_C,_D],[B,D,H,J,M,N,_B,_D],[B,D,H,J,M,N,_C],[B,D,H,J,M,N,_C,_D],[B,D,H,J,M,N,_D],[B,D,H,J,M,_B],[B,D,H,J,M,_B,_C],[B,D,H,J,M,_B,_C,_D],[B,D,H,J,M,_B,_D],[B,D,H,J,M,_C],[B,D,H,J,M,_C,_D],[B,D,H,J,M,_D],[B,D,J],[B,D,J,M],[B,D,J,M,N],[B,D,J,M,N,_B],[B,D,J,M,N,_B,_C],[B,D,J,M,N,_B,_C,_D],[B,D,J,M,N,_B,_D],[B,D,J,M,N,_C],[B,D,J,M,N,_C,_D],[B,D,J,M,N,_D],[B,D,J,M,_B],[B,D,J,M,_B,_C],[B,D,J,M,_B,_C,_D],[B,D,J,M,_B,_D],[B,D,J,M,_C],[B,D,J,M,_C,_D],[B,D,J,M,_D],[B,D,J,_B],[B,D,J,_B,_C],[B,D,J,_B,_C,_D],[B,D,J,_B,_D],[B,D,J,_C],[B,D,J,_C,_D],[B,D,J,_D],[B,F],[B,F,H,J,M],[B,F,H,J,M,N],[B,F,H,J,M,N,_B],[B,F,H,J,M,N,_B,_C],[B,F,H,J,M,N,_B,_C,_D],[B,F,H,J,M,N,_B,_D],[B,F,H,J,M,N,_C],[B,F,H,J,M,N,_C,_D],[B,F,H,J,M,N,_D],[B,F,H,J,M,_B],[B,F,H,J,M,_B,_C],[B,F,H,J,M,_B,_C,_D],[B,F,H,J,M,_B,_D],[B,F,H,J,M,_C],[B,F,H,J,M,_C,_D],[B,F,H,J,M,_D],[B,F,J],[B,F,J,M],[B,F,J,M,N],[B,F,J,M,N,_B],[B,F,J,M,N,_B,_C],[B,F,J,M,N,_B,_C,_D],[B,F,J,M,N,_B,_D],[B,F,J,M,N,_C],[B,F,J,M,N,_C,_D],[B,F,J,M,N,_D],[B,F,J,M,_B],[B,F,J,M,_B,_C],[B,F,J,M,_B,_C,_D],[B,F,J,M,_B,_D],[B,F,J,M,_C],[B,F,J,M,_C,_D],[B,F,J,M,_D],[B,F,J,_B],[B,F,J,_B,_C],[B,F,J,_B,_C,_D],[B,F,J,_B,_D],[B,F,J,_C],[B,F,J,_C,_D],[B,F,J,_D],[B,F,M,N],[B,H,J,M],[B,H,J,M,N],[B,H,J,M,N,_B],[B,H,J,M,N,_B,_C],[B,H,J,M,N,_B,_C,_D],[B,H,J,M,N,_B,_D],[B,H,J,M,N,_C],[B,H,J,M,N,_C,_D],[B,H,J,M,N,_D],[B,H,J,M,_B],[B,H,J,M,_B,_C],[B,H,J,M,_B,_C,_D],[B,H,J,M,_B,_D],[B,H,J,M,_C],[B,H,J,M,_C,_D],[B,H,J,M,_D],[B,J],[B,J,M],[B,J,M,N],[B,J,M,N,_B],[B,J,M,N,_B,_C],[B,J,M,N,_B,_C,_D],[B,J,M,N,_B,_D],[B,J,M,N,_C],[B,J,M,N,_C,_D],[B,J,M,N,_D],[B,J,M,_B],[B,J,M,_B,_C],[B,J,M,_B,_C,_D],[B,J,M,_B,_D],[B,J,M,_C],[B,J,M,_C,_D],[B,J,M,_D],[B,J,_B],[B,J,_B,_C],[B,J,_B,_C,_D],[B,J,_B,_D],[B,J,_C],[B,J,_C,_D],[B,J,_D],[C,D,F,H,J,M],[C,D,F,H,J,M,N],[C,D,F,H,J,M,N,_B],[C,D,F,H,J,M,N,_B,_C],[C,D,F,H,J,M,N,_B,_C,_D],[C,D,F,H,J,M,N,_B,_D],[C,D,F,H,J,M,N,_C],[C,D,F,H,J,M,N,_C,_D],[C,D,F,H,J,M,N,_D],[C,D,F,H,J,M,_B],[C,D,F,H,J,M,_B,_C],[C,D,F,H,J,M,_B,_C,_D],[C,D,F,H,J,M,_B,_D],[C,D,F,H,J,M,_C],[C,D,F,H,J,M,_C,_D],[C,D,F,H,J,M,_D],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N],[C,D,F,J,M,N,_B],[C,D,F,J,M,N,_B,_C],[C,D,F,J,M,N,_B,_C,_D],[C,D,F,J,M,N,_B,_D],[C,D,F,J,M,N,_C],[C,D,F,J,M,N,_C,_D],[C,D,F,J,M,N,_D],[C,D,F,J,M,_B],[C,D,F,J,M,_B,_C],[C,D,F,J,M,_B,_C,_D],[C,D,F,J,M,_B,_D],[C,D,F,J,M,_C],[C,D,F,J,M,_C,_D],[C,D,F,J,M,_D],[C,D,F,J,_B],[C,D,F,J,_B,_C],[C,D,F,J,_B,_C,_D],[C,D,F,J,_B,_D],[C,D,F,J,_C],[C,D,F,J,_C,_D],[C,D,F,J,_D],[C,D,H,J,M],[C,D,H,J,M,N],[C,D,H,J,M,N,_B],[C,D,H,J,M,N,_B,_C],[C,D,H,J,M,N,_B,_C,_D],[C,D,H,J,M,N,_B,_D],[C,D,H,J,M,N,_C],[C,D,H,J,M,N,_C,_D],[C,D,H,J,M,N,_D],[C,D,H,J,M,_B],[C,D,H,J,M,_B,_C],[C,D,H,J,M,_B,_C,_D],[C,D,H,J,M,_B,_D],[C,D,H,J,M,_C],[C,D,H,J,M,_C,_D],[C,D,H,J,M,_D],[C,D,J],[C,D,J,M],[C,D,J,M,N],[C,D,J,M,N,_B],[C,D,J,M,N,_B,_C],[C,D,J,M,N,_B,_C,_D],[C,D,J,M,N,_B,_D],[C,D,J,M,N,_C],[C,D,J,M,N,_C,_D],[C,D,J,M,N,_D],[C,D,J,M,_B],[C,D,J,M,_B,_C],[C,D,J,M,_B,_C,_D],[C,D,J,M,_B,_D],[C,D,J,M,_C],[C,D,J,M,_C,_D],[C,D,J,M,_D],[C,D,J,_B],[C,D,J,_B,_C],[C,D,J,_B,_C,_D],[C,D,J,_B,_D],[C,D,J,_C],[C,D,J,_C,_D],[C,D,J,_D],[C,F,H,J,M],[C,F,H,J,M,N],[C,F,H,J,M,N,_B],[C,F,H,J,M,N,_B,_C],[C,F,H,J,M,N,_B,_C,_D],[C,F,H,J,M,N,_B,_D],[C,F,H,J,M,N,_C],[C,F,H,J,M,N,_C,_D],[C,F,H,J,M,N,_D],[C,F,H,J,M,_B],[C,F,H,J,M,_B,_C],[C,F,H,J,M,_B,_C,_D],[C,F,H,J,M,_B,_D],[C,F,H,J,M,_C],[C,F,H,J,M,_C,_D],[C,F,H,J,M,_D],[C,F,J],[C,F,J,M],[C,F,J,M,N],[C,F,J,M,N,_B],[C,F,J,M,N,_B,_C],[C,F,J,M,N,_B,_C,_D],[C,F,J,M,N,_B,_D],[C,F,J,M,N,_C],[C,F,J,M,N,_C,_D],[C,F,J,M,N,_D],[C,F,J,M,_B],[C,F,J,M,_B,_C],[C,F,J,M,_B,_C,_D],[C,F,J,M,_B,_D],[C,F,J,M,_C],[C,F,J,M,_C,_D],[C,F,J,M,_D],[C,F,J,_B],[C,F,J,_B,_C],[C,F,J,_B,_C,_D],[C,F,J,_B,_D],[C,F,J,_C],[C,F,J,_C,_D],[C,F,J,_D],[C,H,J,M],[C,H,J,M,N],[C,H,J,M,N,_B],[C,H,J,M,N,_B,_C],[C,H,J,M,N,_B,_C,_D],[C,H,J,M,N,_B,_D],[C,H,J,M,N,_C],[C,H,J,M,N,_C,_D],[C,H,J,M,N,_D],[C,H,J,M,_B],[C,H,J,M,_B,_C],[C,H,J,M,_B,_C,_D],[C,H,J,M,_B,_D],[C,H,J,M,_C],[C,H,J,M,_C,_D],[C,H,J,M,_D],[C,J],[C,J,M],[C,J,M,N],[C,J,M,N,_B],[C,J,M,N,_B,_C],[C,J,M,N,_B,_C,_D],[C,J,M,N,_B,_D],[C,J,M,N,_C],[C,J,M,N,_C,_D],[C,J,M,N,_D],[C,J,M,_B],[C,J,M,_B,_C],[C,J,M,_B,_C,_D],[C,J,M,_B,_D],[C,J,M,_C],[C,J,M,_C,_D],[C,J,M,_D],[C,J,_B],[C,J,_B,_C],[C,J,_B,_C,_D],[C,J,_B,_D],[C,J,_C],[C,J,_C,_D],[C,J,_D],[D],[D,F,H,J,M],[D,F,H,J,M,N],[D,F,H,J,M,N,_B],[D,F,H,J,M,N,_B,_C],[D,F,H,J,M,N,_B,_C,_D],[D,F,H,J,M,N,_B,_D],[D,F,H,J,M,N,_C],[D,F,H,J,M,N,_C,_D],[D,F,H,J,M,N,_D],[D,F,H,J,M,_B],[D,F,H,J,M,_B,_C],[D,F,H,J,M,_B,_C,_D],[D,F,H,J,M,_B,_D],[D,F,H,J,M,_C],[D,F,H,J,M,_C,_D],[D,F,H,J,M,_D],[D,F,H,M],[D,F,H,M,N],[D,F,J,M],[D,F,J,M,N],[D,F,J,M,N,_B],[D,F,J,M,N,_B,_C],[D,F,J,M,N,_B,_C,_D],[D,F,J,M,N,_B,_D],[D,F,J,M,N,_C],[D,F,J,M,N,_C,_D],[D,F,J,M,N,_D],[D,F,J,M,_B],[D,F,J,M,_B,_C],[D,F,J,M,_B,_C,_D],[D,F,J,M,_B,_D],[D,F,J,M,_C],[D,F,J,M,_C,_D],[D,F,J,M,_D],[D,F,J,_B],[D,F,J,_B,_C],[D,F,J,_B,_C,_D],[D,F,J,_B,_D],[D,F,J,_C],[D,F,J,_C,_D],[D,F,J,_D],[D,F,M],[D,F,M,N],[D,H],[D,H,J,M],[D,H,J,M,N],[D,H,J,M,N,_B],[D,H,J,M,N,_B,_C],[D,H,J,M,N,_B,_C,_D],[D,H,J,M,N,_B,_D],[D,H,J,M,N,_C],[D,H,J,M,N,_C,_D],[D,H,J,M,N,_D],[D,H,J,M,_B],[D,H,J,M,_B,_C],[D,H,J,M,_B,_C,_D],[D,H,J,M,_B,_D],[D,H,J,M,_C],[D,H,J,M,_C,_D],[D,H,J,M,_D],[D,H,J,_B],[D,H,J,_B,_C],[D,H,J,_B,_C,_D],[D,H,J,_B,_D],[D,H,J,_C],[D,H,J,_C,_D],[D,H,J,_D],[D,H,M],[D,H,M,N],[D,J,M],[D,J,M,N],[D,J,M,N,_B],[D,J,M,N,_B,_C],[D,J,M,N,_B,_C,_D],[D,J,M,N,_B,_D],[D,J,M,N,_C],[D,J,M,N,_C,_D],[D,J,M,N,_D],[D,J,M,_B],[D,J,M,_B,_C],[D,J,M,_B,_C,_D],[D,J,M,_B,_D],[D,J,M,_C],[D,J,M,_C,_D],[D,J,M,_D],[D,J,_B],[D,J,_B,_C],[D,J,_B,_C,_D],[D,J,_B,_D],[D,J,_C],[D,J,_C,_D],[D,J,_D],[D,M],[D,M,N],[_A,I,J],[F],[F,H,J,M],[F,H,J,M,N],[F,H,J,M,N,_B],[F,H,J,M,N,_B,_C],[F,H,J,M,N,_B,_C,_D],[F,H,J,M,N,_B,_D],[F,H,J,M,N,_C],[F,H,J,M,N,_C,_D],[F,H,J,M,N,_D],[F,H,J,M,_B],[F,H,J,M,_B,_C],[F,H,J,M,_B,_C,_D],[F,H,J,M,_B,_D],[F,H,J,M,_C],[F,H,J,M,_C,_D],[F,H,J,M,_D],[F,H,M],[F,H,M,N],[F,J],[F,J,M],[F,J,M,N],[F,J,M,N,_B],[F,J,M,N,_B,_C],[F,J,M,N,_B,_C,_D],[F,J,M,N,_B,_D],[F,J,M,N,_C],[F,J,M,N,_C,_D],[F,J,M,N,_D],[F,J,M,_B],[F,J,M,_B,_C],[F,J,M,_B,_C,_D],[F,J,M,_B,_D],[F,J,M,_C],[F,J,M,_C,_D],[F,J,M,_D],[F,J,_B],[F,J,_B,_C],[F,J,_B,_C,_D],[F,J,_B,_D],[F,J,_C],[F,J,_C,_D],[F,J,_D],[F,M],[F,M,N],[H,J,M],[H,J,M,N],[H,J,M,N,_B],[H,J,M,N,_B,_C],[H,J,M,N,_B,_C,_D],[H,J,M,N,_B,_D],[H,J,M,N,_C],[H,J,M,N,_C,_D],[H,J,M,N,_D],[H,J,M,_B],[H,J,M,_B,_C],[H,J,M,_B,_C,_D],[H,J,M,_B,_D],[H,J,M,_C],[H,J,M,_C,_D],[H,J,M,_D],[H,M],[H,M,N],[I,J],[J],[J,M],[J,M,N],[J,M,N,_B],[J,M,N,_B,_C],[J,M,N,_B,_C,_D],[J,M,N,_B,_D],[J,M,N,_C],[J,M,N,_C,_D],[J,M,N,_D],[J,M,_B],[J,M,_B,_C],[J,M,_B,_C,_D],[J,M,_B,_D],[J,M,_C],[J,M,_C,_D],[J,M,_D],[J,_B],[J,_B,_C],[J,_B,_C,_D],[J,_B,_D],[J,_C],[J,_C,_D],[J,_D],[M],[M,N]]),
        ground([G,K,L]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (E=[pp(poss,np(_B,_C,_D))|_A]),
       mshare([[B],[B,C],[B,C,D],[B,C,D,M],[B,C,D,M,_B],[B,C,D,M,_B,_C],[B,C,D,M,_C],[B,C,D,_B],[B,C,D,_B,_C],[B,C,D,_C],[B,C,M],[B,C,M,_B],[B,C,M,_B,_C],[B,C,M,_C],[B,C,_B],[B,C,_B,_C],[B,C,_C],[B,D],[B,D,M],[B,D,M,_B],[B,D,M,_B,_C],[B,D,M,_C],[B,D,_B],[B,D,_B,_C],[B,D,_C],[B,M],[B,M,_B],[B,M,_B,_C],[B,M,_C],[B,_B],[B,_B,_C],[B,_C],[C],[C,D],[C,D,M],[C,D,M,_B],[C,D,M,_B,_C],[C,D,M,_C],[C,D,_B],[C,D,_B,_C],[C,D,_C],[C,M],[C,M,_B],[C,M,_B,_C],[C,M,_C],[C,_B],[C,_B,_C],[C,_C],[D],[D,M],[D,M,_B],[D,M,_B,_C],[D,M,_C],[D,_B],[D,_B,_C],[D,_C],[_A],[F],[G],[H],[I],[J],[L],[M],[M,_B],[M,_B,_C],[M,_C],[N],[_B],[_B,_C],[_C]]),
       ground([K,_D]), linear(_A), linear(F), linear(G), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,D,F,G,H],[B,C,D,F,G,H,J,M],[B,C,D,F,G,H,J,M,N],[B,C,D,F,G,H,J,M,N,_B],[B,C,D,F,G,H,J,M,N,_B,_C],[B,C,D,F,G,H,J,M,N,_C],[B,C,D,F,G,H,J,M,_B],[B,C,D,F,G,H,J,M,_B,_C],[B,C,D,F,G,H,J,M,_C],[B,C,D,F,G,H,J,_B],[B,C,D,F,G,H,J,_B,_C],[B,C,D,F,G,H,J,_C],[B,C,D,F,G,H,M,N],[B,C,D,F,G,J],[B,C,D,F,G,J,M],[B,C,D,F,G,J,M,N],[B,C,D,F,G,J,M,N,_B],[B,C,D,F,G,J,M,N,_B,_C],[B,C,D,F,G,J,M,N,_C],[B,C,D,F,G,J,M,_B],[B,C,D,F,G,J,M,_B,_C],[B,C,D,F,G,J,M,_C],[B,C,D,F,G,J,_B],[B,C,D,F,G,J,_B,_C],[B,C,D,F,G,J,_C],[B,C,D,F,H,J,M],[B,C,D,F,H,J,M,N],[B,C,D,F,H,J,M,N,_B],[B,C,D,F,H,J,M,N,_B,_C],[B,C,D,F,H,J,M,N,_C],[B,C,D,F,H,J,M,_B],[B,C,D,F,H,J,M,_B,_C],[B,C,D,F,H,J,M,_C],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N],[B,C,D,F,J,M,N,_B],[B,C,D,F,J,M,N,_B,_C],[B,C,D,F,J,M,N,_C],[B,C,D,F,J,M,_B],[B,C,D,F,J,M,_B,_C],[B,C,D,F,J,M,_C],[B,C,D,F,J,_B],[B,C,D,F,J,_B,_C],[B,C,D,F,J,_C],[B,C,D,G,H,J,M],[B,C,D,G,H,J,M,N],[B,C,D,G,H,J,M,N,_B],[B,C,D,G,H,J,M,N,_B,_C],[B,C,D,G,H,J,M,N,_C],[B,C,D,G,H,J,M,_B],[B,C,D,G,H,J,M,_B,_C],[B,C,D,G,H,J,M,_C],[B,C,D,G,J],[B,C,D,G,J,M],[B,C,D,G,J,M,N],[B,C,D,G,J,M,N,_B],[B,C,D,G,J,M,N,_B,_C],[B,C,D,G,J,M,N,_C],[B,C,D,G,J,M,_B],[B,C,D,G,J,M,_B,_C],[B,C,D,G,J,M,_C],[B,C,D,G,J,_B],[B,C,D,G,J,_B,_C],[B,C,D,G,J,_C],[B,C,D,H,J,M],[B,C,D,H,J,M,N],[B,C,D,H,J,M,N,_B],[B,C,D,H,J,M,N,_B,_C],[B,C,D,H,J,M,N,_C],[B,C,D,H,J,M,_B],[B,C,D,H,J,M,_B,_C],[B,C,D,H,J,M,_C],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N],[B,C,D,J,M,N,_B],[B,C,D,J,M,N,_B,_C],[B,C,D,J,M,N,_C],[B,C,D,J,M,_B],[B,C,D,J,M,_B,_C],[B,C,D,J,M,_C],[B,C,D,J,_B],[B,C,D,J,_B,_C],[B,C,D,J,_C],[B,C,F,G],[B,C,F,G,H,J,M],[B,C,F,G,H,J,M,N],[B,C,F,G,H,J,M,N,_B],[B,C,F,G,H,J,M,N,_B,_C],[B,C,F,G,H,J,M,N,_C],[B,C,F,G,H,J,M,_B],[B,C,F,G,H,J,M,_B,_C],[B,C,F,G,H,J,M,_C],[B,C,F,G,J],[B,C,F,G,J,M],[B,C,F,G,J,M,N],[B,C,F,G,J,M,N,_B],[B,C,F,G,J,M,N,_B,_C],[B,C,F,G,J,M,N,_C],[B,C,F,G,J,M,_B],[B,C,F,G,J,M,_B,_C],[B,C,F,G,J,M,_C],[B,C,F,G,J,_B],[B,C,F,G,J,_B,_C],[B,C,F,G,J,_C],[B,C,F,G,M,N],[B,C,F,H,J,M],[B,C,F,H,J,M,N],[B,C,F,H,J,M,N,_B],[B,C,F,H,J,M,N,_B,_C],[B,C,F,H,J,M,N,_C],[B,C,F,H,J,M,_B],[B,C,F,H,J,M,_B,_C],[B,C,F,H,J,M,_C],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N],[B,C,F,J,M,N,_B],[B,C,F,J,M,N,_B,_C],[B,C,F,J,M,N,_C],[B,C,F,J,M,_B],[B,C,F,J,M,_B,_C],[B,C,F,J,M,_C],[B,C,F,J,_B],[B,C,F,J,_B,_C],[B,C,F,J,_C],[B,C,G,H,J,M],[B,C,G,H,J,M,N],[B,C,G,H,J,M,N,_B],[B,C,G,H,J,M,N,_B,_C],[B,C,G,H,J,M,N,_C],[B,C,G,H,J,M,_B],[B,C,G,H,J,M,_B,_C],[B,C,G,H,J,M,_C],[B,C,G,J],[B,C,G,J,M],[B,C,G,J,M,N],[B,C,G,J,M,N,_B],[B,C,G,J,M,N,_B,_C],[B,C,G,J,M,N,_C],[B,C,G,J,M,_B],[B,C,G,J,M,_B,_C],[B,C,G,J,M,_C],[B,C,G,J,_B],[B,C,G,J,_B,_C],[B,C,G,J,_C],[B,C,H,J,M],[B,C,H,J,M,N],[B,C,H,J,M,N,_B],[B,C,H,J,M,N,_B,_C],[B,C,H,J,M,N,_C],[B,C,H,J,M,_B],[B,C,H,J,M,_B,_C],[B,C,H,J,M,_C],[B,C,J],[B,C,J,M],[B,C,J,M,N],[B,C,J,M,N,_B],[B,C,J,M,N,_B,_C],[B,C,J,M,N,_C],[B,C,J,M,_B],[B,C,J,M,_B,_C],[B,C,J,M,_C],[B,C,J,_B],[B,C,J,_B,_C],[B,C,J,_C],[B,D,F,G,H,J,M],[B,D,F,G,H,J,M,N],[B,D,F,G,H,J,M,N,_B],[B,D,F,G,H,J,M,N,_B,_C],[B,D,F,G,H,J,M,N,_C],[B,D,F,G,H,J,M,_B],[B,D,F,G,H,J,M,_B,_C],[B,D,F,G,H,J,M,_C],[B,D,F,G,J],[B,D,F,G,J,M],[B,D,F,G,J,M,N],[B,D,F,G,J,M,N,_B],[B,D,F,G,J,M,N,_B,_C],[B,D,F,G,J,M,N,_C],[B,D,F,G,J,M,_B],[B,D,F,G,J,M,_B,_C],[B,D,F,G,J,M,_C],[B,D,F,G,J,_B],[B,D,F,G,J,_B,_C],[B,D,F,G,J,_C],[B,D,F,H],[B,D,F,H,J,M],[B,D,F,H,J,M,N],[B,D,F,H,J,M,N,_B],[B,D,F,H,J,M,N,_B,_C],[B,D,F,H,J,M,N,_C],[B,D,F,H,J,M,_B],[B,D,F,H,J,M,_B,_C],[B,D,F,H,J,M,_C],[B,D,F,H,J,_B],[B,D,F,H,J,_B,_C],[B,D,F,H,J,_C],[B,D,F,H,M,N],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N],[B,D,F,J,M,N,_B],[B,D,F,J,M,N,_B,_C],[B,D,F,J,M,N,_C],[B,D,F,J,M,_B],[B,D,F,J,M,_B,_C],[B,D,F,J,M,_C],[B,D,F,J,_B],[B,D,F,J,_B,_C],[B,D,F,J,_C],[B,D,G,H,J,M],[B,D,G,H,J,M,N],[B,D,G,H,J,M,N,_B],[B,D,G,H,J,M,N,_B,_C],[B,D,G,H,J,M,N,_C],[B,D,G,H,J,M,_B],[B,D,G,H,J,M,_B,_C],[B,D,G,H,J,M,_C],[B,D,G,J],[B,D,G,J,M],[B,D,G,J,M,N],[B,D,G,J,M,N,_B],[B,D,G,J,M,N,_B,_C],[B,D,G,J,M,N,_C],[B,D,G,J,M,_B],[B,D,G,J,M,_B,_C],[B,D,G,J,M,_C],[B,D,G,J,_B],[B,D,G,J,_B,_C],[B,D,G,J,_C],[B,D,H,J,M],[B,D,H,J,M,N],[B,D,H,J,M,N,_B],[B,D,H,J,M,N,_B,_C],[B,D,H,J,M,N,_C],[B,D,H,J,M,_B],[B,D,H,J,M,_B,_C],[B,D,H,J,M,_C],[B,D,J],[B,D,J,M],[B,D,J,M,N],[B,D,J,M,N,_B],[B,D,J,M,N,_B,_C],[B,D,J,M,N,_C],[B,D,J,M,_B],[B,D,J,M,_B,_C],[B,D,J,M,_C],[B,D,J,_B],[B,D,J,_B,_C],[B,D,J,_C],[B,F],[B,F,G,H,J,M],[B,F,G,H,J,M,N],[B,F,G,H,J,M,N,_B],[B,F,G,H,J,M,N,_B,_C],[B,F,G,H,J,M,N,_C],[B,F,G,H,J,M,_B],[B,F,G,H,J,M,_B,_C],[B,F,G,H,J,M,_C],[B,F,G,J],[B,F,G,J,M],[B,F,G,J,M,N],[B,F,G,J,M,N,_B],[B,F,G,J,M,N,_B,_C],[B,F,G,J,M,N,_C],[B,F,G,J,M,_B],[B,F,G,J,M,_B,_C],[B,F,G,J,M,_C],[B,F,G,J,_B],[B,F,G,J,_B,_C],[B,F,G,J,_C],[B,F,H,J,M],[B,F,H,J,M,N],[B,F,H,J,M,N,_B],[B,F,H,J,M,N,_B,_C],[B,F,H,J,M,N,_C],[B,F,H,J,M,_B],[B,F,H,J,M,_B,_C],[B,F,H,J,M,_C],[B,F,J],[B,F,J,M],[B,F,J,M,N],[B,F,J,M,N,_B],[B,F,J,M,N,_B,_C],[B,F,J,M,N,_C],[B,F,J,M,_B],[B,F,J,M,_B,_C],[B,F,J,M,_C],[B,F,J,_B],[B,F,J,_B,_C],[B,F,J,_C],[B,F,M,N],[B,G,H,J,M],[B,G,H,J,M,N],[B,G,H,J,M,N,_B],[B,G,H,J,M,N,_B,_C],[B,G,H,J,M,N,_C],[B,G,H,J,M,_B],[B,G,H,J,M,_B,_C],[B,G,H,J,M,_C],[B,G,J],[B,G,J,M],[B,G,J,M,N],[B,G,J,M,N,_B],[B,G,J,M,N,_B,_C],[B,G,J,M,N,_C],[B,G,J,M,_B],[B,G,J,M,_B,_C],[B,G,J,M,_C],[B,G,J,_B],[B,G,J,_B,_C],[B,G,J,_C],[B,H,J,M],[B,H,J,M,N],[B,H,J,M,N,_B],[B,H,J,M,N,_B,_C],[B,H,J,M,N,_C],[B,H,J,M,_B],[B,H,J,M,_B,_C],[B,H,J,M,_C],[B,J],[B,J,M],[B,J,M,N],[B,J,M,N,_B],[B,J,M,N,_B,_C],[B,J,M,N,_C],[B,J,M,_B],[B,J,M,_B,_C],[B,J,M,_C],[B,J,_B],[B,J,_B,_C],[B,J,_C],[C,D,F,G,H,J,M],[C,D,F,G,H,J,M,N],[C,D,F,G,H,J,M,N,_B],[C,D,F,G,H,J,M,N,_B,_C],[C,D,F,G,H,J,M,N,_C],[C,D,F,G,H,J,M,_B],[C,D,F,G,H,J,M,_B,_C],[C,D,F,G,H,J,M,_C],[C,D,F,G,J],[C,D,F,G,J,M],[C,D,F,G,J,M,N],[C,D,F,G,J,M,N,_B],[C,D,F,G,J,M,N,_B,_C],[C,D,F,G,J,M,N,_C],[C,D,F,G,J,M,_B],[C,D,F,G,J,M,_B,_C],[C,D,F,G,J,M,_C],[C,D,F,G,J,_B],[C,D,F,G,J,_B,_C],[C,D,F,G,J,_C],[C,D,F,H,J,M],[C,D,F,H,J,M,N],[C,D,F,H,J,M,N,_B],[C,D,F,H,J,M,N,_B,_C],[C,D,F,H,J,M,N,_C],[C,D,F,H,J,M,_B],[C,D,F,H,J,M,_B,_C],[C,D,F,H,J,M,_C],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N],[C,D,F,J,M,N,_B],[C,D,F,J,M,N,_B,_C],[C,D,F,J,M,N,_C],[C,D,F,J,M,_B],[C,D,F,J,M,_B,_C],[C,D,F,J,M,_C],[C,D,F,J,_B],[C,D,F,J,_B,_C],[C,D,F,J,_C],[C,D,G,H],[C,D,G,H,J,M],[C,D,G,H,J,M,N],[C,D,G,H,J,M,N,_B],[C,D,G,H,J,M,N,_B,_C],[C,D,G,H,J,M,N,_C],[C,D,G,H,J,M,_B],[C,D,G,H,J,M,_B,_C],[C,D,G,H,J,M,_C],[C,D,G,H,J,_B],[C,D,G,H,J,_B,_C],[C,D,G,H,J,_C],[C,D,G,H,M,N],[C,D,G,J],[C,D,G,J,M],[C,D,G,J,M,N],[C,D,G,J,M,N,_B],[C,D,G,J,M,N,_B,_C],[C,D,G,J,M,N,_C],[C,D,G,J,M,_B],[C,D,G,J,M,_B,_C],[C,D,G,J,M,_C],[C,D,G,J,_B],[C,D,G,J,_B,_C],[C,D,G,J,_C],[C,D,H,J,M],[C,D,H,J,M,N],[C,D,H,J,M,N,_B],[C,D,H,J,M,N,_B,_C],[C,D,H,J,M,N,_C],[C,D,H,J,M,_B],[C,D,H,J,M,_B,_C],[C,D,H,J,M,_C],[C,D,J],[C,D,J,M],[C,D,J,M,N],[C,D,J,M,N,_B],[C,D,J,M,N,_B,_C],[C,D,J,M,N,_C],[C,D,J,M,_B],[C,D,J,M,_B,_C],[C,D,J,M,_C],[C,D,J,_B],[C,D,J,_B,_C],[C,D,J,_C],[C,F,G,H,J,M],[C,F,G,H,J,M,N],[C,F,G,H,J,M,N,_B],[C,F,G,H,J,M,N,_B,_C],[C,F,G,H,J,M,N,_C],[C,F,G,H,J,M,_B],[C,F,G,H,J,M,_B,_C],[C,F,G,H,J,M,_C],[C,F,G,J],[C,F,G,J,M],[C,F,G,J,M,N],[C,F,G,J,M,N,_B],[C,F,G,J,M,N,_B,_C],[C,F,G,J,M,N,_C],[C,F,G,J,M,_B],[C,F,G,J,M,_B,_C],[C,F,G,J,M,_C],[C,F,G,J,_B],[C,F,G,J,_B,_C],[C,F,G,J,_C],[C,F,H,J,M],[C,F,H,J,M,N],[C,F,H,J,M,N,_B],[C,F,H,J,M,N,_B,_C],[C,F,H,J,M,N,_C],[C,F,H,J,M,_B],[C,F,H,J,M,_B,_C],[C,F,H,J,M,_C],[C,F,J],[C,F,J,M],[C,F,J,M,N],[C,F,J,M,N,_B],[C,F,J,M,N,_B,_C],[C,F,J,M,N,_C],[C,F,J,M,_B],[C,F,J,M,_B,_C],[C,F,J,M,_C],[C,F,J,_B],[C,F,J,_B,_C],[C,F,J,_C],[C,G],[C,G,H,J,M],[C,G,H,J,M,N],[C,G,H,J,M,N,_B],[C,G,H,J,M,N,_B,_C],[C,G,H,J,M,N,_C],[C,G,H,J,M,_B],[C,G,H,J,M,_B,_C],[C,G,H,J,M,_C],[C,G,J],[C,G,J,M],[C,G,J,M,N],[C,G,J,M,N,_B],[C,G,J,M,N,_B,_C],[C,G,J,M,N,_C],[C,G,J,M,_B],[C,G,J,M,_B,_C],[C,G,J,M,_C],[C,G,J,_B],[C,G,J,_B,_C],[C,G,J,_C],[C,G,M,N],[C,H,J,M],[C,H,J,M,N],[C,H,J,M,N,_B],[C,H,J,M,N,_B,_C],[C,H,J,M,N,_C],[C,H,J,M,_B],[C,H,J,M,_B,_C],[C,H,J,M,_C],[C,J],[C,J,M],[C,J,M,N],[C,J,M,N,_B],[C,J,M,N,_B,_C],[C,J,M,N,_C],[C,J,M,_B],[C,J,M,_B,_C],[C,J,M,_C],[C,J,_B],[C,J,_B,_C],[C,J,_C],[D],[D,F,G,H,J,M],[D,F,G,H,J,M,N],[D,F,G,H,J,M,N,_B],[D,F,G,H,J,M,N,_B,_C],[D,F,G,H,J,M,N,_C],[D,F,G,H,J,M,_B],[D,F,G,H,J,M,_B,_C],[D,F,G,H,J,M,_C],[D,F,G,H,M],[D,F,G,H,M,N],[D,F,G,J,M],[D,F,G,J,M,N],[D,F,G,J,M,N,_B],[D,F,G,J,M,N,_B,_C],[D,F,G,J,M,N,_C],[D,F,G,J,M,_B],[D,F,G,J,M,_B,_C],[D,F,G,J,M,_C],[D,F,G,J,_B],[D,F,G,J,_B,_C],[D,F,G,J,_C],[D,F,G,M],[D,F,G,M,N],[D,F,H,J,M],[D,F,H,J,M,N],[D,F,H,J,M,N,_B],[D,F,H,J,M,N,_B,_C],[D,F,H,J,M,N,_C],[D,F,H,J,M,_B],[D,F,H,J,M,_B,_C],[D,F,H,J,M,_C],[D,F,H,M],[D,F,H,M,N],[D,F,J,M],[D,F,J,M,N],[D,F,J,M,N,_B],[D,F,J,M,N,_B,_C],[D,F,J,M,N,_C],[D,F,J,M,_B],[D,F,J,M,_B,_C],[D,F,J,M,_C],[D,F,J,_B],[D,F,J,_B,_C],[D,F,J,_C],[D,F,M],[D,F,M,N],[D,G,H,J,M],[D,G,H,J,M,N],[D,G,H,J,M,N,_B],[D,G,H,J,M,N,_B,_C],[D,G,H,J,M,N,_C],[D,G,H,J,M,_B],[D,G,H,J,M,_B,_C],[D,G,H,J,M,_C],[D,G,H,M],[D,G,H,M,N],[D,G,J,M],[D,G,J,M,N],[D,G,J,M,N,_B],[D,G,J,M,N,_B,_C],[D,G,J,M,N,_C],[D,G,J,M,_B],[D,G,J,M,_B,_C],[D,G,J,M,_C],[D,G,J,_B],[D,G,J,_B,_C],[D,G,J,_C],[D,G,M],[D,G,M,N],[D,H],[D,H,J,M],[D,H,J,M,N],[D,H,J,M,N,_B],[D,H,J,M,N,_B,_C],[D,H,J,M,N,_C],[D,H,J,M,_B],[D,H,J,M,_B,_C],[D,H,J,M,_C],[D,H,J,_B],[D,H,J,_B,_C],[D,H,J,_C],[D,H,M],[D,H,M,N],[D,J,M],[D,J,M,N],[D,J,M,N,_B],[D,J,M,N,_B,_C],[D,J,M,N,_C],[D,J,M,_B],[D,J,M,_B,_C],[D,J,M,_C],[D,J,_B],[D,J,_B,_C],[D,J,_C],[D,M],[D,M,N],[_A,I,J],[F],[F,G],[F,G,H,J,M],[F,G,H,J,M,N],[F,G,H,J,M,N,_B],[F,G,H,J,M,N,_B,_C],[F,G,H,J,M,N,_C],[F,G,H,J,M,_B],[F,G,H,J,M,_B,_C],[F,G,H,J,M,_C],[F,G,H,M],[F,G,H,M,N],[F,G,J],[F,G,J,M],[F,G,J,M,N],[F,G,J,M,N,_B],[F,G,J,M,N,_B,_C],[F,G,J,M,N,_C],[F,G,J,M,_B],[F,G,J,M,_B,_C],[F,G,J,M,_C],[F,G,J,_B],[F,G,J,_B,_C],[F,G,J,_C],[F,G,M],[F,G,M,N],[F,H,J,M],[F,H,J,M,N],[F,H,J,M,N,_B],[F,H,J,M,N,_B,_C],[F,H,J,M,N,_C],[F,H,J,M,_B],[F,H,J,M,_B,_C],[F,H,J,M,_C],[F,H,M],[F,H,M,N],[F,J],[F,J,M],[F,J,M,N],[F,J,M,N,_B],[F,J,M,N,_B,_C],[F,J,M,N,_C],[F,J,M,_B],[F,J,M,_B,_C],[F,J,M,_C],[F,J,_B],[F,J,_B,_C],[F,J,_C],[F,M],[F,M,N],[G],[G,H,J,M],[G,H,J,M,N],[G,H,J,M,N,_B],[G,H,J,M,N,_B,_C],[G,H,J,M,N,_C],[G,H,J,M,_B],[G,H,J,M,_B,_C],[G,H,J,M,_C],[G,H,M],[G,H,M,N],[G,J],[G,J,M],[G,J,M,N],[G,J,M,N,_B],[G,J,M,N,_B,_C],[G,J,M,N,_C],[G,J,M,_B],[G,J,M,_B,_C],[G,J,M,_C],[G,J,_B],[G,J,_B,_C],[G,J,_C],[G,M],[G,M,N],[H,J,M],[H,J,M,N],[H,J,M,N,_B],[H,J,M,N,_B,_C],[H,J,M,N,_C],[H,J,M,_B],[H,J,M,_B,_C],[H,J,M,_C],[H,M],[H,M,N],[I,J],[J],[J,M],[J,M,N],[J,M,N,_B],[J,M,N,_B,_C],[J,M,N,_C],[J,M,_B],[J,M,_B,_C],[J,M,_C],[J,_B],[J,_B,_C],[J,_C],[M],[M,N]]),
        ground([K,L,_D]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (E=[pp(poss,np(_B,_C,_D))|_A]),
       mshare([[B],[B,C],[B,C,D],[B,C,D,M],[B,C,D,M,_B],[B,C,D,M,_B,_C],[B,C,D,M,_B,_C,_D],[B,C,D,M,_B,_D],[B,C,D,M,_C],[B,C,D,M,_C,_D],[B,C,D,M,_D],[B,C,D,_B],[B,C,D,_B,_C],[B,C,D,_B,_C,_D],[B,C,D,_B,_D],[B,C,D,_C],[B,C,D,_C,_D],[B,C,D,_D],[B,C,M],[B,C,M,_B],[B,C,M,_B,_C],[B,C,M,_B,_C,_D],[B,C,M,_B,_D],[B,C,M,_C],[B,C,M,_C,_D],[B,C,M,_D],[B,C,_B],[B,C,_B,_C],[B,C,_B,_C,_D],[B,C,_B,_D],[B,C,_C],[B,C,_C,_D],[B,C,_D],[B,D],[B,D,M],[B,D,M,_B],[B,D,M,_B,_C],[B,D,M,_B,_C,_D],[B,D,M,_B,_D],[B,D,M,_C],[B,D,M,_C,_D],[B,D,M,_D],[B,D,_B],[B,D,_B,_C],[B,D,_B,_C,_D],[B,D,_B,_D],[B,D,_C],[B,D,_C,_D],[B,D,_D],[B,M],[B,M,_B],[B,M,_B,_C],[B,M,_B,_C,_D],[B,M,_B,_D],[B,M,_C],[B,M,_C,_D],[B,M,_D],[B,_B],[B,_B,_C],[B,_B,_C,_D],[B,_B,_D],[B,_C],[B,_C,_D],[B,_D],[C],[C,D],[C,D,M],[C,D,M,_B],[C,D,M,_B,_C],[C,D,M,_B,_C,_D],[C,D,M,_B,_D],[C,D,M,_C],[C,D,M,_C,_D],[C,D,M,_D],[C,D,_B],[C,D,_B,_C],[C,D,_B,_C,_D],[C,D,_B,_D],[C,D,_C],[C,D,_C,_D],[C,D,_D],[C,M],[C,M,_B],[C,M,_B,_C],[C,M,_B,_C,_D],[C,M,_B,_D],[C,M,_C],[C,M,_C,_D],[C,M,_D],[C,_B],[C,_B,_C],[C,_B,_C,_D],[C,_B,_D],[C,_C],[C,_C,_D],[C,_D],[D],[D,M],[D,M,_B],[D,M,_B,_C],[D,M,_B,_C,_D],[D,M,_B,_D],[D,M,_C],[D,M,_C,_D],[D,M,_D],[D,_B],[D,_B,_C],[D,_B,_C,_D],[D,_B,_D],[D,_C],[D,_C,_D],[D,_D],[_A],[F],[G],[H],[I],[J],[L],[M],[M,_B],[M,_B,_C],[M,_B,_C,_D],[M,_B,_D],[M,_C],[M,_C,_D],[M,_D],[N],[_B],[_B,_C],[_B,_C,_D],[_B,_D],[_C],[_C,_D],[_D]]),
       ground([K]), linear(_A), linear(F), linear(G), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,D,F,G,H],[B,C,D,F,G,H,J,M],[B,C,D,F,G,H,J,M,N],[B,C,D,F,G,H,J,M,N,_B],[B,C,D,F,G,H,J,M,N,_B,_C],[B,C,D,F,G,H,J,M,N,_B,_C,_D],[B,C,D,F,G,H,J,M,N,_B,_D],[B,C,D,F,G,H,J,M,N,_C],[B,C,D,F,G,H,J,M,N,_C,_D],[B,C,D,F,G,H,J,M,N,_D],[B,C,D,F,G,H,J,M,_B],[B,C,D,F,G,H,J,M,_B,_C],[B,C,D,F,G,H,J,M,_B,_C,_D],[B,C,D,F,G,H,J,M,_B,_D],[B,C,D,F,G,H,J,M,_C],[B,C,D,F,G,H,J,M,_C,_D],[B,C,D,F,G,H,J,M,_D],[B,C,D,F,G,H,J,_B],[B,C,D,F,G,H,J,_B,_C],[B,C,D,F,G,H,J,_B,_C,_D],[B,C,D,F,G,H,J,_B,_D],[B,C,D,F,G,H,J,_C],[B,C,D,F,G,H,J,_C,_D],[B,C,D,F,G,H,J,_D],[B,C,D,F,G,H,M,N],[B,C,D,F,G,J],[B,C,D,F,G,J,M],[B,C,D,F,G,J,M,N],[B,C,D,F,G,J,M,N,_B],[B,C,D,F,G,J,M,N,_B,_C],[B,C,D,F,G,J,M,N,_B,_C,_D],[B,C,D,F,G,J,M,N,_B,_D],[B,C,D,F,G,J,M,N,_C],[B,C,D,F,G,J,M,N,_C,_D],[B,C,D,F,G,J,M,N,_D],[B,C,D,F,G,J,M,_B],[B,C,D,F,G,J,M,_B,_C],[B,C,D,F,G,J,M,_B,_C,_D],[B,C,D,F,G,J,M,_B,_D],[B,C,D,F,G,J,M,_C],[B,C,D,F,G,J,M,_C,_D],[B,C,D,F,G,J,M,_D],[B,C,D,F,G,J,_B],[B,C,D,F,G,J,_B,_C],[B,C,D,F,G,J,_B,_C,_D],[B,C,D,F,G,J,_B,_D],[B,C,D,F,G,J,_C],[B,C,D,F,G,J,_C,_D],[B,C,D,F,G,J,_D],[B,C,D,F,H,J,M],[B,C,D,F,H,J,M,N],[B,C,D,F,H,J,M,N,_B],[B,C,D,F,H,J,M,N,_B,_C],[B,C,D,F,H,J,M,N,_B,_C,_D],[B,C,D,F,H,J,M,N,_B,_D],[B,C,D,F,H,J,M,N,_C],[B,C,D,F,H,J,M,N,_C,_D],[B,C,D,F,H,J,M,N,_D],[B,C,D,F,H,J,M,_B],[B,C,D,F,H,J,M,_B,_C],[B,C,D,F,H,J,M,_B,_C,_D],[B,C,D,F,H,J,M,_B,_D],[B,C,D,F,H,J,M,_C],[B,C,D,F,H,J,M,_C,_D],[B,C,D,F,H,J,M,_D],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N],[B,C,D,F,J,M,N,_B],[B,C,D,F,J,M,N,_B,_C],[B,C,D,F,J,M,N,_B,_C,_D],[B,C,D,F,J,M,N,_B,_D],[B,C,D,F,J,M,N,_C],[B,C,D,F,J,M,N,_C,_D],[B,C,D,F,J,M,N,_D],[B,C,D,F,J,M,_B],[B,C,D,F,J,M,_B,_C],[B,C,D,F,J,M,_B,_C,_D],[B,C,D,F,J,M,_B,_D],[B,C,D,F,J,M,_C],[B,C,D,F,J,M,_C,_D],[B,C,D,F,J,M,_D],[B,C,D,F,J,_B],[B,C,D,F,J,_B,_C],[B,C,D,F,J,_B,_C,_D],[B,C,D,F,J,_B,_D],[B,C,D,F,J,_C],[B,C,D,F,J,_C,_D],[B,C,D,F,J,_D],[B,C,D,G,H,J,M],[B,C,D,G,H,J,M,N],[B,C,D,G,H,J,M,N,_B],[B,C,D,G,H,J,M,N,_B,_C],[B,C,D,G,H,J,M,N,_B,_C,_D],[B,C,D,G,H,J,M,N,_B,_D],[B,C,D,G,H,J,M,N,_C],[B,C,D,G,H,J,M,N,_C,_D],[B,C,D,G,H,J,M,N,_D],[B,C,D,G,H,J,M,_B],[B,C,D,G,H,J,M,_B,_C],[B,C,D,G,H,J,M,_B,_C,_D],[B,C,D,G,H,J,M,_B,_D],[B,C,D,G,H,J,M,_C],[B,C,D,G,H,J,M,_C,_D],[B,C,D,G,H,J,M,_D],[B,C,D,G,J],[B,C,D,G,J,M],[B,C,D,G,J,M,N],[B,C,D,G,J,M,N,_B],[B,C,D,G,J,M,N,_B,_C],[B,C,D,G,J,M,N,_B,_C,_D],[B,C,D,G,J,M,N,_B,_D],[B,C,D,G,J,M,N,_C],[B,C,D,G,J,M,N,_C,_D],[B,C,D,G,J,M,N,_D],[B,C,D,G,J,M,_B],[B,C,D,G,J,M,_B,_C],[B,C,D,G,J,M,_B,_C,_D],[B,C,D,G,J,M,_B,_D],[B,C,D,G,J,M,_C],[B,C,D,G,J,M,_C,_D],[B,C,D,G,J,M,_D],[B,C,D,G,J,_B],[B,C,D,G,J,_B,_C],[B,C,D,G,J,_B,_C,_D],[B,C,D,G,J,_B,_D],[B,C,D,G,J,_C],[B,C,D,G,J,_C,_D],[B,C,D,G,J,_D],[B,C,D,H,J,M],[B,C,D,H,J,M,N],[B,C,D,H,J,M,N,_B],[B,C,D,H,J,M,N,_B,_C],[B,C,D,H,J,M,N,_B,_C,_D],[B,C,D,H,J,M,N,_B,_D],[B,C,D,H,J,M,N,_C],[B,C,D,H,J,M,N,_C,_D],[B,C,D,H,J,M,N,_D],[B,C,D,H,J,M,_B],[B,C,D,H,J,M,_B,_C],[B,C,D,H,J,M,_B,_C,_D],[B,C,D,H,J,M,_B,_D],[B,C,D,H,J,M,_C],[B,C,D,H,J,M,_C,_D],[B,C,D,H,J,M,_D],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N],[B,C,D,J,M,N,_B],[B,C,D,J,M,N,_B,_C],[B,C,D,J,M,N,_B,_C,_D],[B,C,D,J,M,N,_B,_D],[B,C,D,J,M,N,_C],[B,C,D,J,M,N,_C,_D],[B,C,D,J,M,N,_D],[B,C,D,J,M,_B],[B,C,D,J,M,_B,_C],[B,C,D,J,M,_B,_C,_D],[B,C,D,J,M,_B,_D],[B,C,D,J,M,_C],[B,C,D,J,M,_C,_D],[B,C,D,J,M,_D],[B,C,D,J,_B],[B,C,D,J,_B,_C],[B,C,D,J,_B,_C,_D],[B,C,D,J,_B,_D],[B,C,D,J,_C],[B,C,D,J,_C,_D],[B,C,D,J,_D],[B,C,F,G],[B,C,F,G,H,J,M],[B,C,F,G,H,J,M,N],[B,C,F,G,H,J,M,N,_B],[B,C,F,G,H,J,M,N,_B,_C],[B,C,F,G,H,J,M,N,_B,_C,_D],[B,C,F,G,H,J,M,N,_B,_D],[B,C,F,G,H,J,M,N,_C],[B,C,F,G,H,J,M,N,_C,_D],[B,C,F,G,H,J,M,N,_D],[B,C,F,G,H,J,M,_B],[B,C,F,G,H,J,M,_B,_C],[B,C,F,G,H,J,M,_B,_C,_D],[B,C,F,G,H,J,M,_B,_D],[B,C,F,G,H,J,M,_C],[B,C,F,G,H,J,M,_C,_D],[B,C,F,G,H,J,M,_D],[B,C,F,G,J],[B,C,F,G,J,M],[B,C,F,G,J,M,N],[B,C,F,G,J,M,N,_B],[B,C,F,G,J,M,N,_B,_C],[B,C,F,G,J,M,N,_B,_C,_D],[B,C,F,G,J,M,N,_B,_D],[B,C,F,G,J,M,N,_C],[B,C,F,G,J,M,N,_C,_D],[B,C,F,G,J,M,N,_D],[B,C,F,G,J,M,_B],[B,C,F,G,J,M,_B,_C],[B,C,F,G,J,M,_B,_C,_D],[B,C,F,G,J,M,_B,_D],[B,C,F,G,J,M,_C],[B,C,F,G,J,M,_C,_D],[B,C,F,G,J,M,_D],[B,C,F,G,J,_B],[B,C,F,G,J,_B,_C],[B,C,F,G,J,_B,_C,_D],[B,C,F,G,J,_B,_D],[B,C,F,G,J,_C],[B,C,F,G,J,_C,_D],[B,C,F,G,J,_D],[B,C,F,G,M,N],[B,C,F,H,J,M],[B,C,F,H,J,M,N],[B,C,F,H,J,M,N,_B],[B,C,F,H,J,M,N,_B,_C],[B,C,F,H,J,M,N,_B,_C,_D],[B,C,F,H,J,M,N,_B,_D],[B,C,F,H,J,M,N,_C],[B,C,F,H,J,M,N,_C,_D],[B,C,F,H,J,M,N,_D],[B,C,F,H,J,M,_B],[B,C,F,H,J,M,_B,_C],[B,C,F,H,J,M,_B,_C,_D],[B,C,F,H,J,M,_B,_D],[B,C,F,H,J,M,_C],[B,C,F,H,J,M,_C,_D],[B,C,F,H,J,M,_D],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N],[B,C,F,J,M,N,_B],[B,C,F,J,M,N,_B,_C],[B,C,F,J,M,N,_B,_C,_D],[B,C,F,J,M,N,_B,_D],[B,C,F,J,M,N,_C],[B,C,F,J,M,N,_C,_D],[B,C,F,J,M,N,_D],[B,C,F,J,M,_B],[B,C,F,J,M,_B,_C],[B,C,F,J,M,_B,_C,_D],[B,C,F,J,M,_B,_D],[B,C,F,J,M,_C],[B,C,F,J,M,_C,_D],[B,C,F,J,M,_D],[B,C,F,J,_B],[B,C,F,J,_B,_C],[B,C,F,J,_B,_C,_D],[B,C,F,J,_B,_D],[B,C,F,J,_C],[B,C,F,J,_C,_D],[B,C,F,J,_D],[B,C,G,H,J,M],[B,C,G,H,J,M,N],[B,C,G,H,J,M,N,_B],[B,C,G,H,J,M,N,_B,_C],[B,C,G,H,J,M,N,_B,_C,_D],[B,C,G,H,J,M,N,_B,_D],[B,C,G,H,J,M,N,_C],[B,C,G,H,J,M,N,_C,_D],[B,C,G,H,J,M,N,_D],[B,C,G,H,J,M,_B],[B,C,G,H,J,M,_B,_C],[B,C,G,H,J,M,_B,_C,_D],[B,C,G,H,J,M,_B,_D],[B,C,G,H,J,M,_C],[B,C,G,H,J,M,_C,_D],[B,C,G,H,J,M,_D],[B,C,G,J],[B,C,G,J,M],[B,C,G,J,M,N],[B,C,G,J,M,N,_B],[B,C,G,J,M,N,_B,_C],[B,C,G,J,M,N,_B,_C,_D],[B,C,G,J,M,N,_B,_D],[B,C,G,J,M,N,_C],[B,C,G,J,M,N,_C,_D],[B,C,G,J,M,N,_D],[B,C,G,J,M,_B],[B,C,G,J,M,_B,_C],[B,C,G,J,M,_B,_C,_D],[B,C,G,J,M,_B,_D],[B,C,G,J,M,_C],[B,C,G,J,M,_C,_D],[B,C,G,J,M,_D],[B,C,G,J,_B],[B,C,G,J,_B,_C],[B,C,G,J,_B,_C,_D],[B,C,G,J,_B,_D],[B,C,G,J,_C],[B,C,G,J,_C,_D],[B,C,G,J,_D],[B,C,H,J,M],[B,C,H,J,M,N],[B,C,H,J,M,N,_B],[B,C,H,J,M,N,_B,_C],[B,C,H,J,M,N,_B,_C,_D],[B,C,H,J,M,N,_B,_D],[B,C,H,J,M,N,_C],[B,C,H,J,M,N,_C,_D],[B,C,H,J,M,N,_D],[B,C,H,J,M,_B],[B,C,H,J,M,_B,_C],[B,C,H,J,M,_B,_C,_D],[B,C,H,J,M,_B,_D],[B,C,H,J,M,_C],[B,C,H,J,M,_C,_D],[B,C,H,J,M,_D],[B,C,J],[B,C,J,M],[B,C,J,M,N],[B,C,J,M,N,_B],[B,C,J,M,N,_B,_C],[B,C,J,M,N,_B,_C,_D],[B,C,J,M,N,_B,_D],[B,C,J,M,N,_C],[B,C,J,M,N,_C,_D],[B,C,J,M,N,_D],[B,C,J,M,_B],[B,C,J,M,_B,_C],[B,C,J,M,_B,_C,_D],[B,C,J,M,_B,_D],[B,C,J,M,_C],[B,C,J,M,_C,_D],[B,C,J,M,_D],[B,C,J,_B],[B,C,J,_B,_C],[B,C,J,_B,_C,_D],[B,C,J,_B,_D],[B,C,J,_C],[B,C,J,_C,_D],[B,C,J,_D],[B,D,F,G,H,J,M],[B,D,F,G,H,J,M,N],[B,D,F,G,H,J,M,N,_B],[B,D,F,G,H,J,M,N,_B,_C],[B,D,F,G,H,J,M,N,_B,_C,_D],[B,D,F,G,H,J,M,N,_B,_D],[B,D,F,G,H,J,M,N,_C],[B,D,F,G,H,J,M,N,_C,_D],[B,D,F,G,H,J,M,N,_D],[B,D,F,G,H,J,M,_B],[B,D,F,G,H,J,M,_B,_C],[B,D,F,G,H,J,M,_B,_C,_D],[B,D,F,G,H,J,M,_B,_D],[B,D,F,G,H,J,M,_C],[B,D,F,G,H,J,M,_C,_D],[B,D,F,G,H,J,M,_D],[B,D,F,G,J],[B,D,F,G,J,M],[B,D,F,G,J,M,N],[B,D,F,G,J,M,N,_B],[B,D,F,G,J,M,N,_B,_C],[B,D,F,G,J,M,N,_B,_C,_D],[B,D,F,G,J,M,N,_B,_D],[B,D,F,G,J,M,N,_C],[B,D,F,G,J,M,N,_C,_D],[B,D,F,G,J,M,N,_D],[B,D,F,G,J,M,_B],[B,D,F,G,J,M,_B,_C],[B,D,F,G,J,M,_B,_C,_D],[B,D,F,G,J,M,_B,_D],[B,D,F,G,J,M,_C],[B,D,F,G,J,M,_C,_D],[B,D,F,G,J,M,_D],[B,D,F,G,J,_B],[B,D,F,G,J,_B,_C],[B,D,F,G,J,_B,_C,_D],[B,D,F,G,J,_B,_D],[B,D,F,G,J,_C],[B,D,F,G,J,_C,_D],[B,D,F,G,J,_D],[B,D,F,H],[B,D,F,H,J,M],[B,D,F,H,J,M,N],[B,D,F,H,J,M,N,_B],[B,D,F,H,J,M,N,_B,_C],[B,D,F,H,J,M,N,_B,_C,_D],[B,D,F,H,J,M,N,_B,_D],[B,D,F,H,J,M,N,_C],[B,D,F,H,J,M,N,_C,_D],[B,D,F,H,J,M,N,_D],[B,D,F,H,J,M,_B],[B,D,F,H,J,M,_B,_C],[B,D,F,H,J,M,_B,_C,_D],[B,D,F,H,J,M,_B,_D],[B,D,F,H,J,M,_C],[B,D,F,H,J,M,_C,_D],[B,D,F,H,J,M,_D],[B,D,F,H,J,_B],[B,D,F,H,J,_B,_C],[B,D,F,H,J,_B,_C,_D],[B,D,F,H,J,_B,_D],[B,D,F,H,J,_C],[B,D,F,H,J,_C,_D],[B,D,F,H,J,_D],[B,D,F,H,M,N],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N],[B,D,F,J,M,N,_B],[B,D,F,J,M,N,_B,_C],[B,D,F,J,M,N,_B,_C,_D],[B,D,F,J,M,N,_B,_D],[B,D,F,J,M,N,_C],[B,D,F,J,M,N,_C,_D],[B,D,F,J,M,N,_D],[B,D,F,J,M,_B],[B,D,F,J,M,_B,_C],[B,D,F,J,M,_B,_C,_D],[B,D,F,J,M,_B,_D],[B,D,F,J,M,_C],[B,D,F,J,M,_C,_D],[B,D,F,J,M,_D],[B,D,F,J,_B],[B,D,F,J,_B,_C],[B,D,F,J,_B,_C,_D],[B,D,F,J,_B,_D],[B,D,F,J,_C],[B,D,F,J,_C,_D],[B,D,F,J,_D],[B,D,G,H,J,M],[B,D,G,H,J,M,N],[B,D,G,H,J,M,N,_B],[B,D,G,H,J,M,N,_B,_C],[B,D,G,H,J,M,N,_B,_C,_D],[B,D,G,H,J,M,N,_B,_D],[B,D,G,H,J,M,N,_C],[B,D,G,H,J,M,N,_C,_D],[B,D,G,H,J,M,N,_D],[B,D,G,H,J,M,_B],[B,D,G,H,J,M,_B,_C],[B,D,G,H,J,M,_B,_C,_D],[B,D,G,H,J,M,_B,_D],[B,D,G,H,J,M,_C],[B,D,G,H,J,M,_C,_D],[B,D,G,H,J,M,_D],[B,D,G,J],[B,D,G,J,M],[B,D,G,J,M,N],[B,D,G,J,M,N,_B],[B,D,G,J,M,N,_B,_C],[B,D,G,J,M,N,_B,_C,_D],[B,D,G,J,M,N,_B,_D],[B,D,G,J,M,N,_C],[B,D,G,J,M,N,_C,_D],[B,D,G,J,M,N,_D],[B,D,G,J,M,_B],[B,D,G,J,M,_B,_C],[B,D,G,J,M,_B,_C,_D],[B,D,G,J,M,_B,_D],[B,D,G,J,M,_C],[B,D,G,J,M,_C,_D],[B,D,G,J,M,_D],[B,D,G,J,_B],[B,D,G,J,_B,_C],[B,D,G,J,_B,_C,_D],[B,D,G,J,_B,_D],[B,D,G,J,_C],[B,D,G,J,_C,_D],[B,D,G,J,_D],[B,D,H,J,M],[B,D,H,J,M,N],[B,D,H,J,M,N,_B],[B,D,H,J,M,N,_B,_C],[B,D,H,J,M,N,_B,_C,_D],[B,D,H,J,M,N,_B,_D],[B,D,H,J,M,N,_C],[B,D,H,J,M,N,_C,_D],[B,D,H,J,M,N,_D],[B,D,H,J,M,_B],[B,D,H,J,M,_B,_C],[B,D,H,J,M,_B,_C,_D],[B,D,H,J,M,_B,_D],[B,D,H,J,M,_C],[B,D,H,J,M,_C,_D],[B,D,H,J,M,_D],[B,D,J],[B,D,J,M],[B,D,J,M,N],[B,D,J,M,N,_B],[B,D,J,M,N,_B,_C],[B,D,J,M,N,_B,_C,_D],[B,D,J,M,N,_B,_D],[B,D,J,M,N,_C],[B,D,J,M,N,_C,_D],[B,D,J,M,N,_D],[B,D,J,M,_B],[B,D,J,M,_B,_C],[B,D,J,M,_B,_C,_D],[B,D,J,M,_B,_D],[B,D,J,M,_C],[B,D,J,M,_C,_D],[B,D,J,M,_D],[B,D,J,_B],[B,D,J,_B,_C],[B,D,J,_B,_C,_D],[B,D,J,_B,_D],[B,D,J,_C],[B,D,J,_C,_D],[B,D,J,_D],[B,F],[B,F,G,H,J,M],[B,F,G,H,J,M,N],[B,F,G,H,J,M,N,_B],[B,F,G,H,J,M,N,_B,_C],[B,F,G,H,J,M,N,_B,_C,_D],[B,F,G,H,J,M,N,_B,_D],[B,F,G,H,J,M,N,_C],[B,F,G,H,J,M,N,_C,_D],[B,F,G,H,J,M,N,_D],[B,F,G,H,J,M,_B],[B,F,G,H,J,M,_B,_C],[B,F,G,H,J,M,_B,_C,_D],[B,F,G,H,J,M,_B,_D],[B,F,G,H,J,M,_C],[B,F,G,H,J,M,_C,_D],[B,F,G,H,J,M,_D],[B,F,G,J],[B,F,G,J,M],[B,F,G,J,M,N],[B,F,G,J,M,N,_B],[B,F,G,J,M,N,_B,_C],[B,F,G,J,M,N,_B,_C,_D],[B,F,G,J,M,N,_B,_D],[B,F,G,J,M,N,_C],[B,F,G,J,M,N,_C,_D],[B,F,G,J,M,N,_D],[B,F,G,J,M,_B],[B,F,G,J,M,_B,_C],[B,F,G,J,M,_B,_C,_D],[B,F,G,J,M,_B,_D],[B,F,G,J,M,_C],[B,F,G,J,M,_C,_D],[B,F,G,J,M,_D],[B,F,G,J,_B],[B,F,G,J,_B,_C],[B,F,G,J,_B,_C,_D],[B,F,G,J,_B,_D],[B,F,G,J,_C],[B,F,G,J,_C,_D],[B,F,G,J,_D],[B,F,H,J,M],[B,F,H,J,M,N],[B,F,H,J,M,N,_B],[B,F,H,J,M,N,_B,_C],[B,F,H,J,M,N,_B,_C,_D],[B,F,H,J,M,N,_B,_D],[B,F,H,J,M,N,_C],[B,F,H,J,M,N,_C,_D],[B,F,H,J,M,N,_D],[B,F,H,J,M,_B],[B,F,H,J,M,_B,_C],[B,F,H,J,M,_B,_C,_D],[B,F,H,J,M,_B,_D],[B,F,H,J,M,_C],[B,F,H,J,M,_C,_D],[B,F,H,J,M,_D],[B,F,J],[B,F,J,M],[B,F,J,M,N],[B,F,J,M,N,_B],[B,F,J,M,N,_B,_C],[B,F,J,M,N,_B,_C,_D],[B,F,J,M,N,_B,_D],[B,F,J,M,N,_C],[B,F,J,M,N,_C,_D],[B,F,J,M,N,_D],[B,F,J,M,_B],[B,F,J,M,_B,_C],[B,F,J,M,_B,_C,_D],[B,F,J,M,_B,_D],[B,F,J,M,_C],[B,F,J,M,_C,_D],[B,F,J,M,_D],[B,F,J,_B],[B,F,J,_B,_C],[B,F,J,_B,_C,_D],[B,F,J,_B,_D],[B,F,J,_C],[B,F,J,_C,_D],[B,F,J,_D],[B,F,M,N],[B,G,H,J,M],[B,G,H,J,M,N],[B,G,H,J,M,N,_B],[B,G,H,J,M,N,_B,_C],[B,G,H,J,M,N,_B,_C,_D],[B,G,H,J,M,N,_B,_D],[B,G,H,J,M,N,_C],[B,G,H,J,M,N,_C,_D],[B,G,H,J,M,N,_D],[B,G,H,J,M,_B],[B,G,H,J,M,_B,_C],[B,G,H,J,M,_B,_C,_D],[B,G,H,J,M,_B,_D],[B,G,H,J,M,_C],[B,G,H,J,M,_C,_D],[B,G,H,J,M,_D],[B,G,J],[B,G,J,M],[B,G,J,M,N],[B,G,J,M,N,_B],[B,G,J,M,N,_B,_C],[B,G,J,M,N,_B,_C,_D],[B,G,J,M,N,_B,_D],[B,G,J,M,N,_C],[B,G,J,M,N,_C,_D],[B,G,J,M,N,_D],[B,G,J,M,_B],[B,G,J,M,_B,_C],[B,G,J,M,_B,_C,_D],[B,G,J,M,_B,_D],[B,G,J,M,_C],[B,G,J,M,_C,_D],[B,G,J,M,_D],[B,G,J,_B],[B,G,J,_B,_C],[B,G,J,_B,_C,_D],[B,G,J,_B,_D],[B,G,J,_C],[B,G,J,_C,_D],[B,G,J,_D],[B,H,J,M],[B,H,J,M,N],[B,H,J,M,N,_B],[B,H,J,M,N,_B,_C],[B,H,J,M,N,_B,_C,_D],[B,H,J,M,N,_B,_D],[B,H,J,M,N,_C],[B,H,J,M,N,_C,_D],[B,H,J,M,N,_D],[B,H,J,M,_B],[B,H,J,M,_B,_C],[B,H,J,M,_B,_C,_D],[B,H,J,M,_B,_D],[B,H,J,M,_C],[B,H,J,M,_C,_D],[B,H,J,M,_D],[B,J],[B,J,M],[B,J,M,N],[B,J,M,N,_B],[B,J,M,N,_B,_C],[B,J,M,N,_B,_C,_D],[B,J,M,N,_B,_D],[B,J,M,N,_C],[B,J,M,N,_C,_D],[B,J,M,N,_D],[B,J,M,_B],[B,J,M,_B,_C],[B,J,M,_B,_C,_D],[B,J,M,_B,_D],[B,J,M,_C],[B,J,M,_C,_D],[B,J,M,_D],[B,J,_B],[B,J,_B,_C],[B,J,_B,_C,_D],[B,J,_B,_D],[B,J,_C],[B,J,_C,_D],[B,J,_D],[C,D,F,G,H,J,M],[C,D,F,G,H,J,M,N],[C,D,F,G,H,J,M,N,_B],[C,D,F,G,H,J,M,N,_B,_C],[C,D,F,G,H,J,M,N,_B,_C,_D],[C,D,F,G,H,J,M,N,_B,_D],[C,D,F,G,H,J,M,N,_C],[C,D,F,G,H,J,M,N,_C,_D],[C,D,F,G,H,J,M,N,_D],[C,D,F,G,H,J,M,_B],[C,D,F,G,H,J,M,_B,_C],[C,D,F,G,H,J,M,_B,_C,_D],[C,D,F,G,H,J,M,_B,_D],[C,D,F,G,H,J,M,_C],[C,D,F,G,H,J,M,_C,_D],[C,D,F,G,H,J,M,_D],[C,D,F,G,J],[C,D,F,G,J,M],[C,D,F,G,J,M,N],[C,D,F,G,J,M,N,_B],[C,D,F,G,J,M,N,_B,_C],[C,D,F,G,J,M,N,_B,_C,_D],[C,D,F,G,J,M,N,_B,_D],[C,D,F,G,J,M,N,_C],[C,D,F,G,J,M,N,_C,_D],[C,D,F,G,J,M,N,_D],[C,D,F,G,J,M,_B],[C,D,F,G,J,M,_B,_C],[C,D,F,G,J,M,_B,_C,_D],[C,D,F,G,J,M,_B,_D],[C,D,F,G,J,M,_C],[C,D,F,G,J,M,_C,_D],[C,D,F,G,J,M,_D],[C,D,F,G,J,_B],[C,D,F,G,J,_B,_C],[C,D,F,G,J,_B,_C,_D],[C,D,F,G,J,_B,_D],[C,D,F,G,J,_C],[C,D,F,G,J,_C,_D],[C,D,F,G,J,_D],[C,D,F,H,J,M],[C,D,F,H,J,M,N],[C,D,F,H,J,M,N,_B],[C,D,F,H,J,M,N,_B,_C],[C,D,F,H,J,M,N,_B,_C,_D],[C,D,F,H,J,M,N,_B,_D],[C,D,F,H,J,M,N,_C],[C,D,F,H,J,M,N,_C,_D],[C,D,F,H,J,M,N,_D],[C,D,F,H,J,M,_B],[C,D,F,H,J,M,_B,_C],[C,D,F,H,J,M,_B,_C,_D],[C,D,F,H,J,M,_B,_D],[C,D,F,H,J,M,_C],[C,D,F,H,J,M,_C,_D],[C,D,F,H,J,M,_D],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N],[C,D,F,J,M,N,_B],[C,D,F,J,M,N,_B,_C],[C,D,F,J,M,N,_B,_C,_D],[C,D,F,J,M,N,_B,_D],[C,D,F,J,M,N,_C],[C,D,F,J,M,N,_C,_D],[C,D,F,J,M,N,_D],[C,D,F,J,M,_B],[C,D,F,J,M,_B,_C],[C,D,F,J,M,_B,_C,_D],[C,D,F,J,M,_B,_D],[C,D,F,J,M,_C],[C,D,F,J,M,_C,_D],[C,D,F,J,M,_D],[C,D,F,J,_B],[C,D,F,J,_B,_C],[C,D,F,J,_B,_C,_D],[C,D,F,J,_B,_D],[C,D,F,J,_C],[C,D,F,J,_C,_D],[C,D,F,J,_D],[C,D,G,H],[C,D,G,H,J,M],[C,D,G,H,J,M,N],[C,D,G,H,J,M,N,_B],[C,D,G,H,J,M,N,_B,_C],[C,D,G,H,J,M,N,_B,_C,_D],[C,D,G,H,J,M,N,_B,_D],[C,D,G,H,J,M,N,_C],[C,D,G,H,J,M,N,_C,_D],[C,D,G,H,J,M,N,_D],[C,D,G,H,J,M,_B],[C,D,G,H,J,M,_B,_C],[C,D,G,H,J,M,_B,_C,_D],[C,D,G,H,J,M,_B,_D],[C,D,G,H,J,M,_C],[C,D,G,H,J,M,_C,_D],[C,D,G,H,J,M,_D],[C,D,G,H,J,_B],[C,D,G,H,J,_B,_C],[C,D,G,H,J,_B,_C,_D],[C,D,G,H,J,_B,_D],[C,D,G,H,J,_C],[C,D,G,H,J,_C,_D],[C,D,G,H,J,_D],[C,D,G,H,M,N],[C,D,G,J],[C,D,G,J,M],[C,D,G,J,M,N],[C,D,G,J,M,N,_B],[C,D,G,J,M,N,_B,_C],[C,D,G,J,M,N,_B,_C,_D],[C,D,G,J,M,N,_B,_D],[C,D,G,J,M,N,_C],[C,D,G,J,M,N,_C,_D],[C,D,G,J,M,N,_D],[C,D,G,J,M,_B],[C,D,G,J,M,_B,_C],[C,D,G,J,M,_B,_C,_D],[C,D,G,J,M,_B,_D],[C,D,G,J,M,_C],[C,D,G,J,M,_C,_D],[C,D,G,J,M,_D],[C,D,G,J,_B],[C,D,G,J,_B,_C],[C,D,G,J,_B,_C,_D],[C,D,G,J,_B,_D],[C,D,G,J,_C],[C,D,G,J,_C,_D],[C,D,G,J,_D],[C,D,H,J,M],[C,D,H,J,M,N],[C,D,H,J,M,N,_B],[C,D,H,J,M,N,_B,_C],[C,D,H,J,M,N,_B,_C,_D],[C,D,H,J,M,N,_B,_D],[C,D,H,J,M,N,_C],[C,D,H,J,M,N,_C,_D],[C,D,H,J,M,N,_D],[C,D,H,J,M,_B],[C,D,H,J,M,_B,_C],[C,D,H,J,M,_B,_C,_D],[C,D,H,J,M,_B,_D],[C,D,H,J,M,_C],[C,D,H,J,M,_C,_D],[C,D,H,J,M,_D],[C,D,J],[C,D,J,M],[C,D,J,M,N],[C,D,J,M,N,_B],[C,D,J,M,N,_B,_C],[C,D,J,M,N,_B,_C,_D],[C,D,J,M,N,_B,_D],[C,D,J,M,N,_C],[C,D,J,M,N,_C,_D],[C,D,J,M,N,_D],[C,D,J,M,_B],[C,D,J,M,_B,_C],[C,D,J,M,_B,_C,_D],[C,D,J,M,_B,_D],[C,D,J,M,_C],[C,D,J,M,_C,_D],[C,D,J,M,_D],[C,D,J,_B],[C,D,J,_B,_C],[C,D,J,_B,_C,_D],[C,D,J,_B,_D],[C,D,J,_C],[C,D,J,_C,_D],[C,D,J,_D],[C,F,G,H,J,M],[C,F,G,H,J,M,N],[C,F,G,H,J,M,N,_B],[C,F,G,H,J,M,N,_B,_C],[C,F,G,H,J,M,N,_B,_C,_D],[C,F,G,H,J,M,N,_B,_D],[C,F,G,H,J,M,N,_C],[C,F,G,H,J,M,N,_C,_D],[C,F,G,H,J,M,N,_D],[C,F,G,H,J,M,_B],[C,F,G,H,J,M,_B,_C],[C,F,G,H,J,M,_B,_C,_D],[C,F,G,H,J,M,_B,_D],[C,F,G,H,J,M,_C],[C,F,G,H,J,M,_C,_D],[C,F,G,H,J,M,_D],[C,F,G,J],[C,F,G,J,M],[C,F,G,J,M,N],[C,F,G,J,M,N,_B],[C,F,G,J,M,N,_B,_C],[C,F,G,J,M,N,_B,_C,_D],[C,F,G,J,M,N,_B,_D],[C,F,G,J,M,N,_C],[C,F,G,J,M,N,_C,_D],[C,F,G,J,M,N,_D],[C,F,G,J,M,_B],[C,F,G,J,M,_B,_C],[C,F,G,J,M,_B,_C,_D],[C,F,G,J,M,_B,_D],[C,F,G,J,M,_C],[C,F,G,J,M,_C,_D],[C,F,G,J,M,_D],[C,F,G,J,_B],[C,F,G,J,_B,_C],[C,F,G,J,_B,_C,_D],[C,F,G,J,_B,_D],[C,F,G,J,_C],[C,F,G,J,_C,_D],[C,F,G,J,_D],[C,F,H,J,M],[C,F,H,J,M,N],[C,F,H,J,M,N,_B],[C,F,H,J,M,N,_B,_C],[C,F,H,J,M,N,_B,_C,_D],[C,F,H,J,M,N,_B,_D],[C,F,H,J,M,N,_C],[C,F,H,J,M,N,_C,_D],[C,F,H,J,M,N,_D],[C,F,H,J,M,_B],[C,F,H,J,M,_B,_C],[C,F,H,J,M,_B,_C,_D],[C,F,H,J,M,_B,_D],[C,F,H,J,M,_C],[C,F,H,J,M,_C,_D],[C,F,H,J,M,_D],[C,F,J],[C,F,J,M],[C,F,J,M,N],[C,F,J,M,N,_B],[C,F,J,M,N,_B,_C],[C,F,J,M,N,_B,_C,_D],[C,F,J,M,N,_B,_D],[C,F,J,M,N,_C],[C,F,J,M,N,_C,_D],[C,F,J,M,N,_D],[C,F,J,M,_B],[C,F,J,M,_B,_C],[C,F,J,M,_B,_C,_D],[C,F,J,M,_B,_D],[C,F,J,M,_C],[C,F,J,M,_C,_D],[C,F,J,M,_D],[C,F,J,_B],[C,F,J,_B,_C],[C,F,J,_B,_C,_D],[C,F,J,_B,_D],[C,F,J,_C],[C,F,J,_C,_D],[C,F,J,_D],[C,G],[C,G,H,J,M],[C,G,H,J,M,N],[C,G,H,J,M,N,_B],[C,G,H,J,M,N,_B,_C],[C,G,H,J,M,N,_B,_C,_D],[C,G,H,J,M,N,_B,_D],[C,G,H,J,M,N,_C],[C,G,H,J,M,N,_C,_D],[C,G,H,J,M,N,_D],[C,G,H,J,M,_B],[C,G,H,J,M,_B,_C],[C,G,H,J,M,_B,_C,_D],[C,G,H,J,M,_B,_D],[C,G,H,J,M,_C],[C,G,H,J,M,_C,_D],[C,G,H,J,M,_D],[C,G,J],[C,G,J,M],[C,G,J,M,N],[C,G,J,M,N,_B],[C,G,J,M,N,_B,_C],[C,G,J,M,N,_B,_C,_D],[C,G,J,M,N,_B,_D],[C,G,J,M,N,_C],[C,G,J,M,N,_C,_D],[C,G,J,M,N,_D],[C,G,J,M,_B],[C,G,J,M,_B,_C],[C,G,J,M,_B,_C,_D],[C,G,J,M,_B,_D],[C,G,J,M,_C],[C,G,J,M,_C,_D],[C,G,J,M,_D],[C,G,J,_B],[C,G,J,_B,_C],[C,G,J,_B,_C,_D],[C,G,J,_B,_D],[C,G,J,_C],[C,G,J,_C,_D],[C,G,J,_D],[C,G,M,N],[C,H,J,M],[C,H,J,M,N],[C,H,J,M,N,_B],[C,H,J,M,N,_B,_C],[C,H,J,M,N,_B,_C,_D],[C,H,J,M,N,_B,_D],[C,H,J,M,N,_C],[C,H,J,M,N,_C,_D],[C,H,J,M,N,_D],[C,H,J,M,_B],[C,H,J,M,_B,_C],[C,H,J,M,_B,_C,_D],[C,H,J,M,_B,_D],[C,H,J,M,_C],[C,H,J,M,_C,_D],[C,H,J,M,_D],[C,J],[C,J,M],[C,J,M,N],[C,J,M,N,_B],[C,J,M,N,_B,_C],[C,J,M,N,_B,_C,_D],[C,J,M,N,_B,_D],[C,J,M,N,_C],[C,J,M,N,_C,_D],[C,J,M,N,_D],[C,J,M,_B],[C,J,M,_B,_C],[C,J,M,_B,_C,_D],[C,J,M,_B,_D],[C,J,M,_C],[C,J,M,_C,_D],[C,J,M,_D],[C,J,_B],[C,J,_B,_C],[C,J,_B,_C,_D],[C,J,_B,_D],[C,J,_C],[C,J,_C,_D],[C,J,_D],[D],[D,F,G,H,J,M],[D,F,G,H,J,M,N],[D,F,G,H,J,M,N,_B],[D,F,G,H,J,M,N,_B,_C],[D,F,G,H,J,M,N,_B,_C,_D],[D,F,G,H,J,M,N,_B,_D],[D,F,G,H,J,M,N,_C],[D,F,G,H,J,M,N,_C,_D],[D,F,G,H,J,M,N,_D],[D,F,G,H,J,M,_B],[D,F,G,H,J,M,_B,_C],[D,F,G,H,J,M,_B,_C,_D],[D,F,G,H,J,M,_B,_D],[D,F,G,H,J,M,_C],[D,F,G,H,J,M,_C,_D],[D,F,G,H,J,M,_D],[D,F,G,H,M],[D,F,G,H,M,N],[D,F,G,J,M],[D,F,G,J,M,N],[D,F,G,J,M,N,_B],[D,F,G,J,M,N,_B,_C],[D,F,G,J,M,N,_B,_C,_D],[D,F,G,J,M,N,_B,_D],[D,F,G,J,M,N,_C],[D,F,G,J,M,N,_C,_D],[D,F,G,J,M,N,_D],[D,F,G,J,M,_B],[D,F,G,J,M,_B,_C],[D,F,G,J,M,_B,_C,_D],[D,F,G,J,M,_B,_D],[D,F,G,J,M,_C],[D,F,G,J,M,_C,_D],[D,F,G,J,M,_D],[D,F,G,J,_B],[D,F,G,J,_B,_C],[D,F,G,J,_B,_C,_D],[D,F,G,J,_B,_D],[D,F,G,J,_C],[D,F,G,J,_C,_D],[D,F,G,J,_D],[D,F,G,M],[D,F,G,M,N],[D,F,H,J,M],[D,F,H,J,M,N],[D,F,H,J,M,N,_B],[D,F,H,J,M,N,_B,_C],[D,F,H,J,M,N,_B,_C,_D],[D,F,H,J,M,N,_B,_D],[D,F,H,J,M,N,_C],[D,F,H,J,M,N,_C,_D],[D,F,H,J,M,N,_D],[D,F,H,J,M,_B],[D,F,H,J,M,_B,_C],[D,F,H,J,M,_B,_C,_D],[D,F,H,J,M,_B,_D],[D,F,H,J,M,_C],[D,F,H,J,M,_C,_D],[D,F,H,J,M,_D],[D,F,H,M],[D,F,H,M,N],[D,F,J,M],[D,F,J,M,N],[D,F,J,M,N,_B],[D,F,J,M,N,_B,_C],[D,F,J,M,N,_B,_C,_D],[D,F,J,M,N,_B,_D],[D,F,J,M,N,_C],[D,F,J,M,N,_C,_D],[D,F,J,M,N,_D],[D,F,J,M,_B],[D,F,J,M,_B,_C],[D,F,J,M,_B,_C,_D],[D,F,J,M,_B,_D],[D,F,J,M,_C],[D,F,J,M,_C,_D],[D,F,J,M,_D],[D,F,J,_B],[D,F,J,_B,_C],[D,F,J,_B,_C,_D],[D,F,J,_B,_D],[D,F,J,_C],[D,F,J,_C,_D],[D,F,J,_D],[D,F,M],[D,F,M,N],[D,G,H,J,M],[D,G,H,J,M,N],[D,G,H,J,M,N,_B],[D,G,H,J,M,N,_B,_C],[D,G,H,J,M,N,_B,_C,_D],[D,G,H,J,M,N,_B,_D],[D,G,H,J,M,N,_C],[D,G,H,J,M,N,_C,_D],[D,G,H,J,M,N,_D],[D,G,H,J,M,_B],[D,G,H,J,M,_B,_C],[D,G,H,J,M,_B,_C,_D],[D,G,H,J,M,_B,_D],[D,G,H,J,M,_C],[D,G,H,J,M,_C,_D],[D,G,H,J,M,_D],[D,G,H,M],[D,G,H,M,N],[D,G,J,M],[D,G,J,M,N],[D,G,J,M,N,_B],[D,G,J,M,N,_B,_C],[D,G,J,M,N,_B,_C,_D],[D,G,J,M,N,_B,_D],[D,G,J,M,N,_C],[D,G,J,M,N,_C,_D],[D,G,J,M,N,_D],[D,G,J,M,_B],[D,G,J,M,_B,_C],[D,G,J,M,_B,_C,_D],[D,G,J,M,_B,_D],[D,G,J,M,_C],[D,G,J,M,_C,_D],[D,G,J,M,_D],[D,G,J,_B],[D,G,J,_B,_C],[D,G,J,_B,_C,_D],[D,G,J,_B,_D],[D,G,J,_C],[D,G,J,_C,_D],[D,G,J,_D],[D,G,M],[D,G,M,N],[D,H],[D,H,J,M],[D,H,J,M,N],[D,H,J,M,N,_B],[D,H,J,M,N,_B,_C],[D,H,J,M,N,_B,_C,_D],[D,H,J,M,N,_B,_D],[D,H,J,M,N,_C],[D,H,J,M,N,_C,_D],[D,H,J,M,N,_D],[D,H,J,M,_B],[D,H,J,M,_B,_C],[D,H,J,M,_B,_C,_D],[D,H,J,M,_B,_D],[D,H,J,M,_C],[D,H,J,M,_C,_D],[D,H,J,M,_D],[D,H,J,_B],[D,H,J,_B,_C],[D,H,J,_B,_C,_D],[D,H,J,_B,_D],[D,H,J,_C],[D,H,J,_C,_D],[D,H,J,_D],[D,H,M],[D,H,M,N],[D,J,M],[D,J,M,N],[D,J,M,N,_B],[D,J,M,N,_B,_C],[D,J,M,N,_B,_C,_D],[D,J,M,N,_B,_D],[D,J,M,N,_C],[D,J,M,N,_C,_D],[D,J,M,N,_D],[D,J,M,_B],[D,J,M,_B,_C],[D,J,M,_B,_C,_D],[D,J,M,_B,_D],[D,J,M,_C],[D,J,M,_C,_D],[D,J,M,_D],[D,J,_B],[D,J,_B,_C],[D,J,_B,_C,_D],[D,J,_B,_D],[D,J,_C],[D,J,_C,_D],[D,J,_D],[D,M],[D,M,N],[_A,I,J],[F],[F,G],[F,G,H,J,M],[F,G,H,J,M,N],[F,G,H,J,M,N,_B],[F,G,H,J,M,N,_B,_C],[F,G,H,J,M,N,_B,_C,_D],[F,G,H,J,M,N,_B,_D],[F,G,H,J,M,N,_C],[F,G,H,J,M,N,_C,_D],[F,G,H,J,M,N,_D],[F,G,H,J,M,_B],[F,G,H,J,M,_B,_C],[F,G,H,J,M,_B,_C,_D],[F,G,H,J,M,_B,_D],[F,G,H,J,M,_C],[F,G,H,J,M,_C,_D],[F,G,H,J,M,_D],[F,G,H,M],[F,G,H,M,N],[F,G,J],[F,G,J,M],[F,G,J,M,N],[F,G,J,M,N,_B],[F,G,J,M,N,_B,_C],[F,G,J,M,N,_B,_C,_D],[F,G,J,M,N,_B,_D],[F,G,J,M,N,_C],[F,G,J,M,N,_C,_D],[F,G,J,M,N,_D],[F,G,J,M,_B],[F,G,J,M,_B,_C],[F,G,J,M,_B,_C,_D],[F,G,J,M,_B,_D],[F,G,J,M,_C],[F,G,J,M,_C,_D],[F,G,J,M,_D],[F,G,J,_B],[F,G,J,_B,_C],[F,G,J,_B,_C,_D],[F,G,J,_B,_D],[F,G,J,_C],[F,G,J,_C,_D],[F,G,J,_D],[F,G,M],[F,G,M,N],[F,H,J,M],[F,H,J,M,N],[F,H,J,M,N,_B],[F,H,J,M,N,_B,_C],[F,H,J,M,N,_B,_C,_D],[F,H,J,M,N,_B,_D],[F,H,J,M,N,_C],[F,H,J,M,N,_C,_D],[F,H,J,M,N,_D],[F,H,J,M,_B],[F,H,J,M,_B,_C],[F,H,J,M,_B,_C,_D],[F,H,J,M,_B,_D],[F,H,J,M,_C],[F,H,J,M,_C,_D],[F,H,J,M,_D],[F,H,M],[F,H,M,N],[F,J],[F,J,M],[F,J,M,N],[F,J,M,N,_B],[F,J,M,N,_B,_C],[F,J,M,N,_B,_C,_D],[F,J,M,N,_B,_D],[F,J,M,N,_C],[F,J,M,N,_C,_D],[F,J,M,N,_D],[F,J,M,_B],[F,J,M,_B,_C],[F,J,M,_B,_C,_D],[F,J,M,_B,_D],[F,J,M,_C],[F,J,M,_C,_D],[F,J,M,_D],[F,J,_B],[F,J,_B,_C],[F,J,_B,_C,_D],[F,J,_B,_D],[F,J,_C],[F,J,_C,_D],[F,J,_D],[F,M],[F,M,N],[G],[G,H,J,M],[G,H,J,M,N],[G,H,J,M,N,_B],[G,H,J,M,N,_B,_C],[G,H,J,M,N,_B,_C,_D],[G,H,J,M,N,_B,_D],[G,H,J,M,N,_C],[G,H,J,M,N,_C,_D],[G,H,J,M,N,_D],[G,H,J,M,_B],[G,H,J,M,_B,_C],[G,H,J,M,_B,_C,_D],[G,H,J,M,_B,_D],[G,H,J,M,_C],[G,H,J,M,_C,_D],[G,H,J,M,_D],[G,H,M],[G,H,M,N],[G,J],[G,J,M],[G,J,M,N],[G,J,M,N,_B],[G,J,M,N,_B,_C],[G,J,M,N,_B,_C,_D],[G,J,M,N,_B,_D],[G,J,M,N,_C],[G,J,M,N,_C,_D],[G,J,M,N,_D],[G,J,M,_B],[G,J,M,_B,_C],[G,J,M,_B,_C,_D],[G,J,M,_B,_D],[G,J,M,_C],[G,J,M,_C,_D],[G,J,M,_D],[G,J,_B],[G,J,_B,_C],[G,J,_B,_C,_D],[G,J,_B,_D],[G,J,_C],[G,J,_C,_D],[G,J,_D],[G,M],[G,M,N],[H,J,M],[H,J,M,N],[H,J,M,N,_B],[H,J,M,N,_B,_C],[H,J,M,N,_B,_C,_D],[H,J,M,N,_B,_D],[H,J,M,N,_C],[H,J,M,N,_C,_D],[H,J,M,N,_D],[H,J,M,_B],[H,J,M,_B,_C],[H,J,M,_B,_C,_D],[H,J,M,_B,_D],[H,J,M,_C],[H,J,M,_C,_D],[H,J,M,_D],[H,M],[H,M,N],[I,J],[J],[J,M],[J,M,N],[J,M,N,_B],[J,M,N,_B,_C],[J,M,N,_B,_C,_D],[J,M,N,_B,_D],[J,M,N,_C],[J,M,N,_C,_D],[J,M,N,_D],[J,M,_B],[J,M,_B,_C],[J,M,_B,_C,_D],[J,M,_B,_D],[J,M,_C],[J,M,_C,_D],[J,M,_D],[J,_B],[J,_B,_C],[J,_B,_C,_D],[J,_B,_D],[J,_C],[J,_C,_D],[J,_D],[M],[M,N]]),
        ground([K,L]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (_A=E),
       mshare([[B],[B,C],[C],[_A],[F],[H],[I],[J],[L],[N]]),
       ground([D,G,K,M]), linear(_A), linear(F), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,J],[B,F],[B,J],[C,J],[_A,I,J],[F],[I,J],[J]]),
        ground([D,G,H,K,L,M,N]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (E=[pp(poss,np(_B,_C,_D))|_A]),
       mshare([[B],[B,C],[C],[_A],[F],[H],[I],[J],[L],[N],[_B],[_B,_C],[_C]]),
       ground([D,G,K,M,_D]), linear(_A), linear(F), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,J],[B,C,J,_B],[B,C,J,_B,_C],[B,C,J,_C],[B,F],[B,J],[B,J,_B],[B,J,_B,_C],[B,J,_C],[C,J],[C,J,_B],[C,J,_B,_C],[C,J,_C],[_A,I,J],[F],[I,J],[J],[J,_B],[J,_B,_C],[J,_C]]),
        ground([D,G,H,K,L,M,N,_D]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (E=[pp(poss,np(_B,_C,_D))|_A]),
       mshare([[B],[B,C],[C],[_A],[F],[H],[I],[J],[L],[N],[_B],[_B,_C],[_C],[_D]]),
       ground([D,G,K,M]), linear(_A), linear(F), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,J],[B,C,J,_B],[B,C,J,_B,_C],[B,C,J,_B,_C,_D],[B,C,J,_B,_D],[B,C,J,_C],[B,C,J,_C,_D],[B,C,J,_D],[B,F],[B,J],[B,J,_B],[B,J,_B,_C],[B,J,_B,_C,_D],[B,J,_B,_D],[B,J,_C],[B,J,_C,_D],[B,J,_D],[C,J],[C,J,_B],[C,J,_B,_C],[C,J,_B,_C,_D],[C,J,_B,_D],[C,J,_C],[C,J,_C,_D],[C,J,_D],[_A,I,J],[F],[I,J],[J],[J,_B],[J,_B,_C],[J,_B,_C,_D],[J,_B,_D],[J,_C],[J,_C,_D],[J,_D]]),
        ground([D,G,H,K,L,M,N]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (_A=E),
       mshare([[B],[B,C],[C],[_A],[F],[G],[H],[I],[J],[L],[N]]),
       ground([D,K,M]), linear(_A), linear(F), linear(G), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,F,G],[B,C,J],[B,F],[B,J],[C,G],[C,J],[_A,I,J],[F],[F,G],[G],[I,J],[J]]),
        ground([D,H,K,L,M,N]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (E=[pp(poss,np(_B,_C,_D))|_A]),
       mshare([[B],[B,C],[C],[_A],[F],[G],[H],[I],[J],[L],[N],[_B],[_B,_C],[_C]]),
       ground([D,K,M,_D]), linear(_A), linear(F), linear(G), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,F,G],[B,C,J],[B,C,J,_B],[B,C,J,_B,_C],[B,C,J,_C],[B,F],[B,J],[B,J,_B],[B,J,_B,_C],[B,J,_C],[C,G],[C,J],[C,J,_B],[C,J,_B,_C],[C,J,_C],[_A,I,J],[F],[F,G],[G],[I,J],[J],[J,_B],[J,_B,_C],[J,_C]]),
        ground([D,H,K,L,M,N,_D]), linear(I) ).

:- true pred possessive(B,C,D,_A,E,F,G,H,I,J,K,L,M,N)
   : ( (E=[pp(poss,np(_B,_C,_D))|_A]),
       mshare([[B],[B,C],[C],[_A],[F],[G],[H],[I],[J],[L],[N],[_B],[_B,_C],[_C],[_D]]),
       ground([D,K,M]), linear(_A), linear(F), linear(G), linear(H), linear(I), linear(J), linear(L), linear(N) )
   => ( mshare([[B,C,F,G],[B,C,J],[B,C,J,_B],[B,C,J,_B,_C],[B,C,J,_B,_C,_D],[B,C,J,_B,_D],[B,C,J,_C],[B,C,J,_C,_D],[B,C,J,_D],[B,F],[B,J],[B,J,_B],[B,J,_B,_C],[B,J,_B,_C,_D],[B,J,_B,_D],[B,J,_C],[B,J,_C,_D],[B,J,_D],[C,G],[C,J],[C,J,_B],[C,J,_B,_C],[C,J,_B,_C,_D],[C,J,_B,_D],[C,J,_C],[C,J,_C,_D],[C,J,_D],[_A,I,J],[F],[F,G],[G],[I,J],[J],[J,_B],[J,_B,_C],[J,_B,_C,_D],[J,_B,_D],[J,_C],[J,_C,_D],[J,_D]]),
        ground([D,H,K,L,M,N]), linear(I) ).

possessive(B,C,D,[],E,F,G,H,I,J,K,L,M,N) :-
    true((mshare([[B],[B,C],[B,C,D],[B,C,D,E],[B,C,D,E,G],[B,C,D,E,G,M],[B,C,D,E,M],[B,C,D,G],[B,C,D,G,M],[B,C,D,M],[B,C,E],[B,C,E,G],[B,C,E,G,M],[B,C,E,M],[B,C,G],[B,C,G,M],[B,C,M],[B,D],[B,D,E],[B,D,E,G],[B,D,E,G,M],[B,D,E,M],[B,D,G],[B,D,G,M],[B,D,M],[B,E],[B,E,G],[B,E,G,M],[B,E,M],[B,G],[B,G,M],[B,M],[C],[C,D],[C,D,E],[C,D,E,G],[C,D,E,G,M],[C,D,E,M],[C,D,G],[C,D,G,M],[C,D,M],[C,E],[C,E,G],[C,E,G,M],[C,E,M],[C,G],[C,G,M],[C,M],[D],[D,E],[D,E,G],[D,E,G,M],[D,E,M],[D,G],[D,G,M],[D,M],[E],[E,G],[E,G,M],[E,M],[F],[G],[G,M],[H],[I],[J],[L],[M],[N],[O],[P],[Q],[R],[S],[T],[U],[V]]),ground([K]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,E],[B,C,D,E,M],[B,C,D,M],[B,C,E],[B,C,E,M],[B,C,M],[B,D],[B,D,E],[B,D,E,M],[B,D,M],[B,E],[B,E,M],[B,M],[C],[C,D],[C,D,E],[C,D,E,M],[C,D,M],[C,E],[C,E,M],[C,M],[D],[D,E],[D,E,M],[D,M],[E],[E,M],[F],[G],[H],[I],[J],[L],[M],[N],[O],[P],[Q],[R],[S],[T],[U],[V]]),ground([K]),linear(F),linear(G),linear(H),linear(I),linear(J),linear(L),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,E],[B,C,D,E,M],[B,C,D,M],[B,C,E],[B,C,E,M],[B,C,M],[B,D],[B,D,E],[B,D,E,M],[B,D,M],[B,E],[B,E,M],[B,M],[C],[C,D],[C,D,E],[C,D,E,M],[C,D,M],[C,E],[C,E,M],[C,M],[D],[D,E],[D,E,M],[D,M],[E],[E,M],[F],[H],[I],[J],[L],[M],[N],[O],[P],[Q],[R],[S],[T],[U],[V]]),ground([G,K]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,G],[B,C,D,G,M],[B,C,D,M],[B,C,G],[B,C,G,M],[B,C,M],[B,D],[B,D,G],[B,D,G,M],[B,D,M],[B,G],[B,G,M],[B,M],[C],[C,D],[C,D,G],[C,D,G,M],[C,D,M],[C,G],[C,G,M],[C,M],[D],[D,G],[D,G,M],[D,M],[F],[G],[G,M],[H],[I],[J],[L],[M],[N],[O],[P],[Q],[R],[S],[T],[U],[V]]),ground([E,K]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,M],[B,C,M],[B,D],[B,D,M],[B,M],[C],[C,D],[C,D,M],[C,M],[D],[D,M],[F],[G],[H],[I],[J],[L],[M],[N],[O],[P],[Q],[R],[S],[T],[U],[V]]),ground([E,K]),linear(F),linear(G),linear(H),linear(I),linear(J),linear(L),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,M],[B,C,M],[B,D],[B,D,M],[B,M],[C],[C,D],[C,D,M],[C,M],[D],[D,M],[F],[H],[I],[J],[L],[M],[N],[O],[P],[Q],[R],[S],[T],[U],[V]]),ground([E,G,K]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[C],[E],[F],[G],[H],[I],[J],[L],[N],[O],[P],[Q],[R],[S],[T],[U],[V]]),ground([D,K,M]),linear(F),linear(G),linear(H),linear(I),linear(J),linear(L),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[C],[E],[F],[H],[I],[J],[L],[N],[O],[P],[Q],[R],[S],[T],[U],[V]]),ground([D,G,K,M]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[C],[F],[G],[H],[I],[J],[L],[N],[O],[P],[Q],[R],[S],[T],[U],[V]]),ground([D,E,K,M]),linear(F),linear(G),linear(H),linear(I),linear(J),linear(L),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[C],[F],[H],[I],[J],[L],[N],[O],[P],[Q],[R],[S],[T],[U],[V]]),ground([D,E,G,K,M]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V))),
    gen_case(K,O,M,P),
    true((mshare([[B],[B,C],[B,C,D],[B,C,D,E],[B,C,D,E,G],[B,C,D,E,G,M],[B,C,D,E,G,M,P],[B,C,D,E,M],[B,C,D,E,M,P],[B,C,D,G],[B,C,D,G,M],[B,C,D,G,M,P],[B,C,D,M],[B,C,D,M,P],[B,C,E],[B,C,E,G],[B,C,E,G,M],[B,C,E,G,M,P],[B,C,E,M],[B,C,E,M,P],[B,C,G],[B,C,G,M],[B,C,G,M,P],[B,C,M],[B,C,M,P],[B,D],[B,D,E],[B,D,E,G],[B,D,E,G,M],[B,D,E,G,M,P],[B,D,E,M],[B,D,E,M,P],[B,D,G],[B,D,G,M],[B,D,G,M,P],[B,D,M],[B,D,M,P],[B,E],[B,E,G],[B,E,G,M],[B,E,G,M,P],[B,E,M],[B,E,M,P],[B,G],[B,G,M],[B,G,M,P],[B,M],[B,M,P],[C],[C,D],[C,D,E],[C,D,E,G],[C,D,E,G,M],[C,D,E,G,M,P],[C,D,E,M],[C,D,E,M,P],[C,D,G],[C,D,G,M],[C,D,G,M,P],[C,D,M],[C,D,M,P],[C,E],[C,E,G],[C,E,G,M],[C,E,G,M,P],[C,E,M],[C,E,M,P],[C,G],[C,G,M],[C,G,M,P],[C,M],[C,M,P],[D],[D,E],[D,E,G],[D,E,G,M],[D,E,G,M,P],[D,E,M],[D,E,M,P],[D,G],[D,G,M],[D,G,M,P],[D,M],[D,M,P],[E],[E,G],[E,G,M],[E,G,M,P],[E,M],[E,M,P],[F],[G],[G,M],[G,M,P],[H],[I],[J],[L],[M],[M,P],[N],[Q],[R],[S],[T],[U],[V]]),ground([K,O]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,E],[B,C,D,E,M],[B,C,D,E,M,P],[B,C,D,M],[B,C,D,M,P],[B,C,E],[B,C,E,M],[B,C,E,M,P],[B,C,M],[B,C,M,P],[B,D],[B,D,E],[B,D,E,M],[B,D,E,M,P],[B,D,M],[B,D,M,P],[B,E],[B,E,M],[B,E,M,P],[B,M],[B,M,P],[C],[C,D],[C,D,E],[C,D,E,M],[C,D,E,M,P],[C,D,M],[C,D,M,P],[C,E],[C,E,M],[C,E,M,P],[C,M],[C,M,P],[D],[D,E],[D,E,M],[D,E,M,P],[D,M],[D,M,P],[E],[E,M],[E,M,P],[F],[G],[H],[I],[J],[L],[M],[M,P],[N],[Q],[R],[S],[T],[U],[V]]),ground([K,O]),linear(F),linear(G),linear(H),linear(I),linear(J),linear(L),linear(N),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,E],[B,C,D,E,M],[B,C,D,E,M,P],[B,C,D,M],[B,C,D,M,P],[B,C,E],[B,C,E,M],[B,C,E,M,P],[B,C,M],[B,C,M,P],[B,D],[B,D,E],[B,D,E,M],[B,D,E,M,P],[B,D,M],[B,D,M,P],[B,E],[B,E,M],[B,E,M,P],[B,M],[B,M,P],[C],[C,D],[C,D,E],[C,D,E,M],[C,D,E,M,P],[C,D,M],[C,D,M,P],[C,E],[C,E,M],[C,E,M,P],[C,M],[C,M,P],[D],[D,E],[D,E,M],[D,E,M,P],[D,M],[D,M,P],[E],[E,M],[E,M,P],[F],[H],[I],[J],[L],[M],[M,P],[N],[Q],[R],[S],[T],[U],[V]]),ground([G,K,O]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,G],[B,C,D,G,M],[B,C,D,G,M,P],[B,C,D,M],[B,C,D,M,P],[B,C,G],[B,C,G,M],[B,C,G,M,P],[B,C,M],[B,C,M,P],[B,D],[B,D,G],[B,D,G,M],[B,D,G,M,P],[B,D,M],[B,D,M,P],[B,G],[B,G,M],[B,G,M,P],[B,M],[B,M,P],[C],[C,D],[C,D,G],[C,D,G,M],[C,D,G,M,P],[C,D,M],[C,D,M,P],[C,G],[C,G,M],[C,G,M,P],[C,M],[C,M,P],[D],[D,G],[D,G,M],[D,G,M,P],[D,M],[D,M,P],[F],[G],[G,M],[G,M,P],[H],[I],[J],[L],[M],[M,P],[N],[Q],[R],[S],[T],[U],[V]]),ground([E,K,O]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[C],[C,D],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[F],[G],[H],[I],[J],[L],[M],[M,P],[N],[Q],[R],[S],[T],[U],[V]]),ground([E,K,O]),linear(F),linear(G),linear(H),linear(I),linear(J),linear(L),linear(N),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[C],[C,D],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[F],[H],[I],[J],[L],[M],[M,P],[N],[Q],[R],[S],[T],[U],[V]]),ground([E,G,K,O]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[C],[E],[F],[G],[H],[I],[J],[L],[N],[Q],[R],[S],[T],[U],[V]]),ground([D,K,M,O,P]),linear(F),linear(G),linear(H),linear(I),linear(J),linear(L),linear(N),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[C],[E],[F],[H],[I],[J],[L],[N],[Q],[R],[S],[T],[U],[V]]),ground([D,G,K,M,O,P]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[C],[F],[G],[H],[I],[J],[L],[N],[Q],[R],[S],[T],[U],[V]]),ground([D,E,K,M,O,P]),linear(F),linear(G),linear(H),linear(I),linear(J),linear(L),linear(N),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V);mshare([[B],[B,C],[C],[F],[H],[I],[J],[L],[N],[Q],[R],[S],[T],[U],[V]]),ground([D,E,G,K,M,O,P]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(Q),linear(R),linear(S),linear(T),linear(U),linear(V))),
    np_head0(Q,R,S,O,T,P,U),
    true((mshare([[B],[B,C],[B,C,D],[B,C,D,E],[B,C,D,E,G],[B,C,D,E,G,M],[B,C,D,E,G,M,P],[B,C,D,E,G,M,P,Q],[B,C,D,E,G,M,P,Q,R],[B,C,D,E,G,M,P,Q,R,S],[B,C,D,E,G,M,P,Q,R,S,U],[B,C,D,E,G,M,P,Q,R,U],[B,C,D,E,G,M,P,Q,S],[B,C,D,E,G,M,P,Q,S,U],[B,C,D,E,G,M,P,Q,U],[B,C,D,E,G,M,P,R],[B,C,D,E,G,M,P,R,S],[B,C,D,E,G,M,P,R,S,U],[B,C,D,E,G,M,P,R,U],[B,C,D,E,G,M,P,S],[B,C,D,E,G,M,P,S,U],[B,C,D,E,G,M,P,U],[B,C,D,E,M],[B,C,D,E,M,P],[B,C,D,E,M,P,Q],[B,C,D,E,M,P,Q,R],[B,C,D,E,M,P,Q,R,S],[B,C,D,E,M,P,Q,R,S,U],[B,C,D,E,M,P,Q,R,U],[B,C,D,E,M,P,Q,S],[B,C,D,E,M,P,Q,S,U],[B,C,D,E,M,P,Q,U],[B,C,D,E,M,P,R],[B,C,D,E,M,P,R,S],[B,C,D,E,M,P,R,S,U],[B,C,D,E,M,P,R,U],[B,C,D,E,M,P,S],[B,C,D,E,M,P,S,U],[B,C,D,E,M,P,U],[B,C,D,G],[B,C,D,G,M],[B,C,D,G,M,P],[B,C,D,G,M,P,Q],[B,C,D,G,M,P,Q,R],[B,C,D,G,M,P,Q,R,S],[B,C,D,G,M,P,Q,R,S,U],[B,C,D,G,M,P,Q,R,U],[B,C,D,G,M,P,Q,S],[B,C,D,G,M,P,Q,S,U],[B,C,D,G,M,P,Q,U],[B,C,D,G,M,P,R],[B,C,D,G,M,P,R,S],[B,C,D,G,M,P,R,S,U],[B,C,D,G,M,P,R,U],[B,C,D,G,M,P,S],[B,C,D,G,M,P,S,U],[B,C,D,G,M,P,U],[B,C,D,M],[B,C,D,M,P],[B,C,D,M,P,Q],[B,C,D,M,P,Q,R],[B,C,D,M,P,Q,R,S],[B,C,D,M,P,Q,R,S,U],[B,C,D,M,P,Q,R,U],[B,C,D,M,P,Q,S],[B,C,D,M,P,Q,S,U],[B,C,D,M,P,Q,U],[B,C,D,M,P,R],[B,C,D,M,P,R,S],[B,C,D,M,P,R,S,U],[B,C,D,M,P,R,U],[B,C,D,M,P,S],[B,C,D,M,P,S,U],[B,C,D,M,P,U],[B,C,E],[B,C,E,G],[B,C,E,G,M],[B,C,E,G,M,P],[B,C,E,G,M,P,Q],[B,C,E,G,M,P,Q,R],[B,C,E,G,M,P,Q,R,S],[B,C,E,G,M,P,Q,R,S,U],[B,C,E,G,M,P,Q,R,U],[B,C,E,G,M,P,Q,S],[B,C,E,G,M,P,Q,S,U],[B,C,E,G,M,P,Q,U],[B,C,E,G,M,P,R],[B,C,E,G,M,P,R,S],[B,C,E,G,M,P,R,S,U],[B,C,E,G,M,P,R,U],[B,C,E,G,M,P,S],[B,C,E,G,M,P,S,U],[B,C,E,G,M,P,U],[B,C,E,M],[B,C,E,M,P],[B,C,E,M,P,Q],[B,C,E,M,P,Q,R],[B,C,E,M,P,Q,R,S],[B,C,E,M,P,Q,R,S,U],[B,C,E,M,P,Q,R,U],[B,C,E,M,P,Q,S],[B,C,E,M,P,Q,S,U],[B,C,E,M,P,Q,U],[B,C,E,M,P,R],[B,C,E,M,P,R,S],[B,C,E,M,P,R,S,U],[B,C,E,M,P,R,U],[B,C,E,M,P,S],[B,C,E,M,P,S,U],[B,C,E,M,P,U],[B,C,G],[B,C,G,M],[B,C,G,M,P],[B,C,G,M,P,Q],[B,C,G,M,P,Q,R],[B,C,G,M,P,Q,R,S],[B,C,G,M,P,Q,R,S,U],[B,C,G,M,P,Q,R,U],[B,C,G,M,P,Q,S],[B,C,G,M,P,Q,S,U],[B,C,G,M,P,Q,U],[B,C,G,M,P,R],[B,C,G,M,P,R,S],[B,C,G,M,P,R,S,U],[B,C,G,M,P,R,U],[B,C,G,M,P,S],[B,C,G,M,P,S,U],[B,C,G,M,P,U],[B,C,M],[B,C,M,P],[B,C,M,P,Q],[B,C,M,P,Q,R],[B,C,M,P,Q,R,S],[B,C,M,P,Q,R,S,U],[B,C,M,P,Q,R,U],[B,C,M,P,Q,S],[B,C,M,P,Q,S,U],[B,C,M,P,Q,U],[B,C,M,P,R],[B,C,M,P,R,S],[B,C,M,P,R,S,U],[B,C,M,P,R,U],[B,C,M,P,S],[B,C,M,P,S,U],[B,C,M,P,U],[B,D],[B,D,E],[B,D,E,G],[B,D,E,G,M],[B,D,E,G,M,P],[B,D,E,G,M,P,Q],[B,D,E,G,M,P,Q,R],[B,D,E,G,M,P,Q,R,S],[B,D,E,G,M,P,Q,R,S,U],[B,D,E,G,M,P,Q,R,U],[B,D,E,G,M,P,Q,S],[B,D,E,G,M,P,Q,S,U],[B,D,E,G,M,P,Q,U],[B,D,E,G,M,P,R],[B,D,E,G,M,P,R,S],[B,D,E,G,M,P,R,S,U],[B,D,E,G,M,P,R,U],[B,D,E,G,M,P,S],[B,D,E,G,M,P,S,U],[B,D,E,G,M,P,U],[B,D,E,M],[B,D,E,M,P],[B,D,E,M,P,Q],[B,D,E,M,P,Q,R],[B,D,E,M,P,Q,R,S],[B,D,E,M,P,Q,R,S,U],[B,D,E,M,P,Q,R,U],[B,D,E,M,P,Q,S],[B,D,E,M,P,Q,S,U],[B,D,E,M,P,Q,U],[B,D,E,M,P,R],[B,D,E,M,P,R,S],[B,D,E,M,P,R,S,U],[B,D,E,M,P,R,U],[B,D,E,M,P,S],[B,D,E,M,P,S,U],[B,D,E,M,P,U],[B,D,G],[B,D,G,M],[B,D,G,M,P],[B,D,G,M,P,Q],[B,D,G,M,P,Q,R],[B,D,G,M,P,Q,R,S],[B,D,G,M,P,Q,R,S,U],[B,D,G,M,P,Q,R,U],[B,D,G,M,P,Q,S],[B,D,G,M,P,Q,S,U],[B,D,G,M,P,Q,U],[B,D,G,M,P,R],[B,D,G,M,P,R,S],[B,D,G,M,P,R,S,U],[B,D,G,M,P,R,U],[B,D,G,M,P,S],[B,D,G,M,P,S,U],[B,D,G,M,P,U],[B,D,M],[B,D,M,P],[B,D,M,P,Q],[B,D,M,P,Q,R],[B,D,M,P,Q,R,S],[B,D,M,P,Q,R,S,U],[B,D,M,P,Q,R,U],[B,D,M,P,Q,S],[B,D,M,P,Q,S,U],[B,D,M,P,Q,U],[B,D,M,P,R],[B,D,M,P,R,S],[B,D,M,P,R,S,U],[B,D,M,P,R,U],[B,D,M,P,S],[B,D,M,P,S,U],[B,D,M,P,U],[B,E],[B,E,G],[B,E,G,M],[B,E,G,M,P],[B,E,G,M,P,Q],[B,E,G,M,P,Q,R],[B,E,G,M,P,Q,R,S],[B,E,G,M,P,Q,R,S,U],[B,E,G,M,P,Q,R,U],[B,E,G,M,P,Q,S],[B,E,G,M,P,Q,S,U],[B,E,G,M,P,Q,U],[B,E,G,M,P,R],[B,E,G,M,P,R,S],[B,E,G,M,P,R,S,U],[B,E,G,M,P,R,U],[B,E,G,M,P,S],[B,E,G,M,P,S,U],[B,E,G,M,P,U],[B,E,M],[B,E,M,P],[B,E,M,P,Q],[B,E,M,P,Q,R],[B,E,M,P,Q,R,S],[B,E,M,P,Q,R,S,U],[B,E,M,P,Q,R,U],[B,E,M,P,Q,S],[B,E,M,P,Q,S,U],[B,E,M,P,Q,U],[B,E,M,P,R],[B,E,M,P,R,S],[B,E,M,P,R,S,U],[B,E,M,P,R,U],[B,E,M,P,S],[B,E,M,P,S,U],[B,E,M,P,U],[B,G],[B,G,M],[B,G,M,P],[B,G,M,P,Q],[B,G,M,P,Q,R],[B,G,M,P,Q,R,S],[B,G,M,P,Q,R,S,U],[B,G,M,P,Q,R,U],[B,G,M,P,Q,S],[B,G,M,P,Q,S,U],[B,G,M,P,Q,U],[B,G,M,P,R],[B,G,M,P,R,S],[B,G,M,P,R,S,U],[B,G,M,P,R,U],[B,G,M,P,S],[B,G,M,P,S,U],[B,G,M,P,U],[B,M],[B,M,P],[B,M,P,Q],[B,M,P,Q,R],[B,M,P,Q,R,S],[B,M,P,Q,R,S,U],[B,M,P,Q,R,U],[B,M,P,Q,S],[B,M,P,Q,S,U],[B,M,P,Q,U],[B,M,P,R],[B,M,P,R,S],[B,M,P,R,S,U],[B,M,P,R,U],[B,M,P,S],[B,M,P,S,U],[B,M,P,U],[C],[C,D],[C,D,E],[C,D,E,G],[C,D,E,G,M],[C,D,E,G,M,P],[C,D,E,G,M,P,Q],[C,D,E,G,M,P,Q,R],[C,D,E,G,M,P,Q,R,S],[C,D,E,G,M,P,Q,R,S,U],[C,D,E,G,M,P,Q,R,U],[C,D,E,G,M,P,Q,S],[C,D,E,G,M,P,Q,S,U],[C,D,E,G,M,P,Q,U],[C,D,E,G,M,P,R],[C,D,E,G,M,P,R,S],[C,D,E,G,M,P,R,S,U],[C,D,E,G,M,P,R,U],[C,D,E,G,M,P,S],[C,D,E,G,M,P,S,U],[C,D,E,G,M,P,U],[C,D,E,M],[C,D,E,M,P],[C,D,E,M,P,Q],[C,D,E,M,P,Q,R],[C,D,E,M,P,Q,R,S],[C,D,E,M,P,Q,R,S,U],[C,D,E,M,P,Q,R,U],[C,D,E,M,P,Q,S],[C,D,E,M,P,Q,S,U],[C,D,E,M,P,Q,U],[C,D,E,M,P,R],[C,D,E,M,P,R,S],[C,D,E,M,P,R,S,U],[C,D,E,M,P,R,U],[C,D,E,M,P,S],[C,D,E,M,P,S,U],[C,D,E,M,P,U],[C,D,G],[C,D,G,M],[C,D,G,M,P],[C,D,G,M,P,Q],[C,D,G,M,P,Q,R],[C,D,G,M,P,Q,R,S],[C,D,G,M,P,Q,R,S,U],[C,D,G,M,P,Q,R,U],[C,D,G,M,P,Q,S],[C,D,G,M,P,Q,S,U],[C,D,G,M,P,Q,U],[C,D,G,M,P,R],[C,D,G,M,P,R,S],[C,D,G,M,P,R,S,U],[C,D,G,M,P,R,U],[C,D,G,M,P,S],[C,D,G,M,P,S,U],[C,D,G,M,P,U],[C,D,M],[C,D,M,P],[C,D,M,P,Q],[C,D,M,P,Q,R],[C,D,M,P,Q,R,S],[C,D,M,P,Q,R,S,U],[C,D,M,P,Q,R,U],[C,D,M,P,Q,S],[C,D,M,P,Q,S,U],[C,D,M,P,Q,U],[C,D,M,P,R],[C,D,M,P,R,S],[C,D,M,P,R,S,U],[C,D,M,P,R,U],[C,D,M,P,S],[C,D,M,P,S,U],[C,D,M,P,U],[C,E],[C,E,G],[C,E,G,M],[C,E,G,M,P],[C,E,G,M,P,Q],[C,E,G,M,P,Q,R],[C,E,G,M,P,Q,R,S],[C,E,G,M,P,Q,R,S,U],[C,E,G,M,P,Q,R,U],[C,E,G,M,P,Q,S],[C,E,G,M,P,Q,S,U],[C,E,G,M,P,Q,U],[C,E,G,M,P,R],[C,E,G,M,P,R,S],[C,E,G,M,P,R,S,U],[C,E,G,M,P,R,U],[C,E,G,M,P,S],[C,E,G,M,P,S,U],[C,E,G,M,P,U],[C,E,M],[C,E,M,P],[C,E,M,P,Q],[C,E,M,P,Q,R],[C,E,M,P,Q,R,S],[C,E,M,P,Q,R,S,U],[C,E,M,P,Q,R,U],[C,E,M,P,Q,S],[C,E,M,P,Q,S,U],[C,E,M,P,Q,U],[C,E,M,P,R],[C,E,M,P,R,S],[C,E,M,P,R,S,U],[C,E,M,P,R,U],[C,E,M,P,S],[C,E,M,P,S,U],[C,E,M,P,U],[C,G],[C,G,M],[C,G,M,P],[C,G,M,P,Q],[C,G,M,P,Q,R],[C,G,M,P,Q,R,S],[C,G,M,P,Q,R,S,U],[C,G,M,P,Q,R,U],[C,G,M,P,Q,S],[C,G,M,P,Q,S,U],[C,G,M,P,Q,U],[C,G,M,P,R],[C,G,M,P,R,S],[C,G,M,P,R,S,U],[C,G,M,P,R,U],[C,G,M,P,S],[C,G,M,P,S,U],[C,G,M,P,U],[C,M],[C,M,P],[C,M,P,Q],[C,M,P,Q,R],[C,M,P,Q,R,S],[C,M,P,Q,R,S,U],[C,M,P,Q,R,U],[C,M,P,Q,S],[C,M,P,Q,S,U],[C,M,P,Q,U],[C,M,P,R],[C,M,P,R,S],[C,M,P,R,S,U],[C,M,P,R,U],[C,M,P,S],[C,M,P,S,U],[C,M,P,U],[D],[D,E],[D,E,G],[D,E,G,M],[D,E,G,M,P],[D,E,G,M,P,Q],[D,E,G,M,P,Q,R],[D,E,G,M,P,Q,R,S],[D,E,G,M,P,Q,R,S,U],[D,E,G,M,P,Q,R,U],[D,E,G,M,P,Q,S],[D,E,G,M,P,Q,S,U],[D,E,G,M,P,Q,U],[D,E,G,M,P,R],[D,E,G,M,P,R,S],[D,E,G,M,P,R,S,U],[D,E,G,M,P,R,U],[D,E,G,M,P,S],[D,E,G,M,P,S,U],[D,E,G,M,P,U],[D,E,M],[D,E,M,P],[D,E,M,P,Q],[D,E,M,P,Q,R],[D,E,M,P,Q,R,S],[D,E,M,P,Q,R,S,U],[D,E,M,P,Q,R,U],[D,E,M,P,Q,S],[D,E,M,P,Q,S,U],[D,E,M,P,Q,U],[D,E,M,P,R],[D,E,M,P,R,S],[D,E,M,P,R,S,U],[D,E,M,P,R,U],[D,E,M,P,S],[D,E,M,P,S,U],[D,E,M,P,U],[D,G],[D,G,M],[D,G,M,P],[D,G,M,P,Q],[D,G,M,P,Q,R],[D,G,M,P,Q,R,S],[D,G,M,P,Q,R,S,U],[D,G,M,P,Q,R,U],[D,G,M,P,Q,S],[D,G,M,P,Q,S,U],[D,G,M,P,Q,U],[D,G,M,P,R],[D,G,M,P,R,S],[D,G,M,P,R,S,U],[D,G,M,P,R,U],[D,G,M,P,S],[D,G,M,P,S,U],[D,G,M,P,U],[D,M],[D,M,P],[D,M,P,Q],[D,M,P,Q,R],[D,M,P,Q,R,S],[D,M,P,Q,R,S,U],[D,M,P,Q,R,U],[D,M,P,Q,S],[D,M,P,Q,S,U],[D,M,P,Q,U],[D,M,P,R],[D,M,P,R,S],[D,M,P,R,S,U],[D,M,P,R,U],[D,M,P,S],[D,M,P,S,U],[D,M,P,U],[E],[E,G],[E,G,M],[E,G,M,P],[E,G,M,P,Q],[E,G,M,P,Q,R],[E,G,M,P,Q,R,S],[E,G,M,P,Q,R,S,U],[E,G,M,P,Q,R,U],[E,G,M,P,Q,S],[E,G,M,P,Q,S,U],[E,G,M,P,Q,U],[E,G,M,P,R],[E,G,M,P,R,S],[E,G,M,P,R,S,U],[E,G,M,P,R,U],[E,G,M,P,S],[E,G,M,P,S,U],[E,G,M,P,U],[E,M],[E,M,P],[E,M,P,Q],[E,M,P,Q,R],[E,M,P,Q,R,S],[E,M,P,Q,R,S,U],[E,M,P,Q,R,U],[E,M,P,Q,S],[E,M,P,Q,S,U],[E,M,P,Q,U],[E,M,P,R],[E,M,P,R,S],[E,M,P,R,S,U],[E,M,P,R,U],[E,M,P,S],[E,M,P,S,U],[E,M,P,U],[F],[G],[G,M],[G,M,P],[G,M,P,Q],[G,M,P,Q,R],[G,M,P,Q,R,S],[G,M,P,Q,R,S,U],[G,M,P,Q,R,U],[G,M,P,Q,S],[G,M,P,Q,S,U],[G,M,P,Q,U],[G,M,P,R],[G,M,P,R,S],[G,M,P,R,S,U],[G,M,P,R,U],[G,M,P,S],[G,M,P,S,U],[G,M,P,U],[H],[I],[J],[L],[M],[M,P],[M,P,Q],[M,P,Q,R],[M,P,Q,R,S],[M,P,Q,R,S,U],[M,P,Q,R,U],[M,P,Q,S],[M,P,Q,S,U],[M,P,Q,U],[M,P,R],[M,P,R,S],[M,P,R,S,U],[M,P,R,U],[M,P,S],[M,P,S,U],[M,P,U],[N],[Q],[Q,R],[R],[V]]),ground([K,O,T]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,E],[B,C,D,E,M],[B,C,D,E,M,P],[B,C,D,E,M,P,Q],[B,C,D,E,M,P,Q,R],[B,C,D,E,M,P,Q,R,S],[B,C,D,E,M,P,Q,R,S,U],[B,C,D,E,M,P,Q,R,U],[B,C,D,E,M,P,Q,S],[B,C,D,E,M,P,Q,S,U],[B,C,D,E,M,P,Q,U],[B,C,D,E,M,P,R],[B,C,D,E,M,P,R,S],[B,C,D,E,M,P,R,S,U],[B,C,D,E,M,P,R,U],[B,C,D,E,M,P,S],[B,C,D,E,M,P,S,U],[B,C,D,E,M,P,U],[B,C,D,M],[B,C,D,M,P],[B,C,D,M,P,Q],[B,C,D,M,P,Q,R],[B,C,D,M,P,Q,R,S],[B,C,D,M,P,Q,R,S,U],[B,C,D,M,P,Q,R,U],[B,C,D,M,P,Q,S],[B,C,D,M,P,Q,S,U],[B,C,D,M,P,Q,U],[B,C,D,M,P,R],[B,C,D,M,P,R,S],[B,C,D,M,P,R,S,U],[B,C,D,M,P,R,U],[B,C,D,M,P,S],[B,C,D,M,P,S,U],[B,C,D,M,P,U],[B,C,E],[B,C,E,M],[B,C,E,M,P],[B,C,E,M,P,Q],[B,C,E,M,P,Q,R],[B,C,E,M,P,Q,R,S],[B,C,E,M,P,Q,R,S,U],[B,C,E,M,P,Q,R,U],[B,C,E,M,P,Q,S],[B,C,E,M,P,Q,S,U],[B,C,E,M,P,Q,U],[B,C,E,M,P,R],[B,C,E,M,P,R,S],[B,C,E,M,P,R,S,U],[B,C,E,M,P,R,U],[B,C,E,M,P,S],[B,C,E,M,P,S,U],[B,C,E,M,P,U],[B,C,M],[B,C,M,P],[B,C,M,P,Q],[B,C,M,P,Q,R],[B,C,M,P,Q,R,S],[B,C,M,P,Q,R,S,U],[B,C,M,P,Q,R,U],[B,C,M,P,Q,S],[B,C,M,P,Q,S,U],[B,C,M,P,Q,U],[B,C,M,P,R],[B,C,M,P,R,S],[B,C,M,P,R,S,U],[B,C,M,P,R,U],[B,C,M,P,S],[B,C,M,P,S,U],[B,C,M,P,U],[B,D],[B,D,E],[B,D,E,M],[B,D,E,M,P],[B,D,E,M,P,Q],[B,D,E,M,P,Q,R],[B,D,E,M,P,Q,R,S],[B,D,E,M,P,Q,R,S,U],[B,D,E,M,P,Q,R,U],[B,D,E,M,P,Q,S],[B,D,E,M,P,Q,S,U],[B,D,E,M,P,Q,U],[B,D,E,M,P,R],[B,D,E,M,P,R,S],[B,D,E,M,P,R,S,U],[B,D,E,M,P,R,U],[B,D,E,M,P,S],[B,D,E,M,P,S,U],[B,D,E,M,P,U],[B,D,M],[B,D,M,P],[B,D,M,P,Q],[B,D,M,P,Q,R],[B,D,M,P,Q,R,S],[B,D,M,P,Q,R,S,U],[B,D,M,P,Q,R,U],[B,D,M,P,Q,S],[B,D,M,P,Q,S,U],[B,D,M,P,Q,U],[B,D,M,P,R],[B,D,M,P,R,S],[B,D,M,P,R,S,U],[B,D,M,P,R,U],[B,D,M,P,S],[B,D,M,P,S,U],[B,D,M,P,U],[B,E],[B,E,M],[B,E,M,P],[B,E,M,P,Q],[B,E,M,P,Q,R],[B,E,M,P,Q,R,S],[B,E,M,P,Q,R,S,U],[B,E,M,P,Q,R,U],[B,E,M,P,Q,S],[B,E,M,P,Q,S,U],[B,E,M,P,Q,U],[B,E,M,P,R],[B,E,M,P,R,S],[B,E,M,P,R,S,U],[B,E,M,P,R,U],[B,E,M,P,S],[B,E,M,P,S,U],[B,E,M,P,U],[B,M],[B,M,P],[B,M,P,Q],[B,M,P,Q,R],[B,M,P,Q,R,S],[B,M,P,Q,R,S,U],[B,M,P,Q,R,U],[B,M,P,Q,S],[B,M,P,Q,S,U],[B,M,P,Q,U],[B,M,P,R],[B,M,P,R,S],[B,M,P,R,S,U],[B,M,P,R,U],[B,M,P,S],[B,M,P,S,U],[B,M,P,U],[C],[C,D],[C,D,E],[C,D,E,M],[C,D,E,M,P],[C,D,E,M,P,Q],[C,D,E,M,P,Q,R],[C,D,E,M,P,Q,R,S],[C,D,E,M,P,Q,R,S,U],[C,D,E,M,P,Q,R,U],[C,D,E,M,P,Q,S],[C,D,E,M,P,Q,S,U],[C,D,E,M,P,Q,U],[C,D,E,M,P,R],[C,D,E,M,P,R,S],[C,D,E,M,P,R,S,U],[C,D,E,M,P,R,U],[C,D,E,M,P,S],[C,D,E,M,P,S,U],[C,D,E,M,P,U],[C,D,M],[C,D,M,P],[C,D,M,P,Q],[C,D,M,P,Q,R],[C,D,M,P,Q,R,S],[C,D,M,P,Q,R,S,U],[C,D,M,P,Q,R,U],[C,D,M,P,Q,S],[C,D,M,P,Q,S,U],[C,D,M,P,Q,U],[C,D,M,P,R],[C,D,M,P,R,S],[C,D,M,P,R,S,U],[C,D,M,P,R,U],[C,D,M,P,S],[C,D,M,P,S,U],[C,D,M,P,U],[C,E],[C,E,M],[C,E,M,P],[C,E,M,P,Q],[C,E,M,P,Q,R],[C,E,M,P,Q,R,S],[C,E,M,P,Q,R,S,U],[C,E,M,P,Q,R,U],[C,E,M,P,Q,S],[C,E,M,P,Q,S,U],[C,E,M,P,Q,U],[C,E,M,P,R],[C,E,M,P,R,S],[C,E,M,P,R,S,U],[C,E,M,P,R,U],[C,E,M,P,S],[C,E,M,P,S,U],[C,E,M,P,U],[C,M],[C,M,P],[C,M,P,Q],[C,M,P,Q,R],[C,M,P,Q,R,S],[C,M,P,Q,R,S,U],[C,M,P,Q,R,U],[C,M,P,Q,S],[C,M,P,Q,S,U],[C,M,P,Q,U],[C,M,P,R],[C,M,P,R,S],[C,M,P,R,S,U],[C,M,P,R,U],[C,M,P,S],[C,M,P,S,U],[C,M,P,U],[D],[D,E],[D,E,M],[D,E,M,P],[D,E,M,P,Q],[D,E,M,P,Q,R],[D,E,M,P,Q,R,S],[D,E,M,P,Q,R,S,U],[D,E,M,P,Q,R,U],[D,E,M,P,Q,S],[D,E,M,P,Q,S,U],[D,E,M,P,Q,U],[D,E,M,P,R],[D,E,M,P,R,S],[D,E,M,P,R,S,U],[D,E,M,P,R,U],[D,E,M,P,S],[D,E,M,P,S,U],[D,E,M,P,U],[D,M],[D,M,P],[D,M,P,Q],[D,M,P,Q,R],[D,M,P,Q,R,S],[D,M,P,Q,R,S,U],[D,M,P,Q,R,U],[D,M,P,Q,S],[D,M,P,Q,S,U],[D,M,P,Q,U],[D,M,P,R],[D,M,P,R,S],[D,M,P,R,S,U],[D,M,P,R,U],[D,M,P,S],[D,M,P,S,U],[D,M,P,U],[E],[E,M],[E,M,P],[E,M,P,Q],[E,M,P,Q,R],[E,M,P,Q,R,S],[E,M,P,Q,R,S,U],[E,M,P,Q,R,U],[E,M,P,Q,S],[E,M,P,Q,S,U],[E,M,P,Q,U],[E,M,P,R],[E,M,P,R,S],[E,M,P,R,S,U],[E,M,P,R,U],[E,M,P,S],[E,M,P,S,U],[E,M,P,U],[F],[G],[H],[I],[J],[L],[M],[M,P],[M,P,Q],[M,P,Q,R],[M,P,Q,R,S],[M,P,Q,R,S,U],[M,P,Q,R,U],[M,P,Q,S],[M,P,Q,S,U],[M,P,Q,U],[M,P,R],[M,P,R,S],[M,P,R,S,U],[M,P,R,U],[M,P,S],[M,P,S,U],[M,P,U],[N],[Q],[Q,R],[R],[V]]),ground([K,O,T]),linear(F),linear(G),linear(H),linear(I),linear(J),linear(L),linear(N),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,E],[B,C,D,E,M],[B,C,D,E,M,P],[B,C,D,E,M,P,Q],[B,C,D,E,M,P,Q,R],[B,C,D,E,M,P,Q,R,S],[B,C,D,E,M,P,Q,R,S,U],[B,C,D,E,M,P,Q,R,U],[B,C,D,E,M,P,Q,S],[B,C,D,E,M,P,Q,S,U],[B,C,D,E,M,P,Q,U],[B,C,D,E,M,P,R],[B,C,D,E,M,P,R,S],[B,C,D,E,M,P,R,S,U],[B,C,D,E,M,P,R,U],[B,C,D,E,M,P,S],[B,C,D,E,M,P,S,U],[B,C,D,E,M,P,U],[B,C,D,M],[B,C,D,M,P],[B,C,D,M,P,Q],[B,C,D,M,P,Q,R],[B,C,D,M,P,Q,R,S],[B,C,D,M,P,Q,R,S,U],[B,C,D,M,P,Q,R,U],[B,C,D,M,P,Q,S],[B,C,D,M,P,Q,S,U],[B,C,D,M,P,Q,U],[B,C,D,M,P,R],[B,C,D,M,P,R,S],[B,C,D,M,P,R,S,U],[B,C,D,M,P,R,U],[B,C,D,M,P,S],[B,C,D,M,P,S,U],[B,C,D,M,P,U],[B,C,E],[B,C,E,M],[B,C,E,M,P],[B,C,E,M,P,Q],[B,C,E,M,P,Q,R],[B,C,E,M,P,Q,R,S],[B,C,E,M,P,Q,R,S,U],[B,C,E,M,P,Q,R,U],[B,C,E,M,P,Q,S],[B,C,E,M,P,Q,S,U],[B,C,E,M,P,Q,U],[B,C,E,M,P,R],[B,C,E,M,P,R,S],[B,C,E,M,P,R,S,U],[B,C,E,M,P,R,U],[B,C,E,M,P,S],[B,C,E,M,P,S,U],[B,C,E,M,P,U],[B,C,M],[B,C,M,P],[B,C,M,P,Q],[B,C,M,P,Q,R],[B,C,M,P,Q,R,S],[B,C,M,P,Q,R,S,U],[B,C,M,P,Q,R,U],[B,C,M,P,Q,S],[B,C,M,P,Q,S,U],[B,C,M,P,Q,U],[B,C,M,P,R],[B,C,M,P,R,S],[B,C,M,P,R,S,U],[B,C,M,P,R,U],[B,C,M,P,S],[B,C,M,P,S,U],[B,C,M,P,U],[B,D],[B,D,E],[B,D,E,M],[B,D,E,M,P],[B,D,E,M,P,Q],[B,D,E,M,P,Q,R],[B,D,E,M,P,Q,R,S],[B,D,E,M,P,Q,R,S,U],[B,D,E,M,P,Q,R,U],[B,D,E,M,P,Q,S],[B,D,E,M,P,Q,S,U],[B,D,E,M,P,Q,U],[B,D,E,M,P,R],[B,D,E,M,P,R,S],[B,D,E,M,P,R,S,U],[B,D,E,M,P,R,U],[B,D,E,M,P,S],[B,D,E,M,P,S,U],[B,D,E,M,P,U],[B,D,M],[B,D,M,P],[B,D,M,P,Q],[B,D,M,P,Q,R],[B,D,M,P,Q,R,S],[B,D,M,P,Q,R,S,U],[B,D,M,P,Q,R,U],[B,D,M,P,Q,S],[B,D,M,P,Q,S,U],[B,D,M,P,Q,U],[B,D,M,P,R],[B,D,M,P,R,S],[B,D,M,P,R,S,U],[B,D,M,P,R,U],[B,D,M,P,S],[B,D,M,P,S,U],[B,D,M,P,U],[B,E],[B,E,M],[B,E,M,P],[B,E,M,P,Q],[B,E,M,P,Q,R],[B,E,M,P,Q,R,S],[B,E,M,P,Q,R,S,U],[B,E,M,P,Q,R,U],[B,E,M,P,Q,S],[B,E,M,P,Q,S,U],[B,E,M,P,Q,U],[B,E,M,P,R],[B,E,M,P,R,S],[B,E,M,P,R,S,U],[B,E,M,P,R,U],[B,E,M,P,S],[B,E,M,P,S,U],[B,E,M,P,U],[B,M],[B,M,P],[B,M,P,Q],[B,M,P,Q,R],[B,M,P,Q,R,S],[B,M,P,Q,R,S,U],[B,M,P,Q,R,U],[B,M,P,Q,S],[B,M,P,Q,S,U],[B,M,P,Q,U],[B,M,P,R],[B,M,P,R,S],[B,M,P,R,S,U],[B,M,P,R,U],[B,M,P,S],[B,M,P,S,U],[B,M,P,U],[C],[C,D],[C,D,E],[C,D,E,M],[C,D,E,M,P],[C,D,E,M,P,Q],[C,D,E,M,P,Q,R],[C,D,E,M,P,Q,R,S],[C,D,E,M,P,Q,R,S,U],[C,D,E,M,P,Q,R,U],[C,D,E,M,P,Q,S],[C,D,E,M,P,Q,S,U],[C,D,E,M,P,Q,U],[C,D,E,M,P,R],[C,D,E,M,P,R,S],[C,D,E,M,P,R,S,U],[C,D,E,M,P,R,U],[C,D,E,M,P,S],[C,D,E,M,P,S,U],[C,D,E,M,P,U],[C,D,M],[C,D,M,P],[C,D,M,P,Q],[C,D,M,P,Q,R],[C,D,M,P,Q,R,S],[C,D,M,P,Q,R,S,U],[C,D,M,P,Q,R,U],[C,D,M,P,Q,S],[C,D,M,P,Q,S,U],[C,D,M,P,Q,U],[C,D,M,P,R],[C,D,M,P,R,S],[C,D,M,P,R,S,U],[C,D,M,P,R,U],[C,D,M,P,S],[C,D,M,P,S,U],[C,D,M,P,U],[C,E],[C,E,M],[C,E,M,P],[C,E,M,P,Q],[C,E,M,P,Q,R],[C,E,M,P,Q,R,S],[C,E,M,P,Q,R,S,U],[C,E,M,P,Q,R,U],[C,E,M,P,Q,S],[C,E,M,P,Q,S,U],[C,E,M,P,Q,U],[C,E,M,P,R],[C,E,M,P,R,S],[C,E,M,P,R,S,U],[C,E,M,P,R,U],[C,E,M,P,S],[C,E,M,P,S,U],[C,E,M,P,U],[C,M],[C,M,P],[C,M,P,Q],[C,M,P,Q,R],[C,M,P,Q,R,S],[C,M,P,Q,R,S,U],[C,M,P,Q,R,U],[C,M,P,Q,S],[C,M,P,Q,S,U],[C,M,P,Q,U],[C,M,P,R],[C,M,P,R,S],[C,M,P,R,S,U],[C,M,P,R,U],[C,M,P,S],[C,M,P,S,U],[C,M,P,U],[D],[D,E],[D,E,M],[D,E,M,P],[D,E,M,P,Q],[D,E,M,P,Q,R],[D,E,M,P,Q,R,S],[D,E,M,P,Q,R,S,U],[D,E,M,P,Q,R,U],[D,E,M,P,Q,S],[D,E,M,P,Q,S,U],[D,E,M,P,Q,U],[D,E,M,P,R],[D,E,M,P,R,S],[D,E,M,P,R,S,U],[D,E,M,P,R,U],[D,E,M,P,S],[D,E,M,P,S,U],[D,E,M,P,U],[D,M],[D,M,P],[D,M,P,Q],[D,M,P,Q,R],[D,M,P,Q,R,S],[D,M,P,Q,R,S,U],[D,M,P,Q,R,U],[D,M,P,Q,S],[D,M,P,Q,S,U],[D,M,P,Q,U],[D,M,P,R],[D,M,P,R,S],[D,M,P,R,S,U],[D,M,P,R,U],[D,M,P,S],[D,M,P,S,U],[D,M,P,U],[E],[E,M],[E,M,P],[E,M,P,Q],[E,M,P,Q,R],[E,M,P,Q,R,S],[E,M,P,Q,R,S,U],[E,M,P,Q,R,U],[E,M,P,Q,S],[E,M,P,Q,S,U],[E,M,P,Q,U],[E,M,P,R],[E,M,P,R,S],[E,M,P,R,S,U],[E,M,P,R,U],[E,M,P,S],[E,M,P,S,U],[E,M,P,U],[F],[H],[I],[J],[L],[M],[M,P],[M,P,Q],[M,P,Q,R],[M,P,Q,R,S],[M,P,Q,R,S,U],[M,P,Q,R,U],[M,P,Q,S],[M,P,Q,S,U],[M,P,Q,U],[M,P,R],[M,P,R,S],[M,P,R,S,U],[M,P,R,U],[M,P,S],[M,P,S,U],[M,P,U],[N],[Q],[Q,R],[R],[V]]),ground([G,K,O,T]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,G],[B,C,D,G,M],[B,C,D,G,M,P],[B,C,D,G,M,P,Q],[B,C,D,G,M,P,Q,R],[B,C,D,G,M,P,Q,R,S],[B,C,D,G,M,P,Q,R,S,U],[B,C,D,G,M,P,Q,R,U],[B,C,D,G,M,P,Q,S],[B,C,D,G,M,P,Q,S,U],[B,C,D,G,M,P,Q,U],[B,C,D,G,M,P,R],[B,C,D,G,M,P,R,S],[B,C,D,G,M,P,R,S,U],[B,C,D,G,M,P,R,U],[B,C,D,G,M,P,S],[B,C,D,G,M,P,S,U],[B,C,D,G,M,P,U],[B,C,D,M],[B,C,D,M,P],[B,C,D,M,P,Q],[B,C,D,M,P,Q,R],[B,C,D,M,P,Q,R,S],[B,C,D,M,P,Q,R,S,U],[B,C,D,M,P,Q,R,U],[B,C,D,M,P,Q,S],[B,C,D,M,P,Q,S,U],[B,C,D,M,P,Q,U],[B,C,D,M,P,R],[B,C,D,M,P,R,S],[B,C,D,M,P,R,S,U],[B,C,D,M,P,R,U],[B,C,D,M,P,S],[B,C,D,M,P,S,U],[B,C,D,M,P,U],[B,C,G],[B,C,G,M],[B,C,G,M,P],[B,C,G,M,P,Q],[B,C,G,M,P,Q,R],[B,C,G,M,P,Q,R,S],[B,C,G,M,P,Q,R,S,U],[B,C,G,M,P,Q,R,U],[B,C,G,M,P,Q,S],[B,C,G,M,P,Q,S,U],[B,C,G,M,P,Q,U],[B,C,G,M,P,R],[B,C,G,M,P,R,S],[B,C,G,M,P,R,S,U],[B,C,G,M,P,R,U],[B,C,G,M,P,S],[B,C,G,M,P,S,U],[B,C,G,M,P,U],[B,C,M],[B,C,M,P],[B,C,M,P,Q],[B,C,M,P,Q,R],[B,C,M,P,Q,R,S],[B,C,M,P,Q,R,S,U],[B,C,M,P,Q,R,U],[B,C,M,P,Q,S],[B,C,M,P,Q,S,U],[B,C,M,P,Q,U],[B,C,M,P,R],[B,C,M,P,R,S],[B,C,M,P,R,S,U],[B,C,M,P,R,U],[B,C,M,P,S],[B,C,M,P,S,U],[B,C,M,P,U],[B,D],[B,D,G],[B,D,G,M],[B,D,G,M,P],[B,D,G,M,P,Q],[B,D,G,M,P,Q,R],[B,D,G,M,P,Q,R,S],[B,D,G,M,P,Q,R,S,U],[B,D,G,M,P,Q,R,U],[B,D,G,M,P,Q,S],[B,D,G,M,P,Q,S,U],[B,D,G,M,P,Q,U],[B,D,G,M,P,R],[B,D,G,M,P,R,S],[B,D,G,M,P,R,S,U],[B,D,G,M,P,R,U],[B,D,G,M,P,S],[B,D,G,M,P,S,U],[B,D,G,M,P,U],[B,D,M],[B,D,M,P],[B,D,M,P,Q],[B,D,M,P,Q,R],[B,D,M,P,Q,R,S],[B,D,M,P,Q,R,S,U],[B,D,M,P,Q,R,U],[B,D,M,P,Q,S],[B,D,M,P,Q,S,U],[B,D,M,P,Q,U],[B,D,M,P,R],[B,D,M,P,R,S],[B,D,M,P,R,S,U],[B,D,M,P,R,U],[B,D,M,P,S],[B,D,M,P,S,U],[B,D,M,P,U],[B,G],[B,G,M],[B,G,M,P],[B,G,M,P,Q],[B,G,M,P,Q,R],[B,G,M,P,Q,R,S],[B,G,M,P,Q,R,S,U],[B,G,M,P,Q,R,U],[B,G,M,P,Q,S],[B,G,M,P,Q,S,U],[B,G,M,P,Q,U],[B,G,M,P,R],[B,G,M,P,R,S],[B,G,M,P,R,S,U],[B,G,M,P,R,U],[B,G,M,P,S],[B,G,M,P,S,U],[B,G,M,P,U],[B,M],[B,M,P],[B,M,P,Q],[B,M,P,Q,R],[B,M,P,Q,R,S],[B,M,P,Q,R,S,U],[B,M,P,Q,R,U],[B,M,P,Q,S],[B,M,P,Q,S,U],[B,M,P,Q,U],[B,M,P,R],[B,M,P,R,S],[B,M,P,R,S,U],[B,M,P,R,U],[B,M,P,S],[B,M,P,S,U],[B,M,P,U],[C],[C,D],[C,D,G],[C,D,G,M],[C,D,G,M,P],[C,D,G,M,P,Q],[C,D,G,M,P,Q,R],[C,D,G,M,P,Q,R,S],[C,D,G,M,P,Q,R,S,U],[C,D,G,M,P,Q,R,U],[C,D,G,M,P,Q,S],[C,D,G,M,P,Q,S,U],[C,D,G,M,P,Q,U],[C,D,G,M,P,R],[C,D,G,M,P,R,S],[C,D,G,M,P,R,S,U],[C,D,G,M,P,R,U],[C,D,G,M,P,S],[C,D,G,M,P,S,U],[C,D,G,M,P,U],[C,D,M],[C,D,M,P],[C,D,M,P,Q],[C,D,M,P,Q,R],[C,D,M,P,Q,R,S],[C,D,M,P,Q,R,S,U],[C,D,M,P,Q,R,U],[C,D,M,P,Q,S],[C,D,M,P,Q,S,U],[C,D,M,P,Q,U],[C,D,M,P,R],[C,D,M,P,R,S],[C,D,M,P,R,S,U],[C,D,M,P,R,U],[C,D,M,P,S],[C,D,M,P,S,U],[C,D,M,P,U],[C,G],[C,G,M],[C,G,M,P],[C,G,M,P,Q],[C,G,M,P,Q,R],[C,G,M,P,Q,R,S],[C,G,M,P,Q,R,S,U],[C,G,M,P,Q,R,U],[C,G,M,P,Q,S],[C,G,M,P,Q,S,U],[C,G,M,P,Q,U],[C,G,M,P,R],[C,G,M,P,R,S],[C,G,M,P,R,S,U],[C,G,M,P,R,U],[C,G,M,P,S],[C,G,M,P,S,U],[C,G,M,P,U],[C,M],[C,M,P],[C,M,P,Q],[C,M,P,Q,R],[C,M,P,Q,R,S],[C,M,P,Q,R,S,U],[C,M,P,Q,R,U],[C,M,P,Q,S],[C,M,P,Q,S,U],[C,M,P,Q,U],[C,M,P,R],[C,M,P,R,S],[C,M,P,R,S,U],[C,M,P,R,U],[C,M,P,S],[C,M,P,S,U],[C,M,P,U],[D],[D,G],[D,G,M],[D,G,M,P],[D,G,M,P,Q],[D,G,M,P,Q,R],[D,G,M,P,Q,R,S],[D,G,M,P,Q,R,S,U],[D,G,M,P,Q,R,U],[D,G,M,P,Q,S],[D,G,M,P,Q,S,U],[D,G,M,P,Q,U],[D,G,M,P,R],[D,G,M,P,R,S],[D,G,M,P,R,S,U],[D,G,M,P,R,U],[D,G,M,P,S],[D,G,M,P,S,U],[D,G,M,P,U],[D,M],[D,M,P],[D,M,P,Q],[D,M,P,Q,R],[D,M,P,Q,R,S],[D,M,P,Q,R,S,U],[D,M,P,Q,R,U],[D,M,P,Q,S],[D,M,P,Q,S,U],[D,M,P,Q,U],[D,M,P,R],[D,M,P,R,S],[D,M,P,R,S,U],[D,M,P,R,U],[D,M,P,S],[D,M,P,S,U],[D,M,P,U],[F],[G],[G,M],[G,M,P],[G,M,P,Q],[G,M,P,Q,R],[G,M,P,Q,R,S],[G,M,P,Q,R,S,U],[G,M,P,Q,R,U],[G,M,P,Q,S],[G,M,P,Q,S,U],[G,M,P,Q,U],[G,M,P,R],[G,M,P,R,S],[G,M,P,R,S,U],[G,M,P,R,U],[G,M,P,S],[G,M,P,S,U],[G,M,P,U],[H],[I],[J],[L],[M],[M,P],[M,P,Q],[M,P,Q,R],[M,P,Q,R,S],[M,P,Q,R,S,U],[M,P,Q,R,U],[M,P,Q,S],[M,P,Q,S,U],[M,P,Q,U],[M,P,R],[M,P,R,S],[M,P,R,S,U],[M,P,R,U],[M,P,S],[M,P,S,U],[M,P,U],[N],[Q],[Q,R],[R],[V]]),ground([E,K,O,T]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,M],[B,C,D,M,P],[B,C,D,M,P,Q],[B,C,D,M,P,Q,R],[B,C,D,M,P,Q,R,S],[B,C,D,M,P,Q,R,S,U],[B,C,D,M,P,Q,R,U],[B,C,D,M,P,Q,S],[B,C,D,M,P,Q,S,U],[B,C,D,M,P,Q,U],[B,C,D,M,P,R],[B,C,D,M,P,R,S],[B,C,D,M,P,R,S,U],[B,C,D,M,P,R,U],[B,C,D,M,P,S],[B,C,D,M,P,S,U],[B,C,D,M,P,U],[B,C,M],[B,C,M,P],[B,C,M,P,Q],[B,C,M,P,Q,R],[B,C,M,P,Q,R,S],[B,C,M,P,Q,R,S,U],[B,C,M,P,Q,R,U],[B,C,M,P,Q,S],[B,C,M,P,Q,S,U],[B,C,M,P,Q,U],[B,C,M,P,R],[B,C,M,P,R,S],[B,C,M,P,R,S,U],[B,C,M,P,R,U],[B,C,M,P,S],[B,C,M,P,S,U],[B,C,M,P,U],[B,D],[B,D,M],[B,D,M,P],[B,D,M,P,Q],[B,D,M,P,Q,R],[B,D,M,P,Q,R,S],[B,D,M,P,Q,R,S,U],[B,D,M,P,Q,R,U],[B,D,M,P,Q,S],[B,D,M,P,Q,S,U],[B,D,M,P,Q,U],[B,D,M,P,R],[B,D,M,P,R,S],[B,D,M,P,R,S,U],[B,D,M,P,R,U],[B,D,M,P,S],[B,D,M,P,S,U],[B,D,M,P,U],[B,M],[B,M,P],[B,M,P,Q],[B,M,P,Q,R],[B,M,P,Q,R,S],[B,M,P,Q,R,S,U],[B,M,P,Q,R,U],[B,M,P,Q,S],[B,M,P,Q,S,U],[B,M,P,Q,U],[B,M,P,R],[B,M,P,R,S],[B,M,P,R,S,U],[B,M,P,R,U],[B,M,P,S],[B,M,P,S,U],[B,M,P,U],[C],[C,D],[C,D,M],[C,D,M,P],[C,D,M,P,Q],[C,D,M,P,Q,R],[C,D,M,P,Q,R,S],[C,D,M,P,Q,R,S,U],[C,D,M,P,Q,R,U],[C,D,M,P,Q,S],[C,D,M,P,Q,S,U],[C,D,M,P,Q,U],[C,D,M,P,R],[C,D,M,P,R,S],[C,D,M,P,R,S,U],[C,D,M,P,R,U],[C,D,M,P,S],[C,D,M,P,S,U],[C,D,M,P,U],[C,M],[C,M,P],[C,M,P,Q],[C,M,P,Q,R],[C,M,P,Q,R,S],[C,M,P,Q,R,S,U],[C,M,P,Q,R,U],[C,M,P,Q,S],[C,M,P,Q,S,U],[C,M,P,Q,U],[C,M,P,R],[C,M,P,R,S],[C,M,P,R,S,U],[C,M,P,R,U],[C,M,P,S],[C,M,P,S,U],[C,M,P,U],[D],[D,M],[D,M,P],[D,M,P,Q],[D,M,P,Q,R],[D,M,P,Q,R,S],[D,M,P,Q,R,S,U],[D,M,P,Q,R,U],[D,M,P,Q,S],[D,M,P,Q,S,U],[D,M,P,Q,U],[D,M,P,R],[D,M,P,R,S],[D,M,P,R,S,U],[D,M,P,R,U],[D,M,P,S],[D,M,P,S,U],[D,M,P,U],[F],[G],[H],[I],[J],[L],[M],[M,P],[M,P,Q],[M,P,Q,R],[M,P,Q,R,S],[M,P,Q,R,S,U],[M,P,Q,R,U],[M,P,Q,S],[M,P,Q,S,U],[M,P,Q,U],[M,P,R],[M,P,R,S],[M,P,R,S,U],[M,P,R,U],[M,P,S],[M,P,S,U],[M,P,U],[N],[Q],[Q,R],[R],[V]]),ground([E,K,O,T]),linear(F),linear(G),linear(H),linear(I),linear(J),linear(L),linear(N),linear(V);mshare([[B],[B,C],[B,C,D],[B,C,D,M],[B,C,D,M,P],[B,C,D,M,P,Q],[B,C,D,M,P,Q,R],[B,C,D,M,P,Q,R,S],[B,C,D,M,P,Q,R,S,U],[B,C,D,M,P,Q,R,U],[B,C,D,M,P,Q,S],[B,C,D,M,P,Q,S,U],[B,C,D,M,P,Q,U],[B,C,D,M,P,R],[B,C,D,M,P,R,S],[B,C,D,M,P,R,S,U],[B,C,D,M,P,R,U],[B,C,D,M,P,S],[B,C,D,M,P,S,U],[B,C,D,M,P,U],[B,C,M],[B,C,M,P],[B,C,M,P,Q],[B,C,M,P,Q,R],[B,C,M,P,Q,R,S],[B,C,M,P,Q,R,S,U],[B,C,M,P,Q,R,U],[B,C,M,P,Q,S],[B,C,M,P,Q,S,U],[B,C,M,P,Q,U],[B,C,M,P,R],[B,C,M,P,R,S],[B,C,M,P,R,S,U],[B,C,M,P,R,U],[B,C,M,P,S],[B,C,M,P,S,U],[B,C,M,P,U],[B,D],[B,D,M],[B,D,M,P],[B,D,M,P,Q],[B,D,M,P,Q,R],[B,D,M,P,Q,R,S],[B,D,M,P,Q,R,S,U],[B,D,M,P,Q,R,U],[B,D,M,P,Q,S],[B,D,M,P,Q,S,U],[B,D,M,P,Q,U],[B,D,M,P,R],[B,D,M,P,R,S],[B,D,M,P,R,S,U],[B,D,M,P,R,U],[B,D,M,P,S],[B,D,M,P,S,U],[B,D,M,P,U],[B,M],[B,M,P],[B,M,P,Q],[B,M,P,Q,R],[B,M,P,Q,R,S],[B,M,P,Q,R,S,U],[B,M,P,Q,R,U],[B,M,P,Q,S],[B,M,P,Q,S,U],[B,M,P,Q,U],[B,M,P,R],[B,M,P,R,S],[B,M,P,R,S,U],[B,M,P,R,U],[B,M,P,S],[B,M,P,S,U],[B,M,P,U],[C],[C,D],[C,D,M],[C,D,M,P],[C,D,M,P,Q],[C,D,M,P,Q,R],[C,D,M,P,Q,R,S],[C,D,M,P,Q,R,S,U],[C,D,M,P,Q,R,U],[C,D,M,P,Q,S],[C,D,M,P,Q,S,U],[C,D,M,P,Q,U],[C,D,M,P,R],[C,D,M,P,R,S],[C,D,M,P,R,S,U],[C,D,M,P,R,U],[C,D,M,P,S],[C,D,M,P,S,U],[C,D,M,P,U],[C,M],[C,M,P],[C,M,P,Q],[C,M,P,Q,R],[C,M,P,Q,R,S],[C,M,P,Q,R,S,U],[C,M,P,Q,R,U],[C,M,P,Q,S],[C,M,P,Q,S,U],[C,M,P,Q,U],[C,M,P,R],[C,M,P,R,S],[C,M,P,R,S,U],[C,M,P,R,U],[C,M,P,S],[C,M,P,S,U],[C,M,P,U],[D],[D,M],[D,M,P],[D,M,P,Q],[D,M,P,Q,R],[D,M,P,Q,R,S],[D,M,P,Q,R,S,U],[D,M,P,Q,R,U],[D,M,P,Q,S],[D,M,P,Q,S,U],[D,M,P,Q,U],[D,M,P,R],[D,M,P,R,S],[D,M,P,R,S,U],[D,M,P,R,U],[D,M,P,S],[D,M,P,S,U],[D,M,P,U],[F],[H],[I],[J],[L],[M],[M,P],[M,P,Q],[M,P,Q,R],[M,P,Q,R,S],[M,P,Q,R,S,U],[M,P,Q,R,U],[M,P,Q,S],[M,P,Q,S,U],[M,P,Q,U],[M,P,R],[M,P,R,S],[M,P,R,S,U],[M,P,R,U],[M,P,S],[M,P,S,U],[M,P,U],[N],[Q],[Q,R],[R],[V]]),ground([E,G,K,O,T]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(V);mshare([[B],[B,C],[C],[E],[F],[G],[H],[I],[J],[L],[N],[Q],[Q,R],[R],[V]]),ground([D,K,M,O,P,S,T,U]),linear(F),linear(G),linear(H),linear(I),linear(J),linear(L),linear(N),linear(V);mshare([[B],[B,C],[C],[E],[F],[H],[I],[J],[L],[N],[Q],[Q,R],[R],[V]]),ground([D,G,K,M,O,P,S,T,U]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(V);mshare([[B],[B,C],[C],[F],[G],[H],[I],[J],[L],[N],[Q],[Q,R],[R],[V]]),ground([D,E,K,M,O,P,S,T,U]),linear(F),linear(G),linear(H),linear(I),linear(J),linear(L),linear(N),linear(V);mshare([[B],[B,C],[C],[F],[H],[I],[J],[L],[N],[Q],[Q,R],[R],[V]]),ground([D,E,G,K,M,O,P,S,T,U]),linear(F),linear(H),linear(I),linear(J),linear(L),linear(N),linear(V))),
    possessive(Q,R,S,V,[pp(poss,np(C,B,E))|V],F,G,H,I,J,T,L,U,N),
    true((mshare([[B,C,D,E,F,G,H,J,M,N,P,Q,R,S,U],[B,C,D,E,F,G,H,J,M,N,P,Q,R,U],[B,C,D,E,F,G,H,J,M,N,P,Q,S,U],[B,C,D,E,F,G,H,J,M,N,P,Q,U],[B,C,D,E,F,G,H,J,M,N,P,R,S,U],[B,C,D,E,F,G,H,J,M,N,P,R,U],[B,C,D,E,F,G,H,J,M,N,P,S,U],[B,C,D,E,F,G,H,J,M,N,P,U],[B,C,D,E,F,G,H,J,M,P,Q,R,S],[B,C,D,E,F,G,H,J,M,P,Q,R,S,U],[B,C,D,E,F,G,H,J,M,P,Q,R,U],[B,C,D,E,F,G,H,J,M,P,Q,S,U],[B,C,D,E,F,G,H,J,M,P,Q,U],[B,C,D,E,F,G,H,J,M,P,R,S,U],[B,C,D,E,F,G,H,J,M,P,R,U],[B,C,D,E,F,G,H,J,M,P,S,U],[B,C,D,E,F,G,H,J,M,P,U],[B,C,D,E,F,G,J],[B,C,D,E,F,G,J,M],[B,C,D,E,F,G,J,M,N,P,Q,R,S,U],[B,C,D,E,F,G,J,M,N,P,Q,R,U],[B,C,D,E,F,G,J,M,N,P,Q,S,U],[B,C,D,E,F,G,J,M,N,P,Q,U],[B,C,D,E,F,G,J,M,N,P,R,S,U],[B,C,D,E,F,G,J,M,N,P,R,U],[B,C,D,E,F,G,J,M,N,P,S,U],[B,C,D,E,F,G,J,M,N,P,U],[B,C,D,E,F,G,J,M,P],[B,C,D,E,F,G,J,M,P,Q],[B,C,D,E,F,G,J,M,P,Q,R],[B,C,D,E,F,G,J,M,P,Q,R,S],[B,C,D,E,F,G,J,M,P,Q,R,S,U],[B,C,D,E,F,G,J,M,P,Q,R,U],[B,C,D,E,F,G,J,M,P,Q,S],[B,C,D,E,F,G,J,M,P,Q,S,U],[B,C,D,E,F,G,J,M,P,Q,U],[B,C,D,E,F,G,J,M,P,R],[B,C,D,E,F,G,J,M,P,R,S],[B,C,D,E,F,G,J,M,P,R,S,U],[B,C,D,E,F,G,J,M,P,R,U],[B,C,D,E,F,G,J,M,P,S],[B,C,D,E,F,G,J,M,P,S,U],[B,C,D,E,F,G,J,M,P,U],[B,C,D,E,F,G,J,M,Q],[B,C,D,E,F,G,J,M,Q,R],[B,C,D,E,F,G,J,M,R],[B,C,D,E,F,G,J,Q],[B,C,D,E,F,G,J,Q,R],[B,C,D,E,F,G,J,R],[B,C,D,E,F,H,J,M,N,P,Q,R,S,U],[B,C,D,E,F,H,J,M,N,P,Q,R,U],[B,C,D,E,F,H,J,M,N,P,Q,S,U],[B,C,D,E,F,H,J,M,N,P,Q,U],[B,C,D,E,F,H,J,M,N,P,R,S,U],[B,C,D,E,F,H,J,M,N,P,R,U],[B,C,D,E,F,H,J,M,N,P,S,U],[B,C,D,E,F,H,J,M,N,P,U],[B,C,D,E,F,H,J,M,P,Q,R,S,U],[B,C,D,E,F,H,J,M,P,Q,R,U],[B,C,D,E,F,H,J,M,P,Q,S],[B,C,D,E,F,H,J,M,P,Q,S,U],[B,C,D,E,F,H,J,M,P,Q,U],[B,C,D,E,F,H,J,M,P,R,S,U],[B,C,D,E,F,H,J,M,P,R,U],[B,C,D,E,F,H,J,M,P,S,U],[B,C,D,E,F,H,J,M,P,U],[B,C,D,E,F,J],[B,C,D,E,F,J,M],[B,C,D,E,F,J,M,N,P,Q,R,S,U],[B,C,D,E,F,J,M,N,P,Q,R,U],[B,C,D,E,F,J,M,N,P,Q,S,U],[B,C,D,E,F,J,M,N,P,Q,U],[B,C,D,E,F,J,M,N,P,R,S,U],[B,C,D,E,F,J,M,N,P,R,U],[B,C,D,E,F,J,M,N,P,S,U],[B,C,D,E,F,J,M,N,P,U],[B,C,D,E,F,J,M,P],[B,C,D,E,F,J,M,P,Q],[B,C,D,E,F,J,M,P,Q,R],[B,C,D,E,F,J,M,P,Q,R,S],[B,C,D,E,F,J,M,P,Q,R,S,U],[B,C,D,E,F,J,M,P,Q,R,U],[B,C,D,E,F,J,M,P,Q,S],[B,C,D,E,F,J,M,P,Q,S,U],[B,C,D,E,F,J,M,P,Q,U],[B,C,D,E,F,J,M,P,R],[B,C,D,E,F,J,M,P,R,S],[B,C,D,E,F,J,M,P,R,S,U],[B,C,D,E,F,J,M,P,R,U],[B,C,D,E,F,J,M,P,S],[B,C,D,E,F,J,M,P,S,U],[B,C,D,E,F,J,M,P,U],[B,C,D,E,F,J,M,Q],[B,C,D,E,F,J,M,Q,R],[B,C,D,E,F,J,M,R],[B,C,D,E,F,J,Q],[B,C,D,E,F,J,Q,R],[B,C,D,E,F,J,R],[B,C,D,E,G,H,J,M,N,P,Q,R,S,U],[B,C,D,E,G,H,J,M,N,P,Q,R,U],[B,C,D,E,G,H,J,M,N,P,Q,S,U],[B,C,D,E,G,H,J,M,N,P,Q,U],[B,C,D,E,G,H,J,M,N,P,R,S,U],[B,C,D,E,G,H,J,M,N,P,R,U],[B,C,D,E,G,H,J,M,N,P,S,U],[B,C,D,E,G,H,J,M,N,P,U],[B,C,D,E,G,H,J,M,P,Q,R,S,U],[B,C,D,E,G,H,J,M,P,Q,R,U],[B,C,D,E,G,H,J,M,P,Q,S,U],[B,C,D,E,G,H,J,M,P,Q,U],[B,C,D,E,G,H,J,M,P,R,S],[B,C,D,E,G,H,J,M,P,R,S,U],[B,C,D,E,G,H,J,M,P,R,U],[B,C,D,E,G,H,J,M,P,S,U],[B,C,D,E,G,H,J,M,P,U],[B,C,D,E,G,J],[B,C,D,E,G,J,M],[B,C,D,E,G,J,M,N,P,Q,R,S,U],[B,C,D,E,G,J,M,N,P,Q,R,U],[B,C,D,E,G,J,M,N,P,Q,S,U],[B,C,D,E,G,J,M,N,P,Q,U],[B,C,D,E,G,J,M,N,P,R,S,U],[B,C,D,E,G,J,M,N,P,R,U],[B,C,D,E,G,J,M,N,P,S,U],[B,C,D,E,G,J,M,N,P,U],[B,C,D,E,G,J,M,P],[B,C,D,E,G,J,M,P,Q],[B,C,D,E,G,J,M,P,Q,R],[B,C,D,E,G,J,M,P,Q,R,S],[B,C,D,E,G,J,M,P,Q,R,S,U],[B,C,D,E,G,J,M,P,Q,R,U],[B,C,D,E,G,J,M,P,Q,S],[B,C,D,E,G,J,M,P,Q,S,U],[B,C,D,E,G,J,M,P,Q,U],[B,C,D,E,G,J,M,P,R],[B,C,D,E,G,J,M,P,R,S],[B,C,D,E,G,J,M,P,R,S,U],[B,C,D,E,G,J,M,P,R,U],[B,C,D,E,G,J,M,P,S],[B,C,D,E,G,J,M,P,S,U],[B,C,D,E,G,J,M,P,U],[B,C,D,E,G,J,M,Q],[B,C,D,E,G,J,M,Q,R],[B,C,D,E,G,J,M,R],[B,C,D,E,G,J,Q],[B,C,D,E,G,J,Q,R],[B,C,D,E,G,J,R],[B,C,D,E,H,J,M,N,P,Q,R,S,U],[B,C,D,E,H,J,M,N,P,Q,R,U],[B,C,D,E,H,J,M,N,P,Q,S,U],[B,C,D,E,H,J,M,N,P,Q,U],[B,C,D,E,H,J,M,N,P,R,S,U],[B,C,D,E,H,J,M,N,P,R,U],[B,C,D,E,H,J,M,N,P,S,U],[B,C,D,E,H,J,M,N,P,U],[B,C,D,E,H,J,M,P,Q,R,S,U],[B,C,D,E,H,J,M,P,Q,R,U],[B,C,D,E,H,J,M,P,Q,S,U],[B,C,D,E,H,J,M,P,Q,U],[B,C,D,E,H,J,M,P,R,S,U],[B,C,D,E,H,J,M,P,R,U],[B,C,D,E,H,J,M,P,S],[B,C,D,E,H,J,M,P,S,U],[B,C,D,E,H,J,M,P,U],[B,C,D,E,J],[B,C,D,E,J,M],[B,C,D,E,J,M,N,P,Q,R,S,U],[B,C,D,E,J,M,N,P,Q,R,U],[B,C,D,E,J,M,N,P,Q,S,U],[B,C,D,E,J,M,N,P,Q,U],[B,C,D,E,J,M,N,P,R,S,U],[B,C,D,E,J,M,N,P,R,U],[B,C,D,E,J,M,N,P,S,U],[B,C,D,E,J,M,N,P,U],[B,C,D,E,J,M,P],[B,C,D,E,J,M,P,Q],[B,C,D,E,J,M,P,Q,R],[B,C,D,E,J,M,P,Q,R,S],[B,C,D,E,J,M,P,Q,R,S,U],[B,C,D,E,J,M,P,Q,R,U],[B,C,D,E,J,M,P,Q,S],[B,C,D,E,J,M,P,Q,S,U],[B,C,D,E,J,M,P,Q,U],[B,C,D,E,J,M,P,R],[B,C,D,E,J,M,P,R,S],[B,C,D,E,J,M,P,R,S,U],[B,C,D,E,J,M,P,R,U],[B,C,D,E,J,M,P,S],[B,C,D,E,J,M,P,S,U],[B,C,D,E,J,M,P,U],[B,C,D,E,J,M,Q],[B,C,D,E,J,M,Q,R],[B,C,D,E,J,M,R],[B,C,D,E,J,Q],[B,C,D,E,J,Q,R],[B,C,D,E,J,R],[B,C,D,F,G,H,J,M,N,P,Q,R,S,U],[B,C,D,F,G,H,J,M,N,P,Q,R,U],[B,C,D,F,G,H,J,M,N,P,Q,S,U],[B,C,D,F,G,H,J,M,N,P,Q,U],[B,C,D,F,G,H,J,M,N,P,R,S,U],[B,C,D,F,G,H,J,M,N,P,R,U],[B,C,D,F,G,H,J,M,N,P,S,U],[B,C,D,F,G,H,J,M,N,P,U],[B,C,D,F,G,H,J,M,P,Q,R,S],[B,C,D,F,G,H,J,M,P,Q,R,S,U],[B,C,D,F,G,H,J,M,P,Q,R,U],[B,C,D,F,G,H,J,M,P,Q,S,U],[B,C,D,F,G,H,J,M,P,Q,U],[B,C,D,F,G,H,J,M,P,R,S,U],[B,C,D,F,G,H,J,M,P,R,U],[B,C,D,F,G,H,J,M,P,S,U],[B,C,D,F,G,H,J,M,P,U],[B,C,D,F,G,J],[B,C,D,F,G,J,M],[B,C,D,F,G,J,M,N,P,Q,R,S,U],[B,C,D,F,G,J,M,N,P,Q,R,U],[B,C,D,F,G,J,M,N,P,Q,S,U],[B,C,D,F,G,J,M,N,P,Q,U],[B,C,D,F,G,J,M,N,P,R,S,U],[B,C,D,F,G,J,M,N,P,R,U],[B,C,D,F,G,J,M,N,P,S,U],[B,C,D,F,G,J,M,N,P,U],[B,C,D,F,G,J,M,P],[B,C,D,F,G,J,M,P,Q],[B,C,D,F,G,J,M,P,Q,R],[B,C,D,F,G,J,M,P,Q,R,S],[B,C,D,F,G,J,M,P,Q,R,S,U],[B,C,D,F,G,J,M,P,Q,R,U],[B,C,D,F,G,J,M,P,Q,S],[B,C,D,F,G,J,M,P,Q,S,U],[B,C,D,F,G,J,M,P,Q,U],[B,C,D,F,G,J,M,P,R],[B,C,D,F,G,J,M,P,R,S],[B,C,D,F,G,J,M,P,R,S,U],[B,C,D,F,G,J,M,P,R,U],[B,C,D,F,G,J,M,P,S],[B,C,D,F,G,J,M,P,S,U],[B,C,D,F,G,J,M,P,U],[B,C,D,F,G,J,M,Q],[B,C,D,F,G,J,M,Q,R],[B,C,D,F,G,J,M,R],[B,C,D,F,G,J,Q],[B,C,D,F,G,J,Q,R],[B,C,D,F,G,J,R],[B,C,D,F,H,J,M,N,P,Q,R,S,U],[B,C,D,F,H,J,M,N,P,Q,R,U],[B,C,D,F,H,J,M,N,P,Q,S,U],[B,C,D,F,H,J,M,N,P,Q,U],[B,C,D,F,H,J,M,N,P,R,S,U],[B,C,D,F,H,J,M,N,P,R,U],[B,C,D,F,H,J,M,N,P,S,U],[B,C,D,F,H,J,M,N,P,U],[B,C,D,F,H,J,M,P,Q,R,S,U],[B,C,D,F,H,J,M,P,Q,R,U],[B,C,D,F,H,J,M,P,Q,S],[B,C,D,F,H,J,M,P,Q,S,U],[B,C,D,F,H,J,M,P,Q,U],[B,C,D,F,H,J,M,P,R,S,U],[B,C,D,F,H,J,M,P,R,U],[B,C,D,F,H,J,M,P,S,U],[B,C,D,F,H,J,M,P,U],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N,P,Q,R,S,U],[B,C,D,F,J,M,N,P,Q,R,U],[B,C,D,F,J,M,N,P,Q,S,U],[B,C,D,F,J,M,N,P,Q,U],[B,C,D,F,J,M,N,P,R,S,U],[B,C,D,F,J,M,N,P,R,U],[B,C,D,F,J,M,N,P,S,U],[B,C,D,F,J,M,N,P,U],[B,C,D,F,J,M,P],[B,C,D,F,J,M,P,Q],[B,C,D,F,J,M,P,Q,R],[B,C,D,F,J,M,P,Q,R,S],[B,C,D,F,J,M,P,Q,R,S,U],[B,C,D,F,J,M,P,Q,R,U],[B,C,D,F,J,M,P,Q,S],[B,C,D,F,J,M,P,Q,S,U],[B,C,D,F,J,M,P,Q,U],[B,C,D,F,J,M,P,R],[B,C,D,F,J,M,P,R,S],[B,C,D,F,J,M,P,R,S,U],[B,C,D,F,J,M,P,R,U],[B,C,D,F,J,M,P,S],[B,C,D,F,J,M,P,S,U],[B,C,D,F,J,M,P,U],[B,C,D,F,J,M,Q],[B,C,D,F,J,M,Q,R],[B,C,D,F,J,M,R],[B,C,D,F,J,Q],[B,C,D,F,J,Q,R],[B,C,D,F,J,R],[B,C,D,G,H,J,M,N,P,Q,R,S,U],[B,C,D,G,H,J,M,N,P,Q,R,U],[B,C,D,G,H,J,M,N,P,Q,S,U],[B,C,D,G,H,J,M,N,P,Q,U],[B,C,D,G,H,J,M,N,P,R,S,U],[B,C,D,G,H,J,M,N,P,R,U],[B,C,D,G,H,J,M,N,P,S,U],[B,C,D,G,H,J,M,N,P,U],[B,C,D,G,H,J,M,P,Q,R,S,U],[B,C,D,G,H,J,M,P,Q,R,U],[B,C,D,G,H,J,M,P,Q,S,U],[B,C,D,G,H,J,M,P,Q,U],[B,C,D,G,H,J,M,P,R,S],[B,C,D,G,H,J,M,P,R,S,U],[B,C,D,G,H,J,M,P,R,U],[B,C,D,G,H,J,M,P,S,U],[B,C,D,G,H,J,M,P,U],[B,C,D,G,J],[B,C,D,G,J,M],[B,C,D,G,J,M,N,P,Q,R,S,U],[B,C,D,G,J,M,N,P,Q,R,U],[B,C,D,G,J,M,N,P,Q,S,U],[B,C,D,G,J,M,N,P,Q,U],[B,C,D,G,J,M,N,P,R,S,U],[B,C,D,G,J,M,N,P,R,U],[B,C,D,G,J,M,N,P,S,U],[B,C,D,G,J,M,N,P,U],[B,C,D,G,J,M,P],[B,C,D,G,J,M,P,Q],[B,C,D,G,J,M,P,Q,R],[B,C,D,G,J,M,P,Q,R,S],[B,C,D,G,J,M,P,Q,R,S,U],[B,C,D,G,J,M,P,Q,R,U],[B,C,D,G,J,M,P,Q,S],[B,C,D,G,J,M,P,Q,S,U],[B,C,D,G,J,M,P,Q,U],[B,C,D,G,J,M,P,R],[B,C,D,G,J,M,P,R,S],[B,C,D,G,J,M,P,R,S,U],[B,C,D,G,J,M,P,R,U],[B,C,D,G,J,M,P,S],[B,C,D,G,J,M,P,S,U],[B,C,D,G,J,M,P,U],[B,C,D,G,J,M,Q],[B,C,D,G,J,M,Q,R],[B,C,D,G,J,M,R],[B,C,D,G,J,Q],[B,C,D,G,J,Q,R],[B,C,D,G,J,R],[B,C,D,H,J,M,N,P,Q,R,S,U],[B,C,D,H,J,M,N,P,Q,R,U],[B,C,D,H,J,M,N,P,Q,S,U],[B,C,D,H,J,M,N,P,Q,U],[B,C,D,H,J,M,N,P,R,S,U],[B,C,D,H,J,M,N,P,R,U],[B,C,D,H,J,M,N,P,S,U],[B,C,D,H,J,M,N,P,U],[B,C,D,H,J,M,P,Q,R,S,U],[B,C,D,H,J,M,P,Q,R,U],[B,C,D,H,J,M,P,Q,S,U],[B,C,D,H,J,M,P,Q,U],[B,C,D,H,J,M,P,R,S,U],[B,C,D,H,J,M,P,R,U],[B,C,D,H,J,M,P,S],[B,C,D,H,J,M,P,S,U],[B,C,D,H,J,M,P,U],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N,P,Q,R,S,U],[B,C,D,J,M,N,P,Q,R,U],[B,C,D,J,M,N,P,Q,S,U],[B,C,D,J,M,N,P,Q,U],[B,C,D,J,M,N,P,R,S,U],[B,C,D,J,M,N,P,R,U],[B,C,D,J,M,N,P,S,U],[B,C,D,J,M,N,P,U],[B,C,D,J,M,P],[B,C,D,J,M,P,Q],[B,C,D,J,M,P,Q,R],[B,C,D,J,M,P,Q,R,S],[B,C,D,J,M,P,Q,R,S,U],[B,C,D,J,M,P,Q,R,U],[B,C,D,J,M,P,Q,S],[B,C,D,J,M,P,Q,S,U],[B,C,D,J,M,P,Q,U],[B,C,D,J,M,P,R],[B,C,D,J,M,P,R,S],[B,C,D,J,M,P,R,S,U],[B,C,D,J,M,P,R,U],[B,C,D,J,M,P,S],[B,C,D,J,M,P,S,U],[B,C,D,J,M,P,U],[B,C,D,J,M,Q],[B,C,D,J,M,Q,R],[B,C,D,J,M,R],[B,C,D,J,Q],[B,C,D,J,Q,R],[B,C,D,J,R],[B,C,E,F,G,H,J,M,N,P,Q,R,S,U],[B,C,E,F,G,H,J,M,N,P,Q,R,U],[B,C,E,F,G,H,J,M,N,P,Q,S,U],[B,C,E,F,G,H,J,M,N,P,Q,U],[B,C,E,F,G,H,J,M,N,P,R,S,U],[B,C,E,F,G,H,J,M,N,P,R,U],[B,C,E,F,G,H,J,M,N,P,S,U],[B,C,E,F,G,H,J,M,N,P,U],[B,C,E,F,G,H,J,M,P,Q,R,S],[B,C,E,F,G,H,J,M,P,Q,R,S,U],[B,C,E,F,G,H,J,M,P,Q,R,U],[B,C,E,F,G,H,J,M,P,Q,S,U],[B,C,E,F,G,H,J,M,P,Q,U],[B,C,E,F,G,H,J,M,P,R,S,U],[B,C,E,F,G,H,J,M,P,R,U],[B,C,E,F,G,H,J,M,P,S,U],[B,C,E,F,G,H,J,M,P,U],[B,C,E,F,G,J],[B,C,E,F,G,J,M],[B,C,E,F,G,J,M,N,P,Q,R,S,U],[B,C,E,F,G,J,M,N,P,Q,R,U],[B,C,E,F,G,J,M,N,P,Q,S,U],[B,C,E,F,G,J,M,N,P,Q,U],[B,C,E,F,G,J,M,N,P,R,S,U],[B,C,E,F,G,J,M,N,P,R,U],[B,C,E,F,G,J,M,N,P,S,U],[B,C,E,F,G,J,M,N,P,U],[B,C,E,F,G,J,M,P],[B,C,E,F,G,J,M,P,Q],[B,C,E,F,G,J,M,P,Q,R],[B,C,E,F,G,J,M,P,Q,R,S],[B,C,E,F,G,J,M,P,Q,R,S,U],[B,C,E,F,G,J,M,P,Q,R,U],[B,C,E,F,G,J,M,P,Q,S],[B,C,E,F,G,J,M,P,Q,S,U],[B,C,E,F,G,J,M,P,Q,U],[B,C,E,F,G,J,M,P,R],[B,C,E,F,G,J,M,P,R,S],[B,C,E,F,G,J,M,P,R,S,U],[B,C,E,F,G,J,M,P,R,U],[B,C,E,F,G,J,M,P,S],[B,C,E,F,G,J,M,P,S,U],[B,C,E,F,G,J,M,P,U],[B,C,E,F,G,J,M,Q],[B,C,E,F,G,J,M,Q,R],[B,C,E,F,G,J,M,R],[B,C,E,F,G,J,Q],[B,C,E,F,G,J,Q,R],[B,C,E,F,G,J,R],[B,C,E,F,H,J,M,N,P,Q,R,S,U],[B,C,E,F,H,J,M,N,P,Q,R,U],[B,C,E,F,H,J,M,N,P,Q,S,U],[B,C,E,F,H,J,M,N,P,Q,U],[B,C,E,F,H,J,M,N,P,R,S,U],[B,C,E,F,H,J,M,N,P,R,U],[B,C,E,F,H,J,M,N,P,S,U],[B,C,E,F,H,J,M,N,P,U],[B,C,E,F,H,J,M,P,Q,R,S,U],[B,C,E,F,H,J,M,P,Q,R,U],[B,C,E,F,H,J,M,P,Q,S],[B,C,E,F,H,J,M,P,Q,S,U],[B,C,E,F,H,J,M,P,Q,U],[B,C,E,F,H,J,M,P,R,S,U],[B,C,E,F,H,J,M,P,R,U],[B,C,E,F,H,J,M,P,S,U],[B,C,E,F,H,J,M,P,U],[B,C,E,F,J],[B,C,E,F,J,M],[B,C,E,F,J,M,N,P,Q,R,S,U],[B,C,E,F,J,M,N,P,Q,R,U],[B,C,E,F,J,M,N,P,Q,S,U],[B,C,E,F,J,M,N,P,Q,U],[B,C,E,F,J,M,N,P,R,S,U],[B,C,E,F,J,M,N,P,R,U],[B,C,E,F,J,M,N,P,S,U],[B,C,E,F,J,M,N,P,U],[B,C,E,F,J,M,P],[B,C,E,F,J,M,P,Q],[B,C,E,F,J,M,P,Q,R],[B,C,E,F,J,M,P,Q,R,S],[B,C,E,F,J,M,P,Q,R,S,U],[B,C,E,F,J,M,P,Q,R,U],[B,C,E,F,J,M,P,Q,S],[B,C,E,F,J,M,P,Q,S,U],[B,C,E,F,J,M,P,Q,U],[B,C,E,F,J,M,P,R],[B,C,E,F,J,M,P,R,S],[B,C,E,F,J,M,P,R,S,U],[B,C,E,F,J,M,P,R,U],[B,C,E,F,J,M,P,S],[B,C,E,F,J,M,P,S,U],[B,C,E,F,J,M,P,U],[B,C,E,F,J,M,Q],[B,C,E,F,J,M,Q,R],[B,C,E,F,J,M,R],[B,C,E,F,J,Q],[B,C,E,F,J,Q,R],[B,C,E,F,J,R],[B,C,E,G,H,J,M,N,P,Q,R,S,U],[B,C,E,G,H,J,M,N,P,Q,R,U],[B,C,E,G,H,J,M,N,P,Q,S,U],[B,C,E,G,H,J,M,N,P,Q,U],[B,C,E,G,H,J,M,N,P,R,S,U],[B,C,E,G,H,J,M,N,P,R,U],[B,C,E,G,H,J,M,N,P,S,U],[B,C,E,G,H,J,M,N,P,U],[B,C,E,G,H,J,M,P,Q,R,S,U],[B,C,E,G,H,J,M,P,Q,R,U],[B,C,E,G,H,J,M,P,Q,S,U],[B,C,E,G,H,J,M,P,Q,U],[B,C,E,G,H,J,M,P,R,S],[B,C,E,G,H,J,M,P,R,S,U],[B,C,E,G,H,J,M,P,R,U],[B,C,E,G,H,J,M,P,S,U],[B,C,E,G,H,J,M,P,U],[B,C,E,G,J],[B,C,E,G,J,M],[B,C,E,G,J,M,N,P,Q,R,S,U],[B,C,E,G,J,M,N,P,Q,R,U],[B,C,E,G,J,M,N,P,Q,S,U],[B,C,E,G,J,M,N,P,Q,U],[B,C,E,G,J,M,N,P,R,S,U],[B,C,E,G,J,M,N,P,R,U],[B,C,E,G,J,M,N,P,S,U],[B,C,E,G,J,M,N,P,U],[B,C,E,G,J,M,P],[B,C,E,G,J,M,P,Q],[B,C,E,G,J,M,P,Q,R],[B,C,E,G,J,M,P,Q,R,S],[B,C,E,G,J,M,P,Q,R,S,U],[B,C,E,G,J,M,P,Q,R,U],[B,C,E,G,J,M,P,Q,S],[B,C,E,G,J,M,P,Q,S,U],[B,C,E,G,J,M,P,Q,U],[B,C,E,G,J,M,P,R],[B,C,E,G,J,M,P,R,S],[B,C,E,G,J,M,P,R,S,U],[B,C,E,G,J,M,P,R,U],[B,C,E,G,J,M,P,S],[B,C,E,G,J,M,P,S,U],[B,C,E,G,J,M,P,U],[B,C,E,G,J,M,Q],[B,C,E,G,J,M,Q,R],[B,C,E,G,J,M,R],[B,C,E,G,J,Q],[B,C,E,G,J,Q,R],[B,C,E,G,J,R],[B,C,E,H,J,M,N,P,Q,R,S,U],[B,C,E,H,J,M,N,P,Q,R,U],[B,C,E,H,J,M,N,P,Q,S,U],[B,C,E,H,J,M,N,P,Q,U],[B,C,E,H,J,M,N,P,R,S,U],[B,C,E,H,J,M,N,P,R,U],[B,C,E,H,J,M,N,P,S,U],[B,C,E,H,J,M,N,P,U],[B,C,E,H,J,M,P,Q,R,S,U],[B,C,E,H,J,M,P,Q,R,U],[B,C,E,H,J,M,P,Q,S,U],[B,C,E,H,J,M,P,Q,U],[B,C,E,H,J,M,P,R,S,U],[B,C,E,H,J,M,P,R,U],[B,C,E,H,J,M,P,S],[B,C,E,H,J,M,P,S,U],[B,C,E,H,J,M,P,U],[B,C,E,J],[B,C,E,J,M],[B,C,E,J,M,N,P,Q,R,S,U],[B,C,E,J,M,N,P,Q,R,U],[B,C,E,J,M,N,P,Q,S,U],[B,C,E,J,M,N,P,Q,U],[B,C,E,J,M,N,P,R,S,U],[B,C,E,J,M,N,P,R,U],[B,C,E,J,M,N,P,S,U],[B,C,E,J,M,N,P,U],[B,C,E,J,M,P],[B,C,E,J,M,P,Q],[B,C,E,J,M,P,Q,R],[B,C,E,J,M,P,Q,R,S],[B,C,E,J,M,P,Q,R,S,U],[B,C,E,J,M,P,Q,R,U],[B,C,E,J,M,P,Q,S],[B,C,E,J,M,P,Q,S,U],[B,C,E,J,M,P,Q,U],[B,C,E,J,M,P,R],[B,C,E,J,M,P,R,S],[B,C,E,J,M,P,R,S,U],[B,C,E,J,M,P,R,U],[B,C,E,J,M,P,S],[B,C,E,J,M,P,S,U],[B,C,E,J,M,P,U],[B,C,E,J,M,Q],[B,C,E,J,M,Q,R],[B,C,E,J,M,R],[B,C,E,J,Q],[B,C,E,J,Q,R],[B,C,E,J,R],[B,C,F,G,H,J,M,N,P,Q,R,S,U],[B,C,F,G,H,J,M,N,P,Q,R,U],[B,C,F,G,H,J,M,N,P,Q,S,U],[B,C,F,G,H,J,M,N,P,Q,U],[B,C,F,G,H,J,M,N,P,R,S,U],[B,C,F,G,H,J,M,N,P,R,U],[B,C,F,G,H,J,M,N,P,S,U],[B,C,F,G,H,J,M,N,P,U],[B,C,F,G,H,J,M,P,Q,R,S],[B,C,F,G,H,J,M,P,Q,R,S,U],[B,C,F,G,H,J,M,P,Q,R,U],[B,C,F,G,H,J,M,P,Q,S,U],[B,C,F,G,H,J,M,P,Q,U],[B,C,F,G,H,J,M,P,R,S,U],[B,C,F,G,H,J,M,P,R,U],[B,C,F,G,H,J,M,P,S,U],[B,C,F,G,H,J,M,P,U],[B,C,F,G,J],[B,C,F,G,J,M],[B,C,F,G,J,M,N,P,Q,R,S,U],[B,C,F,G,J,M,N,P,Q,R,U],[B,C,F,G,J,M,N,P,Q,S,U],[B,C,F,G,J,M,N,P,Q,U],[B,C,F,G,J,M,N,P,R,S,U],[B,C,F,G,J,M,N,P,R,U],[B,C,F,G,J,M,N,P,S,U],[B,C,F,G,J,M,N,P,U],[B,C,F,G,J,M,P],[B,C,F,G,J,M,P,Q],[B,C,F,G,J,M,P,Q,R],[B,C,F,G,J,M,P,Q,R,S],[B,C,F,G,J,M,P,Q,R,S,U],[B,C,F,G,J,M,P,Q,R,U],[B,C,F,G,J,M,P,Q,S],[B,C,F,G,J,M,P,Q,S,U],[B,C,F,G,J,M,P,Q,U],[B,C,F,G,J,M,P,R],[B,C,F,G,J,M,P,R,S],[B,C,F,G,J,M,P,R,S,U],[B,C,F,G,J,M,P,R,U],[B,C,F,G,J,M,P,S],[B,C,F,G,J,M,P,S,U],[B,C,F,G,J,M,P,U],[B,C,F,G,J,M,Q],[B,C,F,G,J,M,Q,R],[B,C,F,G,J,M,R],[B,C,F,G,J,Q],[B,C,F,G,J,Q,R],[B,C,F,G,J,R],[B,C,F,H,J,M,N,P,Q,R,S,U],[B,C,F,H,J,M,N,P,Q,R,U],[B,C,F,H,J,M,N,P,Q,S,U],[B,C,F,H,J,M,N,P,Q,U],[B,C,F,H,J,M,N,P,R,S,U],[B,C,F,H,J,M,N,P,R,U],[B,C,F,H,J,M,N,P,S,U],[B,C,F,H,J,M,N,P,U],[B,C,F,H,J,M,P,Q,R,S,U],[B,C,F,H,J,M,P,Q,R,U],[B,C,F,H,J,M,P,Q,S],[B,C,F,H,J,M,P,Q,S,U],[B,C,F,H,J,M,P,Q,U],[B,C,F,H,J,M,P,R,S,U],[B,C,F,H,J,M,P,R,U],[B,C,F,H,J,M,P,S,U],[B,C,F,H,J,M,P,U],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N,P,Q,R,S,U],[B,C,F,J,M,N,P,Q,R,U],[B,C,F,J,M,N,P,Q,S,U],[B,C,F,J,M,N,P,Q,U],[B,C,F,J,M,N,P,R,S,U],[B,C,F,J,M,N,P,R,U],[B,C,F,J,M,N,P,S,U],[B,C,F,J,M,N,P,U],[B,C,F,J,M,P],[B,C,F,J,M,P,Q],[B,C,F,J,M,P,Q,R],[B,C,F,J,M,P,Q,R,S],[B,C,F,J,M,P,Q,R,S,U],[B,C,F,J,M,P,Q,R,U],[B,C,F,J,M,P,Q,S],[B,C,F,J,M,P,Q,S,U],[B,C,F,J,M,P,Q,U],[B,C,F,J,M,P,R],[B,C,F,J,M,P,R,S],[B,C,F,J,M,P,R,S,U],[B,C,F,J,M,P,R,U],[B,C,F,J,M,P,S],[B,C,F,J,M,P,S,U],[B,C,F,J,M,P,U],[B,C,F,J,M,Q],[B,C,F,J,M,Q,R],[B,C,F,J,M,R],[B,C,F,J,Q],[B,C,F,J,Q,R],[B,C,F,J,R],[B,C,G,H,J,M,N,P,Q,R,S,U],[B,C,G,H,J,M,N,P,Q,R,U],[B,C,G,H,J,M,N,P,Q,S,U],[B,C,G,H,J,M,N,P,Q,U],[B,C,G,H,J,M,N,P,R,S,U],[B,C,G,H,J,M,N,P,R,U],[B,C,G,H,J,M,N,P,S,U],[B,C,G,H,J,M,N,P,U],[B,C,G,H,J,M,P,Q,R,S,U],[B,C,G,H,J,M,P,Q,R,U],[B,C,G,H,J,M,P,Q,S,U],[B,C,G,H,J,M,P,Q,U],[B,C,G,H,J,M,P,R,S],[B,C,G,H,J,M,P,R,S,U],[B,C,G,H,J,M,P,R,U],[B,C,G,H,J,M,P,S,U],[B,C,G,H,J,M,P,U],[B,C,G,J],[B,C,G,J,M],[B,C,G,J,M,N,P,Q,R,S,U],[B,C,G,J,M,N,P,Q,R,U],[B,C,G,J,M,N,P,Q,S,U],[B,C,G,J,M,N,P,Q,U],[B,C,G,J,M,N,P,R,S,U],[B,C,G,J,M,N,P,R,U],[B,C,G,J,M,N,P,S,U],[B,C,G,J,M,N,P,U],[B,C,G,J,M,P],[B,C,G,J,M,P,Q],[B,C,G,J,M,P,Q,R],[B,C,G,J,M,P,Q,R,S],[B,C,G,J,M,P,Q,R,S,U],[B,C,G,J,M,P,Q,R,U],[B,C,G,J,M,P,Q,S],[B,C,G,J,M,P,Q,S,U],[B,C,G,J,M,P,Q,U],[B,C,G,J,M,P,R],[B,C,G,J,M,P,R,S],[B,C,G,J,M,P,R,S,U],[B,C,G,J,M,P,R,U],[B,C,G,J,M,P,S],[B,C,G,J,M,P,S,U],[B,C,G,J,M,P,U],[B,C,G,J,M,Q],[B,C,G,J,M,Q,R],[B,C,G,J,M,R],[B,C,G,J,Q],[B,C,G,J,Q,R],[B,C,G,J,R],[B,C,H,J,M,N,P,Q,R,S,U],[B,C,H,J,M,N,P,Q,R,U],[B,C,H,J,M,N,P,Q,S,U],[B,C,H,J,M,N,P,Q,U],[B,C,H,J,M,N,P,R,S,U],[B,C,H,J,M,N,P,R,U],[B,C,H,J,M,N,P,S,U],[B,C,H,J,M,N,P,U],[B,C,H,J,M,P,Q,R,S,U],[B,C,H,J,M,P,Q,R,U],[B,C,H,J,M,P,Q,S,U],[B,C,H,J,M,P,Q,U],[B,C,H,J,M,P,R,S,U],[B,C,H,J,M,P,R,U],[B,C,H,J,M,P,S],[B,C,H,J,M,P,S,U],[B,C,H,J,M,P,U],[B,C,J],[B,C,J,M],[B,C,J,M,N,P,Q,R,S,U],[B,C,J,M,N,P,Q,R,U],[B,C,J,M,N,P,Q,S,U],[B,C,J,M,N,P,Q,U],[B,C,J,M,N,P,R,S,U],[B,C,J,M,N,P,R,U],[B,C,J,M,N,P,S,U],[B,C,J,M,N,P,U],[B,C,J,M,P],[B,C,J,M,P,Q],[B,C,J,M,P,Q,R],[B,C,J,M,P,Q,R,S],[B,C,J,M,P,Q,R,S,U],[B,C,J,M,P,Q,R,U],[B,C,J,M,P,Q,S],[B,C,J,M,P,Q,S,U],[B,C,J,M,P,Q,U],[B,C,J,M,P,R],[B,C,J,M,P,R,S],[B,C,J,M,P,R,S,U],[B,C,J,M,P,R,U],[B,C,J,M,P,S],[B,C,J,M,P,S,U],[B,C,J,M,P,U],[B,C,J,M,Q],[B,C,J,M,Q,R],[B,C,J,M,R],[B,C,J,Q],[B,C,J,Q,R],[B,C,J,R],[B,D,E,F,G,H,J,M,N,P,Q,R,S,U],[B,D,E,F,G,H,J,M,N,P,Q,R,U],[B,D,E,F,G,H,J,M,N,P,Q,S,U],[B,D,E,F,G,H,J,M,N,P,Q,U],[B,D,E,F,G,H,J,M,N,P,R,S,U],[B,D,E,F,G,H,J,M,N,P,R,U],[B,D,E,F,G,H,J,M,N,P,S,U],[B,D,E,F,G,H,J,M,N,P,U],[B,D,E,F,G,H,J,M,P,Q,R,S],[B,D,E,F,G,H,J,M,P,Q,R,S,U],[B,D,E,F,G,H,J,M,P,Q,R,U],[B,D,E,F,G,H,J,M,P,Q,S,U],[B,D,E,F,G,H,J,M,P,Q,U],[B,D,E,F,G,H,J,M,P,R,S,U],[B,D,E,F,G,H,J,M,P,R,U],[B,D,E,F,G,H,J,M,P,S,U],[B,D,E,F,G,H,J,M,P,U],[B,D,E,F,G,J],[B,D,E,F,G,J,M],[B,D,E,F,G,J,M,N,P,Q,R,S,U],[B,D,E,F,G,J,M,N,P,Q,R,U],[B,D,E,F,G,J,M,N,P,Q,S,U],[B,D,E,F,G,J,M,N,P,Q,U],[B,D,E,F,G,J,M,N,P,R,S,U],[B,D,E,F,G,J,M,N,P,R,U],[B,D,E,F,G,J,M,N,P,S,U],[B,D,E,F,G,J,M,N,P,U],[B,D,E,F,G,J,M,P],[B,D,E,F,G,J,M,P,Q],[B,D,E,F,G,J,M,P,Q,R],[B,D,E,F,G,J,M,P,Q,R,S],[B,D,E,F,G,J,M,P,Q,R,S,U],[B,D,E,F,G,J,M,P,Q,R,U],[B,D,E,F,G,J,M,P,Q,S],[B,D,E,F,G,J,M,P,Q,S,U],[B,D,E,F,G,J,M,P,Q,U],[B,D,E,F,G,J,M,P,R],[B,D,E,F,G,J,M,P,R,S],[B,D,E,F,G,J,M,P,R,S,U],[B,D,E,F,G,J,M,P,R,U],[B,D,E,F,G,J,M,P,S],[B,D,E,F,G,J,M,P,S,U],[B,D,E,F,G,J,M,P,U],[B,D,E,F,G,J,M,Q],[B,D,E,F,G,J,M,Q,R],[B,D,E,F,G,J,M,R],[B,D,E,F,G,J,Q],[B,D,E,F,G,J,Q,R],[B,D,E,F,G,J,R],[B,D,E,F,H,J,M,N,P,Q,R,S,U],[B,D,E,F,H,J,M,N,P,Q,R,U],[B,D,E,F,H,J,M,N,P,Q,S,U],[B,D,E,F,H,J,M,N,P,Q,U],[B,D,E,F,H,J,M,N,P,R,S,U],[B,D,E,F,H,J,M,N,P,R,U],[B,D,E,F,H,J,M,N,P,S,U],[B,D,E,F,H,J,M,N,P,U],[B,D,E,F,H,J,M,P,Q,R,S,U],[B,D,E,F,H,J,M,P,Q,R,U],[B,D,E,F,H,J,M,P,Q,S],[B,D,E,F,H,J,M,P,Q,S,U],[B,D,E,F,H,J,M,P,Q,U],[B,D,E,F,H,J,M,P,R,S,U],[B,D,E,F,H,J,M,P,R,U],[B,D,E,F,H,J,M,P,S,U],[B,D,E,F,H,J,M,P,U],[B,D,E,F,J],[B,D,E,F,J,M],[B,D,E,F,J,M,N,P,Q,R,S,U],[B,D,E,F,J,M,N,P,Q,R,U],[B,D,E,F,J,M,N,P,Q,S,U],[B,D,E,F,J,M,N,P,Q,U],[B,D,E,F,J,M,N,P,R,S,U],[B,D,E,F,J,M,N,P,R,U],[B,D,E,F,J,M,N,P,S,U],[B,D,E,F,J,M,N,P,U],[B,D,E,F,J,M,P],[B,D,E,F,J,M,P,Q],[B,D,E,F,J,M,P,Q,R],[B,D,E,F,J,M,P,Q,R,S],[B,D,E,F,J,M,P,Q,R,S,U],[B,D,E,F,J,M,P,Q,R,U],[B,D,E,F,J,M,P,Q,S],[B,D,E,F,J,M,P,Q,S,U],[B,D,E,F,J,M,P,Q,U],[B,D,E,F,J,M,P,R],[B,D,E,F,J,M,P,R,S],[B,D,E,F,J,M,P,R,S,U],[B,D,E,F,J,M,P,R,U],[B,D,E,F,J,M,P,S],[B,D,E,F,J,M,P,S,U],[B,D,E,F,J,M,P,U],[B,D,E,F,J,M,Q],[B,D,E,F,J,M,Q,R],[B,D,E,F,J,M,R],[B,D,E,F,J,Q],[B,D,E,F,J,Q,R],[B,D,E,F,J,R],[B,D,E,G,H,J,M,N,P,Q,R,S,U],[B,D,E,G,H,J,M,N,P,Q,R,U],[B,D,E,G,H,J,M,N,P,Q,S,U],[B,D,E,G,H,J,M,N,P,Q,U],[B,D,E,G,H,J,M,N,P,R,S,U],[B,D,E,G,H,J,M,N,P,R,U],[B,D,E,G,H,J,M,N,P,S,U],[B,D,E,G,H,J,M,N,P,U],[B,D,E,G,H,J,M,P,Q,R,S,U],[B,D,E,G,H,J,M,P,Q,R,U],[B,D,E,G,H,J,M,P,Q,S,U],[B,D,E,G,H,J,M,P,Q,U],[B,D,E,G,H,J,M,P,R,S],[B,D,E,G,H,J,M,P,R,S,U],[B,D,E,G,H,J,M,P,R,U],[B,D,E,G,H,J,M,P,S,U],[B,D,E,G,H,J,M,P,U],[B,D,E,G,J],[B,D,E,G,J,M],[B,D,E,G,J,M,N,P,Q,R,S,U],[B,D,E,G,J,M,N,P,Q,R,U],[B,D,E,G,J,M,N,P,Q,S,U],[B,D,E,G,J,M,N,P,Q,U],[B,D,E,G,J,M,N,P,R,S,U],[B,D,E,G,J,M,N,P,R,U],[B,D,E,G,J,M,N,P,S,U],[B,D,E,G,J,M,N,P,U],[B,D,E,G,J,M,P],[B,D,E,G,J,M,P,Q],[B,D,E,G,J,M,P,Q,R],[B,D,E,G,J,M,P,Q,R,S],[B,D,E,G,J,M,P,Q,R,S,U],[B,D,E,G,J,M,P,Q,R,U],[B,D,E,G,J,M,P,Q,S],[B,D,E,G,J,M,P,Q,S,U],[B,D,E,G,J,M,P,Q,U],[B,D,E,G,J,M,P,R],[B,D,E,G,J,M,P,R,S],[B,D,E,G,J,M,P,R,S,U],[B,D,E,G,J,M,P,R,U],[B,D,E,G,J,M,P,S],[B,D,E,G,J,M,P,S,U],[B,D,E,G,J,M,P,U],[B,D,E,G,J,M,Q],[B,D,E,G,J,M,Q,R],[B,D,E,G,J,M,R],[B,D,E,G,J,Q],[B,D,E,G,J,Q,R],[B,D,E,G,J,R],[B,D,E,H,J,M,N,P,Q,R,S,U],[B,D,E,H,J,M,N,P,Q,R,U],[B,D,E,H,J,M,N,P,Q,S,U],[B,D,E,H,J,M,N,P,Q,U],[B,D,E,H,J,M,N,P,R,S,U],[B,D,E,H,J,M,N,P,R,U],[B,D,E,H,J,M,N,P,S,U],[B,D,E,H,J,M,N,P,U],[B,D,E,H,J,M,P,Q,R,S,U],[B,D,E,H,J,M,P,Q,R,U],[B,D,E,H,J,M,P,Q,S,U],[B,D,E,H,J,M,P,Q,U],[B,D,E,H,J,M,P,R,S,U],[B,D,E,H,J,M,P,R,U],[B,D,E,H,J,M,P,S],[B,D,E,H,J,M,P,S,U],[B,D,E,H,J,M,P,U],[B,D,E,J],[B,D,E,J,M],[B,D,E,J,M,N,P,Q,R,S,U],[B,D,E,J,M,N,P,Q,R,U],[B,D,E,J,M,N,P,Q,S,U],[B,D,E,J,M,N,P,Q,U],[B,D,E,J,M,N,P,R,S,U],[B,D,E,J,M,N,P,R,U],[B,D,E,J,M,N,P,S,U],[B,D,E,J,M,N,P,U],[B,D,E,J,M,P],[B,D,E,J,M,P,Q],[B,D,E,J,M,P,Q,R],[B,D,E,J,M,P,Q,R,S],[B,D,E,J,M,P,Q,R,S,U],[B,D,E,J,M,P,Q,R,U],[B,D,E,J,M,P,Q,S],[B,D,E,J,M,P,Q,S,U],[B,D,E,J,M,P,Q,U],[B,D,E,J,M,P,R],[B,D,E,J,M,P,R,S],[B,D,E,J,M,P,R,S,U],[B,D,E,J,M,P,R,U],[B,D,E,J,M,P,S],[B,D,E,J,M,P,S,U],[B,D,E,J,M,P,U],[B,D,E,J,M,Q],[B,D,E,J,M,Q,R],[B,D,E,J,M,R],[B,D,E,J,Q],[B,D,E,J,Q,R],[B,D,E,J,R],[B,D,F,G,H,J,M,N,P,Q,R,S,U],[B,D,F,G,H,J,M,N,P,Q,R,U],[B,D,F,G,H,J,M,N,P,Q,S,U],[B,D,F,G,H,J,M,N,P,Q,U],[B,D,F,G,H,J,M,N,P,R,S,U],[B,D,F,G,H,J,M,N,P,R,U],[B,D,F,G,H,J,M,N,P,S,U],[B,D,F,G,H,J,M,N,P,U],[B,D,F,G,H,J,M,P,Q,R,S],[B,D,F,G,H,J,M,P,Q,R,S,U],[B,D,F,G,H,J,M,P,Q,R,U],[B,D,F,G,H,J,M,P,Q,S,U],[B,D,F,G,H,J,M,P,Q,U],[B,D,F,G,H,J,M,P,R,S,U],[B,D,F,G,H,J,M,P,R,U],[B,D,F,G,H,J,M,P,S,U],[B,D,F,G,H,J,M,P,U],[B,D,F,G,J],[B,D,F,G,J,M],[B,D,F,G,J,M,N,P,Q,R,S,U],[B,D,F,G,J,M,N,P,Q,R,U],[B,D,F,G,J,M,N,P,Q,S,U],[B,D,F,G,J,M,N,P,Q,U],[B,D,F,G,J,M,N,P,R,S,U],[B,D,F,G,J,M,N,P,R,U],[B,D,F,G,J,M,N,P,S,U],[B,D,F,G,J,M,N,P,U],[B,D,F,G,J,M,P],[B,D,F,G,J,M,P,Q],[B,D,F,G,J,M,P,Q,R],[B,D,F,G,J,M,P,Q,R,S],[B,D,F,G,J,M,P,Q,R,S,U],[B,D,F,G,J,M,P,Q,R,U],[B,D,F,G,J,M,P,Q,S],[B,D,F,G,J,M,P,Q,S,U],[B,D,F,G,J,M,P,Q,U],[B,D,F,G,J,M,P,R],[B,D,F,G,J,M,P,R,S],[B,D,F,G,J,M,P,R,S,U],[B,D,F,G,J,M,P,R,U],[B,D,F,G,J,M,P,S],[B,D,F,G,J,M,P,S,U],[B,D,F,G,J,M,P,U],[B,D,F,G,J,M,Q],[B,D,F,G,J,M,Q,R],[B,D,F,G,J,M,R],[B,D,F,G,J,Q],[B,D,F,G,J,Q,R],[B,D,F,G,J,R],[B,D,F,H,J,M,N,P,Q,R,S,U],[B,D,F,H,J,M,N,P,Q,R,U],[B,D,F,H,J,M,N,P,Q,S,U],[B,D,F,H,J,M,N,P,Q,U],[B,D,F,H,J,M,N,P,R,S,U],[B,D,F,H,J,M,N,P,R,U],[B,D,F,H,J,M,N,P,S,U],[B,D,F,H,J,M,N,P,U],[B,D,F,H,J,M,P,Q,R,S,U],[B,D,F,H,J,M,P,Q,R,U],[B,D,F,H,J,M,P,Q,S],[B,D,F,H,J,M,P,Q,S,U],[B,D,F,H,J,M,P,Q,U],[B,D,F,H,J,M,P,R,S,U],[B,D,F,H,J,M,P,R,U],[B,D,F,H,J,M,P,S,U],[B,D,F,H,J,M,P,U],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N,P,Q,R,S,U],[B,D,F,J,M,N,P,Q,R,U],[B,D,F,J,M,N,P,Q,S,U],[B,D,F,J,M,N,P,Q,U],[B,D,F,J,M,N,P,R,S,U],[B,D,F,J,M,N,P,R,U],[B,D,F,J,M,N,P,S,U],[B,D,F,J,M,N,P,U],[B,D,F,J,M,P],[B,D,F,J,M,P,Q],[B,D,F,J,M,P,Q,R],[B,D,F,J,M,P,Q,R,S],[B,D,F,J,M,P,Q,R,S,U],[B,D,F,J,M,P,Q,R,U],[B,D,F,J,M,P,Q,S],[B,D,F,J,M,P,Q,S,U],[B,D,F,J,M,P,Q,U],[B,D,F,J,M,P,R],[B,D,F,J,M,P,R,S],[B,D,F,J,M,P,R,S,U],[B,D,F,J,M,P,R,U],[B,D,F,J,M,P,S],[B,D,F,J,M,P,S,U],[B,D,F,J,M,P,U],[B,D,F,J,M,Q],[B,D,F,J,M,Q,R],[B,D,F,J,M,R],[B,D,F,J,Q],[B,D,F,J,Q,R],[B,D,F,J,R],[B,D,G,H,J,M,N,P,Q,R,S,U],[B,D,G,H,J,M,N,P,Q,R,U],[B,D,G,H,J,M,N,P,Q,S,U],[B,D,G,H,J,M,N,P,Q,U],[B,D,G,H,J,M,N,P,R,S,U],[B,D,G,H,J,M,N,P,R,U],[B,D,G,H,J,M,N,P,S,U],[B,D,G,H,J,M,N,P,U],[B,D,G,H,J,M,P,Q,R,S,U],[B,D,G,H,J,M,P,Q,R,U],[B,D,G,H,J,M,P,Q,S,U],[B,D,G,H,J,M,P,Q,U],[B,D,G,H,J,M,P,R,S],[B,D,G,H,J,M,P,R,S,U],[B,D,G,H,J,M,P,R,U],[B,D,G,H,J,M,P,S,U],[B,D,G,H,J,M,P,U],[B,D,G,J],[B,D,G,J,M],[B,D,G,J,M,N,P,Q,R,S,U],[B,D,G,J,M,N,P,Q,R,U],[B,D,G,J,M,N,P,Q,S,U],[B,D,G,J,M,N,P,Q,U],[B,D,G,J,M,N,P,R,S,U],[B,D,G,J,M,N,P,R,U],[B,D,G,J,M,N,P,S,U],[B,D,G,J,M,N,P,U],[B,D,G,J,M,P],[B,D,G,J,M,P,Q],[B,D,G,J,M,P,Q,R],[B,D,G,J,M,P,Q,R,S],[B,D,G,J,M,P,Q,R,S,U],[B,D,G,J,M,P,Q,R,U],[B,D,G,J,M,P,Q,S],[B,D,G,J,M,P,Q,S,U],[B,D,G,J,M,P,Q,U],[B,D,G,J,M,P,R],[B,D,G,J,M,P,R,S],[B,D,G,J,M,P,R,S,U],[B,D,G,J,M,P,R,U],[B,D,G,J,M,P,S],[B,D,G,J,M,P,S,U],[B,D,G,J,M,P,U],[B,D,G,J,M,Q],[B,D,G,J,M,Q,R],[B,D,G,J,M,R],[B,D,G,J,Q],[B,D,G,J,Q,R],[B,D,G,J,R],[B,D,H,J,M,N,P,Q,R,S,U],[B,D,H,J,M,N,P,Q,R,U],[B,D,H,J,M,N,P,Q,S,U],[B,D,H,J,M,N,P,Q,U],[B,D,H,J,M,N,P,R,S,U],[B,D,H,J,M,N,P,R,U],[B,D,H,J,M,N,P,S,U],[B,D,H,J,M,N,P,U],[B,D,H,J,M,P,Q,R,S,U],[B,D,H,J,M,P,Q,R,U],[B,D,H,J,M,P,Q,S,U],[B,D,H,J,M,P,Q,U],[B,D,H,J,M,P,R,S,U],[B,D,H,J,M,P,R,U],[B,D,H,J,M,P,S],[B,D,H,J,M,P,S,U],[B,D,H,J,M,P,U],[B,D,J],[B,D,J,M],[B,D,J,M,N,P,Q,R,S,U],[B,D,J,M,N,P,Q,R,U],[B,D,J,M,N,P,Q,S,U],[B,D,J,M,N,P,Q,U],[B,D,J,M,N,P,R,S,U],[B,D,J,M,N,P,R,U],[B,D,J,M,N,P,S,U],[B,D,J,M,N,P,U],[B,D,J,M,P],[B,D,J,M,P,Q],[B,D,J,M,P,Q,R],[B,D,J,M,P,Q,R,S],[B,D,J,M,P,Q,R,S,U],[B,D,J,M,P,Q,R,U],[B,D,J,M,P,Q,S],[B,D,J,M,P,Q,S,U],[B,D,J,M,P,Q,U],[B,D,J,M,P,R],[B,D,J,M,P,R,S],[B,D,J,M,P,R,S,U],[B,D,J,M,P,R,U],[B,D,J,M,P,S],[B,D,J,M,P,S,U],[B,D,J,M,P,U],[B,D,J,M,Q],[B,D,J,M,Q,R],[B,D,J,M,R],[B,D,J,Q],[B,D,J,Q,R],[B,D,J,R],[B,E,F,G,H,J,M,N,P,Q,R,S,U],[B,E,F,G,H,J,M,N,P,Q,R,U],[B,E,F,G,H,J,M,N,P,Q,S,U],[B,E,F,G,H,J,M,N,P,Q,U],[B,E,F,G,H,J,M,N,P,R,S,U],[B,E,F,G,H,J,M,N,P,R,U],[B,E,F,G,H,J,M,N,P,S,U],[B,E,F,G,H,J,M,N,P,U],[B,E,F,G,H,J,M,P,Q,R,S],[B,E,F,G,H,J,M,P,Q,R,S,U],[B,E,F,G,H,J,M,P,Q,R,U],[B,E,F,G,H,J,M,P,Q,S,U],[B,E,F,G,H,J,M,P,Q,U],[B,E,F,G,H,J,M,P,R,S,U],[B,E,F,G,H,J,M,P,R,U],[B,E,F,G,H,J,M,P,S,U],[B,E,F,G,H,J,M,P,U],[B,E,F,G,J],[B,E,F,G,J,M],[B,E,F,G,J,M,N,P,Q,R,S,U],[B,E,F,G,J,M,N,P,Q,R,U],[B,E,F,G,J,M,N,P,Q,S,U],[B,E,F,G,J,M,N,P,Q,U],[B,E,F,G,J,M,N,P,R,S,U],[B,E,F,G,J,M,N,P,R,U],[B,E,F,G,J,M,N,P,S,U],[B,E,F,G,J,M,N,P,U],[B,E,F,G,J,M,P],[B,E,F,G,J,M,P,Q],[B,E,F,G,J,M,P,Q,R],[B,E,F,G,J,M,P,Q,R,S],[B,E,F,G,J,M,P,Q,R,S,U],[B,E,F,G,J,M,P,Q,R,U],[B,E,F,G,J,M,P,Q,S],[B,E,F,G,J,M,P,Q,S,U],[B,E,F,G,J,M,P,Q,U],[B,E,F,G,J,M,P,R],[B,E,F,G,J,M,P,R,S],[B,E,F,G,J,M,P,R,S,U],[B,E,F,G,J,M,P,R,U],[B,E,F,G,J,M,P,S],[B,E,F,G,J,M,P,S,U],[B,E,F,G,J,M,P,U],[B,E,F,G,J,M,Q],[B,E,F,G,J,M,Q,R],[B,E,F,G,J,M,R],[B,E,F,G,J,Q],[B,E,F,G,J,Q,R],[B,E,F,G,J,R],[B,E,F,H,J,M,N,P,Q,R,S,U],[B,E,F,H,J,M,N,P,Q,R,U],[B,E,F,H,J,M,N,P,Q,S,U],[B,E,F,H,J,M,N,P,Q,U],[B,E,F,H,J,M,N,P,R,S,U],[B,E,F,H,J,M,N,P,R,U],[B,E,F,H,J,M,N,P,S,U],[B,E,F,H,J,M,N,P,U],[B,E,F,H,J,M,P,Q,R,S,U],[B,E,F,H,J,M,P,Q,R,U],[B,E,F,H,J,M,P,Q,S],[B,E,F,H,J,M,P,Q,S,U],[B,E,F,H,J,M,P,Q,U],[B,E,F,H,J,M,P,R,S,U],[B,E,F,H,J,M,P,R,U],[B,E,F,H,J,M,P,S,U],[B,E,F,H,J,M,P,U],[B,E,F,J],[B,E,F,J,M],[B,E,F,J,M,N,P,Q,R,S,U],[B,E,F,J,M,N,P,Q,R,U],[B,E,F,J,M,N,P,Q,S,U],[B,E,F,J,M,N,P,Q,U],[B,E,F,J,M,N,P,R,S,U],[B,E,F,J,M,N,P,R,U],[B,E,F,J,M,N,P,S,U],[B,E,F,J,M,N,P,U],[B,E,F,J,M,P],[B,E,F,J,M,P,Q],[B,E,F,J,M,P,Q,R],[B,E,F,J,M,P,Q,R,S],[B,E,F,J,M,P,Q,R,S,U],[B,E,F,J,M,P,Q,R,U],[B,E,F,J,M,P,Q,S],[B,E,F,J,M,P,Q,S,U],[B,E,F,J,M,P,Q,U],[B,E,F,J,M,P,R],[B,E,F,J,M,P,R,S],[B,E,F,J,M,P,R,S,U],[B,E,F,J,M,P,R,U],[B,E,F,J,M,P,S],[B,E,F,J,M,P,S,U],[B,E,F,J,M,P,U],[B,E,F,J,M,Q],[B,E,F,J,M,Q,R],[B,E,F,J,M,R],[B,E,F,J,Q],[B,E,F,J,Q,R],[B,E,F,J,R],[B,E,G,H,J,M,N,P,Q,R,S,U],[B,E,G,H,J,M,N,P,Q,R,U],[B,E,G,H,J,M,N,P,Q,S,U],[B,E,G,H,J,M,N,P,Q,U],[B,E,G,H,J,M,N,P,R,S,U],[B,E,G,H,J,M,N,P,R,U],[B,E,G,H,J,M,N,P,S,U],[B,E,G,H,J,M,N,P,U],[B,E,G,H,J,M,P,Q,R,S,U],[B,E,G,H,J,M,P,Q,R,U],[B,E,G,H,J,M,P,Q,S,U],[B,E,G,H,J,M,P,Q,U],[B,E,G,H,J,M,P,R,S],[B,E,G,H,J,M,P,R,S,U],[B,E,G,H,J,M,P,R,U],[B,E,G,H,J,M,P,S,U],[B,E,G,H,J,M,P,U],[B,E,G,J],[B,E,G,J,M],[B,E,G,J,M,N,P,Q,R,S,U],[B,E,G,J,M,N,P,Q,R,U],[B,E,G,J,M,N,P,Q,S,U],[B,E,G,J,M,N,P,Q,U],[B,E,G,J,M,N,P,R,S,U],[B,E,G,J,M,N,P,R,U],[B,E,G,J,M,N,P,S,U],[B,E,G,J,M,N,P,U],[B,E,G,J,M,P],[B,E,G,J,M,P,Q],[B,E,G,J,M,P,Q,R],[B,E,G,J,M,P,Q,R,S],[B,E,G,J,M,P,Q,R,S,U],[B,E,G,J,M,P,Q,R,U],[B,E,G,J,M,P,Q,S],[B,E,G,J,M,P,Q,S,U],[B,E,G,J,M,P,Q,U],[B,E,G,J,M,P,R],[B,E,G,J,M,P,R,S],[B,E,G,J,M,P,R,S,U],[B,E,G,J,M,P,R,U],[B,E,G,J,M,P,S],[B,E,G,J,M,P,S,U],[B,E,G,J,M,P,U],[B,E,G,J,M,Q],[B,E,G,J,M,Q,R],[B,E,G,J,M,R],[B,E,G,J,Q],[B,E,G,J,Q,R],[B,E,G,J,R],[B,E,H,J,M,N,P,Q,R,S,U],[B,E,H,J,M,N,P,Q,R,U],[B,E,H,J,M,N,P,Q,S,U],[B,E,H,J,M,N,P,Q,U],[B,E,H,J,M,N,P,R,S,U],[B,E,H,J,M,N,P,R,U],[B,E,H,J,M,N,P,S,U],[B,E,H,J,M,N,P,U],[B,E,H,J,M,P,Q,R,S,U],[B,E,H,J,M,P,Q,R,U],[B,E,H,J,M,P,Q,S,U],[B,E,H,J,M,P,Q,U],[B,E,H,J,M,P,R,S,U],[B,E,H,J,M,P,R,U],[B,E,H,J,M,P,S],[B,E,H,J,M,P,S,U],[B,E,H,J,M,P,U],[B,E,J],[B,E,J,M],[B,E,J,M,N,P,Q,R,S,U],[B,E,J,M,N,P,Q,R,U],[B,E,J,M,N,P,Q,S,U],[B,E,J,M,N,P,Q,U],[B,E,J,M,N,P,R,S,U],[B,E,J,M,N,P,R,U],[B,E,J,M,N,P,S,U],[B,E,J,M,N,P,U],[B,E,J,M,P],[B,E,J,M,P,Q],[B,E,J,M,P,Q,R],[B,E,J,M,P,Q,R,S],[B,E,J,M,P,Q,R,S,U],[B,E,J,M,P,Q,R,U],[B,E,J,M,P,Q,S],[B,E,J,M,P,Q,S,U],[B,E,J,M,P,Q,U],[B,E,J,M,P,R],[B,E,J,M,P,R,S],[B,E,J,M,P,R,S,U],[B,E,J,M,P,R,U],[B,E,J,M,P,S],[B,E,J,M,P,S,U],[B,E,J,M,P,U],[B,E,J,M,Q],[B,E,J,M,Q,R],[B,E,J,M,R],[B,E,J,Q],[B,E,J,Q,R],[B,E,J,R],[B,F,G,H,J,M,N,P,Q,R,S,U],[B,F,G,H,J,M,N,P,Q,R,U],[B,F,G,H,J,M,N,P,Q,S,U],[B,F,G,H,J,M,N,P,Q,U],[B,F,G,H,J,M,N,P,R,S,U],[B,F,G,H,J,M,N,P,R,U],[B,F,G,H,J,M,N,P,S,U],[B,F,G,H,J,M,N,P,U],[B,F,G,H,J,M,P,Q,R,S],[B,F,G,H,J,M,P,Q,R,S,U],[B,F,G,H,J,M,P,Q,R,U],[B,F,G,H,J,M,P,Q,S,U],[B,F,G,H,J,M,P,Q,U],[B,F,G,H,J,M,P,R,S,U],[B,F,G,H,J,M,P,R,U],[B,F,G,H,J,M,P,S,U],[B,F,G,H,J,M,P,U],[B,F,G,J],[B,F,G,J,M],[B,F,G,J,M,N,P,Q,R,S,U],[B,F,G,J,M,N,P,Q,R,U],[B,F,G,J,M,N,P,Q,S,U],[B,F,G,J,M,N,P,Q,U],[B,F,G,J,M,N,P,R,S,U],[B,F,G,J,M,N,P,R,U],[B,F,G,J,M,N,P,S,U],[B,F,G,J,M,N,P,U],[B,F,G,J,M,P],[B,F,G,J,M,P,Q],[B,F,G,J,M,P,Q,R],[B,F,G,J,M,P,Q,R,S],[B,F,G,J,M,P,Q,R,S,U],[B,F,G,J,M,P,Q,R,U],[B,F,G,J,M,P,Q,S],[B,F,G,J,M,P,Q,S,U],[B,F,G,J,M,P,Q,U],[B,F,G,J,M,P,R],[B,F,G,J,M,P,R,S],[B,F,G,J,M,P,R,S,U],[B,F,G,J,M,P,R,U],[B,F,G,J,M,P,S],[B,F,G,J,M,P,S,U],[B,F,G,J,M,P,U],[B,F,G,J,M,Q],[B,F,G,J,M,Q,R],[B,F,G,J,M,R],[B,F,G,J,Q],[B,F,G,J,Q,R],[B,F,G,J,R],[B,F,H,J,M,N,P,Q,R,S,U],[B,F,H,J,M,N,P,Q,R,U],[B,F,H,J,M,N,P,Q,S,U],[B,F,H,J,M,N,P,Q,U],[B,F,H,J,M,N,P,R,S,U],[B,F,H,J,M,N,P,R,U],[B,F,H,J,M,N,P,S,U],[B,F,H,J,M,N,P,U],[B,F,H,J,M,P,Q,R,S,U],[B,F,H,J,M,P,Q,R,U],[B,F,H,J,M,P,Q,S],[B,F,H,J,M,P,Q,S,U],[B,F,H,J,M,P,Q,U],[B,F,H,J,M,P,R,S,U],[B,F,H,J,M,P,R,U],[B,F,H,J,M,P,S,U],[B,F,H,J,M,P,U],[B,F,J],[B,F,J,M],[B,F,J,M,N,P,Q,R,S,U],[B,F,J,M,N,P,Q,R,U],[B,F,J,M,N,P,Q,S,U],[B,F,J,M,N,P,Q,U],[B,F,J,M,N,P,R,S,U],[B,F,J,M,N,P,R,U],[B,F,J,M,N,P,S,U],[B,F,J,M,N,P,U],[B,F,J,M,P],[B,F,J,M,P,Q],[B,F,J,M,P,Q,R],[B,F,J,M,P,Q,R,S],[B,F,J,M,P,Q,R,S,U],[B,F,J,M,P,Q,R,U],[B,F,J,M,P,Q,S],[B,F,J,M,P,Q,S,U],[B,F,J,M,P,Q,U],[B,F,J,M,P,R],[B,F,J,M,P,R,S],[B,F,J,M,P,R,S,U],[B,F,J,M,P,R,U],[B,F,J,M,P,S],[B,F,J,M,P,S,U],[B,F,J,M,P,U],[B,F,J,M,Q],[B,F,J,M,Q,R],[B,F,J,M,R],[B,F,J,Q],[B,F,J,Q,R],[B,F,J,R],[B,G,H,J,M,N,P,Q,R,S,U],[B,G,H,J,M,N,P,Q,R,U],[B,G,H,J,M,N,P,Q,S,U],[B,G,H,J,M,N,P,Q,U],[B,G,H,J,M,N,P,R,S,U],[B,G,H,J,M,N,P,R,U],[B,G,H,J,M,N,P,S,U],[B,G,H,J,M,N,P,U],[B,G,H,J,M,P,Q,R,S,U],[B,G,H,J,M,P,Q,R,U],[B,G,H,J,M,P,Q,S,U],[B,G,H,J,M,P,Q,U],[B,G,H,J,M,P,R,S],[B,G,H,J,M,P,R,S,U],[B,G,H,J,M,P,R,U],[B,G,H,J,M,P,S,U],[B,G,H,J,M,P,U],[B,G,J],[B,G,J,M],[B,G,J,M,N,P,Q,R,S,U],[B,G,J,M,N,P,Q,R,U],[B,G,J,M,N,P,Q,S,U],[B,G,J,M,N,P,Q,U],[B,G,J,M,N,P,R,S,U],[B,G,J,M,N,P,R,U],[B,G,J,M,N,P,S,U],[B,G,J,M,N,P,U],[B,G,J,M,P],[B,G,J,M,P,Q],[B,G,J,M,P,Q,R],[B,G,J,M,P,Q,R,S],[B,G,J,M,P,Q,R,S,U],[B,G,J,M,P,Q,R,U],[B,G,J,M,P,Q,S],[B,G,J,M,P,Q,S,U],[B,G,J,M,P,Q,U],[B,G,J,M,P,R],[B,G,J,M,P,R,S],[B,G,J,M,P,R,S,U],[B,G,J,M,P,R,U],[B,G,J,M,P,S],[B,G,J,M,P,S,U],[B,G,J,M,P,U],[B,G,J,M,Q],[B,G,J,M,Q,R],[B,G,J,M,R],[B,G,J,Q],[B,G,J,Q,R],[B,G,J,R],[B,H,J,M,N,P,Q,R,S,U],[B,H,J,M,N,P,Q,R,U],[B,H,J,M,N,P,Q,S,U],[B,H,J,M,N,P,Q,U],[B,H,J,M,N,P,R,S,U],[B,H,J,M,N,P,R,U],[B,H,J,M,N,P,S,U],[B,H,J,M,N,P,U],[B,H,J,M,P,Q,R,S,U],[B,H,J,M,P,Q,R,U],[B,H,J,M,P,Q,S,U],[B,H,J,M,P,Q,U],[B,H,J,M,P,R,S,U],[B,H,J,M,P,R,U],[B,H,J,M,P,S],[B,H,J,M,P,S,U],[B,H,J,M,P,U],[B,J],[B,J,M],[B,J,M,N,P,Q,R,S,U],[B,J,M,N,P,Q,R,U],[B,J,M,N,P,Q,S,U],[B,J,M,N,P,Q,U],[B,J,M,N,P,R,S,U],[B,J,M,N,P,R,U],[B,J,M,N,P,S,U],[B,J,M,N,P,U],[B,J,M,P],[B,J,M,P,Q],[B,J,M,P,Q,R],[B,J,M,P,Q,R,S],[B,J,M,P,Q,R,S,U],[B,J,M,P,Q,R,U],[B,J,M,P,Q,S],[B,J,M,P,Q,S,U],[B,J,M,P,Q,U],[B,J,M,P,R],[B,J,M,P,R,S],[B,J,M,P,R,S,U],[B,J,M,P,R,U],[B,J,M,P,S],[B,J,M,P,S,U],[B,J,M,P,U],[B,J,M,Q],[B,J,M,Q,R],[B,J,M,R],[B,J,Q],[B,J,Q,R],[B,J,R],[C,D,E,F,G,H,J,M,N,P,Q,R,S,U],[C,D,E,F,G,H,J,M,N,P,Q,R,U],[C,D,E,F,G,H,J,M,N,P,Q,S,U],[C,D,E,F,G,H,J,M,N,P,Q,U],[C,D,E,F,G,H,J,M,N,P,R,S,U],[C,D,E,F,G,H,J,M,N,P,R,U],[C,D,E,F,G,H,J,M,N,P,S,U],[C,D,E,F,G,H,J,M,N,P,U],[C,D,E,F,G,H,J,M,P,Q,R,S],[C,D,E,F,G,H,J,M,P,Q,R,S,U],[C,D,E,F,G,H,J,M,P,Q,R,U],[C,D,E,F,G,H,J,M,P,Q,S,U],[C,D,E,F,G,H,J,M,P,Q,U],[C,D,E,F,G,H,J,M,P,R,S,U],[C,D,E,F,G,H,J,M,P,R,U],[C,D,E,F,G,H,J,M,P,S,U],[C,D,E,F,G,H,J,M,P,U],[C,D,E,F,G,J],[C,D,E,F,G,J,M],[C,D,E,F,G,J,M,N,P,Q,R,S,U],[C,D,E,F,G,J,M,N,P,Q,R,U],[C,D,E,F,G,J,M,N,P,Q,S,U],[C,D,E,F,G,J,M,N,P,Q,U],[C,D,E,F,G,J,M,N,P,R,S,U],[C,D,E,F,G,J,M,N,P,R,U],[C,D,E,F,G,J,M,N,P,S,U],[C,D,E,F,G,J,M,N,P,U],[C,D,E,F,G,J,M,P],[C,D,E,F,G,J,M,P,Q],[C,D,E,F,G,J,M,P,Q,R],[C,D,E,F,G,J,M,P,Q,R,S],[C,D,E,F,G,J,M,P,Q,R,S,U],[C,D,E,F,G,J,M,P,Q,R,U],[C,D,E,F,G,J,M,P,Q,S],[C,D,E,F,G,J,M,P,Q,S,U],[C,D,E,F,G,J,M,P,Q,U],[C,D,E,F,G,J,M,P,R],[C,D,E,F,G,J,M,P,R,S],[C,D,E,F,G,J,M,P,R,S,U],[C,D,E,F,G,J,M,P,R,U],[C,D,E,F,G,J,M,P,S],[C,D,E,F,G,J,M,P,S,U],[C,D,E,F,G,J,M,P,U],[C,D,E,F,G,J,M,Q],[C,D,E,F,G,J,M,Q,R],[C,D,E,F,G,J,M,R],[C,D,E,F,G,J,Q],[C,D,E,F,G,J,Q,R],[C,D,E,F,G,J,R],[C,D,E,F,H,J,M,N,P,Q,R,S,U],[C,D,E,F,H,J,M,N,P,Q,R,U],[C,D,E,F,H,J,M,N,P,Q,S,U],[C,D,E,F,H,J,M,N,P,Q,U],[C,D,E,F,H,J,M,N,P,R,S,U],[C,D,E,F,H,J,M,N,P,R,U],[C,D,E,F,H,J,M,N,P,S,U],[C,D,E,F,H,J,M,N,P,U],[C,D,E,F,H,J,M,P,Q,R,S,U],[C,D,E,F,H,J,M,P,Q,R,U],[C,D,E,F,H,J,M,P,Q,S],[C,D,E,F,H,J,M,P,Q,S,U],[C,D,E,F,H,J,M,P,Q,U],[C,D,E,F,H,J,M,P,R,S,U],[C,D,E,F,H,J,M,P,R,U],[C,D,E,F,H,J,M,P,S,U],[C,D,E,F,H,J,M,P,U],[C,D,E,F,J],[C,D,E,F,J,M],[C,D,E,F,J,M,N,P,Q,R,S,U],[C,D,E,F,J,M,N,P,Q,R,U],[C,D,E,F,J,M,N,P,Q,S,U],[C,D,E,F,J,M,N,P,Q,U],[C,D,E,F,J,M,N,P,R,S,U],[C,D,E,F,J,M,N,P,R,U],[C,D,E,F,J,M,N,P,S,U],[C,D,E,F,J,M,N,P,U],[C,D,E,F,J,M,P],[C,D,E,F,J,M,P,Q],[C,D,E,F,J,M,P,Q,R],[C,D,E,F,J,M,P,Q,R,S],[C,D,E,F,J,M,P,Q,R,S,U],[C,D,E,F,J,M,P,Q,R,U],[C,D,E,F,J,M,P,Q,S],[C,D,E,F,J,M,P,Q,S,U],[C,D,E,F,J,M,P,Q,U],[C,D,E,F,J,M,P,R],[C,D,E,F,J,M,P,R,S],[C,D,E,F,J,M,P,R,S,U],[C,D,E,F,J,M,P,R,U],[C,D,E,F,J,M,P,S],[C,D,E,F,J,M,P,S,U],[C,D,E,F,J,M,P,U],[C,D,E,F,J,M,Q],[C,D,E,F,J,M,Q,R],[C,D,E,F,J,M,R],[C,D,E,F,J,Q],[C,D,E,F,J,Q,R],[C,D,E,F,J,R],[C,D,E,G,H,J,M,N,P,Q,R,S,U],[C,D,E,G,H,J,M,N,P,Q,R,U],[C,D,E,G,H,J,M,N,P,Q,S,U],[C,D,E,G,H,J,M,N,P,Q,U],[C,D,E,G,H,J,M,N,P,R,S,U],[C,D,E,G,H,J,M,N,P,R,U],[C,D,E,G,H,J,M,N,P,S,U],[C,D,E,G,H,J,M,N,P,U],[C,D,E,G,H,J,M,P,Q,R,S,U],[C,D,E,G,H,J,M,P,Q,R,U],[C,D,E,G,H,J,M,P,Q,S,U],[C,D,E,G,H,J,M,P,Q,U],[C,D,E,G,H,J,M,P,R,S],[C,D,E,G,H,J,M,P,R,S,U],[C,D,E,G,H,J,M,P,R,U],[C,D,E,G,H,J,M,P,S,U],[C,D,E,G,H,J,M,P,U],[C,D,E,G,J],[C,D,E,G,J,M],[C,D,E,G,J,M,N,P,Q,R,S,U],[C,D,E,G,J,M,N,P,Q,R,U],[C,D,E,G,J,M,N,P,Q,S,U],[C,D,E,G,J,M,N,P,Q,U],[C,D,E,G,J,M,N,P,R,S,U],[C,D,E,G,J,M,N,P,R,U],[C,D,E,G,J,M,N,P,S,U],[C,D,E,G,J,M,N,P,U],[C,D,E,G,J,M,P],[C,D,E,G,J,M,P,Q],[C,D,E,G,J,M,P,Q,R],[C,D,E,G,J,M,P,Q,R,S],[C,D,E,G,J,M,P,Q,R,S,U],[C,D,E,G,J,M,P,Q,R,U],[C,D,E,G,J,M,P,Q,S],[C,D,E,G,J,M,P,Q,S,U],[C,D,E,G,J,M,P,Q,U],[C,D,E,G,J,M,P,R],[C,D,E,G,J,M,P,R,S],[C,D,E,G,J,M,P,R,S,U],[C,D,E,G,J,M,P,R,U],[C,D,E,G,J,M,P,S],[C,D,E,G,J,M,P,S,U],[C,D,E,G,J,M,P,U],[C,D,E,G,J,M,Q],[C,D,E,G,J,M,Q,R],[C,D,E,G,J,M,R],[C,D,E,G,J,Q],[C,D,E,G,J,Q,R],[C,D,E,G,J,R],[C,D,E,H,J,M,N,P,Q,R,S,U],[C,D,E,H,J,M,N,P,Q,R,U],[C,D,E,H,J,M,N,P,Q,S,U],[C,D,E,H,J,M,N,P,Q,U],[C,D,E,H,J,M,N,P,R,S,U],[C,D,E,H,J,M,N,P,R,U],[C,D,E,H,J,M,N,P,S,U],[C,D,E,H,J,M,N,P,U],[C,D,E,H,J,M,P,Q,R,S,U],[C,D,E,H,J,M,P,Q,R,U],[C,D,E,H,J,M,P,Q,S,U],[C,D,E,H,J,M,P,Q,U],[C,D,E,H,J,M,P,R,S,U],[C,D,E,H,J,M,P,R,U],[C,D,E,H,J,M,P,S],[C,D,E,H,J,M,P,S,U],[C,D,E,H,J,M,P,U],[C,D,E,J],[C,D,E,J,M],[C,D,E,J,M,N,P,Q,R,S,U],[C,D,E,J,M,N,P,Q,R,U],[C,D,E,J,M,N,P,Q,S,U],[C,D,E,J,M,N,P,Q,U],[C,D,E,J,M,N,P,R,S,U],[C,D,E,J,M,N,P,R,U],[C,D,E,J,M,N,P,S,U],[C,D,E,J,M,N,P,U],[C,D,E,J,M,P],[C,D,E,J,M,P,Q],[C,D,E,J,M,P,Q,R],[C,D,E,J,M,P,Q,R,S],[C,D,E,J,M,P,Q,R,S,U],[C,D,E,J,M,P,Q,R,U],[C,D,E,J,M,P,Q,S],[C,D,E,J,M,P,Q,S,U],[C,D,E,J,M,P,Q,U],[C,D,E,J,M,P,R],[C,D,E,J,M,P,R,S],[C,D,E,J,M,P,R,S,U],[C,D,E,J,M,P,R,U],[C,D,E,J,M,P,S],[C,D,E,J,M,P,S,U],[C,D,E,J,M,P,U],[C,D,E,J,M,Q],[C,D,E,J,M,Q,R],[C,D,E,J,M,R],[C,D,E,J,Q],[C,D,E,J,Q,R],[C,D,E,J,R],[C,D,F,G,H,J,M,N,P,Q,R,S,U],[C,D,F,G,H,J,M,N,P,Q,R,U],[C,D,F,G,H,J,M,N,P,Q,S,U],[C,D,F,G,H,J,M,N,P,Q,U],[C,D,F,G,H,J,M,N,P,R,S,U],[C,D,F,G,H,J,M,N,P,R,U],[C,D,F,G,H,J,M,N,P,S,U],[C,D,F,G,H,J,M,N,P,U],[C,D,F,G,H,J,M,P,Q,R,S],[C,D,F,G,H,J,M,P,Q,R,S,U],[C,D,F,G,H,J,M,P,Q,R,U],[C,D,F,G,H,J,M,P,Q,S,U],[C,D,F,G,H,J,M,P,Q,U],[C,D,F,G,H,J,M,P,R,S,U],[C,D,F,G,H,J,M,P,R,U],[C,D,F,G,H,J,M,P,S,U],[C,D,F,G,H,J,M,P,U],[C,D,F,G,J],[C,D,F,G,J,M],[C,D,F,G,J,M,N,P,Q,R,S,U],[C,D,F,G,J,M,N,P,Q,R,U],[C,D,F,G,J,M,N,P,Q,S,U],[C,D,F,G,J,M,N,P,Q,U],[C,D,F,G,J,M,N,P,R,S,U],[C,D,F,G,J,M,N,P,R,U],[C,D,F,G,J,M,N,P,S,U],[C,D,F,G,J,M,N,P,U],[C,D,F,G,J,M,P],[C,D,F,G,J,M,P,Q],[C,D,F,G,J,M,P,Q,R],[C,D,F,G,J,M,P,Q,R,S],[C,D,F,G,J,M,P,Q,R,S,U],[C,D,F,G,J,M,P,Q,R,U],[C,D,F,G,J,M,P,Q,S],[C,D,F,G,J,M,P,Q,S,U],[C,D,F,G,J,M,P,Q,U],[C,D,F,G,J,M,P,R],[C,D,F,G,J,M,P,R,S],[C,D,F,G,J,M,P,R,S,U],[C,D,F,G,J,M,P,R,U],[C,D,F,G,J,M,P,S],[C,D,F,G,J,M,P,S,U],[C,D,F,G,J,M,P,U],[C,D,F,G,J,M,Q],[C,D,F,G,J,M,Q,R],[C,D,F,G,J,M,R],[C,D,F,G,J,Q],[C,D,F,G,J,Q,R],[C,D,F,G,J,R],[C,D,F,H,J,M,N,P,Q,R,S,U],[C,D,F,H,J,M,N,P,Q,R,U],[C,D,F,H,J,M,N,P,Q,S,U],[C,D,F,H,J,M,N,P,Q,U],[C,D,F,H,J,M,N,P,R,S,U],[C,D,F,H,J,M,N,P,R,U],[C,D,F,H,J,M,N,P,S,U],[C,D,F,H,J,M,N,P,U],[C,D,F,H,J,M,P,Q,R,S,U],[C,D,F,H,J,M,P,Q,R,U],[C,D,F,H,J,M,P,Q,S],[C,D,F,H,J,M,P,Q,S,U],[C,D,F,H,J,M,P,Q,U],[C,D,F,H,J,M,P,R,S,U],[C,D,F,H,J,M,P,R,U],[C,D,F,H,J,M,P,S,U],[C,D,F,H,J,M,P,U],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N,P,Q,R,S,U],[C,D,F,J,M,N,P,Q,R,U],[C,D,F,J,M,N,P,Q,S,U],[C,D,F,J,M,N,P,Q,U],[C,D,F,J,M,N,P,R,S,U],[C,D,F,J,M,N,P,R,U],[C,D,F,J,M,N,P,S,U],[C,D,F,J,M,N,P,U],[C,D,F,J,M,P],[C,D,F,J,M,P,Q],[C,D,F,J,M,P,Q,R],[C,D,F,J,M,P,Q,R,S],[C,D,F,J,M,P,Q,R,S,U],[C,D,F,J,M,P,Q,R,U],[C,D,F,J,M,P,Q,S],[C,D,F,J,M,P,Q,S,U],[C,D,F,J,M,P,Q,U],[C,D,F,J,M,P,R],[C,D,F,J,M,P,R,S],[C,D,F,J,M,P,R,S,U],[C,D,F,J,M,P,R,U],[C,D,F,J,M,P,S],[C,D,F,J,M,P,S,U],[C,D,F,J,M,P,U],[C,D,F,J,M,Q],[C,D,F,J,M,Q,R],[C,D,F,J,M,R],[C,D,F,J,Q],[C,D,F,J,Q,R],[C,D,F,J,R],[C,D,G,H,J,M,N,P,Q,R,S,U],[C,D,G,H,J,M,N,P,Q,R,U],[C,D,G,H,J,M,N,P,Q,S,U],[C,D,G,H,J,M,N,P,Q,U],[C,D,G,H,J,M,N,P,R,S,U],[C,D,G,H,J,M,N,P,R,U],[C,D,G,H,J,M,N,P,S,U],[C,D,G,H,J,M,N,P,U],[C,D,G,H,J,M,P,Q,R,S,U],[C,D,G,H,J,M,P,Q,R,U],[C,D,G,H,J,M,P,Q,S,U],[C,D,G,H,J,M,P,Q,U],[C,D,G,H,J,M,P,R,S],[C,D,G,H,J,M,P,R,S,U],[C,D,G,H,J,M,P,R,U],[C,D,G,H,J,M,P,S,U],[C,D,G,H,J,M,P,U],[C,D,G,J],[C,D,G,J,M],[C,D,G,J,M,N,P,Q,R,S,U],[C,D,G,J,M,N,P,Q,R,U],[C,D,G,J,M,N,P,Q,S,U],[C,D,G,J,M,N,P,Q,U],[C,D,G,J,M,N,P,R,S,U],[C,D,G,J,M,N,P,R,U],[C,D,G,J,M,N,P,S,U],[C,D,G,J,M,N,P,U],[C,D,G,J,M,P],[C,D,G,J,M,P,Q],[C,D,G,J,M,P,Q,R],[C,D,G,J,M,P,Q,R,S],[C,D,G,J,M,P,Q,R,S,U],[C,D,G,J,M,P,Q,R,U],[C,D,G,J,M,P,Q,S],[C,D,G,J,M,P,Q,S,U],[C,D,G,J,M,P,Q,U],[C,D,G,J,M,P,R],[C,D,G,J,M,P,R,S],[C,D,G,J,M,P,R,S,U],[C,D,G,J,M,P,R,U],[C,D,G,J,M,P,S],[C,D,G,J,M,P,S,U],[C,D,G,J,M,P,U],[C,D,G,J,M,Q],[C,D,G,J,M,Q,R],[C,D,G,J,M,R],[C,D,G,J,Q],[C,D,G,J,Q,R],[C,D,G,J,R],[C,D,H,J,M,N,P,Q,R,S,U],[C,D,H,J,M,N,P,Q,R,U],[C,D,H,J,M,N,P,Q,S,U],[C,D,H,J,M,N,P,Q,U],[C,D,H,J,M,N,P,R,S,U],[C,D,H,J,M,N,P,R,U],[C,D,H,J,M,N,P,S,U],[C,D,H,J,M,N,P,U],[C,D,H,J,M,P,Q,R,S,U],[C,D,H,J,M,P,Q,R,U],[C,D,H,J,M,P,Q,S,U],[C,D,H,J,M,P,Q,U],[C,D,H,J,M,P,R,S,U],[C,D,H,J,M,P,R,U],[C,D,H,J,M,P,S],[C,D,H,J,M,P,S,U],[C,D,H,J,M,P,U],[C,D,J],[C,D,J,M],[C,D,J,M,N,P,Q,R,S,U],[C,D,J,M,N,P,Q,R,U],[C,D,J,M,N,P,Q,S,U],[C,D,J,M,N,P,Q,U],[C,D,J,M,N,P,R,S,U],[C,D,J,M,N,P,R,U],[C,D,J,M,N,P,S,U],[C,D,J,M,N,P,U],[C,D,J,M,P],[C,D,J,M,P,Q],[C,D,J,M,P,Q,R],[C,D,J,M,P,Q,R,S],[C,D,J,M,P,Q,R,S,U],[C,D,J,M,P,Q,R,U],[C,D,J,M,P,Q,S],[C,D,J,M,P,Q,S,U],[C,D,J,M,P,Q,U],[C,D,J,M,P,R],[C,D,J,M,P,R,S],[C,D,J,M,P,R,S,U],[C,D,J,M,P,R,U],[C,D,J,M,P,S],[C,D,J,M,P,S,U],[C,D,J,M,P,U],[C,D,J,M,Q],[C,D,J,M,Q,R],[C,D,J,M,R],[C,D,J,Q],[C,D,J,Q,R],[C,D,J,R],[C,E,F,G,H,J,M,N,P,Q,R,S,U],[C,E,F,G,H,J,M,N,P,Q,R,U],[C,E,F,G,H,J,M,N,P,Q,S,U],[C,E,F,G,H,J,M,N,P,Q,U],[C,E,F,G,H,J,M,N,P,R,S,U],[C,E,F,G,H,J,M,N,P,R,U],[C,E,F,G,H,J,M,N,P,S,U],[C,E,F,G,H,J,M,N,P,U],[C,E,F,G,H,J,M,P,Q,R,S],[C,E,F,G,H,J,M,P,Q,R,S,U],[C,E,F,G,H,J,M,P,Q,R,U],[C,E,F,G,H,J,M,P,Q,S,U],[C,E,F,G,H,J,M,P,Q,U],[C,E,F,G,H,J,M,P,R,S,U],[C,E,F,G,H,J,M,P,R,U],[C,E,F,G,H,J,M,P,S,U],[C,E,F,G,H,J,M,P,U],[C,E,F,G,J],[C,E,F,G,J,M],[C,E,F,G,J,M,N,P,Q,R,S,U],[C,E,F,G,J,M,N,P,Q,R,U],[C,E,F,G,J,M,N,P,Q,S,U],[C,E,F,G,J,M,N,P,Q,U],[C,E,F,G,J,M,N,P,R,S,U],[C,E,F,G,J,M,N,P,R,U],[C,E,F,G,J,M,N,P,S,U],[C,E,F,G,J,M,N,P,U],[C,E,F,G,J,M,P],[C,E,F,G,J,M,P,Q],[C,E,F,G,J,M,P,Q,R],[C,E,F,G,J,M,P,Q,R,S],[C,E,F,G,J,M,P,Q,R,S,U],[C,E,F,G,J,M,P,Q,R,U],[C,E,F,G,J,M,P,Q,S],[C,E,F,G,J,M,P,Q,S,U],[C,E,F,G,J,M,P,Q,U],[C,E,F,G,J,M,P,R],[C,E,F,G,J,M,P,R,S],[C,E,F,G,J,M,P,R,S,U],[C,E,F,G,J,M,P,R,U],[C,E,F,G,J,M,P,S],[C,E,F,G,J,M,P,S,U],[C,E,F,G,J,M,P,U],[C,E,F,G,J,M,Q],[C,E,F,G,J,M,Q,R],[C,E,F,G,J,M,R],[C,E,F,G,J,Q],[C,E,F,G,J,Q,R],[C,E,F,G,J,R],[C,E,F,H,J,M,N,P,Q,R,S,U],[C,E,F,H,J,M,N,P,Q,R,U],[C,E,F,H,J,M,N,P,Q,S,U],[C,E,F,H,J,M,N,P,Q,U],[C,E,F,H,J,M,N,P,R,S,U],[C,E,F,H,J,M,N,P,R,U],[C,E,F,H,J,M,N,P,S,U],[C,E,F,H,J,M,N,P,U],[C,E,F,H,J,M,P,Q,R,S,U],[C,E,F,H,J,M,P,Q,R,U],[C,E,F,H,J,M,P,Q,S],[C,E,F,H,J,M,P,Q,S,U],[C,E,F,H,J,M,P,Q,U],[C,E,F,H,J,M,P,R,S,U],[C,E,F,H,J,M,P,R,U],[C,E,F,H,J,M,P,S,U],[C,E,F,H,J,M,P,U],[C,E,F,J],[C,E,F,J,M],[C,E,F,J,M,N,P,Q,R,S,U],[C,E,F,J,M,N,P,Q,R,U],[C,E,F,J,M,N,P,Q,S,U],[C,E,F,J,M,N,P,Q,U],[C,E,F,J,M,N,P,R,S,U],[C,E,F,J,M,N,P,R,U],[C,E,F,J,M,N,P,S,U],[C,E,F,J,M,N,P,U],[C,E,F,J,M,P],[C,E,F,J,M,P,Q],[C,E,F,J,M,P,Q,R],[C,E,F,J,M,P,Q,R,S],[C,E,F,J,M,P,Q,R,S,U],[C,E,F,J,M,P,Q,R,U],[C,E,F,J,M,P,Q,S],[C,E,F,J,M,P,Q,S,U],[C,E,F,J,M,P,Q,U],[C,E,F,J,M,P,R],[C,E,F,J,M,P,R,S],[C,E,F,J,M,P,R,S,U],[C,E,F,J,M,P,R,U],[C,E,F,J,M,P,S],[C,E,F,J,M,P,S,U],[C,E,F,J,M,P,U],[C,E,F,J,M,Q],[C,E,F,J,M,Q,R],[C,E,F,J,M,R],[C,E,F,J,Q],[C,E,F,J,Q,R],[C,E,F,J,R],[C,E,G,H,J,M,N,P,Q,R,S,U],[C,E,G,H,J,M,N,P,Q,R,U],[C,E,G,H,J,M,N,P,Q,S,U],[C,E,G,H,J,M,N,P,Q,U],[C,E,G,H,J,M,N,P,R,S,U],[C,E,G,H,J,M,N,P,R,U],[C,E,G,H,J,M,N,P,S,U],[C,E,G,H,J,M,N,P,U],[C,E,G,H,J,M,P,Q,R,S,U],[C,E,G,H,J,M,P,Q,R,U],[C,E,G,H,J,M,P,Q,S,U],[C,E,G,H,J,M,P,Q,U],[C,E,G,H,J,M,P,R,S],[C,E,G,H,J,M,P,R,S,U],[C,E,G,H,J,M,P,R,U],[C,E,G,H,J,M,P,S,U],[C,E,G,H,J,M,P,U],[C,E,G,J],[C,E,G,J,M],[C,E,G,J,M,N,P,Q,R,S,U],[C,E,G,J,M,N,P,Q,R,U],[C,E,G,J,M,N,P,Q,S,U],[C,E,G,J,M,N,P,Q,U],[C,E,G,J,M,N,P,R,S,U],[C,E,G,J,M,N,P,R,U],[C,E,G,J,M,N,P,S,U],[C,E,G,J,M,N,P,U],[C,E,G,J,M,P],[C,E,G,J,M,P,Q],[C,E,G,J,M,P,Q,R],[C,E,G,J,M,P,Q,R,S],[C,E,G,J,M,P,Q,R,S,U],[C,E,G,J,M,P,Q,R,U],[C,E,G,J,M,P,Q,S],[C,E,G,J,M,P,Q,S,U],[C,E,G,J,M,P,Q,U],[C,E,G,J,M,P,R],[C,E,G,J,M,P,R,S],[C,E,G,J,M,P,R,S,U],[C,E,G,J,M,P,R,U],[C,E,G,J,M,P,S],[C,E,G,J,M,P,S,U],[C,E,G,J,M,P,U],[C,E,G,J,M,Q],[C,E,G,J,M,Q,R],[C,E,G,J,M,R],[C,E,G,J,Q],[C,E,G,J,Q,R],[C,E,G,J,R],[C,E,H,J,M,N,P,Q,R,S,U],[C,E,H,J,M,N,P,Q,R,U],[C,E,H,J,M,N,P,Q,S,U],[C,E,H,J,M,N,P,Q,U],[C,E,H,J,M,N,P,R,S,U],[C,E,H,J,M,N,P,R,U],[C,E,H,J,M,N,P,S,U],[C,E,H,J,M,N,P,U],[C,E,H,J,M,P,Q,R,S,U],[C,E,H,J,M,P,Q,R,U],[C,E,H,J,M,P,Q,S,U],[C,E,H,J,M,P,Q,U],[C,E,H,J,M,P,R,S,U],[C,E,H,J,M,P,R,U],[C,E,H,J,M,P,S],[C,E,H,J,M,P,S,U],[C,E,H,J,M,P,U],[C,E,J],[C,E,J,M],[C,E,J,M,N,P,Q,R,S,U],[C,E,J,M,N,P,Q,R,U],[C,E,J,M,N,P,Q,S,U],[C,E,J,M,N,P,Q,U],[C,E,J,M,N,P,R,S,U],[C,E,J,M,N,P,R,U],[C,E,J,M,N,P,S,U],[C,E,J,M,N,P,U],[C,E,J,M,P],[C,E,J,M,P,Q],[C,E,J,M,P,Q,R],[C,E,J,M,P,Q,R,S],[C,E,J,M,P,Q,R,S,U],[C,E,J,M,P,Q,R,U],[C,E,J,M,P,Q,S],[C,E,J,M,P,Q,S,U],[C,E,J,M,P,Q,U],[C,E,J,M,P,R],[C,E,J,M,P,R,S],[C,E,J,M,P,R,S,U],[C,E,J,M,P,R,U],[C,E,J,M,P,S],[C,E,J,M,P,S,U],[C,E,J,M,P,U],[C,E,J,M,Q],[C,E,J,M,Q,R],[C,E,J,M,R],[C,E,J,Q],[C,E,J,Q,R],[C,E,J,R],[C,F,G,H,J,M,N,P,Q,R,S,U],[C,F,G,H,J,M,N,P,Q,R,U],[C,F,G,H,J,M,N,P,Q,S,U],[C,F,G,H,J,M,N,P,Q,U],[C,F,G,H,J,M,N,P,R,S,U],[C,F,G,H,J,M,N,P,R,U],[C,F,G,H,J,M,N,P,S,U],[C,F,G,H,J,M,N,P,U],[C,F,G,H,J,M,P,Q,R,S],[C,F,G,H,J,M,P,Q,R,S,U],[C,F,G,H,J,M,P,Q,R,U],[C,F,G,H,J,M,P,Q,S,U],[C,F,G,H,J,M,P,Q,U],[C,F,G,H,J,M,P,R,S,U],[C,F,G,H,J,M,P,R,U],[C,F,G,H,J,M,P,S,U],[C,F,G,H,J,M,P,U],[C,F,G,J],[C,F,G,J,M],[C,F,G,J,M,N,P,Q,R,S,U],[C,F,G,J,M,N,P,Q,R,U],[C,F,G,J,M,N,P,Q,S,U],[C,F,G,J,M,N,P,Q,U],[C,F,G,J,M,N,P,R,S,U],[C,F,G,J,M,N,P,R,U],[C,F,G,J,M,N,P,S,U],[C,F,G,J,M,N,P,U],[C,F,G,J,M,P],[C,F,G,J,M,P,Q],[C,F,G,J,M,P,Q,R],[C,F,G,J,M,P,Q,R,S],[C,F,G,J,M,P,Q,R,S,U],[C,F,G,J,M,P,Q,R,U],[C,F,G,J,M,P,Q,S],[C,F,G,J,M,P,Q,S,U],[C,F,G,J,M,P,Q,U],[C,F,G,J,M,P,R],[C,F,G,J,M,P,R,S],[C,F,G,J,M,P,R,S,U],[C,F,G,J,M,P,R,U],[C,F,G,J,M,P,S],[C,F,G,J,M,P,S,U],[C,F,G,J,M,P,U],[C,F,G,J,M,Q],[C,F,G,J,M,Q,R],[C,F,G,J,M,R],[C,F,G,J,Q],[C,F,G,J,Q,R],[C,F,G,J,R],[C,F,H,J,M,N,P,Q,R,S,U],[C,F,H,J,M,N,P,Q,R,U],[C,F,H,J,M,N,P,Q,S,U],[C,F,H,J,M,N,P,Q,U],[C,F,H,J,M,N,P,R,S,U],[C,F,H,J,M,N,P,R,U],[C,F,H,J,M,N,P,S,U],[C,F,H,J,M,N,P,U],[C,F,H,J,M,P,Q,R,S,U],[C,F,H,J,M,P,Q,R,U],[C,F,H,J,M,P,Q,S],[C,F,H,J,M,P,Q,S,U],[C,F,H,J,M,P,Q,U],[C,F,H,J,M,P,R,S,U],[C,F,H,J,M,P,R,U],[C,F,H,J,M,P,S,U],[C,F,H,J,M,P,U],[C,F,J],[C,F,J,M],[C,F,J,M,N,P,Q,R,S,U],[C,F,J,M,N,P,Q,R,U],[C,F,J,M,N,P,Q,S,U],[C,F,J,M,N,P,Q,U],[C,F,J,M,N,P,R,S,U],[C,F,J,M,N,P,R,U],[C,F,J,M,N,P,S,U],[C,F,J,M,N,P,U],[C,F,J,M,P],[C,F,J,M,P,Q],[C,F,J,M,P,Q,R],[C,F,J,M,P,Q,R,S],[C,F,J,M,P,Q,R,S,U],[C,F,J,M,P,Q,R,U],[C,F,J,M,P,Q,S],[C,F,J,M,P,Q,S,U],[C,F,J,M,P,Q,U],[C,F,J,M,P,R],[C,F,J,M,P,R,S],[C,F,J,M,P,R,S,U],[C,F,J,M,P,R,U],[C,F,J,M,P,S],[C,F,J,M,P,S,U],[C,F,J,M,P,U],[C,F,J,M,Q],[C,F,J,M,Q,R],[C,F,J,M,R],[C,F,J,Q],[C,F,J,Q,R],[C,F,J,R],[C,G,H,J,M,N,P,Q,R,S,U],[C,G,H,J,M,N,P,Q,R,U],[C,G,H,J,M,N,P,Q,S,U],[C,G,H,J,M,N,P,Q,U],[C,G,H,J,M,N,P,R,S,U],[C,G,H,J,M,N,P,R,U],[C,G,H,J,M,N,P,S,U],[C,G,H,J,M,N,P,U],[C,G,H,J,M,P,Q,R,S,U],[C,G,H,J,M,P,Q,R,U],[C,G,H,J,M,P,Q,S,U],[C,G,H,J,M,P,Q,U],[C,G,H,J,M,P,R,S],[C,G,H,J,M,P,R,S,U],[C,G,H,J,M,P,R,U],[C,G,H,J,M,P,S,U],[C,G,H,J,M,P,U],[C,G,J],[C,G,J,M],[C,G,J,M,N,P,Q,R,S,U],[C,G,J,M,N,P,Q,R,U],[C,G,J,M,N,P,Q,S,U],[C,G,J,M,N,P,Q,U],[C,G,J,M,N,P,R,S,U],[C,G,J,M,N,P,R,U],[C,G,J,M,N,P,S,U],[C,G,J,M,N,P,U],[C,G,J,M,P],[C,G,J,M,P,Q],[C,G,J,M,P,Q,R],[C,G,J,M,P,Q,R,S],[C,G,J,M,P,Q,R,S,U],[C,G,J,M,P,Q,R,U],[C,G,J,M,P,Q,S],[C,G,J,M,P,Q,S,U],[C,G,J,M,P,Q,U],[C,G,J,M,P,R],[C,G,J,M,P,R,S],[C,G,J,M,P,R,S,U],[C,G,J,M,P,R,U],[C,G,J,M,P,S],[C,G,J,M,P,S,U],[C,G,J,M,P,U],[C,G,J,M,Q],[C,G,J,M,Q,R],[C,G,J,M,R],[C,G,J,Q],[C,G,J,Q,R],[C,G,J,R],[C,H,J,M,N,P,Q,R,S,U],[C,H,J,M,N,P,Q,R,U],[C,H,J,M,N,P,Q,S,U],[C,H,J,M,N,P,Q,U],[C,H,J,M,N,P,R,S,U],[C,H,J,M,N,P,R,U],[C,H,J,M,N,P,S,U],[C,H,J,M,N,P,U],[C,H,J,M,P,Q,R,S,U],[C,H,J,M,P,Q,R,U],[C,H,J,M,P,Q,S,U],[C,H,J,M,P,Q,U],[C,H,J,M,P,R,S,U],[C,H,J,M,P,R,U],[C,H,J,M,P,S],[C,H,J,M,P,S,U],[C,H,J,M,P,U],[C,J],[C,J,M],[C,J,M,N,P,Q,R,S,U],[C,J,M,N,P,Q,R,U],[C,J,M,N,P,Q,S,U],[C,J,M,N,P,Q,U],[C,J,M,N,P,R,S,U],[C,J,M,N,P,R,U],[C,J,M,N,P,S,U],[C,J,M,N,P,U],[C,J,M,P],[C,J,M,P,Q],[C,J,M,P,Q,R],[C,J,M,P,Q,R,S],[C,J,M,P,Q,R,S,U],[C,J,M,P,Q,R,U],[C,J,M,P,Q,S],[C,J,M,P,Q,S,U],[C,J,M,P,Q,U],[C,J,M,P,R],[C,J,M,P,R,S],[C,J,M,P,R,S,U],[C,J,M,P,R,U],[C,J,M,P,S],[C,J,M,P,S,U],[C,J,M,P,U],[C,J,M,Q],[C,J,M,Q,R],[C,J,M,R],[C,J,Q],[C,J,Q,R],[C,J,R],[D],[D,E,F,G,H,J,M,N,P,Q,R,S,U],[D,E,F,G,H,J,M,N,P,Q,R,U],[D,E,F,G,H,J,M,N,P,Q,S,U],[D,E,F,G,H,J,M,N,P,Q,U],[D,E,F,G,H,J,M,N,P,R,S,U],[D,E,F,G,H,J,M,N,P,R,U],[D,E,F,G,H,J,M,N,P,S,U],[D,E,F,G,H,J,M,N,P,U],[D,E,F,G,H,J,M,P,Q,R,S],[D,E,F,G,H,J,M,P,Q,R,S,U],[D,E,F,G,H,J,M,P,Q,R,U],[D,E,F,G,H,J,M,P,Q,S,U],[D,E,F,G,H,J,M,P,Q,U],[D,E,F,G,H,J,M,P,R,S,U],[D,E,F,G,H,J,M,P,R,U],[D,E,F,G,H,J,M,P,S,U],[D,E,F,G,H,J,M,P,U],[D,E,F,G,J],[D,E,F,G,J,M],[D,E,F,G,J,M,N,P,Q,R,S,U],[D,E,F,G,J,M,N,P,Q,R,U],[D,E,F,G,J,M,N,P,Q,S,U],[D,E,F,G,J,M,N,P,Q,U],[D,E,F,G,J,M,N,P,R,S,U],[D,E,F,G,J,M,N,P,R,U],[D,E,F,G,J,M,N,P,S,U],[D,E,F,G,J,M,N,P,U],[D,E,F,G,J,M,P],[D,E,F,G,J,M,P,Q],[D,E,F,G,J,M,P,Q,R],[D,E,F,G,J,M,P,Q,R,S],[D,E,F,G,J,M,P,Q,R,S,U],[D,E,F,G,J,M,P,Q,R,U],[D,E,F,G,J,M,P,Q,S],[D,E,F,G,J,M,P,Q,S,U],[D,E,F,G,J,M,P,Q,U],[D,E,F,G,J,M,P,R],[D,E,F,G,J,M,P,R,S],[D,E,F,G,J,M,P,R,S,U],[D,E,F,G,J,M,P,R,U],[D,E,F,G,J,M,P,S],[D,E,F,G,J,M,P,S,U],[D,E,F,G,J,M,P,U],[D,E,F,G,J,M,Q],[D,E,F,G,J,M,Q,R],[D,E,F,G,J,M,R],[D,E,F,G,J,Q],[D,E,F,G,J,Q,R],[D,E,F,G,J,R],[D,E,F,H,J,M,N,P,Q,R,S,U],[D,E,F,H,J,M,N,P,Q,R,U],[D,E,F,H,J,M,N,P,Q,S,U],[D,E,F,H,J,M,N,P,Q,U],[D,E,F,H,J,M,N,P,R,S,U],[D,E,F,H,J,M,N,P,R,U],[D,E,F,H,J,M,N,P,S,U],[D,E,F,H,J,M,N,P,U],[D,E,F,H,J,M,P,Q,R,S,U],[D,E,F,H,J,M,P,Q,R,U],[D,E,F,H,J,M,P,Q,S],[D,E,F,H,J,M,P,Q,S,U],[D,E,F,H,J,M,P,Q,U],[D,E,F,H,J,M,P,R,S,U],[D,E,F,H,J,M,P,R,U],[D,E,F,H,J,M,P,S,U],[D,E,F,H,J,M,P,U],[D,E,F,J],[D,E,F,J,M],[D,E,F,J,M,N,P,Q,R,S,U],[D,E,F,J,M,N,P,Q,R,U],[D,E,F,J,M,N,P,Q,S,U],[D,E,F,J,M,N,P,Q,U],[D,E,F,J,M,N,P,R,S,U],[D,E,F,J,M,N,P,R,U],[D,E,F,J,M,N,P,S,U],[D,E,F,J,M,N,P,U],[D,E,F,J,M,P],[D,E,F,J,M,P,Q],[D,E,F,J,M,P,Q,R],[D,E,F,J,M,P,Q,R,S],[D,E,F,J,M,P,Q,R,S,U],[D,E,F,J,M,P,Q,R,U],[D,E,F,J,M,P,Q,S],[D,E,F,J,M,P,Q,S,U],[D,E,F,J,M,P,Q,U],[D,E,F,J,M,P,R],[D,E,F,J,M,P,R,S],[D,E,F,J,M,P,R,S,U],[D,E,F,J,M,P,R,U],[D,E,F,J,M,P,S],[D,E,F,J,M,P,S,U],[D,E,F,J,M,P,U],[D,E,F,J,M,Q],[D,E,F,J,M,Q,R],[D,E,F,J,M,R],[D,E,F,J,Q],[D,E,F,J,Q,R],[D,E,F,J,R],[D,E,G,H,J,M,N,P,Q,R,S,U],[D,E,G,H,J,M,N,P,Q,R,U],[D,E,G,H,J,M,N,P,Q,S,U],[D,E,G,H,J,M,N,P,Q,U],[D,E,G,H,J,M,N,P,R,S,U],[D,E,G,H,J,M,N,P,R,U],[D,E,G,H,J,M,N,P,S,U],[D,E,G,H,J,M,N,P,U],[D,E,G,H,J,M,P,Q,R,S,U],[D,E,G,H,J,M,P,Q,R,U],[D,E,G,H,J,M,P,Q,S,U],[D,E,G,H,J,M,P,Q,U],[D,E,G,H,J,M,P,R,S],[D,E,G,H,J,M,P,R,S,U],[D,E,G,H,J,M,P,R,U],[D,E,G,H,J,M,P,S,U],[D,E,G,H,J,M,P,U],[D,E,G,J],[D,E,G,J,M],[D,E,G,J,M,N,P,Q,R,S,U],[D,E,G,J,M,N,P,Q,R,U],[D,E,G,J,M,N,P,Q,S,U],[D,E,G,J,M,N,P,Q,U],[D,E,G,J,M,N,P,R,S,U],[D,E,G,J,M,N,P,R,U],[D,E,G,J,M,N,P,S,U],[D,E,G,J,M,N,P,U],[D,E,G,J,M,P],[D,E,G,J,M,P,Q],[D,E,G,J,M,P,Q,R],[D,E,G,J,M,P,Q,R,S],[D,E,G,J,M,P,Q,R,S,U],[D,E,G,J,M,P,Q,R,U],[D,E,G,J,M,P,Q,S],[D,E,G,J,M,P,Q,S,U],[D,E,G,J,M,P,Q,U],[D,E,G,J,M,P,R],[D,E,G,J,M,P,R,S],[D,E,G,J,M,P,R,S,U],[D,E,G,J,M,P,R,U],[D,E,G,J,M,P,S],[D,E,G,J,M,P,S,U],[D,E,G,J,M,P,U],[D,E,G,J,M,Q],[D,E,G,J,M,Q,R],[D,E,G,J,M,R],[D,E,G,J,Q],[D,E,G,J,Q,R],[D,E,G,J,R],[D,E,H,J,M,N,P,Q,R,S,U],[D,E,H,J,M,N,P,Q,R,U],[D,E,H,J,M,N,P,Q,S,U],[D,E,H,J,M,N,P,Q,U],[D,E,H,J,M,N,P,R,S,U],[D,E,H,J,M,N,P,R,U],[D,E,H,J,M,N,P,S,U],[D,E,H,J,M,N,P,U],[D,E,H,J,M,P,Q,R,S,U],[D,E,H,J,M,P,Q,R,U],[D,E,H,J,M,P,Q,S,U],[D,E,H,J,M,P,Q,U],[D,E,H,J,M,P,R,S,U],[D,E,H,J,M,P,R,U],[D,E,H,J,M,P,S],[D,E,H,J,M,P,S,U],[D,E,H,J,M,P,U],[D,E,J],[D,E,J,M],[D,E,J,M,N,P,Q,R,S,U],[D,E,J,M,N,P,Q,R,U],[D,E,J,M,N,P,Q,S,U],[D,E,J,M,N,P,Q,U],[D,E,J,M,N,P,R,S,U],[D,E,J,M,N,P,R,U],[D,E,J,M,N,P,S,U],[D,E,J,M,N,P,U],[D,E,J,M,P],[D,E,J,M,P,Q],[D,E,J,M,P,Q,R],[D,E,J,M,P,Q,R,S],[D,E,J,M,P,Q,R,S,U],[D,E,J,M,P,Q,R,U],[D,E,J,M,P,Q,S],[D,E,J,M,P,Q,S,U],[D,E,J,M,P,Q,U],[D,E,J,M,P,R],[D,E,J,M,P,R,S],[D,E,J,M,P,R,S,U],[D,E,J,M,P,R,U],[D,E,J,M,P,S],[D,E,J,M,P,S,U],[D,E,J,M,P,U],[D,E,J,M,Q],[D,E,J,M,Q,R],[D,E,J,M,R],[D,E,J,Q],[D,E,J,Q,R],[D,E,J,R],[D,F,G],[D,F,G,H,J,M,N,P,Q,R,S,U],[D,F,G,H,J,M,N,P,Q,R,U],[D,F,G,H,J,M,N,P,Q,S,U],[D,F,G,H,J,M,N,P,Q,U],[D,F,G,H,J,M,N,P,R,S,U],[D,F,G,H,J,M,N,P,R,U],[D,F,G,H,J,M,N,P,S,U],[D,F,G,H,J,M,N,P,U],[D,F,G,H,J,M,P,Q,R,S,U],[D,F,G,H,J,M,P,Q,R,U],[D,F,G,H,J,M,P,Q,S,U],[D,F,G,H,J,M,P,Q,U],[D,F,G,H,J,M,P,R,S,U],[D,F,G,H,J,M,P,R,U],[D,F,G,H,J,M,P,S,U],[D,F,G,H,J,M,P,U],[D,F,G,H,M,N,P,Q,R,S,U],[D,F,G,H,M,N,P,S,U],[D,F,G,H,M,N,P,U],[D,F,G,H,M,P,Q,R,S],[D,F,G,H,M,P,S,U],[D,F,G,H,M,P,U],[D,F,G,J],[D,F,G,J,M],[D,F,G,J,M,N,P,Q,R,S,U],[D,F,G,J,M,N,P,Q,R,U],[D,F,G,J,M,N,P,Q,S,U],[D,F,G,J,M,N,P,Q,U],[D,F,G,J,M,N,P,R,S,U],[D,F,G,J,M,N,P,R,U],[D,F,G,J,M,N,P,S,U],[D,F,G,J,M,N,P,U],[D,F,G,J,M,P],[D,F,G,J,M,P,Q],[D,F,G,J,M,P,Q,R],[D,F,G,J,M,P,Q,R,S],[D,F,G,J,M,P,Q,R,S,U],[D,F,G,J,M,P,Q,R,U],[D,F,G,J,M,P,Q,S],[D,F,G,J,M,P,Q,S,U],[D,F,G,J,M,P,Q,U],[D,F,G,J,M,P,R],[D,F,G,J,M,P,R,S],[D,F,G,J,M,P,R,S,U],[D,F,G,J,M,P,R,U],[D,F,G,J,M,P,S],[D,F,G,J,M,P,S,U],[D,F,G,J,M,P,U],[D,F,G,J,M,Q],[D,F,G,J,M,Q,R],[D,F,G,J,M,R],[D,F,G,J,Q],[D,F,G,J,Q,R],[D,F,G,J,R],[D,F,G,M],[D,F,G,M,N,P,Q,R,U],[D,F,G,M,N,P,S,U],[D,F,G,M,N,P,U],[D,F,G,M,P],[D,F,G,M,P,Q,R],[D,F,G,M,P,S],[D,F,G,M,P,S,U],[D,F,G,M,P,U],[D,F,G,M,Q,R],[D,F,G,Q,R],[D,F,H,J,M,N,P,Q,R,S,U],[D,F,H,J,M,N,P,Q,R,U],[D,F,H,J,M,N,P,Q,S,U],[D,F,H,J,M,N,P,Q,U],[D,F,H,J,M,N,P,R,S,U],[D,F,H,J,M,N,P,R,U],[D,F,H,J,M,N,P,S,U],[D,F,H,J,M,N,P,U],[D,F,H,J,M,P,Q,R,S,U],[D,F,H,J,M,P,Q,R,U],[D,F,H,J,M,P,Q,S,U],[D,F,H,J,M,P,Q,U],[D,F,H,J,M,P,R,S,U],[D,F,H,J,M,P,R,U],[D,F,H,J,M,P,S,U],[D,F,H,J,M,P,U],[D,F,H,M,N,P,Q,S,U],[D,F,H,M,N,P,S,U],[D,F,H,M,N,P,U],[D,F,H,M,P,Q,S],[D,F,H,M,P,S,U],[D,F,H,M,P,U],[D,F,J,M,N,P,Q,R,S,U],[D,F,J,M,N,P,Q,R,U],[D,F,J,M,N,P,Q,S,U],[D,F,J,M,N,P,Q,U],[D,F,J,M,N,P,R,S,U],[D,F,J,M,N,P,R,U],[D,F,J,M,N,P,S,U],[D,F,J,M,N,P,U],[D,F,J,M,P,Q],[D,F,J,M,P,Q,R],[D,F,J,M,P,Q,R,S],[D,F,J,M,P,Q,R,S,U],[D,F,J,M,P,Q,R,U],[D,F,J,M,P,Q,S],[D,F,J,M,P,Q,S,U],[D,F,J,M,P,Q,U],[D,F,J,M,P,R],[D,F,J,M,P,R,S],[D,F,J,M,P,R,S,U],[D,F,J,M,P,R,U],[D,F,J,M,P,S,U],[D,F,J,M,P,U],[D,F,M,N,P,Q,U],[D,F,M,N,P,S,U],[D,F,M,N,P,U],[D,F,M,P,Q],[D,F,M,P,S,U],[D,F,M,P,U],[D,G],[D,G,H,J,M,N,P,Q,R,S,U],[D,G,H,J,M,N,P,Q,R,U],[D,G,H,J,M,N,P,Q,S,U],[D,G,H,J,M,N,P,Q,U],[D,G,H,J,M,N,P,R,S,U],[D,G,H,J,M,N,P,R,U],[D,G,H,J,M,N,P,S,U],[D,G,H,J,M,N,P,U],[D,G,H,J,M,P,Q,R,S,U],[D,G,H,J,M,P,Q,R,U],[D,G,H,J,M,P,Q,S,U],[D,G,H,J,M,P,Q,U],[D,G,H,J,M,P,R,S,U],[D,G,H,J,M,P,R,U],[D,G,H,J,M,P,S,U],[D,G,H,J,M,P,U],[D,G,H,M,N,P,R,S,U],[D,G,H,M,N,P,S,U],[D,G,H,M,N,P,U],[D,G,H,M,P,R,S],[D,G,H,M,P,S,U],[D,G,H,M,P,U],[D,G,J],[D,G,J,M],[D,G,J,M,N,P,Q,R,S,U],[D,G,J,M,N,P,Q,R,U],[D,G,J,M,N,P,Q,S,U],[D,G,J,M,N,P,Q,U],[D,G,J,M,N,P,R,S,U],[D,G,J,M,N,P,R,U],[D,G,J,M,N,P,S,U],[D,G,J,M,N,P,U],[D,G,J,M,P],[D,G,J,M,P,Q],[D,G,J,M,P,Q,R],[D,G,J,M,P,Q,R,S],[D,G,J,M,P,Q,R,S,U],[D,G,J,M,P,Q,R,U],[D,G,J,M,P,Q,S],[D,G,J,M,P,Q,S,U],[D,G,J,M,P,Q,U],[D,G,J,M,P,R],[D,G,J,M,P,R,S],[D,G,J,M,P,R,S,U],[D,G,J,M,P,R,U],[D,G,J,M,P,S],[D,G,J,M,P,S,U],[D,G,J,M,P,U],[D,G,J,M,Q],[D,G,J,M,Q,R],[D,G,J,M,R],[D,G,J,Q],[D,G,J,Q,R],[D,G,J,R],[D,G,M],[D,G,M,N,P,R,U],[D,G,M,N,P,S,U],[D,G,M,N,P,U],[D,G,M,P],[D,G,M,P,R],[D,G,M,P,S],[D,G,M,P,S,U],[D,G,M,P,U],[D,G,M,R],[D,G,R],[D,H,J,M,N,P,Q,R,S,U],[D,H,J,M,N,P,Q,R,U],[D,H,J,M,N,P,Q,S,U],[D,H,J,M,N,P,Q,U],[D,H,J,M,N,P,R,S,U],[D,H,J,M,N,P,R,U],[D,H,J,M,N,P,S,U],[D,H,J,M,N,P,U],[D,H,J,M,P,Q,R,S,U],[D,H,J,M,P,Q,R,U],[D,H,J,M,P,Q,S,U],[D,H,J,M,P,Q,U],[D,H,J,M,P,R,S,U],[D,H,J,M,P,R,U],[D,H,J,M,P,S,U],[D,H,J,M,P,U],[D,H,M,N,P,S,U],[D,H,M,N,P,U],[D,H,M,P,S],[D,H,M,P,S,U],[D,H,M,P,U],[D,J,M,N,P,Q,R,S,U],[D,J,M,N,P,Q,R,U],[D,J,M,N,P,Q,S,U],[D,J,M,N,P,Q,U],[D,J,M,N,P,R,S,U],[D,J,M,N,P,R,U],[D,J,M,N,P,S,U],[D,J,M,N,P,U],[D,J,M,P,Q],[D,J,M,P,Q,R],[D,J,M,P,Q,R,S],[D,J,M,P,Q,R,S,U],[D,J,M,P,Q,R,U],[D,J,M,P,Q,S],[D,J,M,P,Q,S,U],[D,J,M,P,Q,U],[D,J,M,P,R],[D,J,M,P,R,S],[D,J,M,P,R,S,U],[D,J,M,P,R,U],[D,J,M,P,S,U],[D,J,M,P,U],[D,M],[D,M,N,P,S,U],[D,M,N,P,U],[D,M,P],[D,M,P,S],[D,M,P,S,U],[D,M,P,U],[E,F,G,H,J,M,N,P,Q,R,S,U],[E,F,G,H,J,M,N,P,Q,R,U],[E,F,G,H,J,M,N,P,Q,S,U],[E,F,G,H,J,M,N,P,Q,U],[E,F,G,H,J,M,N,P,R,S,U],[E,F,G,H,J,M,N,P,R,U],[E,F,G,H,J,M,N,P,S,U],[E,F,G,H,J,M,N,P,U],[E,F,G,H,J,M,P,Q,R,S],[E,F,G,H,J,M,P,Q,R,S,U],[E,F,G,H,J,M,P,Q,R,U],[E,F,G,H,J,M,P,Q,S,U],[E,F,G,H,J,M,P,Q,U],[E,F,G,H,J,M,P,R,S,U],[E,F,G,H,J,M,P,R,U],[E,F,G,H,J,M,P,S,U],[E,F,G,H,J,M,P,U],[E,F,G,J],[E,F,G,J,M],[E,F,G,J,M,N,P,Q,R,S,U],[E,F,G,J,M,N,P,Q,R,U],[E,F,G,J,M,N,P,Q,S,U],[E,F,G,J,M,N,P,Q,U],[E,F,G,J,M,N,P,R,S,U],[E,F,G,J,M,N,P,R,U],[E,F,G,J,M,N,P,S,U],[E,F,G,J,M,N,P,U],[E,F,G,J,M,P],[E,F,G,J,M,P,Q],[E,F,G,J,M,P,Q,R],[E,F,G,J,M,P,Q,R,S],[E,F,G,J,M,P,Q,R,S,U],[E,F,G,J,M,P,Q,R,U],[E,F,G,J,M,P,Q,S],[E,F,G,J,M,P,Q,S,U],[E,F,G,J,M,P,Q,U],[E,F,G,J,M,P,R],[E,F,G,J,M,P,R,S],[E,F,G,J,M,P,R,S,U],[E,F,G,J,M,P,R,U],[E,F,G,J,M,P,S],[E,F,G,J,M,P,S,U],[E,F,G,J,M,P,U],[E,F,G,J,M,Q],[E,F,G,J,M,Q,R],[E,F,G,J,M,R],[E,F,G,J,Q],[E,F,G,J,Q,R],[E,F,G,J,R],[E,F,H,J,M,N,P,Q,R,S,U],[E,F,H,J,M,N,P,Q,R,U],[E,F,H,J,M,N,P,Q,S,U],[E,F,H,J,M,N,P,Q,U],[E,F,H,J,M,N,P,R,S,U],[E,F,H,J,M,N,P,R,U],[E,F,H,J,M,N,P,S,U],[E,F,H,J,M,N,P,U],[E,F,H,J,M,P,Q,R,S,U],[E,F,H,J,M,P,Q,R,U],[E,F,H,J,M,P,Q,S],[E,F,H,J,M,P,Q,S,U],[E,F,H,J,M,P,Q,U],[E,F,H,J,M,P,R,S,U],[E,F,H,J,M,P,R,U],[E,F,H,J,M,P,S,U],[E,F,H,J,M,P,U],[E,F,J],[E,F,J,M],[E,F,J,M,N,P,Q,R,S,U],[E,F,J,M,N,P,Q,R,U],[E,F,J,M,N,P,Q,S,U],[E,F,J,M,N,P,Q,U],[E,F,J,M,N,P,R,S,U],[E,F,J,M,N,P,R,U],[E,F,J,M,N,P,S,U],[E,F,J,M,N,P,U],[E,F,J,M,P],[E,F,J,M,P,Q],[E,F,J,M,P,Q,R],[E,F,J,M,P,Q,R,S],[E,F,J,M,P,Q,R,S,U],[E,F,J,M,P,Q,R,U],[E,F,J,M,P,Q,S],[E,F,J,M,P,Q,S,U],[E,F,J,M,P,Q,U],[E,F,J,M,P,R],[E,F,J,M,P,R,S],[E,F,J,M,P,R,S,U],[E,F,J,M,P,R,U],[E,F,J,M,P,S],[E,F,J,M,P,S,U],[E,F,J,M,P,U],[E,F,J,M,Q],[E,F,J,M,Q,R],[E,F,J,M,R],[E,F,J,Q],[E,F,J,Q,R],[E,F,J,R],[E,G,H,J,M,N,P,Q,R,S,U],[E,G,H,J,M,N,P,Q,R,U],[E,G,H,J,M,N,P,Q,S,U],[E,G,H,J,M,N,P,Q,U],[E,G,H,J,M,N,P,R,S,U],[E,G,H,J,M,N,P,R,U],[E,G,H,J,M,N,P,S,U],[E,G,H,J,M,N,P,U],[E,G,H,J,M,P,Q,R,S,U],[E,G,H,J,M,P,Q,R,U],[E,G,H,J,M,P,Q,S,U],[E,G,H,J,M,P,Q,U],[E,G,H,J,M,P,R,S],[E,G,H,J,M,P,R,S,U],[E,G,H,J,M,P,R,U],[E,G,H,J,M,P,S,U],[E,G,H,J,M,P,U],[E,G,J],[E,G,J,M],[E,G,J,M,N,P,Q,R,S,U],[E,G,J,M,N,P,Q,R,U],[E,G,J,M,N,P,Q,S,U],[E,G,J,M,N,P,Q,U],[E,G,J,M,N,P,R,S,U],[E,G,J,M,N,P,R,U],[E,G,J,M,N,P,S,U],[E,G,J,M,N,P,U],[E,G,J,M,P],[E,G,J,M,P,Q],[E,G,J,M,P,Q,R],[E,G,J,M,P,Q,R,S],[E,G,J,M,P,Q,R,S,U],[E,G,J,M,P,Q,R,U],[E,G,J,M,P,Q,S],[E,G,J,M,P,Q,S,U],[E,G,J,M,P,Q,U],[E,G,J,M,P,R],[E,G,J,M,P,R,S],[E,G,J,M,P,R,S,U],[E,G,J,M,P,R,U],[E,G,J,M,P,S],[E,G,J,M,P,S,U],[E,G,J,M,P,U],[E,G,J,M,Q],[E,G,J,M,Q,R],[E,G,J,M,R],[E,G,J,Q],[E,G,J,Q,R],[E,G,J,R],[E,H,J,M,N,P,Q,R,S,U],[E,H,J,M,N,P,Q,R,U],[E,H,J,M,N,P,Q,S,U],[E,H,J,M,N,P,Q,U],[E,H,J,M,N,P,R,S,U],[E,H,J,M,N,P,R,U],[E,H,J,M,N,P,S,U],[E,H,J,M,N,P,U],[E,H,J,M,P,Q,R,S,U],[E,H,J,M,P,Q,R,U],[E,H,J,M,P,Q,S,U],[E,H,J,M,P,Q,U],[E,H,J,M,P,R,S,U],[E,H,J,M,P,R,U],[E,H,J,M,P,S],[E,H,J,M,P,S,U],[E,H,J,M,P,U],[E,J],[E,J,M],[E,J,M,N,P,Q,R,S,U],[E,J,M,N,P,Q,R,U],[E,J,M,N,P,Q,S,U],[E,J,M,N,P,Q,U],[E,J,M,N,P,R,S,U],[E,J,M,N,P,R,U],[E,J,M,N,P,S,U],[E,J,M,N,P,U],[E,J,M,P],[E,J,M,P,Q],[E,J,M,P,Q,R],[E,J,M,P,Q,R,S],[E,J,M,P,Q,R,S,U],[E,J,M,P,Q,R,U],[E,J,M,P,Q,S],[E,J,M,P,Q,S,U],[E,J,M,P,Q,U],[E,J,M,P,R],[E,J,M,P,R,S],[E,J,M,P,R,S,U],[E,J,M,P,R,U],[E,J,M,P,S],[E,J,M,P,S,U],[E,J,M,P,U],[E,J,M,Q],[E,J,M,Q,R],[E,J,M,R],[E,J,Q],[E,J,Q,R],[E,J,R],[F],[F,G],[F,G,H,J,M,N,P,Q,R,S,U],[F,G,H,J,M,N,P,Q,R,U],[F,G,H,J,M,N,P,Q,S,U],[F,G,H,J,M,N,P,Q,U],[F,G,H,J,M,N,P,R,S,U],[F,G,H,J,M,N,P,R,U],[F,G,H,J,M,N,P,S,U],[F,G,H,J,M,N,P,U],[F,G,H,J,M,P,Q,R,S,U],[F,G,H,J,M,P,Q,R,U],[F,G,H,J,M,P,Q,S,U],[F,G,H,J,M,P,Q,U],[F,G,H,J,M,P,R,S,U],[F,G,H,J,M,P,R,U],[F,G,H,J,M,P,S,U],[F,G,H,J,M,P,U],[F,G,H,M,N,P,Q,R,S,U],[F,G,H,M,N,P,S,U],[F,G,H,M,N,P,U],[F,G,H,M,P,Q,R,S],[F,G,H,M,P,S,U],[F,G,H,M,P,U],[F,G,J],[F,G,J,M],[F,G,J,M,N,P,Q,R,S,U],[F,G,J,M,N,P,Q,R,U],[F,G,J,M,N,P,Q,S,U],[F,G,J,M,N,P,Q,U],[F,G,J,M,N,P,R,S,U],[F,G,J,M,N,P,R,U],[F,G,J,M,N,P,S,U],[F,G,J,M,N,P,U],[F,G,J,M,P],[F,G,J,M,P,Q],[F,G,J,M,P,Q,R],[F,G,J,M,P,Q,R,S],[F,G,J,M,P,Q,R,S,U],[F,G,J,M,P,Q,R,U],[F,G,J,M,P,Q,S],[F,G,J,M,P,Q,S,U],[F,G,J,M,P,Q,U],[F,G,J,M,P,R],[F,G,J,M,P,R,S],[F,G,J,M,P,R,S,U],[F,G,J,M,P,R,U],[F,G,J,M,P,S],[F,G,J,M,P,S,U],[F,G,J,M,P,U],[F,G,J,M,Q],[F,G,J,M,Q,R],[F,G,J,M,R],[F,G,J,Q],[F,G,J,Q,R],[F,G,J,R],[F,G,M],[F,G,M,N,P,Q,R,U],[F,G,M,N,P,S,U],[F,G,M,N,P,U],[F,G,M,P],[F,G,M,P,Q,R],[F,G,M,P,S],[F,G,M,P,S,U],[F,G,M,P,U],[F,G,M,Q,R],[F,G,Q,R],[F,H,J,M,N,P,Q,R,S,U],[F,H,J,M,N,P,Q,R,U],[F,H,J,M,N,P,Q,S,U],[F,H,J,M,N,P,Q,U],[F,H,J,M,N,P,R,S,U],[F,H,J,M,N,P,R,U],[F,H,J,M,N,P,S,U],[F,H,J,M,N,P,U],[F,H,J,M,P,Q,R,S,U],[F,H,J,M,P,Q,R,U],[F,H,J,M,P,Q,S,U],[F,H,J,M,P,Q,U],[F,H,J,M,P,R,S,U],[F,H,J,M,P,R,U],[F,H,J,M,P,S,U],[F,H,J,M,P,U],[F,H,M,N,P,Q,S,U],[F,H,M,N,P,S,U],[F,H,M,N,P,U],[F,H,M,P,Q,S],[F,H,M,P,S,U],[F,H,M,P,U],[F,J],[F,J,M,N,P,Q,R,S,U],[F,J,M,N,P,Q,R,U],[F,J,M,N,P,Q,S,U],[F,J,M,N,P,Q,U],[F,J,M,N,P,R,S,U],[F,J,M,N,P,R,U],[F,J,M,N,P,S,U],[F,J,M,N,P,U],[F,J,M,P,Q],[F,J,M,P,Q,R],[F,J,M,P,Q,R,S],[F,J,M,P,Q,R,S,U],[F,J,M,P,Q,R,U],[F,J,M,P,Q,S],[F,J,M,P,Q,S,U],[F,J,M,P,Q,U],[F,J,M,P,R],[F,J,M,P,R,S],[F,J,M,P,R,S,U],[F,J,M,P,R,U],[F,J,M,P,S,U],[F,J,M,P,U],[F,J,Q],[F,J,Q,R],[F,J,R],[F,M,N,P,Q,U],[F,M,N,P,S,U],[F,M,N,P,U],[F,M,P,Q],[F,M,P,S,U],[F,M,P,U],[F,Q],[G],[G,H,J,M,N,P,Q,R,S,U],[G,H,J,M,N,P,Q,R,U],[G,H,J,M,N,P,Q,S,U],[G,H,J,M,N,P,Q,U],[G,H,J,M,N,P,R,S,U],[G,H,J,M,N,P,R,U],[G,H,J,M,N,P,S,U],[G,H,J,M,N,P,U],[G,H,J,M,P,Q,R,S,U],[G,H,J,M,P,Q,R,U],[G,H,J,M,P,Q,S,U],[G,H,J,M,P,Q,U],[G,H,J,M,P,R,S,U],[G,H,J,M,P,R,U],[G,H,J,M,P,S,U],[G,H,J,M,P,U],[G,H,M,N,P,R,S,U],[G,H,M,N,P,S,U],[G,H,M,N,P,U],[G,H,M,P,R,S],[G,H,M,P,S,U],[G,H,M,P,U],[G,J],[G,J,M],[G,J,M,N,P,Q,R,S,U],[G,J,M,N,P,Q,R,U],[G,J,M,N,P,Q,S,U],[G,J,M,N,P,Q,U],[G,J,M,N,P,R,S,U],[G,J,M,N,P,R,U],[G,J,M,N,P,S,U],[G,J,M,N,P,U],[G,J,M,P],[G,J,M,P,Q],[G,J,M,P,Q,R],[G,J,M,P,Q,R,S],[G,J,M,P,Q,R,S,U],[G,J,M,P,Q,R,U],[G,J,M,P,Q,S],[G,J,M,P,Q,S,U],[G,J,M,P,Q,U],[G,J,M,P,R],[G,J,M,P,R,S],[G,J,M,P,R,S,U],[G,J,M,P,R,U],[G,J,M,P,S],[G,J,M,P,S,U],[G,J,M,P,U],[G,J,M,Q],[G,J,M,Q,R],[G,J,M,R],[G,J,Q],[G,J,Q,R],[G,J,R],[G,M],[G,M,N,P,R,U],[G,M,N,P,S,U],[G,M,N,P,U],[G,M,P],[G,M,P,R],[G,M,P,S],[G,M,P,S,U],[G,M,P,U],[G,M,R],[G,R],[H,J,M,N,P,Q,R,S,U],[H,J,M,N,P,Q,R,U],[H,J,M,N,P,Q,S,U],[H,J,M,N,P,Q,U],[H,J,M,N,P,R,S,U],[H,J,M,N,P,R,U],[H,J,M,N,P,S,U],[H,J,M,N,P,U],[H,J,M,P,Q,R,S,U],[H,J,M,P,Q,R,U],[H,J,M,P,Q,S,U],[H,J,M,P,Q,U],[H,J,M,P,R,S,U],[H,J,M,P,R,U],[H,J,M,P,S,U],[H,J,M,P,U],[H,M,N,P,S,U],[H,M,N,P,U],[H,M,P,S],[H,M,P,S,U],[H,M,P,U],[I,J],[I,J,V],[J],[J,M,N,P,Q,R,S,U],[J,M,N,P,Q,R,U],[J,M,N,P,Q,S,U],[J,M,N,P,Q,U],[J,M,N,P,R,S,U],[J,M,N,P,R,U],[J,M,N,P,S,U],[J,M,N,P,U],[J,M,P,Q],[J,M,P,Q,R],[J,M,P,Q,R,S],[J,M,P,Q,R,S,U],[J,M,P,Q,R,U],[J,M,P,Q,S],[J,M,P,Q,S,U],[J,M,P,Q,U],[J,M,P,R],[J,M,P,R,S],[J,M,P,R,S,U],[J,M,P,R,U],[J,M,P,S,U],[J,M,P,U],[J,Q],[J,Q,R],[J,R],[M],[M,N,P,S,U],[M,N,P,U],[M,P],[M,P,S],[M,P,S,U],[M,P,U]]),ground([K,L,O,T]),linear(I);mshare([[B,C,D,E,F,G,H,J,M,N,P,Q,R,S,U],[B,C,D,E,F,G,H,J,M,N,P,Q,R,U],[B,C,D,E,F,G,H,J,M,N,P,Q,S,U],[B,C,D,E,F,G,H,J,M,N,P,Q,U],[B,C,D,E,F,G,H,J,M,N,P,R,S,U],[B,C,D,E,F,G,H,J,M,N,P,R,U],[B,C,D,E,F,G,H,J,M,N,P,S,U],[B,C,D,E,F,G,H,J,M,N,P,U],[B,C,D,E,F,G,H,J,M,P,Q,R,S],[B,C,D,E,F,G,H,J,M,P,Q,R,S,U],[B,C,D,E,F,G,H,J,M,P,Q,R,U],[B,C,D,E,F,G,H,J,M,P,Q,S,U],[B,C,D,E,F,G,H,J,M,P,Q,U],[B,C,D,E,F,G,H,J,M,P,R,S,U],[B,C,D,E,F,G,H,J,M,P,R,U],[B,C,D,E,F,G,H,J,M,P,S,U],[B,C,D,E,F,G,H,J,M,P,U],[B,C,D,E,F,G,J],[B,C,D,E,F,G,J,M],[B,C,D,E,F,G,J,M,N,P,Q,R,S,U],[B,C,D,E,F,G,J,M,N,P,Q,R,U],[B,C,D,E,F,G,J,M,N,P,Q,S,U],[B,C,D,E,F,G,J,M,N,P,Q,U],[B,C,D,E,F,G,J,M,N,P,R,S,U],[B,C,D,E,F,G,J,M,N,P,R,U],[B,C,D,E,F,G,J,M,N,P,S,U],[B,C,D,E,F,G,J,M,N,P,U],[B,C,D,E,F,G,J,M,P],[B,C,D,E,F,G,J,M,P,Q],[B,C,D,E,F,G,J,M,P,Q,R],[B,C,D,E,F,G,J,M,P,Q,R,S],[B,C,D,E,F,G,J,M,P,Q,R,S,U],[B,C,D,E,F,G,J,M,P,Q,R,U],[B,C,D,E,F,G,J,M,P,Q,S],[B,C,D,E,F,G,J,M,P,Q,S,U],[B,C,D,E,F,G,J,M,P,Q,U],[B,C,D,E,F,G,J,M,P,R],[B,C,D,E,F,G,J,M,P,R,S],[B,C,D,E,F,G,J,M,P,R,S,U],[B,C,D,E,F,G,J,M,P,R,U],[B,C,D,E,F,G,J,M,P,S],[B,C,D,E,F,G,J,M,P,S,U],[B,C,D,E,F,G,J,M,P,U],[B,C,D,E,F,G,J,M,Q],[B,C,D,E,F,G,J,M,Q,R],[B,C,D,E,F,G,J,M,R],[B,C,D,E,F,G,J,Q],[B,C,D,E,F,G,J,Q,R],[B,C,D,E,F,G,J,R],[B,C,D,E,F,H,J,M,N,P,Q,R,S,U],[B,C,D,E,F,H,J,M,N,P,Q,R,U],[B,C,D,E,F,H,J,M,N,P,Q,S,U],[B,C,D,E,F,H,J,M,N,P,Q,U],[B,C,D,E,F,H,J,M,N,P,R,S,U],[B,C,D,E,F,H,J,M,N,P,R,U],[B,C,D,E,F,H,J,M,N,P,S,U],[B,C,D,E,F,H,J,M,N,P,U],[B,C,D,E,F,H,J,M,P,Q,R,S,U],[B,C,D,E,F,H,J,M,P,Q,R,U],[B,C,D,E,F,H,J,M,P,Q,S],[B,C,D,E,F,H,J,M,P,Q,S,U],[B,C,D,E,F,H,J,M,P,Q,U],[B,C,D,E,F,H,J,M,P,R,S,U],[B,C,D,E,F,H,J,M,P,R,U],[B,C,D,E,F,H,J,M,P,S,U],[B,C,D,E,F,H,J,M,P,U],[B,C,D,E,F,J],[B,C,D,E,F,J,M],[B,C,D,E,F,J,M,N,P,Q,R,S,U],[B,C,D,E,F,J,M,N,P,Q,R,U],[B,C,D,E,F,J,M,N,P,Q,S,U],[B,C,D,E,F,J,M,N,P,Q,U],[B,C,D,E,F,J,M,N,P,R,S,U],[B,C,D,E,F,J,M,N,P,R,U],[B,C,D,E,F,J,M,N,P,S,U],[B,C,D,E,F,J,M,N,P,U],[B,C,D,E,F,J,M,P],[B,C,D,E,F,J,M,P,Q],[B,C,D,E,F,J,M,P,Q,R],[B,C,D,E,F,J,M,P,Q,R,S],[B,C,D,E,F,J,M,P,Q,R,S,U],[B,C,D,E,F,J,M,P,Q,R,U],[B,C,D,E,F,J,M,P,Q,S],[B,C,D,E,F,J,M,P,Q,S,U],[B,C,D,E,F,J,M,P,Q,U],[B,C,D,E,F,J,M,P,R],[B,C,D,E,F,J,M,P,R,S],[B,C,D,E,F,J,M,P,R,S,U],[B,C,D,E,F,J,M,P,R,U],[B,C,D,E,F,J,M,P,S],[B,C,D,E,F,J,M,P,S,U],[B,C,D,E,F,J,M,P,U],[B,C,D,E,F,J,M,Q],[B,C,D,E,F,J,M,Q,R],[B,C,D,E,F,J,M,R],[B,C,D,E,F,J,Q],[B,C,D,E,F,J,Q,R],[B,C,D,E,F,J,R],[B,C,D,E,G,H,J,M,N,P,Q,R,S,U],[B,C,D,E,G,H,J,M,N,P,Q,R,U],[B,C,D,E,G,H,J,M,N,P,Q,S,U],[B,C,D,E,G,H,J,M,N,P,Q,U],[B,C,D,E,G,H,J,M,N,P,R,S,U],[B,C,D,E,G,H,J,M,N,P,R,U],[B,C,D,E,G,H,J,M,N,P,S,U],[B,C,D,E,G,H,J,M,N,P,U],[B,C,D,E,G,H,J,M,P,Q,R,S,U],[B,C,D,E,G,H,J,M,P,Q,R,U],[B,C,D,E,G,H,J,M,P,Q,S,U],[B,C,D,E,G,H,J,M,P,Q,U],[B,C,D,E,G,H,J,M,P,R,S],[B,C,D,E,G,H,J,M,P,R,S,U],[B,C,D,E,G,H,J,M,P,R,U],[B,C,D,E,G,H,J,M,P,S,U],[B,C,D,E,G,H,J,M,P,U],[B,C,D,E,G,J],[B,C,D,E,G,J,M],[B,C,D,E,G,J,M,N,P,Q,R,S,U],[B,C,D,E,G,J,M,N,P,Q,R,U],[B,C,D,E,G,J,M,N,P,Q,S,U],[B,C,D,E,G,J,M,N,P,Q,U],[B,C,D,E,G,J,M,N,P,R,S,U],[B,C,D,E,G,J,M,N,P,R,U],[B,C,D,E,G,J,M,N,P,S,U],[B,C,D,E,G,J,M,N,P,U],[B,C,D,E,G,J,M,P],[B,C,D,E,G,J,M,P,Q],[B,C,D,E,G,J,M,P,Q,R],[B,C,D,E,G,J,M,P,Q,R,S],[B,C,D,E,G,J,M,P,Q,R,S,U],[B,C,D,E,G,J,M,P,Q,R,U],[B,C,D,E,G,J,M,P,Q,S],[B,C,D,E,G,J,M,P,Q,S,U],[B,C,D,E,G,J,M,P,Q,U],[B,C,D,E,G,J,M,P,R],[B,C,D,E,G,J,M,P,R,S],[B,C,D,E,G,J,M,P,R,S,U],[B,C,D,E,G,J,M,P,R,U],[B,C,D,E,G,J,M,P,S],[B,C,D,E,G,J,M,P,S,U],[B,C,D,E,G,J,M,P,U],[B,C,D,E,G,J,M,Q],[B,C,D,E,G,J,M,Q,R],[B,C,D,E,G,J,M,R],[B,C,D,E,G,J,Q],[B,C,D,E,G,J,Q,R],[B,C,D,E,G,J,R],[B,C,D,E,H,J,M,N,P,Q,R,S,U],[B,C,D,E,H,J,M,N,P,Q,R,U],[B,C,D,E,H,J,M,N,P,Q,S,U],[B,C,D,E,H,J,M,N,P,Q,U],[B,C,D,E,H,J,M,N,P,R,S,U],[B,C,D,E,H,J,M,N,P,R,U],[B,C,D,E,H,J,M,N,P,S,U],[B,C,D,E,H,J,M,N,P,U],[B,C,D,E,H,J,M,P,Q,R,S,U],[B,C,D,E,H,J,M,P,Q,R,U],[B,C,D,E,H,J,M,P,Q,S,U],[B,C,D,E,H,J,M,P,Q,U],[B,C,D,E,H,J,M,P,R,S,U],[B,C,D,E,H,J,M,P,R,U],[B,C,D,E,H,J,M,P,S],[B,C,D,E,H,J,M,P,S,U],[B,C,D,E,H,J,M,P,U],[B,C,D,E,J],[B,C,D,E,J,M],[B,C,D,E,J,M,N,P,Q,R,S,U],[B,C,D,E,J,M,N,P,Q,R,U],[B,C,D,E,J,M,N,P,Q,S,U],[B,C,D,E,J,M,N,P,Q,U],[B,C,D,E,J,M,N,P,R,S,U],[B,C,D,E,J,M,N,P,R,U],[B,C,D,E,J,M,N,P,S,U],[B,C,D,E,J,M,N,P,U],[B,C,D,E,J,M,P],[B,C,D,E,J,M,P,Q],[B,C,D,E,J,M,P,Q,R],[B,C,D,E,J,M,P,Q,R,S],[B,C,D,E,J,M,P,Q,R,S,U],[B,C,D,E,J,M,P,Q,R,U],[B,C,D,E,J,M,P,Q,S],[B,C,D,E,J,M,P,Q,S,U],[B,C,D,E,J,M,P,Q,U],[B,C,D,E,J,M,P,R],[B,C,D,E,J,M,P,R,S],[B,C,D,E,J,M,P,R,S,U],[B,C,D,E,J,M,P,R,U],[B,C,D,E,J,M,P,S],[B,C,D,E,J,M,P,S,U],[B,C,D,E,J,M,P,U],[B,C,D,E,J,M,Q],[B,C,D,E,J,M,Q,R],[B,C,D,E,J,M,R],[B,C,D,E,J,Q],[B,C,D,E,J,Q,R],[B,C,D,E,J,R],[B,C,D,F,G,H,J,M,N,P,Q,R,S,U],[B,C,D,F,G,H,J,M,N,P,Q,R,U],[B,C,D,F,G,H,J,M,N,P,Q,S,U],[B,C,D,F,G,H,J,M,N,P,Q,U],[B,C,D,F,G,H,J,M,N,P,R,S,U],[B,C,D,F,G,H,J,M,N,P,R,U],[B,C,D,F,G,H,J,M,N,P,S,U],[B,C,D,F,G,H,J,M,N,P,U],[B,C,D,F,G,H,J,M,P,Q,R,S],[B,C,D,F,G,H,J,M,P,Q,R,S,U],[B,C,D,F,G,H,J,M,P,Q,R,U],[B,C,D,F,G,H,J,M,P,Q,S,U],[B,C,D,F,G,H,J,M,P,Q,U],[B,C,D,F,G,H,J,M,P,R,S,U],[B,C,D,F,G,H,J,M,P,R,U],[B,C,D,F,G,H,J,M,P,S,U],[B,C,D,F,G,H,J,M,P,U],[B,C,D,F,G,J],[B,C,D,F,G,J,M],[B,C,D,F,G,J,M,N,P,Q,R,S,U],[B,C,D,F,G,J,M,N,P,Q,R,U],[B,C,D,F,G,J,M,N,P,Q,S,U],[B,C,D,F,G,J,M,N,P,Q,U],[B,C,D,F,G,J,M,N,P,R,S,U],[B,C,D,F,G,J,M,N,P,R,U],[B,C,D,F,G,J,M,N,P,S,U],[B,C,D,F,G,J,M,N,P,U],[B,C,D,F,G,J,M,P],[B,C,D,F,G,J,M,P,Q],[B,C,D,F,G,J,M,P,Q,R],[B,C,D,F,G,J,M,P,Q,R,S],[B,C,D,F,G,J,M,P,Q,R,S,U],[B,C,D,F,G,J,M,P,Q,R,U],[B,C,D,F,G,J,M,P,Q,S],[B,C,D,F,G,J,M,P,Q,S,U],[B,C,D,F,G,J,M,P,Q,U],[B,C,D,F,G,J,M,P,R],[B,C,D,F,G,J,M,P,R,S],[B,C,D,F,G,J,M,P,R,S,U],[B,C,D,F,G,J,M,P,R,U],[B,C,D,F,G,J,M,P,S],[B,C,D,F,G,J,M,P,S,U],[B,C,D,F,G,J,M,P,U],[B,C,D,F,G,J,M,Q],[B,C,D,F,G,J,M,Q,R],[B,C,D,F,G,J,M,R],[B,C,D,F,G,J,Q],[B,C,D,F,G,J,Q,R],[B,C,D,F,G,J,R],[B,C,D,F,H,J,M,N,P,Q,R,S,U],[B,C,D,F,H,J,M,N,P,Q,R,U],[B,C,D,F,H,J,M,N,P,Q,S,U],[B,C,D,F,H,J,M,N,P,Q,U],[B,C,D,F,H,J,M,N,P,R,S,U],[B,C,D,F,H,J,M,N,P,R,U],[B,C,D,F,H,J,M,N,P,S,U],[B,C,D,F,H,J,M,N,P,U],[B,C,D,F,H,J,M,P,Q,R,S,U],[B,C,D,F,H,J,M,P,Q,R,U],[B,C,D,F,H,J,M,P,Q,S],[B,C,D,F,H,J,M,P,Q,S,U],[B,C,D,F,H,J,M,P,Q,U],[B,C,D,F,H,J,M,P,R,S,U],[B,C,D,F,H,J,M,P,R,U],[B,C,D,F,H,J,M,P,S,U],[B,C,D,F,H,J,M,P,U],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N,P,Q,R,S,U],[B,C,D,F,J,M,N,P,Q,R,U],[B,C,D,F,J,M,N,P,Q,S,U],[B,C,D,F,J,M,N,P,Q,U],[B,C,D,F,J,M,N,P,R,S,U],[B,C,D,F,J,M,N,P,R,U],[B,C,D,F,J,M,N,P,S,U],[B,C,D,F,J,M,N,P,U],[B,C,D,F,J,M,P],[B,C,D,F,J,M,P,Q],[B,C,D,F,J,M,P,Q,R],[B,C,D,F,J,M,P,Q,R,S],[B,C,D,F,J,M,P,Q,R,S,U],[B,C,D,F,J,M,P,Q,R,U],[B,C,D,F,J,M,P,Q,S],[B,C,D,F,J,M,P,Q,S,U],[B,C,D,F,J,M,P,Q,U],[B,C,D,F,J,M,P,R],[B,C,D,F,J,M,P,R,S],[B,C,D,F,J,M,P,R,S,U],[B,C,D,F,J,M,P,R,U],[B,C,D,F,J,M,P,S],[B,C,D,F,J,M,P,S,U],[B,C,D,F,J,M,P,U],[B,C,D,F,J,M,Q],[B,C,D,F,J,M,Q,R],[B,C,D,F,J,M,R],[B,C,D,F,J,Q],[B,C,D,F,J,Q,R],[B,C,D,F,J,R],[B,C,D,G,H,J,M,N,P,Q,R,S,U],[B,C,D,G,H,J,M,N,P,Q,R,U],[B,C,D,G,H,J,M,N,P,Q,S,U],[B,C,D,G,H,J,M,N,P,Q,U],[B,C,D,G,H,J,M,N,P,R,S,U],[B,C,D,G,H,J,M,N,P,R,U],[B,C,D,G,H,J,M,N,P,S,U],[B,C,D,G,H,J,M,N,P,U],[B,C,D,G,H,J,M,P,Q,R,S,U],[B,C,D,G,H,J,M,P,Q,R,U],[B,C,D,G,H,J,M,P,Q,S,U],[B,C,D,G,H,J,M,P,Q,U],[B,C,D,G,H,J,M,P,R,S],[B,C,D,G,H,J,M,P,R,S,U],[B,C,D,G,H,J,M,P,R,U],[B,C,D,G,H,J,M,P,S,U],[B,C,D,G,H,J,M,P,U],[B,C,D,G,J],[B,C,D,G,J,M],[B,C,D,G,J,M,N,P,Q,R,S,U],[B,C,D,G,J,M,N,P,Q,R,U],[B,C,D,G,J,M,N,P,Q,S,U],[B,C,D,G,J,M,N,P,Q,U],[B,C,D,G,J,M,N,P,R,S,U],[B,C,D,G,J,M,N,P,R,U],[B,C,D,G,J,M,N,P,S,U],[B,C,D,G,J,M,N,P,U],[B,C,D,G,J,M,P],[B,C,D,G,J,M,P,Q],[B,C,D,G,J,M,P,Q,R],[B,C,D,G,J,M,P,Q,R,S],[B,C,D,G,J,M,P,Q,R,S,U],[B,C,D,G,J,M,P,Q,R,U],[B,C,D,G,J,M,P,Q,S],[B,C,D,G,J,M,P,Q,S,U],[B,C,D,G,J,M,P,Q,U],[B,C,D,G,J,M,P,R],[B,C,D,G,J,M,P,R,S],[B,C,D,G,J,M,P,R,S,U],[B,C,D,G,J,M,P,R,U],[B,C,D,G,J,M,P,S],[B,C,D,G,J,M,P,S,U],[B,C,D,G,J,M,P,U],[B,C,D,G,J,M,Q],[B,C,D,G,J,M,Q,R],[B,C,D,G,J,M,R],[B,C,D,G,J,Q],[B,C,D,G,J,Q,R],[B,C,D,G,J,R],[B,C,D,H,J,M,N,P,Q,R,S,U],[B,C,D,H,J,M,N,P,Q,R,U],[B,C,D,H,J,M,N,P,Q,S,U],[B,C,D,H,J,M,N,P,Q,U],[B,C,D,H,J,M,N,P,R,S,U],[B,C,D,H,J,M,N,P,R,U],[B,C,D,H,J,M,N,P,S,U],[B,C,D,H,J,M,N,P,U],[B,C,D,H,J,M,P,Q,R,S,U],[B,C,D,H,J,M,P,Q,R,U],[B,C,D,H,J,M,P,Q,S,U],[B,C,D,H,J,M,P,Q,U],[B,C,D,H,J,M,P,R,S,U],[B,C,D,H,J,M,P,R,U],[B,C,D,H,J,M,P,S],[B,C,D,H,J,M,P,S,U],[B,C,D,H,J,M,P,U],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N,P,Q,R,S,U],[B,C,D,J,M,N,P,Q,R,U],[B,C,D,J,M,N,P,Q,S,U],[B,C,D,J,M,N,P,Q,U],[B,C,D,J,M,N,P,R,S,U],[B,C,D,J,M,N,P,R,U],[B,C,D,J,M,N,P,S,U],[B,C,D,J,M,N,P,U],[B,C,D,J,M,P],[B,C,D,J,M,P,Q],[B,C,D,J,M,P,Q,R],[B,C,D,J,M,P,Q,R,S],[B,C,D,J,M,P,Q,R,S,U],[B,C,D,J,M,P,Q,R,U],[B,C,D,J,M,P,Q,S],[B,C,D,J,M,P,Q,S,U],[B,C,D,J,M,P,Q,U],[B,C,D,J,M,P,R],[B,C,D,J,M,P,R,S],[B,C,D,J,M,P,R,S,U],[B,C,D,J,M,P,R,U],[B,C,D,J,M,P,S],[B,C,D,J,M,P,S,U],[B,C,D,J,M,P,U],[B,C,D,J,M,Q],[B,C,D,J,M,Q,R],[B,C,D,J,M,R],[B,C,D,J,Q],[B,C,D,J,Q,R],[B,C,D,J,R],[B,C,E,F,G,H,J,M,N,P,Q,R,S,U],[B,C,E,F,G,H,J,M,N,P,Q,R,U],[B,C,E,F,G,H,J,M,N,P,Q,S,U],[B,C,E,F,G,H,J,M,N,P,Q,U],[B,C,E,F,G,H,J,M,N,P,R,S,U],[B,C,E,F,G,H,J,M,N,P,R,U],[B,C,E,F,G,H,J,M,N,P,S,U],[B,C,E,F,G,H,J,M,N,P,U],[B,C,E,F,G,H,J,M,P,Q,R,S],[B,C,E,F,G,H,J,M,P,Q,R,S,U],[B,C,E,F,G,H,J,M,P,Q,R,U],[B,C,E,F,G,H,J,M,P,Q,S,U],[B,C,E,F,G,H,J,M,P,Q,U],[B,C,E,F,G,H,J,M,P,R,S,U],[B,C,E,F,G,H,J,M,P,R,U],[B,C,E,F,G,H,J,M,P,S,U],[B,C,E,F,G,H,J,M,P,U],[B,C,E,F,G,J],[B,C,E,F,G,J,M],[B,C,E,F,G,J,M,N,P,Q,R,S,U],[B,C,E,F,G,J,M,N,P,Q,R,U],[B,C,E,F,G,J,M,N,P,Q,S,U],[B,C,E,F,G,J,M,N,P,Q,U],[B,C,E,F,G,J,M,N,P,R,S,U],[B,C,E,F,G,J,M,N,P,R,U],[B,C,E,F,G,J,M,N,P,S,U],[B,C,E,F,G,J,M,N,P,U],[B,C,E,F,G,J,M,P],[B,C,E,F,G,J,M,P,Q],[B,C,E,F,G,J,M,P,Q,R],[B,C,E,F,G,J,M,P,Q,R,S],[B,C,E,F,G,J,M,P,Q,R,S,U],[B,C,E,F,G,J,M,P,Q,R,U],[B,C,E,F,G,J,M,P,Q,S],[B,C,E,F,G,J,M,P,Q,S,U],[B,C,E,F,G,J,M,P,Q,U],[B,C,E,F,G,J,M,P,R],[B,C,E,F,G,J,M,P,R,S],[B,C,E,F,G,J,M,P,R,S,U],[B,C,E,F,G,J,M,P,R,U],[B,C,E,F,G,J,M,P,S],[B,C,E,F,G,J,M,P,S,U],[B,C,E,F,G,J,M,P,U],[B,C,E,F,G,J,M,Q],[B,C,E,F,G,J,M,Q,R],[B,C,E,F,G,J,M,R],[B,C,E,F,G,J,Q],[B,C,E,F,G,J,Q,R],[B,C,E,F,G,J,R],[B,C,E,F,H,J,M,N,P,Q,R,S,U],[B,C,E,F,H,J,M,N,P,Q,R,U],[B,C,E,F,H,J,M,N,P,Q,S,U],[B,C,E,F,H,J,M,N,P,Q,U],[B,C,E,F,H,J,M,N,P,R,S,U],[B,C,E,F,H,J,M,N,P,R,U],[B,C,E,F,H,J,M,N,P,S,U],[B,C,E,F,H,J,M,N,P,U],[B,C,E,F,H,J,M,P,Q,R,S,U],[B,C,E,F,H,J,M,P,Q,R,U],[B,C,E,F,H,J,M,P,Q,S],[B,C,E,F,H,J,M,P,Q,S,U],[B,C,E,F,H,J,M,P,Q,U],[B,C,E,F,H,J,M,P,R,S,U],[B,C,E,F,H,J,M,P,R,U],[B,C,E,F,H,J,M,P,S,U],[B,C,E,F,H,J,M,P,U],[B,C,E,F,J],[B,C,E,F,J,M],[B,C,E,F,J,M,N,P,Q,R,S,U],[B,C,E,F,J,M,N,P,Q,R,U],[B,C,E,F,J,M,N,P,Q,S,U],[B,C,E,F,J,M,N,P,Q,U],[B,C,E,F,J,M,N,P,R,S,U],[B,C,E,F,J,M,N,P,R,U],[B,C,E,F,J,M,N,P,S,U],[B,C,E,F,J,M,N,P,U],[B,C,E,F,J,M,P],[B,C,E,F,J,M,P,Q],[B,C,E,F,J,M,P,Q,R],[B,C,E,F,J,M,P,Q,R,S],[B,C,E,F,J,M,P,Q,R,S,U],[B,C,E,F,J,M,P,Q,R,U],[B,C,E,F,J,M,P,Q,S],[B,C,E,F,J,M,P,Q,S,U],[B,C,E,F,J,M,P,Q,U],[B,C,E,F,J,M,P,R],[B,C,E,F,J,M,P,R,S],[B,C,E,F,J,M,P,R,S,U],[B,C,E,F,J,M,P,R,U],[B,C,E,F,J,M,P,S],[B,C,E,F,J,M,P,S,U],[B,C,E,F,J,M,P,U],[B,C,E,F,J,M,Q],[B,C,E,F,J,M,Q,R],[B,C,E,F,J,M,R],[B,C,E,F,J,Q],[B,C,E,F,J,Q,R],[B,C,E,F,J,R],[B,C,E,G,H,J,M,N,P,Q,R,S,U],[B,C,E,G,H,J,M,N,P,Q,R,U],[B,C,E,G,H,J,M,N,P,Q,S,U],[B,C,E,G,H,J,M,N,P,Q,U],[B,C,E,G,H,J,M,N,P,R,S,U],[B,C,E,G,H,J,M,N,P,R,U],[B,C,E,G,H,J,M,N,P,S,U],[B,C,E,G,H,J,M,N,P,U],[B,C,E,G,H,J,M,P,Q,R,S,U],[B,C,E,G,H,J,M,P,Q,R,U],[B,C,E,G,H,J,M,P,Q,S,U],[B,C,E,G,H,J,M,P,Q,U],[B,C,E,G,H,J,M,P,R,S],[B,C,E,G,H,J,M,P,R,S,U],[B,C,E,G,H,J,M,P,R,U],[B,C,E,G,H,J,M,P,S,U],[B,C,E,G,H,J,M,P,U],[B,C,E,G,J],[B,C,E,G,J,M],[B,C,E,G,J,M,N,P,Q,R,S,U],[B,C,E,G,J,M,N,P,Q,R,U],[B,C,E,G,J,M,N,P,Q,S,U],[B,C,E,G,J,M,N,P,Q,U],[B,C,E,G,J,M,N,P,R,S,U],[B,C,E,G,J,M,N,P,R,U],[B,C,E,G,J,M,N,P,S,U],[B,C,E,G,J,M,N,P,U],[B,C,E,G,J,M,P],[B,C,E,G,J,M,P,Q],[B,C,E,G,J,M,P,Q,R],[B,C,E,G,J,M,P,Q,R,S],[B,C,E,G,J,M,P,Q,R,S,U],[B,C,E,G,J,M,P,Q,R,U],[B,C,E,G,J,M,P,Q,S],[B,C,E,G,J,M,P,Q,S,U],[B,C,E,G,J,M,P,Q,U],[B,C,E,G,J,M,P,R],[B,C,E,G,J,M,P,R,S],[B,C,E,G,J,M,P,R,S,U],[B,C,E,G,J,M,P,R,U],[B,C,E,G,J,M,P,S],[B,C,E,G,J,M,P,S,U],[B,C,E,G,J,M,P,U],[B,C,E,G,J,M,Q],[B,C,E,G,J,M,Q,R],[B,C,E,G,J,M,R],[B,C,E,G,J,Q],[B,C,E,G,J,Q,R],[B,C,E,G,J,R],[B,C,E,H,J,M,N,P,Q,R,S,U],[B,C,E,H,J,M,N,P,Q,R,U],[B,C,E,H,J,M,N,P,Q,S,U],[B,C,E,H,J,M,N,P,Q,U],[B,C,E,H,J,M,N,P,R,S,U],[B,C,E,H,J,M,N,P,R,U],[B,C,E,H,J,M,N,P,S,U],[B,C,E,H,J,M,N,P,U],[B,C,E,H,J,M,P,Q,R,S,U],[B,C,E,H,J,M,P,Q,R,U],[B,C,E,H,J,M,P,Q,S,U],[B,C,E,H,J,M,P,Q,U],[B,C,E,H,J,M,P,R,S,U],[B,C,E,H,J,M,P,R,U],[B,C,E,H,J,M,P,S],[B,C,E,H,J,M,P,S,U],[B,C,E,H,J,M,P,U],[B,C,E,J],[B,C,E,J,M],[B,C,E,J,M,N,P,Q,R,S,U],[B,C,E,J,M,N,P,Q,R,U],[B,C,E,J,M,N,P,Q,S,U],[B,C,E,J,M,N,P,Q,U],[B,C,E,J,M,N,P,R,S,U],[B,C,E,J,M,N,P,R,U],[B,C,E,J,M,N,P,S,U],[B,C,E,J,M,N,P,U],[B,C,E,J,M,P],[B,C,E,J,M,P,Q],[B,C,E,J,M,P,Q,R],[B,C,E,J,M,P,Q,R,S],[B,C,E,J,M,P,Q,R,S,U],[B,C,E,J,M,P,Q,R,U],[B,C,E,J,M,P,Q,S],[B,C,E,J,M,P,Q,S,U],[B,C,E,J,M,P,Q,U],[B,C,E,J,M,P,R],[B,C,E,J,M,P,R,S],[B,C,E,J,M,P,R,S,U],[B,C,E,J,M,P,R,U],[B,C,E,J,M,P,S],[B,C,E,J,M,P,S,U],[B,C,E,J,M,P,U],[B,C,E,J,M,Q],[B,C,E,J,M,Q,R],[B,C,E,J,M,R],[B,C,E,J,Q],[B,C,E,J,Q,R],[B,C,E,J,R],[B,C,F,G,H,J,M,N,P,Q,R,S,U],[B,C,F,G,H,J,M,N,P,Q,R,U],[B,C,F,G,H,J,M,N,P,Q,S,U],[B,C,F,G,H,J,M,N,P,Q,U],[B,C,F,G,H,J,M,N,P,R,S,U],[B,C,F,G,H,J,M,N,P,R,U],[B,C,F,G,H,J,M,N,P,S,U],[B,C,F,G,H,J,M,N,P,U],[B,C,F,G,H,J,M,P,Q,R,S],[B,C,F,G,H,J,M,P,Q,R,S,U],[B,C,F,G,H,J,M,P,Q,R,U],[B,C,F,G,H,J,M,P,Q,S,U],[B,C,F,G,H,J,M,P,Q,U],[B,C,F,G,H,J,M,P,R,S,U],[B,C,F,G,H,J,M,P,R,U],[B,C,F,G,H,J,M,P,S,U],[B,C,F,G,H,J,M,P,U],[B,C,F,G,J],[B,C,F,G,J,M],[B,C,F,G,J,M,N,P,Q,R,S,U],[B,C,F,G,J,M,N,P,Q,R,U],[B,C,F,G,J,M,N,P,Q,S,U],[B,C,F,G,J,M,N,P,Q,U],[B,C,F,G,J,M,N,P,R,S,U],[B,C,F,G,J,M,N,P,R,U],[B,C,F,G,J,M,N,P,S,U],[B,C,F,G,J,M,N,P,U],[B,C,F,G,J,M,P],[B,C,F,G,J,M,P,Q],[B,C,F,G,J,M,P,Q,R],[B,C,F,G,J,M,P,Q,R,S],[B,C,F,G,J,M,P,Q,R,S,U],[B,C,F,G,J,M,P,Q,R,U],[B,C,F,G,J,M,P,Q,S],[B,C,F,G,J,M,P,Q,S,U],[B,C,F,G,J,M,P,Q,U],[B,C,F,G,J,M,P,R],[B,C,F,G,J,M,P,R,S],[B,C,F,G,J,M,P,R,S,U],[B,C,F,G,J,M,P,R,U],[B,C,F,G,J,M,P,S],[B,C,F,G,J,M,P,S,U],[B,C,F,G,J,M,P,U],[B,C,F,G,J,M,Q],[B,C,F,G,J,M,Q,R],[B,C,F,G,J,M,R],[B,C,F,G,J,Q],[B,C,F,G,J,Q,R],[B,C,F,G,J,R],[B,C,F,H,J,M,N,P,Q,R,S,U],[B,C,F,H,J,M,N,P,Q,R,U],[B,C,F,H,J,M,N,P,Q,S,U],[B,C,F,H,J,M,N,P,Q,U],[B,C,F,H,J,M,N,P,R,S,U],[B,C,F,H,J,M,N,P,R,U],[B,C,F,H,J,M,N,P,S,U],[B,C,F,H,J,M,N,P,U],[B,C,F,H,J,M,P,Q,R,S,U],[B,C,F,H,J,M,P,Q,R,U],[B,C,F,H,J,M,P,Q,S],[B,C,F,H,J,M,P,Q,S,U],[B,C,F,H,J,M,P,Q,U],[B,C,F,H,J,M,P,R,S,U],[B,C,F,H,J,M,P,R,U],[B,C,F,H,J,M,P,S,U],[B,C,F,H,J,M,P,U],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N,P,Q,R,S,U],[B,C,F,J,M,N,P,Q,R,U],[B,C,F,J,M,N,P,Q,S,U],[B,C,F,J,M,N,P,Q,U],[B,C,F,J,M,N,P,R,S,U],[B,C,F,J,M,N,P,R,U],[B,C,F,J,M,N,P,S,U],[B,C,F,J,M,N,P,U],[B,C,F,J,M,P],[B,C,F,J,M,P,Q],[B,C,F,J,M,P,Q,R],[B,C,F,J,M,P,Q,R,S],[B,C,F,J,M,P,Q,R,S,U],[B,C,F,J,M,P,Q,R,U],[B,C,F,J,M,P,Q,S],[B,C,F,J,M,P,Q,S,U],[B,C,F,J,M,P,Q,U],[B,C,F,J,M,P,R],[B,C,F,J,M,P,R,S],[B,C,F,J,M,P,R,S,U],[B,C,F,J,M,P,R,U],[B,C,F,J,M,P,S],[B,C,F,J,M,P,S,U],[B,C,F,J,M,P,U],[B,C,F,J,M,Q],[B,C,F,J,M,Q,R],[B,C,F,J,M,R],[B,C,F,J,Q],[B,C,F,J,Q,R],[B,C,F,J,R],[B,C,G,H,J,M,N,P,Q,R,S,U],[B,C,G,H,J,M,N,P,Q,R,U],[B,C,G,H,J,M,N,P,Q,S,U],[B,C,G,H,J,M,N,P,Q,U],[B,C,G,H,J,M,N,P,R,S,U],[B,C,G,H,J,M,N,P,R,U],[B,C,G,H,J,M,N,P,S,U],[B,C,G,H,J,M,N,P,U],[B,C,G,H,J,M,P,Q,R,S,U],[B,C,G,H,J,M,P,Q,R,U],[B,C,G,H,J,M,P,Q,S,U],[B,C,G,H,J,M,P,Q,U],[B,C,G,H,J,M,P,R,S],[B,C,G,H,J,M,P,R,S,U],[B,C,G,H,J,M,P,R,U],[B,C,G,H,J,M,P,S,U],[B,C,G,H,J,M,P,U],[B,C,G,J],[B,C,G,J,M],[B,C,G,J,M,N,P,Q,R,S,U],[B,C,G,J,M,N,P,Q,R,U],[B,C,G,J,M,N,P,Q,S,U],[B,C,G,J,M,N,P,Q,U],[B,C,G,J,M,N,P,R,S,U],[B,C,G,J,M,N,P,R,U],[B,C,G,J,M,N,P,S,U],[B,C,G,J,M,N,P,U],[B,C,G,J,M,P],[B,C,G,J,M,P,Q],[B,C,G,J,M,P,Q,R],[B,C,G,J,M,P,Q,R,S],[B,C,G,J,M,P,Q,R,S,U],[B,C,G,J,M,P,Q,R,U],[B,C,G,J,M,P,Q,S],[B,C,G,J,M,P,Q,S,U],[B,C,G,J,M,P,Q,U],[B,C,G,J,M,P,R],[B,C,G,J,M,P,R,S],[B,C,G,J,M,P,R,S,U],[B,C,G,J,M,P,R,U],[B,C,G,J,M,P,S],[B,C,G,J,M,P,S,U],[B,C,G,J,M,P,U],[B,C,G,J,M,Q],[B,C,G,J,M,Q,R],[B,C,G,J,M,R],[B,C,G,J,Q],[B,C,G,J,Q,R],[B,C,G,J,R],[B,C,H,J,M,N,P,Q,R,S,U],[B,C,H,J,M,N,P,Q,R,U],[B,C,H,J,M,N,P,Q,S,U],[B,C,H,J,M,N,P,Q,U],[B,C,H,J,M,N,P,R,S,U],[B,C,H,J,M,N,P,R,U],[B,C,H,J,M,N,P,S,U],[B,C,H,J,M,N,P,U],[B,C,H,J,M,P,Q,R,S,U],[B,C,H,J,M,P,Q,R,U],[B,C,H,J,M,P,Q,S,U],[B,C,H,J,M,P,Q,U],[B,C,H,J,M,P,R,S,U],[B,C,H,J,M,P,R,U],[B,C,H,J,M,P,S],[B,C,H,J,M,P,S,U],[B,C,H,J,M,P,U],[B,C,J],[B,C,J,M],[B,C,J,M,N,P,Q,R,S,U],[B,C,J,M,N,P,Q,R,U],[B,C,J,M,N,P,Q,S,U],[B,C,J,M,N,P,Q,U],[B,C,J,M,N,P,R,S,U],[B,C,J,M,N,P,R,U],[B,C,J,M,N,P,S,U],[B,C,J,M,N,P,U],[B,C,J,M,P],[B,C,J,M,P,Q],[B,C,J,M,P,Q,R],[B,C,J,M,P,Q,R,S],[B,C,J,M,P,Q,R,S,U],[B,C,J,M,P,Q,R,U],[B,C,J,M,P,Q,S],[B,C,J,M,P,Q,S,U],[B,C,J,M,P,Q,U],[B,C,J,M,P,R],[B,C,J,M,P,R,S],[B,C,J,M,P,R,S,U],[B,C,J,M,P,R,U],[B,C,J,M,P,S],[B,C,J,M,P,S,U],[B,C,J,M,P,U],[B,C,J,M,Q],[B,C,J,M,Q,R],[B,C,J,M,R],[B,C,J,Q],[B,C,J,Q,R],[B,C,J,R],[B,D,E,F,G,H,J,M,N,P,Q,R,S,U],[B,D,E,F,G,H,J,M,N,P,Q,R,U],[B,D,E,F,G,H,J,M,N,P,Q,S,U],[B,D,E,F,G,H,J,M,N,P,Q,U],[B,D,E,F,G,H,J,M,N,P,R,S,U],[B,D,E,F,G,H,J,M,N,P,R,U],[B,D,E,F,G,H,J,M,N,P,S,U],[B,D,E,F,G,H,J,M,N,P,U],[B,D,E,F,G,H,J,M,P,Q,R,S],[B,D,E,F,G,H,J,M,P,Q,R,S,U],[B,D,E,F,G,H,J,M,P,Q,R,U],[B,D,E,F,G,H,J,M,P,Q,S,U],[B,D,E,F,G,H,J,M,P,Q,U],[B,D,E,F,G,H,J,M,P,R,S,U],[B,D,E,F,G,H,J,M,P,R,U],[B,D,E,F,G,H,J,M,P,S,U],[B,D,E,F,G,H,J,M,P,U],[B,D,E,F,G,J],[B,D,E,F,G,J,M],[B,D,E,F,G,J,M,N,P,Q,R,S,U],[B,D,E,F,G,J,M,N,P,Q,R,U],[B,D,E,F,G,J,M,N,P,Q,S,U],[B,D,E,F,G,J,M,N,P,Q,U],[B,D,E,F,G,J,M,N,P,R,S,U],[B,D,E,F,G,J,M,N,P,R,U],[B,D,E,F,G,J,M,N,P,S,U],[B,D,E,F,G,J,M,N,P,U],[B,D,E,F,G,J,M,P],[B,D,E,F,G,J,M,P,Q],[B,D,E,F,G,J,M,P,Q,R],[B,D,E,F,G,J,M,P,Q,R,S],[B,D,E,F,G,J,M,P,Q,R,S,U],[B,D,E,F,G,J,M,P,Q,R,U],[B,D,E,F,G,J,M,P,Q,S],[B,D,E,F,G,J,M,P,Q,S,U],[B,D,E,F,G,J,M,P,Q,U],[B,D,E,F,G,J,M,P,R],[B,D,E,F,G,J,M,P,R,S],[B,D,E,F,G,J,M,P,R,S,U],[B,D,E,F,G,J,M,P,R,U],[B,D,E,F,G,J,M,P,S],[B,D,E,F,G,J,M,P,S,U],[B,D,E,F,G,J,M,P,U],[B,D,E,F,G,J,M,Q],[B,D,E,F,G,J,M,Q,R],[B,D,E,F,G,J,M,R],[B,D,E,F,G,J,Q],[B,D,E,F,G,J,Q,R],[B,D,E,F,G,J,R],[B,D,E,F,H,J,M,N,P,Q,R,S,U],[B,D,E,F,H,J,M,N,P,Q,R,U],[B,D,E,F,H,J,M,N,P,Q,S,U],[B,D,E,F,H,J,M,N,P,Q,U],[B,D,E,F,H,J,M,N,P,R,S,U],[B,D,E,F,H,J,M,N,P,R,U],[B,D,E,F,H,J,M,N,P,S,U],[B,D,E,F,H,J,M,N,P,U],[B,D,E,F,H,J,M,P,Q,R,S,U],[B,D,E,F,H,J,M,P,Q,R,U],[B,D,E,F,H,J,M,P,Q,S],[B,D,E,F,H,J,M,P,Q,S,U],[B,D,E,F,H,J,M,P,Q,U],[B,D,E,F,H,J,M,P,R,S,U],[B,D,E,F,H,J,M,P,R,U],[B,D,E,F,H,J,M,P,S,U],[B,D,E,F,H,J,M,P,U],[B,D,E,F,J],[B,D,E,F,J,M],[B,D,E,F,J,M,N,P,Q,R,S,U],[B,D,E,F,J,M,N,P,Q,R,U],[B,D,E,F,J,M,N,P,Q,S,U],[B,D,E,F,J,M,N,P,Q,U],[B,D,E,F,J,M,N,P,R,S,U],[B,D,E,F,J,M,N,P,R,U],[B,D,E,F,J,M,N,P,S,U],[B,D,E,F,J,M,N,P,U],[B,D,E,F,J,M,P],[B,D,E,F,J,M,P,Q],[B,D,E,F,J,M,P,Q,R],[B,D,E,F,J,M,P,Q,R,S],[B,D,E,F,J,M,P,Q,R,S,U],[B,D,E,F,J,M,P,Q,R,U],[B,D,E,F,J,M,P,Q,S],[B,D,E,F,J,M,P,Q,S,U],[B,D,E,F,J,M,P,Q,U],[B,D,E,F,J,M,P,R],[B,D,E,F,J,M,P,R,S],[B,D,E,F,J,M,P,R,S,U],[B,D,E,F,J,M,P,R,U],[B,D,E,F,J,M,P,S],[B,D,E,F,J,M,P,S,U],[B,D,E,F,J,M,P,U],[B,D,E,F,J,M,Q],[B,D,E,F,J,M,Q,R],[B,D,E,F,J,M,R],[B,D,E,F,J,Q],[B,D,E,F,J,Q,R],[B,D,E,F,J,R],[B,D,E,G,H,J,M,N,P,Q,R,S,U],[B,D,E,G,H,J,M,N,P,Q,R,U],[B,D,E,G,H,J,M,N,P,Q,S,U],[B,D,E,G,H,J,M,N,P,Q,U],[B,D,E,G,H,J,M,N,P,R,S,U],[B,D,E,G,H,J,M,N,P,R,U],[B,D,E,G,H,J,M,N,P,S,U],[B,D,E,G,H,J,M,N,P,U],[B,D,E,G,H,J,M,P,Q,R,S,U],[B,D,E,G,H,J,M,P,Q,R,U],[B,D,E,G,H,J,M,P,Q,S,U],[B,D,E,G,H,J,M,P,Q,U],[B,D,E,G,H,J,M,P,R,S],[B,D,E,G,H,J,M,P,R,S,U],[B,D,E,G,H,J,M,P,R,U],[B,D,E,G,H,J,M,P,S,U],[B,D,E,G,H,J,M,P,U],[B,D,E,G,J],[B,D,E,G,J,M],[B,D,E,G,J,M,N,P,Q,R,S,U],[B,D,E,G,J,M,N,P,Q,R,U],[B,D,E,G,J,M,N,P,Q,S,U],[B,D,E,G,J,M,N,P,Q,U],[B,D,E,G,J,M,N,P,R,S,U],[B,D,E,G,J,M,N,P,R,U],[B,D,E,G,J,M,N,P,S,U],[B,D,E,G,J,M,N,P,U],[B,D,E,G,J,M,P],[B,D,E,G,J,M,P,Q],[B,D,E,G,J,M,P,Q,R],[B,D,E,G,J,M,P,Q,R,S],[B,D,E,G,J,M,P,Q,R,S,U],[B,D,E,G,J,M,P,Q,R,U],[B,D,E,G,J,M,P,Q,S],[B,D,E,G,J,M,P,Q,S,U],[B,D,E,G,J,M,P,Q,U],[B,D,E,G,J,M,P,R],[B,D,E,G,J,M,P,R,S],[B,D,E,G,J,M,P,R,S,U],[B,D,E,G,J,M,P,R,U],[B,D,E,G,J,M,P,S],[B,D,E,G,J,M,P,S,U],[B,D,E,G,J,M,P,U],[B,D,E,G,J,M,Q],[B,D,E,G,J,M,Q,R],[B,D,E,G,J,M,R],[B,D,E,G,J,Q],[B,D,E,G,J,Q,R],[B,D,E,G,J,R],[B,D,E,H,J,M,N,P,Q,R,S,U],[B,D,E,H,J,M,N,P,Q,R,U],[B,D,E,H,J,M,N,P,Q,S,U],[B,D,E,H,J,M,N,P,Q,U],[B,D,E,H,J,M,N,P,R,S,U],[B,D,E,H,J,M,N,P,R,U],[B,D,E,H,J,M,N,P,S,U],[B,D,E,H,J,M,N,P,U],[B,D,E,H,J,M,P,Q,R,S,U],[B,D,E,H,J,M,P,Q,R,U],[B,D,E,H,J,M,P,Q,S,U],[B,D,E,H,J,M,P,Q,U],[B,D,E,H,J,M,P,R,S,U],[B,D,E,H,J,M,P,R,U],[B,D,E,H,J,M,P,S],[B,D,E,H,J,M,P,S,U],[B,D,E,H,J,M,P,U],[B,D,E,J],[B,D,E,J,M],[B,D,E,J,M,N,P,Q,R,S,U],[B,D,E,J,M,N,P,Q,R,U],[B,D,E,J,M,N,P,Q,S,U],[B,D,E,J,M,N,P,Q,U],[B,D,E,J,M,N,P,R,S,U],[B,D,E,J,M,N,P,R,U],[B,D,E,J,M,N,P,S,U],[B,D,E,J,M,N,P,U],[B,D,E,J,M,P],[B,D,E,J,M,P,Q],[B,D,E,J,M,P,Q,R],[B,D,E,J,M,P,Q,R,S],[B,D,E,J,M,P,Q,R,S,U],[B,D,E,J,M,P,Q,R,U],[B,D,E,J,M,P,Q,S],[B,D,E,J,M,P,Q,S,U],[B,D,E,J,M,P,Q,U],[B,D,E,J,M,P,R],[B,D,E,J,M,P,R,S],[B,D,E,J,M,P,R,S,U],[B,D,E,J,M,P,R,U],[B,D,E,J,M,P,S],[B,D,E,J,M,P,S,U],[B,D,E,J,M,P,U],[B,D,E,J,M,Q],[B,D,E,J,M,Q,R],[B,D,E,J,M,R],[B,D,E,J,Q],[B,D,E,J,Q,R],[B,D,E,J,R],[B,D,F,G,H,J,M,N,P,Q,R,S,U],[B,D,F,G,H,J,M,N,P,Q,R,U],[B,D,F,G,H,J,M,N,P,Q,S,U],[B,D,F,G,H,J,M,N,P,Q,U],[B,D,F,G,H,J,M,N,P,R,S,U],[B,D,F,G,H,J,M,N,P,R,U],[B,D,F,G,H,J,M,N,P,S,U],[B,D,F,G,H,J,M,N,P,U],[B,D,F,G,H,J,M,P,Q,R,S],[B,D,F,G,H,J,M,P,Q,R,S,U],[B,D,F,G,H,J,M,P,Q,R,U],[B,D,F,G,H,J,M,P,Q,S,U],[B,D,F,G,H,J,M,P,Q,U],[B,D,F,G,H,J,M,P,R,S,U],[B,D,F,G,H,J,M,P,R,U],[B,D,F,G,H,J,M,P,S,U],[B,D,F,G,H,J,M,P,U],[B,D,F,G,J],[B,D,F,G,J,M],[B,D,F,G,J,M,N,P,Q,R,S,U],[B,D,F,G,J,M,N,P,Q,R,U],[B,D,F,G,J,M,N,P,Q,S,U],[B,D,F,G,J,M,N,P,Q,U],[B,D,F,G,J,M,N,P,R,S,U],[B,D,F,G,J,M,N,P,R,U],[B,D,F,G,J,M,N,P,S,U],[B,D,F,G,J,M,N,P,U],[B,D,F,G,J,M,P],[B,D,F,G,J,M,P,Q],[B,D,F,G,J,M,P,Q,R],[B,D,F,G,J,M,P,Q,R,S],[B,D,F,G,J,M,P,Q,R,S,U],[B,D,F,G,J,M,P,Q,R,U],[B,D,F,G,J,M,P,Q,S],[B,D,F,G,J,M,P,Q,S,U],[B,D,F,G,J,M,P,Q,U],[B,D,F,G,J,M,P,R],[B,D,F,G,J,M,P,R,S],[B,D,F,G,J,M,P,R,S,U],[B,D,F,G,J,M,P,R,U],[B,D,F,G,J,M,P,S],[B,D,F,G,J,M,P,S,U],[B,D,F,G,J,M,P,U],[B,D,F,G,J,M,Q],[B,D,F,G,J,M,Q,R],[B,D,F,G,J,M,R],[B,D,F,G,J,Q],[B,D,F,G,J,Q,R],[B,D,F,G,J,R],[B,D,F,H,J,M,N,P,Q,R,S,U],[B,D,F,H,J,M,N,P,Q,R,U],[B,D,F,H,J,M,N,P,Q,S,U],[B,D,F,H,J,M,N,P,Q,U],[B,D,F,H,J,M,N,P,R,S,U],[B,D,F,H,J,M,N,P,R,U],[B,D,F,H,J,M,N,P,S,U],[B,D,F,H,J,M,N,P,U],[B,D,F,H,J,M,P,Q,R,S,U],[B,D,F,H,J,M,P,Q,R,U],[B,D,F,H,J,M,P,Q,S],[B,D,F,H,J,M,P,Q,S,U],[B,D,F,H,J,M,P,Q,U],[B,D,F,H,J,M,P,R,S,U],[B,D,F,H,J,M,P,R,U],[B,D,F,H,J,M,P,S,U],[B,D,F,H,J,M,P,U],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N,P,Q,R,S,U],[B,D,F,J,M,N,P,Q,R,U],[B,D,F,J,M,N,P,Q,S,U],[B,D,F,J,M,N,P,Q,U],[B,D,F,J,M,N,P,R,S,U],[B,D,F,J,M,N,P,R,U],[B,D,F,J,M,N,P,S,U],[B,D,F,J,M,N,P,U],[B,D,F,J,M,P],[B,D,F,J,M,P,Q],[B,D,F,J,M,P,Q,R],[B,D,F,J,M,P,Q,R,S],[B,D,F,J,M,P,Q,R,S,U],[B,D,F,J,M,P,Q,R,U],[B,D,F,J,M,P,Q,S],[B,D,F,J,M,P,Q,S,U],[B,D,F,J,M,P,Q,U],[B,D,F,J,M,P,R],[B,D,F,J,M,P,R,S],[B,D,F,J,M,P,R,S,U],[B,D,F,J,M,P,R,U],[B,D,F,J,M,P,S],[B,D,F,J,M,P,S,U],[B,D,F,J,M,P,U],[B,D,F,J,M,Q],[B,D,F,J,M,Q,R],[B,D,F,J,M,R],[B,D,F,J,Q],[B,D,F,J,Q,R],[B,D,F,J,R],[B,D,G,H,J,M,N,P,Q,R,S,U],[B,D,G,H,J,M,N,P,Q,R,U],[B,D,G,H,J,M,N,P,Q,S,U],[B,D,G,H,J,M,N,P,Q,U],[B,D,G,H,J,M,N,P,R,S,U],[B,D,G,H,J,M,N,P,R,U],[B,D,G,H,J,M,N,P,S,U],[B,D,G,H,J,M,N,P,U],[B,D,G,H,J,M,P,Q,R,S,U],[B,D,G,H,J,M,P,Q,R,U],[B,D,G,H,J,M,P,Q,S,U],[B,D,G,H,J,M,P,Q,U],[B,D,G,H,J,M,P,R,S],[B,D,G,H,J,M,P,R,S,U],[B,D,G,H,J,M,P,R,U],[B,D,G,H,J,M,P,S,U],[B,D,G,H,J,M,P,U],[B,D,G,J],[B,D,G,J,M],[B,D,G,J,M,N,P,Q,R,S,U],[B,D,G,J,M,N,P,Q,R,U],[B,D,G,J,M,N,P,Q,S,U],[B,D,G,J,M,N,P,Q,U],[B,D,G,J,M,N,P,R,S,U],[B,D,G,J,M,N,P,R,U],[B,D,G,J,M,N,P,S,U],[B,D,G,J,M,N,P,U],[B,D,G,J,M,P],[B,D,G,J,M,P,Q],[B,D,G,J,M,P,Q,R],[B,D,G,J,M,P,Q,R,S],[B,D,G,J,M,P,Q,R,S,U],[B,D,G,J,M,P,Q,R,U],[B,D,G,J,M,P,Q,S],[B,D,G,J,M,P,Q,S,U],[B,D,G,J,M,P,Q,U],[B,D,G,J,M,P,R],[B,D,G,J,M,P,R,S],[B,D,G,J,M,P,R,S,U],[B,D,G,J,M,P,R,U],[B,D,G,J,M,P,S],[B,D,G,J,M,P,S,U],[B,D,G,J,M,P,U],[B,D,G,J,M,Q],[B,D,G,J,M,Q,R],[B,D,G,J,M,R],[B,D,G,J,Q],[B,D,G,J,Q,R],[B,D,G,J,R],[B,D,H,J,M,N,P,Q,R,S,U],[B,D,H,J,M,N,P,Q,R,U],[B,D,H,J,M,N,P,Q,S,U],[B,D,H,J,M,N,P,Q,U],[B,D,H,J,M,N,P,R,S,U],[B,D,H,J,M,N,P,R,U],[B,D,H,J,M,N,P,S,U],[B,D,H,J,M,N,P,U],[B,D,H,J,M,P,Q,R,S,U],[B,D,H,J,M,P,Q,R,U],[B,D,H,J,M,P,Q,S,U],[B,D,H,J,M,P,Q,U],[B,D,H,J,M,P,R,S,U],[B,D,H,J,M,P,R,U],[B,D,H,J,M,P,S],[B,D,H,J,M,P,S,U],[B,D,H,J,M,P,U],[B,D,J],[B,D,J,M],[B,D,J,M,N,P,Q,R,S,U],[B,D,J,M,N,P,Q,R,U],[B,D,J,M,N,P,Q,S,U],[B,D,J,M,N,P,Q,U],[B,D,J,M,N,P,R,S,U],[B,D,J,M,N,P,R,U],[B,D,J,M,N,P,S,U],[B,D,J,M,N,P,U],[B,D,J,M,P],[B,D,J,M,P,Q],[B,D,J,M,P,Q,R],[B,D,J,M,P,Q,R,S],[B,D,J,M,P,Q,R,S,U],[B,D,J,M,P,Q,R,U],[B,D,J,M,P,Q,S],[B,D,J,M,P,Q,S,U],[B,D,J,M,P,Q,U],[B,D,J,M,P,R],[B,D,J,M,P,R,S],[B,D,J,M,P,R,S,U],[B,D,J,M,P,R,U],[B,D,J,M,P,S],[B,D,J,M,P,S,U],[B,D,J,M,P,U],[B,D,J,M,Q],[B,D,J,M,Q,R],[B,D,J,M,R],[B,D,J,Q],[B,D,J,Q,R],[B,D,J,R],[B,E,F,G,H,J,M,N,P,Q,R,S,U],[B,E,F,G,H,J,M,N,P,Q,R,U],[B,E,F,G,H,J,M,N,P,Q,S,U],[B,E,F,G,H,J,M,N,P,Q,U],[B,E,F,G,H,J,M,N,P,R,S,U],[B,E,F,G,H,J,M,N,P,R,U],[B,E,F,G,H,J,M,N,P,S,U],[B,E,F,G,H,J,M,N,P,U],[B,E,F,G,H,J,M,P,Q,R,S],[B,E,F,G,H,J,M,P,Q,R,S,U],[B,E,F,G,H,J,M,P,Q,R,U],[B,E,F,G,H,J,M,P,Q,S,U],[B,E,F,G,H,J,M,P,Q,U],[B,E,F,G,H,J,M,P,R,S,U],[B,E,F,G,H,J,M,P,R,U],[B,E,F,G,H,J,M,P,S,U],[B,E,F,G,H,J,M,P,U],[B,E,F,G,J],[B,E,F,G,J,M],[B,E,F,G,J,M,N,P,Q,R,S,U],[B,E,F,G,J,M,N,P,Q,R,U],[B,E,F,G,J,M,N,P,Q,S,U],[B,E,F,G,J,M,N,P,Q,U],[B,E,F,G,J,M,N,P,R,S,U],[B,E,F,G,J,M,N,P,R,U],[B,E,F,G,J,M,N,P,S,U],[B,E,F,G,J,M,N,P,U],[B,E,F,G,J,M,P],[B,E,F,G,J,M,P,Q],[B,E,F,G,J,M,P,Q,R],[B,E,F,G,J,M,P,Q,R,S],[B,E,F,G,J,M,P,Q,R,S,U],[B,E,F,G,J,M,P,Q,R,U],[B,E,F,G,J,M,P,Q,S],[B,E,F,G,J,M,P,Q,S,U],[B,E,F,G,J,M,P,Q,U],[B,E,F,G,J,M,P,R],[B,E,F,G,J,M,P,R,S],[B,E,F,G,J,M,P,R,S,U],[B,E,F,G,J,M,P,R,U],[B,E,F,G,J,M,P,S],[B,E,F,G,J,M,P,S,U],[B,E,F,G,J,M,P,U],[B,E,F,G,J,M,Q],[B,E,F,G,J,M,Q,R],[B,E,F,G,J,M,R],[B,E,F,G,J,Q],[B,E,F,G,J,Q,R],[B,E,F,G,J,R],[B,E,F,H,J,M,N,P,Q,R,S,U],[B,E,F,H,J,M,N,P,Q,R,U],[B,E,F,H,J,M,N,P,Q,S,U],[B,E,F,H,J,M,N,P,Q,U],[B,E,F,H,J,M,N,P,R,S,U],[B,E,F,H,J,M,N,P,R,U],[B,E,F,H,J,M,N,P,S,U],[B,E,F,H,J,M,N,P,U],[B,E,F,H,J,M,P,Q,R,S,U],[B,E,F,H,J,M,P,Q,R,U],[B,E,F,H,J,M,P,Q,S],[B,E,F,H,J,M,P,Q,S,U],[B,E,F,H,J,M,P,Q,U],[B,E,F,H,J,M,P,R,S,U],[B,E,F,H,J,M,P,R,U],[B,E,F,H,J,M,P,S,U],[B,E,F,H,J,M,P,U],[B,E,F,J],[B,E,F,J,M],[B,E,F,J,M,N,P,Q,R,S,U],[B,E,F,J,M,N,P,Q,R,U],[B,E,F,J,M,N,P,Q,S,U],[B,E,F,J,M,N,P,Q,U],[B,E,F,J,M,N,P,R,S,U],[B,E,F,J,M,N,P,R,U],[B,E,F,J,M,N,P,S,U],[B,E,F,J,M,N,P,U],[B,E,F,J,M,P],[B,E,F,J,M,P,Q],[B,E,F,J,M,P,Q,R],[B,E,F,J,M,P,Q,R,S],[B,E,F,J,M,P,Q,R,S,U],[B,E,F,J,M,P,Q,R,U],[B,E,F,J,M,P,Q,S],[B,E,F,J,M,P,Q,S,U],[B,E,F,J,M,P,Q,U],[B,E,F,J,M,P,R],[B,E,F,J,M,P,R,S],[B,E,F,J,M,P,R,S,U],[B,E,F,J,M,P,R,U],[B,E,F,J,M,P,S],[B,E,F,J,M,P,S,U],[B,E,F,J,M,P,U],[B,E,F,J,M,Q],[B,E,F,J,M,Q,R],[B,E,F,J,M,R],[B,E,F,J,Q],[B,E,F,J,Q,R],[B,E,F,J,R],[B,E,G,H,J,M,N,P,Q,R,S,U],[B,E,G,H,J,M,N,P,Q,R,U],[B,E,G,H,J,M,N,P,Q,S,U],[B,E,G,H,J,M,N,P,Q,U],[B,E,G,H,J,M,N,P,R,S,U],[B,E,G,H,J,M,N,P,R,U],[B,E,G,H,J,M,N,P,S,U],[B,E,G,H,J,M,N,P,U],[B,E,G,H,J,M,P,Q,R,S,U],[B,E,G,H,J,M,P,Q,R,U],[B,E,G,H,J,M,P,Q,S,U],[B,E,G,H,J,M,P,Q,U],[B,E,G,H,J,M,P,R,S],[B,E,G,H,J,M,P,R,S,U],[B,E,G,H,J,M,P,R,U],[B,E,G,H,J,M,P,S,U],[B,E,G,H,J,M,P,U],[B,E,G,J],[B,E,G,J,M],[B,E,G,J,M,N,P,Q,R,S,U],[B,E,G,J,M,N,P,Q,R,U],[B,E,G,J,M,N,P,Q,S,U],[B,E,G,J,M,N,P,Q,U],[B,E,G,J,M,N,P,R,S,U],[B,E,G,J,M,N,P,R,U],[B,E,G,J,M,N,P,S,U],[B,E,G,J,M,N,P,U],[B,E,G,J,M,P],[B,E,G,J,M,P,Q],[B,E,G,J,M,P,Q,R],[B,E,G,J,M,P,Q,R,S],[B,E,G,J,M,P,Q,R,S,U],[B,E,G,J,M,P,Q,R,U],[B,E,G,J,M,P,Q,S],[B,E,G,J,M,P,Q,S,U],[B,E,G,J,M,P,Q,U],[B,E,G,J,M,P,R],[B,E,G,J,M,P,R,S],[B,E,G,J,M,P,R,S,U],[B,E,G,J,M,P,R,U],[B,E,G,J,M,P,S],[B,E,G,J,M,P,S,U],[B,E,G,J,M,P,U],[B,E,G,J,M,Q],[B,E,G,J,M,Q,R],[B,E,G,J,M,R],[B,E,G,J,Q],[B,E,G,J,Q,R],[B,E,G,J,R],[B,E,H,J,M,N,P,Q,R,S,U],[B,E,H,J,M,N,P,Q,R,U],[B,E,H,J,M,N,P,Q,S,U],[B,E,H,J,M,N,P,Q,U],[B,E,H,J,M,N,P,R,S,U],[B,E,H,J,M,N,P,R,U],[B,E,H,J,M,N,P,S,U],[B,E,H,J,M,N,P,U],[B,E,H,J,M,P,Q,R,S,U],[B,E,H,J,M,P,Q,R,U],[B,E,H,J,M,P,Q,S,U],[B,E,H,J,M,P,Q,U],[B,E,H,J,M,P,R,S,U],[B,E,H,J,M,P,R,U],[B,E,H,J,M,P,S],[B,E,H,J,M,P,S,U],[B,E,H,J,M,P,U],[B,E,J],[B,E,J,M],[B,E,J,M,N,P,Q,R,S,U],[B,E,J,M,N,P,Q,R,U],[B,E,J,M,N,P,Q,S,U],[B,E,J,M,N,P,Q,U],[B,E,J,M,N,P,R,S,U],[B,E,J,M,N,P,R,U],[B,E,J,M,N,P,S,U],[B,E,J,M,N,P,U],[B,E,J,M,P],[B,E,J,M,P,Q],[B,E,J,M,P,Q,R],[B,E,J,M,P,Q,R,S],[B,E,J,M,P,Q,R,S,U],[B,E,J,M,P,Q,R,U],[B,E,J,M,P,Q,S],[B,E,J,M,P,Q,S,U],[B,E,J,M,P,Q,U],[B,E,J,M,P,R],[B,E,J,M,P,R,S],[B,E,J,M,P,R,S,U],[B,E,J,M,P,R,U],[B,E,J,M,P,S],[B,E,J,M,P,S,U],[B,E,J,M,P,U],[B,E,J,M,Q],[B,E,J,M,Q,R],[B,E,J,M,R],[B,E,J,Q],[B,E,J,Q,R],[B,E,J,R],[B,F,G,H,J,M,N,P,Q,R,S,U],[B,F,G,H,J,M,N,P,Q,R,U],[B,F,G,H,J,M,N,P,Q,S,U],[B,F,G,H,J,M,N,P,Q,U],[B,F,G,H,J,M,N,P,R,S,U],[B,F,G,H,J,M,N,P,R,U],[B,F,G,H,J,M,N,P,S,U],[B,F,G,H,J,M,N,P,U],[B,F,G,H,J,M,P,Q,R,S],[B,F,G,H,J,M,P,Q,R,S,U],[B,F,G,H,J,M,P,Q,R,U],[B,F,G,H,J,M,P,Q,S,U],[B,F,G,H,J,M,P,Q,U],[B,F,G,H,J,M,P,R,S,U],[B,F,G,H,J,M,P,R,U],[B,F,G,H,J,M,P,S,U],[B,F,G,H,J,M,P,U],[B,F,G,J],[B,F,G,J,M],[B,F,G,J,M,N,P,Q,R,S,U],[B,F,G,J,M,N,P,Q,R,U],[B,F,G,J,M,N,P,Q,S,U],[B,F,G,J,M,N,P,Q,U],[B,F,G,J,M,N,P,R,S,U],[B,F,G,J,M,N,P,R,U],[B,F,G,J,M,N,P,S,U],[B,F,G,J,M,N,P,U],[B,F,G,J,M,P],[B,F,G,J,M,P,Q],[B,F,G,J,M,P,Q,R],[B,F,G,J,M,P,Q,R,S],[B,F,G,J,M,P,Q,R,S,U],[B,F,G,J,M,P,Q,R,U],[B,F,G,J,M,P,Q,S],[B,F,G,J,M,P,Q,S,U],[B,F,G,J,M,P,Q,U],[B,F,G,J,M,P,R],[B,F,G,J,M,P,R,S],[B,F,G,J,M,P,R,S,U],[B,F,G,J,M,P,R,U],[B,F,G,J,M,P,S],[B,F,G,J,M,P,S,U],[B,F,G,J,M,P,U],[B,F,G,J,M,Q],[B,F,G,J,M,Q,R],[B,F,G,J,M,R],[B,F,G,J,Q],[B,F,G,J,Q,R],[B,F,G,J,R],[B,F,H,J,M,N,P,Q,R,S,U],[B,F,H,J,M,N,P,Q,R,U],[B,F,H,J,M,N,P,Q,S,U],[B,F,H,J,M,N,P,Q,U],[B,F,H,J,M,N,P,R,S,U],[B,F,H,J,M,N,P,R,U],[B,F,H,J,M,N,P,S,U],[B,F,H,J,M,N,P,U],[B,F,H,J,M,P,Q,R,S,U],[B,F,H,J,M,P,Q,R,U],[B,F,H,J,M,P,Q,S],[B,F,H,J,M,P,Q,S,U],[B,F,H,J,M,P,Q,U],[B,F,H,J,M,P,R,S,U],[B,F,H,J,M,P,R,U],[B,F,H,J,M,P,S,U],[B,F,H,J,M,P,U],[B,F,J],[B,F,J,M],[B,F,J,M,N,P,Q,R,S,U],[B,F,J,M,N,P,Q,R,U],[B,F,J,M,N,P,Q,S,U],[B,F,J,M,N,P,Q,U],[B,F,J,M,N,P,R,S,U],[B,F,J,M,N,P,R,U],[B,F,J,M,N,P,S,U],[B,F,J,M,N,P,U],[B,F,J,M,P],[B,F,J,M,P,Q],[B,F,J,M,P,Q,R],[B,F,J,M,P,Q,R,S],[B,F,J,M,P,Q,R,S,U],[B,F,J,M,P,Q,R,U],[B,F,J,M,P,Q,S],[B,F,J,M,P,Q,S,U],[B,F,J,M,P,Q,U],[B,F,J,M,P,R],[B,F,J,M,P,R,S],[B,F,J,M,P,R,S,U],[B,F,J,M,P,R,U],[B,F,J,M,P,S],[B,F,J,M,P,S,U],[B,F,J,M,P,U],[B,F,J,M,Q],[B,F,J,M,Q,R],[B,F,J,M,R],[B,F,J,Q],[B,F,J,Q,R],[B,F,J,R],[B,G,H,J,M,N,P,Q,R,S,U],[B,G,H,J,M,N,P,Q,R,U],[B,G,H,J,M,N,P,Q,S,U],[B,G,H,J,M,N,P,Q,U],[B,G,H,J,M,N,P,R,S,U],[B,G,H,J,M,N,P,R,U],[B,G,H,J,M,N,P,S,U],[B,G,H,J,M,N,P,U],[B,G,H,J,M,P,Q,R,S,U],[B,G,H,J,M,P,Q,R,U],[B,G,H,J,M,P,Q,S,U],[B,G,H,J,M,P,Q,U],[B,G,H,J,M,P,R,S],[B,G,H,J,M,P,R,S,U],[B,G,H,J,M,P,R,U],[B,G,H,J,M,P,S,U],[B,G,H,J,M,P,U],[B,G,J],[B,G,J,M],[B,G,J,M,N,P,Q,R,S,U],[B,G,J,M,N,P,Q,R,U],[B,G,J,M,N,P,Q,S,U],[B,G,J,M,N,P,Q,U],[B,G,J,M,N,P,R,S,U],[B,G,J,M,N,P,R,U],[B,G,J,M,N,P,S,U],[B,G,J,M,N,P,U],[B,G,J,M,P],[B,G,J,M,P,Q],[B,G,J,M,P,Q,R],[B,G,J,M,P,Q,R,S],[B,G,J,M,P,Q,R,S,U],[B,G,J,M,P,Q,R,U],[B,G,J,M,P,Q,S],[B,G,J,M,P,Q,S,U],[B,G,J,M,P,Q,U],[B,G,J,M,P,R],[B,G,J,M,P,R,S],[B,G,J,M,P,R,S,U],[B,G,J,M,P,R,U],[B,G,J,M,P,S],[B,G,J,M,P,S,U],[B,G,J,M,P,U],[B,G,J,M,Q],[B,G,J,M,Q,R],[B,G,J,M,R],[B,G,J,Q],[B,G,J,Q,R],[B,G,J,R],[B,H,J,M,N,P,Q,R,S,U],[B,H,J,M,N,P,Q,R,U],[B,H,J,M,N,P,Q,S,U],[B,H,J,M,N,P,Q,U],[B,H,J,M,N,P,R,S,U],[B,H,J,M,N,P,R,U],[B,H,J,M,N,P,S,U],[B,H,J,M,N,P,U],[B,H,J,M,P,Q,R,S,U],[B,H,J,M,P,Q,R,U],[B,H,J,M,P,Q,S,U],[B,H,J,M,P,Q,U],[B,H,J,M,P,R,S,U],[B,H,J,M,P,R,U],[B,H,J,M,P,S],[B,H,J,M,P,S,U],[B,H,J,M,P,U],[B,J],[B,J,M],[B,J,M,N,P,Q,R,S,U],[B,J,M,N,P,Q,R,U],[B,J,M,N,P,Q,S,U],[B,J,M,N,P,Q,U],[B,J,M,N,P,R,S,U],[B,J,M,N,P,R,U],[B,J,M,N,P,S,U],[B,J,M,N,P,U],[B,J,M,P],[B,J,M,P,Q],[B,J,M,P,Q,R],[B,J,M,P,Q,R,S],[B,J,M,P,Q,R,S,U],[B,J,M,P,Q,R,U],[B,J,M,P,Q,S],[B,J,M,P,Q,S,U],[B,J,M,P,Q,U],[B,J,M,P,R],[B,J,M,P,R,S],[B,J,M,P,R,S,U],[B,J,M,P,R,U],[B,J,M,P,S],[B,J,M,P,S,U],[B,J,M,P,U],[B,J,M,Q],[B,J,M,Q,R],[B,J,M,R],[B,J,Q],[B,J,Q,R],[B,J,R],[C,D,E,F,G,H,J,M,N,P,Q,R,S,U],[C,D,E,F,G,H,J,M,N,P,Q,R,U],[C,D,E,F,G,H,J,M,N,P,Q,S,U],[C,D,E,F,G,H,J,M,N,P,Q,U],[C,D,E,F,G,H,J,M,N,P,R,S,U],[C,D,E,F,G,H,J,M,N,P,R,U],[C,D,E,F,G,H,J,M,N,P,S,U],[C,D,E,F,G,H,J,M,N,P,U],[C,D,E,F,G,H,J,M,P,Q,R,S],[C,D,E,F,G,H,J,M,P,Q,R,S,U],[C,D,E,F,G,H,J,M,P,Q,R,U],[C,D,E,F,G,H,J,M,P,Q,S,U],[C,D,E,F,G,H,J,M,P,Q,U],[C,D,E,F,G,H,J,M,P,R,S,U],[C,D,E,F,G,H,J,M,P,R,U],[C,D,E,F,G,H,J,M,P,S,U],[C,D,E,F,G,H,J,M,P,U],[C,D,E,F,G,J],[C,D,E,F,G,J,M],[C,D,E,F,G,J,M,N,P,Q,R,S,U],[C,D,E,F,G,J,M,N,P,Q,R,U],[C,D,E,F,G,J,M,N,P,Q,S,U],[C,D,E,F,G,J,M,N,P,Q,U],[C,D,E,F,G,J,M,N,P,R,S,U],[C,D,E,F,G,J,M,N,P,R,U],[C,D,E,F,G,J,M,N,P,S,U],[C,D,E,F,G,J,M,N,P,U],[C,D,E,F,G,J,M,P],[C,D,E,F,G,J,M,P,Q],[C,D,E,F,G,J,M,P,Q,R],[C,D,E,F,G,J,M,P,Q,R,S],[C,D,E,F,G,J,M,P,Q,R,S,U],[C,D,E,F,G,J,M,P,Q,R,U],[C,D,E,F,G,J,M,P,Q,S],[C,D,E,F,G,J,M,P,Q,S,U],[C,D,E,F,G,J,M,P,Q,U],[C,D,E,F,G,J,M,P,R],[C,D,E,F,G,J,M,P,R,S],[C,D,E,F,G,J,M,P,R,S,U],[C,D,E,F,G,J,M,P,R,U],[C,D,E,F,G,J,M,P,S],[C,D,E,F,G,J,M,P,S,U],[C,D,E,F,G,J,M,P,U],[C,D,E,F,G,J,M,Q],[C,D,E,F,G,J,M,Q,R],[C,D,E,F,G,J,M,R],[C,D,E,F,G,J,Q],[C,D,E,F,G,J,Q,R],[C,D,E,F,G,J,R],[C,D,E,F,H,J,M,N,P,Q,R,S,U],[C,D,E,F,H,J,M,N,P,Q,R,U],[C,D,E,F,H,J,M,N,P,Q,S,U],[C,D,E,F,H,J,M,N,P,Q,U],[C,D,E,F,H,J,M,N,P,R,S,U],[C,D,E,F,H,J,M,N,P,R,U],[C,D,E,F,H,J,M,N,P,S,U],[C,D,E,F,H,J,M,N,P,U],[C,D,E,F,H,J,M,P,Q,R,S,U],[C,D,E,F,H,J,M,P,Q,R,U],[C,D,E,F,H,J,M,P,Q,S],[C,D,E,F,H,J,M,P,Q,S,U],[C,D,E,F,H,J,M,P,Q,U],[C,D,E,F,H,J,M,P,R,S,U],[C,D,E,F,H,J,M,P,R,U],[C,D,E,F,H,J,M,P,S,U],[C,D,E,F,H,J,M,P,U],[C,D,E,F,J],[C,D,E,F,J,M],[C,D,E,F,J,M,N,P,Q,R,S,U],[C,D,E,F,J,M,N,P,Q,R,U],[C,D,E,F,J,M,N,P,Q,S,U],[C,D,E,F,J,M,N,P,Q,U],[C,D,E,F,J,M,N,P,R,S,U],[C,D,E,F,J,M,N,P,R,U],[C,D,E,F,J,M,N,P,S,U],[C,D,E,F,J,M,N,P,U],[C,D,E,F,J,M,P],[C,D,E,F,J,M,P,Q],[C,D,E,F,J,M,P,Q,R],[C,D,E,F,J,M,P,Q,R,S],[C,D,E,F,J,M,P,Q,R,S,U],[C,D,E,F,J,M,P,Q,R,U],[C,D,E,F,J,M,P,Q,S],[C,D,E,F,J,M,P,Q,S,U],[C,D,E,F,J,M,P,Q,U],[C,D,E,F,J,M,P,R],[C,D,E,F,J,M,P,R,S],[C,D,E,F,J,M,P,R,S,U],[C,D,E,F,J,M,P,R,U],[C,D,E,F,J,M,P,S],[C,D,E,F,J,M,P,S,U],[C,D,E,F,J,M,P,U],[C,D,E,F,J,M,Q],[C,D,E,F,J,M,Q,R],[C,D,E,F,J,M,R],[C,D,E,F,J,Q],[C,D,E,F,J,Q,R],[C,D,E,F,J,R],[C,D,E,G,H,J,M,N,P,Q,R,S,U],[C,D,E,G,H,J,M,N,P,Q,R,U],[C,D,E,G,H,J,M,N,P,Q,S,U],[C,D,E,G,H,J,M,N,P,Q,U],[C,D,E,G,H,J,M,N,P,R,S,U],[C,D,E,G,H,J,M,N,P,R,U],[C,D,E,G,H,J,M,N,P,S,U],[C,D,E,G,H,J,M,N,P,U],[C,D,E,G,H,J,M,P,Q,R,S,U],[C,D,E,G,H,J,M,P,Q,R,U],[C,D,E,G,H,J,M,P,Q,S,U],[C,D,E,G,H,J,M,P,Q,U],[C,D,E,G,H,J,M,P,R,S],[C,D,E,G,H,J,M,P,R,S,U],[C,D,E,G,H,J,M,P,R,U],[C,D,E,G,H,J,M,P,S,U],[C,D,E,G,H,J,M,P,U],[C,D,E,G,J],[C,D,E,G,J,M],[C,D,E,G,J,M,N,P,Q,R,S,U],[C,D,E,G,J,M,N,P,Q,R,U],[C,D,E,G,J,M,N,P,Q,S,U],[C,D,E,G,J,M,N,P,Q,U],[C,D,E,G,J,M,N,P,R,S,U],[C,D,E,G,J,M,N,P,R,U],[C,D,E,G,J,M,N,P,S,U],[C,D,E,G,J,M,N,P,U],[C,D,E,G,J,M,P],[C,D,E,G,J,M,P,Q],[C,D,E,G,J,M,P,Q,R],[C,D,E,G,J,M,P,Q,R,S],[C,D,E,G,J,M,P,Q,R,S,U],[C,D,E,G,J,M,P,Q,R,U],[C,D,E,G,J,M,P,Q,S],[C,D,E,G,J,M,P,Q,S,U],[C,D,E,G,J,M,P,Q,U],[C,D,E,G,J,M,P,R],[C,D,E,G,J,M,P,R,S],[C,D,E,G,J,M,P,R,S,U],[C,D,E,G,J,M,P,R,U],[C,D,E,G,J,M,P,S],[C,D,E,G,J,M,P,S,U],[C,D,E,G,J,M,P,U],[C,D,E,G,J,M,Q],[C,D,E,G,J,M,Q,R],[C,D,E,G,J,M,R],[C,D,E,G,J,Q],[C,D,E,G,J,Q,R],[C,D,E,G,J,R],[C,D,E,H,J,M,N,P,Q,R,S,U],[C,D,E,H,J,M,N,P,Q,R,U],[C,D,E,H,J,M,N,P,Q,S,U],[C,D,E,H,J,M,N,P,Q,U],[C,D,E,H,J,M,N,P,R,S,U],[C,D,E,H,J,M,N,P,R,U],[C,D,E,H,J,M,N,P,S,U],[C,D,E,H,J,M,N,P,U],[C,D,E,H,J,M,P,Q,R,S,U],[C,D,E,H,J,M,P,Q,R,U],[C,D,E,H,J,M,P,Q,S,U],[C,D,E,H,J,M,P,Q,U],[C,D,E,H,J,M,P,R,S,U],[C,D,E,H,J,M,P,R,U],[C,D,E,H,J,M,P,S],[C,D,E,H,J,M,P,S,U],[C,D,E,H,J,M,P,U],[C,D,E,J],[C,D,E,J,M],[C,D,E,J,M,N,P,Q,R,S,U],[C,D,E,J,M,N,P,Q,R,U],[C,D,E,J,M,N,P,Q,S,U],[C,D,E,J,M,N,P,Q,U],[C,D,E,J,M,N,P,R,S,U],[C,D,E,J,M,N,P,R,U],[C,D,E,J,M,N,P,S,U],[C,D,E,J,M,N,P,U],[C,D,E,J,M,P],[C,D,E,J,M,P,Q],[C,D,E,J,M,P,Q,R],[C,D,E,J,M,P,Q,R,S],[C,D,E,J,M,P,Q,R,S,U],[C,D,E,J,M,P,Q,R,U],[C,D,E,J,M,P,Q,S],[C,D,E,J,M,P,Q,S,U],[C,D,E,J,M,P,Q,U],[C,D,E,J,M,P,R],[C,D,E,J,M,P,R,S],[C,D,E,J,M,P,R,S,U],[C,D,E,J,M,P,R,U],[C,D,E,J,M,P,S],[C,D,E,J,M,P,S,U],[C,D,E,J,M,P,U],[C,D,E,J,M,Q],[C,D,E,J,M,Q,R],[C,D,E,J,M,R],[C,D,E,J,Q],[C,D,E,J,Q,R],[C,D,E,J,R],[C,D,F,G,H,J,M,N,P,Q,R,S,U],[C,D,F,G,H,J,M,N,P,Q,R,U],[C,D,F,G,H,J,M,N,P,Q,S,U],[C,D,F,G,H,J,M,N,P,Q,U],[C,D,F,G,H,J,M,N,P,R,S,U],[C,D,F,G,H,J,M,N,P,R,U],[C,D,F,G,H,J,M,N,P,S,U],[C,D,F,G,H,J,M,N,P,U],[C,D,F,G,H,J,M,P,Q,R,S],[C,D,F,G,H,J,M,P,Q,R,S,U],[C,D,F,G,H,J,M,P,Q,R,U],[C,D,F,G,H,J,M,P,Q,S,U],[C,D,F,G,H,J,M,P,Q,U],[C,D,F,G,H,J,M,P,R,S,U],[C,D,F,G,H,J,M,P,R,U],[C,D,F,G,H,J,M,P,S,U],[C,D,F,G,H,J,M,P,U],[C,D,F,G,J],[C,D,F,G,J,M],[C,D,F,G,J,M,N,P,Q,R,S,U],[C,D,F,G,J,M,N,P,Q,R,U],[C,D,F,G,J,M,N,P,Q,S,U],[C,D,F,G,J,M,N,P,Q,U],[C,D,F,G,J,M,N,P,R,S,U],[C,D,F,G,J,M,N,P,R,U],[C,D,F,G,J,M,N,P,S,U],[C,D,F,G,J,M,N,P,U],[C,D,F,G,J,M,P],[C,D,F,G,J,M,P,Q],[C,D,F,G,J,M,P,Q,R],[C,D,F,G,J,M,P,Q,R,S],[C,D,F,G,J,M,P,Q,R,S,U],[C,D,F,G,J,M,P,Q,R,U],[C,D,F,G,J,M,P,Q,S],[C,D,F,G,J,M,P,Q,S,U],[C,D,F,G,J,M,P,Q,U],[C,D,F,G,J,M,P,R],[C,D,F,G,J,M,P,R,S],[C,D,F,G,J,M,P,R,S,U],[C,D,F,G,J,M,P,R,U],[C,D,F,G,J,M,P,S],[C,D,F,G,J,M,P,S,U],[C,D,F,G,J,M,P,U],[C,D,F,G,J,M,Q],[C,D,F,G,J,M,Q,R],[C,D,F,G,J,M,R],[C,D,F,G,J,Q],[C,D,F,G,J,Q,R],[C,D,F,G,J,R],[C,D,F,H,J,M,N,P,Q,R,S,U],[C,D,F,H,J,M,N,P,Q,R,U],[C,D,F,H,J,M,N,P,Q,S,U],[C,D,F,H,J,M,N,P,Q,U],[C,D,F,H,J,M,N,P,R,S,U],[C,D,F,H,J,M,N,P,R,U],[C,D,F,H,J,M,N,P,S,U],[C,D,F,H,J,M,N,P,U],[C,D,F,H,J,M,P,Q,R,S,U],[C,D,F,H,J,M,P,Q,R,U],[C,D,F,H,J,M,P,Q,S],[C,D,F,H,J,M,P,Q,S,U],[C,D,F,H,J,M,P,Q,U],[C,D,F,H,J,M,P,R,S,U],[C,D,F,H,J,M,P,R,U],[C,D,F,H,J,M,P,S,U],[C,D,F,H,J,M,P,U],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N,P,Q,R,S,U],[C,D,F,J,M,N,P,Q,R,U],[C,D,F,J,M,N,P,Q,S,U],[C,D,F,J,M,N,P,Q,U],[C,D,F,J,M,N,P,R,S,U],[C,D,F,J,M,N,P,R,U],[C,D,F,J,M,N,P,S,U],[C,D,F,J,M,N,P,U],[C,D,F,J,M,P],[C,D,F,J,M,P,Q],[C,D,F,J,M,P,Q,R],[C,D,F,J,M,P,Q,R,S],[C,D,F,J,M,P,Q,R,S,U],[C,D,F,J,M,P,Q,R,U],[C,D,F,J,M,P,Q,S],[C,D,F,J,M,P,Q,S,U],[C,D,F,J,M,P,Q,U],[C,D,F,J,M,P,R],[C,D,F,J,M,P,R,S],[C,D,F,J,M,P,R,S,U],[C,D,F,J,M,P,R,U],[C,D,F,J,M,P,S],[C,D,F,J,M,P,S,U],[C,D,F,J,M,P,U],[C,D,F,J,M,Q],[C,D,F,J,M,Q,R],[C,D,F,J,M,R],[C,D,F,J,Q],[C,D,F,J,Q,R],[C,D,F,J,R],[C,D,G,H,J,M,N,P,Q,R,S,U],[C,D,G,H,J,M,N,P,Q,R,U],[C,D,G,H,J,M,N,P,Q,S,U],[C,D,G,H,J,M,N,P,Q,U],[C,D,G,H,J,M,N,P,R,S,U],[C,D,G,H,J,M,N,P,R,U],[C,D,G,H,J,M,N,P,S,U],[C,D,G,H,J,M,N,P,U],[C,D,G,H,J,M,P,Q,R,S,U],[C,D,G,H,J,M,P,Q,R,U],[C,D,G,H,J,M,P,Q,S,U],[C,D,G,H,J,M,P,Q,U],[C,D,G,H,J,M,P,R,S],[C,D,G,H,J,M,P,R,S,U],[C,D,G,H,J,M,P,R,U],[C,D,G,H,J,M,P,S,U],[C,D,G,H,J,M,P,U],[C,D,G,J],[C,D,G,J,M],[C,D,G,J,M,N,P,Q,R,S,U],[C,D,G,J,M,N,P,Q,R,U],[C,D,G,J,M,N,P,Q,S,U],[C,D,G,J,M,N,P,Q,U],[C,D,G,J,M,N,P,R,S,U],[C,D,G,J,M,N,P,R,U],[C,D,G,J,M,N,P,S,U],[C,D,G,J,M,N,P,U],[C,D,G,J,M,P],[C,D,G,J,M,P,Q],[C,D,G,J,M,P,Q,R],[C,D,G,J,M,P,Q,R,S],[C,D,G,J,M,P,Q,R,S,U],[C,D,G,J,M,P,Q,R,U],[C,D,G,J,M,P,Q,S],[C,D,G,J,M,P,Q,S,U],[C,D,G,J,M,P,Q,U],[C,D,G,J,M,P,R],[C,D,G,J,M,P,R,S],[C,D,G,J,M,P,R,S,U],[C,D,G,J,M,P,R,U],[C,D,G,J,M,P,S],[C,D,G,J,M,P,S,U],[C,D,G,J,M,P,U],[C,D,G,J,M,Q],[C,D,G,J,M,Q,R],[C,D,G,J,M,R],[C,D,G,J,Q],[C,D,G,J,Q,R],[C,D,G,J,R],[C,D,H,J,M,N,P,Q,R,S,U],[C,D,H,J,M,N,P,Q,R,U],[C,D,H,J,M,N,P,Q,S,U],[C,D,H,J,M,N,P,Q,U],[C,D,H,J,M,N,P,R,S,U],[C,D,H,J,M,N,P,R,U],[C,D,H,J,M,N,P,S,U],[C,D,H,J,M,N,P,U],[C,D,H,J,M,P,Q,R,S,U],[C,D,H,J,M,P,Q,R,U],[C,D,H,J,M,P,Q,S,U],[C,D,H,J,M,P,Q,U],[C,D,H,J,M,P,R,S,U],[C,D,H,J,M,P,R,U],[C,D,H,J,M,P,S],[C,D,H,J,M,P,S,U],[C,D,H,J,M,P,U],[C,D,J],[C,D,J,M],[C,D,J,M,N,P,Q,R,S,U],[C,D,J,M,N,P,Q,R,U],[C,D,J,M,N,P,Q,S,U],[C,D,J,M,N,P,Q,U],[C,D,J,M,N,P,R,S,U],[C,D,J,M,N,P,R,U],[C,D,J,M,N,P,S,U],[C,D,J,M,N,P,U],[C,D,J,M,P],[C,D,J,M,P,Q],[C,D,J,M,P,Q,R],[C,D,J,M,P,Q,R,S],[C,D,J,M,P,Q,R,S,U],[C,D,J,M,P,Q,R,U],[C,D,J,M,P,Q,S],[C,D,J,M,P,Q,S,U],[C,D,J,M,P,Q,U],[C,D,J,M,P,R],[C,D,J,M,P,R,S],[C,D,J,M,P,R,S,U],[C,D,J,M,P,R,U],[C,D,J,M,P,S],[C,D,J,M,P,S,U],[C,D,J,M,P,U],[C,D,J,M,Q],[C,D,J,M,Q,R],[C,D,J,M,R],[C,D,J,Q],[C,D,J,Q,R],[C,D,J,R],[C,E,F,G,H,J,M,N,P,Q,R,S,U],[C,E,F,G,H,J,M,N,P,Q,R,U],[C,E,F,G,H,J,M,N,P,Q,S,U],[C,E,F,G,H,J,M,N,P,Q,U],[C,E,F,G,H,J,M,N,P,R,S,U],[C,E,F,G,H,J,M,N,P,R,U],[C,E,F,G,H,J,M,N,P,S,U],[C,E,F,G,H,J,M,N,P,U],[C,E,F,G,H,J,M,P,Q,R,S],[C,E,F,G,H,J,M,P,Q,R,S,U],[C,E,F,G,H,J,M,P,Q,R,U],[C,E,F,G,H,J,M,P,Q,S,U],[C,E,F,G,H,J,M,P,Q,U],[C,E,F,G,H,J,M,P,R,S,U],[C,E,F,G,H,J,M,P,R,U],[C,E,F,G,H,J,M,P,S,U],[C,E,F,G,H,J,M,P,U],[C,E,F,G,J],[C,E,F,G,J,M],[C,E,F,G,J,M,N,P,Q,R,S,U],[C,E,F,G,J,M,N,P,Q,R,U],[C,E,F,G,J,M,N,P,Q,S,U],[C,E,F,G,J,M,N,P,Q,U],[C,E,F,G,J,M,N,P,R,S,U],[C,E,F,G,J,M,N,P,R,U],[C,E,F,G,J,M,N,P,S,U],[C,E,F,G,J,M,N,P,U],[C,E,F,G,J,M,P],[C,E,F,G,J,M,P,Q],[C,E,F,G,J,M,P,Q,R],[C,E,F,G,J,M,P,Q,R,S],[C,E,F,G,J,M,P,Q,R,S,U],[C,E,F,G,J,M,P,Q,R,U],[C,E,F,G,J,M,P,Q,S],[C,E,F,G,J,M,P,Q,S,U],[C,E,F,G,J,M,P,Q,U],[C,E,F,G,J,M,P,R],[C,E,F,G,J,M,P,R,S],[C,E,F,G,J,M,P,R,S,U],[C,E,F,G,J,M,P,R,U],[C,E,F,G,J,M,P,S],[C,E,F,G,J,M,P,S,U],[C,E,F,G,J,M,P,U],[C,E,F,G,J,M,Q],[C,E,F,G,J,M,Q,R],[C,E,F,G,J,M,R],[C,E,F,G,J,Q],[C,E,F,G,J,Q,R],[C,E,F,G,J,R],[C,E,F,H,J,M,N,P,Q,R,S,U],[C,E,F,H,J,M,N,P,Q,R,U],[C,E,F,H,J,M,N,P,Q,S,U],[C,E,F,H,J,M,N,P,Q,U],[C,E,F,H,J,M,N,P,R,S,U],[C,E,F,H,J,M,N,P,R,U],[C,E,F,H,J,M,N,P,S,U],[C,E,F,H,J,M,N,P,U],[C,E,F,H,J,M,P,Q,R,S,U],[C,E,F,H,J,M,P,Q,R,U],[C,E,F,H,J,M,P,Q,S],[C,E,F,H,J,M,P,Q,S,U],[C,E,F,H,J,M,P,Q,U],[C,E,F,H,J,M,P,R,S,U],[C,E,F,H,J,M,P,R,U],[C,E,F,H,J,M,P,S,U],[C,E,F,H,J,M,P,U],[C,E,F,J],[C,E,F,J,M],[C,E,F,J,M,N,P,Q,R,S,U],[C,E,F,J,M,N,P,Q,R,U],[C,E,F,J,M,N,P,Q,S,U],[C,E,F,J,M,N,P,Q,U],[C,E,F,J,M,N,P,R,S,U],[C,E,F,J,M,N,P,R,U],[C,E,F,J,M,N,P,S,U],[C,E,F,J,M,N,P,U],[C,E,F,J,M,P],[C,E,F,J,M,P,Q],[C,E,F,J,M,P,Q,R],[C,E,F,J,M,P,Q,R,S],[C,E,F,J,M,P,Q,R,S,U],[C,E,F,J,M,P,Q,R,U],[C,E,F,J,M,P,Q,S],[C,E,F,J,M,P,Q,S,U],[C,E,F,J,M,P,Q,U],[C,E,F,J,M,P,R],[C,E,F,J,M,P,R,S],[C,E,F,J,M,P,R,S,U],[C,E,F,J,M,P,R,U],[C,E,F,J,M,P,S],[C,E,F,J,M,P,S,U],[C,E,F,J,M,P,U],[C,E,F,J,M,Q],[C,E,F,J,M,Q,R],[C,E,F,J,M,R],[C,E,F,J,Q],[C,E,F,J,Q,R],[C,E,F,J,R],[C,E,G,H,J,M,N,P,Q,R,S,U],[C,E,G,H,J,M,N,P,Q,R,U],[C,E,G,H,J,M,N,P,Q,S,U],[C,E,G,H,J,M,N,P,Q,U],[C,E,G,H,J,M,N,P,R,S,U],[C,E,G,H,J,M,N,P,R,U],[C,E,G,H,J,M,N,P,S,U],[C,E,G,H,J,M,N,P,U],[C,E,G,H,J,M,P,Q,R,S,U],[C,E,G,H,J,M,P,Q,R,U],[C,E,G,H,J,M,P,Q,S,U],[C,E,G,H,J,M,P,Q,U],[C,E,G,H,J,M,P,R,S],[C,E,G,H,J,M,P,R,S,U],[C,E,G,H,J,M,P,R,U],[C,E,G,H,J,M,P,S,U],[C,E,G,H,J,M,P,U],[C,E,G,J],[C,E,G,J,M],[C,E,G,J,M,N,P,Q,R,S,U],[C,E,G,J,M,N,P,Q,R,U],[C,E,G,J,M,N,P,Q,S,U],[C,E,G,J,M,N,P,Q,U],[C,E,G,J,M,N,P,R,S,U],[C,E,G,J,M,N,P,R,U],[C,E,G,J,M,N,P,S,U],[C,E,G,J,M,N,P,U],[C,E,G,J,M,P],[C,E,G,J,M,P,Q],[C,E,G,J,M,P,Q,R],[C,E,G,J,M,P,Q,R,S],[C,E,G,J,M,P,Q,R,S,U],[C,E,G,J,M,P,Q,R,U],[C,E,G,J,M,P,Q,S],[C,E,G,J,M,P,Q,S,U],[C,E,G,J,M,P,Q,U],[C,E,G,J,M,P,R],[C,E,G,J,M,P,R,S],[C,E,G,J,M,P,R,S,U],[C,E,G,J,M,P,R,U],[C,E,G,J,M,P,S],[C,E,G,J,M,P,S,U],[C,E,G,J,M,P,U],[C,E,G,J,M,Q],[C,E,G,J,M,Q,R],[C,E,G,J,M,R],[C,E,G,J,Q],[C,E,G,J,Q,R],[C,E,G,J,R],[C,E,H,J,M,N,P,Q,R,S,U],[C,E,H,J,M,N,P,Q,R,U],[C,E,H,J,M,N,P,Q,S,U],[C,E,H,J,M,N,P,Q,U],[C,E,H,J,M,N,P,R,S,U],[C,E,H,J,M,N,P,R,U],[C,E,H,J,M,N,P,S,U],[C,E,H,J,M,N,P,U],[C,E,H,J,M,P,Q,R,S,U],[C,E,H,J,M,P,Q,R,U],[C,E,H,J,M,P,Q,S,U],[C,E,H,J,M,P,Q,U],[C,E,H,J,M,P,R,S,U],[C,E,H,J,M,P,R,U],[C,E,H,J,M,P,S],[C,E,H,J,M,P,S,U],[C,E,H,J,M,P,U],[C,E,J],[C,E,J,M],[C,E,J,M,N,P,Q,R,S,U],[C,E,J,M,N,P,Q,R,U],[C,E,J,M,N,P,Q,S,U],[C,E,J,M,N,P,Q,U],[C,E,J,M,N,P,R,S,U],[C,E,J,M,N,P,R,U],[C,E,J,M,N,P,S,U],[C,E,J,M,N,P,U],[C,E,J,M,P],[C,E,J,M,P,Q],[C,E,J,M,P,Q,R],[C,E,J,M,P,Q,R,S],[C,E,J,M,P,Q,R,S,U],[C,E,J,M,P,Q,R,U],[C,E,J,M,P,Q,S],[C,E,J,M,P,Q,S,U],[C,E,J,M,P,Q,U],[C,E,J,M,P,R],[C,E,J,M,P,R,S],[C,E,J,M,P,R,S,U],[C,E,J,M,P,R,U],[C,E,J,M,P,S],[C,E,J,M,P,S,U],[C,E,J,M,P,U],[C,E,J,M,Q],[C,E,J,M,Q,R],[C,E,J,M,R],[C,E,J,Q],[C,E,J,Q,R],[C,E,J,R],[C,F,G,H,J,M,N,P,Q,R,S,U],[C,F,G,H,J,M,N,P,Q,R,U],[C,F,G,H,J,M,N,P,Q,S,U],[C,F,G,H,J,M,N,P,Q,U],[C,F,G,H,J,M,N,P,R,S,U],[C,F,G,H,J,M,N,P,R,U],[C,F,G,H,J,M,N,P,S,U],[C,F,G,H,J,M,N,P,U],[C,F,G,H,J,M,P,Q,R,S],[C,F,G,H,J,M,P,Q,R,S,U],[C,F,G,H,J,M,P,Q,R,U],[C,F,G,H,J,M,P,Q,S,U],[C,F,G,H,J,M,P,Q,U],[C,F,G,H,J,M,P,R,S,U],[C,F,G,H,J,M,P,R,U],[C,F,G,H,J,M,P,S,U],[C,F,G,H,J,M,P,U],[C,F,G,J],[C,F,G,J,M],[C,F,G,J,M,N,P,Q,R,S,U],[C,F,G,J,M,N,P,Q,R,U],[C,F,G,J,M,N,P,Q,S,U],[C,F,G,J,M,N,P,Q,U],[C,F,G,J,M,N,P,R,S,U],[C,F,G,J,M,N,P,R,U],[C,F,G,J,M,N,P,S,U],[C,F,G,J,M,N,P,U],[C,F,G,J,M,P],[C,F,G,J,M,P,Q],[C,F,G,J,M,P,Q,R],[C,F,G,J,M,P,Q,R,S],[C,F,G,J,M,P,Q,R,S,U],[C,F,G,J,M,P,Q,R,U],[C,F,G,J,M,P,Q,S],[C,F,G,J,M,P,Q,S,U],[C,F,G,J,M,P,Q,U],[C,F,G,J,M,P,R],[C,F,G,J,M,P,R,S],[C,F,G,J,M,P,R,S,U],[C,F,G,J,M,P,R,U],[C,F,G,J,M,P,S],[C,F,G,J,M,P,S,U],[C,F,G,J,M,P,U],[C,F,G,J,M,Q],[C,F,G,J,M,Q,R],[C,F,G,J,M,R],[C,F,G,J,Q],[C,F,G,J,Q,R],[C,F,G,J,R],[C,F,H,J,M,N,P,Q,R,S,U],[C,F,H,J,M,N,P,Q,R,U],[C,F,H,J,M,N,P,Q,S,U],[C,F,H,J,M,N,P,Q,U],[C,F,H,J,M,N,P,R,S,U],[C,F,H,J,M,N,P,R,U],[C,F,H,J,M,N,P,S,U],[C,F,H,J,M,N,P,U],[C,F,H,J,M,P,Q,R,S,U],[C,F,H,J,M,P,Q,R,U],[C,F,H,J,M,P,Q,S],[C,F,H,J,M,P,Q,S,U],[C,F,H,J,M,P,Q,U],[C,F,H,J,M,P,R,S,U],[C,F,H,J,M,P,R,U],[C,F,H,J,M,P,S,U],[C,F,H,J,M,P,U],[C,F,J],[C,F,J,M],[C,F,J,M,N,P,Q,R,S,U],[C,F,J,M,N,P,Q,R,U],[C,F,J,M,N,P,Q,S,U],[C,F,J,M,N,P,Q,U],[C,F,J,M,N,P,R,S,U],[C,F,J,M,N,P,R,U],[C,F,J,M,N,P,S,U],[C,F,J,M,N,P,U],[C,F,J,M,P],[C,F,J,M,P,Q],[C,F,J,M,P,Q,R],[C,F,J,M,P,Q,R,S],[C,F,J,M,P,Q,R,S,U],[C,F,J,M,P,Q,R,U],[C,F,J,M,P,Q,S],[C,F,J,M,P,Q,S,U],[C,F,J,M,P,Q,U],[C,F,J,M,P,R],[C,F,J,M,P,R,S],[C,F,J,M,P,R,S,U],[C,F,J,M,P,R,U],[C,F,J,M,P,S],[C,F,J,M,P,S,U],[C,F,J,M,P,U],[C,F,J,M,Q],[C,F,J,M,Q,R],[C,F,J,M,R],[C,F,J,Q],[C,F,J,Q,R],[C,F,J,R],[C,G,H,J,M,N,P,Q,R,S,U],[C,G,H,J,M,N,P,Q,R,U],[C,G,H,J,M,N,P,Q,S,U],[C,G,H,J,M,N,P,Q,U],[C,G,H,J,M,N,P,R,S,U],[C,G,H,J,M,N,P,R,U],[C,G,H,J,M,N,P,S,U],[C,G,H,J,M,N,P,U],[C,G,H,J,M,P,Q,R,S,U],[C,G,H,J,M,P,Q,R,U],[C,G,H,J,M,P,Q,S,U],[C,G,H,J,M,P,Q,U],[C,G,H,J,M,P,R,S],[C,G,H,J,M,P,R,S,U],[C,G,H,J,M,P,R,U],[C,G,H,J,M,P,S,U],[C,G,H,J,M,P,U],[C,G,J],[C,G,J,M],[C,G,J,M,N,P,Q,R,S,U],[C,G,J,M,N,P,Q,R,U],[C,G,J,M,N,P,Q,S,U],[C,G,J,M,N,P,Q,U],[C,G,J,M,N,P,R,S,U],[C,G,J,M,N,P,R,U],[C,G,J,M,N,P,S,U],[C,G,J,M,N,P,U],[C,G,J,M,P],[C,G,J,M,P,Q],[C,G,J,M,P,Q,R],[C,G,J,M,P,Q,R,S],[C,G,J,M,P,Q,R,S,U],[C,G,J,M,P,Q,R,U],[C,G,J,M,P,Q,S],[C,G,J,M,P,Q,S,U],[C,G,J,M,P,Q,U],[C,G,J,M,P,R],[C,G,J,M,P,R,S],[C,G,J,M,P,R,S,U],[C,G,J,M,P,R,U],[C,G,J,M,P,S],[C,G,J,M,P,S,U],[C,G,J,M,P,U],[C,G,J,M,Q],[C,G,J,M,Q,R],[C,G,J,M,R],[C,G,J,Q],[C,G,J,Q,R],[C,G,J,R],[C,H,J,M,N,P,Q,R,S,U],[C,H,J,M,N,P,Q,R,U],[C,H,J,M,N,P,Q,S,U],[C,H,J,M,N,P,Q,U],[C,H,J,M,N,P,R,S,U],[C,H,J,M,N,P,R,U],[C,H,J,M,N,P,S,U],[C,H,J,M,N,P,U],[C,H,J,M,P,Q,R,S,U],[C,H,J,M,P,Q,R,U],[C,H,J,M,P,Q,S,U],[C,H,J,M,P,Q,U],[C,H,J,M,P,R,S,U],[C,H,J,M,P,R,U],[C,H,J,M,P,S],[C,H,J,M,P,S,U],[C,H,J,M,P,U],[C,J],[C,J,M],[C,J,M,N,P,Q,R,S,U],[C,J,M,N,P,Q,R,U],[C,J,M,N,P,Q,S,U],[C,J,M,N,P,Q,U],[C,J,M,N,P,R,S,U],[C,J,M,N,P,R,U],[C,J,M,N,P,S,U],[C,J,M,N,P,U],[C,J,M,P],[C,J,M,P,Q],[C,J,M,P,Q,R],[C,J,M,P,Q,R,S],[C,J,M,P,Q,R,S,U],[C,J,M,P,Q,R,U],[C,J,M,P,Q,S],[C,J,M,P,Q,S,U],[C,J,M,P,Q,U],[C,J,M,P,R],[C,J,M,P,R,S],[C,J,M,P,R,S,U],[C,J,M,P,R,U],[C,J,M,P,S],[C,J,M,P,S,U],[C,J,M,P,U],[C,J,M,Q],[C,J,M,Q,R],[C,J,M,R],[C,J,Q],[C,J,Q,R],[C,J,R],[D],[D,E,F,G,H,J,M,N,P,Q,R,S,U],[D,E,F,G,H,J,M,N,P,Q,R,U],[D,E,F,G,H,J,M,N,P,Q,S,U],[D,E,F,G,H,J,M,N,P,Q,U],[D,E,F,G,H,J,M,N,P,R,S,U],[D,E,F,G,H,J,M,N,P,R,U],[D,E,F,G,H,J,M,N,P,S,U],[D,E,F,G,H,J,M,N,P,U],[D,E,F,G,H,J,M,P,Q,R,S],[D,E,F,G,H,J,M,P,Q,R,S,U],[D,E,F,G,H,J,M,P,Q,R,U],[D,E,F,G,H,J,M,P,Q,S,U],[D,E,F,G,H,J,M,P,Q,U],[D,E,F,G,H,J,M,P,R,S,U],[D,E,F,G,H,J,M,P,R,U],[D,E,F,G,H,J,M,P,S,U],[D,E,F,G,H,J,M,P,U],[D,E,F,G,J],[D,E,F,G,J,M],[D,E,F,G,J,M,N,P,Q,R,S,U],[D,E,F,G,J,M,N,P,Q,R,U],[D,E,F,G,J,M,N,P,Q,S,U],[D,E,F,G,J,M,N,P,Q,U],[D,E,F,G,J,M,N,P,R,S,U],[D,E,F,G,J,M,N,P,R,U],[D,E,F,G,J,M,N,P,S,U],[D,E,F,G,J,M,N,P,U],[D,E,F,G,J,M,P],[D,E,F,G,J,M,P,Q],[D,E,F,G,J,M,P,Q,R],[D,E,F,G,J,M,P,Q,R,S],[D,E,F,G,J,M,P,Q,R,S,U],[D,E,F,G,J,M,P,Q,R,U],[D,E,F,G,J,M,P,Q,S],[D,E,F,G,J,M,P,Q,S,U],[D,E,F,G,J,M,P,Q,U],[D,E,F,G,J,M,P,R],[D,E,F,G,J,M,P,R,S],[D,E,F,G,J,M,P,R,S,U],[D,E,F,G,J,M,P,R,U],[D,E,F,G,J,M,P,S],[D,E,F,G,J,M,P,S,U],[D,E,F,G,J,M,P,U],[D,E,F,G,J,M,Q],[D,E,F,G,J,M,Q,R],[D,E,F,G,J,M,R],[D,E,F,G,J,Q],[D,E,F,G,J,Q,R],[D,E,F,G,J,R],[D,E,F,H,J,M,N,P,Q,R,S,U],[D,E,F,H,J,M,N,P,Q,R,U],[D,E,F,H,J,M,N,P,Q,S,U],[D,E,F,H,J,M,N,P,Q,U],[D,E,F,H,J,M,N,P,R,S,U],[D,E,F,H,J,M,N,P,R,U],[D,E,F,H,J,M,N,P,S,U],[D,E,F,H,J,M,N,P,U],[D,E,F,H,J,M,P,Q,R,S,U],[D,E,F,H,J,M,P,Q,R,U],[D,E,F,H,J,M,P,Q,S],[D,E,F,H,J,M,P,Q,S,U],[D,E,F,H,J,M,P,Q,U],[D,E,F,H,J,M,P,R,S,U],[D,E,F,H,J,M,P,R,U],[D,E,F,H,J,M,P,S,U],[D,E,F,H,J,M,P,U],[D,E,F,J],[D,E,F,J,M],[D,E,F,J,M,N,P,Q,R,S,U],[D,E,F,J,M,N,P,Q,R,U],[D,E,F,J,M,N,P,Q,S,U],[D,E,F,J,M,N,P,Q,U],[D,E,F,J,M,N,P,R,S,U],[D,E,F,J,M,N,P,R,U],[D,E,F,J,M,N,P,S,U],[D,E,F,J,M,N,P,U],[D,E,F,J,M,P],[D,E,F,J,M,P,Q],[D,E,F,J,M,P,Q,R],[D,E,F,J,M,P,Q,R,S],[D,E,F,J,M,P,Q,R,S,U],[D,E,F,J,M,P,Q,R,U],[D,E,F,J,M,P,Q,S],[D,E,F,J,M,P,Q,S,U],[D,E,F,J,M,P,Q,U],[D,E,F,J,M,P,R],[D,E,F,J,M,P,R,S],[D,E,F,J,M,P,R,S,U],[D,E,F,J,M,P,R,U],[D,E,F,J,M,P,S],[D,E,F,J,M,P,S,U],[D,E,F,J,M,P,U],[D,E,F,J,M,Q],[D,E,F,J,M,Q,R],[D,E,F,J,M,R],[D,E,F,J,Q],[D,E,F,J,Q,R],[D,E,F,J,R],[D,E,G,H,J,M,N,P,Q,R,S,U],[D,E,G,H,J,M,N,P,Q,R,U],[D,E,G,H,J,M,N,P,Q,S,U],[D,E,G,H,J,M,N,P,Q,U],[D,E,G,H,J,M,N,P,R,S,U],[D,E,G,H,J,M,N,P,R,U],[D,E,G,H,J,M,N,P,S,U],[D,E,G,H,J,M,N,P,U],[D,E,G,H,J,M,P,Q,R,S,U],[D,E,G,H,J,M,P,Q,R,U],[D,E,G,H,J,M,P,Q,S,U],[D,E,G,H,J,M,P,Q,U],[D,E,G,H,J,M,P,R,S],[D,E,G,H,J,M,P,R,S,U],[D,E,G,H,J,M,P,R,U],[D,E,G,H,J,M,P,S,U],[D,E,G,H,J,M,P,U],[D,E,G,J],[D,E,G,J,M],[D,E,G,J,M,N,P,Q,R,S,U],[D,E,G,J,M,N,P,Q,R,U],[D,E,G,J,M,N,P,Q,S,U],[D,E,G,J,M,N,P,Q,U],[D,E,G,J,M,N,P,R,S,U],[D,E,G,J,M,N,P,R,U],[D,E,G,J,M,N,P,S,U],[D,E,G,J,M,N,P,U],[D,E,G,J,M,P],[D,E,G,J,M,P,Q],[D,E,G,J,M,P,Q,R],[D,E,G,J,M,P,Q,R,S],[D,E,G,J,M,P,Q,R,S,U],[D,E,G,J,M,P,Q,R,U],[D,E,G,J,M,P,Q,S],[D,E,G,J,M,P,Q,S,U],[D,E,G,J,M,P,Q,U],[D,E,G,J,M,P,R],[D,E,G,J,M,P,R,S],[D,E,G,J,M,P,R,S,U],[D,E,G,J,M,P,R,U],[D,E,G,J,M,P,S],[D,E,G,J,M,P,S,U],[D,E,G,J,M,P,U],[D,E,G,J,M,Q],[D,E,G,J,M,Q,R],[D,E,G,J,M,R],[D,E,G,J,Q],[D,E,G,J,Q,R],[D,E,G,J,R],[D,E,H,J,M,N,P,Q,R,S,U],[D,E,H,J,M,N,P,Q,R,U],[D,E,H,J,M,N,P,Q,S,U],[D,E,H,J,M,N,P,Q,U],[D,E,H,J,M,N,P,R,S,U],[D,E,H,J,M,N,P,R,U],[D,E,H,J,M,N,P,S,U],[D,E,H,J,M,N,P,U],[D,E,H,J,M,P,Q,R,S,U],[D,E,H,J,M,P,Q,R,U],[D,E,H,J,M,P,Q,S,U],[D,E,H,J,M,P,Q,U],[D,E,H,J,M,P,R,S,U],[D,E,H,J,M,P,R,U],[D,E,H,J,M,P,S],[D,E,H,J,M,P,S,U],[D,E,H,J,M,P,U],[D,E,J],[D,E,J,M],[D,E,J,M,N,P,Q,R,S,U],[D,E,J,M,N,P,Q,R,U],[D,E,J,M,N,P,Q,S,U],[D,E,J,M,N,P,Q,U],[D,E,J,M,N,P,R,S,U],[D,E,J,M,N,P,R,U],[D,E,J,M,N,P,S,U],[D,E,J,M,N,P,U],[D,E,J,M,P],[D,E,J,M,P,Q],[D,E,J,M,P,Q,R],[D,E,J,M,P,Q,R,S],[D,E,J,M,P,Q,R,S,U],[D,E,J,M,P,Q,R,U],[D,E,J,M,P,Q,S],[D,E,J,M,P,Q,S,U],[D,E,J,M,P,Q,U],[D,E,J,M,P,R],[D,E,J,M,P,R,S],[D,E,J,M,P,R,S,U],[D,E,J,M,P,R,U],[D,E,J,M,P,S],[D,E,J,M,P,S,U],[D,E,J,M,P,U],[D,E,J,M,Q],[D,E,J,M,Q,R],[D,E,J,M,R],[D,E,J,Q],[D,E,J,Q,R],[D,E,J,R],[D,F,G,H,J,M,N,P,Q,R,S,U],[D,F,G,H,J,M,N,P,Q,R,U],[D,F,G,H,J,M,N,P,Q,S,U],[D,F,G,H,J,M,N,P,Q,U],[D,F,G,H,J,M,N,P,R,S,U],[D,F,G,H,J,M,N,P,R,U],[D,F,G,H,J,M,N,P,S,U],[D,F,G,H,J,M,N,P,U],[D,F,G,H,J,M,P,Q,R,S,U],[D,F,G,H,J,M,P,Q,R,U],[D,F,G,H,J,M,P,Q,S,U],[D,F,G,H,J,M,P,Q,U],[D,F,G,H,J,M,P,R,S,U],[D,F,G,H,J,M,P,R,U],[D,F,G,H,J,M,P,S,U],[D,F,G,H,J,M,P,U],[D,F,G,H,M,N,P,Q,R,S,U],[D,F,G,H,M,N,P,S,U],[D,F,G,H,M,N,P,U],[D,F,G,H,M,P,Q,R,S],[D,F,G,H,M,P,S,U],[D,F,G,H,M,P,U],[D,F,G,J,M,N,P,Q,R,S,U],[D,F,G,J,M,N,P,Q,R,U],[D,F,G,J,M,N,P,Q,S,U],[D,F,G,J,M,N,P,Q,U],[D,F,G,J,M,N,P,R,S,U],[D,F,G,J,M,N,P,R,U],[D,F,G,J,M,N,P,S,U],[D,F,G,J,M,N,P,U],[D,F,G,J,M,P,Q],[D,F,G,J,M,P,Q,R],[D,F,G,J,M,P,Q,R,S],[D,F,G,J,M,P,Q,R,S,U],[D,F,G,J,M,P,Q,R,U],[D,F,G,J,M,P,Q,S],[D,F,G,J,M,P,Q,S,U],[D,F,G,J,M,P,Q,U],[D,F,G,J,M,P,R],[D,F,G,J,M,P,R,S],[D,F,G,J,M,P,R,S,U],[D,F,G,J,M,P,R,U],[D,F,G,J,M,P,S,U],[D,F,G,J,M,P,U],[D,F,G,M,N,P,Q,R,U],[D,F,G,M,N,P,S,U],[D,F,G,M,N,P,U],[D,F,G,M,P,Q,R],[D,F,G,M,P,S,U],[D,F,G,M,P,U],[D,F,H,J,M,N,P,Q,R,S,U],[D,F,H,J,M,N,P,Q,R,U],[D,F,H,J,M,N,P,Q,S,U],[D,F,H,J,M,N,P,Q,U],[D,F,H,J,M,N,P,R,S,U],[D,F,H,J,M,N,P,R,U],[D,F,H,J,M,N,P,S,U],[D,F,H,J,M,N,P,U],[D,F,H,J,M,P,Q,R,S,U],[D,F,H,J,M,P,Q,R,U],[D,F,H,J,M,P,Q,S,U],[D,F,H,J,M,P,Q,U],[D,F,H,J,M,P,R,S,U],[D,F,H,J,M,P,R,U],[D,F,H,J,M,P,S,U],[D,F,H,J,M,P,U],[D,F,H,M,N,P,Q,S,U],[D,F,H,M,N,P,S,U],[D,F,H,M,N,P,U],[D,F,H,M,P,Q,S],[D,F,H,M,P,S,U],[D,F,H,M,P,U],[D,F,J,M,N,P,Q,R,S,U],[D,F,J,M,N,P,Q,R,U],[D,F,J,M,N,P,Q,S,U],[D,F,J,M,N,P,Q,U],[D,F,J,M,N,P,R,S,U],[D,F,J,M,N,P,R,U],[D,F,J,M,N,P,S,U],[D,F,J,M,N,P,U],[D,F,J,M,P,Q],[D,F,J,M,P,Q,R],[D,F,J,M,P,Q,R,S],[D,F,J,M,P,Q,R,S,U],[D,F,J,M,P,Q,R,U],[D,F,J,M,P,Q,S],[D,F,J,M,P,Q,S,U],[D,F,J,M,P,Q,U],[D,F,J,M,P,R],[D,F,J,M,P,R,S],[D,F,J,M,P,R,S,U],[D,F,J,M,P,R,U],[D,F,J,M,P,S,U],[D,F,J,M,P,U],[D,F,M,N,P,Q,U],[D,F,M,N,P,S,U],[D,F,M,N,P,U],[D,F,M,P,Q],[D,F,M,P,S,U],[D,F,M,P,U],[D,G,H,J,M,N,P,Q,R,S,U],[D,G,H,J,M,N,P,Q,R,U],[D,G,H,J,M,N,P,Q,S,U],[D,G,H,J,M,N,P,Q,U],[D,G,H,J,M,N,P,R,S,U],[D,G,H,J,M,N,P,R,U],[D,G,H,J,M,N,P,S,U],[D,G,H,J,M,N,P,U],[D,G,H,J,M,P,Q,R,S,U],[D,G,H,J,M,P,Q,R,U],[D,G,H,J,M,P,Q,S,U],[D,G,H,J,M,P,Q,U],[D,G,H,J,M,P,R,S,U],[D,G,H,J,M,P,R,U],[D,G,H,J,M,P,S,U],[D,G,H,J,M,P,U],[D,G,H,M,N,P,R,S,U],[D,G,H,M,N,P,S,U],[D,G,H,M,N,P,U],[D,G,H,M,P,R,S],[D,G,H,M,P,S,U],[D,G,H,M,P,U],[D,G,J,M,N,P,Q,R,S,U],[D,G,J,M,N,P,Q,R,U],[D,G,J,M,N,P,Q,S,U],[D,G,J,M,N,P,Q,U],[D,G,J,M,N,P,R,S,U],[D,G,J,M,N,P,R,U],[D,G,J,M,N,P,S,U],[D,G,J,M,N,P,U],[D,G,J,M,P,Q],[D,G,J,M,P,Q,R],[D,G,J,M,P,Q,R,S],[D,G,J,M,P,Q,R,S,U],[D,G,J,M,P,Q,R,U],[D,G,J,M,P,Q,S],[D,G,J,M,P,Q,S,U],[D,G,J,M,P,Q,U],[D,G,J,M,P,R],[D,G,J,M,P,R,S],[D,G,J,M,P,R,S,U],[D,G,J,M,P,R,U],[D,G,J,M,P,S,U],[D,G,J,M,P,U],[D,G,M,N,P,R,U],[D,G,M,N,P,S,U],[D,G,M,N,P,U],[D,G,M,P,R],[D,G,M,P,S,U],[D,G,M,P,U],[D,H,J,M,N,P,Q,R,S,U],[D,H,J,M,N,P,Q,R,U],[D,H,J,M,N,P,Q,S,U],[D,H,J,M,N,P,Q,U],[D,H,J,M,N,P,R,S,U],[D,H,J,M,N,P,R,U],[D,H,J,M,N,P,S,U],[D,H,J,M,N,P,U],[D,H,J,M,P,Q,R,S,U],[D,H,J,M,P,Q,R,U],[D,H,J,M,P,Q,S,U],[D,H,J,M,P,Q,U],[D,H,J,M,P,R,S,U],[D,H,J,M,P,R,U],[D,H,J,M,P,S,U],[D,H,J,M,P,U],[D,H,M,N,P,S,U],[D,H,M,N,P,U],[D,H,M,P,S],[D,H,M,P,S,U],[D,H,M,P,U],[D,J,M,N,P,Q,R,S,U],[D,J,M,N,P,Q,R,U],[D,J,M,N,P,Q,S,U],[D,J,M,N,P,Q,U],[D,J,M,N,P,R,S,U],[D,J,M,N,P,R,U],[D,J,M,N,P,S,U],[D,J,M,N,P,U],[D,J,M,P,Q],[D,J,M,P,Q,R],[D,J,M,P,Q,R,S],[D,J,M,P,Q,R,S,U],[D,J,M,P,Q,R,U],[D,J,M,P,Q,S],[D,J,M,P,Q,S,U],[D,J,M,P,Q,U],[D,J,M,P,R],[D,J,M,P,R,S],[D,J,M,P,R,S,U],[D,J,M,P,R,U],[D,J,M,P,S,U],[D,J,M,P,U],[D,M],[D,M,N,P,S,U],[D,M,N,P,U],[D,M,P],[D,M,P,S],[D,M,P,S,U],[D,M,P,U],[E,F,G,H,J,M,N,P,Q,R,S,U],[E,F,G,H,J,M,N,P,Q,R,U],[E,F,G,H,J,M,N,P,Q,S,U],[E,F,G,H,J,M,N,P,Q,U],[E,F,G,H,J,M,N,P,R,S,U],[E,F,G,H,J,M,N,P,R,U],[E,F,G,H,J,M,N,P,S,U],[E,F,G,H,J,M,N,P,U],[E,F,G,H,J,M,P,Q,R,S],[E,F,G,H,J,M,P,Q,R,S,U],[E,F,G,H,J,M,P,Q,R,U],[E,F,G,H,J,M,P,Q,S,U],[E,F,G,H,J,M,P,Q,U],[E,F,G,H,J,M,P,R,S,U],[E,F,G,H,J,M,P,R,U],[E,F,G,H,J,M,P,S,U],[E,F,G,H,J,M,P,U],[E,F,G,J],[E,F,G,J,M],[E,F,G,J,M,N,P,Q,R,S,U],[E,F,G,J,M,N,P,Q,R,U],[E,F,G,J,M,N,P,Q,S,U],[E,F,G,J,M,N,P,Q,U],[E,F,G,J,M,N,P,R,S,U],[E,F,G,J,M,N,P,R,U],[E,F,G,J,M,N,P,S,U],[E,F,G,J,M,N,P,U],[E,F,G,J,M,P],[E,F,G,J,M,P,Q],[E,F,G,J,M,P,Q,R],[E,F,G,J,M,P,Q,R,S],[E,F,G,J,M,P,Q,R,S,U],[E,F,G,J,M,P,Q,R,U],[E,F,G,J,M,P,Q,S],[E,F,G,J,M,P,Q,S,U],[E,F,G,J,M,P,Q,U],[E,F,G,J,M,P,R],[E,F,G,J,M,P,R,S],[E,F,G,J,M,P,R,S,U],[E,F,G,J,M,P,R,U],[E,F,G,J,M,P,S],[E,F,G,J,M,P,S,U],[E,F,G,J,M,P,U],[E,F,G,J,M,Q],[E,F,G,J,M,Q,R],[E,F,G,J,M,R],[E,F,G,J,Q],[E,F,G,J,Q,R],[E,F,G,J,R],[E,F,H,J,M,N,P,Q,R,S,U],[E,F,H,J,M,N,P,Q,R,U],[E,F,H,J,M,N,P,Q,S,U],[E,F,H,J,M,N,P,Q,U],[E,F,H,J,M,N,P,R,S,U],[E,F,H,J,M,N,P,R,U],[E,F,H,J,M,N,P,S,U],[E,F,H,J,M,N,P,U],[E,F,H,J,M,P,Q,R,S,U],[E,F,H,J,M,P,Q,R,U],[E,F,H,J,M,P,Q,S],[E,F,H,J,M,P,Q,S,U],[E,F,H,J,M,P,Q,U],[E,F,H,J,M,P,R,S,U],[E,F,H,J,M,P,R,U],[E,F,H,J,M,P,S,U],[E,F,H,J,M,P,U],[E,F,J],[E,F,J,M],[E,F,J,M,N,P,Q,R,S,U],[E,F,J,M,N,P,Q,R,U],[E,F,J,M,N,P,Q,S,U],[E,F,J,M,N,P,Q,U],[E,F,J,M,N,P,R,S,U],[E,F,J,M,N,P,R,U],[E,F,J,M,N,P,S,U],[E,F,J,M,N,P,U],[E,F,J,M,P],[E,F,J,M,P,Q],[E,F,J,M,P,Q,R],[E,F,J,M,P,Q,R,S],[E,F,J,M,P,Q,R,S,U],[E,F,J,M,P,Q,R,U],[E,F,J,M,P,Q,S],[E,F,J,M,P,Q,S,U],[E,F,J,M,P,Q,U],[E,F,J,M,P,R],[E,F,J,M,P,R,S],[E,F,J,M,P,R,S,U],[E,F,J,M,P,R,U],[E,F,J,M,P,S],[E,F,J,M,P,S,U],[E,F,J,M,P,U],[E,F,J,M,Q],[E,F,J,M,Q,R],[E,F,J,M,R],[E,F,J,Q],[E,F,J,Q,R],[E,F,J,R],[E,G,H,J,M,N,P,Q,R,S,U],[E,G,H,J,M,N,P,Q,R,U],[E,G,H,J,M,N,P,Q,S,U],[E,G,H,J,M,N,P,Q,U],[E,G,H,J,M,N,P,R,S,U],[E,G,H,J,M,N,P,R,U],[E,G,H,J,M,N,P,S,U],[E,G,H,J,M,N,P,U],[E,G,H,J,M,P,Q,R,S,U],[E,G,H,J,M,P,Q,R,U],[E,G,H,J,M,P,Q,S,U],[E,G,H,J,M,P,Q,U],[E,G,H,J,M,P,R,S],[E,G,H,J,M,P,R,S,U],[E,G,H,J,M,P,R,U],[E,G,H,J,M,P,S,U],[E,G,H,J,M,P,U],[E,G,J],[E,G,J,M],[E,G,J,M,N,P,Q,R,S,U],[E,G,J,M,N,P,Q,R,U],[E,G,J,M,N,P,Q,S,U],[E,G,J,M,N,P,Q,U],[E,G,J,M,N,P,R,S,U],[E,G,J,M,N,P,R,U],[E,G,J,M,N,P,S,U],[E,G,J,M,N,P,U],[E,G,J,M,P],[E,G,J,M,P,Q],[E,G,J,M,P,Q,R],[E,G,J,M,P,Q,R,S],[E,G,J,M,P,Q,R,S,U],[E,G,J,M,P,Q,R,U],[E,G,J,M,P,Q,S],[E,G,J,M,P,Q,S,U],[E,G,J,M,P,Q,U],[E,G,J,M,P,R],[E,G,J,M,P,R,S],[E,G,J,M,P,R,S,U],[E,G,J,M,P,R,U],[E,G,J,M,P,S],[E,G,J,M,P,S,U],[E,G,J,M,P,U],[E,G,J,M,Q],[E,G,J,M,Q,R],[E,G,J,M,R],[E,G,J,Q],[E,G,J,Q,R],[E,G,J,R],[E,H,J,M,N,P,Q,R,S,U],[E,H,J,M,N,P,Q,R,U],[E,H,J,M,N,P,Q,S,U],[E,H,J,M,N,P,Q,U],[E,H,J,M,N,P,R,S,U],[E,H,J,M,N,P,R,U],[E,H,J,M,N,P,S,U],[E,H,J,M,N,P,U],[E,H,J,M,P,Q,R,S,U],[E,H,J,M,P,Q,R,U],[E,H,J,M,P,Q,S,U],[E,H,J,M,P,Q,U],[E,H,J,M,P,R,S,U],[E,H,J,M,P,R,U],[E,H,J,M,P,S],[E,H,J,M,P,S,U],[E,H,J,M,P,U],[E,J],[E,J,M],[E,J,M,N,P,Q,R,S,U],[E,J,M,N,P,Q,R,U],[E,J,M,N,P,Q,S,U],[E,J,M,N,P,Q,U],[E,J,M,N,P,R,S,U],[E,J,M,N,P,R,U],[E,J,M,N,P,S,U],[E,J,M,N,P,U],[E,J,M,P],[E,J,M,P,Q],[E,J,M,P,Q,R],[E,J,M,P,Q,R,S],[E,J,M,P,Q,R,S,U],[E,J,M,P,Q,R,U],[E,J,M,P,Q,S],[E,J,M,P,Q,S,U],[E,J,M,P,Q,U],[E,J,M,P,R],[E,J,M,P,R,S],[E,J,M,P,R,S,U],[E,J,M,P,R,U],[E,J,M,P,S],[E,J,M,P,S,U],[E,J,M,P,U],[E,J,M,Q],[E,J,M,Q,R],[E,J,M,R],[E,J,Q],[E,J,Q,R],[E,J,R],[F],[F,G],[F,G,H,J,M,N,P,Q,R,S,U],[F,G,H,J,M,N,P,Q,R,U],[F,G,H,J,M,N,P,Q,S,U],[F,G,H,J,M,N,P,Q,U],[F,G,H,J,M,N,P,R,S,U],[F,G,H,J,M,N,P,R,U],[F,G,H,J,M,N,P,S,U],[F,G,H,J,M,N,P,U],[F,G,H,J,M,P,Q,R,S,U],[F,G,H,J,M,P,Q,R,U],[F,G,H,J,M,P,Q,S,U],[F,G,H,J,M,P,Q,U],[F,G,H,J,M,P,R,S,U],[F,G,H,J,M,P,R,U],[F,G,H,J,M,P,S,U],[F,G,H,J,M,P,U],[F,G,H,M,N,P,Q,R,S,U],[F,G,H,M,N,P,S,U],[F,G,H,M,N,P,U],[F,G,H,M,P,Q,R,S],[F,G,H,M,P,S,U],[F,G,H,M,P,U],[F,G,J],[F,G,J,M,N,P,Q,R,S,U],[F,G,J,M,N,P,Q,R,U],[F,G,J,M,N,P,Q,S,U],[F,G,J,M,N,P,Q,U],[F,G,J,M,N,P,R,S,U],[F,G,J,M,N,P,R,U],[F,G,J,M,N,P,S,U],[F,G,J,M,N,P,U],[F,G,J,M,P,Q],[F,G,J,M,P,Q,R],[F,G,J,M,P,Q,R,S],[F,G,J,M,P,Q,R,S,U],[F,G,J,M,P,Q,R,U],[F,G,J,M,P,Q,S],[F,G,J,M,P,Q,S,U],[F,G,J,M,P,Q,U],[F,G,J,M,P,R],[F,G,J,M,P,R,S],[F,G,J,M,P,R,S,U],[F,G,J,M,P,R,U],[F,G,J,M,P,S,U],[F,G,J,M,P,U],[F,G,J,Q],[F,G,J,Q,R],[F,G,J,R],[F,G,M,N,P,Q,R,U],[F,G,M,N,P,S,U],[F,G,M,N,P,U],[F,G,M,P,Q,R],[F,G,M,P,S,U],[F,G,M,P,U],[F,G,Q,R],[F,H,J,M,N,P,Q,R,S,U],[F,H,J,M,N,P,Q,R,U],[F,H,J,M,N,P,Q,S,U],[F,H,J,M,N,P,Q,U],[F,H,J,M,N,P,R,S,U],[F,H,J,M,N,P,R,U],[F,H,J,M,N,P,S,U],[F,H,J,M,N,P,U],[F,H,J,M,P,Q,R,S,U],[F,H,J,M,P,Q,R,U],[F,H,J,M,P,Q,S,U],[F,H,J,M,P,Q,U],[F,H,J,M,P,R,S,U],[F,H,J,M,P,R,U],[F,H,J,M,P,S,U],[F,H,J,M,P,U],[F,H,M,N,P,Q,S,U],[F,H,M,N,P,S,U],[F,H,M,N,P,U],[F,H,M,P,Q,S],[F,H,M,P,S,U],[F,H,M,P,U],[F,J],[F,J,M,N,P,Q,R,S,U],[F,J,M,N,P,Q,R,U],[F,J,M,N,P,Q,S,U],[F,J,M,N,P,Q,U],[F,J,M,N,P,R,S,U],[F,J,M,N,P,R,U],[F,J,M,N,P,S,U],[F,J,M,N,P,U],[F,J,M,P,Q],[F,J,M,P,Q,R],[F,J,M,P,Q,R,S],[F,J,M,P,Q,R,S,U],[F,J,M,P,Q,R,U],[F,J,M,P,Q,S],[F,J,M,P,Q,S,U],[F,J,M,P,Q,U],[F,J,M,P,R],[F,J,M,P,R,S],[F,J,M,P,R,S,U],[F,J,M,P,R,U],[F,J,M,P,S,U],[F,J,M,P,U],[F,J,Q],[F,J,Q,R],[F,J,R],[F,M,N,P,Q,U],[F,M,N,P,S,U],[F,M,N,P,U],[F,M,P,Q],[F,M,P,S,U],[F,M,P,U],[F,Q],[G],[G,H,J,M,N,P,Q,R,S,U],[G,H,J,M,N,P,Q,R,U],[G,H,J,M,N,P,Q,S,U],[G,H,J,M,N,P,Q,U],[G,H,J,M,N,P,R,S,U],[G,H,J,M,N,P,R,U],[G,H,J,M,N,P,S,U],[G,H,J,M,N,P,U],[G,H,J,M,P,Q,R,S,U],[G,H,J,M,P,Q,R,U],[G,H,J,M,P,Q,S,U],[G,H,J,M,P,Q,U],[G,H,J,M,P,R,S,U],[G,H,J,M,P,R,U],[G,H,J,M,P,S,U],[G,H,J,M,P,U],[G,H,M,N,P,R,S,U],[G,H,M,N,P,S,U],[G,H,M,N,P,U],[G,H,M,P,R,S],[G,H,M,P,S,U],[G,H,M,P,U],[G,J],[G,J,M,N,P,Q,R,S,U],[G,J,M,N,P,Q,R,U],[G,J,M,N,P,Q,S,U],[G,J,M,N,P,Q,U],[G,J,M,N,P,R,S,U],[G,J,M,N,P,R,U],[G,J,M,N,P,S,U],[G,J,M,N,P,U],[G,J,M,P,Q],[G,J,M,P,Q,R],[G,J,M,P,Q,R,S],[G,J,M,P,Q,R,S,U],[G,J,M,P,Q,R,U],[G,J,M,P,Q,S],[G,J,M,P,Q,S,U],[G,J,M,P,Q,U],[G,J,M,P,R],[G,J,M,P,R,S],[G,J,M,P,R,S,U],[G,J,M,P,R,U],[G,J,M,P,S,U],[G,J,M,P,U],[G,J,Q],[G,J,Q,R],[G,J,R],[G,M,N,P,R,U],[G,M,N,P,S,U],[G,M,N,P,U],[G,M,P,R],[G,M,P,S,U],[G,M,P,U],[G,R],[H,J,M,N,P,Q,R,S,U],[H,J,M,N,P,Q,R,U],[H,J,M,N,P,Q,S,U],[H,J,M,N,P,Q,U],[H,J,M,N,P,R,S,U],[H,J,M,N,P,R,U],[H,J,M,N,P,S,U],[H,J,M,N,P,U],[H,J,M,P,Q,R,S,U],[H,J,M,P,Q,R,U],[H,J,M,P,Q,S,U],[H,J,M,P,Q,U],[H,J,M,P,R,S,U],[H,J,M,P,R,U],[H,J,M,P,S,U],[H,J,M,P,U],[H,M,N,P,S,U],[H,M,N,P,U],[H,M,P,S],[H,M,P,S,U],[H,M,P,U],[I,J],[I,J,V],[J],[J,M,N,P,Q,R,S,U],[J,M,N,P,Q,R,U],[J,M,N,P,Q,S,U],[J,M,N,P,Q,U],[J,M,N,P,R,S,U],[J,M,N,P,R,U],[J,M,N,P,S,U],[J,M,N,P,U],[J,M,P,Q],[J,M,P,Q,R],[J,M,P,Q,R,S],[J,M,P,Q,R,S,U],[J,M,P,Q,R,U],[J,M,P,Q,S],[J,M,P,Q,S,U],[J,M,P,Q,U],[J,M,P,R],[J,M,P,R,S],[J,M,P,R,S,U],[J,M,P,R,U],[J,M,P,S,U],[J,M,P,U],[J,Q],[J,Q,R],[J,R],[M],[M,N,P,S,U],[M,N,P,U],[M,P],[M,P,S],[M,P,S,U],[M,P,U]]),ground([K,L,O,T]),linear(I);mshare([[B,C,D,E,F,H,J,M,N,P,Q,R,S,U],[B,C,D,E,F,H,J,M,N,P,Q,R,U],[B,C,D,E,F,H,J,M,N,P,Q,S,U],[B,C,D,E,F,H,J,M,N,P,Q,U],[B,C,D,E,F,H,J,M,N,P,R,S,U],[B,C,D,E,F,H,J,M,N,P,R,U],[B,C,D,E,F,H,J,M,N,P,S,U],[B,C,D,E,F,H,J,M,N,P,U],[B,C,D,E,F,H,J,M,P,Q,R,S,U],[B,C,D,E,F,H,J,M,P,Q,R,U],[B,C,D,E,F,H,J,M,P,Q,S],[B,C,D,E,F,H,J,M,P,Q,S,U],[B,C,D,E,F,H,J,M,P,Q,U],[B,C,D,E,F,H,J,M,P,R,S,U],[B,C,D,E,F,H,J,M,P,R,U],[B,C,D,E,F,H,J,M,P,S,U],[B,C,D,E,F,H,J,M,P,U],[B,C,D,E,F,J],[B,C,D,E,F,J,M],[B,C,D,E,F,J,M,N,P,Q,R,S,U],[B,C,D,E,F,J,M,N,P,Q,R,U],[B,C,D,E,F,J,M,N,P,Q,S,U],[B,C,D,E,F,J,M,N,P,Q,U],[B,C,D,E,F,J,M,N,P,R,S,U],[B,C,D,E,F,J,M,N,P,R,U],[B,C,D,E,F,J,M,N,P,S,U],[B,C,D,E,F,J,M,N,P,U],[B,C,D,E,F,J,M,P],[B,C,D,E,F,J,M,P,Q],[B,C,D,E,F,J,M,P,Q,R],[B,C,D,E,F,J,M,P,Q,R,S],[B,C,D,E,F,J,M,P,Q,R,S,U],[B,C,D,E,F,J,M,P,Q,R,U],[B,C,D,E,F,J,M,P,Q,S],[B,C,D,E,F,J,M,P,Q,S,U],[B,C,D,E,F,J,M,P,Q,U],[B,C,D,E,F,J,M,P,R],[B,C,D,E,F,J,M,P,R,S],[B,C,D,E,F,J,M,P,R,S,U],[B,C,D,E,F,J,M,P,R,U],[B,C,D,E,F,J,M,P,S],[B,C,D,E,F,J,M,P,S,U],[B,C,D,E,F,J,M,P,U],[B,C,D,E,F,J,M,Q],[B,C,D,E,F,J,M,Q,R],[B,C,D,E,F,J,M,R],[B,C,D,E,F,J,Q],[B,C,D,E,F,J,Q,R],[B,C,D,E,F,J,R],[B,C,D,E,H,J,M,N,P,Q,R,S,U],[B,C,D,E,H,J,M,N,P,Q,R,U],[B,C,D,E,H,J,M,N,P,Q,S,U],[B,C,D,E,H,J,M,N,P,Q,U],[B,C,D,E,H,J,M,N,P,R,S,U],[B,C,D,E,H,J,M,N,P,R,U],[B,C,D,E,H,J,M,N,P,S,U],[B,C,D,E,H,J,M,N,P,U],[B,C,D,E,H,J,M,P,Q,R,S,U],[B,C,D,E,H,J,M,P,Q,R,U],[B,C,D,E,H,J,M,P,Q,S,U],[B,C,D,E,H,J,M,P,Q,U],[B,C,D,E,H,J,M,P,R,S,U],[B,C,D,E,H,J,M,P,R,U],[B,C,D,E,H,J,M,P,S],[B,C,D,E,H,J,M,P,S,U],[B,C,D,E,H,J,M,P,U],[B,C,D,E,J],[B,C,D,E,J,M],[B,C,D,E,J,M,N,P,Q,R,S,U],[B,C,D,E,J,M,N,P,Q,R,U],[B,C,D,E,J,M,N,P,Q,S,U],[B,C,D,E,J,M,N,P,Q,U],[B,C,D,E,J,M,N,P,R,S,U],[B,C,D,E,J,M,N,P,R,U],[B,C,D,E,J,M,N,P,S,U],[B,C,D,E,J,M,N,P,U],[B,C,D,E,J,M,P],[B,C,D,E,J,M,P,Q],[B,C,D,E,J,M,P,Q,R],[B,C,D,E,J,M,P,Q,R,S],[B,C,D,E,J,M,P,Q,R,S,U],[B,C,D,E,J,M,P,Q,R,U],[B,C,D,E,J,M,P,Q,S],[B,C,D,E,J,M,P,Q,S,U],[B,C,D,E,J,M,P,Q,U],[B,C,D,E,J,M,P,R],[B,C,D,E,J,M,P,R,S],[B,C,D,E,J,M,P,R,S,U],[B,C,D,E,J,M,P,R,U],[B,C,D,E,J,M,P,S],[B,C,D,E,J,M,P,S,U],[B,C,D,E,J,M,P,U],[B,C,D,E,J,M,Q],[B,C,D,E,J,M,Q,R],[B,C,D,E,J,M,R],[B,C,D,E,J,Q],[B,C,D,E,J,Q,R],[B,C,D,E,J,R],[B,C,D,F,H,J,M,N,P,Q,R,S,U],[B,C,D,F,H,J,M,N,P,Q,R,U],[B,C,D,F,H,J,M,N,P,Q,S,U],[B,C,D,F,H,J,M,N,P,Q,U],[B,C,D,F,H,J,M,N,P,R,S,U],[B,C,D,F,H,J,M,N,P,R,U],[B,C,D,F,H,J,M,N,P,S,U],[B,C,D,F,H,J,M,N,P,U],[B,C,D,F,H,J,M,P,Q,R,S,U],[B,C,D,F,H,J,M,P,Q,R,U],[B,C,D,F,H,J,M,P,Q,S],[B,C,D,F,H,J,M,P,Q,S,U],[B,C,D,F,H,J,M,P,Q,U],[B,C,D,F,H,J,M,P,R,S,U],[B,C,D,F,H,J,M,P,R,U],[B,C,D,F,H,J,M,P,S,U],[B,C,D,F,H,J,M,P,U],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N,P,Q,R,S,U],[B,C,D,F,J,M,N,P,Q,R,U],[B,C,D,F,J,M,N,P,Q,S,U],[B,C,D,F,J,M,N,P,Q,U],[B,C,D,F,J,M,N,P,R,S,U],[B,C,D,F,J,M,N,P,R,U],[B,C,D,F,J,M,N,P,S,U],[B,C,D,F,J,M,N,P,U],[B,C,D,F,J,M,P],[B,C,D,F,J,M,P,Q],[B,C,D,F,J,M,P,Q,R],[B,C,D,F,J,M,P,Q,R,S],[B,C,D,F,J,M,P,Q,R,S,U],[B,C,D,F,J,M,P,Q,R,U],[B,C,D,F,J,M,P,Q,S],[B,C,D,F,J,M,P,Q,S,U],[B,C,D,F,J,M,P,Q,U],[B,C,D,F,J,M,P,R],[B,C,D,F,J,M,P,R,S],[B,C,D,F,J,M,P,R,S,U],[B,C,D,F,J,M,P,R,U],[B,C,D,F,J,M,P,S],[B,C,D,F,J,M,P,S,U],[B,C,D,F,J,M,P,U],[B,C,D,F,J,M,Q],[B,C,D,F,J,M,Q,R],[B,C,D,F,J,M,R],[B,C,D,F,J,Q],[B,C,D,F,J,Q,R],[B,C,D,F,J,R],[B,C,D,H,J,M,N,P,Q,R,S,U],[B,C,D,H,J,M,N,P,Q,R,U],[B,C,D,H,J,M,N,P,Q,S,U],[B,C,D,H,J,M,N,P,Q,U],[B,C,D,H,J,M,N,P,R,S,U],[B,C,D,H,J,M,N,P,R,U],[B,C,D,H,J,M,N,P,S,U],[B,C,D,H,J,M,N,P,U],[B,C,D,H,J,M,P,Q,R,S,U],[B,C,D,H,J,M,P,Q,R,U],[B,C,D,H,J,M,P,Q,S,U],[B,C,D,H,J,M,P,Q,U],[B,C,D,H,J,M,P,R,S,U],[B,C,D,H,J,M,P,R,U],[B,C,D,H,J,M,P,S],[B,C,D,H,J,M,P,S,U],[B,C,D,H,J,M,P,U],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N,P,Q,R,S,U],[B,C,D,J,M,N,P,Q,R,U],[B,C,D,J,M,N,P,Q,S,U],[B,C,D,J,M,N,P,Q,U],[B,C,D,J,M,N,P,R,S,U],[B,C,D,J,M,N,P,R,U],[B,C,D,J,M,N,P,S,U],[B,C,D,J,M,N,P,U],[B,C,D,J,M,P],[B,C,D,J,M,P,Q],[B,C,D,J,M,P,Q,R],[B,C,D,J,M,P,Q,R,S],[B,C,D,J,M,P,Q,R,S,U],[B,C,D,J,M,P,Q,R,U],[B,C,D,J,M,P,Q,S],[B,C,D,J,M,P,Q,S,U],[B,C,D,J,M,P,Q,U],[B,C,D,J,M,P,R],[B,C,D,J,M,P,R,S],[B,C,D,J,M,P,R,S,U],[B,C,D,J,M,P,R,U],[B,C,D,J,M,P,S],[B,C,D,J,M,P,S,U],[B,C,D,J,M,P,U],[B,C,D,J,M,Q],[B,C,D,J,M,Q,R],[B,C,D,J,M,R],[B,C,D,J,Q],[B,C,D,J,Q,R],[B,C,D,J,R],[B,C,E,F,H,J,M,N,P,Q,R,S,U],[B,C,E,F,H,J,M,N,P,Q,R,U],[B,C,E,F,H,J,M,N,P,Q,S,U],[B,C,E,F,H,J,M,N,P,Q,U],[B,C,E,F,H,J,M,N,P,R,S,U],[B,C,E,F,H,J,M,N,P,R,U],[B,C,E,F,H,J,M,N,P,S,U],[B,C,E,F,H,J,M,N,P,U],[B,C,E,F,H,J,M,P,Q,R,S,U],[B,C,E,F,H,J,M,P,Q,R,U],[B,C,E,F,H,J,M,P,Q,S],[B,C,E,F,H,J,M,P,Q,S,U],[B,C,E,F,H,J,M,P,Q,U],[B,C,E,F,H,J,M,P,R,S,U],[B,C,E,F,H,J,M,P,R,U],[B,C,E,F,H,J,M,P,S,U],[B,C,E,F,H,J,M,P,U],[B,C,E,F,J],[B,C,E,F,J,M],[B,C,E,F,J,M,N,P,Q,R,S,U],[B,C,E,F,J,M,N,P,Q,R,U],[B,C,E,F,J,M,N,P,Q,S,U],[B,C,E,F,J,M,N,P,Q,U],[B,C,E,F,J,M,N,P,R,S,U],[B,C,E,F,J,M,N,P,R,U],[B,C,E,F,J,M,N,P,S,U],[B,C,E,F,J,M,N,P,U],[B,C,E,F,J,M,P],[B,C,E,F,J,M,P,Q],[B,C,E,F,J,M,P,Q,R],[B,C,E,F,J,M,P,Q,R,S],[B,C,E,F,J,M,P,Q,R,S,U],[B,C,E,F,J,M,P,Q,R,U],[B,C,E,F,J,M,P,Q,S],[B,C,E,F,J,M,P,Q,S,U],[B,C,E,F,J,M,P,Q,U],[B,C,E,F,J,M,P,R],[B,C,E,F,J,M,P,R,S],[B,C,E,F,J,M,P,R,S,U],[B,C,E,F,J,M,P,R,U],[B,C,E,F,J,M,P,S],[B,C,E,F,J,M,P,S,U],[B,C,E,F,J,M,P,U],[B,C,E,F,J,M,Q],[B,C,E,F,J,M,Q,R],[B,C,E,F,J,M,R],[B,C,E,F,J,Q],[B,C,E,F,J,Q,R],[B,C,E,F,J,R],[B,C,E,H,J,M,N,P,Q,R,S,U],[B,C,E,H,J,M,N,P,Q,R,U],[B,C,E,H,J,M,N,P,Q,S,U],[B,C,E,H,J,M,N,P,Q,U],[B,C,E,H,J,M,N,P,R,S,U],[B,C,E,H,J,M,N,P,R,U],[B,C,E,H,J,M,N,P,S,U],[B,C,E,H,J,M,N,P,U],[B,C,E,H,J,M,P,Q,R,S,U],[B,C,E,H,J,M,P,Q,R,U],[B,C,E,H,J,M,P,Q,S,U],[B,C,E,H,J,M,P,Q,U],[B,C,E,H,J,M,P,R,S,U],[B,C,E,H,J,M,P,R,U],[B,C,E,H,J,M,P,S],[B,C,E,H,J,M,P,S,U],[B,C,E,H,J,M,P,U],[B,C,E,J],[B,C,E,J,M],[B,C,E,J,M,N,P,Q,R,S,U],[B,C,E,J,M,N,P,Q,R,U],[B,C,E,J,M,N,P,Q,S,U],[B,C,E,J,M,N,P,Q,U],[B,C,E,J,M,N,P,R,S,U],[B,C,E,J,M,N,P,R,U],[B,C,E,J,M,N,P,S,U],[B,C,E,J,M,N,P,U],[B,C,E,J,M,P],[B,C,E,J,M,P,Q],[B,C,E,J,M,P,Q,R],[B,C,E,J,M,P,Q,R,S],[B,C,E,J,M,P,Q,R,S,U],[B,C,E,J,M,P,Q,R,U],[B,C,E,J,M,P,Q,S],[B,C,E,J,M,P,Q,S,U],[B,C,E,J,M,P,Q,U],[B,C,E,J,M,P,R],[B,C,E,J,M,P,R,S],[B,C,E,J,M,P,R,S,U],[B,C,E,J,M,P,R,U],[B,C,E,J,M,P,S],[B,C,E,J,M,P,S,U],[B,C,E,J,M,P,U],[B,C,E,J,M,Q],[B,C,E,J,M,Q,R],[B,C,E,J,M,R],[B,C,E,J,Q],[B,C,E,J,Q,R],[B,C,E,J,R],[B,C,F,H,J,M,N,P,Q,R,S,U],[B,C,F,H,J,M,N,P,Q,R,U],[B,C,F,H,J,M,N,P,Q,S,U],[B,C,F,H,J,M,N,P,Q,U],[B,C,F,H,J,M,N,P,R,S,U],[B,C,F,H,J,M,N,P,R,U],[B,C,F,H,J,M,N,P,S,U],[B,C,F,H,J,M,N,P,U],[B,C,F,H,J,M,P,Q,R,S,U],[B,C,F,H,J,M,P,Q,R,U],[B,C,F,H,J,M,P,Q,S],[B,C,F,H,J,M,P,Q,S,U],[B,C,F,H,J,M,P,Q,U],[B,C,F,H,J,M,P,R,S,U],[B,C,F,H,J,M,P,R,U],[B,C,F,H,J,M,P,S,U],[B,C,F,H,J,M,P,U],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N,P,Q,R,S,U],[B,C,F,J,M,N,P,Q,R,U],[B,C,F,J,M,N,P,Q,S,U],[B,C,F,J,M,N,P,Q,U],[B,C,F,J,M,N,P,R,S,U],[B,C,F,J,M,N,P,R,U],[B,C,F,J,M,N,P,S,U],[B,C,F,J,M,N,P,U],[B,C,F,J,M,P],[B,C,F,J,M,P,Q],[B,C,F,J,M,P,Q,R],[B,C,F,J,M,P,Q,R,S],[B,C,F,J,M,P,Q,R,S,U],[B,C,F,J,M,P,Q,R,U],[B,C,F,J,M,P,Q,S],[B,C,F,J,M,P,Q,S,U],[B,C,F,J,M,P,Q,U],[B,C,F,J,M,P,R],[B,C,F,J,M,P,R,S],[B,C,F,J,M,P,R,S,U],[B,C,F,J,M,P,R,U],[B,C,F,J,M,P,S],[B,C,F,J,M,P,S,U],[B,C,F,J,M,P,U],[B,C,F,J,M,Q],[B,C,F,J,M,Q,R],[B,C,F,J,M,R],[B,C,F,J,Q],[B,C,F,J,Q,R],[B,C,F,J,R],[B,C,H,J,M,N,P,Q,R,S,U],[B,C,H,J,M,N,P,Q,R,U],[B,C,H,J,M,N,P,Q,S,U],[B,C,H,J,M,N,P,Q,U],[B,C,H,J,M,N,P,R,S,U],[B,C,H,J,M,N,P,R,U],[B,C,H,J,M,N,P,S,U],[B,C,H,J,M,N,P,U],[B,C,H,J,M,P,Q,R,S,U],[B,C,H,J,M,P,Q,R,U],[B,C,H,J,M,P,Q,S,U],[B,C,H,J,M,P,Q,U],[B,C,H,J,M,P,R,S,U],[B,C,H,J,M,P,R,U],[B,C,H,J,M,P,S],[B,C,H,J,M,P,S,U],[B,C,H,J,M,P,U],[B,C,J],[B,C,J,M],[B,C,J,M,N,P,Q,R,S,U],[B,C,J,M,N,P,Q,R,U],[B,C,J,M,N,P,Q,S,U],[B,C,J,M,N,P,Q,U],[B,C,J,M,N,P,R,S,U],[B,C,J,M,N,P,R,U],[B,C,J,M,N,P,S,U],[B,C,J,M,N,P,U],[B,C,J,M,P],[B,C,J,M,P,Q],[B,C,J,M,P,Q,R],[B,C,J,M,P,Q,R,S],[B,C,J,M,P,Q,R,S,U],[B,C,J,M,P,Q,R,U],[B,C,J,M,P,Q,S],[B,C,J,M,P,Q,S,U],[B,C,J,M,P,Q,U],[B,C,J,M,P,R],[B,C,J,M,P,R,S],[B,C,J,M,P,R,S,U],[B,C,J,M,P,R,U],[B,C,J,M,P,S],[B,C,J,M,P,S,U],[B,C,J,M,P,U],[B,C,J,M,Q],[B,C,J,M,Q,R],[B,C,J,M,R],[B,C,J,Q],[B,C,J,Q,R],[B,C,J,R],[B,D,E,F,H,J,M,N,P,Q,R,S,U],[B,D,E,F,H,J,M,N,P,Q,R,U],[B,D,E,F,H,J,M,N,P,Q,S,U],[B,D,E,F,H,J,M,N,P,Q,U],[B,D,E,F,H,J,M,N,P,R,S,U],[B,D,E,F,H,J,M,N,P,R,U],[B,D,E,F,H,J,M,N,P,S,U],[B,D,E,F,H,J,M,N,P,U],[B,D,E,F,H,J,M,P,Q,R,S,U],[B,D,E,F,H,J,M,P,Q,R,U],[B,D,E,F,H,J,M,P,Q,S],[B,D,E,F,H,J,M,P,Q,S,U],[B,D,E,F,H,J,M,P,Q,U],[B,D,E,F,H,J,M,P,R,S,U],[B,D,E,F,H,J,M,P,R,U],[B,D,E,F,H,J,M,P,S,U],[B,D,E,F,H,J,M,P,U],[B,D,E,F,J],[B,D,E,F,J,M],[B,D,E,F,J,M,N,P,Q,R,S,U],[B,D,E,F,J,M,N,P,Q,R,U],[B,D,E,F,J,M,N,P,Q,S,U],[B,D,E,F,J,M,N,P,Q,U],[B,D,E,F,J,M,N,P,R,S,U],[B,D,E,F,J,M,N,P,R,U],[B,D,E,F,J,M,N,P,S,U],[B,D,E,F,J,M,N,P,U],[B,D,E,F,J,M,P],[B,D,E,F,J,M,P,Q],[B,D,E,F,J,M,P,Q,R],[B,D,E,F,J,M,P,Q,R,S],[B,D,E,F,J,M,P,Q,R,S,U],[B,D,E,F,J,M,P,Q,R,U],[B,D,E,F,J,M,P,Q,S],[B,D,E,F,J,M,P,Q,S,U],[B,D,E,F,J,M,P,Q,U],[B,D,E,F,J,M,P,R],[B,D,E,F,J,M,P,R,S],[B,D,E,F,J,M,P,R,S,U],[B,D,E,F,J,M,P,R,U],[B,D,E,F,J,M,P,S],[B,D,E,F,J,M,P,S,U],[B,D,E,F,J,M,P,U],[B,D,E,F,J,M,Q],[B,D,E,F,J,M,Q,R],[B,D,E,F,J,M,R],[B,D,E,F,J,Q],[B,D,E,F,J,Q,R],[B,D,E,F,J,R],[B,D,E,H,J,M,N,P,Q,R,S,U],[B,D,E,H,J,M,N,P,Q,R,U],[B,D,E,H,J,M,N,P,Q,S,U],[B,D,E,H,J,M,N,P,Q,U],[B,D,E,H,J,M,N,P,R,S,U],[B,D,E,H,J,M,N,P,R,U],[B,D,E,H,J,M,N,P,S,U],[B,D,E,H,J,M,N,P,U],[B,D,E,H,J,M,P,Q,R,S,U],[B,D,E,H,J,M,P,Q,R,U],[B,D,E,H,J,M,P,Q,S,U],[B,D,E,H,J,M,P,Q,U],[B,D,E,H,J,M,P,R,S,U],[B,D,E,H,J,M,P,R,U],[B,D,E,H,J,M,P,S],[B,D,E,H,J,M,P,S,U],[B,D,E,H,J,M,P,U],[B,D,E,J],[B,D,E,J,M],[B,D,E,J,M,N,P,Q,R,S,U],[B,D,E,J,M,N,P,Q,R,U],[B,D,E,J,M,N,P,Q,S,U],[B,D,E,J,M,N,P,Q,U],[B,D,E,J,M,N,P,R,S,U],[B,D,E,J,M,N,P,R,U],[B,D,E,J,M,N,P,S,U],[B,D,E,J,M,N,P,U],[B,D,E,J,M,P],[B,D,E,J,M,P,Q],[B,D,E,J,M,P,Q,R],[B,D,E,J,M,P,Q,R,S],[B,D,E,J,M,P,Q,R,S,U],[B,D,E,J,M,P,Q,R,U],[B,D,E,J,M,P,Q,S],[B,D,E,J,M,P,Q,S,U],[B,D,E,J,M,P,Q,U],[B,D,E,J,M,P,R],[B,D,E,J,M,P,R,S],[B,D,E,J,M,P,R,S,U],[B,D,E,J,M,P,R,U],[B,D,E,J,M,P,S],[B,D,E,J,M,P,S,U],[B,D,E,J,M,P,U],[B,D,E,J,M,Q],[B,D,E,J,M,Q,R],[B,D,E,J,M,R],[B,D,E,J,Q],[B,D,E,J,Q,R],[B,D,E,J,R],[B,D,F,H,J,M,N,P,Q,R,S,U],[B,D,F,H,J,M,N,P,Q,R,U],[B,D,F,H,J,M,N,P,Q,S,U],[B,D,F,H,J,M,N,P,Q,U],[B,D,F,H,J,M,N,P,R,S,U],[B,D,F,H,J,M,N,P,R,U],[B,D,F,H,J,M,N,P,S,U],[B,D,F,H,J,M,N,P,U],[B,D,F,H,J,M,P,Q,R,S,U],[B,D,F,H,J,M,P,Q,R,U],[B,D,F,H,J,M,P,Q,S],[B,D,F,H,J,M,P,Q,S,U],[B,D,F,H,J,M,P,Q,U],[B,D,F,H,J,M,P,R,S,U],[B,D,F,H,J,M,P,R,U],[B,D,F,H,J,M,P,S,U],[B,D,F,H,J,M,P,U],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N,P,Q,R,S,U],[B,D,F,J,M,N,P,Q,R,U],[B,D,F,J,M,N,P,Q,S,U],[B,D,F,J,M,N,P,Q,U],[B,D,F,J,M,N,P,R,S,U],[B,D,F,J,M,N,P,R,U],[B,D,F,J,M,N,P,S,U],[B,D,F,J,M,N,P,U],[B,D,F,J,M,P],[B,D,F,J,M,P,Q],[B,D,F,J,M,P,Q,R],[B,D,F,J,M,P,Q,R,S],[B,D,F,J,M,P,Q,R,S,U],[B,D,F,J,M,P,Q,R,U],[B,D,F,J,M,P,Q,S],[B,D,F,J,M,P,Q,S,U],[B,D,F,J,M,P,Q,U],[B,D,F,J,M,P,R],[B,D,F,J,M,P,R,S],[B,D,F,J,M,P,R,S,U],[B,D,F,J,M,P,R,U],[B,D,F,J,M,P,S],[B,D,F,J,M,P,S,U],[B,D,F,J,M,P,U],[B,D,F,J,M,Q],[B,D,F,J,M,Q,R],[B,D,F,J,M,R],[B,D,F,J,Q],[B,D,F,J,Q,R],[B,D,F,J,R],[B,D,H,J,M,N,P,Q,R,S,U],[B,D,H,J,M,N,P,Q,R,U],[B,D,H,J,M,N,P,Q,S,U],[B,D,H,J,M,N,P,Q,U],[B,D,H,J,M,N,P,R,S,U],[B,D,H,J,M,N,P,R,U],[B,D,H,J,M,N,P,S,U],[B,D,H,J,M,N,P,U],[B,D,H,J,M,P,Q,R,S,U],[B,D,H,J,M,P,Q,R,U],[B,D,H,J,M,P,Q,S,U],[B,D,H,J,M,P,Q,U],[B,D,H,J,M,P,R,S,U],[B,D,H,J,M,P,R,U],[B,D,H,J,M,P,S],[B,D,H,J,M,P,S,U],[B,D,H,J,M,P,U],[B,D,J],[B,D,J,M],[B,D,J,M,N,P,Q,R,S,U],[B,D,J,M,N,P,Q,R,U],[B,D,J,M,N,P,Q,S,U],[B,D,J,M,N,P,Q,U],[B,D,J,M,N,P,R,S,U],[B,D,J,M,N,P,R,U],[B,D,J,M,N,P,S,U],[B,D,J,M,N,P,U],[B,D,J,M,P],[B,D,J,M,P,Q],[B,D,J,M,P,Q,R],[B,D,J,M,P,Q,R,S],[B,D,J,M,P,Q,R,S,U],[B,D,J,M,P,Q,R,U],[B,D,J,M,P,Q,S],[B,D,J,M,P,Q,S,U],[B,D,J,M,P,Q,U],[B,D,J,M,P,R],[B,D,J,M,P,R,S],[B,D,J,M,P,R,S,U],[B,D,J,M,P,R,U],[B,D,J,M,P,S],[B,D,J,M,P,S,U],[B,D,J,M,P,U],[B,D,J,M,Q],[B,D,J,M,Q,R],[B,D,J,M,R],[B,D,J,Q],[B,D,J,Q,R],[B,D,J,R],[B,E,F,H,J,M,N,P,Q,R,S,U],[B,E,F,H,J,M,N,P,Q,R,U],[B,E,F,H,J,M,N,P,Q,S,U],[B,E,F,H,J,M,N,P,Q,U],[B,E,F,H,J,M,N,P,R,S,U],[B,E,F,H,J,M,N,P,R,U],[B,E,F,H,J,M,N,P,S,U],[B,E,F,H,J,M,N,P,U],[B,E,F,H,J,M,P,Q,R,S,U],[B,E,F,H,J,M,P,Q,R,U],[B,E,F,H,J,M,P,Q,S],[B,E,F,H,J,M,P,Q,S,U],[B,E,F,H,J,M,P,Q,U],[B,E,F,H,J,M,P,R,S,U],[B,E,F,H,J,M,P,R,U],[B,E,F,H,J,M,P,S,U],[B,E,F,H,J,M,P,U],[B,E,F,J],[B,E,F,J,M],[B,E,F,J,M,N,P,Q,R,S,U],[B,E,F,J,M,N,P,Q,R,U],[B,E,F,J,M,N,P,Q,S,U],[B,E,F,J,M,N,P,Q,U],[B,E,F,J,M,N,P,R,S,U],[B,E,F,J,M,N,P,R,U],[B,E,F,J,M,N,P,S,U],[B,E,F,J,M,N,P,U],[B,E,F,J,M,P],[B,E,F,J,M,P,Q],[B,E,F,J,M,P,Q,R],[B,E,F,J,M,P,Q,R,S],[B,E,F,J,M,P,Q,R,S,U],[B,E,F,J,M,P,Q,R,U],[B,E,F,J,M,P,Q,S],[B,E,F,J,M,P,Q,S,U],[B,E,F,J,M,P,Q,U],[B,E,F,J,M,P,R],[B,E,F,J,M,P,R,S],[B,E,F,J,M,P,R,S,U],[B,E,F,J,M,P,R,U],[B,E,F,J,M,P,S],[B,E,F,J,M,P,S,U],[B,E,F,J,M,P,U],[B,E,F,J,M,Q],[B,E,F,J,M,Q,R],[B,E,F,J,M,R],[B,E,F,J,Q],[B,E,F,J,Q,R],[B,E,F,J,R],[B,E,H,J,M,N,P,Q,R,S,U],[B,E,H,J,M,N,P,Q,R,U],[B,E,H,J,M,N,P,Q,S,U],[B,E,H,J,M,N,P,Q,U],[B,E,H,J,M,N,P,R,S,U],[B,E,H,J,M,N,P,R,U],[B,E,H,J,M,N,P,S,U],[B,E,H,J,M,N,P,U],[B,E,H,J,M,P,Q,R,S,U],[B,E,H,J,M,P,Q,R,U],[B,E,H,J,M,P,Q,S,U],[B,E,H,J,M,P,Q,U],[B,E,H,J,M,P,R,S,U],[B,E,H,J,M,P,R,U],[B,E,H,J,M,P,S],[B,E,H,J,M,P,S,U],[B,E,H,J,M,P,U],[B,E,J],[B,E,J,M],[B,E,J,M,N,P,Q,R,S,U],[B,E,J,M,N,P,Q,R,U],[B,E,J,M,N,P,Q,S,U],[B,E,J,M,N,P,Q,U],[B,E,J,M,N,P,R,S,U],[B,E,J,M,N,P,R,U],[B,E,J,M,N,P,S,U],[B,E,J,M,N,P,U],[B,E,J,M,P],[B,E,J,M,P,Q],[B,E,J,M,P,Q,R],[B,E,J,M,P,Q,R,S],[B,E,J,M,P,Q,R,S,U],[B,E,J,M,P,Q,R,U],[B,E,J,M,P,Q,S],[B,E,J,M,P,Q,S,U],[B,E,J,M,P,Q,U],[B,E,J,M,P,R],[B,E,J,M,P,R,S],[B,E,J,M,P,R,S,U],[B,E,J,M,P,R,U],[B,E,J,M,P,S],[B,E,J,M,P,S,U],[B,E,J,M,P,U],[B,E,J,M,Q],[B,E,J,M,Q,R],[B,E,J,M,R],[B,E,J,Q],[B,E,J,Q,R],[B,E,J,R],[B,F,H,J,M,N,P,Q,R,S,U],[B,F,H,J,M,N,P,Q,R,U],[B,F,H,J,M,N,P,Q,S,U],[B,F,H,J,M,N,P,Q,U],[B,F,H,J,M,N,P,R,S,U],[B,F,H,J,M,N,P,R,U],[B,F,H,J,M,N,P,S,U],[B,F,H,J,M,N,P,U],[B,F,H,J,M,P,Q,R,S,U],[B,F,H,J,M,P,Q,R,U],[B,F,H,J,M,P,Q,S],[B,F,H,J,M,P,Q,S,U],[B,F,H,J,M,P,Q,U],[B,F,H,J,M,P,R,S,U],[B,F,H,J,M,P,R,U],[B,F,H,J,M,P,S,U],[B,F,H,J,M,P,U],[B,F,J],[B,F,J,M],[B,F,J,M,N,P,Q,R,S,U],[B,F,J,M,N,P,Q,R,U],[B,F,J,M,N,P,Q,S,U],[B,F,J,M,N,P,Q,U],[B,F,J,M,N,P,R,S,U],[B,F,J,M,N,P,R,U],[B,F,J,M,N,P,S,U],[B,F,J,M,N,P,U],[B,F,J,M,P],[B,F,J,M,P,Q],[B,F,J,M,P,Q,R],[B,F,J,M,P,Q,R,S],[B,F,J,M,P,Q,R,S,U],[B,F,J,M,P,Q,R,U],[B,F,J,M,P,Q,S],[B,F,J,M,P,Q,S,U],[B,F,J,M,P,Q,U],[B,F,J,M,P,R],[B,F,J,M,P,R,S],[B,F,J,M,P,R,S,U],[B,F,J,M,P,R,U],[B,F,J,M,P,S],[B,F,J,M,P,S,U],[B,F,J,M,P,U],[B,F,J,M,Q],[B,F,J,M,Q,R],[B,F,J,M,R],[B,F,J,Q],[B,F,J,Q,R],[B,F,J,R],[B,H,J,M,N,P,Q,R,S,U],[B,H,J,M,N,P,Q,R,U],[B,H,J,M,N,P,Q,S,U],[B,H,J,M,N,P,Q,U],[B,H,J,M,N,P,R,S,U],[B,H,J,M,N,P,R,U],[B,H,J,M,N,P,S,U],[B,H,J,M,N,P,U],[B,H,J,M,P,Q,R,S,U],[B,H,J,M,P,Q,R,U],[B,H,J,M,P,Q,S,U],[B,H,J,M,P,Q,U],[B,H,J,M,P,R,S,U],[B,H,J,M,P,R,U],[B,H,J,M,P,S],[B,H,J,M,P,S,U],[B,H,J,M,P,U],[B,J],[B,J,M],[B,J,M,N,P,Q,R,S,U],[B,J,M,N,P,Q,R,U],[B,J,M,N,P,Q,S,U],[B,J,M,N,P,Q,U],[B,J,M,N,P,R,S,U],[B,J,M,N,P,R,U],[B,J,M,N,P,S,U],[B,J,M,N,P,U],[B,J,M,P],[B,J,M,P,Q],[B,J,M,P,Q,R],[B,J,M,P,Q,R,S],[B,J,M,P,Q,R,S,U],[B,J,M,P,Q,R,U],[B,J,M,P,Q,S],[B,J,M,P,Q,S,U],[B,J,M,P,Q,U],[B,J,M,P,R],[B,J,M,P,R,S],[B,J,M,P,R,S,U],[B,J,M,P,R,U],[B,J,M,P,S],[B,J,M,P,S,U],[B,J,M,P,U],[B,J,M,Q],[B,J,M,Q,R],[B,J,M,R],[B,J,Q],[B,J,Q,R],[B,J,R],[C,D,E,F,H,J,M,N,P,Q,R,S,U],[C,D,E,F,H,J,M,N,P,Q,R,U],[C,D,E,F,H,J,M,N,P,Q,S,U],[C,D,E,F,H,J,M,N,P,Q,U],[C,D,E,F,H,J,M,N,P,R,S,U],[C,D,E,F,H,J,M,N,P,R,U],[C,D,E,F,H,J,M,N,P,S,U],[C,D,E,F,H,J,M,N,P,U],[C,D,E,F,H,J,M,P,Q,R,S,U],[C,D,E,F,H,J,M,P,Q,R,U],[C,D,E,F,H,J,M,P,Q,S],[C,D,E,F,H,J,M,P,Q,S,U],[C,D,E,F,H,J,M,P,Q,U],[C,D,E,F,H,J,M,P,R,S,U],[C,D,E,F,H,J,M,P,R,U],[C,D,E,F,H,J,M,P,S,U],[C,D,E,F,H,J,M,P,U],[C,D,E,F,J],[C,D,E,F,J,M],[C,D,E,F,J,M,N,P,Q,R,S,U],[C,D,E,F,J,M,N,P,Q,R,U],[C,D,E,F,J,M,N,P,Q,S,U],[C,D,E,F,J,M,N,P,Q,U],[C,D,E,F,J,M,N,P,R,S,U],[C,D,E,F,J,M,N,P,R,U],[C,D,E,F,J,M,N,P,S,U],[C,D,E,F,J,M,N,P,U],[C,D,E,F,J,M,P],[C,D,E,F,J,M,P,Q],[C,D,E,F,J,M,P,Q,R],[C,D,E,F,J,M,P,Q,R,S],[C,D,E,F,J,M,P,Q,R,S,U],[C,D,E,F,J,M,P,Q,R,U],[C,D,E,F,J,M,P,Q,S],[C,D,E,F,J,M,P,Q,S,U],[C,D,E,F,J,M,P,Q,U],[C,D,E,F,J,M,P,R],[C,D,E,F,J,M,P,R,S],[C,D,E,F,J,M,P,R,S,U],[C,D,E,F,J,M,P,R,U],[C,D,E,F,J,M,P,S],[C,D,E,F,J,M,P,S,U],[C,D,E,F,J,M,P,U],[C,D,E,F,J,M,Q],[C,D,E,F,J,M,Q,R],[C,D,E,F,J,M,R],[C,D,E,F,J,Q],[C,D,E,F,J,Q,R],[C,D,E,F,J,R],[C,D,E,H,J,M,N,P,Q,R,S,U],[C,D,E,H,J,M,N,P,Q,R,U],[C,D,E,H,J,M,N,P,Q,S,U],[C,D,E,H,J,M,N,P,Q,U],[C,D,E,H,J,M,N,P,R,S,U],[C,D,E,H,J,M,N,P,R,U],[C,D,E,H,J,M,N,P,S,U],[C,D,E,H,J,M,N,P,U],[C,D,E,H,J,M,P,Q,R,S,U],[C,D,E,H,J,M,P,Q,R,U],[C,D,E,H,J,M,P,Q,S,U],[C,D,E,H,J,M,P,Q,U],[C,D,E,H,J,M,P,R,S,U],[C,D,E,H,J,M,P,R,U],[C,D,E,H,J,M,P,S],[C,D,E,H,J,M,P,S,U],[C,D,E,H,J,M,P,U],[C,D,E,J],[C,D,E,J,M],[C,D,E,J,M,N,P,Q,R,S,U],[C,D,E,J,M,N,P,Q,R,U],[C,D,E,J,M,N,P,Q,S,U],[C,D,E,J,M,N,P,Q,U],[C,D,E,J,M,N,P,R,S,U],[C,D,E,J,M,N,P,R,U],[C,D,E,J,M,N,P,S,U],[C,D,E,J,M,N,P,U],[C,D,E,J,M,P],[C,D,E,J,M,P,Q],[C,D,E,J,M,P,Q,R],[C,D,E,J,M,P,Q,R,S],[C,D,E,J,M,P,Q,R,S,U],[C,D,E,J,M,P,Q,R,U],[C,D,E,J,M,P,Q,S],[C,D,E,J,M,P,Q,S,U],[C,D,E,J,M,P,Q,U],[C,D,E,J,M,P,R],[C,D,E,J,M,P,R,S],[C,D,E,J,M,P,R,S,U],[C,D,E,J,M,P,R,U],[C,D,E,J,M,P,S],[C,D,E,J,M,P,S,U],[C,D,E,J,M,P,U],[C,D,E,J,M,Q],[C,D,E,J,M,Q,R],[C,D,E,J,M,R],[C,D,E,J,Q],[C,D,E,J,Q,R],[C,D,E,J,R],[C,D,F,H,J,M,N,P,Q,R,S,U],[C,D,F,H,J,M,N,P,Q,R,U],[C,D,F,H,J,M,N,P,Q,S,U],[C,D,F,H,J,M,N,P,Q,U],[C,D,F,H,J,M,N,P,R,S,U],[C,D,F,H,J,M,N,P,R,U],[C,D,F,H,J,M,N,P,S,U],[C,D,F,H,J,M,N,P,U],[C,D,F,H,J,M,P,Q,R,S,U],[C,D,F,H,J,M,P,Q,R,U],[C,D,F,H,J,M,P,Q,S],[C,D,F,H,J,M,P,Q,S,U],[C,D,F,H,J,M,P,Q,U],[C,D,F,H,J,M,P,R,S,U],[C,D,F,H,J,M,P,R,U],[C,D,F,H,J,M,P,S,U],[C,D,F,H,J,M,P,U],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N,P,Q,R,S,U],[C,D,F,J,M,N,P,Q,R,U],[C,D,F,J,M,N,P,Q,S,U],[C,D,F,J,M,N,P,Q,U],[C,D,F,J,M,N,P,R,S,U],[C,D,F,J,M,N,P,R,U],[C,D,F,J,M,N,P,S,U],[C,D,F,J,M,N,P,U],[C,D,F,J,M,P],[C,D,F,J,M,P,Q],[C,D,F,J,M,P,Q,R],[C,D,F,J,M,P,Q,R,S],[C,D,F,J,M,P,Q,R,S,U],[C,D,F,J,M,P,Q,R,U],[C,D,F,J,M,P,Q,S],[C,D,F,J,M,P,Q,S,U],[C,D,F,J,M,P,Q,U],[C,D,F,J,M,P,R],[C,D,F,J,M,P,R,S],[C,D,F,J,M,P,R,S,U],[C,D,F,J,M,P,R,U],[C,D,F,J,M,P,S],[C,D,F,J,M,P,S,U],[C,D,F,J,M,P,U],[C,D,F,J,M,Q],[C,D,F,J,M,Q,R],[C,D,F,J,M,R],[C,D,F,J,Q],[C,D,F,J,Q,R],[C,D,F,J,R],[C,D,H,J,M,N,P,Q,R,S,U],[C,D,H,J,M,N,P,Q,R,U],[C,D,H,J,M,N,P,Q,S,U],[C,D,H,J,M,N,P,Q,U],[C,D,H,J,M,N,P,R,S,U],[C,D,H,J,M,N,P,R,U],[C,D,H,J,M,N,P,S,U],[C,D,H,J,M,N,P,U],[C,D,H,J,M,P,Q,R,S,U],[C,D,H,J,M,P,Q,R,U],[C,D,H,J,M,P,Q,S,U],[C,D,H,J,M,P,Q,U],[C,D,H,J,M,P,R,S,U],[C,D,H,J,M,P,R,U],[C,D,H,J,M,P,S],[C,D,H,J,M,P,S,U],[C,D,H,J,M,P,U],[C,D,J],[C,D,J,M],[C,D,J,M,N,P,Q,R,S,U],[C,D,J,M,N,P,Q,R,U],[C,D,J,M,N,P,Q,S,U],[C,D,J,M,N,P,Q,U],[C,D,J,M,N,P,R,S,U],[C,D,J,M,N,P,R,U],[C,D,J,M,N,P,S,U],[C,D,J,M,N,P,U],[C,D,J,M,P],[C,D,J,M,P,Q],[C,D,J,M,P,Q,R],[C,D,J,M,P,Q,R,S],[C,D,J,M,P,Q,R,S,U],[C,D,J,M,P,Q,R,U],[C,D,J,M,P,Q,S],[C,D,J,M,P,Q,S,U],[C,D,J,M,P,Q,U],[C,D,J,M,P,R],[C,D,J,M,P,R,S],[C,D,J,M,P,R,S,U],[C,D,J,M,P,R,U],[C,D,J,M,P,S],[C,D,J,M,P,S,U],[C,D,J,M,P,U],[C,D,J,M,Q],[C,D,J,M,Q,R],[C,D,J,M,R],[C,D,J,Q],[C,D,J,Q,R],[C,D,J,R],[C,E,F,H,J,M,N,P,Q,R,S,U],[C,E,F,H,J,M,N,P,Q,R,U],[C,E,F,H,J,M,N,P,Q,S,U],[C,E,F,H,J,M,N,P,Q,U],[C,E,F,H,J,M,N,P,R,S,U],[C,E,F,H,J,M,N,P,R,U],[C,E,F,H,J,M,N,P,S,U],[C,E,F,H,J,M,N,P,U],[C,E,F,H,J,M,P,Q,R,S,U],[C,E,F,H,J,M,P,Q,R,U],[C,E,F,H,J,M,P,Q,S],[C,E,F,H,J,M,P,Q,S,U],[C,E,F,H,J,M,P,Q,U],[C,E,F,H,J,M,P,R,S,U],[C,E,F,H,J,M,P,R,U],[C,E,F,H,J,M,P,S,U],[C,E,F,H,J,M,P,U],[C,E,F,J],[C,E,F,J,M],[C,E,F,J,M,N,P,Q,R,S,U],[C,E,F,J,M,N,P,Q,R,U],[C,E,F,J,M,N,P,Q,S,U],[C,E,F,J,M,N,P,Q,U],[C,E,F,J,M,N,P,R,S,U],[C,E,F,J,M,N,P,R,U],[C,E,F,J,M,N,P,S,U],[C,E,F,J,M,N,P,U],[C,E,F,J,M,P],[C,E,F,J,M,P,Q],[C,E,F,J,M,P,Q,R],[C,E,F,J,M,P,Q,R,S],[C,E,F,J,M,P,Q,R,S,U],[C,E,F,J,M,P,Q,R,U],[C,E,F,J,M,P,Q,S],[C,E,F,J,M,P,Q,S,U],[C,E,F,J,M,P,Q,U],[C,E,F,J,M,P,R],[C,E,F,J,M,P,R,S],[C,E,F,J,M,P,R,S,U],[C,E,F,J,M,P,R,U],[C,E,F,J,M,P,S],[C,E,F,J,M,P,S,U],[C,E,F,J,M,P,U],[C,E,F,J,M,Q],[C,E,F,J,M,Q,R],[C,E,F,J,M,R],[C,E,F,J,Q],[C,E,F,J,Q,R],[C,E,F,J,R],[C,E,H,J,M,N,P,Q,R,S,U],[C,E,H,J,M,N,P,Q,R,U],[C,E,H,J,M,N,P,Q,S,U],[C,E,H,J,M,N,P,Q,U],[C,E,H,J,M,N,P,R,S,U],[C,E,H,J,M,N,P,R,U],[C,E,H,J,M,N,P,S,U],[C,E,H,J,M,N,P,U],[C,E,H,J,M,P,Q,R,S,U],[C,E,H,J,M,P,Q,R,U],[C,E,H,J,M,P,Q,S,U],[C,E,H,J,M,P,Q,U],[C,E,H,J,M,P,R,S,U],[C,E,H,J,M,P,R,U],[C,E,H,J,M,P,S],[C,E,H,J,M,P,S,U],[C,E,H,J,M,P,U],[C,E,J],[C,E,J,M],[C,E,J,M,N,P,Q,R,S,U],[C,E,J,M,N,P,Q,R,U],[C,E,J,M,N,P,Q,S,U],[C,E,J,M,N,P,Q,U],[C,E,J,M,N,P,R,S,U],[C,E,J,M,N,P,R,U],[C,E,J,M,N,P,S,U],[C,E,J,M,N,P,U],[C,E,J,M,P],[C,E,J,M,P,Q],[C,E,J,M,P,Q,R],[C,E,J,M,P,Q,R,S],[C,E,J,M,P,Q,R,S,U],[C,E,J,M,P,Q,R,U],[C,E,J,M,P,Q,S],[C,E,J,M,P,Q,S,U],[C,E,J,M,P,Q,U],[C,E,J,M,P,R],[C,E,J,M,P,R,S],[C,E,J,M,P,R,S,U],[C,E,J,M,P,R,U],[C,E,J,M,P,S],[C,E,J,M,P,S,U],[C,E,J,M,P,U],[C,E,J,M,Q],[C,E,J,M,Q,R],[C,E,J,M,R],[C,E,J,Q],[C,E,J,Q,R],[C,E,J,R],[C,F,H,J,M,N,P,Q,R,S,U],[C,F,H,J,M,N,P,Q,R,U],[C,F,H,J,M,N,P,Q,S,U],[C,F,H,J,M,N,P,Q,U],[C,F,H,J,M,N,P,R,S,U],[C,F,H,J,M,N,P,R,U],[C,F,H,J,M,N,P,S,U],[C,F,H,J,M,N,P,U],[C,F,H,J,M,P,Q,R,S,U],[C,F,H,J,M,P,Q,R,U],[C,F,H,J,M,P,Q,S],[C,F,H,J,M,P,Q,S,U],[C,F,H,J,M,P,Q,U],[C,F,H,J,M,P,R,S,U],[C,F,H,J,M,P,R,U],[C,F,H,J,M,P,S,U],[C,F,H,J,M,P,U],[C,F,J],[C,F,J,M],[C,F,J,M,N,P,Q,R,S,U],[C,F,J,M,N,P,Q,R,U],[C,F,J,M,N,P,Q,S,U],[C,F,J,M,N,P,Q,U],[C,F,J,M,N,P,R,S,U],[C,F,J,M,N,P,R,U],[C,F,J,M,N,P,S,U],[C,F,J,M,N,P,U],[C,F,J,M,P],[C,F,J,M,P,Q],[C,F,J,M,P,Q,R],[C,F,J,M,P,Q,R,S],[C,F,J,M,P,Q,R,S,U],[C,F,J,M,P,Q,R,U],[C,F,J,M,P,Q,S],[C,F,J,M,P,Q,S,U],[C,F,J,M,P,Q,U],[C,F,J,M,P,R],[C,F,J,M,P,R,S],[C,F,J,M,P,R,S,U],[C,F,J,M,P,R,U],[C,F,J,M,P,S],[C,F,J,M,P,S,U],[C,F,J,M,P,U],[C,F,J,M,Q],[C,F,J,M,Q,R],[C,F,J,M,R],[C,F,J,Q],[C,F,J,Q,R],[C,F,J,R],[C,H,J,M,N,P,Q,R,S,U],[C,H,J,M,N,P,Q,R,U],[C,H,J,M,N,P,Q,S,U],[C,H,J,M,N,P,Q,U],[C,H,J,M,N,P,R,S,U],[C,H,J,M,N,P,R,U],[C,H,J,M,N,P,S,U],[C,H,J,M,N,P,U],[C,H,J,M,P,Q,R,S,U],[C,H,J,M,P,Q,R,U],[C,H,J,M,P,Q,S,U],[C,H,J,M,P,Q,U],[C,H,J,M,P,R,S,U],[C,H,J,M,P,R,U],[C,H,J,M,P,S],[C,H,J,M,P,S,U],[C,H,J,M,P,U],[C,J],[C,J,M],[C,J,M,N,P,Q,R,S,U],[C,J,M,N,P,Q,R,U],[C,J,M,N,P,Q,S,U],[C,J,M,N,P,Q,U],[C,J,M,N,P,R,S,U],[C,J,M,N,P,R,U],[C,J,M,N,P,S,U],[C,J,M,N,P,U],[C,J,M,P],[C,J,M,P,Q],[C,J,M,P,Q,R],[C,J,M,P,Q,R,S],[C,J,M,P,Q,R,S,U],[C,J,M,P,Q,R,U],[C,J,M,P,Q,S],[C,J,M,P,Q,S,U],[C,J,M,P,Q,U],[C,J,M,P,R],[C,J,M,P,R,S],[C,J,M,P,R,S,U],[C,J,M,P,R,U],[C,J,M,P,S],[C,J,M,P,S,U],[C,J,M,P,U],[C,J,M,Q],[C,J,M,Q,R],[C,J,M,R],[C,J,Q],[C,J,Q,R],[C,J,R],[D],[D,E,F,H,J,M,N,P,Q,R,S,U],[D,E,F,H,J,M,N,P,Q,R,U],[D,E,F,H,J,M,N,P,Q,S,U],[D,E,F,H,J,M,N,P,Q,U],[D,E,F,H,J,M,N,P,R,S,U],[D,E,F,H,J,M,N,P,R,U],[D,E,F,H,J,M,N,P,S,U],[D,E,F,H,J,M,N,P,U],[D,E,F,H,J,M,P,Q,R,S,U],[D,E,F,H,J,M,P,Q,R,U],[D,E,F,H,J,M,P,Q,S],[D,E,F,H,J,M,P,Q,S,U],[D,E,F,H,J,M,P,Q,U],[D,E,F,H,J,M,P,R,S,U],[D,E,F,H,J,M,P,R,U],[D,E,F,H,J,M,P,S,U],[D,E,F,H,J,M,P,U],[D,E,F,J],[D,E,F,J,M],[D,E,F,J,M,N,P,Q,R,S,U],[D,E,F,J,M,N,P,Q,R,U],[D,E,F,J,M,N,P,Q,S,U],[D,E,F,J,M,N,P,Q,U],[D,E,F,J,M,N,P,R,S,U],[D,E,F,J,M,N,P,R,U],[D,E,F,J,M,N,P,S,U],[D,E,F,J,M,N,P,U],[D,E,F,J,M,P],[D,E,F,J,M,P,Q],[D,E,F,J,M,P,Q,R],[D,E,F,J,M,P,Q,R,S],[D,E,F,J,M,P,Q,R,S,U],[D,E,F,J,M,P,Q,R,U],[D,E,F,J,M,P,Q,S],[D,E,F,J,M,P,Q,S,U],[D,E,F,J,M,P,Q,U],[D,E,F,J,M,P,R],[D,E,F,J,M,P,R,S],[D,E,F,J,M,P,R,S,U],[D,E,F,J,M,P,R,U],[D,E,F,J,M,P,S],[D,E,F,J,M,P,S,U],[D,E,F,J,M,P,U],[D,E,F,J,M,Q],[D,E,F,J,M,Q,R],[D,E,F,J,M,R],[D,E,F,J,Q],[D,E,F,J,Q,R],[D,E,F,J,R],[D,E,H,J,M,N,P,Q,R,S,U],[D,E,H,J,M,N,P,Q,R,U],[D,E,H,J,M,N,P,Q,S,U],[D,E,H,J,M,N,P,Q,U],[D,E,H,J,M,N,P,R,S,U],[D,E,H,J,M,N,P,R,U],[D,E,H,J,M,N,P,S,U],[D,E,H,J,M,N,P,U],[D,E,H,J,M,P,Q,R,S,U],[D,E,H,J,M,P,Q,R,U],[D,E,H,J,M,P,Q,S,U],[D,E,H,J,M,P,Q,U],[D,E,H,J,M,P,R,S,U],[D,E,H,J,M,P,R,U],[D,E,H,J,M,P,S],[D,E,H,J,M,P,S,U],[D,E,H,J,M,P,U],[D,E,J],[D,E,J,M],[D,E,J,M,N,P,Q,R,S,U],[D,E,J,M,N,P,Q,R,U],[D,E,J,M,N,P,Q,S,U],[D,E,J,M,N,P,Q,U],[D,E,J,M,N,P,R,S,U],[D,E,J,M,N,P,R,U],[D,E,J,M,N,P,S,U],[D,E,J,M,N,P,U],[D,E,J,M,P],[D,E,J,M,P,Q],[D,E,J,M,P,Q,R],[D,E,J,M,P,Q,R,S],[D,E,J,M,P,Q,R,S,U],[D,E,J,M,P,Q,R,U],[D,E,J,M,P,Q,S],[D,E,J,M,P,Q,S,U],[D,E,J,M,P,Q,U],[D,E,J,M,P,R],[D,E,J,M,P,R,S],[D,E,J,M,P,R,S,U],[D,E,J,M,P,R,U],[D,E,J,M,P,S],[D,E,J,M,P,S,U],[D,E,J,M,P,U],[D,E,J,M,Q],[D,E,J,M,Q,R],[D,E,J,M,R],[D,E,J,Q],[D,E,J,Q,R],[D,E,J,R],[D,F,H,J,M,N,P,Q,R,S,U],[D,F,H,J,M,N,P,Q,R,U],[D,F,H,J,M,N,P,Q,S,U],[D,F,H,J,M,N,P,Q,U],[D,F,H,J,M,N,P,R,S,U],[D,F,H,J,M,N,P,R,U],[D,F,H,J,M,N,P,S,U],[D,F,H,J,M,N,P,U],[D,F,H,J,M,P,Q,R,S,U],[D,F,H,J,M,P,Q,R,U],[D,F,H,J,M,P,Q,S,U],[D,F,H,J,M,P,Q,U],[D,F,H,J,M,P,R,S,U],[D,F,H,J,M,P,R,U],[D,F,H,J,M,P,S,U],[D,F,H,J,M,P,U],[D,F,H,M,N,P,Q,S,U],[D,F,H,M,N,P,S,U],[D,F,H,M,N,P,U],[D,F,H,M,P,Q,S],[D,F,H,M,P,S,U],[D,F,H,M,P,U],[D,F,J,M,N,P,Q,R,S,U],[D,F,J,M,N,P,Q,R,U],[D,F,J,M,N,P,Q,S,U],[D,F,J,M,N,P,Q,U],[D,F,J,M,N,P,R,S,U],[D,F,J,M,N,P,R,U],[D,F,J,M,N,P,S,U],[D,F,J,M,N,P,U],[D,F,J,M,P,Q],[D,F,J,M,P,Q,R],[D,F,J,M,P,Q,R,S],[D,F,J,M,P,Q,R,S,U],[D,F,J,M,P,Q,R,U],[D,F,J,M,P,Q,S],[D,F,J,M,P,Q,S,U],[D,F,J,M,P,Q,U],[D,F,J,M,P,R],[D,F,J,M,P,R,S],[D,F,J,M,P,R,S,U],[D,F,J,M,P,R,U],[D,F,J,M,P,S,U],[D,F,J,M,P,U],[D,F,M,N,P,Q,U],[D,F,M,N,P,S,U],[D,F,M,N,P,U],[D,F,M,P,Q],[D,F,M,P,S,U],[D,F,M,P,U],[D,H,J,M,N,P,Q,R,S,U],[D,H,J,M,N,P,Q,R,U],[D,H,J,M,N,P,Q,S,U],[D,H,J,M,N,P,Q,U],[D,H,J,M,N,P,R,S,U],[D,H,J,M,N,P,R,U],[D,H,J,M,N,P,S,U],[D,H,J,M,N,P,U],[D,H,J,M,P,Q,R,S,U],[D,H,J,M,P,Q,R,U],[D,H,J,M,P,Q,S,U],[D,H,J,M,P,Q,U],[D,H,J,M,P,R,S,U],[D,H,J,M,P,R,U],[D,H,J,M,P,S,U],[D,H,J,M,P,U],[D,H,M,N,P,S,U],[D,H,M,N,P,U],[D,H,M,P,S],[D,H,M,P,S,U],[D,H,M,P,U],[D,J,M,N,P,Q,R,S,U],[D,J,M,N,P,Q,R,U],[D,J,M,N,P,Q,S,U],[D,J,M,N,P,Q,U],[D,J,M,N,P,R,S,U],[D,J,M,N,P,R,U],[D,J,M,N,P,S,U],[D,J,M,N,P,U],[D,J,M,P,Q],[D,J,M,P,Q,R],[D,J,M,P,Q,R,S],[D,J,M,P,Q,R,S,U],[D,J,M,P,Q,R,U],[D,J,M,P,Q,S],[D,J,M,P,Q,S,U],[D,J,M,P,Q,U],[D,J,M,P,R],[D,J,M,P,R,S],[D,J,M,P,R,S,U],[D,J,M,P,R,U],[D,J,M,P,S,U],[D,J,M,P,U],[D,M],[D,M,N,P,S,U],[D,M,N,P,U],[D,M,P],[D,M,P,S],[D,M,P,S,U],[D,M,P,U],[E,F,H,J,M,N,P,Q,R,S,U],[E,F,H,J,M,N,P,Q,R,U],[E,F,H,J,M,N,P,Q,S,U],[E,F,H,J,M,N,P,Q,U],[E,F,H,J,M,N,P,R,S,U],[E,F,H,J,M,N,P,R,U],[E,F,H,J,M,N,P,S,U],[E,F,H,J,M,N,P,U],[E,F,H,J,M,P,Q,R,S,U],[E,F,H,J,M,P,Q,R,U],[E,F,H,J,M,P,Q,S],[E,F,H,J,M,P,Q,S,U],[E,F,H,J,M,P,Q,U],[E,F,H,J,M,P,R,S,U],[E,F,H,J,M,P,R,U],[E,F,H,J,M,P,S,U],[E,F,H,J,M,P,U],[E,F,J],[E,F,J,M],[E,F,J,M,N,P,Q,R,S,U],[E,F,J,M,N,P,Q,R,U],[E,F,J,M,N,P,Q,S,U],[E,F,J,M,N,P,Q,U],[E,F,J,M,N,P,R,S,U],[E,F,J,M,N,P,R,U],[E,F,J,M,N,P,S,U],[E,F,J,M,N,P,U],[E,F,J,M,P],[E,F,J,M,P,Q],[E,F,J,M,P,Q,R],[E,F,J,M,P,Q,R,S],[E,F,J,M,P,Q,R,S,U],[E,F,J,M,P,Q,R,U],[E,F,J,M,P,Q,S],[E,F,J,M,P,Q,S,U],[E,F,J,M,P,Q,U],[E,F,J,M,P,R],[E,F,J,M,P,R,S],[E,F,J,M,P,R,S,U],[E,F,J,M,P,R,U],[E,F,J,M,P,S],[E,F,J,M,P,S,U],[E,F,J,M,P,U],[E,F,J,M,Q],[E,F,J,M,Q,R],[E,F,J,M,R],[E,F,J,Q],[E,F,J,Q,R],[E,F,J,R],[E,H,J,M,N,P,Q,R,S,U],[E,H,J,M,N,P,Q,R,U],[E,H,J,M,N,P,Q,S,U],[E,H,J,M,N,P,Q,U],[E,H,J,M,N,P,R,S,U],[E,H,J,M,N,P,R,U],[E,H,J,M,N,P,S,U],[E,H,J,M,N,P,U],[E,H,J,M,P,Q,R,S,U],[E,H,J,M,P,Q,R,U],[E,H,J,M,P,Q,S,U],[E,H,J,M,P,Q,U],[E,H,J,M,P,R,S,U],[E,H,J,M,P,R,U],[E,H,J,M,P,S],[E,H,J,M,P,S,U],[E,H,J,M,P,U],[E,J],[E,J,M],[E,J,M,N,P,Q,R,S,U],[E,J,M,N,P,Q,R,U],[E,J,M,N,P,Q,S,U],[E,J,M,N,P,Q,U],[E,J,M,N,P,R,S,U],[E,J,M,N,P,R,U],[E,J,M,N,P,S,U],[E,J,M,N,P,U],[E,J,M,P],[E,J,M,P,Q],[E,J,M,P,Q,R],[E,J,M,P,Q,R,S],[E,J,M,P,Q,R,S,U],[E,J,M,P,Q,R,U],[E,J,M,P,Q,S],[E,J,M,P,Q,S,U],[E,J,M,P,Q,U],[E,J,M,P,R],[E,J,M,P,R,S],[E,J,M,P,R,S,U],[E,J,M,P,R,U],[E,J,M,P,S],[E,J,M,P,S,U],[E,J,M,P,U],[E,J,M,Q],[E,J,M,Q,R],[E,J,M,R],[E,J,Q],[E,J,Q,R],[E,J,R],[F],[F,H,J,M,N,P,Q,R,S,U],[F,H,J,M,N,P,Q,R,U],[F,H,J,M,N,P,Q,S,U],[F,H,J,M,N,P,Q,U],[F,H,J,M,N,P,R,S,U],[F,H,J,M,N,P,R,U],[F,H,J,M,N,P,S,U],[F,H,J,M,N,P,U],[F,H,J,M,P,Q,R,S,U],[F,H,J,M,P,Q,R,U],[F,H,J,M,P,Q,S,U],[F,H,J,M,P,Q,U],[F,H,J,M,P,R,S,U],[F,H,J,M,P,R,U],[F,H,J,M,P,S,U],[F,H,J,M,P,U],[F,H,M,N,P,Q,S,U],[F,H,M,N,P,S,U],[F,H,M,N,P,U],[F,H,M,P,Q,S],[F,H,M,P,S,U],[F,H,M,P,U],[F,J],[F,J,M,N,P,Q,R,S,U],[F,J,M,N,P,Q,R,U],[F,J,M,N,P,Q,S,U],[F,J,M,N,P,Q,U],[F,J,M,N,P,R,S,U],[F,J,M,N,P,R,U],[F,J,M,N,P,S,U],[F,J,M,N,P,U],[F,J,M,P,Q],[F,J,M,P,Q,R],[F,J,M,P,Q,R,S],[F,J,M,P,Q,R,S,U],[F,J,M,P,Q,R,U],[F,J,M,P,Q,S],[F,J,M,P,Q,S,U],[F,J,M,P,Q,U],[F,J,M,P,R],[F,J,M,P,R,S],[F,J,M,P,R,S,U],[F,J,M,P,R,U],[F,J,M,P,S,U],[F,J,M,P,U],[F,J,Q],[F,J,Q,R],[F,J,R],[F,M,N,P,Q,U],[F,M,N,P,S,U],[F,M,N,P,U],[F,M,P,Q],[F,M,P,S,U],[F,M,P,U],[F,Q],[H,J,M,N,P,Q,R,S,U],[H,J,M,N,P,Q,R,U],[H,J,M,N,P,Q,S,U],[H,J,M,N,P,Q,U],[H,J,M,N,P,R,S,U],[H,J,M,N,P,R,U],[H,J,M,N,P,S,U],[H,J,M,N,P,U],[H,J,M,P,Q,R,S,U],[H,J,M,P,Q,R,U],[H,J,M,P,Q,S,U],[H,J,M,P,Q,U],[H,J,M,P,R,S,U],[H,J,M,P,R,U],[H,J,M,P,S,U],[H,J,M,P,U],[H,M,N,P,S,U],[H,M,N,P,U],[H,M,P,S],[H,M,P,S,U],[H,M,P,U],[I,J],[I,J,V],[J],[J,M,N,P,Q,R,S,U],[J,M,N,P,Q,R,U],[J,M,N,P,Q,S,U],[J,M,N,P,Q,U],[J,M,N,P,R,S,U],[J,M,N,P,R,U],[J,M,N,P,S,U],[J,M,N,P,U],[J,M,P,Q],[J,M,P,Q,R],[J,M,P,Q,R,S],[J,M,P,Q,R,S,U],[J,M,P,Q,R,U],[J,M,P,Q,S],[J,M,P,Q,S,U],[J,M,P,Q,U],[J,M,P,R],[J,M,P,R,S],[J,M,P,R,S,U],[J,M,P,R,U],[J,M,P,S,U],[J,M,P,U],[J,Q],[J,Q,R],[J,R],[M],[M,N,P,S,U],[M,N,P,U],[M,P],[M,P,S],[M,P,S,U],[M,P,U]]),ground([G,K,L,O,T]),linear(I);mshare([[B,C,D,F,G,H,J,M,N,P,Q,R,S,U],[B,C,D,F,G,H,J,M,N,P,Q,R,U],[B,C,D,F,G,H,J,M,N,P,Q,S,U],[B,C,D,F,G,H,J,M,N,P,Q,U],[B,C,D,F,G,H,J,M,N,P,R,S,U],[B,C,D,F,G,H,J,M,N,P,R,U],[B,C,D,F,G,H,J,M,N,P,S,U],[B,C,D,F,G,H,J,M,N,P,U],[B,C,D,F,G,H,J,M,P,Q,R,S],[B,C,D,F,G,H,J,M,P,Q,R,S,U],[B,C,D,F,G,H,J,M,P,Q,R,U],[B,C,D,F,G,H,J,M,P,Q,S,U],[B,C,D,F,G,H,J,M,P,Q,U],[B,C,D,F,G,H,J,M,P,R,S,U],[B,C,D,F,G,H,J,M,P,R,U],[B,C,D,F,G,H,J,M,P,S,U],[B,C,D,F,G,H,J,M,P,U],[B,C,D,F,G,J],[B,C,D,F,G,J,M],[B,C,D,F,G,J,M,N,P,Q,R,S,U],[B,C,D,F,G,J,M,N,P,Q,R,U],[B,C,D,F,G,J,M,N,P,Q,S,U],[B,C,D,F,G,J,M,N,P,Q,U],[B,C,D,F,G,J,M,N,P,R,S,U],[B,C,D,F,G,J,M,N,P,R,U],[B,C,D,F,G,J,M,N,P,S,U],[B,C,D,F,G,J,M,N,P,U],[B,C,D,F,G,J,M,P],[B,C,D,F,G,J,M,P,Q],[B,C,D,F,G,J,M,P,Q,R],[B,C,D,F,G,J,M,P,Q,R,S],[B,C,D,F,G,J,M,P,Q,R,S,U],[B,C,D,F,G,J,M,P,Q,R,U],[B,C,D,F,G,J,M,P,Q,S],[B,C,D,F,G,J,M,P,Q,S,U],[B,C,D,F,G,J,M,P,Q,U],[B,C,D,F,G,J,M,P,R],[B,C,D,F,G,J,M,P,R,S],[B,C,D,F,G,J,M,P,R,S,U],[B,C,D,F,G,J,M,P,R,U],[B,C,D,F,G,J,M,P,S],[B,C,D,F,G,J,M,P,S,U],[B,C,D,F,G,J,M,P,U],[B,C,D,F,G,J,M,Q],[B,C,D,F,G,J,M,Q,R],[B,C,D,F,G,J,M,R],[B,C,D,F,G,J,Q],[B,C,D,F,G,J,Q,R],[B,C,D,F,G,J,R],[B,C,D,F,H,J,M,N,P,Q,R,S,U],[B,C,D,F,H,J,M,N,P,Q,R,U],[B,C,D,F,H,J,M,N,P,Q,S,U],[B,C,D,F,H,J,M,N,P,Q,U],[B,C,D,F,H,J,M,N,P,R,S,U],[B,C,D,F,H,J,M,N,P,R,U],[B,C,D,F,H,J,M,N,P,S,U],[B,C,D,F,H,J,M,N,P,U],[B,C,D,F,H,J,M,P,Q,R,S,U],[B,C,D,F,H,J,M,P,Q,R,U],[B,C,D,F,H,J,M,P,Q,S],[B,C,D,F,H,J,M,P,Q,S,U],[B,C,D,F,H,J,M,P,Q,U],[B,C,D,F,H,J,M,P,R,S,U],[B,C,D,F,H,J,M,P,R,U],[B,C,D,F,H,J,M,P,S,U],[B,C,D,F,H,J,M,P,U],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N,P,Q,R,S,U],[B,C,D,F,J,M,N,P,Q,R,U],[B,C,D,F,J,M,N,P,Q,S,U],[B,C,D,F,J,M,N,P,Q,U],[B,C,D,F,J,M,N,P,R,S,U],[B,C,D,F,J,M,N,P,R,U],[B,C,D,F,J,M,N,P,S,U],[B,C,D,F,J,M,N,P,U],[B,C,D,F,J,M,P],[B,C,D,F,J,M,P,Q],[B,C,D,F,J,M,P,Q,R],[B,C,D,F,J,M,P,Q,R,S],[B,C,D,F,J,M,P,Q,R,S,U],[B,C,D,F,J,M,P,Q,R,U],[B,C,D,F,J,M,P,Q,S],[B,C,D,F,J,M,P,Q,S,U],[B,C,D,F,J,M,P,Q,U],[B,C,D,F,J,M,P,R],[B,C,D,F,J,M,P,R,S],[B,C,D,F,J,M,P,R,S,U],[B,C,D,F,J,M,P,R,U],[B,C,D,F,J,M,P,S],[B,C,D,F,J,M,P,S,U],[B,C,D,F,J,M,P,U],[B,C,D,F,J,M,Q],[B,C,D,F,J,M,Q,R],[B,C,D,F,J,M,R],[B,C,D,F,J,Q],[B,C,D,F,J,Q,R],[B,C,D,F,J,R],[B,C,D,G,H,J,M,N,P,Q,R,S,U],[B,C,D,G,H,J,M,N,P,Q,R,U],[B,C,D,G,H,J,M,N,P,Q,S,U],[B,C,D,G,H,J,M,N,P,Q,U],[B,C,D,G,H,J,M,N,P,R,S,U],[B,C,D,G,H,J,M,N,P,R,U],[B,C,D,G,H,J,M,N,P,S,U],[B,C,D,G,H,J,M,N,P,U],[B,C,D,G,H,J,M,P,Q,R,S,U],[B,C,D,G,H,J,M,P,Q,R,U],[B,C,D,G,H,J,M,P,Q,S,U],[B,C,D,G,H,J,M,P,Q,U],[B,C,D,G,H,J,M,P,R,S],[B,C,D,G,H,J,M,P,R,S,U],[B,C,D,G,H,J,M,P,R,U],[B,C,D,G,H,J,M,P,S,U],[B,C,D,G,H,J,M,P,U],[B,C,D,G,J],[B,C,D,G,J,M],[B,C,D,G,J,M,N,P,Q,R,S,U],[B,C,D,G,J,M,N,P,Q,R,U],[B,C,D,G,J,M,N,P,Q,S,U],[B,C,D,G,J,M,N,P,Q,U],[B,C,D,G,J,M,N,P,R,S,U],[B,C,D,G,J,M,N,P,R,U],[B,C,D,G,J,M,N,P,S,U],[B,C,D,G,J,M,N,P,U],[B,C,D,G,J,M,P],[B,C,D,G,J,M,P,Q],[B,C,D,G,J,M,P,Q,R],[B,C,D,G,J,M,P,Q,R,S],[B,C,D,G,J,M,P,Q,R,S,U],[B,C,D,G,J,M,P,Q,R,U],[B,C,D,G,J,M,P,Q,S],[B,C,D,G,J,M,P,Q,S,U],[B,C,D,G,J,M,P,Q,U],[B,C,D,G,J,M,P,R],[B,C,D,G,J,M,P,R,S],[B,C,D,G,J,M,P,R,S,U],[B,C,D,G,J,M,P,R,U],[B,C,D,G,J,M,P,S],[B,C,D,G,J,M,P,S,U],[B,C,D,G,J,M,P,U],[B,C,D,G,J,M,Q],[B,C,D,G,J,M,Q,R],[B,C,D,G,J,M,R],[B,C,D,G,J,Q],[B,C,D,G,J,Q,R],[B,C,D,G,J,R],[B,C,D,H,J,M,N,P,Q,R,S,U],[B,C,D,H,J,M,N,P,Q,R,U],[B,C,D,H,J,M,N,P,Q,S,U],[B,C,D,H,J,M,N,P,Q,U],[B,C,D,H,J,M,N,P,R,S,U],[B,C,D,H,J,M,N,P,R,U],[B,C,D,H,J,M,N,P,S,U],[B,C,D,H,J,M,N,P,U],[B,C,D,H,J,M,P,Q,R,S,U],[B,C,D,H,J,M,P,Q,R,U],[B,C,D,H,J,M,P,Q,S,U],[B,C,D,H,J,M,P,Q,U],[B,C,D,H,J,M,P,R,S,U],[B,C,D,H,J,M,P,R,U],[B,C,D,H,J,M,P,S],[B,C,D,H,J,M,P,S,U],[B,C,D,H,J,M,P,U],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N,P,Q,R,S,U],[B,C,D,J,M,N,P,Q,R,U],[B,C,D,J,M,N,P,Q,S,U],[B,C,D,J,M,N,P,Q,U],[B,C,D,J,M,N,P,R,S,U],[B,C,D,J,M,N,P,R,U],[B,C,D,J,M,N,P,S,U],[B,C,D,J,M,N,P,U],[B,C,D,J,M,P],[B,C,D,J,M,P,Q],[B,C,D,J,M,P,Q,R],[B,C,D,J,M,P,Q,R,S],[B,C,D,J,M,P,Q,R,S,U],[B,C,D,J,M,P,Q,R,U],[B,C,D,J,M,P,Q,S],[B,C,D,J,M,P,Q,S,U],[B,C,D,J,M,P,Q,U],[B,C,D,J,M,P,R],[B,C,D,J,M,P,R,S],[B,C,D,J,M,P,R,S,U],[B,C,D,J,M,P,R,U],[B,C,D,J,M,P,S],[B,C,D,J,M,P,S,U],[B,C,D,J,M,P,U],[B,C,D,J,M,Q],[B,C,D,J,M,Q,R],[B,C,D,J,M,R],[B,C,D,J,Q],[B,C,D,J,Q,R],[B,C,D,J,R],[B,C,F,G,H,J,M,N,P,Q,R,S,U],[B,C,F,G,H,J,M,N,P,Q,R,U],[B,C,F,G,H,J,M,N,P,Q,S,U],[B,C,F,G,H,J,M,N,P,Q,U],[B,C,F,G,H,J,M,N,P,R,S,U],[B,C,F,G,H,J,M,N,P,R,U],[B,C,F,G,H,J,M,N,P,S,U],[B,C,F,G,H,J,M,N,P,U],[B,C,F,G,H,J,M,P,Q,R,S],[B,C,F,G,H,J,M,P,Q,R,S,U],[B,C,F,G,H,J,M,P,Q,R,U],[B,C,F,G,H,J,M,P,Q,S,U],[B,C,F,G,H,J,M,P,Q,U],[B,C,F,G,H,J,M,P,R,S,U],[B,C,F,G,H,J,M,P,R,U],[B,C,F,G,H,J,M,P,S,U],[B,C,F,G,H,J,M,P,U],[B,C,F,G,J],[B,C,F,G,J,M],[B,C,F,G,J,M,N,P,Q,R,S,U],[B,C,F,G,J,M,N,P,Q,R,U],[B,C,F,G,J,M,N,P,Q,S,U],[B,C,F,G,J,M,N,P,Q,U],[B,C,F,G,J,M,N,P,R,S,U],[B,C,F,G,J,M,N,P,R,U],[B,C,F,G,J,M,N,P,S,U],[B,C,F,G,J,M,N,P,U],[B,C,F,G,J,M,P],[B,C,F,G,J,M,P,Q],[B,C,F,G,J,M,P,Q,R],[B,C,F,G,J,M,P,Q,R,S],[B,C,F,G,J,M,P,Q,R,S,U],[B,C,F,G,J,M,P,Q,R,U],[B,C,F,G,J,M,P,Q,S],[B,C,F,G,J,M,P,Q,S,U],[B,C,F,G,J,M,P,Q,U],[B,C,F,G,J,M,P,R],[B,C,F,G,J,M,P,R,S],[B,C,F,G,J,M,P,R,S,U],[B,C,F,G,J,M,P,R,U],[B,C,F,G,J,M,P,S],[B,C,F,G,J,M,P,S,U],[B,C,F,G,J,M,P,U],[B,C,F,G,J,M,Q],[B,C,F,G,J,M,Q,R],[B,C,F,G,J,M,R],[B,C,F,G,J,Q],[B,C,F,G,J,Q,R],[B,C,F,G,J,R],[B,C,F,H,J,M,N,P,Q,R,S,U],[B,C,F,H,J,M,N,P,Q,R,U],[B,C,F,H,J,M,N,P,Q,S,U],[B,C,F,H,J,M,N,P,Q,U],[B,C,F,H,J,M,N,P,R,S,U],[B,C,F,H,J,M,N,P,R,U],[B,C,F,H,J,M,N,P,S,U],[B,C,F,H,J,M,N,P,U],[B,C,F,H,J,M,P,Q,R,S,U],[B,C,F,H,J,M,P,Q,R,U],[B,C,F,H,J,M,P,Q,S],[B,C,F,H,J,M,P,Q,S,U],[B,C,F,H,J,M,P,Q,U],[B,C,F,H,J,M,P,R,S,U],[B,C,F,H,J,M,P,R,U],[B,C,F,H,J,M,P,S,U],[B,C,F,H,J,M,P,U],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N,P,Q,R,S,U],[B,C,F,J,M,N,P,Q,R,U],[B,C,F,J,M,N,P,Q,S,U],[B,C,F,J,M,N,P,Q,U],[B,C,F,J,M,N,P,R,S,U],[B,C,F,J,M,N,P,R,U],[B,C,F,J,M,N,P,S,U],[B,C,F,J,M,N,P,U],[B,C,F,J,M,P],[B,C,F,J,M,P,Q],[B,C,F,J,M,P,Q,R],[B,C,F,J,M,P,Q,R,S],[B,C,F,J,M,P,Q,R,S,U],[B,C,F,J,M,P,Q,R,U],[B,C,F,J,M,P,Q,S],[B,C,F,J,M,P,Q,S,U],[B,C,F,J,M,P,Q,U],[B,C,F,J,M,P,R],[B,C,F,J,M,P,R,S],[B,C,F,J,M,P,R,S,U],[B,C,F,J,M,P,R,U],[B,C,F,J,M,P,S],[B,C,F,J,M,P,S,U],[B,C,F,J,M,P,U],[B,C,F,J,M,Q],[B,C,F,J,M,Q,R],[B,C,F,J,M,R],[B,C,F,J,Q],[B,C,F,J,Q,R],[B,C,F,J,R],[B,C,G,H,J,M,N,P,Q,R,S,U],[B,C,G,H,J,M,N,P,Q,R,U],[B,C,G,H,J,M,N,P,Q,S,U],[B,C,G,H,J,M,N,P,Q,U],[B,C,G,H,J,M,N,P,R,S,U],[B,C,G,H,J,M,N,P,R,U],[B,C,G,H,J,M,N,P,S,U],[B,C,G,H,J,M,N,P,U],[B,C,G,H,J,M,P,Q,R,S,U],[B,C,G,H,J,M,P,Q,R,U],[B,C,G,H,J,M,P,Q,S,U],[B,C,G,H,J,M,P,Q,U],[B,C,G,H,J,M,P,R,S],[B,C,G,H,J,M,P,R,S,U],[B,C,G,H,J,M,P,R,U],[B,C,G,H,J,M,P,S,U],[B,C,G,H,J,M,P,U],[B,C,G,J],[B,C,G,J,M],[B,C,G,J,M,N,P,Q,R,S,U],[B,C,G,J,M,N,P,Q,R,U],[B,C,G,J,M,N,P,Q,S,U],[B,C,G,J,M,N,P,Q,U],[B,C,G,J,M,N,P,R,S,U],[B,C,G,J,M,N,P,R,U],[B,C,G,J,M,N,P,S,U],[B,C,G,J,M,N,P,U],[B,C,G,J,M,P],[B,C,G,J,M,P,Q],[B,C,G,J,M,P,Q,R],[B,C,G,J,M,P,Q,R,S],[B,C,G,J,M,P,Q,R,S,U],[B,C,G,J,M,P,Q,R,U],[B,C,G,J,M,P,Q,S],[B,C,G,J,M,P,Q,S,U],[B,C,G,J,M,P,Q,U],[B,C,G,J,M,P,R],[B,C,G,J,M,P,R,S],[B,C,G,J,M,P,R,S,U],[B,C,G,J,M,P,R,U],[B,C,G,J,M,P,S],[B,C,G,J,M,P,S,U],[B,C,G,J,M,P,U],[B,C,G,J,M,Q],[B,C,G,J,M,Q,R],[B,C,G,J,M,R],[B,C,G,J,Q],[B,C,G,J,Q,R],[B,C,G,J,R],[B,C,H,J,M,N,P,Q,R,S,U],[B,C,H,J,M,N,P,Q,R,U],[B,C,H,J,M,N,P,Q,S,U],[B,C,H,J,M,N,P,Q,U],[B,C,H,J,M,N,P,R,S,U],[B,C,H,J,M,N,P,R,U],[B,C,H,J,M,N,P,S,U],[B,C,H,J,M,N,P,U],[B,C,H,J,M,P,Q,R,S,U],[B,C,H,J,M,P,Q,R,U],[B,C,H,J,M,P,Q,S,U],[B,C,H,J,M,P,Q,U],[B,C,H,J,M,P,R,S,U],[B,C,H,J,M,P,R,U],[B,C,H,J,M,P,S],[B,C,H,J,M,P,S,U],[B,C,H,J,M,P,U],[B,C,J],[B,C,J,M],[B,C,J,M,N,P,Q,R,S,U],[B,C,J,M,N,P,Q,R,U],[B,C,J,M,N,P,Q,S,U],[B,C,J,M,N,P,Q,U],[B,C,J,M,N,P,R,S,U],[B,C,J,M,N,P,R,U],[B,C,J,M,N,P,S,U],[B,C,J,M,N,P,U],[B,C,J,M,P],[B,C,J,M,P,Q],[B,C,J,M,P,Q,R],[B,C,J,M,P,Q,R,S],[B,C,J,M,P,Q,R,S,U],[B,C,J,M,P,Q,R,U],[B,C,J,M,P,Q,S],[B,C,J,M,P,Q,S,U],[B,C,J,M,P,Q,U],[B,C,J,M,P,R],[B,C,J,M,P,R,S],[B,C,J,M,P,R,S,U],[B,C,J,M,P,R,U],[B,C,J,M,P,S],[B,C,J,M,P,S,U],[B,C,J,M,P,U],[B,C,J,M,Q],[B,C,J,M,Q,R],[B,C,J,M,R],[B,C,J,Q],[B,C,J,Q,R],[B,C,J,R],[B,D,F,G,H,J,M,N,P,Q,R,S,U],[B,D,F,G,H,J,M,N,P,Q,R,U],[B,D,F,G,H,J,M,N,P,Q,S,U],[B,D,F,G,H,J,M,N,P,Q,U],[B,D,F,G,H,J,M,N,P,R,S,U],[B,D,F,G,H,J,M,N,P,R,U],[B,D,F,G,H,J,M,N,P,S,U],[B,D,F,G,H,J,M,N,P,U],[B,D,F,G,H,J,M,P,Q,R,S],[B,D,F,G,H,J,M,P,Q,R,S,U],[B,D,F,G,H,J,M,P,Q,R,U],[B,D,F,G,H,J,M,P,Q,S,U],[B,D,F,G,H,J,M,P,Q,U],[B,D,F,G,H,J,M,P,R,S,U],[B,D,F,G,H,J,M,P,R,U],[B,D,F,G,H,J,M,P,S,U],[B,D,F,G,H,J,M,P,U],[B,D,F,G,J],[B,D,F,G,J,M],[B,D,F,G,J,M,N,P,Q,R,S,U],[B,D,F,G,J,M,N,P,Q,R,U],[B,D,F,G,J,M,N,P,Q,S,U],[B,D,F,G,J,M,N,P,Q,U],[B,D,F,G,J,M,N,P,R,S,U],[B,D,F,G,J,M,N,P,R,U],[B,D,F,G,J,M,N,P,S,U],[B,D,F,G,J,M,N,P,U],[B,D,F,G,J,M,P],[B,D,F,G,J,M,P,Q],[B,D,F,G,J,M,P,Q,R],[B,D,F,G,J,M,P,Q,R,S],[B,D,F,G,J,M,P,Q,R,S,U],[B,D,F,G,J,M,P,Q,R,U],[B,D,F,G,J,M,P,Q,S],[B,D,F,G,J,M,P,Q,S,U],[B,D,F,G,J,M,P,Q,U],[B,D,F,G,J,M,P,R],[B,D,F,G,J,M,P,R,S],[B,D,F,G,J,M,P,R,S,U],[B,D,F,G,J,M,P,R,U],[B,D,F,G,J,M,P,S],[B,D,F,G,J,M,P,S,U],[B,D,F,G,J,M,P,U],[B,D,F,G,J,M,Q],[B,D,F,G,J,M,Q,R],[B,D,F,G,J,M,R],[B,D,F,G,J,Q],[B,D,F,G,J,Q,R],[B,D,F,G,J,R],[B,D,F,H,J,M,N,P,Q,R,S,U],[B,D,F,H,J,M,N,P,Q,R,U],[B,D,F,H,J,M,N,P,Q,S,U],[B,D,F,H,J,M,N,P,Q,U],[B,D,F,H,J,M,N,P,R,S,U],[B,D,F,H,J,M,N,P,R,U],[B,D,F,H,J,M,N,P,S,U],[B,D,F,H,J,M,N,P,U],[B,D,F,H,J,M,P,Q,R,S,U],[B,D,F,H,J,M,P,Q,R,U],[B,D,F,H,J,M,P,Q,S],[B,D,F,H,J,M,P,Q,S,U],[B,D,F,H,J,M,P,Q,U],[B,D,F,H,J,M,P,R,S,U],[B,D,F,H,J,M,P,R,U],[B,D,F,H,J,M,P,S,U],[B,D,F,H,J,M,P,U],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N,P,Q,R,S,U],[B,D,F,J,M,N,P,Q,R,U],[B,D,F,J,M,N,P,Q,S,U],[B,D,F,J,M,N,P,Q,U],[B,D,F,J,M,N,P,R,S,U],[B,D,F,J,M,N,P,R,U],[B,D,F,J,M,N,P,S,U],[B,D,F,J,M,N,P,U],[B,D,F,J,M,P],[B,D,F,J,M,P,Q],[B,D,F,J,M,P,Q,R],[B,D,F,J,M,P,Q,R,S],[B,D,F,J,M,P,Q,R,S,U],[B,D,F,J,M,P,Q,R,U],[B,D,F,J,M,P,Q,S],[B,D,F,J,M,P,Q,S,U],[B,D,F,J,M,P,Q,U],[B,D,F,J,M,P,R],[B,D,F,J,M,P,R,S],[B,D,F,J,M,P,R,S,U],[B,D,F,J,M,P,R,U],[B,D,F,J,M,P,S],[B,D,F,J,M,P,S,U],[B,D,F,J,M,P,U],[B,D,F,J,M,Q],[B,D,F,J,M,Q,R],[B,D,F,J,M,R],[B,D,F,J,Q],[B,D,F,J,Q,R],[B,D,F,J,R],[B,D,G,H,J,M,N,P,Q,R,S,U],[B,D,G,H,J,M,N,P,Q,R,U],[B,D,G,H,J,M,N,P,Q,S,U],[B,D,G,H,J,M,N,P,Q,U],[B,D,G,H,J,M,N,P,R,S,U],[B,D,G,H,J,M,N,P,R,U],[B,D,G,H,J,M,N,P,S,U],[B,D,G,H,J,M,N,P,U],[B,D,G,H,J,M,P,Q,R,S,U],[B,D,G,H,J,M,P,Q,R,U],[B,D,G,H,J,M,P,Q,S,U],[B,D,G,H,J,M,P,Q,U],[B,D,G,H,J,M,P,R,S],[B,D,G,H,J,M,P,R,S,U],[B,D,G,H,J,M,P,R,U],[B,D,G,H,J,M,P,S,U],[B,D,G,H,J,M,P,U],[B,D,G,J],[B,D,G,J,M],[B,D,G,J,M,N,P,Q,R,S,U],[B,D,G,J,M,N,P,Q,R,U],[B,D,G,J,M,N,P,Q,S,U],[B,D,G,J,M,N,P,Q,U],[B,D,G,J,M,N,P,R,S,U],[B,D,G,J,M,N,P,R,U],[B,D,G,J,M,N,P,S,U],[B,D,G,J,M,N,P,U],[B,D,G,J,M,P],[B,D,G,J,M,P,Q],[B,D,G,J,M,P,Q,R],[B,D,G,J,M,P,Q,R,S],[B,D,G,J,M,P,Q,R,S,U],[B,D,G,J,M,P,Q,R,U],[B,D,G,J,M,P,Q,S],[B,D,G,J,M,P,Q,S,U],[B,D,G,J,M,P,Q,U],[B,D,G,J,M,P,R],[B,D,G,J,M,P,R,S],[B,D,G,J,M,P,R,S,U],[B,D,G,J,M,P,R,U],[B,D,G,J,M,P,S],[B,D,G,J,M,P,S,U],[B,D,G,J,M,P,U],[B,D,G,J,M,Q],[B,D,G,J,M,Q,R],[B,D,G,J,M,R],[B,D,G,J,Q],[B,D,G,J,Q,R],[B,D,G,J,R],[B,D,H,J,M,N,P,Q,R,S,U],[B,D,H,J,M,N,P,Q,R,U],[B,D,H,J,M,N,P,Q,S,U],[B,D,H,J,M,N,P,Q,U],[B,D,H,J,M,N,P,R,S,U],[B,D,H,J,M,N,P,R,U],[B,D,H,J,M,N,P,S,U],[B,D,H,J,M,N,P,U],[B,D,H,J,M,P,Q,R,S,U],[B,D,H,J,M,P,Q,R,U],[B,D,H,J,M,P,Q,S,U],[B,D,H,J,M,P,Q,U],[B,D,H,J,M,P,R,S,U],[B,D,H,J,M,P,R,U],[B,D,H,J,M,P,S],[B,D,H,J,M,P,S,U],[B,D,H,J,M,P,U],[B,D,J],[B,D,J,M],[B,D,J,M,N,P,Q,R,S,U],[B,D,J,M,N,P,Q,R,U],[B,D,J,M,N,P,Q,S,U],[B,D,J,M,N,P,Q,U],[B,D,J,M,N,P,R,S,U],[B,D,J,M,N,P,R,U],[B,D,J,M,N,P,S,U],[B,D,J,M,N,P,U],[B,D,J,M,P],[B,D,J,M,P,Q],[B,D,J,M,P,Q,R],[B,D,J,M,P,Q,R,S],[B,D,J,M,P,Q,R,S,U],[B,D,J,M,P,Q,R,U],[B,D,J,M,P,Q,S],[B,D,J,M,P,Q,S,U],[B,D,J,M,P,Q,U],[B,D,J,M,P,R],[B,D,J,M,P,R,S],[B,D,J,M,P,R,S,U],[B,D,J,M,P,R,U],[B,D,J,M,P,S],[B,D,J,M,P,S,U],[B,D,J,M,P,U],[B,D,J,M,Q],[B,D,J,M,Q,R],[B,D,J,M,R],[B,D,J,Q],[B,D,J,Q,R],[B,D,J,R],[B,F,G,H,J,M,N,P,Q,R,S,U],[B,F,G,H,J,M,N,P,Q,R,U],[B,F,G,H,J,M,N,P,Q,S,U],[B,F,G,H,J,M,N,P,Q,U],[B,F,G,H,J,M,N,P,R,S,U],[B,F,G,H,J,M,N,P,R,U],[B,F,G,H,J,M,N,P,S,U],[B,F,G,H,J,M,N,P,U],[B,F,G,H,J,M,P,Q,R,S],[B,F,G,H,J,M,P,Q,R,S,U],[B,F,G,H,J,M,P,Q,R,U],[B,F,G,H,J,M,P,Q,S,U],[B,F,G,H,J,M,P,Q,U],[B,F,G,H,J,M,P,R,S,U],[B,F,G,H,J,M,P,R,U],[B,F,G,H,J,M,P,S,U],[B,F,G,H,J,M,P,U],[B,F,G,J],[B,F,G,J,M],[B,F,G,J,M,N,P,Q,R,S,U],[B,F,G,J,M,N,P,Q,R,U],[B,F,G,J,M,N,P,Q,S,U],[B,F,G,J,M,N,P,Q,U],[B,F,G,J,M,N,P,R,S,U],[B,F,G,J,M,N,P,R,U],[B,F,G,J,M,N,P,S,U],[B,F,G,J,M,N,P,U],[B,F,G,J,M,P],[B,F,G,J,M,P,Q],[B,F,G,J,M,P,Q,R],[B,F,G,J,M,P,Q,R,S],[B,F,G,J,M,P,Q,R,S,U],[B,F,G,J,M,P,Q,R,U],[B,F,G,J,M,P,Q,S],[B,F,G,J,M,P,Q,S,U],[B,F,G,J,M,P,Q,U],[B,F,G,J,M,P,R],[B,F,G,J,M,P,R,S],[B,F,G,J,M,P,R,S,U],[B,F,G,J,M,P,R,U],[B,F,G,J,M,P,S],[B,F,G,J,M,P,S,U],[B,F,G,J,M,P,U],[B,F,G,J,M,Q],[B,F,G,J,M,Q,R],[B,F,G,J,M,R],[B,F,G,J,Q],[B,F,G,J,Q,R],[B,F,G,J,R],[B,F,H,J,M,N,P,Q,R,S,U],[B,F,H,J,M,N,P,Q,R,U],[B,F,H,J,M,N,P,Q,S,U],[B,F,H,J,M,N,P,Q,U],[B,F,H,J,M,N,P,R,S,U],[B,F,H,J,M,N,P,R,U],[B,F,H,J,M,N,P,S,U],[B,F,H,J,M,N,P,U],[B,F,H,J,M,P,Q,R,S,U],[B,F,H,J,M,P,Q,R,U],[B,F,H,J,M,P,Q,S],[B,F,H,J,M,P,Q,S,U],[B,F,H,J,M,P,Q,U],[B,F,H,J,M,P,R,S,U],[B,F,H,J,M,P,R,U],[B,F,H,J,M,P,S,U],[B,F,H,J,M,P,U],[B,F,J],[B,F,J,M],[B,F,J,M,N,P,Q,R,S,U],[B,F,J,M,N,P,Q,R,U],[B,F,J,M,N,P,Q,S,U],[B,F,J,M,N,P,Q,U],[B,F,J,M,N,P,R,S,U],[B,F,J,M,N,P,R,U],[B,F,J,M,N,P,S,U],[B,F,J,M,N,P,U],[B,F,J,M,P],[B,F,J,M,P,Q],[B,F,J,M,P,Q,R],[B,F,J,M,P,Q,R,S],[B,F,J,M,P,Q,R,S,U],[B,F,J,M,P,Q,R,U],[B,F,J,M,P,Q,S],[B,F,J,M,P,Q,S,U],[B,F,J,M,P,Q,U],[B,F,J,M,P,R],[B,F,J,M,P,R,S],[B,F,J,M,P,R,S,U],[B,F,J,M,P,R,U],[B,F,J,M,P,S],[B,F,J,M,P,S,U],[B,F,J,M,P,U],[B,F,J,M,Q],[B,F,J,M,Q,R],[B,F,J,M,R],[B,F,J,Q],[B,F,J,Q,R],[B,F,J,R],[B,G,H,J,M,N,P,Q,R,S,U],[B,G,H,J,M,N,P,Q,R,U],[B,G,H,J,M,N,P,Q,S,U],[B,G,H,J,M,N,P,Q,U],[B,G,H,J,M,N,P,R,S,U],[B,G,H,J,M,N,P,R,U],[B,G,H,J,M,N,P,S,U],[B,G,H,J,M,N,P,U],[B,G,H,J,M,P,Q,R,S,U],[B,G,H,J,M,P,Q,R,U],[B,G,H,J,M,P,Q,S,U],[B,G,H,J,M,P,Q,U],[B,G,H,J,M,P,R,S],[B,G,H,J,M,P,R,S,U],[B,G,H,J,M,P,R,U],[B,G,H,J,M,P,S,U],[B,G,H,J,M,P,U],[B,G,J],[B,G,J,M],[B,G,J,M,N,P,Q,R,S,U],[B,G,J,M,N,P,Q,R,U],[B,G,J,M,N,P,Q,S,U],[B,G,J,M,N,P,Q,U],[B,G,J,M,N,P,R,S,U],[B,G,J,M,N,P,R,U],[B,G,J,M,N,P,S,U],[B,G,J,M,N,P,U],[B,G,J,M,P],[B,G,J,M,P,Q],[B,G,J,M,P,Q,R],[B,G,J,M,P,Q,R,S],[B,G,J,M,P,Q,R,S,U],[B,G,J,M,P,Q,R,U],[B,G,J,M,P,Q,S],[B,G,J,M,P,Q,S,U],[B,G,J,M,P,Q,U],[B,G,J,M,P,R],[B,G,J,M,P,R,S],[B,G,J,M,P,R,S,U],[B,G,J,M,P,R,U],[B,G,J,M,P,S],[B,G,J,M,P,S,U],[B,G,J,M,P,U],[B,G,J,M,Q],[B,G,J,M,Q,R],[B,G,J,M,R],[B,G,J,Q],[B,G,J,Q,R],[B,G,J,R],[B,H,J,M,N,P,Q,R,S,U],[B,H,J,M,N,P,Q,R,U],[B,H,J,M,N,P,Q,S,U],[B,H,J,M,N,P,Q,U],[B,H,J,M,N,P,R,S,U],[B,H,J,M,N,P,R,U],[B,H,J,M,N,P,S,U],[B,H,J,M,N,P,U],[B,H,J,M,P,Q,R,S,U],[B,H,J,M,P,Q,R,U],[B,H,J,M,P,Q,S,U],[B,H,J,M,P,Q,U],[B,H,J,M,P,R,S,U],[B,H,J,M,P,R,U],[B,H,J,M,P,S],[B,H,J,M,P,S,U],[B,H,J,M,P,U],[B,J],[B,J,M],[B,J,M,N,P,Q,R,S,U],[B,J,M,N,P,Q,R,U],[B,J,M,N,P,Q,S,U],[B,J,M,N,P,Q,U],[B,J,M,N,P,R,S,U],[B,J,M,N,P,R,U],[B,J,M,N,P,S,U],[B,J,M,N,P,U],[B,J,M,P],[B,J,M,P,Q],[B,J,M,P,Q,R],[B,J,M,P,Q,R,S],[B,J,M,P,Q,R,S,U],[B,J,M,P,Q,R,U],[B,J,M,P,Q,S],[B,J,M,P,Q,S,U],[B,J,M,P,Q,U],[B,J,M,P,R],[B,J,M,P,R,S],[B,J,M,P,R,S,U],[B,J,M,P,R,U],[B,J,M,P,S],[B,J,M,P,S,U],[B,J,M,P,U],[B,J,M,Q],[B,J,M,Q,R],[B,J,M,R],[B,J,Q],[B,J,Q,R],[B,J,R],[C,D,F,G,H,J,M,N,P,Q,R,S,U],[C,D,F,G,H,J,M,N,P,Q,R,U],[C,D,F,G,H,J,M,N,P,Q,S,U],[C,D,F,G,H,J,M,N,P,Q,U],[C,D,F,G,H,J,M,N,P,R,S,U],[C,D,F,G,H,J,M,N,P,R,U],[C,D,F,G,H,J,M,N,P,S,U],[C,D,F,G,H,J,M,N,P,U],[C,D,F,G,H,J,M,P,Q,R,S],[C,D,F,G,H,J,M,P,Q,R,S,U],[C,D,F,G,H,J,M,P,Q,R,U],[C,D,F,G,H,J,M,P,Q,S,U],[C,D,F,G,H,J,M,P,Q,U],[C,D,F,G,H,J,M,P,R,S,U],[C,D,F,G,H,J,M,P,R,U],[C,D,F,G,H,J,M,P,S,U],[C,D,F,G,H,J,M,P,U],[C,D,F,G,J],[C,D,F,G,J,M],[C,D,F,G,J,M,N,P,Q,R,S,U],[C,D,F,G,J,M,N,P,Q,R,U],[C,D,F,G,J,M,N,P,Q,S,U],[C,D,F,G,J,M,N,P,Q,U],[C,D,F,G,J,M,N,P,R,S,U],[C,D,F,G,J,M,N,P,R,U],[C,D,F,G,J,M,N,P,S,U],[C,D,F,G,J,M,N,P,U],[C,D,F,G,J,M,P],[C,D,F,G,J,M,P,Q],[C,D,F,G,J,M,P,Q,R],[C,D,F,G,J,M,P,Q,R,S],[C,D,F,G,J,M,P,Q,R,S,U],[C,D,F,G,J,M,P,Q,R,U],[C,D,F,G,J,M,P,Q,S],[C,D,F,G,J,M,P,Q,S,U],[C,D,F,G,J,M,P,Q,U],[C,D,F,G,J,M,P,R],[C,D,F,G,J,M,P,R,S],[C,D,F,G,J,M,P,R,S,U],[C,D,F,G,J,M,P,R,U],[C,D,F,G,J,M,P,S],[C,D,F,G,J,M,P,S,U],[C,D,F,G,J,M,P,U],[C,D,F,G,J,M,Q],[C,D,F,G,J,M,Q,R],[C,D,F,G,J,M,R],[C,D,F,G,J,Q],[C,D,F,G,J,Q,R],[C,D,F,G,J,R],[C,D,F,H,J,M,N,P,Q,R,S,U],[C,D,F,H,J,M,N,P,Q,R,U],[C,D,F,H,J,M,N,P,Q,S,U],[C,D,F,H,J,M,N,P,Q,U],[C,D,F,H,J,M,N,P,R,S,U],[C,D,F,H,J,M,N,P,R,U],[C,D,F,H,J,M,N,P,S,U],[C,D,F,H,J,M,N,P,U],[C,D,F,H,J,M,P,Q,R,S,U],[C,D,F,H,J,M,P,Q,R,U],[C,D,F,H,J,M,P,Q,S],[C,D,F,H,J,M,P,Q,S,U],[C,D,F,H,J,M,P,Q,U],[C,D,F,H,J,M,P,R,S,U],[C,D,F,H,J,M,P,R,U],[C,D,F,H,J,M,P,S,U],[C,D,F,H,J,M,P,U],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N,P,Q,R,S,U],[C,D,F,J,M,N,P,Q,R,U],[C,D,F,J,M,N,P,Q,S,U],[C,D,F,J,M,N,P,Q,U],[C,D,F,J,M,N,P,R,S,U],[C,D,F,J,M,N,P,R,U],[C,D,F,J,M,N,P,S,U],[C,D,F,J,M,N,P,U],[C,D,F,J,M,P],[C,D,F,J,M,P,Q],[C,D,F,J,M,P,Q,R],[C,D,F,J,M,P,Q,R,S],[C,D,F,J,M,P,Q,R,S,U],[C,D,F,J,M,P,Q,R,U],[C,D,F,J,M,P,Q,S],[C,D,F,J,M,P,Q,S,U],[C,D,F,J,M,P,Q,U],[C,D,F,J,M,P,R],[C,D,F,J,M,P,R,S],[C,D,F,J,M,P,R,S,U],[C,D,F,J,M,P,R,U],[C,D,F,J,M,P,S],[C,D,F,J,M,P,S,U],[C,D,F,J,M,P,U],[C,D,F,J,M,Q],[C,D,F,J,M,Q,R],[C,D,F,J,M,R],[C,D,F,J,Q],[C,D,F,J,Q,R],[C,D,F,J,R],[C,D,G,H,J,M,N,P,Q,R,S,U],[C,D,G,H,J,M,N,P,Q,R,U],[C,D,G,H,J,M,N,P,Q,S,U],[C,D,G,H,J,M,N,P,Q,U],[C,D,G,H,J,M,N,P,R,S,U],[C,D,G,H,J,M,N,P,R,U],[C,D,G,H,J,M,N,P,S,U],[C,D,G,H,J,M,N,P,U],[C,D,G,H,J,M,P,Q,R,S,U],[C,D,G,H,J,M,P,Q,R,U],[C,D,G,H,J,M,P,Q,S,U],[C,D,G,H,J,M,P,Q,U],[C,D,G,H,J,M,P,R,S],[C,D,G,H,J,M,P,R,S,U],[C,D,G,H,J,M,P,R,U],[C,D,G,H,J,M,P,S,U],[C,D,G,H,J,M,P,U],[C,D,G,J],[C,D,G,J,M],[C,D,G,J,M,N,P,Q,R,S,U],[C,D,G,J,M,N,P,Q,R,U],[C,D,G,J,M,N,P,Q,S,U],[C,D,G,J,M,N,P,Q,U],[C,D,G,J,M,N,P,R,S,U],[C,D,G,J,M,N,P,R,U],[C,D,G,J,M,N,P,S,U],[C,D,G,J,M,N,P,U],[C,D,G,J,M,P],[C,D,G,J,M,P,Q],[C,D,G,J,M,P,Q,R],[C,D,G,J,M,P,Q,R,S],[C,D,G,J,M,P,Q,R,S,U],[C,D,G,J,M,P,Q,R,U],[C,D,G,J,M,P,Q,S],[C,D,G,J,M,P,Q,S,U],[C,D,G,J,M,P,Q,U],[C,D,G,J,M,P,R],[C,D,G,J,M,P,R,S],[C,D,G,J,M,P,R,S,U],[C,D,G,J,M,P,R,U],[C,D,G,J,M,P,S],[C,D,G,J,M,P,S,U],[C,D,G,J,M,P,U],[C,D,G,J,M,Q],[C,D,G,J,M,Q,R],[C,D,G,J,M,R],[C,D,G,J,Q],[C,D,G,J,Q,R],[C,D,G,J,R],[C,D,H,J,M,N,P,Q,R,S,U],[C,D,H,J,M,N,P,Q,R,U],[C,D,H,J,M,N,P,Q,S,U],[C,D,H,J,M,N,P,Q,U],[C,D,H,J,M,N,P,R,S,U],[C,D,H,J,M,N,P,R,U],[C,D,H,J,M,N,P,S,U],[C,D,H,J,M,N,P,U],[C,D,H,J,M,P,Q,R,S,U],[C,D,H,J,M,P,Q,R,U],[C,D,H,J,M,P,Q,S,U],[C,D,H,J,M,P,Q,U],[C,D,H,J,M,P,R,S,U],[C,D,H,J,M,P,R,U],[C,D,H,J,M,P,S],[C,D,H,J,M,P,S,U],[C,D,H,J,M,P,U],[C,D,J],[C,D,J,M],[C,D,J,M,N,P,Q,R,S,U],[C,D,J,M,N,P,Q,R,U],[C,D,J,M,N,P,Q,S,U],[C,D,J,M,N,P,Q,U],[C,D,J,M,N,P,R,S,U],[C,D,J,M,N,P,R,U],[C,D,J,M,N,P,S,U],[C,D,J,M,N,P,U],[C,D,J,M,P],[C,D,J,M,P,Q],[C,D,J,M,P,Q,R],[C,D,J,M,P,Q,R,S],[C,D,J,M,P,Q,R,S,U],[C,D,J,M,P,Q,R,U],[C,D,J,M,P,Q,S],[C,D,J,M,P,Q,S,U],[C,D,J,M,P,Q,U],[C,D,J,M,P,R],[C,D,J,M,P,R,S],[C,D,J,M,P,R,S,U],[C,D,J,M,P,R,U],[C,D,J,M,P,S],[C,D,J,M,P,S,U],[C,D,J,M,P,U],[C,D,J,M,Q],[C,D,J,M,Q,R],[C,D,J,M,R],[C,D,J,Q],[C,D,J,Q,R],[C,D,J,R],[C,F,G,H,J,M,N,P,Q,R,S,U],[C,F,G,H,J,M,N,P,Q,R,U],[C,F,G,H,J,M,N,P,Q,S,U],[C,F,G,H,J,M,N,P,Q,U],[C,F,G,H,J,M,N,P,R,S,U],[C,F,G,H,J,M,N,P,R,U],[C,F,G,H,J,M,N,P,S,U],[C,F,G,H,J,M,N,P,U],[C,F,G,H,J,M,P,Q,R,S],[C,F,G,H,J,M,P,Q,R,S,U],[C,F,G,H,J,M,P,Q,R,U],[C,F,G,H,J,M,P,Q,S,U],[C,F,G,H,J,M,P,Q,U],[C,F,G,H,J,M,P,R,S,U],[C,F,G,H,J,M,P,R,U],[C,F,G,H,J,M,P,S,U],[C,F,G,H,J,M,P,U],[C,F,G,J],[C,F,G,J,M],[C,F,G,J,M,N,P,Q,R,S,U],[C,F,G,J,M,N,P,Q,R,U],[C,F,G,J,M,N,P,Q,S,U],[C,F,G,J,M,N,P,Q,U],[C,F,G,J,M,N,P,R,S,U],[C,F,G,J,M,N,P,R,U],[C,F,G,J,M,N,P,S,U],[C,F,G,J,M,N,P,U],[C,F,G,J,M,P],[C,F,G,J,M,P,Q],[C,F,G,J,M,P,Q,R],[C,F,G,J,M,P,Q,R,S],[C,F,G,J,M,P,Q,R,S,U],[C,F,G,J,M,P,Q,R,U],[C,F,G,J,M,P,Q,S],[C,F,G,J,M,P,Q,S,U],[C,F,G,J,M,P,Q,U],[C,F,G,J,M,P,R],[C,F,G,J,M,P,R,S],[C,F,G,J,M,P,R,S,U],[C,F,G,J,M,P,R,U],[C,F,G,J,M,P,S],[C,F,G,J,M,P,S,U],[C,F,G,J,M,P,U],[C,F,G,J,M,Q],[C,F,G,J,M,Q,R],[C,F,G,J,M,R],[C,F,G,J,Q],[C,F,G,J,Q,R],[C,F,G,J,R],[C,F,H,J,M,N,P,Q,R,S,U],[C,F,H,J,M,N,P,Q,R,U],[C,F,H,J,M,N,P,Q,S,U],[C,F,H,J,M,N,P,Q,U],[C,F,H,J,M,N,P,R,S,U],[C,F,H,J,M,N,P,R,U],[C,F,H,J,M,N,P,S,U],[C,F,H,J,M,N,P,U],[C,F,H,J,M,P,Q,R,S,U],[C,F,H,J,M,P,Q,R,U],[C,F,H,J,M,P,Q,S],[C,F,H,J,M,P,Q,S,U],[C,F,H,J,M,P,Q,U],[C,F,H,J,M,P,R,S,U],[C,F,H,J,M,P,R,U],[C,F,H,J,M,P,S,U],[C,F,H,J,M,P,U],[C,F,J],[C,F,J,M],[C,F,J,M,N,P,Q,R,S,U],[C,F,J,M,N,P,Q,R,U],[C,F,J,M,N,P,Q,S,U],[C,F,J,M,N,P,Q,U],[C,F,J,M,N,P,R,S,U],[C,F,J,M,N,P,R,U],[C,F,J,M,N,P,S,U],[C,F,J,M,N,P,U],[C,F,J,M,P],[C,F,J,M,P,Q],[C,F,J,M,P,Q,R],[C,F,J,M,P,Q,R,S],[C,F,J,M,P,Q,R,S,U],[C,F,J,M,P,Q,R,U],[C,F,J,M,P,Q,S],[C,F,J,M,P,Q,S,U],[C,F,J,M,P,Q,U],[C,F,J,M,P,R],[C,F,J,M,P,R,S],[C,F,J,M,P,R,S,U],[C,F,J,M,P,R,U],[C,F,J,M,P,S],[C,F,J,M,P,S,U],[C,F,J,M,P,U],[C,F,J,M,Q],[C,F,J,M,Q,R],[C,F,J,M,R],[C,F,J,Q],[C,F,J,Q,R],[C,F,J,R],[C,G,H,J,M,N,P,Q,R,S,U],[C,G,H,J,M,N,P,Q,R,U],[C,G,H,J,M,N,P,Q,S,U],[C,G,H,J,M,N,P,Q,U],[C,G,H,J,M,N,P,R,S,U],[C,G,H,J,M,N,P,R,U],[C,G,H,J,M,N,P,S,U],[C,G,H,J,M,N,P,U],[C,G,H,J,M,P,Q,R,S,U],[C,G,H,J,M,P,Q,R,U],[C,G,H,J,M,P,Q,S,U],[C,G,H,J,M,P,Q,U],[C,G,H,J,M,P,R,S],[C,G,H,J,M,P,R,S,U],[C,G,H,J,M,P,R,U],[C,G,H,J,M,P,S,U],[C,G,H,J,M,P,U],[C,G,J],[C,G,J,M],[C,G,J,M,N,P,Q,R,S,U],[C,G,J,M,N,P,Q,R,U],[C,G,J,M,N,P,Q,S,U],[C,G,J,M,N,P,Q,U],[C,G,J,M,N,P,R,S,U],[C,G,J,M,N,P,R,U],[C,G,J,M,N,P,S,U],[C,G,J,M,N,P,U],[C,G,J,M,P],[C,G,J,M,P,Q],[C,G,J,M,P,Q,R],[C,G,J,M,P,Q,R,S],[C,G,J,M,P,Q,R,S,U],[C,G,J,M,P,Q,R,U],[C,G,J,M,P,Q,S],[C,G,J,M,P,Q,S,U],[C,G,J,M,P,Q,U],[C,G,J,M,P,R],[C,G,J,M,P,R,S],[C,G,J,M,P,R,S,U],[C,G,J,M,P,R,U],[C,G,J,M,P,S],[C,G,J,M,P,S,U],[C,G,J,M,P,U],[C,G,J,M,Q],[C,G,J,M,Q,R],[C,G,J,M,R],[C,G,J,Q],[C,G,J,Q,R],[C,G,J,R],[C,H,J,M,N,P,Q,R,S,U],[C,H,J,M,N,P,Q,R,U],[C,H,J,M,N,P,Q,S,U],[C,H,J,M,N,P,Q,U],[C,H,J,M,N,P,R,S,U],[C,H,J,M,N,P,R,U],[C,H,J,M,N,P,S,U],[C,H,J,M,N,P,U],[C,H,J,M,P,Q,R,S,U],[C,H,J,M,P,Q,R,U],[C,H,J,M,P,Q,S,U],[C,H,J,M,P,Q,U],[C,H,J,M,P,R,S,U],[C,H,J,M,P,R,U],[C,H,J,M,P,S],[C,H,J,M,P,S,U],[C,H,J,M,P,U],[C,J],[C,J,M],[C,J,M,N,P,Q,R,S,U],[C,J,M,N,P,Q,R,U],[C,J,M,N,P,Q,S,U],[C,J,M,N,P,Q,U],[C,J,M,N,P,R,S,U],[C,J,M,N,P,R,U],[C,J,M,N,P,S,U],[C,J,M,N,P,U],[C,J,M,P],[C,J,M,P,Q],[C,J,M,P,Q,R],[C,J,M,P,Q,R,S],[C,J,M,P,Q,R,S,U],[C,J,M,P,Q,R,U],[C,J,M,P,Q,S],[C,J,M,P,Q,S,U],[C,J,M,P,Q,U],[C,J,M,P,R],[C,J,M,P,R,S],[C,J,M,P,R,S,U],[C,J,M,P,R,U],[C,J,M,P,S],[C,J,M,P,S,U],[C,J,M,P,U],[C,J,M,Q],[C,J,M,Q,R],[C,J,M,R],[C,J,Q],[C,J,Q,R],[C,J,R],[D],[D,F,G],[D,F,G,H,J,M,N,P,Q,R,S,U],[D,F,G,H,J,M,N,P,Q,R,U],[D,F,G,H,J,M,N,P,Q,S,U],[D,F,G,H,J,M,N,P,Q,U],[D,F,G,H,J,M,N,P,R,S,U],[D,F,G,H,J,M,N,P,R,U],[D,F,G,H,J,M,N,P,S,U],[D,F,G,H,J,M,N,P,U],[D,F,G,H,J,M,P,Q,R,S,U],[D,F,G,H,J,M,P,Q,R,U],[D,F,G,H,J,M,P,Q,S,U],[D,F,G,H,J,M,P,Q,U],[D,F,G,H,J,M,P,R,S,U],[D,F,G,H,J,M,P,R,U],[D,F,G,H,J,M,P,S,U],[D,F,G,H,J,M,P,U],[D,F,G,H,M,N,P,Q,R,S,U],[D,F,G,H,M,N,P,S,U],[D,F,G,H,M,N,P,U],[D,F,G,H,M,P,Q,R,S],[D,F,G,H,M,P,S,U],[D,F,G,H,M,P,U],[D,F,G,J],[D,F,G,J,M],[D,F,G,J,M,N,P,Q,R,S,U],[D,F,G,J,M,N,P,Q,R,U],[D,F,G,J,M,N,P,Q,S,U],[D,F,G,J,M,N,P,Q,U],[D,F,G,J,M,N,P,R,S,U],[D,F,G,J,M,N,P,R,U],[D,F,G,J,M,N,P,S,U],[D,F,G,J,M,N,P,U],[D,F,G,J,M,P],[D,F,G,J,M,P,Q],[D,F,G,J,M,P,Q,R],[D,F,G,J,M,P,Q,R,S],[D,F,G,J,M,P,Q,R,S,U],[D,F,G,J,M,P,Q,R,U],[D,F,G,J,M,P,Q,S],[D,F,G,J,M,P,Q,S,U],[D,F,G,J,M,P,Q,U],[D,F,G,J,M,P,R],[D,F,G,J,M,P,R,S],[D,F,G,J,M,P,R,S,U],[D,F,G,J,M,P,R,U],[D,F,G,J,M,P,S],[D,F,G,J,M,P,S,U],[D,F,G,J,M,P,U],[D,F,G,J,M,Q],[D,F,G,J,M,Q,R],[D,F,G,J,M,R],[D,F,G,J,Q],[D,F,G,J,Q,R],[D,F,G,J,R],[D,F,G,M],[D,F,G,M,N,P,Q,R,U],[D,F,G,M,N,P,S,U],[D,F,G,M,N,P,U],[D,F,G,M,P],[D,F,G,M,P,Q,R],[D,F,G,M,P,S],[D,F,G,M,P,S,U],[D,F,G,M,P,U],[D,F,G,M,Q,R],[D,F,G,Q,R],[D,F,H,J,M,N,P,Q,R,S,U],[D,F,H,J,M,N,P,Q,R,U],[D,F,H,J,M,N,P,Q,S,U],[D,F,H,J,M,N,P,Q,U],[D,F,H,J,M,N,P,R,S,U],[D,F,H,J,M,N,P,R,U],[D,F,H,J,M,N,P,S,U],[D,F,H,J,M,N,P,U],[D,F,H,J,M,P,Q,R,S,U],[D,F,H,J,M,P,Q,R,U],[D,F,H,J,M,P,Q,S,U],[D,F,H,J,M,P,Q,U],[D,F,H,J,M,P,R,S,U],[D,F,H,J,M,P,R,U],[D,F,H,J,M,P,S,U],[D,F,H,J,M,P,U],[D,F,H,M,N,P,Q,S,U],[D,F,H,M,N,P,S,U],[D,F,H,M,N,P,U],[D,F,H,M,P,Q,S],[D,F,H,M,P,S,U],[D,F,H,M,P,U],[D,F,J,M,N,P,Q,R,S,U],[D,F,J,M,N,P,Q,R,U],[D,F,J,M,N,P,Q,S,U],[D,F,J,M,N,P,Q,U],[D,F,J,M,N,P,R,S,U],[D,F,J,M,N,P,R,U],[D,F,J,M,N,P,S,U],[D,F,J,M,N,P,U],[D,F,J,M,P,Q],[D,F,J,M,P,Q,R],[D,F,J,M,P,Q,R,S],[D,F,J,M,P,Q,R,S,U],[D,F,J,M,P,Q,R,U],[D,F,J,M,P,Q,S],[D,F,J,M,P,Q,S,U],[D,F,J,M,P,Q,U],[D,F,J,M,P,R],[D,F,J,M,P,R,S],[D,F,J,M,P,R,S,U],[D,F,J,M,P,R,U],[D,F,J,M,P,S,U],[D,F,J,M,P,U],[D,F,M,N,P,Q,U],[D,F,M,N,P,S,U],[D,F,M,N,P,U],[D,F,M,P,Q],[D,F,M,P,S,U],[D,F,M,P,U],[D,G],[D,G,H,J,M,N,P,Q,R,S,U],[D,G,H,J,M,N,P,Q,R,U],[D,G,H,J,M,N,P,Q,S,U],[D,G,H,J,M,N,P,Q,U],[D,G,H,J,M,N,P,R,S,U],[D,G,H,J,M,N,P,R,U],[D,G,H,J,M,N,P,S,U],[D,G,H,J,M,N,P,U],[D,G,H,J,M,P,Q,R,S,U],[D,G,H,J,M,P,Q,R,U],[D,G,H,J,M,P,Q,S,U],[D,G,H,J,M,P,Q,U],[D,G,H,J,M,P,R,S,U],[D,G,H,J,M,P,R,U],[D,G,H,J,M,P,S,U],[D,G,H,J,M,P,U],[D,G,H,M,N,P,R,S,U],[D,G,H,M,N,P,S,U],[D,G,H,M,N,P,U],[D,G,H,M,P,R,S],[D,G,H,M,P,S,U],[D,G,H,M,P,U],[D,G,J],[D,G,J,M],[D,G,J,M,N,P,Q,R,S,U],[D,G,J,M,N,P,Q,R,U],[D,G,J,M,N,P,Q,S,U],[D,G,J,M,N,P,Q,U],[D,G,J,M,N,P,R,S,U],[D,G,J,M,N,P,R,U],[D,G,J,M,N,P,S,U],[D,G,J,M,N,P,U],[D,G,J,M,P],[D,G,J,M,P,Q],[D,G,J,M,P,Q,R],[D,G,J,M,P,Q,R,S],[D,G,J,M,P,Q,R,S,U],[D,G,J,M,P,Q,R,U],[D,G,J,M,P,Q,S],[D,G,J,M,P,Q,S,U],[D,G,J,M,P,Q,U],[D,G,J,M,P,R],[D,G,J,M,P,R,S],[D,G,J,M,P,R,S,U],[D,G,J,M,P,R,U],[D,G,J,M,P,S],[D,G,J,M,P,S,U],[D,G,J,M,P,U],[D,G,J,M,Q],[D,G,J,M,Q,R],[D,G,J,M,R],[D,G,J,Q],[D,G,J,Q,R],[D,G,J,R],[D,G,M],[D,G,M,N,P,R,U],[D,G,M,N,P,S,U],[D,G,M,N,P,U],[D,G,M,P],[D,G,M,P,R],[D,G,M,P,S],[D,G,M,P,S,U],[D,G,M,P,U],[D,G,M,R],[D,G,R],[D,H,J,M,N,P,Q,R,S,U],[D,H,J,M,N,P,Q,R,U],[D,H,J,M,N,P,Q,S,U],[D,H,J,M,N,P,Q,U],[D,H,J,M,N,P,R,S,U],[D,H,J,M,N,P,R,U],[D,H,J,M,N,P,S,U],[D,H,J,M,N,P,U],[D,H,J,M,P,Q,R,S,U],[D,H,J,M,P,Q,R,U],[D,H,J,M,P,Q,S,U],[D,H,J,M,P,Q,U],[D,H,J,M,P,R,S,U],[D,H,J,M,P,R,U],[D,H,J,M,P,S,U],[D,H,J,M,P,U],[D,H,M,N,P,S,U],[D,H,M,N,P,U],[D,H,M,P,S],[D,H,M,P,S,U],[D,H,M,P,U],[D,J,M,N,P,Q,R,S,U],[D,J,M,N,P,Q,R,U],[D,J,M,N,P,Q,S,U],[D,J,M,N,P,Q,U],[D,J,M,N,P,R,S,U],[D,J,M,N,P,R,U],[D,J,M,N,P,S,U],[D,J,M,N,P,U],[D,J,M,P,Q],[D,J,M,P,Q,R],[D,J,M,P,Q,R,S],[D,J,M,P,Q,R,S,U],[D,J,M,P,Q,R,U],[D,J,M,P,Q,S],[D,J,M,P,Q,S,U],[D,J,M,P,Q,U],[D,J,M,P,R],[D,J,M,P,R,S],[D,J,M,P,R,S,U],[D,J,M,P,R,U],[D,J,M,P,S,U],[D,J,M,P,U],[D,M],[D,M,N,P,S,U],[D,M,N,P,U],[D,M,P],[D,M,P,S],[D,M,P,S,U],[D,M,P,U],[F],[F,G],[F,G,H,J,M,N,P,Q,R,S,U],[F,G,H,J,M,N,P,Q,R,U],[F,G,H,J,M,N,P,Q,S,U],[F,G,H,J,M,N,P,Q,U],[F,G,H,J,M,N,P,R,S,U],[F,G,H,J,M,N,P,R,U],[F,G,H,J,M,N,P,S,U],[F,G,H,J,M,N,P,U],[F,G,H,J,M,P,Q,R,S,U],[F,G,H,J,M,P,Q,R,U],[F,G,H,J,M,P,Q,S,U],[F,G,H,J,M,P,Q,U],[F,G,H,J,M,P,R,S,U],[F,G,H,J,M,P,R,U],[F,G,H,J,M,P,S,U],[F,G,H,J,M,P,U],[F,G,H,M,N,P,Q,R,S,U],[F,G,H,M,N,P,S,U],[F,G,H,M,N,P,U],[F,G,H,M,P,Q,R,S],[F,G,H,M,P,S,U],[F,G,H,M,P,U],[F,G,J],[F,G,J,M],[F,G,J,M,N,P,Q,R,S,U],[F,G,J,M,N,P,Q,R,U],[F,G,J,M,N,P,Q,S,U],[F,G,J,M,N,P,Q,U],[F,G,J,M,N,P,R,S,U],[F,G,J,M,N,P,R,U],[F,G,J,M,N,P,S,U],[F,G,J,M,N,P,U],[F,G,J,M,P],[F,G,J,M,P,Q],[F,G,J,M,P,Q,R],[F,G,J,M,P,Q,R,S],[F,G,J,M,P,Q,R,S,U],[F,G,J,M,P,Q,R,U],[F,G,J,M,P,Q,S],[F,G,J,M,P,Q,S,U],[F,G,J,M,P,Q,U],[F,G,J,M,P,R],[F,G,J,M,P,R,S],[F,G,J,M,P,R,S,U],[F,G,J,M,P,R,U],[F,G,J,M,P,S],[F,G,J,M,P,S,U],[F,G,J,M,P,U],[F,G,J,M,Q],[F,G,J,M,Q,R],[F,G,J,M,R],[F,G,J,Q],[F,G,J,Q,R],[F,G,J,R],[F,G,M],[F,G,M,N,P,Q,R,U],[F,G,M,N,P,S,U],[F,G,M,N,P,U],[F,G,M,P],[F,G,M,P,Q,R],[F,G,M,P,S],[F,G,M,P,S,U],[F,G,M,P,U],[F,G,M,Q,R],[F,G,Q,R],[F,H,J,M,N,P,Q,R,S,U],[F,H,J,M,N,P,Q,R,U],[F,H,J,M,N,P,Q,S,U],[F,H,J,M,N,P,Q,U],[F,H,J,M,N,P,R,S,U],[F,H,J,M,N,P,R,U],[F,H,J,M,N,P,S,U],[F,H,J,M,N,P,U],[F,H,J,M,P,Q,R,S,U],[F,H,J,M,P,Q,R,U],[F,H,J,M,P,Q,S,U],[F,H,J,M,P,Q,U],[F,H,J,M,P,R,S,U],[F,H,J,M,P,R,U],[F,H,J,M,P,S,U],[F,H,J,M,P,U],[F,H,M,N,P,Q,S,U],[F,H,M,N,P,S,U],[F,H,M,N,P,U],[F,H,M,P,Q,S],[F,H,M,P,S,U],[F,H,M,P,U],[F,J],[F,J,M,N,P,Q,R,S,U],[F,J,M,N,P,Q,R,U],[F,J,M,N,P,Q,S,U],[F,J,M,N,P,Q,U],[F,J,M,N,P,R,S,U],[F,J,M,N,P,R,U],[F,J,M,N,P,S,U],[F,J,M,N,P,U],[F,J,M,P,Q],[F,J,M,P,Q,R],[F,J,M,P,Q,R,S],[F,J,M,P,Q,R,S,U],[F,J,M,P,Q,R,U],[F,J,M,P,Q,S],[F,J,M,P,Q,S,U],[F,J,M,P,Q,U],[F,J,M,P,R],[F,J,M,P,R,S],[F,J,M,P,R,S,U],[F,J,M,P,R,U],[F,J,M,P,S,U],[F,J,M,P,U],[F,J,Q],[F,J,Q,R],[F,J,R],[F,M,N,P,Q,U],[F,M,N,P,S,U],[F,M,N,P,U],[F,M,P,Q],[F,M,P,S,U],[F,M,P,U],[F,Q],[G],[G,H,J,M,N,P,Q,R,S,U],[G,H,J,M,N,P,Q,R,U],[G,H,J,M,N,P,Q,S,U],[G,H,J,M,N,P,Q,U],[G,H,J,M,N,P,R,S,U],[G,H,J,M,N,P,R,U],[G,H,J,M,N,P,S,U],[G,H,J,M,N,P,U],[G,H,J,M,P,Q,R,S,U],[G,H,J,M,P,Q,R,U],[G,H,J,M,P,Q,S,U],[G,H,J,M,P,Q,U],[G,H,J,M,P,R,S,U],[G,H,J,M,P,R,U],[G,H,J,M,P,S,U],[G,H,J,M,P,U],[G,H,M,N,P,R,S,U],[G,H,M,N,P,S,U],[G,H,M,N,P,U],[G,H,M,P,R,S],[G,H,M,P,S,U],[G,H,M,P,U],[G,J],[G,J,M],[G,J,M,N,P,Q,R,S,U],[G,J,M,N,P,Q,R,U],[G,J,M,N,P,Q,S,U],[G,J,M,N,P,Q,U],[G,J,M,N,P,R,S,U],[G,J,M,N,P,R,U],[G,J,M,N,P,S,U],[G,J,M,N,P,U],[G,J,M,P],[G,J,M,P,Q],[G,J,M,P,Q,R],[G,J,M,P,Q,R,S],[G,J,M,P,Q,R,S,U],[G,J,M,P,Q,R,U],[G,J,M,P,Q,S],[G,J,M,P,Q,S,U],[G,J,M,P,Q,U],[G,J,M,P,R],[G,J,M,P,R,S],[G,J,M,P,R,S,U],[G,J,M,P,R,U],[G,J,M,P,S],[G,J,M,P,S,U],[G,J,M,P,U],[G,J,M,Q],[G,J,M,Q,R],[G,J,M,R],[G,J,Q],[G,J,Q,R],[G,J,R],[G,M],[G,M,N,P,R,U],[G,M,N,P,S,U],[G,M,N,P,U],[G,M,P],[G,M,P,R],[G,M,P,S],[G,M,P,S,U],[G,M,P,U],[G,M,R],[G,R],[H,J,M,N,P,Q,R,S,U],[H,J,M,N,P,Q,R,U],[H,J,M,N,P,Q,S,U],[H,J,M,N,P,Q,U],[H,J,M,N,P,R,S,U],[H,J,M,N,P,R,U],[H,J,M,N,P,S,U],[H,J,M,N,P,U],[H,J,M,P,Q,R,S,U],[H,J,M,P,Q,R,U],[H,J,M,P,Q,S,U],[H,J,M,P,Q,U],[H,J,M,P,R,S,U],[H,J,M,P,R,U],[H,J,M,P,S,U],[H,J,M,P,U],[H,M,N,P,S,U],[H,M,N,P,U],[H,M,P,S],[H,M,P,S,U],[H,M,P,U],[I,J],[I,J,V],[J],[J,M,N,P,Q,R,S,U],[J,M,N,P,Q,R,U],[J,M,N,P,Q,S,U],[J,M,N,P,Q,U],[J,M,N,P,R,S,U],[J,M,N,P,R,U],[J,M,N,P,S,U],[J,M,N,P,U],[J,M,P,Q],[J,M,P,Q,R],[J,M,P,Q,R,S],[J,M,P,Q,R,S,U],[J,M,P,Q,R,U],[J,M,P,Q,S],[J,M,P,Q,S,U],[J,M,P,Q,U],[J,M,P,R],[J,M,P,R,S],[J,M,P,R,S,U],[J,M,P,R,U],[J,M,P,S,U],[J,M,P,U],[J,Q],[J,Q,R],[J,R],[M],[M,N,P,S,U],[M,N,P,U],[M,P],[M,P,S],[M,P,S,U],[M,P,U]]),ground([E,K,L,O,T]),linear(I);mshare([[B,C,D,F,G,H,J,M,N,P,Q,R,S,U],[B,C,D,F,G,H,J,M,N,P,Q,R,U],[B,C,D,F,G,H,J,M,N,P,Q,S,U],[B,C,D,F,G,H,J,M,N,P,Q,U],[B,C,D,F,G,H,J,M,N,P,R,S,U],[B,C,D,F,G,H,J,M,N,P,R,U],[B,C,D,F,G,H,J,M,N,P,S,U],[B,C,D,F,G,H,J,M,N,P,U],[B,C,D,F,G,H,J,M,P,Q,R,S],[B,C,D,F,G,H,J,M,P,Q,R,S,U],[B,C,D,F,G,H,J,M,P,Q,R,U],[B,C,D,F,G,H,J,M,P,Q,S,U],[B,C,D,F,G,H,J,M,P,Q,U],[B,C,D,F,G,H,J,M,P,R,S,U],[B,C,D,F,G,H,J,M,P,R,U],[B,C,D,F,G,H,J,M,P,S,U],[B,C,D,F,G,H,J,M,P,U],[B,C,D,F,G,J],[B,C,D,F,G,J,M],[B,C,D,F,G,J,M,N,P,Q,R,S,U],[B,C,D,F,G,J,M,N,P,Q,R,U],[B,C,D,F,G,J,M,N,P,Q,S,U],[B,C,D,F,G,J,M,N,P,Q,U],[B,C,D,F,G,J,M,N,P,R,S,U],[B,C,D,F,G,J,M,N,P,R,U],[B,C,D,F,G,J,M,N,P,S,U],[B,C,D,F,G,J,M,N,P,U],[B,C,D,F,G,J,M,P],[B,C,D,F,G,J,M,P,Q],[B,C,D,F,G,J,M,P,Q,R],[B,C,D,F,G,J,M,P,Q,R,S],[B,C,D,F,G,J,M,P,Q,R,S,U],[B,C,D,F,G,J,M,P,Q,R,U],[B,C,D,F,G,J,M,P,Q,S],[B,C,D,F,G,J,M,P,Q,S,U],[B,C,D,F,G,J,M,P,Q,U],[B,C,D,F,G,J,M,P,R],[B,C,D,F,G,J,M,P,R,S],[B,C,D,F,G,J,M,P,R,S,U],[B,C,D,F,G,J,M,P,R,U],[B,C,D,F,G,J,M,P,S],[B,C,D,F,G,J,M,P,S,U],[B,C,D,F,G,J,M,P,U],[B,C,D,F,G,J,M,Q],[B,C,D,F,G,J,M,Q,R],[B,C,D,F,G,J,M,R],[B,C,D,F,G,J,Q],[B,C,D,F,G,J,Q,R],[B,C,D,F,G,J,R],[B,C,D,F,H,J,M,N,P,Q,R,S,U],[B,C,D,F,H,J,M,N,P,Q,R,U],[B,C,D,F,H,J,M,N,P,Q,S,U],[B,C,D,F,H,J,M,N,P,Q,U],[B,C,D,F,H,J,M,N,P,R,S,U],[B,C,D,F,H,J,M,N,P,R,U],[B,C,D,F,H,J,M,N,P,S,U],[B,C,D,F,H,J,M,N,P,U],[B,C,D,F,H,J,M,P,Q,R,S,U],[B,C,D,F,H,J,M,P,Q,R,U],[B,C,D,F,H,J,M,P,Q,S],[B,C,D,F,H,J,M,P,Q,S,U],[B,C,D,F,H,J,M,P,Q,U],[B,C,D,F,H,J,M,P,R,S,U],[B,C,D,F,H,J,M,P,R,U],[B,C,D,F,H,J,M,P,S,U],[B,C,D,F,H,J,M,P,U],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N,P,Q,R,S,U],[B,C,D,F,J,M,N,P,Q,R,U],[B,C,D,F,J,M,N,P,Q,S,U],[B,C,D,F,J,M,N,P,Q,U],[B,C,D,F,J,M,N,P,R,S,U],[B,C,D,F,J,M,N,P,R,U],[B,C,D,F,J,M,N,P,S,U],[B,C,D,F,J,M,N,P,U],[B,C,D,F,J,M,P],[B,C,D,F,J,M,P,Q],[B,C,D,F,J,M,P,Q,R],[B,C,D,F,J,M,P,Q,R,S],[B,C,D,F,J,M,P,Q,R,S,U],[B,C,D,F,J,M,P,Q,R,U],[B,C,D,F,J,M,P,Q,S],[B,C,D,F,J,M,P,Q,S,U],[B,C,D,F,J,M,P,Q,U],[B,C,D,F,J,M,P,R],[B,C,D,F,J,M,P,R,S],[B,C,D,F,J,M,P,R,S,U],[B,C,D,F,J,M,P,R,U],[B,C,D,F,J,M,P,S],[B,C,D,F,J,M,P,S,U],[B,C,D,F,J,M,P,U],[B,C,D,F,J,M,Q],[B,C,D,F,J,M,Q,R],[B,C,D,F,J,M,R],[B,C,D,F,J,Q],[B,C,D,F,J,Q,R],[B,C,D,F,J,R],[B,C,D,G,H,J,M,N,P,Q,R,S,U],[B,C,D,G,H,J,M,N,P,Q,R,U],[B,C,D,G,H,J,M,N,P,Q,S,U],[B,C,D,G,H,J,M,N,P,Q,U],[B,C,D,G,H,J,M,N,P,R,S,U],[B,C,D,G,H,J,M,N,P,R,U],[B,C,D,G,H,J,M,N,P,S,U],[B,C,D,G,H,J,M,N,P,U],[B,C,D,G,H,J,M,P,Q,R,S,U],[B,C,D,G,H,J,M,P,Q,R,U],[B,C,D,G,H,J,M,P,Q,S,U],[B,C,D,G,H,J,M,P,Q,U],[B,C,D,G,H,J,M,P,R,S],[B,C,D,G,H,J,M,P,R,S,U],[B,C,D,G,H,J,M,P,R,U],[B,C,D,G,H,J,M,P,S,U],[B,C,D,G,H,J,M,P,U],[B,C,D,G,J],[B,C,D,G,J,M],[B,C,D,G,J,M,N,P,Q,R,S,U],[B,C,D,G,J,M,N,P,Q,R,U],[B,C,D,G,J,M,N,P,Q,S,U],[B,C,D,G,J,M,N,P,Q,U],[B,C,D,G,J,M,N,P,R,S,U],[B,C,D,G,J,M,N,P,R,U],[B,C,D,G,J,M,N,P,S,U],[B,C,D,G,J,M,N,P,U],[B,C,D,G,J,M,P],[B,C,D,G,J,M,P,Q],[B,C,D,G,J,M,P,Q,R],[B,C,D,G,J,M,P,Q,R,S],[B,C,D,G,J,M,P,Q,R,S,U],[B,C,D,G,J,M,P,Q,R,U],[B,C,D,G,J,M,P,Q,S],[B,C,D,G,J,M,P,Q,S,U],[B,C,D,G,J,M,P,Q,U],[B,C,D,G,J,M,P,R],[B,C,D,G,J,M,P,R,S],[B,C,D,G,J,M,P,R,S,U],[B,C,D,G,J,M,P,R,U],[B,C,D,G,J,M,P,S],[B,C,D,G,J,M,P,S,U],[B,C,D,G,J,M,P,U],[B,C,D,G,J,M,Q],[B,C,D,G,J,M,Q,R],[B,C,D,G,J,M,R],[B,C,D,G,J,Q],[B,C,D,G,J,Q,R],[B,C,D,G,J,R],[B,C,D,H,J,M,N,P,Q,R,S,U],[B,C,D,H,J,M,N,P,Q,R,U],[B,C,D,H,J,M,N,P,Q,S,U],[B,C,D,H,J,M,N,P,Q,U],[B,C,D,H,J,M,N,P,R,S,U],[B,C,D,H,J,M,N,P,R,U],[B,C,D,H,J,M,N,P,S,U],[B,C,D,H,J,M,N,P,U],[B,C,D,H,J,M,P,Q,R,S,U],[B,C,D,H,J,M,P,Q,R,U],[B,C,D,H,J,M,P,Q,S,U],[B,C,D,H,J,M,P,Q,U],[B,C,D,H,J,M,P,R,S,U],[B,C,D,H,J,M,P,R,U],[B,C,D,H,J,M,P,S],[B,C,D,H,J,M,P,S,U],[B,C,D,H,J,M,P,U],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N,P,Q,R,S,U],[B,C,D,J,M,N,P,Q,R,U],[B,C,D,J,M,N,P,Q,S,U],[B,C,D,J,M,N,P,Q,U],[B,C,D,J,M,N,P,R,S,U],[B,C,D,J,M,N,P,R,U],[B,C,D,J,M,N,P,S,U],[B,C,D,J,M,N,P,U],[B,C,D,J,M,P],[B,C,D,J,M,P,Q],[B,C,D,J,M,P,Q,R],[B,C,D,J,M,P,Q,R,S],[B,C,D,J,M,P,Q,R,S,U],[B,C,D,J,M,P,Q,R,U],[B,C,D,J,M,P,Q,S],[B,C,D,J,M,P,Q,S,U],[B,C,D,J,M,P,Q,U],[B,C,D,J,M,P,R],[B,C,D,J,M,P,R,S],[B,C,D,J,M,P,R,S,U],[B,C,D,J,M,P,R,U],[B,C,D,J,M,P,S],[B,C,D,J,M,P,S,U],[B,C,D,J,M,P,U],[B,C,D,J,M,Q],[B,C,D,J,M,Q,R],[B,C,D,J,M,R],[B,C,D,J,Q],[B,C,D,J,Q,R],[B,C,D,J,R],[B,C,F,G,H,J,M,N,P,Q,R,S,U],[B,C,F,G,H,J,M,N,P,Q,R,U],[B,C,F,G,H,J,M,N,P,Q,S,U],[B,C,F,G,H,J,M,N,P,Q,U],[B,C,F,G,H,J,M,N,P,R,S,U],[B,C,F,G,H,J,M,N,P,R,U],[B,C,F,G,H,J,M,N,P,S,U],[B,C,F,G,H,J,M,N,P,U],[B,C,F,G,H,J,M,P,Q,R,S],[B,C,F,G,H,J,M,P,Q,R,S,U],[B,C,F,G,H,J,M,P,Q,R,U],[B,C,F,G,H,J,M,P,Q,S,U],[B,C,F,G,H,J,M,P,Q,U],[B,C,F,G,H,J,M,P,R,S,U],[B,C,F,G,H,J,M,P,R,U],[B,C,F,G,H,J,M,P,S,U],[B,C,F,G,H,J,M,P,U],[B,C,F,G,J],[B,C,F,G,J,M],[B,C,F,G,J,M,N,P,Q,R,S,U],[B,C,F,G,J,M,N,P,Q,R,U],[B,C,F,G,J,M,N,P,Q,S,U],[B,C,F,G,J,M,N,P,Q,U],[B,C,F,G,J,M,N,P,R,S,U],[B,C,F,G,J,M,N,P,R,U],[B,C,F,G,J,M,N,P,S,U],[B,C,F,G,J,M,N,P,U],[B,C,F,G,J,M,P],[B,C,F,G,J,M,P,Q],[B,C,F,G,J,M,P,Q,R],[B,C,F,G,J,M,P,Q,R,S],[B,C,F,G,J,M,P,Q,R,S,U],[B,C,F,G,J,M,P,Q,R,U],[B,C,F,G,J,M,P,Q,S],[B,C,F,G,J,M,P,Q,S,U],[B,C,F,G,J,M,P,Q,U],[B,C,F,G,J,M,P,R],[B,C,F,G,J,M,P,R,S],[B,C,F,G,J,M,P,R,S,U],[B,C,F,G,J,M,P,R,U],[B,C,F,G,J,M,P,S],[B,C,F,G,J,M,P,S,U],[B,C,F,G,J,M,P,U],[B,C,F,G,J,M,Q],[B,C,F,G,J,M,Q,R],[B,C,F,G,J,M,R],[B,C,F,G,J,Q],[B,C,F,G,J,Q,R],[B,C,F,G,J,R],[B,C,F,H,J,M,N,P,Q,R,S,U],[B,C,F,H,J,M,N,P,Q,R,U],[B,C,F,H,J,M,N,P,Q,S,U],[B,C,F,H,J,M,N,P,Q,U],[B,C,F,H,J,M,N,P,R,S,U],[B,C,F,H,J,M,N,P,R,U],[B,C,F,H,J,M,N,P,S,U],[B,C,F,H,J,M,N,P,U],[B,C,F,H,J,M,P,Q,R,S,U],[B,C,F,H,J,M,P,Q,R,U],[B,C,F,H,J,M,P,Q,S],[B,C,F,H,J,M,P,Q,S,U],[B,C,F,H,J,M,P,Q,U],[B,C,F,H,J,M,P,R,S,U],[B,C,F,H,J,M,P,R,U],[B,C,F,H,J,M,P,S,U],[B,C,F,H,J,M,P,U],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N,P,Q,R,S,U],[B,C,F,J,M,N,P,Q,R,U],[B,C,F,J,M,N,P,Q,S,U],[B,C,F,J,M,N,P,Q,U],[B,C,F,J,M,N,P,R,S,U],[B,C,F,J,M,N,P,R,U],[B,C,F,J,M,N,P,S,U],[B,C,F,J,M,N,P,U],[B,C,F,J,M,P],[B,C,F,J,M,P,Q],[B,C,F,J,M,P,Q,R],[B,C,F,J,M,P,Q,R,S],[B,C,F,J,M,P,Q,R,S,U],[B,C,F,J,M,P,Q,R,U],[B,C,F,J,M,P,Q,S],[B,C,F,J,M,P,Q,S,U],[B,C,F,J,M,P,Q,U],[B,C,F,J,M,P,R],[B,C,F,J,M,P,R,S],[B,C,F,J,M,P,R,S,U],[B,C,F,J,M,P,R,U],[B,C,F,J,M,P,S],[B,C,F,J,M,P,S,U],[B,C,F,J,M,P,U],[B,C,F,J,M,Q],[B,C,F,J,M,Q,R],[B,C,F,J,M,R],[B,C,F,J,Q],[B,C,F,J,Q,R],[B,C,F,J,R],[B,C,G,H,J,M,N,P,Q,R,S,U],[B,C,G,H,J,M,N,P,Q,R,U],[B,C,G,H,J,M,N,P,Q,S,U],[B,C,G,H,J,M,N,P,Q,U],[B,C,G,H,J,M,N,P,R,S,U],[B,C,G,H,J,M,N,P,R,U],[B,C,G,H,J,M,N,P,S,U],[B,C,G,H,J,M,N,P,U],[B,C,G,H,J,M,P,Q,R,S,U],[B,C,G,H,J,M,P,Q,R,U],[B,C,G,H,J,M,P,Q,S,U],[B,C,G,H,J,M,P,Q,U],[B,C,G,H,J,M,P,R,S],[B,C,G,H,J,M,P,R,S,U],[B,C,G,H,J,M,P,R,U],[B,C,G,H,J,M,P,S,U],[B,C,G,H,J,M,P,U],[B,C,G,J],[B,C,G,J,M],[B,C,G,J,M,N,P,Q,R,S,U],[B,C,G,J,M,N,P,Q,R,U],[B,C,G,J,M,N,P,Q,S,U],[B,C,G,J,M,N,P,Q,U],[B,C,G,J,M,N,P,R,S,U],[B,C,G,J,M,N,P,R,U],[B,C,G,J,M,N,P,S,U],[B,C,G,J,M,N,P,U],[B,C,G,J,M,P],[B,C,G,J,M,P,Q],[B,C,G,J,M,P,Q,R],[B,C,G,J,M,P,Q,R,S],[B,C,G,J,M,P,Q,R,S,U],[B,C,G,J,M,P,Q,R,U],[B,C,G,J,M,P,Q,S],[B,C,G,J,M,P,Q,S,U],[B,C,G,J,M,P,Q,U],[B,C,G,J,M,P,R],[B,C,G,J,M,P,R,S],[B,C,G,J,M,P,R,S,U],[B,C,G,J,M,P,R,U],[B,C,G,J,M,P,S],[B,C,G,J,M,P,S,U],[B,C,G,J,M,P,U],[B,C,G,J,M,Q],[B,C,G,J,M,Q,R],[B,C,G,J,M,R],[B,C,G,J,Q],[B,C,G,J,Q,R],[B,C,G,J,R],[B,C,H,J,M,N,P,Q,R,S,U],[B,C,H,J,M,N,P,Q,R,U],[B,C,H,J,M,N,P,Q,S,U],[B,C,H,J,M,N,P,Q,U],[B,C,H,J,M,N,P,R,S,U],[B,C,H,J,M,N,P,R,U],[B,C,H,J,M,N,P,S,U],[B,C,H,J,M,N,P,U],[B,C,H,J,M,P,Q,R,S,U],[B,C,H,J,M,P,Q,R,U],[B,C,H,J,M,P,Q,S,U],[B,C,H,J,M,P,Q,U],[B,C,H,J,M,P,R,S,U],[B,C,H,J,M,P,R,U],[B,C,H,J,M,P,S],[B,C,H,J,M,P,S,U],[B,C,H,J,M,P,U],[B,C,J],[B,C,J,M],[B,C,J,M,N,P,Q,R,S,U],[B,C,J,M,N,P,Q,R,U],[B,C,J,M,N,P,Q,S,U],[B,C,J,M,N,P,Q,U],[B,C,J,M,N,P,R,S,U],[B,C,J,M,N,P,R,U],[B,C,J,M,N,P,S,U],[B,C,J,M,N,P,U],[B,C,J,M,P],[B,C,J,M,P,Q],[B,C,J,M,P,Q,R],[B,C,J,M,P,Q,R,S],[B,C,J,M,P,Q,R,S,U],[B,C,J,M,P,Q,R,U],[B,C,J,M,P,Q,S],[B,C,J,M,P,Q,S,U],[B,C,J,M,P,Q,U],[B,C,J,M,P,R],[B,C,J,M,P,R,S],[B,C,J,M,P,R,S,U],[B,C,J,M,P,R,U],[B,C,J,M,P,S],[B,C,J,M,P,S,U],[B,C,J,M,P,U],[B,C,J,M,Q],[B,C,J,M,Q,R],[B,C,J,M,R],[B,C,J,Q],[B,C,J,Q,R],[B,C,J,R],[B,D,F,G,H,J,M,N,P,Q,R,S,U],[B,D,F,G,H,J,M,N,P,Q,R,U],[B,D,F,G,H,J,M,N,P,Q,S,U],[B,D,F,G,H,J,M,N,P,Q,U],[B,D,F,G,H,J,M,N,P,R,S,U],[B,D,F,G,H,J,M,N,P,R,U],[B,D,F,G,H,J,M,N,P,S,U],[B,D,F,G,H,J,M,N,P,U],[B,D,F,G,H,J,M,P,Q,R,S],[B,D,F,G,H,J,M,P,Q,R,S,U],[B,D,F,G,H,J,M,P,Q,R,U],[B,D,F,G,H,J,M,P,Q,S,U],[B,D,F,G,H,J,M,P,Q,U],[B,D,F,G,H,J,M,P,R,S,U],[B,D,F,G,H,J,M,P,R,U],[B,D,F,G,H,J,M,P,S,U],[B,D,F,G,H,J,M,P,U],[B,D,F,G,J],[B,D,F,G,J,M],[B,D,F,G,J,M,N,P,Q,R,S,U],[B,D,F,G,J,M,N,P,Q,R,U],[B,D,F,G,J,M,N,P,Q,S,U],[B,D,F,G,J,M,N,P,Q,U],[B,D,F,G,J,M,N,P,R,S,U],[B,D,F,G,J,M,N,P,R,U],[B,D,F,G,J,M,N,P,S,U],[B,D,F,G,J,M,N,P,U],[B,D,F,G,J,M,P],[B,D,F,G,J,M,P,Q],[B,D,F,G,J,M,P,Q,R],[B,D,F,G,J,M,P,Q,R,S],[B,D,F,G,J,M,P,Q,R,S,U],[B,D,F,G,J,M,P,Q,R,U],[B,D,F,G,J,M,P,Q,S],[B,D,F,G,J,M,P,Q,S,U],[B,D,F,G,J,M,P,Q,U],[B,D,F,G,J,M,P,R],[B,D,F,G,J,M,P,R,S],[B,D,F,G,J,M,P,R,S,U],[B,D,F,G,J,M,P,R,U],[B,D,F,G,J,M,P,S],[B,D,F,G,J,M,P,S,U],[B,D,F,G,J,M,P,U],[B,D,F,G,J,M,Q],[B,D,F,G,J,M,Q,R],[B,D,F,G,J,M,R],[B,D,F,G,J,Q],[B,D,F,G,J,Q,R],[B,D,F,G,J,R],[B,D,F,H,J,M,N,P,Q,R,S,U],[B,D,F,H,J,M,N,P,Q,R,U],[B,D,F,H,J,M,N,P,Q,S,U],[B,D,F,H,J,M,N,P,Q,U],[B,D,F,H,J,M,N,P,R,S,U],[B,D,F,H,J,M,N,P,R,U],[B,D,F,H,J,M,N,P,S,U],[B,D,F,H,J,M,N,P,U],[B,D,F,H,J,M,P,Q,R,S,U],[B,D,F,H,J,M,P,Q,R,U],[B,D,F,H,J,M,P,Q,S],[B,D,F,H,J,M,P,Q,S,U],[B,D,F,H,J,M,P,Q,U],[B,D,F,H,J,M,P,R,S,U],[B,D,F,H,J,M,P,R,U],[B,D,F,H,J,M,P,S,U],[B,D,F,H,J,M,P,U],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N,P,Q,R,S,U],[B,D,F,J,M,N,P,Q,R,U],[B,D,F,J,M,N,P,Q,S,U],[B,D,F,J,M,N,P,Q,U],[B,D,F,J,M,N,P,R,S,U],[B,D,F,J,M,N,P,R,U],[B,D,F,J,M,N,P,S,U],[B,D,F,J,M,N,P,U],[B,D,F,J,M,P],[B,D,F,J,M,P,Q],[B,D,F,J,M,P,Q,R],[B,D,F,J,M,P,Q,R,S],[B,D,F,J,M,P,Q,R,S,U],[B,D,F,J,M,P,Q,R,U],[B,D,F,J,M,P,Q,S],[B,D,F,J,M,P,Q,S,U],[B,D,F,J,M,P,Q,U],[B,D,F,J,M,P,R],[B,D,F,J,M,P,R,S],[B,D,F,J,M,P,R,S,U],[B,D,F,J,M,P,R,U],[B,D,F,J,M,P,S],[B,D,F,J,M,P,S,U],[B,D,F,J,M,P,U],[B,D,F,J,M,Q],[B,D,F,J,M,Q,R],[B,D,F,J,M,R],[B,D,F,J,Q],[B,D,F,J,Q,R],[B,D,F,J,R],[B,D,G,H,J,M,N,P,Q,R,S,U],[B,D,G,H,J,M,N,P,Q,R,U],[B,D,G,H,J,M,N,P,Q,S,U],[B,D,G,H,J,M,N,P,Q,U],[B,D,G,H,J,M,N,P,R,S,U],[B,D,G,H,J,M,N,P,R,U],[B,D,G,H,J,M,N,P,S,U],[B,D,G,H,J,M,N,P,U],[B,D,G,H,J,M,P,Q,R,S,U],[B,D,G,H,J,M,P,Q,R,U],[B,D,G,H,J,M,P,Q,S,U],[B,D,G,H,J,M,P,Q,U],[B,D,G,H,J,M,P,R,S],[B,D,G,H,J,M,P,R,S,U],[B,D,G,H,J,M,P,R,U],[B,D,G,H,J,M,P,S,U],[B,D,G,H,J,M,P,U],[B,D,G,J],[B,D,G,J,M],[B,D,G,J,M,N,P,Q,R,S,U],[B,D,G,J,M,N,P,Q,R,U],[B,D,G,J,M,N,P,Q,S,U],[B,D,G,J,M,N,P,Q,U],[B,D,G,J,M,N,P,R,S,U],[B,D,G,J,M,N,P,R,U],[B,D,G,J,M,N,P,S,U],[B,D,G,J,M,N,P,U],[B,D,G,J,M,P],[B,D,G,J,M,P,Q],[B,D,G,J,M,P,Q,R],[B,D,G,J,M,P,Q,R,S],[B,D,G,J,M,P,Q,R,S,U],[B,D,G,J,M,P,Q,R,U],[B,D,G,J,M,P,Q,S],[B,D,G,J,M,P,Q,S,U],[B,D,G,J,M,P,Q,U],[B,D,G,J,M,P,R],[B,D,G,J,M,P,R,S],[B,D,G,J,M,P,R,S,U],[B,D,G,J,M,P,R,U],[B,D,G,J,M,P,S],[B,D,G,J,M,P,S,U],[B,D,G,J,M,P,U],[B,D,G,J,M,Q],[B,D,G,J,M,Q,R],[B,D,G,J,M,R],[B,D,G,J,Q],[B,D,G,J,Q,R],[B,D,G,J,R],[B,D,H,J,M,N,P,Q,R,S,U],[B,D,H,J,M,N,P,Q,R,U],[B,D,H,J,M,N,P,Q,S,U],[B,D,H,J,M,N,P,Q,U],[B,D,H,J,M,N,P,R,S,U],[B,D,H,J,M,N,P,R,U],[B,D,H,J,M,N,P,S,U],[B,D,H,J,M,N,P,U],[B,D,H,J,M,P,Q,R,S,U],[B,D,H,J,M,P,Q,R,U],[B,D,H,J,M,P,Q,S,U],[B,D,H,J,M,P,Q,U],[B,D,H,J,M,P,R,S,U],[B,D,H,J,M,P,R,U],[B,D,H,J,M,P,S],[B,D,H,J,M,P,S,U],[B,D,H,J,M,P,U],[B,D,J],[B,D,J,M],[B,D,J,M,N,P,Q,R,S,U],[B,D,J,M,N,P,Q,R,U],[B,D,J,M,N,P,Q,S,U],[B,D,J,M,N,P,Q,U],[B,D,J,M,N,P,R,S,U],[B,D,J,M,N,P,R,U],[B,D,J,M,N,P,S,U],[B,D,J,M,N,P,U],[B,D,J,M,P],[B,D,J,M,P,Q],[B,D,J,M,P,Q,R],[B,D,J,M,P,Q,R,S],[B,D,J,M,P,Q,R,S,U],[B,D,J,M,P,Q,R,U],[B,D,J,M,P,Q,S],[B,D,J,M,P,Q,S,U],[B,D,J,M,P,Q,U],[B,D,J,M,P,R],[B,D,J,M,P,R,S],[B,D,J,M,P,R,S,U],[B,D,J,M,P,R,U],[B,D,J,M,P,S],[B,D,J,M,P,S,U],[B,D,J,M,P,U],[B,D,J,M,Q],[B,D,J,M,Q,R],[B,D,J,M,R],[B,D,J,Q],[B,D,J,Q,R],[B,D,J,R],[B,F,G,H,J,M,N,P,Q,R,S,U],[B,F,G,H,J,M,N,P,Q,R,U],[B,F,G,H,J,M,N,P,Q,S,U],[B,F,G,H,J,M,N,P,Q,U],[B,F,G,H,J,M,N,P,R,S,U],[B,F,G,H,J,M,N,P,R,U],[B,F,G,H,J,M,N,P,S,U],[B,F,G,H,J,M,N,P,U],[B,F,G,H,J,M,P,Q,R,S],[B,F,G,H,J,M,P,Q,R,S,U],[B,F,G,H,J,M,P,Q,R,U],[B,F,G,H,J,M,P,Q,S,U],[B,F,G,H,J,M,P,Q,U],[B,F,G,H,J,M,P,R,S,U],[B,F,G,H,J,M,P,R,U],[B,F,G,H,J,M,P,S,U],[B,F,G,H,J,M,P,U],[B,F,G,J],[B,F,G,J,M],[B,F,G,J,M,N,P,Q,R,S,U],[B,F,G,J,M,N,P,Q,R,U],[B,F,G,J,M,N,P,Q,S,U],[B,F,G,J,M,N,P,Q,U],[B,F,G,J,M,N,P,R,S,U],[B,F,G,J,M,N,P,R,U],[B,F,G,J,M,N,P,S,U],[B,F,G,J,M,N,P,U],[B,F,G,J,M,P],[B,F,G,J,M,P,Q],[B,F,G,J,M,P,Q,R],[B,F,G,J,M,P,Q,R,S],[B,F,G,J,M,P,Q,R,S,U],[B,F,G,J,M,P,Q,R,U],[B,F,G,J,M,P,Q,S],[B,F,G,J,M,P,Q,S,U],[B,F,G,J,M,P,Q,U],[B,F,G,J,M,P,R],[B,F,G,J,M,P,R,S],[B,F,G,J,M,P,R,S,U],[B,F,G,J,M,P,R,U],[B,F,G,J,M,P,S],[B,F,G,J,M,P,S,U],[B,F,G,J,M,P,U],[B,F,G,J,M,Q],[B,F,G,J,M,Q,R],[B,F,G,J,M,R],[B,F,G,J,Q],[B,F,G,J,Q,R],[B,F,G,J,R],[B,F,H,J,M,N,P,Q,R,S,U],[B,F,H,J,M,N,P,Q,R,U],[B,F,H,J,M,N,P,Q,S,U],[B,F,H,J,M,N,P,Q,U],[B,F,H,J,M,N,P,R,S,U],[B,F,H,J,M,N,P,R,U],[B,F,H,J,M,N,P,S,U],[B,F,H,J,M,N,P,U],[B,F,H,J,M,P,Q,R,S,U],[B,F,H,J,M,P,Q,R,U],[B,F,H,J,M,P,Q,S],[B,F,H,J,M,P,Q,S,U],[B,F,H,J,M,P,Q,U],[B,F,H,J,M,P,R,S,U],[B,F,H,J,M,P,R,U],[B,F,H,J,M,P,S,U],[B,F,H,J,M,P,U],[B,F,J],[B,F,J,M],[B,F,J,M,N,P,Q,R,S,U],[B,F,J,M,N,P,Q,R,U],[B,F,J,M,N,P,Q,S,U],[B,F,J,M,N,P,Q,U],[B,F,J,M,N,P,R,S,U],[B,F,J,M,N,P,R,U],[B,F,J,M,N,P,S,U],[B,F,J,M,N,P,U],[B,F,J,M,P],[B,F,J,M,P,Q],[B,F,J,M,P,Q,R],[B,F,J,M,P,Q,R,S],[B,F,J,M,P,Q,R,S,U],[B,F,J,M,P,Q,R,U],[B,F,J,M,P,Q,S],[B,F,J,M,P,Q,S,U],[B,F,J,M,P,Q,U],[B,F,J,M,P,R],[B,F,J,M,P,R,S],[B,F,J,M,P,R,S,U],[B,F,J,M,P,R,U],[B,F,J,M,P,S],[B,F,J,M,P,S,U],[B,F,J,M,P,U],[B,F,J,M,Q],[B,F,J,M,Q,R],[B,F,J,M,R],[B,F,J,Q],[B,F,J,Q,R],[B,F,J,R],[B,G,H,J,M,N,P,Q,R,S,U],[B,G,H,J,M,N,P,Q,R,U],[B,G,H,J,M,N,P,Q,S,U],[B,G,H,J,M,N,P,Q,U],[B,G,H,J,M,N,P,R,S,U],[B,G,H,J,M,N,P,R,U],[B,G,H,J,M,N,P,S,U],[B,G,H,J,M,N,P,U],[B,G,H,J,M,P,Q,R,S,U],[B,G,H,J,M,P,Q,R,U],[B,G,H,J,M,P,Q,S,U],[B,G,H,J,M,P,Q,U],[B,G,H,J,M,P,R,S],[B,G,H,J,M,P,R,S,U],[B,G,H,J,M,P,R,U],[B,G,H,J,M,P,S,U],[B,G,H,J,M,P,U],[B,G,J],[B,G,J,M],[B,G,J,M,N,P,Q,R,S,U],[B,G,J,M,N,P,Q,R,U],[B,G,J,M,N,P,Q,S,U],[B,G,J,M,N,P,Q,U],[B,G,J,M,N,P,R,S,U],[B,G,J,M,N,P,R,U],[B,G,J,M,N,P,S,U],[B,G,J,M,N,P,U],[B,G,J,M,P],[B,G,J,M,P,Q],[B,G,J,M,P,Q,R],[B,G,J,M,P,Q,R,S],[B,G,J,M,P,Q,R,S,U],[B,G,J,M,P,Q,R,U],[B,G,J,M,P,Q,S],[B,G,J,M,P,Q,S,U],[B,G,J,M,P,Q,U],[B,G,J,M,P,R],[B,G,J,M,P,R,S],[B,G,J,M,P,R,S,U],[B,G,J,M,P,R,U],[B,G,J,M,P,S],[B,G,J,M,P,S,U],[B,G,J,M,P,U],[B,G,J,M,Q],[B,G,J,M,Q,R],[B,G,J,M,R],[B,G,J,Q],[B,G,J,Q,R],[B,G,J,R],[B,H,J,M,N,P,Q,R,S,U],[B,H,J,M,N,P,Q,R,U],[B,H,J,M,N,P,Q,S,U],[B,H,J,M,N,P,Q,U],[B,H,J,M,N,P,R,S,U],[B,H,J,M,N,P,R,U],[B,H,J,M,N,P,S,U],[B,H,J,M,N,P,U],[B,H,J,M,P,Q,R,S,U],[B,H,J,M,P,Q,R,U],[B,H,J,M,P,Q,S,U],[B,H,J,M,P,Q,U],[B,H,J,M,P,R,S,U],[B,H,J,M,P,R,U],[B,H,J,M,P,S],[B,H,J,M,P,S,U],[B,H,J,M,P,U],[B,J],[B,J,M],[B,J,M,N,P,Q,R,S,U],[B,J,M,N,P,Q,R,U],[B,J,M,N,P,Q,S,U],[B,J,M,N,P,Q,U],[B,J,M,N,P,R,S,U],[B,J,M,N,P,R,U],[B,J,M,N,P,S,U],[B,J,M,N,P,U],[B,J,M,P],[B,J,M,P,Q],[B,J,M,P,Q,R],[B,J,M,P,Q,R,S],[B,J,M,P,Q,R,S,U],[B,J,M,P,Q,R,U],[B,J,M,P,Q,S],[B,J,M,P,Q,S,U],[B,J,M,P,Q,U],[B,J,M,P,R],[B,J,M,P,R,S],[B,J,M,P,R,S,U],[B,J,M,P,R,U],[B,J,M,P,S],[B,J,M,P,S,U],[B,J,M,P,U],[B,J,M,Q],[B,J,M,Q,R],[B,J,M,R],[B,J,Q],[B,J,Q,R],[B,J,R],[C,D,F,G,H,J,M,N,P,Q,R,S,U],[C,D,F,G,H,J,M,N,P,Q,R,U],[C,D,F,G,H,J,M,N,P,Q,S,U],[C,D,F,G,H,J,M,N,P,Q,U],[C,D,F,G,H,J,M,N,P,R,S,U],[C,D,F,G,H,J,M,N,P,R,U],[C,D,F,G,H,J,M,N,P,S,U],[C,D,F,G,H,J,M,N,P,U],[C,D,F,G,H,J,M,P,Q,R,S],[C,D,F,G,H,J,M,P,Q,R,S,U],[C,D,F,G,H,J,M,P,Q,R,U],[C,D,F,G,H,J,M,P,Q,S,U],[C,D,F,G,H,J,M,P,Q,U],[C,D,F,G,H,J,M,P,R,S,U],[C,D,F,G,H,J,M,P,R,U],[C,D,F,G,H,J,M,P,S,U],[C,D,F,G,H,J,M,P,U],[C,D,F,G,J],[C,D,F,G,J,M],[C,D,F,G,J,M,N,P,Q,R,S,U],[C,D,F,G,J,M,N,P,Q,R,U],[C,D,F,G,J,M,N,P,Q,S,U],[C,D,F,G,J,M,N,P,Q,U],[C,D,F,G,J,M,N,P,R,S,U],[C,D,F,G,J,M,N,P,R,U],[C,D,F,G,J,M,N,P,S,U],[C,D,F,G,J,M,N,P,U],[C,D,F,G,J,M,P],[C,D,F,G,J,M,P,Q],[C,D,F,G,J,M,P,Q,R],[C,D,F,G,J,M,P,Q,R,S],[C,D,F,G,J,M,P,Q,R,S,U],[C,D,F,G,J,M,P,Q,R,U],[C,D,F,G,J,M,P,Q,S],[C,D,F,G,J,M,P,Q,S,U],[C,D,F,G,J,M,P,Q,U],[C,D,F,G,J,M,P,R],[C,D,F,G,J,M,P,R,S],[C,D,F,G,J,M,P,R,S,U],[C,D,F,G,J,M,P,R,U],[C,D,F,G,J,M,P,S],[C,D,F,G,J,M,P,S,U],[C,D,F,G,J,M,P,U],[C,D,F,G,J,M,Q],[C,D,F,G,J,M,Q,R],[C,D,F,G,J,M,R],[C,D,F,G,J,Q],[C,D,F,G,J,Q,R],[C,D,F,G,J,R],[C,D,F,H,J,M,N,P,Q,R,S,U],[C,D,F,H,J,M,N,P,Q,R,U],[C,D,F,H,J,M,N,P,Q,S,U],[C,D,F,H,J,M,N,P,Q,U],[C,D,F,H,J,M,N,P,R,S,U],[C,D,F,H,J,M,N,P,R,U],[C,D,F,H,J,M,N,P,S,U],[C,D,F,H,J,M,N,P,U],[C,D,F,H,J,M,P,Q,R,S,U],[C,D,F,H,J,M,P,Q,R,U],[C,D,F,H,J,M,P,Q,S],[C,D,F,H,J,M,P,Q,S,U],[C,D,F,H,J,M,P,Q,U],[C,D,F,H,J,M,P,R,S,U],[C,D,F,H,J,M,P,R,U],[C,D,F,H,J,M,P,S,U],[C,D,F,H,J,M,P,U],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N,P,Q,R,S,U],[C,D,F,J,M,N,P,Q,R,U],[C,D,F,J,M,N,P,Q,S,U],[C,D,F,J,M,N,P,Q,U],[C,D,F,J,M,N,P,R,S,U],[C,D,F,J,M,N,P,R,U],[C,D,F,J,M,N,P,S,U],[C,D,F,J,M,N,P,U],[C,D,F,J,M,P],[C,D,F,J,M,P,Q],[C,D,F,J,M,P,Q,R],[C,D,F,J,M,P,Q,R,S],[C,D,F,J,M,P,Q,R,S,U],[C,D,F,J,M,P,Q,R,U],[C,D,F,J,M,P,Q,S],[C,D,F,J,M,P,Q,S,U],[C,D,F,J,M,P,Q,U],[C,D,F,J,M,P,R],[C,D,F,J,M,P,R,S],[C,D,F,J,M,P,R,S,U],[C,D,F,J,M,P,R,U],[C,D,F,J,M,P,S],[C,D,F,J,M,P,S,U],[C,D,F,J,M,P,U],[C,D,F,J,M,Q],[C,D,F,J,M,Q,R],[C,D,F,J,M,R],[C,D,F,J,Q],[C,D,F,J,Q,R],[C,D,F,J,R],[C,D,G,H,J,M,N,P,Q,R,S,U],[C,D,G,H,J,M,N,P,Q,R,U],[C,D,G,H,J,M,N,P,Q,S,U],[C,D,G,H,J,M,N,P,Q,U],[C,D,G,H,J,M,N,P,R,S,U],[C,D,G,H,J,M,N,P,R,U],[C,D,G,H,J,M,N,P,S,U],[C,D,G,H,J,M,N,P,U],[C,D,G,H,J,M,P,Q,R,S,U],[C,D,G,H,J,M,P,Q,R,U],[C,D,G,H,J,M,P,Q,S,U],[C,D,G,H,J,M,P,Q,U],[C,D,G,H,J,M,P,R,S],[C,D,G,H,J,M,P,R,S,U],[C,D,G,H,J,M,P,R,U],[C,D,G,H,J,M,P,S,U],[C,D,G,H,J,M,P,U],[C,D,G,J],[C,D,G,J,M],[C,D,G,J,M,N,P,Q,R,S,U],[C,D,G,J,M,N,P,Q,R,U],[C,D,G,J,M,N,P,Q,S,U],[C,D,G,J,M,N,P,Q,U],[C,D,G,J,M,N,P,R,S,U],[C,D,G,J,M,N,P,R,U],[C,D,G,J,M,N,P,S,U],[C,D,G,J,M,N,P,U],[C,D,G,J,M,P],[C,D,G,J,M,P,Q],[C,D,G,J,M,P,Q,R],[C,D,G,J,M,P,Q,R,S],[C,D,G,J,M,P,Q,R,S,U],[C,D,G,J,M,P,Q,R,U],[C,D,G,J,M,P,Q,S],[C,D,G,J,M,P,Q,S,U],[C,D,G,J,M,P,Q,U],[C,D,G,J,M,P,R],[C,D,G,J,M,P,R,S],[C,D,G,J,M,P,R,S,U],[C,D,G,J,M,P,R,U],[C,D,G,J,M,P,S],[C,D,G,J,M,P,S,U],[C,D,G,J,M,P,U],[C,D,G,J,M,Q],[C,D,G,J,M,Q,R],[C,D,G,J,M,R],[C,D,G,J,Q],[C,D,G,J,Q,R],[C,D,G,J,R],[C,D,H,J,M,N,P,Q,R,S,U],[C,D,H,J,M,N,P,Q,R,U],[C,D,H,J,M,N,P,Q,S,U],[C,D,H,J,M,N,P,Q,U],[C,D,H,J,M,N,P,R,S,U],[C,D,H,J,M,N,P,R,U],[C,D,H,J,M,N,P,S,U],[C,D,H,J,M,N,P,U],[C,D,H,J,M,P,Q,R,S,U],[C,D,H,J,M,P,Q,R,U],[C,D,H,J,M,P,Q,S,U],[C,D,H,J,M,P,Q,U],[C,D,H,J,M,P,R,S,U],[C,D,H,J,M,P,R,U],[C,D,H,J,M,P,S],[C,D,H,J,M,P,S,U],[C,D,H,J,M,P,U],[C,D,J],[C,D,J,M],[C,D,J,M,N,P,Q,R,S,U],[C,D,J,M,N,P,Q,R,U],[C,D,J,M,N,P,Q,S,U],[C,D,J,M,N,P,Q,U],[C,D,J,M,N,P,R,S,U],[C,D,J,M,N,P,R,U],[C,D,J,M,N,P,S,U],[C,D,J,M,N,P,U],[C,D,J,M,P],[C,D,J,M,P,Q],[C,D,J,M,P,Q,R],[C,D,J,M,P,Q,R,S],[C,D,J,M,P,Q,R,S,U],[C,D,J,M,P,Q,R,U],[C,D,J,M,P,Q,S],[C,D,J,M,P,Q,S,U],[C,D,J,M,P,Q,U],[C,D,J,M,P,R],[C,D,J,M,P,R,S],[C,D,J,M,P,R,S,U],[C,D,J,M,P,R,U],[C,D,J,M,P,S],[C,D,J,M,P,S,U],[C,D,J,M,P,U],[C,D,J,M,Q],[C,D,J,M,Q,R],[C,D,J,M,R],[C,D,J,Q],[C,D,J,Q,R],[C,D,J,R],[C,F,G,H,J,M,N,P,Q,R,S,U],[C,F,G,H,J,M,N,P,Q,R,U],[C,F,G,H,J,M,N,P,Q,S,U],[C,F,G,H,J,M,N,P,Q,U],[C,F,G,H,J,M,N,P,R,S,U],[C,F,G,H,J,M,N,P,R,U],[C,F,G,H,J,M,N,P,S,U],[C,F,G,H,J,M,N,P,U],[C,F,G,H,J,M,P,Q,R,S],[C,F,G,H,J,M,P,Q,R,S,U],[C,F,G,H,J,M,P,Q,R,U],[C,F,G,H,J,M,P,Q,S,U],[C,F,G,H,J,M,P,Q,U],[C,F,G,H,J,M,P,R,S,U],[C,F,G,H,J,M,P,R,U],[C,F,G,H,J,M,P,S,U],[C,F,G,H,J,M,P,U],[C,F,G,J],[C,F,G,J,M],[C,F,G,J,M,N,P,Q,R,S,U],[C,F,G,J,M,N,P,Q,R,U],[C,F,G,J,M,N,P,Q,S,U],[C,F,G,J,M,N,P,Q,U],[C,F,G,J,M,N,P,R,S,U],[C,F,G,J,M,N,P,R,U],[C,F,G,J,M,N,P,S,U],[C,F,G,J,M,N,P,U],[C,F,G,J,M,P],[C,F,G,J,M,P,Q],[C,F,G,J,M,P,Q,R],[C,F,G,J,M,P,Q,R,S],[C,F,G,J,M,P,Q,R,S,U],[C,F,G,J,M,P,Q,R,U],[C,F,G,J,M,P,Q,S],[C,F,G,J,M,P,Q,S,U],[C,F,G,J,M,P,Q,U],[C,F,G,J,M,P,R],[C,F,G,J,M,P,R,S],[C,F,G,J,M,P,R,S,U],[C,F,G,J,M,P,R,U],[C,F,G,J,M,P,S],[C,F,G,J,M,P,S,U],[C,F,G,J,M,P,U],[C,F,G,J,M,Q],[C,F,G,J,M,Q,R],[C,F,G,J,M,R],[C,F,G,J,Q],[C,F,G,J,Q,R],[C,F,G,J,R],[C,F,H,J,M,N,P,Q,R,S,U],[C,F,H,J,M,N,P,Q,R,U],[C,F,H,J,M,N,P,Q,S,U],[C,F,H,J,M,N,P,Q,U],[C,F,H,J,M,N,P,R,S,U],[C,F,H,J,M,N,P,R,U],[C,F,H,J,M,N,P,S,U],[C,F,H,J,M,N,P,U],[C,F,H,J,M,P,Q,R,S,U],[C,F,H,J,M,P,Q,R,U],[C,F,H,J,M,P,Q,S],[C,F,H,J,M,P,Q,S,U],[C,F,H,J,M,P,Q,U],[C,F,H,J,M,P,R,S,U],[C,F,H,J,M,P,R,U],[C,F,H,J,M,P,S,U],[C,F,H,J,M,P,U],[C,F,J],[C,F,J,M],[C,F,J,M,N,P,Q,R,S,U],[C,F,J,M,N,P,Q,R,U],[C,F,J,M,N,P,Q,S,U],[C,F,J,M,N,P,Q,U],[C,F,J,M,N,P,R,S,U],[C,F,J,M,N,P,R,U],[C,F,J,M,N,P,S,U],[C,F,J,M,N,P,U],[C,F,J,M,P],[C,F,J,M,P,Q],[C,F,J,M,P,Q,R],[C,F,J,M,P,Q,R,S],[C,F,J,M,P,Q,R,S,U],[C,F,J,M,P,Q,R,U],[C,F,J,M,P,Q,S],[C,F,J,M,P,Q,S,U],[C,F,J,M,P,Q,U],[C,F,J,M,P,R],[C,F,J,M,P,R,S],[C,F,J,M,P,R,S,U],[C,F,J,M,P,R,U],[C,F,J,M,P,S],[C,F,J,M,P,S,U],[C,F,J,M,P,U],[C,F,J,M,Q],[C,F,J,M,Q,R],[C,F,J,M,R],[C,F,J,Q],[C,F,J,Q,R],[C,F,J,R],[C,G,H,J,M,N,P,Q,R,S,U],[C,G,H,J,M,N,P,Q,R,U],[C,G,H,J,M,N,P,Q,S,U],[C,G,H,J,M,N,P,Q,U],[C,G,H,J,M,N,P,R,S,U],[C,G,H,J,M,N,P,R,U],[C,G,H,J,M,N,P,S,U],[C,G,H,J,M,N,P,U],[C,G,H,J,M,P,Q,R,S,U],[C,G,H,J,M,P,Q,R,U],[C,G,H,J,M,P,Q,S,U],[C,G,H,J,M,P,Q,U],[C,G,H,J,M,P,R,S],[C,G,H,J,M,P,R,S,U],[C,G,H,J,M,P,R,U],[C,G,H,J,M,P,S,U],[C,G,H,J,M,P,U],[C,G,J],[C,G,J,M],[C,G,J,M,N,P,Q,R,S,U],[C,G,J,M,N,P,Q,R,U],[C,G,J,M,N,P,Q,S,U],[C,G,J,M,N,P,Q,U],[C,G,J,M,N,P,R,S,U],[C,G,J,M,N,P,R,U],[C,G,J,M,N,P,S,U],[C,G,J,M,N,P,U],[C,G,J,M,P],[C,G,J,M,P,Q],[C,G,J,M,P,Q,R],[C,G,J,M,P,Q,R,S],[C,G,J,M,P,Q,R,S,U],[C,G,J,M,P,Q,R,U],[C,G,J,M,P,Q,S],[C,G,J,M,P,Q,S,U],[C,G,J,M,P,Q,U],[C,G,J,M,P,R],[C,G,J,M,P,R,S],[C,G,J,M,P,R,S,U],[C,G,J,M,P,R,U],[C,G,J,M,P,S],[C,G,J,M,P,S,U],[C,G,J,M,P,U],[C,G,J,M,Q],[C,G,J,M,Q,R],[C,G,J,M,R],[C,G,J,Q],[C,G,J,Q,R],[C,G,J,R],[C,H,J,M,N,P,Q,R,S,U],[C,H,J,M,N,P,Q,R,U],[C,H,J,M,N,P,Q,S,U],[C,H,J,M,N,P,Q,U],[C,H,J,M,N,P,R,S,U],[C,H,J,M,N,P,R,U],[C,H,J,M,N,P,S,U],[C,H,J,M,N,P,U],[C,H,J,M,P,Q,R,S,U],[C,H,J,M,P,Q,R,U],[C,H,J,M,P,Q,S,U],[C,H,J,M,P,Q,U],[C,H,J,M,P,R,S,U],[C,H,J,M,P,R,U],[C,H,J,M,P,S],[C,H,J,M,P,S,U],[C,H,J,M,P,U],[C,J],[C,J,M],[C,J,M,N,P,Q,R,S,U],[C,J,M,N,P,Q,R,U],[C,J,M,N,P,Q,S,U],[C,J,M,N,P,Q,U],[C,J,M,N,P,R,S,U],[C,J,M,N,P,R,U],[C,J,M,N,P,S,U],[C,J,M,N,P,U],[C,J,M,P],[C,J,M,P,Q],[C,J,M,P,Q,R],[C,J,M,P,Q,R,S],[C,J,M,P,Q,R,S,U],[C,J,M,P,Q,R,U],[C,J,M,P,Q,S],[C,J,M,P,Q,S,U],[C,J,M,P,Q,U],[C,J,M,P,R],[C,J,M,P,R,S],[C,J,M,P,R,S,U],[C,J,M,P,R,U],[C,J,M,P,S],[C,J,M,P,S,U],[C,J,M,P,U],[C,J,M,Q],[C,J,M,Q,R],[C,J,M,R],[C,J,Q],[C,J,Q,R],[C,J,R],[D],[D,F,G,H,J,M,N,P,Q,R,S,U],[D,F,G,H,J,M,N,P,Q,R,U],[D,F,G,H,J,M,N,P,Q,S,U],[D,F,G,H,J,M,N,P,Q,U],[D,F,G,H,J,M,N,P,R,S,U],[D,F,G,H,J,M,N,P,R,U],[D,F,G,H,J,M,N,P,S,U],[D,F,G,H,J,M,N,P,U],[D,F,G,H,J,M,P,Q,R,S,U],[D,F,G,H,J,M,P,Q,R,U],[D,F,G,H,J,M,P,Q,S,U],[D,F,G,H,J,M,P,Q,U],[D,F,G,H,J,M,P,R,S,U],[D,F,G,H,J,M,P,R,U],[D,F,G,H,J,M,P,S,U],[D,F,G,H,J,M,P,U],[D,F,G,H,M,N,P,Q,R,S,U],[D,F,G,H,M,N,P,S,U],[D,F,G,H,M,N,P,U],[D,F,G,H,M,P,Q,R,S],[D,F,G,H,M,P,S,U],[D,F,G,H,M,P,U],[D,F,G,J,M,N,P,Q,R,S,U],[D,F,G,J,M,N,P,Q,R,U],[D,F,G,J,M,N,P,Q,S,U],[D,F,G,J,M,N,P,Q,U],[D,F,G,J,M,N,P,R,S,U],[D,F,G,J,M,N,P,R,U],[D,F,G,J,M,N,P,S,U],[D,F,G,J,M,N,P,U],[D,F,G,J,M,P,Q],[D,F,G,J,M,P,Q,R],[D,F,G,J,M,P,Q,R,S],[D,F,G,J,M,P,Q,R,S,U],[D,F,G,J,M,P,Q,R,U],[D,F,G,J,M,P,Q,S],[D,F,G,J,M,P,Q,S,U],[D,F,G,J,M,P,Q,U],[D,F,G,J,M,P,R],[D,F,G,J,M,P,R,S],[D,F,G,J,M,P,R,S,U],[D,F,G,J,M,P,R,U],[D,F,G,J,M,P,S,U],[D,F,G,J,M,P,U],[D,F,G,M,N,P,Q,R,U],[D,F,G,M,N,P,S,U],[D,F,G,M,N,P,U],[D,F,G,M,P,Q,R],[D,F,G,M,P,S,U],[D,F,G,M,P,U],[D,F,H,J,M,N,P,Q,R,S,U],[D,F,H,J,M,N,P,Q,R,U],[D,F,H,J,M,N,P,Q,S,U],[D,F,H,J,M,N,P,Q,U],[D,F,H,J,M,N,P,R,S,U],[D,F,H,J,M,N,P,R,U],[D,F,H,J,M,N,P,S,U],[D,F,H,J,M,N,P,U],[D,F,H,J,M,P,Q,R,S,U],[D,F,H,J,M,P,Q,R,U],[D,F,H,J,M,P,Q,S,U],[D,F,H,J,M,P,Q,U],[D,F,H,J,M,P,R,S,U],[D,F,H,J,M,P,R,U],[D,F,H,J,M,P,S,U],[D,F,H,J,M,P,U],[D,F,H,M,N,P,Q,S,U],[D,F,H,M,N,P,S,U],[D,F,H,M,N,P,U],[D,F,H,M,P,Q,S],[D,F,H,M,P,S,U],[D,F,H,M,P,U],[D,F,J,M,N,P,Q,R,S,U],[D,F,J,M,N,P,Q,R,U],[D,F,J,M,N,P,Q,S,U],[D,F,J,M,N,P,Q,U],[D,F,J,M,N,P,R,S,U],[D,F,J,M,N,P,R,U],[D,F,J,M,N,P,S,U],[D,F,J,M,N,P,U],[D,F,J,M,P,Q],[D,F,J,M,P,Q,R],[D,F,J,M,P,Q,R,S],[D,F,J,M,P,Q,R,S,U],[D,F,J,M,P,Q,R,U],[D,F,J,M,P,Q,S],[D,F,J,M,P,Q,S,U],[D,F,J,M,P,Q,U],[D,F,J,M,P,R],[D,F,J,M,P,R,S],[D,F,J,M,P,R,S,U],[D,F,J,M,P,R,U],[D,F,J,M,P,S,U],[D,F,J,M,P,U],[D,F,M,N,P,Q,U],[D,F,M,N,P,S,U],[D,F,M,N,P,U],[D,F,M,P,Q],[D,F,M,P,S,U],[D,F,M,P,U],[D,G,H,J,M,N,P,Q,R,S,U],[D,G,H,J,M,N,P,Q,R,U],[D,G,H,J,M,N,P,Q,S,U],[D,G,H,J,M,N,P,Q,U],[D,G,H,J,M,N,P,R,S,U],[D,G,H,J,M,N,P,R,U],[D,G,H,J,M,N,P,S,U],[D,G,H,J,M,N,P,U],[D,G,H,J,M,P,Q,R,S,U],[D,G,H,J,M,P,Q,R,U],[D,G,H,J,M,P,Q,S,U],[D,G,H,J,M,P,Q,U],[D,G,H,J,M,P,R,S,U],[D,G,H,J,M,P,R,U],[D,G,H,J,M,P,S,U],[D,G,H,J,M,P,U],[D,G,H,M,N,P,R,S,U],[D,G,H,M,N,P,S,U],[D,G,H,M,N,P,U],[D,G,H,M,P,R,S],[D,G,H,M,P,S,U],[D,G,H,M,P,U],[D,G,J,M,N,P,Q,R,S,U],[D,G,J,M,N,P,Q,R,U],[D,G,J,M,N,P,Q,S,U],[D,G,J,M,N,P,Q,U],[D,G,J,M,N,P,R,S,U],[D,G,J,M,N,P,R,U],[D,G,J,M,N,P,S,U],[D,G,J,M,N,P,U],[D,G,J,M,P,Q],[D,G,J,M,P,Q,R],[D,G,J,M,P,Q,R,S],[D,G,J,M,P,Q,R,S,U],[D,G,J,M,P,Q,R,U],[D,G,J,M,P,Q,S],[D,G,J,M,P,Q,S,U],[D,G,J,M,P,Q,U],[D,G,J,M,P,R],[D,G,J,M,P,R,S],[D,G,J,M,P,R,S,U],[D,G,J,M,P,R,U],[D,G,J,M,P,S,U],[D,G,J,M,P,U],[D,G,M,N,P,R,U],[D,G,M,N,P,S,U],[D,G,M,N,P,U],[D,G,M,P,R],[D,G,M,P,S,U],[D,G,M,P,U],[D,H,J,M,N,P,Q,R,S,U],[D,H,J,M,N,P,Q,R,U],[D,H,J,M,N,P,Q,S,U],[D,H,J,M,N,P,Q,U],[D,H,J,M,N,P,R,S,U],[D,H,J,M,N,P,R,U],[D,H,J,M,N,P,S,U],[D,H,J,M,N,P,U],[D,H,J,M,P,Q,R,S,U],[D,H,J,M,P,Q,R,U],[D,H,J,M,P,Q,S,U],[D,H,J,M,P,Q,U],[D,H,J,M,P,R,S,U],[D,H,J,M,P,R,U],[D,H,J,M,P,S,U],[D,H,J,M,P,U],[D,H,M,N,P,S,U],[D,H,M,N,P,U],[D,H,M,P,S],[D,H,M,P,S,U],[D,H,M,P,U],[D,J,M,N,P,Q,R,S,U],[D,J,M,N,P,Q,R,U],[D,J,M,N,P,Q,S,U],[D,J,M,N,P,Q,U],[D,J,M,N,P,R,S,U],[D,J,M,N,P,R,U],[D,J,M,N,P,S,U],[D,J,M,N,P,U],[D,J,M,P,Q],[D,J,M,P,Q,R],[D,J,M,P,Q,R,S],[D,J,M,P,Q,R,S,U],[D,J,M,P,Q,R,U],[D,J,M,P,Q,S],[D,J,M,P,Q,S,U],[D,J,M,P,Q,U],[D,J,M,P,R],[D,J,M,P,R,S],[D,J,M,P,R,S,U],[D,J,M,P,R,U],[D,J,M,P,S,U],[D,J,M,P,U],[D,M],[D,M,N,P,S,U],[D,M,N,P,U],[D,M,P],[D,M,P,S],[D,M,P,S,U],[D,M,P,U],[F],[F,G],[F,G,H,J,M,N,P,Q,R,S,U],[F,G,H,J,M,N,P,Q,R,U],[F,G,H,J,M,N,P,Q,S,U],[F,G,H,J,M,N,P,Q,U],[F,G,H,J,M,N,P,R,S,U],[F,G,H,J,M,N,P,R,U],[F,G,H,J,M,N,P,S,U],[F,G,H,J,M,N,P,U],[F,G,H,J,M,P,Q,R,S,U],[F,G,H,J,M,P,Q,R,U],[F,G,H,J,M,P,Q,S,U],[F,G,H,J,M,P,Q,U],[F,G,H,J,M,P,R,S,U],[F,G,H,J,M,P,R,U],[F,G,H,J,M,P,S,U],[F,G,H,J,M,P,U],[F,G,H,M,N,P,Q,R,S,U],[F,G,H,M,N,P,S,U],[F,G,H,M,N,P,U],[F,G,H,M,P,Q,R,S],[F,G,H,M,P,S,U],[F,G,H,M,P,U],[F,G,J],[F,G,J,M,N,P,Q,R,S,U],[F,G,J,M,N,P,Q,R,U],[F,G,J,M,N,P,Q,S,U],[F,G,J,M,N,P,Q,U],[F,G,J,M,N,P,R,S,U],[F,G,J,M,N,P,R,U],[F,G,J,M,N,P,S,U],[F,G,J,M,N,P,U],[F,G,J,M,P,Q],[F,G,J,M,P,Q,R],[F,G,J,M,P,Q,R,S],[F,G,J,M,P,Q,R,S,U],[F,G,J,M,P,Q,R,U],[F,G,J,M,P,Q,S],[F,G,J,M,P,Q,S,U],[F,G,J,M,P,Q,U],[F,G,J,M,P,R],[F,G,J,M,P,R,S],[F,G,J,M,P,R,S,U],[F,G,J,M,P,R,U],[F,G,J,M,P,S,U],[F,G,J,M,P,U],[F,G,J,Q],[F,G,J,Q,R],[F,G,J,R],[F,G,M,N,P,Q,R,U],[F,G,M,N,P,S,U],[F,G,M,N,P,U],[F,G,M,P,Q,R],[F,G,M,P,S,U],[F,G,M,P,U],[F,G,Q,R],[F,H,J,M,N,P,Q,R,S,U],[F,H,J,M,N,P,Q,R,U],[F,H,J,M,N,P,Q,S,U],[F,H,J,M,N,P,Q,U],[F,H,J,M,N,P,R,S,U],[F,H,J,M,N,P,R,U],[F,H,J,M,N,P,S,U],[F,H,J,M,N,P,U],[F,H,J,M,P,Q,R,S,U],[F,H,J,M,P,Q,R,U],[F,H,J,M,P,Q,S,U],[F,H,J,M,P,Q,U],[F,H,J,M,P,R,S,U],[F,H,J,M,P,R,U],[F,H,J,M,P,S,U],[F,H,J,M,P,U],[F,H,M,N,P,Q,S,U],[F,H,M,N,P,S,U],[F,H,M,N,P,U],[F,H,M,P,Q,S],[F,H,M,P,S,U],[F,H,M,P,U],[F,J],[F,J,M,N,P,Q,R,S,U],[F,J,M,N,P,Q,R,U],[F,J,M,N,P,Q,S,U],[F,J,M,N,P,Q,U],[F,J,M,N,P,R,S,U],[F,J,M,N,P,R,U],[F,J,M,N,P,S,U],[F,J,M,N,P,U],[F,J,M,P,Q],[F,J,M,P,Q,R],[F,J,M,P,Q,R,S],[F,J,M,P,Q,R,S,U],[F,J,M,P,Q,R,U],[F,J,M,P,Q,S],[F,J,M,P,Q,S,U],[F,J,M,P,Q,U],[F,J,M,P,R],[F,J,M,P,R,S],[F,J,M,P,R,S,U],[F,J,M,P,R,U],[F,J,M,P,S,U],[F,J,M,P,U],[F,J,Q],[F,J,Q,R],[F,J,R],[F,M,N,P,Q,U],[F,M,N,P,S,U],[F,M,N,P,U],[F,M,P,Q],[F,M,P,S,U],[F,M,P,U],[F,Q],[G],[G,H,J,M,N,P,Q,R,S,U],[G,H,J,M,N,P,Q,R,U],[G,H,J,M,N,P,Q,S,U],[G,H,J,M,N,P,Q,U],[G,H,J,M,N,P,R,S,U],[G,H,J,M,N,P,R,U],[G,H,J,M,N,P,S,U],[G,H,J,M,N,P,U],[G,H,J,M,P,Q,R,S,U],[G,H,J,M,P,Q,R,U],[G,H,J,M,P,Q,S,U],[G,H,J,M,P,Q,U],[G,H,J,M,P,R,S,U],[G,H,J,M,P,R,U],[G,H,J,M,P,S,U],[G,H,J,M,P,U],[G,H,M,N,P,R,S,U],[G,H,M,N,P,S,U],[G,H,M,N,P,U],[G,H,M,P,R,S],[G,H,M,P,S,U],[G,H,M,P,U],[G,J],[G,J,M,N,P,Q,R,S,U],[G,J,M,N,P,Q,R,U],[G,J,M,N,P,Q,S,U],[G,J,M,N,P,Q,U],[G,J,M,N,P,R,S,U],[G,J,M,N,P,R,U],[G,J,M,N,P,S,U],[G,J,M,N,P,U],[G,J,M,P,Q],[G,J,M,P,Q,R],[G,J,M,P,Q,R,S],[G,J,M,P,Q,R,S,U],[G,J,M,P,Q,R,U],[G,J,M,P,Q,S],[G,J,M,P,Q,S,U],[G,J,M,P,Q,U],[G,J,M,P,R],[G,J,M,P,R,S],[G,J,M,P,R,S,U],[G,J,M,P,R,U],[G,J,M,P,S,U],[G,J,M,P,U],[G,J,Q],[G,J,Q,R],[G,J,R],[G,M,N,P,R,U],[G,M,N,P,S,U],[G,M,N,P,U],[G,M,P,R],[G,M,P,S,U],[G,M,P,U],[G,R],[H,J,M,N,P,Q,R,S,U],[H,J,M,N,P,Q,R,U],[H,J,M,N,P,Q,S,U],[H,J,M,N,P,Q,U],[H,J,M,N,P,R,S,U],[H,J,M,N,P,R,U],[H,J,M,N,P,S,U],[H,J,M,N,P,U],[H,J,M,P,Q,R,S,U],[H,J,M,P,Q,R,U],[H,J,M,P,Q,S,U],[H,J,M,P,Q,U],[H,J,M,P,R,S,U],[H,J,M,P,R,U],[H,J,M,P,S,U],[H,J,M,P,U],[H,M,N,P,S,U],[H,M,N,P,U],[H,M,P,S],[H,M,P,S,U],[H,M,P,U],[I,J],[I,J,V],[J],[J,M,N,P,Q,R,S,U],[J,M,N,P,Q,R,U],[J,M,N,P,Q,S,U],[J,M,N,P,Q,U],[J,M,N,P,R,S,U],[J,M,N,P,R,U],[J,M,N,P,S,U],[J,M,N,P,U],[J,M,P,Q],[J,M,P,Q,R],[J,M,P,Q,R,S],[J,M,P,Q,R,S,U],[J,M,P,Q,R,U],[J,M,P,Q,S],[J,M,P,Q,S,U],[J,M,P,Q,U],[J,M,P,R],[J,M,P,R,S],[J,M,P,R,S,U],[J,M,P,R,U],[J,M,P,S,U],[J,M,P,U],[J,Q],[J,Q,R],[J,R],[M],[M,N,P,S,U],[M,N,P,U],[M,P],[M,P,S],[M,P,S,U],[M,P,U]]),ground([E,K,L,O,T]),linear(I);mshare([[B,C,D,F,H,J,M,N,P,Q,R,S,U],[B,C,D,F,H,J,M,N,P,Q,R,U],[B,C,D,F,H,J,M,N,P,Q,S,U],[B,C,D,F,H,J,M,N,P,Q,U],[B,C,D,F,H,J,M,N,P,R,S,U],[B,C,D,F,H,J,M,N,P,R,U],[B,C,D,F,H,J,M,N,P,S,U],[B,C,D,F,H,J,M,N,P,U],[B,C,D,F,H,J,M,P,Q,R,S,U],[B,C,D,F,H,J,M,P,Q,R,U],[B,C,D,F,H,J,M,P,Q,S],[B,C,D,F,H,J,M,P,Q,S,U],[B,C,D,F,H,J,M,P,Q,U],[B,C,D,F,H,J,M,P,R,S,U],[B,C,D,F,H,J,M,P,R,U],[B,C,D,F,H,J,M,P,S,U],[B,C,D,F,H,J,M,P,U],[B,C,D,F,J],[B,C,D,F,J,M],[B,C,D,F,J,M,N,P,Q,R,S,U],[B,C,D,F,J,M,N,P,Q,R,U],[B,C,D,F,J,M,N,P,Q,S,U],[B,C,D,F,J,M,N,P,Q,U],[B,C,D,F,J,M,N,P,R,S,U],[B,C,D,F,J,M,N,P,R,U],[B,C,D,F,J,M,N,P,S,U],[B,C,D,F,J,M,N,P,U],[B,C,D,F,J,M,P],[B,C,D,F,J,M,P,Q],[B,C,D,F,J,M,P,Q,R],[B,C,D,F,J,M,P,Q,R,S],[B,C,D,F,J,M,P,Q,R,S,U],[B,C,D,F,J,M,P,Q,R,U],[B,C,D,F,J,M,P,Q,S],[B,C,D,F,J,M,P,Q,S,U],[B,C,D,F,J,M,P,Q,U],[B,C,D,F,J,M,P,R],[B,C,D,F,J,M,P,R,S],[B,C,D,F,J,M,P,R,S,U],[B,C,D,F,J,M,P,R,U],[B,C,D,F,J,M,P,S],[B,C,D,F,J,M,P,S,U],[B,C,D,F,J,M,P,U],[B,C,D,F,J,M,Q],[B,C,D,F,J,M,Q,R],[B,C,D,F,J,M,R],[B,C,D,F,J,Q],[B,C,D,F,J,Q,R],[B,C,D,F,J,R],[B,C,D,H,J,M,N,P,Q,R,S,U],[B,C,D,H,J,M,N,P,Q,R,U],[B,C,D,H,J,M,N,P,Q,S,U],[B,C,D,H,J,M,N,P,Q,U],[B,C,D,H,J,M,N,P,R,S,U],[B,C,D,H,J,M,N,P,R,U],[B,C,D,H,J,M,N,P,S,U],[B,C,D,H,J,M,N,P,U],[B,C,D,H,J,M,P,Q,R,S,U],[B,C,D,H,J,M,P,Q,R,U],[B,C,D,H,J,M,P,Q,S,U],[B,C,D,H,J,M,P,Q,U],[B,C,D,H,J,M,P,R,S,U],[B,C,D,H,J,M,P,R,U],[B,C,D,H,J,M,P,S],[B,C,D,H,J,M,P,S,U],[B,C,D,H,J,M,P,U],[B,C,D,J],[B,C,D,J,M],[B,C,D,J,M,N,P,Q,R,S,U],[B,C,D,J,M,N,P,Q,R,U],[B,C,D,J,M,N,P,Q,S,U],[B,C,D,J,M,N,P,Q,U],[B,C,D,J,M,N,P,R,S,U],[B,C,D,J,M,N,P,R,U],[B,C,D,J,M,N,P,S,U],[B,C,D,J,M,N,P,U],[B,C,D,J,M,P],[B,C,D,J,M,P,Q],[B,C,D,J,M,P,Q,R],[B,C,D,J,M,P,Q,R,S],[B,C,D,J,M,P,Q,R,S,U],[B,C,D,J,M,P,Q,R,U],[B,C,D,J,M,P,Q,S],[B,C,D,J,M,P,Q,S,U],[B,C,D,J,M,P,Q,U],[B,C,D,J,M,P,R],[B,C,D,J,M,P,R,S],[B,C,D,J,M,P,R,S,U],[B,C,D,J,M,P,R,U],[B,C,D,J,M,P,S],[B,C,D,J,M,P,S,U],[B,C,D,J,M,P,U],[B,C,D,J,M,Q],[B,C,D,J,M,Q,R],[B,C,D,J,M,R],[B,C,D,J,Q],[B,C,D,J,Q,R],[B,C,D,J,R],[B,C,F,H,J,M,N,P,Q,R,S,U],[B,C,F,H,J,M,N,P,Q,R,U],[B,C,F,H,J,M,N,P,Q,S,U],[B,C,F,H,J,M,N,P,Q,U],[B,C,F,H,J,M,N,P,R,S,U],[B,C,F,H,J,M,N,P,R,U],[B,C,F,H,J,M,N,P,S,U],[B,C,F,H,J,M,N,P,U],[B,C,F,H,J,M,P,Q,R,S,U],[B,C,F,H,J,M,P,Q,R,U],[B,C,F,H,J,M,P,Q,S],[B,C,F,H,J,M,P,Q,S,U],[B,C,F,H,J,M,P,Q,U],[B,C,F,H,J,M,P,R,S,U],[B,C,F,H,J,M,P,R,U],[B,C,F,H,J,M,P,S,U],[B,C,F,H,J,M,P,U],[B,C,F,J],[B,C,F,J,M],[B,C,F,J,M,N,P,Q,R,S,U],[B,C,F,J,M,N,P,Q,R,U],[B,C,F,J,M,N,P,Q,S,U],[B,C,F,J,M,N,P,Q,U],[B,C,F,J,M,N,P,R,S,U],[B,C,F,J,M,N,P,R,U],[B,C,F,J,M,N,P,S,U],[B,C,F,J,M,N,P,U],[B,C,F,J,M,P],[B,C,F,J,M,P,Q],[B,C,F,J,M,P,Q,R],[B,C,F,J,M,P,Q,R,S],[B,C,F,J,M,P,Q,R,S,U],[B,C,F,J,M,P,Q,R,U],[B,C,F,J,M,P,Q,S],[B,C,F,J,M,P,Q,S,U],[B,C,F,J,M,P,Q,U],[B,C,F,J,M,P,R],[B,C,F,J,M,P,R,S],[B,C,F,J,M,P,R,S,U],[B,C,F,J,M,P,R,U],[B,C,F,J,M,P,S],[B,C,F,J,M,P,S,U],[B,C,F,J,M,P,U],[B,C,F,J,M,Q],[B,C,F,J,M,Q,R],[B,C,F,J,M,R],[B,C,F,J,Q],[B,C,F,J,Q,R],[B,C,F,J,R],[B,C,H,J,M,N,P,Q,R,S,U],[B,C,H,J,M,N,P,Q,R,U],[B,C,H,J,M,N,P,Q,S,U],[B,C,H,J,M,N,P,Q,U],[B,C,H,J,M,N,P,R,S,U],[B,C,H,J,M,N,P,R,U],[B,C,H,J,M,N,P,S,U],[B,C,H,J,M,N,P,U],[B,C,H,J,M,P,Q,R,S,U],[B,C,H,J,M,P,Q,R,U],[B,C,H,J,M,P,Q,S,U],[B,C,H,J,M,P,Q,U],[B,C,H,J,M,P,R,S,U],[B,C,H,J,M,P,R,U],[B,C,H,J,M,P,S],[B,C,H,J,M,P,S,U],[B,C,H,J,M,P,U],[B,C,J],[B,C,J,M],[B,C,J,M,N,P,Q,R,S,U],[B,C,J,M,N,P,Q,R,U],[B,C,J,M,N,P,Q,S,U],[B,C,J,M,N,P,Q,U],[B,C,J,M,N,P,R,S,U],[B,C,J,M,N,P,R,U],[B,C,J,M,N,P,S,U],[B,C,J,M,N,P,U],[B,C,J,M,P],[B,C,J,M,P,Q],[B,C,J,M,P,Q,R],[B,C,J,M,P,Q,R,S],[B,C,J,M,P,Q,R,S,U],[B,C,J,M,P,Q,R,U],[B,C,J,M,P,Q,S],[B,C,J,M,P,Q,S,U],[B,C,J,M,P,Q,U],[B,C,J,M,P,R],[B,C,J,M,P,R,S],[B,C,J,M,P,R,S,U],[B,C,J,M,P,R,U],[B,C,J,M,P,S],[B,C,J,M,P,S,U],[B,C,J,M,P,U],[B,C,J,M,Q],[B,C,J,M,Q,R],[B,C,J,M,R],[B,C,J,Q],[B,C,J,Q,R],[B,C,J,R],[B,D,F,H,J,M,N,P,Q,R,S,U],[B,D,F,H,J,M,N,P,Q,R,U],[B,D,F,H,J,M,N,P,Q,S,U],[B,D,F,H,J,M,N,P,Q,U],[B,D,F,H,J,M,N,P,R,S,U],[B,D,F,H,J,M,N,P,R,U],[B,D,F,H,J,M,N,P,S,U],[B,D,F,H,J,M,N,P,U],[B,D,F,H,J,M,P,Q,R,S,U],[B,D,F,H,J,M,P,Q,R,U],[B,D,F,H,J,M,P,Q,S],[B,D,F,H,J,M,P,Q,S,U],[B,D,F,H,J,M,P,Q,U],[B,D,F,H,J,M,P,R,S,U],[B,D,F,H,J,M,P,R,U],[B,D,F,H,J,M,P,S,U],[B,D,F,H,J,M,P,U],[B,D,F,J],[B,D,F,J,M],[B,D,F,J,M,N,P,Q,R,S,U],[B,D,F,J,M,N,P,Q,R,U],[B,D,F,J,M,N,P,Q,S,U],[B,D,F,J,M,N,P,Q,U],[B,D,F,J,M,N,P,R,S,U],[B,D,F,J,M,N,P,R,U],[B,D,F,J,M,N,P,S,U],[B,D,F,J,M,N,P,U],[B,D,F,J,M,P],[B,D,F,J,M,P,Q],[B,D,F,J,M,P,Q,R],[B,D,F,J,M,P,Q,R,S],[B,D,F,J,M,P,Q,R,S,U],[B,D,F,J,M,P,Q,R,U],[B,D,F,J,M,P,Q,S],[B,D,F,J,M,P,Q,S,U],[B,D,F,J,M,P,Q,U],[B,D,F,J,M,P,R],[B,D,F,J,M,P,R,S],[B,D,F,J,M,P,R,S,U],[B,D,F,J,M,P,R,U],[B,D,F,J,M,P,S],[B,D,F,J,M,P,S,U],[B,D,F,J,M,P,U],[B,D,F,J,M,Q],[B,D,F,J,M,Q,R],[B,D,F,J,M,R],[B,D,F,J,Q],[B,D,F,J,Q,R],[B,D,F,J,R],[B,D,H,J,M,N,P,Q,R,S,U],[B,D,H,J,M,N,P,Q,R,U],[B,D,H,J,M,N,P,Q,S,U],[B,D,H,J,M,N,P,Q,U],[B,D,H,J,M,N,P,R,S,U],[B,D,H,J,M,N,P,R,U],[B,D,H,J,M,N,P,S,U],[B,D,H,J,M,N,P,U],[B,D,H,J,M,P,Q,R,S,U],[B,D,H,J,M,P,Q,R,U],[B,D,H,J,M,P,Q,S,U],[B,D,H,J,M,P,Q,U],[B,D,H,J,M,P,R,S,U],[B,D,H,J,M,P,R,U],[B,D,H,J,M,P,S],[B,D,H,J,M,P,S,U],[B,D,H,J,M,P,U],[B,D,J],[B,D,J,M],[B,D,J,M,N,P,Q,R,S,U],[B,D,J,M,N,P,Q,R,U],[B,D,J,M,N,P,Q,S,U],[B,D,J,M,N,P,Q,U],[B,D,J,M,N,P,R,S,U],[B,D,J,M,N,P,R,U],[B,D,J,M,N,P,S,U],[B,D,J,M,N,P,U],[B,D,J,M,P],[B,D,J,M,P,Q],[B,D,J,M,P,Q,R],[B,D,J,M,P,Q,R,S],[B,D,J,M,P,Q,R,S,U],[B,D,J,M,P,Q,R,U],[B,D,J,M,P,Q,S],[B,D,J,M,P,Q,S,U],[B,D,J,M,P,Q,U],[B,D,J,M,P,R],[B,D,J,M,P,R,S],[B,D,J,M,P,R,S,U],[B,D,J,M,P,R,U],[B,D,J,M,P,S],[B,D,J,M,P,S,U],[B,D,J,M,P,U],[B,D,J,M,Q],[B,D,J,M,Q,R],[B,D,J,M,R],[B,D,J,Q],[B,D,J,Q,R],[B,D,J,R],[B,F,H,J,M,N,P,Q,R,S,U],[B,F,H,J,M,N,P,Q,R,U],[B,F,H,J,M,N,P,Q,S,U],[B,F,H,J,M,N,P,Q,U],[B,F,H,J,M,N,P,R,S,U],[B,F,H,J,M,N,P,R,U],[B,F,H,J,M,N,P,S,U],[B,F,H,J,M,N,P,U],[B,F,H,J,M,P,Q,R,S,U],[B,F,H,J,M,P,Q,R,U],[B,F,H,J,M,P,Q,S],[B,F,H,J,M,P,Q,S,U],[B,F,H,J,M,P,Q,U],[B,F,H,J,M,P,R,S,U],[B,F,H,J,M,P,R,U],[B,F,H,J,M,P,S,U],[B,F,H,J,M,P,U],[B,F,J],[B,F,J,M],[B,F,J,M,N,P,Q,R,S,U],[B,F,J,M,N,P,Q,R,U],[B,F,J,M,N,P,Q,S,U],[B,F,J,M,N,P,Q,U],[B,F,J,M,N,P,R,S,U],[B,F,J,M,N,P,R,U],[B,F,J,M,N,P,S,U],[B,F,J,M,N,P,U],[B,F,J,M,P],[B,F,J,M,P,Q],[B,F,J,M,P,Q,R],[B,F,J,M,P,Q,R,S],[B,F,J,M,P,Q,R,S,U],[B,F,J,M,P,Q,R,U],[B,F,J,M,P,Q,S],[B,F,J,M,P,Q,S,U],[B,F,J,M,P,Q,U],[B,F,J,M,P,R],[B,F,J,M,P,R,S],[B,F,J,M,P,R,S,U],[B,F,J,M,P,R,U],[B,F,J,M,P,S],[B,F,J,M,P,S,U],[B,F,J,M,P,U],[B,F,J,M,Q],[B,F,J,M,Q,R],[B,F,J,M,R],[B,F,J,Q],[B,F,J,Q,R],[B,F,J,R],[B,H,J,M,N,P,Q,R,S,U],[B,H,J,M,N,P,Q,R,U],[B,H,J,M,N,P,Q,S,U],[B,H,J,M,N,P,Q,U],[B,H,J,M,N,P,R,S,U],[B,H,J,M,N,P,R,U],[B,H,J,M,N,P,S,U],[B,H,J,M,N,P,U],[B,H,J,M,P,Q,R,S,U],[B,H,J,M,P,Q,R,U],[B,H,J,M,P,Q,S,U],[B,H,J,M,P,Q,U],[B,H,J,M,P,R,S,U],[B,H,J,M,P,R,U],[B,H,J,M,P,S],[B,H,J,M,P,S,U],[B,H,J,M,P,U],[B,J],[B,J,M],[B,J,M,N,P,Q,R,S,U],[B,J,M,N,P,Q,R,U],[B,J,M,N,P,Q,S,U],[B,J,M,N,P,Q,U],[B,J,M,N,P,R,S,U],[B,J,M,N,P,R,U],[B,J,M,N,P,S,U],[B,J,M,N,P,U],[B,J,M,P],[B,J,M,P,Q],[B,J,M,P,Q,R],[B,J,M,P,Q,R,S],[B,J,M,P,Q,R,S,U],[B,J,M,P,Q,R,U],[B,J,M,P,Q,S],[B,J,M,P,Q,S,U],[B,J,M,P,Q,U],[B,J,M,P,R],[B,J,M,P,R,S],[B,J,M,P,R,S,U],[B,J,M,P,R,U],[B,J,M,P,S],[B,J,M,P,S,U],[B,J,M,P,U],[B,J,M,Q],[B,J,M,Q,R],[B,J,M,R],[B,J,Q],[B,J,Q,R],[B,J,R],[C,D,F,H,J,M,N,P,Q,R,S,U],[C,D,F,H,J,M,N,P,Q,R,U],[C,D,F,H,J,M,N,P,Q,S,U],[C,D,F,H,J,M,N,P,Q,U],[C,D,F,H,J,M,N,P,R,S,U],[C,D,F,H,J,M,N,P,R,U],[C,D,F,H,J,M,N,P,S,U],[C,D,F,H,J,M,N,P,U],[C,D,F,H,J,M,P,Q,R,S,U],[C,D,F,H,J,M,P,Q,R,U],[C,D,F,H,J,M,P,Q,S],[C,D,F,H,J,M,P,Q,S,U],[C,D,F,H,J,M,P,Q,U],[C,D,F,H,J,M,P,R,S,U],[C,D,F,H,J,M,P,R,U],[C,D,F,H,J,M,P,S,U],[C,D,F,H,J,M,P,U],[C,D,F,J],[C,D,F,J,M],[C,D,F,J,M,N,P,Q,R,S,U],[C,D,F,J,M,N,P,Q,R,U],[C,D,F,J,M,N,P,Q,S,U],[C,D,F,J,M,N,P,Q,U],[C,D,F,J,M,N,P,R,S,U],[C,D,F,J,M,N,P,R,U],[C,D,F,J,M,N,P,S,U],[C,D,F,J,M,N,P,U],[C,D,F,J,M,P],[C,D,F,J,M,P,Q],[C,D,F,J,M,P,Q,R],[C,D,F,J,M,P,Q,R,S],[C,D,F,J,M,P,Q,R,S,U],[C,D,F,J,M,P,Q,R,U],[C,D,F,J,M,P,Q,S],[C,D,F,J,M,P,Q,S,U],[C,D,F,J,M,P,Q,U],[C,D,F,J,M,P,R],[C,D,F,J,M,P,R,S],[C,D,F,J,M,P,R,S,U],[C,D,F,J,M,P,R,U],[C,D,F,J,M,P,S],[C,D,F,J,M,P,S,U],[C,D,F,J,M,P,U],[C,D,F,J,M,Q],[C,D,F,J,M,Q,R],[C,D,F,J,M,R],[C,D,F,J,Q],[C,D,F,J,Q,R],[C,D,F,J,R],[C,D,H,J,M,N,P,Q,R,S,U],[C,D,H,J,M,N,P,Q,R,U],[C,D,H,J,M,N,P,Q,S,U],[C,D,H,J,M,N,P,Q,U],[C,D,H,J,M,N,P,R,S,U],[C,D,H,J,M,N,P,R,U],[C,D,H,J,M,N,P,S,U],[C,D,H,J,M,N,P,U],[C,D,H,J,M,P,Q,R,S,U],[C,D,H,J,M,P,Q,R,U],[C,D,H,J,M,P,Q,S,U],[C,D,H,J,M,P,Q,U],[C,D,H,J,M,P,R,S,U],[C,D,H,J,M,P,R,U],[C,D,H,J,M,P,S],[C,D,H,J,M,P,S,U],[C,D,H,J,M,P,U],[C,D,J],[C,D,J,M],[C,D,J,M,N,P,Q,R,S,U],[C,D,J,M,N,P,Q,R,U],[C,D,J,M,N,P,Q,S,U],[C,D,J,M,N,P,Q,U],[C,D,J,M,N,P,R,S,U],[C,D,J,M,N,P,R,U],[C,D,J,M,N,P,S,U],[C,D,J,M,N,P,U],[C,D,J,M,P],[C,D,J,M,P,Q],[C,D,J,M,P,Q,R],[C,D,J,M,P,Q,R,S],[C,D,J,M,P,Q,R,S,U],[C,D,J,M,P,Q,R,U],[C,D,J,M,P,Q,S],[C,D,J,M,P,Q,S,U],[C,D,J,M,P,Q,U],[C,D,J,M,P,R],[C,D,J,M,P,R,S],[C,D,J,M,P,R,S,U],[C,D,J,M,P,R,U],[C,D,J,M,P,S],[C,D,J,M,P,S,U],[C,D,J,M,P,U],[C,D,J,M,Q],[C,D,J,M,Q,R],[C,D,J,M,R],[C,D,J,Q],[C,D,J,Q,R],[C,D,J,R],[C,F,H,J,M,N,P,Q,R,S,U],[C,F,H,J,M,N,P,Q,R,U],[C,F,H,J,M,N,P,Q,S,U],[C,F,H,J,M,N,P,Q,U],[C,F,H,J,M,N,P,R,S,U],[C,F,H,J,M,N,P,R,U],[C,F,H,J,M,N,P,S,U],[C,F,H,J,M,N,P,U],[C,F,H,J,M,P,Q,R,S,U],[C,F,H,J,M,P,Q,R,U],[C,F,H,J,M,P,Q,S],[C,F,H,J,M,P,Q,S,U],[C,F,H,J,M,P,Q,U],[C,F,H,J,M,P,R,S,U],[C,F,H,J,M,P,R,U],[C,F,H,J,M,P,S,U],[C,F,H,J,M,P,U],[C,F,J],[C,F,J,M],[C,F,J,M,N,P,Q,R,S,U],[C,F,J,M,N,P,Q,R,U],[C,F,J,M,N,P,Q,S,U],[C,F,J,M,N,P,Q,U],[C,F,J,M,N,P,R,S,U],[C,F,J,M,N,P,R,U],[C,F,J,M,N,P,S,U],[C,F,J,M,N,P,U],[C,F,J,M,P],[C,F,J,M,P,Q],[C,F,J,M,P,Q,R],[C,F,J,M,P,Q,R,S],[C,F,J,M,P,Q,R,S,U],[C,F,J,M,P,Q,R,U],[C,F,J,M,P,Q,S],[C,F,J,M,P,Q,S,U],[C,F,J,M,P,Q,U],[C,F,J,M,P,R],[C,F,J,M,P,R,S],[C,F,J,M,P,R,S,U],[C,F,J,M,P,R,U],[C,F,J,M,P,S],[C,F,J,M,P,S,U],[C,F,J,M,P,U],[C,F,J,M,Q],[C,F,J,M,Q,R],[C,F,J,M,R],[C,F,J,Q],[C,F,J,Q,R],[C,F,J,R],[C,H,J,M,N,P,Q,R,S,U],[C,H,J,M,N,P,Q,R,U],[C,H,J,M,N,P,Q,S,U],[C,H,J,M,N,P,Q,U],[C,H,J,M,N,P,R,S,U],[C,H,J,M,N,P,R,U],[C,H,J,M,N,P,S,U],[C,H,J,M,N,P,U],[C,H,J,M,P,Q,R,S,U],[C,H,J,M,P,Q,R,U],[C,H,J,M,P,Q,S,U],[C,H,J,M,P,Q,U],[C,H,J,M,P,R,S,U],[C,H,J,M,P,R,U],[C,H,J,M,P,S],[C,H,J,M,P,S,U],[C,H,J,M,P,U],[C,J],[C,J,M],[C,J,M,N,P,Q,R,S,U],[C,J,M,N,P,Q,R,U],[C,J,M,N,P,Q,S,U],[C,J,M,N,P,Q,U],[C,J,M,N,P,R,S,U],[C,J,M,N,P,R,U],[C,J,M,N,P,S,U],[C,J,M,N,P,U],[C,J,M,P],[C,J,M,P,Q],[C,J,M,P,Q,R],[C,J,M,P,Q,R,S],[C,J,M,P,Q,R,S,U],[C,J,M,P,Q,R,U],[C,J,M,P,Q,S],[C,J,M,P,Q,S,U],[C,J,M,P,Q,U],[C,J,M,P,R],[C,J,M,P,R,S],[C,J,M,P,R,S,U],[C,J,M,P,R,U],[C,J,M,P,S],[C,J,M,P,S,U],[C,J,M,P,U],[C,J,M,Q],[C,J,M,Q,R],[C,J,M,R],[C,J,Q],[C,J,Q,R],[C,J,R],[D],[D,F,H,J,M,N,P,Q,R,S,U],[D,F,H,J,M,N,P,Q,R,U],[D,F,H,J,M,N,P,Q,S,U],[D,F,H,J,M,N,P,Q,U],[D,F,H,J,M,N,P,R,S,U],[D,F,H,J,M,N,P,R,U],[D,F,H,J,M,N,P,S,U],[D,F,H,J,M,N,P,U],[D,F,H,J,M,P,Q,R,S,U],[D,F,H,J,M,P,Q,R,U],[D,F,H,J,M,P,Q,S,U],[D,F,H,J,M,P,Q,U],[D,F,H,J,M,P,R,S,U],[D,F,H,J,M,P,R,U],[D,F,H,J,M,P,S,U],[D,F,H,J,M,P,U],[D,F,H,M,N,P,Q,S,U],[D,F,H,M,N,P,S,U],[D,F,H,M,N,P,U],[D,F,H,M,P,Q,S],[D,F,H,M,P,S,U],[D,F,H,M,P,U],[D,F,J,M,N,P,Q,R,S,U],[D,F,J,M,N,P,Q,R,U],[D,F,J,M,N,P,Q,S,U],[D,F,J,M,N,P,Q,U],[D,F,J,M,N,P,R,S,U],[D,F,J,M,N,P,R,U],[D,F,J,M,N,P,S,U],[D,F,J,M,N,P,U],[D,F,J,M,P,Q],[D,F,J,M,P,Q,R],[D,F,J,M,P,Q,R,S],[D,F,J,M,P,Q,R,S,U],[D,F,J,M,P,Q,R,U],[D,F,J,M,P,Q,S],[D,F,J,M,P,Q,S,U],[D,F,J,M,P,Q,U],[D,F,J,M,P,R],[D,F,J,M,P,R,S],[D,F,J,M,P,R,S,U],[D,F,J,M,P,R,U],[D,F,J,M,P,S,U],[D,F,J,M,P,U],[D,F,M,N,P,Q,U],[D,F,M,N,P,S,U],[D,F,M,N,P,U],[D,F,M,P,Q],[D,F,M,P,S,U],[D,F,M,P,U],[D,H,J,M,N,P,Q,R,S,U],[D,H,J,M,N,P,Q,R,U],[D,H,J,M,N,P,Q,S,U],[D,H,J,M,N,P,Q,U],[D,H,J,M,N,P,R,S,U],[D,H,J,M,N,P,R,U],[D,H,J,M,N,P,S,U],[D,H,J,M,N,P,U],[D,H,J,M,P,Q,R,S,U],[D,H,J,M,P,Q,R,U],[D,H,J,M,P,Q,S,U],[D,H,J,M,P,Q,U],[D,H,J,M,P,R,S,U],[D,H,J,M,P,R,U],[D,H,J,M,P,S,U],[D,H,J,M,P,U],[D,H,M,N,P,S,U],[D,H,M,N,P,U],[D,H,M,P,S],[D,H,M,P,S,U],[D,H,M,P,U],[D,J,M,N,P,Q,R,S,U],[D,J,M,N,P,Q,R,U],[D,J,M,N,P,Q,S,U],[D,J,M,N,P,Q,U],[D,J,M,N,P,R,S,U],[D,J,M,N,P,R,U],[D,J,M,N,P,S,U],[D,J,M,N,P,U],[D,J,M,P,Q],[D,J,M,P,Q,R],[D,J,M,P,Q,R,S],[D,J,M,P,Q,R,S,U],[D,J,M,P,Q,R,U],[D,J,M,P,Q,S],[D,J,M,P,Q,S,U],[D,J,M,P,Q,U],[D,J,M,P,R],[D,J,M,P,R,S],[D,J,M,P,R,S,U],[D,J,M,P,R,U],[D,J,M,P,S,U],[D,J,M,P,U],[D,M],[D,M,N,P,S,U],[D,M,N,P,U],[D,M,P],[D,M,P,S],[D,M,P,S,U],[D,M,P,U],[F],[F,H,J,M,N,P,Q,R,S,U],[F,H,J,M,N,P,Q,R,U],[F,H,J,M,N,P,Q,S,U],[F,H,J,M,N,P,Q,U],[F,H,J,M,N,P,R,S,U],[F,H,J,M,N,P,R,U],[F,H,J,M,N,P,S,U],[F,H,J,M,N,P,U],[F,H,J,M,P,Q,R,S,U],[F,H,J,M,P,Q,R,U],[F,H,J,M,P,Q,S,U],[F,H,J,M,P,Q,U],[F,H,J,M,P,R,S,U],[F,H,J,M,P,R,U],[F,H,J,M,P,S,U],[F,H,J,M,P,U],[F,H,M,N,P,Q,S,U],[F,H,M,N,P,S,U],[F,H,M,N,P,U],[F,H,M,P,Q,S],[F,H,M,P,S,U],[F,H,M,P,U],[F,J],[F,J,M,N,P,Q,R,S,U],[F,J,M,N,P,Q,R,U],[F,J,M,N,P,Q,S,U],[F,J,M,N,P,Q,U],[F,J,M,N,P,R,S,U],[F,J,M,N,P,R,U],[F,J,M,N,P,S,U],[F,J,M,N,P,U],[F,J,M,P,Q],[F,J,M,P,Q,R],[F,J,M,P,Q,R,S],[F,J,M,P,Q,R,S,U],[F,J,M,P,Q,R,U],[F,J,M,P,Q,S],[F,J,M,P,Q,S,U],[F,J,M,P,Q,U],[F,J,M,P,R],[F,J,M,P,R,S],[F,J,M,P,R,S,U],[F,J,M,P,R,U],[F,J,M,P,S,U],[F,J,M,P,U],[F,J,Q],[F,J,Q,R],[F,J,R],[F,M,N,P,Q,U],[F,M,N,P,S,U],[F,M,N,P,U],[F,M,P,Q],[F,M,P,S,U],[F,M,P,U],[F,Q],[H,J,M,N,P,Q,R,S,U],[H,J,M,N,P,Q,R,U],[H,J,M,N,P,Q,S,U],[H,J,M,N,P,Q,U],[H,J,M,N,P,R,S,U],[H,J,M,N,P,R,U],[H,J,M,N,P,S,U],[H,J,M,N,P,U],[H,J,M,P,Q,R,S,U],[H,J,M,P,Q,R,U],[H,J,M,P,Q,S,U],[H,J,M,P,Q,U],[H,J,M,P,R,S,U],[H,J,M,P,R,U],[H,J,M,P,S,U],[H,J,M,P,U],[H,M,N,P,S,U],[H,M,N,P,U],[H,M,P,S],[H,M,P,S,U],[H,M,P,U],[I,J],[I,J,V],[J],[J,M,N,P,Q,R,S,U],[J,M,N,P,Q,R,U],[J,M,N,P,Q,S,U],[J,M,N,P,Q,U],[J,M,N,P,R,S,U],[J,M,N,P,R,U],[J,M,N,P,S,U],[J,M,N,P,U],[J,M,P,Q],[J,M,P,Q,R],[J,M,P,Q,R,S],[J,M,P,Q,R,S,U],[J,M,P,Q,R,U],[J,M,P,Q,S],[J,M,P,Q,S,U],[J,M,P,Q,U],[J,M,P,R],[J,M,P,R,S],[J,M,P,R,S,U],[J,M,P,R,U],[J,M,P,S,U],[J,M,P,U],[J,Q],[J,Q,R],[J,R],[M],[M,N,P,S,U],[M,N,P,U],[M,P],[M,P,S],[M,P,S,U],[M,P,U]]),ground([E,G,K,L,O,T]),linear(I);mshare([[B,C,E,J],[B,C,E,J,Q],[B,C,E,J,Q,R],[B,C,E,J,R],[B,C,J],[B,C,J,Q],[B,C,J,Q,R],[B,C,J,R],[B,E,J],[B,E,J,Q],[B,E,J,Q,R],[B,E,J,R],[B,J],[B,J,Q],[B,J,Q,R],[B,J,R],[C,E,J],[C,E,J,Q],[C,E,J,Q,R],[C,E,J,R],[C,J],[C,J,Q],[C,J,Q,R],[C,J,R],[E,J],[E,J,Q],[E,J,Q,R],[E,J,R],[F],[F,G],[F,G,Q,R],[F,Q],[G],[G,R],[I,J],[I,J,V],[J],[J,Q],[J,Q,R],[J,R]]),ground([D,H,K,L,M,N,O,P,S,T,U]),linear(I);mshare([[B,C,E,J],[B,C,E,J,Q],[B,C,E,J,Q,R],[B,C,E,J,R],[B,C,J],[B,C,J,Q],[B,C,J,Q,R],[B,C,J,R],[B,E,J],[B,E,J,Q],[B,E,J,Q,R],[B,E,J,R],[B,J],[B,J,Q],[B,J,Q,R],[B,J,R],[C,E,J],[C,E,J,Q],[C,E,J,Q,R],[C,E,J,R],[C,J],[C,J,Q],[C,J,Q,R],[C,J,R],[E,J],[E,J,Q],[E,J,Q,R],[E,J,R],[F],[F,Q],[I,J],[I,J,V],[J],[J,Q],[J,Q,R],[J,R]]),ground([D,G,H,K,L,M,N,O,P,S,T,U]),linear(I);mshare([[B,C,J],[B,C,J,Q],[B,C,J,Q,R],[B,C,J,R],[B,J],[B,J,Q],[B,J,Q,R],[B,J,R],[C,J],[C,J,Q],[C,J,Q,R],[C,J,R],[F],[F,G],[F,G,Q,R],[F,Q],[G],[G,R],[I,J],[I,J,V],[J],[J,Q],[J,Q,R],[J,R]]),ground([D,E,H,K,L,M,N,O,P,S,T,U]),linear(I);mshare([[B,C,J],[B,C,J,Q],[B,C,J,Q,R],[B,C,J,R],[B,J],[B,J,Q],[B,J,Q,R],[B,J,R],[C,J],[C,J,Q],[C,J,Q,R],[C,J,R],[F],[F,Q],[I,J],[I,J,V],[J],[J,Q],[J,Q,R],[J,R]]),ground([D,E,G,H,K,L,M,N,O,P,S,T,U]),linear(I))).
possessive(B,C,D,E,F,B,C,D,E,F,G,G,H,H).

:- true pred gen_case(B,C,D,_A)
   : ( mshare([[C],[D],[_A]]),
       ground([B]), linear(C), linear(_A) )
   => ( mshare([[D],[D,_A]]),
        ground([B,C]) ).

:- true pred gen_case(B,C,D,_A)
   : ( mshare([[C],[_A]]),
       ground([B,D]), linear(C), linear(_A) )
   => ground([B,C,D,_A]).

gen_case(B,C,D,x(nogap,terminal,the,E)) :-
    true((mshare([[C],[D],[E]]),ground([B]),linear(C),linear(E);mshare([[C],[E]]),ground([B,D]),linear(C),linear(E))),
    gen_marker(B,C,D,E),
    true((mshare([[D],[D,E]]),ground([B,C]);ground([B,C,D,E]))).

:- true pred an_s(B,C,D,E)
   : ( mshare([[C],[D],[E]]),
       ground([B]), linear(C), linear(E) )
   => ( mshare([[D],[D,E]]),
        ground([B,C]) ).

:- true pred an_s(B,C,D,E)
   : ( mshare([[C],[E]]),
       ground([B,D]), linear(C), linear(E) )
   => ground([B,C,D,E]).

an_s(B,C,D,E) :-
    true((mshare([[C],[D],[E]]),ground([B]),linear(C),linear(E);mshare([[C],[E]]),ground([B,D]),linear(C),linear(E))),
    ~(s,B,C,D,E),
    true((mshare([[D],[D,E]]),ground([B,C]);ground([B,C,D,E]))).
an_s(B,B,C,C).

:- true pred determiner(B,C,D,E,F,G,H)
   : ( (D=indef),
       mshare([[B],[C],[F],[H]]),
       ground([E,G]), linear(B), linear(C), linear(F), linear(H) )
   => ( mshare([[B,C],[C]]),
        ground([E,F,G,H]) ).

:- true pred determiner(B,C,D,E,F,G,H)
   : ( (D=indef),
       mshare([[B],[C,G],[F],[G],[H]]),
       ground([E]), linear(B), linear(F), linear(H) )
   => ( mshare([[B,C,G],[B,C,G,H],[B,G],[B,G,H],[C,G],[C,G,H],[G],[G,H]]),
        ground([E,F]) ).

:- true pred determiner(B,C,D,E,F,G,H)
   : ( (D=indef),
       mshare([[B],[C],[F],[G],[H]]),
       ground([E]), linear(B), linear(C), linear(F), linear(H) )
   => ( mshare([[B,C],[B,C,G],[B,C,G,H],[B,G],[B,G,H],[C],[C,G],[C,G,H],[G],[G,H]]),
        ground([E,F]) ).

:- true pred determiner(B,C,D,E,F,G,H)
   : ( mshare([[B],[C],[D],[F],[G],[H]]),
       ground([E]), linear(B), linear(C), linear(D), linear(F), linear(H) )
   => ( mshare([[B,C],[B,C,D,G],[B,C,D,G,H],[B,C,G],[B,C,G,H],[B,D,G],[B,D,G,H],[B,G],[B,G,H],[C],[C,D,G],[C,D,G,H],[C,G],[C,G,H],[D,G],[D,G,H],[G],[G,H]]),
        ground([E,F]) ).

:- true pred determiner(B,C,D,E,F,G,H)
   : ( mshare([[B],[C],[D],[F],[H]]),
       ground([E,G]), linear(B), linear(C), linear(D), linear(F), linear(H) )
   => ( mshare([[B,C],[C]]),
        ground([D,E,F,G,H]) ).

determiner(B,C,D,E,F,G,H) :-
    true((mshare([[B],[C],[D],[F],[G],[H]]),ground([E]),linear(B),linear(C),linear(D),linear(F),linear(H);mshare([[B],[C],[D],[F],[H]]),ground([E,G]),linear(B),linear(C),linear(D),linear(F),linear(H);mshare([[B],[C],[F],[G],[H]]),ground([D,E]),linear(B),linear(C),linear(F),linear(H);mshare([[B],[C],[F],[H]]),ground([D,E,G]),linear(B),linear(C),linear(F),linear(H);mshare([[B],[C,G],[F],[G],[H]]),ground([D,E]),linear(B),linear(F),linear(H))),
    det(B,C,D,E,F,G,H),
    true((mshare([[B,C],[B,C,D,G],[B,C,D,G,H],[B,C,G],[B,C,G,H],[B,D,G],[B,D,G,H],[B,G],[B,G,H],[C],[C,D,G],[C,D,G,H],[C,G],[C,G,H],[D,G],[D,G,H],[G],[G,H]]),ground([E,F]);mshare([[B,C],[B,C,G],[B,C,G,H],[B,G],[B,G,H],[C],[C,G],[C,G,H],[G],[G,H]]),ground([D,E,F]);mshare([[B,C],[C]]),ground([D,E,F,G,H]);mshare([[B,C,G],[B,C,G,H],[B,G],[B,G,H],[C,G],[C,G,H],[G],[G,H]]),ground([D,E,F]))).
determiner(B,C,D,E,F,G,H) :-
    true((mshare([[B],[C],[D],[F],[G],[H]]),ground([E]),linear(B),linear(C),linear(D),linear(F),linear(H);mshare([[B],[C],[D],[F],[H]]),ground([E,G]),linear(B),linear(C),linear(D),linear(F),linear(H);mshare([[B],[C],[F],[G],[H]]),ground([D,E]),linear(B),linear(C),linear(F),linear(H);mshare([[B],[C],[F],[H]]),ground([D,E,G]),linear(B),linear(C),linear(F),linear(H);mshare([[B],[C,G],[F],[G],[H]]),ground([D,E]),linear(B),linear(F),linear(H))),
    quant_phrase(B,C,D,E,F,G,H),
    true((mshare([[G],[G,H]]),ground([B,C,D,E,F]);ground([B,C,D,E,F,G,H]))).

:- true pred quant_phrase(_A,D,E,F,G,H,I)
   : ( mshare([[_A],[D,H],[G],[H],[I]]),
       ground([E,F]), linear(_A), linear(G), linear(I) )
   => ( mshare([[H],[H,I]]),
        ground([_A,D,E,F,G]) ).

:- true pred quant_phrase(_A,D,E,F,G,H,I)
   : ( mshare([[_A],[D],[G],[H],[I]]),
       ground([E,F]), linear(_A), linear(D), linear(G), linear(I) )
   => ( mshare([[H],[H,I]]),
        ground([_A,D,E,F,G]) ).

:- true pred quant_phrase(_A,D,E,F,G,H,I)
   : ( mshare([[_A],[D],[E],[G],[H],[I]]),
       ground([F]), linear(_A), linear(D), linear(E), linear(G), linear(I) )
   => ( mshare([[H],[H,I]]),
        ground([_A,D,E,F,G]) ).

:- true pred quant_phrase(_A,D,E,F,G,H,I)
   : ( mshare([[_A],[D],[G],[I]]),
       ground([E,F,H]), linear(_A), linear(D), linear(G), linear(I) )
   => ground([_A,D,E,F,G,H,I]).

:- true pred quant_phrase(_A,D,E,F,G,H,I)
   : ( mshare([[_A],[D],[E],[G],[I]]),
       ground([F,H]), linear(_A), linear(D), linear(E), linear(G), linear(I) )
   => ground([_A,D,E,F,G,H,I]).

quant_phrase(quant(B,C),D,E,F,G,H,I) :-
    true((mshare([[D],[E],[G],[H],[I],[B],[C],[J],[K]]),ground([F]),linear(D),linear(E),linear(G),linear(I),linear(B),linear(C),linear(J),linear(K);mshare([[D],[E],[G],[I],[B],[C],[J],[K]]),ground([F,H]),linear(D),linear(E),linear(G),linear(I),linear(B),linear(C),linear(J),linear(K);mshare([[D],[G],[H],[I],[B],[C],[J],[K]]),ground([E,F]),linear(D),linear(G),linear(I),linear(B),linear(C),linear(J),linear(K);mshare([[D],[G],[I],[B],[C],[J],[K]]),ground([E,F,H]),linear(D),linear(G),linear(I),linear(B),linear(C),linear(J),linear(K);mshare([[D,H],[G],[H],[I],[B],[C],[J],[K]]),ground([E,F]),linear(G),linear(I),linear(B),linear(C),linear(J),linear(K))),
    quant(B,E,F,J,H,K),
    true((mshare([[D],[G],[H],[H,K],[I],[C]]),ground([E,F,B,J]),linear(D),linear(G),linear(I),linear(C);mshare([[D],[G],[I],[C]]),ground([E,F,H,B,J,K]),linear(D),linear(G),linear(I),linear(C);mshare([[D,H],[D,H,K],[G],[H],[H,K],[I],[C]]),ground([E,F,B,J]),linear(G),linear(I),linear(C))),
    number(C,D,J,G,K,I),
    true((mshare([[H],[H,I,K],[H,K]]),ground([D,E,F,G,B,C,J]);ground([D,E,F,G,H,I,B,C,J,K]))).

:- true pred quant(B,_A,C,D,E,F)
   : ( mshare([[B],[D],[E],[F]]),
       ground([_A,C]), linear(B), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([B,_A,C,D]) ).

:- true pred quant(B,_A,C,D,E,F)
   : ( mshare([[B],[_A],[D],[E],[F]]),
       ground([C]), linear(B), linear(_A), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([B,_A,C,D]) ).

:- true pred quant(B,_A,C,D,E,F)
   : ( mshare([[B],[D],[F]]),
       ground([_A,C,E]), linear(B), linear(D), linear(F) )
   => ground([B,_A,C,D,E,F]).

:- true pred quant(B,_A,C,D,E,F)
   : ( mshare([[B],[_A],[D],[F]]),
       ground([C,E]), linear(B), linear(_A), linear(D), linear(F) )
   => ground([B,_A,C,D,E,F]).

quant(B,indef,C,D,E,F) :-
    true((mshare([[B],[D],[E],[F],[G],[H],[I],[J],[K]]),ground([C]),linear(B),linear(D),linear(F),linear(G),linear(H),linear(I),linear(J),linear(K);mshare([[B],[D],[F],[G],[H],[I],[J],[K]]),ground([C,E]),linear(B),linear(D),linear(F),linear(G),linear(H),linear(I),linear(J),linear(K))),
    neg_adv(G,B,C,H,E,I),
    true((mshare([[B,G],[D],[E],[E,I],[F],[J],[K]]),ground([C,H]),linear(B),linear(D),linear(F),linear(G),linear(J),linear(K);mshare([[B,G],[D],[F],[J],[K]]),ground([C,E,H,I]),linear(B),linear(D),linear(F),linear(G),linear(J),linear(K))),
    comp_adv(G,H,J,I,K),
    true((mshare([[D],[E],[E,I],[E,I,K],[F]]),ground([B,C,G,H,J]),linear(D),linear(F);mshare([[D],[F]]),ground([B,C,E,G,H,I,J,K]),linear(D),linear(F))),
    ~(than,J,D,K,F),
    true((mshare([[E],[E,F,I,K],[E,I],[E,I,K]]),ground([B,C,D,G,H,J]);ground([B,C,D,E,F,G,H,I,J,K]))).
quant(B,indef,C,D,E,F) :-
    true((mshare([[B],[D],[E],[F],[G],[H],[I]]),ground([C]),linear(B),linear(D),linear(F),linear(G),linear(H),linear(I);mshare([[B],[D],[F],[G],[H],[I]]),ground([C,E]),linear(B),linear(D),linear(F),linear(G),linear(H),linear(I))),
    ~(at,C,G,E,H),
    true((mshare([[B],[D],[E],[E,H],[F],[I]]),ground([C,G]),linear(B),linear(D),linear(F),linear(I);mshare([[B],[D],[F],[I]]),ground([C,E,G,H]),linear(B),linear(D),linear(F),linear(I))),
    sup_adv(I,G,D,H,F),
    true((mshare([[B]]),ground([C,D,E,F,G,H,I]),linear(B);mshare([[B],[E],[E,F,H],[E,H]]),ground([C,D,G,I]),linear(B))),
    sup_op(I,B),
    true((mshare([[E],[E,F,H],[E,H]]),ground([B,C,D,G,I]);ground([B,C,D,E,F,G,H,I]))).
quant(the,def,B,C,D,E) :-
    true((mshare([[C],[D],[E]]),ground([B]),linear(C),linear(E);mshare([[C],[E]]),ground([B,D]),linear(C),linear(E))),
    ~(the,B,C,D,E),
    true((mshare([[D],[D,E]]),ground([B,C]);ground([B,C,D,E]))).
quant(same,indef,B,B,C,C).

:- true pred neg_adv(B,_A,C,D,E,F)
   : ( mshare([[B],[_A],[D],[E],[F]]),
       ground([C]), linear(B), linear(_A), linear(D), linear(F) )
   => ( mshare([[B,_A],[E],[E,F]]),
        ground([C,D]), linear(B), linear(_A) ).

:- true pred neg_adv(B,_A,C,D,E,F)
   : ( mshare([[B],[_A],[D],[F]]),
       ground([C,E]), linear(B), linear(_A), linear(D), linear(F) )
   => ( mshare([[B,_A]]),
        ground([C,D,E,F]), linear(B), linear(_A) ).

neg_adv(B,not+B,C,D,E,F) :-
    true((mshare([[B],[D],[E],[F]]),ground([C]),linear(B),linear(D),linear(F);mshare([[B],[D],[F]]),ground([C,E]),linear(B),linear(D),linear(F))),
    ~(not,C,D,E,F),
    true((mshare([[B]]),ground([C,D,E,F]),linear(B);mshare([[B],[E],[E,F]]),ground([C,D]),linear(B))).
neg_adv(B,B,C,C,D,D).

:- true pred sup_op(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]), linear(_B) )
   => ground([_A,_B]).

sup_op(least,not+less).
sup_op(most,not+more).

:- true pred np_mods(B,C,D,_A,G,H,I,J,K,L,M,N)
   : ( mshare([[B],[D],[_A],[H],[J],[L],[N]]),
       ground([C,G,I,K,M]), linear(D), linear(_A), linear(H), linear(J), linear(L), linear(N) )
   => ( mshare([[B],[B,_A],[B,_A,N],[B,N],[D,_A],[_A],[_A,N],[N]]),
        ground([C,G,H,I,J,K,L,M]), linear(D) ).

:- true pred np_mods(B,C,D,_A,G,H,I,J,K,L,M,N)
   : ( mshare([[D],[_A],[H],[J],[L],[N]]),
       ground([B,C,G,I,K,M]), linear(D), linear(_A), linear(H), linear(J), linear(L), linear(N) )
   => ( mshare([[D,_A],[_A],[_A,N],[N]]),
        ground([B,C,G,H,I,J,K,L,M]), linear(D) ).

:- true pred np_mods(B,C,D,_A,G,H,I,J,K,L,M,N)
   : ( mshare([[D],[_A],[H],[J],[L],[M],[N]]),
       ground([B,C,G,I,K]), linear(D), linear(_A), linear(H), linear(J), linear(L), linear(N) )
   => ( mshare([[D,_A],[_A],[_A,M],[_A,M,N],[_A,N],[M],[M,N],[N]]),
        ground([B,C,G,H,I,J,K,L]), linear(D) ).

:- true pred np_mods(B,C,D,_A,G,H,I,J,K,L,M,N)
   : ( mshare([[B],[B,M],[D],[_A],[H],[J],[L],[M],[N]]),
       ground([C,G,I,K]), linear(D), linear(_A), linear(H), linear(J), linear(L), linear(N) )
   => ( mshare([[B],[B,_A],[B,_A,M],[B,_A,M,N],[B,_A,N],[B,M],[B,M,N],[B,N],[D,_A],[_A],[_A,M],[_A,M,N],[_A,N],[M],[M,N],[N]]),
        ground([C,G,H,I,J,K,L]), linear(D) ).

np_mods(B,C,D,[E|F],G,H,I,J,K,L,M,N) :-
    true((mshare([[B],[B,M],[D],[H],[J],[L],[M],[N],[E],[F],[O],[P],[Q],[R],[S],[T],[U]]),ground([C,G,I,K]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(E),linear(F),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U);mshare([[B],[D],[H],[J],[L],[N],[E],[F],[O],[P],[Q],[R],[S],[T],[U]]),ground([C,G,I,K,M]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(E),linear(F),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U);mshare([[D],[H],[J],[L],[M],[N],[E],[F],[O],[P],[Q],[R],[S],[T],[U]]),ground([B,C,G,I,K]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(E),linear(F),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U);mshare([[D],[H],[J],[L],[N],[E],[F],[O],[P],[Q],[R],[S],[T],[U]]),ground([B,C,G,I,K,M]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(E),linear(F),linear(O),linear(P),linear(Q),linear(R),linear(S),linear(T),linear(U))),
    np_mod(B,C,E,G,O,K,P,M,Q),
    true((mshare([[B],[B,M],[B,M,E],[B,M,E,O],[B,M,E,O,Q],[B,M,E,Q],[B,M,O],[B,M,O,Q],[B,M,Q],[B,E],[B,E,Q],[B,Q],[D],[H],[J],[L],[M],[M,E],[M,E,O],[M,E,O,Q],[M,E,Q],[M,O],[M,O,Q],[M,Q],[N],[E],[E,Q],[F],[Q],[R],[S],[T],[U]]),ground([C,G,I,K,P]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(R),linear(S),linear(T),linear(U);mshare([[B],[B,E],[B,E,Q],[B,Q],[D],[H],[J],[L],[N],[E],[E,Q],[F],[Q],[R],[S],[T],[U]]),ground([C,G,I,K,M,O,P]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(R),linear(S),linear(T),linear(U);mshare([[D],[H],[J],[L],[M],[M,E],[M,E,O],[M,E,O,Q],[M,E,Q],[M,O],[M,O,Q],[M,Q],[N],[E],[E,Q],[F],[Q],[R],[S],[T],[U]]),ground([B,C,G,I,K,P]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(R),linear(S),linear(T),linear(U);mshare([[D],[H],[J],[L],[N],[E],[E,Q],[F],[Q],[R],[S],[T],[U]]),ground([B,C,G,I,K,M,O,P]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(R),linear(S),linear(T),linear(U))),
    trace1(R),
    true((mshare([[B],[B,M],[B,M,E],[B,M,E,O],[B,M,E,O,Q],[B,M,E,Q],[B,M,O],[B,M,O,Q],[B,M,Q],[B,E],[B,E,Q],[B,Q],[D],[H],[J],[L],[M],[M,E],[M,E,O],[M,E,O,Q],[M,E,Q],[M,O],[M,O,Q],[M,Q],[N],[E],[E,Q],[F],[Q],[S],[T],[U]]),ground([C,G,I,K,P,R]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(S),linear(T),linear(U);mshare([[B],[B,E],[B,E,Q],[B,Q],[D],[H],[J],[L],[N],[E],[E,Q],[F],[Q],[S],[T],[U]]),ground([C,G,I,K,M,O,P,R]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(S),linear(T),linear(U);mshare([[D],[H],[J],[L],[M],[M,E],[M,E,O],[M,E,O,Q],[M,E,Q],[M,O],[M,O,Q],[M,Q],[N],[E],[E,Q],[F],[Q],[S],[T],[U]]),ground([B,C,G,I,K,P,R]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(S),linear(T),linear(U);mshare([[D],[H],[J],[L],[N],[E],[E,Q],[F],[Q],[S],[T],[U]]),ground([B,C,G,I,K,M,O,P,R]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(S),linear(T),linear(U))),
    myplus(R,O,S),
    true((mshare([[B],[B,M],[B,M,E],[B,M,E,O],[B,M,E,O,Q],[B,M,E,Q],[B,M,O],[B,M,O,Q],[B,M,Q],[B,E],[B,E,Q],[B,Q],[D],[H],[J],[L],[M],[M,E],[M,E,O],[M,E,O,Q],[M,E,Q],[M,O],[M,O,Q],[M,Q],[N],[E],[E,Q],[F],[Q],[T],[U]]),ground([C,G,I,K,P,R,S]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(T),linear(U);mshare([[B],[B,E],[B,E,Q],[B,Q],[D],[H],[J],[L],[N],[E],[E,Q],[F],[Q],[T],[U]]),ground([C,G,I,K,M,O,P,R,S]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(T),linear(U);mshare([[D],[H],[J],[L],[M],[M,E],[M,E,O],[M,E,O,Q],[M,E,Q],[M,O],[M,O,Q],[M,Q],[N],[E],[E,Q],[F],[Q],[T],[U]]),ground([B,C,G,I,K,P,R,S]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(T),linear(U);mshare([[D],[H],[J],[L],[N],[E],[E,Q],[F],[Q],[T],[U]]),ground([B,C,G,I,K,M,O,P,R,S]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(T),linear(U))),
    minus(G,S,T),
    true((mshare([[B],[B,M],[B,M,E],[B,M,E,O],[B,M,E,O,Q],[B,M,E,Q],[B,M,O],[B,M,O,Q],[B,M,Q],[B,E],[B,E,Q],[B,Q],[D],[H],[J],[L],[M],[M,E],[M,E,O],[M,E,O,Q],[M,E,Q],[M,O],[M,O,Q],[M,Q],[N],[E],[E,Q],[F],[Q],[U]]),ground([C,G,I,K,P,R,S,T]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(U);mshare([[B],[B,E],[B,E,Q],[B,Q],[D],[H],[J],[L],[N],[E],[E,Q],[F],[Q],[U]]),ground([C,G,I,K,M,O,P,R,S,T]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(U);mshare([[D],[H],[J],[L],[M],[M,E],[M,E,O],[M,E,O,Q],[M,E,Q],[M,O],[M,O,Q],[M,Q],[N],[E],[E,Q],[F],[Q],[U]]),ground([B,C,G,I,K,P,R,S,T]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(U);mshare([[D],[H],[J],[L],[N],[E],[E,Q],[F],[Q],[U]]),ground([B,C,G,I,K,M,O,P,R,S,T]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F),linear(U))),
    myplus(O,G,U),
    true((mshare([[B],[B,M],[B,M,E],[B,M,E,Q],[B,M,Q],[B,E],[B,E,Q],[B,Q],[D],[H],[J],[L],[M],[M,E],[M,E,Q],[M,Q],[N],[E],[E,Q],[F],[Q]]),ground([C,G,I,K,O,P,R,S,T,U]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F);mshare([[B],[B,E],[B,E,Q],[B,Q],[D],[H],[J],[L],[N],[E],[E,Q],[F],[Q]]),ground([C,G,I,K,M,O,P,R,S,T,U]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F);mshare([[D],[H],[J],[L],[M],[M,E],[M,E,Q],[M,Q],[N],[E],[E,Q],[F],[Q]]),ground([B,C,G,I,K,O,P,R,S,T,U]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F);mshare([[D],[H],[J],[L],[N],[E],[E,Q],[F],[Q]]),ground([B,C,G,I,K,M,O,P,R,S,T,U]),linear(D),linear(H),linear(J),linear(L),linear(N),linear(F))),
    np_mods(B,C,D,F,T,H,U,J,P,L,Q,N),
    true((mshare([[B],[B,M],[B,M,N],[B,M,N,E],[B,M,N,E,F],[B,M,N,E,F,Q],[B,M,N,E,Q],[B,M,N,F],[B,M,N,F,Q],[B,M,N,Q],[B,M,E],[B,M,E,F],[B,M,E,F,Q],[B,M,E,Q],[B,M,F],[B,M,F,Q],[B,M,Q],[B,N],[B,N,E],[B,N,E,F],[B,N,E,F,Q],[B,N,E,Q],[B,N,F],[B,N,F,Q],[B,N,Q],[B,E],[B,E,F],[B,E,F,Q],[B,E,Q],[B,F],[B,F,Q],[B,Q],[D,F],[M],[M,N,E,F,Q],[M,N,E,Q],[M,N,F,Q],[M,N,Q],[M,E],[M,E,F,Q],[M,E,Q],[M,F,Q],[M,Q],[N],[N,E,F,Q],[N,E,Q],[N,F],[N,F,Q],[N,Q],[E],[E,F,Q],[E,Q],[F],[F,Q],[Q]]),ground([C,G,H,I,J,K,L,O,P,R,S,T,U]),linear(D);mshare([[B],[B,N],[B,N,E],[B,N,E,F],[B,N,E,F,Q],[B,N,E,Q],[B,N,F],[B,N,F,Q],[B,N,Q],[B,E],[B,E,F],[B,E,F,Q],[B,E,Q],[B,F],[B,F,Q],[B,Q],[D,F],[N],[N,E,F,Q],[N,E,Q],[N,F],[N,F,Q],[N,Q],[E],[E,F,Q],[E,Q],[F],[F,Q],[Q]]),ground([C,G,H,I,J,K,L,M,O,P,R,S,T,U]),linear(D);mshare([[D,F],[M],[M,N,E,F,Q],[M,N,E,Q],[M,N,F,Q],[M,N,Q],[M,E],[M,E,F,Q],[M,E,Q],[M,F,Q],[M,Q],[N],[N,E,F,Q],[N,E,Q],[N,F],[N,F,Q],[N,Q],[E],[E,F,Q],[E,Q],[F],[F,Q],[Q]]),ground([B,C,G,H,I,J,K,L,O,P,R,S,T,U]),linear(D);mshare([[D,F],[N],[N,E,F,Q],[N,E,Q],[N,F],[N,F,Q],[N,Q],[E],[E,F,Q],[E,Q],[F],[F,Q],[Q]]),ground([B,C,G,H,I,J,K,L,M,O,P,R,S,T,U]),linear(D))).
np_mods(B,C,D,D,E,E,F,F,G,G,H,H).

:- true pred np_mod(B,C,D,E,F,G,H,I,J)
   : ( mshare([[B],[D],[F],[H],[J]]),
       ground([C,E,G,I]), linear(D), linear(F), linear(H), linear(J) )
   => ( mshare([[B],[B,D],[B,D,J],[B,J],[D],[D,J],[J]]),
        ground([C,E,F,G,H,I]) ).

:- true pred np_mod(B,C,D,E,F,G,H,I,J)
   : ( mshare([[D],[F],[H],[J]]),
       ground([B,C,E,G,I]), linear(D), linear(F), linear(H), linear(J) )
   => ( mshare([[D],[D,J],[J]]),
        ground([B,C,E,F,G,H,I]) ).

:- true pred np_mod(B,C,D,E,F,G,H,I,J)
   : ( mshare([[B],[B,I],[D],[F],[H],[I],[J]]),
       ground([C,E,G]), linear(D), linear(F), linear(H), linear(J) )
   => ( mshare([[B],[B,D],[B,D,F,I],[B,D,F,I,J],[B,D,I],[B,D,I,J],[B,D,J],[B,F,I],[B,F,I,J],[B,I],[B,I,J],[B,J],[D],[D,F,I],[D,F,I,J],[D,I],[D,I,J],[D,J],[F,I],[F,I,J],[I],[I,J],[J]]),
        ground([C,E,G,H]) ).

:- true pred np_mod(B,C,D,E,F,G,H,I,J)
   : ( mshare([[D],[F],[H],[I],[J]]),
       ground([B,C,E,G]), linear(D), linear(F), linear(H), linear(J) )
   => ( mshare([[D],[D,F,I],[D,F,I,J],[D,I],[D,I,J],[D,J],[F,I],[F,I,J],[I],[I,J],[J]]),
        ground([B,C,E,G,H]) ).

np_mod(B,C,D,E,F,G,H,I,J) :-
    true((mshare([[B],[B,I],[D],[F],[H],[I],[J]]),ground([C,E,G]),linear(D),linear(F),linear(H),linear(J);mshare([[B],[D],[F],[H],[J]]),ground([C,E,G,I]),linear(D),linear(F),linear(H),linear(J);mshare([[D],[F],[H],[I],[J]]),ground([B,C,E,G]),linear(D),linear(F),linear(H),linear(J);mshare([[D],[F],[H],[J]]),ground([B,C,E,G,I]),linear(D),linear(F),linear(H),linear(J))),
    pp(D,C,E,F,G,H,I,J),
    true((mshare([[B],[B,D,F,I],[B,D,F,I,J],[B,D,I],[B,D,I,J],[B,F,I],[B,F,I,J],[B,I],[B,I,J],[D],[D,F,I],[D,F,I,J],[D,I],[D,I,J],[D,J],[F,I],[F,I,J],[I],[I,J],[J]]),ground([C,E,G,H]);mshare([[B],[D],[D,J],[J]]),ground([C,E,F,G,H,I]);mshare([[D],[D,F,I],[D,F,I,J],[D,I],[D,I,J],[D,J],[F,I],[F,I,J],[I],[I,J],[J]]),ground([B,C,E,G,H]);mshare([[D],[D,J],[J]]),ground([B,C,E,F,G,H,I]))).
np_mod(B,C,D,E,F,G,H,I,J) :-
    true((mshare([[B],[B,I],[D],[F],[H],[I],[J]]),ground([C,E,G]),linear(D),linear(F),linear(H),linear(J);mshare([[B],[D],[F],[H],[J]]),ground([C,E,G,I]),linear(D),linear(F),linear(H),linear(J);mshare([[D],[F],[H],[I],[J]]),ground([B,C,E,G]),linear(D),linear(F),linear(H),linear(J);mshare([[D],[F],[H],[J]]),ground([B,C,E,G,I]),linear(D),linear(F),linear(H),linear(J))),
    reduced_relative(B,D,E,F,G,H,I,J),
    true((mshare([[B],[B,D],[B,D,I],[B,D,I,J],[B,D,J],[B,I],[B,I,J],[B,J],[D],[D,I],[D,I,J],[D,J],[I],[I,J],[J]]),ground([C,E,F,G,H]);mshare([[B],[B,D],[B,D,J],[B,J],[D],[D,J],[J]]),ground([C,E,F,G,H,I]);mshare([[D],[D,I],[D,I,J],[D,J],[I],[I,J],[J]]),ground([B,C,E,F,G,H]);mshare([[D],[D,J],[J]]),ground([B,C,E,F,G,H,I]))).

:- true pred verb_mods(_A,D,E,F,G,H,I,J)
   : ( mshare([[_A],[F],[H],[I],[J]]),
       ground([D,E,G]), linear(_A), linear(F), linear(H), linear(J) )
   => ( mshare([[_A],[_A,I],[_A,I,J],[_A,J],[I],[I,J],[J]]),
        ground([D,E,F,G,H]) ).

verb_mods([B|C],D,E,F,G,H,I,J) :-
    true((
        mshare([[F],[H],[I],[J],[B],[C],[K],[L],[M],[N],[O],[P],[Q]]),
        ground([D,E,G]),
        linear(F),
        linear(H),
        linear(J),
        linear(B),
        linear(C),
        linear(K),
        linear(L),
        linear(M),
        linear(N),
        linear(O),
        linear(P),
        linear(Q)
    )),
    verb_mod(B,D,K,G,L,I,M),
    true((
        mshare([[F],[H],[I],[I,B],[I,B,K],[I,B,K,M],[I,B,M],[I,K],[I,K,M],[I,M],[J],[B],[B,M],[C],[M],[N],[O],[P],[Q]]),
        ground([D,E,G,L]),
        linear(F),
        linear(H),
        linear(J),
        linear(C),
        linear(N),
        linear(O),
        linear(P),
        linear(Q)
    )),
    trace1(N),
    true((
        mshare([[F],[H],[I],[I,B],[I,B,K],[I,B,K,M],[I,B,M],[I,K],[I,K,M],[I,M],[J],[B],[B,M],[C],[M],[O],[P],[Q]]),
        ground([D,E,G,L,N]),
        linear(F),
        linear(H),
        linear(J),
        linear(C),
        linear(O),
        linear(P),
        linear(Q)
    )),
    myplus(N,K,O),
    true((
        mshare([[F],[H],[I],[I,B],[I,B,K],[I,B,K,M],[I,B,M],[I,K],[I,K,M],[I,M],[J],[B],[B,M],[C],[M],[P],[Q]]),
        ground([D,E,G,L,N,O]),
        linear(F),
        linear(H),
        linear(J),
        linear(C),
        linear(P),
        linear(Q)
    )),
    minus(D,O,P),
    true((
        mshare([[F],[H],[I],[I,B],[I,B,K],[I,B,K,M],[I,B,M],[I,K],[I,K,M],[I,M],[J],[B],[B,M],[C],[M],[Q]]),
        ground([D,E,G,L,N,O,P]),
        linear(F),
        linear(H),
        linear(J),
        linear(C),
        linear(Q)
    )),
    myplus(K,D,Q),
    true((
        mshare([[F],[H],[I],[I,B],[I,B,M],[I,M],[J],[B],[B,M],[C],[M]]),
        ground([D,E,G,K,L,N,O,P,Q]),
        linear(F),
        linear(H),
        linear(J),
        linear(C)
    )),
    verb_mods(C,P,Q,F,L,H,M,J),
    true((
        mshare([[I],[I,J,B,C,M],[I,J,B,M],[I,J,C,M],[I,J,M],[I,B],[I,B,C,M],[I,B,M],[I,C,M],[I,M],[J],[J,B,C,M],[J,B,M],[J,C],[J,C,M],[J,M],[B],[B,C,M],[B,M],[C],[C,M],[M]]),
        ground([D,E,F,G,H,K,L,N,O,P,Q])
    )).
verb_mods([],B,C,C,D,D,E,E).

:- true pred verb_mod(B,C,D,E,F,G,H)
   : ( mshare([[B],[D],[F],[G],[H]]),
       ground([C,E]), linear(B), linear(D), linear(F), linear(H) )
   => ( mshare([[B],[B,D,G],[B,D,G,H],[B,G],[B,G,H],[B,H],[D,G],[D,G,H],[G],[G,H],[H]]),
        ground([C,E,F]) ).

verb_mod(B,C,D,E,F,G,H) :-
    true((
        mshare([[B],[D],[F],[G],[H]]),
        ground([C,E]),
        linear(B),
        linear(D),
        linear(F),
        linear(H)
    )),
    adv_phrase(B,C,D,E,F,G,H),
    true((
        mshare([[B],[B,D,G],[B,D,G,H],[B,G],[B,G,H],[B,H],[D,G],[D,G,H],[G],[G,H],[H]]),
        ground([C,E,F])
    )).
verb_mod(B,C,D,E,F,G,H) :-
    true((
        mshare([[B],[D],[F],[G],[H]]),
        ground([C,E]),
        linear(B),
        linear(D),
        linear(F),
        linear(H)
    )),
    is_adv(C),
    true((
        mshare([[B],[D],[F],[G],[H]]),
        ground([C,E]),
        linear(B),
        linear(D),
        linear(F),
        linear(H)
    )),
    adverb(B,E,F,G,H),
    true((
        mshare([[D],[G],[G,H]]),
        ground([B,C,E,F]),
        linear(D)
    )),
    empty(D),
    true((
        mshare([[G],[G,H]]),
        ground([B,C,D,E,F])
    )).
verb_mod(B,C,D,E,F,G,H) :-
    true((
        mshare([[B],[D],[F],[G],[H]]),
        ground([C,E]),
        linear(B),
        linear(D),
        linear(F),
        linear(H)
    )),
    pp(B,compl,C,D,E,F,G,H),
    true((
        mshare([[B],[B,D,G],[B,D,G,H],[B,G],[B,G,H],[B,H],[D,G],[D,G,H],[G],[G,H],[H]]),
        ground([C,E,F])
    )).

:- true pred adjs(_A,D,E,F,G)
   : ( mshare([[_A],[E],[F],[G]]),
       ground([D]), linear(_A), linear(E), linear(G) )
   => ( mshare([[F],[F,G]]),
        ground([_A,D,E]) ).

:- true pred adjs(_A,D,E,F,G)
   : ( mshare([[_A],[E],[G]]),
       ground([D,F]), linear(_A), linear(E), linear(G) )
   => ground([_A,D,E,F,G]).

adjs([B|C],D,E,F,G) :-
    true((mshare([[E],[F],[G],[B],[C],[H],[I]]),ground([D]),linear(E),linear(G),linear(B),linear(C),linear(H),linear(I);mshare([[E],[G],[B],[C],[H],[I]]),ground([D,F]),linear(E),linear(G),linear(B),linear(C),linear(H),linear(I))),
    pre_adj(B,D,H,F,I),
    true((mshare([[E],[F],[F,I],[G],[C]]),ground([D,B,H]),linear(E),linear(G),linear(C);mshare([[E],[G],[C]]),ground([D,F,B,H,I]),linear(E),linear(G),linear(C))),
    adjs(C,H,E,I,G),
    true((mshare([[F],[F,G,I],[F,I]]),ground([D,E,B,C,H]);ground([D,E,F,G,B,C,H,I]))).
adjs([],B,B,C,C).

:- true pred pre_adj(B,C,D,E,F)
   : ( mshare([[B],[D],[E],[F]]),
       ground([C]), linear(B), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([B,C,D]) ).

:- true pred pre_adj(B,C,D,E,F)
   : ( mshare([[B],[D],[F]]),
       ground([C,E]), linear(B), linear(D), linear(F) )
   => ground([B,C,D,E,F]).

pre_adj(B,C,D,E,F) :-
    true((mshare([[B],[D],[E],[F],[G]]),ground([C]),linear(B),linear(D),linear(F),linear(G);mshare([[B],[D],[F],[G]]),ground([C,E]),linear(B),linear(D),linear(F),linear(G))),
    adj(G,B,C,D,E,F),
    true((mshare([[E],[E,F]]),ground([B,C,D,G]);ground([B,C,D,E,F,G]))).
pre_adj(B,C,D,E,F) :-
    true((mshare([[B],[D],[E],[F]]),ground([C]),linear(B),linear(D),linear(F);mshare([[B],[D],[F]]),ground([C,E]),linear(B),linear(D),linear(F))),
    sup_phrase(B,C,D,E,F),
    true((mshare([[E],[E,F]]),ground([B,C,D]);ground([B,C,D,E,F]))).

:- true pred sup_phrase(_A,C,D,E,F)
   : ( mshare([[_A],[D],[E],[F]]),
       ground([C]), linear(_A), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([_A,C,D]) ).

:- true pred sup_phrase(_A,C,D,E,F)
   : ( mshare([[_A],[D],[F]]),
       ground([C,E]), linear(_A), linear(D), linear(F) )
   => ground([_A,C,D,E,F]).

sup_phrase(sup(most,B),C,D,E,F) :-
    true((mshare([[D],[E],[F],[B]]),ground([C]),linear(D),linear(F),linear(B);mshare([[D],[F],[B]]),ground([C,E]),linear(D),linear(F),linear(B))),
    sup_adj(B,C,D,E,F),
    true((mshare([[E],[E,F]]),ground([C,D,B]);ground([C,D,E,F,B]))).
sup_phrase(sup(B,C),D,E,F,G) :-
    true((mshare([[E],[F],[G],[B],[C],[I],[J]]),ground([D]),linear(E),linear(G),linear(B),linear(C),linear(I),linear(J);mshare([[E],[G],[B],[C],[I],[J]]),ground([D,F]),linear(E),linear(G),linear(B),linear(C),linear(I),linear(J))),
    sup_adv(B,D,I,F,J),
    true((mshare([[E],[F],[F,J],[G],[C]]),ground([D,B,I]),linear(E),linear(G),linear(C);mshare([[E],[G],[C]]),ground([D,F,B,I,J]),linear(E),linear(G),linear(C))),
    adj(quant,C,I,E,J,G),
    true((mshare([[F],[F,G,J],[F,J]]),ground([D,E,B,C,I]);ground([D,E,F,G,B,C,I,J]))).

:- true pred comp_phrase(_A,E,F,G,H,I)
   : ( mshare([[_A],[E],[G],[I]]),
       ground([F,H]), linear(_A), linear(E), linear(G), linear(I) )
   => ( mshare([[_A],[_A,I],[I]]),
        ground([E,F,G,H]) ).

:- true pred comp_phrase(_A,E,F,G,H,I)
   : ( mshare([[_A],[E],[G],[H],[I]]),
       ground([F]), linear(_A), linear(E), linear(G), linear(I) )
   => ( mshare([[_A],[_A,E,H],[_A,E,H,I],[_A,H],[_A,H,I],[_A,I],[E,H],[E,H,I],[H],[H,I],[I]]),
        ground([F,G]) ).

comp_phrase(comp(B,C,D),E,F,G,H,I) :-
    true((mshare([[E],[G],[H],[I],[B],[C],[D],[J],[K],[L],[M],[N],[O]]),ground([F]),linear(E),linear(G),linear(I),linear(B),linear(C),linear(D),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O);mshare([[E],[G],[I],[B],[C],[D],[J],[K],[L],[M],[N],[O]]),ground([F,H]),linear(E),linear(G),linear(I),linear(B),linear(C),linear(D),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O))),
    ( comp(B,C,F,J,H,K) ),
    true((mshare([[E],[G],[H],[H,K],[I],[D],[L],[M],[N],[O]]),ground([F,B,C,J]),linear(E),linear(G),linear(I),linear(D),linear(L),linear(M),linear(N),linear(O);mshare([[E],[G],[I],[D],[L],[M],[N],[O]]),ground([F,H,B,C,J,K]),linear(E),linear(G),linear(I),linear(D),linear(L),linear(M),linear(N),linear(O))),
    np_no_trace(L),
    true((mshare([[E],[G],[H],[H,K],[I],[D],[M],[N],[O]]),ground([F,B,C,J,L]),linear(E),linear(G),linear(I),linear(D),linear(M),linear(N),linear(O);mshare([[E],[G],[I],[D],[M],[N],[O]]),ground([F,H,B,C,J,K,L]),linear(E),linear(G),linear(I),linear(D),linear(M),linear(N),linear(O))),
    prep_case(M),
    true((mshare([[E],[G],[H],[H,K],[I],[D],[N],[O]]),ground([F,B,C,J,L,M]),linear(E),linear(G),linear(I),linear(D),linear(N),linear(O);mshare([[E],[G],[I],[D],[N],[O]]),ground([F,H,B,C,J,K,L,M]),linear(E),linear(G),linear(I),linear(D),linear(N),linear(O))),
    np(D,N,M,O,compl,L,E,J,G,K,I),
    true((mshare([[E,H,I,D,K],[E,H,I,D,K,N],[E,H,I,D,K,N,O],[E,H,I,D,K,O],[E,H,I,K],[E,H,I,K,N],[E,H,I,K,N,O],[E,H,I,K,O],[E,H,D,K],[E,H,D,K,N],[E,H,D,K,N,O],[E,H,D,K,O],[E,H,K],[E,H,K,N],[E,H,K,N,O],[E,H,K,O],[H],[H,I,D,K],[H,I,D,K,N],[H,I,D,K,N,O],[H,I,D,K,O],[H,I,K],[H,I,K,N],[H,I,K,N,O],[H,I,K,O],[H,D,K],[H,D,K,N],[H,D,K,N,O],[H,D,K,O],[H,K],[H,K,N],[H,K,N,O],[H,K,O],[I],[I,D],[I,D,N],[D],[D,N],[N]]),ground([F,G,B,C,J,L,M]);mshare([[I],[I,D],[I,D,N],[D],[D,N],[N]]),ground([E,F,G,H,B,C,J,K,L,M,O]))).

:- true pred comp(B,C,D,E,F,G)
   : ( mshare([[B],[C],[E],[G]]),
       ground([D,F]), linear(B), linear(C), linear(E), linear(G) )
   => ground([B,C,D,E,F,G]).

:- true pred comp(B,C,D,E,F,G)
   : ( mshare([[B],[C],[E],[F],[G]]),
       ground([D]), linear(B), linear(C), linear(E), linear(G) )
   => ( mshare([[F],[F,G]]),
        ground([B,C,D,E]) ).

comp(B,C,D,E,F,G) :-
    true((mshare([[B],[C],[E],[F],[G],[H],[I],[J],[K]]),ground([D]),linear(B),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K);mshare([[B],[C],[E],[G],[H],[I],[J],[K]]),ground([D,F]),linear(B),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K))),
    comp_adv(B,D,H,F,I),
    true((mshare([[C],[E],[F],[F,I],[G],[J],[K]]),ground([B,D,H]),linear(C),linear(E),linear(G),linear(J),linear(K);mshare([[C],[E],[G],[J],[K]]),ground([B,D,F,H,I]),linear(C),linear(E),linear(G),linear(J),linear(K))),
    adj(quant,C,H,J,I,K),
    true((mshare([[E],[F],[F,I],[F,I,K],[G]]),ground([B,C,D,H,J]),linear(E),linear(G);mshare([[E],[G]]),ground([B,C,D,F,H,I,J,K]),linear(E),linear(G))),
    ~(than,J,E,K,G),
    true((mshare([[F],[F,G,I,K],[F,I],[F,I,K]]),ground([B,C,D,E,H,J]);ground([B,C,D,E,F,G,H,I,J,K]))).
comp(more,B,C,D,E,F) :-
    true((mshare([[B],[D],[E],[F],[G],[H]]),ground([C]),linear(B),linear(D),linear(F),linear(G),linear(H);mshare([[B],[D],[F],[G],[H]]),ground([C,E]),linear(B),linear(D),linear(F),linear(G),linear(H))),
    rel_adj(B,C,G,E,H),
    true((mshare([[D],[E],[E,H],[F]]),ground([B,C,G]),linear(D),linear(F);mshare([[D],[F]]),ground([B,C,E,G,H]),linear(D),linear(F))),
    ~(than,G,D,H,F),
    true((mshare([[E],[E,F,H],[E,H]]),ground([B,C,D,G]);ground([B,C,D,E,F,G,H]))).
comp(same,B,C,D,E,F) :-
    true((mshare([[B],[D],[E],[F],[G],[H],[I],[J]]),ground([C]),linear(B),linear(D),linear(F),linear(G),linear(H),linear(I),linear(J);mshare([[B],[D],[F],[G],[H],[I],[J]]),ground([C,E]),linear(B),linear(D),linear(F),linear(G),linear(H),linear(I),linear(J))),
    ~(as,C,G,E,H),
    true((mshare([[B],[D],[E],[E,H],[F],[I],[J]]),ground([C,G]),linear(B),linear(D),linear(F),linear(I),linear(J);mshare([[B],[D],[F],[I],[J]]),ground([C,E,G,H]),linear(B),linear(D),linear(F),linear(I),linear(J))),
    adj(quant,B,G,I,H,J),
    true((mshare([[D],[E],[E,H],[E,H,J],[F]]),ground([B,C,G,I]),linear(D),linear(F);mshare([[D],[F]]),ground([B,C,E,G,H,I,J]),linear(D),linear(F))),
    ~(as,I,D,J,F),
    true((mshare([[E],[E,F,H,J],[E,H],[E,H,J]]),ground([B,C,D,G,I]);ground([B,C,D,E,F,G,H,I,J]))).

:- true pred relative(B,_A,D,E,F,G,H,I,J)
   : ( mshare([[_A],[F],[H],[I],[J]]),
       ground([B,D,E,G]), linear(_A), linear(F), linear(H), linear(J) )
   => ( mshare([[_A],[_A,I],[_A,I,J],[_A,J],[I],[I,J],[J]]),
        ground([B,D,E,F,G,H]) ).

:- true pred relative(B,_A,D,E,F,G,H,I,J)
   : ( mshare([[B],[B,I],[_A],[F],[H],[I],[J]]),
       ground([D,E,G]), linear(_A), linear(F), linear(H), linear(J) )
   => ( mshare([[B],[B,_A],[B,_A,I],[B,_A,I,J],[B,_A,J],[B,I],[B,I,J],[B,J],[_A],[_A,I],[_A,I,J],[_A,J],[I],[I,J],[J]]),
        ground([D,E,F,G,H]) ).

relative(B,[C],D,E,F,G,H,I,J) :-
    true((mshare([[B],[B,I],[F],[H],[I],[J],[C],[K]]),ground([D,E,G]),linear(F),linear(H),linear(J),linear(C),linear(K);mshare([[F],[H],[I],[J],[C],[K]]),ground([B,D,E,G]),linear(F),linear(H),linear(J),linear(C),linear(K))),
    is_pred(D),
    true((mshare([[B],[B,I],[F],[H],[I],[J],[C],[K]]),ground([D,E,G]),linear(F),linear(H),linear(J),linear(C),linear(K);mshare([[F],[H],[I],[J],[C],[K]]),ground([B,D,E,G]),linear(F),linear(H),linear(J),linear(C),linear(K))),
    rel_conj(B,K,C,F,G,H,I,J),
    true((mshare([[B],[B,I],[B,I,J],[B,I,J,C],[B,I,C],[B,J],[B,J,C],[B,C],[I],[I,J],[I,J,C],[I,C],[J],[J,C],[C],[C,K],[K]]),ground([D,E,F,G,H]);mshare([[I],[I,J],[I,J,C],[I,C],[J],[J,C],[C],[C,K],[K]]),ground([B,D,E,F,G,H]))).
relative(B,[],C,D,D,E,E,F,F).

:- true pred rel_conj(B,C,D,E,F,G,H,I)
   : ( mshare([[B],[B,H],[C],[D],[E],[G],[H],[I]]),
       ground([F]), linear(C), linear(D), linear(E), linear(G), linear(I) )
   => ( mshare([[B],[B,D],[B,D,H],[B,D,H,I],[B,D,I],[B,H],[B,H,I],[B,I],[C],[C,D],[D],[D,H],[D,H,I],[D,I],[H],[H,I],[I]]),
        ground([E,F,G]) ).

:- true pred rel_conj(B,C,D,E,F,G,H,I)
   : ( mshare([[B],[B,H],[C],[D],[E],[G],[H],[I]]),
       ground([F]), linear(D), linear(E), linear(G), linear(I) )
   => ( mshare([[B],[B,D],[B,D,H],[B,D,H,I],[B,D,I],[B,H],[B,H,I],[B,I],[C],[C,D],[D],[D,H],[D,H,I],[D,I],[H],[H,I],[I]]),
        ground([E,F,G]) ).

:- true pred rel_conj(B,C,D,E,F,G,H,I)
   : ( mshare([[C],[D],[E],[G],[H],[I]]),
       ground([B,F]), linear(C), linear(D), linear(E), linear(G), linear(I) )
   => ( mshare([[C],[C,D],[D],[D,H],[D,H,I],[D,I],[H],[H,I],[I]]),
        ground([B,E,F,G]) ).

:- true pred rel_conj(B,C,D,E,F,G,H,I)
   : ( mshare([[C],[D],[E],[G],[H],[I]]),
       ground([B,F]), linear(D), linear(E), linear(G), linear(I) )
   => ( mshare([[C],[C,D],[D],[D,H],[D,H,I],[D,I],[H],[H,I],[I]]),
        ground([B,E,F,G]) ).

rel_conj(B,C,D,E,F,G,H,I) :-
    true((mshare([[B],[B,H],[C],[D],[E],[G],[H],[I],[J],[K],[L],[M]]),ground([F]),linear(C),linear(D),linear(E),linear(G),linear(I),linear(J),linear(K),linear(L),linear(M);mshare([[B],[B,H],[C],[D],[E],[G],[H],[I],[J],[K],[L],[M]]),ground([F]),linear(D),linear(E),linear(G),linear(I),linear(J),linear(K),linear(L),linear(M);mshare([[C],[D],[E],[G],[H],[I],[J],[K],[L],[M]]),ground([B,F]),linear(C),linear(D),linear(E),linear(G),linear(I),linear(J),linear(K),linear(L),linear(M);mshare([[C],[D],[E],[G],[H],[I],[J],[K],[L],[M]]),ground([B,F]),linear(D),linear(E),linear(G),linear(I),linear(J),linear(K),linear(L),linear(M))),
    rel(B,J,K,F,L,H,M),
    true((mshare([[B],[B,H],[B,H,J],[B,H,J,M],[B,H,M],[B,J],[B,J,M],[B,M],[C],[D],[E],[G],[H],[H,J],[H,J,M],[H,M],[I],[J],[J,M],[M]]),ground([F,K,L]),linear(C),linear(D),linear(E),linear(G),linear(I);mshare([[B],[B,H],[B,H,J],[B,H,J,M],[B,H,M],[B,J],[B,J,M],[B,M],[C],[D],[E],[G],[H],[H,J],[H,J,M],[H,M],[I],[J],[J,M],[M]]),ground([F,K,L]),linear(D),linear(E),linear(G),linear(I);mshare([[C],[D],[E],[G],[H],[H,J],[H,J,M],[H,M],[I],[J],[J,M],[M]]),ground([B,F,K,L]),linear(C),linear(D),linear(E),linear(G),linear(I);mshare([[C],[D],[E],[G],[H],[H,J],[H,J,M],[H,M],[I],[J],[J,M],[M]]),ground([B,F,K,L]),linear(D),linear(E),linear(G),linear(I))),
    rel_rest(B,C,J,D,K,E,L,G,M,I),
    true((mshare([[B],[B,D],[B,D,H],[B,D,H,I],[B,D,H,I,J],[B,D,H,I,J,M],[B,D,H,I,M],[B,D,H,J],[B,D,H,J,M],[B,D,H,M],[B,D,I],[B,D,I,J],[B,D,I,J,M],[B,D,I,M],[B,D,J],[B,D,J,M],[B,D,M],[B,H],[B,H,I],[B,H,I,M],[B,H,M],[B,I],[B,I,M],[B,M],[C],[C,D],[D],[D,H,I,J,M],[D,H,I,M],[D,H,J],[D,H,J,M],[D,H,M],[D,I],[D,I,J,M],[D,I,M],[D,J],[D,J,M],[D,M],[H],[H,I,M],[H,M],[I],[I,M],[M]]),ground([E,F,G,K,L]);mshare([[C],[C,D],[D],[D,H,I,J,M],[D,H,I,M],[D,H,J],[D,H,J,M],[D,H,M],[D,I],[D,I,J,M],[D,I,M],[D,J],[D,J,M],[D,M],[H],[H,I,M],[H,M],[I],[I,M],[M]]),ground([B,E,F,G,K,L]))).

:- true pred rel_rest(B,C,D,E,F,G,H,I,J,K)
   : ( mshare([[C],[D],[D,J],[E],[G],[I],[J],[K]]),
       ground([B,F,H]), linear(E), linear(G), linear(I), linear(K) )
   => ( mshare([[C],[C,E],[D,E],[D,E,J],[D,E,J,K],[E],[E,J],[E,J,K],[E,K],[J],[J,K],[K]]),
        ground([B,F,G,H,I]) ).

:- true pred rel_rest(B,C,D,E,F,G,H,I,J,K)
   : ( mshare([[B],[B,D],[B,D,J],[B,J],[C],[D],[D,J],[E],[G],[I],[J],[K]]),
       ground([F,H]), linear(E), linear(G), linear(I), linear(K) )
   => ( mshare([[B],[B,D,E],[B,D,E,J],[B,D,E,J,K],[B,D,E,K],[B,E],[B,E,J],[B,E,J,K],[B,E,K],[B,J],[B,J,K],[B,K],[C],[C,E],[D,E],[D,E,J],[D,E,J,K],[E],[E,J],[E,J,K],[E,K],[J],[J,K],[K]]),
        ground([F,G,H,I]) ).

:- true pred rel_rest(B,C,D,E,F,G,H,I,J,K)
   : ( mshare([[B],[B,D],[B,D,J],[B,J],[C],[D],[D,J],[E],[G],[I],[J],[K]]),
       ground([F,H]), linear(C), linear(E), linear(G), linear(I), linear(K) )
   => ( mshare([[B],[B,D,E],[B,D,E,J],[B,D,E,J,K],[B,D,E,K],[B,E],[B,E,J],[B,E,J,K],[B,E,K],[B,J],[B,J,K],[B,K],[C],[C,E],[D,E],[D,E,J],[D,E,J,K],[E],[E,J],[E,J,K],[E,K],[J],[J,K],[K]]),
        ground([F,G,H,I]) ).

:- true pred rel_rest(B,C,D,E,F,G,H,I,J,K)
   : ( mshare([[C],[D],[D,J],[E],[G],[I],[J],[K]]),
       ground([B,F,H]), linear(C), linear(E), linear(G), linear(I), linear(K) )
   => ( mshare([[C],[C,E],[D,E],[D,E,J],[D,E,J,K],[E],[E,J],[E,J,K],[E,K],[J],[J,K],[K]]),
        ground([B,F,G,H,I]) ).

rel_rest(B,C,D,E,F,G,H,I,J,K) :-
    true((mshare([[B],[B,D],[B,D,J],[B,J],[C],[D],[D,J],[E],[G],[I],[J],[K],[L],[M],[N],[O]]),ground([F,H]),linear(C),linear(E),linear(G),linear(I),linear(K),linear(L),linear(M),linear(N),linear(O);mshare([[B],[B,D],[B,D,J],[B,J],[C],[D],[D,J],[E],[G],[I],[J],[K],[L],[M],[N],[O]]),ground([F,H]),linear(E),linear(G),linear(I),linear(K),linear(L),linear(M),linear(N),linear(O);mshare([[C],[D],[D,J],[E],[G],[I],[J],[K],[L],[M],[N],[O]]),ground([B,F,H]),linear(C),linear(E),linear(G),linear(I),linear(K),linear(L),linear(M),linear(N),linear(O);mshare([[C],[D],[D,J],[E],[G],[I],[J],[K],[L],[M],[N],[O]]),ground([B,F,H]),linear(E),linear(G),linear(I),linear(K),linear(L),linear(M),linear(N),linear(O))),
    conj(C,L,D,M,E,H,N,J,O),
    true((mshare([[B],[B,D,E],[B,D,E,J],[B,D,E,J,O],[B,J],[B,J,O],[C,E,L],[D,E],[D,E,J],[D,E,J,O],[E,M],[G],[I],[J],[J,O],[K]]),ground([F,H,N]),linear(G),linear(I),linear(K),linear(M);mshare([[C,E,L],[D,E],[D,E,J],[D,E,J,O],[E,M],[G],[I],[J],[J,O],[K]]),ground([B,F,H,N]),linear(G),linear(I),linear(K),linear(M))),
    rel_conj(B,L,M,G,N,I,O,K),
    true((mshare([[B],[B,D,E],[B,D,E,J],[B,D,E,J,K],[B,D,E,J,K,M],[B,D,E,J,K,M,O],[B,D,E,J,K,O],[B,D,E,J,M],[B,D,E,J,M,O],[B,D,E,J,O],[B,D,E,K],[B,D,E,K,M],[B,D,E,M],[B,E,J,K,M],[B,E,J,K,M,O],[B,E,J,M],[B,E,J,M,O],[B,E,K,M],[B,E,M],[B,J],[B,J,K],[B,J,K,O],[B,J,O],[B,K],[C,E,L],[C,E,L,M],[D,E],[D,E,J],[D,E,J,K,M,O],[D,E,J,K,O],[D,E,J,M,O],[D,E,J,O],[E,J,K,M,O],[E,J,M,O],[E,K,M],[E,M],[J],[J,K,O],[J,O],[K]]),ground([F,G,H,I,N]);mshare([[C,E,L],[C,E,L,M],[D,E],[D,E,J],[D,E,J,K,M,O],[D,E,J,K,O],[D,E,J,M,O],[D,E,J,O],[E,J,K,M,O],[E,J,M,O],[E,K,M],[E,M],[J],[J,K,O],[J,O],[K]]),ground([B,F,G,H,I,N]))).
rel_rest(B,C,D,D,E,E,F,F,G,G).

:- true pred rel(B,_A,E,F,G,H,I)
   : ( mshare([[B],[B,H],[_A],[E],[G],[H],[I]]),
       ground([F]), linear(_A), linear(E), linear(G), linear(I) )
   => ( mshare([[B],[B,_A],[B,_A,H],[B,_A,H,I],[B,_A,I],[B,H],[B,H,I],[B,I],[_A],[_A,H],[_A,H,I],[_A,I],[H],[H,I],[I]]),
        ground([E,F,G]) ).

:- true pred rel(B,_A,E,F,G,H,I)
   : ( mshare([[_A],[E],[G],[H],[I]]),
       ground([B,F]), linear(_A), linear(E), linear(G), linear(I) )
   => ( mshare([[_A],[_A,H],[_A,H,I],[_A,I],[H],[H,I],[I]]),
        ground([B,E,F,G]) ).

rel(B,rel(C,D),E,F,G,H,I) :-
    true((mshare([[B],[B,H],[E],[G],[H],[I],[C],[D],[J],[K],[L],[M],[N],[O],[P],[Q]]),ground([F]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q);mshare([[E],[G],[H],[I],[C],[D],[J],[K],[L],[M],[N],[O],[P],[Q]]),ground([B,F]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q))),
    myopen(F,J,H,K),
    true((mshare([[B],[B,H,K],[E],[G],[H,K],[I],[C],[D],[L],[M],[N],[O],[P],[Q]]),ground([F,J]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q);mshare([[E],[G],[H,K],[I],[C],[D],[L],[M],[N],[O],[P],[Q]]),ground([B,F,J]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q))),
    variable(B,C,J,L,K,M),
    true((mshare([[B],[B,H,C,K],[B,H,C,K,M],[B,H,K],[B,H,K,M],[B,C],[B,C,M],[B,M],[E],[G],[H,C,K],[H,C,K,M],[H,K],[H,K,M],[I],[C],[C,M],[D],[M],[N],[O],[P],[Q]]),ground([F,J,L]),linear(E),linear(G),linear(I),linear(D),linear(N),linear(O),linear(P),linear(Q);mshare([[E],[G],[H,C,K],[H,C,K,M],[H,K],[H,K,M],[I],[C],[C,M],[D],[M],[N],[O],[P],[Q]]),ground([B,F,J,L]),linear(E),linear(G),linear(I),linear(D),linear(N),linear(O),linear(P),linear(Q))),
    s(D,N,L,O,M,P),
    true((mshare([[B],[B,H,C,D,K,M],[B,H,C,D,K,M,P],[B,H,C,K],[B,H,C,K,M],[B,H,C,K,M,P],[B,H,D,K,M],[B,H,D,K,M,P],[B,H,K],[B,H,K,M],[B,H,K,M,P],[B,C],[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[E],[G],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I],[C],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P],[Q]]),ground([F,J,L,N,O]),linear(E),linear(G),linear(I),linear(Q);mshare([[E],[G],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I],[C],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P],[Q]]),ground([B,F,J,L,N,O]),linear(E),linear(G),linear(I),linear(Q))),
    trace1(Q),
    true((mshare([[B],[B,H,C,D,K,M],[B,H,C,D,K,M,P],[B,H,C,K],[B,H,C,K,M],[B,H,C,K,M,P],[B,H,D,K,M],[B,H,D,K,M,P],[B,H,K],[B,H,K,M],[B,H,K,M,P],[B,C],[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[E],[G],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I],[C],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([F,J,L,N,O,Q]),linear(E),linear(G),linear(I);mshare([[E],[G],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I],[C],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([B,F,J,L,N,O,Q]),linear(E),linear(G),linear(I))),
    minus(N,Q,E),
    true((mshare([[B],[B,H,C,D,K,M],[B,H,C,D,K,M,P],[B,H,C,K],[B,H,C,K,M],[B,H,C,K,M,P],[B,H,D,K,M],[B,H,D,K,M,P],[B,H,K],[B,H,K,M],[B,H,K,M,P],[B,C],[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[G],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I],[C],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([E,F,J,L,N,O,Q]),linear(G),linear(I);mshare([[G],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I],[C],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([B,E,F,J,L,N,O,Q]),linear(G),linear(I))),
    close(O,G,P,I),
    true((mshare([[B],[B,H,I,C,D,K,M,P],[B,H,I,C,K,M,P],[B,H,I,D,K,M,P],[B,H,I,K,M,P],[B,H,C,D,K,M],[B,H,C,D,K,M,P],[B,H,C,K],[B,H,C,K,M],[B,H,C,K,M,P],[B,H,D,K,M],[B,H,D,K,M,P],[B,H,K],[B,H,K,M],[B,H,K,M,P],[B,I,C,D,M,P],[B,I,C,M,P],[B,I,D,M,P],[B,I,M,P],[B,C],[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[H,I,C,D,K,M,P],[H,I,C,K,M,P],[H,I,D,K,M,P],[H,I,K,M,P],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I,C,D,M,P],[I,C,M,P],[I,D,M,P],[I,D,P],[I,M,P],[I,P],[C],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([E,F,G,J,L,N,O,Q]);mshare([[H,I,C,D,K,M,P],[H,I,C,K,M,P],[H,I,D,K,M,P],[H,I,K,M,P],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I,C,D,M,P],[I,C,M,P],[I,D,M,P],[I,D,P],[I,M,P],[I,P],[C],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([B,E,F,G,J,L,N,O,Q]))).

:- true pred variable(B,C,D,E,F,_A)
   : ( mshare([[B],[B,F],[C],[E],[F],[_A]]),
       ground([D]), linear(C), linear(E), linear(_A) )
   => ( mshare([[B],[B,C],[B,C,F],[B,C,F,_A],[B,C,_A],[B,F],[B,F,_A],[B,_A],[C],[C,F],[C,F,_A],[C,_A],[F],[F,_A],[_A]]),
        ground([D,E]) ).

:- true pred variable(B,C,D,E,F,_A)
   : ( mshare([[C],[E],[F],[_A]]),
       ground([B,D]), linear(C), linear(E), linear(_A) )
   => ( mshare([[C],[C,F],[C,F,_A],[C,_A],[F],[F,_A],[_A]]),
        ground([B,D,E]) ).

variable(B,C,D,E,F,x(gap,nonterminal,np(np(B,wh(C),[]),B,G,H,I,J,K),L)) :-
    true((mshare([[B],[B,F],[C],[E],[F],[L],[G],[H],[I],[J],[K]]),ground([D]),linear(C),linear(E),linear(L),linear(G),linear(H),linear(I),linear(J),linear(K);mshare([[C],[E],[F],[L],[G],[H],[I],[J],[K]]),ground([B,D]),linear(C),linear(E),linear(L),linear(G),linear(H),linear(I),linear(J),linear(K))),
    ~(that,D,E,F,L),
    true((mshare([[B],[B,F],[B,F,L],[C],[F],[F,L],[G],[H],[I],[J],[K]]),ground([D,E]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(K);mshare([[C],[F],[F,L],[G],[H],[I],[J],[K]]),ground([B,D,E]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(K))),
    trace1(J,K),
    true((mshare([[B],[B,F],[B,F,L],[C],[F],[F,L],[G],[H],[I],[J]]),ground([D,E,K]),linear(C),linear(G),linear(H),linear(I),linear(J);mshare([[C],[F],[F,L],[G],[H],[I],[J]]),ground([B,D,E,K]),linear(C),linear(G),linear(H),linear(I),linear(J))).
variable(B,C,D,E,F,x(gap,nonterminal,np(G,H,I,J,K,L,M),N)) :-
    true((mshare([[B],[B,F],[C],[E],[F],[N],[G],[H],[I],[J],[K],[L],[M]]),ground([D]),linear(C),linear(E),linear(N),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M);mshare([[C],[E],[F],[N],[G],[H],[I],[J],[K],[L],[M]]),ground([B,D]),linear(C),linear(E),linear(N),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M))),
    wh(C,B,G,H,I,D,E,F,N),
    true((mshare([[B],[B,C],[B,C,F],[B,C,F,N],[B,C,F,N,G],[B,C,F,N,G,H],[B,C,F,N,G,H,I],[B,C,F,N,G,I],[B,C,F,N,H],[B,C,F,N,H,I],[B,C,F,N,I],[B,C,F,G],[B,C,F,G,H],[B,C,F,G,H,I],[B,C,F,G,I],[B,C,F,H],[B,C,F,H,I],[B,C,F,I],[B,C,N],[B,C,N,G],[B,C,N,G,H],[B,C,N,G,H,I],[B,C,N,G,I],[B,C,N,H],[B,C,N,H,I],[B,C,N,I],[B,C,G],[B,C,G,H],[B,C,G,H,I],[B,C,G,I],[B,C,H],[B,C,H,I],[B,C,I],[B,F],[B,F,N],[B,F,N,G],[B,F,N,G,H],[B,F,N,G,H,I],[B,F,N,G,I],[B,F,N,H],[B,F,N,H,I],[B,F,N,I],[B,F,G],[B,F,G,H],[B,F,G,H,I],[B,F,G,I],[B,F,H],[B,F,H,I],[B,F,I],[B,N],[B,N,G],[B,N,G,H],[B,N,G,H,I],[B,N,G,I],[B,N,H],[B,N,H,I],[B,N,I],[B,G],[B,G,H],[B,G,H,I],[B,G,I],[B,H],[B,H,I],[B,I],[C],[C,F],[C,F,N],[C,F,N,G],[C,F,N,G,H],[C,F,N,G,H,I],[C,F,N,G,I],[C,F,N,H],[C,F,N,H,I],[C,F,N,I],[C,F,G],[C,F,G,H],[C,F,G,H,I],[C,F,G,I],[C,F,H],[C,F,H,I],[C,F,I],[C,N],[C,N,G],[C,N,G,H],[C,N,G,H,I],[C,N,G,I],[C,N,H],[C,N,H,I],[C,N,I],[C,G],[C,G,H],[C,G,H,I],[C,G,I],[C,H],[C,H,I],[C,I],[F],[F,N],[F,N,G],[F,N,G,H],[F,N,G,H,I],[F,N,G,I],[F,N,H],[F,N,H,I],[F,N,I],[F,G],[F,G,H],[F,G,H,I],[F,G,I],[F,H],[F,H,I],[F,I],[N],[N,G],[N,G,H],[G],[G,H],[I],[J],[K],[L],[M]]),ground([D,E]),linear(J),linear(K),linear(L),linear(M);mshare([[C],[C,F],[C,F,N],[C,F,N,G],[C,F,N,G,H],[C,F,N,G,H,I],[C,F,N,G,I],[C,F,N,H],[C,F,N,H,I],[C,F,N,I],[C,F,G],[C,F,G,H],[C,F,G,H,I],[C,F,G,I],[C,F,H],[C,F,H,I],[C,F,I],[C,N],[C,N,G],[C,N,G,H],[C,N,G,H,I],[C,N,G,I],[C,N,H],[C,N,H,I],[C,N,I],[C,G],[C,G,H],[C,G,H,I],[C,G,I],[C,H],[C,H,I],[C,I],[F],[F,N],[F,N,G],[F,N,G,H],[F,N,G,H,I],[F,N,G,I],[F,N,H],[F,N,H,I],[F,N,I],[F,G],[F,G,H],[F,G,H,I],[F,G,I],[F,H],[F,H,I],[F,I],[N],[N,G],[N,G,H],[G],[G,H],[I],[J],[K],[L],[M]]),ground([B,D,E]),linear(J),linear(K),linear(L),linear(M))),
    trace1(L,M),
    true((mshare([[B],[B,C],[B,C,F],[B,C,F,N],[B,C,F,N,G],[B,C,F,N,G,H],[B,C,F,N,G,H,I],[B,C,F,N,G,I],[B,C,F,N,H],[B,C,F,N,H,I],[B,C,F,N,I],[B,C,F,G],[B,C,F,G,H],[B,C,F,G,H,I],[B,C,F,G,I],[B,C,F,H],[B,C,F,H,I],[B,C,F,I],[B,C,N],[B,C,N,G],[B,C,N,G,H],[B,C,N,G,H,I],[B,C,N,G,I],[B,C,N,H],[B,C,N,H,I],[B,C,N,I],[B,C,G],[B,C,G,H],[B,C,G,H,I],[B,C,G,I],[B,C,H],[B,C,H,I],[B,C,I],[B,F],[B,F,N],[B,F,N,G],[B,F,N,G,H],[B,F,N,G,H,I],[B,F,N,G,I],[B,F,N,H],[B,F,N,H,I],[B,F,N,I],[B,F,G],[B,F,G,H],[B,F,G,H,I],[B,F,G,I],[B,F,H],[B,F,H,I],[B,F,I],[B,N],[B,N,G],[B,N,G,H],[B,N,G,H,I],[B,N,G,I],[B,N,H],[B,N,H,I],[B,N,I],[B,G],[B,G,H],[B,G,H,I],[B,G,I],[B,H],[B,H,I],[B,I],[C],[C,F],[C,F,N],[C,F,N,G],[C,F,N,G,H],[C,F,N,G,H,I],[C,F,N,G,I],[C,F,N,H],[C,F,N,H,I],[C,F,N,I],[C,F,G],[C,F,G,H],[C,F,G,H,I],[C,F,G,I],[C,F,H],[C,F,H,I],[C,F,I],[C,N],[C,N,G],[C,N,G,H],[C,N,G,H,I],[C,N,G,I],[C,N,H],[C,N,H,I],[C,N,I],[C,G],[C,G,H],[C,G,H,I],[C,G,I],[C,H],[C,H,I],[C,I],[F],[F,N],[F,N,G],[F,N,G,H],[F,N,G,H,I],[F,N,G,I],[F,N,H],[F,N,H,I],[F,N,I],[F,G],[F,G,H],[F,G,H,I],[F,G,I],[F,H],[F,H,I],[F,I],[N],[N,G],[N,G,H],[G],[G,H],[I],[J],[K],[L]]),ground([D,E,M]),linear(J),linear(K),linear(L);mshare([[C],[C,F],[C,F,N],[C,F,N,G],[C,F,N,G,H],[C,F,N,G,H,I],[C,F,N,G,I],[C,F,N,H],[C,F,N,H,I],[C,F,N,I],[C,F,G],[C,F,G,H],[C,F,G,H,I],[C,F,G,I],[C,F,H],[C,F,H,I],[C,F,I],[C,N],[C,N,G],[C,N,G,H],[C,N,G,H,I],[C,N,G,I],[C,N,H],[C,N,H,I],[C,N,I],[C,G],[C,G,H],[C,G,H,I],[C,G,I],[C,H],[C,H,I],[C,I],[F],[F,N],[F,N,G],[F,N,G,H],[F,N,G,H,I],[F,N,G,I],[F,N,H],[F,N,H,I],[F,N,I],[F,G],[F,G,H],[F,G,H,I],[F,G,I],[F,H],[F,H,I],[F,I],[N],[N,G],[N,G,H],[G],[G,H],[I],[J],[K],[L]]),ground([B,D,E,M]),linear(J),linear(K),linear(L))).
variable(B,C,D,E,F,x(gap,nonterminal,pp(pp(G,H),compl,I,J),K)) :-
    true((mshare([[B],[B,F],[C],[E],[F],[K],[I],[J],[G],[H],[L],[M],[N],[O]]),ground([D]),linear(C),linear(E),linear(K),linear(I),linear(J),linear(G),linear(H),linear(L),linear(M),linear(N),linear(O);mshare([[C],[E],[F],[K],[I],[J],[G],[H],[L],[M],[N],[O]]),ground([B,D]),linear(C),linear(E),linear(K),linear(I),linear(J),linear(G),linear(H),linear(L),linear(M),linear(N),linear(O))),
    prep(G,D,L,F,M),
    true((mshare([[B],[B,F],[B,F,M],[C],[E],[F],[F,M],[K],[I],[J],[H],[N],[O]]),ground([D,G,L]),linear(C),linear(E),linear(K),linear(I),linear(J),linear(H),linear(N),linear(O);mshare([[C],[E],[F],[F,M],[K],[I],[J],[H],[N],[O]]),ground([B,D,G,L]),linear(C),linear(E),linear(K),linear(I),linear(J),linear(H),linear(N),linear(O))),
    wh(C,B,H,N,O,L,E,M,K),
    true((mshare([[B],[B,C],[B,C,F],[B,C,F,K],[B,C,F,K,H],[B,C,F,K,H,M],[B,C,F,K,H,M,N],[B,C,F,K,H,M,N,O],[B,C,F,K,H,M,O],[B,C,F,K,H,N],[B,C,F,K,H,N,O],[B,C,F,K,H,O],[B,C,F,K,M],[B,C,F,K,M,N],[B,C,F,K,M,N,O],[B,C,F,K,M,O],[B,C,F,K,N],[B,C,F,K,N,O],[B,C,F,K,O],[B,C,F,H],[B,C,F,H,M],[B,C,F,H,M,N],[B,C,F,H,M,N,O],[B,C,F,H,M,O],[B,C,F,H,N],[B,C,F,H,N,O],[B,C,F,H,O],[B,C,F,M],[B,C,F,M,N],[B,C,F,M,N,O],[B,C,F,M,O],[B,C,F,N],[B,C,F,N,O],[B,C,F,O],[B,C,K],[B,C,K,H],[B,C,K,H,N],[B,C,K,H,N,O],[B,C,K,H,O],[B,C,K,N],[B,C,K,N,O],[B,C,K,O],[B,C,H],[B,C,H,N],[B,C,H,N,O],[B,C,H,O],[B,C,N],[B,C,N,O],[B,C,O],[B,F],[B,F,K],[B,F,K,H],[B,F,K,H,M],[B,F,K,H,M,N],[B,F,K,H,M,N,O],[B,F,K,H,M,O],[B,F,K,H,N],[B,F,K,H,N,O],[B,F,K,H,O],[B,F,K,M],[B,F,K,M,N],[B,F,K,M,N,O],[B,F,K,M,O],[B,F,K,N],[B,F,K,N,O],[B,F,K,O],[B,F,H],[B,F,H,M],[B,F,H,M,N],[B,F,H,M,N,O],[B,F,H,M,O],[B,F,H,N],[B,F,H,N,O],[B,F,H,O],[B,F,M],[B,F,M,N],[B,F,M,N,O],[B,F,M,O],[B,F,N],[B,F,N,O],[B,F,O],[B,K],[B,K,H],[B,K,H,N],[B,K,H,N,O],[B,K,H,O],[B,K,N],[B,K,N,O],[B,K,O],[B,H],[B,H,N],[B,H,N,O],[B,H,O],[B,N],[B,N,O],[B,O],[C],[C,F,K,H,M],[C,F,K,H,M,N],[C,F,K,H,M,N,O],[C,F,K,H,M,O],[C,F,K,M],[C,F,K,M,N],[C,F,K,M,N,O],[C,F,K,M,O],[C,F,H,M],[C,F,H,M,N],[C,F,H,M,N,O],[C,F,H,M,O],[C,F,M],[C,F,M,N],[C,F,M,N,O],[C,F,M,O],[C,K],[C,K,H],[C,K,H,N],[C,K,H,N,O],[C,K,H,O],[C,K,N],[C,K,N,O],[C,K,O],[C,H],[C,H,N],[C,H,N,O],[C,H,O],[C,N],[C,N,O],[C,O],[F],[F,K,H,M],[F,K,H,M,N],[F,K,H,M,N,O],[F,K,H,M,O],[F,K,M],[F,K,M,N],[F,K,M,N,O],[F,K,M,O],[F,H,M],[F,H,M,N],[F,H,M,N,O],[F,H,M,O],[F,M],[F,M,N],[F,M,N,O],[F,M,O],[K],[K,H],[K,H,N],[I],[J],[H],[H,N],[O]]),ground([D,E,G,L]),linear(I),linear(J);mshare([[C],[C,F,K,H,M],[C,F,K,H,M,N],[C,F,K,H,M,N,O],[C,F,K,H,M,O],[C,F,K,M],[C,F,K,M,N],[C,F,K,M,N,O],[C,F,K,M,O],[C,F,H,M],[C,F,H,M,N],[C,F,H,M,N,O],[C,F,H,M,O],[C,F,M],[C,F,M,N],[C,F,M,N,O],[C,F,M,O],[C,K],[C,K,H],[C,K,H,N],[C,K,H,N,O],[C,K,H,O],[C,K,N],[C,K,N,O],[C,K,O],[C,H],[C,H,N],[C,H,N,O],[C,H,O],[C,N],[C,N,O],[C,O],[F],[F,K,H,M],[F,K,H,M,N],[F,K,H,M,N,O],[F,K,H,M,O],[F,K,M],[F,K,M,N],[F,K,M,N,O],[F,K,M,O],[F,H,M],[F,H,M,N],[F,H,M,N,O],[F,H,M,O],[F,M],[F,M,N],[F,M,N,O],[F,M,O],[K],[K,H],[K,H,N],[I],[J],[H],[H,N],[O]]),ground([B,D,E,G,L]),linear(I),linear(J))),
    trace1(I,J),
    true((mshare([[B],[B,C],[B,C,F],[B,C,F,K],[B,C,F,K,H],[B,C,F,K,H,M],[B,C,F,K,H,M,N],[B,C,F,K,H,M,N,O],[B,C,F,K,H,M,O],[B,C,F,K,H,N],[B,C,F,K,H,N,O],[B,C,F,K,H,O],[B,C,F,K,M],[B,C,F,K,M,N],[B,C,F,K,M,N,O],[B,C,F,K,M,O],[B,C,F,K,N],[B,C,F,K,N,O],[B,C,F,K,O],[B,C,F,H],[B,C,F,H,M],[B,C,F,H,M,N],[B,C,F,H,M,N,O],[B,C,F,H,M,O],[B,C,F,H,N],[B,C,F,H,N,O],[B,C,F,H,O],[B,C,F,M],[B,C,F,M,N],[B,C,F,M,N,O],[B,C,F,M,O],[B,C,F,N],[B,C,F,N,O],[B,C,F,O],[B,C,K],[B,C,K,H],[B,C,K,H,N],[B,C,K,H,N,O],[B,C,K,H,O],[B,C,K,N],[B,C,K,N,O],[B,C,K,O],[B,C,H],[B,C,H,N],[B,C,H,N,O],[B,C,H,O],[B,C,N],[B,C,N,O],[B,C,O],[B,F],[B,F,K],[B,F,K,H],[B,F,K,H,M],[B,F,K,H,M,N],[B,F,K,H,M,N,O],[B,F,K,H,M,O],[B,F,K,H,N],[B,F,K,H,N,O],[B,F,K,H,O],[B,F,K,M],[B,F,K,M,N],[B,F,K,M,N,O],[B,F,K,M,O],[B,F,K,N],[B,F,K,N,O],[B,F,K,O],[B,F,H],[B,F,H,M],[B,F,H,M,N],[B,F,H,M,N,O],[B,F,H,M,O],[B,F,H,N],[B,F,H,N,O],[B,F,H,O],[B,F,M],[B,F,M,N],[B,F,M,N,O],[B,F,M,O],[B,F,N],[B,F,N,O],[B,F,O],[B,K],[B,K,H],[B,K,H,N],[B,K,H,N,O],[B,K,H,O],[B,K,N],[B,K,N,O],[B,K,O],[B,H],[B,H,N],[B,H,N,O],[B,H,O],[B,N],[B,N,O],[B,O],[C],[C,F,K,H,M],[C,F,K,H,M,N],[C,F,K,H,M,N,O],[C,F,K,H,M,O],[C,F,K,M],[C,F,K,M,N],[C,F,K,M,N,O],[C,F,K,M,O],[C,F,H,M],[C,F,H,M,N],[C,F,H,M,N,O],[C,F,H,M,O],[C,F,M],[C,F,M,N],[C,F,M,N,O],[C,F,M,O],[C,K],[C,K,H],[C,K,H,N],[C,K,H,N,O],[C,K,H,O],[C,K,N],[C,K,N,O],[C,K,O],[C,H],[C,H,N],[C,H,N,O],[C,H,O],[C,N],[C,N,O],[C,O],[F],[F,K,H,M],[F,K,H,M,N],[F,K,H,M,N,O],[F,K,H,M,O],[F,K,M],[F,K,M,N],[F,K,M,N,O],[F,K,M,O],[F,H,M],[F,H,M,N],[F,H,M,N,O],[F,H,M,O],[F,M],[F,M,N],[F,M,N,O],[F,M,O],[K],[K,H],[K,H,N],[I],[H],[H,N],[O]]),ground([D,E,J,G,L]),linear(I);mshare([[C],[C,F,K,H,M],[C,F,K,H,M,N],[C,F,K,H,M,N,O],[C,F,K,H,M,O],[C,F,K,M],[C,F,K,M,N],[C,F,K,M,N,O],[C,F,K,M,O],[C,F,H,M],[C,F,H,M,N],[C,F,H,M,N,O],[C,F,H,M,O],[C,F,M],[C,F,M,N],[C,F,M,N,O],[C,F,M,O],[C,K],[C,K,H],[C,K,H,N],[C,K,H,N,O],[C,K,H,O],[C,K,N],[C,K,N,O],[C,K,O],[C,H],[C,H,N],[C,H,N,O],[C,H,O],[C,N],[C,N,O],[C,O],[F],[F,K,H,M],[F,K,H,M,N],[F,K,H,M,N,O],[F,K,H,M,O],[F,K,M],[F,K,M,N],[F,K,M,N,O],[F,K,M,O],[F,H,M],[F,H,M,N],[F,H,M,N,O],[F,H,M,O],[F,M],[F,M,N],[F,M,N,O],[F,M,O],[K],[K,H],[K,H,N],[I],[H],[H,N],[O]]),ground([B,D,E,J,G,L]),linear(I))),
    compl_case(O),
    true((mshare([[B],[B,C],[B,C,F],[B,C,F,K],[B,C,F,K,H],[B,C,F,K,H,M],[B,C,F,K,H,M,N],[B,C,F,K,H,M,N,O],[B,C,F,K,H,M,O],[B,C,F,K,H,N],[B,C,F,K,H,N,O],[B,C,F,K,H,O],[B,C,F,K,M],[B,C,F,K,M,N],[B,C,F,K,M,N,O],[B,C,F,K,M,O],[B,C,F,K,N],[B,C,F,K,N,O],[B,C,F,K,O],[B,C,F,H],[B,C,F,H,M],[B,C,F,H,M,N],[B,C,F,H,M,N,O],[B,C,F,H,M,O],[B,C,F,H,N],[B,C,F,H,N,O],[B,C,F,H,O],[B,C,F,M],[B,C,F,M,N],[B,C,F,M,N,O],[B,C,F,M,O],[B,C,F,N],[B,C,F,N,O],[B,C,F,O],[B,C,K],[B,C,K,H],[B,C,K,H,N],[B,C,K,H,N,O],[B,C,K,H,O],[B,C,K,N],[B,C,K,N,O],[B,C,K,O],[B,C,H],[B,C,H,N],[B,C,H,N,O],[B,C,H,O],[B,C,N],[B,C,N,O],[B,C,O],[B,F],[B,F,K],[B,F,K,H],[B,F,K,H,M],[B,F,K,H,M,N],[B,F,K,H,M,N,O],[B,F,K,H,M,O],[B,F,K,H,N],[B,F,K,H,N,O],[B,F,K,H,O],[B,F,K,M],[B,F,K,M,N],[B,F,K,M,N,O],[B,F,K,M,O],[B,F,K,N],[B,F,K,N,O],[B,F,K,O],[B,F,H],[B,F,H,M],[B,F,H,M,N],[B,F,H,M,N,O],[B,F,H,M,O],[B,F,H,N],[B,F,H,N,O],[B,F,H,O],[B,F,M],[B,F,M,N],[B,F,M,N,O],[B,F,M,O],[B,F,N],[B,F,N,O],[B,F,O],[B,K],[B,K,H],[B,K,H,N],[B,K,H,N,O],[B,K,H,O],[B,K,N],[B,K,N,O],[B,K,O],[B,H],[B,H,N],[B,H,N,O],[B,H,O],[B,N],[B,N,O],[B,O],[C],[C,F,K,H,M],[C,F,K,H,M,N],[C,F,K,H,M,N,O],[C,F,K,H,M,O],[C,F,K,M],[C,F,K,M,N],[C,F,K,M,N,O],[C,F,K,M,O],[C,F,H,M],[C,F,H,M,N],[C,F,H,M,N,O],[C,F,H,M,O],[C,F,M],[C,F,M,N],[C,F,M,N,O],[C,F,M,O],[C,K],[C,K,H],[C,K,H,N],[C,K,H,N,O],[C,K,H,O],[C,K,N],[C,K,N,O],[C,K,O],[C,H],[C,H,N],[C,H,N,O],[C,H,O],[C,N],[C,N,O],[C,O],[F],[F,K,H,M],[F,K,H,M,N],[F,K,H,M,N,O],[F,K,H,M,O],[F,K,M],[F,K,M,N],[F,K,M,N,O],[F,K,M,O],[F,H,M],[F,H,M,N],[F,H,M,N,O],[F,H,M,O],[F,M],[F,M,N],[F,M,N,O],[F,M,O],[K],[K,H],[K,H,N],[I],[H],[H,N],[O]]),ground([D,E,J,G,L]),linear(I);mshare([[C],[C,F,K,H,M],[C,F,K,H,M,N],[C,F,K,H,M,N,O],[C,F,K,H,M,O],[C,F,K,M],[C,F,K,M,N],[C,F,K,M,N,O],[C,F,K,M,O],[C,F,H,M],[C,F,H,M,N],[C,F,H,M,N,O],[C,F,H,M,O],[C,F,M],[C,F,M,N],[C,F,M,N,O],[C,F,M,O],[C,K],[C,K,H],[C,K,H,N],[C,K,H,N,O],[C,K,H,O],[C,K,N],[C,K,N,O],[C,K,O],[C,H],[C,H,N],[C,H,N,O],[C,H,O],[C,N],[C,N,O],[C,O],[F],[F,K,H,M],[F,K,H,M,N],[F,K,H,M,N,O],[F,K,H,M,O],[F,K,M],[F,K,M,N],[F,K,M,N,O],[F,K,M,O],[F,H,M],[F,H,M,N],[F,H,M,N,O],[F,H,M,O],[F,M],[F,M,N],[F,M,N,O],[F,M,O],[K],[K,H],[K,H,N],[I],[H],[H,N],[O]]),ground([B,D,E,J,G,L]),linear(I))).

:- true pred wh(B,C,_A,_B,D,E,F,G,H)
   : ( mshare([[B],[C],[C,G],[_A],[_B],[D],[F],[G],[H]]),
       ground([E]), linear(B), linear(_A), linear(_B), linear(D), linear(F), linear(H) )
   => ( mshare([[B],[B,C],[B,C,_A],[B,C,_A,_B],[B,C,_A,_B,D],[B,C,_A,_B,D,G],[B,C,_A,_B,D,G,H],[B,C,_A,_B,D,H],[B,C,_A,_B,G],[B,C,_A,_B,G,H],[B,C,_A,_B,H],[B,C,_A,D],[B,C,_A,D,G],[B,C,_A,D,G,H],[B,C,_A,D,H],[B,C,_A,G],[B,C,_A,G,H],[B,C,_A,H],[B,C,_B],[B,C,_B,D],[B,C,_B,D,G],[B,C,_B,D,G,H],[B,C,_B,D,H],[B,C,_B,G],[B,C,_B,G,H],[B,C,_B,H],[B,C,D],[B,C,D,G],[B,C,D,G,H],[B,C,D,H],[B,C,G],[B,C,G,H],[B,C,H],[B,_A],[B,_A,_B],[B,_A,_B,D],[B,_A,_B,D,G],[B,_A,_B,D,G,H],[B,_A,_B,D,H],[B,_A,_B,G],[B,_A,_B,G,H],[B,_A,_B,H],[B,_A,D],[B,_A,D,G],[B,_A,D,G,H],[B,_A,D,H],[B,_A,G],[B,_A,G,H],[B,_A,H],[B,_B],[B,_B,D],[B,_B,D,G],[B,_B,D,G,H],[B,_B,D,H],[B,_B,G],[B,_B,G,H],[B,_B,H],[B,D],[B,D,G],[B,D,G,H],[B,D,H],[B,G],[B,G,H],[B,H],[C],[C,_A],[C,_A,_B],[C,_A,_B,D],[C,_A,_B,D,G],[C,_A,_B,D,G,H],[C,_A,_B,D,H],[C,_A,_B,G],[C,_A,_B,G,H],[C,_A,_B,H],[C,_A,D],[C,_A,D,G],[C,_A,D,G,H],[C,_A,D,H],[C,_A,G],[C,_A,G,H],[C,_A,H],[C,_B],[C,_B,D],[C,_B,D,G],[C,_B,D,G,H],[C,_B,D,H],[C,_B,G],[C,_B,G,H],[C,_B,H],[C,D],[C,D,G],[C,D,G,H],[C,D,H],[C,G],[C,G,H],[C,H],[_A],[_A,_B],[_A,_B,D,G],[_A,_B,D,G,H],[_A,_B,G],[_A,_B,G,H],[_A,_B,H],[_A,D,G],[_A,D,G,H],[_A,G],[_A,G,H],[_A,H],[_B,D,G],[_B,D,G,H],[_B,G],[_B,G,H],[D],[D,G],[D,G,H],[G],[G,H],[H]]),
        ground([E,F]) ).

:- true pred wh(B,C,_A,_B,D,E,F,G,H)
   : ( mshare([[B],[_A],[_B],[D],[F],[G],[H]]),
       ground([C,E]), linear(B), linear(_A), linear(_B), linear(D), linear(F), linear(H) )
   => ( mshare([[B],[B,_A],[B,_A,_B],[B,_A,_B,D],[B,_A,_B,D,G],[B,_A,_B,D,G,H],[B,_A,_B,D,H],[B,_A,_B,G],[B,_A,_B,G,H],[B,_A,_B,H],[B,_A,D],[B,_A,D,G],[B,_A,D,G,H],[B,_A,D,H],[B,_A,G],[B,_A,G,H],[B,_A,H],[B,_B],[B,_B,D],[B,_B,D,G],[B,_B,D,G,H],[B,_B,D,H],[B,_B,G],[B,_B,G,H],[B,_B,H],[B,D],[B,D,G],[B,D,G,H],[B,D,H],[B,G],[B,G,H],[B,H],[_A],[_A,_B],[_A,_B,D,G],[_A,_B,D,G,H],[_A,_B,G],[_A,_B,G,H],[_A,_B,H],[_A,D,G],[_A,D,G,H],[_A,G],[_A,G,H],[_A,H],[_B,D,G],[_B,D,G,H],[_B,G],[_B,G,H],[D],[D,G],[D,G,H],[G],[G,H],[H]]),
        ground([C,E,F]) ).

wh(B,C,np(C,wh(B),[]),C,D,E,F,G,H) :-
    true((mshare([[B],[C],[C,G],[D],[F],[G],[H],[I]]),ground([E]),linear(B),linear(D),linear(F),linear(H),linear(I);mshare([[B],[D],[F],[G],[H],[I]]),ground([C,E]),linear(B),linear(D),linear(F),linear(H),linear(I))),
    rel_pron(I,E,F,G,H),
    true((mshare([[B],[C],[C,G],[C,G,H],[D],[G],[G,H]]),ground([E,F,I]),linear(B),linear(D);mshare([[B],[D],[G],[G,H]]),ground([C,E,F,I]),linear(B),linear(D))),
    role(I,decl,D),
    true((mshare([[B],[C],[C,G],[C,G,H],[D],[G],[G,H]]),ground([E,F,I]),linear(B);mshare([[B],[D],[G],[G,H]]),ground([C,E,F,I]),linear(B))).
wh(B,C,np(D,E,[pp(F,G)]),D,H,I,J,K,L) :-
    true((mshare([[B],[C],[C,K],[D],[H],[J],[K],[L],[E],[F],[G],[N],[O],[M],[P],[Q],[R],[S]]),ground([I]),linear(B),linear(D),linear(H),linear(J),linear(L),linear(E),linear(F),linear(G),linear(N),linear(O),linear(M),linear(P),linear(Q),linear(R),linear(S);mshare([[B],[D],[H],[J],[K],[L],[E],[F],[G],[N],[O],[M],[P],[Q],[R],[S]]),ground([C,I]),linear(B),linear(D),linear(H),linear(J),linear(L),linear(E),linear(F),linear(G),linear(N),linear(O),linear(M),linear(P),linear(Q),linear(R),linear(S))),
    np_head0(E,D,M+common,I,N,K,O),
    true((mshare([[B],[C],[C,D,K],[C,D,K,E],[C,D,K,E,O],[C,D,K,E,O,M],[C,D,K,E,M],[C,D,K,O],[C,D,K,O,M],[C,D,K,M],[C,K],[C,K,E],[C,K,E,O],[C,K,E,O,M],[C,K,E,M],[C,K,O],[C,K,O,M],[C,K,M],[D],[D,K],[D,K,E],[D,K,E,O],[D,K,E,O,M],[D,K,E,M],[D,K,O],[D,K,O,M],[D,K,M],[D,E],[H],[J],[K],[K,E],[K,E,O],[K,E,O,M],[K,E,M],[K,O],[K,O,M],[K,M],[L],[F],[G],[P],[Q],[R],[S]]),ground([I,N]),linear(B),linear(H),linear(J),linear(L),linear(F),linear(G),linear(P),linear(Q),linear(R),linear(S);mshare([[B],[D],[D,K],[D,K,E],[D,K,E,O],[D,K,E,O,M],[D,K,E,M],[D,K,O],[D,K,O,M],[D,K,M],[D,E],[H],[J],[K],[K,E],[K,E,O],[K,E,O,M],[K,E,M],[K,O],[K,O,M],[K,M],[L],[F],[G],[P],[Q],[R],[S]]),ground([C,I,N]),linear(B),linear(H),linear(J),linear(L),linear(F),linear(G),linear(P),linear(Q),linear(R),linear(S))),
    prep(F,N,P,O,Q),
    true((mshare([[B],[C],[C,D,K],[C,D,K,E],[C,D,K,E,O],[C,D,K,E,O,M],[C,D,K,E,O,M,Q],[C,D,K,E,O,Q],[C,D,K,E,M],[C,D,K,O],[C,D,K,O,M],[C,D,K,O,M,Q],[C,D,K,O,Q],[C,D,K,M],[C,K],[C,K,E],[C,K,E,O],[C,K,E,O,M],[C,K,E,O,M,Q],[C,K,E,O,Q],[C,K,E,M],[C,K,O],[C,K,O,M],[C,K,O,M,Q],[C,K,O,Q],[C,K,M],[D],[D,K],[D,K,E],[D,K,E,O],[D,K,E,O,M],[D,K,E,O,M,Q],[D,K,E,O,Q],[D,K,E,M],[D,K,O],[D,K,O,M],[D,K,O,M,Q],[D,K,O,Q],[D,K,M],[D,E],[H],[J],[K],[K,E],[K,E,O],[K,E,O,M],[K,E,O,M,Q],[K,E,O,Q],[K,E,M],[K,O],[K,O,M],[K,O,M,Q],[K,O,Q],[K,M],[L],[G],[R],[S]]),ground([I,F,N,P]),linear(B),linear(H),linear(J),linear(L),linear(G),linear(R),linear(S);mshare([[B],[D],[D,K],[D,K,E],[D,K,E,O],[D,K,E,O,M],[D,K,E,O,M,Q],[D,K,E,O,Q],[D,K,E,M],[D,K,O],[D,K,O,M],[D,K,O,M,Q],[D,K,O,Q],[D,K,M],[D,E],[H],[J],[K],[K,E],[K,E,O],[K,E,O,M],[K,E,O,M,Q],[K,E,O,Q],[K,E,M],[K,O],[K,O,M],[K,O,M,Q],[K,O,Q],[K,M],[L],[G],[R],[S]]),ground([C,I,F,N,P]),linear(B),linear(H),linear(J),linear(L),linear(G),linear(R),linear(S))),
    wh(B,C,G,R,S,P,J,Q,L),
    true((mshare([[B],[B,C],[B,C,D,K],[B,C,D,K,L],[B,C,D,K,L,E],[B,C,D,K,L,E,G],[B,C,D,K,L,E,G,O],[B,C,D,K,L,E,G,O,M],[B,C,D,K,L,E,G,O,M,Q],[B,C,D,K,L,E,G,O,M,Q,R],[B,C,D,K,L,E,G,O,M,Q,R,S],[B,C,D,K,L,E,G,O,M,Q,S],[B,C,D,K,L,E,G,O,M,R],[B,C,D,K,L,E,G,O,M,R,S],[B,C,D,K,L,E,G,O,M,S],[B,C,D,K,L,E,G,O,Q],[B,C,D,K,L,E,G,O,Q,R],[B,C,D,K,L,E,G,O,Q,R,S],[B,C,D,K,L,E,G,O,Q,S],[B,C,D,K,L,E,G,O,R],[B,C,D,K,L,E,G,O,R,S],[B,C,D,K,L,E,G,O,S],[B,C,D,K,L,E,G,M],[B,C,D,K,L,E,G,M,R],[B,C,D,K,L,E,G,M,R,S],[B,C,D,K,L,E,G,M,S],[B,C,D,K,L,E,G,R],[B,C,D,K,L,E,G,R,S],[B,C,D,K,L,E,G,S],[B,C,D,K,L,E,O],[B,C,D,K,L,E,O,M],[B,C,D,K,L,E,O,M,Q],[B,C,D,K,L,E,O,M,Q,R],[B,C,D,K,L,E,O,M,Q,R,S],[B,C,D,K,L,E,O,M,Q,S],[B,C,D,K,L,E,O,M,R],[B,C,D,K,L,E,O,M,R,S],[B,C,D,K,L,E,O,M,S],[B,C,D,K,L,E,O,Q],[B,C,D,K,L,E,O,Q,R],[B,C,D,K,L,E,O,Q,R,S],[B,C,D,K,L,E,O,Q,S],[B,C,D,K,L,E,O,R],[B,C,D,K,L,E,O,R,S],[B,C,D,K,L,E,O,S],[B,C,D,K,L,E,M],[B,C,D,K,L,E,M,R],[B,C,D,K,L,E,M,R,S],[B,C,D,K,L,E,M,S],[B,C,D,K,L,E,R],[B,C,D,K,L,E,R,S],[B,C,D,K,L,E,S],[B,C,D,K,L,G],[B,C,D,K,L,G,O],[B,C,D,K,L,G,O,M],[B,C,D,K,L,G,O,M,Q],[B,C,D,K,L,G,O,M,Q,R],[B,C,D,K,L,G,O,M,Q,R,S],[B,C,D,K,L,G,O,M,Q,S],[B,C,D,K,L,G,O,M,R],[B,C,D,K,L,G,O,M,R,S],[B,C,D,K,L,G,O,M,S],[B,C,D,K,L,G,O,Q],[B,C,D,K,L,G,O,Q,R],[B,C,D,K,L,G,O,Q,R,S],[B,C,D,K,L,G,O,Q,S],[B,C,D,K,L,G,O,R],[B,C,D,K,L,G,O,R,S],[B,C,D,K,L,G,O,S],[B,C,D,K,L,G,M],[B,C,D,K,L,G,M,R],[B,C,D,K,L,G,M,R,S],[B,C,D,K,L,G,M,S],[B,C,D,K,L,G,R],[B,C,D,K,L,G,R,S],[B,C,D,K,L,G,S],[B,C,D,K,L,O],[B,C,D,K,L,O,M],[B,C,D,K,L,O,M,Q],[B,C,D,K,L,O,M,Q,R],[B,C,D,K,L,O,M,Q,R,S],[B,C,D,K,L,O,M,Q,S],[B,C,D,K,L,O,M,R],[B,C,D,K,L,O,M,R,S],[B,C,D,K,L,O,M,S],[B,C,D,K,L,O,Q],[B,C,D,K,L,O,Q,R],[B,C,D,K,L,O,Q,R,S],[B,C,D,K,L,O,Q,S],[B,C,D,K,L,O,R],[B,C,D,K,L,O,R,S],[B,C,D,K,L,O,S],[B,C,D,K,L,M],[B,C,D,K,L,M,R],[B,C,D,K,L,M,R,S],[B,C,D,K,L,M,S],[B,C,D,K,L,R],[B,C,D,K,L,R,S],[B,C,D,K,L,S],[B,C,D,K,E],[B,C,D,K,E,G],[B,C,D,K,E,G,O],[B,C,D,K,E,G,O,M],[B,C,D,K,E,G,O,M,Q],[B,C,D,K,E,G,O,M,Q,R],[B,C,D,K,E,G,O,M,Q,R,S],[B,C,D,K,E,G,O,M,Q,S],[B,C,D,K,E,G,O,M,R],[B,C,D,K,E,G,O,M,R,S],[B,C,D,K,E,G,O,M,S],[B,C,D,K,E,G,O,Q],[B,C,D,K,E,G,O,Q,R],[B,C,D,K,E,G,O,Q,R,S],[B,C,D,K,E,G,O,Q,S],[B,C,D,K,E,G,O,R],[B,C,D,K,E,G,O,R,S],[B,C,D,K,E,G,O,S],[B,C,D,K,E,G,M],[B,C,D,K,E,G,M,R],[B,C,D,K,E,G,M,R,S],[B,C,D,K,E,G,M,S],[B,C,D,K,E,G,R],[B,C,D,K,E,G,R,S],[B,C,D,K,E,G,S],[B,C,D,K,E,O],[B,C,D,K,E,O,M],[B,C,D,K,E,O,M,Q],[B,C,D,K,E,O,M,Q,R],[B,C,D,K,E,O,M,Q,R,S],[B,C,D,K,E,O,M,Q,S],[B,C,D,K,E,O,M,R],[B,C,D,K,E,O,M,R,S],[B,C,D,K,E,O,M,S],[B,C,D,K,E,O,Q],[B,C,D,K,E,O,Q,R],[B,C,D,K,E,O,Q,R,S],[B,C,D,K,E,O,Q,S],[B,C,D,K,E,O,R],[B,C,D,K,E,O,R,S],[B,C,D,K,E,O,S],[B,C,D,K,E,M],[B,C,D,K,E,M,R],[B,C,D,K,E,M,R,S],[B,C,D,K,E,M,S],[B,C,D,K,E,R],[B,C,D,K,E,R,S],[B,C,D,K,E,S],[B,C,D,K,G],[B,C,D,K,G,O],[B,C,D,K,G,O,M],[B,C,D,K,G,O,M,Q],[B,C,D,K,G,O,M,Q,R],[B,C,D,K,G,O,M,Q,R,S],[B,C,D,K,G,O,M,Q,S],[B,C,D,K,G,O,M,R],[B,C,D,K,G,O,M,R,S],[B,C,D,K,G,O,M,S],[B,C,D,K,G,O,Q],[B,C,D,K,G,O,Q,R],[B,C,D,K,G,O,Q,R,S],[B,C,D,K,G,O,Q,S],[B,C,D,K,G,O,R],[B,C,D,K,G,O,R,S],[B,C,D,K,G,O,S],[B,C,D,K,G,M],[B,C,D,K,G,M,R],[B,C,D,K,G,M,R,S],[B,C,D,K,G,M,S],[B,C,D,K,G,R],[B,C,D,K,G,R,S],[B,C,D,K,G,S],[B,C,D,K,O],[B,C,D,K,O,M],[B,C,D,K,O,M,Q],[B,C,D,K,O,M,Q,R],[B,C,D,K,O,M,Q,R,S],[B,C,D,K,O,M,Q,S],[B,C,D,K,O,M,R],[B,C,D,K,O,M,R,S],[B,C,D,K,O,M,S],[B,C,D,K,O,Q],[B,C,D,K,O,Q,R],[B,C,D,K,O,Q,R,S],[B,C,D,K,O,Q,S],[B,C,D,K,O,R],[B,C,D,K,O,R,S],[B,C,D,K,O,S],[B,C,D,K,M],[B,C,D,K,M,R],[B,C,D,K,M,R,S],[B,C,D,K,M,S],[B,C,D,K,R],[B,C,D,K,R,S],[B,C,D,K,S],[B,C,K],[B,C,K,L],[B,C,K,L,E],[B,C,K,L,E,G],[B,C,K,L,E,G,O],[B,C,K,L,E,G,O,M],[B,C,K,L,E,G,O,M,Q],[B,C,K,L,E,G,O,M,Q,R],[B,C,K,L,E,G,O,M,Q,R,S],[B,C,K,L,E,G,O,M,Q,S],[B,C,K,L,E,G,O,M,R],[B,C,K,L,E,G,O,M,R,S],[B,C,K,L,E,G,O,M,S],[B,C,K,L,E,G,O,Q],[B,C,K,L,E,G,O,Q,R],[B,C,K,L,E,G,O,Q,R,S],[B,C,K,L,E,G,O,Q,S],[B,C,K,L,E,G,O,R],[B,C,K,L,E,G,O,R,S],[B,C,K,L,E,G,O,S],[B,C,K,L,E,G,M],[B,C,K,L,E,G,M,R],[B,C,K,L,E,G,M,R,S],[B,C,K,L,E,G,M,S],[B,C,K,L,E,G,R],[B,C,K,L,E,G,R,S],[B,C,K,L,E,G,S],[B,C,K,L,E,O],[B,C,K,L,E,O,M],[B,C,K,L,E,O,M,Q],[B,C,K,L,E,O,M,Q,R],[B,C,K,L,E,O,M,Q,R,S],[B,C,K,L,E,O,M,Q,S],[B,C,K,L,E,O,M,R],[B,C,K,L,E,O,M,R,S],[B,C,K,L,E,O,M,S],[B,C,K,L,E,O,Q],[B,C,K,L,E,O,Q,R],[B,C,K,L,E,O,Q,R,S],[B,C,K,L,E,O,Q,S],[B,C,K,L,E,O,R],[B,C,K,L,E,O,R,S],[B,C,K,L,E,O,S],[B,C,K,L,E,M],[B,C,K,L,E,M,R],[B,C,K,L,E,M,R,S],[B,C,K,L,E,M,S],[B,C,K,L,E,R],[B,C,K,L,E,R,S],[B,C,K,L,E,S],[B,C,K,L,G],[B,C,K,L,G,O],[B,C,K,L,G,O,M],[B,C,K,L,G,O,M,Q],[B,C,K,L,G,O,M,Q,R],[B,C,K,L,G,O,M,Q,R,S],[B,C,K,L,G,O,M,Q,S],[B,C,K,L,G,O,M,R],[B,C,K,L,G,O,M,R,S],[B,C,K,L,G,O,M,S],[B,C,K,L,G,O,Q],[B,C,K,L,G,O,Q,R],[B,C,K,L,G,O,Q,R,S],[B,C,K,L,G,O,Q,S],[B,C,K,L,G,O,R],[B,C,K,L,G,O,R,S],[B,C,K,L,G,O,S],[B,C,K,L,G,M],[B,C,K,L,G,M,R],[B,C,K,L,G,M,R,S],[B,C,K,L,G,M,S],[B,C,K,L,G,R],[B,C,K,L,G,R,S],[B,C,K,L,G,S],[B,C,K,L,O],[B,C,K,L,O,M],[B,C,K,L,O,M,Q],[B,C,K,L,O,M,Q,R],[B,C,K,L,O,M,Q,R,S],[B,C,K,L,O,M,Q,S],[B,C,K,L,O,M,R],[B,C,K,L,O,M,R,S],[B,C,K,L,O,M,S],[B,C,K,L,O,Q],[B,C,K,L,O,Q,R],[B,C,K,L,O,Q,R,S],[B,C,K,L,O,Q,S],[B,C,K,L,O,R],[B,C,K,L,O,R,S],[B,C,K,L,O,S],[B,C,K,L,M],[B,C,K,L,M,R],[B,C,K,L,M,R,S],[B,C,K,L,M,S],[B,C,K,L,R],[B,C,K,L,R,S],[B,C,K,L,S],[B,C,K,E],[B,C,K,E,G],[B,C,K,E,G,O],[B,C,K,E,G,O,M],[B,C,K,E,G,O,M,Q],[B,C,K,E,G,O,M,Q,R],[B,C,K,E,G,O,M,Q,R,S],[B,C,K,E,G,O,M,Q,S],[B,C,K,E,G,O,M,R],[B,C,K,E,G,O,M,R,S],[B,C,K,E,G,O,M,S],[B,C,K,E,G,O,Q],[B,C,K,E,G,O,Q,R],[B,C,K,E,G,O,Q,R,S],[B,C,K,E,G,O,Q,S],[B,C,K,E,G,O,R],[B,C,K,E,G,O,R,S],[B,C,K,E,G,O,S],[B,C,K,E,G,M],[B,C,K,E,G,M,R],[B,C,K,E,G,M,R,S],[B,C,K,E,G,M,S],[B,C,K,E,G,R],[B,C,K,E,G,R,S],[B,C,K,E,G,S],[B,C,K,E,O],[B,C,K,E,O,M],[B,C,K,E,O,M,Q],[B,C,K,E,O,M,Q,R],[B,C,K,E,O,M,Q,R,S],[B,C,K,E,O,M,Q,S],[B,C,K,E,O,M,R],[B,C,K,E,O,M,R,S],[B,C,K,E,O,M,S],[B,C,K,E,O,Q],[B,C,K,E,O,Q,R],[B,C,K,E,O,Q,R,S],[B,C,K,E,O,Q,S],[B,C,K,E,O,R],[B,C,K,E,O,R,S],[B,C,K,E,O,S],[B,C,K,E,M],[B,C,K,E,M,R],[B,C,K,E,M,R,S],[B,C,K,E,M,S],[B,C,K,E,R],[B,C,K,E,R,S],[B,C,K,E,S],[B,C,K,G],[B,C,K,G,O],[B,C,K,G,O,M],[B,C,K,G,O,M,Q],[B,C,K,G,O,M,Q,R],[B,C,K,G,O,M,Q,R,S],[B,C,K,G,O,M,Q,S],[B,C,K,G,O,M,R],[B,C,K,G,O,M,R,S],[B,C,K,G,O,M,S],[B,C,K,G,O,Q],[B,C,K,G,O,Q,R],[B,C,K,G,O,Q,R,S],[B,C,K,G,O,Q,S],[B,C,K,G,O,R],[B,C,K,G,O,R,S],[B,C,K,G,O,S],[B,C,K,G,M],[B,C,K,G,M,R],[B,C,K,G,M,R,S],[B,C,K,G,M,S],[B,C,K,G,R],[B,C,K,G,R,S],[B,C,K,G,S],[B,C,K,O],[B,C,K,O,M],[B,C,K,O,M,Q],[B,C,K,O,M,Q,R],[B,C,K,O,M,Q,R,S],[B,C,K,O,M,Q,S],[B,C,K,O,M,R],[B,C,K,O,M,R,S],[B,C,K,O,M,S],[B,C,K,O,Q],[B,C,K,O,Q,R],[B,C,K,O,Q,R,S],[B,C,K,O,Q,S],[B,C,K,O,R],[B,C,K,O,R,S],[B,C,K,O,S],[B,C,K,M],[B,C,K,M,R],[B,C,K,M,R,S],[B,C,K,M,S],[B,C,K,R],[B,C,K,R,S],[B,C,K,S],[B,C,L],[B,C,L,G],[B,C,L,G,R],[B,C,L,G,R,S],[B,C,L,G,S],[B,C,L,R],[B,C,L,R,S],[B,C,L,S],[B,C,G],[B,C,G,R],[B,C,G,R,S],[B,C,G,S],[B,C,R],[B,C,R,S],[B,C,S],[B,D,K,L,E,G,O,M,Q],[B,D,K,L,E,G,O,M,Q,R],[B,D,K,L,E,G,O,M,Q,R,S],[B,D,K,L,E,G,O,M,Q,S],[B,D,K,L,E,G,O,Q],[B,D,K,L,E,G,O,Q,R],[B,D,K,L,E,G,O,Q,R,S],[B,D,K,L,E,G,O,Q,S],[B,D,K,L,E,O,M,Q],[B,D,K,L,E,O,M,Q,R],[B,D,K,L,E,O,M,Q,R,S],[B,D,K,L,E,O,M,Q,S],[B,D,K,L,E,O,Q],[B,D,K,L,E,O,Q,R],[B,D,K,L,E,O,Q,R,S],[B,D,K,L,E,O,Q,S],[B,D,K,L,G,O,M,Q],[B,D,K,L,G,O,M,Q,R],[B,D,K,L,G,O,M,Q,R,S],[B,D,K,L,G,O,M,Q,S],[B,D,K,L,G,O,Q],[B,D,K,L,G,O,Q,R],[B,D,K,L,G,O,Q,R,S],[B,D,K,L,G,O,Q,S],[B,D,K,L,O,M,Q],[B,D,K,L,O,M,Q,R],[B,D,K,L,O,M,Q,R,S],[B,D,K,L,O,M,Q,S],[B,D,K,L,O,Q],[B,D,K,L,O,Q,R],[B,D,K,L,O,Q,R,S],[B,D,K,L,O,Q,S],[B,D,K,E,G,O,M,Q],[B,D,K,E,G,O,M,Q,R],[B,D,K,E,G,O,M,Q,R,S],[B,D,K,E,G,O,M,Q,S],[B,D,K,E,G,O,Q],[B,D,K,E,G,O,Q,R],[B,D,K,E,G,O,Q,R,S],[B,D,K,E,G,O,Q,S],[B,D,K,E,O,M,Q],[B,D,K,E,O,M,Q,R],[B,D,K,E,O,M,Q,R,S],[B,D,K,E,O,M,Q,S],[B,D,K,E,O,Q],[B,D,K,E,O,Q,R],[B,D,K,E,O,Q,R,S],[B,D,K,E,O,Q,S],[B,D,K,G,O,M,Q],[B,D,K,G,O,M,Q,R],[B,D,K,G,O,M,Q,R,S],[B,D,K,G,O,M,Q,S],[B,D,K,G,O,Q],[B,D,K,G,O,Q,R],[B,D,K,G,O,Q,R,S],[B,D,K,G,O,Q,S],[B,D,K,O,M,Q],[B,D,K,O,M,Q,R],[B,D,K,O,M,Q,R,S],[B,D,K,O,M,Q,S],[B,D,K,O,Q],[B,D,K,O,Q,R],[B,D,K,O,Q,R,S],[B,D,K,O,Q,S],[B,K,L,E,G,O,M,Q],[B,K,L,E,G,O,M,Q,R],[B,K,L,E,G,O,M,Q,R,S],[B,K,L,E,G,O,M,Q,S],[B,K,L,E,G,O,Q],[B,K,L,E,G,O,Q,R],[B,K,L,E,G,O,Q,R,S],[B,K,L,E,G,O,Q,S],[B,K,L,E,O,M,Q],[B,K,L,E,O,M,Q,R],[B,K,L,E,O,M,Q,R,S],[B,K,L,E,O,M,Q,S],[B,K,L,E,O,Q],[B,K,L,E,O,Q,R],[B,K,L,E,O,Q,R,S],[B,K,L,E,O,Q,S],[B,K,L,G,O,M,Q],[B,K,L,G,O,M,Q,R],[B,K,L,G,O,M,Q,R,S],[B,K,L,G,O,M,Q,S],[B,K,L,G,O,Q],[B,K,L,G,O,Q,R],[B,K,L,G,O,Q,R,S],[B,K,L,G,O,Q,S],[B,K,L,O,M,Q],[B,K,L,O,M,Q,R],[B,K,L,O,M,Q,R,S],[B,K,L,O,M,Q,S],[B,K,L,O,Q],[B,K,L,O,Q,R],[B,K,L,O,Q,R,S],[B,K,L,O,Q,S],[B,K,E,G,O,M,Q],[B,K,E,G,O,M,Q,R],[B,K,E,G,O,M,Q,R,S],[B,K,E,G,O,M,Q,S],[B,K,E,G,O,Q],[B,K,E,G,O,Q,R],[B,K,E,G,O,Q,R,S],[B,K,E,G,O,Q,S],[B,K,E,O,M,Q],[B,K,E,O,M,Q,R],[B,K,E,O,M,Q,R,S],[B,K,E,O,M,Q,S],[B,K,E,O,Q],[B,K,E,O,Q,R],[B,K,E,O,Q,R,S],[B,K,E,O,Q,S],[B,K,G,O,M,Q],[B,K,G,O,M,Q,R],[B,K,G,O,M,Q,R,S],[B,K,G,O,M,Q,S],[B,K,G,O,Q],[B,K,G,O,Q,R],[B,K,G,O,Q,R,S],[B,K,G,O,Q,S],[B,K,O,M,Q],[B,K,O,M,Q,R],[B,K,O,M,Q,R,S],[B,K,O,M,Q,S],[B,K,O,Q],[B,K,O,Q,R],[B,K,O,Q,R,S],[B,K,O,Q,S],[B,L],[B,L,G],[B,L,G,R],[B,L,G,R,S],[B,L,G,S],[B,L,R],[B,L,R,S],[B,L,S],[B,G],[B,G,R],[B,G,R,S],[B,G,S],[B,R],[B,R,S],[B,S],[C],[C,D,K],[C,D,K,L],[C,D,K,L,E],[C,D,K,L,E,G],[C,D,K,L,E,G,O],[C,D,K,L,E,G,O,M],[C,D,K,L,E,G,O,M,Q],[C,D,K,L,E,G,O,M,Q,R],[C,D,K,L,E,G,O,M,Q,R,S],[C,D,K,L,E,G,O,M,Q,S],[C,D,K,L,E,G,O,M,R],[C,D,K,L,E,G,O,M,R,S],[C,D,K,L,E,G,O,M,S],[C,D,K,L,E,G,O,Q],[C,D,K,L,E,G,O,Q,R],[C,D,K,L,E,G,O,Q,R,S],[C,D,K,L,E,G,O,Q,S],[C,D,K,L,E,G,O,R],[C,D,K,L,E,G,O,R,S],[C,D,K,L,E,G,O,S],[C,D,K,L,E,G,M],[C,D,K,L,E,G,M,R],[C,D,K,L,E,G,M,R,S],[C,D,K,L,E,G,M,S],[C,D,K,L,E,G,R],[C,D,K,L,E,G,R,S],[C,D,K,L,E,G,S],[C,D,K,L,E,O],[C,D,K,L,E,O,M],[C,D,K,L,E,O,M,Q],[C,D,K,L,E,O,M,Q,R],[C,D,K,L,E,O,M,Q,R,S],[C,D,K,L,E,O,M,Q,S],[C,D,K,L,E,O,M,R],[C,D,K,L,E,O,M,R,S],[C,D,K,L,E,O,M,S],[C,D,K,L,E,O,Q],[C,D,K,L,E,O,Q,R],[C,D,K,L,E,O,Q,R,S],[C,D,K,L,E,O,Q,S],[C,D,K,L,E,O,R],[C,D,K,L,E,O,R,S],[C,D,K,L,E,O,S],[C,D,K,L,E,M],[C,D,K,L,E,M,R],[C,D,K,L,E,M,R,S],[C,D,K,L,E,M,S],[C,D,K,L,E,R],[C,D,K,L,E,R,S],[C,D,K,L,E,S],[C,D,K,L,G],[C,D,K,L,G,O],[C,D,K,L,G,O,M],[C,D,K,L,G,O,M,Q],[C,D,K,L,G,O,M,Q,R],[C,D,K,L,G,O,M,Q,R,S],[C,D,K,L,G,O,M,Q,S],[C,D,K,L,G,O,M,R],[C,D,K,L,G,O,M,R,S],[C,D,K,L,G,O,M,S],[C,D,K,L,G,O,Q],[C,D,K,L,G,O,Q,R],[C,D,K,L,G,O,Q,R,S],[C,D,K,L,G,O,Q,S],[C,D,K,L,G,O,R],[C,D,K,L,G,O,R,S],[C,D,K,L,G,O,S],[C,D,K,L,G,M],[C,D,K,L,G,M,R],[C,D,K,L,G,M,R,S],[C,D,K,L,G,M,S],[C,D,K,L,G,R],[C,D,K,L,G,R,S],[C,D,K,L,G,S],[C,D,K,L,O],[C,D,K,L,O,M],[C,D,K,L,O,M,Q],[C,D,K,L,O,M,Q,R],[C,D,K,L,O,M,Q,R,S],[C,D,K,L,O,M,Q,S],[C,D,K,L,O,M,R],[C,D,K,L,O,M,R,S],[C,D,K,L,O,M,S],[C,D,K,L,O,Q],[C,D,K,L,O,Q,R],[C,D,K,L,O,Q,R,S],[C,D,K,L,O,Q,S],[C,D,K,L,O,R],[C,D,K,L,O,R,S],[C,D,K,L,O,S],[C,D,K,L,M],[C,D,K,L,M,R],[C,D,K,L,M,R,S],[C,D,K,L,M,S],[C,D,K,L,R],[C,D,K,L,R,S],[C,D,K,L,S],[C,D,K,E],[C,D,K,E,G],[C,D,K,E,G,O],[C,D,K,E,G,O,M],[C,D,K,E,G,O,M,Q],[C,D,K,E,G,O,M,Q,R],[C,D,K,E,G,O,M,Q,R,S],[C,D,K,E,G,O,M,Q,S],[C,D,K,E,G,O,M,R],[C,D,K,E,G,O,M,R,S],[C,D,K,E,G,O,M,S],[C,D,K,E,G,O,Q],[C,D,K,E,G,O,Q,R],[C,D,K,E,G,O,Q,R,S],[C,D,K,E,G,O,Q,S],[C,D,K,E,G,O,R],[C,D,K,E,G,O,R,S],[C,D,K,E,G,O,S],[C,D,K,E,G,M],[C,D,K,E,G,M,R],[C,D,K,E,G,M,R,S],[C,D,K,E,G,M,S],[C,D,K,E,G,R],[C,D,K,E,G,R,S],[C,D,K,E,G,S],[C,D,K,E,O],[C,D,K,E,O,M],[C,D,K,E,O,M,Q],[C,D,K,E,O,M,Q,R],[C,D,K,E,O,M,Q,R,S],[C,D,K,E,O,M,Q,S],[C,D,K,E,O,M,R],[C,D,K,E,O,M,R,S],[C,D,K,E,O,M,S],[C,D,K,E,O,Q],[C,D,K,E,O,Q,R],[C,D,K,E,O,Q,R,S],[C,D,K,E,O,Q,S],[C,D,K,E,O,R],[C,D,K,E,O,R,S],[C,D,K,E,O,S],[C,D,K,E,M],[C,D,K,E,M,R],[C,D,K,E,M,R,S],[C,D,K,E,M,S],[C,D,K,E,R],[C,D,K,E,R,S],[C,D,K,E,S],[C,D,K,G],[C,D,K,G,O],[C,D,K,G,O,M],[C,D,K,G,O,M,Q],[C,D,K,G,O,M,Q,R],[C,D,K,G,O,M,Q,R,S],[C,D,K,G,O,M,Q,S],[C,D,K,G,O,M,R],[C,D,K,G,O,M,R,S],[C,D,K,G,O,M,S],[C,D,K,G,O,Q],[C,D,K,G,O,Q,R],[C,D,K,G,O,Q,R,S],[C,D,K,G,O,Q,S],[C,D,K,G,O,R],[C,D,K,G,O,R,S],[C,D,K,G,O,S],[C,D,K,G,M],[C,D,K,G,M,R],[C,D,K,G,M,R,S],[C,D,K,G,M,S],[C,D,K,G,R],[C,D,K,G,R,S],[C,D,K,G,S],[C,D,K,O],[C,D,K,O,M],[C,D,K,O,M,Q],[C,D,K,O,M,Q,R],[C,D,K,O,M,Q,R,S],[C,D,K,O,M,Q,S],[C,D,K,O,M,R],[C,D,K,O,M,R,S],[C,D,K,O,M,S],[C,D,K,O,Q],[C,D,K,O,Q,R],[C,D,K,O,Q,R,S],[C,D,K,O,Q,S],[C,D,K,O,R],[C,D,K,O,R,S],[C,D,K,O,S],[C,D,K,M],[C,D,K,M,R],[C,D,K,M,R,S],[C,D,K,M,S],[C,D,K,R],[C,D,K,R,S],[C,D,K,S],[C,K],[C,K,L],[C,K,L,E],[C,K,L,E,G],[C,K,L,E,G,O],[C,K,L,E,G,O,M],[C,K,L,E,G,O,M,Q],[C,K,L,E,G,O,M,Q,R],[C,K,L,E,G,O,M,Q,R,S],[C,K,L,E,G,O,M,Q,S],[C,K,L,E,G,O,M,R],[C,K,L,E,G,O,M,R,S],[C,K,L,E,G,O,M,S],[C,K,L,E,G,O,Q],[C,K,L,E,G,O,Q,R],[C,K,L,E,G,O,Q,R,S],[C,K,L,E,G,O,Q,S],[C,K,L,E,G,O,R],[C,K,L,E,G,O,R,S],[C,K,L,E,G,O,S],[C,K,L,E,G,M],[C,K,L,E,G,M,R],[C,K,L,E,G,M,R,S],[C,K,L,E,G,M,S],[C,K,L,E,G,R],[C,K,L,E,G,R,S],[C,K,L,E,G,S],[C,K,L,E,O],[C,K,L,E,O,M],[C,K,L,E,O,M,Q],[C,K,L,E,O,M,Q,R],[C,K,L,E,O,M,Q,R,S],[C,K,L,E,O,M,Q,S],[C,K,L,E,O,M,R],[C,K,L,E,O,M,R,S],[C,K,L,E,O,M,S],[C,K,L,E,O,Q],[C,K,L,E,O,Q,R],[C,K,L,E,O,Q,R,S],[C,K,L,E,O,Q,S],[C,K,L,E,O,R],[C,K,L,E,O,R,S],[C,K,L,E,O,S],[C,K,L,E,M],[C,K,L,E,M,R],[C,K,L,E,M,R,S],[C,K,L,E,M,S],[C,K,L,E,R],[C,K,L,E,R,S],[C,K,L,E,S],[C,K,L,G],[C,K,L,G,O],[C,K,L,G,O,M],[C,K,L,G,O,M,Q],[C,K,L,G,O,M,Q,R],[C,K,L,G,O,M,Q,R,S],[C,K,L,G,O,M,Q,S],[C,K,L,G,O,M,R],[C,K,L,G,O,M,R,S],[C,K,L,G,O,M,S],[C,K,L,G,O,Q],[C,K,L,G,O,Q,R],[C,K,L,G,O,Q,R,S],[C,K,L,G,O,Q,S],[C,K,L,G,O,R],[C,K,L,G,O,R,S],[C,K,L,G,O,S],[C,K,L,G,M],[C,K,L,G,M,R],[C,K,L,G,M,R,S],[C,K,L,G,M,S],[C,K,L,G,R],[C,K,L,G,R,S],[C,K,L,G,S],[C,K,L,O],[C,K,L,O,M],[C,K,L,O,M,Q],[C,K,L,O,M,Q,R],[C,K,L,O,M,Q,R,S],[C,K,L,O,M,Q,S],[C,K,L,O,M,R],[C,K,L,O,M,R,S],[C,K,L,O,M,S],[C,K,L,O,Q],[C,K,L,O,Q,R],[C,K,L,O,Q,R,S],[C,K,L,O,Q,S],[C,K,L,O,R],[C,K,L,O,R,S],[C,K,L,O,S],[C,K,L,M],[C,K,L,M,R],[C,K,L,M,R,S],[C,K,L,M,S],[C,K,L,R],[C,K,L,R,S],[C,K,L,S],[C,K,E],[C,K,E,G],[C,K,E,G,O],[C,K,E,G,O,M],[C,K,E,G,O,M,Q],[C,K,E,G,O,M,Q,R],[C,K,E,G,O,M,Q,R,S],[C,K,E,G,O,M,Q,S],[C,K,E,G,O,M,R],[C,K,E,G,O,M,R,S],[C,K,E,G,O,M,S],[C,K,E,G,O,Q],[C,K,E,G,O,Q,R],[C,K,E,G,O,Q,R,S],[C,K,E,G,O,Q,S],[C,K,E,G,O,R],[C,K,E,G,O,R,S],[C,K,E,G,O,S],[C,K,E,G,M],[C,K,E,G,M,R],[C,K,E,G,M,R,S],[C,K,E,G,M,S],[C,K,E,G,R],[C,K,E,G,R,S],[C,K,E,G,S],[C,K,E,O],[C,K,E,O,M],[C,K,E,O,M,Q],[C,K,E,O,M,Q,R],[C,K,E,O,M,Q,R,S],[C,K,E,O,M,Q,S],[C,K,E,O,M,R],[C,K,E,O,M,R,S],[C,K,E,O,M,S],[C,K,E,O,Q],[C,K,E,O,Q,R],[C,K,E,O,Q,R,S],[C,K,E,O,Q,S],[C,K,E,O,R],[C,K,E,O,R,S],[C,K,E,O,S],[C,K,E,M],[C,K,E,M,R],[C,K,E,M,R,S],[C,K,E,M,S],[C,K,E,R],[C,K,E,R,S],[C,K,E,S],[C,K,G],[C,K,G,O],[C,K,G,O,M],[C,K,G,O,M,Q],[C,K,G,O,M,Q,R],[C,K,G,O,M,Q,R,S],[C,K,G,O,M,Q,S],[C,K,G,O,M,R],[C,K,G,O,M,R,S],[C,K,G,O,M,S],[C,K,G,O,Q],[C,K,G,O,Q,R],[C,K,G,O,Q,R,S],[C,K,G,O,Q,S],[C,K,G,O,R],[C,K,G,O,R,S],[C,K,G,O,S],[C,K,G,M],[C,K,G,M,R],[C,K,G,M,R,S],[C,K,G,M,S],[C,K,G,R],[C,K,G,R,S],[C,K,G,S],[C,K,O],[C,K,O,M],[C,K,O,M,Q],[C,K,O,M,Q,R],[C,K,O,M,Q,R,S],[C,K,O,M,Q,S],[C,K,O,M,R],[C,K,O,M,R,S],[C,K,O,M,S],[C,K,O,Q],[C,K,O,Q,R],[C,K,O,Q,R,S],[C,K,O,Q,S],[C,K,O,R],[C,K,O,R,S],[C,K,O,S],[C,K,M],[C,K,M,R],[C,K,M,R,S],[C,K,M,S],[C,K,R],[C,K,R,S],[C,K,S],[C,L],[C,L,G],[C,L,G,R],[C,L,G,R,S],[C,L,G,S],[C,L,R],[C,L,R,S],[C,L,S],[C,G],[C,G,R],[C,G,R,S],[C,G,S],[C,R],[C,R,S],[C,S],[D],[D,K],[D,K,L,E,G,O,M,Q],[D,K,L,E,G,O,M,Q,R],[D,K,L,E,G,O,M,Q,R,S],[D,K,L,E,G,O,M,Q,S],[D,K,L,E,G,O,Q],[D,K,L,E,G,O,Q,R],[D,K,L,E,G,O,Q,R,S],[D,K,L,E,G,O,Q,S],[D,K,L,E,O,M,Q],[D,K,L,E,O,M,Q,R],[D,K,L,E,O,M,Q,R,S],[D,K,L,E,O,M,Q,S],[D,K,L,E,O,Q],[D,K,L,E,O,Q,R],[D,K,L,E,O,Q,R,S],[D,K,L,E,O,Q,S],[D,K,L,G,O,M,Q],[D,K,L,G,O,M,Q,R],[D,K,L,G,O,M,Q,R,S],[D,K,L,G,O,M,Q,S],[D,K,L,G,O,Q],[D,K,L,G,O,Q,R],[D,K,L,G,O,Q,R,S],[D,K,L,G,O,Q,S],[D,K,L,O,M,Q],[D,K,L,O,M,Q,R],[D,K,L,O,M,Q,R,S],[D,K,L,O,M,Q,S],[D,K,L,O,Q],[D,K,L,O,Q,R],[D,K,L,O,Q,R,S],[D,K,L,O,Q,S],[D,K,E],[D,K,E,G,O,M,Q],[D,K,E,G,O,M,Q,R],[D,K,E,G,O,M,Q,R,S],[D,K,E,G,O,M,Q,S],[D,K,E,G,O,Q],[D,K,E,G,O,Q,R],[D,K,E,G,O,Q,R,S],[D,K,E,G,O,Q,S],[D,K,E,O],[D,K,E,O,M],[D,K,E,O,M,Q],[D,K,E,O,M,Q,R],[D,K,E,O,M,Q,R,S],[D,K,E,O,M,Q,S],[D,K,E,O,Q],[D,K,E,O,Q,R],[D,K,E,O,Q,R,S],[D,K,E,O,Q,S],[D,K,E,M],[D,K,G,O,M,Q],[D,K,G,O,M,Q,R],[D,K,G,O,M,Q,R,S],[D,K,G,O,M,Q,S],[D,K,G,O,Q],[D,K,G,O,Q,R],[D,K,G,O,Q,R,S],[D,K,G,O,Q,S],[D,K,O],[D,K,O,M],[D,K,O,M,Q],[D,K,O,M,Q,R],[D,K,O,M,Q,R,S],[D,K,O,M,Q,S],[D,K,O,Q],[D,K,O,Q,R],[D,K,O,Q,R,S],[D,K,O,Q,S],[D,K,M],[D,E],[H],[K],[K,L,E,G,O,M,Q],[K,L,E,G,O,M,Q,R],[K,L,E,G,O,M,Q,R,S],[K,L,E,G,O,M,Q,S],[K,L,E,G,O,Q],[K,L,E,G,O,Q,R],[K,L,E,G,O,Q,R,S],[K,L,E,G,O,Q,S],[K,L,E,O,M,Q],[K,L,E,O,M,Q,R],[K,L,E,O,M,Q,R,S],[K,L,E,O,M,Q,S],[K,L,E,O,Q],[K,L,E,O,Q,R],[K,L,E,O,Q,R,S],[K,L,E,O,Q,S],[K,L,G,O,M,Q],[K,L,G,O,M,Q,R],[K,L,G,O,M,Q,R,S],[K,L,G,O,M,Q,S],[K,L,G,O,Q],[K,L,G,O,Q,R],[K,L,G,O,Q,R,S],[K,L,G,O,Q,S],[K,L,O,M,Q],[K,L,O,M,Q,R],[K,L,O,M,Q,R,S],[K,L,O,M,Q,S],[K,L,O,Q],[K,L,O,Q,R],[K,L,O,Q,R,S],[K,L,O,Q,S],[K,E],[K,E,G,O,M,Q],[K,E,G,O,M,Q,R],[K,E,G,O,M,Q,R,S],[K,E,G,O,M,Q,S],[K,E,G,O,Q],[K,E,G,O,Q,R],[K,E,G,O,Q,R,S],[K,E,G,O,Q,S],[K,E,O],[K,E,O,M],[K,E,O,M,Q],[K,E,O,M,Q,R],[K,E,O,M,Q,R,S],[K,E,O,M,Q,S],[K,E,O,Q],[K,E,O,Q,R],[K,E,O,Q,R,S],[K,E,O,Q,S],[K,E,M],[K,G,O,M,Q],[K,G,O,M,Q,R],[K,G,O,M,Q,R,S],[K,G,O,M,Q,S],[K,G,O,Q],[K,G,O,Q,R],[K,G,O,Q,R,S],[K,G,O,Q,S],[K,O],[K,O,M],[K,O,M,Q],[K,O,M,Q,R],[K,O,M,Q,R,S],[K,O,M,Q,S],[K,O,Q],[K,O,Q,R],[K,O,Q,R,S],[K,O,Q,S],[K,M],[L],[L,G],[L,G,R],[G],[G,R],[S]]),ground([I,J,F,N,P]),linear(H);mshare([[B],[B,D,K,L,E,G,O,M,Q],[B,D,K,L,E,G,O,M,Q,R],[B,D,K,L,E,G,O,M,Q,R,S],[B,D,K,L,E,G,O,M,Q,S],[B,D,K,L,E,G,O,Q],[B,D,K,L,E,G,O,Q,R],[B,D,K,L,E,G,O,Q,R,S],[B,D,K,L,E,G,O,Q,S],[B,D,K,L,E,O,M,Q],[B,D,K,L,E,O,M,Q,R],[B,D,K,L,E,O,M,Q,R,S],[B,D,K,L,E,O,M,Q,S],[B,D,K,L,E,O,Q],[B,D,K,L,E,O,Q,R],[B,D,K,L,E,O,Q,R,S],[B,D,K,L,E,O,Q,S],[B,D,K,L,G,O,M,Q],[B,D,K,L,G,O,M,Q,R],[B,D,K,L,G,O,M,Q,R,S],[B,D,K,L,G,O,M,Q,S],[B,D,K,L,G,O,Q],[B,D,K,L,G,O,Q,R],[B,D,K,L,G,O,Q,R,S],[B,D,K,L,G,O,Q,S],[B,D,K,L,O,M,Q],[B,D,K,L,O,M,Q,R],[B,D,K,L,O,M,Q,R,S],[B,D,K,L,O,M,Q,S],[B,D,K,L,O,Q],[B,D,K,L,O,Q,R],[B,D,K,L,O,Q,R,S],[B,D,K,L,O,Q,S],[B,D,K,E,G,O,M,Q],[B,D,K,E,G,O,M,Q,R],[B,D,K,E,G,O,M,Q,R,S],[B,D,K,E,G,O,M,Q,S],[B,D,K,E,G,O,Q],[B,D,K,E,G,O,Q,R],[B,D,K,E,G,O,Q,R,S],[B,D,K,E,G,O,Q,S],[B,D,K,E,O,M,Q],[B,D,K,E,O,M,Q,R],[B,D,K,E,O,M,Q,R,S],[B,D,K,E,O,M,Q,S],[B,D,K,E,O,Q],[B,D,K,E,O,Q,R],[B,D,K,E,O,Q,R,S],[B,D,K,E,O,Q,S],[B,D,K,G,O,M,Q],[B,D,K,G,O,M,Q,R],[B,D,K,G,O,M,Q,R,S],[B,D,K,G,O,M,Q,S],[B,D,K,G,O,Q],[B,D,K,G,O,Q,R],[B,D,K,G,O,Q,R,S],[B,D,K,G,O,Q,S],[B,D,K,O,M,Q],[B,D,K,O,M,Q,R],[B,D,K,O,M,Q,R,S],[B,D,K,O,M,Q,S],[B,D,K,O,Q],[B,D,K,O,Q,R],[B,D,K,O,Q,R,S],[B,D,K,O,Q,S],[B,K,L,E,G,O,M,Q],[B,K,L,E,G,O,M,Q,R],[B,K,L,E,G,O,M,Q,R,S],[B,K,L,E,G,O,M,Q,S],[B,K,L,E,G,O,Q],[B,K,L,E,G,O,Q,R],[B,K,L,E,G,O,Q,R,S],[B,K,L,E,G,O,Q,S],[B,K,L,E,O,M,Q],[B,K,L,E,O,M,Q,R],[B,K,L,E,O,M,Q,R,S],[B,K,L,E,O,M,Q,S],[B,K,L,E,O,Q],[B,K,L,E,O,Q,R],[B,K,L,E,O,Q,R,S],[B,K,L,E,O,Q,S],[B,K,L,G,O,M,Q],[B,K,L,G,O,M,Q,R],[B,K,L,G,O,M,Q,R,S],[B,K,L,G,O,M,Q,S],[B,K,L,G,O,Q],[B,K,L,G,O,Q,R],[B,K,L,G,O,Q,R,S],[B,K,L,G,O,Q,S],[B,K,L,O,M,Q],[B,K,L,O,M,Q,R],[B,K,L,O,M,Q,R,S],[B,K,L,O,M,Q,S],[B,K,L,O,Q],[B,K,L,O,Q,R],[B,K,L,O,Q,R,S],[B,K,L,O,Q,S],[B,K,E,G,O,M,Q],[B,K,E,G,O,M,Q,R],[B,K,E,G,O,M,Q,R,S],[B,K,E,G,O,M,Q,S],[B,K,E,G,O,Q],[B,K,E,G,O,Q,R],[B,K,E,G,O,Q,R,S],[B,K,E,G,O,Q,S],[B,K,E,O,M,Q],[B,K,E,O,M,Q,R],[B,K,E,O,M,Q,R,S],[B,K,E,O,M,Q,S],[B,K,E,O,Q],[B,K,E,O,Q,R],[B,K,E,O,Q,R,S],[B,K,E,O,Q,S],[B,K,G,O,M,Q],[B,K,G,O,M,Q,R],[B,K,G,O,M,Q,R,S],[B,K,G,O,M,Q,S],[B,K,G,O,Q],[B,K,G,O,Q,R],[B,K,G,O,Q,R,S],[B,K,G,O,Q,S],[B,K,O,M,Q],[B,K,O,M,Q,R],[B,K,O,M,Q,R,S],[B,K,O,M,Q,S],[B,K,O,Q],[B,K,O,Q,R],[B,K,O,Q,R,S],[B,K,O,Q,S],[B,L],[B,L,G],[B,L,G,R],[B,L,G,R,S],[B,L,G,S],[B,L,R],[B,L,R,S],[B,L,S],[B,G],[B,G,R],[B,G,R,S],[B,G,S],[B,R],[B,R,S],[B,S],[D],[D,K],[D,K,L,E,G,O,M,Q],[D,K,L,E,G,O,M,Q,R],[D,K,L,E,G,O,M,Q,R,S],[D,K,L,E,G,O,M,Q,S],[D,K,L,E,G,O,Q],[D,K,L,E,G,O,Q,R],[D,K,L,E,G,O,Q,R,S],[D,K,L,E,G,O,Q,S],[D,K,L,E,O,M,Q],[D,K,L,E,O,M,Q,R],[D,K,L,E,O,M,Q,R,S],[D,K,L,E,O,M,Q,S],[D,K,L,E,O,Q],[D,K,L,E,O,Q,R],[D,K,L,E,O,Q,R,S],[D,K,L,E,O,Q,S],[D,K,L,G,O,M,Q],[D,K,L,G,O,M,Q,R],[D,K,L,G,O,M,Q,R,S],[D,K,L,G,O,M,Q,S],[D,K,L,G,O,Q],[D,K,L,G,O,Q,R],[D,K,L,G,O,Q,R,S],[D,K,L,G,O,Q,S],[D,K,L,O,M,Q],[D,K,L,O,M,Q,R],[D,K,L,O,M,Q,R,S],[D,K,L,O,M,Q,S],[D,K,L,O,Q],[D,K,L,O,Q,R],[D,K,L,O,Q,R,S],[D,K,L,O,Q,S],[D,K,E],[D,K,E,G,O,M,Q],[D,K,E,G,O,M,Q,R],[D,K,E,G,O,M,Q,R,S],[D,K,E,G,O,M,Q,S],[D,K,E,G,O,Q],[D,K,E,G,O,Q,R],[D,K,E,G,O,Q,R,S],[D,K,E,G,O,Q,S],[D,K,E,O],[D,K,E,O,M],[D,K,E,O,M,Q],[D,K,E,O,M,Q,R],[D,K,E,O,M,Q,R,S],[D,K,E,O,M,Q,S],[D,K,E,O,Q],[D,K,E,O,Q,R],[D,K,E,O,Q,R,S],[D,K,E,O,Q,S],[D,K,E,M],[D,K,G,O,M,Q],[D,K,G,O,M,Q,R],[D,K,G,O,M,Q,R,S],[D,K,G,O,M,Q,S],[D,K,G,O,Q],[D,K,G,O,Q,R],[D,K,G,O,Q,R,S],[D,K,G,O,Q,S],[D,K,O],[D,K,O,M],[D,K,O,M,Q],[D,K,O,M,Q,R],[D,K,O,M,Q,R,S],[D,K,O,M,Q,S],[D,K,O,Q],[D,K,O,Q,R],[D,K,O,Q,R,S],[D,K,O,Q,S],[D,K,M],[D,E],[H],[K],[K,L,E,G,O,M,Q],[K,L,E,G,O,M,Q,R],[K,L,E,G,O,M,Q,R,S],[K,L,E,G,O,M,Q,S],[K,L,E,G,O,Q],[K,L,E,G,O,Q,R],[K,L,E,G,O,Q,R,S],[K,L,E,G,O,Q,S],[K,L,E,O,M,Q],[K,L,E,O,M,Q,R],[K,L,E,O,M,Q,R,S],[K,L,E,O,M,Q,S],[K,L,E,O,Q],[K,L,E,O,Q,R],[K,L,E,O,Q,R,S],[K,L,E,O,Q,S],[K,L,G,O,M,Q],[K,L,G,O,M,Q,R],[K,L,G,O,M,Q,R,S],[K,L,G,O,M,Q,S],[K,L,G,O,Q],[K,L,G,O,Q,R],[K,L,G,O,Q,R,S],[K,L,G,O,Q,S],[K,L,O,M,Q],[K,L,O,M,Q,R],[K,L,O,M,Q,R,S],[K,L,O,M,Q,S],[K,L,O,Q],[K,L,O,Q,R],[K,L,O,Q,R,S],[K,L,O,Q,S],[K,E],[K,E,G,O,M,Q],[K,E,G,O,M,Q,R],[K,E,G,O,M,Q,R,S],[K,E,G,O,M,Q,S],[K,E,G,O,Q],[K,E,G,O,Q,R],[K,E,G,O,Q,R,S],[K,E,G,O,Q,S],[K,E,O],[K,E,O,M],[K,E,O,M,Q],[K,E,O,M,Q,R],[K,E,O,M,Q,R,S],[K,E,O,M,Q,S],[K,E,O,Q],[K,E,O,Q,R],[K,E,O,Q,R,S],[K,E,O,Q,S],[K,E,M],[K,G,O,M,Q],[K,G,O,M,Q,R],[K,G,O,M,Q,R,S],[K,G,O,M,Q,S],[K,G,O,Q],[K,G,O,Q,R],[K,G,O,Q,R,S],[K,G,O,Q,S],[K,O],[K,O,M],[K,O,M,Q],[K,O,M,Q,R],[K,O,M,Q,R,S],[K,O,M,Q,S],[K,O,Q],[K,O,Q,R],[K,O,Q,R,S],[K,O,Q,S],[K,M],[L],[L,G],[L,G,R],[G],[G,R],[S]]),ground([C,I,J,F,N,P]),linear(H))).
wh(B,C,D,E,F,G,H,I,J) :-
    true((mshare([[B],[C],[C,I],[D],[E],[F],[H],[I],[J],[K],[L],[M],[N]]),ground([G]),linear(B),linear(D),linear(E),linear(F),linear(H),linear(J),linear(K),linear(L),linear(M),linear(N);mshare([[B],[D],[E],[F],[H],[I],[J],[K],[L],[M],[N]]),ground([C,G]),linear(B),linear(D),linear(E),linear(F),linear(H),linear(J),linear(K),linear(L),linear(M),linear(N))),
    whose(B,C,G,K,I,L),
    true((mshare([[B,L],[C,I,L],[C,L],[D],[E],[F],[H],[I],[I,L],[J],[M],[N]]),ground([G,K]),linear(B),linear(D),linear(E),linear(F),linear(H),linear(J),linear(M),linear(N);mshare([[B,L],[D],[E],[F],[H],[I],[I,L],[J],[M],[N]]),ground([C,G,K]),linear(B),linear(D),linear(E),linear(F),linear(H),linear(J),linear(M),linear(N))),
    s_all(M),
    true((mshare([[B,L],[C,I,L],[C,L],[D],[E],[F],[H],[I],[I,L],[J],[N]]),ground([G,K,M]),linear(B),linear(D),linear(E),linear(F),linear(H),linear(J),linear(N);mshare([[B,L],[D],[E],[F],[H],[I],[I,L],[J],[N]]),ground([C,G,K,M]),linear(B),linear(D),linear(E),linear(F),linear(H),linear(J),linear(N))),
    np(D,E,F,def,subj,M,N,K,H,L,J),
    true((mshare([[B,C,D,E,F,I,J,L],[B,C,D,E,F,I,J,L,N],[B,C,D,E,F,I,L],[B,C,D,E,F,I,L,N],[B,C,D,E,F,J,L],[B,C,D,E,F,J,L,N],[B,C,D,E,F,L],[B,C,D,E,F,L,N],[B,C,D,E,I,J,L],[B,C,D,E,I,J,L,N],[B,C,D,E,I,L],[B,C,D,E,I,L,N],[B,C,D,E,J,L],[B,C,D,E,J,L,N],[B,C,D,E,L],[B,C,D,E,L,N],[B,C,D,F,I,J,L],[B,C,D,F,I,J,L,N],[B,C,D,F,I,L],[B,C,D,F,I,L,N],[B,C,D,F,J,L],[B,C,D,F,J,L,N],[B,C,D,F,L],[B,C,D,F,L,N],[B,C,D,I,J,L],[B,C,D,I,J,L,N],[B,C,D,I,L],[B,C,D,I,L,N],[B,C,D,J,L],[B,C,D,J,L,N],[B,C,D,L],[B,C,D,L,N],[B,C,E,F,I,J,L],[B,C,E,F,I,J,L,N],[B,C,E,F,I,L],[B,C,E,F,I,L,N],[B,C,E,F,J,L],[B,C,E,F,J,L,N],[B,C,E,F,L],[B,C,E,F,L,N],[B,C,E,I,J,L],[B,C,E,I,J,L,N],[B,C,E,I,L],[B,C,E,I,L,N],[B,C,E,J,L],[B,C,E,J,L,N],[B,C,E,L],[B,C,E,L,N],[B,C,F,I,J,L],[B,C,F,I,J,L,N],[B,C,F,I,L],[B,C,F,I,L,N],[B,C,F,J,L],[B,C,F,J,L,N],[B,C,F,L],[B,C,F,L,N],[B,C,I,J,L],[B,C,I,J,L,N],[B,C,I,L],[B,C,I,L,N],[B,C,J,L],[B,C,J,L,N],[B,C,L],[B,C,L,N],[B,D,E,F,I,J,L],[B,D,E,F,I,J,L,N],[B,D,E,F,I,L],[B,D,E,F,I,L,N],[B,D,E,F,J,L],[B,D,E,F,J,L,N],[B,D,E,F,L],[B,D,E,F,L,N],[B,D,E,I,J,L],[B,D,E,I,J,L,N],[B,D,E,I,L],[B,D,E,I,L,N],[B,D,E,J,L],[B,D,E,J,L,N],[B,D,E,L],[B,D,E,L,N],[B,D,F,I,J,L],[B,D,F,I,J,L,N],[B,D,F,I,L],[B,D,F,I,L,N],[B,D,F,J,L],[B,D,F,J,L,N],[B,D,F,L],[B,D,F,L,N],[B,D,I,J,L],[B,D,I,J,L,N],[B,D,I,L],[B,D,I,L,N],[B,D,J,L],[B,D,J,L,N],[B,D,L],[B,D,L,N],[B,E,F,I,J,L],[B,E,F,I,J,L,N],[B,E,F,I,L],[B,E,F,I,L,N],[B,E,F,J,L],[B,E,F,J,L,N],[B,E,F,L],[B,E,F,L,N],[B,E,I,J,L],[B,E,I,J,L,N],[B,E,I,L],[B,E,I,L,N],[B,E,J,L],[B,E,J,L,N],[B,E,L],[B,E,L,N],[B,F,I,J,L],[B,F,I,J,L,N],[B,F,I,L],[B,F,I,L,N],[B,F,J,L],[B,F,J,L,N],[B,F,L],[B,F,L,N],[B,I,J,L],[B,I,J,L,N],[B,I,L],[B,I,L,N],[B,J,L],[B,J,L,N],[B,L],[B,L,N],[C,D,E,F,I,J,L],[C,D,E,F,I,J,L,N],[C,D,E,F,I,L],[C,D,E,F,I,L,N],[C,D,E,F,J,L],[C,D,E,F,J,L,N],[C,D,E,F,L],[C,D,E,F,L,N],[C,D,E,I,J,L],[C,D,E,I,J,L,N],[C,D,E,I,L],[C,D,E,I,L,N],[C,D,E,J,L],[C,D,E,J,L,N],[C,D,E,L],[C,D,E,L,N],[C,D,F,I,J,L],[C,D,F,I,J,L,N],[C,D,F,I,L],[C,D,F,I,L,N],[C,D,F,J,L],[C,D,F,J,L,N],[C,D,F,L],[C,D,F,L,N],[C,D,I,J,L],[C,D,I,J,L,N],[C,D,I,L],[C,D,I,L,N],[C,D,J,L],[C,D,J,L,N],[C,D,L],[C,D,L,N],[C,E,F,I,J,L],[C,E,F,I,J,L,N],[C,E,F,I,L],[C,E,F,I,L,N],[C,E,F,J,L],[C,E,F,J,L,N],[C,E,F,L],[C,E,F,L,N],[C,E,I,J,L],[C,E,I,J,L,N],[C,E,I,L],[C,E,I,L,N],[C,E,J,L],[C,E,J,L,N],[C,E,L],[C,E,L,N],[C,F,I,J,L],[C,F,I,J,L,N],[C,F,I,L],[C,F,I,L,N],[C,F,J,L],[C,F,J,L,N],[C,F,L],[C,F,L,N],[C,I,J,L],[C,I,J,L,N],[C,I,L],[C,I,L,N],[C,J,L],[C,J,L,N],[C,L],[C,L,N],[D],[D,E],[D,E,F,I,J,L],[D,E,F,I,J,L,N],[D,E,F,I,L],[D,E,F,I,L,N],[D,E,I,J,L],[D,E,I,J,L,N],[D,E,I,L],[D,E,I,L,N],[D,E,J],[D,F,I,J,L],[D,F,I,J,L,N],[D,F,I,L],[D,F,I,L,N],[D,I,J,L],[D,I,J,L,N],[D,I,L],[D,I,L,N],[D,J],[E,F,I,J,L],[E,F,I,J,L,N],[E,F,I,L],[E,F,I,L,N],[E,I,J,L],[E,I,J,L,N],[E,I,L],[E,I,L,N],[F],[F,I,J,L],[F,I,J,L,N],[F,I,L],[F,I,L,N],[I],[I,J,L],[I,J,L,N],[I,L],[I,L,N],[J]]),ground([G,H,K,M]);mshare([[B,D,E,F,I,J,L],[B,D,E,F,I,J,L,N],[B,D,E,F,I,L],[B,D,E,F,I,L,N],[B,D,E,F,J,L],[B,D,E,F,J,L,N],[B,D,E,F,L],[B,D,E,F,L,N],[B,D,E,I,J,L],[B,D,E,I,J,L,N],[B,D,E,I,L],[B,D,E,I,L,N],[B,D,E,J,L],[B,D,E,J,L,N],[B,D,E,L],[B,D,E,L,N],[B,D,F,I,J,L],[B,D,F,I,J,L,N],[B,D,F,I,L],[B,D,F,I,L,N],[B,D,F,J,L],[B,D,F,J,L,N],[B,D,F,L],[B,D,F,L,N],[B,D,I,J,L],[B,D,I,J,L,N],[B,D,I,L],[B,D,I,L,N],[B,D,J,L],[B,D,J,L,N],[B,D,L],[B,D,L,N],[B,E,F,I,J,L],[B,E,F,I,J,L,N],[B,E,F,I,L],[B,E,F,I,L,N],[B,E,F,J,L],[B,E,F,J,L,N],[B,E,F,L],[B,E,F,L,N],[B,E,I,J,L],[B,E,I,J,L,N],[B,E,I,L],[B,E,I,L,N],[B,E,J,L],[B,E,J,L,N],[B,E,L],[B,E,L,N],[B,F,I,J,L],[B,F,I,J,L,N],[B,F,I,L],[B,F,I,L,N],[B,F,J,L],[B,F,J,L,N],[B,F,L],[B,F,L,N],[B,I,J,L],[B,I,J,L,N],[B,I,L],[B,I,L,N],[B,J,L],[B,J,L,N],[B,L],[B,L,N],[D],[D,E],[D,E,F,I,J,L],[D,E,F,I,J,L,N],[D,E,F,I,L],[D,E,F,I,L,N],[D,E,I,J,L],[D,E,I,J,L,N],[D,E,I,L],[D,E,I,L,N],[D,E,J],[D,F,I,J,L],[D,F,I,J,L,N],[D,F,I,L],[D,F,I,L,N],[D,I,J,L],[D,I,J,L,N],[D,I,L],[D,I,L,N],[D,J],[E,F,I,J,L],[E,F,I,J,L,N],[E,F,I,L],[E,F,I,L,N],[E,I,J,L],[E,I,J,L,N],[E,I,L],[E,I,L,N],[F],[F,I,J,L],[F,I,J,L,N],[F,I,L],[F,I,L,N],[I],[I,J,L],[I,J,L,N],[I,L],[I,L,N],[J]]),ground([C,G,H,K,M]))).

:- true pred reduced_relative(B,C,D,E,F,G,H,I)
   : ( mshare([[B],[C],[E],[G],[I]]),
       ground([D,F,H]), linear(C), linear(E), linear(G), linear(I) )
   => ( mshare([[B],[B,C],[B,C,I],[B,I],[C],[C,I],[I]]),
        ground([D,E,F,G,H]) ).

:- true pred reduced_relative(B,C,D,E,F,G,H,I)
   : ( mshare([[C],[E],[G],[I]]),
       ground([B,D,F,H]), linear(C), linear(E), linear(G), linear(I) )
   => ( mshare([[C],[C,I],[I]]),
        ground([B,D,E,F,G,H]) ).

:- true pred reduced_relative(B,C,D,E,F,G,H,I)
   : ( mshare([[B],[B,H],[C],[E],[G],[H],[I]]),
       ground([D,F]), linear(C), linear(E), linear(G), linear(I) )
   => ( mshare([[B],[B,C],[B,C,H],[B,C,H,I],[B,C,I],[B,H],[B,H,I],[B,I],[C],[C,H],[C,H,I],[C,I],[H],[H,I],[I]]),
        ground([D,E,F,G]) ).

:- true pred reduced_relative(B,C,D,E,F,G,H,I)
   : ( mshare([[C],[E],[G],[H],[I]]),
       ground([B,D,F]), linear(C), linear(E), linear(G), linear(I) )
   => ( mshare([[C],[C,H],[C,H,I],[C,I],[H],[H,I],[I]]),
        ground([B,D,E,F,G]) ).

reduced_relative(B,C,D,E,F,G,H,I) :-
    true((mshare([[B],[B,H],[C],[E],[G],[H],[I],[J]]),ground([D,F]),linear(C),linear(E),linear(G),linear(I),linear(J);mshare([[B],[C],[E],[G],[I],[J]]),ground([D,F,H]),linear(C),linear(E),linear(G),linear(I),linear(J);mshare([[C],[E],[G],[H],[I],[J]]),ground([B,D,F]),linear(C),linear(E),linear(G),linear(I),linear(J);mshare([[C],[E],[G],[I],[J]]),ground([B,D,F,H]),linear(C),linear(E),linear(G),linear(I),linear(J))),
    is_pred(D),
    true((mshare([[B],[B,H],[C],[E],[G],[H],[I],[J]]),ground([D,F]),linear(C),linear(E),linear(G),linear(I),linear(J);mshare([[B],[C],[E],[G],[I],[J]]),ground([D,F,H]),linear(C),linear(E),linear(G),linear(I),linear(J);mshare([[C],[E],[G],[H],[I],[J]]),ground([B,D,F]),linear(C),linear(E),linear(G),linear(I),linear(J);mshare([[C],[E],[G],[I],[J]]),ground([B,D,F,H]),linear(C),linear(E),linear(G),linear(I),linear(J))),
    reduced_rel_conj(B,J,C,E,F,G,H,I),
    true((mshare([[B],[B,C],[B,C,H],[B,C,H,I],[B,C,I],[B,H],[B,H,I],[B,I],[C],[C,H],[C,H,I],[C,I],[C,J],[H],[H,I],[I],[J]]),ground([D,E,F,G]);mshare([[B],[B,C],[B,C,I],[B,I],[C],[C,I],[C,J],[I],[J]]),ground([D,E,F,G,H]);mshare([[C],[C,H],[C,H,I],[C,I],[C,J],[H],[H,I],[I],[J]]),ground([B,D,E,F,G]);mshare([[C],[C,I],[C,J],[I],[J]]),ground([B,D,E,F,G,H]))).

:- true pred reduced_rel_conj(B,C,D,E,F,G,H,I)
   : ( mshare([[B],[C],[D],[E],[G],[I]]),
       ground([F,H]), linear(C), linear(D), linear(E), linear(G), linear(I) )
   => ( mshare([[B],[B,D],[B,D,I],[B,I],[C],[C,D],[D],[D,I],[I]]),
        ground([E,F,G,H]) ).

:- true pred reduced_rel_conj(B,C,D,E,F,G,H,I)
   : ( mshare([[C],[D],[E],[G],[I]]),
       ground([B,F,H]), linear(C), linear(D), linear(E), linear(G), linear(I) )
   => ( mshare([[C],[C,D],[D],[D,I],[I]]),
        ground([B,E,F,G,H]) ).

:- true pred reduced_rel_conj(B,C,D,E,F,G,H,I)
   : ( mshare([[B],[B,H],[C],[D],[E],[G],[H],[I]]),
       ground([F]), linear(C), linear(D), linear(E), linear(G), linear(I) )
   => ( mshare([[B],[B,D],[B,D,H],[B,D,H,I],[B,D,I],[B,H],[B,H,I],[B,I],[C],[C,D],[D],[D,H],[D,H,I],[D,I],[H],[H,I],[I]]),
        ground([E,F,G]) ).

:- true pred reduced_rel_conj(B,C,D,E,F,G,H,I)
   : ( mshare([[B],[B,H],[C],[D],[E],[G],[H],[I]]),
       ground([F]), linear(D), linear(E), linear(G), linear(I) )
   => ( mshare([[B],[B,D],[B,D,H],[B,D,H,I],[B,D,I],[B,H],[B,H,I],[B,I],[C],[C,D],[D],[D,H],[D,H,I],[D,I],[H],[H,I],[I]]),
        ground([E,F,G]) ).

:- true pred reduced_rel_conj(B,C,D,E,F,G,H,I)
   : ( mshare([[C],[D],[E],[G],[H],[I]]),
       ground([B,F]), linear(C), linear(D), linear(E), linear(G), linear(I) )
   => ( mshare([[C],[C,D],[D],[D,H],[D,H,I],[D,I],[H],[H,I],[I]]),
        ground([B,E,F,G]) ).

:- true pred reduced_rel_conj(B,C,D,E,F,G,H,I)
   : ( mshare([[C],[D],[E],[G],[H],[I]]),
       ground([B,F]), linear(D), linear(E), linear(G), linear(I) )
   => ( mshare([[C],[C,D],[D],[D,H],[D,H,I],[D,I],[H],[H,I],[I]]),
        ground([B,E,F,G]) ).

reduced_rel_conj(B,C,D,E,F,G,H,I) :-
    true((mshare([[B],[B,H],[C],[D],[E],[G],[H],[I],[J],[K],[L],[M]]),ground([F]),linear(C),linear(D),linear(E),linear(G),linear(I),linear(J),linear(K),linear(L),linear(M);mshare([[B],[B,H],[C],[D],[E],[G],[H],[I],[J],[K],[L],[M]]),ground([F]),linear(D),linear(E),linear(G),linear(I),linear(J),linear(K),linear(L),linear(M);mshare([[B],[C],[D],[E],[G],[I],[J],[K],[L],[M]]),ground([F,H]),linear(C),linear(D),linear(E),linear(G),linear(I),linear(J),linear(K),linear(L),linear(M);mshare([[C],[D],[E],[G],[H],[I],[J],[K],[L],[M]]),ground([B,F]),linear(C),linear(D),linear(E),linear(G),linear(I),linear(J),linear(K),linear(L),linear(M);mshare([[C],[D],[E],[G],[H],[I],[J],[K],[L],[M]]),ground([B,F]),linear(D),linear(E),linear(G),linear(I),linear(J),linear(K),linear(L),linear(M);mshare([[C],[D],[E],[G],[I],[J],[K],[L],[M]]),ground([B,F,H]),linear(C),linear(D),linear(E),linear(G),linear(I),linear(J),linear(K),linear(L),linear(M))),
    reduced_rel(B,J,K,F,L,H,M),
    true((mshare([[B],[B,H],[B,H,J],[B,H,J,M],[B,H,M],[B,J],[B,J,M],[B,M],[C],[D],[E],[G],[H],[H,J],[H,J,M],[H,M],[I],[J],[J,M],[M]]),ground([F,K,L]),linear(C),linear(D),linear(E),linear(G),linear(I);mshare([[B],[B,H],[B,H,J],[B,H,J,M],[B,H,M],[B,J],[B,J,M],[B,M],[C],[D],[E],[G],[H],[H,J],[H,J,M],[H,M],[I],[J],[J,M],[M]]),ground([F,K,L]),linear(D),linear(E),linear(G),linear(I);mshare([[B],[B,J],[B,J,M],[B,M],[C],[D],[E],[G],[I],[J],[J,M],[M]]),ground([F,H,K,L]),linear(C),linear(D),linear(E),linear(G),linear(I);mshare([[C],[D],[E],[G],[H],[H,J],[H,J,M],[H,M],[I],[J],[J,M],[M]]),ground([B,F,K,L]),linear(C),linear(D),linear(E),linear(G),linear(I);mshare([[C],[D],[E],[G],[H],[H,J],[H,J,M],[H,M],[I],[J],[J,M],[M]]),ground([B,F,K,L]),linear(D),linear(E),linear(G),linear(I);mshare([[C],[D],[E],[G],[I],[J],[J,M],[M]]),ground([B,F,H,K,L]),linear(C),linear(D),linear(E),linear(G),linear(I))),
    reduced_rel_rest(B,C,J,D,K,E,L,G,M,I),
    true((mshare([[B],[B,D],[B,D,H],[B,D,H,I],[B,D,H,I,J],[B,D,H,I,J,M],[B,D,H,I,M],[B,D,H,J],[B,D,H,J,M],[B,D,H,M],[B,D,I],[B,D,I,J],[B,D,I,J,M],[B,D,I,M],[B,D,J],[B,D,J,M],[B,D,M],[B,H],[B,H,I],[B,H,I,M],[B,H,M],[B,I],[B,I,M],[B,M],[C],[C,D],[D],[D,H,I,J,M],[D,H,I,M],[D,H,J],[D,H,J,M],[D,H,M],[D,I],[D,I,J,M],[D,I,M],[D,J],[D,J,M],[D,M],[H],[H,I,M],[H,M],[I],[I,M],[M]]),ground([E,F,G,K,L]);mshare([[B],[B,D],[B,D,I],[B,D,I,J],[B,D,I,J,M],[B,D,I,M],[B,D,J],[B,D,J,M],[B,D,M],[B,I],[B,I,M],[B,M],[C],[C,D],[D],[D,I],[D,I,J,M],[D,I,M],[D,J],[D,J,M],[D,M],[I],[I,M],[M]]),ground([E,F,G,H,K,L]);mshare([[C],[C,D],[D],[D,H,I,J,M],[D,H,I,M],[D,H,J],[D,H,J,M],[D,H,M],[D,I],[D,I,J,M],[D,I,M],[D,J],[D,J,M],[D,M],[H],[H,I,M],[H,M],[I],[I,M],[M]]),ground([B,E,F,G,K,L]);mshare([[C],[C,D],[D],[D,I],[D,I,J,M],[D,I,M],[D,J],[D,J,M],[D,M],[I],[I,M],[M]]),ground([B,E,F,G,H,K,L]))).

:- true pred reduced_rel_rest(B,C,D,E,F,G,H,I,J,K)
   : ( mshare([[C],[D],[D,J],[E],[G],[I],[J],[K]]),
       ground([B,F,H]), linear(E), linear(G), linear(I), linear(K) )
   => ( mshare([[C],[C,E],[D,E],[D,E,J],[D,E,J,K],[E],[E,J],[E,J,K],[E,K],[J],[J,K],[K]]),
        ground([B,F,G,H,I]) ).

:- true pred reduced_rel_rest(B,C,D,E,F,G,H,I,J,K)
   : ( mshare([[B],[B,D],[B,D,J],[B,J],[C],[D],[D,J],[E],[G],[I],[J],[K]]),
       ground([F,H]), linear(E), linear(G), linear(I), linear(K) )
   => ( mshare([[B],[B,D,E],[B,D,E,J],[B,D,E,J,K],[B,D,E,K],[B,E],[B,E,J],[B,E,J,K],[B,E,K],[B,J],[B,J,K],[B,K],[C],[C,E],[D,E],[D,E,J],[D,E,J,K],[E],[E,J],[E,J,K],[E,K],[J],[J,K],[K]]),
        ground([F,G,H,I]) ).

:- true pred reduced_rel_rest(B,C,D,E,F,G,H,I,J,K)
   : ( mshare([[C],[D],[D,J],[E],[G],[I],[J],[K]]),
       ground([B,F,H]), linear(C), linear(E), linear(G), linear(I), linear(K) )
   => ( mshare([[C],[C,E],[D,E],[D,E,J],[D,E,J,K],[E],[E,J],[E,J,K],[E,K],[J],[J,K],[K]]),
        ground([B,F,G,H,I]) ).

:- true pred reduced_rel_rest(B,C,D,E,F,G,H,I,J,K)
   : ( mshare([[B],[B,D],[B,D,J],[B,J],[C],[D],[D,J],[E],[G],[I],[J],[K]]),
       ground([F,H]), linear(C), linear(E), linear(G), linear(I), linear(K) )
   => ( mshare([[B],[B,D,E],[B,D,E,J],[B,D,E,J,K],[B,D,E,K],[B,E],[B,E,J],[B,E,J,K],[B,E,K],[B,J],[B,J,K],[B,K],[C],[C,E],[D,E],[D,E,J],[D,E,J,K],[E],[E,J],[E,J,K],[E,K],[J],[J,K],[K]]),
        ground([F,G,H,I]) ).

reduced_rel_rest(B,C,D,E,F,G,H,I,J,K) :-
    true((mshare([[B],[B,D],[B,D,J],[B,J],[C],[D],[D,J],[E],[G],[I],[J],[K],[L],[M],[N],[O]]),ground([F,H]),linear(C),linear(E),linear(G),linear(I),linear(K),linear(L),linear(M),linear(N),linear(O);mshare([[B],[B,D],[B,D,J],[B,J],[C],[D],[D,J],[E],[G],[I],[J],[K],[L],[M],[N],[O]]),ground([F,H]),linear(E),linear(G),linear(I),linear(K),linear(L),linear(M),linear(N),linear(O);mshare([[C],[D],[D,J],[E],[G],[I],[J],[K],[L],[M],[N],[O]]),ground([B,F,H]),linear(C),linear(E),linear(G),linear(I),linear(K),linear(L),linear(M),linear(N),linear(O);mshare([[C],[D],[D,J],[E],[G],[I],[J],[K],[L],[M],[N],[O]]),ground([B,F,H]),linear(E),linear(G),linear(I),linear(K),linear(L),linear(M),linear(N),linear(O))),
    conj(C,L,D,M,E,H,N,J,O),
    true((mshare([[B],[B,D,E],[B,D,E,J],[B,D,E,J,O],[B,J],[B,J,O],[C,E,L],[D,E],[D,E,J],[D,E,J,O],[E,M],[G],[I],[J],[J,O],[K]]),ground([F,H,N]),linear(G),linear(I),linear(K),linear(M);mshare([[C,E,L],[D,E],[D,E,J],[D,E,J,O],[E,M],[G],[I],[J],[J,O],[K]]),ground([B,F,H,N]),linear(G),linear(I),linear(K),linear(M))),
    reduced_rel_conj(B,L,M,G,N,I,O,K),
    true((mshare([[B],[B,D,E],[B,D,E,J],[B,D,E,J,K],[B,D,E,J,K,M],[B,D,E,J,K,M,O],[B,D,E,J,K,O],[B,D,E,J,M],[B,D,E,J,M,O],[B,D,E,J,O],[B,D,E,K],[B,D,E,K,M],[B,D,E,M],[B,E,J,K,M],[B,E,J,K,M,O],[B,E,J,M],[B,E,J,M,O],[B,E,K,M],[B,E,M],[B,J],[B,J,K],[B,J,K,O],[B,J,O],[B,K],[C,E,L],[C,E,L,M],[D,E],[D,E,J],[D,E,J,K,M,O],[D,E,J,K,O],[D,E,J,M,O],[D,E,J,O],[E,J,K,M,O],[E,J,M,O],[E,K,M],[E,M],[J],[J,K,O],[J,O],[K]]),ground([F,G,H,I,N]);mshare([[C,E,L],[C,E,L,M],[D,E],[D,E,J],[D,E,J,K,M,O],[D,E,J,K,O],[D,E,J,M,O],[D,E,J,O],[E,J,K,M,O],[E,J,M,O],[E,K,M],[E,M],[J],[J,K,O],[J,O],[K]]),ground([B,F,G,H,I,N]))).
reduced_rel_rest(B,C,D,D,E,E,F,F,G,G).

:- true pred reduced_rel(B,_A,E,F,G,H,I)
   : ( mshare([[B],[_A],[E],[G],[I]]),
       ground([F,H]), linear(_A), linear(E), linear(G), linear(I) )
   => ( mshare([[B],[B,_A],[B,_A,I],[B,I],[_A],[_A,I],[I]]),
        ground([E,F,G,H]) ).

:- true pred reduced_rel(B,_A,E,F,G,H,I)
   : ( mshare([[_A],[E],[G],[I]]),
       ground([B,F,H]), linear(_A), linear(E), linear(G), linear(I) )
   => ( mshare([[_A],[_A,I],[I]]),
        ground([B,E,F,G,H]) ).

:- true pred reduced_rel(B,_A,E,F,G,H,I)
   : ( mshare([[B],[B,H],[_A],[E],[G],[H],[I]]),
       ground([F]), linear(_A), linear(E), linear(G), linear(I) )
   => ( mshare([[B],[B,_A],[B,_A,H],[B,_A,H,I],[B,_A,I],[B,H],[B,H,I],[B,I],[_A],[_A,H],[_A,H,I],[_A,I],[H],[H,I],[I]]),
        ground([E,F,G]) ).

:- true pred reduced_rel(B,_A,E,F,G,H,I)
   : ( mshare([[_A],[E],[G],[H],[I]]),
       ground([B,F]), linear(_A), linear(E), linear(G), linear(I) )
   => ( mshare([[_A],[_A,H],[_A,H,I],[_A,I],[H],[H,I],[I]]),
        ground([B,E,F,G]) ).

reduced_rel(B,reduced_rel(C,D),E,F,G,H,I) :-
    true((mshare([[B],[B,H],[E],[G],[H],[I],[C],[D],[J],[K],[L],[M],[N],[O],[P],[Q]]),ground([F]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q);mshare([[B],[E],[G],[I],[C],[D],[J],[K],[L],[M],[N],[O],[P],[Q]]),ground([F,H]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q);mshare([[E],[G],[H],[I],[C],[D],[J],[K],[L],[M],[N],[O],[P],[Q]]),ground([B,F]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q);mshare([[E],[G],[I],[C],[D],[J],[K],[L],[M],[N],[O],[P],[Q]]),ground([B,F,H]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(J),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q))),
    myopen(F,J,H,K),
    true((mshare([[B],[B,H,K],[E],[G],[H,K],[I],[C],[D],[L],[M],[N],[O],[P],[Q]]),ground([F,J]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q);mshare([[B],[E],[G],[I],[C],[D],[L],[M],[N],[O],[P],[Q]]),ground([F,H,J,K]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q);mshare([[E],[G],[H,K],[I],[C],[D],[L],[M],[N],[O],[P],[Q]]),ground([B,F,J]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q);mshare([[E],[G],[I],[C],[D],[L],[M],[N],[O],[P],[Q]]),ground([B,F,H,J,K]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(L),linear(M),linear(N),linear(O),linear(P),linear(Q))),
    reduced_wh(B,C,J,L,K,M),
    true((mshare([[B,H,K,M],[B,M],[E],[G],[H,K],[H,K,M],[I],[C,M],[D],[M],[N],[O],[P],[Q]]),ground([F,J,L]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(N),linear(O),linear(P),linear(Q);mshare([[B,M],[E],[G],[I],[C,M],[D],[M],[N],[O],[P],[Q]]),ground([F,H,J,K,L]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(N),linear(O),linear(P),linear(Q);mshare([[E],[G],[H,K],[H,K,M],[I],[C,M],[D],[M],[N],[O],[P],[Q]]),ground([B,F,J,L]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(N),linear(O),linear(P),linear(Q);mshare([[E],[G],[I],[C,M],[D],[M],[N],[O],[P],[Q]]),ground([B,F,H,J,K,L]),linear(E),linear(G),linear(I),linear(C),linear(D),linear(N),linear(O),linear(P),linear(Q))),
    s(D,N,L,O,M,P),
    true((mshare([[B,H,C,D,K,M],[B,H,C,D,K,M,P],[B,H,C,K,M],[B,H,C,K,M,P],[B,H,D,K,M],[B,H,D,K,M,P],[B,H,K,M],[B,H,K,M,P],[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[E],[G],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P],[Q]]),ground([F,J,L,N,O]),linear(E),linear(G),linear(I),linear(Q);mshare([[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[E],[G],[I],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P],[Q]]),ground([F,H,J,K,L,N,O]),linear(E),linear(G),linear(I),linear(Q);mshare([[E],[G],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P],[Q]]),ground([B,F,J,L,N,O]),linear(E),linear(G),linear(I),linear(Q);mshare([[E],[G],[I],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P],[Q]]),ground([B,F,H,J,K,L,N,O]),linear(E),linear(G),linear(I),linear(Q))),
    trace1(Q),
    true((mshare([[B,H,C,D,K,M],[B,H,C,D,K,M,P],[B,H,C,K,M],[B,H,C,K,M,P],[B,H,D,K,M],[B,H,D,K,M,P],[B,H,K,M],[B,H,K,M,P],[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[E],[G],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([F,J,L,N,O,Q]),linear(E),linear(G),linear(I);mshare([[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[E],[G],[I],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([F,H,J,K,L,N,O,Q]),linear(E),linear(G),linear(I);mshare([[E],[G],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([B,F,J,L,N,O,Q]),linear(E),linear(G),linear(I);mshare([[E],[G],[I],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([B,F,H,J,K,L,N,O,Q]),linear(E),linear(G),linear(I))),
    minus(N,Q,E),
    true((mshare([[B,H,C,D,K,M],[B,H,C,D,K,M,P],[B,H,C,K,M],[B,H,C,K,M,P],[B,H,D,K,M],[B,H,D,K,M,P],[B,H,K,M],[B,H,K,M,P],[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[G],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([E,F,J,L,N,O,Q]),linear(G),linear(I);mshare([[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[G],[I],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([E,F,H,J,K,L,N,O,Q]),linear(G),linear(I);mshare([[G],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([B,E,F,J,L,N,O,Q]),linear(G),linear(I);mshare([[G],[I],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([B,E,F,H,J,K,L,N,O,Q]),linear(G),linear(I))),
    close(O,G,P,I),
    true((mshare([[B,H,I,C,D,K,M,P],[B,H,I,C,K,M,P],[B,H,I,D,K,M,P],[B,H,I,K,M,P],[B,H,C,D,K,M],[B,H,C,D,K,M,P],[B,H,C,K,M],[B,H,C,K,M,P],[B,H,D,K,M],[B,H,D,K,M,P],[B,H,K,M],[B,H,K,M,P],[B,I,C,D,M,P],[B,I,C,M,P],[B,I,D,M,P],[B,I,M,P],[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[H,I,C,D,K,M,P],[H,I,C,K,M,P],[H,I,D,K,M,P],[H,I,K,M,P],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I,C,D,M,P],[I,C,M,P],[I,D,M,P],[I,D,P],[I,M,P],[I,P],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([E,F,G,J,L,N,O,Q]);mshare([[B,I,C,D,M,P],[B,I,C,M,P],[B,I,D,M,P],[B,I,M,P],[B,C,D,M],[B,C,D,M,P],[B,C,M],[B,C,M,P],[B,D,M],[B,D,M,P],[B,M],[B,M,P],[I,C,D,M,P],[I,C,M,P],[I,D,M,P],[I,D,P],[I,M,P],[I,P],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([E,F,G,H,J,K,L,N,O,Q]);mshare([[H,I,C,D,K,M,P],[H,I,C,K,M,P],[H,I,D,K,M,P],[H,I,K,M,P],[H,C,D,K,M],[H,C,D,K,M,P],[H,C,K,M],[H,C,K,M,P],[H,D,K,M],[H,D,K,M,P],[H,K],[H,K,M],[H,K,M,P],[I,C,D,M,P],[I,C,M,P],[I,D,M,P],[I,D,P],[I,M,P],[I,P],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([B,E,F,G,J,L,N,O,Q]);mshare([[I,C,D,M,P],[I,C,M,P],[I,D,M,P],[I,D,P],[I,M,P],[I,P],[C,D,M],[C,D,M,P],[C,M],[C,M,P],[D],[D,M],[D,M,P],[D,P],[M],[M,P],[P]]),ground([B,E,F,G,H,J,K,L,N,O,Q]))).

:- true pred reduced_wh(B,C,D,E,F,_A)
   : ( mshare([[B],[C],[E],[_A]]),
       ground([D,F]), linear(C), linear(E), linear(_A) )
   => ( mshare([[B,_A],[C,_A],[_A]]),
        ground([D,E,F]), linear(C) ).

:- true pred reduced_wh(B,C,D,E,F,_A)
   : ( mshare([[C],[E],[_A]]),
       ground([B,D,F]), linear(C), linear(E), linear(_A) )
   => ( mshare([[C,_A],[_A]]),
        ground([B,D,E,F]), linear(C) ).

:- true pred reduced_wh(B,C,D,E,F,_A)
   : ( mshare([[B],[B,F],[C],[E],[F],[_A]]),
       ground([D]), linear(C), linear(E), linear(_A) )
   => ( mshare([[B,F,_A],[B,_A],[C,_A],[F],[F,_A],[_A]]),
        ground([D,E]), linear(C) ).

:- true pred reduced_wh(B,C,D,E,F,_A)
   : ( mshare([[C],[E],[F],[_A]]),
       ground([B,D]), linear(C), linear(E), linear(_A) )
   => ( mshare([[C,_A],[F],[F,_A],[_A]]),
        ground([B,D,E]), linear(C) ).

reduced_wh(B,C,D,E,F,x(nogap,nonterminal,np(np(B,wh(C),[]),B,G,H,I,J,K),x(nogap,nonterminal,verb_form(be,pres+fin,B,main),x(nogap,nonterminal,neg(L,M),x(nogap,nonterminal,predicate(M,N,O),P))))) :-
    true((mshare([[B],[B,F],[C],[E],[F],[G],[H],[I],[J],[K],[L],[M],[P],[N],[O],[Q],[R],[S]]),ground([D]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(P),linear(N),linear(O),linear(Q),linear(R),linear(S);mshare([[B],[C],[E],[G],[H],[I],[J],[K],[L],[M],[P],[N],[O],[Q],[R],[S]]),ground([D,F]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(P),linear(N),linear(O),linear(Q),linear(R),linear(S);mshare([[C],[E],[F],[G],[H],[I],[J],[K],[L],[M],[P],[N],[O],[Q],[R],[S]]),ground([B,D]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(P),linear(N),linear(O),linear(Q),linear(R),linear(S);mshare([[C],[E],[G],[H],[I],[J],[K],[L],[M],[P],[N],[O],[Q],[R],[S]]),ground([B,D,F]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(P),linear(N),linear(O),linear(Q),linear(R),linear(S))),
    neg(Q,M,D,R,F,S),
    true((mshare([[B],[B,F],[B,F,M],[B,F,M,Q],[B,F,M,Q,S],[B,F,M,S],[B,F,Q],[B,F,Q,S],[B,F,S],[C],[E],[F],[F,M],[F,M,Q],[F,M,Q,S],[F,M,S],[F,Q],[F,Q,S],[F,S],[G],[H],[I],[J],[K],[L],[P],[N],[O],[Q]]),ground([D,R]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(P),linear(N),linear(O);mshare([[B],[C],[E],[G],[H],[I],[J],[K],[L],[P],[N],[O],[Q]]),ground([D,F,M,R,S]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(P),linear(N),linear(O);mshare([[C],[E],[F],[F,M],[F,M,Q],[F,M,Q,S],[F,M,S],[F,Q],[F,Q,S],[F,S],[G],[H],[I],[J],[K],[L],[P],[N],[O],[Q]]),ground([B,D,R]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(P),linear(N),linear(O);mshare([[C],[E],[G],[H],[I],[J],[K],[L],[P],[N],[O],[Q]]),ground([B,D,F,M,R,S]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(P),linear(N),linear(O))),
    predicate(M,N,O,R,E,S,P),
    true((mshare([[B],[B,F],[B,F,M],[B,F,M,P,N,O,Q,S],[B,F,M,P,N,O,S],[B,F,M,P,N,Q,S],[B,F,M,P,N,S],[B,F,M,P,O,Q,S],[B,F,M,P,O,S],[B,F,M,P,Q,S],[B,F,M,P,S],[B,F,M,N,O,Q,S],[B,F,M,N,O,S],[B,F,M,N,Q,S],[B,F,M,N,S],[B,F,M,O,Q,S],[B,F,M,O,S],[B,F,M,Q],[B,F,M,Q,S],[B,F,M,S],[B,F,P,N,O,Q,S],[B,F,P,N,O,S],[B,F,P,N,Q,S],[B,F,P,N,S],[B,F,P,O,Q,S],[B,F,P,O,S],[B,F,P,Q,S],[B,F,P,S],[B,F,N,O,Q,S],[B,F,N,O,S],[B,F,N,Q,S],[B,F,N,S],[B,F,O,Q,S],[B,F,O,S],[B,F,Q],[B,F,Q,S],[B,F,S],[C],[F],[F,M],[F,M,P,N,O,Q,S],[F,M,P,N,O,S],[F,M,P,N,Q,S],[F,M,P,N,S],[F,M,P,O,Q,S],[F,M,P,O,S],[F,M,P,Q,S],[F,M,P,S],[F,M,N,O,Q,S],[F,M,N,O,S],[F,M,N,Q,S],[F,M,N,S],[F,M,O,Q,S],[F,M,O,S],[F,M,Q],[F,M,Q,S],[F,M,S],[F,P,N,O,Q,S],[F,P,N,O,S],[F,P,N,Q,S],[F,P,N,S],[F,P,O,Q,S],[F,P,O,S],[F,P,Q,S],[F,P,S],[F,N,O,Q,S],[F,N,O,S],[F,N,Q,S],[F,N,S],[F,O,Q,S],[F,O,S],[F,Q],[F,Q,S],[F,S],[G],[H],[I],[J],[K],[L],[P],[P,N],[N],[Q]]),ground([D,E,R]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L);mshare([[B],[C],[G],[H],[I],[J],[K],[L],[P],[P,N],[N],[Q]]),ground([D,E,F,M,O,R,S]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L);mshare([[C],[F],[F,M],[F,M,P,N,O,Q,S],[F,M,P,N,O,S],[F,M,P,N,Q,S],[F,M,P,N,S],[F,M,P,O,Q,S],[F,M,P,O,S],[F,M,P,Q,S],[F,M,P,S],[F,M,N,O,Q,S],[F,M,N,O,S],[F,M,N,Q,S],[F,M,N,S],[F,M,O,Q,S],[F,M,O,S],[F,M,Q],[F,M,Q,S],[F,M,S],[F,P,N,O,Q,S],[F,P,N,O,S],[F,P,N,Q,S],[F,P,N,S],[F,P,O,Q,S],[F,P,O,S],[F,P,Q,S],[F,P,S],[F,N,O,Q,S],[F,N,O,S],[F,N,Q,S],[F,N,S],[F,O,Q,S],[F,O,S],[F,Q],[F,Q,S],[F,S],[G],[H],[I],[J],[K],[L],[P],[P,N],[N],[Q]]),ground([B,D,E,R]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L);mshare([[C],[G],[H],[I],[J],[K],[L],[P],[P,N],[N],[Q]]),ground([B,D,E,F,M,O,R,S]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L))),
    trace1(J,K),
    true((mshare([[B],[B,F],[B,F,M],[B,F,M,P,N,O,Q,S],[B,F,M,P,N,O,S],[B,F,M,P,N,Q,S],[B,F,M,P,N,S],[B,F,M,P,O,Q,S],[B,F,M,P,O,S],[B,F,M,P,Q,S],[B,F,M,P,S],[B,F,M,N,O,Q,S],[B,F,M,N,O,S],[B,F,M,N,Q,S],[B,F,M,N,S],[B,F,M,O,Q,S],[B,F,M,O,S],[B,F,M,Q],[B,F,M,Q,S],[B,F,M,S],[B,F,P,N,O,Q,S],[B,F,P,N,O,S],[B,F,P,N,Q,S],[B,F,P,N,S],[B,F,P,O,Q,S],[B,F,P,O,S],[B,F,P,Q,S],[B,F,P,S],[B,F,N,O,Q,S],[B,F,N,O,S],[B,F,N,Q,S],[B,F,N,S],[B,F,O,Q,S],[B,F,O,S],[B,F,Q],[B,F,Q,S],[B,F,S],[C],[F],[F,M],[F,M,P,N,O,Q,S],[F,M,P,N,O,S],[F,M,P,N,Q,S],[F,M,P,N,S],[F,M,P,O,Q,S],[F,M,P,O,S],[F,M,P,Q,S],[F,M,P,S],[F,M,N,O,Q,S],[F,M,N,O,S],[F,M,N,Q,S],[F,M,N,S],[F,M,O,Q,S],[F,M,O,S],[F,M,Q],[F,M,Q,S],[F,M,S],[F,P,N,O,Q,S],[F,P,N,O,S],[F,P,N,Q,S],[F,P,N,S],[F,P,O,Q,S],[F,P,O,S],[F,P,Q,S],[F,P,S],[F,N,O,Q,S],[F,N,O,S],[F,N,Q,S],[F,N,S],[F,O,Q,S],[F,O,S],[F,Q],[F,Q,S],[F,S],[G],[H],[I],[J],[L],[P],[P,N],[N],[Q]]),ground([D,E,K,R]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(L);mshare([[B],[C],[G],[H],[I],[J],[L],[P],[P,N],[N],[Q]]),ground([D,E,F,K,M,O,R,S]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(L);mshare([[C],[F],[F,M],[F,M,P,N,O,Q,S],[F,M,P,N,O,S],[F,M,P,N,Q,S],[F,M,P,N,S],[F,M,P,O,Q,S],[F,M,P,O,S],[F,M,P,Q,S],[F,M,P,S],[F,M,N,O,Q,S],[F,M,N,O,S],[F,M,N,Q,S],[F,M,N,S],[F,M,O,Q,S],[F,M,O,S],[F,M,Q],[F,M,Q,S],[F,M,S],[F,P,N,O,Q,S],[F,P,N,O,S],[F,P,N,Q,S],[F,P,N,S],[F,P,O,Q,S],[F,P,O,S],[F,P,Q,S],[F,P,S],[F,N,O,Q,S],[F,N,O,S],[F,N,Q,S],[F,N,S],[F,O,Q,S],[F,O,S],[F,Q],[F,Q,S],[F,S],[G],[H],[I],[J],[L],[P],[P,N],[N],[Q]]),ground([B,D,E,K,R]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(L);mshare([[C],[G],[H],[I],[J],[L],[P],[P,N],[N],[Q]]),ground([B,D,E,F,K,M,O,R,S]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(L))),
    subj_case(G),
    true((mshare([[B],[B,F],[B,F,M],[B,F,M,P,N,O,Q,S],[B,F,M,P,N,O,S],[B,F,M,P,N,Q,S],[B,F,M,P,N,S],[B,F,M,P,O,Q,S],[B,F,M,P,O,S],[B,F,M,P,Q,S],[B,F,M,P,S],[B,F,M,N,O,Q,S],[B,F,M,N,O,S],[B,F,M,N,Q,S],[B,F,M,N,S],[B,F,M,O,Q,S],[B,F,M,O,S],[B,F,M,Q],[B,F,M,Q,S],[B,F,M,S],[B,F,P,N,O,Q,S],[B,F,P,N,O,S],[B,F,P,N,Q,S],[B,F,P,N,S],[B,F,P,O,Q,S],[B,F,P,O,S],[B,F,P,Q,S],[B,F,P,S],[B,F,N,O,Q,S],[B,F,N,O,S],[B,F,N,Q,S],[B,F,N,S],[B,F,O,Q,S],[B,F,O,S],[B,F,Q],[B,F,Q,S],[B,F,S],[C],[F],[F,M],[F,M,P,N,O,Q,S],[F,M,P,N,O,S],[F,M,P,N,Q,S],[F,M,P,N,S],[F,M,P,O,Q,S],[F,M,P,O,S],[F,M,P,Q,S],[F,M,P,S],[F,M,N,O,Q,S],[F,M,N,O,S],[F,M,N,Q,S],[F,M,N,S],[F,M,O,Q,S],[F,M,O,S],[F,M,Q],[F,M,Q,S],[F,M,S],[F,P,N,O,Q,S],[F,P,N,O,S],[F,P,N,Q,S],[F,P,N,S],[F,P,O,Q,S],[F,P,O,S],[F,P,Q,S],[F,P,S],[F,N,O,Q,S],[F,N,O,S],[F,N,Q,S],[F,N,S],[F,O,Q,S],[F,O,S],[F,Q],[F,Q,S],[F,S],[H],[I],[J],[L],[P],[P,N],[N],[Q]]),ground([D,E,G,K,R]),linear(C),linear(H),linear(I),linear(J),linear(L);mshare([[B],[C],[H],[I],[J],[L],[P],[P,N],[N],[Q]]),ground([D,E,F,G,K,M,O,R,S]),linear(C),linear(H),linear(I),linear(J),linear(L);mshare([[C],[F],[F,M],[F,M,P,N,O,Q,S],[F,M,P,N,O,S],[F,M,P,N,Q,S],[F,M,P,N,S],[F,M,P,O,Q,S],[F,M,P,O,S],[F,M,P,Q,S],[F,M,P,S],[F,M,N,O,Q,S],[F,M,N,O,S],[F,M,N,Q,S],[F,M,N,S],[F,M,O,Q,S],[F,M,O,S],[F,M,Q],[F,M,Q,S],[F,M,S],[F,P,N,O,Q,S],[F,P,N,O,S],[F,P,N,Q,S],[F,P,N,S],[F,P,O,Q,S],[F,P,O,S],[F,P,Q,S],[F,P,S],[F,N,O,Q,S],[F,N,O,S],[F,N,Q,S],[F,N,S],[F,O,Q,S],[F,O,S],[F,Q],[F,Q,S],[F,S],[H],[I],[J],[L],[P],[P,N],[N],[Q]]),ground([B,D,E,G,K,R]),linear(C),linear(H),linear(I),linear(J),linear(L);mshare([[C],[H],[I],[J],[L],[P],[P,N],[N],[Q]]),ground([B,D,E,F,G,K,M,O,R,S]),linear(C),linear(H),linear(I),linear(J),linear(L))).
reduced_wh(B,C,D,E,F,x(nogap,nonterminal,np(np(B,wh(C),[]),B,G,H,I,J,K),x(nogap,nonterminal,verb(L,M,N,O),P))) :-
    true((mshare([[B],[B,F],[C],[E],[F],[G],[H],[I],[J],[K],[P],[L],[M],[N],[O]]),ground([D]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(P),linear(L),linear(M),linear(N),linear(O);mshare([[B],[C],[E],[G],[H],[I],[J],[K],[P],[L],[M],[N],[O]]),ground([D,F]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(P),linear(L),linear(M),linear(N),linear(O);mshare([[C],[E],[F],[G],[H],[I],[J],[K],[P],[L],[M],[N],[O]]),ground([B,D]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(P),linear(L),linear(M),linear(N),linear(O);mshare([[C],[E],[G],[H],[I],[J],[K],[P],[L],[M],[N],[O]]),ground([B,D,F]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(P),linear(L),linear(M),linear(N),linear(O))),
    participle(L,N,O,D,E,F,P),
    true((mshare([[B],[B,F],[B,F,P],[B,F,P,L],[B,F,L],[C],[F],[F,P],[F,P,L],[F,L],[G],[H],[I],[J],[K],[M]]),ground([D,E,N,O]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(K),linear(M);mshare([[B],[C],[G],[H],[I],[J],[K],[M]]),ground([D,E,F,P,L,N,O]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(K),linear(M);mshare([[C],[F],[F,P],[F,P,L],[F,L],[G],[H],[I],[J],[K],[M]]),ground([B,D,E,N,O]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(K),linear(M);mshare([[C],[G],[H],[I],[J],[K],[M]]),ground([B,D,E,F,P,L,N,O]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(K),linear(M))),
    trace1(J,K),
    true((mshare([[B],[B,F],[B,F,P],[B,F,P,L],[B,F,L],[C],[F],[F,P],[F,P,L],[F,L],[G],[H],[I],[J],[M]]),ground([D,E,K,N,O]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(M);mshare([[B],[C],[G],[H],[I],[J],[M]]),ground([D,E,F,K,P,L,N,O]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(M);mshare([[C],[F],[F,P],[F,P,L],[F,L],[G],[H],[I],[J],[M]]),ground([B,D,E,K,N,O]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(M);mshare([[C],[G],[H],[I],[J],[M]]),ground([B,D,E,F,K,P,L,N,O]),linear(C),linear(G),linear(H),linear(I),linear(J),linear(M))),
    subj_case(G),
    true((mshare([[B],[B,F],[B,F,P],[B,F,P,L],[B,F,L],[C],[F],[F,P],[F,P,L],[F,L],[H],[I],[J],[M]]),ground([D,E,G,K,N,O]),linear(C),linear(H),linear(I),linear(J),linear(M);mshare([[B],[C],[H],[I],[J],[M]]),ground([D,E,F,G,K,P,L,N,O]),linear(C),linear(H),linear(I),linear(J),linear(M);mshare([[C],[F],[F,P],[F,P,L],[F,L],[H],[I],[J],[M]]),ground([B,D,E,G,K,N,O]),linear(C),linear(H),linear(I),linear(J),linear(M);mshare([[C],[H],[I],[J],[M]]),ground([B,D,E,F,G,K,P,L,N,O]),linear(C),linear(H),linear(I),linear(J),linear(M))).
reduced_wh(B,C,D,E,F,x(nogap,nonterminal,np(G,H,I,J,K,L,M),x(gap,nonterminal,np(np(B,wh(C),[]),B,N,O,P,Q,R),S))) :-
    true((mshare([[B],[B,F],[C],[E],[F],[G],[H],[I],[J],[K],[L],[M],[S],[N],[O],[P],[Q],[R],[T],[U],[V]]),ground([D]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(S),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(T),linear(U),linear(V);mshare([[B],[C],[E],[G],[H],[I],[J],[K],[L],[M],[S],[N],[O],[P],[Q],[R],[T],[U],[V]]),ground([D,F]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(S),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(T),linear(U),linear(V);mshare([[C],[E],[F],[G],[H],[I],[J],[K],[L],[M],[S],[N],[O],[P],[Q],[R],[T],[U],[V]]),ground([B,D]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(S),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(T),linear(U),linear(V);mshare([[C],[E],[G],[H],[I],[J],[K],[L],[M],[S],[N],[O],[P],[Q],[R],[T],[U],[V]]),ground([B,D,F]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(S),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(T),linear(U),linear(V))),
    s_all(T),
    true((mshare([[B],[B,F],[C],[E],[F],[G],[H],[I],[J],[K],[L],[M],[S],[N],[O],[P],[Q],[R],[U],[V]]),ground([D,T]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(S),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(U),linear(V);mshare([[B],[C],[E],[G],[H],[I],[J],[K],[L],[M],[S],[N],[O],[P],[Q],[R],[U],[V]]),ground([D,F,T]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(S),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(U),linear(V);mshare([[C],[E],[F],[G],[H],[I],[J],[K],[L],[M],[S],[N],[O],[P],[Q],[R],[U],[V]]),ground([B,D,T]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(S),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(U),linear(V);mshare([[C],[E],[G],[H],[I],[J],[K],[L],[M],[S],[N],[O],[P],[Q],[R],[U],[V]]),ground([B,D,F,T]),linear(C),linear(E),linear(G),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M),linear(S),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(U),linear(V))),
    subj_case(I),
    true((mshare([[B],[B,F],[C],[E],[F],[G],[H],[J],[K],[L],[M],[S],[N],[O],[P],[Q],[R],[U],[V]]),ground([D,I,T]),linear(C),linear(E),linear(G),linear(H),linear(J),linear(K),linear(L),linear(M),linear(S),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(U),linear(V);mshare([[B],[C],[E],[G],[H],[J],[K],[L],[M],[S],[N],[O],[P],[Q],[R],[U],[V]]),ground([D,F,I,T]),linear(C),linear(E),linear(G),linear(H),linear(J),linear(K),linear(L),linear(M),linear(S),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(U),linear(V);mshare([[C],[E],[F],[G],[H],[J],[K],[L],[M],[S],[N],[O],[P],[Q],[R],[U],[V]]),ground([B,D,I,T]),linear(C),linear(E),linear(G),linear(H),linear(J),linear(K),linear(L),linear(M),linear(S),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(U),linear(V);mshare([[C],[E],[G],[H],[J],[K],[L],[M],[S],[N],[O],[P],[Q],[R],[U],[V]]),ground([B,D,F,I,T]),linear(C),linear(E),linear(G),linear(H),linear(J),linear(K),linear(L),linear(M),linear(S),linear(N),linear(O),linear(P),linear(Q),linear(R),linear(U),linear(V))),
    verb_case(N),
    true((mshare([[B],[B,F],[C],[E],[F],[G],[H],[J],[K],[L],[M],[S],[O],[P],[Q],[R],[U],[V]]),ground([D,I,N,T]),linear(C),linear(E),linear(G),linear(H),linear(J),linear(K),linear(L),linear(M),linear(S),linear(O),linear(P),linear(Q),linear(R),linear(U),linear(V);mshare([[B],[C],[E],[G],[H],[J],[K],[L],[M],[S],[O],[P],[Q],[R],[U],[V]]),ground([D,F,I,N,T]),linear(C),linear(E),linear(G),linear(H),linear(J),linear(K),linear(L),linear(M),linear(S),linear(O),linear(P),linear(Q),linear(R),linear(U),linear(V);mshare([[C],[E],[F],[G],[H],[J],[K],[L],[M],[S],[O],[P],[Q],[R],[U],[V]]),ground([B,D,I,N,T]),linear(C),linear(E),linear(G),linear(H),linear(J),linear(K),linear(L),linear(M),linear(S),linear(O),linear(P),linear(Q),linear(R),linear(U),linear(V);mshare([[C],[E],[G],[H],[J],[K],[L],[M],[S],[O],[P],[Q],[R],[U],[V]]),ground([B,D,F,I,N,T]),linear(C),linear(E),linear(G),linear(H),linear(J),linear(K),linear(L),linear(M),linear(S),linear(O),linear(P),linear(Q),linear(R),linear(U),linear(V))),
    np(G,H,U,J,subj,T,V,D,E,F,S),
    true((mshare([[B],[B,F],[B,F,G],[B,F,G,H],[B,F,G,H,J],[B,F,G,H,J,S],[B,F,G,H,J,S,U],[B,F,G,H,J,S,U,V],[B,F,G,H,J,S,V],[B,F,G,H,J,U],[B,F,G,H,J,U,V],[B,F,G,H,J,V],[B,F,G,H,S],[B,F,G,H,S,U],[B,F,G,H,S,U,V],[B,F,G,H,S,V],[B,F,G,H,U],[B,F,G,H,U,V],[B,F,G,H,V],[B,F,G,J],[B,F,G,J,S],[B,F,G,J,S,U],[B,F,G,J,S,U,V],[B,F,G,J,S,V],[B,F,G,J,U],[B,F,G,J,U,V],[B,F,G,J,V],[B,F,G,S],[B,F,G,S,U],[B,F,G,S,U,V],[B,F,G,S,V],[B,F,G,U],[B,F,G,U,V],[B,F,G,V],[B,F,H],[B,F,H,J],[B,F,H,J,S],[B,F,H,J,S,U],[B,F,H,J,S,U,V],[B,F,H,J,S,V],[B,F,H,J,U],[B,F,H,J,U,V],[B,F,H,J,V],[B,F,H,S],[B,F,H,S,U],[B,F,H,S,U,V],[B,F,H,S,V],[B,F,H,U],[B,F,H,U,V],[B,F,H,V],[B,F,J],[B,F,J,S],[B,F,J,S,U],[B,F,J,S,U,V],[B,F,J,S,V],[B,F,J,U],[B,F,J,U,V],[B,F,J,V],[B,F,S],[B,F,S,U],[B,F,S,U,V],[B,F,S,V],[B,F,U],[B,F,U,V],[B,F,V],[C],[F],[F,G],[F,G,H],[F,G,H,J],[F,G,H,J,S],[F,G,H,J,S,U],[F,G,H,J,S,U,V],[F,G,H,J,S,V],[F,G,H,J,U],[F,G,H,J,U,V],[F,G,H,J,V],[F,G,H,S],[F,G,H,S,U],[F,G,H,S,U,V],[F,G,H,S,V],[F,G,H,U],[F,G,H,U,V],[F,G,H,V],[F,G,J],[F,G,J,S],[F,G,J,S,U],[F,G,J,S,U,V],[F,G,J,S,V],[F,G,J,U],[F,G,J,U,V],[F,G,J,V],[F,G,S],[F,G,S,U],[F,G,S,U,V],[F,G,S,V],[F,G,U],[F,G,U,V],[F,G,V],[F,H],[F,H,J],[F,H,J,S],[F,H,J,S,U],[F,H,J,S,U,V],[F,H,J,S,V],[F,H,J,U],[F,H,J,U,V],[F,H,J,V],[F,H,S],[F,H,S,U],[F,H,S,U,V],[F,H,S,V],[F,H,U],[F,H,U,V],[F,H,V],[F,J],[F,J,S],[F,J,S,U],[F,J,S,U,V],[F,J,S,V],[F,J,U],[F,J,U,V],[F,J,V],[F,S],[F,S,U],[F,S,U,V],[F,S,V],[F,U],[F,U,V],[F,V],[G],[G,H],[G,H,S],[G,S],[H],[K],[L],[M],[S],[O],[P],[Q],[R],[U]]),ground([D,E,I,N,T]),linear(C),linear(K),linear(L),linear(M),linear(O),linear(P),linear(Q),linear(R);mshare([[B],[C],[G],[G,H],[G,H,S],[G,S],[H],[K],[L],[M],[S],[O],[P],[Q],[R],[U]]),ground([D,E,F,I,J,N,T,V]),linear(C),linear(K),linear(L),linear(M),linear(O),linear(P),linear(Q),linear(R);mshare([[C],[F],[F,G],[F,G,H],[F,G,H,J],[F,G,H,J,S],[F,G,H,J,S,U],[F,G,H,J,S,U,V],[F,G,H,J,S,V],[F,G,H,J,U],[F,G,H,J,U,V],[F,G,H,J,V],[F,G,H,S],[F,G,H,S,U],[F,G,H,S,U,V],[F,G,H,S,V],[F,G,H,U],[F,G,H,U,V],[F,G,H,V],[F,G,J],[F,G,J,S],[F,G,J,S,U],[F,G,J,S,U,V],[F,G,J,S,V],[F,G,J,U],[F,G,J,U,V],[F,G,J,V],[F,G,S],[F,G,S,U],[F,G,S,U,V],[F,G,S,V],[F,G,U],[F,G,U,V],[F,G,V],[F,H],[F,H,J],[F,H,J,S],[F,H,J,S,U],[F,H,J,S,U,V],[F,H,J,S,V],[F,H,J,U],[F,H,J,U,V],[F,H,J,V],[F,H,S],[F,H,S,U],[F,H,S,U,V],[F,H,S,V],[F,H,U],[F,H,U,V],[F,H,V],[F,J],[F,J,S],[F,J,S,U],[F,J,S,U,V],[F,J,S,V],[F,J,U],[F,J,U,V],[F,J,V],[F,S],[F,S,U],[F,S,U,V],[F,S,V],[F,U],[F,U,V],[F,V],[G],[G,H],[G,H,S],[G,S],[H],[K],[L],[M],[S],[O],[P],[Q],[R],[U]]),ground([B,D,E,I,N,T]),linear(C),linear(K),linear(L),linear(M),linear(O),linear(P),linear(Q),linear(R);mshare([[C],[G],[G,H],[G,H,S],[G,S],[H],[K],[L],[M],[S],[O],[P],[Q],[R],[U]]),ground([B,D,E,F,I,J,N,T,V]),linear(C),linear(K),linear(L),linear(M),linear(O),linear(P),linear(Q),linear(R))),
    trace1(L,M),
    true((mshare([[B],[B,F],[B,F,G],[B,F,G,H],[B,F,G,H,J],[B,F,G,H,J,S],[B,F,G,H,J,S,U],[B,F,G,H,J,S,U,V],[B,F,G,H,J,S,V],[B,F,G,H,J,U],[B,F,G,H,J,U,V],[B,F,G,H,J,V],[B,F,G,H,S],[B,F,G,H,S,U],[B,F,G,H,S,U,V],[B,F,G,H,S,V],[B,F,G,H,U],[B,F,G,H,U,V],[B,F,G,H,V],[B,F,G,J],[B,F,G,J,S],[B,F,G,J,S,U],[B,F,G,J,S,U,V],[B,F,G,J,S,V],[B,F,G,J,U],[B,F,G,J,U,V],[B,F,G,J,V],[B,F,G,S],[B,F,G,S,U],[B,F,G,S,U,V],[B,F,G,S,V],[B,F,G,U],[B,F,G,U,V],[B,F,G,V],[B,F,H],[B,F,H,J],[B,F,H,J,S],[B,F,H,J,S,U],[B,F,H,J,S,U,V],[B,F,H,J,S,V],[B,F,H,J,U],[B,F,H,J,U,V],[B,F,H,J,V],[B,F,H,S],[B,F,H,S,U],[B,F,H,S,U,V],[B,F,H,S,V],[B,F,H,U],[B,F,H,U,V],[B,F,H,V],[B,F,J],[B,F,J,S],[B,F,J,S,U],[B,F,J,S,U,V],[B,F,J,S,V],[B,F,J,U],[B,F,J,U,V],[B,F,J,V],[B,F,S],[B,F,S,U],[B,F,S,U,V],[B,F,S,V],[B,F,U],[B,F,U,V],[B,F,V],[C],[F],[F,G],[F,G,H],[F,G,H,J],[F,G,H,J,S],[F,G,H,J,S,U],[F,G,H,J,S,U,V],[F,G,H,J,S,V],[F,G,H,J,U],[F,G,H,J,U,V],[F,G,H,J,V],[F,G,H,S],[F,G,H,S,U],[F,G,H,S,U,V],[F,G,H,S,V],[F,G,H,U],[F,G,H,U,V],[F,G,H,V],[F,G,J],[F,G,J,S],[F,G,J,S,U],[F,G,J,S,U,V],[F,G,J,S,V],[F,G,J,U],[F,G,J,U,V],[F,G,J,V],[F,G,S],[F,G,S,U],[F,G,S,U,V],[F,G,S,V],[F,G,U],[F,G,U,V],[F,G,V],[F,H],[F,H,J],[F,H,J,S],[F,H,J,S,U],[F,H,J,S,U,V],[F,H,J,S,V],[F,H,J,U],[F,H,J,U,V],[F,H,J,V],[F,H,S],[F,H,S,U],[F,H,S,U,V],[F,H,S,V],[F,H,U],[F,H,U,V],[F,H,V],[F,J],[F,J,S],[F,J,S,U],[F,J,S,U,V],[F,J,S,V],[F,J,U],[F,J,U,V],[F,J,V],[F,S],[F,S,U],[F,S,U,V],[F,S,V],[F,U],[F,U,V],[F,V],[G],[G,H],[G,H,S],[G,S],[H],[K],[L],[S],[O],[P],[Q],[R],[U]]),ground([D,E,I,M,N,T]),linear(C),linear(K),linear(L),linear(O),linear(P),linear(Q),linear(R);mshare([[B],[C],[G],[G,H],[G,H,S],[G,S],[H],[K],[L],[S],[O],[P],[Q],[R],[U]]),ground([D,E,F,I,J,M,N,T,V]),linear(C),linear(K),linear(L),linear(O),linear(P),linear(Q),linear(R);mshare([[C],[F],[F,G],[F,G,H],[F,G,H,J],[F,G,H,J,S],[F,G,H,J,S,U],[F,G,H,J,S,U,V],[F,G,H,J,S,V],[F,G,H,J,U],[F,G,H,J,U,V],[F,G,H,J,V],[F,G,H,S],[F,G,H,S,U],[F,G,H,S,U,V],[F,G,H,S,V],[F,G,H,U],[F,G,H,U,V],[F,G,H,V],[F,G,J],[F,G,J,S],[F,G,J,S,U],[F,G,J,S,U,V],[F,G,J,S,V],[F,G,J,U],[F,G,J,U,V],[F,G,J,V],[F,G,S],[F,G,S,U],[F,G,S,U,V],[F,G,S,V],[F,G,U],[F,G,U,V],[F,G,V],[F,H],[F,H,J],[F,H,J,S],[F,H,J,S,U],[F,H,J,S,U,V],[F,H,J,S,V],[F,H,J,U],[F,H,J,U,V],[F,H,J,V],[F,H,S],[F,H,S,U],[F,H,S,U,V],[F,H,S,V],[F,H,U],[F,H,U,V],[F,H,V],[F,J],[F,J,S],[F,J,S,U],[F,J,S,U,V],[F,J,S,V],[F,J,U],[F,J,U,V],[F,J,V],[F,S],[F,S,U],[F,S,U,V],[F,S,V],[F,U],[F,U,V],[F,V],[G],[G,H],[G,H,S],[G,S],[H],[K],[L],[S],[O],[P],[Q],[R],[U]]),ground([B,D,E,I,M,N,T]),linear(C),linear(K),linear(L),linear(O),linear(P),linear(Q),linear(R);mshare([[C],[G],[G,H],[G,H,S],[G,S],[H],[K],[L],[S],[O],[P],[Q],[R],[U]]),ground([B,D,E,F,I,J,M,N,T,V]),linear(C),linear(K),linear(L),linear(O),linear(P),linear(Q),linear(R))),
    trace1(Q,R),
    true((mshare([[B],[B,F],[B,F,G],[B,F,G,H],[B,F,G,H,J],[B,F,G,H,J,S],[B,F,G,H,J,S,U],[B,F,G,H,J,S,U,V],[B,F,G,H,J,S,V],[B,F,G,H,J,U],[B,F,G,H,J,U,V],[B,F,G,H,J,V],[B,F,G,H,S],[B,F,G,H,S,U],[B,F,G,H,S,U,V],[B,F,G,H,S,V],[B,F,G,H,U],[B,F,G,H,U,V],[B,F,G,H,V],[B,F,G,J],[B,F,G,J,S],[B,F,G,J,S,U],[B,F,G,J,S,U,V],[B,F,G,J,S,V],[B,F,G,J,U],[B,F,G,J,U,V],[B,F,G,J,V],[B,F,G,S],[B,F,G,S,U],[B,F,G,S,U,V],[B,F,G,S,V],[B,F,G,U],[B,F,G,U,V],[B,F,G,V],[B,F,H],[B,F,H,J],[B,F,H,J,S],[B,F,H,J,S,U],[B,F,H,J,S,U,V],[B,F,H,J,S,V],[B,F,H,J,U],[B,F,H,J,U,V],[B,F,H,J,V],[B,F,H,S],[B,F,H,S,U],[B,F,H,S,U,V],[B,F,H,S,V],[B,F,H,U],[B,F,H,U,V],[B,F,H,V],[B,F,J],[B,F,J,S],[B,F,J,S,U],[B,F,J,S,U,V],[B,F,J,S,V],[B,F,J,U],[B,F,J,U,V],[B,F,J,V],[B,F,S],[B,F,S,U],[B,F,S,U,V],[B,F,S,V],[B,F,U],[B,F,U,V],[B,F,V],[C],[F],[F,G],[F,G,H],[F,G,H,J],[F,G,H,J,S],[F,G,H,J,S,U],[F,G,H,J,S,U,V],[F,G,H,J,S,V],[F,G,H,J,U],[F,G,H,J,U,V],[F,G,H,J,V],[F,G,H,S],[F,G,H,S,U],[F,G,H,S,U,V],[F,G,H,S,V],[F,G,H,U],[F,G,H,U,V],[F,G,H,V],[F,G,J],[F,G,J,S],[F,G,J,S,U],[F,G,J,S,U,V],[F,G,J,S,V],[F,G,J,U],[F,G,J,U,V],[F,G,J,V],[F,G,S],[F,G,S,U],[F,G,S,U,V],[F,G,S,V],[F,G,U],[F,G,U,V],[F,G,V],[F,H],[F,H,J],[F,H,J,S],[F,H,J,S,U],[F,H,J,S,U,V],[F,H,J,S,V],[F,H,J,U],[F,H,J,U,V],[F,H,J,V],[F,H,S],[F,H,S,U],[F,H,S,U,V],[F,H,S,V],[F,H,U],[F,H,U,V],[F,H,V],[F,J],[F,J,S],[F,J,S,U],[F,J,S,U,V],[F,J,S,V],[F,J,U],[F,J,U,V],[F,J,V],[F,S],[F,S,U],[F,S,U,V],[F,S,V],[F,U],[F,U,V],[F,V],[G],[G,H],[G,H,S],[G,S],[H],[K],[L],[S],[O],[P],[Q],[U]]),ground([D,E,I,M,N,R,T]),linear(C),linear(K),linear(L),linear(O),linear(P),linear(Q);mshare([[B],[C],[G],[G,H],[G,H,S],[G,S],[H],[K],[L],[S],[O],[P],[Q],[U]]),ground([D,E,F,I,J,M,N,R,T,V]),linear(C),linear(K),linear(L),linear(O),linear(P),linear(Q);mshare([[C],[F],[F,G],[F,G,H],[F,G,H,J],[F,G,H,J,S],[F,G,H,J,S,U],[F,G,H,J,S,U,V],[F,G,H,J,S,V],[F,G,H,J,U],[F,G,H,J,U,V],[F,G,H,J,V],[F,G,H,S],[F,G,H,S,U],[F,G,H,S,U,V],[F,G,H,S,V],[F,G,H,U],[F,G,H,U,V],[F,G,H,V],[F,G,J],[F,G,J,S],[F,G,J,S,U],[F,G,J,S,U,V],[F,G,J,S,V],[F,G,J,U],[F,G,J,U,V],[F,G,J,V],[F,G,S],[F,G,S,U],[F,G,S,U,V],[F,G,S,V],[F,G,U],[F,G,U,V],[F,G,V],[F,H],[F,H,J],[F,H,J,S],[F,H,J,S,U],[F,H,J,S,U,V],[F,H,J,S,V],[F,H,J,U],[F,H,J,U,V],[F,H,J,V],[F,H,S],[F,H,S,U],[F,H,S,U,V],[F,H,S,V],[F,H,U],[F,H,U,V],[F,H,V],[F,J],[F,J,S],[F,J,S,U],[F,J,S,U,V],[F,J,S,V],[F,J,U],[F,J,U,V],[F,J,V],[F,S],[F,S,U],[F,S,U,V],[F,S,V],[F,U],[F,U,V],[F,V],[G],[G,H],[G,H,S],[G,S],[H],[K],[L],[S],[O],[P],[Q],[U]]),ground([B,D,E,I,M,N,R,T]),linear(C),linear(K),linear(L),linear(O),linear(P),linear(Q);mshare([[C],[G],[G,H],[G,H,S],[G,S],[H],[K],[L],[S],[O],[P],[Q],[U]]),ground([B,D,E,F,I,J,M,N,R,T,V]),linear(C),linear(K),linear(L),linear(O),linear(P),linear(Q))).

:- true pred verb(B,C,D,E,F,J,G,H)
   : ( mshare([[B],[C],[C,G],[D],[E],[J],[G],[H]]),
       ground([F]), linear(B), linear(D), linear(E), linear(J), linear(H) )
   => ( mshare([[B],[B,C,D,E,G],[B,C,D,E,G,H],[B,C,D,G],[B,C,D,G,H],[B,C,E,G],[B,C,E,G,H],[B,C,G],[B,C,G,H],[B,D,E,G],[B,D,E,G,H],[B,D,G],[B,D,G,H],[B,E,G],[B,E,G,H],[B,G],[B,G,H],[C],[C,D,E,G],[C,D,E,G,H],[C,D,G],[C,D,G,H],[C,E,G],[C,E,G,H],[C,G],[C,G,H],[D,E,G],[D,E,G,H],[D,G],[D,G,H],[E,G],[E,G,H],[G],[G,H]]),
        ground([F,J]) ).

verb(B,C,D,E,F,F,G,H) :-
    true((
        mshare([[B],[C],[C,G],[D],[E],[G],[H]]),
        ground([F]),
        linear(B),
        linear(D),
        linear(E),
        linear(H)
    )),
    virtual(verb(B,C,D,E),G,H),
    true((
        mshare([[B,C,D,E,G],[B,C,D,E,G,H],[B,C,D,G],[B,C,D,G,H],[B,C,E,G],[B,C,E,G,H],[B,C,G],[B,C,G,H],[B,D,E,G],[B,D,E,G,H],[B,D,G],[B,D,G,H],[B,E,G],[B,E,G,H],[B,G],[B,G,H],[C,D,E,G],[C,D,E,G,H],[C,D,G],[C,D,G,H],[C,E,G],[C,E,G,H],[C,G],[C,G,H],[D,E,G],[D,E,G,H],[D,G],[D,G,H],[E,G],[E,G,H],[G],[G,H]]),
        ground([F])
    )).
verb(verb(B,C,D+fin,E,F),G,H,C,I,J,K,L) :-
    true((
        mshare([[G],[G,K],[H],[C],[J],[K],[L],[B],[E],[F],[D],[M],[N],[O],[P],[Q],[R],[S]]),
        ground([I]),
        linear(H),
        linear(C),
        linear(J),
        linear(L),
        linear(B),
        linear(E),
        linear(F),
        linear(D),
        linear(M),
        linear(N),
        linear(O),
        linear(P),
        linear(Q),
        linear(R),
        linear(S)
    )),
    verb_form(M,D+fin,G,N,I,O,K,P),
    true((
        mshare([[G],[G,K],[G,K,D],[G,K,D,M],[G,K,D,M,N],[G,K,D,M,N,P],[G,K,D,M,P],[G,K,D,N],[G,K,D,N,P],[G,K,D,P],[G,K,M],[G,K,M,N],[G,K,M,N,P],[G,K,M,P],[G,K,N],[G,K,N,P],[G,K,P],[H],[C],[J],[K],[K,D],[K,D,M],[K,D,M,N],[K,D,M,N,P],[K,D,M,P],[K,D,N],[K,D,N,P],[K,D,P],[K,M],[K,M,N],[K,M,N,P],[K,M,P],[K,N],[K,N,P],[K,P],[L],[B],[E],[F],[D],[N],[Q],[R],[S]]),
        ground([I,O]),
        linear(H),
        linear(C),
        linear(J),
        linear(L),
        linear(B),
        linear(E),
        linear(F),
        linear(Q),
        linear(R),
        linear(S)
    )),
    verb_type(M,Q),
    true((
        mshare([[G],[G,K],[G,K,D],[G,K,D,N],[G,K,D,N,P],[G,K,D,P],[G,K,N],[G,K,N,P],[G,K,P],[H],[C],[J],[K],[K,D],[K,D,N],[K,D,N,P],[K,D,P],[K,N],[K,N,P],[K,P],[L],[B],[E],[F],[D],[N],[R],[S]]),
        ground([I,M,O,Q]),
        linear(H),
        linear(C),
        linear(J),
        linear(L),
        linear(B),
        linear(E),
        linear(F),
        linear(R),
        linear(S)
    )),
    neg(Q,F,O,R,P,S),
    true((
        mshare([[G],[G,K],[G,K,F,D,N,P],[G,K,F,D,N,P,S],[G,K,F,D,P],[G,K,F,D,P,S],[G,K,F,N,P],[G,K,F,N,P,S],[G,K,F,P],[G,K,F,P,S],[G,K,D],[G,K,D,N],[G,K,D,N,P],[G,K,D,N,P,S],[G,K,D,P],[G,K,D,P,S],[G,K,N],[G,K,N,P],[G,K,N,P,S],[G,K,P],[G,K,P,S],[H],[C],[J],[K],[K,F,D,N,P],[K,F,D,N,P,S],[K,F,D,P],[K,F,D,P,S],[K,F,N,P],[K,F,N,P,S],[K,F,P],[K,F,P,S],[K,D],[K,D,N],[K,D,N,P],[K,D,N,P,S],[K,D,P],[K,D,P,S],[K,N],[K,N,P],[K,N,P,S],[K,P],[K,P,S],[L],[B],[E],[D],[N]]),
        ground([I,M,O,Q,R]),
        linear(H),
        linear(C),
        linear(J),
        linear(L),
        linear(B),
        linear(E)
    )),
    rest_verb(N,M,B,C,E,R,J,S,L),
    true((
        mshare([[G],[G,K],[G,K,L,B,F,D,P,S],[G,K,L,B,F,P,S],[G,K,L,B,D,P,S],[G,K,L,B,P,S],[G,K,L,F,D,P,S],[G,K,L,F,P,S],[G,K,L,D,P,S],[G,K,L,P,S],[G,K,B,F,D,P,S],[G,K,B,F,P,S],[G,K,B,D,P,S],[G,K,B,P,S],[G,K,F,D,P],[G,K,F,D,P,S],[G,K,F,P],[G,K,F,P,S],[G,K,D],[G,K,D,P],[G,K,D,P,S],[G,K,P],[G,K,P,S],[H],[K],[K,L,B,F,D,P,S],[K,L,B,F,P,S],[K,L,B,D,P,S],[K,L,B,P,S],[K,L,F,D,P,S],[K,L,F,P,S],[K,L,D,P,S],[K,L,P,S],[K,B,F,D,P,S],[K,B,F,P,S],[K,B,D,P,S],[K,B,P,S],[K,F,D,P],[K,F,D,P,S],[K,F,P],[K,F,P,S],[K,D],[K,D,P],[K,D,P,S],[K,P],[K,P,S],[D]]),
        ground([C,I,J,E,M,N,O,Q,R]),
        linear(H)
    )),
    verb_type(B,H),
    true((
        mshare([[G],[G,K],[G,K,L,F,D,P,S],[G,K,L,F,P,S],[G,K,L,D,P,S],[G,K,L,P,S],[G,K,F,D,P],[G,K,F,D,P,S],[G,K,F,P],[G,K,F,P,S],[G,K,D],[G,K,D,P],[G,K,D,P,S],[G,K,P],[G,K,P,S],[K],[K,L,F,D,P,S],[K,L,F,P,S],[K,L,D,P,S],[K,L,P,S],[K,F,D,P],[K,F,D,P,S],[K,F,P],[K,F,P,S],[K,D],[K,D,P],[K,D,P,S],[K,P],[K,P,S],[D]]),
        ground([H,C,I,J,B,E,M,N,O,Q,R])
    )).

:- true pred rest_verb(_A,_B,B,C,D,E,F,G,H)
   : ( mshare([[_A],[_A,G],[B],[C],[D],[F],[G],[H]]),
       ground([_B,E]), linear(B), linear(C), linear(D), linear(F), linear(H) )
   => ( mshare([[B,G],[B,G,H],[G],[G,H]]),
        ground([_A,_B,C,D,E,F]) ).

rest_verb(aux,have,B,C,[perf|D],E,F,G,H) :-
    true((
        mshare([[B],[C],[F],[G],[H],[D],[I],[J],[K],[L],[M]]),
        ground([E]),
        linear(B),
        linear(C),
        linear(F),
        linear(H),
        linear(D),
        linear(I),
        linear(J),
        linear(K),
        linear(L),
        linear(M)
    )),
    verb_form(I,past+part,J,K,E,L,G,M),
    true((
        mshare([[B],[C],[F],[G],[G,I],[G,I,J],[G,I,J,K],[G,I,J,K,M],[G,I,J,M],[G,I,K],[G,I,K,M],[G,I,M],[G,J],[G,J,K],[G,J,K,M],[G,J,M],[G,K],[G,K,M],[G,M],[H],[D],[J],[K]]),
        ground([E,L]),
        linear(B),
        linear(C),
        linear(F),
        linear(H),
        linear(D)
    )),
    have(I,B,C,D,L,F,M,H),
    true((
        mshare([[B,G,H,I,J,K,M],[B,G,H,I,J,M],[B,G,H,I,K,M],[B,G,H,I,M],[B,G,H,J,K,M],[B,G,H,J,M],[B,G,H,K,M],[B,G,H,M],[B,G,I],[B,G,I,J],[B,G,I,J,K],[B,G,I,K],[B,G,J,K,M],[B,G,J,M],[B,G,K,M],[B,G,M],[G],[G,H,J,K,M],[G,H,J,M],[G,H,K,M],[G,H,M],[G,J],[G,J,K],[G,J,K,M],[G,J,M],[G,K],[G,K,M],[G,M],[J],[K]]),
        ground([C,E,F,D,L])
    )).
rest_verb(aux,be,B,C,D,E,F,G,H) :-
    true((
        mshare([[B],[C],[D],[F],[G],[H],[I],[J],[K],[L],[M],[N]]),
        ground([E]),
        linear(B),
        linear(C),
        linear(D),
        linear(F),
        linear(H),
        linear(I),
        linear(J),
        linear(K),
        linear(L),
        linear(M),
        linear(N)
    )),
    verb_form(I,J,K,L,E,M,G,N),
    true((
        mshare([[B],[C],[D],[F],[G],[G,I],[G,I,J],[G,I,J,K],[G,I,J,K,L],[G,I,J,K,L,N],[G,I,J,K,N],[G,I,J,L],[G,I,J,L,N],[G,I,J,N],[G,I,K],[G,I,K,L],[G,I,K,L,N],[G,I,K,N],[G,I,L],[G,I,L,N],[G,I,N],[G,J],[G,J,K],[G,J,K,L],[G,J,K,L,N],[G,J,K,N],[G,J,L],[G,J,L,N],[G,J,N],[G,K],[G,K,L],[G,K,L,N],[G,K,N],[G,L],[G,L,N],[G,N],[H],[J],[K],[L]]),
        ground([E,M]),
        linear(B),
        linear(C),
        linear(D),
        linear(F),
        linear(H)
    )),
    be(J,I,B,C,D,M,F,N,H),
    true((
        mshare([[B,G,H,I,K,L,N],[B,G,H,I,K,N],[B,G,H,I,L,N],[B,G,H,I,N],[B,G,I],[B,G,I,K],[B,G,I,K,L],[B,G,I,L],[G],[G,H,K,L,N],[G,H,K,N],[G,H,L,N],[G,H,N],[G,K],[G,K,L],[G,K,L,N],[G,K,N],[G,L],[G,L,N],[G,N],[K],[L]]),
        ground([C,D,E,F,J,M])
    )).
rest_verb(aux,do,B,active,[],C,D,E,F) :-
    true((
        mshare([[B],[D],[E],[F],[G],[H]]),
        ground([C]),
        linear(B),
        linear(D),
        linear(F),
        linear(G),
        linear(H)
    )),
    verb_form(B,inf,G,H,C,D,E,F),
    true((
        mshare([[B,E],[B,E,F],[B,E,F,G],[B,E,F,G,H],[B,E,F,H],[B,E,G],[B,E,G,H],[B,E,H],[E],[E,F],[E,F,G],[E,F,G,H],[E,F,H],[E,G],[E,G,H],[E,H],[G],[H]]),
        ground([C,D])
    )).
rest_verb(main,B,B,active,[],C,C,D,D).

:- true pred have(_A,B,C,D,E,F,G,H)
   : ( mshare([[_A],[_A,G],[B],[C],[D],[F],[G],[H]]),
       ground([E]), linear(B), linear(C), linear(D), linear(F), linear(H) )
   => ( mshare([[_A,B],[_A,B,G,H],[B,G],[B,G,H],[G],[G,H]]),
        ground([C,D,E,F]) ).

have(be,B,C,D,E,F,G,H) :-
    true((
        mshare([[B],[C],[D],[F],[G],[H],[I],[J],[K],[L],[M],[N]]),
        ground([E]),
        linear(B),
        linear(C),
        linear(D),
        linear(F),
        linear(H),
        linear(I),
        linear(J),
        linear(K),
        linear(L),
        linear(M),
        linear(N)
    )),
    verb_form(I,J,K,L,E,M,G,N),
    true((
        mshare([[B],[C],[D],[F],[G],[G,I],[G,I,J],[G,I,J,K],[G,I,J,K,L],[G,I,J,K,L,N],[G,I,J,K,N],[G,I,J,L],[G,I,J,L,N],[G,I,J,N],[G,I,K],[G,I,K,L],[G,I,K,L,N],[G,I,K,N],[G,I,L],[G,I,L,N],[G,I,N],[G,J],[G,J,K],[G,J,K,L],[G,J,K,L,N],[G,J,K,N],[G,J,L],[G,J,L,N],[G,J,N],[G,K],[G,K,L],[G,K,L,N],[G,K,N],[G,L],[G,L,N],[G,N],[H],[J],[K],[L]]),
        ground([E,M]),
        linear(B),
        linear(C),
        linear(D),
        linear(F),
        linear(H)
    )),
    be(J,I,B,C,D,M,F,N,H),
    true((
        mshare([[B,G,H,I,K,L,N],[B,G,H,I,K,N],[B,G,H,I,L,N],[B,G,H,I,N],[B,G,I],[B,G,I,K],[B,G,I,K,L],[B,G,I,L],[G],[G,H,K,L,N],[G,H,K,N],[G,H,L,N],[G,H,N],[G,K],[G,K,L],[G,K,L,N],[G,K,N],[G,L],[G,L,N],[G,N],[K],[L]]),
        ground([C,D,E,F,J,M])
    )).
have(B,B,active,[],C,C,D,D).

:- true pred be(_A,B,_B,_C,_D,C,F,D,H)
   : ( mshare([[_A],[_A,B],[_A,B,D],[_A,D],[B],[B,D],[_B],[_C],[_D],[F],[D],[H]]),
       ground([C]), linear(_B), linear(_C), linear(_D), linear(F), linear(H) )
   => ( mshare([[B,_B],[B,_B,D,H],[D],[D,H]]),
        ground([_A,_C,_D,C,F]) ).

be(past+part,B,B,passive,[],C,C,D,D).
be(pres+part,B,C,D,[prog],E,F,G,H) :-
    true((
        mshare([[B],[B,G],[C],[D],[F],[G],[H]]),
        ground([E]),
        linear(C),
        linear(D),
        linear(F),
        linear(H)
    )),
    passive(B,C,D,E,F,G,H),
    true((
        mshare([[B,C],[B,C,G,H],[G],[G,H]]),
        ground([D,E,F])
    )).

:- true pred passive(_A,B,_B,C,D,E,F)
   : ( mshare([[_A],[_A,E],[B],[_B],[D],[E],[F]]),
       ground([C]), linear(B), linear(_B), linear(D), linear(F) )
   => ( mshare([[_A,B],[_A,B,E,F],[E],[E,F]]),
        ground([_B,C,D]) ).

passive(be,B,passive,C,D,E,F) :-
    true((
        mshare([[B],[D],[E],[F],[G],[H],[I]]),
        ground([C]),
        linear(B),
        linear(D),
        linear(F),
        linear(G),
        linear(H),
        linear(I)
    )),
    verb_form(B,past+part,G,H,C,D,E,F),
    true((
        mshare([[B,E],[B,E,F],[B,E,F,G],[B,E,F,G,H],[B,E,F,H],[B,E,G],[B,E,G,H],[B,E,H],[E],[E,F],[E,F,G],[E,F,G,H],[E,F,H],[E,G],[E,G,H],[E,H],[G],[H],[I]]),
        ground([C,D]),
        linear(I)
    )),
    verb_type(B,I),
    true((
        mshare([[E],[E,F],[E,F,G],[E,F,G,H],[E,F,H],[E,G],[E,G,H],[E,H],[G],[H]]),
        ground([B,C,D,I])
    )),
    passive(I),
    true((
        mshare([[E],[E,F],[E,F,G],[E,F,G,H],[E,F,H],[E,G],[E,G,H],[E,H],[G],[H]]),
        ground([B,C,D,I])
    )).
passive(B,B,active,C,C,D,D).

:- true pred participle(_A,F,C,G,H,I,J)
   : ( mshare([[_A],[F],[C],[H],[J]]),
       ground([G,I]), linear(_A), linear(F), linear(C), linear(H), linear(J) )
   => ground([_A,F,C,G,H,I,J]).

:- true pred participle(_A,F,C,G,H,I,J)
   : ( mshare([[_A],[F],[C],[H],[I],[J]]),
       ground([G]), linear(_A), linear(F), linear(C), linear(H), linear(J) )
   => ( mshare([[_A,I],[_A,I,J],[I],[I,J]]),
        ground([F,C,G,H]) ).

participle(verb(B,C,inf,D,E),F,C,G,H,I,J) :-
    true((mshare([[F],[C],[H],[I],[J],[B],[D],[E],[K],[L],[M],[N],[O],[P]]),ground([G]),linear(F),linear(C),linear(H),linear(J),linear(B),linear(D),linear(E),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P);mshare([[F],[C],[H],[J],[B],[D],[E],[K],[L],[M],[N],[O],[P]]),ground([G,I]),linear(F),linear(C),linear(H),linear(J),linear(B),linear(D),linear(E),linear(K),linear(L),linear(M),linear(N),linear(O),linear(P))),
    neg(K,E,G,L,I,M),
    true((mshare([[F],[C],[H],[I],[I,E],[I,E,K],[I,E,K,M],[I,E,M],[I,K],[I,K,M],[I,M],[J],[B],[D],[K],[N],[O],[P]]),ground([G,L]),linear(F),linear(C),linear(H),linear(J),linear(B),linear(D),linear(N),linear(O),linear(P);mshare([[F],[C],[H],[J],[B],[D],[K],[N],[O],[P]]),ground([G,I,E,L,M]),linear(F),linear(C),linear(H),linear(J),linear(B),linear(D),linear(N),linear(O),linear(P))),
    verb_form(B,N,O,P,L,H,M,J),
    true((mshare([[F],[C],[I],[I,J,B,E,K,M],[I,J,B,E,K,M,N],[I,J,B,E,K,M,N,O],[I,J,B,E,K,M,N,O,P],[I,J,B,E,K,M,N,P],[I,J,B,E,K,M,O],[I,J,B,E,K,M,O,P],[I,J,B,E,K,M,P],[I,J,B,E,M],[I,J,B,E,M,N],[I,J,B,E,M,N,O],[I,J,B,E,M,N,O,P],[I,J,B,E,M,N,P],[I,J,B,E,M,O],[I,J,B,E,M,O,P],[I,J,B,E,M,P],[I,J,B,K,M],[I,J,B,K,M,N],[I,J,B,K,M,N,O],[I,J,B,K,M,N,O,P],[I,J,B,K,M,N,P],[I,J,B,K,M,O],[I,J,B,K,M,O,P],[I,J,B,K,M,P],[I,J,B,M],[I,J,B,M,N],[I,J,B,M,N,O],[I,J,B,M,N,O,P],[I,J,B,M,N,P],[I,J,B,M,O],[I,J,B,M,O,P],[I,J,B,M,P],[I,J,E,K,M],[I,J,E,K,M,N],[I,J,E,K,M,N,O],[I,J,E,K,M,N,O,P],[I,J,E,K,M,N,P],[I,J,E,K,M,O],[I,J,E,K,M,O,P],[I,J,E,K,M,P],[I,J,E,M],[I,J,E,M,N],[I,J,E,M,N,O],[I,J,E,M,N,O,P],[I,J,E,M,N,P],[I,J,E,M,O],[I,J,E,M,O,P],[I,J,E,M,P],[I,J,K,M],[I,J,K,M,N],[I,J,K,M,N,O],[I,J,K,M,N,O,P],[I,J,K,M,N,P],[I,J,K,M,O],[I,J,K,M,O,P],[I,J,K,M,P],[I,J,M],[I,J,M,N],[I,J,M,N,O],[I,J,M,N,O,P],[I,J,M,N,P],[I,J,M,O],[I,J,M,O,P],[I,J,M,P],[I,B,E,K,M],[I,B,E,K,M,N],[I,B,E,K,M,N,O],[I,B,E,K,M,N,O,P],[I,B,E,K,M,N,P],[I,B,E,K,M,O],[I,B,E,K,M,O,P],[I,B,E,K,M,P],[I,B,E,M],[I,B,E,M,N],[I,B,E,M,N,O],[I,B,E,M,N,O,P],[I,B,E,M,N,P],[I,B,E,M,O],[I,B,E,M,O,P],[I,B,E,M,P],[I,B,K,M],[I,B,K,M,N],[I,B,K,M,N,O],[I,B,K,M,N,O,P],[I,B,K,M,N,P],[I,B,K,M,O],[I,B,K,M,O,P],[I,B,K,M,P],[I,B,M],[I,B,M,N],[I,B,M,N,O],[I,B,M,N,O,P],[I,B,M,N,P],[I,B,M,O],[I,B,M,O,P],[I,B,M,P],[I,E],[I,E,K],[I,E,K,M],[I,E,K,M,N],[I,E,K,M,N,O],[I,E,K,M,N,O,P],[I,E,K,M,N,P],[I,E,K,M,O],[I,E,K,M,O,P],[I,E,K,M,P],[I,E,M],[I,E,M,N],[I,E,M,N,O],[I,E,M,N,O,P],[I,E,M,N,P],[I,E,M,O],[I,E,M,O,P],[I,E,M,P],[I,K],[I,K,M],[I,K,M,N],[I,K,M,N,O],[I,K,M,N,O,P],[I,K,M,N,P],[I,K,M,O],[I,K,M,O,P],[I,K,M,P],[I,M],[I,M,N],[I,M,N,O],[I,M,N,O,P],[I,M,N,P],[I,M,O],[I,M,O,P],[I,M,P],[D],[K],[N],[O],[P]]),ground([G,H,L]),linear(F),linear(C),linear(D);mshare([[F],[C],[D],[K],[N],[O],[P]]),ground([G,H,I,J,B,E,L,M]),linear(F),linear(C),linear(D))),
    participle(N,C,D),
    true((mshare([[F],[I],[I,J,B,E,K,M],[I,J,B,E,K,M,O],[I,J,B,E,K,M,O,P],[I,J,B,E,K,M,P],[I,J,B,E,M],[I,J,B,E,M,O],[I,J,B,E,M,O,P],[I,J,B,E,M,P],[I,J,B,K,M],[I,J,B,K,M,O],[I,J,B,K,M,O,P],[I,J,B,K,M,P],[I,J,B,M],[I,J,B,M,O],[I,J,B,M,O,P],[I,J,B,M,P],[I,J,E,K,M],[I,J,E,K,M,O],[I,J,E,K,M,O,P],[I,J,E,K,M,P],[I,J,E,M],[I,J,E,M,O],[I,J,E,M,O,P],[I,J,E,M,P],[I,J,K,M],[I,J,K,M,O],[I,J,K,M,O,P],[I,J,K,M,P],[I,J,M],[I,J,M,O],[I,J,M,O,P],[I,J,M,P],[I,B,E,K,M],[I,B,E,K,M,O],[I,B,E,K,M,O,P],[I,B,E,K,M,P],[I,B,E,M],[I,B,E,M,O],[I,B,E,M,O,P],[I,B,E,M,P],[I,B,K,M],[I,B,K,M,O],[I,B,K,M,O,P],[I,B,K,M,P],[I,B,M],[I,B,M,O],[I,B,M,O,P],[I,B,M,P],[I,E],[I,E,K],[I,E,K,M],[I,E,K,M,O],[I,E,K,M,O,P],[I,E,K,M,P],[I,E,M],[I,E,M,O],[I,E,M,O,P],[I,E,M,P],[I,K],[I,K,M],[I,K,M,O],[I,K,M,O,P],[I,K,M,P],[I,M],[I,M,O],[I,M,O,P],[I,M,P],[K],[O],[P]]),ground([C,G,H,D,L,N]),linear(F);mshare([[F],[K],[O],[P]]),ground([C,G,H,I,J,B,D,E,L,M,N]),linear(F))),
    verb_type(B,F),
    true((mshare([[I],[I,J,E,K,M],[I,J,E,K,M,O],[I,J,E,K,M,O,P],[I,J,E,K,M,P],[I,J,E,M],[I,J,E,M,O],[I,J,E,M,O,P],[I,J,E,M,P],[I,J,K,M],[I,J,K,M,O],[I,J,K,M,O,P],[I,J,K,M,P],[I,J,M],[I,J,M,O],[I,J,M,O,P],[I,J,M,P],[I,E],[I,E,K],[I,E,K,M],[I,E,K,M,O],[I,E,K,M,O,P],[I,E,K,M,P],[I,E,M],[I,E,M,O],[I,E,M,O,P],[I,E,M,P],[I,K],[I,K,M],[I,K,M,O],[I,K,M,O,P],[I,K,M,P],[I,M],[I,M,O],[I,M,O,P],[I,M,P],[K],[O],[P]]),ground([F,C,G,H,B,D,L,N]);mshare([[K],[O],[P]]),ground([F,C,G,H,I,J,B,D,E,L,M,N]))).

:- true pred passive(_A)
   : ground([_A])
   => ground([_A]).

passive(B+trans).
passive(B+ditrans).

:- true pred participle(_A,_B,_C)
   : ( mshare([[_A],[_B],[_C]]),
       linear(_B), linear(_C) )
   => ground([_A,_B,_C]).

participle(pres+part,active,[prog]).
participle(past+part,passive,[]).

:- true pred close(B,_A,C,D)
   : ( mshare([[_A],[C],[D]]),
       ground([B]), linear(_A), linear(D) )
   => ( mshare([[C],[C,D]]),
        ground([B,_A]) ).

close(B,B,C,D) :-
    true((
        mshare([[C],[D]]),
        ground([B]),
        linear(D)
    )),
    virtual(close,C,D),
    true((
        mshare([[C],[C,D]]),
        ground([B])
    )).

:- true pred myopen(B,_A,C,_B)
   : ( mshare([[_A],[_B]]),
       ground([B,C]), linear(_A), linear(_B) )
   => ground([B,_A,C,_B]).

:- true pred myopen(B,_A,C,_B)
   : ( mshare([[_A],[C],[_B]]),
       ground([B]), linear(_A), linear(_B) )
   => ( mshare([[C,_B]]),
        ground([B,_A]) ).

myopen(B,B,C,x(gap,nonterminal,close,C)).

:- true pred verb_args(B,D,E,F,G,H,I,J,K)
   : ( mshare([[B],[B,D],[B,D,J],[B,J],[D],[D,J],[E],[G],[I],[J],[K]]),
       ground([F,H]), linear(E), linear(G), linear(I), linear(K) )
   => ( mshare([[B],[B,D],[B,D,E,G,J],[B,D,E,G,J,K],[B,D,E,J],[B,D,E,J,K],[B,D,G,J],[B,D,G,J,K],[B,D,J],[B,D,J,K],[B,E,G,J],[B,E,G,J,K],[B,E,J],[B,E,J,K],[B,G,J],[B,G,J,K],[B,J],[B,J,K],[D],[D,E,G,J],[D,E,G,J,K],[D,E,J],[D,E,J,K],[D,G,J],[D,G,J,K],[D,J],[D,J,K],[E],[E,G],[E,G,J],[E,G,J,K],[E,G,K],[E,J],[E,J,K],[E,K],[G],[G,J],[G,J,K],[G,K],[J],[J,K],[K]]),
        ground([F,H,I]) ).

verb_args(B+C,D,E,F,G,H,I,J,K) :-
    true((
        mshare([[D],[D,J],[D,J,B],[D,J,B,C],[D,J,C],[D,B],[D,B,C],[D,C],[E],[G],[I],[J],[J,B],[J,B,C],[J,C],[K],[B],[B,C],[C],[L],[M],[N],[O]]),
        ground([F,H]),
        linear(E),
        linear(G),
        linear(I),
        linear(K),
        linear(L),
        linear(M),
        linear(N),
        linear(O)
    )),
    advs(E,L,M,H,N,J,O),
    true((
        mshare([[D],[D,J],[D,J,B],[D,J,B,C],[D,J,B,C,O],[D,J,B,O],[D,J,C],[D,J,C,O],[D,J,O],[D,B],[D,B,C],[D,C],[E,L],[G],[I],[J],[J,B],[J,B,C],[J,B,C,O],[J,B,O],[J,C],[J,C,O],[J,O],[K],[B],[B,C],[C],[M]]),
        ground([F,H,N]),
        linear(E),
        linear(G),
        linear(I),
        linear(K),
        linear(L),
        linear(M)
    )),
    verb_args(C,D,L,F,G,N,I,O,K),
    true((
        mshare([[D],[D,E,G,J,K,B,C,L,O],[D,E,G,J,K,B,L,O],[D,E,G,J,K,C,L,O],[D,E,G,J,K,L,O],[D,E,G,J,B,C,L,O],[D,E,G,J,B,L,O],[D,E,G,J,C,L,O],[D,E,G,J,L,O],[D,E,J,K,B,C,L,O],[D,E,J,K,B,L,O],[D,E,J,K,C,L,O],[D,E,J,K,L,O],[D,E,J,B,C,L,O],[D,E,J,B,L,O],[D,E,J,C,L,O],[D,E,J,L,O],[D,G,J,K,B,C,O],[D,G,J,K,B,O],[D,G,J,K,C,O],[D,G,J,K,O],[D,G,J,B,C,O],[D,G,J,B,O],[D,G,J,C,O],[D,G,J,O],[D,J],[D,J,K,B,C,O],[D,J,K,B,O],[D,J,K,C,O],[D,J,K,O],[D,J,B],[D,J,B,C],[D,J,B,C,O],[D,J,B,O],[D,J,C],[D,J,C,O],[D,J,O],[D,B],[D,B,C],[D,C],[E,G,J,K,B,C,L,O],[E,G,J,K,B,L,O],[E,G,J,K,C,L,O],[E,G,J,K,L,O],[E,G,J,B,C,L,O],[E,G,J,B,L,O],[E,G,J,C,L,O],[E,G,J,L,O],[E,G,K,L],[E,G,L],[E,J,K,B,C,L,O],[E,J,K,B,L,O],[E,J,K,C,L,O],[E,J,K,L,O],[E,J,B,C,L,O],[E,J,B,L,O],[E,J,C,L,O],[E,J,L,O],[E,K,L],[E,L],[G],[G,J,K,B,C,O],[G,J,K,B,O],[G,J,K,C,O],[G,J,K,O],[G,J,B,C,O],[G,J,B,O],[G,J,C,O],[G,J,O],[G,K],[J],[J,K,B,C,O],[J,K,B,O],[J,K,C,O],[J,K,O],[J,B],[J,B,C],[J,B,C,O],[J,B,O],[J,C],[J,C,O],[J,O],[K],[B],[B,C],[C],[M]]),
        ground([F,H,I,N]),
        linear(M)
    )).
verb_args(trans,active,[arg(dir,B)],C,D,E,F,G,H) :-
    true((
        mshare([[D],[F],[G],[H],[B]]),
        ground([C,E]),
        linear(D),
        linear(F),
        linear(H),
        linear(B)
    )),
    verb_arg(np,B,D,E,F,G,H),
    true((
        mshare([[D,G],[D,G,H],[D,G,H,B],[D,G,B],[G],[G,H],[G,H,B],[G,B],[H],[H,B],[B]]),
        ground([C,E,F])
    )).
verb_args(ditrans,B,[arg(C,D)|E],F,G,H,I,J,K) :-
    true((
        mshare([[B],[B,J],[G],[I],[J],[K],[E],[C],[D],[L],[M],[N]]),
        ground([F,H]),
        linear(G),
        linear(I),
        linear(K),
        linear(E),
        linear(C),
        linear(D),
        linear(L),
        linear(M),
        linear(N)
    )),
    verb_arg(np,D,L,H,M,J,N),
    true((
        mshare([[B],[B,J],[B,J,D],[B,J,D,L],[B,J,D,L,N],[B,J,D,N],[B,J,L],[B,J,L,N],[B,J,N],[G],[I],[J],[J,D],[J,D,L],[J,D,L,N],[J,D,N],[J,L],[J,L,N],[J,N],[K],[E],[C],[D],[D,N],[N]]),
        ground([F,H,M]),
        linear(G),
        linear(I),
        linear(K),
        linear(E),
        linear(C)
    )),
    object(C,E,L,G,M,I,N,K),
    true((
        mshare([[B],[B,G,J,K,E,D,N],[B,G,J,K,E,N],[B,G,J,K,D,N],[B,G,J,K,N],[B,G,J,E,D,N],[B,G,J,E,N],[B,G,J,D,N],[B,G,J,N],[B,J],[B,J,K,E,D,N],[B,J,K,E,N],[B,J,K,D,N],[B,J,K,N],[B,J,E,D,N],[B,J,E,N],[B,J,D],[B,J,D,N],[B,J,N],[G,J,K,E,D,N],[G,J,K,E,N],[G,J,K,D,N],[G,J,K,N],[G,J,E,D,N],[G,J,E,N],[G,J,D,N],[G,J,N],[G,K,E,D,N],[G,K,E,N],[G,K,D,N],[G,K,N],[G,E,D,N],[G,E,N],[G,D,N],[G,N],[J],[J,K,E,D,N],[J,K,E,N],[J,K,D,N],[J,K,N],[J,E,D,N],[J,E,N],[J,D],[J,D,N],[J,N],[K],[K,E],[K,E,D,N],[K,E,N],[K,D,N],[K,N],[E],[E,D,N],[E,N],[D],[D,N],[N]]),
        ground([F,H,I,C,L,M])
    )).
verb_args(be,B,[void],C,C,D,E,F,G) :-
    true((
        mshare([[B],[B,F],[E],[F],[G]]),
        ground([C,D]),
        linear(E),
        linear(G)
    )),
    terminal(there,D,E,F,G),
    true((
        mshare([[B],[B,F],[B,F,G],[F],[F,G]]),
        ground([C,D,E])
    )).
verb_args(be,B,[arg(predicate,C)],D,E,F,G,H,I) :-
    true((
        mshare([[B],[B,H],[E],[G],[H],[I],[C],[J]]),
        ground([D,F]),
        linear(E),
        linear(G),
        linear(I),
        linear(C),
        linear(J)
    )),
    pred_conj(J,C,E,F,G,H,I),
    true((
        mshare([[B],[B,E,H],[B,E,H,I],[B,E,H,I,C],[B,E,H,C],[B,H],[B,H,I],[B,H,I,C],[B,H,C],[E],[E,H],[E,H,I],[E,H,I,C],[E,H,C],[E,I],[E,I,C],[E,C],[H],[H,I],[H,I,C],[H,C],[I],[I,C],[C],[C,J],[J]]),
        ground([D,F,G])
    )).
verb_args(be,B,[arg(dir,C)],D,E,F,G,H,I) :-
    true((
        mshare([[B],[B,H],[E],[G],[H],[I],[C]]),
        ground([D,F]),
        linear(E),
        linear(G),
        linear(I),
        linear(C)
    )),
    verb_arg(np,C,E,F,G,H,I),
    true((
        mshare([[B],[B,E,H],[B,E,H,I],[B,E,H,I,C],[B,E,H,C],[B,H],[B,H,I],[B,H,I,C],[B,H,C],[E,H],[E,H,I],[E,H,I,C],[E,H,C],[H],[H,I],[H,I,C],[H,C],[I],[I,C],[C]]),
        ground([D,F,G])
    )).
verb_args(have,active,[arg(dir,B)],C,D,E,F,G,H) :-
    true((
        mshare([[D],[F],[G],[H],[B]]),
        ground([C,E]),
        linear(D),
        linear(F),
        linear(H),
        linear(B)
    )),
    verb_arg(np,B,D,E,F,G,H),
    true((
        mshare([[D,G],[D,G,H],[D,G,H,B],[D,G,B],[G],[G,H],[G,H,B],[G,B],[H],[H,B],[B]]),
        ground([C,E,F])
    )).
verb_args(B,C,[],D,D,E,E,F,F) :-
    true((
        mshare([[B],[B,C],[B,C,F],[B,F],[C],[C,F],[F]]),
        ground([D,E])
    )),
    no_args(B),
    true((
        mshare([[C],[C,F],[F]]),
        ground([B,D,E])
    )).

:- true pred object(B,C,D,E,F,G,H,I)
   : ( mshare([[B],[C],[D],[D,H],[E],[G],[H],[I]]),
       ground([F]), linear(B), linear(C), linear(E), linear(G), linear(I) )
   => ( mshare([[C],[C,E,H],[C,E,H,I],[C,H],[C,H,I],[C,I],[E,H],[E,H,I],[H],[H,I],[I]]),
        ground([B,D,F,G]) ).

object(B,C,D,E,F,G,H,I) :-
    true((
        mshare([[B],[C],[D],[D,H],[E],[G],[H],[I],[J],[K],[L],[M],[N]]),
        ground([F]),
        linear(B),
        linear(C),
        linear(E),
        linear(G),
        linear(I),
        linear(J),
        linear(K),
        linear(L),
        linear(M),
        linear(N)
    )),
    adv(J),
    true((
        mshare([[B],[C],[D],[D,H],[E],[G],[H],[I],[K],[L],[M],[N]]),
        ground([F,J]),
        linear(B),
        linear(C),
        linear(E),
        linear(G),
        linear(I),
        linear(K),
        linear(L),
        linear(M),
        linear(N)
    )),
    minus(J,D,K),
    true((
        mshare([[B],[C],[E],[G],[H],[I],[L],[M],[N]]),
        ground([D,F,J,K]),
        linear(B),
        linear(C),
        linear(E),
        linear(G),
        linear(I),
        linear(L),
        linear(M),
        linear(N)
    )),
    advs(C,L,K,F,M,H,N),
    true((
        mshare([[B],[C,L],[E],[G],[H],[H,N],[I]]),
        ground([D,F,J,K,M]),
        linear(B),
        linear(C),
        linear(E),
        linear(G),
        linear(I),
        linear(L)
    )),
    obj(B,L,D,E,M,G,N,I),
    true((
        mshare([[C,E,H,I,L,N],[C,E,H,L,N],[C,H,I,L,N],[C,H,L,N],[C,I,L],[C,L],[E,H,I,N],[E,H,N],[H],[H,I,N],[H,N],[I]]),
        ground([B,D,F,G,J,K,M])
    )).

:- true pred obj(_A,_B,C,D,E,F,G,H)
   : ( mshare([[_A],[_B],[D],[F],[G],[H]]),
       ground([C,E]), linear(_A), linear(_B), linear(D), linear(F), linear(H) )
   => ( mshare([[_B],[_B,D,G],[_B,D,G,H],[_B,G],[_B,G,H],[_B,H],[D,G],[D,G,H],[G],[G,H],[H]]),
        ground([_A,C,E,F]) ).

obj(ind,[arg(dir,B)],C,D,E,F,G,H) :-
    true((
        mshare([[D],[F],[G],[H],[B]]),
        ground([C,E]),
        linear(D),
        linear(F),
        linear(H),
        linear(B)
    )),
    verb_arg(np,B,D,E,F,G,H),
    true((
        mshare([[D,G],[D,G,H],[D,G,H,B],[D,G,B],[G],[G,H],[G,H,B],[G,B],[H],[H,B],[B]]),
        ground([C,E,F])
    )).
obj(dir,[],B,B,C,C,D,D).

:- true pred pred_conj(B,C,D,E,F,G,H)
   : ( mshare([[B],[C],[D],[F],[G],[H]]),
       ground([E]), linear(B), linear(C), linear(D), linear(F), linear(H) )
   => ( mshare([[B],[B,C],[C],[C,D],[C,D,G],[C,D,G,H],[C,D,H],[C,G],[C,G,H],[C,H],[D],[D,G],[D,G,H],[D,H],[G],[G,H],[H]]),
        ground([E,F]) ).

:- true pred pred_conj(B,C,D,E,F,G,H)
   : ( mshare([[B],[C],[D],[F],[G],[H]]),
       ground([E]), linear(C), linear(D), linear(F), linear(H) )
   => ( mshare([[B],[B,C],[C],[C,D],[C,D,G],[C,D,G,H],[C,D,H],[C,G],[C,G,H],[C,H],[D],[D,G],[D,G,H],[D,H],[G],[G,H],[H]]),
        ground([E,F]) ).

pred_conj(B,C,D,E,F,G,H) :-
    true((mshare([[B],[C],[D],[F],[G],[H],[I],[J],[K],[L],[M]]),ground([E]),linear(B),linear(C),linear(D),linear(F),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M);mshare([[B],[C],[D],[F],[G],[H],[I],[J],[K],[L],[M]]),ground([E]),linear(C),linear(D),linear(F),linear(H),linear(I),linear(J),linear(K),linear(L),linear(M))),
    predicate(I,J,K,E,L,G,M),
    true((mshare([[B],[C],[D],[F],[G],[G,I],[G,I,J],[G,I,J,K],[G,I,J,K,M],[G,I,J,M],[G,I,K],[G,I,K,M],[G,I,M],[G,J],[G,J,K],[G,J,K,M],[G,J,M],[G,K],[G,K,M],[G,M],[H],[I],[J],[J,M],[M]]),ground([E,L]),linear(B),linear(C),linear(D),linear(F),linear(H);mshare([[B],[C],[D],[F],[G],[G,I],[G,I,J],[G,I,J,K],[G,I,J,K,M],[G,I,J,M],[G,I,K],[G,I,K,M],[G,I,M],[G,J],[G,J,K],[G,J,K,M],[G,J,M],[G,K],[G,K,M],[G,M],[H],[I],[J],[J,M],[M]]),ground([E,L]),linear(C),linear(D),linear(F),linear(H))),
    pred_rest(B,J,C,K,D,L,F,M,H),
    true((
        mshare([[B],[B,C],[C],[C,D],[C,D,G,H,I,J,K,M],[C,D,G,H,I,J,M],[C,D,G,H,I,K,M],[C,D,G,H,I,M],[C,D,G,H,J,K,M],[C,D,G,H,J,M],[C,D,G,H,K,M],[C,D,G,H,M],[C,D,G,I,J,K],[C,D,G,I,J,K,M],[C,D,G,I,J,M],[C,D,G,I,K,M],[C,D,G,I,M],[C,D,G,J,K],[C,D,G,J,K,M],[C,D,G,J,M],[C,D,G,K,M],[C,D,G,M],[C,D,H],[C,D,H,J,M],[C,D,H,M],[C,D,J,M],[C,D,M],[C,G,H,I,J,K,M],[C,G,H,I,J,M],[C,G,H,I,K,M],[C,G,H,I,M],[C,G,H,J,K,M],[C,G,H,J,M],[C,G,H,K,M],[C,G,H,M],[C,G,I,J],[C,G,I,J,K],[C,G,I,J,K,M],[C,G,I,J,M],[C,G,I,K,M],[C,G,I,M],[C,G,J],[C,G,J,K],[C,G,J,K,M],[C,G,J,M],[C,G,K,M],[C,G,M],[C,H],[C,H,J,M],[C,H,M],[C,J],[C,J,M],[C,M],[D],[D,G,H,I,K,M],[D,G,H,I,M],[D,G,H,K,M],[D,G,H,M],[D,G,I,K],[D,G,I,K,M],[D,G,I,M],[D,G,K],[D,G,K,M],[D,G,M],[D,H],[D,H,M],[D,M],[G],[G,H,I,K,M],[G,H,I,M],[G,H,K,M],[G,H,M],[G,I],[G,I,K],[G,I,K,M],[G,I,M],[G,K],[G,K,M],[G,M],[H],[H,M],[I],[M]]),
        ground([E,F,L])
    )).

:- true pred pred_rest(B,C,D,E,F,G,H,I,J)
   : ( mshare([[B],[C],[C,E],[C,E,I],[C,I],[D],[E],[E,I],[F],[H],[I],[J]]),
       ground([G]), linear(D), linear(F), linear(H), linear(J) )
   => ( mshare([[B],[B,D],[C,D],[C,D,E],[C,D,E,F],[C,D,E,F,I],[C,D,E,F,I,J],[C,D,E,I],[C,D,E,I,J],[C,D,F,I],[C,D,F,I,J],[C,D,I],[C,D,I,J],[D],[D,E,F,I],[D,E,F,I,J],[D,E,I],[D,E,I,J],[D,F],[D,F,I],[D,F,I,J],[D,F,J],[D,I],[D,I,J],[D,J],[E],[E,F],[E,F,I],[E,F,I,J],[E,I],[E,I,J],[F],[F,I],[F,I,J],[F,J],[I],[I,J],[J]]),
        ground([G,H]) ).

:- true pred pred_rest(B,C,D,E,F,G,H,I,J)
   : ( mshare([[B],[C],[C,E],[C,E,I],[C,I],[D],[E],[E,I],[F],[H],[I],[J]]),
       ground([G]), linear(B), linear(D), linear(F), linear(H), linear(J) )
   => ( mshare([[B],[B,D],[C,D],[C,D,E],[C,D,E,F],[C,D,E,F,I],[C,D,E,F,I,J],[C,D,E,I],[C,D,E,I,J],[C,D,F,I],[C,D,F,I,J],[C,D,I],[C,D,I,J],[D],[D,E,F,I],[D,E,F,I,J],[D,E,I],[D,E,I,J],[D,F],[D,F,I],[D,F,I,J],[D,F,J],[D,I],[D,I,J],[D,J],[E],[E,F],[E,F,I],[E,F,I,J],[E,I],[E,I,J],[F],[F,I],[F,I,J],[F,J],[I],[I,J],[J]]),
        ground([G,H]) ).

pred_rest(B,C,D,E,F,G,H,I,J) :-
    true((mshare([[B],[C],[C,E],[C,E,I],[C,I],[D],[E],[E,I],[F],[H],[I],[J],[K],[L],[M],[N]]),ground([G]),linear(B),linear(D),linear(F),linear(H),linear(J),linear(K),linear(L),linear(M),linear(N);mshare([[B],[C],[C,E],[C,E,I],[C,I],[D],[E],[E,I],[F],[H],[I],[J],[K],[L],[M],[N]]),ground([G]),linear(D),linear(F),linear(H),linear(J),linear(K),linear(L),linear(M),linear(N))),
    conj(B,K,C,L,D,G,M,I,N),
    true((
        mshare([[B,D,K],[C,D],[C,D,E],[C,D,E,I],[C,D,E,I,N],[C,D,I],[C,D,I,N],[D,L],[E],[E,I],[E,I,N],[F],[H],[I],[I,N],[J]]),
        ground([G,M]),
        linear(F),
        linear(H),
        linear(J),
        linear(L)
    )),
    pred_conj(K,L,F,M,H,N,J),
    true((
        mshare([[B,D,K],[B,D,K,L],[C,D],[C,D,E],[C,D,E,F,I,J,L,N],[C,D,E,F,I,J,N],[C,D,E,F,I,L,N],[C,D,E,F,I,N],[C,D,E,I],[C,D,E,I,J,L,N],[C,D,E,I,J,N],[C,D,E,I,L,N],[C,D,E,I,N],[C,D,F,I,J,L,N],[C,D,F,I,J,N],[C,D,F,I,L,N],[C,D,F,I,N],[C,D,I],[C,D,I,J,L,N],[C,D,I,J,N],[C,D,I,L,N],[C,D,I,N],[D,E,F,I,J,L,N],[D,E,F,I,L,N],[D,E,I,J,L,N],[D,E,I,L,N],[D,F,I,J,L,N],[D,F,I,L,N],[D,F,J,L],[D,F,L],[D,I,J,L,N],[D,I,L,N],[D,J,L],[D,L],[E],[E,F,I,J,N],[E,F,I,N],[E,I],[E,I,J,N],[E,I,N],[F],[F,I,J,N],[F,I,N],[F,J],[I],[I,J,N],[I,N],[J]]),
        ground([G,H,M])
    )).
pred_rest(B,C,C,D,D,E,E,F,F).

:- true pred verb_arg(_A,B,C,D,E,F,G)
   : ( (_A=np),
       mshare([[B],[C],[E],[F],[G]]),
       ground([D]), linear(B), linear(C), linear(E), linear(G) )
   => ( mshare([[B],[B,C,F],[B,C,F,G],[B,F],[B,F,G],[B,G],[C,F],[C,F,G],[F],[F,G],[G]]),
        ground([D,E]) ).

verb_arg(np,B,C,D,E,F,G) :-
    true((
        mshare([[B],[C],[E],[F],[G],[H],[I],[J],[K]]),
        ground([D]),
        linear(B),
        linear(C),
        linear(E),
        linear(G),
        linear(H),
        linear(I),
        linear(J),
        linear(K)
    )),
    s_all(H),
    true((
        mshare([[B],[C],[E],[F],[G],[I],[J],[K]]),
        ground([D,H]),
        linear(B),
        linear(C),
        linear(E),
        linear(G),
        linear(I),
        linear(J),
        linear(K)
    )),
    verb_case(I),
    true((
        mshare([[B],[C],[E],[F],[G],[J],[K]]),
        ground([D,H,I]),
        linear(B),
        linear(C),
        linear(E),
        linear(G),
        linear(J),
        linear(K)
    )),
    np(B,J,I,K,compl,H,C,D,E,F,G),
    true((
        mshare([[B],[B,C,F],[B,C,F,G],[B,C,F,G,J],[B,C,F,G,J,K],[B,C,F,G,K],[B,C,F,J],[B,C,F,J,K],[B,C,F,K],[B,F],[B,F,G],[B,F,G,J],[B,F,G,J,K],[B,F,G,K],[B,F,J],[B,F,J,K],[B,F,K],[B,G],[B,G,J],[B,J],[C,F],[C,F,G],[C,F,G,J],[C,F,G,J,K],[C,F,G,K],[C,F,J],[C,F,J,K],[C,F,K],[F],[F,G],[F,G,J],[F,G,J,K],[F,G,K],[F,J],[F,J,K],[F,K],[G],[J]]),
        ground([D,E,H,I])
    )).

:- true pred advs(B,D,E,F,G,H,I)
   : ( mshare([[B],[D],[G],[H],[I]]),
       ground([E,F]), linear(B), linear(D), linear(G), linear(I) )
   => ( mshare([[B,D],[H],[H,I]]),
        ground([E,F,G]), linear(B), linear(D) ).

:- true pred advs(B,D,E,F,G,H,I)
   : ( mshare([[B],[D],[E],[G],[H],[I]]),
       ground([F]), linear(B), linear(D), linear(E), linear(G), linear(I) )
   => ( mshare([[B,D],[E],[H],[H,I]]),
        ground([F,G]), linear(B), linear(D), linear(E) ).

advs([B|C],D,E,F,G,H,I) :-
    true((mshare([[D],[E],[G],[H],[I],[B],[C],[J],[K]]),ground([F]),linear(D),linear(E),linear(G),linear(I),linear(B),linear(C),linear(J),linear(K);mshare([[D],[G],[H],[I],[B],[C],[J],[K]]),ground([E,F]),linear(D),linear(G),linear(I),linear(B),linear(C),linear(J),linear(K))),
    is_adv(E),
    true((mshare([[D],[E],[G],[H],[I],[B],[C],[J],[K]]),ground([F]),linear(D),linear(E),linear(G),linear(I),linear(B),linear(C),linear(J),linear(K);mshare([[D],[G],[H],[I],[B],[C],[J],[K]]),ground([E,F]),linear(D),linear(G),linear(I),linear(B),linear(C),linear(J),linear(K))),
    adverb(B,F,J,H,K),
    true((mshare([[D],[E],[G],[H],[H,K],[I],[C]]),ground([F,B,J]),linear(D),linear(E),linear(G),linear(I),linear(C);mshare([[D],[G],[H],[H,K],[I],[C]]),ground([E,F,B,J]),linear(D),linear(G),linear(I),linear(C))),
    advs(C,D,E,J,G,K,I),
    true((mshare([[D,C],[E],[H],[H,I,K],[H,K]]),ground([F,G,B,J]),linear(D),linear(E),linear(C);mshare([[D,C],[H],[H,I,K],[H,K]]),ground([E,F,G,B,J]),linear(D),linear(C))).
advs(B,B,C,D,D,E,E).

:- true pred adj_phrase(B,C,D,E,F,G)
   : ( mshare([[B],[C],[E],[G]]),
       ground([D,F]), linear(B), linear(C), linear(E), linear(G) )
   => ( mshare([[B],[B,G],[G]]),
        ground([C,D,E,F]) ).

:- true pred adj_phrase(B,C,D,E,F,G)
   : ( mshare([[B],[C],[E],[F],[G]]),
       ground([D]), linear(B), linear(C), linear(E), linear(G) )
   => ( mshare([[B],[B,C,F],[B,C,F,G],[B,F],[B,F,G],[B,G],[C,F],[C,F,G],[F],[F,G],[G]]),
        ground([D,E]) ).

adj_phrase(B,C,D,E,F,G) :-
    true((mshare([[B],[C],[E],[F],[G],[H]]),ground([D]),linear(B),linear(C),linear(E),linear(G),linear(H);mshare([[B],[C],[E],[G],[H]]),ground([D,F]),linear(B),linear(C),linear(E),linear(G),linear(H))),
    adj(H,B,D,E,F,G),
    true((mshare([[C]]),ground([B,D,E,F,G,H]),linear(C);mshare([[C],[F],[F,G]]),ground([B,D,E,H]),linear(C))),
    empty(C),
    true((mshare([[F],[F,G]]),ground([B,C,D,E,H]);ground([B,C,D,E,F,G,H]))).
adj_phrase(B,C,D,E,F,G) :-
    true((mshare([[B],[C],[E],[F],[G]]),ground([D]),linear(B),linear(C),linear(E),linear(G);mshare([[B],[C],[E],[G]]),ground([D,F]),linear(B),linear(C),linear(E),linear(G))),
    comp_phrase(B,C,D,E,F,G),
    true((mshare([[B],[B,C,F],[B,C,F,G],[B,F],[B,F,G],[B,G],[C,F],[C,F,G],[F],[F,G],[G]]),ground([D,E]);mshare([[B],[B,G],[G]]),ground([C,D,E,F]))).

:- true pred no_args(_A)
   : mshare([[_A]])
   => ground([_A]).

no_args(trans).
no_args(ditrans).
no_args(intrans).

:- true pred conj(_A,_B,E,F,_C,G,H,I,J)
   : ( mshare([[_A],[_B],[E],[E,I],[F],[_C],[H],[I],[J]]),
       ground([G]), linear(_A), linear(_B), linear(F), linear(_C), linear(H), linear(J) )
   => ( mshare([[_A,_B,_C],[E,_C],[E,_C,I],[E,_C,I,J],[F,_C],[I],[I,J]]),
        ground([G,H]), linear(F) ).

:- true pred conj(_A,_B,E,F,_C,G,H,I,J)
   : ( mshare([[_A],[_B],[E],[E,I],[F],[_C],[H],[I],[J]]),
       ground([G]), linear(_B), linear(F), linear(_C), linear(H), linear(J) )
   => ( mshare([[_A,_B,_C],[E,_C],[E,_C,I],[E,_C,I,J],[F,_C],[I],[I,J]]),
        ground([G,H]), linear(F) ).

conj(conj(B,C),conj(B,D),E,F,conj(B,E,F),G,H,I,J) :-
    true((mshare([[E],[E,I],[F],[H],[I],[J],[B],[B,C],[C],[D]]),ground([G]),linear(F),linear(H),linear(J),linear(D);mshare([[E],[E,I],[F],[H],[I],[J],[B],[C],[D]]),ground([G]),linear(F),linear(H),linear(J),linear(B),linear(C),linear(D))),
    conj(B,C,D,G,H,I,J),
    true((
        mshare([[E],[E,I],[E,I,J],[F],[I],[I,J],[B]]),
        ground([G,H,C,D]),
        linear(F)
    )).

:- true pred noun(B,C,D,E,F,G)
   : ( mshare([[B],[C],[C,F],[E],[F],[G]]),
       ground([D]), linear(B), linear(E), linear(G) )
   => ( mshare([[C],[C,F],[C,F,G],[F],[F,G]]),
        ground([B,D,E]) ).

:- true pred noun(B,C,D,E,F,G)
   : ( mshare([[B],[C],[E],[G]]),
       ground([D,F]), linear(B), linear(E), linear(G) )
   => ( mshare([[C]]),
        ground([B,D,E,F,G]) ).

noun(B,C,D,E,F,G) :-
    true((mshare([[B],[C],[C,F],[E],[F],[G],[H]]),ground([D]),linear(B),linear(E),linear(G),linear(H);mshare([[B],[C],[E],[G],[H]]),ground([D,F]),linear(B),linear(E),linear(G),linear(H))),
    terminal(H,D,E,F,G),
    true((mshare([[B],[C]]),ground([D,E,F,G,H]),linear(B);mshare([[B],[C],[C,F],[C,F,G],[C,F,G,H],[C,F,H],[F],[F,G],[F,G,H],[F,H]]),ground([D,E]),linear(B))),
    noun_form(H,B,C),
    true((mshare([[C]]),ground([B,D,E,F,G,H]);mshare([[C],[C,F],[C,F,G],[F],[F,G]]),ground([B,D,E,H]))).

:- true pred adj(B,_A,D,E,F,G)
   : ( (B=quant),
       mshare([[_A],[E],[F],[G]]),
       ground([D]), linear(_A), linear(E), linear(G) )
   => ( mshare([[F],[F,G]]),
        ground([_A,D,E]) ).

:- true pred adj(B,_A,D,E,F,G)
   : ( (B=quant),
       mshare([[_A],[E],[G]]),
       ground([D,F]), linear(_A), linear(E), linear(G) )
   => ground([_A,D,E,F,G]).

:- true pred adj(B,_A,D,E,F,G)
   : ( mshare([[B],[_A],[E],[F],[G]]),
       ground([D]), linear(B), linear(_A), linear(E), linear(G) )
   => ( mshare([[F],[F,G]]),
        ground([B,_A,D,E]) ).

:- true pred adj(B,_A,D,E,F,G)
   : ( mshare([[B],[_A],[E],[G]]),
       ground([D,F]), linear(B), linear(_A), linear(E), linear(G) )
   => ground([B,_A,D,E,F,G]).

adj(B,adj(C),D,E,F,G) :-
    true((mshare([[B],[E],[F],[G],[C]]),ground([D]),linear(B),linear(E),linear(G),linear(C);mshare([[B],[E],[G],[C]]),ground([D,F]),linear(B),linear(E),linear(G),linear(C);mshare([[E],[F],[G],[C]]),ground([B,D]),linear(E),linear(G),linear(C);mshare([[E],[G],[C]]),ground([B,D,F]),linear(E),linear(G),linear(C))),
    terminal(C,D,E,F,G),
    true((mshare([[B]]),ground([D,E,F,G,C]),linear(B);mshare([[B],[F],[F,G],[F,G,C],[F,C]]),ground([D,E]),linear(B);mshare([[F],[F,G],[F,G,C],[F,C]]),ground([B,D,E]);ground([B,D,E,F,G,C]))),
    adj(C,B),
    true((mshare([[F],[F,G]]),ground([B,D,E,C]);ground([B,D,E,F,G,C]))).

:- true pred prep(_A,C,D,E,F)
   : ( mshare([[_A],[D],[E],[F]]),
       ground([C]), linear(_A), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([_A,C,D]) ).

:- true pred prep(_A,C,D,E,F)
   : ( mshare([[_A],[D],[F]]),
       ground([C,E]), linear(_A), linear(D), linear(F) )
   => ground([_A,C,D,E,F]).

:- true pred prep(_A,C,D,E,F)
   : ( mshare([[D],[F]]),
       ground([_A,C,E]), linear(D), linear(F) )
   => ground([_A,C,D,E,F]).

:- true pred prep(_A,C,D,E,F)
   : ( mshare([[D],[E],[F]]),
       ground([_A,C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([_A,C,D]) ).

prep(prep(B),C,D,E,F) :-
    true((mshare([[D],[E],[F]]),ground([C,B]),linear(D),linear(F);mshare([[D],[E],[F],[B]]),ground([C]),linear(D),linear(F),linear(B);mshare([[D],[F]]),ground([C,E,B]),linear(D),linear(F);mshare([[D],[F],[B]]),ground([C,E]),linear(D),linear(F),linear(B))),
    terminal(B,C,D,E,F),
    true((mshare([[E],[E,F]]),ground([C,D,B]);mshare([[E],[E,F],[E,F,B],[E,B]]),ground([C,D]);ground([C,D,E,F,B]))),
    prep(B),
    true((mshare([[E],[E,F]]),ground([C,D,B]);ground([C,D,E,F,B]))).

:- true pred rel_adj(_A,C,D,E,F)
   : ( mshare([[_A],[D],[E],[F]]),
       ground([C]), linear(_A), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([_A,C,D]) ).

:- true pred rel_adj(_A,C,D,E,F)
   : ( mshare([[_A],[D],[F]]),
       ground([C,E]), linear(_A), linear(D), linear(F) )
   => ground([_A,C,D,E,F]).

rel_adj(adj(B),C,D,E,F) :-
    true((mshare([[D],[E],[F],[B],[G]]),ground([C]),linear(D),linear(F),linear(B),linear(G);mshare([[D],[F],[B],[G]]),ground([C,E]),linear(D),linear(F),linear(B),linear(G))),
    terminal(G,C,D,E,F),
    true((mshare([[E],[E,F],[E,F,G],[E,G],[B]]),ground([C,D]),linear(B);mshare([[B]]),ground([C,D,E,F,G]),linear(B))),
    rel_adj(G,B),
    true((mshare([[E],[E,F]]),ground([C,D,B,G]);ground([C,D,E,F,B,G]))).

:- true pred sup_adj(_A,C,D,E,F)
   : ( mshare([[_A],[D],[E],[F]]),
       ground([C]), linear(_A), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([_A,C,D]) ).

:- true pred sup_adj(_A,C,D,E,F)
   : ( mshare([[_A],[D],[F]]),
       ground([C,E]), linear(_A), linear(D), linear(F) )
   => ground([_A,C,D,E,F]).

sup_adj(adj(B),C,D,E,F) :-
    true((mshare([[D],[E],[F],[B],[G]]),ground([C]),linear(D),linear(F),linear(B),linear(G);mshare([[D],[F],[B],[G]]),ground([C,E]),linear(D),linear(F),linear(B),linear(G))),
    terminal(G,C,D,E,F),
    true((mshare([[E],[E,F],[E,F,G],[E,G],[B]]),ground([C,D]),linear(B);mshare([[B]]),ground([C,D,E,F,G]),linear(B))),
    sup_adj(G,B),
    true((mshare([[E],[E,F]]),ground([C,D,B,G]);ground([C,D,E,F,B,G]))).

:- true pred comp_adv(_A,B,C,D,E)
   : ( mshare([[_A],[C],[D],[E]]),
       ground([B]), linear(_A), linear(C), linear(E) )
   => ( mshare([[D],[D,E]]),
        ground([_A,B,C]) ).

:- true pred comp_adv(_A,B,C,D,E)
   : ( mshare([[_A],[C],[E]]),
       ground([B,D]), linear(_A), linear(C), linear(E) )
   => ground([_A,B,C,D,E]).

comp_adv(less,B,C,D,E) :-
    true((mshare([[C],[D],[E]]),ground([B]),linear(C),linear(E);mshare([[C],[E]]),ground([B,D]),linear(C),linear(E))),
    ~(less,B,C,D,E),
    true((mshare([[D],[D,E]]),ground([B,C]);ground([B,C,D,E]))).
comp_adv(more,B,C,D,E) :-
    true((mshare([[C],[D],[E]]),ground([B]),linear(C),linear(E);mshare([[C],[E]]),ground([B,D]),linear(C),linear(E))),
    ~(more,B,C,D,E),
    true((mshare([[D],[D,E]]),ground([B,C]);ground([B,C,D,E]))).

:- true pred sup_adv(_A,B,C,D,E)
   : ( mshare([[_A],[C],[D],[E]]),
       ground([B]), linear(_A), linear(C), linear(E) )
   => ( mshare([[D],[D,E]]),
        ground([_A,B,C]) ).

:- true pred sup_adv(_A,B,C,D,E)
   : ( mshare([[_A],[C],[E]]),
       ground([B,D]), linear(_A), linear(C), linear(E) )
   => ground([_A,B,C,D,E]).

sup_adv(least,B,C,D,E) :-
    true((mshare([[C],[D],[E]]),ground([B]),linear(C),linear(E);mshare([[C],[E]]),ground([B,D]),linear(C),linear(E))),
    ~(least,B,C,D,E),
    true((mshare([[D],[D,E]]),ground([B,C]);ground([B,C,D,E]))).
sup_adv(most,B,C,D,E) :-
    true((mshare([[C],[D],[E]]),ground([B]),linear(C),linear(E);mshare([[C],[E]]),ground([B,D]),linear(C),linear(E))),
    ~(most,B,C,D,E),
    true((mshare([[D],[D,E]]),ground([B,C]);ground([B,C,D,E]))).

:- true pred rel_pron(B,C,D,E,F)
   : ( mshare([[B],[D],[E],[F]]),
       ground([C]), linear(B), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([B,C,D]) ).

rel_pron(B,C,D,E,F) :-
    true((
        mshare([[B],[D],[E],[F],[G]]),
        ground([C]),
        linear(B),
        linear(D),
        linear(F),
        linear(G)
    )),
    terminal(G,C,D,E,F),
    true((
        mshare([[B],[E],[E,F],[E,F,G],[E,G]]),
        ground([C,D]),
        linear(B)
    )),
    rel_pron(G,B),
    true((
        mshare([[E],[E,F]]),
        ground([B,C,D,G])
    )).

:- true pred name(B,C,D,E,F)
   : ( mshare([[B],[D],[E],[F]]),
       ground([C]), linear(B), linear(D), linear(F) )
   => ( mshare([[B,E],[B,E,F],[E],[E,F]]),
        ground([C,D]) ).

:- true pred name(B,C,D,E,F)
   : ( mshare([[B],[D],[F]]),
       ground([C,E]), linear(B), linear(D), linear(F) )
   => ground([B,C,D,E,F]).

name(B,C,D,E,F) :-
    true((mshare([[B],[D],[E],[F],[G],[H]]),ground([C]),linear(B),linear(D),linear(F),linear(G),linear(H);mshare([[B],[D],[F],[G],[H]]),ground([C,E]),linear(B),linear(D),linear(F),linear(G),linear(H))),
    opt_the(C,G,E,H),
    true((mshare([[B],[D],[E],[E,H],[F]]),ground([C,G]),linear(B),linear(D),linear(F);mshare([[B],[D],[F]]),ground([C,E,G,H]),linear(B),linear(D),linear(F))),
    terminal(B,G,D,H,F),
    true((mshare([[B,E,F,H],[B,E,H],[E],[E,F,H],[E,H]]),ground([C,D,G]);ground([B,C,D,E,F,G,H]))),
    name(B),
    true((mshare([[B,E,F,H],[B,E,H],[E],[E,F,H],[E,H]]),ground([C,D,G]);ground([B,C,D,E,F,G,H]))).

:- true pred int_art(B,_A,_B,C,D,E,F)
   : ( mshare([[B],[_A],[_B],[D],[E],[F]]),
       ground([C]), linear(B), linear(_A), linear(_B), linear(D), linear(F) )
   => ( mshare([[B,_B],[_A],[E],[E,F]]),
        ground([C,D]), linear(B), linear(_B) ).

:- true pred int_art(B,_A,_B,C,D,E,F)
   : ( mshare([[B],[_A],[_B],[D],[F]]),
       ground([C,E]), linear(B), linear(_A), linear(_B), linear(D), linear(F) )
   => ( mshare([[B,_B],[_A]]),
        ground([C,D,E,F]), linear(B), linear(_B) ).

int_art(B,plu,quant(same,wh(B)),C,D,E,F) :-
    true((mshare([[B],[D],[E],[F],[G],[H]]),ground([C]),linear(B),linear(D),linear(F),linear(G),linear(H);mshare([[B],[D],[F],[G],[H]]),ground([C,E]),linear(B),linear(D),linear(F),linear(G),linear(H))),
    ~(how,C,G,E,H),
    true((mshare([[B],[D],[E],[E,H],[F]]),ground([C,G]),linear(B),linear(D),linear(F);mshare([[B],[D],[F]]),ground([C,E,G,H]),linear(B),linear(D),linear(F))),
    ~(many,G,D,H,F),
    true((mshare([[B]]),ground([C,D,E,F,G,H]),linear(B);mshare([[B],[E],[E,F,H],[E,H]]),ground([C,D,G]),linear(B))).
int_art(B,C,D,E,F,G,H) :-
    true((mshare([[B],[C],[D],[F],[G],[H],[I]]),ground([E]),linear(B),linear(C),linear(D),linear(F),linear(H),linear(I);mshare([[B],[C],[D],[F],[H],[I]]),ground([E,G]),linear(B),linear(C),linear(D),linear(F),linear(H),linear(I))),
    terminal(I,E,F,G,H),
    true((mshare([[B],[C],[D]]),ground([E,F,G,H,I]),linear(B),linear(C),linear(D);mshare([[B],[C],[D],[G],[G,H],[G,H,I],[G,I]]),ground([E,F]),linear(B),linear(C),linear(D))),
    int_art(I,B,C,D),
    true((mshare([[B,D],[C]]),ground([E,F,G,H,I]),linear(B),linear(C),linear(D);mshare([[B,D],[C],[G],[G,H]]),ground([E,F,I]),linear(B),linear(C),linear(D))).

:- true pred int_pron(B,C,D,E,F)
   : ( mshare([[B],[D],[E],[F]]),
       ground([C]), linear(B), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([B,C,D]) ).

:- true pred int_pron(B,C,D,E,F)
   : ( mshare([[B],[D],[F]]),
       ground([C,E]), linear(B), linear(D), linear(F) )
   => ground([B,C,D,E,F]).

int_pron(B,C,D,E,F) :-
    true((mshare([[B],[D],[E],[F],[G]]),ground([C]),linear(B),linear(D),linear(F),linear(G);mshare([[B],[D],[F],[G]]),ground([C,E]),linear(B),linear(D),linear(F),linear(G))),
    terminal(G,C,D,E,F),
    true((mshare([[B]]),ground([C,D,E,F,G]),linear(B);mshare([[B],[E],[E,F],[E,F,G],[E,G]]),ground([C,D]),linear(B))),
    int_pron(G,B),
    true((mshare([[E],[E,F]]),ground([B,C,D,G]);ground([B,C,D,E,F,G]))).

:- true pred adverb(_A,C,D,E,F)
   : ( mshare([[_A],[D],[E],[F]]),
       ground([C]), linear(_A), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([_A,C,D]) ).

adverb(adv(B),C,D,E,F) :-
    true((
        mshare([[D],[E],[F],[B]]),
        ground([C]),
        linear(D),
        linear(F),
        linear(B)
    )),
    terminal(B,C,D,E,F),
    true((
        mshare([[E],[E,F],[E,F,B],[E,B]]),
        ground([C,D])
    )),
    adverb(B),
    true((
        mshare([[E],[E,F]]),
        ground([C,D,B])
    )).

:- true pred poss_pron(_A,_B,E,F,G,H)
   : ( mshare([[_A],[_B],[F],[G],[H]]),
       ground([E]), linear(_A), linear(_B), linear(F), linear(H) )
   => ( mshare([[_A],[_B],[G],[G,H]]),
        ground([E,F]) ).

:- true pred poss_pron(_A,_B,E,F,G,H)
   : ( mshare([[_A],[_B],[F],[H]]),
       ground([E,G]), linear(_A), linear(_B), linear(F), linear(H) )
   => ( mshare([[_A],[_B]]),
        ground([E,F,G,H]) ).

poss_pron(pronoun(B),C+D,E,F,G,H) :-
    true((mshare([[F],[G],[H],[B],[C],[D],[I]]),ground([E]),linear(F),linear(H),linear(B),linear(C),linear(D),linear(I);mshare([[F],[H],[B],[C],[D],[I]]),ground([E,G]),linear(F),linear(H),linear(B),linear(C),linear(D),linear(I))),
    terminal(I,E,F,G,H),
    true((mshare([[G],[G,H],[G,H,I],[G,I],[B],[C],[D]]),ground([E,F]),linear(B),linear(C),linear(D);mshare([[B],[C],[D]]),ground([E,F,G,H,I]),linear(B),linear(C),linear(D))),
    poss_pron(I,B,C,D),
    true((mshare([[G],[G,H],[B],[D]]),ground([E,F,C,I]);mshare([[B],[D]]),ground([E,F,G,H,C,I]))).

:- true pred pers_pron(_A,_B,E,F,G,H,I)
   : ( mshare([[_A],[_B],[E],[G],[I]]),
       ground([F,H]), linear(_A), linear(_B), linear(E), linear(G), linear(I) )
   => ( mshare([[_A],[_B],[E]]),
        ground([F,G,H,I]) ).

:- true pred pers_pron(_A,_B,E,F,G,H,I)
   : ( mshare([[_A],[_B,H],[E],[G],[H],[I]]),
       ground([F]), linear(_A), linear(E), linear(G), linear(I) )
   => ( mshare([[_A],[_B,H],[_B,H,I],[E],[H],[H,I]]),
        ground([F,G]) ).

:- true pred pers_pron(_A,_B,E,F,G,H,I)
   : ( mshare([[_A],[_B],[E],[G],[H],[I]]),
       ground([F]), linear(_A), linear(_B), linear(E), linear(G), linear(I) )
   => ( mshare([[_A],[_B],[E],[H],[H,I]]),
        ground([F,G]) ).

:- true pred pers_pron(_A,_B,E,F,G,H,I)
   : ( mshare([[_A],[E],[G],[H],[I]]),
       ground([_B,F]), linear(_A), linear(E), linear(G), linear(I) )
   => ( mshare([[_A],[E],[H],[H,I]]),
        ground([_B,F,G]) ).

:- true pred pers_pron(_A,_B,E,F,G,H,I)
   : ( mshare([[_A],[E],[G],[I]]),
       ground([_B,F,H]), linear(_A), linear(E), linear(G), linear(I) )
   => ( mshare([[_A],[E]]),
        ground([_B,F,G,H,I]) ).

pers_pron(pronoun(B),C+D,E,F,G,H,I) :-
    true((mshare([[E],[G],[H],[H,C],[H,C,D],[H,D],[I],[B],[J]]),ground([F]),linear(E),linear(G),linear(I),linear(B),linear(J);mshare([[E],[G],[H],[I],[B],[C],[D],[J]]),ground([F]),linear(E),linear(G),linear(I),linear(B),linear(C),linear(D),linear(J);mshare([[E],[G],[H],[I],[B],[J]]),ground([F,C,D]),linear(E),linear(G),linear(I),linear(B),linear(J);mshare([[E],[G],[I],[B],[C],[D],[J]]),ground([F,H]),linear(E),linear(G),linear(I),linear(B),linear(C),linear(D),linear(J);mshare([[E],[G],[I],[B],[J]]),ground([F,H,C,D]),linear(E),linear(G),linear(I),linear(B),linear(J))),
    terminal(J,F,G,H,I),
    true((mshare([[E],[H],[H,I],[H,I,C],[H,I,C,D],[H,I,C,D,J],[H,I,C,J],[H,I,D],[H,I,D,J],[H,I,J],[H,C],[H,C,D],[H,C,D,J],[H,C,J],[H,D],[H,D,J],[H,J],[B]]),ground([F,G]),linear(E),linear(B);mshare([[E],[H],[H,I],[H,I,J],[H,J],[B]]),ground([F,G,C,D]),linear(E),linear(B);mshare([[E],[H],[H,I],[H,I,J],[H,J],[B],[C],[D]]),ground([F,G]),linear(E),linear(B),linear(C),linear(D);mshare([[E],[B]]),ground([F,G,H,I,C,D,J]),linear(E),linear(B);mshare([[E],[B],[C],[D]]),ground([F,G,H,I,J]),linear(E),linear(B),linear(C),linear(D))),
    pers_pron(J,B,C,D,E),
    true((mshare([[E],[H],[H,I],[H,I,D],[H,D],[B]]),ground([F,G,C,J]);mshare([[E],[H],[H,I],[B]]),ground([F,G,C,D,J]);mshare([[E],[H],[H,I],[B],[D]]),ground([F,G,C,J]);mshare([[E],[B]]),ground([F,G,H,I,C,D,J]);mshare([[E],[B],[D]]),ground([F,G,H,I,C,J]))).

:- true pred quantifier_pron(B,C,D,E,F,G)
   : ( mshare([[B],[C],[E],[F],[G]]),
       ground([D]), linear(B), linear(C), linear(E), linear(G) )
   => ( mshare([[F],[F,G]]),
        ground([B,C,D,E]) ).

:- true pred quantifier_pron(B,C,D,E,F,G)
   : ( mshare([[B],[C],[E],[G]]),
       ground([D,F]), linear(B), linear(C), linear(E), linear(G) )
   => ground([B,C,D,E,F,G]).

quantifier_pron(B,C,D,E,F,G) :-
    true((mshare([[B],[C],[E],[F],[G],[H]]),ground([D]),linear(B),linear(C),linear(E),linear(G),linear(H);mshare([[B],[C],[E],[G],[H]]),ground([D,F]),linear(B),linear(C),linear(E),linear(G),linear(H))),
    terminal(H,D,E,F,G),
    true((mshare([[B],[C]]),ground([D,E,F,G,H]),linear(B),linear(C);mshare([[B],[C],[F],[F,G],[F,G,H],[F,H]]),ground([D,E]),linear(B),linear(C))),
    quantifier_pron(H,B,C),
    true((mshare([[F],[F,G]]),ground([B,C,D,E,H]);ground([B,C,D,E,F,G,H]))).

:- true pred context_pron(_A,_B,B,C,D,E)
   : ( mshare([[_A],[_B],[C],[D],[E]]),
       ground([B]), linear(_A), linear(_B), linear(C), linear(E) )
   => ( mshare([[D],[D,E]]),
        ground([_A,_B,B,C]) ).

:- true pred context_pron(_A,_B,B,C,D,E)
   : ( mshare([[_A],[_B],[C],[E]]),
       ground([B,D]), linear(_A), linear(_B), linear(C), linear(E) )
   => ground([_A,_B,B,C,D,E]).

context_pron(prep(in),place,B,C,D,E) :-
    true((mshare([[C],[D],[E]]),ground([B]),linear(C),linear(E);mshare([[C],[E]]),ground([B,D]),linear(C),linear(E))),
    ~(where,B,C,D,E),
    true((mshare([[D],[D,E]]),ground([B,C]);ground([B,C,D,E]))).
context_pron(prep(at),time,B,C,D,E) :-
    true((mshare([[C],[D],[E]]),ground([B]),linear(C),linear(E);mshare([[C],[E]]),ground([B,D]),linear(C),linear(E))),
    ~(when,B,C,D,E),
    true((mshare([[D],[D,E]]),ground([B,C]);ground([B,C,D,E]))).

:- true pred number(_A,C,D,E,F,G)
   : ( mshare([[_A],[C],[C,F],[E],[F],[G]]),
       ground([D]), linear(_A), linear(E), linear(G) )
   => ( mshare([[F],[F,G]]),
        ground([_A,C,D,E]) ).

:- true pred number(_A,C,D,E,F,G)
   : ( mshare([[_A],[C],[E],[F],[G]]),
       ground([D]), linear(_A), linear(C), linear(E), linear(G) )
   => ( mshare([[F],[F,G]]),
        ground([_A,C,D,E]) ).

:- true pred number(_A,C,D,E,F,G)
   : ( mshare([[_A],[C],[E],[G]]),
       ground([D,F]), linear(_A), linear(C), linear(E), linear(G) )
   => ground([_A,C,D,E,F,G]).

number(nb(B),C,D,E,F,G) :-
    true((mshare([[C],[C,F],[E],[F],[G],[B],[H]]),ground([D]),linear(E),linear(G),linear(B),linear(H);mshare([[C],[E],[F],[G],[B],[H]]),ground([D]),linear(C),linear(E),linear(G),linear(B),linear(H);mshare([[C],[E],[G],[B],[H]]),ground([D,F]),linear(C),linear(E),linear(G),linear(B),linear(H))),
    terminal(H,D,E,F,G),
    true((mshare([[C],[C,F],[C,F,G],[C,F,G,H],[C,F,H],[F],[F,G],[F,G,H],[F,H],[B]]),ground([D,E]),linear(B);mshare([[C],[F],[F,G],[F,G,H],[F,H],[B]]),ground([D,E]),linear(C),linear(B);mshare([[C],[B]]),ground([D,E,F,G,H]),linear(C),linear(B))),
    number(H,B,C),
    true((mshare([[F],[F,G]]),ground([C,D,E,B,H]);ground([C,D,E,F,G,B,H]))).

:- true pred terminator(B,C,D,E,F)
   : ( (B=!),
       mshare([[E]]),
       ground([C,D,F]) )
   => ( mshare([[E]]),
        ground([C,D,F]) ).

:- true pred terminator(B,C,D,E,F)
   : ( (B= ?),
       mshare([[E]]),
       ground([C,D,F]) )
   => ( mshare([[E]]),
        ground([C,D,F]) ).

:- true pred terminator(B,C,D,E,F)
   : ( (B='.'),
       mshare([[E]]),
       ground([C,D,F]) )
   => ( mshare([[E]]),
        ground([C,D,F]) ).

terminator(B,C,D,E,F) :-
    true((
        mshare([[E],[G]]),
        ground([B,C,D,F]),
        linear(G)
    )),
    terminal(G,C,D,E,F),
    true((
        mshare([[E],[E,G]]),
        ground([B,C,D,F])
    )),
    terminator(G,B),
    true((
        mshare([[E]]),
        ground([B,C,D,F,G])
    )).

:- true pred opt_the(B,_A,C,E)
   : ( mshare([[_A],[C],[E]]),
       ground([B]), linear(_A), linear(E) )
   => ( mshare([[C],[C,E]]),
        ground([B,_A]) ).

:- true pred opt_the(B,_A,C,E)
   : ( mshare([[_A],[E]]),
       ground([B,C]), linear(_A), linear(E) )
   => ground([B,_A,C,E]).

opt_the(B,B,C,C).
opt_the(B,C,D,E) :-
    true((mshare([[C],[D],[E]]),ground([B]),linear(C),linear(E);mshare([[C],[E]]),ground([B,D]),linear(C),linear(E))),
    ~(the,B,C,D,E),
    true((mshare([[D],[D,E]]),ground([B,C]);ground([B,C,D,E]))).

:- true pred conj(B,_A,_B,C,D,E,F)
   : ( mshare([[B],[B,_A],[_A],[_B],[D],[E],[F]]),
       ground([C]), linear(_B), linear(D), linear(F) )
   => ( mshare([[B],[E],[E,F]]),
        ground([_A,_B,C,D]) ).

:- true pred conj(B,_A,_B,C,D,E,F)
   : ( mshare([[B],[_A],[_B],[D],[E],[F]]),
       ground([C]), linear(B), linear(_A), linear(_B), linear(D), linear(F) )
   => ( mshare([[B],[E],[E,F]]),
        ground([_A,_B,C,D]) ).

conj(B,list,list,C,D,E,F) :-
    true((mshare([[B],[D],[E],[F]]),ground([C]),linear(B),linear(D),linear(F);mshare([[B],[D],[E],[F]]),ground([C]),linear(D),linear(F))),
    terminal(',',C,D,E,F),
    true((mshare([[B],[E],[E,F]]),ground([C,D]);mshare([[B],[E],[E,F]]),ground([C,D]),linear(B))).
conj(B,list,end,C,D,E,F) :-
    true((mshare([[B],[D],[E],[F]]),ground([C]),linear(B),linear(D),linear(F);mshare([[B],[D],[E],[F]]),ground([C]),linear(D),linear(F))),
    terminal(B,C,D,E,F),
    true((
        mshare([[B,E],[B,E,F],[E],[E,F]]),
        ground([C,D])
    )),
    conj(B),
    true((
        mshare([[E],[E,F]]),
        ground([B,C,D])
    )).

:- true pred loc_pred(B,C,D,E,F)
   : ( mshare([[B],[D],[F]]),
       ground([C,E]), linear(B), linear(D), linear(F) )
   => ground([B,C,D,E,F]).

:- true pred loc_pred(B,C,D,E,F)
   : ( mshare([[B],[D],[E],[F]]),
       ground([C]), linear(B), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([B,C,D]) ).

loc_pred(B,C,D,E,F) :-
    true((mshare([[B],[D],[E],[F],[G]]),ground([C]),linear(B),linear(D),linear(F),linear(G);mshare([[B],[D],[F],[G]]),ground([C,E]),linear(B),linear(D),linear(F),linear(G))),
    terminal(G,C,D,E,F),
    true((mshare([[B]]),ground([C,D,E,F,G]),linear(B);mshare([[B],[E],[E,F],[E,F,G],[E,G]]),ground([C,D]),linear(B))),
    loc_pred(G,B),
    true((mshare([[E],[E,F]]),ground([B,C,D,G]);ground([B,C,D,E,F,G]))).

:- true pred ~(B,C,D,E,F)
   : ( (B=how),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=when),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=where),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=many),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=whose),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=','),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=of),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=how),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=when),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=where),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=of),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=many),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=whose),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=not),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=that),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=as),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=than),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=the),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=at),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=s),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B= ~),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=most),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=least),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=more),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=less),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=there),
       mshare([[D],[E],[F]]),
       ground([C]), linear(D), linear(F) )
   => ( mshare([[E],[E,F]]),
        ground([C,D]) ).

:- true pred ~(B,C,D,E,F)
   : ( (B=as),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=than),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=not),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=the),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=at),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=s),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B= ~),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=most),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=least),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=more),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=less),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

:- true pred ~(B,C,D,E,F)
   : ( (B=there),
       mshare([[D],[F]]),
       ground([C,E]), linear(D), linear(F) )
   => ground([C,D,E,F]).

~(B,C,D,E,F) :-
    true((mshare([[D],[E],[F]]),ground([B,C]),linear(D),linear(F);mshare([[D],[F]]),ground([B,C,E]),linear(D),linear(F))),
    terminal(B,C,D,E,F),
    true((mshare([[E],[E,F]]),ground([B,C,D]);ground([B,C,D,E,F]))),
    ~(B),
    true((mshare([[E],[E,F]]),ground([B,C,D]);ground([B,C,D,E,F]))).

word(Word) :-
    ~(Word).
word(Word) :-
    conj(Word).
word(Word) :-
    adverb(Word).
word(Word) :-
    sup_adj(Word,_1).
word(Word) :-
    rel_adj(Word,_1).
word(Word) :-
    adj(Word,_1).
word(Word) :-
    name(Word).
word(Word) :-
    terminator(Word,_1).
word(Word) :-
    pers_pron(Word,_1,_2,_3,_4).
word(Word) :-
    poss_pron(Word,_1,_2,_3).
word(Word) :-
    rel_pron(Word,_1).
word(Word) :-
    verb_form(Word,_1,_2,_3).
word(Word) :-
    noun_form(Word,_1,_2).
word(Word) :-
    prep(Word).
word(Word) :-
    quantifier_pron(Word,_1,_2).
word(Word) :-
    number(Word,_1,_2).
word(Word) :-
    det(Word,_1,_2,_3).
word(Word) :-
    int_art(Word,_1,_2,_3).
word(Word) :-
    int_pron(Word,_1).
word(Word) :-
    loc_pred(Word,_1).

:- true pred ~(_A)
   : ground([_A])
   => ground([_A]).

~(how).
~(whose).
~(there).
~(of).
~(~).
~(',').
~(s).
~(than).
~(at).
~(the).
~(not).
~(as).
~(that).
~(less).
~(more).
~(least).
~(most).
~(many).
~(where).
~(when).

:- true pred conj(_A)
   : mshare([[_A]])
   => ground([_A]).

conj(and).
conj(or).

:- true pred int_pron(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_B) )
   => ground([_A,_B]).

:- true pred int_pron(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]), linear(_B) )
   => ground([_A,_B]).

int_pron(what,undef).
int_pron(which,undef).
int_pron(who,subj).
int_pron(whom,compl).

:- true pred int_art(_A,X,_1,_B)
   : ( mshare([[_A],[X],[_1],[_B]]),
       linear(X), linear(_1), linear(_B) )
   => ( mshare([[X,_B],[_1]]),
        ground([_A]), linear(X), linear(_1), linear(_B) ).

:- true pred int_art(_A,X,_1,_B)
   : ( mshare([[X],[_1],[_B]]),
       ground([_A]), linear(X), linear(_1), linear(_B) )
   => ( mshare([[X,_B],[_1]]),
        ground([_A]), linear(X), linear(_1), linear(_B) ).

int_art(what,X,_1,int_det(X)).
int_art(which,X,_1,int_det(X)).

:- true pred det(_A,No,_B,_C)
   : ( mshare([[_A],[_A,No],[No],[_B]]),
       ground([_C]), linear(_B) )
   => ( mshare([[No],[No,_B]]),
        ground([_A,_C]) ).

:- true pred det(_A,No,_B,_C)
   : ( mshare([[_A],[No],[_B]]),
       ground([_C]), linear(No), linear(_B) )
   => ( mshare([[No],[No,_B]]),
        ground([_A,_C]) ).

:- true pred det(_A,No,_B,_C)
   : ( mshare([[_A],[No],[_B],[_C]]),
       linear(No), linear(_B), linear(_C) )
   => ( mshare([[No],[No,_B]]),
        ground([_A,_C]) ).

:- true pred det(_A,No,_B,_C)
   : ( mshare([[No],[_B]]),
       ground([_A,_C]), linear(No), linear(_B) )
   => ( mshare([[No],[No,_B]]),
        ground([_A,_C]) ).

:- true pred det(_A,No,_B,_C)
   : ( mshare([[No],[_B],[_C]]),
       ground([_A]), linear(No), linear(_B), linear(_C) )
   => ( mshare([[No],[No,_B]]),
        ground([_A,_C]) ).

det(the,No,the(No),def).
det(a,sin,a,indef).
det(an,sin,a,indef).
det(every,sin,every,indef).
det(some,_1,some,indef).
det(any,_1,any,indef).
det(all,plu,all,indef).
det(each,sin,each,indef).
det(no,_1,no,indef).

:- true pred number(W,I,Nb)
   : ( mshare([[W],[W,Nb],[I],[Nb]]),
       linear(I) )
   => ground([W,I,Nb]).

:- true pred number(W,I,Nb)
   : ( mshare([[W],[I],[Nb]]),
       linear(I), linear(Nb) )
   => ground([W,I,Nb]).

:- true pred number(W,I,Nb)
   : ( mshare([[I],[Nb]]),
       ground([W]), linear(I), linear(Nb) )
   => ground([W,I,Nb]).

number(W,I,Nb) :-
    true((mshare([[W],[W,Nb],[I],[Nb]]),linear(I);mshare([[W],[I],[Nb]]),linear(I),linear(Nb);mshare([[I],[Nb]]),ground([W]),linear(I),linear(Nb))),
    tr_number(W,I),
    true((mshare([[W,I],[W,I,Nb],[Nb]]);mshare([[W,I],[Nb]]),linear(Nb);mshare([[Nb]]),ground([W,I]),linear(Nb))),
    ag_number(I,Nb),
    true(ground([W,I,Nb])).

:- true pred tr_number(_A,I)
   : ( mshare([[_A],[I]]),
       linear(I) )
   => mshare([[_A,I]]).

:- true pred tr_number(_A,I)
   : ( mshare([[I]]),
       ground([_A]), linear(I) )
   => ground([_A,I]).

tr_number(nb(I),I).
tr_number(one,1).
tr_number(two,2).
tr_number(three,3).
tr_number(four,4).
tr_number(five,5).
tr_number(six,6).
tr_number(seven,7).
tr_number(eight,8).
tr_number(nine,9).
tr_number(ten,10).

:- true pred ag_number(N,_A)
   : mshare([[N],[N,_A],[_A]])
   => ground([N,_A]).

:- true pred ag_number(N,_A)
   : ( mshare([[N],[_A]]),
       linear(_A) )
   => ground([N,_A]).

:- true pred ag_number(N,_A)
   : ( mshare([[_A]]),
       ground([N]), linear(_A) )
   => ground([N,_A]).

ag_number(1,sin).
ag_number(N,plu) :-
    true((mshare([[N]]);ground([N]))),
    N>1,
    true(ground([N])).

:- true pred quantifier_pron(_A,_B,_C)
   : ( mshare([[_A],[_B],[_C]]),
       linear(_B), linear(_C) )
   => ground([_A,_B,_C]).

:- true pred quantifier_pron(_A,_B,_C)
   : ( mshare([[_B],[_C]]),
       ground([_A]), linear(_B), linear(_C) )
   => ground([_A,_B,_C]).

quantifier_pron(everybody,every,person).
quantifier_pron(everyone,every,person).
quantifier_pron(everything,every,thing).
quantifier_pron(somebody,some,person).
quantifier_pron(someone,some,person).
quantifier_pron(something,some,thing).
quantifier_pron(anybody,any,person).
quantifier_pron(anyone,any,person).
quantifier_pron(anything,any,thing).
quantifier_pron(nobody,no,person).
quantifier_pron(nothing,no,thing).

:- true pred prep(_A)
   : ground([_A])
   => ground([_A]).

:- true pred prep(_A)
   : mshare([[_A]])
   => ground([_A]).

prep(as).
prep(at).
prep(of).
prep(to).
prep(by).
prep(with).
prep(in).
prep(on).
prep(from).
prep(into).
prep(through).

:- true pred noun_form(Plu,Sin,_1)
   : ( mshare([[Plu],[Plu,_1],[Sin],[_1]]),
       linear(Sin) )
   => ( mshare([[_1]]),
        ground([Plu,Sin]) ).

:- true pred noun_form(Plu,Sin,_1)
   : ( mshare([[Sin],[_1]]),
       ground([Plu]), linear(Sin) )
   => ( mshare([[_1]]),
        ground([Plu,Sin]) ).

noun_form(Plu,Sin,plu) :-
    true((mshare([[Plu],[Sin]]),linear(Sin);mshare([[Sin]]),ground([Plu]),linear(Sin))),
    noun_plu(Plu,Sin),
    true(ground([Plu,Sin])).
noun_form(Sin,Sin,sin) :-
    true((mshare([[Sin]]);ground([Sin]))),
    noun_sin(Sin),
    true(ground([Sin])).
noun_form(proportion,proportion,_1).
noun_form(percentage,percentage,_1).

:- true pred root_form(_A)
   : ( mshare([[_A]]),
       linear(_A) )
   => mshare([[_A]]).

:- true pred root_form(_A)
   : mshare([[_A]])
   => mshare([[_A]]).

root_form(1+sin).
root_form(2+_1).
root_form(1+plu).
root_form(3+plu).

:- true pred verb_root(_A)
   : ground([_A])
   => ground([_A]).

:- true pred verb_root(_A)
   : mshare([[_A]])
   => ground([_A]).

verb_root(be).
verb_root(have).
verb_root(do).
verb_root(border).
verb_root(contain).
verb_root(drain).
verb_root(exceed).
verb_root(flow).
verb_root(rise).

:- true pred regular_pres(_A)
   : ground([_A])
   => ground([_A]).

:- true pred regular_pres(_A)
   : mshare([[_A]])
   => ground([_A]).

regular_pres(have).
regular_pres(do).
regular_pres(rise).
regular_pres(border).
regular_pres(contain).
regular_pres(drain).
regular_pres(exceed).
regular_pres(flow).

:- true pred regular_past(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]), linear(_B) )
   => ground([_A,_B]).

:- true pred regular_past(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_B) )
   => ground([_A,_B]).

regular_past(had,have).
regular_past(bordered,border).
regular_past(contained,contain).
regular_past(drained,drain).
regular_past(exceeded,exceed).
regular_past(flowed,flow).

:- true pred rel_pron(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_B) )
   => ground([_A,_B]).

rel_pron(who,subj).
rel_pron(whom,compl).
rel_pron(which,undef).

:- true pred poss_pron(_A,_1,_B,_2)
   : ( mshare([[_A],[_1],[_B],[_2]]),
       linear(_1), linear(_B), linear(_2) )
   => ( mshare([[_1],[_2]]),
        ground([_A,_B]) ).

:- true pred poss_pron(_A,_1,_B,_2)
   : ( mshare([[_1],[_B],[_2]]),
       ground([_A]), linear(_1), linear(_B), linear(_2) )
   => ( mshare([[_1],[_2]]),
        ground([_A,_B]) ).

poss_pron(my,_1,1,sin).
poss_pron(your,_1,2,_2).
poss_pron(his,masc,3,sin).
poss_pron(her,fem,3,sin).
poss_pron(its,neut,3,sin).
poss_pron(our,_1,1,plu).
poss_pron(their,_1,3,plu).

:- true pred pers_pron(_A,_1,_B,_2,_3)
   : ( mshare([[_A],[_A,_B],[_A,_B,_2],[_A,_2],[_1],[_B],[_B,_2],[_2],[_3]]),
       linear(_1), linear(_3) )
   => ( mshare([[_1],[_2],[_3]]),
        ground([_A,_B]) ).

:- true pred pers_pron(_A,_1,_B,_2,_3)
   : ( mshare([[_A],[_1],[_3]]),
       ground([_B,_2]), linear(_1), linear(_3) )
   => ( mshare([[_1],[_3]]),
        ground([_A,_B,_2]) ).

:- true pred pers_pron(_A,_1,_B,_2,_3)
   : ( mshare([[_A],[_1],[_B],[_2],[_3]]),
       linear(_1), linear(_B), linear(_2), linear(_3) )
   => ( mshare([[_1],[_2],[_3]]),
        ground([_A,_B]) ).

:- true pred pers_pron(_A,_1,_B,_2,_3)
   : ( mshare([[_1],[_3]]),
       ground([_A,_B,_2]), linear(_1), linear(_3) )
   => ( mshare([[_1],[_3]]),
        ground([_A,_B,_2]) ).

:- true pred pers_pron(_A,_1,_B,_2,_3)
   : ( mshare([[_1],[_B],[_2],[_3]]),
       ground([_A]), linear(_1), linear(_B), linear(_2), linear(_3) )
   => ( mshare([[_1],[_2],[_3]]),
        ground([_A,_B]) ).

pers_pron(i,_1,1,sin,subj).
pers_pron(you,_1,2,_2,_3).
pers_pron(he,masc,3,sin,subj).
pers_pron(she,fem,3,sin,subj).
pers_pron(it,neut,3,sin,_1).
pers_pron(we,_1,1,plu,subj).
pers_pron(them,_1,3,plu,subj).
pers_pron(me,_1,1,sin,compl(_2)).
pers_pron(him,masc,3,sin,compl(_1)).
pers_pron(her,fem,3,sin,compl(_1)).
pers_pron(us,_1,1,plu,compl(_2)).
pers_pron(them,_1,3,plu,compl(_2)).

:- true pred terminator(_A,_1)
   : ( mshare([[_A]]),
       ground([_1]) )
   => ground([_A,_1]).

terminator('.',_1).
terminator(?,?).
terminator(!,!).

:- true pred name(_1)
   : mshare([[_1]])
   => mshare([[_1]]).

:- true pred name(_1)
   : ground([_1])
   => ground([_1]).

name(_1).

:- true pred loc_pred(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_B) )
   => ground([_A,_B]).

:- true pred loc_pred(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]), linear(_B) )
   => ground([_A,_B]).

loc_pred(east,prep(eastof)).
loc_pred(west,prep(westof)).
loc_pred(north,prep(northof)).
loc_pred(south,prep(southof)).

:- true pred adj(_A,_B)
   : ( mshare([[_A]]),
       ground([_B]) )
   => ground([_A,_B]).

:- true pred adj(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_B) )
   => ground([_A,_B]).

:- true pred adj(_A,_B)
   : ground([_A,_B])
   => ground([_A,_B]).

:- true pred adj(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]), linear(_B) )
   => ground([_A,_B]).

adj(minimum,restr).
adj(maximum,restr).
adj(average,restr).
adj(total,restr).
adj(african,restr).
adj(american,restr).
adj(asian,restr).
adj(european,restr).
adj(great,quant).
adj(big,quant).
adj(small,quant).
adj(large,quant).
adj(old,quant).
adj(new,quant).
adj(populous,quant).

:- true pred rel_adj(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_B) )
   => ground([_A,_B]).

:- true pred rel_adj(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]), linear(_B) )
   => ground([_A,_B]).

rel_adj(greater,great).
rel_adj(less,small).
rel_adj(bigger,big).
rel_adj(smaller,small).
rel_adj(larger,large).
rel_adj(older,old).
rel_adj(newer,new).

:- true pred sup_adj(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_B) )
   => ground([_A,_B]).

:- true pred sup_adj(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]), linear(_B) )
   => ground([_A,_B]).

sup_adj(biggest,big).
sup_adj(smallest,small).
sup_adj(largest,large).
sup_adj(oldest,old).
sup_adj(newest,new).

:- true pred noun_sin(_A)
   : mshare([[_A]])
   => ground([_A]).

:- true pred noun_sin(_A)
   : ground([_A])
   => ground([_A]).

noun_sin(average).
noun_sin(total).
noun_sin(sum).
noun_sin(degree).
noun_sin(sqmile).
noun_sin(ksqmile).
noun_sin(thousand).
noun_sin(million).
noun_sin(time).
noun_sin(place).
noun_sin(area).
noun_sin(capital).
noun_sin(city).
noun_sin(continent).
noun_sin(country).
noun_sin(latitude).
noun_sin(longitude).
noun_sin(ocean).
noun_sin(person).
noun_sin(population).
noun_sin(region).
noun_sin(river).
noun_sin(sea).
noun_sin(seamass).
noun_sin(number).

:- true pred noun_plu(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_B) )
   => ground([_A,_B]).

:- true pred noun_plu(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]), linear(_B) )
   => ground([_A,_B]).

noun_plu(averages,average).
noun_plu(totals,total).
noun_plu(sums,sum).
noun_plu(degrees,degree).
noun_plu(sqmiles,sqmile).
noun_plu(ksqmiles,ksqmile).
noun_plu(million,million).
noun_plu(thousand,thousand).
noun_plu(times,time).
noun_plu(places,place).
noun_plu(areas,area).
noun_plu(capitals,capital).
noun_plu(cities,city).
noun_plu(continents,continent).
noun_plu(countries,country).
noun_plu(latitudes,latitude).
noun_plu(longitudes,longitude).
noun_plu(oceans,ocean).
noun_plu(persons,person).
noun_plu(people,person).
noun_plu(populations,population).
noun_plu(regions,region).
noun_plu(rivers,river).
noun_plu(seas,sea).
noun_plu(seamasses,seamass).
noun_plu(numbers,number).

:- true pred verb_form(V,Root,_A,_1)
   : ( mshare([[Root],[_1]]),
       ground([V,_A]), linear(Root), linear(_1) )
   => ( mshare([[_1]]),
        ground([V,Root,_A]) ).

:- true pred verb_form(V,Root,_A,_1)
   : ( mshare([[V],[Root],[_1]]),
       ground([_A]), linear(Root), linear(_1) )
   => ( mshare([[_1]]),
        ground([V,Root,_A]) ).

:- true pred verb_form(V,Root,_A,_1)
   : ( mshare([[V],[V,_1],[Root],[_A],[_1]]),
       linear(Root), linear(_A) )
   => ( mshare([[_A],[_1]]),
        ground([V,Root]) ).

:- true pred verb_form(V,Root,_A,_1)
   : ( mshare([[V],[Root],[_A],[_1]]),
       linear(Root), linear(_A), linear(_1) )
   => ( mshare([[_A],[_1]]),
        ground([V,Root]) ).

:- true pred verb_form(V,Root,_A,_1)
   : ( mshare([[Root],[_A],[_1]]),
       ground([V]), linear(Root), linear(_A), linear(_1) )
   => ( mshare([[_A],[_1]]),
        ground([V,Root]) ).

verb_form(V,V,inf,_1) :-
    true((mshare([[V],[V,_1],[_1]]);mshare([[V],[_1]]),linear(_1);mshare([[_1]]),ground([V]),linear(_1))),
    verb_root(V),
    true((mshare([[_1]]),ground([V]);mshare([[_1]]),ground([V]),linear(_1))).
verb_form(V,V,pres+fin,Agmt) :-
    true((mshare([[V],[V,Agmt],[Agmt]]);mshare([[V],[Agmt]]),linear(Agmt);mshare([[Agmt]]),ground([V]),linear(Agmt))),
    regular_pres(V),
    true((mshare([[Agmt]]),ground([V]);mshare([[Agmt]]),ground([V]),linear(Agmt))),
    root_form(Agmt),
    true((
        mshare([[Agmt]]),
        ground([V])
    )),
    verb_root(V),
    true((
        mshare([[Agmt]]),
        ground([V])
    )).
verb_form(Past,Root,past+_2,_1) :-
    true((mshare([[Past],[Past,_1],[Root],[_1],[_2]]),linear(Root),linear(_2);mshare([[Past],[Root],[_1]]),ground([_2]),linear(Root),linear(_1);mshare([[Past],[Root],[_1],[_2]]),linear(Root),linear(_1),linear(_2);mshare([[Root],[_1]]),ground([Past,_2]),linear(Root),linear(_1);mshare([[Root],[_1],[_2]]),ground([Past]),linear(Root),linear(_1),linear(_2))),
    regular_past(Past,Root),
    true((mshare([[_1]]),ground([Past,Root,_2]),linear(_1);mshare([[_1],[_2]]),ground([Past,Root]),linear(_1),linear(_2);mshare([[_1],[_2]]),ground([Past,Root]),linear(_2))).
verb_form(am,be,pres+fin,1+sin).
verb_form(are,be,pres+fin,2+sin).
verb_form(is,be,pres+fin,3+sin).
verb_form(are,be,pres+fin,_1+plu).
verb_form(was,be,past+fin,1+sin).
verb_form(were,be,past+fin,2+sin).
verb_form(was,be,past+fin,3+sin).
verb_form(were,be,past+fin,_1+plu).
verb_form(been,be,past+part,_1).
verb_form(being,be,pres+part,_1).
verb_form(has,have,pres+fin,3+sin).
verb_form(having,have,pres+part,_1).
verb_form(does,do,pres+fin,3+sin).
verb_form(did,do,past+fin,_1).
verb_form(doing,do,pres+part,_1).
verb_form(done,do,past+part,_1).
verb_form(flows,flow,pres+fin,3+sin).
verb_form(flowing,flow,pres+part,_1).
verb_form(rises,rise,pres+fin,3+sin).
verb_form(rose,rise,past+fin,_1).
verb_form(risen,rise,past+part,_1).
verb_form(borders,border,pres+fin,3+sin).
verb_form(bordering,border,pres+part,_1).
verb_form(contains,contain,pres+fin,3+sin).
verb_form(containing,contain,pres+part,_1).
verb_form(drains,drain,pres+fin,3+sin).
verb_form(draining,drain,pres+part,_1).
verb_form(exceeds,exceed,pres+fin,3+sin).
verb_form(exceeding,exceed,pres+part,_1).

:- true pred verb_type(_A,_B)
   : ( (_B=aux+_C),
       mshare([[_C]]),
       ground([_A]), linear(_C) )
   => ground([_A,_C]).

:- true pred verb_type(_A,_B)
   : ( (_B=aux+_C),
       mshare([[_A],[_C]]),
       linear(_C) )
   => ground([_A,_C]).

:- true pred verb_type(_A,_B)
   : ( mshare([[_A],[_B]]),
       linear(_B) )
   => ground([_A,_B]).

:- true pred verb_type(_A,_B)
   : ( mshare([[_B]]),
       ground([_A]), linear(_B) )
   => ground([_A,_B]).

verb_type(have,aux+have).
verb_type(be,aux+be).
verb_type(do,aux+ditrans).
verb_type(rise,main+intrans).
verb_type(border,main+trans).
verb_type(contain,main+trans).
verb_type(drain,main+intrans).
verb_type(exceed,main+trans).
verb_type(flow,main+intrans).

:- true pred adverb(_A)
   : mshare([[_A]])
   => ground([_A]).

adverb(yesterday).
adverb(tomorrow).


