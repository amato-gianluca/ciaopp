:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

:- op(700,xfx,less_than).

:- initialization(op(700,xfx,less_than)).

'\006\call_in_module'(poly_10,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true(true),
    poly_10,
    true(true).

:- true pred poly_10.

poly_10 :-
    true(mshare([[P],[_1]])),
    test_poly(P),
    true((
        mshare([[_1]]),
        ground([P])
    )),
    poly_exp(10,P,_1),
    true(ground([P,_1])).

:- true pred test_poly(P)
   : mshare([[P]])
   => ground([P]).

test_poly(P) :-
    true(mshare([[P],[Q]])),
    poly_add(poly(x,[term(0,1),term(1,1)]),poly(y,[term(1,1)]),Q),
    true((
        mshare([[P]]),
        ground([Q])
    )),
    poly_add(poly(z,[term(1,1)]),Q,P),
    true(ground([P,Q])).

:- true pred _A less_than _B
   : ground([_A,_B])
   => ground([_A,_B]).

x less_than y.
y less_than z.
x less_than z.

:- true pred poly_add(Poly,C,_A)
   : ( mshare([[_A]]),
       ground([Poly,C]) )
   => ground([Poly,C,_A]).

:- true pred poly_add(Poly,C,_A)
   : ( (Poly=poly(z,[term(1,1)])),
       mshare([[_A]]),
       ground([C]) )
   => ground([C,_A]).

:- true pred poly_add(Poly,C,_A)
   : ( (Poly=poly(x,[term(0,1),term(1,1)])), (C=poly(y,[term(1,1)])),
       mshare([[_A]]) )
   => ground([_A]).

poly_add(poly(Var,Terms1),poly(Var,Terms2),poly(Var,Terms)) :-
    !,
    true((
        mshare([[Terms]]),
        ground([Var,Terms1,Terms2])
    )),
    term_add(Terms1,Terms2,Terms),
    true(ground([Var,Terms1,Terms2,Terms])).
poly_add(poly(Var1,Terms1),poly(Var2,Terms2),poly(Var1,Terms)) :-
    true((
        mshare([[Terms]]),
        ground([Var1,Terms1,Var2,Terms2])
    )),
    Var1 less_than Var2,
    !,
    true((
        mshare([[Terms]]),
        ground([Var1,Terms1,Var2,Terms2])
    )),
    add_to_order_zero_term(Terms1,poly(Var2,Terms2),Terms),
    true(ground([Var1,Terms1,Var2,Terms2,Terms])).
poly_add(Poly,poly(Var,Terms2),poly(Var,Terms)) :-
    !,
    true((
        mshare([[Terms]]),
        ground([Poly,Var,Terms2])
    )),
    add_to_order_zero_term(Terms2,Poly,Terms),
    true(ground([Poly,Var,Terms2,Terms])).
poly_add(poly(Var,Terms1),C,poly(Var,Terms)) :-
    !,
    true((
        mshare([[Terms]]),
        ground([C,Var,Terms1])
    )),
    add_to_order_zero_term(Terms1,C,Terms),
    true(ground([C,Var,Terms1,Terms])).
poly_add(C1,C2,C) :-
    true((
        mshare([[C]]),
        ground([C1,C2])
    )),
    C is C1+C2,
    true(ground([C1,C2,C])).

:- true pred term_add(Terms1,X,_A)
   : ( (X=[term(_C,_D)|_B]),
       mshare([[_A]]),
       ground([Terms1,_B,_C,_D]) )
   => ground([Terms1,_A,_B,_C,_D]).

:- true pred term_add(Terms1,X,_A)
   : ( mshare([[_A]]),
       ground([Terms1,X]) )
   => ground([Terms1,X,_A]).

term_add([],X,X) :-
    !,
    true(ground([X])).
term_add(X,[],X) :-
    !,
    true(ground([X])).
term_add([term(E,C1)|Terms1],[term(E,C2)|Terms2],[term(E,C)|Terms]) :-
    !,
    true((
        mshare([[Terms],[Terms,C],[C]]),
        ground([Terms1,E,C1,Terms2,C2])
    )),
    poly_add(C1,C2,C),
    true((
        mshare([[Terms]]),
        ground([Terms1,E,C1,Terms2,C2,C])
    )),
    term_add(Terms1,Terms2,Terms),
    true(ground([Terms1,E,C1,Terms2,C2,Terms,C])).
term_add([term(E1,C1)|Terms1],[term(E2,C2)|Terms2],[term(E1,C1)|Terms]) :-
    true((
        mshare([[Terms]]),
        ground([Terms1,E1,C1,Terms2,E2,C2])
    )),
    E1<E2,
    !,
    true((
        mshare([[Terms]]),
        ground([Terms1,E1,C1,Terms2,E2,C2])
    )),
    term_add(Terms1,[term(E2,C2)|Terms2],Terms),
    true(ground([Terms1,E1,C1,Terms2,E2,C2,Terms])).
term_add(Terms1,[term(E2,C2)|Terms2],[term(E2,C2)|Terms]) :-
    true((
        mshare([[Terms]]),
        ground([Terms1,Terms2,E2,C2])
    )),
    term_add(Terms1,Terms2,Terms),
    true(ground([Terms1,Terms2,E2,C2,Terms])).

:- true pred add_to_order_zero_term(Terms,C2,_A)
   : ( mshare([[_A]]),
       ground([Terms,C2]) )
   => ground([Terms,C2,_A]).

:- true pred add_to_order_zero_term(Terms,C2,_A)
   : ( (C2=poly(_B,_C)),
       mshare([[_A]]),
       ground([Terms,_B,_C]) )
   => ground([Terms,_A,_B,_C]).

add_to_order_zero_term([term(0,C1)|Terms],C2,[term(0,C)|Terms]) :-
    !,
    true((
        mshare([[C]]),
        ground([C2,Terms,C1])
    )),
    poly_add(C1,C2,C),
    true(ground([C2,Terms,C1,C])).
add_to_order_zero_term(Terms,C,[term(0,C)|Terms]).

:- true pred poly_exp(N,_1,Result)
   : ( mshare([[Result]]),
       ground([N,_1]) )
   => ground([N,_1,Result]).

:- true pred poly_exp(N,_1,Result)
   : ( (N=10),
       mshare([[Result]]),
       ground([_1]) )
   => ground([_1,Result]).

poly_exp(0,_1,1) :-
    !,
    true(ground([_1])).
poly_exp(N,Poly,Result) :-
    true((
        mshare([[Result],[M],[Part]]),
        ground([N,Poly])
    )),
    M is N>>1,
    true((
        mshare([[Result],[Part]]),
        ground([N,Poly,M])
    )),
    N is M<<1,
    !,
    true((
        mshare([[Result],[Part]]),
        ground([N,Poly,M])
    )),
    poly_exp(M,Poly,Part),
    true((
        mshare([[Result]]),
        ground([N,Poly,M,Part])
    )),
    poly_mul(Part,Part,Result),
    true(ground([N,Poly,Result,M,Part])).
poly_exp(N,Poly,Result) :-
    true((
        mshare([[Result],[M],[Part]]),
        ground([N,Poly])
    )),
    M is N-1,
    true((
        mshare([[Result],[Part]]),
        ground([N,Poly,M])
    )),
    poly_exp(M,Poly,Part),
    true((
        mshare([[Result]]),
        ground([N,Poly,M,Part])
    )),
    poly_mul(Poly,Part,Result),
    true(ground([N,Poly,Result,M,Part])).

:- true pred poly_mul(P,C,_A)
   : ( (P=C),
       mshare([[_A]]),
       ground([P]) )
   => ground([P,_A]).

:- true pred poly_mul(P,C,_A)
   : ( mshare([[_A]]),
       ground([P,C]) )
   => ground([P,C,_A]).

poly_mul(poly(Var,Terms1),poly(Var,Terms2),poly(Var,Terms)) :-
    !,
    true((
        mshare([[Terms]]),
        ground([Var,Terms1,Terms2])
    )),
    term_mul(Terms1,Terms2,Terms),
    true(ground([Var,Terms1,Terms2,Terms])).
poly_mul(poly(Var1,Terms1),poly(Var2,Terms2),poly(Var1,Terms)) :-
    true((
        mshare([[Terms]]),
        ground([Var1,Terms1,Var2,Terms2])
    )),
    Var1 less_than Var2,
    !,
    true((
        mshare([[Terms]]),
        ground([Var1,Terms1,Var2,Terms2])
    )),
    mul_through(Terms1,poly(Var2,Terms2),Terms),
    true(ground([Var1,Terms1,Var2,Terms2,Terms])).
poly_mul(P,poly(Var,Terms2),poly(Var,Terms)) :-
    !,
    true((
        mshare([[Terms]]),
        ground([P,Var,Terms2])
    )),
    mul_through(Terms2,P,Terms),
    true(ground([P,Var,Terms2,Terms])).
poly_mul(poly(Var,Terms1),C,poly(Var,Terms)) :-
    !,
    true((
        mshare([[Terms]]),
        ground([C,Var,Terms1])
    )),
    mul_through(Terms1,C,Terms),
    true(ground([C,Var,Terms1,Terms])).
poly_mul(C1,C2,C) :-
    true((
        mshare([[C]]),
        ground([C1,C2])
    )),
    C is C1*C2,
    true(ground([C1,C2,C])).

:- true pred term_mul(_A,_1,Terms)
   : ( mshare([[Terms]]),
       ground([_A,_1]) )
   => ground([_A,_1,Terms]).

term_mul([],_1,[]) :-
    !,
    true(ground([_1])).
term_mul(_1,[],[]) :-
    !,
    true(ground([_1])).
term_mul([Term|Terms1],Terms2,Terms) :-
    true((
        mshare([[Terms],[PartA],[PartB]]),
        ground([Terms2,Term,Terms1])
    )),
    single_term_mul(Terms2,Term,PartA),
    true((
        mshare([[Terms],[PartB]]),
        ground([Terms2,Term,Terms1,PartA])
    )),
    term_mul(Terms1,Terms2,PartB),
    true((
        mshare([[Terms]]),
        ground([Terms2,Term,Terms1,PartA,PartB])
    )),
    term_add(PartA,PartB,Terms),
    true(ground([Terms2,Terms,Term,Terms1,PartA,PartB])).

:- true pred single_term_mul(_A,_1,_B)
   : ( (_1=term(_C,_D)),
       mshare([[_B]]),
       ground([_A,_C,_D]) )
   => ground([_A,_B,_C,_D]).

:- true pred single_term_mul(_A,_1,_B)
   : ( mshare([[_B]]),
       ground([_A,_1]) )
   => ground([_A,_1,_B]).

single_term_mul([],_1,[]) :-
    !,
    true(ground([_1])).
single_term_mul([term(E1,C1)|Terms1],term(E2,C2),[term(E,C)|Terms]) :-
    true((
        mshare([[Terms],[Terms,E],[Terms,E,C],[Terms,C],[E],[E,C],[C]]),
        ground([Terms1,E1,C1,E2,C2])
    )),
    E is E1+E2,
    true((
        mshare([[Terms],[Terms,C],[C]]),
        ground([Terms1,E1,C1,E2,C2,E])
    )),
    poly_mul(C1,C2,C),
    true((
        mshare([[Terms]]),
        ground([Terms1,E1,C1,E2,C2,E,C])
    )),
    single_term_mul(Terms1,term(E2,C2),Terms),
    true(ground([Terms1,E1,C1,E2,C2,Terms,E,C])).

:- true pred mul_through(_A,_1,_B)
   : ( (_1=poly(_C,_D)),
       mshare([[_B]]),
       ground([_A,_C,_D]) )
   => ground([_A,_B,_C,_D]).

:- true pred mul_through(_A,_1,_B)
   : ( mshare([[_B]]),
       ground([_A,_1]) )
   => ground([_A,_1,_B]).

mul_through([],_1,[]) :-
    !,
    true(ground([_1])).
mul_through([term(E,Term)|Terms],Poly,[term(E,NewTerm)|NewTerms]) :-
    true((
        mshare([[NewTerms],[NewTerms,NewTerm],[NewTerm]]),
        ground([Poly,Terms,E,Term])
    )),
    poly_mul(Term,Poly,NewTerm),
    true((
        mshare([[NewTerms]]),
        ground([Poly,Terms,E,Term,NewTerm])
    )),
    mul_through(Terms,Poly,NewTerms),
    true(ground([Poly,Terms,E,Term,NewTerms,NewTerm])).


