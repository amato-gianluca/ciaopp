:- module(_1,[],[default,assertions,nativeprops,dcg]).

:- set_prolog_flag(single_var_warnings,off).

:- set_prolog_flag(multi_arity_warnings,off).

'\006\call_in_module'(reducer,_1) :-
    !,
    call(_1).

:- entry top.

:- true pred top.

top :-
    true((
        mshare([[_Ans1],[_Ans2]]),
        linear(_Ans1),
        linear(_Ans2),
        shlin2([([_Ans1],[_Ans1]),([_Ans2],[_Ans2])])
    )),
    try(fac(3),_Ans1),
    true((
        mshare([[_Ans2]]),
        ground([_Ans1]),
        linear(_Ans2),
        shlin2([([_Ans2],[_Ans2])])
    )),
    try(quick([3,1,2]),_Ans2),
    true(ground([_Ans1,_Ans2])).

:- true pred try(_inpexpr,_anslist)
   : ( (_inpexpr=quick([3,1,2])),
       mshare([[_anslist]]),
       linear(_anslist), shlin2([([_anslist],[_anslist])]) )
   => ground([_anslist]).

:- true pred try(_inpexpr,_anslist)
   : ( (_inpexpr=fac(3)),
       mshare([[_anslist]]),
       linear(_anslist), shlin2([([_anslist],[_anslist])]) )
   => ground([_anslist]).

try(_inpexpr,_anslist) :-
    true((
        mshare([[_anslist],[_list],[_curry],[_ans]]),
        ground([_inpexpr]),
        linear(_anslist),
        linear(_list),
        linear(_curry),
        linear(_ans),
        shlin2([([_anslist],[_anslist]),([_list],[_list]),([_curry],[_curry]),([_ans],[_ans])])
    )),
    listify(_inpexpr,_list),
    true((
        mshare([[_anslist],[_curry],[_ans]]),
        ground([_inpexpr,_list]),
        linear(_anslist),
        linear(_curry),
        linear(_ans),
        shlin2([([_anslist],[_anslist]),([_curry],[_curry]),([_ans],[_ans])])
    )),
    curry(_list,_curry),
    true((
        mshare([[_anslist],[_ans]]),
        ground([_inpexpr,_list,_curry]),
        linear(_anslist),
        linear(_ans),
        shlin2([([_anslist],[_anslist]),([_ans],[_ans])])
    )),
    t_reduce(_curry,_ans),
    true((
        mshare([[_anslist]]),
        ground([_inpexpr,_list,_curry,_ans]),
        linear(_anslist),
        shlin2([([_anslist],[_anslist])])
    )),
    make_list(_ans,_anslist),
    true(ground([_inpexpr,_anslist,_list,_curry,_ans])).

:- true pred end(X)
   : ground([X])
   => ground([X]).

:- true pred end(X)
   : ( mshare([[X]]),
       linear(X), shlin2([([X],[X])]) )
   => ground([X]).

end(X) :-
    true((mshare([[X]]),linear(X),shlin2([([X],[X])]);ground([X]))),
    atom(X),
    !,
    true(ground([X])).
end(X) :-
    true((mshare([[X]]),linear(X),shlin2([([X],[X])]);ground([X]))),
    X==[],
    true(ground([X])).

:- true pred list_functor_name(Name)
   : ground([Name])
   => ground([Name]).

:- true pred list_functor_name(Name)
   : ( mshare([[Name]]),
       linear(Name), shlin2([([Name],[Name])]) )
   => ground([Name]).

list_functor_name(Name) :-
    true((mshare([[Name],[_1],[_2],[_3]]),linear(Name),linear(_1),linear(_2),linear(_3),shlin2([([Name],[Name]),([_1],[_1]),([_2],[_2]),([_3],[_3])]);mshare([[_1],[_2],[_3]]),ground([Name]),linear(_1),linear(_2),linear(_3),shlin2([([_1],[_1]),([_2],[_2]),([_3],[_3])]))),
    atom(Name),
    !,
    true((
        mshare([[_1],[_2],[_3]]),
        ground([Name]),
        linear(_1),
        linear(_2),
        linear(_3),
        shlin2([([_1],[_1]),([_2],[_2]),([_3],[_3])])
    )),
    functor([_2|_3],Name,_1),
    true((
        mshare([[_2],[_3]]),
        ground([Name,_1]),
        linear(_2),
        linear(_3),
        shlin2([([_2],[_2]),([_3],[_3])])
    )).
list_functor_name(Name) :-
    true((mshare([[Name],[_4],[_5],[_6]]),linear(Name),linear(_4),linear(_5),linear(_6),shlin2([([Name],[Name]),([_4],[_4]),([_5],[_5]),([_6],[_6])]);mshare([[_4],[_5],[_6]]),ground([Name]),linear(_4),linear(_5),linear(_6),shlin2([([_4],[_4]),([_5],[_5]),([_6],[_6])]))),
    var(Name),
    !,
    true((fails(_);mshare([[Name],[_4],[_5],[_6]]),linear(Name),linear(_4),linear(_5),linear(_6),shlin2([([Name],[Name]),([_4],[Name,_4]),([_5],[Name,_5]),([_6],[Name,_6])]))),
    functor([_5|_6],Name,_4),
    true((fails(_);mshare([[_5],[_6]]),ground([Name,_4]),linear(_5),linear(_6),shlin2([([_5],[Name,_5]),([_6],[Name,_6])]))).

:- true pred t_def(_A,_B,_C)
   : ( mshare([[_B],[_C]]),
       ground([_A]), linear(_B), linear(_C), shlin2([([_B],[_B]),([_C],[_C])]) )
   => ( mshare([[_B,_C]]),
        ground([_A]), linear(_B), shlin2([([_B,_C],[_B])]) ).

t_def(fac,[N],cond(N=0,1,N*fac(N-1))).
t_def(quick,[_l],cond(_l=[],[],cond(tl(_l)=[],_l,quick2(split(hd(_l),tl(_l)))))).
t_def(quick2,[_l],my_append(quick(hd(_l)),quick(tl(_l)))).
t_def(split,[_e,_l],cond(_l=[],[[_e]],cond(hd(_l)=<_e,inserthead(hd(_l),split(_e,tl(_l))),inserttail(hd(_l),split(_e,tl(_l)))))).
t_def(inserthead,[_e,_l],[[_e|hd(_l)]|tl(_l)]).
t_def(inserttail,[_e,_l],[hd(_l),_e|tl(_l)]).
t_def(my_append,[_a,_b],cond(_a=[],_b,[hd(_a)|my_append(tl(_a),_b)])).

:- true pred t_reduce(_expr,_ans)
   : ( (_ans=[_A,_B|_C]),
       mshare([[_expr],[_A],[_B]]),
       ground([_C]), linear(_expr), linear(_A), linear(_B), shlin2([([_expr],[_expr]),([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[_expr]]),
        ground([_A,_B,_C]), linear(_expr), shlin2([([_expr],[_expr])]) ).

:- true pred t_reduce(_expr,_ans)
   : ( (_ans=[_A,_B|_C]),
       mshare([[_A],[_B]]),
       ground([_expr,_C]), linear(_A), linear(_B), shlin2([([_A],[_A]),([_B],[_B])]) )
   => ground([_expr,_A,_B,_C]).

:- true pred t_reduce(_expr,_ans)
   : ( mshare([[_ans]]),
       ground([_expr]), linear(_ans), shlin2([([_ans],[_ans])]) )
   => ground([_expr,_ans]).

:- true pred t_reduce(_expr,_ans)
   : ( mshare([[_expr],[_ans]]),
       linear(_expr), linear(_ans), shlin2([([_expr],[_expr]),([_ans],[_ans])]) )
   => ( mshare([[_expr]]),
        ground([_ans]), linear(_expr), shlin2([([_expr],[_expr])]) ).

t_reduce(_expr,_ans) :-
    true((mshare([[_expr],[_ans]]),linear(_expr),linear(_ans),shlin2([([_expr],[_expr]),([_ans],[_ans])]);mshare([[_ans]]),ground([_expr]),linear(_ans),shlin2([([_ans],[_ans])]))),
    atomic(_expr),
    !,
    true((
        mshare([[_ans]]),
        ground([_expr]),
        linear(_ans),
        shlin2([([_ans],[_ans])])
    )),
    _ans=_expr,
    true(ground([_expr,_ans])).
t_reduce([_y,_x|LF],[_yr,_xr|LF]) :-
    true((mshare([[_y],[_x],[LF],[_yr],[_xr]]),linear(_y),linear(_x),linear(LF),linear(_yr),linear(_xr),shlin2([([_y],[_y]),([_x],[_x]),([LF],[LF]),([_yr],[_yr]),([_xr],[_xr])]);mshare([[_y],[_x],[_yr],[_xr]]),ground([LF]),linear(_y),linear(_x),linear(_yr),linear(_xr),shlin2([([_y],[_y]),([_x],[_x]),([_yr],[_yr]),([_xr],[_xr])]);mshare([[_yr],[_xr]]),ground([_y,_x,LF]),linear(_yr),linear(_xr),shlin2([([_yr],[_yr]),([_xr],[_xr])]))),
    list_functor_name(LF),
    true((mshare([[_y],[_x],[_yr],[_xr]]),ground([LF]),linear(_y),linear(_x),linear(_yr),linear(_xr),shlin2([([_y],[_y]),([_x],[_x]),([_yr],[_yr]),([_xr],[_xr])]);mshare([[_yr],[_xr]]),ground([_y,_x,LF]),linear(_yr),linear(_xr),shlin2([([_yr],[_yr]),([_xr],[_xr])]))),
    t_reduce(_x,_xr),
    !,
    true((mshare([[_y],[_x],[_yr]]),ground([LF,_xr]),linear(_y),linear(_x),linear(_yr),shlin2([([_y],[_y]),([_x],[_x]),([_yr],[_yr])]);mshare([[_yr]]),ground([_y,_x,LF,_xr]),linear(_yr),shlin2([([_yr],[_yr])]))),
    t_reduce(_y,_yr),
    !,
    true((mshare([[_y],[_x]]),ground([LF,_yr,_xr]),linear(_y),linear(_x),shlin2([([_y],[_y]),([_x],[_x])]);ground([_y,_x,LF,_yr,_xr]))).
t_reduce(_expr,_ans) :-
    true((mshare([[_expr],[_ans],[_next],[_red],[_form]]),linear(_expr),linear(_ans),linear(_next),linear(_red),linear(_form),shlin2([([_expr],[_expr]),([_ans],[_ans]),([_next],[_next]),([_red],[_red]),([_form],[_form])]);mshare([[_ans],[_next],[_red],[_form]]),ground([_expr]),linear(_ans),linear(_next),linear(_red),linear(_form),shlin2([([_ans],[_ans]),([_next],[_next]),([_red],[_red]),([_form],[_form])]))),
    t_append(_next,_red,_form,_expr),
    true((mshare([[_expr,_next],[_expr,_form],[_ans],[_next,_red]]),linear(_expr),linear(_ans),linear(_next),linear(_red),linear(_form),shlin2([([_expr,_next],[_expr,_next]),([_expr,_form],[_expr,_form]),([_ans],[_ans]),([_next,_red],[_next,_red])]);mshare([[_ans],[_next,_red]]),ground([_expr,_form]),linear(_ans),linear(_next),linear(_red),shlin2([([_ans],[_ans]),([_next,_red],[_next,_red])]))),
    t_redex(_form,_red),
    !,
    true((mshare([[_expr,_next],[_expr,_next,_red,_form],[_expr,_form],[_ans],[_next,_red]]),linear(_expr),linear(_ans),linear(_next),linear(_red),linear(_form),shlin2([([_expr,_next],[_expr,_next]),([_expr,_next,_red,_form],[_expr,_next,_red,_form]),([_expr,_form],[_expr,_form]),([_ans],[_ans]),([_next,_red],[_next,_red])]);mshare([[_ans],[_next,_red]]),ground([_expr,_form]),linear(_ans),linear(_next),linear(_red),shlin2([([_ans],[_ans]),([_next,_red],[_next,_red])]))),
    t_reduce(_next,_ans),
    !,
    true((mshare([[_expr,_next],[_expr,_next,_red,_form],[_expr,_form],[_next,_red]]),ground([_ans]),linear(_expr),linear(_next),linear(_red),linear(_form),shlin2([([_expr,_next],[_expr,_next]),([_expr,_next,_red,_form],[_expr,_next,_red,_form]),([_expr,_form],[_expr,_form]),([_next,_red],[_next,_red])]);mshare([[_next,_red]]),ground([_expr,_ans,_form]),linear(_next),linear(_red),shlin2([([_next,_red],[_next,_red])]))).

:- true pred t_append(_link,_A,_l,_B)
   : ( mshare([[_link],[_A],[_l],[_B]]),
       linear(_link), linear(_A), linear(_l), linear(_B), shlin2([([_link],[_link]),([_A],[_A]),([_l],[_l]),([_B],[_B])]) )
   => ( mshare([[_link,_A],[_link,_B],[_l,_B]]),
        linear(_link), linear(_A), linear(_l), linear(_B), shlin2([([_link,_A],[_link,_A]),([_link,_B],[_link,_B]),([_l,_B],[_l,_B])]) ).

:- true pred t_append(_link,_A,_l,_B)
   : ( mshare([[_link],[_A],[_l]]),
       ground([_B]), linear(_link), linear(_A), linear(_l), shlin2([([_link],[_link]),([_A],[_A]),([_l],[_l])]) )
   => ( mshare([[_link,_A]]),
        ground([_l,_B]), linear(_link), linear(_A), shlin2([([_link,_A],[_link,_A])]) ).

t_append(_link,_link,_l,_l).
t_append([_a|_l1],_link,_l2,[_a|_l3]) :-
    true((mshare([[_link],[_l2],[_a],[_l1],[_l3]]),linear(_link),linear(_l2),linear(_a),linear(_l1),linear(_l3),shlin2([([_link],[_link]),([_l2],[_l2]),([_a],[_a]),([_l1],[_l1]),([_l3],[_l3])]);mshare([[_link],[_l2],[_l1]]),ground([_a,_l3]),linear(_link),linear(_l2),linear(_l1),shlin2([([_link],[_link]),([_l2],[_l2]),([_l1],[_l1])]))),
    t_append(_l1,_link,_l2,_l3),
    true((mshare([[_link,_l1]]),ground([_l2,_a,_l3]),linear(_link),linear(_l1),shlin2([([_link,_l1],[_link,_l1])]);mshare([[_link,_l1],[_l2,_l3],[_a],[_l1,_l3]]),linear(_link),linear(_l2),linear(_a),linear(_l1),linear(_l3),shlin2([([_link,_l1],[_link,_l1]),([_l2,_l3],[_l2,_l3]),([_a],[_a]),([_l1,_l3],[_l1,_l3])]))).

:- true pred t_redex(_in,_x)
   : ( mshare([[_in],[_x]]),
       linear(_in), linear(_x), shlin2([([_in],[_in]),([_x],[_x])]) )
   => ( mshare([[_in],[_in,_x],[_x]]),
        linear(_in), linear(_x), shlin2([([_in],[_in]),([_in,_x],[_in,_x]),([_x],[_x])]) ).

:- true pred t_redex(_in,_x)
   : ( mshare([[_x]]),
       ground([_in]), linear(_x), shlin2([([_x],[_x])]) )
   => ( mshare([[_x]]),
        ground([_in]), linear(_x), shlin2([([_x],[_x])]) ).

t_redex([_x,_g,_f,_k|sp],[[_xr|_g],[_xr|_f]|_k]) :-
    true((mshare([[_x],[_g],[_f],[_k],[_xr]]),linear(_x),linear(_g),linear(_f),linear(_k),linear(_xr),shlin2([([_x],[_x]),([_g],[_g]),([_f],[_f]),([_k],[_k]),([_xr],[_xr])]);mshare([[_xr]]),ground([_x,_g,_f,_k]),linear(_xr),shlin2([([_xr],[_xr])]))),
    t_reduce(_x,_xr),
    true((mshare([[_x],[_g],[_f],[_k]]),ground([_xr]),linear(_x),linear(_g),linear(_f),linear(_k),shlin2([([_x],[_x]),([_g],[_g]),([_f],[_f]),([_k],[_k])]);ground([_x,_g,_f,_k,_xr]))).
t_redex([_x,_g,_f,_k|bp],[[_x|_g],_f|_k]).
t_redex([_x,_g,_f,_k|cp],[_g,[_x|_f]|_k]).
t_redex([_x,_g,_f|s],[[_xr|_g],_xr|_f]) :-
    true((mshare([[_x],[_g],[_f],[_xr]]),linear(_x),linear(_g),linear(_f),linear(_xr),shlin2([([_x],[_x]),([_g],[_g]),([_f],[_f]),([_xr],[_xr])]);mshare([[_xr]]),ground([_x,_g,_f]),linear(_xr),shlin2([([_xr],[_xr])]))),
    t_reduce(_x,_xr),
    true((mshare([[_x],[_g],[_f]]),ground([_xr]),linear(_x),linear(_g),linear(_f),shlin2([([_x],[_x]),([_g],[_g]),([_f],[_f])]);ground([_x,_g,_f,_xr]))).
t_redex([_x,_g,_f|b],[[_x|_g]|_f]).
t_redex([_x,_g,_f|c],[_g,_x|_f]).
t_redex([_y,_x|k],_x).
t_redex([_x|i],_x).
t_redex([_elsepart,_ifpart,_cond|cond],_ifpart) :-
    true((mshare([[_ifpart],[_elsepart],[_cond],[_bool]]),linear(_ifpart),linear(_elsepart),linear(_cond),linear(_bool),shlin2([([_ifpart],[_ifpart]),([_elsepart],[_elsepart]),([_cond],[_cond]),([_bool],[_bool])]);mshare([[_bool]]),ground([_ifpart,_elsepart,_cond]),linear(_bool),shlin2([([_bool],[_bool])]))),
    t_reduce(_cond,_bool),
    true((mshare([[_ifpart],[_elsepart],[_cond]]),ground([_bool]),linear(_ifpart),linear(_elsepart),linear(_cond),shlin2([([_ifpart],[_ifpart]),([_elsepart],[_elsepart]),([_cond],[_cond])]);ground([_ifpart,_elsepart,_cond,_bool]))),
    _bool=true,
    !,
    true((mshare([[_ifpart],[_elsepart],[_cond]]),ground([_bool]),linear(_ifpart),linear(_elsepart),linear(_cond),shlin2([([_ifpart],[_ifpart]),([_elsepart],[_elsepart]),([_cond],[_cond])]);ground([_ifpart,_elsepart,_cond,_bool]))).
t_redex([_elsepart,_ifpart,_cond|cond],_elsepart).
t_redex([_f|apply],_fr) :-
    true((mshare([[_fr]]),ground([_f]),linear(_fr),shlin2([([_fr],[_fr])]);mshare([[_fr],[_f]]),linear(_fr),linear(_f),shlin2([([_fr],[_fr]),([_f],[_f])]))),
    t_reduce(_f,_fr),
    true((mshare([[_f]]),ground([_fr]),linear(_f),shlin2([([_f],[_f])]);ground([_fr,_f]))).
t_redex([_arg|hd],_x) :-
    true((mshare([[_x],[_arg],[LF],[_y]]),linear(_x),linear(_arg),linear(LF),linear(_y),shlin2([([_x],[_x]),([_arg],[_arg]),([LF],[LF]),([_y],[_y])]);mshare([[_x],[LF],[_y]]),ground([_arg]),linear(_x),linear(LF),linear(_y),shlin2([([_x],[_x]),([LF],[LF]),([_y],[_y])]))),
    list_functor_name(LF),
    true((mshare([[_x],[_arg],[_y]]),ground([LF]),linear(_x),linear(_arg),linear(_y),shlin2([([_x],[_x]),([_arg],[_arg]),([_y],[_y])]);mshare([[_x],[_y]]),ground([_arg,LF]),linear(_x),linear(_y),shlin2([([_x],[_x]),([_y],[_y])]))),
    t_reduce(_arg,[_y,_x|LF]),
    true((mshare([[_arg]]),ground([_x,LF,_y]),linear(_arg),shlin2([([_arg],[_arg])]);ground([_x,_arg,LF,_y]))).
t_redex([_arg|tl],_y) :-
    true((mshare([[_y],[_arg],[LF],[_x]]),linear(_y),linear(_arg),linear(LF),linear(_x),shlin2([([_y],[_y]),([_arg],[_arg]),([LF],[LF]),([_x],[_x])]);mshare([[_y],[LF],[_x]]),ground([_arg]),linear(_y),linear(LF),linear(_x),shlin2([([_y],[_y]),([LF],[LF]),([_x],[_x])]))),
    list_functor_name(LF),
    true((mshare([[_y],[_arg],[_x]]),ground([LF]),linear(_y),linear(_arg),linear(_x),shlin2([([_y],[_y]),([_arg],[_arg]),([_x],[_x])]);mshare([[_y],[_x]]),ground([_arg,LF]),linear(_y),linear(_x),shlin2([([_y],[_y]),([_x],[_x])]))),
    t_reduce(_arg,[_y,_x|LF]),
    true((mshare([[_arg]]),ground([_y,LF,_x]),linear(_arg),shlin2([([_arg],[_arg])]);ground([_y,_arg,LF,_x]))).
t_redex([_y,_x|_op],_res) :-
    true((mshare([[_res],[_y],[_x],[_op],[_xres],[_yres]]),linear(_res),linear(_y),linear(_x),linear(_op),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x]),([_op],[_op]),([_xres],[_xres]),([_yres],[_yres])]);mshare([[_res],[_xres],[_yres]]),ground([_y,_x,_op]),linear(_res),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_xres],[_xres]),([_yres],[_yres])]))),
    end(_op),
    true((mshare([[_res],[_y],[_x],[_xres],[_yres]]),ground([_op]),linear(_res),linear(_y),linear(_x),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x]),([_xres],[_xres]),([_yres],[_yres])]);mshare([[_res],[_xres],[_yres]]),ground([_y,_x,_op]),linear(_res),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_xres],[_xres]),([_yres],[_yres])]))),
    my_member(_op,[+,-,*,//,mod]),
    true((mshare([[_res],[_y],[_x],[_xres],[_yres]]),ground([_op]),linear(_res),linear(_y),linear(_x),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x]),([_xres],[_xres]),([_yres],[_yres])]);mshare([[_res],[_xres],[_yres]]),ground([_y,_x,_op]),linear(_res),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_xres],[_xres]),([_yres],[_yres])]))),
    t_reduce(_x,_xres),
    true((mshare([[_res],[_y],[_x],[_yres]]),ground([_op,_xres]),linear(_res),linear(_y),linear(_x),linear(_yres),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x]),([_yres],[_yres])]);mshare([[_res],[_yres]]),ground([_y,_x,_op,_xres]),linear(_res),linear(_yres),shlin2([([_res],[_res]),([_yres],[_yres])]))),
    t_reduce(_y,_yres),
    true((mshare([[_res]]),ground([_y,_x,_op,_xres,_yres]),linear(_res),shlin2([([_res],[_res])]);mshare([[_res],[_y],[_x]]),ground([_op,_xres,_yres]),linear(_res),linear(_y),linear(_x),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x])]))),
    number(_xres),
    true((mshare([[_res]]),ground([_y,_x,_op,_xres,_yres]),linear(_res),shlin2([([_res],[_res])]);mshare([[_res],[_y],[_x]]),ground([_op,_xres,_yres]),linear(_res),linear(_y),linear(_x),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x])]))),
    number(_yres),
    true((mshare([[_res]]),ground([_y,_x,_op,_xres,_yres]),linear(_res),shlin2([([_res],[_res])]);mshare([[_res],[_y],[_x]]),ground([_op,_xres,_yres]),linear(_res),linear(_y),linear(_x),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x])]))),
    eval(_op,_res,_xres,_yres),
    true((mshare([[_y],[_x]]),ground([_res,_op,_xres,_yres]),linear(_y),linear(_x),shlin2([([_y],[_y]),([_x],[_x])]);ground([_res,_y,_x,_op,_xres,_yres]))).
t_redex([_y,_x|_test],_res) :-
    true((mshare([[_res],[_y],[_x],[_test],[_xres],[_yres]]),linear(_res),linear(_y),linear(_x),linear(_test),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x]),([_test],[_test]),([_xres],[_xres]),([_yres],[_yres])]);mshare([[_res],[_xres],[_yres]]),ground([_y,_x,_test]),linear(_res),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_xres],[_xres]),([_yres],[_yres])]))),
    end(_test),
    true((mshare([[_res],[_y],[_x],[_xres],[_yres]]),ground([_test]),linear(_res),linear(_y),linear(_x),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x]),([_xres],[_xres]),([_yres],[_yres])]);mshare([[_res],[_xres],[_yres]]),ground([_y,_x,_test]),linear(_res),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_xres],[_xres]),([_yres],[_yres])]))),
    my_member(_test,[<,>,=<,>=,=\=,=:=]),
    true((mshare([[_res],[_y],[_x],[_xres],[_yres]]),ground([_test]),linear(_res),linear(_y),linear(_x),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x]),([_xres],[_xres]),([_yres],[_yres])]);mshare([[_res],[_xres],[_yres]]),ground([_y,_x,_test]),linear(_res),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_xres],[_xres]),([_yres],[_yres])]))),
    t_reduce(_x,_xres),
    true((mshare([[_res],[_y],[_x],[_yres]]),ground([_test,_xres]),linear(_res),linear(_y),linear(_x),linear(_yres),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x]),([_yres],[_yres])]);mshare([[_res],[_yres]]),ground([_y,_x,_test,_xres]),linear(_res),linear(_yres),shlin2([([_res],[_res]),([_yres],[_yres])]))),
    t_reduce(_y,_yres),
    true((mshare([[_res]]),ground([_y,_x,_test,_xres,_yres]),linear(_res),shlin2([([_res],[_res])]);mshare([[_res],[_y],[_x]]),ground([_test,_xres,_yres]),linear(_res),linear(_y),linear(_x),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x])]))),
    number(_xres),
    true((mshare([[_res]]),ground([_y,_x,_test,_xres,_yres]),linear(_res),shlin2([([_res],[_res])]);mshare([[_res],[_y],[_x]]),ground([_test,_xres,_yres]),linear(_res),linear(_y),linear(_x),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x])]))),
    number(_yres),
    true((mshare([[_res]]),ground([_y,_x,_test,_xres,_yres]),linear(_res),shlin2([([_res],[_res])]);mshare([[_res],[_y],[_x]]),ground([_test,_xres,_yres]),linear(_res),linear(_y),linear(_x),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x])]))),
    't_redex/2/15/$disj/1'(_res,_test,_xres,_yres),
    !,
    true((mshare([[_y],[_x]]),ground([_res,_test,_xres,_yres]),linear(_y),linear(_x),shlin2([([_y],[_y]),([_x],[_x])]);ground([_res,_y,_x,_test,_xres,_yres]))).
t_redex([_y,_x|=],_res) :-
    true((mshare([[_res],[_y],[_x],[_xres],[_yres]]),linear(_res),linear(_y),linear(_x),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x]),([_xres],[_xres]),([_yres],[_yres])]);mshare([[_res],[_xres],[_yres]]),ground([_y,_x]),linear(_res),linear(_xres),linear(_yres),shlin2([([_res],[_res]),([_xres],[_xres]),([_yres],[_yres])]))),
    t_reduce(_x,_xres),
    true((mshare([[_res],[_y],[_x],[_yres]]),ground([_xres]),linear(_res),linear(_y),linear(_x),linear(_yres),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x]),([_yres],[_yres])]);mshare([[_res],[_yres]]),ground([_y,_x,_xres]),linear(_res),linear(_yres),shlin2([([_res],[_res]),([_yres],[_yres])]))),
    t_reduce(_y,_yres),
    true((mshare([[_res]]),ground([_y,_x,_xres,_yres]),linear(_res),shlin2([([_res],[_res])]);mshare([[_res],[_y],[_x]]),ground([_xres,_yres]),linear(_res),linear(_y),linear(_x),shlin2([([_res],[_res]),([_y],[_y]),([_x],[_x])]))),
    't_redex/2/16/$disj/1'(_res,_xres,_yres),
    !,
    true((mshare([[_y],[_x]]),ground([_res,_xres,_yres]),linear(_y),linear(_x),shlin2([([_y],[_y]),([_x],[_x])]);ground([_res,_y,_x,_xres,_yres]))).
t_redex([_x|_op],_res) :-
    true((mshare([[_res],[_x],[_op],[_xres],[_t]]),linear(_res),linear(_x),linear(_op),linear(_xres),linear(_t),shlin2([([_res],[_res]),([_x],[_x]),([_op],[_op]),([_xres],[_xres]),([_t],[_t])]);mshare([[_res],[_xres],[_t]]),ground([_x,_op]),linear(_res),linear(_xres),linear(_t),shlin2([([_res],[_res]),([_xres],[_xres]),([_t],[_t])]))),
    end(_op),
    true((mshare([[_res],[_x],[_xres],[_t]]),ground([_op]),linear(_res),linear(_x),linear(_xres),linear(_t),shlin2([([_res],[_res]),([_x],[_x]),([_xres],[_xres]),([_t],[_t])]);mshare([[_res],[_xres],[_t]]),ground([_x,_op]),linear(_res),linear(_xres),linear(_t),shlin2([([_res],[_res]),([_xres],[_xres]),([_t],[_t])]))),
    my_member(_op,[-]),
    true((mshare([[_res],[_x],[_xres],[_t]]),ground([_op]),linear(_res),linear(_x),linear(_xres),linear(_t),shlin2([([_res],[_res]),([_x],[_x]),([_xres],[_xres]),([_t],[_t])]);mshare([[_res],[_xres],[_t]]),ground([_x,_op]),linear(_res),linear(_xres),linear(_t),shlin2([([_res],[_res]),([_xres],[_xres]),([_t],[_t])]))),
    t_reduce(_x,_xres),
    true((mshare([[_res],[_x],[_t]]),ground([_op,_xres]),linear(_res),linear(_x),linear(_t),shlin2([([_res],[_res]),([_x],[_x]),([_t],[_t])]);mshare([[_res],[_t]]),ground([_x,_op,_xres]),linear(_res),linear(_t),shlin2([([_res],[_res]),([_t],[_t])]))),
    number(_xres),
    true((mshare([[_res],[_x],[_t]]),ground([_op,_xres]),linear(_res),linear(_x),linear(_t),shlin2([([_res],[_res]),([_x],[_x]),([_t],[_t])]);mshare([[_res],[_t]]),ground([_x,_op,_xres]),linear(_res),linear(_t),shlin2([([_res],[_res]),([_t],[_t])]))),
    eval1(_op,_t,_xres),
    true((mshare([[_res]]),ground([_x,_op,_xres,_t]),linear(_res),shlin2([([_res],[_res])]);mshare([[_res],[_x]]),ground([_op,_xres,_t]),linear(_res),linear(_x),shlin2([([_res],[_res]),([_x],[_x])]))).
t_redex(_in,_out) :-
    true((mshare([[_in],[_out],[_par],[_func],[_args],[_expr],[_def]]),linear(_in),linear(_out),linear(_par),linear(_func),linear(_args),linear(_expr),linear(_def),shlin2([([_in],[_in]),([_out],[_out]),([_par],[_par]),([_func],[_func]),([_args],[_args]),([_expr],[_expr]),([_def],[_def])]);mshare([[_out],[_par],[_func],[_args],[_expr],[_def]]),ground([_in]),linear(_out),linear(_par),linear(_func),linear(_args),linear(_expr),linear(_def),shlin2([([_out],[_out]),([_par],[_par]),([_func],[_func]),([_args],[_args]),([_expr],[_expr]),([_def],[_def])]))),
    my_append(_par,_func,_in),
    true((mshare([[_in,_par],[_in,_func],[_out],[_args],[_expr],[_def]]),linear(_in),linear(_out),linear(_par),linear(_func),linear(_args),linear(_expr),linear(_def),shlin2([([_in,_par],[_in,_par]),([_in,_func],[_in,_func]),([_out],[_out]),([_args],[_args]),([_expr],[_expr]),([_def],[_def])]);mshare([[_out],[_args],[_expr],[_def]]),ground([_in,_par,_func]),linear(_out),linear(_args),linear(_expr),linear(_def),shlin2([([_out],[_out]),([_args],[_args]),([_expr],[_expr]),([_def],[_def])]))),
    end(_func),
    true((mshare([[_in,_par],[_out],[_args],[_expr],[_def]]),ground([_func]),linear(_in),linear(_out),linear(_par),linear(_args),linear(_expr),linear(_def),shlin2([([_in,_par],[_in,_par]),([_out],[_out]),([_args],[_args]),([_expr],[_expr]),([_def],[_def])]);mshare([[_out],[_args],[_expr],[_def]]),ground([_in,_par,_func]),linear(_out),linear(_args),linear(_expr),linear(_def),shlin2([([_out],[_out]),([_args],[_args]),([_expr],[_expr]),([_def],[_def])]))),
    t_def(_func,_args,_expr),
    true((mshare([[_in,_par],[_out],[_args,_expr],[_def]]),ground([_func]),linear(_in),linear(_out),linear(_par),linear(_args),linear(_def),shlin2([([_in,_par],[_in,_par]),([_out],[_out]),([_args,_expr],[_args]),([_def],[_def])]);mshare([[_out],[_args,_expr],[_def]]),ground([_in,_par,_func]),linear(_out),linear(_args),linear(_def),shlin2([([_out],[_out]),([_args,_expr],[_args]),([_def],[_def])]))),
    t(_args,_expr,_def),
    true((mshare([[_in,_par],[_out],[_args,_expr]]),ground([_func,_def]),linear(_in),linear(_out),linear(_par),shlin2([([_in,_par],[_in,_par]),([_out],[_out]),([_args,_expr],[])]);mshare([[_out],[_args,_expr]]),ground([_in,_par,_func,_def]),linear(_out),shlin2([([_out],[_out]),([_args,_expr],[])]))),
    my_append(_par,_def,_out),
    true((mshare([[_in,_out,_par],[_args,_expr]]),ground([_func,_def]),linear(_in),linear(_out),linear(_par),shlin2([([_in,_out,_par],[_in,_out,_par]),([_args,_expr],[])]);mshare([[_args,_expr]]),ground([_in,_out,_par,_func,_def]),shlin2([([_args,_expr],[])]))).

:- true pred 't_redex/2/15/$disj/1'(_res,_test,_xres,_yres)
   : ( mshare([[_res]]),
       ground([_test,_xres,_yres]), linear(_res), shlin2([([_res],[_res])]) )
   => ground([_res,_test,_xres,_yres]).

't_redex/2/15/$disj/1'(_res,_test,_xres,_yres) :-
    true((
        mshare([[_res]]),
        ground([_test,_xres,_yres]),
        linear(_res),
        shlin2([([_res],[_res])])
    )),
    relop(_test,_xres,_yres),
    !,
    true((
        mshare([[_res]]),
        ground([_test,_xres,_yres]),
        linear(_res),
        shlin2([([_res],[_res])])
    )),
    _res=true,
    true(ground([_res,_test,_xres,_yres])).
't_redex/2/15/$disj/1'(_res,_test,_xres,_yres) :-
    true((
        mshare([[_res]]),
        ground([_test,_xres,_yres]),
        linear(_res),
        shlin2([([_res],[_res])])
    )),
    _res=false,
    true(ground([_res,_test,_xres,_yres])).

:- true pred 't_redex/2/16/$disj/1'(_res,_xres,_yres)
   : ( mshare([[_res]]),
       ground([_xres,_yres]), linear(_res), shlin2([([_res],[_res])]) )
   => ground([_res,_xres,_yres]).

't_redex/2/16/$disj/1'(_res,_xres,_yres) :-
    true((
        mshare([[_res]]),
        ground([_xres,_yres]),
        linear(_res),
        shlin2([([_res],[_res])])
    )),
    _xres=_yres,
    !,
    true((
        mshare([[_res]]),
        ground([_xres,_yres]),
        linear(_res),
        shlin2([([_res],[_res])])
    )),
    _res=true,
    true(ground([_res,_xres,_yres])).
't_redex/2/16/$disj/1'(_res,_xres,_yres) :-
    true((
        mshare([[_res]]),
        ground([_xres,_yres]),
        linear(_res),
        shlin2([([_res],[_res])])
    )),
    _res=false,
    true(ground([_res,_xres,_yres])).

:- true pred eval(_A,C,A,B)
   : ( mshare([[C]]),
       ground([_A,A,B]), linear(C), shlin2([([C],[C])]) )
   => ground([_A,C,A,B]).

eval(+,C,A,B) :-
    true((
        mshare([[C]]),
        ground([A,B]),
        linear(C),
        shlin2([([C],[C])])
    )),
    C is A+B,
    true(ground([C,A,B])).
eval(-,C,A,B) :-
    true((
        mshare([[C]]),
        ground([A,B]),
        linear(C),
        shlin2([([C],[C])])
    )),
    C is A-B,
    true(ground([C,A,B])).
eval(*,C,A,B) :-
    true((
        mshare([[C]]),
        ground([A,B]),
        linear(C),
        shlin2([([C],[C])])
    )),
    C is A*B,
    true(ground([C,A,B])).
eval(//,C,A,B) :-
    true((
        mshare([[C]]),
        ground([A,B]),
        linear(C),
        shlin2([([C],[C])])
    )),
    C is A//B,
    true(ground([C,A,B])).
eval(mod,C,A,B) :-
    true((
        mshare([[C]]),
        ground([A,B]),
        linear(C),
        shlin2([([C],[C])])
    )),
    C is A mod B,
    true(ground([C,A,B])).

:- true pred eval1(_A,C,A)
   : ( mshare([[C]]),
       ground([_A,A]), linear(C), shlin2([([C],[C])]) )
   => ground([_A,C,A]).

eval1(-,C,A) :-
    true((
        mshare([[C]]),
        ground([A]),
        linear(C),
        shlin2([([C],[C])])
    )),
    C is-A,
    true(ground([C,A])).

:- true pred relop(_A,A,B)
   : ground([_A,A,B])
   => ground([_A,A,B]).

relop(<,A,B) :-
    true(ground([A,B])),
    A<B,
    true(ground([A,B])).
relop(>,A,B) :-
    true(ground([A,B])),
    A>B,
    true(ground([A,B])).
relop(=<,A,B) :-
    true(ground([A,B])),
    A=<B,
    true(ground([A,B])).
relop(>=,A,B) :-
    true(ground([A,B])),
    A>=B,
    true(ground([A,B])).
relop(=\=,A,B) :-
    true(ground([A,B])),
    A=\=B,
    true(ground([A,B])).
relop(=:=,A,B) :-
    true(ground([A,B])),
    A=:=B,
    true(ground([A,B])).

:- true pred t(_argvars,_expr,_trans)
   : ( mshare([[_argvars,_expr],[_trans]]),
       linear(_argvars), linear(_trans), shlin2([([_argvars,_expr],[_argvars]),([_trans],[_trans])]) )
   => ( mshare([[_argvars,_expr]]),
        ground([_trans]), shlin2([([_argvars,_expr],[])]) ).

t(_argvars,_expr,_trans) :-
    true((
        mshare([[_argvars,_expr],[_trans],[_list],[_curry]]),
        linear(_argvars),
        linear(_trans),
        linear(_list),
        linear(_curry),
        shlin2([([_argvars,_expr],[_argvars]),([_trans],[_trans]),([_list],[_list]),([_curry],[_curry])])
    )),
    listify(_expr,_list),
    true((
        mshare([[_argvars,_expr],[_trans],[_curry]]),
        ground([_list]),
        linear(_trans),
        linear(_curry),
        shlin2([([_argvars,_expr],[]),([_trans],[_trans]),([_curry],[_curry])])
    )),
    curry(_list,_curry),
    true((
        mshare([[_argvars,_expr],[_trans]]),
        ground([_list,_curry]),
        linear(_trans),
        shlin2([([_argvars,_expr],[]),([_trans],[_trans])])
    )),
    t_argvars(_argvars,_curry,_trans),
    !,
    true((
        mshare([[_argvars,_expr]]),
        ground([_trans,_list,_curry]),
        shlin2([([_argvars,_expr],[])])
    )).

:- true pred t_argvars(_A,_trans,_B)
   : ( mshare([[_A],[_B]]),
       ground([_trans]), linear(_B), shlin2([([_A],[]),([_B],[_B])]) )
   => ( mshare([[_A]]),
        ground([_trans,_B]), shlin2([([_A],[])]) ).

t_argvars([],_trans,_trans).
t_argvars([_x|_argvars],_in,_trans) :-
    true((
        mshare([[_trans],[_x],[_x,_argvars],[_argvars],[_mid],[_vars]]),
        ground([_in]),
        linear(_trans),
        linear(_mid),
        linear(_vars),
        shlin2([([_trans],[_trans]),([_x],[]),([_x,_argvars],[]),([_argvars],[]),([_mid],[_mid]),([_vars],[_vars])])
    )),
    t_argvars(_argvars,_in,_mid),
    true((
        mshare([[_trans],[_x],[_x,_argvars],[_argvars],[_vars]]),
        ground([_in,_mid]),
        linear(_trans),
        linear(_vars),
        shlin2([([_trans],[_trans]),([_x],[]),([_x,_argvars],[]),([_argvars],[]),([_vars],[_vars])])
    )),
    t_vars(_mid,_vars),
    true((
        mshare([[_trans],[_x],[_x,_argvars],[_argvars]]),
        ground([_in,_mid,_vars]),
        linear(_trans),
        shlin2([([_trans],[_trans]),([_x],[]),([_x,_argvars],[]),([_argvars],[])])
    )),
    t_trans(_x,_mid,_vars,_trans),
    true((
        mshare([[_x],[_x,_argvars],[_argvars]]),
        ground([_in,_trans,_mid,_vars]),
        shlin2([([_x],[]),([_x,_argvars],[]),([_argvars],[])])
    )).

:- true pred curry(_a,_cargs)
   : ( mshare([[_cargs]]),
       ground([_a]), linear(_cargs), shlin2([([_cargs],[_cargs])]) )
   => ground([_a,_cargs]).

curry(_a,_a) :-
    true(ground([_a])),
    'curry/2/1/$disj/1'(_a),
    !,
    true(ground([_a])).
curry([_func|_args],_cargs) :-
    true((
        mshare([[_cargs]]),
        ground([_func,_args]),
        linear(_cargs),
        shlin2([([_cargs],[_cargs])])
    )),
    currylist(_args,_cargs,_func),
    true(ground([_cargs,_func,_args])).

:- true pred 'curry/2/1/$disj/1'(_a)
   : ground([_a])
   => ground([_a]).

'curry/2/1/$disj/1'(_a) :-
    true(ground([_a])),
    var(_a),
    true(fails(_)).
'curry/2/1/$disj/1'(_a) :-
    true(ground([_a])),
    atomic(_a),
    true(ground([_a])).

:- true pred currylist(_A,_link,_B)
   : ( (_B=[_C|_D]),
       mshare([[_link]]),
       ground([_A,_C,_D]), linear(_link), shlin2([([_link],[_link])]) )
   => ground([_A,_link,_C,_D]).

:- true pred currylist(_A,_link,_B)
   : ( mshare([[_link]]),
       ground([_A,_B]), linear(_link), shlin2([([_link],[_link])]) )
   => ground([_A,_link,_B]).

currylist([],_link,_link) :-
    !,
    true(ground([_link])).
currylist([_a|_args],_cargs,_link) :-
    true((
        mshare([[_cargs],[_c]]),
        ground([_link,_a,_args]),
        linear(_cargs),
        linear(_c),
        shlin2([([_cargs],[_cargs]),([_c],[_c])])
    )),
    curry(_a,_c),
    true((
        mshare([[_cargs]]),
        ground([_link,_a,_args,_c]),
        linear(_cargs),
        shlin2([([_cargs],[_cargs])])
    )),
    currylist(_args,_cargs,[_c|_link]),
    true(ground([_cargs,_link,_a,_args,_c])).

:- true pred t_vars(_v,_A)
   : ( mshare([[_A]]),
       ground([_v]), linear(_A), shlin2([([_A],[_A])]) )
   => ground([_v,_A]).

:- true pred t_vars(_v,_A)
   : ( (_A=[_B|_C]),
       mshare([[_B],[_C]]),
       ground([_v]), linear(_B), linear(_C), shlin2([([_B],[_B]),([_C],[_C])]) )
   => ground([_v,_B,_C]).

t_vars(_v,[[_v]]) :-
    true(ground([_v])),
    var(_v),
    !,
    true(fails(_)).
t_vars(_a,[[]]) :-
    true(ground([_a])),
    atomic(_a),
    !,
    true(ground([_a])).
t_vars([_func],[[]]) :-
    true(ground([_func])),
    atomic(_func),
    !,
    true(ground([_func])).
t_vars([_arg|_func],[_g,[_g1|_af1],[_g2|_af2]]) :-
    true((
        mshare([[_g],[_g1],[_af1],[_g2],[_af2]]),
        ground([_arg,_func]),
        linear(_g),
        linear(_g1),
        linear(_af1),
        linear(_g2),
        linear(_af2),
        shlin2([([_g],[_g]),([_g1],[_g1]),([_af1],[_af1]),([_g2],[_g2]),([_af2],[_af2])])
    )),
    t_vars(_arg,[_g1|_af1]),
    true((
        mshare([[_g],[_g2],[_af2]]),
        ground([_arg,_func,_g1,_af1]),
        linear(_g),
        linear(_g2),
        linear(_af2),
        shlin2([([_g],[_g]),([_g2],[_g2]),([_af2],[_af2])])
    )),
    t_vars(_func,[_g2|_af2]),
    true((
        mshare([[_g]]),
        ground([_arg,_func,_g1,_af1,_g2,_af2]),
        linear(_g),
        shlin2([([_g],[_g])])
    )),
    unionv(_g1,_g2,_g),
    true(ground([_arg,_func,_g,_g1,_af1,_g2,_af2])).

:- true pred t_trans(_x,_a,_1,_res)
   : ( mshare([[_x],[_res]]),
       ground([_a,_1]), linear(_res), shlin2([([_x],[]),([_res],[_res])]) )
   => ( mshare([[_x]]),
        ground([_a,_1,_res]), shlin2([([_x],[])]) ).

:- true pred t_trans(_x,_a,_1,_res)
   : ( mshare([[_res]]),
       ground([_x,_a,_1]), linear(_res), shlin2([([_res],[_res])]) )
   => ground([_x,_a,_1,_res]).

t_trans(_x,_a,_1,[_a|k]) :-
    true((mshare([[_x]]),ground([_a,_1]),shlin2([([_x],[])]);ground([_x,_a,_1]))),
    't_trans/4/1/$disj/1'(_x,_a),
    !,
    true((mshare([[_x]]),ground([_a,_1]),shlin2([([_x],[])]);ground([_x,_a,_1]))).
t_trans(_x,_y,_1,i) :-
    true((mshare([[_x]]),ground([_y,_1]),shlin2([([_x],[])]);ground([_x,_y,_1]))),
    _x==_y,
    !,
    true(ground([_x,_y,_1])).
t_trans(_x,_e,[_ve|_1],[_e|k]) :-
    true((mshare([[_x]]),ground([_e,_ve,_1]),shlin2([([_x],[])]);ground([_x,_e,_ve,_1]))),
    notinv(_x,_ve),
    true((mshare([[_x]]),ground([_e,_ve,_1]),shlin2([([_x],[])]);ground([_x,_e,_ve,_1]))).
t_trans(_x,[_f|_e],[_vef,_sf,_se],_res) :-
    true((mshare([[_x],[_res],[_vf],[_1],[_ve],[_other]]),ground([_f,_e,_vef,_sf,_se]),linear(_res),linear(_vf),linear(_1),linear(_ve),linear(_other),shlin2([([_x],[]),([_res],[_res]),([_vf],[_vf]),([_1],[_1]),([_ve],[_ve]),([_other],[_other])]);mshare([[_res],[_vf],[_1],[_ve],[_other]]),ground([_x,_f,_e,_vef,_sf,_se]),linear(_res),linear(_vf),linear(_1),linear(_ve),linear(_other),shlin2([([_res],[_res]),([_vf],[_vf]),([_1],[_1]),([_ve],[_ve]),([_other],[_other])]))),
    _sf=[_vf|_1],
    true((mshare([[_x],[_res],[_ve],[_other]]),ground([_f,_e,_vef,_sf,_se,_vf,_1]),linear(_res),linear(_ve),linear(_other),shlin2([([_x],[]),([_res],[_res]),([_ve],[_ve]),([_other],[_other])]);mshare([[_res],[_ve],[_other]]),ground([_x,_f,_e,_vef,_sf,_se,_vf,_1]),linear(_res),linear(_ve),linear(_other),shlin2([([_res],[_res]),([_ve],[_ve]),([_other],[_other])]))),
    _se=[_ve|_other],
    true((mshare([[_x],[_res]]),ground([_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other]),linear(_res),shlin2([([_x],[]),([_res],[_res])]);mshare([[_res]]),ground([_x,_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other]),linear(_res),shlin2([([_res],[_res])]))),
    't_trans/4/4/$disj/1'(_e,_other),
    true((mshare([[_x],[_res]]),ground([_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other]),linear(_res),shlin2([([_x],[]),([_res],[_res])]);mshare([[_res]]),ground([_x,_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other]),linear(_res),shlin2([([_res],[_res])]))),
    t_rule1(_x,_e,_ve,_se,_f,_vf,_sf,_res),
    true((mshare([[_x]]),ground([_res,_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other]),shlin2([([_x],[])]);ground([_x,_res,_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other]))).
t_trans(_x,[_g,_f|_e],[_vefg,_sg,_sef],_res) :-
    true((mshare([[_x],[_res],[_vg],[_1],[_vef],[_sf],[_se],[_ve],[_2],[_vf],[_3]]),ground([_g,_f,_e,_vefg,_sg,_sef]),linear(_res),linear(_vg),linear(_1),linear(_vef),linear(_sf),linear(_se),linear(_ve),linear(_2),linear(_vf),linear(_3),shlin2([([_x],[]),([_res],[_res]),([_vg],[_vg]),([_1],[_1]),([_vef],[_vef]),([_sf],[_sf]),([_se],[_se]),([_ve],[_ve]),([_2],[_2]),([_vf],[_vf]),([_3],[_3])]);mshare([[_res],[_vg],[_1],[_vef],[_sf],[_se],[_ve],[_2],[_vf],[_3]]),ground([_x,_g,_f,_e,_vefg,_sg,_sef]),linear(_res),linear(_vg),linear(_1),linear(_vef),linear(_sf),linear(_se),linear(_ve),linear(_2),linear(_vf),linear(_3),shlin2([([_res],[_res]),([_vg],[_vg]),([_1],[_1]),([_vef],[_vef]),([_sf],[_sf]),([_se],[_se]),([_ve],[_ve]),([_2],[_2]),([_vf],[_vf]),([_3],[_3])]))),
    _sg=[_vg|_1],
    true((mshare([[_x],[_res],[_vef],[_sf],[_se],[_ve],[_2],[_vf],[_3]]),ground([_g,_f,_e,_vefg,_sg,_sef,_vg,_1]),linear(_res),linear(_vef),linear(_sf),linear(_se),linear(_ve),linear(_2),linear(_vf),linear(_3),shlin2([([_x],[]),([_res],[_res]),([_vef],[_vef]),([_sf],[_sf]),([_se],[_se]),([_ve],[_ve]),([_2],[_2]),([_vf],[_vf]),([_3],[_3])]);mshare([[_res],[_vef],[_sf],[_se],[_ve],[_2],[_vf],[_3]]),ground([_x,_g,_f,_e,_vefg,_sg,_sef,_vg,_1]),linear(_res),linear(_vef),linear(_sf),linear(_se),linear(_ve),linear(_2),linear(_vf),linear(_3),shlin2([([_res],[_res]),([_vef],[_vef]),([_sf],[_sf]),([_se],[_se]),([_ve],[_ve]),([_2],[_2]),([_vf],[_vf]),([_3],[_3])]))),
    _sef=[_vef,_sf,_se],
    true((mshare([[_x],[_res],[_ve],[_2],[_vf],[_3]]),ground([_g,_f,_e,_vefg,_sg,_sef,_vg,_1,_vef,_sf,_se]),linear(_res),linear(_ve),linear(_2),linear(_vf),linear(_3),shlin2([([_x],[]),([_res],[_res]),([_ve],[_ve]),([_2],[_2]),([_vf],[_vf]),([_3],[_3])]);mshare([[_res],[_ve],[_2],[_vf],[_3]]),ground([_x,_g,_f,_e,_vefg,_sg,_sef,_vg,_1,_vef,_sf,_se]),linear(_res),linear(_ve),linear(_2),linear(_vf),linear(_3),shlin2([([_res],[_res]),([_ve],[_ve]),([_2],[_2]),([_vf],[_vf]),([_3],[_3])]))),
    _se=[_ve|_2],
    true((mshare([[_x],[_res],[_vf],[_3]]),ground([_g,_f,_e,_vefg,_sg,_sef,_vg,_1,_vef,_sf,_se,_ve,_2]),linear(_res),linear(_vf),linear(_3),shlin2([([_x],[]),([_res],[_res]),([_vf],[_vf]),([_3],[_3])]);mshare([[_res],[_vf],[_3]]),ground([_x,_g,_f,_e,_vefg,_sg,_sef,_vg,_1,_vef,_sf,_se,_ve,_2]),linear(_res),linear(_vf),linear(_3),shlin2([([_res],[_res]),([_vf],[_vf]),([_3],[_3])]))),
    _sf=[_vf|_3],
    true((mshare([[_x],[_res]]),ground([_g,_f,_e,_vefg,_sg,_sef,_vg,_1,_vef,_sf,_se,_ve,_2,_vf,_3]),linear(_res),shlin2([([_x],[]),([_res],[_res])]);mshare([[_res]]),ground([_x,_g,_f,_e,_vefg,_sg,_sef,_vg,_1,_vef,_sf,_se,_ve,_2,_vf,_3]),linear(_res),shlin2([([_res],[_res])]))),
    t_rule2(_x,_e,_f,_vf,_sf,_g,_vg,_sg,_res),
    true((mshare([[_x]]),ground([_res,_g,_f,_e,_vefg,_sg,_sef,_vg,_1,_vef,_sf,_se,_ve,_2,_vf,_3]),shlin2([([_x],[])]);ground([_x,_res,_g,_f,_e,_vefg,_sg,_sef,_vg,_1,_vef,_sf,_se,_ve,_2,_vf,_3]))).

:- true pred 't_trans/4/1/$disj/1'(_x,_a)
   : ground([_x,_a])
   => ground([_x,_a]).

:- true pred 't_trans/4/1/$disj/1'(_x,_a)
   : ( mshare([[_x]]),
       ground([_a]), shlin2([([_x],[])]) )
   => ( mshare([[_x]]),
        ground([_a]), shlin2([([_x],[])]) ).

't_trans/4/1/$disj/1'(_x,_a) :-
    true((mshare([[_x]]),ground([_a]),shlin2([([_x],[])]);ground([_x,_a]))),
    atomic(_a),
    true((mshare([[_x]]),ground([_a]),shlin2([([_x],[])]);ground([_x,_a]))).
't_trans/4/1/$disj/1'(_x,_a) :-
    true((mshare([[_x]]),ground([_a]),shlin2([([_x],[])]);ground([_x,_a]))),
    var(_a),
    true(fails(_)),
    _a\==_x,
    true(fails(_)).

:- true pred 't_trans/4/4/$disj/1'(_e,_other)
   : ground([_e,_other])
   => ground([_e,_other]).

't_trans/4/4/$disj/1'(_e,_other) :-
    true(ground([_e,_other])),
    end(_e),
    true(ground([_e,_other])).
't_trans/4/4/$disj/1'(_e,_other) :-
    true((
        mshare([[_2],[_ve1],[_3]]),
        ground([_e,_other]),
        linear(_2),
        linear(_ve1),
        linear(_3),
        shlin2([([_2],[_2]),([_ve1],[_ve1]),([_3],[_3])])
    )),
    _other=[_2,[_ve1|_3]],
    true(ground([_e,_other,_2,_ve1,_3])),
    _ve1\==[],
    true(ground([_e,_other,_2,_ve1,_3])).

:- true pred t_rule1(_x,_e,_ve,_se,_f,_vf,_sf,_A)
   : ( mshare([[_x],[_A]]),
       ground([_e,_ve,_se,_f,_vf,_sf]), linear(_A), shlin2([([_x],[]),([_A],[_A])]) )
   => ( mshare([[_x]]),
        ground([_e,_ve,_se,_f,_vf,_sf,_A]), shlin2([([_x],[])]) ).

:- true pred t_rule1(_x,_e,_ve,_se,_f,_vf,_sf,_A)
   : ( mshare([[_A]]),
       ground([_x,_e,_ve,_se,_f,_vf,_sf]), linear(_A), shlin2([([_A],[_A])]) )
   => ground([_x,_e,_ve,_se,_f,_vf,_sf,_A]).

t_rule1(_x,_e,_ve,_se,_f,_vf,_sf,_e) :-
    true((mshare([[_x]]),ground([_e,_ve,_se,_f,_vf,_sf]),shlin2([([_x],[])]);ground([_x,_e,_ve,_se,_f,_vf,_sf]))),
    notinv(_x,_ve),
    true((mshare([[_x]]),ground([_e,_ve,_se,_f,_vf,_sf]),shlin2([([_x],[])]);ground([_x,_e,_ve,_se,_f,_vf,_sf]))),
    _x==_f,
    !,
    true(ground([_x,_e,_ve,_se,_f,_vf,_sf])).
t_rule1(_x,_e,_ve,_se,_f,_vf,_sf,[_resf,_e|b]) :-
    true((mshare([[_x],[_resf]]),ground([_e,_ve,_se,_f,_vf,_sf]),linear(_resf),shlin2([([_x],[]),([_resf],[_resf])]);mshare([[_resf]]),ground([_x,_e,_ve,_se,_f,_vf,_sf]),linear(_resf),shlin2([([_resf],[_resf])]))),
    notinv(_x,_ve),
    true((mshare([[_x],[_resf]]),ground([_e,_ve,_se,_f,_vf,_sf]),linear(_resf),shlin2([([_x],[]),([_resf],[_resf])]);mshare([[_resf]]),ground([_x,_e,_ve,_se,_f,_vf,_sf]),linear(_resf),shlin2([([_resf],[_resf])]))),
    inv(_x,_vf),
    true((mshare([[_x],[_resf]]),ground([_e,_ve,_se,_f,_vf,_sf]),linear(_resf),shlin2([([_x],[]),([_resf],[_resf])]);mshare([[_resf]]),ground([_x,_e,_ve,_se,_f,_vf,_sf]),linear(_resf),shlin2([([_resf],[_resf])]))),
    _x\==_f,
    !,
    true((mshare([[_x],[_resf]]),ground([_e,_ve,_se,_f,_vf,_sf]),linear(_resf),shlin2([([_x],[]),([_resf],[_resf])]);mshare([[_resf]]),ground([_x,_e,_ve,_se,_f,_vf,_sf]),linear(_resf),shlin2([([_resf],[_resf])]))),
    t_trans(_x,_f,_sf,_resf),
    true((mshare([[_x]]),ground([_e,_ve,_se,_f,_vf,_sf,_resf]),shlin2([([_x],[])]);ground([_x,_e,_ve,_se,_f,_vf,_sf,_resf]))).
t_rule1(_x,_e,_ve,_se,_f,_vf,_sf,[_f,_rese|c]) :-
    true((mshare([[_x],[_rese]]),ground([_e,_ve,_se,_f,_vf,_sf]),linear(_rese),shlin2([([_x],[]),([_rese],[_rese])]);mshare([[_rese]]),ground([_x,_e,_ve,_se,_f,_vf,_sf]),linear(_rese),shlin2([([_rese],[_rese])]))),
    notinv(_x,_vf),
    !,
    true((mshare([[_x],[_rese]]),ground([_e,_ve,_se,_f,_vf,_sf]),linear(_rese),shlin2([([_x],[]),([_rese],[_rese])]);mshare([[_rese]]),ground([_x,_e,_ve,_se,_f,_vf,_sf]),linear(_rese),shlin2([([_rese],[_rese])]))),
    t_trans(_x,_e,_se,_rese),
    true((mshare([[_x]]),ground([_e,_ve,_se,_f,_vf,_sf,_rese]),shlin2([([_x],[])]);ground([_x,_e,_ve,_se,_f,_vf,_sf,_rese]))).
t_rule1(_x,_e,_ve,_se,_f,_vf,_sf,[_resf,_rese|s]) :-
    true((mshare([[_x],[_resf],[_rese]]),ground([_e,_ve,_se,_f,_vf,_sf]),linear(_resf),linear(_rese),shlin2([([_x],[]),([_resf],[_resf]),([_rese],[_rese])]);mshare([[_resf],[_rese]]),ground([_x,_e,_ve,_se,_f,_vf,_sf]),linear(_resf),linear(_rese),shlin2([([_resf],[_resf]),([_rese],[_rese])]))),
    t_trans(_x,_e,_se,_rese),
    true((mshare([[_x],[_resf]]),ground([_e,_ve,_se,_f,_vf,_sf,_rese]),linear(_resf),shlin2([([_x],[]),([_resf],[_resf])]);mshare([[_resf]]),ground([_x,_e,_ve,_se,_f,_vf,_sf,_rese]),linear(_resf),shlin2([([_resf],[_resf])]))),
    t_trans(_x,_f,_sf,_resf),
    true((mshare([[_x]]),ground([_e,_ve,_se,_f,_vf,_sf,_resf,_rese]),shlin2([([_x],[])]);ground([_x,_e,_ve,_se,_f,_vf,_sf,_resf,_rese]))).

:- true pred t_rule2(_x,_e,_f,_vf,_sf,_g,_vg,_sg,_A)
   : ( mshare([[_A]]),
       ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg]), linear(_A), shlin2([([_A],[_A])]) )
   => ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg,_A]).

:- true pred t_rule2(_x,_e,_f,_vf,_sf,_g,_vg,_sg,_A)
   : ( mshare([[_x],[_A]]),
       ground([_e,_f,_vf,_sf,_g,_vg,_sg]), linear(_A), shlin2([([_x],[]),([_A],[_A])]) )
   => ( mshare([[_x]]),
        ground([_e,_f,_vf,_sf,_g,_vg,_sg,_A]), shlin2([([_x],[])]) ).

t_rule2(_x,_e,_f,_vf,_sf,_g,_vg,_sg,[_g,_e|c]) :-
    true((mshare([[_x]]),ground([_e,_f,_vf,_sf,_g,_vg,_sg]),shlin2([([_x],[])]);ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg]))),
    _x==_f,
    true(ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg])),
    notinv(_x,_vg),
    !,
    true(ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg])).
t_rule2(_x,_e,_f,_vf,_sf,_g,_vg,_sg,[_resg,_e|s]) :-
    true((mshare([[_x],[_resg]]),ground([_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resg),shlin2([([_x],[]),([_resg],[_resg])]);mshare([[_resg]]),ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resg),shlin2([([_resg],[_resg])]))),
    _x==_f,
    !,
    true((
        mshare([[_resg]]),
        ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg]),
        linear(_resg),
        shlin2([([_resg],[_resg])])
    )),
    t_trans(_x,_g,_sg,_resg),
    true(ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg,_resg])).
t_rule2(_x,_e,_f,_vf,_sf,_g,_vg,_sg,[_g,_resf,_e|cp]) :-
    true((mshare([[_x],[_resf]]),ground([_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resf),shlin2([([_x],[]),([_resf],[_resf])]);mshare([[_resf]]),ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resf),shlin2([([_resf],[_resf])]))),
    inv(_x,_vf),
    true((mshare([[_x],[_resf]]),ground([_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resf),shlin2([([_x],[]),([_resf],[_resf])]);mshare([[_resf]]),ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resf),shlin2([([_resf],[_resf])]))),
    notinv(_x,_vg),
    !,
    true((mshare([[_x],[_resf]]),ground([_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resf),shlin2([([_x],[]),([_resf],[_resf])]);mshare([[_resf]]),ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resf),shlin2([([_resf],[_resf])]))),
    t_trans(_x,_f,_sf,_resf),
    true((mshare([[_x]]),ground([_e,_f,_vf,_sf,_g,_vg,_sg,_resf]),shlin2([([_x],[])]);ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg,_resf]))).
t_rule2(_x,_e,_f,_vf,_sf,_g,_vg,_sg,[_resg,_resf,_e|sp]) :-
    true((mshare([[_x],[_resg],[_resf]]),ground([_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resg),linear(_resf),shlin2([([_x],[]),([_resg],[_resg]),([_resf],[_resf])]);mshare([[_resg],[_resf]]),ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resg),linear(_resf),shlin2([([_resg],[_resg]),([_resf],[_resf])]))),
    inv(_x,_vf),
    !,
    true((mshare([[_x],[_resg],[_resf]]),ground([_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resg),linear(_resf),shlin2([([_x],[]),([_resg],[_resg]),([_resf],[_resf])]);mshare([[_resg],[_resf]]),ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resg),linear(_resf),shlin2([([_resg],[_resg]),([_resf],[_resf])]))),
    t_trans(_x,_f,_sf,_resf),
    true((mshare([[_x],[_resg]]),ground([_e,_f,_vf,_sf,_g,_vg,_sg,_resf]),linear(_resg),shlin2([([_x],[]),([_resg],[_resg])]);mshare([[_resg]]),ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg,_resf]),linear(_resg),shlin2([([_resg],[_resg])]))),
    t_trans(_x,_g,_sg,_resg),
    true((mshare([[_x]]),ground([_e,_f,_vf,_sf,_g,_vg,_sg,_resg,_resf]),shlin2([([_x],[])]);ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg,_resg,_resf]))).
t_rule2(_x,_e,_f,_vf,_sf,_g,_vg,_sg,[_f|_e]) :-
    true((mshare([[_x]]),ground([_e,_f,_vf,_sf,_g,_vg,_sg]),shlin2([([_x],[])]);ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg]))),
    _x==_g,
    !,
    true(ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg])).
t_rule2(_x,_e,_f,_vf,_sf,_g,_vg,_sg,[_resg,_f,_e|bp]) :-
    true((mshare([[_x],[_resg]]),ground([_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resg),shlin2([([_x],[]),([_resg],[_resg])]);mshare([[_resg]]),ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg]),linear(_resg),shlin2([([_resg],[_resg])]))),
    t_trans(_x,_g,_sg,_resg),
    true((mshare([[_x]]),ground([_e,_f,_vf,_sf,_g,_vg,_sg,_resg]),shlin2([([_x],[])]);ground([_x,_e,_f,_vf,_sf,_g,_vg,_sg,_resg]))).

:- true pred make_list(_a,_A)
   : ( mshare([[_A]]),
       ground([_a]), linear(_A), shlin2([([_A],[_A])]) )
   => ground([_a,_A]).

make_list(_a,_a) :-
    true(ground([_a])),
    atomic(_a),
    true(ground([_a])).
make_list([_b,_a|LF],[_a|_rb]) :-
    true((
        mshare([[_rb]]),
        ground([_b,_a,LF]),
        linear(_rb),
        shlin2([([_rb],[_rb])])
    )),
    list_functor_name(LF),
    true((
        mshare([[_rb]]),
        ground([_b,_a,LF]),
        linear(_rb),
        shlin2([([_rb],[_rb])])
    )),
    make_list(_b,_rb),
    true(ground([_b,_a,LF,_rb])).

:- true pred listify(_X,_A)
   : ( mshare([[_A]]),
       ground([_X]), linear(_A), shlin2([([_A],[_A])]) )
   => ground([_X,_A]).

:- true pred listify(_X,_A)
   : ( mshare([[_X],[_A]]),
       linear(_A), shlin2([([_X],[]),([_A],[_A])]) )
   => ( mshare([[_X]]),
        ground([_A]), shlin2([([_X],[])]) ).

listify(_X,_X) :-
    true((mshare([[_X]]),shlin2([([_X],[])]);ground([_X]))),
    'listify/2/1/$disj/1'(_X),
    !,
    true(ground([_X])).
listify(_Expr,[_Op|_LArgs]) :-
    true((mshare([[_Expr],[_Op],[_LArgs],[N]]),linear(_Op),linear(_LArgs),linear(N),shlin2([([_Expr],[]),([_Op],[_Op]),([_LArgs],[_LArgs]),([N],[N])]);mshare([[_Op],[_LArgs],[N]]),ground([_Expr]),linear(_Op),linear(_LArgs),linear(N),shlin2([([_Op],[_Op]),([_LArgs],[_LArgs]),([N],[N])]))),
    functor(_Expr,_Op,N),
    true((mshare([[_Expr],[_LArgs]]),ground([_Op,N]),linear(_LArgs),shlin2([([_Expr],[]),([_LArgs],[_LArgs])]);mshare([[_LArgs]]),ground([_Expr,_Op,N]),linear(_LArgs),shlin2([([_LArgs],[_LArgs])]))),
    listify_list(1,N,_Expr,_LArgs),
    true((mshare([[_Expr]]),ground([_Op,_LArgs,N]),shlin2([([_Expr],[])]);ground([_Expr,_Op,_LArgs,N]))).

:- true pred 'listify/2/1/$disj/1'(_X)
   : ( mshare([[_X]]),
       shlin2([([_X],[])]) )
   => ground([_X]).

:- true pred 'listify/2/1/$disj/1'(_X)
   : ground([_X])
   => ground([_X]).

'listify/2/1/$disj/1'(_X) :-
    true((mshare([[_X]]),shlin2([([_X],[])]);ground([_X]))),
    var(_X),
    true((fails(_);mshare([[_X]]),linear(_X),shlin2([([_X],[_X])]))).
'listify/2/1/$disj/1'(_X) :-
    true((mshare([[_X]]),shlin2([([_X],[])]);ground([_X]))),
    atomic(_X),
    true(ground([_X])).

:- true pred listify_list(I,N,_1,_A)
   : ( (I=1),
       mshare([[_A]]),
       ground([N,_1]), linear(_A), shlin2([([_A],[_A])]) )
   => ground([N,_1,_A]).

:- true pred listify_list(I,N,_1,_A)
   : ( mshare([[_1],[_A]]),
       ground([I,N]), linear(_A), shlin2([([_1],[]),([_A],[_A])]) )
   => ( mshare([[_1]]),
        ground([I,N,_A]), shlin2([([_1],[])]) ).

:- true pred listify_list(I,N,_1,_A)
   : ( (I=1),
       mshare([[_1],[_A]]),
       ground([N]), linear(_A), shlin2([([_1],[]),([_A],[_A])]) )
   => ( mshare([[_1]]),
        ground([N,_A]), shlin2([([_1],[])]) ).

:- true pred listify_list(I,N,_1,_A)
   : ( mshare([[_A]]),
       ground([I,N,_1]), linear(_A), shlin2([([_A],[_A])]) )
   => ground([I,N,_1,_A]).

listify_list(I,N,_1,[]) :-
    true((mshare([[_1]]),ground([I,N]),shlin2([([_1],[])]);ground([I,N,_1]))),
    I>N,
    !,
    true((mshare([[_1]]),ground([I,N]),shlin2([([_1],[])]);ground([I,N,_1]))).
listify_list(I,N,_Expr,[_LA|_LArgs]) :-
    true((mshare([[_Expr],[_LA],[_LArgs],[_A],[I1]]),ground([I,N]),linear(_LA),linear(_LArgs),linear(_A),linear(I1),shlin2([([_Expr],[]),([_LA],[_LA]),([_LArgs],[_LArgs]),([_A],[_A]),([I1],[I1])]);mshare([[_LA],[_LArgs],[_A],[I1]]),ground([I,N,_Expr]),linear(_LA),linear(_LArgs),linear(_A),linear(I1),shlin2([([_LA],[_LA]),([_LArgs],[_LArgs]),([_A],[_A]),([I1],[I1])]))),
    I=<N,
    !,
    true((mshare([[_Expr],[_LA],[_LArgs],[_A],[I1]]),ground([I,N]),linear(_LA),linear(_LArgs),linear(_A),linear(I1),shlin2([([_Expr],[]),([_LA],[_LA]),([_LArgs],[_LArgs]),([_A],[_A]),([I1],[I1])]);mshare([[_LA],[_LArgs],[_A],[I1]]),ground([I,N,_Expr]),linear(_LA),linear(_LArgs),linear(_A),linear(I1),shlin2([([_LA],[_LA]),([_LArgs],[_LArgs]),([_A],[_A]),([I1],[I1])]))),
    arg(I,_Expr,_A),
    true((mshare([[_Expr,_A],[_LA],[_LArgs],[I1]]),ground([I,N]),linear(_LA),linear(_LArgs),linear(I1),shlin2([([_Expr,_A],[]),([_LA],[_LA]),([_LArgs],[_LArgs]),([I1],[I1])]);mshare([[_LA],[_LArgs],[I1]]),ground([I,N,_Expr,_A]),linear(_LA),linear(_LArgs),linear(I1),shlin2([([_LA],[_LA]),([_LArgs],[_LArgs]),([I1],[I1])]))),
    listify(_A,_LA),
    true((mshare([[_Expr,_A],[_LArgs],[I1]]),ground([I,N,_LA]),linear(_LArgs),linear(I1),shlin2([([_Expr,_A],[]),([_LArgs],[_LArgs]),([I1],[I1])]);mshare([[_LArgs],[I1]]),ground([I,N,_Expr,_LA,_A]),linear(_LArgs),linear(I1),shlin2([([_LArgs],[_LArgs]),([I1],[I1])]))),
    I1 is I+1,
    true((mshare([[_Expr,_A],[_LArgs]]),ground([I,N,_LA,I1]),linear(_LArgs),shlin2([([_Expr,_A],[]),([_LArgs],[_LArgs])]);mshare([[_LArgs]]),ground([I,N,_Expr,_LA,_A,I1]),linear(_LArgs),shlin2([([_LArgs],[_LArgs])]))),
    listify_list(I1,N,_Expr,_LArgs),
    true((mshare([[_Expr,_A]]),ground([I,N,_LA,_LArgs,I1]),shlin2([([_Expr,_A],[])]);ground([I,N,_Expr,_LA,_LArgs,_A,I1]))).

:- true pred my_member(X,_A)
   : ( (_A=[-]), ground([X]) )
   => ground([X]).

:- true pred my_member(X,_A)
   : ( (_A=[<,>,=<,>=,=\=,=:=]), ground([X]) )
   => ground([X]).

:- true pred my_member(X,_A)
   : ( (_A=[+,-,*,//,mod]), ground([X]) )
   => ground([X]).

:- true pred my_member(X,_A)
   : ground([X,_A])
   => ground([X,_A]).

my_member(X,[X|_1]).
my_member(X,[_1|L]) :-
    true(ground([X,_1,L])),
    my_member(X,L),
    true(ground([X,_1,L])).

:- true pred my_append(_A,L,_B)
   : ( mshare([[_A],[_B]]),
       ground([L]), linear(_A), linear(_B), shlin2([([_A],[_A]),([_B],[_B])]) )
   => ( mshare([[_A,_B]]),
        ground([L]), linear(_A), linear(_B), shlin2([([_A,_B],[_A,_B])]) ).

:- true pred my_append(_A,L,_B)
   : ( mshare([[_A],[L],[_B]]),
       linear(_A), linear(L), linear(_B), shlin2([([_A],[_A]),([L],[L]),([_B],[_B])]) )
   => ( mshare([[_A,_B],[L,_B]]),
        linear(_A), linear(L), linear(_B), shlin2([([_A,_B],[_A,_B]),([L,_B],[L,_B])]) ).

:- true pred my_append(_A,L,_B)
   : ( mshare([[_B]]),
       ground([_A,L]), linear(_B), shlin2([([_B],[_B])]) )
   => ground([_A,L,_B]).

:- true pred my_append(_A,L,_B)
   : ( mshare([[_A],[L]]),
       ground([_B]), linear(_A), linear(L), shlin2([([_A],[_A]),([L],[L])]) )
   => ground([_A,L,_B]).

my_append([],L,L).
my_append([X|L1],L2,[X|L3]) :-
    true((mshare([[L2],[X],[L1],[L3]]),linear(L2),linear(X),linear(L1),linear(L3),shlin2([([L2],[L2]),([X],[X]),([L1],[L1]),([L3],[L3])]);mshare([[L2],[L1]]),ground([X,L3]),linear(L2),linear(L1),shlin2([([L2],[L2]),([L1],[L1])]);mshare([[X],[L1],[L3]]),ground([L2]),linear(X),linear(L1),linear(L3),shlin2([([X],[X]),([L1],[L1]),([L3],[L3])]);mshare([[L3]]),ground([L2,X,L1]),linear(L3),shlin2([([L3],[L3])]))),
    my_append(L1,L2,L3),
    true((mshare([[L2,L3],[X],[L1,L3]]),linear(L2),linear(X),linear(L1),linear(L3),shlin2([([L2,L3],[L2,L3]),([X],[X]),([L1,L3],[L1,L3])]);mshare([[X],[L1,L3]]),ground([L2]),linear(X),linear(L1),linear(L3),shlin2([([X],[X]),([L1,L3],[L1,L3])]);ground([L2,X,L1,L3]))).

intersectv([],_1,[]).
intersectv([A|S1],S2,S) :-
    intersectv_2(S2,A,S1,S).

intersectv_2([],_1,_2,[]).
intersectv_2([B|S2],A,S1,S) :-
    compare(Order,A,B),
    intersectv_3(Order,A,S1,B,S2,S).

intersectv_3(<,_1,S1,B,S2,S) :-
    intersectv_2(S1,B,S2,S).
intersectv_3(=,A,S1,_1,S2,[A|S]) :-
    intersectv(S1,S2,S).
intersectv_3(>,A,S1,_1,S2,S) :-
    intersectv_2(S2,A,S1,S).

intersectv_list([],[]).
intersectv_list([InS|Sets],OutS) :-
    intersectv_list(Sets,InS,OutS).

intersectv_list([],_1,_2) :-
    _2=_1.
intersectv_list([S|Sets],_1,_2) :-
    intersectv(S,_1,_3),
    intersectv_list(Sets,_3,_2).

diffv([],_1,[]).
diffv([A|S1],S2,S) :-
    diffv_2(S2,A,S1,S).

diffv_2([],A,S1,[A|S1]).
diffv_2([B|S2],A,S1,S) :-
    compare(Order,A,B),
    diffv_3(Order,A,S1,B,S2,S).

diffv_3(<,A,S1,B,S2,[A|S]) :-
    diffv(S1,[B|S2],S).
diffv_3(=,A,S1,_1,S2,S) :-
    diffv(S1,S2,S).
diffv_3(>,A,S1,_1,S2,S) :-
    diffv_2(S2,A,S1,S).

:- true pred unionv(_A,S2,S)
   : ( mshare([[S]]),
       ground([_A,S2]), linear(S), shlin2([([S],[S])]) )
   => ground([_A,S2,S]).

unionv([],S2,S2).
unionv([A|S1],S2,S) :-
    true((
        mshare([[S]]),
        ground([S2,A,S1]),
        linear(S),
        shlin2([([S],[S])])
    )),
    unionv_2(S2,A,S1,S),
    true(ground([S2,S,A,S1])).

:- true pred unionv_2(_A,A,S1,S)
   : ( mshare([[S]]),
       ground([_A,A,S1]), linear(S), shlin2([([S],[S])]) )
   => ground([_A,A,S1,S]).

unionv_2([],A,S1,[A|S1]).
unionv_2([B|S2],A,S1,S) :-
    true((
        mshare([[S],[Order]]),
        ground([A,S1,B,S2]),
        linear(S),
        linear(Order),
        shlin2([([S],[S]),([Order],[Order])])
    )),
    compare(Order,A,B),
    true((
        mshare([[S]]),
        ground([A,S1,B,S2,Order]),
        linear(S),
        shlin2([([S],[S])])
    )),
    unionv_3(Order,A,S1,B,S2,S),
    true(ground([A,S1,S,B,S2,Order])).

:- true pred unionv_3(_A,A,S1,B,S2,_B)
   : ( mshare([[_B]]),
       ground([_A,A,S1,B,S2]), linear(_B), shlin2([([_B],[_B])]) )
   => ground([_A,A,S1,B,S2,_B]).

unionv_3(<,A,S1,B,S2,[A|S]) :-
    true((
        mshare([[S]]),
        ground([A,S1,B,S2]),
        linear(S),
        shlin2([([S],[S])])
    )),
    unionv_2(S1,B,S2,S),
    true(ground([A,S1,B,S2,S])).
unionv_3(=,A,S1,_1,S2,[A|S]) :-
    true((
        mshare([[S]]),
        ground([A,S1,_1,S2]),
        linear(S),
        shlin2([([S],[S])])
    )),
    unionv(S1,S2,S),
    true(ground([A,S1,_1,S2,S])).
unionv_3(>,A,S1,B,S2,[B|S]) :-
    true((
        mshare([[S]]),
        ground([A,S1,B,S2]),
        linear(S),
        shlin2([([S],[S])])
    )),
    unionv_2(S2,A,S1,S),
    true(ground([A,S1,B,S2,S])).

subsetv([],_1).
subsetv([A|S1],[B|S2]) :-
    compare(Order,A,B),
    subsetv_2(Order,A,S1,S2).

subsetv_2(=,_1,S1,S2) :-
    subsetv(S1,S2).
subsetv_2(>,A,S1,S2) :-
    subsetv([A|S1],S2).

small_subsetv([],_1).
small_subsetv([A|S1],S2) :-
    inv(A,S2),
    small_subsetv(S1,S2).

:- true pred inv(A,_A)
   : ( mshare([[A]]),
       ground([_A]), shlin2([([A],[])]) )
   => ( mshare([[A]]),
        ground([_A]), shlin2([([A],[])]) ).

:- true pred inv(A,_A)
   : ground([A,_A])
   => ground([A,_A]).

inv(A,[B|S]) :-
    true((mshare([[A],[Order]]),ground([B,S]),linear(Order),shlin2([([A],[]),([Order],[Order])]);mshare([[Order]]),ground([A,B,S]),linear(Order),shlin2([([Order],[Order])]))),
    compare(Order,A,B),
    true((mshare([[A]]),ground([B,S,Order]),shlin2([([A],[])]);ground([A,B,S,Order]))),
    inv_2(Order,A,S),
    true((mshare([[A]]),ground([B,S,Order]),shlin2([([A],[])]);ground([A,B,S,Order]))).

:- true pred inv_2(_A,_1,_2)
   : ( mshare([[_1]]),
       ground([_A,_2]), shlin2([([_1],[])]) )
   => ( mshare([[_1]]),
        ground([_A,_2]), shlin2([([_1],[])]) ).

:- true pred inv_2(_A,_1,_2)
   : ground([_A,_1,_2])
   => ground([_A,_1,_2]).

inv_2(=,_1,_2).
inv_2(>,A,S) :-
    true((mshare([[A]]),ground([S]),shlin2([([A],[])]);ground([A,S]))),
    inv(A,S),
    true((mshare([[A]]),ground([S]),shlin2([([A],[])]);ground([A,S]))).

:- true pred notinv(A,S)
   : ( mshare([[A]]),
       ground([S]), shlin2([([A],[])]) )
   => ( mshare([[A]]),
        ground([S]), shlin2([([A],[])]) ).

:- true pred notinv(A,S)
   : ground([A,S])
   => ground([A,S]).

notinv(A,S) :-
    true((mshare([[A]]),ground([S]),shlin2([([A],[])]);ground([A,S]))),
    notinv_2(S,A),
    true((mshare([[A]]),ground([S]),shlin2([([A],[])]);ground([A,S]))).

:- true pred notinv_2(_A,_1)
   : ground([_A,_1])
   => ground([_A,_1]).

:- true pred notinv_2(_A,_1)
   : ( mshare([[_1]]),
       ground([_A]), shlin2([([_1],[])]) )
   => ( mshare([[_1]]),
        ground([_A]), shlin2([([_1],[])]) ).

notinv_2([],_1).
notinv_2([B|S],A) :-
    true((mshare([[A],[Order]]),ground([B,S]),linear(Order),shlin2([([A],[]),([Order],[Order])]);mshare([[Order]]),ground([A,B,S]),linear(Order),shlin2([([Order],[Order])]))),
    compare(Order,A,B),
    true((mshare([[A]]),ground([B,S,Order]),shlin2([([A],[])]);ground([A,B,S,Order]))),
    notinv_3(Order,A,S),
    true((mshare([[A]]),ground([B,S,Order]),shlin2([([A],[])]);ground([A,B,S,Order]))).

:- true pred notinv_3(_A,_1,_2)
   : ( mshare([[_1]]),
       ground([_A,_2]), shlin2([([_1],[])]) )
   => ( mshare([[_1]]),
        ground([_A,_2]), shlin2([([_1],[])]) ).

:- true pred notinv_3(_A,_1,_2)
   : ground([_A,_1,_2])
   => ground([_A,_1,_2]).

notinv_3(<,_1,_2).
notinv_3(>,A,S) :-
    true((mshare([[A]]),ground([S]),shlin2([([A],[])]);ground([A,S]))),
    notinv_2(S,A),
    true((mshare([[A]]),ground([S]),shlin2([([A],[])]);ground([A,S]))).


