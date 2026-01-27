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
        linear(_Ans2)
    )),
    try(fac(3),_Ans1),
    true((
        mshare([[_Ans2]]),
        ground([_Ans1]),
        linear(_Ans2)
    )),
    try(quick([3,1,2]),_Ans2),
    true(ground([_Ans1,_Ans2])).

:- true pred try(_inpexpr,_anslist)
   : ( (_inpexpr=quick([3,1,2])),
       mshare([[_anslist]]),
       linear(_anslist) )
   => ground([_anslist]).

:- true pred try(_inpexpr,_anslist)
   : ( (_inpexpr=fac(3)),
       mshare([[_anslist]]),
       linear(_anslist) )
   => ground([_anslist]).

try(_inpexpr,_anslist) :-
    true((
        mshare([[_anslist],[_list],[_curry],[_ans]]),
        ground([_inpexpr]),
        linear(_anslist),
        linear(_list),
        linear(_curry),
        linear(_ans)
    )),
    listify(_inpexpr,_list),
    true((
        mshare([[_anslist],[_curry],[_ans]]),
        ground([_inpexpr,_list]),
        linear(_anslist),
        linear(_curry),
        linear(_ans)
    )),
    curry(_list,_curry),
    true((
        mshare([[_anslist],[_ans]]),
        ground([_inpexpr,_list,_curry]),
        linear(_anslist),
        linear(_ans)
    )),
    t_reduce(_curry,_ans),
    true((
        mshare([[_anslist]]),
        ground([_inpexpr,_list,_curry,_ans]),
        linear(_anslist)
    )),
    make_list(_ans,_anslist),
    true(ground([_inpexpr,_anslist,_list,_curry,_ans])).

:- true pred end(X)
   : ground([X])
   => ground([X]).

:- true pred end(X)
   : mshare([[X]])
   => ground([X]).

end(X) :-
    true((mshare([[X]]);ground([X]))),
    atom(X),
    !,
    true(ground([X])).
end(X) :-
    true((mshare([[X]]);ground([X]))),
    X==[],
    true(ground([X])).

:- true pred list_functor_name(Name)
   : ground([Name])
   => ground([Name]).

:- true pred list_functor_name(Name)
   : ( mshare([[Name]]),
       linear(Name) )
   => ground([Name]).

:- true pred list_functor_name(Name)
   : mshare([[Name]])
   => ground([Name]).

list_functor_name(Name) :-
    true((mshare([[Name],[_1],[_2],[_3]]),linear(Name),linear(_1),linear(_2),linear(_3);mshare([[Name],[_1],[_2],[_3]]),linear(_1),linear(_2),linear(_3);mshare([[_1],[_2],[_3]]),ground([Name]),linear(_1),linear(_2),linear(_3))),
    atom(Name),
    !,
    true((
        mshare([[_1],[_2],[_3]]),
        ground([Name]),
        linear(_1),
        linear(_2),
        linear(_3)
    )),
    functor([_2|_3],Name,_1),
    true((
        mshare([[_2],[_3]]),
        ground([Name,_1]),
        linear(_2),
        linear(_3)
    )).
list_functor_name(Name) :-
    true((mshare([[Name],[_4],[_5],[_6]]),linear(Name),linear(_4),linear(_5),linear(_6);mshare([[Name],[_4],[_5],[_6]]),linear(_4),linear(_5),linear(_6);mshare([[_4],[_5],[_6]]),ground([Name]),linear(_4),linear(_5),linear(_6))),
    var(Name),
    !,
    true((fails(_);mshare([[Name],[_4],[_5],[_6]]),linear(Name),linear(_4),linear(_5),linear(_6))),
    functor([_5|_6],Name,_4),
    true((fails(_);mshare([[_5],[_6]]),ground([Name,_4]),linear(_5),linear(_6))).

:- true pred t_def(_A,_B,_C)
   : ( mshare([[_B],[_C]]),
       ground([_A]), linear(_B), linear(_C) )
   => ( mshare([[_B,_C]]),
        ground([_A]), linear(_B) ).

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
       ground([_C]), linear(_A), linear(_B) )
   => ( mshare([[_expr]]),
        ground([_A,_B,_C]) ).

:- true pred t_reduce(_expr,_ans)
   : ( (_ans=[_A,_B|_C]),
       mshare([[_A],[_B]]),
       ground([_expr,_C]), linear(_A), linear(_B) )
   => ground([_expr,_A,_B,_C]).

:- true pred t_reduce(_expr,_ans)
   : ( mshare([[_ans]]),
       ground([_expr]), linear(_ans) )
   => ground([_expr,_ans]).

:- true pred t_reduce(_expr,_ans)
   : ( mshare([[_expr],[_ans]]),
       linear(_ans) )
   => ( mshare([[_expr]]),
        ground([_ans]) ).

t_reduce(_expr,_ans) :-
    true((mshare([[_expr],[_ans]]),linear(_ans);mshare([[_ans]]),ground([_expr]),linear(_ans))),
    atomic(_expr),
    !,
    true((
        mshare([[_ans]]),
        ground([_expr]),
        linear(_ans)
    )),
    _ans=_expr,
    true(ground([_expr,_ans])).
t_reduce([_y,_x|LF],[_yr,_xr|LF]) :-
    true((mshare([[_y],[_y,_x],[_y,_x,LF],[_y,LF],[_x],[_x,LF],[LF],[_yr],[_xr]]),linear(_yr),linear(_xr);mshare([[_y],[_y,_x],[_x],[_yr],[_xr]]),ground([LF]),linear(_yr),linear(_xr);mshare([[_yr],[_xr]]),ground([_y,_x,LF]),linear(_yr),linear(_xr))),
    list_functor_name(LF),
    true((mshare([[_y],[_y,_x],[_x],[_yr],[_xr]]),ground([LF]),linear(_yr),linear(_xr);mshare([[_yr],[_xr]]),ground([_y,_x,LF]),linear(_yr),linear(_xr))),
    t_reduce(_x,_xr),
    !,
    true((mshare([[_y],[_y,_x],[_x],[_yr]]),ground([LF,_xr]),linear(_yr);mshare([[_yr]]),ground([_y,_x,LF,_xr]),linear(_yr))),
    t_reduce(_y,_yr),
    !,
    true((mshare([[_y],[_y,_x],[_x]]),ground([LF,_yr,_xr]);ground([_y,_x,LF,_yr,_xr]))).
t_reduce(_expr,_ans) :-
    true((mshare([[_expr],[_ans],[_next],[_red],[_form]]),linear(_ans),linear(_next),linear(_red),linear(_form);mshare([[_ans],[_next],[_red],[_form]]),ground([_expr]),linear(_ans),linear(_next),linear(_red),linear(_form))),
    t_append(_next,_red,_form,_expr),
    true((mshare([[_expr,_next],[_expr,_next,_form],[_expr,_form],[_ans],[_next,_red]]),linear(_ans),linear(_red);mshare([[_ans],[_next,_red]]),ground([_expr,_form]),linear(_ans),linear(_red))),
    t_redex(_form,_red),
    !,
    true((mshare([[_expr,_next],[_expr,_next,_red,_form],[_expr,_next,_form],[_expr,_form],[_ans],[_next,_red]]),linear(_ans);mshare([[_ans],[_next,_red]]),ground([_expr,_form]),linear(_ans))),
    t_reduce(_next,_ans),
    !,
    true((mshare([[_expr,_next],[_expr,_next,_red],[_expr,_next,_red,_form],[_expr,_next,_form],[_expr,_form],[_next,_red]]),ground([_ans]);mshare([[_next,_red]]),ground([_expr,_ans,_form]))).

:- true pred t_append(_link,_A,_l,_B)
   : ( mshare([[_link],[_A],[_l],[_B]]),
       linear(_link), linear(_A), linear(_l) )
   => ( mshare([[_link,_A],[_link,_l,_B],[_link,_B],[_l,_B]]),
        linear(_A) ).

:- true pred t_append(_link,_A,_l,_B)
   : ( mshare([[_link],[_A],[_l]]),
       ground([_B]), linear(_link), linear(_A), linear(_l) )
   => ( mshare([[_link,_A]]),
        ground([_l,_B]), linear(_A) ).

t_append(_link,_link,_l,_l).
t_append([_a|_l1],_link,_l2,[_a|_l3]) :-
    true((mshare([[_link],[_l2],[_a],[_a,_l3],[_l1],[_l3]]),linear(_link),linear(_l2),linear(_l1);mshare([[_link],[_l2],[_l1]]),ground([_a,_l3]),linear(_link),linear(_l2),linear(_l1))),
    t_append(_l1,_link,_l2,_l3),
    true((mshare([[_link,_l1]]),ground([_l2,_a,_l3]),linear(_link);mshare([[_link,_l1],[_l2,_a,_l1,_l3],[_l2,_a,_l3],[_l2,_l1,_l3],[_l2,_l3],[_a],[_a,_l1,_l3],[_l1,_l3]]),linear(_link))).

:- true pred t_redex(_in,_x)
   : ( mshare([[_in],[_x]]),
       linear(_x) )
   => mshare([[_in],[_in,_x],[_x]]).

:- true pred t_redex(_in,_x)
   : ( mshare([[_x]]),
       ground([_in]), linear(_x) )
   => ( mshare([[_x]]),
        ground([_in]) ).

t_redex([_x,_g,_f,_k|sp],[[_xr|_g],[_xr|_f]|_k]) :-
    true((mshare([[_x],[_x,_g],[_x,_g,_f],[_x,_g,_f,_k],[_x,_g,_k],[_x,_f],[_x,_f,_k],[_x,_k],[_g],[_g,_f],[_g,_f,_k],[_g,_k],[_f],[_f,_k],[_k],[_xr]]),linear(_xr);mshare([[_xr]]),ground([_x,_g,_f,_k]),linear(_xr))),
    t_reduce(_x,_xr),
    true((mshare([[_x],[_x,_g],[_x,_g,_f],[_x,_g,_f,_k],[_x,_g,_k],[_x,_f],[_x,_f,_k],[_x,_k],[_g],[_g,_f],[_g,_f,_k],[_g,_k],[_f],[_f,_k],[_k]]),ground([_xr]);ground([_x,_g,_f,_k,_xr]))).
t_redex([_x,_g,_f,_k|bp],[[_x|_g],_f|_k]).
t_redex([_x,_g,_f,_k|cp],[_g,[_x|_f]|_k]).
t_redex([_x,_g,_f|s],[[_xr|_g],_xr|_f]) :-
    true((mshare([[_x],[_x,_g],[_x,_g,_f],[_x,_f],[_g],[_g,_f],[_f],[_xr]]),linear(_xr);mshare([[_xr]]),ground([_x,_g,_f]),linear(_xr))),
    t_reduce(_x,_xr),
    true((mshare([[_x],[_x,_g],[_x,_g,_f],[_x,_f],[_g],[_g,_f],[_f]]),ground([_xr]);ground([_x,_g,_f,_xr]))).
t_redex([_x,_g,_f|b],[[_x|_g]|_f]).
t_redex([_x,_g,_f|c],[_g,_x|_f]).
t_redex([_y,_x|k],_x).
t_redex([_x|i],_x).
t_redex([_elsepart,_ifpart,_cond|cond],_ifpart) :-
    true((mshare([[_ifpart],[_ifpart,_elsepart],[_ifpart,_elsepart,_cond],[_ifpart,_cond],[_elsepart],[_elsepart,_cond],[_cond],[_bool]]),linear(_bool);mshare([[_bool]]),ground([_ifpart,_elsepart,_cond]),linear(_bool))),
    t_reduce(_cond,_bool),
    true((mshare([[_ifpart],[_ifpart,_elsepart],[_ifpart,_elsepart,_cond],[_ifpart,_cond],[_elsepart],[_elsepart,_cond],[_cond]]),ground([_bool]);ground([_ifpart,_elsepart,_cond,_bool]))),
    _bool=true,
    !,
    true((mshare([[_ifpart],[_ifpart,_elsepart],[_ifpart,_elsepart,_cond],[_ifpart,_cond],[_elsepart],[_elsepart,_cond],[_cond]]),ground([_bool]);ground([_ifpart,_elsepart,_cond,_bool]))).
t_redex([_elsepart,_ifpart,_cond|cond],_elsepart).
t_redex([_f|apply],_fr) :-
    true((mshare([[_fr]]),ground([_f]),linear(_fr);mshare([[_fr],[_f]]),linear(_fr))),
    t_reduce(_f,_fr),
    true((mshare([[_f]]),ground([_fr]);ground([_fr,_f]))).
t_redex([_arg|hd],_x) :-
    true((mshare([[_x],[_arg],[LF],[_y]]),linear(_x),linear(LF),linear(_y);mshare([[_x],[LF],[_y]]),ground([_arg]),linear(_x),linear(LF),linear(_y))),
    list_functor_name(LF),
    true((mshare([[_x],[_arg],[_y]]),ground([LF]),linear(_x),linear(_y);mshare([[_x],[_y]]),ground([_arg,LF]),linear(_x),linear(_y))),
    t_reduce(_arg,[_y,_x|LF]),
    true((mshare([[_arg]]),ground([_x,LF,_y]);ground([_x,_arg,LF,_y]))).
t_redex([_arg|tl],_y) :-
    true((mshare([[_y],[_arg],[LF],[_x]]),linear(_y),linear(LF),linear(_x);mshare([[_y],[LF],[_x]]),ground([_arg]),linear(_y),linear(LF),linear(_x))),
    list_functor_name(LF),
    true((mshare([[_y],[_arg],[_x]]),ground([LF]),linear(_y),linear(_x);mshare([[_y],[_x]]),ground([_arg,LF]),linear(_y),linear(_x))),
    t_reduce(_arg,[_y,_x|LF]),
    true((mshare([[_arg]]),ground([_y,LF,_x]);ground([_y,_arg,LF,_x]))).
t_redex([_y,_x|_op],_res) :-
    true((mshare([[_res],[_y],[_y,_x],[_y,_x,_op],[_y,_op],[_x],[_x,_op],[_op],[_xres],[_yres]]),linear(_res),linear(_xres),linear(_yres);mshare([[_res],[_xres],[_yres]]),ground([_y,_x,_op]),linear(_res),linear(_xres),linear(_yres))),
    end(_op),
    true((mshare([[_res],[_y],[_y,_x],[_x],[_xres],[_yres]]),ground([_op]),linear(_res),linear(_xres),linear(_yres);mshare([[_res],[_xres],[_yres]]),ground([_y,_x,_op]),linear(_res),linear(_xres),linear(_yres))),
    my_member(_op,[+,-,*,//,mod]),
    true((mshare([[_res],[_y],[_y,_x],[_x],[_xres],[_yres]]),ground([_op]),linear(_res),linear(_xres),linear(_yres);mshare([[_res],[_xres],[_yres]]),ground([_y,_x,_op]),linear(_res),linear(_xres),linear(_yres))),
    t_reduce(_x,_xres),
    true((mshare([[_res],[_y],[_y,_x],[_x],[_yres]]),ground([_op,_xres]),linear(_res),linear(_yres);mshare([[_res],[_yres]]),ground([_y,_x,_op,_xres]),linear(_res),linear(_yres))),
    t_reduce(_y,_yres),
    true((mshare([[_res]]),ground([_y,_x,_op,_xres,_yres]),linear(_res);mshare([[_res],[_y],[_y,_x],[_x]]),ground([_op,_xres,_yres]),linear(_res))),
    number(_xres),
    true((mshare([[_res]]),ground([_y,_x,_op,_xres,_yres]),linear(_res);mshare([[_res],[_y],[_y,_x],[_x]]),ground([_op,_xres,_yres]),linear(_res))),
    number(_yres),
    true((mshare([[_res]]),ground([_y,_x,_op,_xres,_yres]),linear(_res);mshare([[_res],[_y],[_y,_x],[_x]]),ground([_op,_xres,_yres]),linear(_res))),
    eval(_op,_res,_xres,_yres),
    true((mshare([[_y],[_y,_x],[_x]]),ground([_res,_op,_xres,_yres]);ground([_res,_y,_x,_op,_xres,_yres]))).
t_redex([_y,_x|_test],_res) :-
    true((mshare([[_res],[_y],[_y,_x],[_y,_x,_test],[_y,_test],[_x],[_x,_test],[_test],[_xres],[_yres]]),linear(_res),linear(_xres),linear(_yres);mshare([[_res],[_xres],[_yres]]),ground([_y,_x,_test]),linear(_res),linear(_xres),linear(_yres))),
    end(_test),
    true((mshare([[_res],[_y],[_y,_x],[_x],[_xres],[_yres]]),ground([_test]),linear(_res),linear(_xres),linear(_yres);mshare([[_res],[_xres],[_yres]]),ground([_y,_x,_test]),linear(_res),linear(_xres),linear(_yres))),
    my_member(_test,[<,>,=<,>=,=\=,=:=]),
    true((mshare([[_res],[_y],[_y,_x],[_x],[_xres],[_yres]]),ground([_test]),linear(_res),linear(_xres),linear(_yres);mshare([[_res],[_xres],[_yres]]),ground([_y,_x,_test]),linear(_res),linear(_xres),linear(_yres))),
    t_reduce(_x,_xres),
    true((mshare([[_res],[_y],[_y,_x],[_x],[_yres]]),ground([_test,_xres]),linear(_res),linear(_yres);mshare([[_res],[_yres]]),ground([_y,_x,_test,_xres]),linear(_res),linear(_yres))),
    t_reduce(_y,_yres),
    true((mshare([[_res]]),ground([_y,_x,_test,_xres,_yres]),linear(_res);mshare([[_res],[_y],[_y,_x],[_x]]),ground([_test,_xres,_yres]),linear(_res))),
    number(_xres),
    true((mshare([[_res]]),ground([_y,_x,_test,_xres,_yres]),linear(_res);mshare([[_res],[_y],[_y,_x],[_x]]),ground([_test,_xres,_yres]),linear(_res))),
    number(_yres),
    true((mshare([[_res]]),ground([_y,_x,_test,_xres,_yres]),linear(_res);mshare([[_res],[_y],[_y,_x],[_x]]),ground([_test,_xres,_yres]),linear(_res))),
    't_redex/2/15/$disj/1'(_res,_test,_xres,_yres),
    !,
    true((mshare([[_y],[_y,_x],[_x]]),ground([_res,_test,_xres,_yres]);ground([_res,_y,_x,_test,_xres,_yres]))).
t_redex([_y,_x|=],_res) :-
    true((mshare([[_res],[_y],[_y,_x],[_x],[_xres],[_yres]]),linear(_res),linear(_xres),linear(_yres);mshare([[_res],[_xres],[_yres]]),ground([_y,_x]),linear(_res),linear(_xres),linear(_yres))),
    t_reduce(_x,_xres),
    true((mshare([[_res],[_y],[_y,_x],[_x],[_yres]]),ground([_xres]),linear(_res),linear(_yres);mshare([[_res],[_yres]]),ground([_y,_x,_xres]),linear(_res),linear(_yres))),
    t_reduce(_y,_yres),
    true((mshare([[_res]]),ground([_y,_x,_xres,_yres]),linear(_res);mshare([[_res],[_y],[_y,_x],[_x]]),ground([_xres,_yres]),linear(_res))),
    't_redex/2/16/$disj/1'(_res,_xres,_yres),
    !,
    true((mshare([[_y],[_y,_x],[_x]]),ground([_res,_xres,_yres]);ground([_res,_y,_x,_xres,_yres]))).
t_redex([_x|_op],_res) :-
    true((mshare([[_res],[_x],[_x,_op],[_op],[_xres],[_t]]),linear(_res),linear(_xres),linear(_t);mshare([[_res],[_xres],[_t]]),ground([_x,_op]),linear(_res),linear(_xres),linear(_t))),
    end(_op),
    true((mshare([[_res],[_x],[_xres],[_t]]),ground([_op]),linear(_res),linear(_xres),linear(_t);mshare([[_res],[_xres],[_t]]),ground([_x,_op]),linear(_res),linear(_xres),linear(_t))),
    my_member(_op,[-]),
    true((mshare([[_res],[_x],[_xres],[_t]]),ground([_op]),linear(_res),linear(_xres),linear(_t);mshare([[_res],[_xres],[_t]]),ground([_x,_op]),linear(_res),linear(_xres),linear(_t))),
    t_reduce(_x,_xres),
    true((mshare([[_res],[_x],[_t]]),ground([_op,_xres]),linear(_res),linear(_t);mshare([[_res],[_t]]),ground([_x,_op,_xres]),linear(_res),linear(_t))),
    number(_xres),
    true((mshare([[_res],[_x],[_t]]),ground([_op,_xres]),linear(_res),linear(_t);mshare([[_res],[_t]]),ground([_x,_op,_xres]),linear(_res),linear(_t))),
    eval1(_op,_t,_xres),
    true((mshare([[_res]]),ground([_x,_op,_xres,_t]),linear(_res);mshare([[_res],[_x]]),ground([_op,_xres,_t]),linear(_res))).
t_redex(_in,_out) :-
    true((mshare([[_in],[_out],[_par],[_func],[_args],[_expr],[_def]]),linear(_out),linear(_par),linear(_func),linear(_args),linear(_expr),linear(_def);mshare([[_out],[_par],[_func],[_args],[_expr],[_def]]),ground([_in]),linear(_out),linear(_par),linear(_func),linear(_args),linear(_expr),linear(_def))),
    my_append(_par,_func,_in),
    true((mshare([[_in,_par],[_in,_par,_func],[_in,_func],[_out],[_args],[_expr],[_def]]),linear(_out),linear(_args),linear(_expr),linear(_def);mshare([[_out],[_args],[_expr],[_def]]),ground([_in,_par,_func]),linear(_out),linear(_args),linear(_expr),linear(_def))),
    end(_func),
    true((mshare([[_in,_par],[_out],[_args],[_expr],[_def]]),ground([_func]),linear(_out),linear(_args),linear(_expr),linear(_def);mshare([[_out],[_args],[_expr],[_def]]),ground([_in,_par,_func]),linear(_out),linear(_args),linear(_expr),linear(_def))),
    t_def(_func,_args,_expr),
    true((mshare([[_in,_par],[_out],[_args,_expr],[_def]]),ground([_func]),linear(_out),linear(_args),linear(_def);mshare([[_out],[_args,_expr],[_def]]),ground([_in,_par,_func]),linear(_out),linear(_args),linear(_def))),
    t(_args,_expr,_def),
    true((mshare([[_in,_par],[_out],[_args,_expr],[_args,_expr,_def]]),ground([_func]),linear(_out);mshare([[_out],[_args,_expr],[_args,_expr,_def]]),ground([_in,_par,_func]),linear(_out))),
    my_append(_par,_def,_out),
    true((mshare([[_in,_out,_par],[_out,_args,_expr,_def],[_args,_expr]]),ground([_func]);mshare([[_out,_args,_expr,_def],[_args,_expr]]),ground([_in,_par,_func]))).

:- true pred 't_redex/2/15/$disj/1'(_res,_test,_xres,_yres)
   : ( mshare([[_res]]),
       ground([_test,_xres,_yres]), linear(_res) )
   => ground([_res,_test,_xres,_yres]).

't_redex/2/15/$disj/1'(_res,_test,_xres,_yres) :-
    true((
        mshare([[_res]]),
        ground([_test,_xres,_yres]),
        linear(_res)
    )),
    relop(_test,_xres,_yres),
    !,
    true((
        mshare([[_res]]),
        ground([_test,_xres,_yres]),
        linear(_res)
    )),
    _res=true,
    true(ground([_res,_test,_xres,_yres])).
't_redex/2/15/$disj/1'(_res,_test,_xres,_yres) :-
    true((
        mshare([[_res]]),
        ground([_test,_xres,_yres]),
        linear(_res)
    )),
    _res=false,
    true(ground([_res,_test,_xres,_yres])).

:- true pred 't_redex/2/16/$disj/1'(_res,_xres,_yres)
   : ( mshare([[_res]]),
       ground([_xres,_yres]), linear(_res) )
   => ground([_res,_xres,_yres]).

't_redex/2/16/$disj/1'(_res,_xres,_yres) :-
    true((
        mshare([[_res]]),
        ground([_xres,_yres]),
        linear(_res)
    )),
    _xres=_yres,
    !,
    true((
        mshare([[_res]]),
        ground([_xres,_yres]),
        linear(_res)
    )),
    _res=true,
    true(ground([_res,_xres,_yres])).
't_redex/2/16/$disj/1'(_res,_xres,_yres) :-
    true((
        mshare([[_res]]),
        ground([_xres,_yres]),
        linear(_res)
    )),
    _res=false,
    true(ground([_res,_xres,_yres])).

:- true pred eval(_A,C,A,B)
   : ( mshare([[C]]),
       ground([_A,A,B]), linear(C) )
   => ground([_A,C,A,B]).

eval(+,C,A,B) :-
    true((
        mshare([[C]]),
        ground([A,B]),
        linear(C)
    )),
    C is A+B,
    true(ground([C,A,B])).
eval(-,C,A,B) :-
    true((
        mshare([[C]]),
        ground([A,B]),
        linear(C)
    )),
    C is A-B,
    true(ground([C,A,B])).
eval(*,C,A,B) :-
    true((
        mshare([[C]]),
        ground([A,B]),
        linear(C)
    )),
    C is A*B,
    true(ground([C,A,B])).
eval(//,C,A,B) :-
    true((
        mshare([[C]]),
        ground([A,B]),
        linear(C)
    )),
    C is A//B,
    true(ground([C,A,B])).
eval(mod,C,A,B) :-
    true((
        mshare([[C]]),
        ground([A,B]),
        linear(C)
    )),
    C is A mod B,
    true(ground([C,A,B])).

:- true pred eval1(_A,C,A)
   : ( mshare([[C]]),
       ground([_A,A]), linear(C) )
   => ground([_A,C,A]).

eval1(-,C,A) :-
    true((
        mshare([[C]]),
        ground([A]),
        linear(C)
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
       linear(_argvars), linear(_trans) )
   => mshare([[_argvars,_expr],[_argvars,_expr,_trans]]).

t(_argvars,_expr,_trans) :-
    true((
        mshare([[_argvars,_expr],[_trans],[_list],[_curry]]),
        linear(_argvars),
        linear(_trans),
        linear(_list),
        linear(_curry)
    )),
    listify(_expr,_list),
    true((
        mshare([[_argvars,_expr],[_argvars,_expr,_list],[_trans],[_curry]]),
        linear(_trans),
        linear(_curry)
    )),
    curry(_list,_curry),
    true((
        mshare([[_argvars,_expr],[_argvars,_expr,_list,_curry],[_trans]]),
        linear(_trans)
    )),
    t_argvars(_argvars,_curry,_trans),
    !,
    true(mshare([[_argvars,_expr],[_argvars,_expr,_trans,_list,_curry],[_argvars,_expr,_list,_curry]])).

:- true pred t_argvars(_A,_trans,_B)
   : ( mshare([[_A],[_A,_trans],[_B]]),
       linear(_B) )
   => mshare([[_A],[_A,_trans],[_A,_trans,_B]]).

:- true pred t_argvars(_A,_trans,_B)
   : ( mshare([[_A],[_A,_trans],[_trans],[_B]]),
       linear(_B) )
   => mshare([[_A],[_A,_trans],[_A,_trans,_B],[_trans,_B]]).

t_argvars([],_trans,_trans).
t_argvars([_x|_argvars],_in,_trans) :-
    true((mshare([[_in],[_in,_x],[_in,_x,_argvars],[_in,_argvars],[_trans],[_x],[_x,_argvars],[_argvars],[_mid],[_vars]]),linear(_trans),linear(_mid),linear(_vars);mshare([[_in,_x],[_in,_x,_argvars],[_in,_argvars],[_trans],[_x],[_x,_argvars],[_argvars],[_mid],[_vars]]),linear(_trans),linear(_mid),linear(_vars))),
    t_argvars(_argvars,_in,_mid),
    true((mshare([[_in,_x,_argvars],[_in,_x,_argvars,_mid],[_in,_x,_mid],[_in,_argvars],[_in,_argvars,_mid],[_in,_mid],[_trans],[_x],[_x,_argvars],[_argvars],[_vars]]),linear(_trans),linear(_vars);mshare([[_in,_x,_argvars],[_in,_x,_argvars,_mid],[_in,_x,_mid],[_in,_argvars],[_in,_argvars,_mid],[_trans],[_x],[_x,_argvars],[_argvars],[_vars]]),linear(_trans),linear(_vars))),
    t_vars(_mid,_vars),
    true((mshare([[_in,_x,_argvars],[_in,_x,_argvars,_mid,_vars],[_in,_x,_mid,_vars],[_in,_argvars],[_in,_argvars,_mid,_vars],[_in,_mid,_vars],[_trans],[_x],[_x,_argvars],[_argvars]]),linear(_trans);mshare([[_in,_x,_argvars],[_in,_x,_argvars,_mid,_vars],[_in,_x,_mid,_vars],[_in,_argvars],[_in,_argvars,_mid,_vars],[_trans],[_x],[_x,_argvars],[_argvars]]),linear(_trans))),
    t_trans(_x,_mid,_vars,_trans),
    true((mshare([[_in,_trans,_x,_argvars,_mid,_vars],[_in,_trans,_x,_mid,_vars],[_in,_trans,_argvars,_mid,_vars],[_in,_trans,_mid,_vars],[_in,_x,_argvars],[_in,_x,_argvars,_mid,_vars],[_in,_x,_mid,_vars],[_in,_argvars],[_x],[_x,_argvars],[_argvars]]);mshare([[_in,_trans,_x,_argvars,_mid,_vars],[_in,_trans,_x,_mid,_vars],[_in,_trans,_argvars,_mid,_vars],[_in,_x,_argvars],[_in,_x,_argvars,_mid,_vars],[_in,_x,_mid,_vars],[_in,_argvars],[_x],[_x,_argvars],[_argvars]]))).

:- true pred curry(_a,_cargs)
   : ( mshare([[_cargs]]),
       ground([_a]), linear(_cargs) )
   => ground([_a,_cargs]).

:- true pred curry(_a,_cargs)
   : ( mshare([[_a],[_cargs]]),
       linear(_cargs) )
   => mshare([[_a,_cargs]]).

curry(_a,_a) :-
    true((mshare([[_a]]);ground([_a]))),
    'curry/2/1/$disj/1'(_a),
    !,
    true((mshare([[_a]]);ground([_a]))).
curry([_func|_args],_cargs) :-
    true((mshare([[_cargs]]),ground([_func,_args]),linear(_cargs);mshare([[_cargs],[_func],[_func,_args],[_args]]),linear(_cargs))),
    currylist(_args,_cargs,_func),
    true((mshare([[_cargs,_func],[_cargs,_func,_args],[_cargs,_args]]);ground([_cargs,_func,_args]))).

:- true pred 'curry/2/1/$disj/1'(_a)
   : mshare([[_a]])
   => mshare([[_a]]).

:- true pred 'curry/2/1/$disj/1'(_a)
   : ground([_a])
   => ground([_a]).

'curry/2/1/$disj/1'(_a) :-
    true((mshare([[_a]]);ground([_a]))),
    var(_a),
    true((fails(_);mshare([[_a]]),linear(_a))).
'curry/2/1/$disj/1'(_a) :-
    true((mshare([[_a]]);ground([_a]))),
    atomic(_a),
    true(ground([_a])).

:- true pred currylist(_A,_link,_B)
   : ( (_B=[_C|_D]),
       mshare([[_link]]),
       ground([_A,_C,_D]), linear(_link) )
   => ground([_A,_link,_C,_D]).

:- true pred currylist(_A,_link,_B)
   : ( mshare([[_link]]),
       ground([_A,_B]), linear(_link) )
   => ground([_A,_link,_B]).

:- true pred currylist(_A,_link,_B)
   : ( (_B=[_C|_D]),
       mshare([[_A],[_A,_C],[_A,_C,_D],[_A,_D],[_link],[_C],[_C,_D],[_D]]),
       linear(_link) )
   => mshare([[_A,_link],[_A,_link,_C],[_A,_link,_C,_D],[_A,_link,_D],[_link,_C],[_link,_C,_D],[_link,_D]]).

:- true pred currylist(_A,_link,_B)
   : ( mshare([[_A],[_A,_B],[_link],[_B]]),
       linear(_link) )
   => mshare([[_A,_link],[_A,_link,_B],[_link,_B]]).

currylist([],_link,_link) :-
    !,
    true((mshare([[_link]]);ground([_link]))).
currylist([_a|_args],_cargs,_link) :-
    true((mshare([[_cargs],[_link],[_link,_a],[_link,_a,_args],[_link,_args],[_a],[_a,_args],[_args],[_c]]),linear(_cargs),linear(_c);mshare([[_cargs],[_c]]),ground([_link,_a,_args]),linear(_cargs),linear(_c))),
    curry(_a,_c),
    true((mshare([[_cargs]]),ground([_link,_a,_args,_c]),linear(_cargs);mshare([[_cargs],[_link],[_link,_a,_args,_c],[_link,_a,_c],[_link,_args],[_a,_args,_c],[_a,_c],[_args]]),linear(_cargs))),
    currylist(_args,_cargs,[_c|_link]),
    true((mshare([[_cargs,_link],[_cargs,_link,_a,_args,_c],[_cargs,_link,_a,_c],[_cargs,_link,_args],[_cargs,_a,_args,_c],[_cargs,_a,_c],[_cargs,_args]]);ground([_cargs,_link,_a,_args,_c]))).

:- true pred t_vars(_v,_A)
   : ( mshare([[_v],[_A]]),
       linear(_A) )
   => mshare([[_v,_A]]).

:- true pred t_vars(_v,_A)
   : ( (_A=[_B|_C]),
       mshare([[_v],[_B],[_C]]),
       linear(_B), linear(_C) )
   => mshare([[_v,_B],[_v,_B,_C],[_v,_C]]).

t_vars(_v,[[_v]]) :-
    true(mshare([[_v]])),
    var(_v),
    !,
    true((
        mshare([[_v]]),
        linear(_v)
    )).
t_vars(_a,[[]]) :-
    true(mshare([[_a]])),
    atomic(_a),
    !,
    true(ground([_a])).
t_vars([_func],[[]]) :-
    true(mshare([[_func]])),
    atomic(_func),
    !,
    true(ground([_func])).
t_vars([_arg|_func],[_g,[_g1|_af1],[_g2|_af2]]) :-
    true((
        mshare([[_arg],[_arg,_func],[_func],[_g],[_g1],[_af1],[_g2],[_af2]]),
        linear(_g),
        linear(_g1),
        linear(_af1),
        linear(_g2),
        linear(_af2)
    )),
    t_vars(_arg,[_g1|_af1]),
    true((
        mshare([[_arg,_func,_g1],[_arg,_func,_g1,_af1],[_arg,_func,_af1],[_arg,_g1],[_arg,_g1,_af1],[_arg,_af1],[_func],[_g],[_g2],[_af2]]),
        linear(_g),
        linear(_g2),
        linear(_af2)
    )),
    t_vars(_func,[_g2|_af2]),
    true((
        mshare([[_arg,_func,_g1,_af1,_g2],[_arg,_func,_g1,_af1,_g2,_af2],[_arg,_func,_g1,_af1,_af2],[_arg,_func,_g1,_g2],[_arg,_func,_g1,_g2,_af2],[_arg,_func,_g1,_af2],[_arg,_func,_af1,_g2],[_arg,_func,_af1,_g2,_af2],[_arg,_func,_af1,_af2],[_arg,_g1],[_arg,_g1,_af1],[_arg,_af1],[_func,_g2],[_func,_g2,_af2],[_func,_af2],[_g]]),
        linear(_g)
    )),
    unionv(_g1,_g2,_g),
    true(mshare([[_arg,_func,_g,_g1,_af1,_g2],[_arg,_func,_g,_g1,_af1,_g2,_af2],[_arg,_func,_g,_g1,_af1,_af2],[_arg,_func,_g,_g1,_g2],[_arg,_func,_g,_g1,_g2,_af2],[_arg,_func,_g,_g1,_af2],[_arg,_func,_g,_af1,_g2],[_arg,_func,_g,_af1,_g2,_af2],[_arg,_func,_g1,_af1,_g2],[_arg,_func,_g1,_af1,_g2,_af2],[_arg,_func,_g1,_af1,_af2],[_arg,_func,_g1,_g2],[_arg,_func,_g1,_g2,_af2],[_arg,_func,_g1,_af2],[_arg,_func,_af1,_g2],[_arg,_func,_af1,_g2,_af2],[_arg,_func,_af1,_af2],[_arg,_g,_g1],[_arg,_g,_g1,_af1],[_arg,_g1],[_arg,_g1,_af1],[_arg,_af1],[_func,_g,_g2],[_func,_g,_g2,_af2],[_func,_g2],[_func,_g2,_af2],[_func,_af2]])).

:- true pred t_trans(_x,_a,_1,_res)
   : ( mshare([[_x],[_x,_a,_1],[_a,_1],[_res]]),
       linear(_res) )
   => mshare([[_x],[_x,_a,_1],[_x,_a,_1,_res],[_a,_1,_res]]).

:- true pred t_trans(_x,_a,_1,_res)
   : ( mshare([[_x],[_x,_a],[_x,_a,_1],[_x,_1],[_a],[_a,_1],[_1],[_res]]),
       linear(_res) )
   => mshare([[_x],[_x,_a],[_x,_a,_1],[_x,_a,_1,_res],[_x,_a,_res],[_x,_1],[_a,_1,_res],[_a,_res],[_1]]).

t_trans(_x,_a,_1,[_a|k]) :-
    true((mshare([[_x],[_x,_a],[_x,_a,_1],[_x,_1],[_a],[_a,_1],[_1]]);mshare([[_x],[_x,_a,_1],[_a,_1]]))),
    't_trans/4/1/$disj/1'(_x,_a),
    !,
    true((mshare([[_x],[_x,_a],[_x,_a,_1],[_x,_1],[_a],[_a,_1],[_1]]);mshare([[_x],[_x,_a,_1],[_a,_1]]))).
t_trans(_x,_y,_1,i) :-
    true((mshare([[_x],[_x,_y],[_x,_y,_1],[_x,_1],[_y],[_y,_1],[_1]]);mshare([[_x],[_x,_y,_1],[_y,_1]]))),
    _x==_y,
    !,
    true((mshare([[_x,_y],[_x,_y,_1],[_1]]);mshare([[_x,_y,_1]]))).
t_trans(_x,_e,[_ve|_1],[_e|k]) :-
    true((mshare([[_x],[_x,_e],[_x,_e,_ve],[_x,_e,_ve,_1],[_x,_e,_1],[_x,_ve],[_x,_ve,_1],[_x,_1],[_e],[_e,_ve],[_e,_ve,_1],[_e,_1],[_ve],[_ve,_1],[_1]]);mshare([[_x],[_x,_e,_ve],[_x,_e,_ve,_1],[_x,_e,_1],[_e,_ve],[_e,_ve,_1],[_e,_1]]))),
    notinv(_x,_ve),
    true((mshare([[_x],[_x,_e],[_x,_e,_ve],[_x,_e,_ve,_1],[_x,_e,_1],[_x,_ve],[_x,_ve,_1],[_x,_1],[_e],[_e,_ve],[_e,_ve,_1],[_e,_1],[_ve],[_ve,_1],[_1]]);mshare([[_x],[_x,_e,_ve],[_x,_e,_ve,_1],[_x,_e,_1],[_e,_ve],[_e,_ve,_1],[_e,_1]]))).
t_trans(_x,[_f|_e],[_vef,_sf,_se],_res) :-
    true((mshare([[_x],[_x,_f],[_x,_f,_e],[_x,_f,_e,_vef],[_x,_f,_e,_vef,_sf],[_x,_f,_e,_vef,_sf,_se],[_x,_f,_e,_vef,_se],[_x,_f,_e,_sf],[_x,_f,_e,_sf,_se],[_x,_f,_e,_se],[_x,_f,_vef],[_x,_f,_vef,_sf],[_x,_f,_vef,_sf,_se],[_x,_f,_vef,_se],[_x,_f,_sf],[_x,_f,_sf,_se],[_x,_f,_se],[_x,_e],[_x,_e,_vef],[_x,_e,_vef,_sf],[_x,_e,_vef,_sf,_se],[_x,_e,_vef,_se],[_x,_e,_sf],[_x,_e,_sf,_se],[_x,_e,_se],[_x,_vef],[_x,_vef,_sf],[_x,_vef,_sf,_se],[_x,_vef,_se],[_x,_sf],[_x,_sf,_se],[_x,_se],[_res],[_f],[_f,_e],[_f,_e,_vef],[_f,_e,_vef,_sf],[_f,_e,_vef,_sf,_se],[_f,_e,_vef,_se],[_f,_e,_sf],[_f,_e,_sf,_se],[_f,_e,_se],[_f,_vef],[_f,_vef,_sf],[_f,_vef,_sf,_se],[_f,_vef,_se],[_f,_sf],[_f,_sf,_se],[_f,_se],[_e],[_e,_vef],[_e,_vef,_sf],[_e,_vef,_sf,_se],[_e,_vef,_se],[_e,_sf],[_e,_sf,_se],[_e,_se],[_vef],[_vef,_sf],[_vef,_sf,_se],[_vef,_se],[_sf],[_sf,_se],[_se],[_vf],[_1],[_ve],[_other]]),linear(_res),linear(_vf),linear(_1),linear(_ve),linear(_other);mshare([[_x],[_x,_f,_e,_vef],[_x,_f,_e,_vef,_sf],[_x,_f,_e,_vef,_sf,_se],[_x,_f,_e,_vef,_se],[_x,_f,_e,_sf],[_x,_f,_e,_sf,_se],[_x,_f,_e,_se],[_x,_f,_vef],[_x,_f,_vef,_sf],[_x,_f,_vef,_sf,_se],[_x,_f,_vef,_se],[_x,_f,_sf],[_x,_f,_sf,_se],[_x,_f,_se],[_x,_e,_vef],[_x,_e,_vef,_sf],[_x,_e,_vef,_sf,_se],[_x,_e,_vef,_se],[_x,_e,_sf],[_x,_e,_sf,_se],[_x,_e,_se],[_res],[_f,_e,_vef],[_f,_e,_vef,_sf],[_f,_e,_vef,_sf,_se],[_f,_e,_vef,_se],[_f,_e,_sf],[_f,_e,_sf,_se],[_f,_e,_se],[_f,_vef],[_f,_vef,_sf],[_f,_vef,_sf,_se],[_f,_vef,_se],[_f,_sf],[_f,_sf,_se],[_f,_se],[_e,_vef],[_e,_vef,_sf],[_e,_vef,_sf,_se],[_e,_vef,_se],[_e,_sf],[_e,_sf,_se],[_e,_se],[_vf],[_1],[_ve],[_other]]),linear(_res),linear(_vf),linear(_1),linear(_ve),linear(_other))),
    _sf=[_vf|_1],
    true((mshare([[_x],[_x,_f],[_x,_f,_e],[_x,_f,_e,_vef],[_x,_f,_e,_vef,_sf,_se,_vf],[_x,_f,_e,_vef,_sf,_se,_vf,_1],[_x,_f,_e,_vef,_sf,_se,_1],[_x,_f,_e,_vef,_sf,_vf],[_x,_f,_e,_vef,_sf,_vf,_1],[_x,_f,_e,_vef,_sf,_1],[_x,_f,_e,_vef,_se],[_x,_f,_e,_sf,_se,_vf],[_x,_f,_e,_sf,_se,_vf,_1],[_x,_f,_e,_sf,_se,_1],[_x,_f,_e,_sf,_vf],[_x,_f,_e,_sf,_vf,_1],[_x,_f,_e,_sf,_1],[_x,_f,_e,_se],[_x,_f,_vef],[_x,_f,_vef,_sf,_se,_vf],[_x,_f,_vef,_sf,_se,_vf,_1],[_x,_f,_vef,_sf,_se,_1],[_x,_f,_vef,_sf,_vf],[_x,_f,_vef,_sf,_vf,_1],[_x,_f,_vef,_sf,_1],[_x,_f,_vef,_se],[_x,_f,_sf,_se,_vf],[_x,_f,_sf,_se,_vf,_1],[_x,_f,_sf,_se,_1],[_x,_f,_sf,_vf],[_x,_f,_sf,_vf,_1],[_x,_f,_sf,_1],[_x,_f,_se],[_x,_e],[_x,_e,_vef],[_x,_e,_vef,_sf,_se,_vf],[_x,_e,_vef,_sf,_se,_vf,_1],[_x,_e,_vef,_sf,_se,_1],[_x,_e,_vef,_sf,_vf],[_x,_e,_vef,_sf,_vf,_1],[_x,_e,_vef,_sf,_1],[_x,_e,_vef,_se],[_x,_e,_sf,_se,_vf],[_x,_e,_sf,_se,_vf,_1],[_x,_e,_sf,_se,_1],[_x,_e,_sf,_vf],[_x,_e,_sf,_vf,_1],[_x,_e,_sf,_1],[_x,_e,_se],[_x,_vef],[_x,_vef,_sf,_se,_vf],[_x,_vef,_sf,_se,_vf,_1],[_x,_vef,_sf,_se,_1],[_x,_vef,_sf,_vf],[_x,_vef,_sf,_vf,_1],[_x,_vef,_sf,_1],[_x,_vef,_se],[_x,_sf,_se,_vf],[_x,_sf,_se,_vf,_1],[_x,_sf,_se,_1],[_x,_sf,_vf],[_x,_sf,_vf,_1],[_x,_sf,_1],[_x,_se],[_res],[_f],[_f,_e],[_f,_e,_vef],[_f,_e,_vef,_sf,_se,_vf],[_f,_e,_vef,_sf,_se,_vf,_1],[_f,_e,_vef,_sf,_se,_1],[_f,_e,_vef,_sf,_vf],[_f,_e,_vef,_sf,_vf,_1],[_f,_e,_vef,_sf,_1],[_f,_e,_vef,_se],[_f,_e,_sf,_se,_vf],[_f,_e,_sf,_se,_vf,_1],[_f,_e,_sf,_se,_1],[_f,_e,_sf,_vf],[_f,_e,_sf,_vf,_1],[_f,_e,_sf,_1],[_f,_e,_se],[_f,_vef],[_f,_vef,_sf,_se,_vf],[_f,_vef,_sf,_se,_vf,_1],[_f,_vef,_sf,_se,_1],[_f,_vef,_sf,_vf],[_f,_vef,_sf,_vf,_1],[_f,_vef,_sf,_1],[_f,_vef,_se],[_f,_sf,_se,_vf],[_f,_sf,_se,_vf,_1],[_f,_sf,_se,_1],[_f,_sf,_vf],[_f,_sf,_vf,_1],[_f,_sf,_1],[_f,_se],[_e],[_e,_vef],[_e,_vef,_sf,_se,_vf],[_e,_vef,_sf,_se,_vf,_1],[_e,_vef,_sf,_se,_1],[_e,_vef,_sf,_vf],[_e,_vef,_sf,_vf,_1],[_e,_vef,_sf,_1],[_e,_vef,_se],[_e,_sf,_se,_vf],[_e,_sf,_se,_vf,_1],[_e,_sf,_se,_1],[_e,_sf,_vf],[_e,_sf,_vf,_1],[_e,_sf,_1],[_e,_se],[_vef],[_vef,_sf,_se,_vf],[_vef,_sf,_se,_vf,_1],[_vef,_sf,_se,_1],[_vef,_sf,_vf],[_vef,_sf,_vf,_1],[_vef,_sf,_1],[_vef,_se],[_sf,_se,_vf],[_sf,_se,_vf,_1],[_sf,_se,_1],[_sf,_vf],[_sf,_vf,_1],[_sf,_1],[_se],[_ve],[_other]]),linear(_res),linear(_ve),linear(_other);mshare([[_x],[_x,_f,_e,_vef],[_x,_f,_e,_vef,_sf,_se,_vf],[_x,_f,_e,_vef,_sf,_se,_vf,_1],[_x,_f,_e,_vef,_sf,_se,_1],[_x,_f,_e,_vef,_sf,_vf],[_x,_f,_e,_vef,_sf,_vf,_1],[_x,_f,_e,_vef,_sf,_1],[_x,_f,_e,_vef,_se],[_x,_f,_e,_sf,_se,_vf],[_x,_f,_e,_sf,_se,_vf,_1],[_x,_f,_e,_sf,_se,_1],[_x,_f,_e,_sf,_vf],[_x,_f,_e,_sf,_vf,_1],[_x,_f,_e,_sf,_1],[_x,_f,_e,_se],[_x,_f,_vef],[_x,_f,_vef,_sf,_se,_vf],[_x,_f,_vef,_sf,_se,_vf,_1],[_x,_f,_vef,_sf,_se,_1],[_x,_f,_vef,_sf,_vf],[_x,_f,_vef,_sf,_vf,_1],[_x,_f,_vef,_sf,_1],[_x,_f,_vef,_se],[_x,_f,_sf,_se,_vf],[_x,_f,_sf,_se,_vf,_1],[_x,_f,_sf,_se,_1],[_x,_f,_sf,_vf],[_x,_f,_sf,_vf,_1],[_x,_f,_sf,_1],[_x,_f,_se],[_x,_e,_vef],[_x,_e,_vef,_sf,_se,_vf],[_x,_e,_vef,_sf,_se,_vf,_1],[_x,_e,_vef,_sf,_se,_1],[_x,_e,_vef,_sf,_vf],[_x,_e,_vef,_sf,_vf,_1],[_x,_e,_vef,_sf,_1],[_x,_e,_vef,_se],[_x,_e,_sf,_se,_vf],[_x,_e,_sf,_se,_vf,_1],[_x,_e,_sf,_se,_1],[_x,_e,_sf,_vf],[_x,_e,_sf,_vf,_1],[_x,_e,_sf,_1],[_x,_e,_se],[_res],[_f,_e,_vef],[_f,_e,_vef,_sf,_se,_vf],[_f,_e,_vef,_sf,_se,_vf,_1],[_f,_e,_vef,_sf,_se,_1],[_f,_e,_vef,_sf,_vf],[_f,_e,_vef,_sf,_vf,_1],[_f,_e,_vef,_sf,_1],[_f,_e,_vef,_se],[_f,_e,_sf,_se,_vf],[_f,_e,_sf,_se,_vf,_1],[_f,_e,_sf,_se,_1],[_f,_e,_sf,_vf],[_f,_e,_sf,_vf,_1],[_f,_e,_sf,_1],[_f,_e,_se],[_f,_vef],[_f,_vef,_sf,_se,_vf],[_f,_vef,_sf,_se,_vf,_1],[_f,_vef,_sf,_se,_1],[_f,_vef,_sf,_vf],[_f,_vef,_sf,_vf,_1],[_f,_vef,_sf,_1],[_f,_vef,_se],[_f,_sf,_se,_vf],[_f,_sf,_se,_vf,_1],[_f,_sf,_se,_1],[_f,_sf,_vf],[_f,_sf,_vf,_1],[_f,_sf,_1],[_f,_se],[_e,_vef],[_e,_vef,_sf,_se,_vf],[_e,_vef,_sf,_se,_vf,_1],[_e,_vef,_sf,_se,_1],[_e,_vef,_sf,_vf],[_e,_vef,_sf,_vf,_1],[_e,_vef,_sf,_1],[_e,_vef,_se],[_e,_sf,_se,_vf],[_e,_sf,_se,_vf,_1],[_e,_sf,_se,_1],[_e,_sf,_vf],[_e,_sf,_vf,_1],[_e,_sf,_1],[_e,_se],[_ve],[_other]]),linear(_res),linear(_ve),linear(_other))),
    _se=[_ve|_other],
    true((mshare([[_x],[_x,_f],[_x,_f,_e],[_x,_f,_e,_vef],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_ve],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_ve],[_x,_f,_e,_vef,_sf,_se,_vf,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_other],[_x,_f,_e,_vef,_sf,_se,_1,_ve],[_x,_f,_e,_vef,_sf,_se,_1,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_1,_other],[_x,_f,_e,_vef,_sf,_vf],[_x,_f,_e,_vef,_sf,_vf,_1],[_x,_f,_e,_vef,_sf,_1],[_x,_f,_e,_vef,_se,_ve],[_x,_f,_e,_vef,_se,_ve,_other],[_x,_f,_e,_vef,_se,_other],[_x,_f,_e,_sf,_se,_vf,_1,_ve],[_x,_f,_e,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_e,_sf,_se,_vf,_1,_other],[_x,_f,_e,_sf,_se,_vf,_ve],[_x,_f,_e,_sf,_se,_vf,_ve,_other],[_x,_f,_e,_sf,_se,_vf,_other],[_x,_f,_e,_sf,_se,_1,_ve],[_x,_f,_e,_sf,_se,_1,_ve,_other],[_x,_f,_e,_sf,_se,_1,_other],[_x,_f,_e,_sf,_vf],[_x,_f,_e,_sf,_vf,_1],[_x,_f,_e,_sf,_1],[_x,_f,_e,_se,_ve],[_x,_f,_e,_se,_ve,_other],[_x,_f,_e,_se,_other],[_x,_f,_vef],[_x,_f,_vef,_sf,_se,_vf,_1,_ve],[_x,_f,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_vef,_sf,_se,_vf,_1,_other],[_x,_f,_vef,_sf,_se,_vf,_ve],[_x,_f,_vef,_sf,_se,_vf,_ve,_other],[_x,_f,_vef,_sf,_se,_vf,_other],[_x,_f,_vef,_sf,_se,_1,_ve],[_x,_f,_vef,_sf,_se,_1,_ve,_other],[_x,_f,_vef,_sf,_se,_1,_other],[_x,_f,_vef,_sf,_vf],[_x,_f,_vef,_sf,_vf,_1],[_x,_f,_vef,_sf,_1],[_x,_f,_vef,_se,_ve],[_x,_f,_vef,_se,_ve,_other],[_x,_f,_vef,_se,_other],[_x,_f,_sf,_se,_vf,_1,_ve],[_x,_f,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_sf,_se,_vf,_1,_other],[_x,_f,_sf,_se,_vf,_ve],[_x,_f,_sf,_se,_vf,_ve,_other],[_x,_f,_sf,_se,_vf,_other],[_x,_f,_sf,_se,_1,_ve],[_x,_f,_sf,_se,_1,_ve,_other],[_x,_f,_sf,_se,_1,_other],[_x,_f,_sf,_vf],[_x,_f,_sf,_vf,_1],[_x,_f,_sf,_1],[_x,_f,_se,_ve],[_x,_f,_se,_ve,_other],[_x,_f,_se,_other],[_x,_e],[_x,_e,_vef],[_x,_e,_vef,_sf,_se,_vf,_1,_ve],[_x,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_e,_vef,_sf,_se,_vf,_1,_other],[_x,_e,_vef,_sf,_se,_vf,_ve],[_x,_e,_vef,_sf,_se,_vf,_ve,_other],[_x,_e,_vef,_sf,_se,_vf,_other],[_x,_e,_vef,_sf,_se,_1,_ve],[_x,_e,_vef,_sf,_se,_1,_ve,_other],[_x,_e,_vef,_sf,_se,_1,_other],[_x,_e,_vef,_sf,_vf],[_x,_e,_vef,_sf,_vf,_1],[_x,_e,_vef,_sf,_1],[_x,_e,_vef,_se,_ve],[_x,_e,_vef,_se,_ve,_other],[_x,_e,_vef,_se,_other],[_x,_e,_sf,_se,_vf,_1,_ve],[_x,_e,_sf,_se,_vf,_1,_ve,_other],[_x,_e,_sf,_se,_vf,_1,_other],[_x,_e,_sf,_se,_vf,_ve],[_x,_e,_sf,_se,_vf,_ve,_other],[_x,_e,_sf,_se,_vf,_other],[_x,_e,_sf,_se,_1,_ve],[_x,_e,_sf,_se,_1,_ve,_other],[_x,_e,_sf,_se,_1,_other],[_x,_e,_sf,_vf],[_x,_e,_sf,_vf,_1],[_x,_e,_sf,_1],[_x,_e,_se,_ve],[_x,_e,_se,_ve,_other],[_x,_e,_se,_other],[_x,_vef],[_x,_vef,_sf,_se,_vf,_1,_ve],[_x,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_vef,_sf,_se,_vf,_1,_other],[_x,_vef,_sf,_se,_vf,_ve],[_x,_vef,_sf,_se,_vf,_ve,_other],[_x,_vef,_sf,_se,_vf,_other],[_x,_vef,_sf,_se,_1,_ve],[_x,_vef,_sf,_se,_1,_ve,_other],[_x,_vef,_sf,_se,_1,_other],[_x,_vef,_sf,_vf],[_x,_vef,_sf,_vf,_1],[_x,_vef,_sf,_1],[_x,_vef,_se,_ve],[_x,_vef,_se,_ve,_other],[_x,_vef,_se,_other],[_x,_sf,_se,_vf,_1,_ve],[_x,_sf,_se,_vf,_1,_ve,_other],[_x,_sf,_se,_vf,_1,_other],[_x,_sf,_se,_vf,_ve],[_x,_sf,_se,_vf,_ve,_other],[_x,_sf,_se,_vf,_other],[_x,_sf,_se,_1,_ve],[_x,_sf,_se,_1,_ve,_other],[_x,_sf,_se,_1,_other],[_x,_sf,_vf],[_x,_sf,_vf,_1],[_x,_sf,_1],[_x,_se,_ve],[_x,_se,_ve,_other],[_x,_se,_other],[_res],[_f],[_f,_e],[_f,_e,_vef],[_f,_e,_vef,_sf,_se,_vf,_1,_ve],[_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_f,_e,_vef,_sf,_se,_vf,_1,_other],[_f,_e,_vef,_sf,_se,_vf,_ve],[_f,_e,_vef,_sf,_se,_vf,_ve,_other],[_f,_e,_vef,_sf,_se,_vf,_other],[_f,_e,_vef,_sf,_se,_1,_ve],[_f,_e,_vef,_sf,_se,_1,_ve,_other],[_f,_e,_vef,_sf,_se,_1,_other],[_f,_e,_vef,_sf,_vf],[_f,_e,_vef,_sf,_vf,_1],[_f,_e,_vef,_sf,_1],[_f,_e,_vef,_se,_ve],[_f,_e,_vef,_se,_ve,_other],[_f,_e,_vef,_se,_other],[_f,_e,_sf,_se,_vf,_1,_ve],[_f,_e,_sf,_se,_vf,_1,_ve,_other],[_f,_e,_sf,_se,_vf,_1,_other],[_f,_e,_sf,_se,_vf,_ve],[_f,_e,_sf,_se,_vf,_ve,_other],[_f,_e,_sf,_se,_vf,_other],[_f,_e,_sf,_se,_1,_ve],[_f,_e,_sf,_se,_1,_ve,_other],[_f,_e,_sf,_se,_1,_other],[_f,_e,_sf,_vf],[_f,_e,_sf,_vf,_1],[_f,_e,_sf,_1],[_f,_e,_se,_ve],[_f,_e,_se,_ve,_other],[_f,_e,_se,_other],[_f,_vef],[_f,_vef,_sf,_se,_vf,_1,_ve],[_f,_vef,_sf,_se,_vf,_1,_ve,_other],[_f,_vef,_sf,_se,_vf,_1,_other],[_f,_vef,_sf,_se,_vf,_ve],[_f,_vef,_sf,_se,_vf,_ve,_other],[_f,_vef,_sf,_se,_vf,_other],[_f,_vef,_sf,_se,_1,_ve],[_f,_vef,_sf,_se,_1,_ve,_other],[_f,_vef,_sf,_se,_1,_other],[_f,_vef,_sf,_vf],[_f,_vef,_sf,_vf,_1],[_f,_vef,_sf,_1],[_f,_vef,_se,_ve],[_f,_vef,_se,_ve,_other],[_f,_vef,_se,_other],[_f,_sf,_se,_vf,_1,_ve],[_f,_sf,_se,_vf,_1,_ve,_other],[_f,_sf,_se,_vf,_1,_other],[_f,_sf,_se,_vf,_ve],[_f,_sf,_se,_vf,_ve,_other],[_f,_sf,_se,_vf,_other],[_f,_sf,_se,_1,_ve],[_f,_sf,_se,_1,_ve,_other],[_f,_sf,_se,_1,_other],[_f,_sf,_vf],[_f,_sf,_vf,_1],[_f,_sf,_1],[_f,_se,_ve],[_f,_se,_ve,_other],[_f,_se,_other],[_e],[_e,_vef],[_e,_vef,_sf,_se,_vf,_1,_ve],[_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_e,_vef,_sf,_se,_vf,_1,_other],[_e,_vef,_sf,_se,_vf,_ve],[_e,_vef,_sf,_se,_vf,_ve,_other],[_e,_vef,_sf,_se,_vf,_other],[_e,_vef,_sf,_se,_1,_ve],[_e,_vef,_sf,_se,_1,_ve,_other],[_e,_vef,_sf,_se,_1,_other],[_e,_vef,_sf,_vf],[_e,_vef,_sf,_vf,_1],[_e,_vef,_sf,_1],[_e,_vef,_se,_ve],[_e,_vef,_se,_ve,_other],[_e,_vef,_se,_other],[_e,_sf,_se,_vf,_1,_ve],[_e,_sf,_se,_vf,_1,_ve,_other],[_e,_sf,_se,_vf,_1,_other],[_e,_sf,_se,_vf,_ve],[_e,_sf,_se,_vf,_ve,_other],[_e,_sf,_se,_vf,_other],[_e,_sf,_se,_1,_ve],[_e,_sf,_se,_1,_ve,_other],[_e,_sf,_se,_1,_other],[_e,_sf,_vf],[_e,_sf,_vf,_1],[_e,_sf,_1],[_e,_se,_ve],[_e,_se,_ve,_other],[_e,_se,_other],[_vef],[_vef,_sf,_se,_vf,_1,_ve],[_vef,_sf,_se,_vf,_1,_ve,_other],[_vef,_sf,_se,_vf,_1,_other],[_vef,_sf,_se,_vf,_ve],[_vef,_sf,_se,_vf,_ve,_other],[_vef,_sf,_se,_vf,_other],[_vef,_sf,_se,_1,_ve],[_vef,_sf,_se,_1,_ve,_other],[_vef,_sf,_se,_1,_other],[_vef,_sf,_vf],[_vef,_sf,_vf,_1],[_vef,_sf,_1],[_vef,_se,_ve],[_vef,_se,_ve,_other],[_vef,_se,_other],[_sf,_se,_vf,_1,_ve],[_sf,_se,_vf,_1,_ve,_other],[_sf,_se,_vf,_1,_other],[_sf,_se,_vf,_ve],[_sf,_se,_vf,_ve,_other],[_sf,_se,_vf,_other],[_sf,_se,_1,_ve],[_sf,_se,_1,_ve,_other],[_sf,_se,_1,_other],[_sf,_vf],[_sf,_vf,_1],[_sf,_1],[_se,_ve],[_se,_ve,_other],[_se,_other]]),linear(_res);mshare([[_x],[_x,_f,_e,_vef],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_ve],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_ve],[_x,_f,_e,_vef,_sf,_se,_vf,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_other],[_x,_f,_e,_vef,_sf,_se,_1,_ve],[_x,_f,_e,_vef,_sf,_se,_1,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_1,_other],[_x,_f,_e,_vef,_sf,_vf],[_x,_f,_e,_vef,_sf,_vf,_1],[_x,_f,_e,_vef,_sf,_1],[_x,_f,_e,_vef,_se,_ve],[_x,_f,_e,_vef,_se,_ve,_other],[_x,_f,_e,_vef,_se,_other],[_x,_f,_e,_sf,_se,_vf,_1,_ve],[_x,_f,_e,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_e,_sf,_se,_vf,_1,_other],[_x,_f,_e,_sf,_se,_vf,_ve],[_x,_f,_e,_sf,_se,_vf,_ve,_other],[_x,_f,_e,_sf,_se,_vf,_other],[_x,_f,_e,_sf,_se,_1,_ve],[_x,_f,_e,_sf,_se,_1,_ve,_other],[_x,_f,_e,_sf,_se,_1,_other],[_x,_f,_e,_sf,_vf],[_x,_f,_e,_sf,_vf,_1],[_x,_f,_e,_sf,_1],[_x,_f,_e,_se,_ve],[_x,_f,_e,_se,_ve,_other],[_x,_f,_e,_se,_other],[_x,_f,_vef],[_x,_f,_vef,_sf,_se,_vf,_1,_ve],[_x,_f,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_vef,_sf,_se,_vf,_1,_other],[_x,_f,_vef,_sf,_se,_vf,_ve],[_x,_f,_vef,_sf,_se,_vf,_ve,_other],[_x,_f,_vef,_sf,_se,_vf,_other],[_x,_f,_vef,_sf,_se,_1,_ve],[_x,_f,_vef,_sf,_se,_1,_ve,_other],[_x,_f,_vef,_sf,_se,_1,_other],[_x,_f,_vef,_sf,_vf],[_x,_f,_vef,_sf,_vf,_1],[_x,_f,_vef,_sf,_1],[_x,_f,_vef,_se,_ve],[_x,_f,_vef,_se,_ve,_other],[_x,_f,_vef,_se,_other],[_x,_f,_sf,_se,_vf,_1,_ve],[_x,_f,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_sf,_se,_vf,_1,_other],[_x,_f,_sf,_se,_vf,_ve],[_x,_f,_sf,_se,_vf,_ve,_other],[_x,_f,_sf,_se,_vf,_other],[_x,_f,_sf,_se,_1,_ve],[_x,_f,_sf,_se,_1,_ve,_other],[_x,_f,_sf,_se,_1,_other],[_x,_f,_sf,_vf],[_x,_f,_sf,_vf,_1],[_x,_f,_sf,_1],[_x,_f,_se,_ve],[_x,_f,_se,_ve,_other],[_x,_f,_se,_other],[_x,_e,_vef],[_x,_e,_vef,_sf,_se,_vf,_1,_ve],[_x,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_e,_vef,_sf,_se,_vf,_1,_other],[_x,_e,_vef,_sf,_se,_vf,_ve],[_x,_e,_vef,_sf,_se,_vf,_ve,_other],[_x,_e,_vef,_sf,_se,_vf,_other],[_x,_e,_vef,_sf,_se,_1,_ve],[_x,_e,_vef,_sf,_se,_1,_ve,_other],[_x,_e,_vef,_sf,_se,_1,_other],[_x,_e,_vef,_sf,_vf],[_x,_e,_vef,_sf,_vf,_1],[_x,_e,_vef,_sf,_1],[_x,_e,_vef,_se,_ve],[_x,_e,_vef,_se,_ve,_other],[_x,_e,_vef,_se,_other],[_x,_e,_sf,_se,_vf,_1,_ve],[_x,_e,_sf,_se,_vf,_1,_ve,_other],[_x,_e,_sf,_se,_vf,_1,_other],[_x,_e,_sf,_se,_vf,_ve],[_x,_e,_sf,_se,_vf,_ve,_other],[_x,_e,_sf,_se,_vf,_other],[_x,_e,_sf,_se,_1,_ve],[_x,_e,_sf,_se,_1,_ve,_other],[_x,_e,_sf,_se,_1,_other],[_x,_e,_sf,_vf],[_x,_e,_sf,_vf,_1],[_x,_e,_sf,_1],[_x,_e,_se,_ve],[_x,_e,_se,_ve,_other],[_x,_e,_se,_other],[_res],[_f,_e,_vef],[_f,_e,_vef,_sf,_se,_vf,_1,_ve],[_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_f,_e,_vef,_sf,_se,_vf,_1,_other],[_f,_e,_vef,_sf,_se,_vf,_ve],[_f,_e,_vef,_sf,_se,_vf,_ve,_other],[_f,_e,_vef,_sf,_se,_vf,_other],[_f,_e,_vef,_sf,_se,_1,_ve],[_f,_e,_vef,_sf,_se,_1,_ve,_other],[_f,_e,_vef,_sf,_se,_1,_other],[_f,_e,_vef,_sf,_vf],[_f,_e,_vef,_sf,_vf,_1],[_f,_e,_vef,_sf,_1],[_f,_e,_vef,_se,_ve],[_f,_e,_vef,_se,_ve,_other],[_f,_e,_vef,_se,_other],[_f,_e,_sf,_se,_vf,_1,_ve],[_f,_e,_sf,_se,_vf,_1,_ve,_other],[_f,_e,_sf,_se,_vf,_1,_other],[_f,_e,_sf,_se,_vf,_ve],[_f,_e,_sf,_se,_vf,_ve,_other],[_f,_e,_sf,_se,_vf,_other],[_f,_e,_sf,_se,_1,_ve],[_f,_e,_sf,_se,_1,_ve,_other],[_f,_e,_sf,_se,_1,_other],[_f,_e,_sf,_vf],[_f,_e,_sf,_vf,_1],[_f,_e,_sf,_1],[_f,_e,_se,_ve],[_f,_e,_se,_ve,_other],[_f,_e,_se,_other],[_f,_vef],[_f,_vef,_sf,_se,_vf,_1,_ve],[_f,_vef,_sf,_se,_vf,_1,_ve,_other],[_f,_vef,_sf,_se,_vf,_1,_other],[_f,_vef,_sf,_se,_vf,_ve],[_f,_vef,_sf,_se,_vf,_ve,_other],[_f,_vef,_sf,_se,_vf,_other],[_f,_vef,_sf,_se,_1,_ve],[_f,_vef,_sf,_se,_1,_ve,_other],[_f,_vef,_sf,_se,_1,_other],[_f,_vef,_sf,_vf],[_f,_vef,_sf,_vf,_1],[_f,_vef,_sf,_1],[_f,_vef,_se,_ve],[_f,_vef,_se,_ve,_other],[_f,_vef,_se,_other],[_f,_sf,_se,_vf,_1,_ve],[_f,_sf,_se,_vf,_1,_ve,_other],[_f,_sf,_se,_vf,_1,_other],[_f,_sf,_se,_vf,_ve],[_f,_sf,_se,_vf,_ve,_other],[_f,_sf,_se,_vf,_other],[_f,_sf,_se,_1,_ve],[_f,_sf,_se,_1,_ve,_other],[_f,_sf,_se,_1,_other],[_f,_sf,_vf],[_f,_sf,_vf,_1],[_f,_sf,_1],[_f,_se,_ve],[_f,_se,_ve,_other],[_f,_se,_other],[_e,_vef],[_e,_vef,_sf,_se,_vf,_1,_ve],[_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_e,_vef,_sf,_se,_vf,_1,_other],[_e,_vef,_sf,_se,_vf,_ve],[_e,_vef,_sf,_se,_vf,_ve,_other],[_e,_vef,_sf,_se,_vf,_other],[_e,_vef,_sf,_se,_1,_ve],[_e,_vef,_sf,_se,_1,_ve,_other],[_e,_vef,_sf,_se,_1,_other],[_e,_vef,_sf,_vf],[_e,_vef,_sf,_vf,_1],[_e,_vef,_sf,_1],[_e,_vef,_se,_ve],[_e,_vef,_se,_ve,_other],[_e,_vef,_se,_other],[_e,_sf,_se,_vf,_1,_ve],[_e,_sf,_se,_vf,_1,_ve,_other],[_e,_sf,_se,_vf,_1,_other],[_e,_sf,_se,_vf,_ve],[_e,_sf,_se,_vf,_ve,_other],[_e,_sf,_se,_vf,_other],[_e,_sf,_se,_1,_ve],[_e,_sf,_se,_1,_ve,_other],[_e,_sf,_se,_1,_other],[_e,_sf,_vf],[_e,_sf,_vf,_1],[_e,_sf,_1],[_e,_se,_ve],[_e,_se,_ve,_other],[_e,_se,_other]]),linear(_res))),
    't_trans/4/4/$disj/1'(_e,_other),
    true((mshare([[_x],[_x,_f],[_x,_f,_e],[_x,_f,_e,_vef],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_ve],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_ve],[_x,_f,_e,_vef,_sf,_se,_vf,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_other],[_x,_f,_e,_vef,_sf,_se,_1,_ve],[_x,_f,_e,_vef,_sf,_se,_1,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_1,_other],[_x,_f,_e,_vef,_sf,_vf],[_x,_f,_e,_vef,_sf,_vf,_1],[_x,_f,_e,_vef,_sf,_1],[_x,_f,_e,_vef,_se,_ve],[_x,_f,_e,_vef,_se,_ve,_other],[_x,_f,_e,_vef,_se,_other],[_x,_f,_e,_sf,_se,_vf,_1,_ve],[_x,_f,_e,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_e,_sf,_se,_vf,_1,_other],[_x,_f,_e,_sf,_se,_vf,_ve],[_x,_f,_e,_sf,_se,_vf,_ve,_other],[_x,_f,_e,_sf,_se,_vf,_other],[_x,_f,_e,_sf,_se,_1,_ve],[_x,_f,_e,_sf,_se,_1,_ve,_other],[_x,_f,_e,_sf,_se,_1,_other],[_x,_f,_e,_sf,_vf],[_x,_f,_e,_sf,_vf,_1],[_x,_f,_e,_sf,_1],[_x,_f,_e,_se,_ve],[_x,_f,_e,_se,_ve,_other],[_x,_f,_e,_se,_other],[_x,_f,_vef],[_x,_f,_vef,_sf,_se,_vf,_1,_ve],[_x,_f,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_vef,_sf,_se,_vf,_1,_other],[_x,_f,_vef,_sf,_se,_vf,_ve],[_x,_f,_vef,_sf,_se,_vf,_ve,_other],[_x,_f,_vef,_sf,_se,_vf,_other],[_x,_f,_vef,_sf,_se,_1,_ve],[_x,_f,_vef,_sf,_se,_1,_ve,_other],[_x,_f,_vef,_sf,_se,_1,_other],[_x,_f,_vef,_sf,_vf],[_x,_f,_vef,_sf,_vf,_1],[_x,_f,_vef,_sf,_1],[_x,_f,_vef,_se,_ve],[_x,_f,_vef,_se,_ve,_other],[_x,_f,_vef,_se,_other],[_x,_f,_sf,_se,_vf,_1,_ve],[_x,_f,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_sf,_se,_vf,_1,_other],[_x,_f,_sf,_se,_vf,_ve],[_x,_f,_sf,_se,_vf,_ve,_other],[_x,_f,_sf,_se,_vf,_other],[_x,_f,_sf,_se,_1,_ve],[_x,_f,_sf,_se,_1,_ve,_other],[_x,_f,_sf,_se,_1,_other],[_x,_f,_sf,_vf],[_x,_f,_sf,_vf,_1],[_x,_f,_sf,_1],[_x,_f,_se,_ve],[_x,_f,_se,_ve,_other],[_x,_f,_se,_other],[_x,_e],[_x,_e,_vef],[_x,_e,_vef,_sf,_se,_vf,_1,_ve],[_x,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_e,_vef,_sf,_se,_vf,_1,_other],[_x,_e,_vef,_sf,_se,_vf,_ve],[_x,_e,_vef,_sf,_se,_vf,_ve,_other],[_x,_e,_vef,_sf,_se,_vf,_other],[_x,_e,_vef,_sf,_se,_1,_ve],[_x,_e,_vef,_sf,_se,_1,_ve,_other],[_x,_e,_vef,_sf,_se,_1,_other],[_x,_e,_vef,_sf,_vf],[_x,_e,_vef,_sf,_vf,_1],[_x,_e,_vef,_sf,_1],[_x,_e,_vef,_se,_ve],[_x,_e,_vef,_se,_ve,_other],[_x,_e,_vef,_se,_other],[_x,_e,_sf,_se,_vf,_1,_ve],[_x,_e,_sf,_se,_vf,_1,_ve,_other],[_x,_e,_sf,_se,_vf,_1,_other],[_x,_e,_sf,_se,_vf,_ve],[_x,_e,_sf,_se,_vf,_ve,_other],[_x,_e,_sf,_se,_vf,_other],[_x,_e,_sf,_se,_1,_ve],[_x,_e,_sf,_se,_1,_ve,_other],[_x,_e,_sf,_se,_1,_other],[_x,_e,_sf,_vf],[_x,_e,_sf,_vf,_1],[_x,_e,_sf,_1],[_x,_e,_se,_ve],[_x,_e,_se,_ve,_other],[_x,_e,_se,_other],[_x,_vef],[_x,_vef,_sf,_se,_vf,_1,_ve],[_x,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_vef,_sf,_se,_vf,_1,_other],[_x,_vef,_sf,_se,_vf,_ve],[_x,_vef,_sf,_se,_vf,_ve,_other],[_x,_vef,_sf,_se,_vf,_other],[_x,_vef,_sf,_se,_1,_ve],[_x,_vef,_sf,_se,_1,_ve,_other],[_x,_vef,_sf,_se,_1,_other],[_x,_vef,_sf,_vf],[_x,_vef,_sf,_vf,_1],[_x,_vef,_sf,_1],[_x,_vef,_se,_ve],[_x,_vef,_se,_ve,_other],[_x,_vef,_se,_other],[_x,_sf,_se,_vf,_1,_ve],[_x,_sf,_se,_vf,_1,_ve,_other],[_x,_sf,_se,_vf,_1,_other],[_x,_sf,_se,_vf,_ve],[_x,_sf,_se,_vf,_ve,_other],[_x,_sf,_se,_vf,_other],[_x,_sf,_se,_1,_ve],[_x,_sf,_se,_1,_ve,_other],[_x,_sf,_se,_1,_other],[_x,_sf,_vf],[_x,_sf,_vf,_1],[_x,_sf,_1],[_x,_se,_ve],[_x,_se,_ve,_other],[_x,_se,_other],[_res],[_f],[_f,_e],[_f,_e,_vef],[_f,_e,_vef,_sf,_se,_vf,_1,_ve],[_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_f,_e,_vef,_sf,_se,_vf,_1,_other],[_f,_e,_vef,_sf,_se,_vf,_ve],[_f,_e,_vef,_sf,_se,_vf,_ve,_other],[_f,_e,_vef,_sf,_se,_vf,_other],[_f,_e,_vef,_sf,_se,_1,_ve],[_f,_e,_vef,_sf,_se,_1,_ve,_other],[_f,_e,_vef,_sf,_se,_1,_other],[_f,_e,_vef,_sf,_vf],[_f,_e,_vef,_sf,_vf,_1],[_f,_e,_vef,_sf,_1],[_f,_e,_vef,_se,_ve],[_f,_e,_vef,_se,_ve,_other],[_f,_e,_vef,_se,_other],[_f,_e,_sf,_se,_vf,_1,_ve],[_f,_e,_sf,_se,_vf,_1,_ve,_other],[_f,_e,_sf,_se,_vf,_1,_other],[_f,_e,_sf,_se,_vf,_ve],[_f,_e,_sf,_se,_vf,_ve,_other],[_f,_e,_sf,_se,_vf,_other],[_f,_e,_sf,_se,_1,_ve],[_f,_e,_sf,_se,_1,_ve,_other],[_f,_e,_sf,_se,_1,_other],[_f,_e,_sf,_vf],[_f,_e,_sf,_vf,_1],[_f,_e,_sf,_1],[_f,_e,_se,_ve],[_f,_e,_se,_ve,_other],[_f,_e,_se,_other],[_f,_vef],[_f,_vef,_sf,_se,_vf,_1,_ve],[_f,_vef,_sf,_se,_vf,_1,_ve,_other],[_f,_vef,_sf,_se,_vf,_1,_other],[_f,_vef,_sf,_se,_vf,_ve],[_f,_vef,_sf,_se,_vf,_ve,_other],[_f,_vef,_sf,_se,_vf,_other],[_f,_vef,_sf,_se,_1,_ve],[_f,_vef,_sf,_se,_1,_ve,_other],[_f,_vef,_sf,_se,_1,_other],[_f,_vef,_sf,_vf],[_f,_vef,_sf,_vf,_1],[_f,_vef,_sf,_1],[_f,_vef,_se,_ve],[_f,_vef,_se,_ve,_other],[_f,_vef,_se,_other],[_f,_sf,_se,_vf,_1,_ve],[_f,_sf,_se,_vf,_1,_ve,_other],[_f,_sf,_se,_vf,_1,_other],[_f,_sf,_se,_vf,_ve],[_f,_sf,_se,_vf,_ve,_other],[_f,_sf,_se,_vf,_other],[_f,_sf,_se,_1,_ve],[_f,_sf,_se,_1,_ve,_other],[_f,_sf,_se,_1,_other],[_f,_sf,_vf],[_f,_sf,_vf,_1],[_f,_sf,_1],[_f,_se,_ve],[_f,_se,_ve,_other],[_f,_se,_other],[_e],[_e,_vef],[_e,_vef,_sf,_se,_vf,_1,_ve],[_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_e,_vef,_sf,_se,_vf,_1,_other],[_e,_vef,_sf,_se,_vf,_ve],[_e,_vef,_sf,_se,_vf,_ve,_other],[_e,_vef,_sf,_se,_vf,_other],[_e,_vef,_sf,_se,_1,_ve],[_e,_vef,_sf,_se,_1,_ve,_other],[_e,_vef,_sf,_se,_1,_other],[_e,_vef,_sf,_vf],[_e,_vef,_sf,_vf,_1],[_e,_vef,_sf,_1],[_e,_vef,_se,_ve],[_e,_vef,_se,_ve,_other],[_e,_vef,_se,_other],[_e,_sf,_se,_vf,_1,_ve],[_e,_sf,_se,_vf,_1,_ve,_other],[_e,_sf,_se,_vf,_1,_other],[_e,_sf,_se,_vf,_ve],[_e,_sf,_se,_vf,_ve,_other],[_e,_sf,_se,_vf,_other],[_e,_sf,_se,_1,_ve],[_e,_sf,_se,_1,_ve,_other],[_e,_sf,_se,_1,_other],[_e,_sf,_vf],[_e,_sf,_vf,_1],[_e,_sf,_1],[_e,_se,_ve],[_e,_se,_ve,_other],[_e,_se,_other],[_vef],[_vef,_sf,_se,_vf,_1,_ve],[_vef,_sf,_se,_vf,_1,_ve,_other],[_vef,_sf,_se,_vf,_1,_other],[_vef,_sf,_se,_vf,_ve],[_vef,_sf,_se,_vf,_ve,_other],[_vef,_sf,_se,_vf,_other],[_vef,_sf,_se,_1,_ve],[_vef,_sf,_se,_1,_ve,_other],[_vef,_sf,_se,_1,_other],[_vef,_sf,_vf],[_vef,_sf,_vf,_1],[_vef,_sf,_1],[_vef,_se,_ve],[_vef,_se,_ve,_other],[_vef,_se,_other],[_sf,_se,_vf,_1,_ve],[_sf,_se,_vf,_1,_ve,_other],[_sf,_se,_vf,_1,_other],[_sf,_se,_vf,_ve],[_sf,_se,_vf,_ve,_other],[_sf,_se,_vf,_other],[_sf,_se,_1,_ve],[_sf,_se,_1,_ve,_other],[_sf,_se,_1,_other],[_sf,_vf],[_sf,_vf,_1],[_sf,_1],[_se,_ve],[_se,_ve,_other],[_se,_other]]),linear(_res);mshare([[_x],[_x,_f,_e,_vef],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_ve],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_ve],[_x,_f,_e,_vef,_sf,_se,_vf,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_other],[_x,_f,_e,_vef,_sf,_se,_1,_ve],[_x,_f,_e,_vef,_sf,_se,_1,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_1,_other],[_x,_f,_e,_vef,_sf,_vf],[_x,_f,_e,_vef,_sf,_vf,_1],[_x,_f,_e,_vef,_sf,_1],[_x,_f,_e,_vef,_se,_ve],[_x,_f,_e,_vef,_se,_ve,_other],[_x,_f,_e,_vef,_se,_other],[_x,_f,_e,_sf,_se,_vf,_1,_ve],[_x,_f,_e,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_e,_sf,_se,_vf,_1,_other],[_x,_f,_e,_sf,_se,_vf,_ve],[_x,_f,_e,_sf,_se,_vf,_ve,_other],[_x,_f,_e,_sf,_se,_vf,_other],[_x,_f,_e,_sf,_se,_1,_ve],[_x,_f,_e,_sf,_se,_1,_ve,_other],[_x,_f,_e,_sf,_se,_1,_other],[_x,_f,_e,_sf,_vf],[_x,_f,_e,_sf,_vf,_1],[_x,_f,_e,_sf,_1],[_x,_f,_e,_se,_ve],[_x,_f,_e,_se,_ve,_other],[_x,_f,_e,_se,_other],[_x,_f,_vef],[_x,_f,_vef,_sf,_se,_vf,_1,_ve],[_x,_f,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_vef,_sf,_se,_vf,_1,_other],[_x,_f,_vef,_sf,_se,_vf,_ve],[_x,_f,_vef,_sf,_se,_vf,_ve,_other],[_x,_f,_vef,_sf,_se,_vf,_other],[_x,_f,_vef,_sf,_se,_1,_ve],[_x,_f,_vef,_sf,_se,_1,_ve,_other],[_x,_f,_vef,_sf,_se,_1,_other],[_x,_f,_vef,_sf,_vf],[_x,_f,_vef,_sf,_vf,_1],[_x,_f,_vef,_sf,_1],[_x,_f,_vef,_se,_ve],[_x,_f,_vef,_se,_ve,_other],[_x,_f,_vef,_se,_other],[_x,_f,_sf,_se,_vf,_1,_ve],[_x,_f,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_sf,_se,_vf,_1,_other],[_x,_f,_sf,_se,_vf,_ve],[_x,_f,_sf,_se,_vf,_ve,_other],[_x,_f,_sf,_se,_vf,_other],[_x,_f,_sf,_se,_1,_ve],[_x,_f,_sf,_se,_1,_ve,_other],[_x,_f,_sf,_se,_1,_other],[_x,_f,_sf,_vf],[_x,_f,_sf,_vf,_1],[_x,_f,_sf,_1],[_x,_f,_se,_ve],[_x,_f,_se,_ve,_other],[_x,_f,_se,_other],[_x,_e,_vef],[_x,_e,_vef,_sf,_se,_vf,_1,_ve],[_x,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_e,_vef,_sf,_se,_vf,_1,_other],[_x,_e,_vef,_sf,_se,_vf,_ve],[_x,_e,_vef,_sf,_se,_vf,_ve,_other],[_x,_e,_vef,_sf,_se,_vf,_other],[_x,_e,_vef,_sf,_se,_1,_ve],[_x,_e,_vef,_sf,_se,_1,_ve,_other],[_x,_e,_vef,_sf,_se,_1,_other],[_x,_e,_vef,_sf,_vf],[_x,_e,_vef,_sf,_vf,_1],[_x,_e,_vef,_sf,_1],[_x,_e,_vef,_se,_ve],[_x,_e,_vef,_se,_ve,_other],[_x,_e,_vef,_se,_other],[_x,_e,_sf,_se,_vf,_1,_ve],[_x,_e,_sf,_se,_vf,_1,_ve,_other],[_x,_e,_sf,_se,_vf,_1,_other],[_x,_e,_sf,_se,_vf,_ve],[_x,_e,_sf,_se,_vf,_ve,_other],[_x,_e,_sf,_se,_vf,_other],[_x,_e,_sf,_se,_1,_ve],[_x,_e,_sf,_se,_1,_ve,_other],[_x,_e,_sf,_se,_1,_other],[_x,_e,_sf,_vf],[_x,_e,_sf,_vf,_1],[_x,_e,_sf,_1],[_x,_e,_se,_ve],[_x,_e,_se,_ve,_other],[_x,_e,_se,_other],[_res],[_f,_e,_vef],[_f,_e,_vef,_sf,_se,_vf,_1,_ve],[_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_f,_e,_vef,_sf,_se,_vf,_1,_other],[_f,_e,_vef,_sf,_se,_vf,_ve],[_f,_e,_vef,_sf,_se,_vf,_ve,_other],[_f,_e,_vef,_sf,_se,_vf,_other],[_f,_e,_vef,_sf,_se,_1,_ve],[_f,_e,_vef,_sf,_se,_1,_ve,_other],[_f,_e,_vef,_sf,_se,_1,_other],[_f,_e,_vef,_sf,_vf],[_f,_e,_vef,_sf,_vf,_1],[_f,_e,_vef,_sf,_1],[_f,_e,_vef,_se,_ve],[_f,_e,_vef,_se,_ve,_other],[_f,_e,_vef,_se,_other],[_f,_e,_sf,_se,_vf,_1,_ve],[_f,_e,_sf,_se,_vf,_1,_ve,_other],[_f,_e,_sf,_se,_vf,_1,_other],[_f,_e,_sf,_se,_vf,_ve],[_f,_e,_sf,_se,_vf,_ve,_other],[_f,_e,_sf,_se,_vf,_other],[_f,_e,_sf,_se,_1,_ve],[_f,_e,_sf,_se,_1,_ve,_other],[_f,_e,_sf,_se,_1,_other],[_f,_e,_sf,_vf],[_f,_e,_sf,_vf,_1],[_f,_e,_sf,_1],[_f,_e,_se,_ve],[_f,_e,_se,_ve,_other],[_f,_e,_se,_other],[_f,_vef],[_f,_vef,_sf,_se,_vf,_1,_ve],[_f,_vef,_sf,_se,_vf,_1,_ve,_other],[_f,_vef,_sf,_se,_vf,_1,_other],[_f,_vef,_sf,_se,_vf,_ve],[_f,_vef,_sf,_se,_vf,_ve,_other],[_f,_vef,_sf,_se,_vf,_other],[_f,_vef,_sf,_se,_1,_ve],[_f,_vef,_sf,_se,_1,_ve,_other],[_f,_vef,_sf,_se,_1,_other],[_f,_vef,_sf,_vf],[_f,_vef,_sf,_vf,_1],[_f,_vef,_sf,_1],[_f,_vef,_se,_ve],[_f,_vef,_se,_ve,_other],[_f,_vef,_se,_other],[_f,_sf,_se,_vf,_1,_ve],[_f,_sf,_se,_vf,_1,_ve,_other],[_f,_sf,_se,_vf,_1,_other],[_f,_sf,_se,_vf,_ve],[_f,_sf,_se,_vf,_ve,_other],[_f,_sf,_se,_vf,_other],[_f,_sf,_se,_1,_ve],[_f,_sf,_se,_1,_ve,_other],[_f,_sf,_se,_1,_other],[_f,_sf,_vf],[_f,_sf,_vf,_1],[_f,_sf,_1],[_f,_se,_ve],[_f,_se,_ve,_other],[_f,_se,_other],[_e,_vef],[_e,_vef,_sf,_se,_vf,_1,_ve],[_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_e,_vef,_sf,_se,_vf,_1,_other],[_e,_vef,_sf,_se,_vf,_ve],[_e,_vef,_sf,_se,_vf,_ve,_other],[_e,_vef,_sf,_se,_vf,_other],[_e,_vef,_sf,_se,_1,_ve],[_e,_vef,_sf,_se,_1,_ve,_other],[_e,_vef,_sf,_se,_1,_other],[_e,_vef,_sf,_vf],[_e,_vef,_sf,_vf,_1],[_e,_vef,_sf,_1],[_e,_vef,_se,_ve],[_e,_vef,_se,_ve,_other],[_e,_vef,_se,_other],[_e,_sf,_se,_vf,_1,_ve],[_e,_sf,_se,_vf,_1,_ve,_other],[_e,_sf,_se,_vf,_1,_other],[_e,_sf,_se,_vf,_ve],[_e,_sf,_se,_vf,_ve,_other],[_e,_sf,_se,_vf,_other],[_e,_sf,_se,_1,_ve],[_e,_sf,_se,_1,_ve,_other],[_e,_sf,_se,_1,_other],[_e,_sf,_vf],[_e,_sf,_vf,_1],[_e,_sf,_1],[_e,_se,_ve],[_e,_se,_ve,_other],[_e,_se,_other]]),linear(_res))),
    t_rule1(_x,_e,_ve,_se,_f,_vf,_sf,_res),
    true((mshare([[_x],[_x,_res,_f],[_x,_res,_f,_e],[_x,_res,_f,_e,_vef],[_x,_res,_f,_e,_vef,_sf,_se,_vf,_1,_ve],[_x,_res,_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_res,_f,_e,_vef,_sf,_se,_vf,_1,_other],[_x,_res,_f,_e,_vef,_sf,_se,_vf,_ve],[_x,_res,_f,_e,_vef,_sf,_se,_vf,_ve,_other],[_x,_res,_f,_e,_vef,_sf,_se,_vf,_other],[_x,_res,_f,_e,_vef,_sf,_se,_1,_ve],[_x,_res,_f,_e,_vef,_sf,_se,_1,_ve,_other],[_x,_res,_f,_e,_vef,_sf,_se,_1,_other],[_x,_res,_f,_e,_vef,_sf,_vf],[_x,_res,_f,_e,_vef,_sf,_vf,_1],[_x,_res,_f,_e,_vef,_sf,_1],[_x,_res,_f,_e,_vef,_se,_ve],[_x,_res,_f,_e,_vef,_se,_ve,_other],[_x,_res,_f,_e,_vef,_se,_other],[_x,_res,_f,_e,_sf,_se,_vf,_1,_ve],[_x,_res,_f,_e,_sf,_se,_vf,_1,_ve,_other],[_x,_res,_f,_e,_sf,_se,_vf,_1,_other],[_x,_res,_f,_e,_sf,_se,_vf,_ve],[_x,_res,_f,_e,_sf,_se,_vf,_ve,_other],[_x,_res,_f,_e,_sf,_se,_vf,_other],[_x,_res,_f,_e,_sf,_se,_1,_ve],[_x,_res,_f,_e,_sf,_se,_1,_ve,_other],[_x,_res,_f,_e,_sf,_se,_1,_other],[_x,_res,_f,_e,_sf,_vf],[_x,_res,_f,_e,_sf,_vf,_1],[_x,_res,_f,_e,_sf,_1],[_x,_res,_f,_e,_se,_ve],[_x,_res,_f,_e,_se,_ve,_other],[_x,_res,_f,_e,_se,_other],[_x,_res,_f,_vef],[_x,_res,_f,_vef,_sf,_se,_vf,_1,_ve],[_x,_res,_f,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_res,_f,_vef,_sf,_se,_vf,_1,_other],[_x,_res,_f,_vef,_sf,_se,_vf,_ve],[_x,_res,_f,_vef,_sf,_se,_vf,_ve,_other],[_x,_res,_f,_vef,_sf,_se,_vf,_other],[_x,_res,_f,_vef,_sf,_se,_1,_ve],[_x,_res,_f,_vef,_sf,_se,_1,_ve,_other],[_x,_res,_f,_vef,_sf,_se,_1,_other],[_x,_res,_f,_vef,_sf,_vf],[_x,_res,_f,_vef,_sf,_vf,_1],[_x,_res,_f,_vef,_sf,_1],[_x,_res,_f,_vef,_se,_ve],[_x,_res,_f,_vef,_se,_ve,_other],[_x,_res,_f,_vef,_se,_other],[_x,_res,_f,_sf,_se,_vf,_1,_ve],[_x,_res,_f,_sf,_se,_vf,_1,_ve,_other],[_x,_res,_f,_sf,_se,_vf,_1,_other],[_x,_res,_f,_sf,_se,_vf,_ve],[_x,_res,_f,_sf,_se,_vf,_ve,_other],[_x,_res,_f,_sf,_se,_vf,_other],[_x,_res,_f,_sf,_se,_1,_ve],[_x,_res,_f,_sf,_se,_1,_ve,_other],[_x,_res,_f,_sf,_se,_1,_other],[_x,_res,_f,_sf,_vf],[_x,_res,_f,_sf,_vf,_1],[_x,_res,_f,_sf,_1],[_x,_res,_f,_se,_ve],[_x,_res,_f,_se,_ve,_other],[_x,_res,_f,_se,_other],[_x,_res,_e],[_x,_res,_e,_vef],[_x,_res,_e,_vef,_sf,_se,_vf,_1,_ve],[_x,_res,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_res,_e,_vef,_sf,_se,_vf,_1,_other],[_x,_res,_e,_vef,_sf,_se,_vf,_ve],[_x,_res,_e,_vef,_sf,_se,_vf,_ve,_other],[_x,_res,_e,_vef,_sf,_se,_vf,_other],[_x,_res,_e,_vef,_sf,_se,_1,_ve],[_x,_res,_e,_vef,_sf,_se,_1,_ve,_other],[_x,_res,_e,_vef,_sf,_se,_1,_other],[_x,_res,_e,_vef,_sf,_vf],[_x,_res,_e,_vef,_sf,_vf,_1],[_x,_res,_e,_vef,_sf,_1],[_x,_res,_e,_vef,_se,_ve],[_x,_res,_e,_vef,_se,_ve,_other],[_x,_res,_e,_vef,_se,_other],[_x,_res,_e,_sf,_se,_vf,_1,_ve],[_x,_res,_e,_sf,_se,_vf,_1,_ve,_other],[_x,_res,_e,_sf,_se,_vf,_1,_other],[_x,_res,_e,_sf,_se,_vf,_ve],[_x,_res,_e,_sf,_se,_vf,_ve,_other],[_x,_res,_e,_sf,_se,_vf,_other],[_x,_res,_e,_sf,_se,_1,_ve],[_x,_res,_e,_sf,_se,_1,_ve,_other],[_x,_res,_e,_sf,_se,_1,_other],[_x,_res,_e,_sf,_vf],[_x,_res,_e,_sf,_vf,_1],[_x,_res,_e,_sf,_1],[_x,_res,_e,_se,_ve],[_x,_res,_e,_se,_ve,_other],[_x,_res,_e,_se,_other],[_x,_f],[_x,_f,_e],[_x,_f,_e,_vef],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_ve],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_1,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_ve],[_x,_f,_e,_vef,_sf,_se,_vf,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_vf,_other],[_x,_f,_e,_vef,_sf,_se,_1,_ve],[_x,_f,_e,_vef,_sf,_se,_1,_ve,_other],[_x,_f,_e,_vef,_sf,_se,_1,_other],[_x,_f,_e,_vef,_sf,_vf],[_x,_f,_e,_vef,_sf,_vf,_1],[_x,_f,_e,_vef,_sf,_1],[_x,_f,_e,_vef,_se,_ve],[_x,_f,_e,_vef,_se,_ve,_other],[_x,_f,_e,_vef,_se,_other],[_x,_f,_e,_sf,_se,_vf,_1,_ve],[_x,_f,_e,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_e,_sf,_se,_vf,_1,_other],[_x,_f,_e,_sf,_se,_vf,_ve],[_x,_f,_e,_sf,_se,_vf,_ve,_other],[_x,_f,_e,_sf,_se,_vf,_other],[_x,_f,_e,_sf,_se,_1,_ve],[_x,_f,_e,_sf,_se,_1,_ve,_other],[_x,_f,_e,_sf,_se,_1,_other],[_x,_f,_e,_sf,_vf],[_x,_f,_e,_sf,_vf,_1],[_x,_f,_e,_sf,_1],[_x,_f,_e,_se,_ve],[_x,_f,_e,_se,_ve,_other],[_x,_f,_e,_se,_other],[_x,_f,_vef],[_x,_f,_vef,_sf,_se,_vf,_1,_ve],[_x,_f,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_vef,_sf,_se,_vf,_1,_other],[_x,_f,_vef,_sf,_se,_vf,_ve],[_x,_f,_vef,_sf,_se,_vf,_ve,_other],[_x,_f,_vef,_sf,_se,_vf,_other],[_x,_f,_vef,_sf,_se,_1,_ve],[_x,_f,_vef,_sf,_se,_1,_ve,_other],[_x,_f,_vef,_sf,_se,_1,_other],[_x,_f,_vef,_sf,_vf],[_x,_f,_vef,_sf,_vf,_1],[_x,_f,_vef,_sf,_1],[_x,_f,_vef,_se,_ve],[_x,_f,_vef,_se,_ve,_other],[_x,_f,_vef,_se,_other],[_x,_f,_sf,_se,_vf,_1,_ve],[_x,_f,_sf,_se,_vf,_1,_ve,_other],[_x,_f,_sf,_se,_vf,_1,_other],[_x,_f,_sf,_se,_vf,_ve],[_x,_f,_sf,_se,_vf,_ve,_other],[_x,_f,_sf,_se,_vf,_other],[_x,_f,_sf,_se,_1,_ve],[_x,_f,_sf,_se,_1,_ve,_other],[_x,_f,_sf,_se,_1,_other],[_x,_f,_sf,_vf],[_x,_f,_sf,_vf,_1],[_x,_f,_sf,_1],[_x,_f,_se,_ve],[_x,_f,_se,_ve,_other],[_x,_f,_se,_other],[_x,_e],[_x,_e,_vef],[_x,_e,_vef,_sf,_se,_vf,_1,_ve],[_x,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_e,_vef,_sf,_se,_vf,_1,_other],[_x,_e,_vef,_sf,_se,_vf,_ve],[_x,_e,_vef,_sf,_se,_vf,_ve,_other],[_x,_e,_vef,_sf,_se,_vf,_other],[_x,_e,_vef,_sf,_se,_1,_ve],[_x,_e,_vef,_sf,_se,_1,_ve,_other],[_x,_e,_vef,_sf,_se,_1,_other],[_x,_e,_vef,_sf,_vf],[_x,_e,_vef,_sf,_vf,_1],[_x,_e,_vef,_sf,_1],[_x,_e,_vef,_se,_ve],[_x,_e,_vef,_se,_ve,_other],[_x,_e,_vef,_se,_other],[_x,_e,_sf,_se,_vf,_1,_ve],[_x,_e,_sf,_se,_vf,_1,_ve,_other],[_x,_e,_sf,_se,_vf,_1,_other],[_x,_e,_sf,_se,_vf,_ve],[_x,_e,_sf,_se,_vf,_ve,_other],[_x,_e,_sf,_se,_vf,_other],[_x,_e,_sf,_se,_1,_ve],[_x,_e,_sf,_se,_1,_ve,_other],[_x,_e,_sf,_se,_1,_other],[_x,_e,_sf,_vf],[_x,_e,_sf,_vf,_1],[_x,_e,_sf,_1],[_x,_e,_se,_ve],[_x,_e,_se,_ve,_other],[_x,_e,_se,_other],[_x,_vef],[_x,_vef,_sf,_se,_vf,_1,_ve],[_x,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_vef,_sf,_se,_vf,_1,_other],[_x,_vef,_sf,_se,_vf,_ve],[_x,_vef,_sf,_se,_vf,_ve,_other],[_x,_vef,_sf,_se,_vf,_other],[_x,_vef,_sf,_se,_1,_ve],[_x,_vef,_sf,_se,_1,_ve,_other],[_x,_vef,_sf,_se,_1,_other],[_x,_vef,_sf,_vf],[_x,_vef,_sf,_vf,_1],[_x,_vef,_sf,_1],[_x,_vef,_se,_ve],[_x,_vef,_se,_ve,_other],[_x,_vef,_se,_other],[_x,_sf,_se,_vf,_1,_ve],[_x,_sf,_se,_vf,_1,_ve,_other],[_x,_sf,_se,_vf,_1,_other],[_x,_sf,_se,_vf,_ve],[_x,_sf,_se,_vf,_ve,_other],[_x,_sf,_se,_vf,_other],[_x,_sf,_se,_1,_ve],[_x,_sf,_se,_1,_ve,_other],[_x,_sf,_se,_1,_other],[_x,_sf,_vf],[_x,_sf,_vf,_1],[_x,_sf,_1],[_x,_se,_ve],[_x,_se,_ve,_other],[_x,_se,_other],[_res,_f],[_res,_f,_e],[_res,_f,_e,_vef],[_res,_f,_e,_vef,_sf,_se,_vf,_1,_ve],[_res,_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_res,_f,_e,_vef,_sf,_se,_vf,_1,_other],[_res,_f,_e,_vef,_sf,_se,_vf,_ve],[_res,_f,_e,_vef,_sf,_se,_vf,_ve,_other],[_res,_f,_e,_vef,_sf,_se,_vf,_other],[_res,_f,_e,_vef,_sf,_se,_1,_ve],[_res,_f,_e,_vef,_sf,_se,_1,_ve,_other],[_res,_f,_e,_vef,_sf,_se,_1,_other],[_res,_f,_e,_vef,_sf,_vf],[_res,_f,_e,_vef,_sf,_vf,_1],[_res,_f,_e,_vef,_sf,_1],[_res,_f,_e,_vef,_se,_ve],[_res,_f,_e,_vef,_se,_ve,_other],[_res,_f,_e,_vef,_se,_other],[_res,_f,_e,_sf,_se,_vf,_1,_ve],[_res,_f,_e,_sf,_se,_vf,_1,_ve,_other],[_res,_f,_e,_sf,_se,_vf,_1,_other],[_res,_f,_e,_sf,_se,_vf,_ve],[_res,_f,_e,_sf,_se,_vf,_ve,_other],[_res,_f,_e,_sf,_se,_vf,_other],[_res,_f,_e,_sf,_se,_1,_ve],[_res,_f,_e,_sf,_se,_1,_ve,_other],[_res,_f,_e,_sf,_se,_1,_other],[_res,_f,_e,_sf,_vf],[_res,_f,_e,_sf,_vf,_1],[_res,_f,_e,_sf,_1],[_res,_f,_e,_se,_ve],[_res,_f,_e,_se,_ve,_other],[_res,_f,_e,_se,_other],[_res,_f,_vef],[_res,_f,_vef,_sf,_se,_vf,_1,_ve],[_res,_f,_vef,_sf,_se,_vf,_1,_ve,_other],[_res,_f,_vef,_sf,_se,_vf,_1,_other],[_res,_f,_vef,_sf,_se,_vf,_ve],[_res,_f,_vef,_sf,_se,_vf,_ve,_other],[_res,_f,_vef,_sf,_se,_vf,_other],[_res,_f,_vef,_sf,_se,_1,_ve],[_res,_f,_vef,_sf,_se,_1,_ve,_other],[_res,_f,_vef,_sf,_se,_1,_other],[_res,_f,_vef,_sf,_vf],[_res,_f,_vef,_sf,_vf,_1],[_res,_f,_vef,_sf,_1],[_res,_f,_vef,_se,_ve],[_res,_f,_vef,_se,_ve,_other],[_res,_f,_vef,_se,_other],[_res,_f,_sf,_se,_vf,_1,_ve],[_res,_f,_sf,_se,_vf,_1,_ve,_other],[_res,_f,_sf,_se,_vf,_1,_other],[_res,_f,_sf,_se,_vf,_ve],[_res,_f,_sf,_se,_vf,_ve,_other],[_res,_f,_sf,_se,_vf,_other],[_res,_f,_sf,_se,_1,_ve],[_res,_f,_sf,_se,_1,_ve,_other],[_res,_f,_sf,_se,_1,_other],[_res,_f,_sf,_vf],[_res,_f,_sf,_vf,_1],[_res,_f,_sf,_1],[_res,_f,_se,_ve],[_res,_f,_se,_ve,_other],[_res,_f,_se,_other],[_res,_e],[_res,_e,_vef],[_res,_e,_vef,_sf,_se,_vf,_1,_ve],[_res,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_res,_e,_vef,_sf,_se,_vf,_1,_other],[_res,_e,_vef,_sf,_se,_vf,_ve],[_res,_e,_vef,_sf,_se,_vf,_ve,_other],[_res,_e,_vef,_sf,_se,_vf,_other],[_res,_e,_vef,_sf,_se,_1,_ve],[_res,_e,_vef,_sf,_se,_1,_ve,_other],[_res,_e,_vef,_sf,_se,_1,_other],[_res,_e,_vef,_sf,_vf],[_res,_e,_vef,_sf,_vf,_1],[_res,_e,_vef,_sf,_1],[_res,_e,_vef,_se,_ve],[_res,_e,_vef,_se,_ve,_other],[_res,_e,_vef,_se,_other],[_res,_e,_sf,_se,_vf,_1,_ve],[_res,_e,_sf,_se,_vf,_1,_ve,_other],[_res,_e,_sf,_se,_vf,_1,_other],[_res,_e,_sf,_se,_vf,_ve],[_res,_e,_sf,_se,_vf,_ve,_other],[_res,_e,_sf,_se,_vf,_other],[_res,_e,_sf,_se,_1,_ve],[_res,_e,_sf,_se,_1,_ve,_other],[_res,_e,_sf,_se,_1,_other],[_res,_e,_sf,_vf],[_res,_e,_sf,_vf,_1],[_res,_e,_sf,_1],[_res,_e,_se,_ve],[_res,_e,_se,_ve,_other],[_res,_e,_se,_other],[_vef],[_vef,_sf,_se,_vf,_1,_ve],[_vef,_sf,_se,_vf,_1,_ve,_other],[_vef,_sf,_se,_vf,_1,_other],[_vef,_sf,_se,_vf,_ve],[_vef,_sf,_se,_vf,_ve,_other],[_vef,_sf,_se,_vf,_other],[_vef,_sf,_se,_1,_ve],[_vef,_sf,_se,_1,_ve,_other],[_vef,_sf,_se,_1,_other],[_vef,_sf,_vf],[_vef,_sf,_vf,_1],[_vef,_sf,_1],[_vef,_se,_ve],[_vef,_se,_ve,_other],[_vef,_se,_other],[_sf,_se,_vf,_1,_ve],[_sf,_se,_vf,_1,_ve,_other],[_sf,_se,_vf,_1,_other],[_sf,_se,_vf,_ve],[_sf,_se,_vf,_ve,_other],[_sf,_se,_vf,_other],[_sf,_se,_1,_ve],[_sf,_se,_1,_ve,_other],[_sf,_se,_1,_other],[_sf,_vf],[_sf,_vf,_1],[_sf,_1],[_se,_ve],[_se,_ve,_other],[_se,_other]]);mshare([[_x],[_x,_res,_f,_e,_vef],[_x,_res,_f,_e,_vef,_sf,_se,_vf,_1,_ve],[_x,_res,_f,_e,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_res,_f,_e,_vef,_sf,_se,_vf,_1,_other],[_x,_res,_f,_e,_vef,_sf,_se,_vf,_ve],[_x,_res,_f,_e,_vef,_sf,_se,_vf,_ve,_other],[_x,_res,_f,_e,_vef,_sf,_se,_vf,_other],[_x,_res,_f,_e,_vef,_sf,_se,_1,_ve],[_x,_res,_f,_e,_vef,_sf,_se,_1,_ve,_other],[_x,_res,_f,_e,_vef,_sf,_se,_1,_other],[_x,_res,_f,_e,_vef,_sf,_vf],[_x,_res,_f,_e,_vef,_sf,_vf,_1],[_x,_res,_f,_e,_vef,_sf,_1],[_x,_res,_f,_e,_vef,_se,_ve],[_x,_res,_f,_e,_vef,_se,_ve,_other],[_x,_res,_f,_e,_vef,_se,_other],[_x,_res,_f,_e,_sf,_se,_vf,_1,_ve],[_x,_res,_f,_e,_sf,_se,_vf,_1,_ve,_other],[_x,_res,_f,_e,_sf,_se,_vf,_1,_other],[_x,_res,_f,_e,_sf,_se,_vf,_ve],[_x,_res,_f,_e,_sf,_se,_vf,_ve,_other],[_x,_res,_f,_e,_sf,_se,_vf,_other],[_x,_res,_f,_e,_sf,_se,_1,_ve],[_x,_res,_f,_e,_sf,_se,_1,_ve,_other],[_x,_res,_f,_e,_sf,_se,_1,_other],[_x,_res,_f,_e,_sf,_vf],[_x,_res,_f,_e,_sf,_vf,_1],[_x,_res,_f,_e,_sf,_1],[_x,_res,_f,_e,_se,_ve],[_x,_res,_f,_e,_se,_ve,_other],[_x,_res,_f,_e,_se,_other],[_x,_res,_f,_vef],[_x,_res,_f,_vef,_sf,_se,_vf,_1,_ve],[_x,_res,_f,_vef,_sf,_se,_vf,_1,_ve,_other],[_x,_res,_f,_vef,_sf,_se,_vf,_1,_other],[_x,_res,_f,_vef,_sf,_se,_vf,_ve