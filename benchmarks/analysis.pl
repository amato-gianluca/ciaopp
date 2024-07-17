#!/usr/bin/env ciao-shell

:- use_module(library(format)).
:- use_module(ciaopp(ciaopp)).
:- use_module(library(profilercc/profiler_utils)).
:- use_module(library(timeout), [call_with_time_limit/2]).

file('boyer.pl').
file('browse.pl').
file('chat_parser.pl').
file('crypt.pl').
file('derive.pl').
file('divide10.pl').
file('eval.pl').
file('fast_mu.pl').
file('fib.pl').
file('flatten.pl').
file('log10.pl').
file('meta_qsort.pl').
file('moded_path.pl').
file('mu.pl').
file('nand.pl').
file('nreverse.pl').
file('ops8.pl').
file('perfect.pl').
file('pingpong.pl').
file('poly_10.pl').
file('prover.pl').
file('qsort.pl').
file('queens_8.pl').
file('query.pl').
file('reducer.pl').
file('sendmore.pl').
file('serialise.pl').
file('sieve.pl').
% crashes even with timeout active
%file('simple_analyzer.pl').
file('tak.pl').
file('times10.pl').
file('unify.pl').
file('zebra.pl').

global_option(types, none).
global_option(collapse_ai_vers, off).
global_option(pp_info, on).
global_option(shlin2_full_output, on).

set_global_options :-
    global_option(Option, Value),
    set_pp_flag(Option, Value),
    fail.
set_global_options :- !.

analyze_all_files :-
    file(File),
    module(File),
    catch(
        call_with_time_limit(10000, profile(analyze(as_sharing))),
        _,
        format('Timeout for ~w~n', [File])
    ),
    fail.
analyze_all_files :- !.

main(_) :-
    set_global_options,
    set_pp_flag(modes,as_sharing),
    set_pp_flag(mgu_sh_optimize,optimal),
    analyze_all_files,
    profile_dump.
