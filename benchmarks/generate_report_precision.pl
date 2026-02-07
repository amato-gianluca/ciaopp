:- module(generate_report_precision, [run/0, analyze/1]).

:- use_package(assertions).

:- doc(title, "Extract precision reports from benchmarks results").
:- doc(module,"
This module compares the results of the benchmarks on several abstract domains
with different options. It produces a files for the properties:
- mshare: set sharing groups
- linear: variable linearity
- ground: variable groundness.

For the whole analysis, execute:
:- run.

For the analysis of a specific property, execute:
:- analyze(mshare).
:- analyze(linear).
:- analyze(groound).

Copyright 2024-2026 Francesca Scozzari <francesca.scozzari@unich.i> and
                    Gianluca Amato <gianluca.amato@unich.it>
").

:- use_module(library(lists)).
:- use_module(library(numlists)).
:- use_module(library(system)).
:- use_module(library(sets)).
:- use_module(library(terms_vars)).

:- op(700,xfx,less_than).
:- op(950,xfy,#).
:- op(850,xfy,&).
:- op(500,fx,+).
:- op(500,fx,-).

run :-
    analyze1(mshare, true),
    analyze1(linear, false),
    analyze1(ground, false).

% the following declares the existence of the predicate even in absence of
% clauses

:- multifile option/1.

% if avoid_counting_true_pred is defined, the analysis will not consider the
% properties inside ":-true pred"

option(avoid_counting_true_pred).

analyze(Property) :- analyze1(Property, true).

analyze1(Property, Header) :-
    programs(Programs),
    analyses(Analyses),
    ( Header == true ->
        format('property,program', []),
        print_first_row(Analyses),
        format('~n', [])
    ;
        true
    ),
    analyze_files(Property,'results/', Programs).

programs([
    boyer, browse, chat_parser, crypt, derive, divide10, eval, fast_mu, fib, flatten, log10, meta_qsort,
    moded_path, mu, nand, nreverse, ops8, perfect, pingpong, poly_10, prover, qsort, queens_8, query, reducer,
    sendmore, serialise, sieve, simple_analyzer, tak, times10, unify, zebra
]).

analyses([
    as_shlin2_opt,as_shlin2_opt_mgu,as_shlin2_noopt,as_shlin2_noopt_mgu,
    as_shlin_opt_opt, as_shlin_opt, as_shlin_noindcheck, as_shlin_noopt, as_shlin_opt_mgu,
    as_shlin_noindcheck_mgu, as_shlin_noopt_mgu,
    as_sharing_opt, as_sharing_noopt, as_sharing_opt_mgu, as_sharing_noopt_mgu,
    share, shfrlin
]).

print_first_row([]).
print_first_row([A|Rest]) :-
    format(',~q', A),
    print_first_row(Rest).

analyze_files(_,_, []).
analyze_files(Property, Directory, [Program|Rest]) :-
    atom_concat(Directory, Program, FilePath),
    analyses(Analyses),
    format('~q,~q', [Property,Program]),
    analyze_options(Property, Analyses, Program, FilePath),
    format('~n', []),
    analyze_files(Property, Directory, Rest).

analyze_options(_,[],_,_).
analyze_options(Property, [Analysis|Rest], Program, FilePath) :-
    atom_concat(FilePath,/,FilePathSlash),
    atom_concat(FilePathSlash,Analysis,FilePathAnalysis),
    atom_concat(FilePathAnalysis,'.pl',File),
    (   file_exists(File)
    ->  count_properties_in_file(File, Property, TotalCount),
        format(',~q', TotalCount)
    ;   format(',', [])     % File does not exist
    ),
    analyze_options(Property, Rest, Program, FilePath).

% Entry point to count properties in a file
count_properties_in_file(File, Property, TotalCount) :-
    Property=mshare,!,
    read_file(File, Clauses),
    findall(Count, (
        member(Clause, Clauses),
        analyze_clause(Clause, Property, MshareTerms),
        count_mshare_args(MshareTerms, Count)
    ), Counts),
    sum_list(Counts, TotalCount).

count_properties_in_file(File, Property, TotalCount) :-
    Property=linear,!,
    read_file(File, Clauses),
    findall(Count, (
        member(Clause, Clauses),
        analyze_clause(Clause, Property, LinearTerms),
        count_linear_args(LinearTerms, Count)
    ), Counts),
    sum_list(Counts, TotalCount).

count_properties_in_file(File, Property, TotalCount) :-
    Property=ground,!,
    read_file(File, Clauses),
    findall(Count, (
        member(Clause, Clauses),
        analyze_clause(Clause, Property, MshareTerms),
        count_linear_args(MshareTerms, Count)
    ), Counts),
    sum_list(Counts, TotalCount).

% Read the file and get all clauses
read_file(File, Clauses) :-
    open(File, read, Stream),
    read_clauses(Stream, Clauses),
    close(Stream).

read_clauses(Stream, [Clause|Clauses]) :-
    read(Stream, Clause),
    Clause \== end_of_file,
    !,
    read_clauses(Stream, Clauses).
read_clauses(end_of_file, []) :- !.
read_clauses(_, []) :- !.

analyze_clause((:- entry _Head), _, []) :- !.

analyze_clause((:- true pred _Head : _Pre => _Post), _Property, []) :-
    option(avoid_counting_true_pred), !.

analyze_clause((:- true pred Head : Pre => Post), Property, Terms) :- !,
    varset(Head, Vars),
    extract_property(Pre, Vars, Property, PreTerms),
    extract_property(Post, Vars, Property, PostTerms),
    append(PreTerms, PostTerms, Terms).

analyze_clause((:- _Head),_, []) :-  !.

analyze_clause((Head :- Body), Property, Terms) :- !,
    varset((Head :- Body), Vars),
    analyze_body(Body, Vars, Property, Terms).

analyze_body(true(X), Vars, Property, Terms) :- !,
    extract_property(X, Vars, Property, Terms).

analyze_body((A,B), Vars, Property, Terms) :- !,
    analyze_body(A, Vars, Property, TermsA),
    analyze_body(B, Vars, Property, TermsB),
    append(TermsA, TermsB, Terms).

analyze_body(_, _Vars, _Property, []).

extract_property((A;B), Vars, mshare, Terms) :- !,
    extract_property(A, Vars, mshare, TermsA),
    extract_property(B, Vars, mshare, TermsB),
    ord_intersection(TermsA, TermsB, Terms).

extract_property((A;B), Vars, Property, Terms) :- !,
    extract_property(A, Vars, Property, TermsA),
    extract_property(B, Vars, Property, TermsB),
    merge(TermsA, TermsB, Terms).

extract_property((A,B), Vars, Property, Terms) :- !,
    extract_property(A, Vars, Property, TermsA),
    extract_property(B, Vars, Property, TermsB),
    append(TermsA, TermsB, Terms).

extract_property(linear(V), _Vars, linear, [V]) :- !.
extract_property(ground(L), _Vars, linear, L) :- !.
extract_property(fails(_), Vars, linear, Vars) :- !.
extract_property(_, _Vars, linear, []) :- !.

extract_property(ground(L), _Vars, ground, L) :- !.
extract_property(fails(_), Vars, ground, Vars) :- !.
extract_property(_, _Vars, ground, []) :- !.

extract_property(X, _Vars, Property, Terms) :-
    X =.. [Property,Terms],
    !.
extract_property(_, _Vars, _, []) :- !.

count_mshare_args([[]|T], C) :- !, count_mshare_args(T,C).
count_mshare_args([_|T], C1) :- !, count_mshare_args(T,C), C1 is C + 1.
count_mshare_args(_, 0).

count_linear_args(L, C) :- length(L, C).
