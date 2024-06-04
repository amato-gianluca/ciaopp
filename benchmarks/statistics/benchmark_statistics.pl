:- module(benchmark_statistics, [run/0, analyze/1]).

%:- doc(title, "Sharing * Lin abstract domain").
%:- doc(module,"
% "This module compares the results of the benchmarks on several abstract domains
% with different options. It produces 3 csv files for the properties:
% - mshare: set sharing groups
% - linear: variable linearity
% - ground: variable groundness.

% For the whole analysis, execute:
% :- run.
%
% For the analysis of a specific property, execute:
% :- analyze(mshare).
% :- analyze(linear).
% :- analyze(groound).

% Copyright 2024 Francesca Scozzari <francesca.scozzari@unich.i> e
%                Gianluca Amato <gianluca.amato@unich.it>
% ").

:- use_module(library(lists)).
:- use_module(engine(stream_basic)).
:- use_module(library(system), [file_exists/1]).
:- use_module(library(sets)).

:- use_package(assertions).

:- op(700,xfx,less_than).
:- op(950,xfy,#).
:- op(850,xfy,&).
:- op(500,fx,+).
:- op(500,fx,-).

run :-
    analyze1(mshare, true),
    analyze1(linear, false),
    analyze1(ground, false).

% options
% if avoid_counting_true_pred is defined, the analysis will not consider the properties inside ":-true pred"
option(avoid_counting_true_pred).

% the following predicates should be always present
% (otherwise there is an error of missing predicate definition)
option(_) :- fail.

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
    analyze_files(Property,'benchmarks/save/', Programs).

% problem arises with program reducer
programs([
    boyer, browse, chat_parser, crypt, derive, divide10, eval, fast_mu, fib, flatten, log10, meta_qsort,
    moded_path, mu, nand, nreverse, ops8, perfect, pingpong, poly_10, prover, qsort, queens_8, query,
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

% Entry point to count mshare arguments in a file
count_properties_in_file(File, Property, TotalCount) :-
    Property=mshare,!,
    read_file(File, Clauses),
    findall(Count, (
        member(Clause, Clauses),
        extract_terms(Clause, Property, MshareTerms),
        count_mshare_args(MshareTerms, Count)
    ), Counts),
    sumlist(Counts, TotalCount).

count_properties_in_file(File, Property, TotalCount) :-
    Property=linear,!,
    read_file(File, Clauses),
    findall(Count, (
        member(Clause, Clauses),
        extract_terms(Clause, Property, LinearTerms),
        count_linear_args(LinearTerms, Count)
    ), Counts),
    sumlist(Counts, TotalCount).

count_properties_in_file(File, Property, TotalCount) :-
    Property=ground,!,
    read_file(File, Clauses),
    findall(Count, (
        member(Clause, Clauses),
        extract_terms(Clause, Property, MshareTerms),
        count_linear_args(MshareTerms, Count)
    ), Counts),
    sumlist(Counts, TotalCount).

% Read the file and get all clauses
read_file(File, Clauses) :-
    open(File, read, Stream),
    read_clauses(Stream, Clauses),
    close(Stream).

read_clauses(Stream, [Clause|Clauses]) :-
    read(Stream, Clause),
    Clause \== end_of_file,  % Ensure end of file is handled
    !,
    read_clauses(Stream, Clauses).
read_clauses(end_of_file, []) :- !.
read_clauses(_, []) :- !.

% Extract all terms from a clause
extract_terms(true(X), Property, Terms) :- !,
    extract_property(X, Property, Terms).

extract_terms((:- entry _Head), _, []) :- !.

extract_terms((:- true pred _Head : _Pre => _Post), _Property, []) :-
    option(avoid_counting_true_pred), !.

extract_terms((:- true pred _Head : Pre => Post), Property, Terms) :- !,
    extract_property(Pre, Property, PreTerms),
    extract_property(Post, Property, PostTerms),
    append(PreTerms, PostTerms, Terms).

extract_terms((:- _Head),_, []) :- !.

extract_terms((_Head :- Body), Property, Terms) :- !,
    extract_terms(Body, Property, Terms).

extract_terms((A,B),Property, Terms) :- !,
    extract_terms(A, Property, TermsA),
    extract_terms(B, Property, TermsB),
    append(TermsA, TermsB, Terms).

extract_terms(_, linear, []) :- !.
extract_terms(_, ground, []) :- !.
extract_terms(_, _, [[]]).

extract_property((A;B), mshare, Terms) :- !,
    extract_property(A, mshare, TermsA),
    extract_property(B, mshare, TermsB),
    ord_intersection(TermsA, TermsB, Terms).

extract_property((A;B), Property, Terms) :- !,
    extract_property(A, Property, TermsA),
    extract_property(B, Property, TermsB),
    merge(TermsA, TermsB, Terms).

extract_property((A,B), Property, Terms) :- !,
    extract_property(A, Property, TermsA),
    extract_property(B, Property, TermsB),
    append(TermsA, TermsB, Terms).

extract_property(linear(V), linear, [V]) :- !.
extract_property(_, linear, []) :- !.

extract_property(ground(L), ground, L) :- !.
extract_property(_, ground, []) :- !.

extract_property(X, Property, Terms) :-
    X=..[Property,Terms],
    !.
extract_property(_, _, []) :- !.

count_mshare_args([[]|T], C) :- !, count_mshare_args(T,C).
count_mshare_args([_|T], C1) :- !, count_mshare_args(T,C), C1 is C + 1.
count_mshare_args(_, 0) .

count_linear_args([], 0) :- !.
count_linear_args([_|T], L) :- !,
    count_linear_args(T,L1),
    L is L1 + 1.

% Define sumlist/2 if not available
sumlist([], 0).
sumlist([H|T], Sum) :-
    sumlist(T, Rest),
    Sum is H + Rest.
