:- module(measure_program_size, [run/0]).

:- use_package(assertions).

:- use_module(library(lists)).
:- use_module(library(numlists)).
:- use_module(library(sets)).
:- use_module(library(system)).
:- use_module(library(hiordlib)).
:- use_module(library(terms_vars)).

:- op(700,xfx,less_than).
:- op(950,xfy,#).
:- op(850,xfy,&).
:- op(500,fx,+).
:- op(500,fx,-).

programs([
    boyer, browse, chat_parser, crypt, derive, divide10, eval, fast_mu, fib, flatten, log10, meta_qsort,
    moded_path, mu, nand, nreverse, ops8, perfect, pingpong, poly_10, prover, qsort, queens_8, query, reducer,
    sendmore, serialise, sieve, simple_analyzer, tak, times10, unify, zebra
]).

run :-
    format('program,size,predicates,clauses,totvar,maxvar~n', []),
    programs(Programs),
    analyze_files('src/', Programs).


analyze_files(_, []).
analyze_files(Directory, [Program|Rest]) :-
    atom_concat(Directory, Program, FilePath),
    atom_concat(FilePath, '.pl', File),
    format('~q', Program),
    analyze_file(File),
    format('~n', []),
    analyze_files(Directory, Rest).

% Entry point to count mshare arguments in a file
analyze_file(File) :-
    file_property(File, size(Size)),
    format(',~q', Size),
    open(File, read, Stream),
    read_clauses(Stream, Clauses),
    analyze_clauses(Clauses),
    close(Stream).

analyze_clauses(Clauses) :-
    count_predicates(Clauses, SizePredicates),
    format(',~q', SizePredicates),
    count_clauses(Clauses, SizeClauses),
    format(',~q', SizeClauses),
    count_variables(Clauses, TotVars, MaxVars),
    format(',~q,~q', [TotVars, MaxVars]).

count_predicates(Clauses, Size) :-
    collect_predicates(Clauses, Predicates),
    length(Predicates, Size).

collect_predicates([(Head :- _Body)| Rest], Preds) :-
    !,
    collect_predicates(Rest, Preds0),
    functor(Head, Pred, Arg),
    insert(Preds0, (Pred, Arg), Preds).
collect_predicates([(:- _Body)| Rest], Preds) :-
    !,
    collect_predicates(Rest, Preds).

collect_predicates([Head | Rest], Preds) :-
    !,
    collect_predicates(Rest, Preds0),
    functor(Head, Pred, Arg),
    insert(Preds0, (Pred, Arg), Preds).
collect_predicates([], []).

count_clauses(Clauses, Size) :-
    maplist(count_clause, Clauses, Counts),
    sum_list(Counts, Size).

count_clause((_Head :- _Rest), 1) :- !.
count_clause((:- _Body), 0) :- !.
count_clause(_, 1).

count_variables(Clauses, SizeTot, SizeMax) :-
    maplist(count_variables_in_clause, Clauses, Counts),
    sum_list(Counts, SizeTot),
    max_list(Counts, SizeMax).

max_list([X], X) :- !.
max_list([X|Y], Z) :-
    max_list(Y, Z0),
    (X > Z0 -> Z = X ; Z = Z0).

count_variables_in_clause((:- _Body), 0) :- !.
count_variables_in_clause(Clause, V) :-
    varset(Clause, Vs),
    length(Vs, V).

read_clauses(Stream, [Clause|Clauses]) :-
    read(Stream, Clause),
    Clause \== end_of_file,
    !,
    read_clauses(Stream, Clauses).
read_clauses(_, []).
