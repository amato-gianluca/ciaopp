:- module(ciaopp_ref_man,[],[assertions]).

:- doc(filetype, application).

:- doc(title,"The CiaoPP Program Processor").
:- doc(subtitle, "A Program Analysis, Verification, Debugging, and Optimization Tool").
:- doc(author, "The Ciao Development Team").

:- doc(logo, 'ciao-logo').

:- doc(subtitle_extra,"REFERENCE MANUAL").
:- doc(subtitle_extra,"@bf{The Ciao Documentation Series}").
:- doc(subtitle_extra,"@href{https://ciao-lang.org/}").
:- doc(subtitle_extra,"@em{Generated/Printed on:} @today{}").
:- doc(subtitle_extra,"Technical Report CLIP 1/06 (first version 8/95).").

% TODO: Replace 'credits' by 'editor'? (JFMC)
:- doc(credits, "@bf{Edited by:}").
:- doc(credits, "Francisco Bueno").
:- doc(credits, "Manuel Hermenegildo").
:- doc(credits, "Pedro L@'{o}pez").
:- doc(credits, "Jos@'{e} Francisco Morales").
:- doc(credits, "Germ@'{a}n Puebla").

:- include(core_docsrc(common/'ClipAddress')).

:- doc(copyright, "Copyright @copyright{} 1996-2011 Francisco Bueno,
Manuel Hermenegildo, Pedro L@'{o}pez, Jos@'{e} Francisco Morales,
and Germ@'{a}n Puebla.

@include{FreeDocLicense.lpdoc}
").

:- doc(usage,"The @apl{ciaopp} executable starts a shell at which
    prompt you can issue any of the commands described below and 
    in the next chapter as exports.").

:- doc(summary, "@include{CiaoPPRefSummary.lpdoc}

@p

@bf{Note:} This is the CiaoPP @bf{reference} manual. To begin using
CiaoPP, we suggest you start by following one or more of the companion
CiaoPP @bf{tutorials} available in the Ciao system documentation.
").

:- doc(module, "

CiaoPP is the abstract interpretation-based preprocessor of the Ciao
multi-paradigm program development environment. 
CiaoPP can perform a number of program debugging,
analysis, and source-to-source transformation tasks on (Ciao) Prolog
programs. These tasks include:

@begin{itemize}

@item @concept{Inference of properties} of the predicates and literals of the
program, including @concept{types}, @concept{modes} (@ref{groundness and sharing}),
@ref{term structure}, and other @concept{variable instantiation} properties,
@concept{non-failure}, @concept{determinacy}, bounds on @concept{computational
cost} (e.g., @ref{number of resolution steps of the computation}), bounds on
@concept{size of terms} in the program, etc (see @ref{Available abstract domains}).

@item Certain kinds of @concept{static debugging} and verification,
finding errors before running the program. This includes checking how
programs call system library predicates and also @concept{checking the
assertions} present in the program or in other modules used by the
program. Such assertions represent essentially partial
@concept{specifications} of the program.

@item Several kinds of source to source @concept{program
transformations} such as @concept{program specialization}, slicing,
@concept{partial evaluation} of a program,
@concept{program parallelization} (taking @concept{granularity
control} into account), inclusion of @concept{run-time tests} for assertions 
which cannot be checked completely at compile-time, etc.

@item The abstract model of the program inferred by the analyzers can
be used to certify that untrusted mobile code is safe w.r.t. a given
policy (this implements the @em{abstraction-carrying code} approach to
mobile code safety).

@end{itemize}

The information generated by analysis, program properties to be
verified, descriptions of the system libraries, directives provided to
guide analysis, etc.  are all written in the same @concept{assertion
language}, which is in turn also processed by the Ciao system
documentation generator, @apl{lpdoc}.

CiaoPP is distributed under the @concept{GNU general public
license}.

@section{How to use this manual}

This is a @em{reference manual}. I also includes a part on the CiaoPP
internals. You can use this manual to:

@begin{itemize}

@item Look up descriptions for the commands, flags, options, domains,
      transformations, etc. of CiaoPP.  In the html versions of the
      manual you can use the search facility to this end.  In other
      versions the Predicate/Method Definition Index can help you in
      locating commands; the Regular Type Definition Index can help in
      locating the definitions of the types associated to the
      arguments of commands; the Concept Definition Index may help in
      locating the part of the manual where a particular feature of
      CiaoPP is described; and the Global Index includes all of the
      above plus references to pages where the command, type, or
      concept is used (not necessarily defined).

@item Learn about how to extend CiaoPP, for example by defining new
      analysis domains. 

@item Learn about CiaoPP internals.
@end{itemize}

Since this is a @bf{reference} manual, to begin using CiaoPP, we
suggest you start by following one or more of the companion CiaoPP
@bf{tutorials} that are available in the Ciao system documentation.

@comment{MH: I think this was out of place:}
@comment{This chapter gives a brief overview of CiaoPP and its capabilities.}

This manual assumes in some places some familiarity with the
techniques that implement the different functionalities, such as
abstract interpretation, partial evaluation, etc. However, references
are included to technical papers that explain in detail such
techniques.

@section{Note}

Since we are often merging new functionality into the CiaoPP
distribution from more experimental versions, you may find sometimes
that some documented functionality in this manual is not available or
not working properly. We will be grateful if you report any missing
functionality or bugs you find.

").

%% An overview of the functionalities available is
%% given in @cite{ciaopp-tutorial} in the form of a tutorial on CiaoPP.

%% Old note
%%     We are in the process of merging all CiaoPP functionality into
%%     the 1.2 version. In the meantime, the current distribution is
%%     marked as alpha and you may find that some functionality
%%     documented in this manual is not available or not working
%%     properly.  Please bear with us in the meantime. Sorry for any
%%     inconvenience.


%% TODO: duplicated in advanced tutorial
%
% @section{Getting started}
% 
% A CiaoPP session consists in the preprocessing of a file. The session
% is governed by a menu, where you can choose the kind of preprocessing
% you want to be done to your file among several analyses and program
% transformations available.  Clicking on the icon
% @image{button-options} in the buffer containing the file to be
% preprocessed displays the menu, which will look (depending on the
% options available in the current CiaoPP version) something like the
% ``Preprocessor Option Browser'' shown in the following figure:
% 
%  @image{naive-menu}
% 
% Except for the first and last lines, which refer to loading or saving
% a menu configuration (a predetermined set of selected values for the
% different menu options), each line corresponds to an option you can
% select, each having several possible values. You can select either
% analysis (@tt{analyze}) or assertion checking (@tt{check_assertions})
% or certificate checking (@tt{check_certificate}) or program
% optimization (@tt{optimize}), and you can later combine the four kinds
% of preprocessing.  The relevant options for the @tt{action group}
% selected are then shown, together with the relevant flags.  A
% description of the values for each option will be given as it is used
% in the corresponding section of this manual.
% 
% CiaoPP can help you to analyze your program, in order to infer 
% properties of the predicates and literals in your program (which might
% be useful in the subsequent steps during the same session). You can use
% Cost Analysis to infer both lower and upper bounds on the computational 
% time cost and sizes of terms of procedures in a program.
% Mode Analyses obtain at compile-time accurate variable groundness and sharing
% information and other @concept{variable instantiation}
% properties. Type Analysis infers regular types. 
% Regular types are explained in detail in @ref{Declaring regular types}.
% Non-failure and Determinacy Analyses detect procedures and goals that can 
% be guaranteed to not fail and/or to be deterministic.
% 
% CiaoPP also can help to optimize your program (by means
% of source-to-source @index{program transformations}), using
% program specialization, partial evaluation, program parallelization and
% granularity control, and other program transformations.
% Specialization can help to simplify your program w.r.t. the
% analysis information (eliminating dead code, predicates that are
% guaranteed to either succeed or fail, etc.), specialize it and then
% simplify it, or just specialize it, i.e., to unfold all versions of the
% predicates in your program. CiaoPP can also perform automatic parallelization 
% of your source program during precompilation using several @em{annotation}
% algorithms, and granularity control on parallel programs, transforming
% the program in order to perform run--time granularity control, i.e., deciding 
% parallel or sequential execution of goals depending on the estimated amount of
% work under them (estimated by cost analysis).
% 
% CiaoPP also helps in @index{debugging} your programs. It makes possible
% to perform @index{static debugging}, i.e., finding errors at compile-time, 
% before running the program, and also dynamic debugging, in the sense of 
% including @index{run-time tests} that will perform the checking for errors
% at run-time.
%  Static debugging is performed by @index{assertion checking}.
% This includes checking the ways in which programs call the system
% library predicates and also checking the assertions present in
% the program or in other modules used by the program. Such assertions
% essentially represent partial @index{specifications} of the program.
% For dynamic checking, CiaoPP will include run-time tests for the parts of
% assertions which cannot be checked completely at compile-time.
% 
% @ref{Using assertions for preprocessing programs}, gives
% an overview on the use of the assertion language in CiaoPP.
% In that chapter and the following ones, several existing properties that
% can be used in assertions are described. Programmers can also define
% their own properties (see the abovementioned chapters).

% ---------------------------------------------------------------------------

:- include(ciaopp_docsrc('CHANGELOG')).

