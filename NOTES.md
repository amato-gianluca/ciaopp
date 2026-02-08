# Notes on the CiaoPP development

The following are information useful for the development of new abstract domains using the PLAI analyzer and, more in general, about using CiaoPP and the Ciao system.

## Abstract domains development

Every abstract domain should include the `ciaopp(plai/plai_domain)` source file. In turn, this cause the loading of the package `aidomain`. The relation between these component is the following:
  * The `aidomain` package introduces the support for new declarations like `dom_def`,  `dom_top`, `dom_impl`, etc... which make easier to develop an abstract domain. Collectively, these declarations implement a sort of inheritance mechanism which allows to reuse the implementation of an abstract operator in multiple domains.
  * The `plai_domain` include file contains the declarations (with the `dom_op` directive) of all abstract operators and the default implementation (together with the `dom_base` directive) for some of them.
  * The code for a specific abstract domain implements (with the `dom_impl` directive) the other abstract operators, or overrides the default implementation.

We now see more in detail the new declarations implemented in the `aidomain` package.

### The `aidomain` package

From the point of view of CiaoPP, an abstract domain is essentially an atom, that is the domain name. The predicate `aidomain(X)` is true if `X` a valid domain name.

When an analyzer like PLAI wants to execute an abstract operation, calls one of many **interface predicates**, like `amgu/5`, described in the CiaoPP documentation: https://ciao-lang.org/ciao/build/doc/ciaopp.html/domains.html. The first argument of such predicates is invariably the abstract domain the analyzer wants to use.

However, the predicates implemented by the user for a new abstract domain do not include this first argument: the declarations introduced by the `aidomain` package allows the user to write code specific for a single domain, that is later linked to the interface predicates used by CiaoPP.

The code for `aidomain` is the following:
```prolog
:- package(aidomain).

:- discontiguous(aidomain/1).
:- multifile(aidomain/1).

:- load_compilation_module(library(aidomain/aidomain_tr)).
:- add_sentence_trans(aidomain_tr:treat_sent/3, 310).
```

It essentially declares the multifile and discontinuous predicate `aidomain/1` and installs a sentence translator which implements the new declarations from the `aidomain_tr` module.

Let's see these directives in detail. All the directives we are going to describe take an abstract domain as first argument. If a variable is given, that is bound to the default domain provided in the `dom_def` declaration or, in absence of a default domain`, to the name of the current module.

In order to implement these directives, the translator uses many data predicates (https://ciao-lang.org/ciao/build/doc/ciao.html/datafacts_doc.html). All these data predicates takes a module identifier as the last argument.

#### :- dom_def(AbsInt, Props)

Declares that we are going to implement the domain `AbsInt` with properties `Props`. The latter is a list of properties, chosen among:
  * `deriv(BaseDom)`: declares the base domain of `AbsInt`, to be used with the `dom_base_deriv` directive;
  * `default`: sets the current domain as the default value for the dom directives.

The declaration is translated into the fact `aidomain(AbsInt)`, asserting to the rest of CiaoPP that `AbsInt` is a valid abstract domain.

*Implementation notes*: The base domain in recorded in the data predicate `dom_def(AbsInt,BaseDom,M)`, the default domain in `dom_default(AbsInt, M)`. If a base domain is not provided, `dom_def` is asserted anyway with the implicit `basedom` base domain.

#### :- dom_def(AbsInt)

Equivalent to `:- dom_def(AbsInt, [])`.

#### :- dom_op(F/A)

Declares the existence of the abstract operator `F/A`. At the moment it is only used in the `plai_domain` include file.

This directive is translated into the declaration of a discontiguous and multifile predicate named `aidom.F` with arity `A+1`. This is an **intermediate predicate**. The `dom_itf` directive will route to this predicate all the requests to the interface predicates.

*Implementation notes*: The presence of this declaration is recorded in the data predicate `dom_op(F, A, M)`.

#### :- dom_base(F/A)

Declares that the abstract operator `F/A` has a default implementation, named `basedom_F` of arity A+1 (since, the first argument is the abstract domain). At the moment it is only used in the `plai_domain` include file.

The declaration is removed from the compilation, but when the module has been completely read, the `dom_base` declarations are used to generate code which routes the intermediate predicate to the default implementation. The following code is generated for each abstract domain `AbsInt` in the module:
```prolog
aidom.F(AbsInt, V1, ..., VA) :- basedom_F(AbsInt, V1, ..., VA).
```

*Implementation notes*: The presence of this declaration is stored in the data predicate `dom_base(F, A, M)`.

#### :- dom_base_deriv(BaseAbsInt, F/A, Props)

Declares that the abstract operator `F/A` for a domain whose base (as declared in `dom_def`) is `BaseAbsInt` has a default implementation. At the moment it is only used in the `domain(domains/nonrel_base)` include file that simplifies the development of non-relational domains. The predicate name and arity of the default implementation depends on the list of the property `Props`, which may contain:
  * `noq`: if present, the base implementation is called `F`, otherwise it is called `BaseAbsInt_F`;
  * `noself`: if present, the base implementation has arity `A`, otherwise it has arity `A+1` and the first argument is supposed to be the derived abstract domain.

The declaration is removed from the compilation, but when the module has been completely read, the `dom_base_deriv` declarations are used to generate code which routes the intermediate predicate to the default implementation, similarly to the `dom_base` directive.

*Implementation notes*: The presence of this declaration is stored in the data predicate `dom_base_deriv(BaseAbsInt, F, A, Props, M)`.

#### :- dom_impl(AbsInt, F/A, Props)

Declares that we are going to implement the abstract operator `F/A` for the domain `AbsInt`. `Props` is a list of properties, which may be:
  * `from(MB:AbsIntB)`: it tells that we are going to reuse the implementation of `F/A` from the `AbsIntB` domain of the `MB` module. Actually, `AbsIntB` is only used if property `noq` is not present (see later).
  * `from(AbsIntB)`: it is equivalent to `from(AbsIntB:AbsIntB)`.
  * `noq`: if provided, the predicate implementing the abstract operator is expected to be called `F`, otherwise it should be called `AbsInt_F` (if no `from` property is provided) or `AbsIntB_F` (if the `from` property is provided). Generally `noq` is always used.

The declaration is replaced by code that reroutes calls to the intermediate predicates for the domain `AbsInt` to the real implementation. For example, if `[Props=noq]` it becomes
```prolog
aidom.F(AbsInt, V1, ..., VA) :- F(V1, ..., VA).
```
where the `AbsInt` in the first argument is bound to the name of the domain. Instead, if `Prop=[from(mod:dom)]` we get
```prolog
aidom.F(AbsInt, V1, ..., VA) :- F(V1, ..., VA).
```

#### :- dom_impl(AbsInt, F/A)

Equivalent to `:- dom_impl(AbsInt, F/A, [])`.

#### :- dom_impl(as(AbsInt, Trait), F/A, Props)

It seems this form is never used in the CiaoPP code. The argument `as(AbsInt, Trait)` is called a *qualified domain*. The only change w.r.t. the form with an unqualified domain is that the clause emitted in place of the declaration are for the predicate `Trait_F` instead of `aidom.F`.

#### :- dom_impl(as(AbsInt, Trait), F/A)

Equivalent to `:- dom_impl(as(AbsInt, Trait), F/A, []`.

#### :- dom_itf

Declares that the current module will be the gateway between the interface predicates used by CiaoPP and the intermediate predicates. It is only used in the `ciao(plai/domain_hooks)` include file, which is loaded by the `ciao(plai/domains)` module. The existence of this gateway is the reason that all domains should be loaded as modules in the `domain_hooks` file.

The directive is removed by the compilation, but at the end of the module, for each domain operation `F/A` defined with the `dom_op` declaration, the `dom_itf` directive creates a clause which routes the interface predicate `F` of parity `A+1` to the intermediate predicate `aidom.F` of the same arity created by the `dom_impl`, `dom_base` and `dom_base_deriv` declarations, as follows:
```prolog
F(AbsInt, V1, ... VA) :- aidom.F(AbsInt, V1, ..., VA).
```

*Implementation note*: the presence of this declaration is stored in the data predicate `dom_itf(M)`.

## Profiling

* For implementing profiling, load the package `profilercc` in the modulo you want to profile and annotate predicates with the directive `:- cost_center pred/arity`. In the Ciao top level, load module `library(profilercc/profiler_utils)`, then use the goal `profile_reset, prodile(Goal), profile_sump.`

* Profiling work in some limited way. If you want it to work with 100% functionalities, you need to configure the CIAO Engine accordingly. It is enough to give the command
```bash
./ciao-boot.sh configure --core:debug-level=profile
```
and recompile with
```bash
./ciao-boot.sh build
```
However, the `ciaodbg` module seems old and incompatible with recent changes in the engine.

## Others

  * Analyze file by hand with the following Prolog commands (`experiments/sharing_experiments.pl` is the file to be analyzed):
  ```prolog
  use_module(library(profilercc/profiler_utils)).
  set_pp_flag(mgu_sh_optimize,optimal).
  set_pp_flag(modes,as_sharing).
  set_pp_flag(types,none).
  set_pp_flag(collapse_ai_vers,off).
  set_pp_flag(pp_info, on).
  module('experiments/sharing_experiments.pl').
  profile(analyze(as_sharing)).
  profile_dump.
  ```
