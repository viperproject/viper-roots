# Viper Total Heap Semantics and Metatheory for Viper-to-Boogie

This repository contains the total heap semantics formalization for the [Viper intermediate
verification language](https://www.pm.inf.ethz.ch/research/viper.html) and the metatheory
supporting the generation of proofs for the Viper-to-Boogie implementation.
The formalization is done using the [Isabelle theorem prover](https://isabelle.in.tum.de/).

## Installation

To check and explore the formalization, you need to download the Isabelle theorem prover.
The formalization has been tested on Isabelle 2022 (which is not the latest one), 
which you can download from [here](https://isabelle.in.tum.de/website-Isabelle2022/dist/)
(there are executables for Linux, Mac, Windows).

Before the Isabelle files can be checked and explored, there are two Isabelle dependencies that 
must be installed:
* The formalization of the Boogie semantics (in the directory `foundational_boogie`)
* Common files used for the formalization of the Viper language (in the directory `vipersemcommon`)

To install these dependencies run the following commands at the root of the repository:

```
isabelle components -u foundational_boogie/BoogieLang
isabelle components -u vipersemcommon
```

where `isabelle` is the Isabelle executable. On Windows, the commands need to be
run in the Isabelle cygwin instance (TODO: show commands).

## Viper Total Heap Semantics

The total heap semantics is formalized in:

* `TotalViperState.thy`: Viper states
* `TotalExpressions.thy`: Expression evaluation and inhale reduction
* `TotalSemantics.thy`: Statement reduction

## Boogie semantics

The Boogie semantics is in the Boogie folder `foundational_boogie` (via a submodule).
The file `BoogieInterface.thy` contains some useful definitions and lemmas to interface with 
the Boogie semantics.

## Relational rules for deriving forward simulation judgements

The generic forward simulation between Viper and Boogie is defined in `Simulation.thy`, 
which includes all the instantiation-independent rules.

The common instantiation of the forward simulation and the corresponding relational rules
are given in:

* `ExpWfRel.thy`: the expression well-definedness check instantiation
* `InhaleRel.thy`: the inhale simulation instantiation
* `ExhaleRel.thy`: the remcheck instantiation. 
* `StmtRel.thy`: the statement simulation instantiation 
  * lemma `exhale_rel_star` shows the rule for the separating conjunction derived via the instantiation-independent composition rule and consequence rule.

## Viper and Boogie Connection Setup

There are various Isabelle theory files that set up the connection between Viper and Boogie.
These include:

* `ViperBoogieAbsValueInst.thy`: The interpretation of the uninterpreted Boogie types.
  This includes an instantiation of the polymorphic heap.
* `ViperBoogieBasicRel.thy`: The concrete state relation between Viper and Boogie states.

## Metatheory for the Final Theorem

`ViperBoogieEndToEnd.thy` includes lemmas that help with generating a proof of the final
theorem.

## Custom Tactics for the Generation of Proofs

Files that end with `ML.thy` contain our Isabelle tactics for automatically
proving goals. We use these tactics when generating proofs between Viper and Boogie 
programs. Many of the tactics take hints as input, which are provided by our
instrumentation of the Viper-to-Boogie implementation.

The implementation language for most tactics is Standard ML, which is the implementation
language of Isabelle. Some simple tactics are written in [Eisbach](https://isabelle.in.tum.de/dist/Isabelle2023/doc/eisbach.pdf), which is a language specifically designed for tactics.