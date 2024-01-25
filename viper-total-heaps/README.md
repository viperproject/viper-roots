# Viper Total Heap Semantics and Metatheory for Viper-to-Boogie Proofs

This directory contains the total heap semantics formalization for the [Viper intermediate
verification language](https://www.pm.inf.ethz.ch/research/viper.html) and the metatheory
supporting the generation of proofs for the Viper-to-Boogie implementation.
The formalization is done using the [Isabelle theorem prover](https://isabelle.in.tum.de/).

## Installation

For installation instructions, see the README.md file at the toplevel of this repository.

## Viper Total Heap Semantics

The total heap semantics is formalized in:

* `TotalViperState.thy`: Viper states
* `TotalExpressions.thy`: Expression evaluation and inhale reduction
* `TotalSemantics.thy`: Statement reduction

Note that the semantics already contains some preliminary support for predicates.
The semantics needs to still be adjusted to accurately model predicates.

## Boogie semantics

The Boogie semantics is in the Boogie folder `foundational_boogie` (via a submodule).
`BoogieInterface.thy` at the root contains some useful definitions and 
lemmas to interface with the Boogie semantics.

## Metatheory for Viper-to-Boogie proofs

### Relational rules for deriving forward simulation judgements

The generic forward simulation between Viper and Boogie is defined in `Simulation.thy`, 
which includes all the instantiation-independent rules.

The common instantiations of the forward simulation and the corresponding relational rules
are given in:

* `ExpWfRel.thy`: the expression well-definedness check instantiation
* `InhaleRel.thy`: the inhale simulation instantiation
* `ExhaleRel.thy`: the remcheck simulation instantiation 
* `StmtRel.thy`: the statement simulation instantiation 
  * lemma `exhale_rel_star` shows the rule for the separating conjunction derived via the instantiation-independent composition rule and consequence rule.

The relational rules defined in these files often rely on a judgement relating 
the evaluation of Viper and Boogie expressions, which is defined in `ExpRel.thy`. 
`ExpRel.thy` also contains relational rules for deriving expression relation 
judgements.

### Viper and Boogie Connection Setup

There are various theory files that set up the connection between Viper and Boogie.
These include:

* `ViperBoogieAbsValueInst.thy`: The interpretation of the uninterpreted Boogie types.
  This includes an instantiation of the polymorphic heap.
* `ViperBoogieBasicRel.thy`: The concrete state relation between Viper and Boogie states.
* `ViperBoogieFunctionInst.thy`: Concrete interpretations of uninterpreted Boogie functions 
  emitted by the Viper-to-Boogie implementation.

### Metatheory for the Final Theorem

`ViperBoogieEndToEnd.thy` includes lemmas that help with generating a proof of the final
theorem under the assumption that the forward simulation results hold. 

### Custom Tactics for the Generation of Proofs

Files that end with `ML.thy` contain Isabelle tactics for automatically
proving goals. The generation of proofs between Viper and Boogie 
programs makes use of these tactics. One of the the main tactics is defined in 
`StmtRelML.thy` to automatically prove a forward simulation.
Many of the tactics take hints as input, which are provided by our instrumentation 
of the Viper-to-Boogie implementation.

The implementation language for most tactics is Standard ML, which is the implementation
language of Isabelle. Some simple tactics are written in [Eisbach](https://isabelle.in.tum.de/dist/Isabelle2023/doc/eisbach.pdf), which is a language specifically designed for tactics.
