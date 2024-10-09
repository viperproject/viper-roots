# ViperSemAbstract

## Files

### AbstractSemantics.thy

- This file defines the syntax for "semantic" Viper programs, where assertions, expressions, etc. are semantic
(see `datatype ('a, 'v, 'r) abs_stmt`).
- It also defines an operational semantics for these programs, `red_stmt`, with both angelic and demonic nondeterminism.
- Finally, it defines a separation logic proof system for these programs, `SL_proof`.
There is (should be) exactly *one* rule per syntactic construct. In particular, there is no frame rule, and no consequence rule.
Consequence can be applied at the relevant places; for example, the rule for exhale `RuleExhale` allows the precondition `B` to be
weakened to `A && P`.
- Note that all of the above are parametric on the state model `'a`, which is required to be a separation algebra `sep_algebra`.
This state model is then "augmented" with a store of local variables and a trace (for old-expressions), in the file `LiftSepAlgebra.thy`
in ViperSemCommon.

Open questions:
- Rule for heap-dependent heap-assignments?
- Rule for labels? Could be done with a modality, but how can this modality be used in the front-end logic? Can we showcase this with a method call translation?
- Do we actually need the frame-preserving axioms?

### AbstractSemanticsProperties.thy

This file imports `AbstractSemantics.thy`, and proves that if a semantic Viper statement is correct (meaning that there exist reductions
from initial states to sets of states), then there exists an SL proof for this statement.

### EquiViper.thy

- This file defines an equirecursive state model for Viper, `'a virtual_state`, composed of a permission mask (total map from heap locations
to real permission amounts), and a partial heap (partial map from heap locations to values). It is constrained such that it has a defined value for every heap location to which it has non-zero permission.
- This file also proves that the type `'a virtual_state` can be seen as a `sep_algebra`.
- Finally, this file defines how to reduce pure expressions (`red_pure`) and evaluate assertions (`sat`) in virtual states.

Open questions:
- Should virtual states be bounded (i.e., have permission amounts at most 1)?
- If not, where should we bound the permissions?

### Instantiation.thy

- This file instantiates the locale from `AbstractSemantics.thy` with the `'a virtual_state` type from `EquiViper.thy`.
- It also defines a translation (`compile`) from syntactic Viper statements (`stmt` defined in `vipersemcommon/ViperLang.thy`)
to "semantic" Viper statements (`abs_stmt` defined in `AbstractSemantics.thy`).

Open questions:
- Should we compile while loops and method calls to their encodings? In this case, the `compile` function should take a program as argument.
- Domain types are currently ignored.

### Files related to the "Fractional Resources" paper

The following files formalize the theory from the "Fractional resources in unbounded separation logic" paper (which gives a meaning to
fractional predicates) for Viper virtual states:
- CombinabilityInSemMult.thy
- EquiSemAuxLemma.thy
- FixedPointEquiSem.thy
- PredInterpCompleteLattice.thy
- SemSynMultEquiv.thy
