This supplementary material contains our Isabelle/HOL formalization of the claims made in the paper.
We have tested successfully with Isabelle 2022.


################################
# Structure
################################

It contains 6 folders:

foundational_boogie:
- This is a dependency of viper-total-heaps, which can be ignored.

vipersemcommon:
- Formalizes common parts of Viper (mainly syntactic).

viper-total-heaps:
- Formalization of VCGSem discussed in section 4.2.

vipersemabstract:
- Formalization of CoreIVL, its operational and axiomatic semantics (from section 3),
  key results (such as soundness and completeness), instantiation of ViperCore.
  Also contains the formalization of the symbolic execution described in 4.1,
  and prove its soundness w.r.t. ViperCore.

viper-abstract-refines-total:
- Soundness of VCGSem w.r.t. ViperCore.

simple-frontend:
- Formalization of the IDF-based CSL from section 5.1, of the front-end translation
  from 5.2, as well as its soundness proof.


################################
# Installing the Components
################################

Our formalization consists of multiple Isabelle components, which should be installed before
exploring or checking the formalization, as follows:

> /path/to/isabelle/bin/isabelle components -u foundational_boogie/BoogieLang
> /path/to/isabelle/bin/isabelle components -u vipersemcommon
> /path/to/isabelle/bin/isabelle components -u viper-total-heaps
> /path/to/isabelle/bin/isabelle components -u vipersemabstract


################################
# Key Files
################################

In vipersemcommon:
- SepAlgebraDef.thy: Definition of our IDF algebra from section 3.1.

In simple-frontend:
- ParImp.thy: Defines the ParImp language
- CSL_IDF.thy: Contains our IDF-based CSL, and its soundness proof
- FrontEndTranslation.thy: Soundness proof of our front-end translation

In viper-abstract-refines-total:
- AbstractRefinesTotal.thy: Soundness proof of VCGSem w.r.t. ViperCore

In vipersemabstract:
- AbstractSemantics.thy: Defines CoreIVL, and its operational and axiomatic semantics
- AbstractSemanticsProperties.thy: Proves the operational-to-axiomatic soundness
- EquiViper.thy: Instantiation of Viper state model as an IDF algebra.
- Instantiation.thy: Instantiation of ViperCore
- SymbolicExecDef.thy: Definition of the symbolic execution from section 4
- SymbolicExecSound.thy: Soundness proof of the symbolic execution w.r.t. ViperCore
