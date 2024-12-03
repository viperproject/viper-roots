# Viper Roots

This repository contains the Viper Roots formalization for the [Viper intermediate
verification language](https://www.pm.inf.ethz.ch/research/viper.html).
The formalization is done using the [Isabelle theorem prover](https://isabelle.in.tum.de/).

## Installation

To check and explore the formalization, you need to download the Isabelle theorem prover.
The formalization has been tested on Isabelle 2024, 
which you can download from [here](https://isabelle.in.tum.de/website-Isabelle2024/dist/)
(there are executables for Linux, Mac, Windows).

This repository is split into separate subpackages linked via Isabelle sessions. To setup the development, you have to register these sessions with Isabelle 

```
isabelle components -u foundational_boogie/BoogieLang
isabelle components -u vipersemcommon
isabelle components -u viper-total-heaps
isabelle components -u vipersemabstract
isabelle components -u viper-abstract-refines-total
isabelle components -u simple-frontend
```
where `isabelle` is the Isabelle executable. On Windows, the commands need to be
run in the Isabelle cygwin instance (TODO: show commands for Windows).
Alternatively, you can add the path to these sessions to the Isabelle `ROOTS` file
(the `ROOTS` file is located at the root of the folder that contains Isabelle).

## Folder Structure

The repository contains 6 folders:

foundational_boogie:
- This is the formalization of the Boogie intermediate verification language, which is maintained in a separate repository. This formalization is a dependency of viper-total-heaps.

vipersemcommon:
- Formalizes common parts of Viper (mainly syntactic aspects).

viper-total-heaps:
- A Viper semantics that at a high level reflects the verification condition generation (VCG) back-end of Viper.

vipeyrsemabstract:
- Formalization of a generic intermediate verification language, which we call *CoreIVL*.
  Different instantiations of CoreIVL yield different IVLs.
  This formalization includes an operational and an axiomatic semantics for CoreIVL,
  key results (such as soundness and completeness).
- Additionally contains an instantiation of CoreIVL that yields Viper; we call this 
  instantiation *ViperCore*.
- Also contains the formalization of the symbolic execution described in 4.1,
  and a proof showing its soundness w.r.t. ViperCore.

viper-abstract-refines-total:
- Soundness of the VCG semantics w.r.t. ViperCore.

simple-frontend:
- Formalizes a front-end translation from a concurrent language ParImp into Viper and 
  proves this translation sound w.r.t. ViperCore.
  This proof is done by connecting the ViperCore axiomatic semantics with a concurrent
  separation logic (CSL) for ParImp (note that this CSL is based on implicit dynamic frames).

## Selected Key Files

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
- SymbolicExecDef.thy: Definition of the symbolic execution
- SymbolicExecSound.thy: Soundness proof of the symbolic execution w.r.t. ViperCore

