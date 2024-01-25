# Common Files for Viper Formalization in Isabelle

This repository contains common files for the Isabelle formalization of the [Viper intermediate verification language](https://www.pm.inf.ethz.ch/research/viper.html). These files include:

* `ViperLang.thy`: the syntax of Viper.
* `ValueAndBasicState.thy`: Viper values and other useful concepts for defining the semantics.
* `Binop.thy`: the evaluation of unary and binary operations.
* `SepAlgebra.thy`: various type classes for Viper states, which includes partial commutative monoids and
separation algebras

The other files contain helper definitions.