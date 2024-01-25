# Viper Roots

This repository contains the Viper Roots formalization for the [Viper intermediate
verification language](https://www.pm.inf.ethz.ch/research/viper.html).
The formalization is done using the [Isabelle theorem prover](https://isabelle.in.tum.de/).

## Installation

To check and explore the formalization, you need to download the Isabelle theorem prover.
The formalization has been tested on Isabelle 2022 (which is not the latest one), 
which you can download from [here](https://isabelle.in.tum.de/website-Isabelle2022/dist/)
(there are executables for Linux, Mac, Windows).

This repository is split into separate subpackages linked via Isabelle sessions. To setup the development, you have to register these sessions with Isabelle 

```
isabelle components -u vipersemcommon
isabelle components -u viper-total-heaps
```
where `isabelle` is the Isabelle executable. On Windows, the commands need to be
run in the Isabelle cygwin instance (TODO: show commands for Windows).

Additionally, some parts of `viper-total-heaps` depend on a [formalization of the Boogie semantics](https://github.com/gauravpartha/foundational_boogie/). This semantics is included in this repository as a submodule and should be added as an isabelle component via the following command:
```
isabelle components -u foundational_boogie/BoogieLang
```

You can explore the files in the Isabelle IDE. To just check that the proofs succeed,
run `isabelle build -j4 -D viper-total-heaps` at the root of the repository (`j4` tells Isabelle to 
use 4 cores; you may use any suitable number).
