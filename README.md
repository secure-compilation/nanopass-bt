# Nanopass Back-Translation of Call-Return Trees for Mechanized Secure Compilation Proofs #

This repository contains the anonymized Coq development of the paper
/Nanopass Back-Translation of Call-Return Trees for Mechanized Secure Compilation Proofs/

### Prerequisites ###

This development has been built and tested under Coq 8.12.2, using Mathematical Components 1.11.0,
Extensional Structures 0.3.0 and Coq Utils commit #81eaf5b6c2ed5.

We recommend the installation via the OCaml package manager, OPAM:
- Create a new switch for this development: `opam switch create nano-bt ocaml-base-compiler.4.10.2`
  (don't forget to run `eval $(opam env)` as instructed by the command).
- Add the Coq OPAM repositories: `opam repo add coq-released https://coq.inria.fr/opam/released/` then
  `opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev`.
- Pin Coq to 8.12.2: `opam pin add coq 8.12.2`.
- Pin the Mathematical Components library to 1.11.0:
  `opam pin add coq-mathcomp-ssreflect 1.11.0` then `opam install coq-mathcomp-fingroup coq-mathcomp-algebra`.
- Pin the Extensional Structures to 0.3.0: `opam pin add coq-extructures 0.3.0`. This should install `coq-deriving` version
  0.1.1 automatically (as a dependency). Otherwise, pin `coq-deriving` to 0.1.1: `opam pin add coq-deriving 0.1.1`.
- With that, you have everything required to build the Coq Utils version we are using:
  first, pin it to the commit 81eaf5b6c2ed5:
  `opam pin add -e coq-utils git@github.com:arthuraa/coq-utils.git#81eaf5b6c2ed5`. Then, remove the two lines 
  for the dependency on `coq-extructures` and `coq-deriving`. Then add at the end `version: "81eaf5b6c2ed5"`.

### Replaying the proofs ###

    $ make

### Navigate the development ###
The main entry point of the development is the `Source/Theorem.v`
file. 
It contains the formalization of the nanopass back-translation as
presented in the paper.

The main theorem is `p_bt_does_t`. To check the assumptions,
evaluate the buffer and run the command
 ``` coq
Print Assumptions p_bt_does_t.
 ```
Coq should report no axioms.

The `Source/` folder contains the following files:
- The languages are defined in the file `Source/BacktranslationLanguages.v`
- The back-translation steps are defined in `Source/BacktranslationCompilers.v`
- The simulations are proved in `Source/BacktranslationSimulations.v`
- The file `Source/BacktranslationExpressions.v` contains the details
  of how we build the back-translated expressions
- The source language is defined in `Source/Language.v` and
  `Source/CS.v`

The other folders contain libraries that we borrow from Abate et al.'s development, and they are completely unmodified.


### License ###
- This code is licensed under the Apache License, Version 2.0 (see `LICENSE`)
- The code in the `CompCert` dir is adapted based on files in the
  `common` and `lib` dirs of CompCert and is thus dual-licensed under
  the INRIA Non-Commercial License Agreement and the GNU General
  Public License version 2 or later (see `Compcert/LICENSE`)
