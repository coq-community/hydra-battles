# Hydras & Co.

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/hydra-battles/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/hydra-battles/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/hydra-battles#contributions-are-welcome

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



This Coq-based project has four parts:

- An exploration of some properties of Kirby and Paris' hydra
  battles, including the study of several representations of
  ordinal numbers and a part of the so-called _Ketonen and Solovay
  machinery_ (combinatorial properties of epsilon0).

  This part also hosts a formalization by Russell O'Connor of
  primitive recursive functions and Peano Arithmetic (PA).

- Some algorithms for computing _x^n_ with as few multiplications as
  possible (using _addition chains_).

- A bridge to definitions and results in the
  [Gaia project](https://github.com/coq-community/gaia), in particular
  on ordinals.

- A proof originally by Russell O'Connor of the Gödel-Rosser 1st
  incompleteness theorem, which says that any first order theory
  extending NN (which is PA without induction) that is complete is
  inconsistent.

Both the [documentation](https://coq-community.org/hydra-battles/doc/hydras.pdf)
and the Coq sources are _work continuously in progress_. For more information on
how the project is organized, maintained, and documented, see
[this paper](https://hal.archives-ouvertes.fr/hal-03404668) from
the proceedings of [JFLA 2022](http://jfla.inria.fr/jfla2022.html).

## Meta

- Author(s):
  - Yves Bertot
  - Pierre Castéran
  - Évelyne Contejean
  - Jeremy Damour
  - Stéphane Desarzens
  - Russell O'Connor
  - Karl Palmskog
  - Clément Pit-Claudel
  - Théo Zimmermann
- Coq-community maintainer(s):
  - Pierre Castéran ([**@Casteran**](https://github.com/Casteran))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.14 or later
- Additional dependencies:
  - [Equations](https://github.com/mattam82/Coq-Equations) 1.2 or later
  - [Coq-elpi](https://github.com/LPCIC/coq-elpi) 1.16 or later
  - [MathComp SSReflect](https://github.com/math-comp/math-comp) 1.15 or later
  - [MathComp Algebra](https://github.com/math-comp/math-comp)
  - [Gaia's Schütte ordinals](https://github.com/coq-community/gaia) 1.14 or later
  - [Mczify](https://github.com/math-comp/mczify)
  - [LibHyps](https://github.com/Matafou/LibHyps)
  - [CoqPrime](https://github.com/thery/coqprime)
  - [ZornsLemma](https://github.com/coq-community/zorns-lemma) 10.2.0 or later
- Coq namespace: `hydras`, `additions`, `gaia_hydras`, `Goedel`
- Related publication(s):
  - [Hydras & Co.: Formalized mathematics in Coq for inspiration and entertainment](https://hal.archives-ouvertes.fr/hal-03404668) 
  - [Essential Incompleteness of Arithmetic Verified by Coq](https://arxiv.org/abs/cs/0505034) doi:[10.1007/11541868_16](https://doi.org/10.1007/11541868_16)
  - [Accessible Independence Results for Peano Arithmetic](https://faculty.baruch.cuny.edu/lkirby/accessible_independence_results.pdf) doi:[10.1112/blms/14.4.285](https://doi.org/10.1112/blms/14.4.285)
  - [Rapidly Growing Ramsey Functions](https://www.jstor.org/stable/2006985) doi:[10.2307/2006985](https://doi.org/10.2307/2006985)
  - [Proof Theory](https://link.springer.com/book/10.1007/978-3-642-66473-1) doi:[10.1007/978-3-642-66473-1](https://doi.org/10.1007/978-3-642-66473-1)

## Building and installation

- To get the required dependencies, you can use [opam](https://opam.ocaml.org)
  or [Nix](https://nixos.org). With opam:
  - `opam install ./coq-hydra-battles.opam --deps-only` to get the _hydra battles_ dependencies;
  - `opam install ./coq-addition-chains.opam --deps-only` to get the _addition chains_ dependencies.
  - `opam install ./coq-gaia-hydras.opam --deps-only` to get the _gaia hydras_ dependencies.
  - `opam install ./coq-goedel.opam --deps-only` to get the _Goedel_ dependencies.

  With Nix, just run `nix-shell` to get all the dependencies
  (including for building the documentation). If you only want the
  dependencies to build a sub-package, you can run one of:
  - `nix-shell --argstr job hydra-battles`
  - `nix-shell --argstr job addition-chains`
  - `nix-shell --argstr job gaia-hydras`
  - `nix-shell --argstr job goedel`

- Building the PDF documentation also requires
  [Alectryon](https://github.com/cpitclaudel/alectryon) 1.4
  and [SerAPI](https://github.com/ejgallego/coq-serapi).
  See [`doc/movies/Readme.md`](doc/movies/Readme.md) for details.

- The general Makefile is in the top directory:
  - `make` : compilation of the Coq scripts
  - `make pdf` : generation of PDF documentation as `doc/hydras.pdf`
  - `make html` : generation of HTML documentation in `theories/html`

- You may also rely on `dune` to install just one part. Run:
  - `dune build coq-hydra-battles.install` to build only the _hydra battles_ part
  - `dune build coq-addition-chains.install` to build only the _addition chains_ part
  - `dune build coq-gaia-hydras.install` to build only the _gaia hydras_ part
  - `dune build coq-goedel.install` to build only the _goedel_ part

- Documentation for the `master` branch is continuously deployed at:
  - https://coq-community.org/hydra-battles/doc/hydras.pdf
  - https://coq-community.org/hydra-battles/theories/html/toc.html

## Contents

### Coq sources (directory theories)

- theories/ordinals

  - Hydra/*.v 
    - Representation in _Coq_ of hydras and hydra battles
    - A proof of termination of all hydra battles (using ordinal numbers below epsilon0)
    - A proof that no variant bounded by some ordinal less than epsilon0 can prove this termination
    - Comparison of the length of some kind of Hydra battles with the Hardy hierarchy of fast growing functions
    
  - OrdinalNotations/*.v
    - Generic formalization on ordinal notations (well-founded ordered datatypes with a comparison function)

  - Epsilon0/*.v
    - Data types for representing ordinals less than epsilon0 in Cantor normal form
    - The _Ketonen-Solovay machinery_: canonical sequences, accessibility, paths inside epsilon0
    - Representation of some hierarchies of fast growing functions

  - Schutte/*.v
    - An axiomatization of countable ordinals, after Kurt Schütte. It is intended to be a reference for the data types considered in theories/Epsilon0.

  - Gamma0/*.v
    - A data type for ordinals below Gamma0 in Veblen normal form (**draft**).

  - rpo/*.v
    - A contribution on _recursive path orderings_ by Evelyne Contejean.

  - Ackermann/*.v
    - Primitive recursive functions, first-order logic, NN, and PA

  - MoreAck/*.v
     - Complements to the legacy **Ackermann** library

  - Prelude/*.v
    - Various auxiliary definitions and lemmas

- theories/additions/*.v  
  - Addition chains

- theories/gaia/*.v
  - Bridge to the ordinals in Gaia that are encoded following Schütte and Ackermann

- theories/goedel/*.v
  - Gödel's 1st incompleteness theorem and its variations

### Exercises

- exercises/ordinals/*.v
  - Exercises on ordinals

- exercises/primrec/*.v
  - Exercises on primitive recursive functions

## Contributions are welcome

Any suggestion for improving the Coq scripts and/or the documentation will be taken into account.

- In particular, we would be delighted to replace proofs with simpler ones, and/or to propose various proofs or definitions of the same concept, in order to illustrate different techniques and patterns. New tactics for automatizing the proofs are welcome too.

- Along the text, we propose several _projects_, the solution of which is planned to be integrated in the development.

- Please do not hesitate to send your remarks as GitHub issues and your suggestions of improvements (including solutions of "projects") as pull requests.
- Of course, new topics are welcome !

- If you wish to contribute without having to clone the project /
  install the dependencies on your machine, you may use
  [Gitpod](https://gitpod.io/#https://github.com/coq-community/hydra-battles/)
  to get an editor and all the dependencies in your browser, with
  support to open pull requests as well.

- __Contact__ : pierre dot casteran at gmail dot com

A bibliography is at the end of the documentation. Please feel free to suggest more references to us.
