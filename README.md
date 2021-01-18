<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Hydra battles in Coq

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/hydra-battles/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/hydra-battles/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



An exploration of some properties of Kirby and Paris' hydra battles,
with the help of the Coq Proof assistant. This development includes
the study of several representations of ordinal numbers, and a part
of the so-called Ketonen and Solovay machinery (combinatorial
properties of epsilon0). This project now hosts the part of goedel
dedicated to primitive recursive functions and Peano arithmetics.

## Meta

- Author(s):
  - Pierre Castéran
  - Russel O'Connor
- Coq-community maintainer(s):
  - Pierre Castéran ([**@Casteran**](https://github.com/Casteran))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.12 to 8.13
- Additional dependencies:
  - [Equations](https://github.com/mattam82/Coq-Equations) 1.2
- Coq namespace: `hydras`
- Related publication(s):
  - [Accessible Independence Results for Peano Arithmetic](https://faculty.baruch.cuny.edu/lkirby/accessible_independence_results.pdf) doi:[10.1112/blms/14.4.285](https://doi.org/10.1112/blms/14.4.285)
  - [Rapidly Growing Ramsey Functions](https://www.jstor.org/stable/2006985) doi:[10.2307/2006985](https://doi.org/10.2307/2006985)
  - [Proof Theory](https://link.springer.com/book/10.1007/978-3-642-66473-1) doi:[10.1007/978-3-642-66473-1](https://doi.org/10.1007/978-3-642-66473-1)

## Building and installation instructions

The easiest way to install the latest released version of Hydra battles in Coq
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hydra-battles
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/hydra-battles.git
cd hydra-battles
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



