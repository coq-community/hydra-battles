<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Goedel

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/goedel/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/goedel/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



A proof in Coq of the Gödel-Rosser 1st incompleteness theorem,
which says that any first order theory extending NN (which is PA
without induction) that is complete is inconsistent.

## Meta

- Author(s):
  - Russell O'Connor (initial)
- Coq-community maintainer(s):
  - Pierre Castéran ([**@Casteran**](https://github.com/Casteran))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.7 or later
- Additional dependencies:
  - Ackermann (primitive recursive functions library that is part of this repository)
  - [Pocklington](https://github.com/coq-community/pocklington)
- Coq namespace: `Goedel`
- Related publication(s):
  - [Essential Incompleteness of Arithmetic Verified by Coq](https://arxiv.org/abs/cs/0505034) doi:[10.1007/11541868_16](https://doi.org/10.1007/11541868_16)

## Building and installation instructions

The easiest way to install the latest released version of Goedel
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-goedel
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/goedel.git
cd goedel
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation

More information about the project can be found at [this website](http://r6.ca/goedel1.html).


## Projects

 The directory theories/Ackermann contains two (not solved yet) exercises about primitive recursive functions:
 theories\_Ackermann\_Fibonacci\_project.v and theories\_Ackermann\_Ackermann_project.v.
 Please contribute!
