#  Hydra Battles and Cie (_work in progress_).

This contribution contains two parts:

- An exploration of some properties of Kirby and Paris' hydra battles, with the help of the **Coq** Proof assistant. This development includes the study of several representations of ordinal numbers, and a part of the so-called _Ketonen and Solovay machinery_ (combinatorial properties of epsilon0).

- Some algorithms for computing _x^n_ with as few multiplications as possible (using _addition chains_).


##  Installation
-   __Warning:__  A few files use __Coq__ plug-ins. The easiest way is to install  the following __opam__ packages:
      __coq-equations__,  __coq-paramcoq__, __coq_mathcomp-ssreflect__ and 
    __coq-mathcomp-algebra__. In case of problems, please compile with __make -k__ the rest of the files.
      
-  the general Makefile is in the top directory 
     - make : compilation of the Coq scripts
     - make pdf : generation of the documentation
     - make html : generation of coqdoc html files 

##   Contents

### Documentation
- https://coq-community.org/hydra-battles/hydras.pdf
     
- The command `make pdf` generates a local copy as `doc/hydras.pdf`

###  coqdoc html files
 - directory theories/html


### Coq sources (directory theories)

- theories/ordinals/
  -   Hydra/*.v 
      -    Representation in _Coq_ of hydras and hydra 
   battles
      - A proof of termination of all hydra battles (using ordinal numbers below epsilon0)
      - A proof that no variant bounded by some ordinal less than epsilon0 can prove this termination
      - Comparison of the length of some kind of Hydra battles with the Hardy hierarchy of fast growing functions
    
  -  Epsilon0/*.v
	  - Data types for representing ordinals less than epsilon0 in Cantor normal form
	  - The _Ketonen-Solovay machinery_: canonical sequences, accessibility, paths inside epsilon0
	  - Representation of some hierarchies of fast growing functions
   
 -  Schutte/*.v
       - An axiomatization of countable ordinals, after Kurt Schütte. It is intended to be a reference for the data types considered in theories/Epsilon0.

  - Gamma0/*.v
       - A data type for ordinals below Gamma0 in Veblen normal form (**draft**).
  
  - rpo/*.v
      - A contribution on _recursive path orderings_ by Evelyne Contejean.
  
  - Prelude/*.v
     - Various auxiliary definitions and lemmas

- theories/additions/*.v
  
      - Addition chains

 
## Contributions are welcome ! 
  Any suggestion for improving the Coq scripts and/or the documentation will be taken into account.
  
  - In particular, we would be delighted to replace proofs with simpler ones, and/or to propose various proofs or definitions of the same concept, in order to illustrate different techniques and patterns. New tactics for automatizing the proofs are welcome too.

  - Along the text, we propose several _projects_, the solution of which is planned to be integrated in the development. 
  
 - Please do not hesitate to send your remarks as GitHub  issues and your suggestions of improvements (including solutions of "projects") as pull requests. 
  
  - __Contact__ : pierre dot casteran at gmail dot com   

A bibliography is at the end of the documentation. Please feel free to suggest us more references. 

