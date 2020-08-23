#  Hydras and roosters

An exploration of some properties of Kirby and Paris' hydra battles, with the help of the **Coq** Proof assistant (_draft_).


_All of the Coq scripts and latex files in this project are available under the [CeCILL-B license](https://cecill.info/licences/Licence_CeCILL-B_V1-en.html)_.

##  Installation
-  the general Makefile is in the top directory 

##   Contents

### Documentation
- latex/hydras.pdf  

###  coqdoc html files
 - directory src/html


### Coq sources (directory src)

- src/Hydra/*.v
   - Representation in _Coq_ of hydras and hydra 
   battles
   - A proof of termination of all hydra battles (using ordinal numbers below epsilon0)
   - A proof that no variant bounded by some ordinal less than epsilon0 can prove this termination
   - Comparison of the length of some kind of Hydra battles with the Hardy hierarchy of fast growing functions
    
-  src/Epsilon0/*.v
	- Data types for representing ordinals less than epsilon0 in Cantor normal form
	- The _Ketonen-Solovay machinery_: canonical sequences, accessibility, paths inside epsilon0
	- Representation of some hierarchies of fast growing functions
   
- src/Schutte/*.v
     - An axiomatization of countable ordinals, after Kurt Schütte. It is intended to be a reference for the data types considered in src/Epsilon0.

- scr/Gamma0/*.v
      - A data type for ordinals below Gamma0 in Veblen normal form (**draft**).
  
- src/rpo/*.v
   - A contribution on _recursive path orderings_ by Evelyne Contejean.
  
- src/Prelude/*.v
  - Various auxiliary definitions and lemmas

 


## Main mathematical references

1.  L. Kirby and J. Paris, _Accessible Independence Results for Peano Arithmetic_,
	Bulletin of the London Mathematical Society,  1982, pp 725-731.
	
	
2. J. Ketonen and R. Solovay, _Rapidly Growing Ramsey Functions_, Annals of Mathematics, 1981, 2, pp 267-314.
 
 
3. Kurt Schütte, _Proof Theory_, Springer, 1977.
