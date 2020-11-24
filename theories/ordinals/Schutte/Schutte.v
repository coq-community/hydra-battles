
(**

  Axiomatic definition of countable ordinal numbers (after Kurt Schutte's
  "Proof Theory" 

 Pierre Casteran (LaBRI, University of Bordeaux)
 with contributions by Florian Hatat (formerly student at ENS Lyon)

*)



From hydras.ordinals Require Export Schutte_basics Ordering_Functions
        Addition AP CNF Critical Correctness_E0.



(** * Warning


This directory contains an adaptation to Coq of the mathematical 
presentation of the set of countable ordinal numbers by K. Schutte.

In order to respect as most as possible the style of that presentation, 
we chosed to work in classical logic augmented by Hilbert's [[epsilon]]
operator. 

So, all the construction herein is powered by six axioms, three of them are
Schutte's axioms, and the other ones allow us to work in that "classical" framework, still using the Coq proof assistant and its libraries.


** Schutte's Axioms 

 We consider a type [ON] (Ordinal numbers), well-ordered by some relation 
 [lt], and such that every subset [X] of [Ord] is countable iff [X] is bounded.


[[

Axiom AX1 : WO lt.

Axiom AX2 : forall X: Ensemble Ord, (exists a,  (forall y, X y -> y < a)) ->
                                   countable X.


Axiom AX3 : forall X : Ensemble Ord,
              countable X -> 
              exists a,  forall y, X y -> y < a.

]]

** Classical logic and Hilbert style 

*** From [Coq.Logic.Classical]


[[
Axiom classic : forall P:Prop, P \/ ~ P.
]]


*** From [Coq.Logic.Epsilon]

[[

Axiom epsilon_statement :
  forall (A : Type) (P : A->Prop), inhabited A ->
    { x : A | (exists x, P x) -> P x }.

]] 


*** Needed for [epsilon] to work properly.

[[
Axiom inh_Ord : inhabited Ord.

]]



* Main result

In #<a href="teaser.Ordinals.Axiomatic.Injection_from_T1.html"> this module </a>#,
we build  an embedding from the set of ordinal terms in Cantor Normal Form into
the interval of ordinal numbers strictly less than [epsilon0].



**)
