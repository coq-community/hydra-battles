
(**

  Axiomatic definition of countable ordinal numbers (after Kurt Schutte's
  "Proof Theory" 

 Pierre Casteran (LaBRI, University of Bordeaux)
 with contributions by Florian Hatat (formerly student at ENS Lyon)

*)



From hydras Require Export Schutte_basics Ordering_Functions
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
**)
(* begin snippet Ex42a:: no-out *)
Example Ex42: omega + 42 + omega^2 = omega^2. 
(* end snippet Ex42a *)
Proof.

  (* begin snippet Ex42b *)
  assert (HAP:= AP_phi0 2). (* .no-out *)
  elim  HAP; intros _ H0; apply H0; clear H0. 
  (* end snippet Ex42b *)
  (* begin snippet Ex42d *)
  Check AP_plus_closed. (* .unfold .no-goals *)
  (* end snippet Ex42d *)
  (* begin snippet Ex42c *)
  assert (Hlt: omega < omega^2) by 
      (rewrite omega_eqn; apply phi0_mono, finite_mono;
        auto with arith).
  (* end  snippet Ex42c *)
  

  (* begin snippet Ex42e *)
  apply AP_plus_closed; trivial. 
  (* ... *)
  (* end snippet Ex42e *)
  -  apply lt_trans with omega; [| trivial]. 
     apply finite_lt_omega. 
Qed. 




