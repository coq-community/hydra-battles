
(* Pierre Castéran, LaBRI and University of Bordeaux  *)

Require Import Epsilon0_Needed_Generic.
Import Hydra_Lemmas Epsilon0 Canon Paths Relation_Operators.
Import O2H.

(** We generalize the results of libraries Omega_Small and Omega2_Small:
   We prove that no ordinal strictly less than epsilon0 can be used as a variant
   for proving the termination of all hydra battles.

 
   In these proofs, we use the so-called "Ketonen-Solovay machinery" for building
a proof that shares the same structure as for the libraries above, but is much 
longer 
 *)
(** **  Bounded variants *)

Open Scope t1_scope.
Section Impossibility_Proof.
  

  Context (Var : BoundedVariant free).

  Hint Resolve nf_m : hydra.

  
  Lemma m_ge : m big_h o<= m small_h.
  Proof.
    apply m_ge_generic.
    intros;  generalize Hvar ;  destruct 1.
    apply variant_decr with i. 
    intro ; subst; now apply (head_no_round_n _  _ H).
    exists i; apply H.    
  Qed.


  
  (** ** Proof of the inequality m small_h o< m big_h 
   *)

  
  Lemma m_variant_LT : forall h h', h -+-> h' -> m h' o< m h.
  Proof.
    intros h h' H;eapply m_strict_mono with (1 := Hvar)(2:= H).
  Qed.



  Lemma  big_to_small : big_h  -+-> small_h.
  Proof. 
    unfold big_h, small_h. apply LT_to_round_plus; auto.
    unfold beta_h. apply (m_bounded big_h); auto.
  Qed.

  Lemma m_lt : m small_h o< m big_h.
  Proof. apply m_variant_LT,  big_to_small. Qed.
  

  Fact self_lt_free : m big_h o<  m big_h .
  Proof. 
    apply LE_LT_trans with (m small_h ).
    - apply m_ge.
    - apply m_lt.
  Qed. 

  Theorem Impossibility_free : False.
  Proof.  apply (LT_irrefl self_lt_free).  Qed.


End Impossibility_Proof.


Check Impossibility_free.

