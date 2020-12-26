
(**  Pierre Castéran, LaBRI and University of Bordeaux  *)

From hydras Require Import Epsilon0_Needed_Generic.
Import Hydra_Lemmas Epsilon0 Canon Paths Relation_Operators.
Import O2H.

(** We generalize the results of libraries Omega_Small and Omega2_Small:
   We prove that no ordinal strictly less than epsilon0 can be used as a variant
   for proving the termination of all hydra battles.
We use the so-called "Ketonen-Solovay machinery" for building
a proof that shares the same structure as for the libraries above, but is much 
longer 
 *)

(** **  Bounded variants *)

Open Scope t1_scope.
Section Impossibility_Proof.
  
  Context 
          (mu: T1)
          (Hmu: nf mu)
          (m : Hydra -> T1)
          (Var : Hvariant  free m)
          (Hy : BoundedVariant (Lt:= LT) (Wf:= T1_wf) free m Var mu).


  Hint Resolve nf_m : hydra.

  
  Lemma m_ge : m (big_h mu) t1<= m (small_h mu m).
  Proof.
    About m_ge_generic.
eapply m_ge_generic.
auto.
intros.   generalize Var ;  destruct 1.
    apply variant_decr with i. 
    intro ; subst; now apply (head_no_round_n _  _ H).
    exists i; apply H.    
  Qed.


  
  (** ** Proof of the inequality m small_h t1< m big_h 
   *)

  
  Lemma m_variant_LT : forall h h', h -+-> h' -> m h' t1< m h.
  Proof.
    intros h h' H;eapply m_strict_mono with (1 := Var)(2:= H).
  Qed.



  Lemma  big_to_small : big_h mu  -+-> (small_h mu m).
  Proof. 
    unfold big_h, small_h. apply LT_to_round_plus; auto.
    unfold beta_h. apply (m_bounded (big_h mu)); auto.
  Qed.

  Lemma m_lt : m (small_h mu m) t1< m (big_h mu).
  Proof. apply m_variant_LT,  big_to_small. Qed.
  

  Fact self_lt_free : m (big_h mu) t1<  m (big_h mu).
  Proof. 
    apply LE_LT_trans with (m (small_h mu m)).
    - apply m_ge.
    - apply m_lt.
  Qed. 

  Theorem Impossibility_free : False.
  Proof.  apply (LT_irrefl self_lt_free).  Qed.


End Impossibility_Proof.


Check Impossibility_free.

