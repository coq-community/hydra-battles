(** The order [lt] on [T] is not well-founded *)

From hydras Require Import T1.
From Coq Require Import Relations.

Section Proof_of_lt_not_wf.

  Hypothesis lt_wf : well_founded lt.

  Fixpoint  s (i:nat) : T1 :=
    match i with
      0 => phi0 2
    | S j => cons 1 0 (s j)
    end.

  Lemma s_decr : forall i,  lt (s (S i)) (s i).
  Proof.
    induction i.
      compute; auto.
      cbn;  apply tail_lt; apply IHi.
  Qed.

  (* From [coq-art] exercises *)
  
  Section seq_intro.
    Variable A: Type.
    Variable seq : nat -> A.
    Variable R : A -> A -> Prop.
    Hypothesis Rwf : well_founded R.
    Let is_in_seq (x:A) :=  exists i : nat, x = seq i.


    Lemma not_acc : forall a b:A, R a b -> ~ Acc R a -> ~ Acc R b.
    Proof.
      intros a b H H0 H1;  absurd (Acc R a); auto.
    Qed.

    Lemma acc_imp : forall a b:A, R a b -> Acc R b -> Acc R a.
    Proof.
      intros a b H H0;  generalize a H; now induction H0.
    Qed.

    Lemma not_decreasing_aux : ~ (forall n:nat, R (seq (S n)) (seq n)). 
    Proof.
      unfold not in |- *; intro Hseq.
      assert  (H : forall a:A, is_in_seq a -> ~ Acc R a).
      -   intro a; pattern a in |- *; apply well_founded_ind with A R; auto.
          intros x Hx [i Hi]; generalize (Hseq i); intro H0; rewrite Hi.
          apply not_acc with (seq (S i)); auto.
          apply Hx.
          +  rewrite Hi; auto.
          +  exists (S i); auto.
      - apply (H (seq 0)). 
        +  exists 0; trivial. 
        + apply Rwf.
    Qed.


  End seq_intro.

  Theorem not_decreasing (A:Type)(R: relation A) (Hwf : well_founded R) :
    ~ (exists seq : nat -> A, (forall i:nat, R (seq (S i)) (seq i))).
  Proof.
    intros [s Hs].  apply (not_decreasing_aux _ s R Hwf Hs).
  Qed.

  Lemma contrad : False.
    apply (not_decreasing T1 lt lt_wf).  exists s.
    apply  s_decr.
  Qed.  

End Proof_of_lt_not_wf.

Lemma lt_not_wf : ~ well_founded lt.
  exact contrad. 
Qed.
