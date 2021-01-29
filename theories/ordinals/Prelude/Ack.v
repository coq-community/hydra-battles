From hydras Require Export Iterates .
From Coq Require Import Lia.

Fixpoint Ack (m:nat) : nat -> nat :=
  match m with 0 => S
          |   S n => fun k =>  iterate (Ack n) (S k) 1
  end.




(** *** Equations (from wikipedia) *)

Lemma Ack_0 : Ack 0 = S.
Proof refl_equal.

Lemma Ack_S_0 m : Ack (S m) 0 = Ack m 1. 
Proof.  now simpl. Qed.

Lemma Ack_S_S : forall m p,
    Ack (S m) (S p) = Ack m (Ack (S m) p).
Proof.  now simpl. Qed.


Definition phi_Ack (f : nat -> nat) (k : nat) :=
  iterate f (S k) 1.

Definition phi_Ack' (f : nat -> nat) (k : nat) :=
  iterate f  k (f 1).

Lemma phi_Ack'_ext f g: (forall x, f x = g x) ->
                        forall p,  phi_Ack' f p = phi_Ack' g p.
Proof.
  induction p.      
  -  cbn; auto.
  -  cbn;  unfold phi_Ack' in IHp;  rewrite IHp;  apply H.
Qed.

Lemma phi_phi'_Ack : forall f k,
    phi_Ack f k = phi_Ack' f k.
Proof.
  unfold phi_Ack, phi_Ack'; intros.
  now rewrite iterate_S_eqn2.
Qed.

Lemma Ack_paraphrase : forall m ,  Ack m  =
                                   match m with
                                   | 0 => S 
                                   | S p =>  phi_Ack  (Ack p) 
                                   end.
Proof.
  destruct m; reflexivity.
Qed.

Lemma Ack_paraphrase' : forall m k,  Ack m  k=
                                     match m with
                                     | 0 => S k
                                     | S p =>  phi_Ack'  (Ack p) k
                                     end.
Proof.
  destruct m.
  -   reflexivity.
  - intro k; rewrite <- phi_phi'_Ack; reflexivity.
Qed.

Lemma Ack_as_iter' : forall m p, Ack m p = iterate phi_Ack' m S p.
Proof.
  induction  m.
  - reflexivity.
  -intro p; rewrite Ack_paraphrase', iterate_S_eqn.
   apply phi_Ack'_ext; auto.
Qed.


Lemma Ack_as_iter : forall m , Ack m  = iterate phi_Ack m S.
Proof.
  induction  m.
  - reflexivity.
  - rewrite Ack_paraphrase, iterate_S_eqn;  now rewrite IHm.
Qed.




Section Ack_Properties.
  Let P (n:nat) := 
    strict_mono (Ack n) /\
    S <<=  (Ack n) /\
    (forall m,  Ack n m <= Ack (S n) m).

  Lemma P0 : P 0.
  Proof.
    repeat split.
    - intros x y; cbn; auto with arith.
    -  apply smono_Sle.
       + discriminate.
       + intros x y; cbn; auto with arith.
    - intro m; simpl (Ack 1); cbn; induction m; cbn; auto with arith. 
  Qed.

  Section Induc.
    Variable n:nat.

    Hypothesis Hn : P n.
    
    Lemma L1 : strict_mono (Ack (S n)).
    Proof.
      intros m p H; cbn.
      destruct Hn as [H1 H2]; apply H1.
      apply iterate_lt; auto.
      - split; auto.
        destruct H2;  auto.
    Qed.

    Lemma L2 : S <<= Ack (S n).
    Proof.
      intros p; destruct Hn as [H1 [H2 H3]]. 
      transitivity (Ack n p).
      - apply H2.
      - apply H3. 
    Qed.

    Remark Ack_n_mono_weak : forall x y, x <= y ->
                                         Ack n x <= Ack n y.
    Proof.
      intros x y H; destruct (Lt.le_lt_or_eq _ _ H).
      apply PeanoNat.Nat.lt_le_incl; auto.
      - destruct Hn.
        apply H1; auto.
      - rewrite H0;auto.
    Qed.

    Lemma L3 : forall m, Ack (S n) m <= Ack (S (S n)) m.
    Proof.
      destruct Hn as [H1 [H2 H3]].
      intro m; simpl (Ack (S (S n)) m); simpl (Ack (S n) m).  
      apply Ack_n_mono_weak.
      apply iterate_mono_weak_2.
      - intro; transitivity (S x). 
        + auto.
        + apply H2.
      - transitivity (S m); auto.
        replace (S m) with (iterate S m 1).
        +  apply iterate_mono_1 with 0; auto.
           * intros x y H; auto with arith.
           * intro x; auto.
           * intros; generalize (L2 n0); auto.
        + induction m; cbn; auto.
    Qed.


    Lemma L5: P (S n).
    Proof.
      repeat split.
      - apply L1.
      - apply L2.
      - apply L3.
    Qed. 

  End Induc.

  
  Lemma Ack_properties : forall n, P n.
  Proof.
    induction n.
    apply P0.
    apply L5; auto.
  Qed.

End Ack_Properties.


Lemma L6 (x:nat): forall n, 2 + n <= Ack (2+x) n.
Proof.
  induction x.
   -  intros; simpl (2+0).
      induction n; auto with arith.
      rewrite     Ack_S_S.
      transitivity (Ack 0 (Ack 2 n)).
      +  rewrite Ack_0; lia.
      +  destruct (Ack_properties 0) as [_ [H1 H2]].
         apply H2.
   - replace (2 + S x) with (S (2 + x)) by lia.
     destruct (Ack_properties (2+x)) as [_ [H1 H2]]. 
     intro n; transitivity   (Ack (2 + x) n); auto.
Qed.

Lemma L07 : forall x n, Ack (S x) (S n) <= Ack (2+x) n.
Proof. 
  intro.
  destruct n.
  -   simpl (2 + x); rewrite Ack_S_0; left.
  -  simpl (2+ x); rewrite (Ack_S_S  (S x)).
     generalize (L6 x n ). intro H.
     apply Ack_n_mono_weak.
   + destruct (Ack_properties (S x)) as [H1 [H2 H3]].
     repeat split; auto.
   + simpl plus in H; auto.
Qed.

Lemma L08 (x n:nat) : Ack x (Ack x n) <= Ack (S x) (S n) .
Proof.
  destruct (Ack_properties x) as [H1 [H2 H3]].
  transitivity (Ack x (Ack (S x) n)); auto.
  - apply Ack_n_mono_weak.  
    + repeat split;auto.   
    +  apply H3; rewrite <- Ack_S_S; auto.
Qed.

Lemma L09 (x n:nat) : Ack x (Ack x n) <= Ack (S (S x)) n.
Proof.
  transitivity (Ack (S x) (S n) ).
  - apply  L08.
  - apply L07.
Qed.

Lemma L010 : forall x y ,  x<= y -> forall n,  Ack x n <= Ack y n.
Proof.
  induction 1; auto.
  intro n; transitivity (Ack m n); auto.
  destruct (Ack_properties m) as [_ [_ H0]]; auto.
Qed.

Lemma L7 : forall k m n, Ack k (Ack m n) <= Ack (2 + max k m) n.
Proof.
  intros; pose (x:= Nat.max k m).
  - fold x.
    assert (H:m <= x) by lia.
    assert (H0: k <= x) by lia.
    simpl (2 + x); transitivity (Ack x (Ack m n)). 
    +  apply L010; auto.
    +  transitivity (Ack x (Ack  x n)).
       *  apply Ack_n_mono_weak.
          destruct (Ack_properties x) as [H1 [H2 H3]].
          repeat split; auto.
          apply L010; lia.
  * apply L09.
Qed.

