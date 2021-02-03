From hydras Require Export Iterates Exp2.
From Coq Require Import Lia.


(** About the famous Ackermann function *)


(** Definition *)

Fixpoint Ack (m:nat) : nat -> nat :=
  match m with
  | 0 => S
  |   S n => fun k =>  iterate (Ack n) (S k) 1
  end.


(** *** Equations *)

Lemma Ack_0 : Ack 0 = S.
Proof refl_equal.

Lemma Ack_S_0 m : Ack (S m) 0 = Ack m 1. 
Proof.  now cbn. Qed.

Lemma Ack_S_S : forall m p,
    Ack (S m) (S p) = Ack m (Ack (S m) p).
Proof.  now cbn. Qed.

Lemma Ack_1_n n : Ack 1 n = S (S n).
Proof.
  cbn; f_equal.
  induction n; cbn ;auto.
Qed.  

Lemma Ack_2_n n: Ack 2  n = 2 * n + 3.
Proof.
  induction  n.
  -  reflexivity. 
  -  rewrite Ack_S_S, IHn, Ack_1_n; lia.
Qed.


Lemma Ack_3_n n: Ack 3 n = exp2 (S (S (S n))) - 3.
Proof.
  induction n.
  -  reflexivity.
  - rewrite Ack_S_S, Ack_2_n, IHn.
    replace ( exp2 (S (S (S (S n))))) with (2 * exp2 (S (S (S n)))).
     2: reflexivity.

    assert (3 <= exp2 (S (S (S n)))).
    { clear IHn;induction n; cbn.
      auto with arith.
        simpl in IHn.
lia.   }

    pose (n0 := exp2 (S (S (S n)))).
    fold n0; fold n0 in H.
    lia.
Qed.



Lemma Ack_4_n n : Ack 4 n = hyper_exp2 (S (S (S n))) - 3.
Proof.
  induction n.
  - cbn. reflexivity. 
  -  assert (3 <= hyper_exp2 (S (S (S n)))). {
       clear IHn; induction n.
       cbn.
       auto with arith.
       rewrite hyper_exp2_S.    
       transitivity (hyper_exp2 (S (S (S n)))).
       auto.
       generalize (hyper_exp2 (S (S (S n))) ).
       induction  n0.
       cbn; auto.
       cbn.
       assert (0 < exp2 n0).
       clear IHn0; induction n0.
       cbn;auto.
       cbn; lia.
       lia.
     }
     rewrite Ack_S_S, IHn.
     rewrite Ack_3_n; rewrite (hyper_exp2_S  (S (S (S n)))).
     replace (S (S (S (hyper_exp2 (S (S (S n))) - 3))))
       with (hyper_exp2 (S (S (S n)))); auto.
     lia.
Qed.


(** ** Ackermann function as a 2nd-order iteration *)


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

(** ** monotony properties *)




Section Ack_Properties.
  Let P (n:nat) := 
    strict_mono (Ack n) /\
    S <<=  (Ack n) /\
    (forall m,  Ack n m <= Ack (S n) m).

  Remark P0 : P 0.
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
      
    Remark  Rem1 : strict_mono (Ack (S n)).
    Proof.
      intros m p H; cbn.
      destruct Hn as [H1 H2]; apply H1.
      apply iterate_lt; auto.
      - split; auto.
        destruct H2;  auto.
    Qed.

    Remark Rem2 : S <<= Ack (S n).
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
      - destruct Hn as [H1 _]; apply H1; auto.
      - rewrite H0;auto.
    Qed.

    Remark Rem3 : forall m, Ack (S n) m <= Ack (S (S n)) m.
    Proof.
      destruct Hn as [H1 [H2 H3]].
      intro m; simpl (Ack (S (S n)) m); simpl (Ack (S n) m).  
      apply Ack_n_mono_weak.
      apply iterate_mono_weak_2.
      - intro; transitivity (S x); auto.
      - transitivity (S m); auto.
        replace (S m) with (iterate S m 1).
        +  apply iterate_mono_1 with 0; auto.
           * intros x y H; auto with arith.
           * intro x; auto.
           * intros; generalize (Rem2 n0); auto.
        + induction m; cbn; auto.
    Qed.


    Lemma L5: P (S n).
    Proof.
      repeat split.
      - apply Rem1.
      - apply Rem2.
      - apply Rem3.
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
  intro; destruct n.
  -  simpl (2 + x); rewrite Ack_S_0; left.
  -  simpl (2 + x); rewrite (Ack_S_S  (S x)).
     generalize (L6 x n ); intro H;  apply Ack_n_mono_weak.
     + destruct (Ack_properties (S x)) as [H1 [H2 H3]];
       repeat split; auto.
     + auto. 
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

Lemma Ack_mono_l : forall x y ,  x <= y -> forall n,  Ack x n <= Ack y n.
Proof.
  induction 1; auto.
  intro n; transitivity (Ack m n); auto.
  destruct (Ack_properties m) as [_ [_ H0]]; auto.
Qed.

Lemma Ack_Ack_le : forall k m n, Ack k (Ack m n) <= Ack (2 + max k m) n.
Proof.
  intros; pose (x:= Nat.max k m).
  - fold x.
    assert (H:m <= x) by lia.
    assert (H0: k <= x) by lia.
    simpl (2 + x); transitivity (Ack x (Ack m n)). 
    +  apply Ack_mono_l; auto.
    +  transitivity (Ack x (Ack  x n)).
       *  apply Ack_n_mono_weak.
          destruct (Ack_properties x) as [H1 [H2 H3]].
          repeat split; auto.
          apply Ack_mono_l; lia.
       * apply L09.
Qed.


Lemma Ack_Sn_plus : forall n p, S n +  p < Ack (S n) p.
Proof.
  induction n.
  -  intro; rewrite Ack_1_n; lia.
  -  induction p.
   + rewrite Ack_S_0.
     specialize (IHn 1); lia.
   + rewrite Ack_S_S.
     assert   (Ack (S (S n)) p < Ack (S n) (Ack (S (S n)) p)).
     {
       destruct (Ack_properties (S n)) as [H [H0 H1]].
       apply H0.
     }
     eapply Lt.le_lt_trans with (2:= H).
     replace (S (S n) + S p) with (S (S (S n) + p)) by lia.
     apply IHp.
Qed.

(** A key step in the proof that Ack is not primitive recursive *)
(** To do: prove (exists n, forall x y,  Ack x y <= Ack n (x + y) . *)

Section Contrad.
  Variable n: nat.
  Hypothesis  Hn :  forall x y,  Ack x y <= Ack n (x + y) .

  Remark R01 : n <> 0.
  Proof.
    intro H;  subst; specialize (Hn 2 1).
    compute in Hn; lia.
  Qed.


  Remark R02: n <> 1.
  Proof. 
    intro H; subst; specialize (Hn 2 2).
    compute in Hn;  lia.
  Qed.

  Remark R03 : max 2 n = n.
  Proof.
    apply PeanoNat.Nat.max_r.
    case_eq  n; intro.
    -  destruct (R01 H).
    -  destruct n0.
       +  intro H; destruct (R02 H).
       + intro; subst. auto with arith.
  Qed.

  Remark R04 : Ack n (2 * n + 3) = Ack n (Ack 2 n).
  Proof.
    now rewrite Ack_2_n.
  Qed.
  
  Remark R05 : Ack n (2 * n + 3) <= Ack (n + 2) n.
  Proof.
    transitivity (Ack n (Ack 2 n)).
    -  now  rewrite  R04.
    - replace (n+2) with  (2 + max n 2).
      +  apply  Ack_Ack_le.
      + rewrite PeanoNat.Nat.add_comm;  now rewrite Max.max_comm, R03.
  Qed.  

  Remark R06 : Ack (n+ 2) n <= Ack n (2 * n + 2).
  Proof.
    specialize (Hn (n+2) n).
    replace (2* n + 2) with (n+2 + n) by lia;  auto.
  Qed.

  Remark R07 : Ack n (2 * n + 3) <= Ack n (2* n + 2).
  Proof.
    eapply Le.le_trans.
    - apply R05.
    - apply R06.
  Qed.


  Remark R08 :  Ack n (2* n + 2) < Ack n (2 * n + 3).
  Proof.
    destruct (Ack_properties n) as [H _]; apply H; lia.
  Qed.

  Lemma contrad : False.
  Proof.
    generalize R07, R08; intros; lia.
  Qed.

End Contrad.




