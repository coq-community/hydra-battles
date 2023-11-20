(** Cantor's pairing function 
    (Originally  Russel O'Connors [goedel] contrib  *)


Require Import Arith Coq.Lists.List Lia.
From hydras Require Import extEqualNat primRec.
From hydras Require Export Compat815 ssrnat_extracts.
Import PRNotations.
Import Nat.


(**  * Bijection from [nat * nat] to [nat] *)

(** ** Preliminary definitions *)

(** Sum of all natural numbers upto [n] *)

(* begin snippet sumToNDef:: no-out *)
Fixpoint sumToN (n : nat): nat :=
  match n with 
    0 => 0
  | S p => S p + sumToN p 
  end. 
(* end snippet sumToNDef *)

(* begin snippet sumToN1:: no-out *)
Lemma sumToN1 n : n <= sumToN n.
(* end snippet sumToN1 *)
Proof.
  induction n as [| n Hrecn]; [trivial |];
    simpl in |- *; apply le_n_S, Nat.le_add_r.
Qed.

(* begin snippet sumToN2:: no-out *)
Lemma sumToN2 b a :  a <= b -> sumToN a <= sumToN b.
(* end snippet sumToN2 *)
Proof.
  revert a; induction b as [| b Hrecb]; intros.
  - simpl in |- *; rewrite  (Nat.le_0_r a) in H; now subst. 
  - rewrite  Nat.lt_eq_cases in H; destruct H as [H | H].
    + transitivity (sumToN b).
      * apply Hrecb; auto.
        apply Compat815.lt_n_Sm_le; auto.
      * cbn in |- *; apply le_S; rewrite Nat.add_comm.
        apply le_add_r.
    + subst a; reflexivity.  
Qed.

(* begin snippet sumToNPR:: no-out *)
#[export] Instance sumToNIsPR : isPR 1 sumToN.
Proof.
  unfold sumToN in |- *.
  apply indIsPR with (f := fun x y : nat => S x + y).
  apply compose2_2IsPR
    with (f := fun x y : nat => S x)
         (g := fun x y : nat => y)
         (h := plus).
  - apply filter10IsPR, succIsPR.
  - apply pi2_2IsPR.
  - apply plusIsPR.
Qed.
(* end snippet sumToNPR *)

(** ** Definition and properties of [cPair] *)

(**  The [cPair] function defined below is slightly different 
     from the "usual" Cantor pairing function shown in  a big part 
     of the litterature (and Coq's standard library). 
      Since both versions are equivalent upto a swap of the 
      arguments [a] and [b], we still use  Russel O'Connors notations *)

(* begin snippet cPairDef *)
Definition cPair (a b : nat) := a + sumToN (a + b).

Compute cPair 4 0. 
(* end snippet cPairDef *)

(* begin snippet Compatibility:: no-out  *)
(** Usual definition (e.g. wikipedia) *)

 Definition xPair a b := b + sumToN ( b + a).

 Lemma xPairDef a b : xPair a b = cPair b a. 
 Proof.  reflexivity. Qed. 
(* end snippet Compatibility *)


(* begin snippet cPairIsPR:: no-out *)
#[export] Instance cPairIsPR : isPR 2 cPair.
Proof.
  unfold cPair; apply compose2_2IsPR
    with
    (f := fun x y : nat => x)
    (g := fun x y : nat => sumToN (x + y))
    (h := plus).
  - apply pi1_2IsPR.
  - apply compose2_1IsPR; [apply plusIsPR | apply sumToNIsPR].
  - apply plusIsPR.
Qed.
(* end snippet cPairIsPR *)

Section CPair_Injectivity.

  Remark cPairInjHelp :
    forall a b c d : nat, cPair a b = cPair c d -> a + b = c + d.
  Proof.
    assert (H: forall a b : nat, a < b -> a + sumToN a < sumToN b).
    {
      simple induction b.
      - intros H; elim (Nat.nlt_0_r _ H).
      -  intros n H H0; simpl in |- *.
         assert (H1: a <= n)
         by (apply Compat815.lt_n_Sm_le; assumption).
         rewrite Nat.lt_eq_cases in H1; destruct H1. 
        +  apply Nat.lt_trans with (sumToN n).
            * auto.
            * apply Compat815.le_lt_n_Sm.
              rewrite Nat.add_comm; apply le_add_r.
            +  rewrite H1.
               apply Nat.lt_succ_diag_r .
    }
    unfold cPair in |- *; 
    assert
      (H0: forall a b c d : nat,
          a <= c -> b <= d -> a + sumToN c = b + sumToN d -> c = d).
    { intros a b c d H0 H1 H2; induction (le_gt_cases c d).
      - induction (Compat815.le_lt_or_eq _ _ H3).
        + assert (H5: a + sumToN c < sumToN d).
          { apply Nat.le_lt_trans with (c + sumToN c); [| auto].
            now apply Nat.add_le_mono_r; auto. 
          }
          rewrite H2 in H5; elim (Compat815.lt_not_le _ _ H5).
          rewrite Nat.add_comm;apply le_add_r.
        + auto.
      - assert (H4: b + sumToN d < sumToN c).
      { apply Nat.le_lt_trans with (d + sumToN d).
        - apply Nat.add_le_mono_r; auto.
        - auto.
      }
      rewrite <- H2 in H4;  elim (Compat815.lt_not_le _ _ H4).
      rewrite add_comm; apply le_add_r.
    }
    intros; eapply H0.
    - apply Nat.le_add_r.
    - apply Nat.le_add_r.
    - auto.
  Qed.

  (* begin snippet cPairInj1:: no-out *)
  Lemma cPairInj1 a b c d: cPair a b = cPair c d -> a = c.
  (* end snippet cPairInj1 *)
  Proof.
    intro H; assert (H0: a + b = c + d)
      by (apply cPairInjHelp; auto).
    unfold cPair in H; rewrite (Nat.add_comm a) in H; 
      rewrite (Nat.add_comm c) in H.
    rewrite H0 in H; now rewrite Nat.add_cancel_l in H. 
  Qed.

  (* begin snippet cPairInj2:: no-out *)
  Lemma cPairInj2  a b c d : cPair a b = cPair c d -> b = d.
  (* end snippet cPairInj2 *)
  Proof.
    intro H;  assert (H0: a + b = c + d) by
      ( apply cPairInjHelp; auto ).
    assert (H1: a = c) by (eapply cPairInj1; apply H).
    rewrite H1 in H0; now rewrite Nat.add_cancel_l in H0. 
  Qed.

End CPair_Injectivity.

Section CPair_projections.

  (* @todo document boundedSearch *)

  (* begin snippet searchXY *)
  Let searchXY (a : nat) :=
        boundedSearch (fun a y : nat => ltBool a (sumToN y.+1)) a.
  (* end snippet searchXY *)

  (* begin snippet cPairPi12 *)
  Definition cPairPi1 (a : nat) := a - sumToN (searchXY a).
  Definition cPairPi2 (a : nat) := searchXY a - cPairPi1 a.
  (* end snippet cPairPi12 *)

Lemma cPairProjectionsHelp (a b: nat):
  b < sumToN a.+1 -> sumToN a <= b -> searchXY b = a.
Proof.
  intros H H0; unfold searchXY in |- *.
  induction (boundedSearch2 (fun b y : nat => ltBool b (sumToN y.+1)) b).
  - rewrite H1.
    induction (eq_nat_dec b a).
    + auto.
    + elim (ltBoolFalse b (sumToN a.+1)).
      * apply (boundedSearch1
                 (fun b y : nat => ltBool b (sumToN y.+1)) b).
        rewrite H1.
        destruct (Nat.lt_gt_cases b a) as [H2 _]; specialize (H2 b0);
          destruct H2 as [H2 | H2]. 
        -- rewrite Nat.lt_nge in H2. destruct H2. 
           apply Nat.le_trans with (sumToN a).
           apply sumToN1.
           auto.
        -- auto.
      * auto.
  - set (c := boundedSearch (fun b y : nat => ltBool b (sumToN y.+1 )) b) in *.
    induction (eq_nat_dec c a).
    + auto.
    + elim (ltBoolFalse b (sumToN a.+1)).
      apply (boundedSearch1 (fun b y : nat => ltBool b (sumToN y.+1)) b).
      fold c in |- *.
      rewrite lt_gt_cases in b0; destruct b0 as [H2 | H2]; [trivial|].
      rewrite Nat.le_ngt in H0; destruct H0.
      * apply Nat.lt_le_trans with (sumToN c.+1).
        -- apply ltBoolTrue.
           auto.
        -- assert (c.+1 <= a).
           { apply Compat815.lt_n_Sm_le.
             now rewrite <- Nat.succ_lt_mono.
           } apply sumToN2; auto.
      * assumption.
      * assumption.
Qed.

(* begin snippet cPairProjections:: no-out *)
Lemma cPairProjections a: cPair (cPairPi1 a) (cPairPi2 a) = a.
(* end snippet cPairProjections *)
Proof.
  revert a; assert (H: 
        forall a b : nat, b < sumToN a ->
                          cPair (cPairPi1 b) (cPairPi2 b) = b).
  { intros a b H; induction a as [| a Hreca].
    - simpl in H; elim (Nat.nlt_0_r _ H).
    - induction (Nat.le_gt_cases (sumToN a) b).
     assert (searchXY b = a)
       by (apply cPairProjectionsHelp; auto).
      unfold cPair in |- *.
      replace (cPairPi1 b + cPairPi2 b) with a.
      unfold cPairPi1 in |- *.
      rewrite H1; now rewrite Nat.sub_add.
      unfold cPairPi2 in |- *.
      rewrite H1, Nat.add_comm,  Nat.sub_add.
      auto.
      unfold cPairPi1 in |- *.
      rewrite H1.
      simpl in H.
      erewrite Nat.add_le_mono_l.
      rewrite Nat.add_comm, sub_add. 

      apply Compat815.lt_n_Sm_le; auto.
      rewrite add_comm;  apply H; auto.
      auto.
      apply Hreca.
      auto.
  }
  intros a; apply H with (S a).
  apply Nat.lt_le_trans with (S a).
  apply Nat.lt_succ_diag_r .
  apply sumToN1.
Qed.

#[local] Instance searchXYIsPR : isPR 1 searchXY.
Proof.
  unfold searchXY in |- *.
  apply boundSearchIsPR with (P := fun a y : nat => ltBool a (sumToN (S y))).
  unfold isPRrel in |- *.
  apply
    compose2_2IsPR
    with
    (h := charFunction 2 ltBool)
    (f := fun a y : nat => a)
    (g := fun a y : nat => sumToN (S y)).
  - apply pi1_2IsPR.
  - apply filter01IsPR with (g := fun y : nat => sumToN (S y)).
    apply compose1_1IsPR.
    + apply succIsPR.
    + apply sumToNIsPR.
 - apply ltIsPR.
Qed.

(* begin snippet  cPairPi1IsPR:: no-out *)
#[export] Instance cPairPi1IsPR : isPR 1 cPairPi1.
(* end snippet  cPairPi1IsPR *)
Proof.
  unfold cPairPi1 in |- *.
  apply compose1_2IsPR 
  with
    (g := minus)
    (f := fun x : nat => x)
    (f' := fun a : nat => sumToN (searchXY a)).
  - apply idIsPR.
  - apply compose1_1IsPR.
    + apply searchXYIsPR.
    + apply sumToNIsPR.
  - apply minusIsPR.
Qed.

(* begin snippet  cPairProjections1:: no-out *)
Lemma cPairProjections1 (a b : nat): cPairPi1 (cPair a b) = a.
(* end snippet  cPairProjections1 *)
Proof.
  unfold cPair, cPairPi1  in |- *.
  replace (searchXY (a + sumToN (a + b))) with (a + b).
  now rewrite Nat.add_sub.
  symmetry  in |- *; apply cPairProjectionsHelp.
  - simpl in |- *; apply Nat.lt_succ_r.
    apply Nat.add_le_mono_r, Nat.le_add_r.
  - rewrite (Nat.add_comm a (sumToN (a + b))); apply le_add_r.
Qed.

(* begin snippet  cPairProjections2:: no-out *)
Lemma cPairProjections2 (a b : nat): cPairPi2 (cPair a b) = b.
(* end snippet  cPairProjections2 *)
Proof.
  unfold cPairPi2 in |- *; rewrite cPairProjections1; unfold cPair in |- *.
  replace (searchXY (a + sumToN (a + b))) with (a + b).
  - rewrite Nat.add_comm; apply Nat.add_sub .
  - symmetry  in |- *; apply cPairProjectionsHelp; simpl in |- *.
    + rewrite Nat.lt_succ_r; apply Nat.add_le_mono_r, Nat.le_add_r.
    + rewrite (Nat.add_comm a (sumToN (a + b)));apply le_add_r.
Qed.


(* begin snippet  cPairPi2IsPR:: no-out *)
#[export] Instance cPairPi2IsPR : isPR 1 cPairPi2.
(* end snippet  cPairPi2IsPR *)
Proof.
  unfold cPairPi2 in |- *.
  apply compose1_2IsPR with (g := minus) (f := searchXY) (f' := cPairPi1).
  - apply searchXYIsPR.
  - apply cPairPi1IsPR.
  - apply minusIsPR.
Qed.


End CPair_projections.

Section CPair_Order.

  (* begin snippet cPairLe1:: no-out *)
  Lemma cPairLe1 (a b : nat) : a <= cPair a b.
  (* end snippet cPairLe1 *)
  Proof. unfold cPair in |- *; apply Nat.le_add_r. Qed.


  (* begin snippet cPairLe1A:: no-out *)
  Lemma cPairLe1A (a : nat) : cPairPi1 a <= a.
  (* end snippet cPairLe1A *)
  Proof. 
    transitivity (cPair (cPairPi1 a) (cPairPi2 a)).
    - apply cPairLe1.
    - rewrite cPairProjections; apply le_n.
  Qed.

  (* begin snippet cPairLe2:: no-out *)
  Lemma cPairLe2 (a b : nat) : b <= cPair a b.
  (* end snippet cPairLe2 *)
  Proof.
    unfold cPair in |- *; eapply Nat.le_trans with (b + a). 
    - apply Nat.le_add_r.
    - rewrite (Nat.add_comm b a); transitivity (sumToN (a + b)).
      + apply sumToN1.
      + rewrite (Nat.add_comm _ (sumToN (a + b))); apply le_add_r.
  Qed.

  (* begin snippet cPairLe2A:: no-out *)
  Lemma cPairLe2A (a: nat): cPairPi2 a <= a.
  (* end snippet cPairLe2A *)
  Proof.
    transitivity (cPair (cPairPi1 a) (cPairPi2 a)).
    - apply cPairLe2.
    - rewrite cPairProjections; apply le_n.
  Qed.

  (* begin snippet cPairLe3:: no-out *)
  Lemma cPairLe3 (a b c d : nat): a <= b -> c <= d -> cPair a c <= cPair b d.
  (* end snippet cPairLe3 *)
  Proof.
    intros H H0; unfold cPair in |- *;
      transitivity (a + sumToN (b + d)).
    - apply Nat.add_le_mono_l, sumToN2; transitivity (a + d).
      + now apply Nat.add_le_mono_l.
      + now apply Nat.add_le_mono_r.
    - now apply Nat.add_le_mono_r.
  Qed.

  (* begin snippet cPairLt1:: no-out *)
  Lemma cPairLt1 (a b : nat): a < cPair a (S b).
  (* end snippet cPairLt1 *)
  Proof.
    unfold cPair in |- *.
    rewrite (Nat.add_comm a (S b)); simpl in |- *.
    rewrite Nat.add_comm; simpl in |- *; rewrite Nat.add_comm.
    apply le_n_S, Nat.le_add_r.
  Qed.

  (* begin snippet cPairLt2:: no-out *)
  Lemma cPairLt2 (a b : nat): b < cPair (S a) b.
  (* end snippet cPairLt2 *)
  Proof.
    unfold cPair in |- *; simpl in |- *;
      unfold lt in |- *; apply le_n_S.
    eapply Nat.le_trans.
    - apply Nat.le_add_r. 
    - rewrite Nat.add_comm at 1. 
      apply Nat.add_le_mono_l.
      apply le_S.
      eapply Nat.le_trans.
      + apply Nat.le_add_r.
      + rewrite Nat.add_comm; apply Nat.le_add_r.
  Qed.

End CPair_Order.

Require Import Extraction. 
Section code_nat_list.

(* begin snippet codeListDef:: no-out *)
Fixpoint codeList (l : list nat) : nat :=
  match l with
  | nil => 0
  | n :: l' => S (cPair n (codeList l'))
  end.
Compute codeList (3::1::nil). 
Compute codeList (2::3::1::nil). 
(* end snippet codeListDef *)

(* begin snippet codeListInj:: no-out *)
Lemma codeListInj (l m : list nat): codeList l = codeList m -> l = m.
Proof.
  (* ... *)
(* end snippet codeListInj *)

  revert m; induction l as [| a l Hrecl].
  - intros m H; destruct m as [| n l].
   + reflexivity.
   + discriminate H.
  - intros m H; destruct m as [| n l0].
    + discriminate H.
    + (* begin snippet codeListInja:: no-in unfold *)
      simpl in H.
      (* end snippet codeListInja *) replace n with a.
      * rewrite (Hrecl l0); [reflexivity |].
        eapply cPairInj2; apply eq_add_S, H. 
      * eapply cPairInj1; apply eq_add_S, H.
Qed.


(* begin snippet codeNthDef:: no-out  *)
Definition codeNth (n m:nat) : nat :=
  let X := nat_rec (fun _ : nat => nat)
             m
             (fun _ Hrecn : nat => cPairPi2 (pred Hrecn)) n
  in cPairPi1 (pred X).
(* end snippet codeNthDef *)




(** drops [n] first elements from [l] *)
Let drop (n : nat) : forall (l : list nat), list nat.
Proof.
  induction n as [| n Hrecn].
  - exact (fun l => l).
  - intros l; apply Hrecn; destruct l.
   + exact (nil (A:=nat)).
   + exact l.
Defined.

(* begin snippet codeNthCorrect:: no-out *)
Lemma codeNthCorrect :
  forall (n : nat) (l : list nat), codeNth n (codeList l) = nth n l 0.
(* end snippet codeNthCorrect *)
Proof.
  unfold codeNth in |- *.
  set
    (A :=
       fun l : list nat => match l with
                           | nil => nil (A:=nat)
                           | _ :: l0 => l0
                           end) in *.
  assert (H: forall l : list nat,
             cPairPi2 (pred (codeList l)) = codeList (A l)).
  { destruct l; simpl in |- *.
    apply (cPairProjections2 0 0).
    apply cPairProjections2.
  }
  assert
    (H0: forall (n : nat) (l : list nat),
        nat_rec (fun _ : nat => nat) (codeList l)
          (fun _ Hrecn : nat => cPairPi2 (pred Hrecn)) n = 
          codeList (drop n l)).
  {
    simple induction n; simpl in |- *.
    reflexivity.
    intros n0 H0 l; rewrite H0, H. 
    unfold A in |- *; clear H0; revert l. 
    induction n0 as [| n0 Hrecn0]; simpl in |- *; intros.
    - reflexivity.
    - destruct l.
      + apply (Hrecn0 nil).
      + apply Hrecn0.
  }
  intros n l.
  replace (nth n l 0) with match drop n l with
                           | nil => 0
                           | a :: _ => a
                           end.  
  rewrite H0; destruct (drop n l).
  + simpl in |- *; apply (cPairProjections1 0 0).
  + simpl in |- *;  apply cPairProjections1.
  + revert l; induction n as [| n Hrecn].
   * destruct l; reflexivity.
   * destruct l.
    -- simpl in Hrecn; destruct n; apply (Hrecn nil).
    -- simpl in |- *; auto.
Qed.

(* begin snippet codeNthIsPR:: no-out *)
#[export] Instance codeNthIsPR : isPR 2 codeNth.
(* end snippet codeNthIsPR *)
Proof.
  unfold codeNth in |- *; apply compose2_1IsPR
    with
    (g := fun x : nat => cPairPi1 (pred x))
    (f := fun n m : nat =>
            nat_rec (fun _ : nat => nat) m
              (fun _ Hrecn : nat => cPairPi2 (pred Hrecn)) n).
  - apply ind1ParamIsPR
    with
    (g := fun m : nat => m)
    (f := fun _ Hrecn m : nat => cPairPi2 (pred Hrecn)).
    + apply filter010IsPR with (g := fun x : nat => cPairPi2 (pred x)).
      apply compose1_1IsPR.
      * apply predIsPR.
      * apply cPairPi2IsPR.
    + apply idIsPR.
  - apply compose1_1IsPR.
    + apply predIsPR.
    + apply cPairPi1IsPR.
Qed.

End code_nat_list.

Extraction codeNth.
Print codeNth.

Section Strong_Recursion.
(* begin snippet evalStrongRecDef *)
Definition evalStrongRecHelp (n : nat) (f : naryFunc n.+2) :
  naryFunc n.+1 :=
  evalPrimRecFunc n (evalComposeFunc n 0 (Vector.nil _) (codeList nil))
    (evalComposeFunc n.+2 2
       (Vector.cons _ f _
          (Vector.cons _ (evalProjFunc n.+2 n
                            (Nat.lt_lt_succ_r _ _
                               (Nat.lt_succ_diag_r  _))) _
             (Vector.nil _))) 
       (fun a b : nat => S (cPair a b))).

Definition evalStrongRec (n : nat) (f : naryFunc n.+2):
  naryFunc n.+1 :=
  evalComposeFunc n.+1 1
    (Vector.cons _
       (fun z : nat => evalStrongRecHelp n f z.+1) _ (Vector.nil _))
    (fun z : nat => cPairPi1 z.-1).
(* end snippet evalStrongRecDef *)

(* begin snippet evalStrongRecPR:: no-out *)
#[export] Instance
 evalStrongRecIsPR (n : nat) (f : naryFunc n.+2):
  isPR _  f -> isPR _ (evalStrongRec n f).
(* end snippet evalStrongRecPR *)
Proof.
  intros; unfold evalStrongRec, evalStrongRecHelp in |- *.
  fold (naryFunc n.+1) in |- *.
  set
    (A :=
       evalPrimRecFunc n
         (evalComposeFunc n 0 (Vector.nil (naryFunc n)) (codeList nil))
         (evalComposeFunc (S (S n)) 2
            (Vector.cons (naryFunc (S (S n))) f 1
               (Vector.cons (naryFunc (S (S n)))
                  (evalProjFunc (S (S n)) n
                     (Nat.lt_lt_succ_r n (S n)
                        (Nat.lt_succ_diag_r  n))) 0
                  (Vector.nil (naryFunc (S (S n))))))
            (fun a b : nat => S (cPair a b))))
    in *.
  assert (H0: isPR (S n) A).
  { unfold A in |- *.
    assert (isPR 2 (fun a b : nat => S (cPair a b))).
    { apply compose2_1IsPR.
      apply cPairIsPR.
      apply succIsPR.
    }
    assert (H1: isPR 1 (fun z : nat => cPairPi1 (pred z))).
    { apply compose1_1IsPR.
      apply predIsPR.
      apply cPairPi1IsPR.
    }
    induction H as (x, p).
    induction H0 as (x0, p0).
    induction H1 as (x1, p1).
    exists
      (primRecFunc n (PRcomp zeroFunc (PRnil _))
       (PRcomp x0 
            [ x ;  projFunc n.+2 n
                              (Nat.lt_lt_succ_r n n.+1
                                 (Nat.lt_succ_diag_r n))]))%pr.
    apply
      extEqualTrans
      with
      (evalPrimRecFunc n (evalComposeFunc n 0 (Vector.nil _) 0)
         (evalComposeFunc n.+2 2
            (Vector.cons _ (evalPrimRec _ x) _
               (Vector.cons _ (evalProjFunc n.+2 n
                                 (Nat.lt_lt_succ_r n n.+1
                                    (Nat.lt_succ_diag_r  n))) _
                  (Vector.nil _))) (evalPrimRec _ x0))).
    apply extEqualRefl.
    apply extEqualPrimRec.
    simpl in |- *.
    apply extEqualRefl.
    apply extEqualCompose.
    unfold extEqualVector, extEqualVectorGeneral, Vector.t_rect.
    repeat split; auto.
    apply extEqualRefl.
    auto.
  }
  assert (H1: isPR n.+1 (fun z : nat => A z.+1)).
  { apply compose1_NIsPR; auto.
    apply succIsPR.
  }
  clear H0; assert (H0: isPR 1 (fun z : nat => cPairPi1 z.-1)).
  { apply compose1_1IsPR.
    apply predIsPR.
    apply cPairPi1IsPR.
  }
  destruct H0 as [x p]; destruct H1 as [x0 p0].
  exists (PRcomp x [x0])%pr.
  simpl; fold (naryFunc n); intros c; apply extEqualCompose.
  unfold extEqualVector in |- *.
  simpl in |- *; repeat split.
  - apply (p0 c).
  -  trivial.
Qed.

(* begin snippet computeEvalStrongRecHelp:: no-out *)
Lemma computeEvalStrongRecHelp :
  forall (n : nat) (f : naryFunc n.+2) (c : nat),
    evalStrongRecHelp n f c.+1 =
      compose2 n (evalStrongRecHelp n f c)
        (fun a0 : nat =>
           evalComposeFunc n 2
             (Vector.cons (naryFunc n) (f c a0) 1
                (Vector.cons (naryFunc n) (evalConstFunc n a0) 0
                   (Vector.nil (naryFunc n))))
             (fun a1 b0 : nat => S (cPair a1 b0))).
(* end snippet computeEvalStrongRecHelp:: no-out *)
Proof.
  intros n f c; unfold evalStrongRecHelp at 1 in |- *; simpl in |- *.
  fold (naryFunc n) in |- *.
  induction (eq_nat_dec n n.+1).
  - destruct (neq_succ_diag_r n a).
  - induction (eq_nat_dec n n).
    + replace
        (evalPrimRecFunc n
           (evalComposeFunc n 0 (Vector.nil (naryFunc n)) 0)
           (fun a0 a1 : nat =>
              evalComposeFunc n 2
                (Vector.cons (naryFunc n) (f a0 a1) 1
                   (Vector.cons (naryFunc n)
                      (evalConstFunc n a1) 0 (Vector.nil (naryFunc n))))
                (fun a2 b0 : nat => (cPair a2 b0).+1)) c)
        with
        (evalStrongRecHelp n f c).
      reflexivity.
      unfold evalStrongRecHelp at 1 in |- *.
      simpl in |- *.
      fold (naryFunc n) in |- *.
      induction (eq_nat_dec n n.+1).
      elim b; auto.
      induction (eq_nat_dec n n).
      * reflexivity.
      * elim b1; auto.
    + elim b0; auto.
Qed.


Fixpoint listValues  (f : naryFunc 2) (n : nat) : list nat :=
  match n with
    0 => nil
  | S m => evalStrongRec _ f m :: listValues f m
  end.


Lemma evalStrongRecHelp1 :
 forall (f : naryFunc 2) (n m : nat),
   m < n ->
   codeNth (n - m.+1) (evalStrongRecHelp _ f n) = evalStrongRec _ f m.
Proof.
  assert
    (H: forall (f : naryFunc 2) (n : nat),
        evalStrongRecHelp _ f n = codeList (listValues f n)).
  {
    intros f n; induction n as [| n Hrecn].
    - simpl in |- *; unfold evalStrongRecHelp in |- *; simpl in |- *.
      reflexivity.
    - unfold evalStrongRecHelp in |- *; simpl in |- *; 
        unfold evalStrongRecHelp in Hrecn; simpl in Hrecn; rewrite Hrecn.
      unfold evalStrongRec in |- *; simpl in |- *.
      now rewrite cPairProjections1, Hrecn.
  }
  intros f n m H0; rewrite H, codeNthCorrect.
  induction n as [| n Hrecn].
   - elim (Nat.nlt_0_r _ H0).
   - induction (Compat815.le_lt_or_eq _ _ H0).
     rewrite Nat.sub_succ_l; simpl in |- *.
     rewrite Hrecn.
     reflexivity.
     apply Nat.succ_lt_mono; auto.
     apply Compat815.lt_n_Sm_le; auto.
     inversion H1.
     rewrite  Nat.sub_diag; reflexivity. 
Qed.

Lemma evalStrongRecHelpParam :
  forall (a n c : nat) (f : naryFunc a.+3),
    extEqual a (evalStrongRecHelp (S a) f n c)
      (evalStrongRecHelp a (fun x y : nat => f x y c) n).
Proof.
  intros a n c f; unfold evalStrongRecHelp in |- *.
  eapply extEqualTrans.
  - apply extEqualSym.
    apply evalPrimRecParam.
  - assert
    (H: extEqual a.+1
       (evalPrimRecFunc a
          (evalComposeFunc a.+1 0
             (Vector.nil (naryFunc a.+1)) (codeList nil) c)
          (fun x y : nat =>
             evalComposeFunc a.+3 2
               (Vector.cons (naryFunc a.+3) f 1
                  (Vector.cons _
                     (evalProjFunc _ a.+1
                        (Nat.lt_lt_succ_r a.+1 a.+2
                           (Nat.lt_succ_diag_r  a.+1))) 0
                     (Vector.nil (naryFunc a.+3))))
               (fun a0 b : nat => S (cPair a0 b)) x y c))
       (evalPrimRecFunc a
          (evalComposeFunc a 0 (Vector.nil (naryFunc a)) (codeList nil))
          (evalComposeFunc a.+2 2
             (Vector.cons (naryFunc a.+2) (fun x y : nat => f x y c) 1
                (Vector.cons (naryFunc a.+2)
                   (evalProjFunc _ a (Nat.lt_lt_succ_r a a.+1
                                                (Nat.lt_succ_diag_r a))) 0
                   (Vector.nil (naryFunc a.+2))))
             (fun a0 b : nat => S (cPair a0 b))))).
    { apply
        (extEqualPrimRec a
           (evalComposeFunc a.+1 0
              (Vector.nil (naryFunc a.+1))
              (codeList nil) c)).
      simpl in |- *; apply extEqualRefl.
      - simpl in |- *; fold (naryFunc a) in |- *.
        induction
          (sumbool_rec
             (fun _ : {a = a.+1} + {a <> a.+1} =>
                {a.+1 = a.+2} + {a.+1 <> a.+2})
             (fun a0 : a = a.+1 => left (a.+1 <> a.+2) (f_equal S a0 ))
             (fun b : a <> S a => right (a.+1 = a.+2) (not_eq_S a a.+1 b))
             (eq_nat_dec a a.+1)).
        + elim (Compat815.lt_not_le a.+1 a.+2).
          * apply Nat.lt_succ_diag_r.
          * rewrite <- a0; auto.
        + induction
            (sumbool_rec (fun _ : {a = a} + {a <> a} =>
                            {a.+1 = a.+1} + {a.+1 <> a.+1})
               (fun a0 : a = a => left (a.+1 <> a.+1) (f_equal S a0))
               (fun b0 : a <> a => right (a.+1 = a.+1) (not_eq_S a a b0)) 
               (eq_nat_dec a a)).
            induction (eq_nat_dec a a.+1).
          * elim (Compat815.lt_not_le a a.+1).
            -- apply Nat.lt_succ_diag_r.
            -- rewrite <- a1; auto.
          * induction (eq_nat_dec a a).
            -- intros;  apply extEqualRefl.
            -- elim b1; auto.
          * elim b0; auto.
    }
    apply (H n).
Qed.

Lemma evalStrongRecHelp2 :
  forall (a : nat) (f : naryFunc a.+2) (n m : nat),
    m < n ->
    extEqual _
      (evalComposeFunc _ 1
         (Vector.cons _ (evalStrongRecHelp _ f n) 0 (Vector.nil _))
         (fun b : nat => codeNth (n - m.+1) b)) (evalStrongRec _ f m).
Proof.
  intro a; fold (naryFunc a) in |- *.
  induction a as [| a Hreca].
  - simpl in |- *.
    apply evalStrongRecHelp1.
  - simpl in |- *.
  intros f n m H c; fold (naryFunc a) in |- *.
  set (g := fun x y : nat => f x y c) in *.
  assert
    (H0: extEqual a
       (evalComposeFunc a 1
          (Vector.cons (naryFunc a)
             (evalStrongRecHelp a g n) 0 (Vector.nil (naryFunc a)))
          (fun b : nat => codeNth (n - S m) b)) (evalStrongRec a g m))
      by (apply Hreca; auto).
  unfold g in H0; clear g Hreca.
  apply extEqualTrans with (evalStrongRec a (fun x y : nat => f x y c) m).
  + apply
    extEqualTrans
    with
    (evalComposeFunc a 1
       (Vector.cons (naryFunc a)
          (evalStrongRecHelp a (fun x y : nat => f x y c) n)
          0 (Vector.nil (naryFunc a)))
       (fun b : nat => codeNth (n - S m) b)).
    * apply extEqualCompose; unfold extEqualVector in |- *.
      simpl in |- *; repeat split.
      apply evalStrongRecHelpParam.
      apply extEqualRefl.
    * apply H0.
  + unfold evalStrongRec in |- *; simpl in |- *.
    fold (naryFunc a) in |- *; apply extEqualCompose.
    unfold extEqualVector in |- *; simpl in |- *; repeat split.
    * apply extEqualSym.
      apply evalStrongRecHelpParam.
    * apply extEqualRefl.
Qed.

#[export] Instance  callIsPR (g : nat -> nat) (H : isPR 1 g) :
   isPR 2 (fun a recs : nat => codeNth (a - S (g a)) recs).
Proof.
  apply  compose2_2IsPR
    with (f := fun a recs : nat => a - S (g a))
         (g := fun a recs : nat => recs).
  - apply filter10IsPR with (g := fun a : nat => a - S (g a)).
    apply compose1_2IsPR with
      (f := fun a : nat => a)
      (f' := fun a : nat => S (g a)).
    + apply idIsPR.
    + apply compose1_1IsPR.
      * assumption.
      * apply succIsPR.
    + apply minusIsPR.
  - apply pi2_2IsPR.
  - apply codeNthIsPR.
Qed.

End Strong_Recursion.

#[export] Instance div2IsPR : isPR 1 div2.
Proof.
  assert
    (H: isPR 1
          (evalStrongRec 0
             (fun n recs : nat =>
                switchPR n
                  (switchPR n.-1
                     (codeNth (n - (n.-2).+1) recs).+1
                     0)
                  0))).
  { apply evalStrongRecIsPR.
    assert (H : isPR 2 (fun n recs : nat => 0)).
    { exists (PRcomp zeroFunc (PRnil _))%pr; intros ?; cbn; now reflexivity.
    }
    apply compose2_3IsPR with
    (f1 := fun n recs : nat => n)
    (f2 := fun n recs : nat =>
             switchPR n.-1
               (S (codeNth (n - (n.-2).+1) recs)) 0)
    (f3 := fun n recs : nat => 0).
    - apply pi1_2IsPR.
    - apply compose2_3IsPR with
        (f1 := fun n recs : nat => n.-1)
        (f2 := fun n recs : nat =>
                 S (codeNth (n - (n.-2).+1) recs))
        (f3 := fun n recs : nat => 0).
      + apply filter10IsPR.
        apply predIsPR.
      + apply compose2_1IsPR with
            (f := fun n recs : nat =>
                    codeNth (n - S n.-2) recs).
        * apply compose2_2IsPR with
            (f := fun n recs : nat => n - S n.-2)
            (g := fun n recs : nat => recs).
          apply filter10IsPR with
            (g := fun n : nat => n - S n.-2).
          apply compose1_2IsPR with
            (f := fun n : nat => n)
            (f' := fun n : nat => S n.-2).
          apply idIsPR.
          apply compose1_1IsPR with
            (f := fun n : nat => n.-2).
          apply compose1_1IsPR; apply predIsPR.
          apply succIsPR.
          apply minusIsPR.
          apply pi2_2IsPR.
          apply codeNthIsPR.
        * apply succIsPR.
      + auto.
      + apply switchIsPR.
    - auto.
    - apply switchIsPR.
  }
  destruct H as [x p]; exists x.
  eapply extEqualTrans.
  - apply p.
  - clear p x; simpl in |- *; intro c.
    set  (f := fun n recs : nat =>
                 switchPR n (switchPR n.-1
                               (S (codeNth (n - S n.-2)
                                     recs)) 0)  0) in *. 
    elim c using Compat815.ind_0_1_SS.
    + unfold evalStrongRec in |- *; simpl in |- *; auto.
    + unfold evalStrongRec in |- *; simpl in |- *;
        apply cPairProjections1.
    + intros n H; unfold evalStrongRec, evalComposeFunc,
        evalOneParamList 
        in |- *.
      rewrite computeEvalStrongRecHelp.
      unfold f at 2 in |- *;
        set (A := n.+2 - S (n.+2.-2)).
      simpl in |- *; rewrite cPairProjections1; apply eq_S.
      rewrite <- H; unfold A in |- *; apply evalStrongRecHelp1.
      auto.
Qed.

Lemma cPairLemma1 :
  forall a b : nat, (a + b) * S (a + b) + 2 * a = 2 * cPair a b.
Proof. 
  intros a b. unfold cPair in |- *.
   assert (2 * sumToN (a + b) = (a + b) * S (a + b)) by
     (induction (a + b); simpl in |- *; lia).
    lia.
Qed. 

(** abbreviations a la Lisp (to improve) *)

Module LispAbbreviations.
  #[global] Notation car := cPairPi1. 
  #[global] Notation cdr  := cPairPi2. 
  #[global] Notation caar n := (cPairPi1 (cPairPi1 n)). 
  #[global] Notation cadr n := (cPairPi1 (cPairPi2 n)). 
  #[global] Notation caddr n := (cPairPi1 (cPairPi2 (cPairPi2 n))). 
 
  #[global] Notation cddr n := (cPairPi2 (cPairPi2 n)). 
  #[global] Notation cdddr n := (cPairPi2 (cPairPi2 (cPairPi2 n))). 
  #[global] Notation cddddr n := 
    (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n)))).

End LispAbbreviations. 


(** ** Triples 
   (moved from codeSubFormula.v)
*)

Definition cTriple (a b c : nat) : nat := cPair a (cPair b c).

Definition cTriplePi1 (n : nat) : nat := cPairPi1 n.

Definition cTriplePi2 (n : nat) : nat := cPairPi1  (cPairPi2 n).

Definition cTriplePi3 (n : nat) : nat := cPairPi2 (cPairPi2 n).

#[export] Instance cTripleIsPR : isPR 3 cTriple.
Proof.
  unfold cTriple; apply compose3_2IsPR with
    (g := cPair)
    (f1 := fun a b c : nat => a)
    (f2 := fun a b c : nat => cPair b c).
  - apply pi1_3IsPR. 
  - apply filter011IsPR with (g := fun b c : nat => cPair b c).
    apply cPairIsPR.
  - apply cPairIsPR.
Qed.

#[export] Instance cTriplePi1IsPR : isPR 1 cTriplePi1.
Proof. apply cPairPi1IsPR. Qed.

#[export] Instance cTriplePi2IsPR : isPR 1 cTriplePi2.
Proof.
  unfold cTriplePi2; apply compose1_1IsPR.
  - apply cPairPi2IsPR.
  - apply cPairPi1IsPR.
Qed.

#[export] Instance cTriplePi3IsPR : isPR 1 cTriplePi3.
Proof.
  unfold cTriplePi3; apply compose1_1IsPR; apply cPairPi2IsPR.
Qed.

Lemma cTripleProj1 (a b c : nat) :  cTriplePi1 (cTriple a b c) = a.
Proof.  unfold cTriplePi1, cTriple; apply cPairProjections1. Qed.

Lemma cTripleProj2 (a b c : nat) : cTriplePi2 (cTriple a b c) = b.
Proof. 
  unfold cTriplePi2, cTriple; rewrite cPairProjections2; 
    apply cPairProjections1.
Qed.

Lemma cTripleProj3 (a b c : nat) : cTriplePi3 (cTriple a b c) = c.
Proof. 
  unfold cTriplePi3, cTriple; rewrite cPairProjections2.
  apply cPairProjections2.
Qed.

Lemma cTripleProj (a: nat) :
 cTriple (cTriplePi1 a) (cTriplePi2 a) (cTriplePi3 a) = a.
Proof.
unfold cTriple, cTriplePi1, cTriplePi2, cTriplePi3; 
  repeat rewrite cPairProjections; reflexivity.
Qed.


