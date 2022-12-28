(** Cantor's pairing function 
    (Originally  Russel O'Connors [goedel] contrib  *)


Require Import Arith Coq.Lists.List .
From hydras Require Import extEqualNat primRec.
From hydras Require Import Compat815.
Import Nat.


(**  * Bijection from [nat * nat] to [nat] *)

(** ** Preliminary definitions *)

(** Sum of all natural numbers upto [n] *)

(* begin snippet sumToNDef:: no-out *)
Definition sumToN (n : nat) :=
  nat_rec (fun _ => nat) 0 (fun x y : nat => S x + y) n.
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
Lemma sumToNIsPR : isPR 1 sumToN.
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
      rguments [a] and [b], we still use  Russel O'Connors notations *)

(* begin snippet cPairDef *)
Definition cPair (a b : nat) := a + sumToN (a + b).

Compute cPair 4 0. 
(* end snippet cPairDef *)

(* begin snippet cPairIsPR:: no-out *)
Lemma cPairIsPR : isPR 2 cPair.
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
        boundedSearch (fun a y : nat => ltBool a (sumToN (S y))) a.
  (* end snippet searchXY *)

  (* begin snippet cPairPi12 *)
  Definition cPairPi1 (a : nat) := a - sumToN (searchXY a).
  Definition cPairPi2 (a : nat) := searchXY a - cPairPi1 a.
  (* end snippet cPairPi12 *)

Lemma cPairProjectionsHelp (a b: nat):
  b < sumToN (S a) -> sumToN a <= b -> searchXY b = a.
Proof.
  intros H H0; unfold searchXY in |- *.
  induction (boundedSearch2 (fun b y : nat => ltBool b (sumToN (S y))) b).
  - rewrite H1.
    induction (eq_nat_dec b a).
    + auto.
    + elim (ltBoolFalse b (sumToN (S a))).
      * apply (boundedSearch1
                 (fun b y : nat => ltBool b (sumToN (S y))) b).
        rewrite H1.
        destruct (Nat.lt_gt_cases b a) as [H2 _]; specialize (H2 b0);
          destruct H2 as [H2 | H2]. 
        -- rewrite Nat.lt_nge in H2. destruct H2. 
           apply Nat.le_trans with (sumToN a).
           apply sumToN1.
           auto.
        -- auto.
      * auto.
  - set (c := boundedSearch (fun b y : nat => ltBool b (sumToN (S y))) b) in *.
    induction (eq_nat_dec c a).
    + auto.
    + elim (ltBoolFalse b (sumToN (S a))).
      apply (boundedSearch1 (fun b y : nat => ltBool b (sumToN (S y))) b).
      fold c in |- *.
      rewrite lt_gt_cases in b0; destruct b0 as [H2 | H2]; [trivial|].
      rewrite Nat.le_ngt in H0; destruct H0.
      * apply Nat.lt_le_trans with (sumToN (S c)).
        -- apply ltBoolTrue.
           auto.
        -- assert (S c <= a).
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

Remark searchXYIsPR : isPR 1 searchXY.
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
Lemma cPairPi1IsPR : isPR 1 cPairPi1.
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
Lemma cPairPi2IsPR : isPR 1 cPairPi2.
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
  Lemma cPairLe2 ( a b : nat) : b <= cPair a b.
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
Lemma codeNthIsPR : isPR 2 codeNth.
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
Definition evalStrongRecHelp (n : nat) (f : naryFunc (S (S n))) :
  naryFunc (S n) :=
  evalPrimRecFunc n (evalComposeFunc n 0 (Vector.nil _) (codeList nil))
    (evalComposeFunc (S (S n)) 2
       (Vector.cons _ f _
          (Vector.cons _ (evalProjFunc (S (S n)) n
                            (Nat.lt_lt_succ_r _ _
                               (Nat.lt_succ_diag_r  _))) _
             (Vector.nil _))) 
       (fun a b : nat => S (cPair a b))).

Definition evalStrongRec (n : nat) (f : naryFunc (S (S n))) :
  naryFunc (S n) :=
  evalComposeFunc (S n) 1
    (Vector.cons _
       (fun z : nat => evalStrongRecHelp n f (S z)) _ (Vector.nil _))
    (fun z : nat => cPairPi1 (pred z)).
(* end snippet evalStrongRecDef *)

(* begin snippet evalStrongRecPR:: no-out *)
Lemma evalStrongRecIsPR (n : nat) (f : naryFunc (S (S n))) :
  isPR (S (S n))  f -> isPR (S n) (evalStrongRec n f).
(* end snippet evalStrongRecPR *)
Proof.
  intros; unfold evalStrongRec, evalStrongRecHelp in |- *.
  fold (naryFunc (S n)) in |- *.
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
      (primRecFunc n (composeFunc n 0 (PRnil _) zeroFunc)
         (composeFunc (S (S n)) 2
            (PRcons _ _ x
               (PRcons _ _ (projFunc (S (S n)) n
                              (Nat.lt_lt_succ_r n (S n)
                                 (Nat.lt_succ_diag_r  n)))
                  (PRnil _))) x0)).
    apply
      extEqualTrans
      with
      (evalPrimRecFunc n (evalComposeFunc n 0 (Vector.nil _) 0)
         (evalComposeFunc (S (S n)) 2
            (Vector.cons _ (evalPrimRec _ x) _
               (Vector.cons _ (evalProjFunc (S (S n)) n
                                 (Nat.lt_lt_succ_r n (S n)
                                    (Nat.lt_succ_diag_r  n))) _
                  (Vector.nil _))) (evalPrimRec _ x0))).
    apply extEqualRefl.
    apply extEqualPrimRec.
    simpl in |- *.
    apply extEqualRefl.
    apply extEqualCompose.
    unfold extEqualVector, extEqualVectorGeneral, Vector.t_rect in |- *.
    repeat split; auto.
    apply extEqualRefl.
    auto.
  }
  assert (H1: isPR (S n) (fun z : nat => A (S z))).
  { apply compose1_NIsPR; auto.
    apply succIsPR.
  }
  clear H0; assert (H0: isPR 1 (fun z : nat => cPairPi1 (pred z))).
  { apply compose1_1IsPR.
    apply predIsPR.
    apply cPairPi1IsPR.
  }
  induction H0 as (x, p).
  induction H1 as (x0, p0).
  exists (composeFunc (S n) 1 (PRcons _ _ x0 (PRnil _)) x).
  simpl in |- *.
  fold (naryFunc n) in |- *.
  intros c; apply extEqualCompose.
  unfold extEqualVector in |- *.
  simpl in |- *; repeat split.
  - apply (p0 c).
  -  trivial.
Qed.

(* begin snippet computeEvalStrongRecHelp:: no-out *)
Lemma computeEvalStrongRecHelp :
  forall (n : nat) (f : naryFunc (S (S n))) (c : nat),
    evalStrongRecHelp n f (S c) =
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
  induction (eq_nat_dec n (S n)).
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
                (fun a2 b0 : nat => S (cPair a2 b0))) c)
        with
        (evalStrongRecHelp n f c).
      reflexivity.
      unfold evalStrongRecHelp at 1 in |- *.
      simpl in |- *.
      fold (naryFunc n) in |- *.
      induction (eq_nat_dec n (S n)).
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
   codeNth (n - S m) (evalStrongRecHelp _ f n) = evalStrongRec _ f m.
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
  forall (a n c : nat) (f : naryFunc (S (S (S a)))),
    extEqual a (evalStrongRecHelp (S a) f n c)
      (evalStrongRecHelp a (fun x y : nat => f x y c) n).
Proof.
  intros a n c f; unfold evalStrongRecHelp in |- *.
  eapply extEqualTrans.
  - apply extEqualSym.
    apply evalPrimRecParam.
  - assert
    (H: extEqual (S a)
       (evalPrimRecFunc a
          (evalComposeFunc (S a) 0
             (Vector.nil (naryFunc (S a))) (codeList nil) c)
          (fun x y : nat =>
             evalComposeFunc (S (S (S a))) 2
               (Vector.cons (naryFunc (S (S (S a)))) f 1
                  (Vector.cons (naryFunc (S (S (S a))))
                     (evalProjFunc (S (S (S a))) (S a)
                        (Nat.lt_lt_succ_r (S a) (S (S a))
                           (Nat.lt_succ_diag_r  (S a)))) 0
                     (Vector.nil (naryFunc (S (S (S a)))))))
               (fun a0 b : nat => S (cPair a0 b)) x y c))
       (evalPrimRecFunc a
          (evalComposeFunc a 0 (Vector.nil (naryFunc a)) (codeList nil))
          (evalComposeFunc (S (S a)) 2
             (Vector.cons (naryFunc (S (S a))) (fun x y : nat => f x y c) 1
                (Vector.cons (naryFunc (S (S a)))
                   (evalProjFunc (S (S a)) a (Nat.lt_lt_succ_r a (S a)
                                                (Nat.lt_succ_diag_r  a))) 0
                   (Vector.nil (naryFunc (S (S a))))))
             (fun a0 b : nat => S (cPair a0 b))))).
    { apply
        (extEqualPrimRec a
           (evalComposeFunc (S a) 0
              (Vector.nil (naryFunc (S a)))
              (codeList nil) c)).
      simpl in |- *; apply extEqualRefl.
      - simpl in |- *; fold (naryFunc a) in |- *.
        induction
          (sumbool_rec
             (fun _ : {a = S a} + {a <> S a} =>
                {S a = S (S a)} + {S a <> S (S a)})
             (fun a0 : a = S a => left (S a <> S (S a)) (f_equal S a0))
             (fun b : a <> S a => right (S a = S (S a)) (not_eq_S a (S a) b))
             (eq_nat_dec a (S a))).
        + elim (Compat815.lt_not_le (S a) (S (S a))).
          * apply Nat.lt_succ_diag_r.
          * rewrite <- a0; auto.
        + induction
            (sumbool_rec (fun _ : {a = a} + {a <> a} =>
                            {S a = S a} + {S a <> S a})
               (fun a0 : a = a => left (S a <> S a) (f_equal S a0))
               (fun b0 : a <> a => right (S a = S a) (not_eq_S a a b0)) 
               (eq_nat_dec a a)).
            induction (eq_nat_dec a (S a)).
          * elim (Compat815.lt_not_le a (S a)).
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
  forall (a : nat) (f : naryFunc (S (S a))) (n m : nat),
    m < n ->
    extEqual _
      (evalComposeFunc _ 1
         (Vector.cons _ (evalStrongRecHelp _ f n) 0 (Vector.nil _))
         (fun b : nat => codeNth (n - S m) b)) (evalStrongRec _ f m).
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

Lemma callIsPR (g : nat -> nat) :
 isPR 1 g -> isPR 2 (fun a recs : nat => codeNth (a - S (g a)) recs).
Proof.
  intros H; apply  compose2_2IsPR
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

Lemma div2IsPR : isPR 1 div2.
Proof.
  assert
    (H: isPR 1
          (evalStrongRec 0
             (fun n recs : nat =>
                switchPR n
                  (switchPR (pred n)
                     (S (codeNth (n - S (pred (pred n))) recs))
                     0)
                  0))).
  { apply evalStrongRecIsPR.
    assert (H : isPR 2 (fun n recs : nat => 0)).
    { exists (composeFunc 2 0 (PRnil _) zeroFunc).
      simpl in |- *; auto.
    }
    apply compose2_3IsPR with
    (f1 := fun n recs : nat => n)
    (f2 := fun n recs : nat =>
             switchPR (pred n)
               (S (codeNth (n - S (pred (pred n))) recs)) 0)
    (f3 := fun n recs : nat => 0).
    - apply pi1_2IsPR.
    - apply compose2_3IsPR with
        (f1 := fun n recs : nat => pred n)
        (f2 := fun n recs : nat =>
                 S (codeNth (n - S (pred (pred n))) recs))
        (f3 := fun n recs : nat => 0).
      + apply filter10IsPR.
        apply predIsPR.
      + apply compose2_1IsPR with
            (f := fun n recs : nat =>
                    codeNth (n - S (pred (pred n))) recs).
        * apply compose2_2IsPR with
            (f := fun n recs : nat => n - S (pred (pred n)))
            (g := fun n recs : nat => recs).
          apply filter10IsPR with
            (g := fun n : nat => n - S (pred (pred n))).
          apply compose1_2IsPR with
            (f := fun n : nat => n)
            (f' := fun n : nat => S (pred (pred n))).
          apply idIsPR.
          apply compose1_1IsPR with
            (f := fun n : nat => pred (pred n)).
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
                 switchPR n (switchPR (pred n)
                               (S (codeNth (n - S (pred (pred n)))
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
        set (A := S (S n) - S (pred (pred (S (S n))))) in *.
      simpl in |- *; rewrite cPairProjections1; apply eq_S.
      rewrite <- H; unfold A in |- *; apply evalStrongRecHelp1.
      auto.
Qed.

(** abbrviations a la Lisp (to improve) *)

Module LispAbbreviations.
  #[global] Notation car n := (cPairPi1 n). 
  #[global] Notation caar n := (cPairPi1 (cPairPi1 n)). 
  #[global] Notation cadr n := (cPairPi1 (cPairPi2 n)). 

  #[global] Notation cdr n := (cPairPi2 n). 
  #[global] Notation cddr n := (cPairPi2 (cPairPi2 n)). 
  #[global] Notation cdddr n := (cPairPi2 (cPairPi2 (cPairPi2 n))). 
  #[global] Notation cddddr n := 
    (cPairPi2 (cPairPi2 (cPairPi2 (cPairPi2 n)))).

End LispAbbreviations. 

(* Fails with 8.13 *)

(* Compatibility with Stdlib's Cantor pairing function *)
(*
From Coq Require  Cantor.

Lemma cPair_compat (a b : nat) : cPair a b = Cantor.to_nat (b,a). 
Proof. unfold cPair, Cantor.to_nat; f_equal. Qed.

Lemma proj_compat (n: nat) : (cPairPi2 n, cPairPi1 n) =
                               Cantor.of_nat n. 
Proof. 
  rewrite <- (cPairProjections n)at 3;
    now rewrite cPair_compat,  Cantor.cancel_of_to.
Qed.

 *)

