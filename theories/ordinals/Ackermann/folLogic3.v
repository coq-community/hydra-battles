(** folLogic2.3

    Original script by Russel O'Connor

*)

From Coq Require Import Ensembles List Arith Lia.
From LibHyps Require Export LibHyps.

From hydras.Ackermann Require Import ListExt folProp folProof.
From hydras.Ackermann Require Export folLogic folLogic2.
From hydras.Ackermann Require Import subProp folReplace subAll misc.
From hydras Require Import Compat815.
From hydras Require Export MoreLibHyps. 
Import FolNotations.

Section Equality_Logic_Rules.

Variable L : Language.
Notation Formula := (Formula L) (only parsing).
Notation Formulas := (Formulas L) (only parsing).
Notation System := (System L) (only parsing).
Notation Term := (Term L) (only parsing).
Notation Terms := (Terms L) (only parsing).

Let Prf := Prf L.
Let SysPrf := SysPrf L.

Lemma eqRefl (T : fol.System L) (a : fol.Term L): 
  SysPrf T (a = a)%fol.
Proof.
  replace (a = a)%fol with 
    (substF (v#0 = v#0)%fol 0 a).
  apply (forallE L).
  - apply sysExtend with (Empty_set (fol.Formula L)).
    + intros f H; destruct H.
    + apply forallI.
     * apply (notInFreeVarSys L).
     * exists (nil (A:=fol.Formula L)).
       exists (EQ1 L); contradiction.
  - rewrite (subFormulaEqual L); reflexivity.
Qed.

Lemma eqSym (T : fol.System L) (a b : fol.Term L):
  SysPrf T (a = b)%fol -> SysPrf T (b = a)%fol.
Proof.
  intros H;apply (impE L) with (equal a b); [ | easy].
  set (m := fun x : nat => match x with
                         | O => a
                         | S _ => b
                         end) in *.
  apply (impE L) with
    (subAllFormula L (v#0 = v#1 -> v#1 = v#0)%fol
       (fun x : nat =>
        match le_lt_dec 2 x with
        | left _ => var x
        | right _ => m x
        end)).
  + simpl; destruct (le_lt_dec 2 0) as [l | l].
    * lia.
    * destruct (le_lt_dec 2 1) as [l0 | l0].
      -- lia.
      -- apply (impRefl L).
  + apply (subAllCloseFrom L).
    apply sysExtend with (Empty_set (fol.Formula L)).
    * intros x H0; destruct H0. 
    * simpl; apply forallI.
      -- apply (notInFreeVarSys L).
      -- apply forallI.
         ++ apply (notInFreeVarSys L).
         ++ exists (nil (A:=fol.Formula L)).
            exists (EQ2 L); contradiction.
Qed.

Lemma eqTrans  (T : fol.System L) (a b c : fol.Term L):
 SysPrf T (a = b)%fol -> SysPrf T (b = c)%fol -> 
 SysPrf T (a = c)%fol.
Proof.
  intros H H0; apply (impE L) with (equal b c); [ | easy].
  apply (impE L) with (equal a b);  [ | easy];  clear H0 H.
  set (m x:= match x with | O => a | 1 => b  | _ => c  end) in *.
  apply (impE L) with
    (subAllFormula L
       (v#0 = v#1 -> v#1 = v#2 -> v#0 = v#2)%fol
       (fun x : nat =>
        match le_lt_dec 3 x with
        | left _ => var x
        | right _ => m x
        end)).
  - simpl in |- *; induction (le_lt_dec 3 0) as [a0 | b0]; [lia | ].
    destruct (le_lt_dec 3 1)as [? | l]; [lia | ].
    destruct  (le_lt_dec 3 2) as [? | l0]; [lia | ].
    apply (impRefl L).
  - apply (subAllCloseFrom L); apply sysExtend with (Empty_set (fol.Formula L)).
    + intros f H; destruct H. 
    + simpl in |- *; apply forallI.
      * apply (notInFreeVarSys L).
      * apply forallI.
        -- apply (notInFreeVarSys L).
        -- apply forallI.
           ++ apply (notInFreeVarSys L).
           ++ exists nil,  (EQ3 L); contradiction.
Qed.

Fixpoint PairwiseEqual (T : fol.System L) (n : nat) {struct n} :
 fol.Terms L n -> fol.Terms L n -> Prop :=
  match n return (fol.Terms L n -> fol.Terms L n -> Prop) with
  | O => fun ts ss : fol.Terms L 0 => True
  | S x =>
      fun ts ss : fol.Terms L (S x) =>
      let (a, b) := proj1_sig (consTerms L x ts) in
      let (c, d) := proj1_sig (consTerms L x ss) in
      SysPrf T (a = c)%fol /\ PairwiseEqual T x b d
  end.

(** TODO : specify and document *)

Let termsMap (m : nat) (ts ss : fol.Terms L m) : nat -> fol.Term L.
Proof. 
  induction m as [| m Hrecm].
  - exact (fun n : nat => var n).
  - destruct (consTerms L _ ts)as [[a b] p].
    destruct  (consTerms L _ ss) as [[a0 b0] e].
    exact
      (fun n : nat =>
         match eq_nat_dec n (m + m) with
         | left _ => a
         | right _ =>
             match eq_nat_dec n (S (m + m)) with
             | left _ => a0
             | right _ => Hrecm b b0 n
             end
         end).
Defined.


Remark subAllnVars1 (a : nat) (ts ss : fol.Terms L a):
 ts = subAllTerms L _ (fst (nVars L a)) (termsMap a ts ss).
Proof.
  induction a as [| a Hreca].
  - simpl; symmetry; apply (nilTerms L).
  - assert
      (H: forall v : nat, In v (freeVarTs (fst (nVars L a))) -> v < a + a).
    {  intros v H; clear Hreca ss ts.
       induction a as [| a Hreca].
       - elim H.
       - simpl in H; induction (nVars L a).
         simpl in H.
         induction H as [H| H].
         rewrite <- H.
         rewrite Nat.add_succ_r.
         simpl in |- *.
         apply Nat.lt_lt_succ_r.
         apply Nat.lt_succ_diag_r .

         rewrite Nat.add_succ_r.
         apply Nat.lt_trans with (a + a).
         apply Hreca.
         apply H.
         simpl in |- *.
         apply Nat.lt_lt_succ_r.
         apply Nat.lt_succ_diag_r .
    } 
    simpl in |- *.
    induction (consTerms L a ts) as [(a0,b) p].
   
    induction (consTerms L a ss) as [ (a1, b0) p0].
    simpl in |- *.
    simpl in H.
    induction (nVars L a) as [a2 b1].
    simpl in |- *.
    simpl in Hreca.
    destruct  (eq_nat_dec (a + a) (a + a)) as [e | n].
    { simpl in p.
      rewrite <- p.
      replace
        (subAllTerms L a a2
           (fun n : nat =>
              match eq_nat_dec n (a + a) with
              | left _ => a0
              | right _ =>
                  match eq_nat_dec n (S (a + a)) with
                  | left _ => a1
                  | right _ => termsMap a b b0 n
                  end
              end)) with (subAllTerms L a a2 (termsMap a b b0)).
      + now rewrite <- Hreca.
      + apply subAllTerms_ext.
        intros m H0.  destruct  (eq_nat_dec m (a + a)) as [e0 | n].
        * elim (Compat815.lt_not_le m (a + a)).
          -- apply H; auto.
          -- lia. 
        * destruct (eq_nat_dec m (S (a + a))) as [a4 | _].
          -- elim (Compat815.lt_not_le m (a + a)).
             apply H; auto.
             rewrite a4; apply Nat.le_succ_diag_r.
          -- reflexivity.
    }   
    + elim n; auto.
Qed.



Remark subAllnVars2 (a : nat) (ts ss : fol.Terms L a):
 ss = subAllTerms L _ (snd (nVars L a)) (termsMap a ts ss).
Proof.
  induction a as [| a Hreca].
  - simpl; symmetry; apply (nilTerms L).
  - assert
      (H: forall v : nat, In v (freeVarTs (snd (nVars L a))) -> v < a + a).
    { intros v H; clear Hreca ss ts; induction a as [| a Hreca].
      - elim H.
      - simpl in H; induction (nVars L a) as [a0 b].
        simpl in H; destruct H as [H| H].
        subst. lia. 
        rewrite Nat.add_succ_r.
        simpl in |- *.
        apply Nat.lt_trans with (a + a).
        + apply Hreca, H. 
        + lia.
    }
    simpl in |- *; destruct (consTerms L a ts) as [[a0 b] e];
      destruct (consTerms L a ss) as [[a1 b0] p].
    simpl in |- *; simpl in H.
    induction (nVars L a) as [a2 b1].
    Opaque eq_nat_dec.
    simpl.
    Transparent eq_nat_dec.
    destruct (eq_nat_dec (S (a+a)) (a + a)) as [e0 | n]. 
    + lia. 
    + destruct (eq_nat_dec (S (a + a)) (S (a+a))) as [e0 | n0].
      * replace
          (subAllTerms L a b1
             (fun n : nat =>
                match eq_nat_dec n (a + a) with
                | left _ => a0
                | right _ =>
                    match eq_nat_dec n (S (a + a)) with
                    | left _ => a1
                    | right _ => termsMap a b b0 n
                    end
                end)) 
          with (subAllTerms L a b1 (termsMap a b b0)).
        rewrite <- Hreca; now rewrite <- p. 
        apply subAllTerms_ext.
        intros m H0.
        destruct (eq_nat_dec m (a + a)) as [e1 | n1].
      --  elim (Compat815.lt_not_le m (a + a)).
          apply H; auto.
          rewrite e1; auto.
      -- destruct (eq_nat_dec m (S (a + a))) as [e1 | n2].
         ++ elim (Compat815.lt_not_le m (a + a)).
            apply H; auto.
            lia. 
         ++ easy. 
      * elim n0; auto.
Qed.

Remark addPairwiseEquals (T : fol.System L) (n : nat) (ts ss : fol.Terms L n):
  PairwiseEqual T n ts ss ->
  forall m0 : nat -> fol.Term L,
    (forall q : nat, q < n + n -> m0 q = termsMap n ts ss q) ->
    forall f0 : fol.Formula L,
      SysPrf T
        (subAllFormula L
           (nat_rec (fun _ : nat => fol.Formula L) f0
              (fun (n : nat) (Hrecn : fol.Formula L) =>
                 (v#(n + n) = v#(S (n + n)) -> Hrecn)%fol
                 )
              n) m0) -> SysPrf T (subAllFormula L f0 m0).
Proof.
  intros H.
  set (m := termsMap n ts ss) in *.
  induction n as [| n Hrecn].
  - simpl in |- *; auto.
  - simpl in (value of m); simpl in H.
    destruct (consTerms L n ts) as [[a b] p].
    induction (consTerms L n ss) as [[a0 b0] p0].
    simpl in H; simpl in (value of m).
    destruct H as (H, H0); simpl in |- *.
    intros m0 H1 f0 H2; apply (Hrecn b b0).
    + auto.
    + intros q H3; rewrite H1. 
      * unfold m in |- *.
        destruct (eq_nat_dec q (n + n))as [e | n0].
      -- subst; lia.
     -- induction (eq_nat_dec q (S (n + n))).
        ++ elim (Compat815.lt_not_le _ _ H3).
           rewrite a1.
           apply Nat.le_succ_diag_r.
        ++  reflexivity.
      * rewrite Nat.add_succ_r.
        simpl in |- *.
        repeat apply Nat.lt_lt_succ_r.
        auto.
    + apply (impE L) with (m0 (n + n) = m0 (S (n + n)))%fol.
      * apply H2.
      * rewrite Nat.add_succ_r in H1.
        repeat rewrite H1.
        unfold m in |- *.
        destruct (eq_nat_dec (n + n) (n + n)) as [a1 | b1].
        -- destruct (eq_nat_dec (S (n + n)) (n + n)) as [e | n0].
           ++ lia.
           ++ induction (eq_nat_dec (S (n + n)) (S (n + n))) as [a2 | b2].
              apply H.
              elim b2; auto.
        -- elim b1; auto.
        -- simpl in |- *. lia. 
        -- simpl in |- *; lia. 
Qed.

Lemma equalRelation (T : fol.System L) (r : Relations L) (ts ss : fol.Terms L _):
 PairwiseEqual T _ ts ss -> SysPrf T (atomic r ts <-> atomic r ss)%fol.
Proof.
  intros H.
  set (n := arityR L r) in *.
  set (m := termsMap n ts ss) in *.
  rewrite (subAllnVars1 _ ts ss).
  fold m in |- *; rewrite (subAllnVars2 _ ts ss); fold m in |- *.
  replace
    (iffH (atomic r (subAllTerms L n (fst (nVars L n)) m))
       (atomic r (subAllTerms L n (snd (nVars L n)) m))) with
    (subAllFormula L
       (iffH (atomic r (fst (nVars L n))) (atomic r (snd (nVars L n)))) m);
    [ idtac | reflexivity ].
  cut (SysPrf T (subAllFormula L (AxmEq4 L r) m)).
  - unfold AxmEq4 in |- *; fold n in |- *.
    replace
      (prod_rec (fun _ : fol.Terms L n * fol.Terms L n => fol.Formula L)
         (fun a b : fol.Terms L n =>
            iffH (atomic r a) (atomic r b)) 
         (nVars L n)) with
      (iffH (atomic r (fst (nVars L n))) (atomic r (snd (nVars L n)))).
   + generalize (iffH (atomic r (fst (nVars L n))) (atomic r (snd (nVars L n)))).
     intros f H0; apply (addPairwiseEquals T n ts ss).
     * auto.
     * unfold m in |- *; auto.
     * auto.
   + destruct (nVars L n) as [a b].
     reflexivity.
  - replace (subAllFormula L (AxmEq4 L r) m) with
      (subAllFormula L (AxmEq4 L r)
         (fun x : nat =>
            match le_lt_dec (n + n) x with
            | left _ => var x
            | right _ => m x
            end)).
    + apply (subAllCloseFrom L).
      apply sysExtend with (Empty_set (fol.Formula L)).
      intros f H0; destruct H0.
      clear m H ts ss T.
      induction n as [| n Hrecn].
      * simpl in |- *; exists (nil (A:=fol.Formula L)).
        exists (EQ4 L r); contradiction.
      * simpl in |- *; apply (forallI L).
        apply (notInFreeVarSys L).
        rewrite Nat.add_succ_r.
        simpl in |- *.
        apply (forallI L).
        apply (notInFreeVarSys L).
        apply Hrecn.
    + apply subAllFormula_ext.
      intros m0 H0;clear H0 H.
      destruct (le_lt_dec (n + n) m0) as [l | l].
      * unfold m in |- *.
        induction n as [| n Hrecn].
        -- reflexivity.
        -- simpl in |- *.
           destruct (consTerms L n ts) as [[a0 b] p]. 
           destruct (consTerms L n ss) as [[a b0] p0]. 
           simpl in |- *.
           induction (eq_nat_dec m0 (n + n)) as [a1 | b1].
           ** subst; lia.
           ** destruct  (eq_nat_dec m0 (S (n + n))).
            lia.
            apply Hrecn; lia.
      * reflexivity.
Qed.

Lemma equalFunction (T : fol.System L) (f : Functions L) (ts ss : fol.Terms L _):
 PairwiseEqual T _ ts ss -> SysPrf T (apply f ts =  apply f ss)%fol.
Proof.
  intros H.
  set (n := arityF L f) in *.
  set (m := termsMap n ts ss) in *.
  rewrite (subAllnVars1 _ ts ss).
  fold m in |- *.
  rewrite (subAllnVars2 _ ts ss).
  fold m in |- *.
  replace
    (equal (apply f (subAllTerms L n (fst (nVars L n)) m))
       (apply f (subAllTerms L n (snd (nVars L n)) m))) with
    (subAllFormula L
       (equal (apply f (fst (nVars L n))) (apply f (snd (nVars L n)))) m);
    [ idtac | reflexivity ].
  cut (SysPrf T (subAllFormula L (AxmEq5 L f) m)).
  - unfold AxmEq5 in |- *; fold n in |- *.
    replace
      (prod_rec (fun _ : fol.Terms L n * fol.Terms L n => fol.Formula L)
         (fun a b : fol.Terms L n =>
            equal (apply f a) (apply f b)) 
         (nVars L n)) 
      with
      (equal (apply f (fst (nVars L n))) (apply f (snd (nVars L n)))).
    + generalize (equal (apply f (fst (nVars L n))) (apply f (snd (nVars L n)))).
      intros f0 H0; apply (addPairwiseEquals T n ts ss).
      auto.
      unfold m in |- *; auto.
      auto.
    + induction (nVars L n) as [a b].
      reflexivity.
  - replace (subAllFormula L (AxmEq5 L f) m) with
      (subAllFormula L (AxmEq5 L f)
         (fun x : nat =>
            match le_lt_dec (n + n) x with
            | left _ => var x
            | right _ => m x
            end)).
    + apply (subAllCloseFrom L).
      apply sysExtend with (Empty_set (fol.Formula L)).
      red; destruct 1. 
      clear m H ts ss T; induction n as [| n Hrecn].
      * simpl in |- *.
        exists (nil (A:=fol.Formula L)).
        exists (EQ5 L f).
        contradiction.
      * simpl in |- *; apply (forallI L).
        apply (notInFreeVarSys L).
        rewrite Nat.add_succ_r.
        simpl in |- *.
        apply (forallI L).
        apply (notInFreeVarSys L).
        apply Hrecn.
    + apply subAllFormula_ext.
      intros m0 H0; clear H0 H.
      destruct (le_lt_dec (n + n) m0) as [l | l].
      * unfold m in |- *.
        induction n as [| n Hrecn].
        -- reflexivity.
        -- simpl in |- *.
           destruct (consTerms L n ts) as [(a0, b) p].
           induction (consTerms L n ss) as [(a1, b0) p0]. 
           simpl in |- *.
           induction (eq_nat_dec m0 (n + n)).
           ++ lia.
           ++ induction (eq_nat_dec m0 (S (n + n))).
             subst; lia. 
             apply Hrecn. lia.
      * reflexivity.
Qed.

Lemma subWithEqualsTerm (a b t : fol.Term L) (v : nat) 
  (T : fol.System L):
 SysPrf T (a = b)%fol ->
 SysPrf T (substT t v a =  substT t v b)%fol.
Proof.
  intros H; elim t using  Term_Terms_ind  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             PairwiseEqual T _ (substTs ts v a)
               (substTs ts v b)); simpl in |- *. 
    - intros n; induction (eq_nat_dec v n); [easy | apply eqRefl].
    - intros f t0 H0; apply equalFunction.
      apply H0.
    - auto.
    - intros.  
      destruct
        (consTerms L n
           (Tcons (substT t0 v a) (substTs t1 v a))). 
      destruct x as [a0 b0].
      destruct
        (consTerms L n
           (Tcons (substT t0 v b) (substTs t1 v b))).  
      destruct x as [a1 b1]. 
      simpl in |- *.  simpl in e0; simpl in e.
      inversion e0.
      inversion e. 
      auto.
      rewrite (inj_pair2_eq_dec _ eq_nat_dec _ _ _ _ H4).
      rewrite (inj_pair2_eq_dec _ eq_nat_dec _ _ _ _ H6).
      auto.
Qed.

Lemma subWithEqualsTerms (a b : fol.Term L) (n : nat) (ts : fol.Terms L n) 
  (v : nat) (T : fol.System L):
  SysPrf T (a = b)%fol ->
  PairwiseEqual T _ (substTs ts v a) (substTs ts v b).
Proof.
  intros H; induction ts as [| n t ts Hrects]; simpl in |- *.
  - auto.
  - destruct
      (consTerms L n
         (Tcons (substT t v a) (substTs ts v a))) as [[a0 b0] p].
    destruct
      (consTerms L n
         (Tcons (substT t v b) (substTs ts v b))) as [[a1 b1] e].
    simpl in |- *; simpl in p,  e.
    inversion p.
    inversion e.
    split.
    + apply subWithEqualsTerm; auto.
    + rewrite (inj_pair2_eq_dec _ eq_nat_dec _ _ _ _ H2).
      now rewrite (inj_pair2_eq_dec _ eq_nat_dec _ _ _ _ H4).
Qed.

Lemma subWithEquals :
  forall (f : fol.Formula L) (v : nat) (a b : fol.Term L) (T : fol.System L),
    SysPrf T (a = b)%fol ->
    SysPrf T 
      (substF f v a -> substF f v b)%fol.
Proof.
  intro f; elim f using Formula_depth_ind2; intros.
  - repeat rewrite subFormulaEqual.
    apply (impI L).
    apply eqTrans with (substT t v a).
    + apply subWithEqualsTerm.
      apply (sysWeaken L).
      now apply eqSym.
    + apply eqTrans with (substT t0 v a).
      * apply (Axm L); right; constructor.
      * apply subWithEqualsTerm.
        now apply (sysWeaken L).
  - apply (iffE1 L).
    repeat rewrite subFormulaRelation.
    apply equalRelation.
    now apply subWithEqualsTerms.
  - repeat rewrite subFormulaImp.
    repeat apply (impI L).
    apply impE with (substF f1 v a).
    + apply H0.
      now repeat apply (sysWeaken L).
    + apply impE with (substF f0 v a).
      * apply (Axm L); left; right; constructor.
      * apply impE with (substF f0 v b).
        -- apply H.
           repeat apply (sysWeaken L).
           now apply eqSym.
        -- apply (Axm L); right; constructor.
  - repeat rewrite subFormulaNot.
    apply (cp2 L), H; now apply eqSym.
  - decompose record (subFormulaForall2 L a v v0 a0) /r;
      intros x H2 H1 H3 H5.

    rewrite H5; clear H5.
    decompose record (subFormulaForall2 L a v v0 b) /r; 
      intros x0 H5 H4 H6 H8;  rewrite H8; clear H8.
    destruct  (eq_nat_dec v v0) as [e | n].
    + apply (impRefl L).
    + set
        (nv :=
           v0
             :: List.remove eq_nat_dec v (freeVarF a) ++
             freeVarT a0 ++ freeVarT b) in *.
      apply  (impTrans L) with
        (forallH (newVar nv)
           (substF (substF a v (var (newVar nv)))
              v0 a0)).
      * apply sysExtend with (Empty_set (fol.Formula L)).
        intros g H7; destruct H7. 
        apply
          (impTrans L)
          with
          (forallH (newVar nv)
             (substF 
                (substF (substF a v (var x)) v0 a0)
                x (var (newVar nv)))).
        apply (iffE1 L).
        apply (rebindForall L).
        unfold not in |- *.  intros H7.
        elim (newVar1 nv).
        unfold nv at 2 in |- *.
        assert
          (H8: In (newVar nv)
                 (freeVarF 
                    (substF  (substF a v (var x)) v0 a0)))
          by (eapply in_remove; apply H7).
        induction (freeVarSubFormula3 _ _ _ _ _ H8).
        -- assert
          (In (newVar nv) (freeVarF (substF a v (var x)))) by
          (eapply in_remove; apply H9). 
        induction (freeVarSubFormula3 _ _ _ _ _ H10).
           ++ right.
              apply in_or_app.
              auto.
           ++ elim (in_remove_neq _ _ _ _ _ H7).
              induction H11 as [H11| H11].
              auto.
              contradiction.
        -- right.
           auto with datatypes.
        -- apply (iffE1 L).
           apply (reduceForall L).
           apply (notInFreeVarSys L).
           apply
             (iffTrans L)
             with
             (substF (substF (substF a v (var x)) x
                   (var (newVar nv))) v0 a0).
           ++ apply (subFormulaExch L); auto.
              unfold not in |- *; intros.
              elim (newVar1 nv).
              unfold nv at 2 in |- *.
              simpl in |- *.
              left.
              induction H7 as [H7| H7].
              auto.
              contradiction.
           ++ apply (reduceSub L).
              apply (notInFreeVarSys L).
              now apply (subFormulaTrans L).
      * apply
          (impTrans L)
          with
          (forallH (newVar nv)
             (substF (substF a v (var (newVar nv)))
                v0 b)).
        -- apply impE with (equal a0 b).
           ++ apply sysExtend with (Empty_set (fol.Formula L)).
              intros f0 H7; destruct H7.
              repeat apply (impI L).
              ** apply forallI.
                 unfold not in |- *; intros.
                 destruct H7 as (x1, (H7, H8)).
                 destruct H8 as [x1 H8| x1 H8];
                   [ induction H8 as [x1 H8| x1 H8] | induction H8 ]. 
                 induction H8; simple induction H8.
                 induction H8.
                 simpl in H7.
                 elim (newVar1 nv).
                 unfold nv at 2 in |- *.
                 right.
                 auto with datatypes.
                 elim (in_remove_neq _ _ _ _ _ H7).
                 reflexivity.
                 apply impE with
                   (substF (substF a v (var (newVar nv))) v0 a0).
                 apply H.
                 eapply eqDepth.
                 symmetry  in |- *.
                 apply (subFormulaDepth L).
                 apply depthForall.
                 apply (Axm L); left; right; constructor.
                 eapply forallSimp.
                 apply (Axm L); right; constructor.
           ++ apply H0.
        -- apply sysExtend with (Empty_set (fol.Formula L)).
           intros g H7; induction H7.
           apply (iffE2 L); apply (iffTrans L) with
             (forallH (newVar nv)
                (substF 
                   (substF (substF a v (var x0)) v0 b)
                   x0 (var (newVar nv)))).
           apply (rebindForall L).
           intros H7; elim (newVar1 nv).
           unfold nv at 2 in |- *.
           assert
             (H8: In (newVar nv)
                    (freeVarF
                       (substF  
                          (substF  a v (var x0)) v0 b)))
             by (eapply in_remove; apply H7).
           induction (freeVarSubFormula3 _ _ _ _ _ H8).
           assert
             ( H10:In (newVar nv) 
                     (freeVarF  (substF a v (var x0)))) by
             (eapply in_remove; apply H9).
           induction (freeVarSubFormula3 _ _ _ _ _ H10).
           right; apply in_or_app.
           now left. 
           elim (in_remove_neq _ _ _ _ _ H7).
           induction H11 as [H11| H11].
           ++ auto.
           ++ contradiction.
           ++ right; auto with datatypes.
           ++ apply (reduceForall L).  
             ** apply (notInFreeVarSys L).
             ** apply (iffTrans L) with
                  (substF 
                     (substF 
                        (substF a v (var  x0)) x0
                        (var (newVar nv))) v0 b).
                apply (subFormulaExch L); auto.
                intros H7. 
                elim (newVar1 nv).
                unfold nv at 2 in |- *.
                simpl in |- *.
                left.
                induction H7 as [H7| H7].
                auto.
                contradiction.
                apply (reduceSub L).
                apply (notInFreeVarSys L).
                apply (subFormulaTrans L).
                auto.
Qed.

End Equality_Logic_Rules.
