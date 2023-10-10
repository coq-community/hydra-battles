(**  PA : Peano Arithmetic 

       Original development by Russel O'Connor 
       Bullets and abbreviations by Pierre Casteran 
*)

From Coq Require Import Arith Lia Ensembles Decidable.
Require Import folProp subAll folLogic3.
Require Export Languages LNT.
Require Import NewNotations.



Section PA.

Definition PA1 := (allH 0, Succ v#0 <> Zero)%nt.

Definition PA2 := (allH 1 0, Succ v#0 = Succ v#1 -> v#0 = v#1)%nt.

Definition PA3 := (allH 0, v#0 + Zero = v#0)%nt. 

Definition PA4 := (allH 1 0, v#0 + Succ v#1 = Succ (v#0 + v#1))%nt.

Definition PA5 := (allH 0, v#0 * Zero = Zero)%nt. 

Definition PA6 := (allH 1 0, v#0 * Succ v#1 = v#0 * v#1 + v#0)%nt.

Definition PA7 (f : Formula) (v : nat) : Formula :=
   let f_0 := substF f v Zero%nt in
   let f_Sv := substF f v (Succ v#v)%nt in
   close _  (f_0 -> (allH v, f -> f_Sv) -> allH v, f)%nt.

Definition InductionSchema (f : Formula) : Prop :=
  exists g : Formula, (exists v : nat, f = PA7 g v).

Definition PA := SetAdds InductionSchema PA1 PA2 PA3 PA4 PA5 PA6.

Definition open :=
  Formula_rec LNT (fun _ => Formula) (fun t t0 : Term => (t = t0)%nt)
    (fun (r : Relations LNT) 
         (ts : Terms (arityR LNT r)) =>  atomic r ts) 
    (fun (f : Formula) _ (f0 : Formula) _ => (f -> f0)%nt)
    (fun (f : Formula) _ => (~ f)%nt)
    (fun (n : nat) _ (recf : Formula) => recf).

Lemma PAdec : forall x : Formula, decidable (In _ PA x).
Proof.
  intros x.
  unfold PA in |- *.
  induction (formula_eqdec LNT LNT_eqdec x PA6).
  - rewrite a; left; right; constructor.
  - induction (formula_eqdec LNT LNT_eqdec x PA5).
    + rewrite a; left; left; right; constructor.
    + induction (formula_eqdec LNT LNT_eqdec x PA4).
      * rewrite a; left; do 2 left; right; constructor.
      * induction (formula_eqdec LNT LNT_eqdec x PA3).
        -- rewrite a; left; do 3 left; right; constructor.
        -- induction (formula_eqdec LNT LNT_eqdec x PA2).
           ++ rewrite a; left; do 4 left; right; constructor.
           ++ induction (formula_eqdec LNT LNT_eqdec x PA1).
              ** rewrite a; left; do 5 left; right; constructor.
              ** cut (In Formula InductionSchema x \/ 
                        ~ In Formula InductionSchema x).
                 { intros  [H| H].
                   - left; do 6 left; assumption.
                   - right; intro H0. 
                     repeat tauto || induction H0.
                 } 
                 clear b b0 b1 b2 b3 b4.
                 assert
                   (H: forall y : Formula,
                       (decidable 
                          (exists (f : Formula) (v : nat),
                              (substF  f v Zero ->
                               (allH v, f -> substF f v (Succ v#v)) -> 
                               allH v, f)%nt 
                              = y))).
                 { intros y;
                   destruct y as [t t0| r t| f f0| f| n f];
                   try (right; unfold not in |- *; 
                        intros; decompose record H; discriminate ).
                   destruct f0 as [t t0| r t| f0 f1| f0| n f0];
                     try (right; unfold not in |- *; intros; 
                          decompose record H; discriminate).
                   destruct f0 as [t t0| r t| f0 f2| f0| n f0];
                     try (right; unfold not in |- *; intros; 
                          decompose record H; discriminate).
                   destruct f1 as [t t0| r t| f1 f2| f1| n0 f1];
                     try (right; unfold not in |- *; intros; 
                          decompose record H; discriminate).
                   destruct (formula_eqdec LNT LNT_eqdec (substF f1 n0 Zero) f) 
                     as [a | b].
                   - rewrite <- a; clear a f.
                     destruct f0 as [t t0| r t| f f0| f| n1 f];
                       try (right; unfold not in |- *; intros; 
                            decompose record H; discriminate).
                     induction (formula_eqdec LNT LNT_eqdec f1 f) as [a | b].
                     + rewrite <- a; clear a f.
                       induction
                         (formula_eqdec LNT LNT_eqdec
                            (substF f1 n0 (Succ (v#n0))%nt) f0).
                       * rewrite <- a; clear a f0.
                         induction (eq_nat_dec n n0) as [a | b].
                         -- rewrite a; left.
                            exists f1.
                            exists n0.
                            reflexivity.
                         -- right; unfold not in |- *; intros; 
                              apply b; decompose record H /r.
                            intros H x0 x1 H1; inversion H1; auto.
                       *  right; unfold not in |- *; intros; apply b; 
                            decompose record H /r.
                          intros H x0 x1 H1; inversion H1; 
                            reflexivity.
                     + right; unfold not in |- *; intros; apply b; 
                         decompose record H /r. 
                       intros H x0 x1 H1; inversion H1; auto.
                   -  right; unfold not in |- *; intros; apply b; 
                        decompose record H /r.
                      intros H x0 x1 H1; inversion H1; auto.
                 }                 
                 induction (formula_eqdec LNT LNT_eqdec x (close LNT (open x))) as [a | b].
                 --- induction (H (open x)).
                     left.
                     unfold In, InductionSchema, PA7 in |- *.
                     decompose record H0 /r.
                     intros x0 x1 H2; exists x0, x1; now rewrite H2.
                     right.
                     intros H1; apply H0.
                     unfold In, InductionSchema, PA7 in H1.
                     decompose record H1 /r.
                     intros x0 x1 H3; exists x0, x1; rewrite H3.
                     unfold close.  
                 induction
                   (List.nodup eq_nat_dec
                      (freeVarF 
                        (substF x0 x1 Zero ->
                          (allH x1, x0 -> substF x0 x1 (Succ (v#x1))) ->
                          allH x1, x0)%nt)).
                  simpl; reflexivity.
                 simpl; assumption.
                 --- right; intros H0; apply b.
                     unfold In, InductionSchema, PA7 in H0.
                     decompose record H0 /r.
                     intros x0 x1 H2; rewrite H2.
                     replace
                       (open
                          (close LNT
                             (substF x0 x1 Zero ->
                              (allH x1, x0 -> 
                                        substF x0 x1 (Succ v#x1)) -> 
                              allH x1, x0)%nt))
                       with
                       (substF x0 x1 Zero ->
                        (allH x1, x0 -> 
                                  substF x0 x1 (Succ v#x1)) -> 
                        allH x1, x0)%nt;
                       [reflexivity |]. 
                     unfold close in |- *.
                     induction
                       (List.nodup eq_nat_dec
                          (freeVarF 
                             (substF x0 x1 Zero ->
                              (allH x1, x0 -> substF x0 x1 (Succ (v#x1))) ->
                              (allH x1, x0)))%nt).
                     simpl; reflexivity.
                     simpl; auto.
Qed.

Lemma closedPA1 : ClosedSystem LNT PA.
Proof.
  unfold ClosedSystem, PA in |- *.
  intros v f H.
  induction H as [x H| x H].
  - induction H as [x H| x H].
    + induction H as [x H| x H].
      * induction H as [x H| x H].
      -- induction H as [x H| x H].
         ++  induction H as [x H| x H].
             ** induction H as (x0, H).
                induction H as (x1, H).
                unfold PA7 in H.
                rewrite H.
                apply freeVarClosed.
             ** induction H; auto.
         ++ induction H; auto.
      -- induction H; auto.
      * induction H; auto.
    + induction H; auto.
- induction H; auto.
Qed.

Lemma closedPA : forall v : nat, ~ In_freeVarSys LNT v PA.
Proof.
 intros v H; unfold In_freeVarSys in H.
 destruct H as [x H]; elim closedPA1 with v x; tauto.
Qed.

Lemma pa1 (a : Term):  SysPrf PA (Succ a <> Zero)%nt.
Proof.
  replace (Succ a <> Zero)%nt with  (substF (Succ v#0 <> Zero)%nt 0 a).
  - apply forallE, Axm; repeat (try right; constructor) || left.
  - reflexivity.
Qed.

Lemma pa2 (a b : Term):  SysPrf PA (Succ a = Succ b ->  a = b)%nt.
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  replace (Succ a = Succ b ->  a = b)%nt with
    (subAllFormula LNT
       (Succ v#0 = Succ v#1 ->  v#0 = v#1)%nt
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  - apply (subAllCloseFrom LNT).
    simpl; apply Axm; repeat (try right; constructor) || left.
  - simpl; induction (le_lt_dec 2 0). 
    + lia. 
    + destruct (le_lt_dec 2 1).
      * lia.
      * reflexivity.
Qed.

Lemma pa3 (a : Term): SysPrf PA (a + Zero = a)%nt.
Proof.
  replace (a + Zero = a)%nt with  (substF  (v#0 + Zero = v#0)%nt 0 a).
  - apply forallE, Axm; repeat (try right; constructor) || left.
  - reflexivity.
Qed.

Lemma pa4 ( a b : Term) :  SysPrf PA (a + Succ b = Succ (a + b))%nt.
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  replace (a + Succ b = Succ (a + b))%nt with
    (subAllFormula LNT
       (v#0 + Succ v#1 = Succ (v#0  + v#1))%nt
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  - apply (subAllCloseFrom LNT).
    simpl in |- *.
    apply Axm; repeat (try right; constructor) || left.
  - simpl in |- *.
    induction (le_lt_dec 2 0).
    + lia.
    + induction (le_lt_dec 2 1).
      * lia.
      * reflexivity.
Qed.

Lemma pa5 (a : Term): SysPrf PA (a * Zero = Zero)%nt.
Proof.
  replace (a * Zero = Zero)%nt with
    (substF (v#0 * Zero = Zero)%nt 0 a).
  - apply forallE.
    apply Axm; repeat (try right; constructor) || left.
  - reflexivity.
Qed.

Lemma pa6 (a b : Term) :  SysPrf PA (a * Succ b = a * b + a)%nt.
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  replace (a * Succ b = a * b + a)%nt with 
    (subAllFormula LNT
       (v#0 * Succ (v#1) = v#0 * v#1 + v#0)%nt
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  - apply (subAllCloseFrom LNT).
    simpl in |- *.
    apply Axm; repeat (try right; constructor) || left.
  - simpl in |- *.
    induction (le_lt_dec 2 0).
    + lia.
    + induction (le_lt_dec 2 1).
      * lia.
      * reflexivity.
Qed.

Lemma induct (f : Formula) (v : nat):
  let f_0 := substF f v Zero
  in let f_Sv := substF f v (Succ (v#v))%nt
     in  SysPrf PA f_0 ->
         SysPrf PA (allH v, f -> f_Sv)%nt
         -> SysPrf PA (allH v, f)%nt.
Proof. 
  intros ? ? H H0; eapply impE.
  - eapply impE.
    + apply (openClosed LNT).
      apply Axm; repeat left.
      unfold InductionSchema in |- *.
      unfold In in |- *.
      unfold PA7 in |- *.
      exists f, v; reflexivity.
    + apply H.
- apply H0.
Qed.

End PA.


