(**  NN2PA.v : 

Original version by Russel O'Connor

*)


From Coq Require Import Ensembles List Arith.

Require Import folProp  folProof  subProp  folLogic3  folReplace  NN
  PAtheory.
Require Export LNN2LNT.
Require Import subAll ListExt.
Import NNnotations.

Lemma NN2PA (f : fol.Formula LNN):
  folProof.SysPrf LNN NN f -> SysPrf PA (LNN2LNT_formula f). 
Proof.
  intro H; apply translateProof with NN.
  - apply closedPA1.
  - intros f0 H0; unfold NN in H0.
    destruct H0 as [x H0| x H0].
    + destruct  H0 as [x H0| x H0].
      * destruct H0 as [x H0| x H0].
        -- destruct H0 as [x H0| x H0].
           ++ destruct H0 as [x H0| x H0].
              ** destruct H0 as [x H0| x H0].
                 destruct H0 as [x H0| x H0].
                 destruct H0 as [x H0| x H0].
                 destruct H0.
                 apply Axm; repeat (try right; constructor) || left.
                 destruct H0.
                 apply Axm; repeat (try right; constructor) || left.
                 destruct H0.
                 apply Axm; repeat (try right; constructor) || left.
                 destruct H0.
                 apply Axm; repeat (try right; constructor) || left.
              ** destruct H0.
                 apply Axm; repeat (try right; constructor) || left.
           ++ destruct H0.
              apply Axm; repeat (try right; constructor) || left.
        -- destruct H0.
           apply NN72PA.
      * destruct H0.
        apply NN82PA.
    + destruct H0.
      apply NN92PA.
  - apply H.
Qed.


(** If  [F[x\0]], [F[x\1]] ... [F[x\m-1]] are provable in PA,
       then [ v_x <' m -> F] is also provable (where [a <' b] is the translation of [a < b] into PA).

   More precisely: 

*)
Lemma PAboundedLT :
  forall (m : nat) (F : LNT.Formula) (x : nat),
    (forall n : nat,
        n < m -> SysPrf PA (substF F x (natToTerm n))) ->
    SysPrf PA (LNN2LNT_formula (v#x < LNN.natToTerm m)%nn -> F)%nt.
Proof.
simple induction m. 
- intros F x H; apply impI.
  apply contradiction with 
    (LNN2LNT_formula (v#x < LNN.natToTerm 0)%nn).
  apply Axm; right; constructor.
  apply sysWeaken.
  replace (notH (LNN2LNT_formula (LNN.LT (var x) (LNN.natToTerm 0)))) 
    with
    (LNN2LNT_formula (notH  (LNN.LT (var x) (LNN.natToTerm 0)))).
  + apply NN2PA.
    apply nn7.
  + reflexivity.
- intros n H a x H0; apply impI.
  eapply orE.
  + apply impE with 
      (LNN2LNT_formula (LNN.LT (var x) (LNN.natToTerm (S n)))).
    * apply sysWeaken.
      assert (H1: SysPrf PA (LNN2LNT_formula
                     ((v#x < S_ (LNN.natToTerm n)) ->
                      (v#x < LNN.natToTerm n) \/ 
                        v#x = LNN.natToTerm n))%nn)
      by (apply NN2PA, nn8). 
      simpl in H1; simpl. 
      unfold orH; apply H1.
    * apply Axm; right; constructor.
  + apply sysWeaken.
    simpl in H; apply H; auto. 
  + apply sysWeaken, impI.
    rewrite <- (subFormulaId LNT a x).
    rewrite LNN2LNT_natToTerm.
    apply impE with (substF a x (natToTerm n)).
    * apply (subWithEquals LNT).
      apply eqSym.
      apply Axm; right; constructor.
    * apply sysWeaken.
      apply H0.
      apply Nat.lt_succ_diag_r .
Qed.
