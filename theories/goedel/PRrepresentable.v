(** TO DO: Define abbreviations and re-indent !!! 
**)
From Coq Require Import Arith.
From hydras.Ackermann Require Import extEqualNat.
From hydras.Ackermann Require Import subAll.
From hydras.Ackermann Require Import folProp.
From hydras.Ackermann Require Import subProp.
From hydras.Ackermann Require Import folReplace.
From hydras.Ackermann Require Import folLogic3.
From hydras.Ackermann Require Import NN.
From hydras.Ackermann Require Import NNtheory.
From hydras.Ackermann Require Import primRec.
From Coqprime Require Import ChineseRem.
From hydras.Ackermann Require Import expressible.
From Coq Require Import List.
From Coq Require Vector.
From hydras.Ackermann Require Import ListExt.
From hydras.Ackermann Require Import cPair.
From Coq Require Import Decidable.
From Coq Require Import Lia.
From hydras Require Import Compat815.

#[local] Arguments apply _ _ _ : clear implicits.

Import LispAbbreviations. 

Section Primitive_Recursive_Representable.

Definition Representable := Representable NN.
Definition RepresentableAlternate := RepresentableAlternate NN closedNN1.
Definition RepresentableHelp := RepresentableHelp NN.
Definition Representable_ext := Representable_ext NN.

Definition beta (a z : nat) : nat :=
  snd
    (proj1_sig
       (div_eucl (coPrimeBeta z (cPairPi1 a)) (gtBeta z (cPairPi1 a))
          (cPairPi2 a))).

Definition betaFormula : Formula :=
exH 3
  (v_ 3 < S_ (v_ 2) /\
   exH 4
     (v_ 4 < S_ (v_ 2) /\
      (v_ 3 + v_ 4) * S_ (v_ 3 + v_ 4) + natToTerm 2 * v_ 3 =
      natToTerm 2 * v_ 2 /\
      v_ 0 < S_ (v_ 3 * S_ (v_ 1)) /\
      exH 5 (v_ 5 < S_ (v_ 4) /\ v_ 0 + v_ 5 * S_ (v_ 3 * S_ (v_ 1)) = v_ 4)))%fol.
 
Lemma betaRepresentable : Representable 2 beta betaFormula.
Proof.
 assert (cPairLemma1 :
          forall a b : nat, (a + b) * S (a + b) + 2 * a = 2 * cPair a b).
 { intros a b. unfold cPair in |- *.
   assert (2 * sumToN (a + b) = (a + b) * S (a + b)) by
     (induction (a + b); simpl in |- *; lia).
    lia. }
 unfold Representable in |- *; split.
 - intros v H. simpl in H. lia.
 - simpl in |- *. intros a a0. unfold betaFormula in |- *.
   assert
      (forall (A : Formula) (v x a : nat),
       v <> x ->
       substituteFormula LNN (existH v A) x (natToTerm a) =
       existH v (substituteFormula LNN A x (natToTerm a))).
   { intros A v x a1 H; rewrite (subFormulaExist LNN).
     destruct (eq_nat_dec v x) as [H0 | H0]; try congruence.
     destruct (In_dec eq_nat_dec v (freeVarTerm LNN (natToTerm a1))) 
        as [i | i]; try reflexivity.
     elim (closedNatToTerm _ _ i). }
    assert
      (forall (t1 t2 : Term) (v a : nat),
       substituteFormula LNN (LT t1 t2) v (natToTerm a) =
       LT (substituteTerm LNN t1 v (natToTerm a))
          (substituteTerm LNN t2 v (natToTerm a))).
    { intros. unfold LT at 1 in |- *. now rewrite (subFormulaRelation LNN). }
    repeat first
    [ rewrite H; [| discriminate ]
    | rewrite H0
    | rewrite (subFormulaAnd LNN)
    | rewrite (subFormulaEqual LNN) ].
    simpl in |- *; repeat rewrite (subTermNil LNN).
   + assert
       (SysPrf NN
          (iffH
             (existH 3
                (andH (LT (var 3) (natToTerm (S a)))
                   (existH 4
                      (andH (LT (var 4) (natToTerm (S a)))
                         (andH
                            (equal
                               (Plus
                                  (Times (Plus (var 3) (var 4))
                                     (Succ (Plus (var 3) (var 4))))
                                  (Times (natToTerm 2) (var 3)))
                               (Times (natToTerm 2) (natToTerm a)))
                            (andH
                               (LT (var 0)
                                  (Succ (Times (var 3) (Succ (natToTerm a0)))))
                               (existH 5
                                  (andH (LT (var 5) (Succ (var 4)))
                                     (equal
                                        (Plus (var 0)
                                           (Times (var 5)
                                              (Succ
                                                 (Times (var 3)
                                                    (Succ (natToTerm a0))))))
                                        (var 4))))))))))
             (equal (var 0) (natToTerm (beta a a0))))); auto.
   apply iffI.
   * apply impI. apply existSys.
     -- apply closedNN.
     -- intros [H1 | H1]; try lia. 
        simpl in H1; elim (closedNatToTerm _ _ H1).
     -- apply impE with (LT (var 3) (natToTerm (S a))).
     ++ apply impE with
          (existH 4
             (andH (LT (var 4) (natToTerm (S a)))
                (andH
                   (equal
                      (Plus
                         (Times (Plus (var 3) (var 4))
                            (Succ (Plus (var 3) (var 4))))
                         (Times (natToTerm 2) (var 3)))
                      (Times (natToTerm 2) (natToTerm a)))
                   (andH (LT (var 0) 
                            (Succ (Times (var 3) (Succ (natToTerm a0)))))
                      (existH 5
                         (andH (LT (var 5) (Succ (var 4)))
                            (equal
                               (Plus (var 0)
                                  (Times (var 5)
                                     (Succ (Times (var 3) 
                                              (Succ (natToTerm a0))))))
                               (var 4)))))))).
        ** apply sysWeaken. apply impI. apply existSys.
           --- apply closedNN.
           --- replace
               (freeVarFormula LNN
                  (impH (LT (var 3) (natToTerm (S a)))
                     (equal (var 0) (natToTerm (beta a a0))))) 
               with
               ((freeVarTerm LNN (var 3) ++ 
                   freeVarTerm LNN (natToTerm (S a))) ++
                  freeVarFormula LNN (equal (var 0) 
                                        (natToTerm (beta a a0))))
               by (rewrite <- freeVarLT; reflexivity).
               intros [H1 | H1]; try lia.
               destruct (in_app_or _ _ _ H1) as [H2 | H2].
           +++ elim (closedNatToTerm _ _ H2).
           +++ destruct H2 as [H2| H2]; try lia. 
               elim (closedNatToTerm _ _ H2).
           --- apply impTrans with
                      (andH (equal (var 3) (natToTerm (cPairPi1 a)))
                         (equal (var 4) (natToTerm (cPairPi2 a)))).
           +++ apply impI.
               apply impE with
                 (equal
                    (Plus (Times (Plus (var 3) (var 4)) 
                             (Succ (Plus (var 3) (var 4))))
                       (Times (natToTerm 2) (var 3)))
                    (Times (natToTerm 2) (natToTerm a))).
               *** apply impE with (LT (var 4) (natToTerm (S a))).
                   ---- apply impE with 
                          (LT (var 3) (natToTerm (S a))).
                   ++++ do 2 apply sysWeaken.
                        apply boundedLT; intros n H1.
                        rewrite (subFormulaImp LNN).
                        unfold LT at 1 in |- *.
                        rewrite (subFormulaRelation LNN).
                        simpl in |- *.
                        rewrite subTermNil.
                        **** (* fold (var 4) in |- *. *)
                             replace 
                               (apply LNN Languages.Succ 
                                  (Tcons (natToTerm a)
                                     (Tnil)))
                               with (natToTerm (S a)); 
                               [| reflexivity ].
                             fold (LT (var 4) (natToTerm (S a))).
                             apply boundedLT. intros n0 H2.
                             repeat rewrite (subFormulaImp LNN).
                             repeat rewrite (subFormulaAnd LNN).
                             repeat rewrite (subFormulaEqual LNN).
                             assert 
                               ((substituteTerm LNN
                                   (substituteTerm LNN
                                      (Plus (Times (Plus (var 3) (var 4)) 
                                               (Succ (Plus (var 3) (var 4))))
                                         (Times (Succ (Succ Zero)) (var 3))) 
                                      3 (natToTerm n)) 4
                                   (natToTerm n0)) =
                                  (Plus
                                     (Times (Plus (natToTerm n) (natToTerm n0))
                                        (Succ (Plus (natToTerm n) 
                                                 (natToTerm n0))))
                                     (Times (Succ (Succ Zero))
                                        (natToTerm n)))) as H3.
                             { simpl in |- *.
                               repeat (rewrite (subTermNil LNN (natToTerm n)));
                                 [| apply closedNatToTerm].
                               reflexivity. }
                             rewrite H3; clear H3.
                             assert
                               ((substituteTerm LNN
                                   (substituteTerm LNN 
                                      (Times (Succ (Succ Zero)) (natToTerm a)) 
                                      3  (natToTerm n)) 4 (natToTerm n0)) =
                                  (Times (natToTerm 2) (natToTerm a))).
                             { simpl in |- *;
                               repeat (rewrite (subTermNil _ (natToTerm a)); 
                                       [| apply closedNatToTerm ]).
                               reflexivity. }
                             simpl in |- *.
                             assert
                               (forall (a b : nat) (s : Term),
                                   substituteTerm LNN (natToTerm a) b s =
                                     natToTerm a).
                             { intros; apply (subTermNil LNN).
                               apply closedNatToTerm. }
                             repeat rewrite H4.
                             apply impTrans with
                               (equal 
                                (natToTerm ((n + n0) * S (n + n0) + 2 * n)) 
                                (natToTerm (2 * a))).
                             { apply impI. eapply eqTrans.
                               - apply sysWeaken; apply eqSym; apply natPlus.
                               - eapply eqTrans.
                               + apply eqPlus. eapply eqTrans.
                                 * apply sysWeaken; apply eqSym; apply natTimes.
                                 * eapply eqTrans.
                                   -- apply eqTimes.
                                   ++ apply sysWeaken; apply eqSym. 
                                      apply natPlus.
                                   ++ eapply eqTrans.
                                      ** apply sysWeaken; apply eqSym.
                                         simpl in |- *. apply eqSucc. 
                                         apply natPlus.
                                      ** apply eqRefl.
                                   -- apply eqRefl.
                                 * apply sysWeaken; apply eqSym. 
                                   apply natTimes.
                               + eapply eqTrans.
                                 * apply Axm; right; constructor.
                                 * apply sysWeaken.
                                   replace
                                     (apply LNN Languages.Succ
                                        (Tcons (apply LNN Languages.Succ
                                              (Tcons 
                                                 (apply LNN Languages.Zero
                                                    (Tnil))
                                                 (Tnil)))
                                           (Tnil)))
                                     with (natToTerm 2) by reflexivity.
                                   apply natTimes. }
                             { rewrite cPairLemma1.
                               destruct (eq_nat_dec a (cPair n n0)) as [e | e].
                               - rewrite e, cPairProjections1, 
                                   cPairProjections2.
                                               apply impI. 
                                               apply andI; apply eqRefl.
                               - apply impI.
                                 apply contradiction with
                                   (equal (natToTerm (2 * cPair n n0)) 
                                      (natToTerm (2 * a))).
                               + apply Axm; right; constructor.
                               + apply sysWeaken. apply natNE. lia. }
                        **** apply closedNatToTerm.
                   ++++ apply Axm; right; constructor.
                   ---- eapply andE1. apply Axm; left; right; constructor.
               *** eapply andE1. eapply andE2.
                   apply Axm; left; right; constructor.
           +++ repeat apply impI.
               apply impE with
                         (existH 5
                           (andH (LT (var 5) (Succ (var 4)))
                             (equal
                               (Plus (var 0)
                                  (Times (var 5) 
                                     (Succ (Times (var 3) 
                                              (Succ (natToTerm a0))))))
                                     (var 4)))).
               *** apply impE with (LT (var 0) 
                                             (Succ (Times (var 3)
                                                      (Succ (natToTerm a0))))).
                   ---- rewrite <-
                                  (subFormulaId LNN
                                     (impH (LT (var 0) 
                                              (Succ (Times (var 3) 
                                                       (Succ (natToTerm a0)))))
                                      (impH
                                       (existH 5
                                        (andH (LT (var 5) (Succ (var 4)))
                                         (equal
                                          (Plus (var 0)
                                            (Times (var 5)
                                             (Succ (Times (var 3)
                                               (Succ (natToTerm a0))))))
                                          (var 4))))
                                       (equal (var 0) 
                                          (natToTerm (beta a a0))))) 3).
                                 apply impE with
                                  (substituteFormula LNN
                                   (impH (LT (var 0) 
                                            (Succ (Times (var 3) 
                                                     (Succ (natToTerm a0)))))
                                     (impH
                                       (existH 5
                                        (andH (LT (var 5) (Succ (var 4)))
                                          (equal
                                           (Plus (var 0)
                                             (Times (var 5)
                                               (Succ (Times (var 3)
                                                        (Succ 
                                                           (natToTerm a0))))))
                                           (var 4)))) 
                                       (equal (var 0) 
                                          (natToTerm (beta a a0))))) 3
                                    (natToTerm (cPairPi1 a))).
                                 ++++ apply (subWithEquals LNN). apply eqSym. eapply andE1.
                                      apply Axm; right; constructor.
                                 ++++ rewrite <-
                                       (subFormulaId LNN
                                          (substituteFormula LNN
                                             (impH (LT (var 0) (Succ (Times (var 3) (Succ (natToTerm a0)))))
                                                (impH
                                                   (existH 5
                                                      (andH (LT (var 5) (Succ (var 4)))
                                                         (equal
                                                            (Plus (var 0)
                                                               (Times (var 5)
                                                                  (Succ (Times (var 3) (Succ (natToTerm a0))))))
                                                            (var 4)))) (equal (var 0) (natToTerm (beta a a0))))) 3
                                             (natToTerm (cPairPi1 a))) 4).
                                      apply
                                       impE
                                        with
                                          (substituteFormula LNN
                                             (substituteFormula LNN
                                                (impH (LT (var 0) (Succ (Times (var 3) (Succ (natToTerm a0)))))
                                                   (impH
                                                      (existH 5
                                                         (andH (LT (var 5) (Succ (var 4)))
                                                            (equal
                                                               (Plus (var 0)
                                                                  (Times (var 5)
                                                                     (Succ (Times (var 3) (Succ (natToTerm a0))))))
                                                               (var 4)))) (equal (var 0) (natToTerm (beta a a0)))))
                                                3 (natToTerm (cPairPi1 a))) 4 (natToTerm (cPairPi2 a))).
                                      ***** apply (subWithEquals LNN). apply eqSym. eapply andE2.
                                            apply Axm; right; constructor.
                                      ***** do 2 apply sysWeaken.
                                            repeat first
                                            [ rewrite H; [| discriminate ]
                                            | rewrite H0
                                            | rewrite (subFormulaImp LNN)
                                            | rewrite (subFormulaAnd LNN)
                                            | rewrite (subFormulaEqual LNN) ].
                                            simpl in |- *.
                                            repeat (rewrite (subTermNil LNN); [| apply closedNatToTerm ]).
                                            repeat (rewrite (subTermNil LNN (natToTerm a0)); [| apply closedNatToTerm ]).
                                            repeat (rewrite (subTermNil LNN (natToTerm (beta a a0))); [| apply closedNatToTerm ]).
                                            apply impTrans with (LT (var 0) (natToTerm (S (cPairPi1 a * S a0)))).
                                            { apply impI.
                                              apply
                                               impE
                                                with
                                                 (substituteFormula LNN (LT (var 0) (var 1)) 1
                                                  (natToTerm (S (cPairPi1 a * S a0)))).
                                              - unfold LT at 2 in |- *.
                                                rewrite (subFormulaRelation LNN).
                                                apply impRefl.
                                              - apply
                                                  impE
                                                    with
                                                     (substituteFormula LNN (LT (var 0) (var 1)) 1
                                                      (Succ (Times (natToTerm (cPairPi1 a)) (Succ (natToTerm a0))))).
                                                + apply (subWithEquals LNN). apply sysWeaken. simpl in |- *.
                                                  apply eqSucc.
                                                  replace (Succ (natToTerm a0)) with (natToTerm (S a0)) by reflexivity.
                                                  apply natTimes.
                                                + unfold LT at 2 in |- *.
                                                  rewrite (subFormulaRelation LNN).
                                                  apply Axm; right; constructor. }
                                            { apply boundedLT. intros n H1.
                                              repeat first
                                              [ rewrite H; [| discriminate ]
                                              | rewrite H0
                                              | rewrite (subFormulaImp LNN)
                                              | rewrite (subFormulaAnd LNN)
                                              | rewrite (subFormulaEqual LNN) ].
                                              simpl in |- *.
                                              repeat (rewrite (subTermNil LNN); [| apply closedNatToTerm ]).
                                              apply impI. apply existSys.
                                              - apply closedNN.
                                              - simpl in |- *. intro H2.
                                                destruct (in_app_or _ _ _ H2) as [H3 | H3]; 
                                                  elim (closedNatToTerm _ _ H3).
                                              - apply
                                                 impE
                                                  with
                                                    (fol.equal 
                                                       (apply LNN Languages.Plus
                                                          (Tcons (natToTerm n)
                                                             (Tcons                                                                 (apply LNN Languages.Times
                                                                   (Tcons (var  5)
                                                                      (Tcons 
                                                                         (apply LNN Languages.Succ
                                                                            (Tcons 
                                                                               (apply LNN Languages.Times
                                                                                  (Tcons  (natToTerm (cPairPi1 a))
                                                                                     (Tcons 
                                                                                        (apply LNN Languages.Succ
                                                                                           (Tcons  
                                                                                              (natToTerm a0) 
                                                                                              (Tnil))) 
                                                                                        (Tnil)))) 
                                                                               (Tnil ))) (Tnil)))) 
                                                                (Tnil )))) (natToTerm (cPairPi2 a))).
                                                + apply impE with (LT (var 5) (natToTerm (S (cPairPi2 a)))).
                                                  apply sysWeaken.
                                                  * apply boundedLT. intros n0 H2.
                                                    repeat first
                                                     [ rewrite H; [| discriminate ]
                                                     | rewrite H0
                                                     | rewrite (subFormulaImp LNN)
                                                     | rewrite (subFormulaAnd LNN)
                                                     | rewrite (subFormulaEqual LNN) ].
                                                    simpl in |- *.
                                                    repeat (rewrite (subTermNil LNN); [| apply closedNatToTerm ]).
                                                    apply impI. destruct (eq_nat_dec n (beta a a0)) as [e | e].
                                                    -- rewrite <- e. apply eqRefl.
                                                    -- apply
                                                        contradiction
                                                         with
                                                           (equal (natToTerm (n + n0 * S (cPairPi1 a * S a0)))
                                                              (natToTerm (cPairPi2 a))).
                                                       ++ eapply eqTrans; [| apply Axm; right; constructor ].
                                                          apply sysWeaken. eapply eqTrans.
                                                          ** apply eqSym. apply natPlus.
                                                          ** replace
                                                              (apply LNN Languages.Plus
                                                                 (Tcons  (natToTerm n)
                                                                    (Tcons 
                                                                       (apply LNN Languages.Times
                                                                          (Tcons  (natToTerm n0)
                                                                             (Tcons 
                                                                                (apply LNN Languages.Succ
                                                                                   (Tcons 
                                                                                      (apply LNN Languages.Times
                                                                                         (Tcons  (natToTerm (cPairPi1 a))
                                                                                            (Tcons 
                                                                                               (apply LNN Languages.Succ
                                                                                                  (Tcons (natToTerm a0) (Tnil)))
                                                                                               (Tnil )))) (Tnil ))) 
                                                                                (Tnil )))) (Tnil )))) with
                                                              (Plus (natToTerm n)
                                                                 (Times (natToTerm n0)
                                                                    (Succ (Times (natToTerm (cPairPi1 a)) (Succ (natToTerm a0))))))
                                                              by reflexivity.
                                                              apply eqPlus.
                                                              --- apply eqRefl.
                                                              --- eapply eqTrans.
                                                                  +++ apply eqSym. apply natTimes.
                                                                  +++ apply eqTimes. apply eqRefl.
                                                                      simpl in |- *. apply eqSucc.
                                                                      replace (Succ (natToTerm a0)) 
                                                                        with (natToTerm (S a0)) by reflexivity.
                                                                      apply eqSym. apply natTimes.
                                                       ++ apply sysWeaken. apply natNE.
                                                          intro; elim e. unfold beta in |- *.
                                                          destruct
                                                            (div_eucl (coPrimeBeta a0 (cPairPi1 a)) (gtBeta a0 (cPairPi1 a)) (cPairPi2 a)) as [[a1 b0] H4].
                                                          simpl in H4. simpl in |- *.
                                                          destruct H4 as (H4, H5).
                                                          unfold coPrimeBeta in H4.
                                                          rewrite Nat.add_comm in H3.
                                                          eapply uniqueRem.
                                                          ** apply Nat.lt_0_succ.
                                                          ** exists n0; split; [symmetry |]; eauto.
                                                          ** exists a1; split; eauto.
                                                  * eapply andE1. apply Axm; right; constructor.
                                                + eapply andE2. apply Axm; right; constructor. }
                            ---- eapply andE1. eapply andE2. eapply andE2. apply Axm; left; right; constructor.
                        *** eapply andE2. eapply andE2. eapply andE2. apply Axm; left; right; constructor.
             ** eapply andE2. apply Axm; right; constructor.
          ++ eapply andE1. apply Axm; right; constructor.
      * apply impI. unfold beta in |- *.
        destruct (div_eucl (coPrimeBeta a0 (cPairPi1 a)) (gtBeta a0 (cPairPi1 a)) (cPairPi2 a)) as [x H1].
        induction x as (a1, b). simpl in |- *. simpl in H1. destruct H1 as (H1, H2).
        apply existI with (natToTerm (cPairPi1 a)). rewrite (subFormulaAnd LNN). apply andI.
        -- apply sysWeaken. rewrite H0. simpl in |- *. rewrite subTermNil.
           ++ replace (apply LNN Languages.Succ (Tcons (natToTerm a) (Tnil ))) with (natToTerm (S a)) by reflexivity.
              apply natLT. apply Nat.lt_succ_r. apply Nat.le_trans with (cPair (cPairPi1 a) (cPairPi2 a)).
              apply cPairLe1. rewrite cPairProjections. apply le_n.
           ++ apply closedNatToTerm.
        -- rewrite H; try lia.
           ++ apply existI with (natToTerm (cPairPi2 a)). repeat rewrite (subFormulaAnd LNN). apply andI.
              ** apply sysWeaken. repeat rewrite H0. simpl in |- *.
                 repeat rewrite (subTermNil LNN (natToTerm a)).
                 --- replace (apply LNN Languages.Succ (Tcons (natToTerm a) (Tnil ))) with (natToTerm (S a))
                       by reflexivity.
                     apply natLT. apply Nat.lt_succ_r. apply Nat.le_trans with (cPair (cPairPi1 a) (cPairPi2 a)).
                     +++ apply cPairLe2.
                     +++ rewrite cPairProjections. apply le_n.
                 --- apply closedNatToTerm.
                 --- apply closedNatToTerm.
              ** apply andI.
                 --- repeat rewrite (subFormulaEqual LNN). simpl in |- *.
                     repeat
                      (rewrite (subTermNil LNN (natToTerm (cPairPi1 a)));
                        [| apply closedNatToTerm ]).
                     repeat
                      (rewrite (subTermNil LNN (natToTerm a)); [| apply closedNatToTerm ]).
                     replace
                      (equal 
                         (apply LNN Languages.Plus
                            (Tcons
                               (apply LNN Languages.Times
                                  (Tcons
                                     (apply LNN Languages.Plus
                                        (Tcons (natToTerm (cPairPi1 a))
                                           (Tcons (natToTerm (cPairPi2 a)) (Tnil ))))
                                     (Tcons
                                        (apply LNN Languages.Succ
                                           (Tcons
                                              (apply LNN Languages.Plus
                                                 (Tcons (natToTerm (cPairPi1 a))
                                                    (Tcons (natToTerm (cPairPi2 a))
                                                       (Tnil )))) (Tnil )))
                                        (Tnil))))
                               (Tcons
                                  (apply LNN Languages.Times
                                     (Tcons
                                        (apply LNN Languages.Succ
                                           (Tcons
                                              (apply LNN Languages.Succ
                                                 (Tcons
                                                    (apply LNN Languages.Zero (Tnil ))
                                                    (Tnil ))) (Tnil )))
                                        (Tcons (natToTerm (cPairPi1 a)) (Tnil ))))
                                  (Tnil ))))
                         (apply LNN Languages.Times
                            (Tcons
                               (apply LNN Languages.Succ
                                  (Tcons
                                     (apply LNN Languages.Succ
                                        (Tcons (apply LNN Languages.Zero (Tnil ))
                                           (Tnil ))) (Tnil )))
                               (Tcons (natToTerm a) (Tnil ))))) with
                      (equal
                         (Plus
                            (Times (Plus (natToTerm (cPairPi1 a)) (natToTerm (cPairPi2 a)))
                               (Succ (Plus (natToTerm (cPairPi1 a)) (natToTerm (cPairPi2 a)))))
                            (Times (natToTerm 2) (natToTerm (cPairPi1 a))))
                         (Times (natToTerm 2) (natToTerm a))) by reflexivity.
                     apply
                      eqTrans
                       with
                         (natToTerm
                            ((cPairPi1 a + cPairPi2 a) * S (cPairPi1 a + cPairPi2 a) +
                             2 * cPairPi1 a)).
                     +++ apply sysWeaken. apply eqSym. eapply eqTrans.
                         *** apply eqSym. apply natPlus.
                         *** apply eqPlus.
                             ---- eapply eqTrans.
                                  ++++ apply eqSym. apply natTimes.
                                  ++++ apply eqTimes.
                                       **** apply eqSym. apply natPlus.
                                       **** simpl in |- *. apply eqSucc. apply eqSym. apply natPlus.
                             ---- apply eqSym. apply natTimes.
                     +++ rewrite cPairLemma1. apply eqSym. rewrite cPairProjections. apply sysWeaken. apply natTimes.
                 --- apply andI.
                     +++ rewrite <-
                          (subFormulaId LNN
                             (substituteFormula LNN
                                (substituteFormula LNN
                                   (LT (var 0) (Succ (Times (var 3) (Succ (natToTerm a0))))) 3
                                   (natToTerm (cPairPi1 a))) 4 (natToTerm (cPairPi2 a))) 0).
                         apply
                          impE
                           with
                             (substituteFormula LNN
                                (substituteFormula LNN
                                   (substituteFormula LNN
                                      (LT (var 0) (Succ (Times (var 3) (Succ (natToTerm a0))))) 3
                                      (natToTerm (cPairPi1 a))) 4 (natToTerm (cPairPi2 a))) 0
                                (natToTerm b)).
                         *** apply (subWithEquals LNN). apply eqSym. apply Axm; right; constructor.
                         *** apply sysWeaken. repeat rewrite H0. simpl in |- *.
                             repeat
                              (rewrite (subTermNil LNN (natToTerm (cPairPi1 a)));
                                [| apply closedNatToTerm ]).
                             repeat
                              (rewrite (subTermNil LNN (natToTerm a0)); [| apply closedNatToTerm ]).
                             apply
                              impE
                               with
                                 (substituteFormula LNN (LT (natToTerm b) (var 0)) 0
                                    (Succ (Times (natToTerm (cPairPi1 a)) (Succ (natToTerm a0))))).
                             ---- unfold LT at 1 in |- *. rewrite (subFormulaRelation LNN).
                                  simpl in |- *.
                                  repeat
                                   (rewrite (subTermNil LNN (natToTerm b)); [| apply closedNatToTerm ]).
                                  apply impRefl.
                             ---- apply
                                   impE
                                    with
                                      (substituteFormula LNN (LT (natToTerm b) (var 0)) 0
                                         (natToTerm (S (cPairPi1 a * S a0)))).
                                  ++++ apply (subWithEquals LNN). simpl in |- *. apply eqSucc.
                                       replace (Succ (natToTerm a0)) with (natToTerm (S a0)) by reflexivity.
                                       apply eqSym. apply natTimes.
                                  ++++ rewrite H0.
                                       repeat (rewrite (subTermNil LNN (natToTerm b)); [| apply closedNatToTerm ]).
                                       rewrite (subTermVar1 LNN). apply natLT. apply H2.
                     +++ repeat (rewrite H; [| discriminate ]).
                         apply existI with (natToTerm a1).
                         rewrite <-
                          (subFormulaId LNN
                             (substituteFormula LNN
                                (substituteFormula LNN
                                   (substituteFormula LNN
                                      (andH (LT (var 5) (Succ (var 4)))
                                         (equal
                                            (Plus (var 0)
                                               (Times (var 5)
                                                  (Succ (Times (var 3) (Succ (natToTerm a0))))))
                                            (var 4))) 3 (natToTerm (cPairPi1 a))) 4
                                   (natToTerm (cPairPi2 a))) 5 (natToTerm a1)) 0).
                         apply
                          impE
                           with
                             (substituteFormula LNN
                                (substituteFormula LNN
                                   (substituteFormula LNN
                                      (substituteFormula LNN
                                         (andH (LT (var 5) (Succ (var 4)))
                                            (equal
                                               (Plus (var 0)
                                                  (Times (var 5)
                                                     (Succ (Times (var 3) (Succ (natToTerm a0))))))
                                               (var 4))) 3 (natToTerm (cPairPi1 a))) 4
                                      (natToTerm (cPairPi2 a))) 5 (natToTerm a1)) 0 
                                (natToTerm b)).
                         *** apply (subWithEquals LNN). apply eqSym. apply Axm; right; constructor.
                         *** apply sysWeaken.
                             repeat first
                              [ rewrite H; [| discriminate ]
                              | rewrite H0
                              | rewrite (subFormulaImp LNN)
                              | rewrite (subFormulaAnd LNN)
                              | rewrite (subFormulaEqual LNN) ].
                             simpl in |- *.
                             repeat
                              (rewrite (subTermNil LNN (natToTerm (cPairPi1 a)));
                                [| apply closedNatToTerm ]).
                             repeat
                              (rewrite (subTermNil LNN (natToTerm a0)); [| apply closedNatToTerm ]).
                             repeat
                              (rewrite (subTermNil LNN (natToTerm (cPairPi2 a)));
                                [| apply closedNatToTerm ]).
                             repeat
                              (rewrite (subTermNil LNN (natToTerm a1)); [| apply closedNatToTerm ]).
                             apply andI.
                             ---- replace (apply LNN Languages.Succ (Tcons (natToTerm (cPairPi2 a)) (Tnil ))) 
                                    with (natToTerm (S (cPairPi2 a))) by reflexivity.
                                  apply natLT. unfold coPrimeBeta in *. lia.
                             ---- replace
                                   (apply LNN Languages.Plus
                                      (Tcons (natToTerm b)
                                         (Tcons
                                            (apply LNN Languages.Times
                                               (Tcons (natToTerm a1)
                                                  (Tcons
                                                     (apply LNN Languages.Succ
                                                        (Tcons
                                                           (apply LNN Languages.Times
                                                              (Tcons (natToTerm (cPairPi1 a))
                                                                 (Tcons
                                                                    (apply LNN Languages.Succ
                                                                       (Tcons (natToTerm a0) (Tnil )))
                                                                    (Tnil )))) (Tnil ))) 
                                                     (Tnil )))) (Tnil )))) with
                                   (Plus (natToTerm b)
                                      (Times (natToTerm a1)
                                         (Succ (Times (natToTerm (cPairPi1 a)) (Succ (natToTerm a0)))))) by reflexivity.
                                  apply eqTrans with (natToTerm (a1 *  coPrimeBeta a0 (cPairPi1 a) + b)).
                                  ++++ rewrite Nat.add_comm. apply eqSym. eapply eqTrans.
                                       **** apply eqSym. apply natPlus.
                                       **** apply eqPlus.
                                            +++++ apply eqRefl.
                                            +++++ eapply eqTrans.
                                                  ***** apply eqSym. apply natTimes.
                                                  ***** apply eqTimes.
                                                         apply eqRefl.
                                                         unfold coPrimeBeta in |- *. simpl in |- *.
                                                              apply eqSucc.
                                                              replace (Succ (natToTerm a0)) with (natToTerm (S a0)) by reflexivity.
                                                              apply eqSym. apply natTimes.
                                  ++++ rewrite <- H1. apply eqRefl.
   + apply closedNatToTerm.
Qed.

Fixpoint addExists (m n : nat) (f : Formula) {struct n} : Formula :=
  match n with
  | O => f
  | S n' => existH (n' + m) (addExists m n' f)
  end.

Lemma freeVarAddExists1 :
 forall (n m v : nat) (A : Formula),
 In v (freeVarFormula LNN (addExists m n A)) -> In v (freeVarFormula LNN A).
Proof.
  intros n m v A H. induction n as [| n Hrecn].
  - simpl in H. exact H.
  - simpl in H. apply Hrecn. eapply In_list_remove1. exact H.
Qed.

Lemma freeVarAddExists2 :
 forall (n m v : nat) (A : Formula),
 In v (freeVarFormula LNN (addExists m n A)) -> n + m <= v \/ v < m.
Proof.
  intros n m v A H. induction n as [| n Hrecn]; try lia.
  simpl in H. simpl in |- *.
  assert (In v (freeVarFormula LNN (addExists m n A))) as H1.
  { eapply In_list_remove1. exact H. }
  pose proof (In_list_remove2 _ _ _ _ _ H).
  pose proof (Hrecn H1). lia.
Qed.

Lemma reduceAddExistsOneWay :
 forall (n m : nat) (A B : Formula),
 SysPrf NN (impH A B) -> SysPrf NN (impH (addExists m n A) (addExists m n B)).
Proof.
  intros n m A B H. apply impI. induction n as [| n Hrecn].
  - apply impE with A.
    + apply sysWeaken. apply H.
    + apply Axm; right; constructor.
  - simpl in |- *. apply existSys.
    + apply closedNN.
    + simpl in |- *; intro H0.
      pose proof (In_list_remove2 _ _ _ _ _ H0). congruence.
    + apply existSimp. exact Hrecn.
Qed.

Lemma reduceAddExists :
 forall (n m : nat) (A B : Formula),
 SysPrf NN (iffH A B) -> SysPrf NN (iffH (addExists m n A) (addExists m n B)).
Proof.
  intros n m A B H. induction n as [| n Hrecn]; simpl in |- *; auto.
  apply (reduceExist LNN); auto. apply closedNN.
Qed.

Lemma subAddExistsNice :
 forall (n m : nat) (A : Formula) (v : nat) (s : Term),
 n + m <= v \/ v < m ->
 (forall v : nat, In v (freeVarTerm LNN s) -> n + m <= v \/ v < m) ->
 substituteFormula LNN (addExists m n A) v s =
 addExists m n (substituteFormula LNN A v s).
Proof.
  intros n m A v s H H0. induction n as [| n Hrecn]; simpl in |- *; auto.
  rewrite (subFormulaExist LNN).
  destruct (eq_nat_dec (n + m) v) as [e | e]; try lia.
  destruct (in_dec Nat.eq_dec (n + m) (freeVarTerm LNN s)) as [e0 | e0].
  - pose proof (H0 _ e0). lia.
  - rewrite Hrecn.
    + reflexivity.
    + lia.
    + intros v0 H1. pose proof (H0 _ H1). lia.
Qed.

Fixpoint addForalls (m n : nat) (f : Formula) {struct n} : Formula :=
  match n with
  | O => f
  | S n' => forallH (n' + m) (addForalls m n' f)
  end.

Lemma freeVarAddForalls1 :
 forall (n m v : nat) (A : Formula),
 In v (freeVarFormula LNN (addForalls m n A)) -> In v (freeVarFormula LNN A).
Proof.
  intros n m v A H. induction n as [| n Hrecn]; simpl in H; auto.
  apply Hrecn. eapply In_list_remove1. exact H.
Qed.

Lemma freeVarAddForalls2 :
 forall (n m v : nat) (A : Formula),
 In v (freeVarFormula LNN (addForalls m n A)) -> n + m <= v \/ v < m.
Proof.
  intros n m v A H. induction n as [| n Hrecn]; try lia.
  simpl in H. simpl in |- *.
  assert (In v (freeVarFormula LNN (addForalls m n A))).
  { eapply In_list_remove1. exact H. }
  pose proof (Hrecn H0). pose proof (In_list_remove2 _ _ _ _ _ H). lia.
Qed.

Lemma reduceAddForalls :
 forall (n m : nat) (A B : Formula),
 SysPrf NN (iffH A B) ->
 SysPrf NN (iffH (addForalls m n A) (addForalls m n B)).
Proof.
  intros n m A B H. induction n as [| n Hrecn]; simpl in |- *; auto.
  apply (reduceForall LNN). apply closedNN. auto.
Qed.

Lemma subAddForallsNice :
 forall (n m : nat) (A : Formula) (v : nat) (s : Term),
 n + m <= v \/ v < m ->
 (forall v : nat, In v (freeVarTerm LNN s) -> n + m <= v \/ v < m) ->
 substituteFormula LNN (addForalls m n A) v s =
 addForalls m n (substituteFormula LNN A v s).
Proof.
  intros n m A v s H H0. induction n as [| n Hrecn]; simpl in |- *; auto.
  rewrite (subFormulaForall LNN). destruct (eq_nat_dec (n + m) v) as [e | e]; try lia.
  destruct (in_dec Nat.eq_dec (n + m) (freeVarTerm LNN s)) as [e0 | e0].
  - pose proof (H0 _ e0). lia.
  - rewrite Hrecn.
    + reflexivity.
    + lia.
    + intros v0 H1. pose proof (H0 _ H1). lia.
Qed.

Fixpoint FormulasToFormula (n w m : nat)
 (vs : Vector.t (Formula * naryFunc n) m) {struct vs} : Formula :=
  match vs with
  | Vector.nil => equal (var 0) (var 0)
  | Vector.cons v m' vs' =>
      andH (substituteFormula LNN (fst v) 0 (var (S m' + w)))
        (FormulasToFormula n w m' vs')
  end.

Fixpoint FormulasToFuncs (n m : nat) (vs : Vector.t (Formula * naryFunc n) m)
 {struct vs} : Vector.t (naryFunc n) m :=
  match vs in (Vector.t _ m) return (Vector.t (naryFunc n) m) with
  | Vector.nil => Vector.nil _
  | Vector.cons v m' vs' => Vector.cons _ (snd v) m' (FormulasToFuncs n m' vs')
  end.

Fixpoint RepresentablesHelp (n m : nat)
 (vs : Vector.t (Formula * naryFunc n) m) {struct vs} : Prop :=
  match vs with
  | Vector.nil => True
  | Vector.cons a m' vs' =>
      RepresentableHelp _ (snd a) (fst a) /\ RepresentablesHelp n m' vs'
  end.

Definition succFormula : Formula := equal (var 0) (Succ (var 1)).

Remark succRepresentable : Representable 1 S succFormula.
Proof.
  unfold Representable in |- *. split.
  - simpl. lia.
  - intros a. unfold succFormula in |- *.
    rewrite (subFormulaEqual LNN). apply iffRefl.
Qed.

Definition zeroFormula : Formula := equal (var 0) Zero.

Remark zeroRepresentable : Representable 0 0 zeroFormula.
Proof.
  unfold Representable in |- *. split.
  - simpl. lia.
  - apply iffRefl.
Qed.

Definition projFormula (m : nat) : Formula := equal (var 0) (var (S m)).


Remark projRepresentable :
 forall (n m : nat) (pr : m < n),
 Representable n (evalProjFunc n m pr) (projFormula m).
Proof.
  intros n m pr; unfold Representable in |- *. split.
  - simpl. lia.
  - induction n as [| n Hrecn]; try lia.
    simpl in |- *. intros a. destruct (Nat.eq_dec m n) as [e | e].
    + rewrite e. clear e Hrecn pr m. induction n as [| n Hrecn].
      * simpl in |- *. unfold projFormula in |- *.
        rewrite (subFormulaEqual LNN). apply iffRefl.
      * simpl in |- *. intros a0. unfold projFormula in |- *.
        repeat rewrite (subFormulaEqual LNN). simpl in |- *.
        destruct (Nat.eq_dec n n); try lia.
        replace
          (equal  (var 0)
            (substituteTerm LNN (natToTerm a) (S n)
              (natToTerm a0)))
          with
          (substituteFormula LNN (equal (var 0)
                                  (var (S n))) (S n)
              (natToTerm a)).
        -- auto.
        -- rewrite (subFormulaEqual LNN); simpl in |- *.
           destruct (Nat.eq_dec n n); try lia.
           rewrite subTermNil; try reflexivity.
           apply closedNatToTerm.
    + apply RepresentableAlternate with (equal (var 0) (var (S m))).
      * apply iffSym. apply (subFormulaNil LNN). simpl in |- *. lia.
      * auto.
Qed.


Definition composeSigmaFormula (n w m : nat) (A : Vector.t (Formula * naryFunc n) m)
  (B : Formula) : Formula :=
  addExists (S w) m
    (andH (FormulasToFormula n w m A)
       (subAllFormula LNN B
          (fun x : nat =>
           match x with
           | O => var 0
           | S x' => var (S x' + w)
           end))).


Remark composeSigmaRepresentable :
 forall n w m : nat,
 n <= w ->
 forall (A : Vector.t (Formula * naryFunc n) m) (B : Formula) (g : naryFunc m),
 RepresentablesHelp n m A ->
 Vector.t_rect (Formula * naryFunc n) (fun _ _ => Prop) True
   (fun (pair : Formula * naryFunc n) (m : nat) (v : Vector.t _ m) (rec : Prop) =>
    (forall v : nat, In v (freeVarFormula LNN (fst pair)) -> v <= n) /\ rec)
   m A ->
 Representable m g B ->
 Representable n (evalComposeFunc n m (FormulasToFuncs n m A) g)
   (composeSigmaFormula n w m A B).
Proof.
  assert
  (forall n w m : nat,
   n <= w ->
   forall (A : Vector.t (Formula * naryFunc n) m) (B : Formula) (g : naryFunc m),
   RepresentablesHelp n m A ->
   Vector.t_rect (Formula * naryFunc n) (fun _ _ => Prop) True
     (fun (pair : Formula * naryFunc n) (m : nat) (v : Vector.t _ m)
        (rec : Prop) =>
      (forall v : nat, In v (freeVarFormula LNN (fst pair)) -> v <= n) /\ rec)
     m A ->
   Representable m g B ->
   RepresentableHelp n (evalComposeFunc n m (FormulasToFuncs n m A) g)
     (composeSigmaFormula n w m A B)).
  { intro. induction n as [| n Hrecn]; simpl in |- *.
    + intros w m H v.
      induction v as [| a n v Hrecv]; simpl in |- *; intros B g H0 H1 H2.
      - unfold composeSigmaFormula in |- *. simpl in |- *.
        replace
         (subAllFormula LNN B
            (fun x : nat => match x with
                            | O => var 0
                            | S x' => var (S (x' + w))
                            end)) with (subAllFormula LNN B (fun x : nat => var x)).
        * apply iffTrans with B.
          ++ apply iffTrans with (subAllFormula LNN B (fun x : nat => var x)).
             -- apply iffI; apply impI.
                ** eapply andE2. apply Axm; right; constructor.
                ** apply andI.
                   +++ apply eqRefl.
                   +++ apply Axm; right; constructor.
             -- apply (subAllFormulaId LNN).
          ++ induction H2 as (H2, H3). auto.
        * apply subAllFormula_ext. intros m H3. destruct m as [| n]; auto.
          destruct H2 as (H2, H4). apply H2 in H3. lia.
      - destruct H0 as (H0, H3). destruct H1 as (H1, H4). destruct H2 as (H2, H5).
        assert
         (forall a : nat,
          SysPrf NN
            (iffH
               (composeSigmaFormula 0 w n v
                  (substituteFormula LNN B (S n) (natToTerm a)))
               (equal (var 0) (natToTerm (evalList n (FormulasToFuncs 0 n v) (g a)))))).
        { intros a0. apply Hrecv; auto. split.
          + intros v0 H6. destruct (freeVarSubFormula3 _ _ _ _ _ H6).
            - assert (In v0 (freeVarFormula LNN B)).
              { eapply In_list_remove1. exact H7. }
              pose proof (In_list_remove2 _ _ _ _ _ H7).
              pose proof (H2 _ H8). lia.
            - elim (closedNatToTerm _ _ H7).
          + apply H5. }
        clear Hrecv. unfold composeSigmaFormula in |- *.
        unfold composeSigmaFormula in H6. simpl in |- *.
        apply
         iffTrans
          with
            (addExists (S w) n
               (andH (FormulasToFormula 0 w n v)
                  (subAllFormula LNN
                     (substituteFormula LNN B (S n) (natToTerm (snd a)))
                     (fun x : nat =>
                      match x with
                      | O => var 0
                      | S x' => var (S (x' + w))
                      end)))); [| apply H6 ].
        clear H6.
        apply
         iffTrans
          with
            (existH (n + S w)
               (addExists (S w) n
                  (andH
                     (andH
                        (substituteFormula LNN (equal (var 0) (natToTerm (snd a))) 0
                           (var (S (n + w)))) (FormulasToFormula 0 w n v))
                     (subAllFormula LNN B
                        (fun x : nat =>
                         match x with
                         | O => var 0
                         | S x' => var (S (x' + w))
                         end))))).
        * apply (reduceExist LNN).
          ++ apply closedNN.
          ++ apply reduceAddExists.
             repeat apply (reduceAnd LNN); try apply iffRefl.
             apply (reduceSub LNN); auto.
             apply closedNN.
        * rewrite (subFormulaEqual LNN). rewrite (subTermVar1 LNN).
          rewrite (subTermNil LNN).
          apply
           iffTrans
             with
              (existH (n + S w)
                 (andH (equal (var (S (n + w))) (natToTerm (snd a)))
                    (addExists (S w) n
                       (andH (FormulasToFormula 0 w n v)
                          (subAllFormula LNN B
                             (fun x : nat =>
                              match x with
                              | O => var 0
                              | S x' => var (S (x' + w))
                              end)))))).
          ++ apply (reduceExist LNN).
             -- apply closedNN.
             -- apply iffI.
                ** apply impI. apply andI.
                   cut
                    (SysPrf
                       (Ensembles.Add (fol.Formula LNN) NN
                          (andH
                             (andH (equal  (var (S (n + w))) (natToTerm (snd a)))
                                (FormulasToFormula 0 w n v))
                             (subAllFormula LNN B
                                (fun x : nat =>
                                 match x with
                                 | O => var 0
                                 | S x' => var (S (x' + w))
                                 end)))) (equal (var (S (n + w))) (natToTerm (snd a)))).
                   +++ generalize
                        (andH
                           (andH (equal (var (S (n + w))) (natToTerm (snd a)))
                              (FormulasToFormula 0 w n v))
                           (subAllFormula LNN B
                              (fun x : nat =>
                               match x with
                               | O => var 0
                               | S x' => var (S (x' + w))
                               end))).
                       cut (n + w < S (n + w)); try lia.
                       --- generalize (S (n + w)).
                           intros n0 H6 f H7.
                           clear H5 H2 H4 H1 H3 H0 g B v.
                           induction n as [| n Hrecn].
                           *** simpl in |- *. auto.
                           *** simpl in |- *. apply existSys.
                               ++++ apply closedNN.
                               ++++ simpl in |- *; intro.
                                    destruct H0 as [H0 | H0]; try lia.
                                    elim (closedNatToTerm _ _ H0).
                               ++++ apply Hrecn. lia.
                   +++ eapply andE1. eapply andE1. apply Axm; right; constructor.
                   +++ apply
                        impE
                         with
                           (addExists (S w) n
                              (andH
                                 (andH (equal (var (S (n + w))) (natToTerm (snd a)))
                                    (FormulasToFormula 0 w n v))
                                 (subAllFormula LNN B
                                    (fun x : nat =>
                                     match x with
                                     | O => var 0
                                     | S x' => var (S (x' + w))
                                     end)))).
                       --- apply sysWeaken.
                           apply reduceAddExistsOneWay.
                           apply impI. apply andI.
                           *** eapply andE2. eapply andE1.
                               apply Axm; right; constructor.
                           *** eapply andE2.
                               apply Axm; right; constructor.
                       --- apply Axm; right; constructor.
                ** apply impI.
                   apply
                    impE
                     with
                       (addExists (S w) n
                          (andH (FormulasToFormula 0 w n v)
                             (subAllFormula LNN B
                                (fun x : nat =>
                                 match x with
                                 | O => var 0
                                 | S x' => var (S (x' + w))
                                 end)))).
                   +++ apply impE with (equal (var (S (n + w))) (natToTerm (snd a))).
                       --- apply sysWeaken. apply impI.
                           cut
                            (SysPrf
                               (Ensembles.Add (fol.Formula LNN) NN
                                  (equal (var (S (n + w))) (natToTerm (snd a))))
                               (impH
                                  (andH (FormulasToFormula 0 w n v)
                                     (subAllFormula LNN B
                                        (fun x : nat =>
                                         match x with
                                         | O => var 0
                                         | S x' => var (S (x' + w))
                                         end)))
                                  (andH
                                     (andH (equal (var (S (n + w))) (natToTerm (snd a)))
                                        (FormulasToFormula 0 w n v))
                                     (subAllFormula LNN B
                                        (fun x : nat =>
                                         match x with
                                         | O => var 0
                                         | S x' => var (S (x' + w))
                                         end))))).
                           *** generalize
                                (andH (FormulasToFormula 0 w n v)
                                   (subAllFormula LNN B
                                      (fun x : nat =>
                                       match x with
                                       | O => var 0
                                       | S x' => var (S (x' + w))
                                       end)))
                                (andH
                                   (andH (equal (var (S (n + w))) (natToTerm (snd a)))
                                      (FormulasToFormula 0 w n v))
                                   (subAllFormula LNN B
                                      (fun x : nat =>
                                       match x with
                                       | O => var 0
                                       | S x' => var (S (x' + w))
                                       end))).
                               cut (n + w < S (n + w)); try lia.
                               generalize (S (n + w)).
                               clear H5 H2 H4 H1 H3 H0 g B v.
                               induction n as [| n Hrecn]; auto.
                               simpl in |- *. intros n0 H0 f f0 H1.
                               apply impI. apply existSys.
                               ++++ intro. destruct H2 as (x, H2).
                                    destruct H2 as (H2, H3).
                                    destruct H3 as [x H3 | x H3].
                                    ---- elim (closedNN (n + S w)). 
                                         exists x. auto.
                                    ---- destruct H3. simpl in H2.
                                         destruct H2 as [H2 | H2]; try lia.
                                         elim (closedNatToTerm _ _ H2).
                               ++++ simpl in |- *. intro H2.
                                    elim (In_list_remove2 _ _ _ _ _ H2). auto.
                               ++++ apply existSimp. apply impE with (addExists (S w) n f).
                                    ---- apply sysWeaken. apply Hrecn; auto. lia.
                                    ---- apply Axm; right; constructor.
                           *** apply impI. repeat apply andI.
                               ++++ apply Axm; left; right; constructor.
                               ++++ eapply andE1. apply Axm; right; constructor.
                               ++++ eapply andE2. apply Axm; right; constructor.
                       --- eapply andE1. apply Axm; right; constructor.
                   +++ eapply andE2. apply Axm; right; constructor.
          ++ apply
              iffTrans
               with
                 (substituteFormula LNN
                    (addExists (S w) n
                       (andH (FormulasToFormula 0 w n v)
                          (subAllFormula LNN B
                             (fun x : nat =>
                              match x with
                              | O => var 0
                              | S x' => var (S (x' + w))
                              end)))) (S n + w) (natToTerm (snd a))).
             -- apply iffI.
                ** apply impI. apply existSys.
                   +++ apply closedNN.
                   +++ intro H6. destruct (freeVarSubFormula3 _ _ _ _ _ H6).
                       ---- elim (In_list_remove2 _ _ _ _ _ H7). lia.
                       ---- elim (closedNatToTerm _ _ H7).
                   +++ apply
                        impE
                         with
                           (substituteFormula LNN
                              (addExists (S w) n
                                 (andH (FormulasToFormula 0 w n v)
                                    (subAllFormula LNN B
                                       (fun x : nat =>
                                        match x with
                                        | O => var 0
                                        | S x' => var (S (x' + w))
                                        end)))) (S n + w) (var (S n + w))).
                       --- apply (subWithEquals LNN). eapply andE1.
                           apply Axm; right; constructor.
                       --- rewrite (subFormulaId LNN). eapply andE2.
                           apply Axm; right; constructor.
                ** apply impI. apply existI with (natToTerm (snd a)).
                   rewrite (subFormulaAnd LNN). rewrite Nat.add_succ_r.
                   apply andI.
                   +++ rewrite subFormulaEqual. rewrite (subTermVar1 LNN).
                       rewrite (subTermNil LNN).
                       --- apply eqRefl.
                       --- apply closedNatToTerm.
                   +++ apply Axm; right; constructor.
             -- rewrite subAddExistsNice.
                ** apply reduceAddExists. rewrite (subFormulaAnd LNN).
                   apply (reduceAnd LNN).
                   +++ apply (subFormulaNil LNN).
                       cut (n + w < S n + w); try lia.
                       generalize (S n + w). clear H5 H3 g H2.
                       induction v as [| a0 n v Hrecv]; unfold not in |- *; intros n0 H2 H3.
                       --- simpl in H3. lia.
                       --- simpl in H3. destruct (in_app_or _ _ _ H3) as [H5 | H5].
                           *** simpl in H4.
                               induction (freeVarSubFormula3 _ _ _ _ _ H5) as [H6 | H6].
                             elim (proj1 (Nat.le_ngt n0 0)).
                               ++++ decompose record H4. apply H7.
                                    eapply In_list_remove1. apply H6.
                               ++++ lia.
                               ++++ destruct H6 as [H6 | H6].
                                    ---- lia.
                                    ---- elim H6.
                           *** lazymatch goal with _ : In ?n _ |- _ => elim Hrecv with n end.
                               ++++ simpl in H4. tauto.
                               ++++ lia.
                               ++++ auto.
                   +++ eapply iffTrans. apply (subSubAllFormula LNN).
                       apply iffSym. eapply iffTrans.
                       --- apply (subAllSubFormula LNN).
                       --- replace
                            (subAllFormula LNN B
                               (fun n1 : nat =>
                                substituteTerm LNN
                                  match n1 with
                                  | O => var 0
                                  | S x' => var (S (x' + w))
                                  end (S n + w) (natToTerm (snd a)))) with
                            (subAllFormula LNN B
                               (fun x : nat =>
                                match eq_nat_dec (S n) x with
                                | left _ =>
                                    subAllTerm LNN (natToTerm (snd a))
                                      (fun x0 : nat =>
                                       match x0 with
                                       | O => var 0
                                       | S x' => var (S (x' + w))
                                       end)
                                | right _ =>
                                    (fun x0 : nat =>
                                     match x0 with
                                     | O => var 0
                                     | S x' => var (S (x' + w))
                                     end) x
                                end)).
                           *** apply iffRefl.
                           *** apply subAllFormula_ext. intros m H6.
                               destruct (eq_nat_dec (S n) m) as [e | e].
                               ++++ rewrite <- e. rewrite (subTermVar1 LNN).
                                    clear H0. induction (snd a).
                                    ---- simpl in |- *. reflexivity.
                                    ---- simpl in |- *. rewrite IHn0. reflexivity.
                               ++++ destruct m as [| n0].
                                    ---- simpl in |- *. reflexivity.
                                    ---- rewrite (subTermVar2 LNN).
                                         **** reflexivity.
                                         **** lia.
                ** lia.
                ** intros v0 H6. elim (closedNatToTerm _ _ H6).
          ++ apply closedNatToTerm.
    + intros. 
      set
       (v' :=
        Vector.t_rec (Formula * (nat -> naryFunc n))
          (fun (m : nat) (v : Vector.t _ m) => Vector.t (Formula * naryFunc n) m)
          (Vector.nil _)
          (fun (pair : Formula * (nat -> naryFunc n)) (m : nat) 
             (v : Vector.t _ m) (rec : Vector.t (Formula * naryFunc n) m) =>
           Vector.cons _
             (substituteFormula LNN (fst pair) (S n) (natToTerm a), snd pair a) m
             rec) _ A) in *.
      assert
       (RepresentableHelp n (evalComposeFunc n m (FormulasToFuncs n m v') g)
          (addExists (S w) m
             (andH (FormulasToFormula n w m v')
                (subAllFormula LNN B
                   (fun x : nat =>
                    match x with
                    | O => var 0
                    | S x' => var (S (x' + w))
                    end))))).
      - unfold composeSigmaFormula in Hrecn.
        simpl in Hrecn. apply Hrecn.
        * lia.
        * clear B g H2.
          induction A as [| a0 n0 A HrecA]; simpl in (value of v'); simpl in |- *; auto.
          split.
          ++ simpl in H0. destruct H0 as (H0, H2). apply H0.
          ++ apply HrecA.
             -- destruct H0 as (H0, H2). auto.
             -- simpl in H1. destruct H1 as (H1, H2). auto.
        * simpl in H1. clear H2 H0 g B. induction A as [| a0 n0 A HrecA].
          ++ simpl in |- *. auto.
          ++ simpl in |- *. split.
             -- simpl in H1. destruct H1 as (H0, H1). intros v H2.
                destruct (freeVarSubFormula3 _ _ _ _ _ H2).
                ** assert (v <= S n).
                   { apply H0. eapply In_list_remove1. exact H3. }
                   destruct (proj1 (Nat.lt_eq_cases v (S n))).
                   +++ assumption. 
                   +++ lia.
                   +++ elim (In_list_remove2 _ _ _ _ _ H3). auto.
                ** elim (closedNatToTerm _ _ H3).
             -- apply HrecA. destruct H1 as (H0, H1). auto.
        * auto.
      - unfold composeSigmaFormula in |- *. clear Hrecn.
        apply
         RepresentableAlternate
          with
            (addExists (S w) m
               (andH (FormulasToFormula n w m v')
                  (subAllFormula LNN B
                     (fun x : nat =>
                      match x with
                      | O => var 0
                      | S x' => var (S (x' + w))
                      end)))).
        * rewrite subAddExistsNice.
          ++ apply reduceAddExists. rewrite (subFormulaAnd LNN).
             apply (reduceAnd LNN).
             -- clear H3 H2 H1 H0 g B. induction A as [| a0 n0 A HrecA].
                ** simpl in |- *. apply iffSym. apply (subFormulaNil LNN). simpl in |- *. lia.
                ** simpl in |- *. rewrite (subFormulaAnd LNN).
                   apply (reduceAnd LNN); [| apply HrecA ].
                   apply (subFormulaExch LNN); try lia.
                   +++ apply closedNatToTerm.
                   +++ unfold not in |- *; intros. destruct H0 as [H0 | H0].
                       --- lia.
                       --- apply H0.
             -- apply iffSym. apply (subFormulaNil LNN).
                intro H4. decompose record (freeVarSubAllFormula1 _ _ _ _ H4).
                destruct x as [| n0].
                ** destruct H7 as [H5 | H5]; try lia. elim H5.
                ** destruct H7 as [H5| H5].
                   +++ lia.
                   +++ elim H5.
          ++ lia.
          ++ intros. elim (closedNatToTerm _ _ H4).
        * apply Representable_ext with (evalComposeFunc n m (FormulasToFuncs n m v') g).
          clear H3 H2 H1 H0 B.
          ++ apply extEqualCompose.
             -- unfold extEqualVector in |- *. clear g.
                induction A as [| a0 n0 A HrecA]; simpl in |- *; auto.
                split.
                ** apply extEqualRefl.
                ** apply HrecA.
             -- apply extEqualRefl.
          ++ apply H3. }
  intros n w m H0 A B g H1 H2 H3. split.
  + intros v H4. unfold composeSigmaFormula in H4.
    assert
     (In v
        (freeVarFormula LNN
           (andH (FormulasToFormula n w m A)
              (subAllFormula LNN B
                 (fun x : nat =>
                  match x with
                  | O => var 0
                  | S x' => var (S x' + w)
                  end))))).
    { eapply freeVarAddExists1. apply H4. }
    simpl in H5. destruct (in_app_or _ _ _ H5).
    - assert (m + S w <= v \/ v < S w).
      { eapply freeVarAddExists2. apply H4. }
      clear H5 H4 H3 H1 g B.
      induction A as [| a n0 A HrecA].
      * simpl in H6. lia.
      * simpl in H6. destruct (in_app_or _ _ _ H6).
        ++ simpl in H2. destruct H2 as (H2, H3).
           destruct (freeVarSubFormula3 _ _ _ _ _ H1) as [H4 | H4].
           -- apply H2. eapply In_list_remove1. exact H4.
           -- destruct H4 as [H4 | H4].
              ** lia.
              ** elim H4.
        ++ apply HrecA; auto.
           -- simpl in H2. tauto.
           -- lia.
    - decompose record (freeVarSubAllFormula1 _ _ _ _ H6).
      destruct x as [| n0].
      * destruct H9 as [H7 | H7]; try lia. elim H7.
      * induction H9 as [H7 | H7].
        ++ rewrite <- H7. destruct H3 as (H3, H9).
           assert (S n0 <= m). { apply H3. auto. }
           destruct (freeVarAddExists2 _ _ _ _ H4) as [H11 | H11].
           -- lia.
           -- lia.
        ++ elim H7.
  + apply H; auto.
Qed.











Remark boundedCheck :
 forall P : nat -> Prop,
 (forall x : nat, decidable (P x)) ->
 forall c : nat,
 (forall d : nat, d < c -> ~ P d) \/ (exists d : nat, d < c /\ P d).
Proof.
  intros P H c. induction c as [| c Hrecc].
  + left; intros d H0. lia.
  + destruct (H c) as [e | e].
    - right. exists c. split; auto.
    - destruct Hrecc as [H0 | H0].
      * left. intros d H1. assert (d < c \/ d = c) as H2 by lia. destruct H2.
        ++ eauto.
        ++ congruence.
      * destruct H0 as (x, H0). right. exists x. split; try lia. tauto.
Qed.

Remark smallestExists :
 forall P : nat -> Prop,
 (forall x : nat, decidable (P x)) ->
 forall c : nat,
 P c -> exists a : nat, P a /\ (forall b : nat, b < a -> ~ P b).
Proof.
  assert
   (forall P : nat -> Prop,
   (forall x : nat, decidable (P x)) ->
    forall d c : nat,
    c < d -> P c -> exists a : nat, P a /\ (forall b : nat, b < a -> ~ P b)).
  { intros P H d. induction d as [| d Hrecd].
    + intros c H0 H1. lia.
    + intros c H0 H1. assert (c < d \/ c = d) as H2 by lia. destruct H2.
      - eauto.
      - destruct (boundedCheck P H c).
        * exists c. tauto.
        * destruct H3 as (x, H3). apply (Hrecd x).
          ++ lia.
          ++ tauto. }
  intros P H0 c H1. eapply H.
  + exact H0.
  + exact (Nat.lt_succ_diag_r c).
  + exact H1.
Qed.

Definition minimize (A B : Formula) (v x : nat) : Formula :=
  andH A
    (forallH x
       (impH (LT (var x) (var v)) (notH (substituteFormula LNN B v (var x))))).

Remark minimize1 :
 forall (A B : Formula) (v x : nat),
 v <> x ->
 ~ In x (freeVarFormula LNN B) ->
 forall a : nat,
 SysPrf NN (substituteFormula LNN A v (natToTerm a)) ->
 SysPrf NN (substituteFormula LNN B v (natToTerm a)) ->
 (forall b : nat,
  b < a -> SysPrf NN (notH (substituteFormula LNN A v (natToTerm b)))) ->
 (forall b : nat,
  b < a -> SysPrf NN (notH (substituteFormula LNN B v (natToTerm b)))) ->
 SysPrf NN (iffH (minimize A B v x) (equal (var v) (natToTerm a))).
Proof.
  intros A B v x H H0 a H1 H2 H3 H4. apply iffI.
  unfold minimize in |- *. apply impI.
  apply
   impE
    with
      (substituteFormula LNN
         (impH (LT (var x) (var v)) (notH (substituteFormula LNN B v (var x))))
         x (natToTerm a)).
  + rewrite (subFormulaImp LNN). rewrite (subFormulaNot LNN).
    apply
     impTrans
      with
        (impH (LT (natToTerm a) (var v))
           (notH (substituteFormula LNN B v (natToTerm a)))).
    - apply iffE1. apply (reduceImp LNN).
      * unfold LT at 2 in |- *. rewrite (subFormulaRelation LNN).
        simpl in |- *. destruct (eq_nat_dec x x) as [e | e]; try lia.
        destruct (eq_nat_dec x v).
        ++ elim H. auto.
        ++ apply iffRefl.
      * apply (reduceNot LNN). apply (subFormulaTrans LNN).
        intro H5. elim H0. eapply In_list_remove1. exact H5.
    - apply impTrans with (notH (LT (natToTerm a) (var v))).
      * apply impI. apply impE with (notH (notH (substituteFormula LNN B v (natToTerm a)))).
        apply cp2.
        ++ apply Axm; right; constructor.
        ++ apply nnI. do 2 apply sysWeaken. exact H2.
      * apply impE with (notH (LT (var v) (natToTerm a))).
        apply
         orE
          with
            (LT (var v) (natToTerm a))
            (orH (equal (var v) (natToTerm a)) (LT (natToTerm a) (var v))).
        ++ apply sysWeaken. apply nn9.
        ++ repeat apply impI.
           apply contradiction with (LT (var v) (natToTerm a)).
           -- apply Axm; left; left; right; constructor.
           -- apply Axm; left; right; constructor.
        ++ apply impI. apply orSys; repeat apply impI.
           -- apply Axm; left; left; right; constructor.
           -- apply contradiction with (LT (natToTerm a) (var v)).
              ** apply Axm; left; left; right; constructor.
              ** apply Axm; right; constructor.
        ++ apply impE with (notH (notH A)). apply cp2.
           -- apply sysWeaken. apply boundedLT. intros n H5.
              rewrite (subFormulaNot LNN). auto.
           -- apply nnI. eapply andE1. apply Axm; right; constructor.
  + apply forallE. eapply andE2. apply Axm; right; constructor.
  + apply impI. unfold minimize in |- *.
    rewrite <-
     (subFormulaId LNN
        (andH A
           (forallH x
              (impH (LT (var x) (var v))
                 (notH (substituteFormula LNN B v (var x)))))) v).
    apply
     impE
      with
        (substituteFormula LNN
           (andH A
              (forallH x
                 (impH (LT (var x) (var v))
                    (notH (substituteFormula LNN B v (var x)))))) v 
           (natToTerm a)).
    - apply (subWithEquals LNN). apply eqSym. apply Axm; right; constructor.
    - apply sysWeaken. rewrite (subFormulaAnd LNN). apply andI.
      * auto.
      * rewrite (subFormulaForall LNN). destruct (eq_nat_dec x v) as [e | e]; try congruence.
        destruct (In_dec eq_nat_dec x (freeVarTerm LNN (natToTerm a))) as [e0 | e0].
        ++ elim (closedNatToTerm _ _ e0).
        ++ apply forallI. apply closedNN. rewrite (subFormulaImp LNN).
           unfold LT in |- *. rewrite (subFormulaRelation LNN).
           simpl in |- *. destruct (eq_nat_dec v v) as [e1 | e1]; try congruence.
           -- induction (eq_nat_dec v x) as [e2 | e2]; try congruence.
              apply impI. apply forallE. apply forallI. intro H5.
              destruct H5 as (x0, H5); destruct H5 as (H5, H6).
              destruct H6 as [x0 H6 | x0 H6].
              ** elim closedNN with v. exists x0; auto.
              ** destruct H6. destruct H5 as [H5 | H5]; try congruence.
                 fold (freeVarTerm LNN (natToTerm a)) in H5. simpl in H5.
                 rewrite <- app_nil_end in H5. elim (closedNatToTerm _ _ H5).
              ** apply impE with (LT (var x) (natToTerm a)).
                 +++ apply sysWeaken. apply boundedLT. intros n H5.
                     rewrite (subFormulaNot LNN).
                     apply impE with (notH (substituteFormula LNN B v (natToTerm n))).
                     --- apply cp2. apply iffE1. apply (subFormulaTrans LNN).
                         intro H6. elim H0. eapply In_list_remove1. exact H6.
                     --- apply H4; auto.
                 +++ apply Axm; right; constructor.
Qed.

Lemma subFormulaMinimize :
 forall (A B : Formula) (v x z : nat) (s : Term),
 ~ In x (freeVarTerm LNN s) ->
 ~ In v (freeVarTerm LNN s) ->
 x <> z ->
 v <> z ->
 SysPrf NN
   (iffH (substituteFormula LNN (minimize A B v x) z s)
      (minimize (substituteFormula LNN A z s) (substituteFormula LNN B z s) v
         x)).
Proof.
  intros A B v x z s H H0 H1 H2. unfold minimize in |- *.
  rewrite (subFormulaAnd LNN). rewrite (subFormulaForall LNN).
  destruct (eq_nat_dec x z) as [e | e]; try congruence.
  destruct (In_dec eq_nat_dec x (freeVarTerm LNN s)) as [e0 | e0]; try tauto.
  rewrite (subFormulaImp LNN). unfold LT at 1 in |- *.
  rewrite (subFormulaRelation LNN). simpl in |- *.
  destruct (eq_nat_dec z x); try congruence.
  destruct (eq_nat_dec z v); try congruence.
  rewrite (subFormulaNot LNN).
  repeat first
   [ apply iffRefl
   | apply (reduceAnd LNN)
   | apply (reduceImp LNN)
   | apply (reduceNot LNN)
   | apply (reduceForall LNN); [ apply closedNN |] ].
  apply (subFormulaExch LNN).
  + congruence. 
  + simpl in |- *. intro H3. tauto.
  + auto.
Qed.

Definition primRecSigmaFormulaHelp (n : nat) (SigA SigB : Formula) : Formula :=
  andH
    (existH 0
       (andH SigA
          (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2
             (var (S (S n))))))
    (forallH (S (S (S n)))
       (impH (LT (var (S (S (S n)))) (var (S n)))
          (existH 0
             (existH (S n)
                (andH
                   (substituteFormula LNN
                      (substituteFormula LNN
                         (substituteFormula LNN betaFormula 1
                            (var (S (S (S n))))) 2 
                         (var (S (S n)))) 0 (var (S n)))
                   (andH
                      (substituteFormula LNN SigB (S (S n))
                         (var (S (S (S n)))))
                      (substituteFormula LNN
                         (substituteFormula LNN betaFormula 1
                            (Succ (var (S (S (S n)))))) 2 
                         (var (S (S n)))))))))).

Definition primRecPiFormulaHelp (n : nat) (SigA SigB : Formula) : Formula :=
  andH
    (forallH 0
       (impH SigA
          (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2
             (var (S (S n))))))
    (forallH (S (S (S n)))
       (impH (LT (var (S (S (S n)))) (var (S n)))
          (forallH 0
             (forallH (S n)
                (impH
                   (substituteFormula LNN
                      (substituteFormula LNN
                         (substituteFormula LNN betaFormula 1
                            (var (S (S (S n))))) 2 
                         (var (S (S n)))) 0 (var (S n)))
                   (impH
                      (substituteFormula LNN SigB (S (S n))
                         (var (S (S (S n)))))
                      (substituteFormula LNN
                         (substituteFormula LNN betaFormula 1
                            (Succ (var (S (S (S n)))))) 2 
                         (var (S (S n)))))))))).

Lemma freeVarPrimRecSigmaFormulaHelp1 :
 forall (n : nat) (A B : Formula) (v : nat),
 In v (freeVarFormula LNN (primRecSigmaFormulaHelp n A B)) ->
 In v (freeVarFormula LNN A) \/
 In v (freeVarFormula LNN B) \/ v = S (S n) \/ v = S n.
Proof.
  intros n A B v H. unfold primRecSigmaFormulaHelp in H.
  assert
   (forall v : nat,
    In v (freeVarFormula LNN betaFormula) -> v = 0 \/ v = 1 \/ v = 2).
  { intros v0 H0. assert (Representable 2 beta betaFormula).
    apply betaRepresentable. destruct H1 as (H1, H2).
    apply H1 in H0. lia. }
  repeat
   match goal with
   | H:(In v (freeVarFormula LNN (existH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarFormula LNN X2));
        [ eapply In_list_remove1; apply H
        | assert (v <> X1); [ eapply In_list_remove2; apply H | clear H ] ]
   | H:(In v (freeVarFormula LNN (forallH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarFormula LNN X2));
        [ eapply In_list_remove1; apply H
        | assert (v <> X1); [ eapply In_list_remove2; apply H | clear H ] ]
   | H:(In v (List.remove _ ?X1 (freeVarFormula LNN ?X2))) |- _ =>
       assert (In v (freeVarFormula LNN X2));
        [ eapply In_list_remove1; apply H
        | assert (v <> X1); [ eapply In_list_remove2; apply H | clear H ] ]
   | H:(In v (freeVarFormula LNN (andH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarFormula LNN X1 ++ freeVarFormula LNN X2));
        [ apply H | clear H ]
   | H:(In v (freeVarFormula LNN (impH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarFormula LNN X1 ++ freeVarFormula LNN X2));
        [ apply H | clear H ]
   | H:(In v (_ ++ _)) |- _ =>
       destruct (in_app_or _ _ _ H); clear H
   | H:(In v (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _ =>
       induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
   | H:(In v (freeVarFormula LNN (LT ?X1 ?X2))) |- _ =>
       rewrite freeVarLT in H
   | H:(In v (freeVarFormula LNN betaFormula)) |- _ =>
       decompose sum (H0 v H); clear H
   end; try tauto;
   match goal with
   | H:(In v _) |- _ => simpl in H; decompose sum H; clear H
   end; auto;
   try match goal with
       | H:(?X1 = ?X2),H2:(?X2 <> ?X1) |- _ => elim H2; auto
       end; simpl in |- *; try tauto.
Qed.

Lemma freeVarPrimRecPiFormulaHelp1 :
 forall (n : nat) (A B : Formula) (v : nat),
 In v (freeVarFormula LNN (primRecPiFormulaHelp n A B)) ->
 In v (freeVarFormula LNN A) \/
 In v (freeVarFormula LNN B) \/ v = S (S n) \/ v = S n.
Proof.
  intros n A B v H. unfold primRecPiFormulaHelp in H.
  assert
   (forall v : nat,
    In v (freeVarFormula LNN betaFormula) -> v = 0 \/ v = 1 \/ v = 2).
  { intros v0 H0. assert (Representable 2 beta betaFormula).
    apply betaRepresentable.
    destruct H1 as (H1, H2). apply H1 in H0. lia. }
  repeat
   match goal with
   | H:(In v (freeVarFormula LNN (existH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarFormula LNN X2));
        [ eapply In_list_remove1; apply H
        | assert (v <> X1); [ eapply In_list_remove2; apply H | clear H ] ]
   | H:(In v (freeVarFormula LNN (forallH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarFormula LNN X2));
        [ eapply In_list_remove1; apply H
        | assert (v <> X1); [ eapply In_list_remove2; apply H | clear H ] ]
   | H:(In v (List.remove  eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _ =>
       assert (In v (freeVarFormula LNN X2));
        [ eapply In_list_remove1; apply H
        | assert (v <> X1); [ eapply In_list_remove2; apply H | clear H ] ]
   | H:(In v (freeVarFormula LNN (andH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarFormula LNN X1 ++ freeVarFormula LNN X2));
        [ apply H | clear H ]
   | H:(In v (freeVarFormula LNN (impH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarFormula LNN X1 ++ freeVarFormula LNN X2));
        [ apply H | clear H ]
   | H:(In v (_ ++ _)) |- _ =>
       induction (in_app_or _ _ _ H); clear H
   | H:(In v (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _ =>
       induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
   | H:(In v (freeVarFormula LNN (LT ?X1 ?X2))) |- _ =>
       rewrite freeVarLT in H
   | H:(In v (freeVarFormula LNN betaFormula)) |- _ =>
       decompose sum (H0 v H); clear H
   end; try tauto;
   match goal with
   | H:(In v _) |- _ => simpl in H; decompose sum H; clear H
   end; auto;
   try match goal with
       | H:(?X1 = ?X2),H2:(?X2 <> ?X1) |- _ => elim H2; auto
       end; simpl in |- *; try tauto.
Qed.

Definition primRecSigmaFormula (n : nat) (SigA SigB : Formula) : Formula :=
  existH (S (S n))
    (andH
       (minimize (primRecSigmaFormulaHelp n SigA SigB)
          (primRecPiFormulaHelp n SigA SigB) (S (S n)) 
          (S (S (S (S n)))))
       (substituteFormula LNN
          (substituteFormula LNN betaFormula 2 (var (S (S n)))) 1 
          (var (S n)))).

Remark notBoundedForall :
 forall (P : nat -> Prop) (b : nat),
 (forall x : nat, decidable (P x)) ->
 ~ (forall n : nat, n < b -> P n) -> exists n : nat, n < b /\ ~ P n.
Proof.
  intros P b H H0. induction b as [| b Hrecb].
  + elim H0. lia.
  + destruct (H b) as [e | e].
    - assert (~ (forall n : nat, n < b -> P n)).
      { intro H1. elim H0. intros n H2.
        assert (n < b \/ n = b) as H3 by lia. destruct H3.
        + auto.
        + rewrite H3; auto. }
      decompose record (Hrecb H1).
      exists x. split; auto; lia.
    - exists b. split; auto; lia.
Qed.


Lemma succ_plus_discr : forall n m : nat, n <> S (m + n).
Proof.
  lia.
Qed.

Remark In_betaFormula_subst_1_2_0 :
 forall (a b c : Term) (v : nat),
 In v
   (freeVarFormula LNN
      (substituteFormula LNN
         (substituteFormula LNN (substituteFormula LNN betaFormula 1 a) 2 b)
         0 c)) ->
 In v (freeVarTerm LNN a) \/
 In v (freeVarTerm LNN b) \/ In v (freeVarTerm LNN c).
Proof.
  intros a b c v H. destruct (freeVarSubFormula3 _ _ _ _ _ H) as [H0 | H0].
  + assert
     (In v
        (freeVarFormula LNN
           (substituteFormula LNN (substituteFormula LNN betaFormula 1 a) 2 b))).
    { eapply In_list_remove1; apply H0. }
    destruct (freeVarSubFormula3 _ _ _ _ _ H1) as [H2 | H2].
    - assert (In v (freeVarFormula LNN (substituteFormula LNN betaFormula 1 a))).
      { eapply In_list_remove1; apply H2. }
      destruct (freeVarSubFormula3 _ _ _ _ _ H3) as [H4 | H4].
      * destruct v as [| n].
        ++ elim (In_list_remove2 _ _ _ _ _ H0). reflexivity.
        ++ destruct n as [| n].
           -- elim (In_list_remove2 _ _ _ _ _ H4); reflexivity.
           -- destruct n as [| n].
              ** elim (In_list_remove2 _ _ _ _ _ H2). reflexivity.
              ** elim (proj1 (Nat.le_ngt  (S (S (S n))) 2)).
                 +++ assert (Representable 2 beta betaFormula).
                     { apply betaRepresentable. }
                     destruct H5 as (H5, H6). apply H5.
                     eapply In_list_remove1. exact H4.
                 +++ lia.
      * tauto.
    - tauto.
  + tauto.
Qed.

Remark In_betaFormula_subst_1_2 :
 forall (a b : Term) (v : nat),
 In v
   (freeVarFormula LNN
      (substituteFormula LNN (substituteFormula LNN betaFormula 1 a) 2 b)) ->
 In v (freeVarTerm LNN a) \/
 In v (freeVarTerm LNN b) \/ In v (freeVarTerm LNN (var 0)).
Proof.
  intros a b v H. apply In_betaFormula_subst_1_2_0.
  rewrite (subFormulaId LNN). exact H.
Qed.

Remark In_betaFormula_subst_1 :
 forall (a : Term) (v : nat),
 In v (freeVarFormula LNN (substituteFormula LNN betaFormula 1 a)) ->
 In v (freeVarTerm LNN a) \/
 In v (freeVarTerm LNN (var 2)) \/ In v (freeVarTerm LNN (var 0)).
Proof.
  intros a v H. apply In_betaFormula_subst_1_2.
  rewrite (subFormulaId LNN). exact H.
Qed.

Remark In_betaFormula :
 forall v : nat,
 In v (freeVarFormula LNN betaFormula) ->
 In v (freeVarTerm LNN (var 1)) \/
 In v (freeVarTerm LNN (var 2)) \/ In v (freeVarTerm LNN (var 0)).
Proof.
  intros v H. apply In_betaFormula_subst_1.
  rewrite (subFormulaId LNN). exact H.
Qed.

Remark In_betaFormula_subst_2 :
 forall (a : Term) (v : nat),
 In v (freeVarFormula LNN (substituteFormula LNN betaFormula 2 a)) ->
 In v (freeVarTerm LNN a) \/
 In v (freeVarTerm LNN (var 1)) \/ In v (freeVarTerm LNN (var 0)).
Proof.
  intros a v H. rewrite <- (subFormulaId LNN betaFormula 1) in H.
  decompose sum (In_betaFormula_subst_1_2 _ _ _ H); tauto.
Qed.

Remark In_betaFormula_subst_2_1 :
 forall (a b : Term) (v : nat),
 In v
   (freeVarFormula LNN
      (substituteFormula LNN (substituteFormula LNN betaFormula 2 a) 1 b)) ->
 In v (freeVarTerm LNN a) \/
 In v (freeVarTerm LNN b) \/ In v (freeVarTerm LNN (var 0)).
Proof.
  intros a b v H. destruct (freeVarSubFormula3 _ _ _ _ _ H) as [H0 | H0].
  + assert (In v (freeVarFormula LNN (substituteFormula LNN betaFormula 2 a))).
    { eapply In_list_remove1. apply H0. }
    decompose sum (In_betaFormula_subst_2 _ _ H1); try tauto.
    destruct H3 as [H2 | H2].
    elim (In_list_remove2 _ _ _ _ _ H0).
    symmetry  in |- *; assumption.
    elim H2.
  + tauto.
Qed.

Ltac PRsolveFV A B n :=
  unfold  not in |- *; intros;
   repeat
    match goal with
    | H:(_ = _) |- _ => discriminate H
    | H:(?X1 <> ?X1) |- _ => elim H; reflexivity
    | H:(?X1 = S ?X1) |- _ => elim (n_Sn _ H)
    | H:(S ?X1 = ?X1) |- _ =>
        elim (n_Sn X1); symmetry  in |- *; apply H
    | H:(?X1 = S (S ?X1)) |- _ => elim (Compat815.n_SSn _ H)
    | H:(S (S ?X1) = ?X1) |- _ =>
        elim (Compat815.n_SSn X1); symmetry  in |- *; apply H
    | H:(?X1 = S (S (S ?X1))) |- _ =>
        elim (Compat815.n_SSSn _ H)
    | H:(S (S (S ?X1)) = ?X1) |- _ =>
        elim (Compat815.n_SSSn X1); symmetry  in |- *; apply H
    | H:(In ?X3
           (freeVarFormula LNN
              (substituteFormula LNN
                 (substituteFormula LNN
                    (substituteFormula LNN betaFormula 1 _) 2 _) 0 _))) |- _
    =>
        decompose sum (In_betaFormula_subst_1_2_0 _ _ _ _ H); clear H
    | H:(In ?X3
           (freeVarFormula LNN
              (substituteFormula LNN (substituteFormula LNN betaFormula 1 _)
                 2 _))) |- _ =>
        decompose sum (In_betaFormula_subst_1_2 _ _ _ H); clear H
    | H:(In ?X3 (freeVarFormula LNN (substituteFormula LNN betaFormula 1 _)))
    |- _ =>
        decompose sum (In_betaFormula_subst_1 _ _ H); clear H
    | H:(In ?X3 (freeVarFormula LNN betaFormula)) |- _ =>
        decompose sum (In_betaFormula _ H); clear H
    | H:(In ?X3
           (freeVarFormula LNN
              (substituteFormula LNN (substituteFormula LNN betaFormula 2 _)
                 1 _))) |- _ =>
        decompose sum (In_betaFormula_subst_2_1 _ _ _ H); clear H
    | H:(In ?X3 (freeVarFormula LNN (substituteFormula LNN betaFormula 2 _)))
    |- _ =>
        decompose sum (In_betaFormula_subst_2 _ _ H);
         clear H
          (*
          Match Context With
          *)
    | H:(In ?X3 (freeVarFormula LNN (existH ?X1 ?X2))) |- _ =>
        assert
         (In X3 (List.remove  eq_nat_dec X1 (freeVarFormula LNN X2)));
         [ apply H | clear H ]
    | H:(In ?X3 (freeVarFormula LNN (forallH ?X1 ?X2))) |- _ =>
        assert
         (In X3 (List.remove eq_nat_dec X1 (freeVarFormula LNN X2)));
         [ apply H | clear H ]
    | 
    (*
    .
    *)
    H:(In ?X3 (List.remove  eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _
    =>
        assert (In X3 (freeVarFormula LNN X2));
         [ eapply In_list_remove1; apply H
         | assert (X3 <> X1); [ eapply In_list_remove2; apply H | clear H ] ]
    | H:(In ?X3 (freeVarFormula LNN (andH ?X1 ?X2))) |- _ =>
        assert (In X3 (freeVarFormula LNN X1 ++ freeVarFormula LNN X2));
         [ apply H | clear H ]
    | H:(In ?X3 (freeVarFormula LNN (impH ?X1 ?X2))) |- _ =>
        assert (In X3 (freeVarFormula LNN X1 ++ freeVarFormula LNN X2));
         [ apply H | clear H ]
    | H:(In ?X3 (freeVarFormula LNN (notH ?X1))) |- _ =>
        assert (In X3 (freeVarFormula LNN X1)); [ apply H | clear H ]
    | H:(In _ (freeVarFormula LNN (primRecPiFormulaHelp _ _ _))) |- _ =>
        decompose sum (freeVarPrimRecPiFormulaHelp1 _ _ _ _ H); clear H
    | J:(In ?X3 (freeVarFormula LNN A)),H:(forall v : nat,
                                           In v (freeVarFormula LNN A) ->
                                           v <= S n) |- _ =>
        elim (proj1 (Nat.le_ngt X3 (S n)));
         [ apply H; apply J | 
           clear J; 
           repeat apply Nat.lt_succ_diag_r || apply  Nat.lt_lt_succ_r]
    | H:(In ?X3 (freeVarFormula LNN B)),H0:(forall v : nat,
                                            In v (freeVarFormula LNN B) ->
                                            v <= S (S (S n))) |- _ =>
        elim (proj1 (Nat.le_ngt X3 (S (S (S n)))));
         [ apply H0; apply H | clear H; repeat apply Nat.lt_succ_diag_r || apply Nat.lt_lt_succ_r]
    | H:(In _ (_ ++ _)) |- _ =>
        induction (in_app_or _ _ _ H); clear H
    | H:(In _ (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _
    =>
        induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
    | H:(In _ (freeVarFormula LNN (LT ?X1 ?X2))) |- _ =>
        rewrite freeVarLT in H
    | H:(In _ (freeVarTerm LNN (natToTerm _))) |- _ =>
        elim (closedNatToTerm _ _ H)
    | H:(In _ (freeVarTerm LNN Zero)) |- _ =>
        elim H
    | H:(In _ (freeVarTerm LNN (Succ _))) |- _ =>
        rewrite freeVarSucc in H
    | H:(In _ (freeVarTerm LNN (var _))) |- _ =>
        simpl in H; decompose sum H; clear H
    | H:(In _ (freeVarTerm LNN (var  _))) |- _ =>
        simpl in H; decompose sum H; clear H
    end.

Remark primRecSigmaRepresentable :
 forall (n : nat) (A : Formula) (g : naryFunc n),
 Representable n g A ->
 forall (B : Formula) (h : naryFunc (S (S n))),
 Representable (S (S n)) h B ->
 Representable (S n) (evalPrimRecFunc n g h) (primRecSigmaFormula n A B).
Proof.
  assert
   (forall (n : nat) (A : Formula) (g : naryFunc n),
    Representable n g A ->
    forall (B : Formula) (h : naryFunc (S (S n))),
    Representable (S (S n)) h B ->
    RepresentableHelp (S n) (evalPrimRecFunc n g h) (primRecSigmaFormula n A B)).
  { induction n as [| n Hrecn].
    + simpl; intros A g H B h H0. unfold primRecSigmaFormula. intros a. rewrite (subFormulaExist LNN).
      induction (In_dec eq_nat_dec 2 (freeVarTerm LNN (natToTerm a))) as [a0 | b].
      - elim (closedNatToTerm _ _ a0).
      - simpl. clear b. assert (repBeta : Representable 2 beta betaFormula).
        { apply betaRepresentable. }
        rewrite (subFormulaAnd LNN). repeat rewrite (subFormulaId LNN).
        apply
         iffTrans
          with
            (existH 2
               (andH
                  (minimize
                     (substituteFormula LNN (primRecSigmaFormulaHelp 0 A B) 1
                        (natToTerm a))
                     (substituteFormula LNN (primRecPiFormulaHelp 0 A B) 1
                        (natToTerm a)) 2 4)
                  (substituteFormula LNN betaFormula 1 (natToTerm a)))).
        * apply (reduceExist LNN).
          ++ apply closedNN.
          ++ apply (reduceAnd LNN).
             -- apply subFormulaMinimize; first [ discriminate | apply closedNatToTerm ].
             -- apply iffRefl.
        * set (f := evalPrimRecFunc 0 g h) in *. destruct (betaTheorem1 (S a) f) as [x p]. destruct x as (a0, b). simpl in p.
          set (P := fun c : nat => forall z : nat, z < S a -> f z = beta c z) in *.
          assert (forall c : nat, decidable (P c)).
          { intros c. unfold decidable, P. set (Q := fun z : nat => f z <> beta c z) in *.
            assert (forall z : nat, decidable (Q z)).
            { intros. unfold decidable, Q. destruct (eq_nat_dec (f z) (beta c z)); auto. }
            destruct (boundedCheck Q H1 (S a)) as [H2 | H2].
            + left. unfold Q in H2. intros z H3. destruct (eq_nat_dec (f z) (beta c z)).
              - auto.
              - elim (H2 z); auto.
            + right. intro H3. destruct H2 as (x, H2). destruct H2 as (H2, H4). elim H4. apply H3; auto. }
          induction (smallestExists P H1 (cPair b a0)).
          ++ destruct H2 as (H2, H3). clear H1 p b a0.
             apply
              iffTrans
               with
                 (existH 2
                    (andH (equal (var 2) (natToTerm x))
                       (substituteFormula LNN betaFormula 1 (natToTerm a)))).
             -- apply (reduceExist LNN).
                ** apply closedNN.
                ** apply (reduceAnd LNN).
                   +++ assert
                        (subExistSpecial :
                         forall (F : Formula) (a b c : nat),
                         b <> c ->
                         substituteFormula LNN (existH b F) c (natToTerm a) =
                         existH b (substituteFormula LNN F c (natToTerm a))).
                       { intros F a0 b c H1. rewrite (subFormulaExist LNN). destruct (eq_nat_dec b c) as [e | e].
                         + elim H1. auto.
                         + destruct (In_dec eq_nat_dec b (freeVarTerm LNN (natToTerm a0))) as [H4 | H4].
                           - elim (closedNatToTerm _ _ H4).
                           - reflexivity. }
                       assert
                        (subForallSpecial :
                         forall (F : Formula) (a b c : nat),
                         b <> c ->
                         substituteFormula LNN (forallH b F) c (natToTerm a) =
                         forallH b (substituteFormula LNN F c (natToTerm a))).
                       { intros F a0 b c H1. rewrite (subFormulaForall LNN). destruct (eq_nat_dec b c) as [e | e].
                         + elim H1. auto.
                         + destruct (In_dec eq_nat_dec b (freeVarTerm LNN (natToTerm a0))) as [e0 | e0].
                           - elim (closedNatToTerm _ _ e0).
                           - reflexivity. }
                       apply minimize1.
                       --- discriminate.
                       --- intro H1. destruct (freeVarSubFormula3 _ _ _ _ _ H1) as [H4 | H4].
                           *** assert (In 4 (freeVarFormula LNN (primRecPiFormulaHelp 0 A B))).
                               { eapply In_list_remove1. apply H4. }
                               decompose sum (freeVarPrimRecPiFormulaHelp1 _ _ _ _ H5).
                               ++++ destruct H as (H, H7). elim (proj1 (Nat.le_ngt 4 0)).
                                    ---- apply H. apply H6.
                                    ---- repeat constructor.
                               ++++ destruct H0 as (H0, H6). elim (proj1 (Nat.le_ngt 4 2)).
                                    ---- apply H0. apply H7.
                                    ---- repeat constructor.
                               ++++ discriminate H6.
                               ++++ discriminate H6.
                           *** elim (closedNatToTerm _ _ H4).
                       --- unfold primRecSigmaFormulaHelp.
                           repeat first
                            [ rewrite subExistSpecial; [| discriminate ]
                            | rewrite subForallSpecial; [| discriminate ]
                            | rewrite (subFormulaAnd LNN)
                            | rewrite (subFormulaImp LNN) ].
                           rewrite (subFormulaExist LNN). simpl.
                           repeat first
                            [ rewrite subExistSpecial; [| discriminate ]
                            | rewrite subForallSpecial; [| discriminate ]
                            | rewrite (subFormulaAnd LNN)
                            | rewrite (subFormulaImp LNN) ].
                           apply andI.
                           *** apply existI with (natToTerm (f 0)). rewrite (subFormulaAnd LNN). apply andI.
                               ++++ unfold f, evalPrimRecFunc. destruct H as (H, H1). simpl in H1.
                                    apply impE with (substituteFormula LNN A 0 (natToTerm g)).
                                    ---- apply iffE2. apply (reduceSub LNN).
                                         **** apply closedNN.
                                         **** apply iffTrans with (substituteFormula LNN A 2 (natToTerm x)).
                                              apply (reduceSub LNN).
                                              { apply closedNN. }
                                              { apply (subFormulaNil LNN). intro H4. elim (proj1 (Nat.le_ngt 1 0)).
                                                + apply H; auto.
                                                + auto. }
                                              { apply (subFormulaNil LNN). intro H4. elim (proj1 (Nat.le_ngt 2 0)).
                                                + apply H; auto.
                                                + auto. }
                                    ---- apply
                                          impE
                                           with (substituteFormula LNN (equal (var 0) (natToTerm g)) 0 (natToTerm g)).
                                         **** apply iffE2. apply (reduceSub LNN).
                                              { apply closedNN. }
                                              { auto. }
                                         **** rewrite (subFormulaEqual LNN). simpl. rewrite (subTermNil LNN).
                                              { apply eqRefl. }
                                              { apply closedNatToTerm. }
                               ++++ destruct repBeta as (H1, H4). simpl in H4. rewrite (subFormulaId LNN).
                                    apply
                                     impE
                                      with
                                        (substituteFormula LNN
                                           (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2
                                              (natToTerm x)) 0 (natToTerm (f 0))).
                                    ---- apply iffE2. apply (reduceSub LNN).
                                         **** apply closedNN.
                                         **** apply (reduceSub LNN).
                                              { apply closedNN. }
                                              { apply (subFormulaNil LNN). intro H5.
                                                destruct (freeVarSubFormula3 _ _ _ _ _ H5) as [H6 | H6].
                                                + elim (In_list_remove2 _ _ _ _ _ H6). reflexivity.
                                                + elim H6. }
                                    ---- apply
                                          impE
                                           with
                                             (substituteFormula LNN (equal (var 0) (natToTerm (beta x 0))) 0
                                                (natToTerm (f 0))).
                                         **** apply iffE2. apply (reduceSub LNN).
                                              { apply closedNN. }
                                              { apply
                                                 iffTrans
                                                  with
                                                    (substituteFormula LNN
                                                       (substituteFormula LNN betaFormula 2 (natToTerm x)) 1
                                                       (natToTerm 0)).
                                                + apply (subFormulaExch LNN).
                                                  - discriminate.
                                                  - apply closedNatToTerm.
                                                  - apply closedNatToTerm.
                                                + apply H4. }
                                         **** rewrite (subFormulaEqual LNN). simpl. rewrite (subTermNil LNN).
                                              { rewrite H2. apply eqRefl. apply Nat.lt_0_succ. }
                                              { apply closedNatToTerm. }
                           *** apply forallI.
                               ++++ apply closedNN.
                               ++++ apply impTrans with (LT (var 3) (natToTerm a)).
                                    ---- unfold LT at 1. repeat rewrite (subFormulaRelation LNN). simpl.
                                         rewrite (subTermNil LNN).
                                         **** apply impRefl.
                                         **** apply closedNatToTerm.
                                    ---- apply boundedLT. intros n H1. repeat rewrite (subFormulaId LNN).
                                         repeat first
                                          [ rewrite subExistSpecial; [| discriminate ]
                                          | rewrite subForallSpecial; [| discriminate ]
                                          | rewrite (subFormulaAnd LNN)
                                          | rewrite (subFormulaImp LNN) ].
                                         apply existI with (natToTerm (f (S n))).
                                         repeat first
                                          [ rewrite subExistSpecial; [| discriminate ]
                                          | rewrite subForallSpecial; [| discriminate ]
                                          | rewrite (subFormulaAnd LNN)
                                          | rewrite (subFormulaImp LNN) ].
                                         apply existI with (natToTerm (f n)).
                                         repeat first
                                          [ rewrite subExistSpecial; [| discriminate ]
                                          | rewrite subForallSpecial; [| discriminate ]
                                          | rewrite (subFormulaAnd LNN)
                                          | rewrite (subFormulaImp LNN) ].
                                         apply andI.
                                         **** destruct repBeta as (H4, H5). simpl in H5.
                                              apply
                                               impE
                                                with
                                                  (substituteFormula LNN
                                                     (substituteFormula LNN
                                                        (substituteFormula LNN
                                                           (substituteFormula LNN
                                                              (substituteFormula LNN
                                                                 (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                 (natToTerm x)) 0 (var 1)) 3 (natToTerm n)) 0
                                                        (natToTerm (f (S n)))) 1 (natToTerm (f n))).
                                              { apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                apply (subFormulaExch LNN).
                                                + discriminate.
                                                + apply closedNatToTerm.
                                                + intro H6. induction H6 as [H6 | H6].
                                                  - discriminate H6.
                                                  - elim H6. }
                                              { apply
                                                 impE
                                                  with
                                                    (substituteFormula LNN
                                                       (substituteFormula LNN
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                   (natToTerm x)) 3 (natToTerm n)) 0
                                                             (var 1)) 0 (natToTerm (f (S n)))) 1 (natToTerm (f n))).
                                                + apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                  apply (subFormulaExch LNN).
                                                  - discriminate.
                                                  - apply closedNatToTerm.
                                                  - intro H6. destruct H6 as [H6 | H6].
                                                    * discriminate H6.
                                                    * elim H6.
                                                + apply
                                                   impE
                                                    with
                                                      (substituteFormula LNN
                                                         (substituteFormula LNN
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN
                                                                  (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                  (natToTerm x)) 3 (natToTerm n)) 0 (var 1)) 1
                                                         (natToTerm (f n))).
                                                  - apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaNil LNN). intro H6.
                                                    destruct (freeVarSubFormula3 _ _ _ _ _ H6) as [H7 | H7].
                                                    * elim (In_list_remove2 _ _ _ _ _ H7). reflexivity.
                                                    * destruct H7 as [H7 | H7].
                                                      ++ discriminate H7.
                                                      ++ elim H7.
                                                  - apply
                                                     impE
                                                      with
                                                        (substituteFormula LNN
                                                           (substituteFormula LNN
                                                              (substituteFormula LNN
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN betaFormula 2 (natToTerm x)) 1
                                                                    (var 3)) 3 (natToTerm n)) 0 (var 1)) 1
                                                           (natToTerm (f n))).
                                                    * apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                      apply (subFormulaExch LNN).
                                                      ++ discriminate.
                                                      ++ intro H6. destruct H6 as [H6 | H6].
                                                         -- discriminate H6.
                                                         -- elim H6.
                                                      ++ apply closedNatToTerm.
                                                    * apply
                                                       impE
                                                        with
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 2 (natToTerm x)) 1
                                                                   (natToTerm n)) 0 (var 1)) 1 (natToTerm (f n))).
                                                      ++ apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                         apply (subFormulaTrans LNN). intro H6.
                                                         assert
                                                          (In 3
                                                             (freeVarFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)))).
                                                         { eapply In_list_remove1. apply H6. }
                                                         destruct (freeVarSubFormula3 _ _ _ _ _ H7) as [H8 | H8].
                                                         -- elim (proj1 (Nat.le_ngt 3 2)).
                                                            ** apply H4. eapply In_list_remove1. apply H8.
                                                            ** repeat constructor.
                                                         -- elim (closedNatToTerm _ _ H8).
                                                      ++ apply
                                                          impE
                                                           with
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN (equal (var 0) (natToTerm (beta x n))) 0
                                                                   (var 1)) 1 (natToTerm (f n))).
                                                         -- apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                            apply H5.
                                                         -- repeat rewrite (subFormulaEqual LNN). simpl.
                                                            repeat rewrite (subTermNil LNN (natToTerm (beta x n))).
                                                            ** rewrite H2. apply eqRefl. apply Nat.lt_lt_succ_r. apply H1.
                                                            ** apply closedNatToTerm.
                                                            ** apply closedNatToTerm. }
                                         **** apply andI.
                                              { destruct H0 as (H0, H4). simpl in H4.
                                                apply
                                                 impE
                                                  with
                                                    (substituteFormula LNN
                                                       (substituteFormula LNN
                                                          (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 3
                                                             (natToTerm n)) 0 (natToTerm (f (S n)))) 1
                                                       (natToTerm (f n))).
                                                + apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                  apply (subFormulaNil LNN). intro H5.
                                                  destruct (freeVarSubFormula3 _ _ _ _ _ H5) as [H6 | [H6 | H6]].
                                                  - elim (In_list_remove2 _ _ _ _ _ H6). reflexivity.
                                                  - discriminate H6.
                                                  - elim H6.
                                                + apply
                                                   impE
                                                    with
                                                      (substituteFormula LNN
                                                         (substituteFormula LNN (substituteFormula LNN B 2 (natToTerm n)) 0
                                                            (natToTerm (f (S n)))) 1 (natToTerm (f n))).
                                                  - apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaTrans LNN). intro H5. elim (proj1 (Nat.le_ngt 3 2)).
                                                    * apply H0. eapply In_list_remove1. apply H5.
                                                    * repeat constructor.
                                                  - apply
                                                     impE
                                                      with
                                                        (substituteFormula LNN
                                                           (substituteFormula LNN (substituteFormula LNN B 2 (natToTerm n)) 1
                                                              (natToTerm (f n))) 0 (natToTerm (f (S n)))).
                                                    * apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                      apply (subFormulaExch LNN).
                                                      ++ discriminate.
                                                      ++ apply closedNatToTerm.
                                                      ++ apply closedNatToTerm.
                                                    * apply
                                                       impE
                                                        with
                                                          (substituteFormula LNN (equal (var 0) (natToTerm (h n (f n)))) 0
                                                             (natToTerm (f (S n)))).
                                                      ++ apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                         apply H4.
                                                      ++ rewrite (subFormulaEqual LNN). simpl. rewrite (subTermNil LNN).
                                                         -- unfold f. simpl. apply eqRefl.
                                                         -- apply closedNatToTerm. }
                                              { apply
                                                 impE
                                                  with
                                                    (substituteFormula LNN
                                                       (substituteFormula LNN
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN betaFormula 2 (natToTerm x)) 1
                                                                (Succ (var 3))) 3 (natToTerm n)) 0
                                                          (natToTerm (f (S n)))) 1 (natToTerm (f n))).
                                                + apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                  apply (subFormulaExch LNN).
                                                  - discriminate.
                                                  - simpl. intro H4. lia.
                                                  - apply closedNatToTerm.
                                                + apply
                                                   impE
                                                    with
                                                      (substituteFormula LNN
                                                         (substituteFormula LNN
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN
                                                                  (substituteFormula LNN betaFormula 2 (natToTerm x)) 3
                                                                  (natToTerm n)) 1 (natToTerm (S n))) 0
                                                            (natToTerm (f (S n)))) 1 (natToTerm (f n))).
                                                  - apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    replace (natToTerm (S n)) with
                                                     (substituteTerm LNN (Succ (var 3)) 3 (natToTerm n)).
                                                    * apply (subSubFormula LNN).
                                                      ++ discriminate.
                                                      ++ apply closedNatToTerm.
                                                    * simpl. reflexivity.
                                                  - destruct repBeta as (H4, H5).
                                                    apply
                                                     impE
                                                      with
                                                        (substituteFormula LNN
                                                           (substituteFormula LNN
                                                              (substituteFormula LNN
                                                                 (substituteFormula LNN betaFormula 2 (natToTerm x)) 1
                                                                 (natToTerm (S n))) 0 (natToTerm (f (S n)))) 1 
                                                           (natToTerm (f n))).
                                                    * apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                      apply (subFormulaNil LNN). intro H6.
                                                      destruct (freeVarSubFormula3 _ _ _ _ _ H6) as [H7 | H7].
                                                      ++ elim (proj1 (Nat.le_ngt  3 2)).
                                                         -- apply H4. eapply In_list_remove1. apply H7.
                                                         -- repeat constructor.
                                                      ++ elim (closedNatToTerm _ _ H7).
                                                    * simpl in H5.
                                                      apply
                                                       impE
                                                        with
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN (equal (var 0) (natToTerm (beta x (S n)))) 0
                                                                (natToTerm (f (S n)))) 1 (natToTerm (f n))).
                                                      ++ apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                         apply H5.
                                                      ++ repeat rewrite (subFormulaEqual LNN). simpl.
                                                         repeat
                                                          (rewrite (subTermNil LNN (natToTerm (beta x (S n))));
                                                            [| apply closedNatToTerm ]).
                                                         rewrite (subTermNil LNN).
                                                         -- rewrite H2.
                                                            ** apply eqRefl.
                                                            ** apply (proj1 (Nat.succ_lt_mono n a)). apply H1.
                                                         -- apply closedNatToTerm. }
                       --- unfold primRecPiFormulaHelp.
                           repeat first
                            [ rewrite subExistSpecial; [| discriminate ]
                            | rewrite subForallSpecial; [| discriminate ]
                            | rewrite (subFormulaAnd LNN)
                            | rewrite (subFormulaImp LNN) ].
                           rewrite (subFormulaForall LNN). simpl.
                           repeat first
                            [ rewrite subExistSpecial; [| discriminate ]
                            | rewrite subForallSpecial; [| discriminate ]
                            | rewrite (subFormulaAnd LNN)
                            | rewrite (subFormulaImp LNN) ].
                           apply andI.
                           *** apply forallI.
                               ++++ apply closedNN.
                               ++++ destruct H as (H, H1). simpl in H1.
                                    apply
                                     impTrans
                                      with
                                        (substituteFormula LNN
                                           (substituteFormula LNN (equal (var 0) (natToTerm g)) 1 (natToTerm a))
                                           2 (natToTerm x)).
                                    ---- apply iffE1. apply (reduceSub LNN).
                                         **** apply closedNN.
                                         **** apply (reduceSub LNN).
                                              { apply closedNN. }
                                              { apply H1. }
                                    ---- repeat rewrite (subFormulaEqual LNN). simpl.
                                         repeat
                                          (rewrite (subTermNil LNN (natToTerm g)); [| apply closedNatToTerm ]).
                                         apply impI.
                                         rewrite <-
                                          (subFormulaId LNN
                                             (substituteFormula LNN
                                                (substituteFormula LNN
                                                   (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2
                                                      (var 2)) 1 (natToTerm a)) 2 (natToTerm x)) 0).
                                         apply
                                          impE
                                            with
                                             (substituteFormula LNN
                                                (substituteFormula LNN
                                                   (substituteFormula LNN
                                                      (substituteFormula LNN
                                                         (substituteFormula LNN betaFormula 1 Zero) 2 
                                                         (var 2)) 1 (natToTerm a)) 2 (natToTerm x)) 0 
                                                (natToTerm g)).
                                         **** apply (subWithEquals LNN). apply eqSym. apply Axm; right; constructor.
                                         **** apply sysWeaken. clear H1. destruct repBeta as (H1, H4). simpl in H4.
                                              rewrite (subFormulaId LNN).
                                              apply
                                               impE
                                                with
                                                  (substituteFormula LNN
                                                     (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2
                                                        (natToTerm x)) 0 (natToTerm (f 0))).
                                              { apply iffE2. apply (reduceSub LNN).
                                                + apply closedNN.
                                                + apply (reduceSub LNN). apply closedNN. apply (subFormulaNil LNN).
                                                  intro H5. destruct (freeVarSubFormula3 _ _ _ _ _ H5) as [H6 | H6].
                                                  - elim (In_list_remove2 _ _ _ _ _ H6). reflexivity.
                                                  - elim H6. }
                                              { apply
                                                 impE
                                                  with
                                                    (substituteFormula LNN (equal (var 0) (natToTerm (beta x 0))) 0
                                                       (natToTerm (f 0))).
                                                + apply iffE2. apply (reduceSub LNN).
                                                  - apply closedNN.
                                                  - apply
                                                     iffTrans
                                                      with
                                                        (substituteFormula LNN
                                                           (substituteFormula LNN betaFormula 2 (natToTerm x)) 1
                                                           (natToTerm 0)).
                                                    * apply (subFormulaExch LNN).
                                                      ++ discriminate.
                                                      ++ apply closedNatToTerm.
                                                      ++ apply closedNatToTerm.
                                                    * apply H4.
                                                + rewrite (subFormulaEqual LNN). simpl. rewrite (subTermNil LNN).
                                                  - rewrite H2. apply eqRefl. apply Nat.lt_0_succ.
                                                  - apply closedNatToTerm. }
                           *** apply forallI.
                               ++++ apply closedNN.
                               ++++ apply impTrans with (LT (var 3) (natToTerm a)).
                                    ---- unfold LT at 1. repeat rewrite (subFormulaRelation LNN). simpl.
                                         rewrite (subTermNil LNN).
                                         **** apply impRefl.
                                         **** apply closedNatToTerm.
                                    ---- apply boundedLT. intros n H1. repeat rewrite (subFormulaId LNN).
                                         repeat first
                                          [ rewrite subExistSpecial; [| discriminate ]
                                          | rewrite subForallSpecial; [| discriminate ]
                                          | rewrite (subFormulaAnd LNN)
                                          | rewrite (subFormulaImp LNN) ].
                                         apply forallI.
                                         **** apply closedNN.
                                         **** apply forallI.
                                              { apply closedNN. }
                                              { apply impTrans with (equal (var 1) (natToTerm (f n))).
                                                + destruct repBeta as (H4, H5). simpl in H5.
                                                  apply
                                                   impTrans
                                                    with
                                                      (substituteFormula LNN
                                                         (substituteFormula LNN
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                               (natToTerm x)) 0 (var 1)) 3 (natToTerm n)).
                                                  apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                  - apply (subFormulaExch LNN).
                                                    * discriminate.
                                                    * intro H6. destruct H6 as [H6 | H6].
                                                      ++ discriminate H6.
                                                      ++ elim H6.
                                                    * apply closedNatToTerm.
                                                  - apply
                                                     impTrans
                                                      with
                                                        (substituteFormula LNN
                                                           (substituteFormula LNN
                                                              (substituteFormula LNN
                                                                 (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                 (natToTerm x)) 3 (natToTerm n)) 0 (var 1)).
                                                    * apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                      apply (subFormulaExch LNN).
                                                      ++ discriminate.
                                                      ++ intro H6. destruct H6 as [H6 | H6].
                                                         -- discriminate H6.
                                                         -- elim H6.
                                                      ++ apply closedNatToTerm.
                                                    * apply
                                                       impTrans
                                                        with
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 2 (natToTerm x)) 1
                                                                   (var 3)) 3 (natToTerm n)) 0 (var 1)).
                                                      ++ apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                         apply (subFormulaExch LNN).
                                                         -- discriminate.
                                                         -- apply closedNatToTerm.
                                                         -- intro H6. destruct H6 as [H6 | H6].
                                                            ** discriminate H6.
                                                            ** elim H6.
                                                      ++ apply
                                                          impTrans
                                                           with
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 2 (natToTerm x)) 1
                                                                   (natToTerm n)) 0 (var 1)).
                                                         -- apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                            apply (subFormulaTrans LNN). intro H6.
                                                            assert
                                                             (In 3
                                                                (freeVarFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)))).
                                                            { eapply In_list_remove1. apply H6. }
                                                            destruct (freeVarSubFormula3 _ _ _ _ _ H7) as [H8 | H8].
                                                            ** elim (proj1 (Nat.le_ngt 3 2)). apply H4. eapply In_list_remove1.
                                                               +++ apply H8.
                                                               +++ repeat constructor.
                                                            ** elim (closedNatToTerm _ _ H8).
                                                         -- apply
                                                             impTrans
                                                              with
                                                                (substituteFormula LNN (equal (var 0) (natToTerm (beta x n))) 0 (var 1)).
                                                            ** apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                               apply H5.
                                                            ** repeat rewrite (subFormulaEqual LNN). simpl.
                                                               repeat rewrite (subTermNil LNN (natToTerm (beta x n))).
                                                               ++++ rewrite H2.
                                                                    ---- apply impRefl.
                                                                    ---- apply Nat.lt_lt_succ_r. apply H1.
                                                               ++++ apply closedNatToTerm.
                                                + rewrite <-
                                                   (subFormulaId LNN
                                                      (impH 
                                                         (substituteFormula LNN
                                                            (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2
                                                               (natToTerm x)) 3 (natToTerm n))
                                                         (substituteFormula LNN
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2
                                                               (natToTerm x)) 3 (natToTerm n))) 1).
                                                  apply impI.
                                                  apply
                                                   impE
                                                    with
                                                      (substituteFormula LNN
                                                         (impH 
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2
                                                                  (natToTerm x)) 3 (natToTerm n))
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN
                                                                  (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2
                                                                  (natToTerm x)) 3 (natToTerm n))) 1
                                                         (natToTerm (f n))).
                                                  - apply (subWithEquals LNN). apply eqSym. apply Axm; right; constructor.
                                                  - apply sysWeaken. rewrite (subFormulaImp LNN).
                                                    apply impTrans with (equal (var 0) (natToTerm (f (S n)))).
                                                    * destruct H0 as (H0, H4). simpl in H4.
                                                      apply
                                                       impTrans
                                                        with
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 3
                                                                (natToTerm n)) 1 (natToTerm (f n))).
                                                      ++ apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                         apply (subFormulaNil LNN). intro H5.
                                                         destruct (freeVarSubFormula3 _ _ _ _ _ H5) as [H6 | [H6 | H6]].
                                                         -- elim (In_list_remove2 _ _ _ _ _ H6). reflexivity.
                                                         -- discriminate H6.
                                                         -- elim H6.
                                                      ++ apply
                                                          impTrans
                                                           with
                                                             (substituteFormula LNN (substituteFormula LNN B 2 (natToTerm n)) 1
                                                                (natToTerm (f n))).
                                                         -- apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                            apply (subFormulaTrans LNN). intro H5. elim (proj1 (Nat.le_ngt 3 2)).
                                                            ** apply H0. eapply In_list_remove1. apply H5.
                                                            ** repeat constructor.
                                                         -- unfold f. simpl. apply iffE1. apply H4.
                                                    * rewrite <-
                                                       (subFormulaId LNN
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2
                                                                   (natToTerm x)) 3 (natToTerm n)) 1 (natToTerm (f n))) 0).
                                                      apply impI.
                                                      apply
                                                       impE
                                                        with
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN
                                                                      (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2
                                                                      (natToTerm x)) 3 (natToTerm n)) 1 (natToTerm (f n))) 0
                                                             (natToTerm (f (S n)))).
                                                      ++ apply (subWithEquals LNN). apply eqSym. apply Axm; right; constructor.
                                                      ++ apply sysWeaken.
                                                         apply
                                                          impE
                                                           with
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN
                                                                      (substituteFormula LNN
                                                                         (substituteFormula LNN betaFormula 2 (natToTerm x)) 1
                                                                         (Succ (var 3))) 3 (natToTerm n)) 1
                                                                   (natToTerm (f n))) 0 (natToTerm (f (S n)))).
                                                         -- apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                            apply (subFormulaExch LNN).
                                                            ** discriminate.
                                                            ** simpl. lia.
                                                            ** apply closedNatToTerm.
                                                         -- apply
                                                             impE
                                                              with
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN
                                                                      (substituteFormula LNN
                                                                         (substituteFormula LNN
                                                                            (substituteFormula LNN betaFormula 2 (natToTerm x)) 3
                                                                            (natToTerm n)) 1 (natToTerm (S n))) 1 
                                                                      (natToTerm (f n))) 0 (natToTerm (f (S n)))).
                                                            ** apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                               replace (natToTerm (S n)) with
                                                                (substituteTerm LNN (Succ (var 3)) 3 (natToTerm n)).
                                                               +++ apply (subSubFormula LNN).
                                                                   --- discriminate.
                                                                   --- apply closedNatToTerm.
                                                               +++ simpl. reflexivity.
                                                            ** destruct repBeta as (H4, H5).
                                                               apply
                                                                impE
                                                                 with
                                                                   (substituteFormula LNN
                                                                      (substituteFormula LNN
                                                                         (substituteFormula LNN
                                                                            (substituteFormula LNN betaFormula 2 (natToTerm x)) 1
                                                                            (natToTerm (S n))) 1 (natToTerm (f n))) 0
                                                                      (natToTerm (f (S n)))).
                                                               +++ apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                   apply (subFormulaNil LNN). intro H6.
                                                                   destruct (freeVarSubFormula3 _ _ _ _ _ H6) as [H7 | H7].
                                                                   --- elim (proj1 (Nat.le_ngt 3 2)).
                                                                       *** apply H4. eapply In_list_remove1. apply H7.
                                                                       *** repeat constructor.
                                                                   --- elim (closedNatToTerm _ _ H7).
                                                               +++ simpl in H5.
                                                                   apply
                                                                    impE
                                                                     with
                                                                       (substituteFormula LNN
                                                                          (substituteFormula LNN (equal (var 0) (natToTerm (beta x (S n)))) 1
                                                                             (natToTerm (f n))) 0 (natToTerm (f (S n)))).
                                                                   --- apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                       apply H5.
                                                                   --- repeat rewrite (subFormulaEqual LNN). simpl.
                                                                       repeat
                                                                        (rewrite (subTermNil LNN (natToTerm (beta x (S n))));
                                                                          [| apply closedNatToTerm ]).
                                                                       rewrite H2.
                                                                       *** apply eqRefl.
                                                                       *** repeat rewrite <-  Nat.succ_lt_mono. apply H1. }
                     --- intros b H1. assert (forall z : nat, decidable (f z = beta b z)).
                         { unfold decidable. intros z. destruct (eq_nat_dec (f z) (beta b z)); auto. }
                         decompose record
                          (notBoundedForall (fun z : nat => f z = beta b z) (S a) H4 (H3 b H1)).
                         apply impE with (notH (equal (natToTerm (f x0)) (natToTerm (beta b x0)))).
                         *** apply cp2. unfold primRecSigmaFormulaHelp.
                             repeat first
                              [ rewrite subExistSpecial; [| discriminate ]
                              | rewrite subForallSpecial; [| discriminate ]
                              | rewrite (subFormulaAnd LNN)
                              | rewrite (subFormulaImp LNN) ].
                             rewrite (subFormulaExist LNN). simpl.
                             repeat first
                              [ rewrite subExistSpecial; [| discriminate ]
                              | rewrite subForallSpecial; [| discriminate ]
                              | rewrite (subFormulaAnd LNN)
                              | rewrite (subFormulaImp LNN) ].
                             apply impI. clear H4 H1 H3 H2 x P H7.
                             induction x0 as [| x0 Hrecx0].
                             ++++ apply
                                   impE
                                    with
                                      (existH 0
                                         (andH
                                            (substituteFormula LNN (substituteFormula LNN A 1 (natToTerm a)) 2
                                               (natToTerm b))
                                            (substituteFormula LNN
                                               (substituteFormula LNN
                                                  (substituteFormula LNN
                                                     (substituteFormula LNN betaFormula 1 Zero) 2
                                                     (var 2)) 1 (natToTerm a)) 2 (natToTerm b)))).
                                  ---- apply sysWeaken. apply impI. apply existSys.
                                       **** apply closedNN.
                                       **** intro H1. destruct (in_app_or _ _ _ H1) as [H2 | H2].
                                            { elim (closedNatToTerm _ _ H2). }
                                            { elim (closedNatToTerm _ _ H2). }
                                       **** apply eqTrans with (var 0).
                                            { destruct H as (H, H1). simpl in H1. apply eqSym. unfold f; simpl.
                                              apply impE with A.
                                              + apply sysWeaken. apply iffE1. assumption.
                                              + apply
                                                 impE
                                                  with
                                                    (substituteFormula LNN (substituteFormula LNN A 1 (natToTerm a)) 2
                                                       (natToTerm b)).
                                                - apply sysWeaken. apply iffE1.
                                                  apply iffTrans with (substituteFormula LNN A 2 (natToTerm b)).
                                                  * repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaNil LNN). intro H2. elim (proj1 (Nat.le_ngt 1 0)); auto.
                                                  * apply (subFormulaNil LNN). intro H2. elim (proj1 (Nat.le_ngt 2 0)); auto.
                                                - eapply andE1. apply Axm; right; constructor. }
                                            { destruct repBeta as (H1, H2). simpl in H2.
                                              apply
                                               impE
                                                with
                                                  (substituteFormula LNN
                                                     (substituteFormula LNN
                                                        (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2
                                                           (var 2)) 1 (natToTerm a)) 2 (natToTerm b)).
                                              + apply sysWeaken. apply iffE1.
                                                apply
                                                 iffTrans
                                                  with
                                                    (substituteFormula LNN
                                                       (substituteFormula LNN betaFormula 2 (natToTerm b)) 1
                                                       (natToTerm 0)).
                                                - rewrite (subFormulaId LNN).
                                                  apply
                                                   iffTrans
                                                    with
                                                      (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2
                                                         (natToTerm b)).
                                                  * repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaNil LNN). intro H3.
                                                    destruct (freeVarSubFormula3 _ _ _ _ _ H3) as [H4 | H4].
                                                    ++ elim (In_list_remove2 _ _ _ _ _ H4); reflexivity.
                                                    ++ apply H4.
                                                  * apply (subFormulaExch LNN).
                                                    ++ discriminate.
                                                    ++ apply closedNatToTerm.
                                                    ++ apply closedNatToTerm.
                                                - apply H2.
                                              + eapply andE2. apply Axm; right; constructor. }
                                  ---- eapply andE1. apply Axm; right; constructor.
                             ++++ apply impE with (equal (natToTerm (f x0)) (natToTerm (beta b x0))); [| apply Hrecx0 ].
                                  ---- clear Hrecx0.
                                       apply
                                        impE
                                         with
                                           (forallH 3
                                              (impH 
                                                 (substituteFormula LNN
                                                    (substituteFormula LNN (LT (var 3) (var 1)) 1 (natToTerm a)) 2
                                                    (natToTerm b))
                                                 (existH 0
                                                    (existH 1
                                                       (andH
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                   (var 2)) 0 (var 1)) 2 (natToTerm b))
                                                          (andH 
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN B 2 (var 3)) 2
                                                                (natToTerm b))
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 1
                                                                      (Succ (var 3))) 2 (var 2)) 2
                                                                (natToTerm b))))))));
                                        [| eapply andE2; apply Axm; right; constructor ].
                                       apply sysWeaken.
                                       apply
                                        impTrans
                                         with
                                           (substituteFormula LNN
                                              (impH 
                                                 (substituteFormula LNN
                                                    (substituteFormula LNN (LT (var 3) (var 1)) 1 (natToTerm a)) 2
                                                    (natToTerm b))
                                                 (existH 0
                                                    (existH 1
                                                       (andH 
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                   (var 2)) 0 (var 1)) 2 (natToTerm b))
                                                          (andH
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN B 2 (var 3)) 2
                                                                (natToTerm b))
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 1
                                                                      (Succ (var 3))) 2 (var 2)) 2
                                                                (natToTerm b))))))) 3 (natToTerm x0)).
                                       **** apply impI. apply forallE. apply Axm; right; constructor.
                                       **** repeat first
                                             [ rewrite subExistSpecial; [| discriminate ]
                                             | rewrite subForallSpecial; [| discriminate ]
                                             | rewrite (subFormulaAnd LNN)
                                             | rewrite (subFormulaImp LNN) ].
                                            apply
                                             impTrans
                                              with
                                                (existH 0
                                                   (existH 1
                                                      (andH
                                                         (substituteFormula LNN
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN
                                                                  (substituteFormula LNN
                                                                     (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                     (var 2)) 0 (var 1)) 2 (natToTerm b)) 3
                                                            (natToTerm x0))
                                                         (andH
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN (substituteFormula LNN B 2 (var 3))
                                                                  2 (natToTerm b)) 3 (natToTerm x0))
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN
                                                                  (substituteFormula LNN
                                                                     (substituteFormula LNN betaFormula 1 (Succ (var 3)))
                                                                     2 (var 2)) 2 (natToTerm b)) 3
                                                               (natToTerm x0)))))).
                                            { apply impI.
                                              apply
                                               impE
                                                with
                                                  (substituteFormula LNN
                                                     (substituteFormula LNN
                                                        (substituteFormula LNN (LT (var 3) (var 1)) 1 (natToTerm a)) 2
                                                        (natToTerm b)) 3 (natToTerm x0)).
                                              + apply Axm; right; constructor.
                                              + apply sysWeaken. unfold LT. repeat rewrite (subFormulaRelation LNN). simpl.
                                                repeat (rewrite (subTermNil LNN (natToTerm a)); [| apply closedNatToTerm ]).
                                                fold (LT (natToTerm x0) (natToTerm a)). apply natLT. now rewrite Nat.succ_lt_mono.   }
                                            { apply impI.
                                              assert
                                               (forall n : nat,
                                                ~
                                                In n
                                                  (freeVarFormula LNN
                                                     (impH (equal (natToTerm (f x0)) (natToTerm (beta b x0)))
                                                        (equal (natToTerm (f (S x0))) (natToTerm (beta b (S x0))))))).
                                              { simpl. intros n H1.
                                                destruct (in_app_or _ _ _ H1) as [H2 | H2]; induction (in_app_or _ _ _ H2) as [H3 | H3];
                                                  elim (closedNatToTerm _ _ H3). }
                                              apply existSys.
                                              + apply closedNN.
                                              + apply H1.
                                              + apply existSys.
                                                - apply closedNN.
                                                - apply H1.
                                                - unfold f at 2; simpl. fold (f x0) in |- *.
                                                  apply impE with (equal (var 1) (natToTerm (beta b x0))).
                                                  * apply impI. apply impE with (equal (var 0) (natToTerm (h x0 (beta b x0)))).
                                                    ++ repeat apply impI. apply eqTrans with (var 0).
                                                       -- apply eqTrans with (natToTerm (h x0 (beta b x0))).
                                                          ** destruct (eq_nat_dec (f x0) (beta b x0)) as [a0 | b0].
                                                             +++ rewrite a0. apply eqRefl.
                                                             +++ apply contradiction with (equal (natToTerm (f x0)) (natToTerm (beta b x0))).
                                                                 --- apply Axm; right; constructor.
                                                                 --- do 4 apply sysWeaken. apply natNE. auto.
                                                          ** apply eqSym. apply Axm; left; right; constructor.
                                                       -- apply
                                                           impE
                                                            with
                                                              (substituteFormula LNN
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN
                                                                       (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 
                                                                       (var 2)) 2 (natToTerm b)) 3 (natToTerm x0)).
                                                          ** do 4 apply sysWeaken. apply iffE1. destruct repBeta as (H2, H3).
                                                             simpl in H3.
                                                             apply
                                                              iffTrans
                                                               with
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN betaFormula 2 (natToTerm b)) 1
                                                                    (natToTerm (S x0))).
                                                             +++ rewrite (subFormulaId LNN).
                                                                 apply
                                                                  iffTrans
                                                                   with
                                                                     (substituteFormula LNN
                                                                        (substituteFormula LNN
                                                                           (substituteFormula LNN betaFormula 2 (natToTerm b)) 1
                                                                           (Succ (var 3))) 3 (natToTerm x0)).
                                                                 --- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                     apply (subFormulaExch LNN).
                                                                     *** discriminate.
                                                                     *** simpl; lia.
                                                                     *** apply closedNatToTerm.
                                                                 --- apply
                                                                      iffTrans
                                                                       with
                                                                         (substituteFormula LNN
                                                                            (substituteFormula LNN
                                                                               (substituteFormula LNN betaFormula 2 (natToTerm b)) 3
                                                                               (natToTerm x0)) 1
                                                                            (substituteTerm LNN (Succ (var 3)) 3 (natToTerm x0))).
                                                                     *** apply (subSubFormula LNN).
                                                                         ++++ discriminate.
                                                                         ++++ apply closedNatToTerm.
                                                                     *** simpl.
                                                                         apply
                                                                          iffTrans
                                                                           with
                                                                             (substituteFormula LNN
                                                                                (substituteFormula LNN betaFormula 2 (natToTerm b)) 1
                                                                                (substituteTerm LNN (Succ (var 3)) 3 (natToTerm x0))).
                                                                         ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                              apply (subFormulaNil LNN).
                                                                              intro H4. destruct (freeVarSubFormula3 _ _ _ _ _ H4) as [H5 | H5].
                                                                              ---- elim (proj1 (Nat.le_ngt 3 2)).
                                                                                   **** apply H2. eapply In_list_remove1. apply H5.
                                                                                   **** repeat constructor.
                                                                              ---- elim (closedNatToTerm _ _ H5).
                                                                         ++++ apply iffRefl.
                                                             +++ apply H3.
                                                          ** eapply andE2. eapply andE2. apply Axm; do 3 left; right; constructor.
                                                     ++ apply
                                                         impE
                                                          with
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN
                                                                  (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2
                                                                     (natToTerm b)) 3 (natToTerm x0)) 1 (natToTerm (beta b x0))).
                                                        -- do 2 apply sysWeaken. destruct H0 as (H0, H2). simpl in H2. apply iffE1.
                                                           apply
                                                            iffTrans
                                                             with
                                                               (substituteFormula LNN (substituteFormula LNN B 2 (natToTerm x0)) 1
                                                                  (natToTerm (beta b x0))).
                                                           ** apply
                                                               iffTrans
                                                                with
                                                                  (substituteFormula LNN
                                                                     (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 3
                                                                        (natToTerm x0)) 1 (natToTerm (beta b x0))).
                                                              +++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                  apply (subFormulaNil LNN). intro H3.
                                                                  destruct (freeVarSubFormula3 _ _ _ _ _ H3) as [H4 | H4].
                                                                  --- elim (In_list_remove2 _ _ _ _ _ H4). reflexivity.
                                                                  --- destruct H4 as [H4 | H4].
                                                                      *** discriminate H4.
                                                                      *** apply H4.
                                                              +++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                  apply (subFormulaTrans LNN). intro H3. elim (proj1 (Nat.le_ngt 3 2)).
                                                                  --- apply H0. eapply In_list_remove1. apply H3.
                                                                  --- repeat constructor.
                                                           ** apply H2.
                                                        -- apply
                                                            impE
                                                             with
                                                               (substituteFormula LNN
                                                                  (substituteFormula LNN
                                                                     (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2
                                                                        (natToTerm b)) 3 (natToTerm x0)) 1 (var 1)).
                                                           ** apply (subWithEquals LNN). apply Axm; right; constructor.
                                                           ** repeat rewrite (subFormulaId LNN). eapply andE1. eapply andE2.
                                                              apply Axm; left; right; constructor.
                                                  * apply
                                                     impE
                                                      with
                                                        (substituteFormula LNN
                                                           (substituteFormula LNN
                                                              (substituteFormula LNN
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                    (var 2)) 0 (var 1)) 2 (natToTerm b)) 3
                                                           (natToTerm x0)).
                                                    ++ apply sysWeaken. apply iffE1. destruct repBeta as (H2, H3). simpl in H3.
                                                       apply
                                                        iffTrans
                                                         with
                                                           (substituteFormula LNN (equal (var 0) (natToTerm (beta b x0))) 0 (var 1)).
                                                       -- rewrite (subFormulaId LNN).
                                                          apply
                                                           iffTrans
                                                            with
                                                              (substituteFormula LNN
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN
                                                                       (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                       (natToTerm b)) 0 (var 1)) 3 (natToTerm x0)).
                                                          ** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                             apply (subFormulaExch LNN).
                                                             +++ discriminate.
                                                             +++ intros [H4 | H4].
                                                                 --- discriminate H4.
                                                                 --- apply H4.
                                                             +++ apply closedNatToTerm.
                                                          ** apply
                                                              iffTrans
                                                               with
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN
                                                                       (substituteFormula LNN
                                                                          (substituteFormula LNN betaFormula 1 (var 3)) 2 
                                                                          (natToTerm b)) 3 (natToTerm x0)) 0 (var 1)).
                                                             +++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                 apply (subFormulaExch LNN).
                                                                 --- discriminate.
                                                                 --- intros [H4 | H4].
                                                                     *** discriminate H4.
                                                                     *** apply H4.
                                                                 --- apply closedNatToTerm.
                                                             +++ apply (reduceSub LNN).
                                                                 --- apply closedNN.
                                                                 --- apply
                                                                      iffTrans
                                                                       with
                                                                         (substituteFormula LNN
                                                                            (substituteFormula LNN
                                                                               (substituteFormula LNN betaFormula 2 (natToTerm b)) 1
                                                                               (var 3)) 3 (natToTerm x0)).
                                                                     *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                         apply (subFormulaExch LNN).
                                                                         ++++ discriminate.
                                                                         ++++ intros [H4 | H4].
                                                                              ---- discriminate H4.
                                                                              ---- apply H4.
                                                                         ++++ apply closedNatToTerm.
                                                                     *** apply
                                                                          iffTrans
                                                                           with
                                                                             (substituteFormula LNN
                                                                                (substituteFormula LNN betaFormula 2 (natToTerm b)) 1
                                                                                (natToTerm x0)).
                                                                         ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                              apply (subFormulaTrans LNN). intro H4.
                                                                              assert
                                                                               (In 3
                                                                                  (freeVarFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)))).
                                                                              { eapply In_list_remove1. apply H4. }
                                                                              destruct (freeVarSubFormula3 _ _ _ _ _ H5) as [H7 | H7].
                                                                              ---- elim (proj1 (Nat.le_ngt 3 2)).
                                                                                   **** apply H2. eapply In_list_remove1. apply H7.
                                                                                   **** repeat constructor.
                                                                              ---- elim (closedNatToTerm _ _ H7).
                                                                         ++++ apply H3.
                                                       -- rewrite (subFormulaEqual LNN). simpl. rewrite subTermNil.
                                                          ** apply iffRefl.
                                                          ** apply closedNatToTerm.
                                                    ++ eapply andE1. apply Axm; right; constructor. }
                                  ---- apply Nat.lt_lt_succ_r. now rewrite Nat.succ_lt_mono. 
                         *** apply natNE. auto.
                     --- intros b H1. assert (forall z : nat, decidable (f z = beta b z)).
                         { unfold decidable. intros z. destruct (eq_nat_dec (f z) (beta b z)); auto. }
                         decompose record
                          (notBoundedForall (fun z : nat => f z = beta b z) (S a) H4 (H3 b H1)).
                         apply impE with (notH (equal (natToTerm (f x0)) (natToTerm (beta b x0)))).
                         *** apply cp2. unfold primRecPiFormulaHelp.
                             repeat first
                              [ rewrite subExistSpecial; [| discriminate ]
                              | rewrite subForallSpecial; [| discriminate ]
                              | rewrite (subFormulaAnd LNN)
                              | rewrite (subFormulaImp LNN) ].
                             rewrite (subFormulaForall LNN). simpl.
                             repeat first
                              [ rewrite subExistSpecial; [| discriminate ]
                              | rewrite subForallSpecial; [| discriminate ]
                              | rewrite (subFormulaAnd LNN)
                              | rewrite (subFormulaImp LNN) ].
                             apply impI. clear H4 H1 H3 H2 x P H7. induction x0 as [| x0 Hrecx0].
                             ++++ apply
                                   impE
                                    with
                                      (forallH 0
                                         (impH 
                                            (substituteFormula LNN (substituteFormula LNN A 1 (natToTerm a)) 2
                                               (natToTerm b))
                                            (substituteFormula LNN
                                               (substituteFormula LNN
                                                  (substituteFormula LNN
                                                     (substituteFormula LNN betaFormula 1 Zero) 2
                                                     (var 2)) 1 (natToTerm a)) 2 (natToTerm b)))).
                                  ---- apply sysWeaken.
                                       apply
                                        impTrans
                                         with
                                           (substituteFormula LNN
                                              (impH 
                                                 (substituteFormula LNN (substituteFormula LNN A 1 (natToTerm a)) 2
                                                    (natToTerm b))
                                                 (substituteFormula LNN
                                                    (substituteFormula LNN
                                                       (substituteFormula LNN
                                                          (substituteFormula LNN betaFormula 1 Zero) 2
                                                          (var 2)) 1 (natToTerm a)) 2 (natToTerm b))) 0
                                              (natToTerm (f 0))).
                                       **** apply impI. apply forallE. apply Axm; right; constructor.
                                       **** apply impI. rewrite (subFormulaImp LNN).
                                            apply
                                             impE
                                              with
                                                (substituteFormula LNN
                                                   (substituteFormula LNN
                                                      (substituteFormula LNN
                                                         (substituteFormula LNN
                                                            (substituteFormula LNN betaFormula 1 Zero) 2
                                                            (var 2)) 1 (natToTerm a)) 2 (natToTerm b)) 0
                                                   (natToTerm (f 0))).
                                            { apply sysWeaken.
                                              apply
                                               impTrans
                                                with
                                                  (substituteFormula LNN (equal (var 0) (natToTerm (beta b 0))) 0
                                                     (natToTerm (f 0))).
                                              + apply iffE1. apply (reduceSub LNN).
                                                - apply closedNN.
                                                - rewrite (subFormulaId LNN). destruct repBeta as (H1, H2). simpl in H2.
                                                  apply
                                                   iffTrans
                                                    with
                                                      (substituteFormula LNN
                                                         (substituteFormula LNN betaFormula 2 (natToTerm b)) 1
                                                         (natToTerm 0)).
                                                  * apply
                                                     iffTrans
                                                      with
                                                        (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2
                                                           (natToTerm b)).
                                                    ++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                       apply (subFormulaNil LNN). intro H3.
                                                       destruct (freeVarSubFormula3 _ _ _ _ _ H3) as [H4 | H4].
                                                       -- elim (In_list_remove2 _ _ _ _ _ H4); reflexivity.
                                                       -- apply H4.
                                                    ++ apply (subFormulaExch LNN).
                                                       -- discriminate.
                                                       -- apply closedNatToTerm.
                                                       -- apply closedNatToTerm.
                                                  * apply H2.
                                              + rewrite (subFormulaEqual LNN). simpl. rewrite (subTermNil LNN).
                                                - apply impRefl.
                                                - apply closedNatToTerm. }
                                            { apply
                                               impE
                                                with
                                                  (substituteFormula LNN
                                                     (substituteFormula LNN (substituteFormula LNN A 1 (natToTerm a)) 2
                                                        (natToTerm b)) 0 (natToTerm (f 0))).
                                              + apply Axm; right; constructor.
                                              + apply sysWeaken.
                                                apply
                                                 impE
                                                  with
                                                    (substituteFormula LNN (equal (var 0) (natToTerm (f 0))) 0
                                                       (natToTerm (f 0))).
                                                - apply iffE2. apply (reduceSub LNN); [ apply closedNN |].
                                                  destruct H as (H, H1). simpl in H1. unfold f; simpl.
                                                  apply iffTrans with A; [| assumption ].
                                                  apply iffTrans with (substituteFormula LNN A 2 (natToTerm b)).
                                                  * repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaNil LNN). intro H2. elim (proj1 (Nat.le_ngt 1 0)); auto.
                                                  * apply (subFormulaNil LNN). intro H2. elim (proj1 (Nat.le_ngt 2 0)); auto.
                                                - rewrite (subFormulaEqual LNN). simpl. rewrite (subTermNil LNN).
                                                  * apply eqRefl.
                                                  * apply closedNatToTerm. }
                                  ---- eapply andE1. apply Axm; right; constructor.
                             ++++ apply impE with (equal (natToTerm (f x0)) (natToTerm (beta b x0))); [| apply Hrecx0 ].
                                  ---- clear Hrecx0.
                                       apply
                                        impE
                                         with
                                           (forallH 3
                                              (impH 
                                                 (substituteFormula LNN
                                                    (substituteFormula LNN (LT (var 3) (var 1)) 1 (natToTerm a)) 2
                                                    (natToTerm b))
                                                 (forallH 0
                                                    (forallH 1
                                                       (impH 
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                   (var 2)) 0 (var 1)) 2 (natToTerm b))
                                                          (impH 
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN B 2 (var 3)) 2
                                                                (natToTerm b))
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 1
                                                                      (Succ (var 3))) 2 (var 2)) 2
                                                                (natToTerm b))))))));
                                        [| eapply andE2; apply Axm; right; constructor ].
                                       apply sysWeaken.
                                       apply
                                        impTrans
                                         with
                                           (substituteFormula LNN
                                              (impH 
                                                 (substituteFormula LNN
                                                    (substituteFormula LNN (LT (var 3) (var 1)) 1 (natToTerm a)) 2
                                                    (natToTerm b))
                                                 (forallH 0
                                                    (forallH 1
                                                       (impH
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                   (var 2)) 0 (var 1)) 2 (natToTerm b))
                                                          (impH 
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN B 2 (var 3)) 2
                                                                (natToTerm b))
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 1
                                                                      (Succ (var 3))) 2 (var 2)) 2
                                                                (natToTerm b))))))) 3 (natToTerm x0)).
                                       **** apply impI. apply forallE. apply Axm; right; constructor.
                                       **** repeat first
                                             [ rewrite subExistSpecial; [| discriminate ]
                                             | rewrite subForallSpecial; [| discriminate ]
                                             | rewrite (subFormulaAnd LNN)
                                             | rewrite (subFormulaImp LNN) ].
                                            apply
                                             impTrans
                                              with
                                                (forallH 0
                                                   (forallH 1
                                                      (impH 
                                                         (substituteFormula LNN
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN
                                                                  (substituteFormula LNN
                                                                     (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                     (var 2)) 0 (var 1)) 2 (natToTerm b)) 3
                                                            (natToTerm x0))
                                                         (impH 
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN (substituteFormula LNN B 2 (var 3))
                                                                  2 (natToTerm b)) 3 (natToTerm x0))
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN
                                                                  (substituteFormula LNN
                                                                     (substituteFormula LNN betaFormula 1 (Succ (var 3)))
                                                                     2 (var 2)) 2 (natToTerm b)) 3
                                                               (natToTerm x0)))))).
                                            { apply impI.
                                              apply
                                               impE
                                                with
                                                  (substituteFormula LNN
                                                     (substituteFormula LNN
                                                        (substituteFormula LNN (LT (var 3) (var 1)) 1 (natToTerm a)) 2
                                                        (natToTerm b)) 3 (natToTerm x0)).
                                              + apply Axm; right; constructor.
                                              + apply sysWeaken. unfold LT. repeat rewrite (subFormulaRelation LNN). simpl.
                                                repeat (rewrite (subTermNil LNN (natToTerm a)); [| apply closedNatToTerm ]).
                                                fold (LT (natToTerm x0) (natToTerm a)). apply natLT. now apply Nat.succ_lt_mono. }
                                            { apply
                                               impTrans
                                                with
                                                  (substituteFormula LNN
                                                     (forallH 1
                                                        (impH 
                                                           (substituteFormula LNN
                                                              (substituteFormula LNN
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN
                                                                       (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                       (var 2)) 0 (var 1)) 2 (natToTerm b)) 3
                                                              (natToTerm x0))
                                                           (impH
                                                              (substituteFormula LNN
                                                                 (substituteFormula LNN (substituteFormula LNN B 2 (var 3))
                                                                    2 (natToTerm b)) 3 (natToTerm x0))
                                                              (substituteFormula LNN
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN
                                                                       (substituteFormula LNN betaFormula 1 (Succ (var 3)))
                                                                       2 (var 2)) 2 (natToTerm b)) 3
                                                                 (natToTerm x0))))) 0 (natToTerm (f (S x0)))).
                                              + apply impI. apply forallE. apply Axm; right; constructor.
                                              + repeat first
                                                 [ rewrite subExistSpecial; [| discriminate ]
                                                 | rewrite subForallSpecial; [| discriminate ]
                                                 | rewrite (subFormulaAnd LNN)
                                                 | rewrite (subFormulaImp LNN) ].
                                                apply
                                                 impTrans
                                                  with
                                                    (substituteFormula LNN
                                                       (impH
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN
                                                                      (substituteFormula LNN
                                                                         (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                         (var 2)) 0 (var 1)) 2 (natToTerm b)) 3
                                                                (natToTerm x0)) 0 (natToTerm (f (S x0))))
                                                          (impH
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN (substituteFormula LNN B 2 (var 3))
                                                                      2 (natToTerm b)) 3 (natToTerm x0)) 0
                                                                (natToTerm (f (S x0))))
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN
                                                                      (substituteFormula LNN
                                                                         (substituteFormula LNN betaFormula 1 (Succ (var 3)))
                                                                         2 (var 2)) 2 (natToTerm b)) 3
                                                                   (natToTerm x0)) 0 (natToTerm (f (S x0)))))) 1
                                                       (natToTerm (beta b x0))).
                                                - apply impI. apply forallE. apply Axm; right; constructor.
                                                - repeat first
                                                   [ rewrite subExistSpecial; [| discriminate ]
                                                   | rewrite subForallSpecial; [| discriminate ]
                                                   | rewrite (subFormulaAnd LNN)
                                                   | rewrite (subFormulaImp LNN) ].
                                                  repeat apply impI.
                                                  apply
                                                   impE
                                                    with
                                                      (substituteFormula LNN (equal (var 0) (natToTerm (beta b (S x0)))) 0
                                                         (natToTerm (f (S x0)))).
                                                  * rewrite (subFormulaEqual LNN). simpl. rewrite (subTermNil LNN).
                                                    ++ apply impRefl.
                                                    ++ apply closedNatToTerm.
                                                  * apply
                                                     impE
                                                      with
                                                        (substituteFormula LNN
                                                           (substituteFormula LNN
                                                              (substituteFormula LNN
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN
                                                                       (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2
                                                                       (var 2)) 2 (natToTerm b)) 3 (natToTerm x0)) 0
                                                              (natToTerm (f (S x0)))) 1 (natToTerm (beta b x0))).
                                                    ++ do 2 apply sysWeaken. apply iffE1.
                                                       apply
                                                        iffTrans
                                                         with
                                                           (substituteFormula LNN
                                                              (substituteFormula LNN
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN
                                                                       (substituteFormula LNN
                                                                          (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2
                                                                          (var 2)) 2 (natToTerm b)) 3 (natToTerm x0)) 1
                                                                 (natToTerm (beta b x0))) 0 (natToTerm (f (S x0)))).
                                                       -- apply (subFormulaExch LNN).
                                                          ** discriminate.
                                                          ** apply closedNatToTerm.
                                                          ** apply closedNatToTerm.
                                                       -- apply (reduceSub LNN).
                                                          ** apply closedNN.
                                                          ** destruct H0 as (H0, H1). destruct repBeta as (H2, H3). simpl in H3.
                                                             apply
                                                              iffTrans
                                                               with
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN betaFormula 2 (natToTerm b)) 1
                                                                    (natToTerm (S x0))).
                                                             +++ rewrite (subFormulaId LNN).
                                                                 apply
                                                                  iffTrans
                                                                   with
                                                                     (substituteFormula LNN
                                                                        (substituteFormula LNN
                                                                           (substituteFormula LNN
                                                                              (substituteFormula LNN betaFormula 2 (natToTerm b)) 1
                                                                              (Succ (var 3))) 3 (natToTerm x0)) 1 (natToTerm (beta b x0))).
                                                                 --- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                     apply (subFormulaExch LNN).
                                                                     *** discriminate.
                                                                     *** intros [H4 | H4].
                                                                         ++++ discriminate H4.
                                                                         ++++ apply H4.
                                                                     *** apply closedNatToTerm.
                                                                 --- apply
                                                                      iffTrans
                                                                       with
                                                                         (substituteFormula LNN
                                                                            (substituteFormula LNN
                                                                               (substituteFormula LNN
                                                                                  (substituteFormula LNN betaFormula 2 (natToTerm b)) 3
                                                                                  (natToTerm x0)) 1
                                                                               (substituteTerm LNN (Succ (var 3)) 3 (natToTerm x0))) 1
                                                                            (natToTerm (beta b x0))).
                                                                     *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                         apply (subSubFormula LNN).
                                                                         ++++ discriminate.
                                                                         ++++ apply closedNatToTerm.
                                                                     *** simpl.
                                                                         apply
                                                                          iffTrans
                                                                           with
                                                                             (substituteFormula LNN
                                                                                (substituteFormula LNN
                                                                                   (substituteFormula LNN betaFormula 2 (natToTerm b)) 1
                                                                                   (substituteTerm LNN (Succ (var 3)) 3 (natToTerm x0))) 1
                                                                                (natToTerm (beta b x0))).
                                                                         ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                              apply (subFormulaNil LNN). intro H4.
                                                                              destruct (freeVarSubFormula3 _ _ _ _ _ H4) as [H5 | H5].
                                                                              { elim (proj1 (Nat.le_ngt  3 2)).
                                                                                + apply H2. eapply In_list_remove1. apply H5.
                                                                                + repeat constructor. }
                                                                              { elim (closedNatToTerm _ _ H5). }
                                                                         ++++ apply (subFormulaNil LNN). intro H4.
                                                                              destruct (freeVarSubFormula3 _ _ _ _ _ H4) as [H5 | H5].
                                                                              { elim (In_list_remove2 _ _ _ _ _ H5). reflexivity. }
                                                                              { rewrite freeVarSucc in H5. elim (closedNatToTerm _ _ H5). }
                                                             +++ apply H3.
                                                    ++ eapply impE.
                                                       -- eapply impE.
                                                          ** apply Axm; left; right; constructor.
                                                          ** do 2 apply sysWeaken.
                                                             apply
                                                              impE
                                                               with
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN (equal (var 1) (natToTerm (beta b x0))) 0
                                                                       (natToTerm (f (S x0)))) 1 (natToTerm (beta b x0))).
                                                             +++ apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                 destruct H0 as (H0, H1). destruct repBeta as (H2, H3). simpl in H3.
                                                                 apply
                                                                  iffTrans
                                                                   with
                                                                     (substituteFormula LNN (equal (var 0) (natToTerm (beta b x0))) 0 (var 1)).
                                                                 --- rewrite (subFormulaId LNN).
                                                                     apply
                                                                      iffTrans
                                                                       with
                                                                         (substituteFormula LNN
                                                                            (substituteFormula LNN
                                                                               (substituteFormula LNN
                                                                                  (substituteFormula LNN betaFormula 1 (var 3)) 2 
                                                                                  (natToTerm b)) 0 (var 1)) 3 (natToTerm x0)).
                                                                     *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                         apply (subFormulaExch LNN).
                                                                         ++++ discriminate.
                                                                         ++++ intros [H4 | H4].
                                                                              ---- discriminate H4.
                                                                              ---- apply H4.
                                                                         ++++ apply closedNatToTerm.
                                                                     *** apply
                                                                          iffTrans
                                                                           with
                                                                             (substituteFormula LNN
                                                                                (substituteFormula LNN
                                                                                   (substituteFormula LNN
                                                                                      (substituteFormula LNN betaFormula 1 (var 3)) 2
                                                                                      (natToTerm b)) 3 (natToTerm x0)) 0 (var 1)).
                                                                         ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                              apply (subFormulaExch LNN).
                                                                              ---- discriminate.
                                                                              ---- simpl. lia.
                                                                              ---- apply closedNatToTerm.
                                                                         ++++ apply (reduceSub LNN).
                                                                              ---- apply closedNN.
                                                                              ---- apply
                                                                                    iffTrans
                                                                                     with
                                                                                       (substituteFormula LNN
                                                                                          (substituteFormula LNN
                                                                                             (substituteFormula LNN betaFormula 2 (natToTerm b)) 1
                                                                                             (var 3)) 3 (natToTerm x0)).
                                                                                   **** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                                        apply (subFormulaExch LNN).
                                                                                        { discriminate. }
                                                                                        { simpl. lia. }
                                                                                        { apply closedNatToTerm. }
                                                                                   **** apply
                                                                                         iffTrans
                                                                                          with
                                                                                            (substituteFormula LNN
                                                                                               (substituteFormula LNN betaFormula 2 (natToTerm b)) 1 
                                                                                               (natToTerm x0)).
                                                                                        { repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                                          apply (subFormulaTrans LNN). intro H4.
                                                                                          assert
                                                                                           (In 3
                                                                                              (freeVarFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)))).
                                                                                          { eapply In_list_remove1. apply H4. }
                                                                                          destruct (freeVarSubFormula3 _ _ _ _ _ H5) as [H7 | H7].
                                                                                          + elim (proj1 (Nat.le_ngt 3 2)).
                                                                                            - apply H2. eapply In_list_remove1. apply H7.
                                                                                            - repeat constructor.
                                                                                          + elim (closedNatToTerm _ _ H7). }
                                                                                        { apply H3. }
                                                                 --- rewrite (subFormulaEqual LNN). simpl. rewrite subTermNil.
                                                                     **** apply iffRefl.
                                                                     **** apply closedNatToTerm.
                                                             +++ repeat rewrite (subFormulaEqual LNN). simpl.
                                                                 repeat rewrite (subTermNil LNN (natToTerm (beta b x0)));
                                                                   try apply closedNatToTerm.
                                                                 apply eqRefl.
                                                       -- apply
                                                           impE
                                                            with
                                                              (substituteFormula LNN
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN
                                                                       (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2
                                                                          (natToTerm b)) 3 (natToTerm x0)) 0
                                                                    (natToTerm (f (S x0)))) 1 (natToTerm (f x0))).
                                                          ** apply (subWithEquals LNN). apply Axm; right; constructor.
                                                          ** do 2 apply sysWeaken.
                                                             apply
                                                              impE
                                                               with
                                                                 (substituteFormula LNN
                                                                    (substituteFormula LNN
                                                                       (substituteFormula LNN
                                                                          (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2
                                                                             (natToTerm b)) 3 (natToTerm x0)) 1
                                                                       (natToTerm (f x0))) 0 (natToTerm (f (S x0)))).
                                                             +++ apply iffE1. apply (subFormulaExch LNN).
                                                                 --- discriminate.
                                                                 --- apply closedNatToTerm.
                                                                 --- apply closedNatToTerm.
                                                             +++ apply
                                                                  impE
                                                                   with
                                                                     (substituteFormula LNN (equal (var 0) (natToTerm (f (S x0)))) 0
                                                                        (natToTerm (f (S x0)))).
                                                                 --- apply iffE2. apply (reduceSub LNN).
                                                                     *** apply closedNN.
                                                                     *** destruct H0 as (H0, H1). simpl in H1.
                                                                         apply
                                                                          iffTrans
                                                                           with
                                                                             (substituteFormula LNN (substituteFormula LNN B 2 (natToTerm x0)) 1
                                                                                (natToTerm (f x0))).
                                                                         ++++ apply
                                                                               iffTrans
                                                                                with
                                                                                  (substituteFormula LNN
                                                                                     (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 3
                                                                                        (natToTerm x0)) 1 (natToTerm (f x0))).
                                                                              ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                                   apply (subFormulaNil LNN). intro H2.
                                                                                   destruct (freeVarSubFormula3 _ _ _ _ _ H2) as [H3 | H3].
                                                                                   **** elim (In_list_remove2 _ _ _ _ _ H3). reflexivity.
                                                                                   **** destruct H3 as [H3 | H3].
                                                                                        { discriminate H3. }
                                                                                        { apply H3. }
                                                                              ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                                   apply (subFormulaTrans LNN). intro H2.
                                                                                   elim (proj1 (Nat.le_ngt 3 2)).
                                                                                   **** apply H0. eapply In_list_remove1. apply H2.
                                                                                   **** repeat constructor.
                                                                         ++++ unfold f. simpl. apply H1.
                                                                 --- rewrite (subFormulaEqual LNN). simpl.
                                                                     rewrite (subTermNil LNN).
                                                                     *** apply eqRefl.
                                                                     *** apply closedNatToTerm. }
                                  ---- apply Nat.lt_lt_succ_r. now rewrite Nat.succ_lt_mono. 
                         *** apply natNE. auto.
                 +++ apply iffRefl.
           -- apply
               iffTrans
                with
                  (substituteFormula LNN
                     (substituteFormula LNN betaFormula 1 (natToTerm a)) 2 
                     (natToTerm x)).
              ** apply iffI.
                 +++ apply impI. apply existSys.
                     --- apply closedNN.
                     --- intro H1. destruct (freeVarSubFormula3 _ _ _ _ _ H1) as [H4 | H4].
                         *** elim (In_list_remove2 _ _ _ _ _ H4). reflexivity.
                         *** elim (closedNatToTerm _ _ H4).
                     --- apply
                          impE
                           with
                             (substituteFormula LNN
                                (substituteFormula LNN betaFormula 1 (natToTerm a)) 2 
                                (var 2)).
                         *** apply (subWithEquals LNN). eapply andE1. apply Axm; right; constructor.
                         *** rewrite (subFormulaId LNN). eapply andE2. apply Axm; right; constructor.
                 +++ apply impI. apply existI with (natToTerm x). rewrite (subFormulaAnd LNN). apply andI.
                     --- rewrite (subFormulaEqual LNN). simpl. rewrite subTermNil.
                         *** apply eqRefl.
                         *** apply closedNatToTerm.
                     --- apply Axm; right; constructor.
              ** apply
                  iffTrans
                   with
                     (substituteFormula LNN
                        (substituteFormula LNN betaFormula 2 (natToTerm x)) 1 
                        (natToTerm a)).
                 +++ apply (subFormulaExch LNN).
                     --- discriminate.
                     --- apply closedNatToTerm.
                     --- apply closedNatToTerm.
                 +++ rewrite H2.
                     --- destruct repBeta as (H1, H4). apply H4.
                     --- apply Nat.lt_succ_diag_r.
        ++ unfold P. intros z H2. unfold beta. repeat rewrite cPairProjections1. repeat rewrite cPairProjections2.
           apply (p z). assumption.
    + simpl. intros A g H B h H0 a a0.
      apply
       Representable_ext
        with (evalPrimRecFunc n (g a0) (fun x y : nat => h x y a0) a).
      - induction a as [| a Hreca].
        * simpl. apply extEqualRefl.
        * simpl. apply extEqualCompose2.
          ++ apply Hreca.
          ++ apply extEqualRefl.
      - destruct H as (H, H1). destruct H0 as (H0, H2). simpl in H1. simpl in H2.
        assert
         (RepresentableHelp n
            (evalPrimRecFunc n (g a0) (fun x y : nat => h x y a0) a)
            (substituteFormula LNN
               (primRecSigmaFormula n (substituteFormula LNN A (S n) (natToTerm a0))
                  (substituteFormula LNN
                     (substituteFormula LNN
                        (substituteFormula LNN B (S n) (natToTerm a0))
                        (S (S n)) (var (S n))) (S (S (S n)))
                     (var (S (S n))))) (S n) (natToTerm a))).
        { apply Hrecn.
          + split.
            - intros v H3. induction (freeVarSubFormula3 _ _ _ _ _ H3).
              * assert (v <= S n).
                { apply H. eapply In_list_remove1. apply H4. }
                destruct (proj1 (Nat.lt_eq_cases v (S n)) H5) as [H6 | H6].
                ++ now apply Nat.lt_succ_r. 
                ++ elim (In_list_remove2 _ _ _ _ _ H4). auto.
              * elim (closedNatToTerm _ _ H4).
            - apply H1.
          + split.
            - intros v H3.
              repeat
               match goal with
               | H:(In v (List.remove  eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _ =>
                   assert (In v (freeVarFormula LNN X2));
                    [ eapply In_list_remove1; apply H
                    | assert (v <> X1); [ eapply In_list_remove2; apply H | clear H ] ]
               | H:(In v (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _ =>
                   induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
               end.
              * assert (v <= S (S (S n))).
                { apply H0. auto. }
                lia.
              * elim (closedNatToTerm _ _ H4).
              * destruct H4 as [H3| H3].
                ++ rewrite <- H3. apply Nat.le_succ_diag_r.
                ++ elim H3.
              * destruct H4 as [H3| H3].
                ++ rewrite <- H3. apply le_n.
                ++ elim H3.
            - simpl. intros.
              apply
               RepresentableAlternate
                with
                  (substituteFormula LNN
                     (substituteFormula LNN
                        (substituteFormula LNN B (S (S (S n))) (natToTerm a1))
                        (S (S n)) (natToTerm a2)) (S n) (natToTerm a0)).
              * apply iffSym.
                apply
                 iffTrans
                  with
                    (substituteFormula LNN
                       (substituteFormula LNN
                          (substituteFormula LNN
                             (substituteFormula LNN B (S n) (natToTerm a0))
                             (S (S n)) (var (S n))) (S (S (S n))) (natToTerm a1))
                       (S n) (natToTerm a2)).
                ++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                   apply (subFormulaTrans LNN). intro H3.
                   repeat
                    match goal with
                    | H:(In ?X1 (List.remove eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _
                    =>
                        elim (In_list_remove2 _ _ _ _ _ H); reflexivity
                    | H:(In ?X3 (List.remove  eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _
                    =>
                        assert (In X3 (freeVarFormula LNN X2));
                         [ eapply In_list_remove1; apply H
                         | assert (X3 <> X1); [ eapply In_list_remove2; apply H | clear H ] ]
                    | H:(In ?X4 (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _
                    =>
                        induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
                    | H:(In ?X4 (freeVarTerm LNN (var ?X1))) |- _ =>
                        induction H as [H3| H3]; [ idtac | contradiction ]
                    end.
                    congruence.
                 ++ apply
                     iffTrans
                      with
                        (substituteFormula LNN
                           (substituteFormula LNN
                              (substituteFormula LNN
                                 (substituteFormula LNN B (S n) (natToTerm a0))
                                 (S (S (S n))) (natToTerm a1)) (S (S n))
                              (var (S n))) (S n) (natToTerm a2)).
                    -- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaExch LNN).
                       ** lia.
                       ** simpl. lia.
                       ** apply closedNatToTerm.
                    -- apply
                        iffTrans
                         with
                           (substituteFormula LNN
                              (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0))
                                 (S (S (S n))) (natToTerm a1)) (S (S n)) (natToTerm a2)).
                       ** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                          apply (subFormulaTrans LNN). intro H3.
                          repeat
                           match goal with
                           | H:(In ?X1 (List.remove eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _
                           =>
                               elim (In_list_remove2 _ _ _ _ _ H); reflexivity
                           | H:(In ?X3 (List.remove eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _
                           =>
                               assert (In X3 (freeVarFormula LNN X2));
                                [ eapply In_list_remove1; apply H
                                | assert (X3 <> X1); [ eapply In_list_remove2; apply H | clear H ] ]
                           | H:(In ?X4 (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _
                           =>
                               induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
                           | H:(In ?X4 (freeVarTerm LNN (var ?X1))) |- _ =>
                               simple induction H; [ idtac | contradiction ]
                           end.
                          +++ elim (closedNatToTerm _ _ H3).
                          +++ elim (closedNatToTerm _ _ H3).
                       ** apply
                           iffTrans
                            with
                              (substituteFormula LNN
                                 (substituteFormula LNN
                                    (substituteFormula LNN B (S (S (S n))) (natToTerm a1)) 
                                    (S n) (natToTerm a0)) (S (S n)) (natToTerm a2)).
                          +++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                              apply (subFormulaExch LNN).
                              --- lia.
                              --- apply closedNatToTerm.
                              --- apply closedNatToTerm.
                          +++ apply (subFormulaExch LNN).
                              --- lia.
                              --- apply closedNatToTerm.
                              --- apply closedNatToTerm.
              * apply H2. }
        apply
         RepresentableAlternate
          with
            (substituteFormula LNN
               (primRecSigmaFormula n (substituteFormula LNN A (S n) (natToTerm a0))
                  (substituteFormula LNN
                     (substituteFormula LNN
                        (substituteFormula LNN B (S n) (natToTerm a0)) 
                        (S (S n)) (var (S n))) (S (S (S n))) 
                     (var (S (S n))))) (S n) (natToTerm a)).
        * clear H3 Hrecn. apply iffSym.
          apply
           iffTrans
            with
              (substituteFormula LNN
                 (substituteFormula LNN (primRecSigmaFormula (S n) A B) 
                    (S n) (natToTerm a0)) (S (S n)) (natToTerm a)).
          ++ apply (subFormulaExch LNN).
             -- lia.
             -- apply closedNatToTerm.
             -- apply closedNatToTerm.
          ++ apply
              iffTrans
               with
                 (substituteFormula LNN
                    (substituteFormula LNN
                       (substituteFormula LNN (primRecSigmaFormula (S n) A B) 
                          (S n) (natToTerm a0)) (S (S n)) (var (S n))) 
                    (S n) (natToTerm a)).
             -- apply iffSym. apply (subFormulaTrans LNN). intro H3.
                assert
                 (In (S n)
                    (freeVarFormula LNN
                       (substituteFormula LNN (primRecSigmaFormula (S n) A B) 
                          (S n) (natToTerm a0)))).
                 { eapply In_list_remove1. apply H3. }
                destruct (freeVarSubFormula3 _ _ _ _ _ H4) as [H5 | H5].
                ** elim (In_list_remove2 _ _ _ _ _ H5). reflexivity.
                ** elim (closedNatToTerm _ _ H5).
             -- apply (reduceSub LNN). apply closedNN. unfold primRecSigmaFormula.
                assert (H3 := I). (* For hyps numbering compatibility *)
                assert (H4 := I). (* For hyps numbering compatibility *)
                assert
                 (subExistSpecial :
                  forall (F : Formula) (a b c : nat),
                  b <> c ->
                  substituteFormula LNN (existH b F) c (natToTerm a) =
                  existH b (substituteFormula LNN F c (natToTerm a))).
                { intros F a1 b c H5. rewrite (subFormulaExist LNN). destruct (eq_nat_dec b c) as [e | e].
                  + elim H5. auto.
                  + destruct (In_dec eq_nat_dec b (freeVarTerm LNN (natToTerm a1))) as [e0 | e0].
                    - elim (closedNatToTerm _ _ e0).
                    - reflexivity. }
                assert
                 (subForallSpecial :
                  forall (F : Formula) (a b c : nat),
                  b <> c ->
                  substituteFormula LNN (forallH b F) c (natToTerm a) =
                  forallH b (substituteFormula LNN F c (natToTerm a))).
                { intros F a1 b c H5. rewrite (subFormulaForall LNN). destruct (eq_nat_dec b c) as [e | e].
                  + elim H5. auto.
                  + destruct (In_dec eq_nat_dec b (freeVarTerm LNN (natToTerm a1))) as [e0 | e0].
                    - elim (closedNatToTerm _ _ e0).
                    - reflexivity. }
                assert (forall a b : nat, a <> b -> b <> a) by auto.
                assert
                 (subExistSpecial2 :
                  forall (F : Formula) (a b c : nat),
                  b <> c ->
                  b <> a ->
                  substituteFormula LNN (existH b F) c (var a) =
                  existH b (substituteFormula LNN F c (var a))).
                { intros F a1 b c H6 H7. rewrite (subFormulaExist LNN). destruct (eq_nat_dec b c) as [e | e].
                  + elim H6. auto.
                  + destruct (In_dec eq_nat_dec b (freeVarTerm LNN (var a1))) as [e0 | e0].
                    - destruct e0 as [H8| H8].
                      * elim H7; auto.
                      * elim H8.
                    - reflexivity. }
                assert
                 (subForallSpecial2 :
                  forall (F : Formula) (a b c : nat),
                  b <> c ->
                  b <> a ->
                  substituteFormula LNN (forallH b F) c (var a) =
                  forallH b (substituteFormula LNN F c (var a))).
                { intros F a1 b c H6 H7. rewrite (subFormulaForall LNN). destruct (eq_nat_dec b c) as [e | e].
                  + elim H6. auto.
                  + destruct (In_dec eq_nat_dec b (freeVarTerm LNN (var a1))) as [e0 | e0].
                    - destruct e0 as [H8 | H8].
                      * elim H7; auto.
                      * elim H8.
                    - reflexivity. }
                assert (H6 := I). (* For hyps numbering compatibility *)
                assert (H7 := I). (* For hyps numbering compatibility *)
                assert
                 (forall (a b : Term) (v : nat) (s : Term),
                  substituteFormula LNN (LT a b) v s =
                  LT (substituteTerm LNN a v s) (substituteTerm LNN b v s)).
                { intros a1 b v s. unfold LT. rewrite (subFormulaRelation LNN). reflexivity. }
                assert
                 (forall (f : Formula) (a : nat) (s : Term),
                  substituteFormula LNN (existH a f) a s = existH a f).
                { intros f a1 s. rewrite (subFormulaExist LNN). destruct (eq_nat_dec a1 a1) as [e | e].
                  + reflexivity.
                  + elim e; auto. }
                assert
                 (forall (f : Formula) (a : nat) (s : Term),
                  substituteFormula LNN (forallH a f) a s = forallH a f).
                { intros f a1 s. rewrite (subFormulaForall LNN). destruct (eq_nat_dec a1 a1) as [e | e].
                  + reflexivity.
                  + elim e; auto. }
                assert (H11 := I). (* For hyps numbering compatibility *)
                assert (H12 := I). (* For hyps numbering compatibility *)
                assert (H13 := I). (* For hyps numbering compatibility *)
                assert (H14 := I). (* For hyps numbering compatibility *)
                assert (H15 := I). (* For hyps numbering compatibility *)
                assert (H16 := I). (* For hyps numbering compatibility *)
Opaque substituteFormula.
                unfold minimize, primRecSigmaFormulaHelp, primRecPiFormulaHelp;
                 repeat first
                  [ discriminate
                  | simple apply iffRefl
                  | simple apply (reduceExist LNN); [ apply closedNN |]
                  | simple apply (reduceForall LNN); [ apply closedNN |]
                  | simple apply (reduceAnd LNN)
                  | simple apply (reduceImp LNN)
                  | simple apply (reduceNot LNN)
                  | match goal with
                    |  |-
                    (folProof.SysPrf LNN NN
                       (iffH 
                          (substituteFormula LNN
                             (substituteFormula LNN (existH (S (S n)) ?X1) ?X2
                                (var (S (S n)))) ?X3 ?X4) _)) =>
                        apply
                         iffTrans
                          with
                            (substituteFormula LNN
                               (substituteFormula LNN
                                  (existH (S n)
                                     (substituteFormula LNN X1 (S (S n)) (var (S n)))) X2
                                  (var (S (S n)))) X3 X4);
                         [ repeat (apply (reduceSub LNN); [ apply closedNN |]);
                            apply (rebindExist LNN)
                         |]
                    |  |-
                    (folProof.SysPrf LNN NN
                       (iffH 
                          (substituteFormula LNN
                             (substituteFormula LNN
                                (substituteFormula LNN (forallH (S (S n)) ?X1) ?X2
                                   (var (S (S n)))) ?X3 ?X4) ?X5 ?X6) _)) =>
                        apply
                         iffTrans
                          with
                            (substituteFormula LNN
                               (substituteFormula LNN
                                  (substituteFormula LNN
                                     (forallH (S n)
                                        (substituteFormula LNN X1 (S (S n)) (var (S n)))) X2
                                     (var (S (S n)))) X3 X4) X5 X6);
                         [ repeat (apply (reduceSub LNN); [ apply closedNN |]);
                            apply (rebindForall LNN)
                         |]
                    |  |-
                    (folProof.SysPrf LNN NN
                       (iffH 
                          (substituteFormula LNN (forallH (S ?X6) ?X1) ?X2 (var (S ?X6))) _))
                    =>
                        apply
                         iffTrans
                          with
                            (substituteFormula LNN
                               (forallH X6 (substituteFormula LNN X1 (S X6) (var X6))) X2
                               (var (S X6)));
                         [ repeat (apply (reduceSub LNN); [ apply closedNN |]);
                            apply (rebindForall LNN)
                         |]
                    |  |- (folProof.SysPrf LNN NN (iffH (existH (S ?X1) ?X2) ?X3)) =>
                        apply
                         iffTrans with (existH X1 (substituteFormula LNN X2 (S X1) (var X1)));
                         [ apply (rebindExist LNN) |]
                    |  |- (folProof.SysPrf LNN NN (iffH (forallH (S ?X1) ?X2) ?X3))
                    =>
                        apply
                         iffTrans
                          with (forallH X1 (substituteFormula LNN X2 (S X1) (var X1)));
                         [ apply (rebindForall LNN) |]
                    |  |- (?X1 <> S ?X1) => lia
                    |  |- (?X1 <> S (S ?X1)) => lia
                    |  |- (?X1 <> S (S (S ?X1))) => lia
                    |  |- (?X1 <> S (S (S (S ?X1)))) => lia
                    |  |- (S ?X1 <> ?X1) => lia
                    |  |- (S (S ?X1) <> ?X1) => lia
                    |  |- (S (S (S ?X1)) <> ?X1) => lia
                    |  |- (S (S (S (S ?X1))) <> ?X1) => lia
                    |  |- (~ In _ _) => PRsolveFV A B n
                    end
                  | rewrite H9
                  | rewrite H10
                  | rewrite (subFormulaAnd LNN)
                  | rewrite (subFormulaImp LNN)
                  | rewrite (subFormulaNot LNN)
                  | rewrite H8
                  | rewrite (subTermVar1 LNN)
                  | rewrite (subTermVar2 LNN)
                  | rewrite subForallSpecial2;
                     let fail :=
                      (match goal with
                       |  |- (?X1 <> ?X1) => constr:(false)
                       | _ => constr:(true)
                       end) in
                     match constr:(fail) with
                     | true => idtac
                     end
                  | rewrite subForallSpecial
                  | rewrite subExistSpecial2;
                     let fail :=
                      (match goal with
                       |  |- (?X1 <> ?X1) => constr:(false)
                       | _ => constr:(true)
                       end) in
                     match constr:(fail) with
                     | true => idtac
                     end
                  | rewrite subExistSpecial ].
                ** apply
                    iffTrans
                     with
                       (substituteFormula LNN (substituteFormula LNN A (S n) (natToTerm a0))
                          (S (S (S n))) (var (S (S n)))).
                   +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN). PRsolveFV A B n.
                   +++ apply (subFormulaNil LNN). PRsolveFV A B n.
                ** apply
                    iffTrans
                     with
                       (substituteFormula LNN
                          (substituteFormula LNN
                             (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2
                                (var (S (S (S n))))) (S (S n)) (var (S n))) 
                          (S (S (S n))) (var (S (S n)))).
                   +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN). PRsolveFV A B n.
                   +++ apply
                        iffTrans
                         with
                           (substituteFormula LNN
                              (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2
                                 (var (S (S (S n))))) (S (S (S n))) (var (S (S n)))).
                       --- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN). PRsolveFV A B n.
                       --- apply (subFormulaTrans LNN). PRsolveFV A B n.
                ** apply
                    iffTrans
                     with
                       (substituteFormula LNN
                          (substituteFormula LNN
                             (substituteFormula LNN
                                (substituteFormula LNN
                                   (substituteFormula LNN
                                      (substituteFormula LNN betaFormula 1
                                         (var (S (S (S (S n)))))) 2 (var (S (S (S n))))) 0
                                   (var (S (S n)))) (S (S n)) (var (S n))) 
                             (S (S (S n))) (var (S (S n)))) (S (S (S (S n))))
                          (var (S (S (S n))))).
                   +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN). PRsolveFV A B n.
                   +++ apply
                        iffTrans
                         with
                           (substituteFormula LNN
                              (substituteFormula LNN
                                 (substituteFormula LNN
                                    (substituteFormula LNN
                                       (substituteFormula LNN betaFormula 1 (var (S (S (S (S n))))))
                                       2 (var (S (S (S n))))) 0 (var (S n))) 
                                 (S (S (S n))) (var (S (S n)))) (S (S (S (S n))))
                              (var (S (S (S n))))).
                       --- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaTrans LNN). PRsolveFV A B n.
                       --- apply
                            iffTrans
                             with
                               (substituteFormula LNN
                                  (substituteFormula LNN
                                     (substituteFormula LNN
                                        (substituteFormula LNN
                                           (substituteFormula LNN betaFormula 1 (var (S (S (S (S n))))))
                                           2 (var (S (S (S n))))) (S (S (S n))) 
                                        (var (S (S n)))) 0 (var (S n))) (S (S (S (S n))))
                                  (var (S (S (S n))))).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaExch LNN); PRsolveFV A B n.
                           *** apply
                                iffTrans
                                 with
                                   (substituteFormula LNN
                                      (substituteFormula LNN
                                         (substituteFormula LNN
                                            (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) 2
                                            (var (S (S n)))) 0 (var (S n))) (S (S (S (S n))))
                                      (var (S (S (S n))))).
                               ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply (subFormulaTrans LNN). PRsolveFV A B n.
                               ++++ apply
                                     iffTrans
                                      with
                                        (substituteFormula LNN
                                           (substituteFormula LNN
                                              (substituteFormula LNN
                                                 (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) 2
                                                 (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))) 0
                                           (var (S n))).
                                    ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                         apply (subFormulaExch LNN); PRsolveFV A B n.
                                    ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                         apply
                                          iffTrans
                                           with
                                             (substituteFormula LNN
                                                (substituteFormula LNN
                                                   (substituteFormula LNN betaFormula 1 (var (S (S (S (S n))))))
                                                   (S (S (S (S n)))) (var (S (S (S n))))) 2 
                                                (var (S (S n)))).
                                         **** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                              apply (subFormulaExch LNN); PRsolveFV A B n.
                                         **** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                              apply (subFormulaTrans LNN). PRsolveFV A B n.
                ** apply
                    iffTrans
                     with
                       (substituteFormula LNN
                          (substituteFormula LNN
                             (substituteFormula LNN
                                (substituteFormula LNN
                                   (substituteFormula LNN B (S n) (natToTerm a0)) 
                                   (S (S (S n))) (var (S (S (S (S n)))))) 
                                (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n))))
                          (S (S (S (S n)))) (var (S (S (S n))))).
                   +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaExch LNN); PRsolveFV A B n.
                   +++ apply
                        iffTrans
                         with
                           (substituteFormula LNN
                              (substituteFormula LNN
                                 (substituteFormula LNN
                                    (substituteFormula LNN
                                       (substituteFormula LNN B (S n) (natToTerm a0)) 
                                       (S (S n)) (var (S n))) (S (S (S n))) 
                                    (var (S (S (S (S n)))))) (S (S (S n))) 
                                 (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))).
                       --- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaExch LNN); PRsolveFV A B n.
                       --- apply
                            iffTrans
                             with
                               (substituteFormula LNN
                                  (substituteFormula LNN
                                     (substituteFormula LNN
                                        (substituteFormula LNN B (S n) 
                                           (natToTerm a0)) 
                                        (S (S n)) (var (S n))) 
                                     (S (S (S n))) (var (S (S (S (S n))))))
                                  (S (S (S (S n)))) (var (S (S (S n))))).
                           *** repeat (apply (reduceSub LNN);
                                       [ apply closedNN |]). 
                               apply (subFormulaNil LNN); PRsolveFV A B n.
                           *** apply
                                iffTrans
                                 with
                                   (substituteFormula LNN
                                      (substituteFormula LNN 
                                         (substituteFormula LNN B (S n)
                                            (natToTerm a0))
                                         (S (S n)) (var (S n))) (S (S (S n)))
                                      (var (S (S (S n))))).
                               ++++ apply (subFormulaTrans LNN); 
                                      PRsolveFV A B n.
                               ++++ apply iffSym. 
                                    apply (subFormulaTrans LNN);
                                      PRsolveFV A B n.
                ** apply
                    iffTrans
                     with
                       (substituteFormula LNN
                          (substituteFormula LNN
                             (substituteFormula LNN
                                (substituteFormula LNN
                                   (substituteFormula LNN betaFormula 1
                                      (Succ (var (S (S (S (S n))))))) 2 
                                   (var (S (S (S n))))) (S (S n)) (var (S n))) 
                             (S (S (S n))) (var (S (S n)))) (S (S (S (S n))))
                          (var (S (S (S n))))).
                   +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN); PRsolveFV A B n.
                   +++ apply
                        iffTrans
                         with
                           (substituteFormula LNN
                              (substituteFormula LNN
                                 (substituteFormula LNN
                                    (substituteFormula LNN betaFormula 1
                                       (Succ (var (S (S (S (S n))))))) 2 (var (S (S (S n)))))
                                 (S (S (S n))) (var (S (S n)))) (S (S (S (S n))))
                              (var (S (S (S n))))).
                       --- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN); PRsolveFV A B n.
                       --- apply
                            iffTrans
                             with
                               (substituteFormula LNN
                                  (substituteFormula LNN
                                     (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S (S n)))))))
                                     2 (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                               apply (subFormulaTrans LNN); PRsolveFV A B n.
                           *** apply
                                iffTrans
                                 with
                                   (substituteFormula LNN
                                      (substituteFormula LNN
                                         (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S (S n)))))))
                                         (S (S (S (S n)))) (var (S (S (S n))))) 2 
                                      (var (S (S n)))).
                               ++++ apply (subFormulaExch LNN); PRsolveFV A B n.
                               ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply
                                     iffTrans
                                      with
                                        (substituteFormula LNN
                                           (substituteFormula LNN betaFormula (S (S (S (S n))))
                                              (var (S (S (S n))))) 1
                                           (substituteTerm LNN (Succ (var (S (S (S (S n)))))) 
                                              (S (S (S (S n)))) (var (S (S (S n)))))).
                                    ---- apply (subSubFormula LNN); PRsolveFV A B n.
                                    ---- replace
                                          (substituteTerm LNN (Succ (var (S (S (S (S n)))))) 
                                             (S (S (S (S n)))) (var (S (S (S n))))) with
                                          (Succ
                                             (substituteTerm LNN (var (S (S (S (S n))))) (S (S (S (S n))))
                                                (var (S (S (S n)))))).
                                         **** rewrite (subTermVar1 LNN).
                                              repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                              apply (subFormulaNil LNN); PRsolveFV A B n.
                                         **** reflexivity.
                **  apply
                    iffTrans
                     with
                       (substituteFormula LNN
                          (substituteFormula LNN
                             (substituteFormula LNN
                                (substituteFormula LNN A (S n) (natToTerm a0)) 
                                (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n))))
                          (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
                   +++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                       apply (subFormulaNil LNN); PRsolveFV A B n.
                   +++ apply
                        iffTrans
                         with
                           (substituteFormula LNN
                              (substituteFormula LNN (substituteFormula LNN A (S n) (natToTerm a0))
                                 (S (S (S n))) (var (S (S n)))) (S (S (S (S (S n)))))
                              (var (S (S (S (S n)))))).
                       --- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN); PRsolveFV A B n.
                       --- apply
                            iffTrans
                             with
                               (substituteFormula LNN (substituteFormula LNN A (S n) (natToTerm a0))
                                  (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN); PRsolveFV A B n.
                           *** apply iffTrans with (substituteFormula LNN A (S n) (natToTerm a0)).
                               ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply (subFormulaNil LNN); PRsolveFV A B n.
                               ++++ apply iffSym. apply (subFormulaNil LNN); PRsolveFV A B n.
                ** apply
                    iffTrans
                     with
                       (substituteFormula LNN
                          (substituteFormula LNN
                             (substituteFormula LNN
                                (substituteFormula LNN
                                   (substituteFormula LNN
                                      (substituteFormula LNN betaFormula 1 Zero) 2
                                      (var (S (S (S (S (S n))))))) (S n) 
                                   (natToTerm a0)) (S (S n)) (var (S n))) 
                             (S (S (S n))) (var (S (S n)))) (S (S (S (S (S n)))))
                          (var (S (S (S (S n)))))).
                   +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaTrans LNN); PRsolveFV A B n.
                   +++ apply
                        iffTrans
                         with
                           (substituteFormula LNN
                              (substituteFormula LNN
                                 (substituteFormula LNN
                                    (substituteFormula LNN
                                       (substituteFormula LNN betaFormula 1 Zero) 2
                                       (var (S (S (S (S (S n))))))) (S (S n)) 
                                    (var (S n))) (S (S (S n))) (var (S (S n))))
                              (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
                       --- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN); PRsolveFV A B n.
                           lia.
                       --- apply
                            iffTrans
                             with
                               (substituteFormula LNN
                                  (substituteFormula LNN
                                     (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2
                                        (var (S (S (S (S (S n))))))) (S (S (S n))) 
                                     (var (S (S n)))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                               apply (subFormulaNil LNN); PRsolveFV A B n.
                           *** apply
                                iffTrans
                                 with
                                   (substituteFormula LNN
                                      (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2
                                         (var (S (S (S (S (S n))))))) (S (S (S (S (S n)))))
                                      (var (S (S (S (S n)))))).
                               ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply (subFormulaNil LNN); PRsolveFV A B n.
                               ++++ apply
                                     iffTrans
                                      with
                                        (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2
                                           (var (S (S (S (S n)))))).
                                    ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                         apply (subFormulaTrans LNN); PRsolveFV A B n.
                                    ---- apply iffSym. apply (subFormulaTrans LNN); PRsolveFV A B n. congruence.
                ** apply
                    iffTrans
                     with
                       (substituteFormula LNN
                          (substituteFormula LNN
                             (substituteFormula LNN
                                (substituteFormula LNN
                                   (substituteFormula LNN
                                      (substituteFormula LNN
                                         (substituteFormula LNN
                                            (substituteFormula LNN
                                               (substituteFormula LNN betaFormula 1
                                                  (var (S (S (S (S n)))))) 2 
                                               (var (S (S (S n))))) (S (S (S n)))
                                            (var (S (S (S (S (S n))))))) 0 
                                         (var (S (S n)))) (S n) (natToTerm a0)) 
                                   (S (S n)) (var (S n))) (S (S (S n))) 
                                (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n)))))
                          (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
                   +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaExch LNN); PRsolveFV A B n.
                   +++ apply
                        iffTrans
                         with
                           (substituteFormula LNN
                              (substituteFormula LNN
                                 (substituteFormula LNN
                                    (substituteFormula LNN
                                       (substituteFormula LNN
                                          (substituteFormula LNN
                                             (substituteFormula LNN
                                                (substituteFormula LNN betaFormula 1
                                                   (var (S (S (S (S n)))))) 2
                                                (var (S (S (S (S (S n))))))) 0 
                                             (var (S (S n)))) (S n) (natToTerm a0)) 
                                       (S (S n)) (var (S n))) (S (S (S n))) 
                                    (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n)))))
                              (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
                       --- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaTrans LNN); PRsolveFV A B n.
                       --- apply
                            iffTrans
                             with
                               (substituteFormula LNN
                                  (substituteFormula LNN
                                     (substituteFormula LNN
                                        (substituteFormula LNN
                                           (substituteFormula LNN
                                              (substituteFormula LNN
                                                 (substituteFormula LNN betaFormula 1
                                                    (var (S (S (S (S n)))))) 2
                                                 (var (S (S (S (S (S n))))))) 0 
                                              (var (S (S n)))) (S (S n)) (var (S n))) 
                                        (S (S (S n))) (var (S (S n)))) (S (S (S (S n))))
                                     (var (S (S (S n))))) (S (S (S (S (S n))))) 
                                  (var (S (S (S (S n)))))).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                               apply (subFormulaNil LNN); PRsolveFV A B n. lia.
                           *** apply
                                iffTrans
                                 with
                                   (substituteFormula LNN
                                      (substituteFormula LNN
                                         (substituteFormula LNN
                                            (substituteFormula LNN
                                               (substituteFormula LNN
                                                  (substituteFormula LNN betaFormula 1
                                                     (var (S (S (S (S n)))))) 2 (var (S (S (S (S (S n)))))))
                                               0 (var (S n))) (S (S (S n))) (var (S (S n))))
                                         (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n)))))
                                      (var (S (S (S (S n)))))).
                               ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply (subFormulaTrans LNN); PRsolveFV A B n.
                               ++++ apply
                                     iffTrans
                                      with
                                        (substituteFormula LNN
                                           (substituteFormula LNN
                                              (substituteFormula LNN
                                                 (substituteFormula LNN
                                                    (substituteFormula LNN betaFormula 1 (var (S (S (S (S n))))))
                                                    2 (var (S (S (S (S (S n))))))) 0 (var (S n)))
                                              (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n)))))
                                           (var (S (S (S (S n)))))).
                                    ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                         apply (subFormulaNil LNN); PRsolveFV A B n.
                                    ---- apply
                                          iffTrans
                                           with
                                             (substituteFormula LNN
                                                (substituteFormula LNN
                                                   (substituteFormula LNN
                                                      (substituteFormula LNN
                                                         (substituteFormula LNN betaFormula 1 (var (S (S (S (S n))))))
                                                         2 (var (S (S (S (S (S n))))))) (S (S (S (S n))))
                                                      (var (S (S (S n))))) 0 (var (S n))) (S (S (S (S (S n)))))
                                                (var (S (S (S (S n)))))).
                                         **** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                              apply (subFormulaExch LNN); PRsolveFV A B n.
                                         **** apply
                                               iffTrans
                                                with
                                                  (substituteFormula LNN
                                                     (substituteFormula LNN
                                                        (substituteFormula LNN
                                                           (substituteFormula LNN
                                                              (substituteFormula LNN betaFormula 1 (var (S (S (S (S n))))))
                                                              (S (S (S (S n)))) (var (S (S (S n))))) 2
                                                           (var (S (S (S (S (S n))))))) 0 (var (S n)))
                                                     (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
                                              { repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                apply (subFormulaExch LNN); PRsolveFV A B n. }
                                              { apply
                                                 iffTrans
                                                  with
                                                    (substituteFormula LNN
                                                       (substituteFormula LNN
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN betaFormula 1 (var (S (S (S n))))) 2
                                                             (var (S (S (S (S (S n))))))) 0 (var (S n)))
                                                       (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
                                                + repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                  apply (subFormulaTrans LNN); PRsolveFV A B n.
                                                + apply
                                                   iffTrans
                                                    with
                                                      (substituteFormula LNN
                                                         (substituteFormula LNN
                                                            (substituteFormula LNN
                                                               (substituteFormula LNN betaFormula 1 (var (S (S (S n))))) 2
                                                               (var (S (S (S (S (S n))))))) (S (S (S (S (S n)))))
                                                            (var (S (S (S (S n)))))) 0 (var (S n))).
                                                  - repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaExch LNN); PRsolveFV A B n. lia.
                                                  - apply
                                                     iffTrans
                                                      with
                                                        (substituteFormula LNN
                                                           (substituteFormula LNN
                                                              (substituteFormula LNN betaFormula 1 (var (S (S (S n))))) 2
                                                              (var (S (S (S (S n)))))) 0 (var (S n))).
                                                    * repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                      apply (subFormulaTrans LNN); PRsolveFV A B n.
                                                    * apply iffSym.
                                                      apply
                                                       iffTrans
                                                        with
                                                          (substituteFormula LNN
                                                             (substituteFormula LNN
                                                                (substituteFormula LNN
                                                                   (substituteFormula LNN betaFormula 1 (var (S (S (S n))))) 2
                                                                   (var (S (S n)))) (S (S n)) (var (S (S (S (S n)))))) 0
                                                             (var (S n))).
                                                      ++ apply (subFormulaExch LNN); PRsolveFV A B n.
                                                      ++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                         apply (subFormulaTrans LNN); PRsolveFV A B n. congruence. }
                ** apply
                    iffTrans
                     with
                       (substituteFormula LNN
                          (substituteFormula LNN
                             (substituteFormula LNN
                                (substituteFormula LNN
                                   (substituteFormula LNN
                                      (substituteFormula LNN B (S (S (S n)))
                                         (var (S (S (S (S n)))))) (S n) 
                                      (natToTerm a0)) (S (S n)) (var (S n))) 
                                (S (S (S n))) (var (S (S n)))) (S (S (S (S n))))
                             (var (S (S (S n))))) (S (S (S (S (S n))))) 
                          (var (S (S (S (S n)))))).
                   +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN); PRsolveFV A B n.
                   +++ apply
                        iffTrans
                         with
                           (substituteFormula LNN
                              (substituteFormula LNN
                                 (substituteFormula LNN
                                    (substituteFormula LNN
                                       (substituteFormula LNN B (S (S (S n)))
                                          (var (S (S (S (S n)))))) (S n) (natToTerm a0)) 
                                    (S (S n)) (var (S n))) (S (S (S (S n)))) 
                                 (var (S (S (S n))))) (S (S (S (S (S n))))) 
                              (var (S (S (S (S n)))))).
                       --- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN); PRsolveFV A B n.
                       --- apply
                            iffTrans
                             with
                               (substituteFormula LNN
                                  (substituteFormula LNN
                                     (substituteFormula LNN
                                        (substituteFormula LNN
                                           (substituteFormula LNN B (S n) (natToTerm a0)) 
                                           (S (S (S n))) (var (S (S (S (S n)))))) 
                                        (S (S n)) (var (S n))) (S (S (S (S n)))) 
                                     (var (S (S (S n))))) (S (S (S (S (S n))))) 
                                  (var (S (S (S (S n)))))).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaExch LNN); PRsolveFV A B n.
                           *** apply
                                iffTrans
                                 with
                                   (substituteFormula LNN
                                      (substituteFormula LNN
                                         (substituteFormula LNN
                                            (substituteFormula LNN
                                               (substituteFormula LNN B (S n) (natToTerm a0)) 
                                               (S (S n)) (var (S n))) (S (S (S n))) 
                                            (var (S (S (S (S n)))))) (S (S (S (S n)))) 
                                         (var (S (S (S n))))) (S (S (S (S (S n))))) 
                                      (var (S (S (S (S n)))))).
                               ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply (subFormulaExch LNN); PRsolveFV A B n.
                               ++++ apply
                                     iffTrans
                                      with
                                        (substituteFormula LNN
                                           (substituteFormula LNN
                                              (substituteFormula LNN
                                                 (substituteFormula LNN B (S n) (natToTerm a0)) 
                                                 (S (S n)) (var (S n))) (S (S (S n))) (var (S (S (S n)))))
                                           (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
                                    ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                         apply (subFormulaTrans LNN); PRsolveFV A B n.
                                    ---- apply
                                          iffTrans
                                           with
                                             (substituteFormula LNN
                                                (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0))
                                                   (S (S n)) (var (S n))) (S (S (S n))) (var (S (S (S n))))).
                                         **** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                              apply (subFormulaNil LNN); PRsolveFV A B n. lia.
                                         **** apply iffSym.
                                              apply
                                               iffTrans
                                                with
                                                  (substituteFormula LNN
                                                     (substituteFormula LNN
                                                        (substituteFormula LNN
                                                           (substituteFormula LNN B (S n) (natToTerm a0)) 
                                                           (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) 
                                                     (S (S n)) (var (S (S (S n))))).
                                              { apply (subFormulaNil LNN); PRsolveFV A B n. }
                                              { apply (subFormulaTrans LNN); PRsolveFV A B n. }
                ** apply
                    iffTrans
                     with
                       (substituteFormula LNN
                          (substituteFormula LNN
                             (substituteFormula LNN
                                (substituteFormula LNN
                                   (substituteFormula LNN
                                      (substituteFormula LNN
                                         (substituteFormula LNN betaFormula 1
                                            (Succ (var (S (S (S (S n))))))) 2
                                         (var (S (S (S (S (S n))))))) 
                                      (S n) (natToTerm a0)) (S (S n)) 
                                   (var (S n))) (S (S (S n))) (var (S (S n)))) 
                             (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n)))))
                          (var (S (S (S (S n)))))).
                   +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaTrans LNN); PRsolveFV A B n.
                   +++ apply
                        iffTrans
                         with
                           (substituteFormula LNN
                              (substituteFormula LNN
                                 (substituteFormula LNN
                                    (substituteFormula LNN
                                       (substituteFormula LNN
                                          (substituteFormula LNN betaFormula 1
                                             (Succ (var (S (S (S (S n))))))) 2
                                          (var (S (S (S (S (S n))))))) (S (S n)) 
                                       (var (S n))) (S (S (S n))) (var (S (S n)))) 
                                 (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n)))))
                              (var (S (S (S (S n)))))).
                       --- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                           apply (subFormulaNil LNN); PRsolveFV A B n. lia.
                       --- apply
                            iffTrans
                             with
                               (substituteFormula LNN
                                  (substituteFormula LNN
                                     (substituteFormula LNN
                                        (substituteFormula LNN
                                           (substituteFormula LNN betaFormula 1
                                              (Succ (var (S (S (S (S n))))))) 2
                                           (var (S (S (S (S (S n))))))) (S (S (S n))) 
                                        (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n)))))
                                  (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                               apply (subFormulaNil LNN); PRsolveFV A B n.
                           *** apply
                                iffTrans
                                 with
                                   (substituteFormula LNN
                                      (substituteFormula LNN
                                         (substituteFormula LNN
                                            (substituteFormula LNN betaFormula 1
                                               (Succ (var (S (S (S (S n))))))) 2 (var (S (S (S (S (S n)))))))
                                         (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n)))))
                                      (var (S (S (S (S n)))))).
                               ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply (subFormulaNil LNN); PRsolveFV A B n.
                               ++++ apply
                                     iffTrans
                                      with
                                        (substituteFormula LNN
                                           (substituteFormula LNN
                                              (substituteFormula LNN
                                                 (substituteFormula LNN betaFormula 1
                                                    (Succ (var (S (S (S (S n))))))) (S (S (S (S n))))
                                                 (var (S (S (S n))))) 2 (var (S (S (S (S (S n)))))))
                                           (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
                                    ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                         apply (subFormulaExch LNN); PRsolveFV A B n.
                                    ---- apply
                                          iffTrans
                                           with
                                             (substituteFormula LNN
                                                (substituteFormula LNN
                                                   (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S (S n)))))))
                                                   (S (S (S (S n)))) (var (S (S (S n))))) 2 
                                                (var (S (S (S (S n)))))).
                                         **** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                              apply (subFormulaTrans LNN); PRsolveFV A B n.
                                         **** apply
                                               iffTrans
                                                with
                                                  (substituteFormula LNN
                                                     (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S n)))))) 2
                                                     (var (S (S (S (S n)))))).
                                              { repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                apply
                                                 iffTrans
                                                  with
                                                    (substituteFormula LNN
                                                       (substituteFormula LNN betaFormula (S (S (S (S n))))
                                                          (var (S (S (S n))))) 1
                                                       (substituteTerm LNN (Succ (var (S (S (S (S n)))))) 
                                                          (S (S (S (S n)))) (var (S (S (S n)))))).
                                                + apply (subSubFormula LNN); PRsolveFV A B n.
                                                + replace
                                                   (substituteTerm LNN (Succ (var (S (S (S (S n)))))) 
                                                      (S (S (S (S n)))) (var (S (S (S n))))) with
                                                   (Succ
                                                      (substituteTerm LNN (var (S (S (S (S n))))) (S (S (S (S n))))
                                                         (var (S (S (S n)))))).
                                                  - rewrite (subTermVar1 LNN).
                                                    repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaNil LNN); PRsolveFV A B n.
                                                  - reflexivity. }
                                              { apply iffSym. apply (subFormulaTrans LNN); PRsolveFV A B n. congruence. }
                ** apply
                    iffTrans
                     with
                       (substituteFormula LNN
                          (substituteFormula LNN
                             (substituteFormula LNN
                                (substituteFormula LNN betaFormula 2 (var (S (S (S n))))) 1
                                (var (S (S n)))) (S (S n)) (var (S n))) 
                          (S (S (S n))) (var (S (S n)))).
                   +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN); PRsolveFV A B n.
                   +++ apply
                        iffTrans
                         with
                           (substituteFormula LNN
                              (substituteFormula LNN
                                 (substituteFormula LNN betaFormula 2 (var (S (S (S n))))) 1
                                 (var (S n))) (S (S (S n))) (var (S (S n)))).
                       --- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                           apply (subFormulaTrans LNN); PRsolveFV A B n.
                       --- apply
                            iffTrans
                             with
                               (substituteFormula LNN
                                  (substituteFormula LNN
                                     (substituteFormula LNN betaFormula 2 (var (S (S (S n)))))
                                     (S (S (S n))) (var (S (S n)))) 1 (var (S n))).
                           *** apply (subFormulaExch LNN); PRsolveFV A B n.
                           *** repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
                               apply (subFormulaTrans LNN); PRsolveFV A B n.
        * apply H3. }
  intros n A g H0 B h H1. split.
  + destruct H0 as (H0, H2). destruct H1 as (H1, H3). intros v H4.
    assert (forall v : nat, In v (freeVarFormula LNN betaFormula) -> v <= 2).
    { eapply proj1. apply betaRepresentable. }
    assert (forall v : nat, v <> S (S n) -> v <= S (S n) -> v <= S n).
    { intros v0 H6 H7. 
      destruct (proj1 (Nat.lt_eq_cases v0 (S (S n))) H7) as [H8 | H8].
      + now apply Nat.lt_succ_r. 
      + elim H6; assumption. }
    unfold primRecSigmaFormula, minimize, existH in H4;
     repeat
      match goal with
      | H1:(?X1 = ?X2),H2:(?X1 <> ?X2) |- _ =>
          elim H2; apply H1
      | H1:(?X1 = ?X2),H2:(?X2 <> ?X1) |- _ =>
          elim H2; symmetry  in |- *; apply H1
      | H:(v = ?X1) |- _ => rewrite H; clear H
      | H:(?X1 = v) |- _ =>
          rewrite <- H; clear H
      | H:(In ?X3 (freeVarFormula LNN (existH ?X1 ?X2))) |- _ =>
          assert (In X3 (List.remove  eq_nat_dec X1 (freeVarFormula LNN X2)));
           [ apply H | clear H ]
      | H:(In ?X3 (freeVarFormula LNN (forallH ?X1 ?X2))) |- _ =>
          assert (In X3 (List.remove  eq_nat_dec X1 (freeVarFormula LNN X2)));
           [ apply H | clear H ]
      | H:(In ?X3 (List.remove eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _
      =>
          assert (In X3 (freeVarFormula LNN X2));
           [ eapply In_list_remove1; apply H
           | assert (X3 <> X1); [ eapply In_list_remove2; apply H | clear H ] ]
      | H:(In ?X3 (freeVarFormula LNN (andH ?X1 ?X2))) |- _ =>
          assert (In X3 (freeVarFormula LNN X1 ++ freeVarFormula LNN X2));
           [ apply H | clear H ]
      | H:(In ?X3 (freeVarFormula LNN (impH ?X1 ?X2))) |- _ =>
          assert (In X3 (freeVarFormula LNN X1 ++ freeVarFormula LNN X2));
           [ apply H | clear H ]
      | H:(In ?X3 (freeVarFormula LNN (notH ?X1))) |- _ =>
          assert (In X3 (freeVarFormula LNN X1)); [ apply H | clear H ]
      | H:(In _ (freeVarFormula LNN (primRecSigmaFormulaHelp _ _ _))) |- _ =>
          decompose sum (freeVarPrimRecSigmaFormulaHelp1 _ _ _ _ H); clear H
      | H:(In _ (freeVarFormula LNN (primRecPiFormulaHelp _ _ _))) |- _ =>
      decompose sum (freeVarPrimRecPiFormulaHelp1 _ _ _ _ H); clear H
      | H:(In ?X3 (freeVarFormula LNN A)) |- _ =>
          apply Nat.le_trans with n; [ apply H0; apply H | apply Nat.le_succ_diag_r ]
      | H:(In ?X3 (freeVarFormula LNN B)) |- _ =>
          apply H6; [ clear H | apply H1; apply H ]
      | H:(In _ (_ ++ _)) |- _ =>
          induction (in_app_or _ _ _ H); clear H
      | H:(In _ (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _ =>
          induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
      | H:(In _ (freeVarFormula LNN (LT ?X1 ?X2))) |- _ =>
          rewrite freeVarLT in H
      | H:(In _ (freeVarTerm LNN (natToTerm _))) |- _ =>
          elim (closedNatToTerm _ _ H)
      | H:(In _ (freeVarTerm LNN Zero)) |- _ =>
          elim H
      | H:(In _ (freeVarTerm LNN (Succ _))) |- _ =>
          rewrite freeVarSucc in H
      | H:(In _ (freeVarTerm LNN (var _))) |- _ =>
          simpl in H; decompose sum H; clear H
      | H:(In _ (freeVarTerm LNN (var  _))) |- _ =>
          simpl in H; decompose sum H; clear H
      end; try first [ assumption | apply le_n ].
      assert (v <= 2) by auto. lia.
  + apply H; auto.
Qed.
(* end *)

Fixpoint primRecFormula (n : nat) (f : PrimRec n) {struct f} : Formula :=
  match f with
  | succFunc => succFormula
  | zeroFunc => zeroFormula
  | projFunc n m _ => projFormula m
  | composeFunc n m g h =>
      composeSigmaFormula n n m (primRecsFormula n m g) (primRecFormula m h)
  | primRecFunc n g h =>
      primRecSigmaFormula n (primRecFormula n g) (primRecFormula (S (S n)) h)
  end
 
 with primRecsFormula (n m : nat) (fs : PrimRecs n m) {struct fs} :
 Vector.t (Formula * naryFunc n) m :=
  match fs in (PrimRecs n m) return (Vector.t (Formula * naryFunc n) m) with
  | PRnil n => Vector.nil _
  | PRcons n m f fs' =>
      Vector.cons (Formula * naryFunc n) (primRecFormula n f, evalPrimRec n f) m
        (primRecsFormula n m fs')
  end.

Lemma primRecRepresentable1 :
 forall (n : nat) (f : PrimRec n),
 Representable n (evalPrimRec n f) (primRecFormula n f).
Proof.
  intros n f.
  elim f using
   PrimRec_PrimRecs_ind
    with
      (P0 := fun (n m : nat) (fs : PrimRecs n m) =>
             RepresentablesHelp n m (primRecsFormula n m fs) /\
             extEqualVector _ _ (FormulasToFuncs n m (primRecsFormula n m fs))
               (evalPrimRecs n m fs) /\
             Vector.t_rect (Formula * naryFunc n) (fun _ _ => Prop) True
               (fun (pair : Formula * naryFunc n) (m : nat) 
                  (v : Vector.t _ m) (rec : Prop) =>
                (forall v : nat, In v (freeVarFormula LNN (fst pair)) -> v <= n) /\
                rec) m (primRecsFormula n m fs)).
  + apply succRepresentable.
  + apply zeroRepresentable.
  + intros n0 m l. simpl in |- *. apply projRepresentable.
  + simpl in |- *; intros n0 m g H h H0. decompose record H.
    assert
     (Representable n0
        (evalComposeFunc n0 m (FormulasToFuncs n0 m (primRecsFormula n0 m g))
           (evalPrimRec m h))
        (composeSigmaFormula n0 n0 m (primRecsFormula n0 m g)
           (primRecFormula m h))).
    { apply composeSigmaRepresentable; auto. }
    induction H2 as (H2, H5). split.
    - assumption.
    - apply
       Representable_ext
        with
          (evalComposeFunc n0 m (FormulasToFuncs n0 m (primRecsFormula n0 m g))
             (evalPrimRec m h)).
      * apply extEqualCompose.
        ++ assumption.
        ++ apply extEqualRefl.
      * assumption.
  + simpl in |- *. intros n0 g H h H0.
    apply primRecSigmaRepresentable; auto.
  + simpl in |- *. tauto.
  + simpl in |- *; intros n0 m p H p0 H0.
    decompose record H0. clear H0.
    repeat split; auto.
    - induction H as (H, H0); auto.
    - apply extEqualRefl.
    - induction H as (H, H0); auto.
Qed.

Lemma primRecRepresentable :
 forall (n : nat) (f : naryFunc n) (p : isPR n f),
 Representable n f (primRecFormula n (proj1_sig p)).
Proof.
  intros n f p.
  assert
   (Representable n (evalPrimRec n (proj1_sig p))
      (primRecFormula n (proj1_sig p))).
  { apply primRecRepresentable1. }
  induction H as (H, H0). split.
  + assumption.
  + destruct p as (x, p).
    eapply Representable_ext with (evalPrimRec n x); assumption.
Qed.

End Primitive_Recursive_Representable.
