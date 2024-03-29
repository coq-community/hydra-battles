(** 
    Original version by Russel O'Connor 

    This library is dedicated to the proof of the theorem:
    "Every primitive recursive function is representable in [NN]"

    - Let  [f] be any [n]-ary arithmetic function, and [p] a proof that this function is primitive recursive.
      Out of [p], we can associate a [NN]-formula which correctly expresses [f].

    - The main difficulty is to associate a [NN]-formula to the case where [f] can be defined by a primitive 
        recursive scheme. 
        This is made possible with the help of Goedel's [beta]-function, studied in the 
         #<a=href="https://github.com/thery/coqprime/blob/master/src/Coqprime/N/ChineseRem.v">ChineseRem</a>#%\href{https://github.com/thery/coqprime/blob/master/src/Coqprime/N/ChineseRem.v}{ChineseRem}%
        library. This function allows 
         to represent a sequence of computation steps through a first-order formula (theorem [ChineseRem.BetaTheorem]).

 *)

(* begin hide *)
From Coq Require Import Arith.
From hydras.Ackermann Require Import extEqualNat subAll folProp subProp folReplace
  folLogic3 NN NNtheory primRec  expressible.
From Coqprime Require Import ChineseRem.
From Coq Require Import  Vector List Lia.
From hydras Require Import ListExt cPair MoreDecidable.
From hydras Require Import Compat815 ssrnat_extracts.
From LibHyps Require Export LibHyps.
From hydras Require Export MoreLibHyps NewNotations.
Import NNnotations. 
#[local] Arguments apply _ _ _ : clear implicits.
Import LispAbbreviations. 
From Coq Require Import Utf8.

Coercion natToTerm : nat >-> Term.

(** * Goedel's beta function *)

#[global] Notation rem a b Hposb :=
  (snd (proj1_sig (div_eucl b Hposb a))).

Definition beta (a z : nat) : nat :=
  rem (cdr a) (coPrimeBeta z (car a)) (gtBeta z (car a)).

Notation β := beta.

(** From CoqPrime.ChineseRem 

coPrimeBeta = fun z c : nat => S (c * S z)
     : nat -> nat -> nat

gtBeta : forall z c : nat, coPrimeBeta z c > 0
*)

(* ** Usual Definition (cf Wikipedia's page) 
      Will be replaced with [ChineseRem.beta] in future releases.

*)

Module Usual.
  Definition beta x y z := rem x  (y * z.+1).+1  (gtBeta _ _).
  Notation β:= beta.
End Usual. 


(** Paraphrase lemmas *)

Lemma beta_def x y z :  β (cPair x y) z = 
                          rem y (S (x * S z)) (gtBeta _ _).
Proof.
  unfold beta. now rewrite !cPairProjections2, !cPairProjections1.
Qed.


Lemma betaEquiv:  
  forall x y z,  β (cPair x y) z = Usual.β y x z.
Proof. 
  intros x y z; now rewrite beta_def. 
Qed. 


(** Variations on  CoqPrime's [BetaTheorem1]  *)

Lemma betaThm2 n (y : nat -> nat) :
  {a : nat * nat |
      forall z, z < n -> y z = β (cPair (fst a) (snd a)) z}.
Proof. 
  destruct (betaTheorem1 n y) as [x e]; exists (snd x, fst x). 
  intros; unfold beta; 
    rewrite !cPairProjections2, !cPairProjections1; simpl; 
    now apply e. 
Qed. 

Lemma betaThm3 n (y : nat -> nat) :
  {a : nat |
      forall z, z < n -> y z = β (cPair (car a) (cdr a)) z}.
Proof.  
  destruct (betaThm2 n y) as [x e]; exists (cPair (fst x) (snd x)).
  intros; rewrite !cPairProjections2, !cPairProjections1; auto.
Qed.

Lemma betaThm4 n (y : nat -> nat) :
  {a : nat |
      forall z, z < n -> y z = Usual.β (cdr a) (car a) z}.
Proof.
 destruct (betaThm3 n y) as [x e]; exists x; intros z Hz.
 intros ; rewrite <- betaEquiv; now apply e. 
Qed. 

Lemma betaThm5 :
  forall (n : nat) (y : nat -> nat),
    {a : nat * nat
    | forall z : nat, z < n -> y z = Usual.β (fst a) (snd a) z }.
Proof. 
  intros n y; destruct (betaTheorem1 n y) as [x e]. 
  unfold Usual.β; now exists x. 
Qed. 

(** NN formula associated with [beta] *)

Definition betaFormula : Formula :=
(exH 3,
  v#3 < Succ v#2 /\
   exH 4,
     (v#4 < Succ v#2 /\
      (v#3 + v#4) * Succ (v#3 + v#4) + 2 * v#3 =
      n2t 2 * v#2 /\
      v#0 < Succ (v#3 * Succ v#1) /\
      exH 5, (v#5 < Succ v#4 /\ 
                v#0 +  v#5 * Succ (v#3 * Succ v#1) = v#4))
)%fol.

Notation βR := betaFormula. 

Section Primitive_Recursive_Representable.

Definition Representable := Representable NN.
Definition RepresentableAlternate := RepresentableAlternate NN closedNN1.
Definition RepresentableHelp := RepresentableHelp NN.
Definition Representable_ext := Representable_ext NN.

Lemma betaRepresentable : Representable 2 β βR.
Proof.
  split.
 - intros v H. simpl in H. lia.
 - simpl; intros a a0; unfold βR. 
   assert
      (H: forall (A : Formula) (v x a : nat),
       v <> x ->
       substF (existH v A) x (n2t a) =
       existH v (substF A x (n2t a))).
   { intros A v x a1 H; rewrite (substExHC _ A v x _ H ); 
       trivial; apply closedNatToTerm.  
   }
    assert
      (H0: forall (t1 t2 : Term) (v a : nat),
       substF (t1 < t2)%fol v (n2t a) =
       (substT t1 v (n2t a) < substT t2 v (n2t a))%fol).
   { intros ? ? ? ?; unfold LT at 1;  now rewrite (subFormulaRelation LNN). }
    repeat first
    [ rewrite H; [| discriminate ]
    | rewrite H0
    | rewrite (subFormulaAnd LNN)
    | rewrite (subFormulaEqual LNN) ].
    simpl in |- *; repeat rewrite (subTermNil LNN).
   + assert (H1: SysPrf NN
                   ((exH 3,
                      v#3 < n2t a.+1 /\
                        (exH 4,
                          v#4 < n2t a.+1 /\
                            (v#3 + v#4) * S_ (v#3 + v#4) + n2t 2 * v#3 = n2t 2 * n2t a /\
                            v#0 < S_ (v#3 * S_ (n2t a0)) /\
                            (exH 5, v#5 < S_ v#4 /\
                                      v#0 + v#5 * S_ (v#3 * S_ (n2t a0)) = v#4)))
                    <->
                      v#0 = n2t (β a a0))%fol); auto.
     apply iffI.
   * apply impI. apply existSys.
     -- apply closedNN.
     -- intros [H1 | H1]; try lia. 
        simpl in H1; elim (closedNatToTerm _ _ H1).
     -- apply impE with (v#3 < n2t (S a))%fol.
     ++ apply impE with
        (exH 4, v#4 < n2t a.+1 
                /\
                (v#3 + v#4) * Succ (v#3 + v#4) + 
                    n2t 2 * v#3 = n2t 2 * n2t a 
                /\
                  v#0 < Succ (v#3 * Succ (n2t a0)) 
                /\
                  (exH 5, v#5 < Succ v#4 /\ 
                            v#0 + v#5 * Succ (v#3 * Succ (n2t a0)) 
                            = v#4))%fol.
 
        ** apply sysWeaken. apply impI. apply existSys.
           --- apply closedNN.
           --- replace
               (freeVarF 
                  (v#3 < n2t (a.+1) ->  v#0 = (n2t (β a a0)))%fol)
               with
               ((freeVarT (L:=LNN) (var 3) ++ 
                   freeVarT (n2t a.+1)) ++
                  freeVarF (v#0 = n2t (β a a0))%fol)
               by (rewrite <- freeVarLT; reflexivity).
               intros [H1 | H1]; try lia.
               destruct (in_app_or _ _ _ H1) as [H2 | H2].
           +++ elim (closedNatToTerm _ _ H2).
           +++ destruct H2 as [H2| H2]; try lia. 
               elim (closedNatToTerm _ _ H2).
           --- apply impTrans with
                      (andH (equal (var 3) (n2t (car a)))
                         (equal (var 4) (n2t (cdr a)))).
           +++ apply impI.
               apply impE with
                 (equal
                    (Plus (Times (Plus (var 3) (var 4)) 
                             (Succ (Plus (var 3) (var 4))))
                       (Times (n2t 2) (var 3)))
                    (Times (n2t 2) (n2t a))).
               *** apply impE with (v#4 < n2t (S a))%fol. 
                   ---- apply impE with (v#3 < n2t (S a))%fol.
                   ++++ do 2 apply sysWeaken.
                        apply boundedLT; intros n H1.
                        rewrite (subFormulaImp LNN).
                        unfold LT at 1 in |- *.
                        rewrite (subFormulaRelation LNN).
                        simpl in |- *.
                        rewrite subTermNil.
                        **** 
                             replace 
                               (apply LNN Languages.Succ_ 
                                  (Tcons (n2t a)
                                     (Tnil)))
                               with (n2t (S a)); 
                               [| reflexivity ].
                             fold (LT (var 4) (n2t (S a))). 
                             apply boundedLT. intros n0 H2.
                             repeat rewrite (subFormulaImp LNN).
                             repeat rewrite (subFormulaAnd LNN).
                             repeat rewrite (subFormulaEqual LNN).
                             assert 
                               (H3: (substT 
                                   (substT 
                                      (Plus (Times (v#3 + v#4)%fol 
                                               (Succ (Plus (var 3) (var 4))))
                                         (Times (Succ (Succ Zero)) (var 3))) 
                                      3 (n2t n)) 4
                                   (n2t n0)) =
                                  (Plus
                                     (Times (Plus (n2t n) (n2t n0))
                                        (Succ (n2t n + n2t n0))%fol)
                                     (Times (Succ (Succ Zero))
                                        (n2t n)))) .
                             { simpl in |- *.
                               repeat (rewrite (subTermNil LNN (n2t n)));
                                 [| apply closedNatToTerm].
                               reflexivity. }
                             rewrite H3; clear H3.
                             assert
                               (H3: (substT
                                   (substT 
                                      (Times (Succ (Succ Zero)) (n2t a)) 
                                      3  (n2t n)) 4 (n2t n0)) =
                                  (Times (n2t 2) (n2t a))).
                             { simpl in |- *;
                               repeat (rewrite (subTermNil _ (n2t a)); 
                                       [| apply closedNatToTerm ]).
                               reflexivity. }
                             simpl in |- *.
                             assert
                               (forall (a b : nat) (s : Term),
                                   substT (n2t a) b s =
                                     n2t a).
                             { intros; apply (subTermNil LNN).
                               apply closedNatToTerm. }
                             repeat rewrite H4.
                             apply impTrans with 
                               (equal 
                                (n2t ((n + n0) * S (n + n0) + 2 * n)) 
                                (n2t (2 * a))).
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
                                   replace (S_ (S_ (apply LNN Zero_ Tnil)))%fol 
                                    
                                     with (n2t 2) by reflexivity.
                                   apply natTimes. }
                             { rewrite cPairLemma1.
                               destruct (eq_nat_dec a (cPair n n0)) as [e | e].
                               - rewrite e, cPairProjections1, 
                                   cPairProjections2.
                                               apply impI. 
                                               apply andI; apply eqRefl.
                               - apply impI.
                                 apply contradiction with
                                   (equal (n2t (2 * cPair n n0)) 
                                      (n2t (2 * a))).
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
                                              (Succ (n2t a0))))))
                                     (var 4)))).
               *** apply impE with (LT (var 0) 
                                             (Succ (Times (var 3)
                                                      (Succ (n2t a0))))).
                   ---- rewrite <-
                                  (subFormulaId LNN
                                     (impH (LT (var 0) 
                                              (Succ (Times (var 3) 
                                                       (Succ (n2t a0)))))
                                      (impH
                                       (existH 5
                                        (andH (LT (var 5) (Succ (var 4)))
                                         (equal
                                          (Plus (var 0)
                                            (Times (var 5)
                                             (Succ (Times (var 3)
                                               (Succ (n2t a0))))))
                                          (var 4))))
                                       (equal (var 0) 
                                          (n2t (β a a0))))) 3).
                                 apply impE with
                                  (substF 
                                   (impH (LT (var 0) 
                                            (Succ (Times (var 3) 
                                                     (Succ (n2t a0)))))
                                     (impH
                                       (existH 5
                                        (andH (LT (var 5) (Succ (var 4)))
                                          (equal
                                           (Plus (var 0)
                                             (Times (var 5)
                                               (Succ (Times (var 3)
                                                        (Succ 
                                                           (n2t a0))))))
                                           (var 4)))) 
                                       (equal (var 0) 
                                          (n2t (β a a0))))) 3
                                    (n2t (car a))).
                                 ++++ apply (subWithEquals LNN). apply eqSym. eapply andE1.
                                      apply Axm; right; constructor.
                                 ++++ rewrite <-
                                       (subFormulaId LNN
                                          (substF 
                                             (impH (LT (var 0) (Succ (Times (var 3) (Succ (n2t a0)))))
                                                (impH
                                                   (existH 5
                                                      (andH (LT (var 5) (Succ (var 4)))
                                                         (equal
                                                            (Plus (var 0)
                                                               (Times (var 5)
                                                                  (Succ (Times (var 3) (Succ (n2t a0))))))
                                                            (var 4)))) (equal (var 0) (n2t (β a a0))))) 3
                                             (n2t (car a))) 4).
                                      apply
                                       impE
                                        with
                                          (substF 
                                             (substF 
                                                (impH (LT (var 0) (Succ (Times (var 3) (Succ (n2t a0)))))
                                                   (impH
                                                      (existH 5
                                                         (andH (LT (var 5) (Succ (var 4)))
                                                            (equal
                                                               (Plus (var 0)
                                                                  (Times (var 5)
                                                                     (Succ (Times (var 3) (Succ (n2t a0))))))
                                                               (var 4)))) (equal (var 0) (n2t (β a a0)))))
                                                3 (n2t (car a))) 4 (n2t (cdr a))).
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
                                            repeat (rewrite (subTermNil LNN (n2t a0)); [| apply closedNatToTerm ]).
                                            repeat (rewrite (subTermNil LNN (n2t (β a a0))); [| apply closedNatToTerm ]).
                                            apply impTrans with (LT (var 0) (n2t (S (car a * S a0)))).
                                            { apply impI.
                                              apply
                                               impE
                                                with
                                                 (substF (LT (var 0) (var 1)) 1
                                                  (n2t (S (car a * S a0)))).
                                              - unfold LT at 2 in |- *.
                                                rewrite (subFormulaRelation LNN).
                                                apply impRefl.
                                              - apply
                                                  impE
                                                    with
                                                     (substF (v#0 < v#1)%fol 1
                                                      (Succ (Times (n2t (car a)) (Succ (n2t a0))))).
                                                + apply (subWithEquals LNN). apply sysWeaken. simpl.
                                                  apply eqSucc.
                                                  change (Succ (n2t a0)) with (n2t a0.+1).
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
                                                       (apply LNN Languages.Plus_
                                                          (Tcons (n2t n)
                                                             (Tcons                                                                 (apply LNN Languages.Times_
                                                                   (Tcons (var  5)
                                                                      (Tcons 
                                                                         (apply LNN Languages.Succ_
                                                                            (Tcons 
                                                                               (apply LNN Languages.Times_
                                                                                  (Tcons  (n2t (car a))
                                                                                     (Tcons 
                                                                                        (apply LNN Languages.Succ_
                                                                                           (Tcons  
                                                                                              (n2t a0) 
                                                                                              (Tnil))) 
                                                                                        (Tnil)))) 
                                                                               (Tnil ))) (Tnil)))) 
                                                                (Tnil )))) (n2t (cdr a))).
                                                + apply impE with (LT (var 5) (n2t (S (cdr a)))).
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
                                                    apply impI. destruct (eq_nat_dec n (β a a0)) as [e | e].
                                                    -- rewrite <- e. apply eqRefl.
                                                    -- apply
                                                        contradiction
                                                         with
                                                           (equal (n2t (n + n0 * S (car a * S a0)))
                                                              (n2t (cdr a))).
                                                       ++ eapply eqTrans; [| apply Axm; right; constructor ].
                                                          apply sysWeaken. eapply eqTrans.
                                                          ** apply eqSym. apply natPlus.
                                                          ** replace
                                                              (apply LNN Languages.Plus_
                                                                 (Tcons  (n2t n)
                                                                    (Tcons 
                                                                       (apply LNN Languages.Times_
                                                                          (Tcons  (n2t n0)
                                                                             (Tcons 
                                                                                (apply LNN Languages.Succ_
                                                                                   (Tcons 
                                                                                      (apply LNN Languages.Times_
                                                                                         (Tcons  (n2t (car a))
                                                                                            (Tcons 
                                                                                               (apply LNN Languages.Succ_
                                                                                                  (Tcons (n2t a0) (Tnil)))
                                                                                               (Tnil )))) (Tnil ))) 
                                                                                (Tnil )))) (Tnil )))) with
                                                              (Plus (n2t n)
                                                                 (Times (n2t n0)
                                                                    (Succ (Times (n2t (car a)) (Succ (n2t a0))))))
                                                              by reflexivity.
                                                              apply eqPlus.
                                                              --- apply eqRefl.
                                                              --- eapply eqTrans.
                                                                  +++ apply eqSym. apply natTimes.
                                                                  +++ apply eqTimes. apply eqRefl.
                                                                      simpl in |- *. apply eqSucc.
                                                                      replace (Succ (n2t a0)) 
                                                                        with (n2t (S a0)) by reflexivity.
                                                                      apply eqSym. apply natTimes.
                                                       ++ apply sysWeaken. apply natNE.
                                                          intro; elim e. unfold beta in |- *.
                                                          destruct
                                                            (div_eucl (coPrimeBeta a0 (car a)) (gtBeta a0 (car a)) (cdr a)) as [[a1 b0] H4].
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
        destruct (div_eucl (coPrimeBeta a0 (car a)) (gtBeta a0 (car a)) (cdr a)) as [x H1].
        induction x as (a1, b). simpl in |- *. simpl in H1. destruct H1 as (H1, H2).
        apply existI with (n2t (car a)). rewrite (subFormulaAnd LNN). apply andI.
        -- apply sysWeaken. rewrite H0. simpl in |- *. rewrite subTermNil.
           ++ replace (apply LNN Languages.Succ_ (Tcons (n2t a) (Tnil ))) with (n2t (S a)) by reflexivity.
              apply natLT. apply Nat.lt_succ_r. apply Nat.le_trans with (cPair (car a) (cdr a)).
              apply cPairLe1. rewrite cPairProjections. apply le_n.
           ++ apply closedNatToTerm.
        -- rewrite H; try lia.
           ++ apply existI with (n2t (cdr a)). repeat rewrite (subFormulaAnd LNN). apply andI.
              ** apply sysWeaken. repeat rewrite H0. simpl in |- *.
                 repeat rewrite (subTermNil LNN (n2t a)).
                 --- replace (apply LNN Languages.Succ_ (Tcons (n2t a) (Tnil ))) with (n2t (S a))
                       by reflexivity.
                     apply natLT. apply Nat.lt_succ_r. apply Nat.le_trans with (cPair (car a) (cdr a)).
                     +++ apply cPairLe2.
                     +++ rewrite cPairProjections. apply le_n.
                 --- apply closedNatToTerm.
                 --- apply closedNatToTerm.
              ** apply andI.
                 --- repeat rewrite (subFormulaEqual LNN). simpl in |- *.
                     repeat
                      (rewrite (subTermNil LNN (n2t (car a)));
                        [| apply closedNatToTerm ]).
                     repeat
                      (rewrite (subTermNil LNN (n2t a)); [| apply closedNatToTerm ]).
                     replace
                      (equal 
                         (apply LNN Languages.Plus_
                            (Tcons
                               (apply LNN Languages.Times_
                                  (Tcons
                                     (apply LNN Languages.Plus_
                                        (Tcons (n2t (car a))
                                           (Tcons (n2t (cdr a)) (Tnil ))))
                                     (Tcons
                                        (apply LNN Languages.Succ_
                                           (Tcons
                                              (apply LNN Languages.Plus_
                                                 (Tcons (n2t (car a))
                                                    (Tcons (n2t (cdr a))
                                                       (Tnil )))) (Tnil )))
                                        (Tnil))))
                               (Tcons
                                  (apply LNN Languages.Times_
                                     (Tcons
                                        (apply LNN Languages.Succ_
                                           (Tcons
                                              (apply LNN Languages.Succ_
                                                 (Tcons
                                                    (apply LNN 
                                                       Languages.Zero_ (Tnil ))
                                                    (Tnil ))) (Tnil )))
                                        (Tcons (n2t (car a)) (Tnil ))))
                                  (Tnil ))))
                         (apply LNN Languages.Times_
                            (Tcons
                               (apply LNN Languages.Succ_
                                  (Tcons
                                     (apply LNN Languages.Succ_
                                        (Tcons (apply LNN Languages.Zero_ (Tnil ))
                                           (Tnil ))) (Tnil )))
                               (Tcons (n2t a) (Tnil ))))) with
                      (equal
                         (Plus
                            (Times (Plus (n2t (car a)) (n2t (cdr a)))
                               (Succ (Plus (n2t (car a)) (n2t (cdr a)))))
                            (Times (n2t 2) (n2t (car a))))
                         (Times (n2t 2) (n2t a))) by reflexivity.
                     apply
                      eqTrans
                       with
                         (n2t
                            ((car a + cdr a) * S (car a + cdr a) +
                             2 * car a)).
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
                             (substF 
                                (substF 
                                   (LT (var 0) (S_ (Times (var 3) (S_ (n2t a0))))) 3
                                   (n2t (car a))) 4 (n2t (cdr a))) 0).
                         apply
                          impE
                           with
                             (substF 
                                (substF 
                                   (substF 
                                      (LT (var 0) (Succ (Times (var 3) (Succ (n2t a0))))) 3
                                      (n2t (car a))) 4 (n2t (cdr a))) 0
                                (n2t b)).
                         *** apply (subWithEquals LNN). apply eqSym. apply Axm; right; constructor.
                         *** apply sysWeaken. repeat rewrite H0. simpl in |- *.
                             repeat
                              (rewrite (subTermNil LNN (n2t (car a)));
                                [| apply closedNatToTerm ]).
                             repeat
                              (rewrite (subTermNil LNN (n2t a0)); [| apply closedNatToTerm ]).
                             apply
                              impE
                               with
                                 (substF (LT (n2t b) (var 0)) 0
                                    (Succ (Times (n2t (car a)) (Succ (n2t a0))))).
                             ---- unfold LT at 1 in |- *. rewrite (subFormulaRelation LNN).
                                  simpl in |- *.
                                  repeat
                                   (rewrite (subTermNil LNN (n2t b)); [| apply closedNatToTerm ]).
                                  apply impRefl.
                             ---- apply
                                   impE
                                    with
                                      (substF (LT (n2t b) (var 0)) 0
                                         (n2t (S (car a * S a0)))).
                                  ++++ apply (subWithEquals LNN). simpl in |- *. apply eqSucc.
                                       replace (Succ (n2t a0)) with (n2t (S a0)) by reflexivity.
                                       apply eqSym. apply natTimes.
                                  ++++ rewrite H0.
                                       repeat (rewrite (subTermNil LNN (n2t b)); [| apply closedNatToTerm ]).
                                       rewrite (subTermVar1 LNN). apply natLT. apply H2.
                     +++ repeat (rewrite H; [| discriminate ]).
                         apply existI with (n2t a1).
                         rewrite <-
                          (subFormulaId LNN
                             (substF3 
                                (v#5 < S_ v#4 /\ v#0 + v#5 * S_ (v#3 * S_ (n2t a0)) = v#4)%fol
                                3 (n2t (car a))
                                4 (n2t (cdr a))
                                5 (n2t a1))
                             0).
                         apply
                          impE
                           with
                             (substF4 
                                (andH (LT (var 5) (S_ (var 4)))
                                   (equal
                                      (Plus (var 0)
                                         (Times (var 5)
                                            (S_ (Times (var 3) (S_ (n2t a0))))))
                                      (var 4)))
                                         3 (n2t (car a))
                                      4 (n2t (cdr a))
                                   5 (n2t a1)
                                0 (n2t b)).
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
                              (rewrite (subTermNil LNN (n2t (car a)));
                                [| apply closedNatToTerm ]).
                             repeat
                              (rewrite (subTermNil LNN (n2t a0)); [| apply closedNatToTerm ]).
                             repeat
                              (rewrite (subTermNil LNN (n2t (cdr a)));
                                [| apply closedNatToTerm ]).
                             repeat
                              (rewrite (subTermNil LNN (n2t a1)); [| apply closedNatToTerm ]).
                             apply andI.
                             ---- replace  (S_ (n2t (cdr a)))%fol
                                    with (n2t (S (cdr a))) by reflexivity.
                                  apply natLT. unfold coPrimeBeta in *. lia.
                             ---- replace
                                   (apply LNN Languages.Plus_
                                      (Tcons (n2t b)
                                         (Tcons
                                            (apply LNN Languages.Times_
                                               (Tcons (n2t a1)
                                                  (Tcons
                                                     (apply LNN Languages.Succ_
                                                        (Tcons
                                                           (apply LNN Languages.Times_
                                                              (Tcons (n2t (car a))
                                                                 (Tcons
                                                                    (apply LNN Languages.Succ_
                                                                       (Tcons (n2t a0) (Tnil )))
                                                                    (Tnil )))) (Tnil ))) 
                                                     (Tnil )))) (Tnil )))) with
                                   (Plus (n2t b)
                                      (Times (n2t a1)
                                         (Succ (Times (n2t (car a)) (Succ (n2t a0)))))) by reflexivity.
                                  apply eqTrans with (n2t (a1 * coPrimeBeta a0 (car a) + b)).
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
                                                              replace (Succ (n2t a0)) with (n2t (S a0)) by reflexivity.
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
 In v (freeVarF  (addExists m n A)) -> In v (freeVarF A).
Proof.
  intros n m v A H. induction n as [| n Hrecn].
  - simpl in H. exact H.
  - simpl in H. apply Hrecn. eapply in_remove. exact H.
Qed.

Lemma freeVarAddExists2 :
 forall (n m v : nat) (A : Formula),
 In v (freeVarF (addExists m n A)) -> n + m <= v \/ v < m.
Proof.
  intros n m v A H. induction n as [| n Hrecn]; try lia.
  simpl in H. simpl in |- *.
  assert (In v (freeVarF (addExists m n A))) as H1.
  { eapply in_remove. exact H. }
  pose proof (in_remove  _ _ _ _ H).
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
      destruct (in_remove  _ _ _ _ H0). congruence.
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
 (forall v : nat, In v (freeVarT s) -> n + m <= v \/ v < m) ->
 substF (addExists m n A) v s = addExists m n (substF A v s).
Proof.
  intros n m A v s H H0. induction n as [| n Hrecn]; simpl in |- *; auto.
  rewrite (subFormulaExist LNN).
  destruct (eq_nat_dec (n + m) v) as [e | e]; try lia.
  destruct (in_dec Nat.eq_dec (n + m) (freeVarT s)) as [e0 | e0].
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
 In v (freeVarF (addForalls m n A)) -> In v (freeVarF A).
Proof.
  intros n m v A H. induction n as [| n Hrecn]; simpl in H; auto.
  apply Hrecn. eapply in_remove. exact H.
Qed.

Lemma freeVarAddForalls2 :
 forall (n m v : nat) (A : Formula),
 In v (freeVarF (addForalls m n A)) -> n + m <= v \/ v < m.
Proof.
  intros n m v A H. induction n as [| n Hrecn]; try lia.
  simpl in H. simpl in |- *.
  assert (H0: In v (freeVarF (addForalls m n A))).
  { eapply in_remove. exact H. }
  pose proof (Hrecn H0). destruct (in_remove _ _ _ _ H); lia.
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
 (forall v : nat, In v (freeVarT s) -> n + m <= v \/ v < m) ->
 substF (addForalls m n A) v s =
 addForalls m n (substF A v s).
Proof.
  intros n m A v s H H0. induction n as [| n Hrecn]; simpl in |- *; auto.
  rewrite (subFormulaForall LNN). destruct (eq_nat_dec (n + m) v) as [e | e]; try lia.
  destruct (in_dec Nat.eq_dec (n + m) (freeVarT s)) as [e0 | e0].
  - pose proof (H0 _ e0); lia.
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
      andH (substF (fst v) 0 (var (S m' + w)))
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
            (substT (n2t a) (S n)
              (n2t a0)))
          with
          (substF  (v#0 = v#(n.+1))%fol (S n) (n2t a)).
        -- auto.
        -- rewrite subFormulaEqual; simpl in |- *.
           destruct (Nat.eq_dec n n); try lia.
           rewrite subTermNil; try reflexivity.
           apply closedNatToTerm.
    + apply RepresentableAlternate with (v#0 = v#(m.+1))%fol.
      * apply iffSym, subFormulaNil; simpl; lia.
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
    (forall v : nat, In v (freeVarF (fst pair)) -> v <= n) /\ rec)
   m A ->
 Representable m g B ->
 Representable n (evalComposeFunc n m (FormulasToFuncs n m A) g)
   (composeSigmaFormula n w m A B).
Proof.
  assert
  (H: forall n w m : nat,
   n <= w ->
   forall (A : Vector.t (Formula * naryFunc n) m) (B : Formula) (g : naryFunc m),
   RepresentablesHelp n m A ->
   Vector.t_rect (Formula * naryFunc n) (fun _ _ => Prop) True
     (fun (pair : Formula * naryFunc n) (m : nat) (v : Vector.t _ m)
        (rec : Prop) =>
      (forall v : nat, In v (freeVarF (fst pair)) -> v <= n) /\ rec)
     m A ->
   Representable m g B ->
   RepresentableHelp n (evalComposeFunc n m (FormulasToFuncs n m A) g)
     (composeSigmaFormula n w m A B)).
  { intro. induction n as [| n Hrecn]; simpl in |- *.
    - intros w m H v.
      induction v as [| a n v Hrecv]; simpl in |- *; intros B g H0 H1 H2.
      + unfold composeSigmaFormula in |- *. simpl in |- *.
        replace
         (subAllFormula LNN B
            (fun x : nat => match x with
                            | O => var 0
                            | S x' => var (S (x' + w))
                            end)) with (subAllFormula LNN B (fun x : nat => var x)).
        * apply iffTrans with B.
          -- apply iffTrans with (subAllFormula LNN B (fun x : nat => var x)).
             ++ apply iffI; apply impI.
                ** eapply andE2. apply Axm; right; constructor.
                ** apply andI.
                   --- apply eqRefl.
                   --- apply Axm; right; constructor.
             ++ apply (subAllFormulaId LNN).
          -- induction H2 as (H2, H3). auto.
        * apply subAllFormula_ext. intros m H3. destruct m as [| n]; auto.
          destruct H2 as (H2, H4). apply H2 in H3. lia.
      + destruct H0 as (H0, H3). destruct H1 as (H1, H4). destruct H2 as (H2, H5).
        assert
         (H6: forall a : nat,
          SysPrf NN
            (iffH
               (composeSigmaFormula 0 w n v
                  (substF B (S n) (n2t a)))
               (equal (var 0) (n2t (evalList n (FormulasToFuncs 0 n v) (g a)))))).
        { intros a0. apply Hrecv; auto. split.
          - intros v0 H6. destruct (freeVarSubFormula3 _ _ _ _ _ H6).
            + assert (H8: In v0 (freeVarF B)).
              { eapply in_remove. exact H7. }
              destruct (in_remove _ _ _ _ H7).
              pose proof (H2 _ H8). lia.
            + elim (closedNatToTerm _ _ H7).
          - apply H5. }
        clear Hrecv. unfold composeSigmaFormula in |- *.
        unfold composeSigmaFormula in H6. simpl in |- *.
        apply
         iffTrans
          with
            (addExists (S w) n
               (andH (FormulasToFormula 0 w n v)
                  (subAllFormula LNN
                     (substF B (S n) (n2t (snd a)))
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
                        (substF (equal (var 0) (n2t (snd a))) 0
                           (var (S (n + w)))) (FormulasToFormula 0 w n v))
                     (subAllFormula LNN B
                        (fun x : nat =>
                         match x with
                         | O => var 0
                         | S x' => var (S (x' + w))
                         end))))).
        * apply (reduceExist LNN).
          -- apply closedNN.
          -- apply reduceAddExists.
             repeat apply (reduceAnd LNN); try apply iffRefl.
             apply (reduceSub LNN); auto.
             apply closedNN.
        * rewrite (subFormulaEqual LNN). rewrite (subTermVar1 LNN).
          rewrite (subTermNil LNN).
          apply
           iffTrans
             with
              (existH (n + S w)
                 (andH (equal (var (S (n + w))) (n2t (snd a)))
                    (addExists (S w) n
                       (andH (FormulasToFormula 0 w n v)
                          (subAllFormula LNN B
                             (fun x : nat =>
                              match x with
                              | O => var 0
                              | S x' => var (S (x' + w))
                              end)))))).
          -- apply (reduceExist LNN).
             ++ apply closedNN.
             ++ apply iffI.
                ** apply impI. apply andI.
                   cut
                    (SysPrf
                       (Ensembles.Add (fol.Formula LNN) NN
                          (andH
                             (andH (equal  (var (S (n + w))) (n2t (snd a)))
                                (FormulasToFormula 0 w n v))
                             (subAllFormula LNN B
                                (fun x : nat =>
                                 match x with
                                 | O => var 0
                                 | S x' => var (S (x' + w))
                                 end)))) (equal (var (S (n + w))) (n2t (snd a)))).
                   --- generalize
                        (andH
                           (andH (equal (var (S (n + w))) (n2t (snd a)))
                              (FormulasToFormula 0 w n v))
                           (subAllFormula LNN B
                              (fun x : nat =>
                               match x with
                               | O => var 0
                               | S x' => var (S (x' + w))
                               end))).
                       cut (n + w < S (n + w)); try lia.
                       +++ generalize (S (n + w)).
                           intros n0 H6 f H7.
                           clear H5 H2 H4 H1 H3 H0 g B v.
                           induction n as [| n Hrecn].
                           *** simpl in |- *. auto.
                           *** simpl in |- *. apply existSys.
                               ---- apply closedNN.
                               ---- simpl in |- *; intro.
                                    destruct H0 as [H0 | H0]; try lia.
                                    elim (closedNatToTerm _ _ H0).
                               ---- apply Hrecn. lia.
                   --- eapply andE1. eapply andE1. apply Axm; right; constructor.
                   --- apply
                        impE
                         with
                           (addExists (S w) n
                              (andH
                                 (andH (equal (var (S (n + w))) (n2t (snd a)))
                                    (FormulasToFormula 0 w n v))
                                 (subAllFormula LNN B
                                    (fun x : nat =>
                                     match x with
                                     | O => var 0
                                     | S x' => var (S (x' + w))
                                     end)))).
                       +++ apply sysWeaken.
                           apply reduceAddExistsOneWay.
                           apply impI. apply andI.
                           *** eapply andE2. eapply andE1.
                               apply Axm; right; constructor.
                           *** eapply andE2.
                               apply Axm; right; constructor.
                       +++ apply Axm; right; constructor.
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
                   --- apply impE with (equal (var (S (n + w))) (n2t (snd a))).
                       +++ apply sysWeaken. apply impI.
                           cut
                            (SysPrf
                               (Ensembles.Add (fol.Formula LNN) NN
                                  (equal (var (S (n + w))) (n2t (snd a))))
                               (impH
                                  (andH (FormulasToFormula 0 w n v)
                                     (subAllFormula LNN B
                                        (fun x : nat =>
                                         match x with
                                         | O => var 0
                                         | S x' => var (S (x' + w))
                                         end)))
                                  (andH
                                     (andH (equal (var (S (n + w))) (n2t (snd a)))
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
                                   (andH (equal (var (S (n + w))) (n2t (snd a)))
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
                               ---- intro. destruct H2 as (x, H2).
                                    destruct H2 as (H2, H3).
                                    destruct H3 as [x H3 | x H3].
                                    ++++ elim (closedNN (n + S w)). 
                                         exists x. auto.
                                    ++++ destruct H3. simpl in H2.
                                         destruct H2 as [H2 | H2]; try lia.
                                         elim (closedNatToTerm _ _ H2).
                               ---- simpl in |- *. intro H2.
                                    elim (in_remove _ _ _ _ H2). auto.
                               ---- apply existSimp. 
                                    apply impE with (addExists (S w) n f).
                                    ++++ apply sysWeaken. apply Hrecn; auto. lia.
                                    ++++ apply Axm; right; constructor.
                           *** apply impI. repeat apply andI.
                               ---- apply Axm; left; right; constructor.
                               ---- eapply andE1. apply Axm; right; constructor.
                               ---- eapply andE2. apply Axm; right; constructor.
                       +++ eapply andE1. apply Axm; right; constructor.
                   --- eapply andE2. apply Axm; right; constructor.
          -- apply
              iffTrans
               with
                 (substF
                    (addExists (S w) n
                       (andH (FormulasToFormula 0 w n v)
                          (subAllFormula LNN B
                             (fun x : nat =>
                              match x with
                              | O => var 0
                              | S x' => var (S (x' + w))
                              end)))) (S n + w) (n2t (snd a))).
             ++ apply iffI.
                ** apply impI. apply existSys.
                   --- apply closedNN.
                   --- intro H6. destruct (freeVarSubFormula3 _ _ _ _ _ H6).
                       +++ elim (in_remove _ _ _ _ H7). lia.
                       +++ elim (closedNatToTerm _ _ H7).
                   --- apply
                        impE
                         with
                           (substF 
                              (addExists (S w) n
                                 (andH (FormulasToFormula 0 w n v)
                                    (subAllFormula LNN B
                                       (fun x : nat =>
                                        match x with
                                        | O => var 0
                                        | S x' => var (S (x' + w))
                                        end)))) (S n + w) (var (S n + w))).
                       +++ apply (subWithEquals LNN). eapply andE1.
                           apply Axm; right; constructor.
                       +++ rewrite (subFormulaId LNN). eapply andE2.
                           apply Axm; right; constructor.
                ** apply impI. apply existI with (n2t (snd a)).
                   rewrite (subFormulaAnd LNN). rewrite Nat.add_succ_r.
                   apply andI.
                   --- rewrite subFormulaEqual. rewrite (subTermVar1 LNN).
                       rewrite (subTermNil LNN).
                       +++ apply eqRefl.
                       +++ apply closedNatToTerm.
                   --- apply Axm; right; constructor.
             ++ rewrite subAddExistsNice.
                ** apply reduceAddExists. rewrite (subFormulaAnd LNN).
                   apply (reduceAnd LNN).
                   --- apply (subFormulaNil LNN).
                       cut (n + w < S n + w); try lia.
                       generalize (S n + w). clear H5 H3 g H2.
                       induction v as [| a0 n v Hrecv]; unfold not in |- *; intros n0 H2 H3.
                       +++ simpl in H3. lia.
                       +++ simpl in H3. destruct (in_app_or _ _ _ H3) as [H5 | H5].
                           *** simpl in H4.
                               induction (freeVarSubFormula3 _ _ _ _ _ H5) as [H6 | H6].
                             elim (proj1 (Nat.le_ngt n0 0)).
                               ---- decompose record H4 /r. intros H7 H8; apply H7.
                                    eapply in_remove. apply H6.
                               ---- lia.
                               ---- destruct H6 as [H6 | H6].
                                    ++++ lia.
                                    ++++ elim H6.
                           *** lazymatch goal with _ : In ?n _ |- _ => elim Hrecv with n end.
                               ---- simpl in H4. tauto.
                               ---- lia.
                               ---- auto.
                   --- eapply iffTrans. apply (subSubAllFormula LNN).
                       apply iffSym. eapply iffTrans.
                       +++ apply (subAllSubFormula LNN).
                       +++ replace
                            (subAllFormula LNN B
                               (fun n1 : nat =>
                                substT 
                                  match n1 with
                                  | O => var 0
                                  | S x' => var (S (x' + w))
                                  end (S n + w) (n2t (snd a)))) with
                            (subAllFormula LNN B
                               (fun x : nat =>
                                match eq_nat_dec (S n) x with
                                | left _ =>
                                    subAllTerm LNN (n2t (snd a))
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
                               ---- rewrite <- e. rewrite (subTermVar1 LNN).
                                    clear H0. induction (snd a).
                                    ++++ simpl in |- *. reflexivity.
                                    ++++ simpl in |- *. rewrite IHn0. reflexivity.
                               ---- destruct m as [| n0].
                                    ++++ simpl in |- *. reflexivity.
                                    ++++ rewrite (subTermVar2 LNN).
                                         **** reflexivity.
                                         **** lia.
                ** lia.
                ** intros v0 H6. elim (closedNatToTerm _ _ H6).
          -- apply closedNatToTerm.
    - intros. 
      set
       (v' :=
        Vector.t_rec (Formula * (nat -> naryFunc n))
          (fun (m : nat) (v : Vector.t _ m) => Vector.t (Formula * naryFunc n) m)
          (Vector.nil _)
          (fun (pair : Formula * (nat -> naryFunc n)) (m : nat) 
             (v : Vector.t _ m) (rec : Vector.t (Formula * naryFunc n) m) =>
           Vector.cons _
             (substF (fst pair) (S n) (n2t a), snd pair a) m
             rec) _ A) in *.
      assert
       (H3:RepresentableHelp n (evalComposeFunc n m (FormulasToFuncs n m v') g)
          (addExists (S w) m
             (andH (FormulasToFormula n w m v')
                (subAllFormula LNN B
                   (fun x : nat =>
                    match x with
                    | O => var 0
                    | S x' => var (S (x' + w))
                    end))))).
      + unfold composeSigmaFormula in Hrecn.
        simpl in Hrecn. apply Hrecn.
        * lia.
        * clear B g H2.
          induction A as [| a0 n0 A HrecA]; 
            simpl in (value of v'); simpl in |- *; auto.
          split.
          -- simpl in H0. destruct H0 as (H0, H2). apply H0.
          -- apply HrecA.
             ++ destruct H0 as (H0, H2). auto.
             ++ simpl in H1. destruct H1 as (H1, H2). auto.
        * simpl in H1. clear H2 H0 g B. induction A as [| a0 n0 A HrecA].
          -- simpl in |- *. auto.
          -- simpl in |- *. split.
             ++ simpl in H1. destruct H1 as (H0, H1). intros v H2.
                destruct (freeVarSubFormula3 _ _ _ _ _ H2).
                ** assert (H4: v <= S n).
                   { apply H0. eapply in_remove. exact H3. }
                   destruct (proj1 (Nat.lt_eq_cases v (S n))).
                   --- assumption. 
                   --- lia.
                   --- elim (in_remove_neq _ _ _ _ _ H3). auto.
                ** elim (closedNatToTerm _ _ H3).
             ++ apply HrecA. destruct H1 as (H0, H1). auto.
        * auto.
      + unfold composeSigmaFormula in |- *. clear Hrecn.
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
          -- apply reduceAddExists. rewrite (subFormulaAnd LNN).
             apply (reduceAnd LNN).
             ++ clear H3 H2 H1 H0 g B. induction A as [| a0 n0 A HrecA].
                ** simpl in |- *. apply iffSym. apply (subFormulaNil LNN). simpl in |- *. lia.
                ** simpl in |- *. rewrite (subFormulaAnd LNN).
                   apply (reduceAnd LNN); [| apply HrecA ].
                   apply (subFormulaExch LNN); try lia.
                   --- apply closedNatToTerm.
                   --- unfold not in |- *; intros. destruct H0 as [H0 | H0].
                       +++ lia.
                       +++ apply H0.
             ++ apply iffSym. apply (subFormulaNil LNN).
                intro H4. decompose record (freeVarSubAllFormula1 _ _ _ _ H4) /r; 
                  intros x H6 H7.
                destruct x as [| n0].
                ** destruct H7 as [H5 | H5]; try lia. elim H5.
                ** destruct H7 as [H5| H5].
                   --- lia.
                   --- elim H5.
          -- lia.
          -- intros. elim (closedNatToTerm _ _ H4).
        * apply Representable_ext with (evalComposeFunc n m (FormulasToFuncs n m v') g).
          clear H3 H2 H1 H0 B.
          -- apply extEqualCompose.
             ++ unfold extEqualVector in |- *. clear g.
                induction A as [| a0 n0 A HrecA]; simpl in |- *; auto.
                split.
                ** apply extEqualRefl.
                ** apply HrecA.
             ++ apply extEqualRefl.
          -- apply H3. }
  intros n w m H0 A B g H1 H2 H3. split.
  - intros v H4. unfold composeSigmaFormula in H4.
    assert
     (H5: In v
        (freeVarF
           (andH (FormulasToFormula n w m A)
              (subAllFormula LNN B
                 (fun x : nat =>
                  match x with
                  | O => var 0
                  | S x' => var (S x' + w)
                  end))))).
    { eapply freeVarAddExists1. apply H4. }
    simpl in H5. destruct (in_app_or _ _ _ H5).
    + assert (H7: m + S w <= v \/ v < S w).
      { eapply freeVarAddExists2. apply H4. }
      clear H5 H4 H3 H1 g B.
      induction A as [| a n0 A HrecA].
      * simpl in H6. lia.
      * simpl in H6. destruct (in_app_or _ _ _ H6).
        -- simpl in H2. destruct H2 as (H2, H3).
           destruct (freeVarSubFormula3 _ _ _ _ _ H1) as [H4 | H4].
           ++ apply H2. eapply in_remove. exact H4.
           ++ destruct H4 as [H4 | H4].
              ** lia.
              ** elim H4.
        -- apply HrecA; auto.
           ++ simpl in H2. tauto.
           ++ lia.
    + decompose record (freeVarSubAllFormula1 _ _ _ _ H6) /r; intros x H8 H9.
      destruct x as [| n0].
      * destruct H9 as [H7 | H7]; try lia. elim H7.
      * induction H9 as [H7 | H7].
        -- rewrite <- H7. destruct H3 as (H3, H9).
           assert (H10: S n0 <= m). { apply H3. auto. }
           destruct (freeVarAddExists2 _ _ _ _ H4) as [H11 | H11].
           ++ lia.
           ++ lia.
        -- elim H7.
  - apply H; auto.
Qed.



Definition minimize (A B : Formula) (v x : nat) : Formula :=
  (A /\ allH x, v#x < v#v -> ~ substF B v v#x)%fol.
     

Remark minimize1 :
 forall (A B : Formula) (v x : nat),
 v <> x ->
 ~ In x (freeVarF B) ->
 forall a : nat,
 SysPrf NN (substF A v (n2t a)) ->
 SysPrf NN (substF B v (n2t a)) ->
 (forall b : nat,
  b < a -> SysPrf NN (notH (substF A v (n2t b)))) ->
 (forall b : nat,
  b < a -> SysPrf NN (notH (substF B v (n2t b)))) ->
 SysPrf NN (iffH (minimize A B v x) (equal (var v) (n2t a))).
Proof.
  intros A B v x H H0 a H1 H2 H3 H4. apply iffI.
  unfold minimize in |- *. apply impI.
  apply
   impE
    with
      (substF 
         (impH (LT (var x) (var v)) (notH (substF B v (var x))))
         x (n2t a)).
  - rewrite (subFormulaImp LNN). rewrite (subFormulaNot LNN).
    apply
     impTrans
      with
        (impH (LT (n2t a) (var v))
           (notH (substF B v (n2t a)))).
    + apply iffE1. apply (reduceImp LNN).
      * unfold LT at 2 in |- *. rewrite (subFormulaRelation LNN).
        simpl in |- *. destruct (eq_nat_dec x x) as [e | e]; try lia.
        destruct (eq_nat_dec x v).
        -- elim H. auto.
        -- apply iffRefl.
      * apply (reduceNot LNN). apply (subFormulaTrans LNN).
        intro H5. elim H0. eapply in_remove. exact H5.
    + apply impTrans with (notH (LT (n2t a) (var v))).
      * apply impI. 
        apply impE with (notH (notH (substF B v (n2t a)))).
        apply cp2.
        -- apply Axm; right; constructor.
        -- apply nnI. do 2 apply sysWeaken. exact H2.
      * apply impE with (notH (LT (var v) (n2t a))).
        apply
         orE
          with
            (LT (var v) (n2t a))
            (orH (equal (var v) (n2t a)) (LT (n2t a) (var v))).
        -- apply sysWeaken. apply nn9.
        -- repeat apply impI.
           apply contradiction with (LT (var v) (n2t a)).
           ++ apply Axm; left; left; right; constructor.
           ++ apply Axm; left; right; constructor.
        -- apply impI. apply orSys; repeat apply impI.
           ++ apply Axm; left; left; right; constructor.
           ++ apply contradiction with (LT (n2t a) (var v)).
              ** apply Axm; left; left; right; constructor.
              ** apply Axm; right; constructor.
        -- apply impE with (notH (notH A)). apply cp2.
           ++ apply sysWeaken. apply boundedLT. intros n H5.
              rewrite (subFormulaNot LNN). auto.
           ++ apply nnI. eapply andE1. apply Axm; right; constructor.
  - apply forallE. eapply andE2. apply Axm; right; constructor.
  - apply impI. unfold minimize in |- *.
    rewrite <-
     (subFormulaId LNN
        (andH A
           (forallH x
              (impH (LT (var x) (var v))
                 (notH (substF B v (var x)))))) v).
    apply
     impE
      with
        (substF 
           (andH A
              (forallH x
                 (impH (LT (var x) (var v))
                    (notH (substF B v (var x)))))) v 
           (n2t a)).
    + apply (subWithEquals LNN). apply eqSym. apply Axm; right; constructor.
    + apply sysWeaken. rewrite (subFormulaAnd LNN). apply andI.
      * auto.
      * rewrite (subFormulaForall LNN). destruct (eq_nat_dec x v) as [e | e];
          try congruence.
        destruct (In_dec eq_nat_dec x (freeVarT (n2t a))) as [e0 | e0].
        -- elim (closedNatToTerm _ _ e0).
        -- apply forallI. apply closedNN. rewrite (subFormulaImp LNN).
           unfold LT in |- *. rewrite (subFormulaRelation LNN).
           simpl in |- *. destruct (eq_nat_dec v v) as [e1 | e1]; try congruence.
           ++ induction (eq_nat_dec v x) as [e2 | e2]; try congruence.
              apply impI. apply forallE. apply forallI. intro H5.
              destruct H5 as (x0, H5); destruct H5 as (H5, H6).
              destruct H6 as [x0 H6 | x0 H6].
              ** elim closedNN with v. exists x0; auto.
              ** destruct H6. destruct H5 as [H5 | H5]; try congruence.
                 fold (freeVarT (n2t a)) in H5. simpl in H5.
                 rewrite  app_nil_r in H5. elim (closedNatToTerm _ _ H5).
              ** apply impE with (LT (var x) (n2t a)).
                 --- apply sysWeaken. apply boundedLT. intros n H5.
                     rewrite (subFormulaNot LNN).
                     apply impE with (notH (substF B v (n2t n))).
                     +++ apply cp2. apply iffE1. apply (subFormulaTrans LNN).
                         intro H6. elim H0. eapply in_remove. exact H6.
                     +++ apply H4; auto.
                 --- apply Axm; right; constructor.
Qed.

Lemma subFormulaMinimize :
 forall (A B : Formula) (v x z : nat) (s : Term),
 ~ In x (freeVarT s) ->
 ~ In v (freeVarT s) ->
 x <> z ->
 v <> z ->
 SysPrf NN
   (iffH (substF  (minimize A B v x) z s)
      (minimize (substF A z s) (substF B z s) v
         x)).
Proof.
  intros A B v x z s H H0 H1 H2. unfold minimize in |- *.
  rewrite (subFormulaAnd LNN). rewrite (subFormulaForall LNN).
  destruct (eq_nat_dec x z) as [e | e]; try congruence.
  destruct (In_dec eq_nat_dec x (freeVarT s)) as [e0 | e0]; try tauto.
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
  - congruence. 
  - simpl in |- *. intro H3. tauto.
  - auto.
Qed.




Definition primRecSigmaFormulaHelp (n : nat) (SigA SigB : Formula) : Formula :=
  andH
    (existH 0
       (andH SigA
          (substF2 βR 1 Zero 2 (var n.+2))))
    (forallH n.+3
       (impH (LT (var n.+3) (var n.+1))
          (existH 0
             (existH (S n)
                (andH
                   (substF3 βR 
                      1 (var n.+3)
                      2 (var n.+2)
                      0 (var n.+1))
                   (andH
                      (substF SigB n.+2 (var n.+3))
                      (substF2 βR 
                         1 (Succ (var (n.+3)))
                         2 (var n.+2)))))))).

Definition primRecPiFormulaHelp (n : nat) (SigA SigB : Formula) : Formula :=
  andH
    (forallH 0
       (impH SigA
          (substF2 βR 1 Zero 2 (var n.+2))))
    (forallH n.+3
       (impH (LT (var n.+3) (var n.+1))
          (forallH 0
             (forallH n.+1
                (impH
                   (substF3 βR 
                      1 (var n.+3)
                      2 (var n.+2)
                      0 (var n.+1))
                   (impH
                      (substF SigB 
                         n.+2 (var n.+3))
                      (substF2 βR 
                         1 (Succ (var n.+3))
                         2 (var n.+2)))))))).

Lemma freeVarPrimRecSigmaFormulaHelp1 :
 forall (n : nat) (A B : Formula) (v : nat),
 In v (freeVarF (primRecSigmaFormulaHelp n A B)) ->
 In v (freeVarF A) \/
 In v (freeVarF B) \/ v = n.+2 \/ v = n.+1.
Proof.
  intros n A B v H. unfold primRecSigmaFormulaHelp in H.
  assert
   (H0: forall v : nat,
    In v (freeVarF βR) -> v = 0 \/ v = 1 \/ v = 2).
  { intros v0 H0. assert (H1: Representable 2 β βR).
    apply betaRepresentable. destruct H1 as (H1, H2).
    apply H1 in H0. lia. }
  repeat
   match goal with
   | H:(In v (freeVarF (existH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarF X2));
        [ eapply in_remove; apply H
        | assert (v <> X1); [ eapply in_remove_neq; apply H | clear H ] ]
   | H:(In v (freeVarF (forallH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarF X2));
        [ eapply in_remove; apply H
        | assert (v <> X1); [ eapply in_remove_neq; apply H | clear H ] ]
   | H:(In v (List.remove _ ?X1 (freeVarF ?X2))) |- _ =>
       assert (In v (freeVarF X2));
        [ eapply in_remove; apply H
        | assert (v <> X1); [ eapply in_remove_neq; apply H | clear H ] ]
   | H:(In v (freeVarF (andH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarF X1 ++ freeVarF X2));
        [ apply H | clear H ]
   | H:(In v (freeVarF (impH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarF X1 ++ freeVarF X2));
        [ apply H | clear H ]
   | H:(In v (_ ++ _)) |- _ =>
       destruct (in_app_or _ _ _ H); clear H
   | H:(In v (freeVarF (substF ?X1 ?X2 ?X3))) |- _ =>
       induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
   | H:(In v (freeVarF (LT ?X1 ?X2))) |- _ =>
       rewrite freeVarLT in H
   | H:(In v (freeVarF  βR)) |- _ =>
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
 In v (freeVarF (primRecPiFormulaHelp n A B)) ->
 In v (freeVarF A) \/
 In v (freeVarF B) \/ v = n.+2 \/ v = n.+1.
Proof.
  intros n A B v H. unfold primRecPiFormulaHelp in H.
  assert
   (H0: forall v : nat,
    In v (freeVarF βR) -> v = 0 \/ v = 1 \/ v = 2).
  { intros v0 H0. assert (Representable 2 β βR).
    apply betaRepresentable.
    destruct H1 as (H1, H2). apply H1 in H0. lia. }
  repeat
   match goal with
   | H:(In v (freeVarF (existH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarF X2));
        [ eapply in_remove; apply H
        | assert (v <> X1); [ eapply in_remove_neq; apply H | clear H ] ]
   | H:(In v (freeVarF (forallH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarF X2));
        [ eapply in_remove; apply H
        | assert (v <> X1); [ eapply in_remove_neq; apply H | clear H ] ]
   | H:(In v (List.remove  eq_nat_dec ?X1 (freeVarF ?X2))) |- _ =>
       assert (In v (freeVarF X2));
        [ eapply in_remove; apply H
        | assert (v <> X1); [ eapply in_remove_neq; apply H | clear H ] ]
   | H:(In v (freeVarF (andH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarF X1 ++ freeVarF X2));
        [ apply H | clear H ]
   | H:(In v (freeVarF (impH ?X1 ?X2))) |- _ =>
       assert (In v (freeVarF X1 ++ freeVarF X2));
        [ apply H | clear H ]
   | H:(In v (_ ++ _)) |- _ =>
       induction (in_app_or _ _ _ H); clear H
   | H:(In v (freeVarF (substF ?X1 ?X2 ?X3))) |- _ =>
       induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
   | H:(In v (freeVarF (LT ?X1 ?X2))) |- _ =>
       rewrite freeVarLT in H
   | H:(In v (freeVarF βR)) |- _ =>
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
  existH n.+2
    (andH
       (minimize (primRecSigmaFormulaHelp n SigA SigB)
          (primRecPiFormulaHelp n SigA SigB) n.+2 n.+4)
       (substF2  βR 
          2 (var n.+2)
          1 (var n.+1))).

Remark notBoundedForall :
 forall (P : nat -> Prop) (b : nat),
 (forall x : nat, decidable (P x)) ->
 ~ (forall n : nat, n < b -> P n) -> exists n : nat, n < b /\ ~ P n.
Proof.
  intros P b H H0; induction b as [| b Hrecb].
  - elim H0. lia.
  - destruct (H b) as [e | e].
    + assert (H1: ~ (forall n : nat, n < b -> P n)).
      { intro H1. elim H0. intros n H2.
        assert (n < b \/ n = b) as H3 by lia. destruct H3.
        - auto.
        - rewrite H3; auto. }
      decompose record (Hrecb H1) /r; intros x H3 H4.
      exists x. split; auto; lia.
    + exists b. split; auto; lia.
Qed.

Remark In_betaFormula_subst_1_2_0 :
 forall (a b c : Term) (v : nat),
 In v
   (freeVarF 
      (substF3  βR 1 a 2 b 0 c)) ->
 In v (freeVarT a) \/ In v (freeVarT b) \/ In v (freeVarT c).
Proof.
  intros a b c v H. destruct (freeVarSubFormula3 _ _ _ _ _ H) as [H0 | H0].
  - assert
     (H1: In v
        (freeVarF 
           (substF2 βR 1 a 2 b))).
    { eapply in_remove; apply H0. }
    destruct (freeVarSubFormula3 _ _ _ _ _ H1) as [H2 | H2].
    + assert (H3: In v (freeVarF (substF βR 1 a))).
      { eapply in_remove; apply H2. }
      destruct (freeVarSubFormula3 _ _ _ _ _ H3) as [H4 | H4].
      * destruct v as [| n].
        -- elim (in_remove_neq _ _ _ _ _ H0). reflexivity.
        -- destruct n as [| n].
           ++ elim (in_remove_neq _ _ _ _ _ H4); reflexivity.
           ++ destruct n as [| n].
              ** elim (in_remove_neq _ _ _ _ _ H2). reflexivity.
              ** elim (proj1 (Nat.le_ngt  (S (S (S n))) 2)).
                 --- assert (H5: Representable 2 β βR).
                     { apply betaRepresentable. }
                     destruct H5 as (H5, H6). apply H5.
                     eapply in_remove. exact H4.
                 --- lia.
      * tauto.
    + tauto.
  - tauto.
Qed.

Remark In_betaFormula_subst_1_2 :
  forall (a b : Term) (v : nat),
    In v
      (freeVarF 
         (substF (substF βR 1 a) 2 b)) ->
    In v (freeVarT a) \/
      In v (freeVarT b) \/ In v (freeVarT (L:=LNN) (var 0)).
Proof.
  intros a b v H. apply In_betaFormula_subst_1_2_0.
  rewrite (subFormulaId LNN); exact H.
Qed.

Remark In_betaFormula_subst_1 :
 forall (a : Term) (v : nat),
 In v (freeVarF (substF βR 1 a)) ->
 In v (freeVarT a) \/
 In v (@freeVarT LNN (var 2)) \/ In v (@freeVarT LNN (var 0)).
Proof.
  intros a v H. apply In_betaFormula_subst_1_2.
  rewrite (subFormulaId LNN). exact H.
Qed.

Remark In_betaFormula :
 forall v : nat,
 In v (freeVarF βR) ->
 In v (@freeVarT LNN (var 1)) \/
 In v (@freeVarT LNN (var 2)) \/ In v (@freeVarT LNN (var 0)).
Proof.
  intros v H. apply In_betaFormula_subst_1.
  rewrite (subFormulaId LNN). exact H.
Qed.

Remark In_betaFormula_subst_2 :
 forall (a : Term) (v : nat),
 In v (freeVarF (substF βR 2 a)) ->
 In v (freeVarT a) \/
 In v (@freeVarT LNN (var 1)) \/ In v (@freeVarT LNN (var 0)).
Proof.
  intros a v H. rewrite <- (subFormulaId LNN βR 1) in H.
  decompose sum (In_betaFormula_subst_1_2 _ _ _ H); tauto.
Qed.

Remark In_betaFormula_subst_2_1 :
 forall (a b : Term) (v : nat),
 In v
   (freeVarF 
      (substF  (substF βR 2 a) 1 b)) ->
 In v (freeVarT a) \/
 In v (freeVarT b) \/ In v (@freeVarT LNN (var 0)).
Proof.
  intros a b v H. destruct (freeVarSubFormula3 _ _ _ _ _ H) as [H0 | H0].
  - assert (H1: In v (freeVarF (substF βR 2 a))).
    { eapply in_remove. apply H0. }
    decompose sum (In_betaFormula_subst_2 _ _ H1); try tauto.
    destruct H3 as [H2 | H2].
    elim (in_remove_neq _ _ _ _ _ H0).
    symmetry  in |- *; assumption.
    elim H2.
  - tauto.
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
           (freeVarF 
              (substF3   βR 1 _ 2 _ 0 _)))|- _
    => decompose sum (In_betaFormula_subst_1_2_0 _ _ _ _ H); clear H
    | H:(In ?X3
           (freeVarF 
              (substF2 βR 1 _ 2 _))) |- _ =>
        decompose sum (In_betaFormula_subst_1_2 _ _ _ H); clear H
    | H:(In ?X3 (freeVarF (substF βR 1 _)))
    |- _ =>
        decompose sum (In_betaFormula_subst_1 _ _ H); clear H
    | H:(In ?X3 (freeVarF βR)) |- _ =>
        decompose sum (In_betaFormula _ H); clear H
    | H:(In ?X3
           (freeVarF 
              (substF2 βR 2 _ 1 _))) |- _ =>
        decompose sum (In_betaFormula_subst_2_1 _ _ _ H); clear H
    | H:(In ?X3 (freeVarF (substF βR 2 _)))
    |- _ =>
        decompose sum (In_betaFormula_subst_2 _ _ H);
         clear H
    | H:(In ?X3 (freeVarF (existH ?X1 ?X2))) |- _ =>
        assert
         (In X3 (List.remove  eq_nat_dec X1 (freeVarF X2)));
         [ apply H | clear H ]
    | H:(In ?X3 (freeVarF (forallH ?X1 ?X2))) |- _ =>
        assert
         (In X3 (List.remove eq_nat_dec X1 (freeVarF X2)));
         [ apply H | clear H ]
    | 
    (*
    .
    *)
    H:(In ?X3 (List.remove  eq_nat_dec ?X1 (freeVarF ?X2))) |- _
    =>
        assert (In X3 (freeVarF X2));
         [ eapply in_remove; apply H
         | assert (X3 <> X1); [ eapply in_remove_neq; apply H | clear H ] ]
    | H:(In ?X3 (freeVarF (andH ?X1 ?X2))) |- _ =>
        assert (In X3 (freeVarF X1 ++ freeVarF X2));
         [ apply H | clear H ]
    | H:(In ?X3 (freeVarF  (impH ?X1 ?X2))) |- _ =>
        assert (In X3 (freeVarF X1 ++ freeVarF X2));
         [ apply H | clear H ]
    | H:(In ?X3 (freeVarF  (notH ?X1))) |- _ =>
        assert (In X3 (freeVarF  X1)); [ apply H | clear H ]
    | H:(In _ (freeVarF (primRecPiFormulaHelp _ _ _))) |- _ =>
        decompose sum (freeVarPrimRecPiFormulaHelp1 _ _ _ _ H); clear H
    | J:(In ?X3 (freeVarF A)),H:(forall v : nat,
                                           In v (freeVarF A) ->
                                           v <= S n) |- _ =>
        elim (proj1 (Nat.le_ngt X3 (S n)));
         [ apply H; apply J | 
           clear J; 
           repeat apply Nat.lt_succ_diag_r || apply  Nat.lt_lt_succ_r]
    | H:(In ?X3 (freeVarF B)),H0:(forall v : nat,
                                            In v (freeVarF B) ->
                                            v <= S (S (S n))) |- _ =>
        elim (proj1 (Nat.le_ngt X3 (S (S (S n)))));
         [ apply H0; apply H | clear H; 
                               repeat 
                                 apply Nat.lt_succ_diag_r || apply Nat.lt_lt_succ_r]
    | H:(In _ (_ ++ _)) |- _ =>
        induction (in_app_or _ _ _ H); clear H
    | H:(In _ (freeVarF (substF ?X1 ?X2 ?X3))) |- _
    =>
        induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
    | H:(In _ (freeVarF (LT ?X1 ?X2))) |- _ =>
        rewrite freeVarLT in H
    | H:(In _ (freeVarT (n2t _))) |- _ =>
        elim (closedNatToTerm _ _ H)
    | H:(In _ (freeVarT Zero)) |- _ =>
        elim H
    | H:(In _ (freeVarT (Succ _))) |- _ =>
        rewrite freeVarSucc in H
    | H:(In _ (@freeVarT LNN (var _))) |- _ =>
        simpl in H; decompose sum H; clear H
    | H:(In _ (@freeVarT LNN (var  _))) |- _ =>
        simpl in H; decompose sum H; clear H
    end.

Remark primRecSigmaRepresentable :
 forall (n : nat) (A : Formula) (g : naryFunc n),
 Representable n g A ->
 forall (B : Formula) (h : naryFunc (S (S n))),
 Representable n.+2 h B ->
 Representable (S n) (evalPrimRecFunc n g h) (primRecSigmaFormula n A B).
Proof.
  assert
   (H: forall (n : nat) (A : Formula) (g : naryFunc n),
    Representable n g A ->
    forall (B : Formula) (h : naryFunc (S (S n))),
    Representable (S (S n)) h B ->
    RepresentableHelp (S n) (evalPrimRecFunc n g h) (primRecSigmaFormula n A B)).
  { induction n as [| n Hrecn].
    - simpl; intros A g H B h H0.
      unfold primRecSigmaFormula. intros a. rewrite (subFormulaExist LNN).
      induction (In_dec eq_nat_dec 2 (freeVarT (n2t a))) as [a0 | b].
      + elim (closedNatToTerm _ _ a0).
      + simpl. clear b. assert (repBeta : Representable 2 β βR).
        { apply betaRepresentable. }
        rewrite (subFormulaAnd LNN). repeat rewrite (subFormulaId LNN).
        apply
         iffTrans
          with
            (existH 2
               (andH
                  (minimize
                     (substF  (primRecSigmaFormulaHelp 0 A B) 1
                        (n2t a))
                     (substF (primRecPiFormulaHelp 0 A B) 1
                        (n2t a)) 2 4)
                  (substF βR 1 (n2t a)))).
        * apply (reduceExist LNN).
          -- apply closedNN.
          -- apply (reduceAnd LNN).
             ++ apply subFormulaMinimize; first [ discriminate | apply closedNatToTerm ].
             ++ apply iffRefl.
        * set (f := evalPrimRecFunc 0 g h) in *. 
          destruct (betaTheorem1 (S a) f) as [x p]. 
          destruct x as (a0, b). simpl in p.
          set (P := fun c : nat => forall z : nat, z < S a -> f z = β c z) in *.
          assert (H1: forall c : nat, decidable (P c)).
          { intros c. unfold decidable, P. 
            set (Q := fun z : nat => f z <> β c z) in *.
            assert (H1: forall z : nat, decidable (Q z)).
            { intros. unfold decidable, Q. 
              destruct (eq_nat_dec (f z) (β c z)); auto. }
            destruct (boundedCheck Q H1 (S a)) as [H2 | H2].
            - left. unfold Q in H2. intros z H3. 
              destruct (eq_nat_dec (f z) (β c z)).
              + auto.
              + elim (H2 z); auto.
            - right. intro H3. destruct H2 as (x, H2). destruct H2 as (H2, H4). 
              elim H4. apply H3; auto. }
          induction (smallestExists P H1 (cPair b a0)).
          -- destruct H2 as (H2, H3). clear H1 p b a0.
             apply
              iffTrans
               with
                 (existH 2
                    (andH (equal (var 2) (n2t x))
                       (substF  βR 1 (n2t a)))).
             ++ apply (reduceExist LNN).
                ** apply closedNN.
                ** apply (reduceAnd LNN).
                   --- assert
                        (subExistSpecial :
                         forall (F : Formula) (a b c : nat),
                         b <> c ->
                         substF (existH b F) c (n2t a) =
                         existH b (substF F c (n2t a))).
                       { intros F a0 b c H1. rewrite (subFormulaExist LNN). 
                         destruct (eq_nat_dec b c) as [e | e].
                         - elim H1. auto.
                         - destruct 
                             (In_dec eq_nat_dec b (freeVarT (n2t a0))) 
                             as [H4 | H4].
                           + elim (closedNatToTerm _ _ H4).
                           + reflexivity. }
                       assert
                        (subForallSpecial :
                         forall (F : Formula) (a b c : nat),
                         b <> c ->
                         substF (forallH b F) c (n2t a) =
                         forallH b (substF F c (n2t a))).
                       { intros F a0 b c H1. rewrite (subFormulaForall LNN). 
                         destruct (eq_nat_dec b c) as [e | e].
                         - elim H1. auto.
                         - destruct (In_dec eq_nat_dec b 
                                       (freeVarT (n2t a0))) as [e0 | e0].
                           + elim (closedNatToTerm _ _ e0).
                           + reflexivity. }
                       apply minimize1.
                       +++ discriminate.
                       +++ intro H1. 
                           destruct (freeVarSubFormula3 _ _ _ _ _ H1) as [H4 | H4].
                           *** assert (H5: In 4 (freeVarF 
                                               (primRecPiFormulaHelp 0 A B))).
                               { eapply in_remove. apply H4. }
                               decompose sum (freeVarPrimRecPiFormulaHelp1 _ _ _ _ H5) /r.
                               ---- intro H6; destruct H as (H, H7). 
                                    elim (proj1 (Nat.le_ngt 4 0)).
                                    ++++ apply H. apply H6.
                                    ++++ repeat constructor.
                               ---- intro H7;  destruct H0 as (H0, H6). 
                                    elim (proj1 (Nat.le_ngt 4 2)).
                                    ++++ apply H0. apply H7.
                                    ++++ repeat constructor.
                               ---- discriminate 1.
                               ---- discriminate 1.
                           *** elim (closedNatToTerm _ _ H4).
                       +++ unfold primRecSigmaFormulaHelp.
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
                           *** apply existI with (n2t (f 0)). 
                               rewrite (subFormulaAnd LNN). apply andI.
                               ---- unfold f, evalPrimRecFunc. 
                                    destruct H as (H, H1). simpl in H1.
                                    apply impE with 
                                      (substF A 0 (n2t g)).
                                    ++++ apply iffE2. apply (reduceSub LNN).
                                         **** apply closedNN.
                                         **** apply iffTrans with (substF A 2 (n2t x)).
                                              apply (reduceSub LNN).
                                              { apply closedNN. }
                                              { apply (subFormulaNil LNN). 
                                                intro H4. 
                                                elim (proj1 (Nat.le_ngt 1 0)).
                                                - apply H; auto.
                                                - auto. }
                                              { apply (subFormulaNil LNN). 
                                                intro H4. 
                                                elim (proj1 (Nat.le_ngt 2 0)).
                                                - apply H; auto.
                                                - auto. }
                                    ++++ apply
                                          impE
                                           with (substF (equal (var 0) (n2t g)) 0 (n2t g)).
                                         **** apply iffE2. apply (reduceSub LNN).
                                              { apply closedNN. }
                                              { auto. }
                                         **** rewrite (subFormulaEqual LNN). 
                                              simpl. rewrite (subTermNil LNN).
                                              { apply eqRefl. }
                                              { apply closedNatToTerm. }
                               ---- destruct repBeta as (H1, H4). 
                                    simpl in H4. rewrite (subFormulaId LNN).
                                    apply impE with
                                        (substF3 βR 
                                           1 Zero
                                           2 (n2t x) 
                                           0 (n2t (f 0))).
                                    ++++ apply iffE2; apply (reduceSub LNN).
                                         **** apply closedNN.
                                         **** apply (reduceSub LNN).
                                              { apply closedNN. }
                                              { apply (subFormulaNil LNN). intro H5.
                                                destruct (freeVarSubFormula3 _ _ _ _ _ H5) as [H6 | H6].
                                                - elim (in_remove_neq _ _ _ _ _ H6). reflexivity.
                                                - elim H6. }
                                    ++++ apply impE with
                                             (substF (v#0 = n2t (β x 0))%fol 0 (n2t (f 0))).
                                         **** apply iffE2, (reduceSub LNN).
                                              { apply closedNN. }
                                              { apply
                                                 iffTrans
                                                  with
                                                    (substF2 βR 
                                                       2 (n2t x)
                                                       1 (n2t 0)).
                                                - apply (subFormulaExch LNN).
                                                  + discriminate.
                                                  + apply closedNatToTerm.
                                                  + apply closedNatToTerm.
                                                - apply H4. }
                                         **** rewrite (subFormulaEqual LNN). 
                                              simpl; rewrite (subTermNil LNN).
                                              { rewrite H2; [apply eqRefl | apply Nat.lt_0_succ]. }
                                              { apply closedNatToTerm. }
                           *** apply forallI.
                               ---- apply closedNN.
                               ---- apply impTrans with (v#3 < n2t a)%fol.
                                    ++++ unfold LT at 1. 
                                         repeat rewrite (subFormulaRelation LNN). 
                                         simpl.
                                         rewrite (subTermNil LNN).
                                         **** apply impRefl.
                                         **** apply closedNatToTerm.
                                    ++++ apply boundedLT. intros n H1. 
                                         repeat rewrite (subFormulaId LNN).
                                         repeat first
                                          [ rewrite subExistSpecial; [| discriminate ]
                                          | rewrite subForallSpecial; [| discriminate ]
                                          | rewrite (subFormulaAnd LNN)
                                          | rewrite (subFormulaImp LNN) ].
                                         apply existI with (n2t (f (S n))).
                                         repeat first
                                          [ rewrite subExistSpecial; [| discriminate ]
                                          | rewrite subForallSpecial; [| discriminate ]
                                          | rewrite (subFormulaAnd LNN)
                                          | rewrite (subFormulaImp LNN) ].
                                         apply existI with (n2t (f n)).
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
                                                  (substF6  βR
                                                    1 (var 3)  
                                                    2 (n2t x)
                                                    0 (var 1) 
                                                    3 (n2t n)
                                                    0 (n2t (f n.+1))
                                                    1 (n2t (f n))).
                                              { apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                apply (subFormulaExch LNN).
                                                - discriminate.
                                                - apply closedNatToTerm.
                                                - intro H6. induction H6 as [H6 | H6].
                                                  + discriminate H6.
                                                  + elim H6. }
                                              { apply
                                                 impE
                                                  with
                                                    (substF6 βR
                                                       1 (var 3)
                                                       2 (n2t x)
                                                       3 (n2t n)
                                                       0 (var 1)
                                                       0 (n2t (f n.+1))
                                                       1 (n2t (f n))).
                                                - apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                  apply (subFormulaExch LNN).
                                                  + discriminate.
                                                  + apply closedNatToTerm.
                                                  + intros [H6 | H6].
                                                    * discriminate H6.
                                                    * elim H6.
                                                - apply impE with
                                                      (substF5 βR
                                                         1 (var 3)
                                                         2 (n2t x)
                                                         3 (n2t n)
                                                         0 (var 1)
                                                         1 (n2t (f n))).
                                                  + apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaNil LNN). intro H6.
                                                    destruct (freeVarSubFormula3 _ _ _ _ _ H6) as [H7 | H7].
                                                    * elim (in_remove_neq _ _ _ _ _ H7). reflexivity.
                                                    * destruct H7 as [H7 | H7].
                                                      -- discriminate H7.
                                                      -- elim H7.
                                                  + apply impE with
                                                        (substF5 βR 
                                                           2 (n2t x)
                                                           1 (var 3)
                                                           3 (n2t n)
                                                           0 (var 1)
                                                           1 (n2t (f n))).
                                                    * apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                      apply (subFormulaExch LNN).
                                                      -- discriminate.
                                                      -- intro H6. destruct H6 as [H6 | H6].
                                                         ++ discriminate H6.
                                                         ++ elim H6.
                                                      -- apply closedNatToTerm.
                                                    * apply
                                                       impE
                                                        with
                                                          (substF4 βR 
                                                             2 (n2t x)
                                                             1 (n2t n)
                                                             0 (var 1)
                                                             1 (n2t (f n))).
                                                      -- apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                         apply (subFormulaTrans LNN). intro H6.
                                                         assert
                                                          (H7: In 3
                                                             (freeVarF (substF βR 2 (n2t x)))).
                                                         { eapply in_remove. apply H6. }
                                                         destruct (freeVarSubFormula3 _ _ _ _ _ H7) as [H8 | H8].
                                                         ++ elim (proj1 (Nat.le_ngt 3 2)).
                                                            ** apply H4. eapply in_remove. apply H8.
                                                            ** repeat constructor.
                                                         ++ elim (closedNatToTerm _ _ H8).
                                                      -- apply impE with
                                                             (substF2 (v#0 = n2t (β x n))%fol
                                                                0 (var 1)
                                                                1 (n2t (f n))).
                                                         ++ apply iffE2;repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                            apply H5.
                                                         ++ repeat rewrite (subFormulaEqual LNN). simpl.
                                                            repeat rewrite (subTermNil LNN (n2t (β x n))).
                                                            ** rewrite H2. apply eqRefl. apply Nat.lt_lt_succ_r. apply H1.
                                                            ** apply closedNatToTerm.
                                                            ** apply closedNatToTerm. }
                                         **** apply andI.
                                              { destruct H0 as (H0, H4). simpl in H4.
                                                apply
                                                 impE
                                                  with
                                                    (substF4 B 
                                                       2 (var 3)
                                                       3 (n2t n)
                                                       0 (n2t (f (S n)))
                                                       1 (n2t (f n))).
                                                - apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                  apply (subFormulaNil LNN). intro H5.
                                                  destruct (freeVarSubFormula3 _ _ _ _ _ H5) as [H6 | [H6 | H6]].
                                                  + elim (in_remove_neq _ _ _ _ _ H6). reflexivity.
                                                  + discriminate H6.
                                                  + elim H6.
                                                - apply
                                                   impE
                                                    with
                                                      (substF3 B 
                                                         2 (n2t n)
                                                         0 (n2t (f (S n)))
                                                         1 (n2t (f n))).
                                                  + apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaTrans LNN). intro H5. elim (proj1 (Nat.le_ngt 3 2)).
                                                    * apply H0. eapply in_remove. apply H5.
                                                    * repeat constructor.
                                                  + apply impE with
                                                        (substF3 B 
                                                           2 (n2t n)
                                                           1 (n2t (f n))
                                                           0 (n2t (f (S n)))).
                                                    * apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                      apply (subFormulaExch LNN).
                                                      -- discriminate.
                                                      -- apply closedNatToTerm.
                                                      -- apply closedNatToTerm.
                                                    * apply
                                                       impE
                                                        with
                                                          (substF  (equal (var 0) (n2t (h n (f n)))) 0
                                                             (n2t (f (S n)))).
                                                      -- apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                         apply H4.
                                                      -- rewrite (subFormulaEqual LNN). simpl. rewrite (subTermNil LNN).
                                                         ++ unfold f. simpl. apply eqRefl.
                                                         ++ apply closedNatToTerm. }
                                              { apply impE with
                                                    (substF5  βR 
                                                       2 (n2t x)
                                                       1 (Succ (var 3))
                                                       3 (n2t n)
                                                       0 (n2t (f (S n)))
                                                       1 (n2t (f n))).
                                                - apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                  apply (subFormulaExch LNN).
                                                  + discriminate.
                                                  + simpl. intro H4. lia.
                                                  + apply closedNatToTerm.
                                                - apply impE with
                                                      (substF5 βR 
                                                         2 (n2t x)
                                                         3 (n2t n)
                                                         1 (n2t (S n))
                                                         0 (n2t (f (S n)))
                                                         1 (n2t (f n))).
                                                  + apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    replace (n2t (S n)) with
                                                     (substT (Succ (var 3)) 3 (n2t n)).
                                                    * apply (subSubFormula LNN).
                                                      -- discriminate.
                                                      -- apply closedNatToTerm.
                                                    * simpl. reflexivity.
                                                  + destruct repBeta as (H4, H5).
                                                    apply
                                                     impE
                                                      with
                                                        (substF4 βR 
                                                           2 (n2t x)
                                                           1 (n2t (S n))
                                                           0 (n2t (f (S n)))
                                                           1 (n2t (f n))).
                                                    * apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                      apply (subFormulaNil LNN). intro H6.
                                                      destruct (freeVarSubFormula3 _ _ _ _ _ H6) as [H7 | H7].
                                                      -- elim (proj1 (Nat.le_ngt  3 2)).
                                                         ++ apply H4. eapply in_remove. apply H7.
                                                         ++ repeat constructor.
                                                      -- elim (closedNatToTerm _ _ H7).
                                                    * simpl in H5.
                                                      apply
                                                       impE
                                                        with
                                                          (substF2
                                                              (equal (var 0) (n2t (β x (S n))))
                                                              0  (n2t (f (S n)))
                                                              1 (n2t (f n))).
                                                      -- apply iffE2. 
                                                         repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                         apply H5.
                                                      -- repeat rewrite (subFormulaEqual LNN). simpl.
                                                         repeat
                                                          (rewrite (subTermNil LNN (n2t (β x (S n))));
                                                            [| apply closedNatToTerm ]).
                                                         rewrite (subTermNil LNN).
                                                         ++ rewrite H2.
                                                            ** apply eqRefl.
                                                            ** apply (proj1 (Nat.succ_lt_mono n a)). apply H1.
                                                         ++ apply closedNatToTerm. }
                       +++ unfold primRecPiFormulaHelp.
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
                               ---- apply closedNN.
                               ---- destruct H as (H, H1). simpl in H1.
                                    apply
                                     impTrans
                                      with
                                        (substF2 (equal (var 0) (n2t g))
                                           1 (n2t a)
                                           2 (n2t x)).
                                    ++++ apply iffE1. apply (reduceSub LNN).
                                         **** apply closedNN.
                                         **** apply (reduceSub LNN).
                                              { apply closedNN. }
                                              { apply H1. }
                                    ++++ repeat rewrite (subFormulaEqual LNN). simpl.
                                         repeat
                                          (rewrite (subTermNil LNN (n2t g)); [| apply closedNatToTerm ]).
                                         apply impI.
                                         rewrite <-
                                          (subFormulaId LNN
                                             (substF4 βR
                                                1 Zero
                                                2 (var 2)
                                                1 (n2t a)
                                                2 (n2t x)) 0).
                                         apply
                                          impE
                                            with
                                             (substF 
                                                (substF 
                                                   (substF 
                                                      (substF 
                                                         (substF βR 1 Zero) 2 
                                                         (var 2)) 1 (n2t a)) 2 (n2t x)) 0 
                                                (n2t g)).
                                         **** apply (subWithEquals LNN). apply eqSym. apply Axm; right; constructor.
                                         **** apply sysWeaken. clear H1. destruct repBeta as (H1, H4). simpl in H4.
                                              rewrite (subFormulaId LNN).
                                              apply impE with
                                                  (substF3  βR
                                                     1 Zero 
                                                     2 (n2t x)
                                                     0 (n2t (f 0))).
                                              { apply iffE2. apply (reduceSub LNN).
                                                - apply closedNN.
                                                - apply (reduceSub LNN). apply closedNN. 
                                                  apply (subFormulaNil LNN).
                                                  intro H5. destruct (freeVarSubFormula3 _ _ _ _ _ H5) as [H6 | H6].
                                                  + elim (in_remove_neq _ _ _ _ _ H6). reflexivity.
                                                  + elim H6. }
                                              { apply impE with
                                                    (substF (equal (var 0) (n2t (β x 0))) 0
                                                       (n2t (f 0))).
                                                - apply iffE2. apply (reduceSub LNN).
                                                  + apply closedNN.
                                                  + apply iffTrans with
                                                        (substF2  βR 
                                                           2 (n2t x)
                                                           1 (n2t 0)).
                                                    * apply (subFormulaExch LNN).
                                                      -- discriminate.
                                                      -- apply closedNatToTerm.
                                                      -- apply closedNatToTerm.
                                                    * apply H4.
                                                - rewrite (subFormulaEqual LNN). simpl. rewrite (subTermNil LNN).
                                                  + rewrite H2. apply eqRefl. apply Nat.lt_0_succ.
                                                  + apply closedNatToTerm. }
                           *** apply forallI.
                               ---- apply closedNN.
                               ---- apply impTrans with (LT (var 3) (n2t a)).
                                    ++++ unfold LT at 1. repeat rewrite (subFormulaRelation LNN). simpl.
                                         rewrite (subTermNil LNN).
                                         **** apply impRefl.
                                         **** apply closedNatToTerm.
                                    ++++ apply boundedLT. intros n H1. repeat rewrite (subFormulaId LNN).
                                         repeat first
                                          [ rewrite subExistSpecial; [| discriminate ]
                                          | rewrite subForallSpecial; [| discriminate ]
                                          | rewrite (subFormulaAnd LNN)
                                          | rewrite (subFormulaImp LNN) ].
                                         apply forallI.
                                         **** apply closedNN.
                                         **** apply forallI.
                                              { apply closedNN. }
                                              { apply impTrans with (equal (var 1) (n2t (f n))).
                                                - destruct repBeta as (H4, H5). simpl in H5.
                                                  apply impTrans with
                                                      (substF4 βR 
                                                         1 (var 3)
                                                         2 (n2t x)
                                                         0 (var 1)
                                                         3 (n2t n)).
                                                  apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                  + apply (subFormulaExch LNN).
                                                    * discriminate.
                                                    * intro H6. destruct H6 as [H6 | H6].
                                                      -- discriminate H6.
                                                      -- elim H6.
                                                    * apply closedNatToTerm.
                                                  + apply
                                                     impTrans
                                                      with
                                                        (substF4 βR 
                                                           1 (var 3)
                                                           2 (n2t x)
                                                           3 (n2t n)
                                                           0 (var 1)).
                                                    * apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                      apply (subFormulaExch LNN).
                                                      -- discriminate.
                                                      -- intro H6. destruct H6 as [H6 | H6].
                                                         ++ discriminate H6.
                                                         ++ elim H6.
                                                      -- apply closedNatToTerm.
                                                    * apply
                                                       impTrans
                                                        with
                                                          (substF4 βR 
                                                             2 (n2t x) 
                                                             1 (var 3)
                                                             3 (n2t n)
                                                             0 (var 1)).
                                                      -- apply iffE2;
                                                           repeat (apply (reduceSub LNN);
                                                                   [ apply closedNN |]).
                                                         apply (subFormulaExch LNN).
                                                         ++ discriminate.
                                                         ++ apply closedNatToTerm.
                                                         ++ intro H6. destruct H6 as [H6 | H6].
                                                            ** discriminate H6.
                                                            ** elim H6.
                                                      -- apply impTrans with
                                                             (substF3 βR 
                                                                2 (n2t x)
                                                                1 (n2t n)
                                                                0 (var 1)).
                                                         ++ apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                            apply (subFormulaTrans LNN). intro H6.
                                                            assert
                                                             (H7: In 3
                                                                (freeVarF (substF βR 2 (n2t x)))).
                                                            { eapply in_remove. apply H6. }
                                                            destruct (freeVarSubFormula3 _ _ _ _ _ H7) as [H8 | H8].
                                                            ** elim (proj1 (Nat.le_ngt 3 2)). apply H4. eapply in_remove.
                                                               --- apply H8.
                                                               --- repeat constructor.
                                                            ** elim (closedNatToTerm _ _ H8).
                                                         ++ apply
                                                             impTrans
                                                              with
                                                                (substF (equal (var 0) (n2t (β x n))) 0 (var 1)).
                                                            ** apply iffE1. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                               apply H5.
                                                            ** repeat rewrite (subFormulaEqual LNN). simpl.
                                                               repeat rewrite (subTermNil LNN (n2t (β x n))).
                                                               --- rewrite H2.
                                                                    +++ apply impRefl.
                                                                    +++ apply Nat.lt_lt_succ_r. apply H1.
                                                               --- apply closedNatToTerm.
                                                - rewrite <-
                                                   (subFormulaId LNN
                                                      (impH 
                                                         (substF3 B 
                                                            2 (var 3) 
                                                            2 (n2t x)
                                                            3 (n2t n))
                                                         (substF3 βR 
                                                            1 (Succ (var 3)) 
                                                            2 (n2t x)
                                                            3 (n2t n))) 1).
                                                  apply impI.
                                                  apply impE with
                                                      (substF
                                                         (impH 
                                                            (substF3 B 
                                                               2 (var 3)
                                                               2 (n2t x)
                                                               3 (n2t n))
                                                            (substF3 βR
                                                               1 (Succ (var 3)) 
                                                               2 (n2t x)
                                                               3 (n2t n))) 1
                                                         (n2t (f n))).
                                                  + apply (subWithEquals LNN). apply eqSym. apply Axm; right; constructor.
                                                  + apply sysWeaken. rewrite (subFormulaImp LNN).
                                                    apply impTrans with (equal (var 0) (n2t (f (S n)))).
                                                    * destruct H0 as (H0, H4). simpl in H4.
                                                      apply impTrans with
                                                          (substF3 B 
                                                             2 (var 3)
                                                             3 (n2t n) 
                                                             1 (n2t (f n))).
                                                      -- apply iffE1. 
                                                         repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                         apply (subFormulaNil LNN). intro H5.
                                                         destruct (freeVarSubFormula3 _ _ _ _ _ H5) as [H6 | [H6 | H6]].
                                                         ++ elim (in_remove_neq _ _ _ _ _ H6). reflexivity.
                                                         ++ discriminate H6.
                                                         ++ elim H6.
                                                      -- apply
                                                          impTrans
                                                           with
                                                             (substF2  B 2 (n2t n) 1 (n2t (f n))).
                                                         ++ apply iffE1. 
                                                            repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                            apply (subFormulaTrans LNN). 
                                                            intro H5; elim (proj1 (Nat.le_ngt 3 2)).
                                                            ** apply H0. eapply in_remove. apply H5.
                                                            ** repeat constructor.
                                                         ++ unfold f. simpl. apply iffE1. apply H4.
                                                    * rewrite <-
                                                       (subFormulaId LNN
                                                          (substF4 βR 
                                                             1 (Succ (var 3)) 
                                                             2 (n2t x)
                                                             3 (n2t n)
                                                             1 (n2t (f n))) 0).
                                                      apply impI.
                                                      apply
                                                       impE
                                                        with
                                                          (substF5 βR 
                                                             1 (Succ (var 3))
                                                             2 (n2t x)
                                                             3 (n2t n)
                                                             1 (n2t (f n))
                                                             0 (n2t (f (S n)))).
                                                      -- apply (subWithEquals LNN). 
                                                         apply eqSym. apply Axm; right; constructor.
                                                      -- apply sysWeaken.
                                                         apply impE with
                                                             (substF5 βR 
                                                                2 (n2t x)
                                                                1 (Succ (var 3))
                                                                3 (n2t n)
                                                                1  (n2t (f n))
                                                                0 (n2t (f (S n)))).
                                                         ++ apply iffE2. 
                                                            repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                            apply (subFormulaExch LNN).
                                                            ** discriminate.
                                                            ** simpl. lia.
                                                            ** apply closedNatToTerm.
                                                         ++ apply impE with
                                                                (substF5 βR 
                                                                   2 (n2t x)
                                                                   3 (n2t n)
                                                                   1 (n2t (S n))
                                                                   1 (n2t (f n))
                                                                   0 (n2t (f (S n)))).
                                                            ** apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                               replace (n2t (S n)) with
                                                                (substT (Succ (var 3)) 3 (n2t n)).
                                                               --- apply (subSubFormula LNN).
                                                                   +++ discriminate.
                                                                   +++ apply closedNatToTerm.
                                                               --- simpl. reflexivity.
                                                            ** destruct repBeta as (H4, H5).
                                                               apply impE with
                                                                   (substF4 βR
                                                                      2 (n2t x)
                                                                      1 (n2t (S n))
                                                                      1 (n2t (f n))
                                                                      0 (n2t (f (S n)))).
                                                               --- apply iffE2. 
                                                                   repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                   apply (subFormulaNil LNN). intro H6.
                                                                   destruct (freeVarSubFormula3 _ _ _ _ _ H6) as [H7 | H7].
                                                                   +++ elim (proj1 (Nat.le_ngt 3 2)).
                                                                       *** apply H4. eapply in_remove. apply H7.
                                                                       *** repeat constructor.
                                                                   +++ elim (closedNatToTerm _ _ H7).
                                                               --- simpl in H5.
                                                                   apply impE with
                                                                     (substF2 (equal (var 0) (n2t (β x (S n))))
                                                                        1  (n2t (f n))
                                                                        0 (n2t (f (S n)))).
                                                                   +++ apply iffE2. 
                                                                       repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                       apply H5.
                                                                   +++ repeat rewrite (subFormulaEqual LNN). simpl.
                                                                       repeat
                                                                        (rewrite (subTermNil LNN (n2t (β x (S n))));
                                                                          [| apply closedNatToTerm ]).
                                                                       rewrite H2.
                                                                       *** apply eqRefl.
                                                                       *** repeat rewrite <-  Nat.succ_lt_mono. apply H1. }

                       +++ intros b H1. 
                         assert (H4: forall z : nat, decidable (f z = β b z)).
                         { unfold decidable. intros z. destruct (eq_nat_dec (f z) (β b z)); auto. }
                         decompose record
                          (notBoundedForall 
                             (fun z : nat => f z = β b z) (S a) H4 (H3 b H1))  /r;
                           intros x0 H6 H7.
                         apply impE with 
                           (notH (equal (n2t (f x0)) (n2t (β b x0)))).
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
                             ---- apply
                                   impE
                                    with
                                      (existH 0
                                         (andH
                                            (substF  (substF  A 1 (n2t a)) 2
                                               (n2t b))
                                            (substF4 βR
                                               1 Zero
                                               2 (var 2)
                                               1 (n2t a)
                                               2 (n2t b)))).
                                  ++++ apply sysWeaken. apply impI. apply existSys.
                                       **** apply closedNN.
                                       **** intro H1. destruct (in_app_or _ _ _ H1) as [H2 | H2].
                                            { elim (closedNatToTerm _ _ H2). }
                                            { elim (closedNatToTerm _ _ H2). }
                                       **** apply eqTrans with (var 0).
                                            { destruct H as (H, H1). simpl in H1. apply eqSym. unfold f; simpl.
                                              apply impE with A.
                                              - apply sysWeaken. apply iffE1. assumption.
                                              - apply impE with
                                                    (substF2  A 1 (n2t a) 2 (n2t b)).
                                                + apply sysWeaken. apply iffE1.
                                                  apply iffTrans with (substF  A 2 (n2t b)).
                                                  * repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaNil LNN). intro H2. elim (proj1 (Nat.le_ngt 1 0)); auto.
                                                  * apply (subFormulaNil LNN). intro H2. elim (proj1 (Nat.le_ngt 2 0)); auto.
                                                + eapply andE1. apply Axm; right; constructor. }
                                            { destruct repBeta as (H1, H2). simpl in H2.
                                              apply impE with
                                                  (substF4 βR
                                                     1 Zero
                                                     2 (var 2)
                                                     1 (n2t a)
                                                     2 (n2t b)).
                                              - apply sysWeaken. apply iffE1.
                                                apply iffTrans with
                                                    (substF2  
                                                       βR 2 (n2t b) 1 (n2t 0)).
                                                + rewrite (subFormulaId LNN).
                                                  apply iffTrans with
                                                      (substF2  βR 1 Zero 2 (n2t b)).
                                                  * repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaNil LNN). intro H3.
                                                    destruct (freeVarSubFormula3 _ _ _ _ _ H3) as [H4 | H4].
                                                    -- elim (in_remove_neq _ _ _ _ _ H4); reflexivity.
                                                    -- apply H4.
                                                  * apply (subFormulaExch LNN).
                                                    -- discriminate.
                                                    -- apply closedNatToTerm.
                                                    -- apply closedNatToTerm.
                                                + apply H2.
                                              - eapply andE2. apply Axm; right; constructor. }
                                  ++++ eapply andE1. apply Axm; right; constructor.
                             ---- apply impE with (equal (n2t (f x0)) (n2t (β b x0))); [| apply Hrecx0 ].
                                  ++++ clear Hrecx0.
                                       apply impE with
                                           (forallH 3
                                              (impH 
                                                 (substF2 
                                                    (LT (var 3) (var 1)) 1 (n2t a) 2 (n2t b))
                                                 (existH 0
                                                    (existH 1
                                                       (andH
                                                          (substF4 βR
                                                             1 (var 3) 
                                                             2 (var 2)
                                                             0 (var 1)
                                                             2 (n2t b))
                                                          (andH 
                                                             (substF2 B 2 (var 3) 2 (n2t b))
                                                             (substF3 βR 
                                                                1 (Succ (var 3)) 
                                                                2 (var 2) 
                                                                2 (n2t b))))))));
                                        [| eapply andE2; apply Axm; right; constructor ].
                                       apply sysWeaken.
                                       apply
                                        impTrans
                                         with
                                           (substF 
                                              (impH 
                                                 (substF2 (LT (var 3) (var 1)) 
                                                    1 (n2t a)
                                                    2 (n2t b))
                                                 (existH 0
                                                    (existH 1
                                                       (andH 
                                                          (substF4 βR
                                                             1 (var 3) 
                                                             2 (var 2)
                                                             0 (var 1)
                                                             2 (n2t b))
                                                          (andH
                                                             (substF2 B 2 (var 3) 2 (n2t b))
                                                             (substF3 βR 
                                                                1 (Succ (var 3))
                                                                2 (var 2)
                                                                2 (n2t b))))))) 
                                              3 (n2t x0)).
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
                                                         (substF5 βR
                                                            1 (var 3)
                                                            2 (var 2)
                                                            0 (var 1)
                                                            2 (n2t b)
                                                            3 (n2t x0))
                                                         (andH
                                                            (substF3 B
                                                               2 (var 3)
                                                               2 (n2t b)
                                                               3 (n2t x0))
                                                            (substF4 βR 
                                                               1 (Succ (var 3))
                                                               2 (var 2)
                                                               2 (n2t b)
                                                               3 (n2t x0)))))).
                                            { apply impI.
                                              apply impE with
                                                  (substF3 
                                                      (LT (var 3) (var 1))
                                                      1 (n2t a)
                                                      2 (n2t b)
                                                      3 (n2t x0)).
                                              - apply Axm; right; constructor.
                                              - apply sysWeaken. unfold LT. 
                                                repeat rewrite (subFormulaRelation LNN). simpl.
                                                repeat (rewrite (subTermNil LNN (n2t a));
                                                        [| apply closedNatToTerm ]).
                                                fold (LT (n2t x0) (n2t a)). 
                                                apply natLT. now rewrite Nat.succ_lt_mono. }
                                            { apply impI.
                                              assert
                                               (H1:forall n : nat,
                                                ~
                                                In n
                                                  (freeVarF
                                                     (impH (equal (n2t (f x0)) (n2t (β b x0)))
                                                        (equal (n2t (f (S x0))) (n2t (β b (S x0))))))).
                                              { simpl. intros n H1.
                                                destruct (in_app_or _ _ _ H1) as [H2 | H2]; induction (in_app_or _ _ _ H2) as [H3 | H3];
                                                  elim (closedNatToTerm _ _ H3). }
                                              apply existSys.
                                              - apply closedNN.
                                              - apply H1.
                                              - apply existSys.
                                                + apply closedNN.
                                                + apply H1.
                                                + unfold f at 2; simpl. fold (f x0) in |- *.
                                                  apply impE with (equal (var 1) (n2t (β b x0))).
                                                  * apply impI. apply impE with (equal (var 0) (n2t (h x0 (β b x0)))).
                                                    -- repeat apply impI. apply eqTrans with (var 0).
                                                       ++ apply eqTrans with (n2t (h x0 (β b x0))).
                                                          ** destruct (eq_nat_dec (f x0) (β b x0)) as [a0 | b0].
                                                             --- rewrite a0. apply eqRefl.
                                                             --- apply contradiction with (equal (n2t (f x0)) (n2t (β b x0))).
                                                                 +++ apply Axm; right; constructor.
                                                                 +++ do 4 apply sysWeaken. apply natNE. auto.
                                                          ** apply eqSym. apply Axm; left; right; constructor.
                                                       ++ apply
                                                           impE
                                                            with
                                                              (substF4 βR
                                                                 1 (Succ (var 3))
                                                                 2 (var 2)
                                                                 2 (n2t b)
                                                                 3 (n2t x0)).
                                                          ** do 4 apply sysWeaken. apply iffE1. 
                                                             destruct repBeta as (H2, H3).
                                                             simpl in H3.
                                                             apply
                                                              iffTrans
                                                               with
                                                                 (substF2  βR
                                                                    2 (n2t b)
                                                                    1 (n2t (S x0))).
                                                             --- rewrite (subFormulaId LNN).
                                                                 apply
                                                                  iffTrans
                                                                   with
                                                                     (substF3 βR
                                                                        2 (n2t b)
                                                                        1 (Succ (var 3))
                                                                        3 (n2t x0)).
                                                                 +++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                     apply (subFormulaExch LNN).
                                                                     *** discriminate.
                                                                     *** simpl; lia.
                                                                     *** apply closedNatToTerm.
                                                                 +++ apply iffTrans with
                                                                         (substF3 βR
                                                                            2 (n2t b)
                                                                            3 (n2t x0)
                                                                            1 (substT (Succ (var 3)) 3 
                                                                                 (n2t x0))).
                                                                     *** apply (subSubFormula LNN).
                                                                         ---- discriminate.
                                                                         ---- apply closedNatToTerm.
                                                                     *** simpl; apply iffTrans with
                                                                             (substF2  βR
                                                                                2 (n2t b) 
                                                                                1 (substT (Succ (var 3)) 3 (n2t x0))).
                                                                         ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                              apply (subFormulaNil LNN).
                                                                              intro H4. destruct (freeVarSubFormula3 _ _ _ _ _ H4) as [H5 | H5].
                                                                              ++++ elim (proj1 (Nat.le_ngt 3 2)).
                                                                                   **** apply H2. eapply in_remove. apply H5.
                                                                                   **** repeat constructor.
                                                                              ++++ elim (closedNatToTerm _ _ H5).
                                                                         ---- apply iffRefl.
                                                             --- apply H3.
                                                          ** eapply andE2. eapply andE2. apply Axm; do 3 left; right; constructor.
                                                     -- apply impE with
                                                            (substF4 B
                                                               2 (var 3)
                                                               2 (n2t b)
                                                               3 (n2t x0)
                                                               1 (n2t (β b x0))).
                                                        ++ do 2 apply sysWeaken. destruct H0 as (H0, H2). simpl in H2. apply iffE1.
                                                           apply
                                                            iffTrans
                                                             with
                                                               (substF2  B
                                                                  2 (n2t x0) 
                                                                  1 (n2t (β b x0))).
                                                           ** apply iffTrans with
                                                                  (substF3  B
                                                                     2 (var 3)
                                                                     3 (n2t x0)
                                                                     1 (n2t (β b x0))).
                                                              --- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                  apply (subFormulaNil LNN). intro H3.
                                                                  destruct (freeVarSubFormula3 _ _ _ _ _ H3) as [H4 | H4].
                                                                  +++ elim (in_remove_neq _ _ _ _ _ H4). reflexivity.
                                                                  +++ destruct H4 as [H4 | H4].
                                                                      *** discriminate H4.
                                                                      *** apply H4.
                                                              --- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                  apply (subFormulaTrans LNN). intro H3. elim (proj1 (Nat.le_ngt 3 2)).
                                                                  +++ apply H0. eapply in_remove. apply H3.
                                                                  +++ repeat constructor.
                                                           ** apply H2.
                                                        ++ apply impE with
                                                               (substF4 B
                                                                  2 (var 3)
                                                                  2 (n2t b)
                                                                  3 (n2t x0)
                                                                  1 (var 1)).
                                                           ** apply (subWithEquals LNN). apply Axm; right; constructor.
                                                           ** repeat rewrite (subFormulaId LNN). eapply andE1. eapply andE2.
                                                              apply Axm; left; right; constructor.
                                                  * apply impE with
                                                        (substF5 βR
                                                           1 (var 3)
                                                           2 (var 2)
                                                           0 (var 1)
                                                           2 (n2t b)
                                                           3 (n2t x0)).
                                                    -- apply sysWeaken. apply iffE1. destruct repBeta as (H2, H3). simpl in H3.
                                                       apply
                                                        iffTrans
                                                         with
                                                           (substF  (equal (var 0) (n2t (β b x0))) 0 (var 1)).
                                                       ++ rewrite (subFormulaId LNN).
                                                          apply iffTrans with
                                                              (substF4 βR
                                                                 1 (var 3)
                                                                 2 (n2t b)
                                                                 0 (var 1)
                                                                 3 (n2t x0)).
                                                          ** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                             apply (subFormulaExch LNN).
                                                             --- discriminate.
                                                             --- intros [H4 | H4].
                                                                 +++ discriminate H4.
                                                                 +++ apply H4.
                                                             --- apply closedNatToTerm.
                                                          ** apply iffTrans with
                                                                 (substF4 βR 
                                                                    1 (var 3)
                                                                    2 (n2t b)
                                                                    3 (n2t x0)
                                                                    0 (var 1)).
                                                             --- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                 apply (subFormulaExch LNN).
                                                                 +++ discriminate.
                                                                 +++ intros [H4 | H4].
                                                                     *** discriminate H4.
                                                                     *** apply H4.
                                                                 +++ apply closedNatToTerm.
                                                             --- apply (reduceSub LNN).
                                                                 +++ apply closedNN.
                                                                 +++ apply iffTrans with
                                                                         (substF3 βR
                                                                            2 (n2t b)
                                                                            1 (var 3)
                                                                            3 (n2t x0)).
                                                                     *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                         apply (subFormulaExch LNN).
                                                                         ---- discriminate.
                                                                         ---- intros [H4 | H4].
                                                                              ++++ discriminate H4.
                                                                              ++++ apply H4.
                                                                         ---- apply closedNatToTerm.
                                                                     *** apply iffTrans with
                                                                             (substF2 βR
                                                                                2 (n2t b)
                                                                                1 (n2t x0)).
                                                                         ---- repeat (apply (reduceSub LNN); [apply closedNN |]).
                                                                              apply (subFormulaTrans LNN). intro H4.
                                                                              assert
                                                                               (H5: In 3
                                                                                  (freeVarF (substF  βR 2 (n2t b)))).
                                                                              { eapply in_remove. apply H4. }
                                                                              destruct (freeVarSubFormula3 _ _ _ _ _ H5) as [H7 | H7].
                                                                              ++++ elim (proj1 (Nat.le_ngt 3 2)).
                                                                                   **** apply H2. eapply in_remove. apply H7.
                                                                                   **** repeat constructor.
                                                                              ++++ elim (closedNatToTerm _ _ H7).
                                                                         ---- apply H3.
                                                       ++ rewrite (subFormulaEqual LNN). simpl. rewrite subTermNil.
                                                          ** apply iffRefl.
                                                          ** apply closedNatToTerm.
                                                    -- eapply andE1. apply Axm; right; constructor. }
                                  ++++ apply Nat.lt_lt_succ_r. now rewrite Nat.succ_lt_mono. 
                         *** apply natNE. auto.
                     +++ intros b H1. 
                         assert (H4: forall z : nat, decidable (f z = β b z)).
                         { unfold decidable. intros z. destruct (eq_nat_dec (f z) (β b z)); auto. }
                         decompose record
                          (notBoundedForall
                             (fun z : nat => f z = β b z) (S a) H4 (H3 b H1)) /r;
                           intros x0 H6 H7.
                         apply impE with 
                           (notH (equal (n2t (f x0)) (n2t (β b x0)))).
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
                             ---- apply
                                   impE
                                    with
                                      (forallH 0
                                         (impH 
                                            (substF2  A 1 (n2t a) 2 (n2t b))
                                            (substF4 βR
                                               1 Zero
                                               2 (var 2)
                                               1 (n2t a)
                                               2 (n2t b)))).
                                  ++++ apply sysWeaken.
                                       apply impTrans with
                                           (substF 
                                              (impH 
                                                 (substF2  A 1 (n2t a) 2 (n2t b))
                                                 (substF4 βR 
                                                    1 Zero
                                                    2 (var 2)
                                                    1 (n2t a)
                                                    2 (n2t b)))
                                              0 (n2t (f 0))).
                                       **** apply impI. apply forallE. apply Axm; right; constructor.
                                       **** apply impI. rewrite (subFormulaImp LNN).
                                            apply impE with
                                                (substF5 βR
                                                   1 Zero
                                                   2 (var 2)
                                                   1 (n2t a)
                                                   2 (n2t b)
                                                   0 (n2t (f 0))).
                                            { apply sysWeaken.
                                              apply
                                               impTrans
                                                with
                                                  (substF  (equal (var 0) (n2t (β b 0))) 0
                                                     (n2t (f 0))).
                                              - apply iffE1. apply (reduceSub LNN).
                                                + apply closedNN.
                                                + rewrite (subFormulaId LNN). destruct repBeta as (H1, H2). simpl in H2.
                                                  apply iffTrans with
                                                      (substF2 βR 2 (n2t b) 1 (n2t 0)).
                                                  * apply iffTrans with
                                                        (substF2 βR 1 Zero 2 (n2t b)).
                                                    -- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                       apply (subFormulaNil LNN). intro H3.
                                                       destruct (freeVarSubFormula3 _ _ _ _ _ H3) as [H4 | H4].
                                                       ++ elim (in_remove_neq _ _ _ _ _ H4); reflexivity.
                                                       ++ apply H4.
                                                    -- apply (subFormulaExch LNN).
                                                       ++ discriminate.
                                                       ++ apply closedNatToTerm.
                                                       ++ apply closedNatToTerm.
                                                  * apply H2.
                                              - rewrite (subFormulaEqual LNN). simpl. rewrite (subTermNil LNN).
                                                + apply impRefl.
                                                + apply closedNatToTerm. }
                                            { apply impE  with
                                                  (substF3 A 1 (n2t a) 2 (n2t b) 0 (n2t (f 0))).
                                              - apply Axm; right; constructor.
                                              - apply sysWeaken.
                                                apply impE with
                                                    (substF  (equal (var 0) (n2t (f 0))) 0 (n2t (f 0))).
                                                + apply iffE2. apply (reduceSub LNN); [ apply closedNN |].
                                                  destruct H as (H, H1). simpl in H1. unfold f; simpl.
                                                  apply iffTrans with A; [| assumption ].
                                                  apply iffTrans with (substF  A 2 (n2t b)).
                                                  * repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaNil LNN). intro H2. elim (proj1 (Nat.le_ngt 1 0)); auto.
                                                  * apply (subFormulaNil LNN). intro H2. elim (proj1 (Nat.le_ngt 2 0)); auto.
                                                + rewrite (subFormulaEqual LNN). simpl. rewrite (subTermNil LNN).
                                                  * apply eqRefl.
                                                  * apply closedNatToTerm. }
                                  ++++ eapply andE1. apply Axm; right; constructor.
                             ---- apply impE with (equal (n2t (f x0)) (n2t (β b x0))); [| apply Hrecx0 ].
                                  ++++ clear Hrecx0.
                                       apply impE with
                                           (forallH 3
                                              (impH 
                                                 (substF2 (LT (var 3) (var 1))
                                                    1 (n2t a)
                                                    2 (n2t b))
                                                 (forallH 0
                                                    (forallH 1
                                                       (impH 
                                                          (substF4 βR
                                                             1 (var 3)
                                                             2 (var 2)
                                                             0 (var 1)
                                                             2 (n2t b))
                                                          (impH 
                                                             (substF2 B 2 (var 3) 2 (n2t b))
                                                             (substF3 βR
                                                                1 (Succ (var 3))
                                                                2 (var 2)
                                                                2 (n2t b))))))));
                                        [| eapply andE2; apply Axm; right; constructor ].
                                       apply sysWeaken.
                                       apply impTrans with
                                           (substF 
                                              (impH 
                                                 (substF2 (LT (var 3) (var 1)) 1 (n2t a) 2 (n2t b))
                                                 (forallH 0
                                                    (forallH 1
                                                       (impH
                                                          (substF4 βR
                                                             1 (var 3)
                                                             2 (var 2)
                                                             0 (var 1)
                                                             2 (n2t b))
                                                          (impH 
                                                             (substF 
                                                                (substF  B 2 (var 3)) 2
                                                                (n2t b))
                                                             (substF3 βR
                                                                1 (Succ (var 3))
                                                                2 (var 2)
                                                                2 (n2t b)))))))
                                              3 (n2t x0)).
                                       **** apply impI. apply forallE. apply Axm; right; constructor.
                                       **** repeat first
                                             [ rewrite subExistSpecial; [| discriminate ]
                                             | rewrite subForallSpecial; [| discriminate ]
                                             | rewrite (subFormulaAnd LNN)
                                             | rewrite (subFormulaImp LNN) ].
                                            apply impTrans with
                                                (forallH 0
                                                   (forallH 1
                                                      (impH 
                                                         (substF5 βR
                                                            1 (var 3)
                                                            2 (var 2)
                                                            0 (var 1)
                                                            2 (n2t b)
                                                            3 (n2t x0))
                                                         (impH 
                                                            (substF3 B
                                                               2 (var 3)
                                                               2 (n2t b)
                                                               3 (n2t x0))
                                                            (substF4 βR
                                                               1 (Succ (var 3))
                                                               2 (var 2)
                                                               2 (n2t b)
                                                               3 (n2t x0)))))).
                                            { apply impI.
                                              apply impE with
                                                  (substF3 (LT (var 3) (var 1))
                                                              1 (n2t a)
                                                              2 (n2t b)
                                                              3 (n2t x0)).
                                              - apply Axm; right; constructor.
                                              - apply sysWeaken. unfold LT. repeat rewrite (subFormulaRelation LNN). simpl.
                                                repeat (rewrite (subTermNil LNN (n2t a)); [| apply closedNatToTerm ]).
                                                fold (LT (n2t x0) (n2t a)). apply natLT. now apply Nat.succ_lt_mono. }
                                            { apply impTrans with
                                                  (substF 
                                                     (forallH 1
                                                        (impH 
                                                           (substF5 βR
                                                              1 (var 3)
                                                              2 (var 2)
                                                              0 (var 1)
                                                              2 (n2t b)
                                                              3 (n2t x0))
                                                           (impH
                                                              (substF3  B
                                                                 2 (var 3)
                                                                 2 (n2t b)
                                                                 3 (n2t x0))
                                                              (substF4 βR 
                                                                 1 (Succ (var 3))
                                                                 2 (var 2)
                                                                 2 (n2t b)
                                                                 3 (n2t x0))))) 
                                                     0 (n2t (f (S x0)))).
                                              - apply impI. apply forallE. apply Axm; right; constructor.
                                              - repeat first
                                                 [ rewrite subExistSpecial; [| discriminate ]
                                                 | rewrite subForallSpecial; [| discriminate ]
                                                 | rewrite (subFormulaAnd LNN)
                                                 | rewrite (subFormulaImp LNN) ].
                                                apply impTrans with
                                                    (substF 
                                                       (impH
                                                          (substF6  βR
                                                             1 (var 3)
                                                             2 (var 2)
                                                             0 (var 1)
                                                             2 (n2t b)
                                                             3 (n2t x0)
                                                             0 (n2t (f (S x0))))
                                                          (impH
                                                             (substF4 B
                                                                2 (var 3)
                                                                2 (n2t b)
                                                                3 (n2t x0)
                                                                0 (n2t (f (S x0))))
                                                             (substF5 βR
                                                                1 (Succ (var 3))
                                                                2 (var 2)
                                                                2 (n2t b)
                                                                3 (n2t x0)
                                                                0 (n2t (f (S x0))))))
                                                       1  (n2t (β b x0))).
                                                + apply impI. apply forallE. apply Axm; right; constructor.
                                                + repeat first
                                                   [ rewrite subExistSpecial; [| discriminate ]
                                                   | rewrite subForallSpecial; [| discriminate ]
                                                   | rewrite (subFormulaAnd LNN)
                                                   | rewrite (subFormulaImp LNN) ].
                                                  repeat apply impI.
                                                  apply impE with
                                                      (substF  (equal (var 0) (n2t (β b (S x0)))) 0
                                                         (n2t (f (S x0)))).
                                                  * rewrite (subFormulaEqual LNN). simpl. rewrite (subTermNil LNN).
                                                    -- apply impRefl.
                                                    -- apply closedNatToTerm.
                                                  * apply impE with
                                                        (substF6  βR
                                                           1 (Succ (var 3))
                                                           2 (var 2)
                                                           2 (n2t b)
                                                           3 (n2t x0)
                                                           0 (n2t (f (S x0)))
                                                           1 (n2t (β b x0))).
                                                    -- do 2 apply sysWeaken. apply iffE1.
                                                       apply
                                                        iffTrans
                                                         with
                                                           (substF6 βR 
                                                              1 (Succ (var 3))
                                                              2 (var 2)  (* ??? *)
                                                              2 (n2t b)
                                                              3 (n2t x0) 
                                                              1 (n2t (β b x0))
                                                              0 (n2t (f (S x0)))).
                                                       ++ apply (subFormulaExch LNN).
                                                          ** discriminate.
                                                          ** apply closedNatToTerm.
                                                          ** apply closedNatToTerm.
                                                       ++ apply (reduceSub LNN).
                                                          ** apply closedNN.
                                                          ** destruct H0 as (H0, H1). destruct repBeta as (H2, H3). simpl in H3.
                                                             apply iffTrans with
                                                                 (substF2 βR 2 (n2t b) 1 (n2t (S x0))).
                                                             --- rewrite (subFormulaId LNN).
                                                                 apply iffTrans with
                                                                     (substF4  βR 
                                                                        2 (n2t b)
                                                                        1 (Succ (var 3))
                                                                        3 (n2t x0)
                                                                        1 (n2t (β b x0))).
                                                                 +++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                     apply (subFormulaExch LNN).
                                                                     *** discriminate.
                                                                     *** intros [H4 | H4].
                                                                         ---- discriminate H4.
                                                                         ---- apply H4.
                                                                     *** apply closedNatToTerm.
                                                                 +++ apply iffTrans with
                                                                         (substF4 βR
                                                                            2 (n2t b)
                                                                            3 (n2t x0)
                                                                            1 (substT (Succ (var 3)) 3 (n2t x0))
                                                                            1 (n2t (β b x0))).
                                                                     *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                         apply (subSubFormula LNN).
                                                                         ---- discriminate.
                                                                         ---- apply closedNatToTerm.
                                                                     *** simpl; apply iffTrans with
                                                                             (substF3 βR
                                                                                2 (n2t b)
                                                                                1 (substT (Succ (var 3)) 3 (n2t x0))
                                                                                1 (n2t (β b x0))).
                                                                         ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                              apply (subFormulaNil LNN). intro H4.
                                                                              destruct (freeVarSubFormula3 _ _ _ _ _ H4) as [H5 | H5].
                                                                              { elim (proj1 (Nat.le_ngt  3 2)).
                                                                                - apply H2. eapply in_remove. apply H5.
                                                                                - repeat constructor. }
                                                                              { elim (closedNatToTerm _ _ H5). }
                                                                         ---- apply (subFormulaNil LNN). intro H4.
                                                                              destruct (freeVarSubFormula3 _ _ _ _ _ H4) as [H5 | H5].
                                                                              { elim (in_remove_neq _ _ _ _ _ H5). reflexivity. }
                                                                              { rewrite freeVarSucc in H5. elim (closedNatToTerm _ _ H5). }
                                                             --- apply H3.
                                                    -- eapply impE.
                                                       ++ eapply impE.
                                                          ** apply Axm; left; right; constructor.
                                                          ** do 2 apply sysWeaken.
                                                             apply impE with
                                                                 (substF2 (equal (var 1) (n2t (β b x0)))
                                                                    0 (n2t (f (S x0)))
                                                                    1 (n2t (β b x0))).
                                                             --- apply iffE2. repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                 destruct H0 as (H0, H1). destruct repBeta as (H2, H3). simpl in H3.
                                                                 apply
                                                                  iffTrans
                                                                   with
                                                                     (substF  (equal (var 0) (n2t (β b x0))) 0 (var 1)).
                                                                 +++ rewrite (subFormulaId LNN).
                                                                     apply iffTrans with
                                                                       (substF4  βR   
                                                                          1 (var 3)
                                                                          2 (n2t b)
                                                                          0 (var 1)
                                                                          3 (n2t x0)).
                                                                     *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                         apply (subFormulaExch LNN).
                                                                         ---- discriminate.
                                                                         ---- intros [H4 | H4].
                                                                              ++++ discriminate H4.
                                                                              ++++ apply H4.
                                                                         ---- apply closedNatToTerm.
                                                                     *** apply iffTrans with
                                                                             (substF4 βR
                                                                                1 (var 3)
                                                                                2 (n2t b)
                                                                                3 (n2t x0)
                                                                                0 (var 1)).
                                                                         ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                              apply (subFormulaExch LNN).
                                                                              ++++ discriminate.
                                                                              ++++ simpl. lia.
                                                                              ++++ apply closedNatToTerm.
                                                                         ---- apply (reduceSub LNN).
                                                                              ++++ apply closedNN.
                                                                              ++++ apply iffTrans with
                                                                                       (substF3 βR
                                                                                          2 (n2t b)
                                                                                          1 (var 3)
                                                                                          3 (n2t x0)).
                                                                                   **** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                                        apply (subFormulaExch LNN).
                                                                                        { discriminate. }
                                                                                        { simpl. lia. }
                                                                                        { apply closedNatToTerm. }
                                                                                   **** apply  iffTrans with 
                                                                                          (substF2  βR
                                                                                             2 (n2t b)
                                                                                             1 (n2t x0)).
                                                                                        { repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                                          apply (subFormulaTrans LNN). intro H4.
                                                                                          assert
                                                                                           (H5: In 3
                                                                                              (freeVarF  (substF  βR 2 (n2t b)))).
                                                                                          { eapply in_remove. apply H4. }
                                                                                          destruct (freeVarSubFormula3 _ _ _ _ _ H5) as [H7 | H7].
                                                                                          - elim (proj1 (Nat.le_ngt 3 2)).
                                                                                            + apply H2. eapply in_remove. apply H7.
                                                                                            + repeat constructor.
                                                                                          - elim (closedNatToTerm _ _ H7). }
                                                                                        { apply H3. }
                                                                 +++ rewrite (subFormulaEqual LNN). simpl. rewrite subTermNil.
                                                                     **** apply iffRefl.
                                                                     **** apply closedNatToTerm.
                                                             --- repeat rewrite (subFormulaEqual LNN). simpl.
                                                                 repeat rewrite (subTermNil LNN (n2t (β b x0)));
                                                                   try apply closedNatToTerm.
                                                                 apply eqRefl.
                                                       ++ apply impE with
                                                              (substF5  B
                                                                 2 (var 3)
                                                                 2 (n2t b)
                                                                 3 (n2t x0)
                                                                 0 (n2t (f (S x0)))
                                                                 1 (n2t (f x0))).
                                                          ** apply (subWithEquals LNN). apply Axm; right; constructor.
                                                          ** do 2 apply sysWeaken.
                                                             apply impE with
                                                                 (substF5 B
                                                                    2 (var 3)
                                                                    2 (n2t b)
                                                                    3 (n2t x0)
                                                                    1 (n2t (f x0))
                                                                    0 (n2t (f (S x0)))).
                                                             --- apply iffE1. apply (subFormulaExch LNN).
                                                                 +++ discriminate.
                                                                 +++ apply closedNatToTerm.
                                                                 +++ apply closedNatToTerm.
                                                             --- apply
                                                                  impE
                                                                   with
                                                                     (substF  (equal (var 0) (n2t (f (S x0))))
                                                                        0 (n2t (f (S x0)))).
                                                                 +++ apply iffE2. apply (reduceSub LNN).
                                                                     *** apply closedNN.
                                                                     *** destruct H0 as (H0, H1). simpl in H1.
                                                                         apply
                                                                          iffTrans
                                                                           with
                                                                             (substF2  B 
                                                                                2 (n2t x0)
                                                                                1 (n2t (f x0))).
                                                                         ---- apply iffTrans with
                                                                                  (substF3 B
                                                                                     2 (var 3)
                                                                                     3 (n2t x0)
                                                                                     1 (n2t (f x0))).
                                                                              ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                                   apply (subFormulaNil LNN). intro H2.
                                                                                   destruct (freeVarSubFormula3 _ _ _ _ _ H2) as [H3 | H3].
                                                                                   **** elim (in_remove_neq _ _ _ _ _ H3). reflexivity.
                                                                                   **** destruct H3 as [H3 | H3].
                                                                                        { discriminate H3. }
                                                                                        { apply H3. }
                                                                              ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                                                   apply (subFormulaTrans LNN). intro H2.
                                                                                   elim (proj1 (Nat.le_ngt 3 2)).
                                                                                   **** apply H0. eapply in_remove. apply H2.
                                                                                   **** repeat constructor.
                                                                         ---- unfold f. simpl. apply H1.
                                                                 +++ rewrite (subFormulaEqual LNN). simpl.
                                                                     rewrite (subTermNil LNN).
                                                                     *** apply eqRefl.
                                                                     *** apply closedNatToTerm. }
                                  ++++ apply Nat.lt_lt_succ_r. now rewrite Nat.succ_lt_mono. 
                         *** apply natNE. auto.
                 --- apply iffRefl.
           ++ apply iffTrans with
                  (substF2 βR 1 (n2t a) 2 (n2t x)).
              ** apply iffI.
                 --- apply impI. apply existSys.
                     +++ apply closedNN.
                     +++ intro H1. destruct (freeVarSubFormula3 _ _ _ _ _ H1) as [H4 | H4].
                         *** elim (in_remove_neq _ _ _ _ _ H4). reflexivity.
                         *** elim (closedNatToTerm _ _ H4).
                     +++ apply impE with
                             (substF2 βR 1 (n2t a) 2 (var 2)).
                         *** apply (subWithEquals LNN). eapply andE1. apply Axm; right; constructor.
                         *** rewrite (subFormulaId LNN). eapply andE2. apply Axm; right; constructor.
                 --- apply impI. apply existI with (n2t x). rewrite (subFormulaAnd LNN). apply andI.
                     +++ rewrite (subFormulaEqual LNN). simpl. rewrite subTermNil.
                         *** apply eqRefl.
                         *** apply closedNatToTerm.
                     +++ apply Axm; right; constructor.
              ** apply iffTrans with
                     (substF2  βR 2 (n2t x) 1 (n2t a)).
                 --- apply (subFormulaExch LNN).
                     +++ discriminate.
                     +++ apply closedNatToTerm.
                     +++ apply closedNatToTerm.
                 --- rewrite H2.
                     +++ destruct repBeta as (H1, H4). apply H4.
                     +++ apply Nat.lt_succ_diag_r.
        -- intros z H2. unfold beta. repeat (rewrite cPairProjections1 || rewrite cPairProjections2).
           now apply (p z). 
    - simpl; intros A g H B h H0 a a0.
      apply
       Representable_ext
        with (evalPrimRecFunc n (g a0) (fun x y : nat => h x y a0) a).
      + induction a as [| a Hreca].
        * simpl. apply extEqualRefl.
        * simpl. apply extEqualCompose2.
          -- apply Hreca.
          -- apply extEqualRefl.
      + destruct H as (H, H1). destruct H0 as (H0, H2). simpl in H1. simpl in H2.
        assert
         (H3: RepresentableHelp n
            (evalPrimRecFunc n (g a0) (fun x y : nat => h x y a0) a)
            (substF 
               (primRecSigmaFormula n (substF  A n.+1 (n2t a0))
                  (substF3 B 
                     n.+1 (n2t a0)
                     n.+2 (var n.+1)
                     n.+3 (var n.+2)))
               n.+1 (n2t a))).
        { apply Hrecn.
          - split.
            + intros v H3. induction (freeVarSubFormula3 _ _ _ _ _ H3).
              * assert (H5: v <= S n).
                { apply H. eapply in_remove. apply H4. }
                destruct (proj1 (Nat.lt_eq_cases v (S n)) H5) as [H6 | H6].
                -- now apply Nat.lt_succ_r. 
                -- elim (in_remove_neq _ _ _ _ _ H4). auto.
              * elim (closedNatToTerm _ _ H4).
            + apply H1.
          - split.
            + intros v H3.
              repeat
               match goal with
               | H:(In v (List.remove  eq_nat_dec ?X1 (freeVarF ?X2))) |- _ =>
                   assert (In v (freeVarF X2));
                    [ eapply in_remove; apply H
                    | assert (v <> X1); [ eapply in_remove_neq; apply H | clear H ] ]
               | H:(In v (freeVarF  (substF ?X1 ?X2 ?X3))) |- _ =>
                   induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
               end.
              * assert (v <= n.+3).
                { apply H0. auto. }
                lia.
              * elim (closedNatToTerm _ _ H4).
              * destruct H4 as [H3| H3].
                -- rewrite <- H3. apply Nat.le_succ_diag_r.
                -- elim H3.
              * destruct H4 as [H3| H3].
                -- rewrite <- H3. apply le_n.
                -- elim H3.
            + simpl. intros.
              apply RepresentableAlternate with
                  (substF3 B
                     n.+3 (n2t a1)
                     n.+2 (n2t a2)
                     n.+1 (n2t a0)).
              * apply iffSym.
                apply iffTrans with
                    (substF4 B 
                       n.+1 (n2t a0)
                       n.+2 (var n.+1)
                       n.+3 (n2t a1)
                       n.+1 (n2t a2)).
                -- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                   apply (subFormulaTrans LNN). intro H3.
                   repeat
                    match goal with
                    | H:(In ?X1 (List.remove eq_nat_dec ?X1 (freeVarF ?X2))) |- _
                    =>
                        elim (in_remove_neq _ _ _ _ _ H); reflexivity
                    | H:(In ?X3 (List.remove  eq_nat_dec ?X1 (freeVarF ?X2))) |- _
                    =>
                        assert (In X3 (freeVarF X2));
                         [ eapply in_remove; apply H
                         | assert (X3 <> X1); [ eapply in_remove_neq; apply H | clear H ] ]
                    | H:(In ?X4 (freeVarF (substF ?X1 ?X2 ?X3))) |- _
                    =>
                        induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
                    | H:(In ?X4 (@freeVarT LNN (var ?X1))) |- _ =>
                        induction H as [H3| H3]; [ idtac | contradiction ]
                    end.
                    congruence.
                 -- apply iffTrans with
                        (substF4 B 
                           n.+1 (n2t a0)
                           n.+3 (n2t a1) 
                           n.+2 (var n.+1)
                           n.+1 (n2t a2)).
                    ++ repeat (apply (reduceSub LNN); [ apply closedNN |]). 
                       apply (subFormulaExch LNN).
                       ** lia.
                       ** simpl. lia.
                       ** apply closedNatToTerm.
                    ++ apply iffTrans with
                           (substF3 B
                              n.+1 (n2t a0)
                              n.+3 (n2t a1)
                              n.+2 (n2t a2)).
                       ** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                          apply (subFormulaTrans LNN). intro H3.
                          repeat
                           match goal with
                           | H:(In ?X1 (List.remove eq_nat_dec ?X1 (freeVarF ?X2))) |- _
                           =>
                               elim (in_remove_neq _ _ _ _ _ H); reflexivity
                           | H:(In ?X3 (List.remove eq_nat_dec ?X1 (freeVarF ?X2))) |- _
                           =>
                               assert (In X3 (freeVarF X2));
                                [ eapply in_remove; apply H
                                | assert (X3 <> X1); [ eapply in_remove_neq; apply H | clear H ] ]
                           | H:(In ?X4 (freeVarF (substF ?X1 ?X2 ?X3))) |- _
                           =>
                               induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
                           | H:(In ?X4 (@freeVarT LNN (var ?X1))) |- _ =>
                               simple induction H; [ idtac | contradiction ]
                           end.
                          --- elim (closedNatToTerm _ _ H3).
                          --- elim (closedNatToTerm _ _ H3).
                       ** apply iffTrans with
                              (substF3 B
                                 n.+3 (n2t a1)
                                 n.+1 (n2t a0)
                                 n.+2 (n2t a2)).
                          --- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                              apply (subFormulaExch LNN).
                              +++ lia.
                              +++ apply closedNatToTerm.
                              +++ apply closedNatToTerm.
                          --- apply (subFormulaExch LNN).
                              +++ lia.
                              +++ apply closedNatToTerm.
                              +++ apply closedNatToTerm.
              * apply H2. }
        apply
         RepresentableAlternate
          with
            (substF 
               (primRecSigmaFormula n (substF A n.+1 (n2t a0))
                  (substF3 B 
                     n.+1 (n2t a0)
                     n.+2 (var n.+1)
                     n.+3 (var n.+2)))
                     n.+1 (n2t a)).
        * clear H3 Hrecn; apply iffSym.
          apply iffTrans with
              (substF2 (primRecSigmaFormula (S n) A B) 
                    n.+1 (n2t a0) n.+2 (n2t a)).
          -- apply (subFormulaExch LNN).
             ++ lia.
             ++ apply closedNatToTerm.
             ++ apply closedNatToTerm.
          -- apply iffTrans with
                 (substF3 (primRecSigmaFormula (S n) A B) 
                    n.+1 (n2t a0)
                    n.+2 (var (S n))
                    n.+1 (n2t a)).
             ++ apply iffSym. apply (subFormulaTrans LNN). intro H3.
                assert
                 (H4: In n.+1
                    (freeVarF 
                       (substF (primRecSigmaFormula n.+1 A B) 
                          n.+1 (n2t a0)))).
                 { eapply in_remove. apply H3. }
                destruct (freeVarSubFormula3 _ _ _ _ _ H4) as [H5 | H5].
                ** elim (in_remove_neq _ _ _ _ _ H5). reflexivity.
                ** elim (closedNatToTerm _ _ H5).
             ++ apply (reduceSub LNN). apply closedNN. unfold primRecSigmaFormula.
                assert (H3 := I). (* For hyps numbering compatibility *)
                assert (H4 := I). (* For hyps numbering compatibility *)
                assert
                 (subExistSpecial :
                  forall (F : Formula) (a b c : nat),
                  b <> c ->
                  substF (existH b F) c (n2t a) =
                  existH b (substF F c (n2t a))).
                { intros F a1 b c H5. rewrite (subFormulaExist LNN). destruct (eq_nat_dec b c) as [e | e].
                  - elim H5. auto.
                  - destruct (In_dec eq_nat_dec b (freeVarT (n2t a1))) as [e0 | e0].
                    + elim (closedNatToTerm _ _ e0).
                    + reflexivity. }
                assert
                 (subForallSpecial :
                  forall (F : Formula) (a b c : nat),
                  b <> c ->
                  substF (forallH b F) c (n2t a) =
                  forallH b (substF F c (n2t a))).
                { intros F a1 b c H5. rewrite (subFormulaForall LNN). destruct (eq_nat_dec b c) as [e | e].
                  - elim H5. auto.
                  - destruct (In_dec eq_nat_dec b (freeVarT (n2t a1))) as [e0 | e0].
                    + elim (closedNatToTerm _ _ e0).
                    + reflexivity. }
                assert (H5: forall a b : nat, a <> b -> b <> a) by auto.
                assert
                 (subExistSpecial2 :
                  forall (F : Formula) (a b c : nat),
                  b <> c ->
                  b <> a ->
                  substF (existH b F) c (var a) =
                  existH b (substF F c (var a))).
                { intros F a1 b c H6 H7. rewrite (subFormulaExist LNN). 
                  destruct (eq_nat_dec b c) as [e | e].
                  - elim H6. auto.
                  - destruct (In_dec eq_nat_dec b (@freeVarT LNN (var a1))) as [e0 | e0].
                    + destruct e0 as [H8| H8].
                      * elim H7; auto.
                      * elim H8.
                    + reflexivity. }
                assert
                 (subForallSpecial2 :
                  forall (F : Formula) (a b c : nat),
                  b <> c ->
                  b <> a ->
                  substF (forallH b F) c (var a) =
                  forallH b (substF F c (var a))).
                { intros F a1 b c H6 H7; rewrite (subFormulaForall LNN). destruct (eq_nat_dec b c) as [e | e].
                  - elim H6. auto.
                  - destruct (In_dec eq_nat_dec b (@freeVarT LNN (var a1))) as [e0 | e0].
                    + destruct e0 as [H8 | H8].
                      * elim H7; auto.
                      * elim H8.
                    + reflexivity. }
                assert (H6 := I). (* For hyps numbering compatibility *)
                assert (H7 := I). (* For hyps numbering compatibility *)
                assert
                 (H8: forall (a b : Term) (v : nat) (s : Term),
                  substF (LT a b) v s =
                  LT (substT a v s) (substT b v s)).
                { intros a1 b v s. unfold LT. rewrite (subFormulaRelation LNN). reflexivity. }
                assert
                 (H9: forall (f : Formula) (a : nat) (s : Term),
                  substF (existH a f) a s = existH a f).
                { intros f a1 s. rewrite (subFormulaExist LNN). destruct (eq_nat_dec a1 a1) as [e | e].
                  - reflexivity.
                  - elim e; auto. }
                assert
                 (H10: forall (f : Formula) (a : nat) (s : Term),
                  substF (forallH a f) a s = forallH a f).
                { intros f a1 s. rewrite (subFormulaForall LNN). destruct (eq_nat_dec a1 a1) as [e | e].
                  - reflexivity.
                  - elim e; auto. }
                assert (H11 := I). (* For hyps numbering compatibility *)
                assert (H12 := I). (* For hyps numbering compatibility *)
                assert (H13 := I). (* For hyps numbering compatibility *)
                assert (H14 := I). (* For hyps numbering compatibility *)
                assert (H15 := I). (* For hyps numbering compatibility *)
                assert (H16 := I). (* For hyps numbering compatibility *)
Opaque substF.
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
                          (substF2 
                             (existH n.+2 ?X1)
                                ?X2 (var n.+2)
                                ?X3 ?X4) _)) =>
                        apply
                         iffTrans
                          with
                            (substF 
                               (substF 
                                  (existH n.+1
                                     (substF X1 n.+2 (var n.+1))) X2
                                  (var n.+2)) X3 X4);
                         [ repeat (apply (reduceSub LNN); [ apply closedNN |]);
                            apply (rebindExist LNN)
                         |]
                    |  |-
                    (folProof.SysPrf LNN NN
                       (iffH 
                          (substF3 
                             (forallH (S (S n)) ?X1) ?X2
                                   (var (S (S n))) ?X3 ?X4 ?X5 ?X6) _)) =>
                        apply
                         iffTrans
                          with
                            (substF
                               (substF 
                                  (substF 
                                     (forallH (S n)
                                        (substF X1 (S (S n)) (var (S n)))) X2
                                     (var (S (S n)))) X3 X4) X5 X6);
                         [ repeat (apply (reduceSub LNN); [ apply closedNN |]);
                            apply (rebindForall LNN)
                         |]
                    |  |-
                    (folProof.SysPrf LNN NN
                       (iffH 
                          (substF (forallH (S ?X6) ?X1) ?X2 (var (S ?X6))) _))
                    =>
                        apply
                         iffTrans
                          with
                            (substF 
                               (forallH X6 (substF X1 (S X6) (var X6))) X2
                               (var (S X6)));
                         [ repeat (apply (reduceSub LNN); [ apply closedNN |]);
                            apply (rebindForall LNN)
                         |]
                    |  |- (folProof.SysPrf LNN NN (iffH (existH (S ?X1) ?X2) ?X3)) =>
                        apply
                         iffTrans with (existH X1 (substF X2 (S X1) (var X1)));
                         [ apply (rebindExist LNN) |]
                    |  |- (folProof.SysPrf LNN NN (iffH (forallH (S ?X1) ?X2) ?X3))
                    =>
                        apply
                         iffTrans
                          with (forallH X1 (substF X2 (S X1) (var X1)));
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

                ** apply iffTrans with
                       (substF2 A n.+1 (n2t a0)  n.+3 (var n.+2)).
                   --- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN). PRsolveFV A B n.
                   --- apply (subFormulaNil LNN). PRsolveFV A B n.
                ** apply iffTrans with
                       (substF4 βR 
                          1 Zero
                          2 (var n.+3)
                          n.+2  (var n.+1)
                          n.+3  (var n.+2)).
                   --- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN). PRsolveFV A B n.
                   --- apply iffTrans with
                           (substF3  βR
                              1 Zero
                              2 (var n.+3)
                              n.+3 (var n.+2)).
                       +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN). PRsolveFV A B n.
                       +++ apply (subFormulaTrans LNN). PRsolveFV A B n.
                ** apply iffTrans with
                       (substF6 βR
                          1 (var n.+4)
                          2 (var n.+3)
                          0 (var n.+2)
                          n.+2 (var n.+1)
                          n.+3 (var n.+2)
                          n.+4 (var n.+3)).
                   --- repeat (apply (reduceSub LNN); [ apply closedNN |]). 
                       apply (subFormulaNil LNN). PRsolveFV A B n.
                   --- apply iffTrans with
                           (substF5 βR
                              1 (var n.+4)
                              2 (var n.+3)
                              0 (var n.+1)
                              n.+3 (var n.+2)
                              n.+4 (var n.+3)).
                       +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaTrans LNN). PRsolveFV A B n.
                       +++ apply iffTrans with
                               (substF5 βR
                                  1 (var n.+4)
                                  2 (var n.+3)
                                  n.+3 (var n.+2)
                                  0 (var n.+1)
                                  n.+4 (var n.+3)).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaExch LNN); PRsolveFV A B n.
                           *** apply iffTrans with
                                   (substF4 βR
                                      1 (var n.+4)
                                      2 (var n.+2)
                                      0 (var n.+1)
                                      n.+4 (var n.+3)).
                               ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply (subFormulaTrans LNN). PRsolveFV A B n.
                               ---- apply iffTrans with
                                        (substF4 βR
                                           1 (var n.+4)
                                           2 (var n.+2)
                                           n.+4 (var n.+3)
                                           0 (var n.+1)).
                                    ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                         apply (subFormulaExch LNN); PRsolveFV A B n.
                                    ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                         apply iffTrans with
                                             (substF3  βR 
                                                1 (var n.+4)
                                                n.+4  (var n.+3)
                                                2 (var n.+2)).
                                         **** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                              apply (subFormulaExch LNN); PRsolveFV A B n.
                                         **** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                              apply (subFormulaTrans LNN). PRsolveFV A B n.
                ** apply iffTrans with
                       (substF5 B
                          n.+1 (n2t a0)
                          n.+3 (var n.+4)
                          n.+2  (var n.+1)
                          n.+3  (var n.+2)
                          n.+4  (var n.+3)).
                   --- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaExch LNN); PRsolveFV A B n.
                   --- apply iffTrans with
                           (substF5 B 
                              n.+1 (n2t a0)
                              n.+2 (var n.+1)
                              n.+3 (var n.+4)
                              n.+3 (var n.+2)
                              n.+4 (var n.+3)).
                       +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaExch LNN); PRsolveFV A B n.
                       +++ apply iffTrans with
                               (substF4 B
                                 n.+1 (n2t a0)
                                  n.+2 (var n.+1)
                                  n.+3  (var n.+4)
                                  n.+4  (var n.+3)).
                           *** repeat (apply (reduceSub LNN);
                                       [ apply closedNN |]). 
                               apply (subFormulaNil LNN); PRsolveFV A B n.
                           *** apply iffTrans with
                                 (substF3 B 
                                    n.+1  (n2t a0)
                                    n.+2 (var n.+1)
                                    n.+3  (var n.+3)).
                               ---- apply (subFormulaTrans LNN); 
                                      PRsolveFV A B n.
                               ---- apply iffSym. 
                                    apply (subFormulaTrans LNN);
                                      PRsolveFV A B n.
                ** apply iffTrans with
                       (substF5  βR 
                          1 (Succ (var n.+4))
                          2 (var n.+3)
                          n.+2  (var n.+1)
                          n.+3 (var n.+2)
                          n.+4 (var n.+3)).
                   --- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN); PRsolveFV A B n.
                   --- apply iffTrans with
                           (substF4 βR 
                              1  (Succ (var n.+4))
                              2 (var n.+3)
                              n.+3  (var n.+2)
                              n.+4  (var n.+3)).
                       +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN); PRsolveFV A B n.
                       +++ apply iffTrans with
                               (substF3 βR
                                  1 (Succ (var n.+4))
                                  2 (var n.+2)
                                  n.+4  (var n.+3)).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                               apply (subFormulaTrans LNN); PRsolveFV A B n.
                           *** apply iffTrans with
                                   (substF3  βR 
                                      1 (Succ (var n.+4))
                                      n.+4 (var n.+3)
                                      2 (var n.+2)).
                               ---- apply (subFormulaExch LNN); PRsolveFV A B n.
                               ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply iffTrans with
                                        (substF2 βR 
                                           n.+4 (var n.+3)
                                           1 (substT (Succ (var n.+4)) n.+4 (var n.+3))).
                                    ++++ apply (subSubFormula LNN); PRsolveFV A B n.
                                    ++++ replace
                                          (substT (Succ (var n.+4)) n.+4 (var n.+3))
                                           with
                                          (Succ
                                             (substT (var n.+4) (n.+4) (var n.+3))).
                                         **** rewrite (subTermVar1 LNN).
                                              repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                              apply (subFormulaNil LNN); PRsolveFV A B n.
                                         **** reflexivity.
                **  apply iffTrans with
                       (substF4 A 
                          n.+1 (n2t a0)
                          n.+2 (var n.+1)
                          n.+3 (var n.+2)
                          n.+5 (var n.+4)).
                   --- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                       apply (subFormulaNil LNN); PRsolveFV A B n.
                   --- apply iffTrans with
                         (substF3 A
                            n.+1 (n2t a0)
                            n.+3 (var n.+2)
                            n.+5  (var n.+4)).
                       +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN); PRsolveFV A B n.
                       +++ apply
                            iffTrans
                             with
                               (substF2 A n.+1 (n2t a0) n.+5 (var n.+4)).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN); PRsolveFV A B n.
                           *** apply iffTrans with (substF A (S n) (n2t a0)).
                               ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply (subFormulaNil LNN); PRsolveFV A B n.
                               ---- apply iffSym. apply (subFormulaNil LNN); PRsolveFV A B n.
                ** apply iffTrans with
                       (substF6 
                          βR 
                          1 Zero
                          2 (var n.+5)
                          n.+1  (n2t a0)
                          n.+2 (var n.+1)
                          n.+3 (var n.+2)
                          n.+5  (var n.+4)).
                   --- repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaTrans LNN); PRsolveFV A B n.
                   --- apply iffTrans with
                           (substF5 βR
                              1 Zero
                              2 (var n.+5)
                              n.+2 (var n.+1)
                              n.+3 (var n.+2)
                              n.+5 (var n.+4)).
                       +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). apply (subFormulaNil LNN); PRsolveFV A B n.
                           lia.
                       +++ apply iffTrans with
                               (substF4 βR
                                  1 Zero
                                  2 (var n.+5)
                                  n.+3 (var n.+2)
                                  n.+5 (var n.+4)).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                               apply (subFormulaNil LNN); PRsolveFV A B n.
                           *** apply iffTrans with
                                   (substF3 βR
                                      1 Zero
                                      2 (var n.+5)
                                      n.+5 (var n.+4)).
                               ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply (subFormulaNil LNN); PRsolveFV A B n.
                               ---- apply
                                     iffTrans
                                      with
                                        (substF2 βR 1 Zero 2 (var n.+4)).
                                    ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                         apply (subFormulaTrans LNN); PRsolveFV A B n.
                                    ++++ apply iffSym. apply (subFormulaTrans LNN); PRsolveFV A B n. congruence.
                ** apply
                    iffTrans
                     with
                       (substF9 
                          βR
                          1 (var n.+4)
                          2 (var n.+3)
                          n.+3 (var n.+5)
                          0 (var n.+2)
                          n.+1 (n2t a0) 
                          n.+2 (var n.+1)
                          n.+3 (var n.+2)
                          n.+4 (var n.+3)
                          n.+5 (var n.+4)).
                   --- repeat (apply (reduceSub LNN); [ apply closedNN |]). 
                       apply (subFormulaExch LNN); PRsolveFV A B n.
                   --- apply iffTrans with
                           (substF8 βR
                              1 (var n.+4)
                              2 (var n.+5)
                              0 (var n.+2)
                              n.+1 (n2t a0)
                              n.+2 (var n.+1)
                              n.+3 (var n.+2)
                              n.+4 (var n.+3)
                              n.+5 (var n.+4)).
                       +++ repeat (apply (reduceSub LNN); [apply closedNN |]). 
                           apply (subFormulaTrans LNN); PRsolveFV A B n.
                       +++ apply iffTrans with
                               (substF7 βR 
                                  1 (var n.+4)
                                  2 (var n.+5)
                                  0  (var n.+2)
                                  n.+2 (var n.+1)
                                  n.+3 (var n.+2)
                                  n.+4 (var n.+3)
                                  n.+5 (var n.+4)).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                               apply (subFormulaNil LNN); PRsolveFV A B n. lia.
                           *** apply iffTrans with
                                   (substF6 βR
                                      1 (var n.+4)
                                      2 (var n.+5)
                                      0 (var n.+1)
                                      n.+3 (var n.+2)
                                      n.+4 (var n.+3)
                                      n.+5 (var n.+4)).
                               ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply (subFormulaTrans LNN); PRsolveFV A B n.
                               ---- apply iffTrans with
                                        (substF5 βR
                                           1 (var n.+4)
                                           2 (var n.+5)
                                           0 (var n.+1)
                                           n.+4 (var n.+3)
                                           n.+5 (var n.+4)).
                                    ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                         apply (subFormulaNil LNN); PRsolveFV A B n.
                                    ++++ apply iffTrans with
                                             (substF5 βR
                                                1 (var n.+4)
                                                2 (var n.+5)
                                                n.+4  (var n.+3)
                                                0 (var n.+1)
                                                n.+5 (var n.+4)).
                                         **** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                              apply (subFormulaExch LNN); PRsolveFV A B n.
                                         **** apply iffTrans with
                                                  (substF5 βR 
                                                     1 (var n.+4)
                                                     n.+4 (var n.+3)
                                                     2 (var n.+5)
                                                     0 (var n.+1)
                                                     n.+5 (var n.+4)).
                                              { repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                apply (subFormulaExch LNN); PRsolveFV A B n. }
                                              { apply iffTrans with
                                                    (substF4 βR
                                                       1 (var n.+3)
                                                       2 (var n.+5)
                                                       0 (var n.+1)
                                                       n.+5 (var n.+4)).
                                                - repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                  apply (subFormulaTrans LNN); PRsolveFV A B n.
                                                - apply
                                                   iffTrans
                                                    with
                                                      (substF4 βR
                                                         1 (var n.+3)
                                                         2 (var n.+5)
                                                         n.+5 (var n.+4)
                                                         0 (var n.+1)).
                                                  + repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaExch LNN); PRsolveFV A B n. lia.
                                                  + apply iffTrans with
                                                        (substF3 βR
                                                           1 (var n.+3)
                                                           2 (var n.+4)
                                                           0 (var n.+1)).
                                                    * repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                      apply (subFormulaTrans LNN); PRsolveFV A B n.
                                                    * apply iffSym.
                                                      apply
                                                       iffTrans
                                                        with
                                                          (substF4 βR
                                                             1 (var n.+3)
                                                             2 (var n.+2)
                                                             n.+2  (var n.+4)
                                                             0 (var n.+1)).
                                                      -- apply (subFormulaExch LNN); PRsolveFV A B n.
                                                      -- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                         apply (subFormulaTrans LNN); PRsolveFV A B n. congruence. }
                ** apply iffTrans with
                       (substF6 B
                          n.+3 (var n.+4)
                          n.+1 (n2t a0)
                          n.+2 (var n.+1)
                          n.+3 (var n.+2)
                          n.+4 (var n.+3)
                          n.+5 (var n.+4)).
                   --- repeat (apply (reduceSub LNN); [ apply closedNN |]). 
                       apply (subFormulaNil LNN); PRsolveFV A B n.
                   --- apply iffTrans with
                           (substF5 B
                              n.+3  (var n.+4)
                              n.+1 (n2t a0)
                              n.+2 (var n.+1)
                              n.+4 (var n.+3)
                              n.+5 (var n.+4)).
                       +++ repeat (apply (reduceSub LNN); [ apply closedNN |]). 
                           apply (subFormulaNil LNN); PRsolveFV A B n.
                       +++ apply
                            iffTrans
                             with
                               (substF5 B
                                  n.+1 (n2t a0)
                                  n.+3 (var n.+4)
                                  n.+2 (var n.+1)
                                  n.+4 (var n.+3)
                                  n.+5 (var n.+4)).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]). 
                               apply (subFormulaExch LNN); PRsolveFV A B n.
                           *** apply iffTrans with
                                   (substF5 B
                                      n.+1 (n2t a0)
                                      n.+2 (var n.+1)
                                      n.+3 (var n.+4)
                                      n.+4 (var n.+3)
                                      n.+5 (var n.+4)).
                               ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply (subFormulaExch LNN); PRsolveFV A B n.
                               ---- apply iffTrans with
                                        (substF4 B
                                           n.+1 (n2t a0)
                                           n.+2 (var n.+1)
                                           n.+3 (var n.+3)
                                           n.+5 (var n.+4)).
                                    ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                         apply (subFormulaTrans LNN); PRsolveFV A B n.
                                    ++++ apply iffTrans with
                                             (substF3 B 
                                                n.+1 (n2t a0)
                                                n.+2  (var n.+1)
                                                n.+3  (var n.+3)).
                                         **** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                              apply (subFormulaNil LNN); PRsolveFV A B n. lia.
                                         **** apply iffSym.
                                              apply iffTrans with
                                                  (substF4 B
                                                     n.+1 (n2t a0) 
                                                     n.+2 (var n.+1)
                                                     n.+3 (var n.+2) 
                                                     n.+2 (var n.+3)).
                                              { apply (subFormulaNil LNN); PRsolveFV A B n. }
                                              { apply (subFormulaTrans LNN); PRsolveFV A B n. }
                ** apply
                    iffTrans
                     with
                       (substF7  βR
                          1 (Succ (var n.+4))
                          2 (var n.+5)
                          n.+1 (n2t a0)
                          n.+2 (var n.+1)
                          n.+3 (var n.+2)
                          n.+4 (var n.+3)
                          n.+5 (var n.+4)).
                   --- repeat (apply (reduceSub LNN); [ apply closedNN |]). 
                       apply (subFormulaTrans LNN); PRsolveFV A B n.
                   --- apply iffTrans with
                           (substF6  βR 
                              1 (Succ (var n.+4))
                              2 (var n.+5)
                              n.+2 (var n.+1)
                              n.+3 (var n.+2)
                              n.+4 (var n.+3)
                              n.+5  (var n.+4)).
                       +++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                           apply (subFormulaNil LNN); PRsolveFV A B n. lia.
                       +++ apply iffTrans with
                               (substF5 βR
                                  1 (Succ (var n.+4))
                                  2 (var n.+5)
                                  n.+3 (var n.+2)
                                  n.+4 (var n.+3)
                                  n.+5 (var n.+4)).
                           *** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                               apply (subFormulaNil LNN); PRsolveFV A B n.
                           *** apply iffTrans with
                                   (substF4 βR
                                      1 (Succ (var n.+4))
                                      2  (var n.+5)
                                      n.+4 (var n.+3)
                                      n.+5 (var n.+4)).
                               ---- repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                    apply (subFormulaNil LNN); PRsolveFV A B n.
                               ---- apply iffTrans with
                                        (substF4 βR
                                           1 (Succ (var n.+4))
                                           n.+4  (var n.+3)
                                           2 (var n.+5)
                                           n.+5  (var n.+4)).
                                    ++++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                         apply (subFormulaExch LNN); PRsolveFV A B n.
                                    ++++ apply iffTrans with
                                             (substF3 βR 
                                                1 (Succ (var n.+4))
                                                n.+4 (var n.+3)
                                                2 (var n.+4)).
                                         **** repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                              apply (subFormulaTrans LNN); PRsolveFV A B n.
                                         **** apply iffTrans with
                                                  (substF2  βR
                                                     1 (Succ (var n.+3))
                                                     2 (var n.+4)).
                                              { repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                apply iffTrans with
                                                    (substF2 βR
                                                       n.+4 (var n.+3)
                                                       1 (substT (Succ (var n.+4))
                                                            n.+4
                                                            (var n.+3))).
                                                - apply (subSubFormula LNN); PRsolveFV A B n.
                                                - replace
                                                   (substT (Succ (var n.+4)) n.+4 (var n.+3))
                                                      with
                                                   (Succ
                                                      (substT (var n.+4) n.+4 (var n.+3))).
                                                  + rewrite (subTermVar1 LNN).
                                                    repeat (apply (reduceSub LNN); [ apply closedNN |]).
                                                    apply (subFormulaNil LNN); PRsolveFV A B n.
                                                  + reflexivity. }
                                              { apply iffSym. apply (subFormulaTrans LNN); PRsolveFV A B n. congruence. }
                ** apply iffTrans with
                       (substF4  βR
                          2 (var n.+3)
                          1 (var n.+2)
                          n.+2 (var n.+1)
                          n.+3 (var n.+2)).
                   --- repeat (apply (reduceSub LNN); [ apply closedNN |]). 
                       apply (subFormulaNil LNN); PRsolveFV A B n.
                   --- apply iffTrans with
                           (substF3 βR
                              2 (var n.+3)
                              1 (var n.+1)
                              n.+3  (var n.+2)).
                       +++ repeat (apply (reduceSub LNN); [ apply closedNN |]).
                           apply (subFormulaTrans LNN); PRsolveFV A B n.
                       +++ apply iffTrans with
                               (substF3 βR
                                  2 (var n.+3)
                                  n.+3 (var n.+2)
                                  1 (var n.+1)).
                           *** apply (subFormulaExch LNN); PRsolveFV A B n.
                           *** repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
                               apply (subFormulaTrans LNN); PRsolveFV A B n.
        * apply H3. }
  intros n A g H0 B h H1. split.
  - destruct H0 as (H0, H2). destruct H1 as (H1, H3). intros v H4.
    assert (H5: forall v : nat, In v (freeVarF βR) -> v <= 2).
    { eapply proj1. apply betaRepresentable. }
    assert (H6: forall v : nat, v <> n.+2 -> v <= n.+2 -> v <= n.+1) by lia.
    unfold primRecSigmaFormula, minimize, existH in H4;
     repeat
      match goal with
      | H1:(?X1 = ?X2), H2:(?X1 <> ?X2) |- _ =>
          elim H2; apply H1
      | H1:(?X1 = ?X2), H2:(?X2 <> ?X1) |- _ =>
          elim H2; symmetry  in |- *; apply H1
      | H:(v = ?X1) |- _ => rewrite H; clear H
      | H:(?X1 = v) |- _ =>
          rewrite <- H; clear H
      | H:(In ?X3 (freeVarF (existH ?X1 ?X2))) |- _ =>
          assert (In X3 (List.remove  eq_nat_dec X1 (freeVarF X2)));
           [ apply H | clear H ]
      | H:(In ?X3 (freeVarF (forallH ?X1 ?X2))) |- _ =>
          assert (In X3 (List.remove  eq_nat_dec X1 (freeVarF X2)));
           [ apply H | clear H ]
      | H:(In ?X3 (List.remove eq_nat_dec ?X1 (freeVarF ?X2))) |- _
      =>
          assert (In X3 (freeVarF X2));
           [ eapply in_remove; apply H
           | assert (X3 <> X1); [ eapply in_remove_neq; apply H | clear H ] ]
      | H:(In ?X3 (freeVarF (andH ?X1 ?X2))) |- _ =>
          assert (In X3 (freeVarF X1 ++ freeVarF X2));
           [ apply H | clear H ]
      | H:(In ?X3 (freeVarF (impH ?X1 ?X2))) |- _ =>
          assert (In X3 (freeVarF X1 ++ freeVarF X2));
           [ apply H | clear H ]
      | H:(In ?X3 (freeVarF (notH ?X1))) |- _ =>
          assert (In X3 (freeVarF X1)); [ apply H | clear H ]
      | H:(In _ (freeVarF (primRecSigmaFormulaHelp _ _ _))) |- _ =>
          decompose sum (freeVarPrimRecSigmaFormulaHelp1 _ _ _ _ H); clear H
      | H:(In _ (freeVarF (primRecPiFormulaHelp _ _ _))) |- _ =>
      decompose sum (freeVarPrimRecPiFormulaHelp1 _ _ _ _ H); clear H
      | H:(In ?X3 (freeVarF A)) |- _ =>
          apply Nat.le_trans with n; [ apply H0; apply H | apply Nat.le_succ_diag_r ]
      | H:(In ?X3 (freeVarF B)) |- _ =>
          apply H6; [ clear H | apply H1; apply H ]
      | H:(In _ (_ ++ _)) |- _ =>
          induction (in_app_or _ _ _ H); clear H
      | H:(In _ (freeVarF (substF ?X1 ?X2 ?X3))) |- _ =>
          induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
      | H:(In _ (freeVarF (LT ?X1 ?X2))) |- _ =>
          rewrite freeVarLT in H
      | H:(In _ (freeVarT (n2t _))) |- _ =>
          elim (closedNatToTerm _ _ H)
      | H:(In _ (freeVarT Zero)) |- _ =>
          elim H
      | H:(In _ (freeVarT (Succ _))) |- _ =>
          rewrite freeVarSucc in H
      | H:(In _ (@freeVarT LNN (var _))) |- _ =>
          simpl in H; decompose sum H; clear H
      | H:(In _ (@freeVarT LNN (var  _))) |- _ =>
          simpl in H; decompose sum H; clear H
      end; try first [ assumption | apply le_n ].
      assert (H7: v <= 2) by auto. lia.
   - apply H; auto.
Qed.

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
  with 
  primRecsFormula (n m : nat) (fs : PrimRecs n m) {struct fs} :
    Vector.t (Formula * naryFunc n) m :=
    match fs in (PrimRecs n m) return (Vector.t (Formula * naryFunc n) m) 
    with
    | PRnil n => Vector.nil _
    | PRcons n m f fs' =>
        Vector.cons (Formula * naryFunc n) 
          (primRecFormula n f, evalPrimRec n f) m (primRecsFormula n m fs')
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
                  (forall v : nat, 
                      In v (freeVarF (fst pair)) -> v <= n) /\
                    rec) m (primRecsFormula n m fs)).
  - apply succRepresentable.
  - apply zeroRepresentable.
  - intros n0 m l; simpl; apply projRepresentable.
  - simpl; intros n0 m g H h H0. 
    decompose record H /r; intros H1 H3 H4.
    assert
     (H2: Representable n0
        (evalComposeFunc n0 m (FormulasToFuncs n0 m 
                                 (primRecsFormula n0 m g))
           (evalPrimRec m h))
        (composeSigmaFormula n0 n0 m (primRecsFormula n0 m g)
           (primRecFormula m h)))
      by (apply composeSigmaRepresentable; auto).
    induction H2 as (H2, H5); split.
    + assumption.
    + apply Representable_ext with
          (evalComposeFunc n0 m 
             (FormulasToFuncs n0 m 
                (primRecsFormula n0 m g))
             (evalPrimRec m h)).
      * apply extEqualCompose.
        -- assumption.
        -- apply extEqualRefl.
      * assumption.
  - simpl in |- *. intros n0 g H h H0.
    apply primRecSigmaRepresentable; auto.
  - simpl; tauto.
  - simpl; intros n0 m p H p0 H0.
    decompose record H0 /r; intros H1 H3 H4; clear H0.
    repeat split; auto.
    + destruct H as [H H0]; auto.
    + apply extEqualRefl.
    + destruct H; auto.
Qed.
(* end hide *)

Theorem primRecRepresentable :
 forall (n : nat) (f : naryFunc n) (p : isPR n f),
 Representable n f (primRecFormula n (fun2PR f)).
Proof.
  intros n f p.
  assert
   (H: Representable n (evalPrimRec n (proj1_sig p))
      (primRecFormula n (proj1_sig p))) by apply primRecRepresentable1.
  destruct H as [H H0]; split.
  - assumption.
  - destruct p as (x, p);
    eapply Representable_ext with (evalPrimRec n x); assumption.
Qed.

(* begin hide *)
End Primitive_Recursive_Representable.
(* end hide *)
