(** * Encoding terms, formulas and proofs

Original script by Russel O'Connor 

 *)

From Coq Require Import Arith.
From hydras.Ackermann Require Import fol folProof cPair.

Section Code_Term_Formula_Proof.

Variable L : Language.
 Section LcodeDef. 
   Variable cF : Functions L -> nat.
   Variable cR : Relations L -> nat.
   Class Lcode : Prop :=
     {  codeFInj : 
       forall f g : Functions L, cF f = cF g -> f = g; 
       codeRInj :
       forall R S : Relations L, cR R = cR S -> R = S
     }.
  End LcodeDef. 

 Definition codeF {cf : Functions L -> nat} {cr : Relations L -> nat} (c: Lcode cf cr) := cf.

 Definition codeR {cf : Functions L -> nat} {cr : Relations L -> nat} (c: Lcode cf cr) := cr.

Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let Prf := Prf L.
Let SysPrf := SysPrf L.

Generalizable All Variables.
Section codeTermFormDef.

  Context `(cl : Lcode cf cr).
Fixpoint codeTerm (t : Term) : nat :=
  match t with
  | var n => cPair 0 n
  | apply f ts => cPair (S (codeF cl f)) (codeTerms _ ts)
  end
 
 with codeTerms (n : nat) (ts : Terms n) {struct ts} : nat :=
  match ts with
  | Tnil => 0
  | Tcons n t ss => S (cPair (codeTerm t) (codeTerms n ss))
  end.

Lemma codeTermInj : 
  forall t s : Term, codeTerm t = codeTerm s -> t = s.
Proof.
  intro t; elim t using Term_Terms_ind
    with (P0 := fun (n : nat) (ts : fol.Terms L n) =>
                  forall ss : Terms n, 
                    codeTerms n ts = codeTerms n ss -> ts = ss).
  - (* variables *) intros n s H; destruct s.
    + simpl in H; apply cPairInj2 in H; now subst. 
    + simpl in H.
      assert (H0: 0 = S (codeF cl f)) by (eapply cPairInj1; apply H). 
      discriminate H0.
  - (* applications *) intros f t0 H s H0; destruct s.
    + simpl in H0.
      assert (H1: S (codeF cl f) = 0) by (eapply cPairInj1; apply H0).
      discriminate H1.
    + simpl in H0; assert (H1: f = f0). 
       { eapply codeFInj. apply cl. apply eq_add_S; eapply cPairInj1; apply H0. }
       cut
         (cPair (S (codeF cl f)) (codeTerms (arityF L f) t0) =
            cPair (S (codeF cl f0)) 
              (codeTerms (arityF L f0) t1)).
       * generalize t1; rewrite <- H1; clear H1 H0 t1.
         intros t1 H0; rewrite (H t1).
         -- reflexivity.
         -- eapply cPairInj2.
            apply H0.
       * apply H0.
  - (* empty sequence *)  
    intros ss H; rewrite <- nilTerms; reflexivity.
  - (* non-empty sequence *)
    intros n t0 H t1 H0 ss H1; induction (consTerms L n ss).
    destruct x as (a, b); simpl in p; rewrite <- p.
    rewrite <- p in H1; simpl in H1; rewrite (H a).
    + rewrite (H0 b).
      * reflexivity.
      * eapply cPairInj2; apply eq_add_S, H1. 
    + eapply cPairInj1.
      apply eq_add_S, H1.
Qed.

Lemma codeTermsInj :
 forall (n : nat) (ts ss : Terms n),
 codeTerms n ts = codeTerms n ss -> ts = ss.
Proof.
  intros n ts; induction ts as [| n t ts Hrects].
  - intros ss H; now rewrite <- (nilTerms L ss).
  - intros ss H.
    destruct (consTerms L n ss) as [(a,b) p].
    simpl in p; rewrite <- p in H |- *. 
    rewrite (Hrects b).
    + rewrite (codeTermInj t a).
      * reflexivity.
      * eapply cPairInj1.
        apply eq_add_S, H. 
    + eapply cPairInj2.
      apply eq_add_S, H. 
Qed.


Fixpoint codeFormula (f : Formula) : nat :=
  match f with
  | equal t1 t2 => cPair 0 (cPair (codeTerm t1) (codeTerm t2))
  | impH f1 f2 => cPair 1 (cPair (codeFormula f1) (codeFormula f2))
  | notH f1 => cPair 2 (codeFormula f1)
  | forallH n f1 => cPair 3 (cPair n (codeFormula f1))
  | atomic R ts => cPair (4 + codeR cl R) (codeTerms _ ts)
  end.


Lemma codeFormulaInj :
  forall f g : Formula, codeFormula f = codeFormula g -> f = g.
Proof.
  intro f; 
    induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf]; 
    intros;
    [ destruct g as [t1 t2| r t1| f f0| f| n f]
    | destruct g as [t0 t1| r0 t0| f f0| f| n f]
    | destruct g as [t t0| r t| f f2| f| n f]
    | destruct g as [t t0| r t| f0 f1| f0| n f0]
    | destruct g as [t t0| r t| f0 f1| f0| n0 f0] ];
    (simpl in H;
     try
       match goal with
       | h:(cPair ?X1 ?X2 = cPair ?X3 ?X4) |- _ =>
           assert  False by ( cut (X1 = X3);
           [ discriminate | eapply cPairInj1; apply h ]); 
           contradiction
       end).
  - (* equality between terms *) 
    rewrite (codeTermInj t t1).
    + rewrite (codeTermInj t0 t2).
      * reflexivity.
      * eapply cPairInj2.
        eapply cPairInj2.
        apply H.
    + eapply cPairInj1.
      eapply cPairInj2.
      apply H.
  - (* atomic formulas *) assert (r = r0).
    { eapply codeRInj. 
      apply cl.
      do 4 apply eq_add_S.
      eapply cPairInj1.
      apply H.
    } 
    cut  (cPair (S (S (S (S (codeR cl r)))))
            (codeTerms (arityR L r) t) =
            cPair (S (S (S (S (codeR cl r0)))))
              (codeTerms (arityR L r0) t0)).
    + generalize t0; rewrite <- H0; clear H0 H t0.
      intros t0 H; rewrite (codeTermsInj _ t t0).
      * reflexivity.
      * eapply cPairInj2; apply H.
    + apply H.
  - (* implication *)
    rewrite (Hrecf1 f).
    + rewrite (Hrecf0 f2).
      * reflexivity.
      * eapply cPairInj2.
        eapply cPairInj2.
        apply H.
    + eapply cPairInj1.
      eapply cPairInj2; apply H.
  - (* negation *) rewrite (Hrecf f0).
    reflexivity.
    eapply cPairInj2.
    apply H.
  - (* universal quantification *) 
    rewrite (Hrecf f0).
    + replace n0 with n.
      * reflexivity.
      * eapply cPairInj1.
        eapply cPairInj2.
        apply H.
    + eapply cPairInj2.
      eapply cPairInj2.
      apply H.
Qed.

Fixpoint codePrf (Z : Formulas) (f : Formula) (prf : Prf Z f) {struct prf} :
 nat :=
  match prf with
  | AXM A => cPair 0 (codeFormula A)
  | MP Axm1 Axm2 A B rec1 rec2 =>
      cPair 1
        (cPair
           (cPair (cPair 1 (cPair (codeFormula A) (codeFormula B)))
              (codePrf _ _ rec1)) (cPair (codeFormula A) (codePrf _ _ rec2)))
  | GEN Axm A v _ rec =>
      cPair 2 (cPair v (cPair (codeFormula A) (codePrf _ _ rec)))
  | IMP1 A B => cPair 3 (cPair (codeFormula A) (codeFormula B))
  | IMP2 A B C =>
      cPair 4 (cPair (codeFormula A) (cPair (codeFormula B) (codeFormula C)))
  | CP A B => cPair 5 (cPair (codeFormula A) (codeFormula B))
  | FA1 A v t => cPair 6 (cPair (codeFormula A) (cPair v (codeTerm t)))
  | FA2 A v _ => cPair 7 (cPair (codeFormula A) v)
  | FA3 A B v => cPair 8 (cPair (codeFormula A) (cPair (codeFormula B) v))
  | EQ1 => cPair 9 0
  | EQ2 => cPair 10 0
  | EQ3 => cPair 11 0
  | EQ4 r => cPair 12 (codeR cl r)
  | EQ5 f => cPair 13 (codeF cl f)
  end.

Lemma codePrfInjAxm :
 forall (a b : Formula) (A B : Formulas) (p : Prf A a) (q : Prf B b),
 codePrf A a p = codePrf B b q -> A = B.
Proof.
  intros a b A B p; generalize B b; clear B b.
  induction p
    as
    [A|
      Axm1 Axm2 A B p1 Hrecp1 p0 Hrecp0|
      Axm A v n p Hrecp|
      A B|
      A B C|
      A B|
      A v t|
      A v n|
      A B v|
    |
    |
    |
      R|
      f]; intros;
    [ destruct q
      as
      [A0|
        Axm1 Axm2 A0 B p p0|
        Axm A0 v n p|
        A0 B|
        A0 B C|
        A0 B|
        A0 v t|
        A0 v n|
        A0 B v|
      |
      |
      |
        R|
        f]
    | destruct q
      as
      [A0|
        Axm0 Axm3 A0 B0 p p2|
        Axm A0 v n p|
        A0 B0|
        A0 B0 C|
        A0 B0|
        A0 v t|
        A0 v n|
        A0 B0 v|
      |
      |
      |
        R|
        f]
    | destruct q
      as
      [A0|
        Axm1 Axm2 A0 B p0 p1|
        Axm0 A0 v0 n0 p0|
        A0 B|
        A0 B C|
        A0 B|
        A0 v0 t|
        A0 v0 n0|
        A0 B v0|
      |
      |
      |
        R|
        f]
    | destruct q
      as
      [A0|
        Axm1 Axm2 A0 B0 p p0|
        Axm A0 v n p|
        A0 B0|
        A0 B0 C|
        A0 B0|
        A0 v t|
        A0 v n|
        A0 B0 v|
      |
      |
      |
        R|
        f]
    | destruct q
      as
      [A0|
        Axm1 Axm2 A0 B0 p p0|
        Axm A0 v n p|
        A0 B0|
        A0 B0 C0|
        A0 B0|
        A0 v t|
        A0 v n|
        A0 B0 v|
      |
      |
      |
        R|
        f]
    | destruct q
      as
      [A0|
        Axm1 Axm2 A0 B0 p p0|
        Axm A0 v n p|
        A0 B0|
        A0 B0 C|
        A0 B0|
        A0 v t|
        A0 v n|
        A0 B0 v|
      |
      |
      |
        R|
        f]
    | destruct q
      as
      [A0|
        Axm1 Axm2 A0 B p p0|
        Axm A0 v0 n p|
        A0 B|
        A0 B C|
        A0 B|
        A0 v0 t0|
        A0 v0 n|
        A0 B v0|
      |
      |
      |
        R|
        f]
    | destruct q
      as
      [A0|
        Axm1 Axm2 A0 B p p0|
        Axm A0 v0 n0 p|
        A0 B|
        A0 B C|
        A0 B|
        A0 v0 t|
        A0 v0 n0|
        A0 B v0|
      |
      |
      |
        R|
        f]
    | destruct q
      as
      [A0|
        Axm1 Axm2 A0 B0 p p0|
        Axm A0 v0 n p|
        A0 B0|
        A0 B0 C|
        A0 B0|
        A0 v0 t|
        A0 v0 n|
        A0 B0 v0|
      |
      |
      |
        R|
        f]
    | destruct q
      as
      [A|
        Axm1 Axm2 A B p p0|
        Axm A v n p|
        A B|
        A B C|
        A B|
        A v t|
        A v n|
        A B v|
      |
      |
      |
        R|
        f]
    | destruct q
      as
      [A|
        Axm1 Axm2 A B p p0|
        Axm A v n p|
        A B|
        A B C|
        A B|
        A v t|
        A v n|
        A B v|
      |
      |
      |
        R|
        f]
    | destruct q
      as
      [A|
        Axm1 Axm2 A B p p0|
        Axm A v n p|
        A B|
        A B C|
        A B|
        A v t|
        A v n|
        A B v|
      |
      |
      |
        R|
        f]
    | destruct q
      as
      [A|
        Axm1 Axm2 A B p p0|
        Axm A v n p|
        A B|
        A B C|
        A B|
        A v t|
        A v n|
        A B v|
      |
      |
      |
        R0|
        f]
    | destruct q
      as
      [A|
        Axm1 Axm2 A B p p0|
        Axm A v n p|
        A B|
        A B C|
        A B|
        A v t|
        A v n|
        A B v|
      |
      |
      |
        R|
        f0] ];
    (simpl in H;
     try
       match goal with
       | h:(cPair ?X1 ?X2 = cPair ?X3 ?X4) |- _ =>
           assert False by (cut (X1 = X3);
           [ discriminate | eapply cPairInj1; apply h ]); contradiction
       end); try reflexivity.
  - replace A0 with A.
    + reflexivity.
    + apply codeFormulaInj; eapply cPairInj2, H.
  - replace Axm0 with Axm1.
    + replace Axm3 with Axm2.
      * reflexivity.
      * eapply Hrecp0 with A0 p2.
        do 3 eapply cPairInj2.
        apply H.
    + eapply Hrecp1 with (impH  A0 B0) p.
      eapply cPairInj2.
      eapply cPairInj1.
      eapply cPairInj2.
      apply H.
  - eapply Hrecp with A0 p0.
    do 3 eapply cPairInj2.
    apply H.
Qed.

Definition codeImp (a b : nat) := cPair 1 (cPair a b).

Lemma codeImpCorrect :
 forall a b : Formula,
 codeImp (codeFormula a) (codeFormula b) = codeFormula (impH a b).
Proof. intros; reflexivity. Qed.

Definition codeNot (a : nat) := cPair 2 a.

Lemma codeNotCorrect :
 forall a : Formula, codeNot (codeFormula a) = codeFormula (notH a).
Proof. intros; reflexivity. Qed.

Definition codeForall (n a : nat) := cPair 3 (cPair n a).

Lemma codeForallCorrect :
 forall (n : nat) (a : Formula),
 codeForall n (codeFormula a) = codeFormula (forallH n a).
Proof.
 intros; reflexivity. Qed.

Definition codeOr (a b : nat) := codeImp (codeNot a) b.

Lemma codeOrCorrect :
 forall a b : Formula,
 codeOr (codeFormula a) (codeFormula b) = codeFormula (orH a b).
Proof. intros; reflexivity. Qed. 

Definition codeAnd (a b : nat) := codeNot (codeOr (codeNot a) (codeNot b)).

Lemma codeAndCorrect :
 forall a b : Formula,
 codeAnd (codeFormula a) (codeFormula b) = codeFormula (andH a b).
Proof. intros; reflexivity. Qed. 

Definition codeIff (a b : nat) := codeAnd (codeImp a b) (codeImp b a).

Lemma codeIffCorrect :
 forall a b : Formula,
 codeIff (codeFormula a) (codeFormula b) = codeFormula (iffH a b).
Proof. intros; reflexivity. Qed.

End codeTermFormDef.


End Code_Term_Formula_Proof.


Arguments codeTerm {L} {cf cr cl} _. 
Arguments codeTerms {L} {cf cr cl n} _. 
Arguments codeFormula {L} {cf cr cl} _. 
Arguments codePrf {L} {cf cr cl} _ _ _. 
