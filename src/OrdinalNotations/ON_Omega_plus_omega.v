(**  The ordinal omega + omega *)


From Coq Require Import Arith Compare_dec Lia.
From hydras Require Import Simple_LexProd OrdinalNotations.Generic
        ON_plus ON_Omega.

Import Relations.
Declare Scope opo_scope.
Delimit Scope opo_scope with opo.
Open Scope ON_scope.
Open Scope opo_scope.

Definition Omega_plus_Omega := ON_plus Omega Omega.

Existing Instance Omega_plus_Omega.

Definition t := @ON_plus.t nat nat.


Example ex1 : inl 7 o< inr 0.
Proof. constructor. Qed.

Notation "'omega'" := (inr 0:t) : opo_scope.
Notation "'omega'" := (@inr nat nat 0) (only printing) : opo_scope.

Open Scope opo_scope.

Definition fin (i:nat) : t := inl i.
Coercion fin : nat >-> t.

Compute ON_compare omega  (fin 8).

Compute ON_compare (8:t)  omega.

Example ex2 :  inl 7 o< omega.
Proof. constructor. Qed.

Lemma omega_is_limit : Limit omega. 
Proof.
  split.
  + exists (inl 0); constructor.
  + inversion 1; subst.
    exists (inl (S x)); split; constructor;auto with arith.
    lia.
Qed.

Lemma limit_is_omega alpha : Limit alpha -> alpha = omega.
Proof.
  destruct alpha.
  - intro H; inversion H.
    destruct n.
    +  destruct H0 as [w Hw].
       inversion Hw.   lia.
    + specialize (H1 (inl n)).
      destruct H1.
      constructor; auto.
      destruct H1.
      inversion H2; subst; inversion H1; subst.
      lia.
  - destruct n.
    + trivial.
    + destruct 1.
      specialize (H0 (inr n)).
      destruct H0.
      constructor; auto.
      destruct H0 as [H0 H1]; inversion H1; inversion H0; subst.
      discriminate.    
      injection H7; intro; subst. lia.
Qed.

Lemma limit_iff (alpha : t) : Limit alpha <-> alpha = omega.
Proof.
  split.
  - intro H; now apply limit_is_omega.
  - intro; subst; apply omega_is_limit.
Qed.

Lemma Successor_inv1 : forall i j, Successor  (inl j) (inl i) -> j = S i. 
Proof.
  destruct 1 as [H H0].
  inversion_clear H.
  assert (H2 : (j = S i \/ S i < j)%nat)  by lia.
  destruct H2; trivial.
  elimtype False. {
    assert (H2: inl i o< inl (S i)) by (constructor; auto).
    assert (H3: inl (S i) o< inl j) by (constructor; auto).
    apply (H0 (inl (S i)) H2 H3). }
Qed.

Lemma Successor_inv2 : forall i j, Successor (inr j) (inr i) -> j = S i. 
Proof.
  destruct 1 as [H H0].
  inversion_clear H.
  assert (H2 : (j = S i \/ S i < j)%nat)  by lia.
  destruct H2; trivial.
  elimtype False. {
    specialize (H0 (inr (S i))).
    assert (H2 :inr i o< inr (S i)) by (constructor; auto).
    assert (H3 :inr (S i) o< inr j) by (constructor; auto).
    apply (H0 H2 H3).  }
Qed.

Lemma Successor_inv3 : forall i j, ~ Successor (inr j) (inl i).
Proof.
  destruct 1 as [H H0].

  specialize (H0 (inl (S i))).
  assert (inl i o< inl (S i)) by (constructor;auto).
  assert (inl (S i) o< inr j) by constructor.
  specialize (H0 H1 H2);  inversion H0.
Qed.

Lemma Successor_inv4 : forall i j, ~ Successor (inl j) (inr i).
Proof.
  destruct 1 as [H H0].
  inversion H.
Qed.

Definition succ (alpha : t) :=
  match alpha with
    inl n => inl (S n)
  | inr n => inr (S n)
  end.


Lemma Successor_succ alpha : Successor (succ alpha) alpha.
   destruct alpha;red;cbn; split.
  - constructor; auto.
  -  destruct z.
     inversion_clear 1.
     inversion_clear 1; lia.
     inversion 2.
  -  constructor; auto.
  - destruct z.
    inversion_clear 1.
    inversion_clear 1.
    inversion_clear 1; lia.
Qed.



Lemma Successor_correct alpha beta : Successor beta alpha <->
                                     beta = succ alpha.
Proof.
  split.  
  - destruct alpha, beta; intro H.
    apply Successor_inv1 in H. subst. reflexivity.
    destruct (Successor_inv3  _ _ H).
    destruct (Successor_inv4  _ _ H).
    apply Successor_inv2 in  H; now subst.
  - intro;subst; now apply Successor_succ.
Qed.


Definition succb (alpha: t) := match alpha with
                                   inr (S  _) | inl (S _) => true
                                 | _ => false
                                 end.

Lemma succb_correct (alpha: t) :
  succb alpha <-> exists beta: t, alpha = succ beta.
Proof.
  destruct alpha; split.
  - destruct n.
   + intro; discriminate.
   +    exists n; reflexivity.
  - intros [[p| p] H].
    + injection H; intro; subst; reflexivity.
    +  discriminate. 
  -  destruct n.
     +  intro; discriminate.   
     + exists (inr n); reflexivity.
  -  intros [[p| p] H].
     +     discriminate.
     + injection H; intro; subst; reflexivity.
Qed.


Lemma omega_not_succ : forall alpha, ~ Successor omega alpha.
Proof.
 destruct alpha.
  apply Successor_inv3.
  intro H; apply Successor_inv2 in H.
  discriminate.
Qed.

Lemma Least_is_0 (alpha:t) : Least alpha <-> alpha = 0.
Proof.
  unfold Least; split; intro H.
  - destruct alpha.    
   +  destruct n.
    * reflexivity.
    *  specialize (H (inl n)); inversion H.
     --  inversion H0; lia.
     --  lia.
   + specialize (H (inl 0)); inversion H.
    *  inversion H0.
  -  subst; destruct y.
     + destruct n.
       * right. 
       * left; constructor.
         lia.
     +   constructor.
         constructor.
Qed.



Lemma ZLS_dec (alpha : t) :
  {alpha = 0} +
  {Limit alpha} +
  {beta : t | Successor alpha beta}.
Proof.
  destruct alpha.
  - destruct n.
    +   left; now left.
    + right; exists (inl n).
      split.
      * constructor. auto with arith.
      * intros beta Hbeta Hbeta'; inversion Hbeta; subst;
          inversion Hbeta';subst; try lia.
  - destruct n.
    left;right.
    split.
    + exists (inl 0); constructor.
    + inversion 1; subst.
      exists (inl (S x)); split; constructor;auto with arith.
      lia.
    + right; exists (inr n); split.
      * constructor. auto with arith.
      *       intros beta Hbeta Hbeta'; inversion Hbeta; subst;
                inversion Hbeta';subst; try lia.
Defined.




Definition Zero_limit_succ_dec : ZeroLimitSucc_dec.
Proof.
  intro alpha;  destruct (ZLS_dec alpha) as [[H | H] | H].
  - left; left; now rewrite  Least_is_0. 
  - left; now right.
  - now right.
Defined.

Definition limitb (alpha: t) := match ON_compare alpha omega
                                with  Eq => true | _ => false end.


Lemma eq_dec (alpha beta: t) : {alpha = beta} + {alpha <> beta}.
Proof.  
 repeat decide equality.
Defined.


Lemma le_introl :
  forall i j :nat, (i<= j)%nat -> inl i  o<= inl j.
Proof.
  intros i j  H; destruct (Lt.le_lt_or_eq _ _ H); auto .
  - left; now constructor.
  - subst; now right. 
Qed.

Lemma le_intror :
  forall i j :nat, (i<= j)%nat -> inr i  o<= inr j.
Proof.
  intros i j  H; destruct (Lt.le_lt_or_eq _ _ H); auto.
  - left; now constructor.
  - subst; now right. 
Qed.

Lemma le_0 : forall p: t,   fin 0 o<= p.
Proof.
  destruct p.  destruct n ; [right |].
  constructor. constructor.  auto with arith.
  left; constructor. 
Qed.





Lemma le_lt_trans : forall p q r, p o<= q -> q o< r -> p o< r.
Proof.
  destruct 1; trivial. 
  intro; now transitivity y.  
Qed.   

Lemma lt_le_trans : forall p q r, p o< q -> q o<= r -> p o< r.
Proof.
  destruct 2; trivial; now  transitivity q.
Qed.   


Lemma lt_succ_le alpha beta : alpha o< beta <-> succ alpha o<= beta.
Proof.  
 destruct alpha, beta. unfold succ; cbn.
 split.
  - inversion_clear 1.
    + apply le_introl.   lia.
  -     inversion_clear 1.
        inversion_clear H0. constructor; lia.
        constructor; auto with arith.
  - split.
     simpl. constructor.
    +  constructor.
    + constructor.
  - split.
    inversion_clear 1.
    inversion_clear 1. inversion H0.
  - split.
   inversion_clear 1.
    simpl.
     apply le_intror. lia.
   simpl.
   inversion_clear 1.
   inversion_clear  H0; constructor;lia.
   constructor;lia.
Qed.


Lemma lt_succ alpha : alpha o< succ alpha.
Proof.
  destruct alpha; simpl; constructor; lia.
Qed.


Lemma lt_omega alpha : alpha o< omega <-> exists n:nat,  alpha = fin n.
 Proof.
   destruct alpha; simpl; split.
  -   inversion_clear 1; exists n; auto.
  -  constructor.
  - inversion 1; lia.
  - destruct 1 as [n0 e]; inversion e.
 Qed.

 Lemma Omega_as_lub  :
   forall alpha, 
     (forall i,  fin i o< alpha) <-> omega o<= alpha.
 Proof.
   intro alpha; destruct (Generic.compare_correct  omega alpha).
   - subst;split.
     +  right.
     + intros; constructor.
   -  split.
      + intro H0; destruct alpha as [n | n].
        *  specialize (H0 n); inversion H0; lia.
        *  destruct n.
           -- right.
           -- left;constructor; auto with arith.
      +  inversion 1.
         * inversion H1; constructor.      
         *  subst; constructor.
   - rewrite (lt_omega alpha) in H; destruct H as [n Hn]; subst; split.
     +  intro H; generalize (H n).
        intro; elimtype False. { inversion H0. lia. }
     + inversion 1;  inversion H0.
 Qed.

Instance Incl : SubON Omega Omega_plus_Omega omega fin.
split.
- intros; reflexivity.
- constructor.
- inversion 1; subst.
  + exists  x; trivial.
  + lia.
Qed.

Goal 6 o< 8.
  auto with arith.
  Set Printing All.
  constructor; auto with arith.
  Unset Printing All.
Qed.
