(**  The ordinal omega + omega *)
Require Import Arith Compare_dec Lia Simple_LexProd Ordinal_generic
        Relation_Operators Disjoint_Union.

Import Relations.
Declare Scope oo_scope.
Delimit Scope oo_scope with oo.
Open Scope oo_scope.

Coercion is_true: bool >-> Sortclass.

Definition t := (nat + nat)%type.
Arguments inl  {A B} _.
Arguments inr  {A B} _.
Print le_AsB.
Definition lt : relation t := le_AsB _ _ Peano.lt Peano.lt.
Infix "<" := lt : oo_scope.

Definition le := clos_refl _ lt.

Infix "<=" := le : oo_scope.

Hint Unfold lt le : OO.
Hint Constructors le_AsB: OO.

Definition fin (n:nat) : t := inl n.

Coercion fin : nat >-> t.

Goal 6 < 8.
auto with arith.
(*  oups *)
constructor; auto with arith.
Qed.


Notation  "'omega'"  := (inr 0) : oo_scope.

Goal 24 < omega.
constructor.
Qed.


Definition succ (alpha : t) := match alpha with
                                 inl i => inl (S i)
                               | inr i => inr (S i)
                               end.

Example ex2 : omega < succ omega.
Proof.
 constructor; auto with arith. 
Qed.



Instance lt_strorder : StrictOrder lt.
Proof.
  split.
  -  intros x  H. inversion H; try lia.
  - intros x y z H H0.  inversion H; inversion H0; subst; try discriminate.
    + injection H5;constructor; lia.
    + constructor.
    + constructor.
    + constructor.
      injection H5; subst; lia.
Qed.
    

Instance le_preorder : PreOrder le.
Proof.
  split.
  -  right.
  - inversion_clear 1; trivial.
    + inversion 1; left.
      * now transitivity y.
      * now subst.
Qed.

Lemma eq_dec (alpha beta: t) : {alpha = beta} + {alpha <> beta}.
Proof.  
 repeat decide equality.
Defined.

Lemma lt_wf : well_founded lt.
Proof. apply wf_disjoint_sum; apply lt_wf. Qed.



Lemma le_introl :
  forall i j :nat, (i<= j)%nat -> inl i  <= inl j.
Proof.
  intros i j  H; destruct (Lt.le_lt_or_eq _ _ H); auto with OO.
  - left; now constructor.
  - subst; now right. 
Qed.

Lemma le_intror :
  forall i j :nat, (i<= j)%nat -> inr i  <= inr j.
Proof.
  intros i j  H; destruct (Lt.le_lt_or_eq _ _ H); auto with OO.
  - left; now constructor.
  - subst; now right. 
Qed.

Lemma le_0 : forall p: t,   0 <= p.
Proof.
  destruct p.  destruct n ; [right |].
  constructor. constructor.  auto with arith.
  left; constructor. 
Qed.





Lemma le_lt_trans : forall p q r, p <= q -> q < r -> p < r.
Proof.
  destruct 1; trivial. 
  intro; now transitivity y.  
Qed.   

Lemma lt_le_trans : forall p q r, p < q -> q <= r -> p < r.
Proof.
  destruct 2; trivial; now  transitivity q.
Qed.   


Lemma lt_succ_le alpha beta : alpha < beta <-> succ alpha <= beta.
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


Lemma lt_succ alpha : alpha < succ alpha.
Proof.
  destruct alpha; simpl; constructor; lia.
Qed.



 Definition compare (alpha beta: t) : comparison :=
   match alpha, beta with
     inl _, inr _ => Lt
   | inl n, inl p | inr n, inr p => Nat.compare n p
   | inr _, inl _ => Gt
  end.

 
 
 Definition lt_b alpha beta : bool :=
  match compare alpha beta with
      Lt => true
    | _ => false
  end.

Definition le_b alpha beta := negb (lt_b beta alpha).

Definition eq_b alpha beta := match compare alpha beta with
                                Eq => true
                              | _ => false
                              end.

Lemma compare_reflect alpha beta :
  match (compare alpha beta)
  with
    Lt => alpha < beta
  | Eq => alpha = beta
  | Gt => beta < alpha
  end.
  destruct alpha, beta; cbn; auto; try (constructor; lia);
    case_eq (Nat.compare n n0);
    ((rewrite Nat.compare_eq_iff;  congruence)
      || (rewrite Nat.compare_lt_iff; now constructor)
      || (rewrite Nat.compare_gt_iff; now constructor)).
Qed.


Lemma compare_correct alpha beta :
    CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
              (compare alpha beta).
Proof.
  generalize (compare_reflect alpha beta).
  destruct (compare alpha beta); now constructor. 
Qed.

Instance OmegaPlusOmega : OrdinalNotation lt_strorder compare.
Proof.
 split.
 - apply compare_correct.
 - apply lt_wf.
Qed.


Lemma lt_eq_lt_dec alpha beta :
  {alpha < beta} + {alpha = beta} + {beta < alpha}.
Proof.
 generalize (compare_reflect alpha beta).
 case_eq (compare alpha beta).
  - intros; left; now right.
  - intros; left; now left.
  - intros; now right.
Defined.


Arguments Ipred {A} {lt} {sto}  _ _.

Lemma Ipred_inv1 : forall i j, Ipred (inl i) (inl j) -> j = S i. 
Proof.
  destruct 1 as [H H0].
  inversion_clear H.
  assert (H2 : (j = S i \/ S i < j)%nat)  by lia.
  destruct H2; trivial.
  elimtype False.
  assert (inl i < inl (S i)) by (constructor; auto).
  assert (inl (S i) < inl j) by (constructor; auto).
  specialize (H0 (inl (S i)) H2 H3).
  destruct H0.
Qed.

Lemma Ipred_inv2 : forall i j, Ipred (inr i) (inr j) -> j = S i. 
Proof.
  destruct 1 as [H H0].
  inversion_clear H.
  
  assert (H2 : (j = S i \/ S i < j)%nat)  by lia.
  destruct H2; trivial.
   elimtype False.
   Print le_AsB.
   specialize (H0 (inr (S i))).
 assert (inr i < inr (S i)) by (constructor; auto).
  assert (inr (S i) < inr j) by (constructor; auto).
  specialize (H0 H2 H3); inversion H0.
Qed.

Lemma Ipred_inv3 : forall i j, ~ Ipred (inl i) (inr j).
Proof.
  destruct 1 as [H H0].

  specialize (H0 (inl (S i))).
  assert (inl i < inl (S i)) by (constructor;auto).
  assert (inl (S i) < inr j) by constructor.
  specialize (H0 H1 H2);  inversion H0.
Qed.

Lemma Ipred_inv4 : forall i j, ~ Ipred (inr i) (inl j).
Proof.
  destruct 1 as [H H0].
  inversion H.
Qed.



Lemma omega_not_succ : forall alpha, ~ Ipred alpha omega.
Proof.
 destruct alpha.
  apply Ipred_inv3.
  intro H; apply Ipred_inv2 in H.
  discriminate.
Qed.



Lemma Successor_succ alpha : Successor (succ alpha) alpha.
Proof.
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



Lemma Successor_correct alpha beta : Successor beta alpha <-> beta = succ alpha.
Proof.
  split.  
  - destruct alpha, beta; intro H.
    apply Ipred_inv1 in H. subst. reflexivity.
    destruct (Ipred_inv3  _ _ H).
    destruct (Ipred_inv4  _ _ H).
apply Ipred_inv2 in  H; now subst.
- intro;subst; now apply Successor_succ.
Qed.


Definition succb (alpha: t) := match alpha with
                                   inr (S  _) | inl (S _) => true
                                 | _ => false
                                 end.



Lemma succb_correct alpha : succb alpha <-> exists beta,  alpha = succ beta.
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


Definition limitb (alpha : t) := match alpha with
                                     (inr 0) => true
                                   | _ => false
                                   end.


Lemma Omega_limit_limitb alpha s : Omega_limit s alpha ->
                                     limitb alpha.
Proof.
   destruct alpha.
   destruct 1.
   elimtype False.
   destruct n.
    specialize (H 0); inversion H.
    lia.
    specialize (H0 (inl  n)).
 destruct H0.
 constructor; auto. 
   specialize (H  x).
   inversion H ; inversion H0; subst. rewrite <- H1 in H5. injection H5.
   intro; subst. lia.
   rewrite <- H1 in H6. discriminate.
   destruct n.
   intro; auto.
   intro H; elimtype False.
   destruct H.

   specialize (H0 (inr n)).
    destruct H0.
    constructor; auto.
    
   -- case_eq (s x).
   intro; subst. intro.
    rewrite H1 in H0; inversion H0.
    intros.
     rewrite H1 in H0.
      specialize (H x).
      rewrite  H1 in *.
    inversion H;
      inversion H0.
 subst.
lia.       
Qed.

Definition canon  alpha i :=
  match alpha with
  | inl 0 => inl 0
  | inl (S n) => inl n
  | inr 0 => inl i
  | inr (S n) => inr n
  end.

Lemma omega_is_limit:
   Omega_limit fin omega.
Proof.
  split.
  - constructor.
  - inversion_clear  1.
    + exists (S x); constructor; auto with arith.
    + lia.
Qed.

 Example Ex1 : limitb omega.
 Proof. reflexivity.  Qed.

 
Lemma limit_is_lub beta :
  limitb beta -> forall alpha, 
    (forall i,  canon beta i < alpha) <-> beta <= alpha.
Proof.  
  destruct beta;intros H alpha;destruct n. simpl.
  inversion H.
  inversion H.
  split.
  intro H0.
   destruct alpha.
   specialize (H0 n). inversion H0; try lia.
   apply le_intror; auto with arith.
   destruct alpha; inversion 1.
   inversion H0.
   inversion H1.
    constructor.
    constructor.
    inversion H.
Qed.

 Definition zero_limit_succ_dec :
  forall alpha: t, 
                ({alpha = 0} + {limitb alpha}) + 
                {beta : t |  alpha = succ beta} .
 Proof.
   destruct alpha as [n | p].
   destruct n.
    left.
    now left.
    right.
     now exists (inl n).
    destruct p.
     left; now right.
   right.  now exists (inr  p).
 Defined.


 
 Lemma lt_omega alpha : alpha < omega <-> exists n:nat,  alpha = n.
 Proof.
   destruct alpha; simpl; split.
  -   inversion_clear 1; exists n; auto.
  -  constructor.
  - inversion 1; lia.
  - destruct 1 as [n0 e]; inversion e.
 Qed.



