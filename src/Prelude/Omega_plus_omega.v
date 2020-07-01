(**  The ordinal omega * omega *)
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
Definition lt : relation t := le_AsB _ _ Peano.lt Peano.lt.
Infix "<" := lt : oo_scope.

Definition le := clos_refl _ lt.

Infix "<=" := le : oo_scope.


Definition zero: t := inl 0.
Notation  "'omega'"  := (inr 0) : oo_scope.


Definition succ (alpha : t) := match alpha with
                                 inl i => inl (S i)
                               | inr i => inr (S i)
                               end.


Definition fin (n:nat) : t := inl n.

Notation "'F'" := fin : oo_scope.

Coercion fin : nat >-> t.


Hint Unfold lt le : OO.
Hint Constructors le_AsB: OO.

Example ex1 :  6 < omega.
Proof.
red;  constructor 2. 
Qed.


Example ex2 : omega < inr 1.
Proof.
 constructor 3; auto with arith.
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


(* ICI *)


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

Lemma compare_refl alpha beta :
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

Lemma lt_eq_lt_dec alpha beta :
  {alpha < beta} + {alpha = beta} + {beta < alpha}.
Proof.
 generalize (compare_refl alpha beta).
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
   Print le_AsB.
specialize (H0 (inl (S i)) (le_aa _ _ _ _ _ _ H)).

inversion H0.
inversion H2.
lia.
lia.
Qed.

Lemma Ipred_inv2 : forall i j, Ipred (inr i) (inr j) -> j = S i. 
Proof.
  destruct 1 as [H H0].
  inversion_clear H.
  
  assert (H2 : (j = S i \/ S i < j)%nat)  by lia.
  destruct H2; trivial.
   elimtype False.
   Print le_AsB.
specialize (H0 (inr (S i)) (le_bb _ _ _ _ _ _ H)).

inversion H0.
inversion H2.
lia.
lia.
Qed.

Lemma Ipred_inv3 : forall i j, ~ Ipred (inl i) (inr j).
Proof.
  destruct 1 as [H H0].

specialize (H0 (inl (S i)) (le_ab  _ _ _ _ _ _ )).

inversion H0.
inversion H1.
lia.
lia.
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



Lemma Ipred_succ : forall alpha,  Ipred alpha (succ alpha).
Proof.
  destruct alpha;red;cbn; split.
  - constructor; auto.
  -  destruct z.
     inversion_clear 1. apply le_introl. lia.
     inversion 1.
  -  constructor; auto.
  - destruct z.
    left.
    constructor.
    inversion_clear 1.
    apply le_intror.
    lia.
Qed.

Lemma succ_ok alpha beta : Ipred alpha beta <-> beta = succ alpha.
Proof.
  split.  
  - destruct alpha, beta; intro H.
    apply Ipred_inv1 in H. subst. reflexivity.
    destruct (Ipred_inv3  _ _ H).
    destruct (Ipred_inv4  _ _ H).
apply Ipred_inv2 in  H; now subst.
- intro;subst; now apply Ipred_succ.
Qed.


Definition is_succ (alpha: t) := match alpha with
                                   inr (S  _) | inl (S _) => true
                                 | _ => false
                                 end.

Definition is_limit (alpha : t) := match alpha with
                                     (inr 0) => true
                                   | _ => false
                                   end.

(** ICI 
Lemma Omega_limit_is_limit alpha s : Omega_limit s alpha ->
                                     is_limit alpha.
Proof.
   destruct alpha.
   destruct 1.
   destruct n0.
   - destruct n.
    +   specialize (H 0).
       inversion H; lia.
    + now  cbn.
   -   destruct (H0 (n, n0)).
    + right; auto with arith. 
    + specialize (H x).
     rewrite lt_succ_le in H1.
     assert (s x < s x) by (eapply lt_le_trans; eauto).
     destruct lt_strorder as [H3 H4].
     destruct (H3 _ H2).
Qed.

Definition canon  alpha i :=
  match alpha with
    (0,0) => (0,0)
  | (_, S p) => (0,p)
  | (S n, 0) => (n, i)
  end.



Lemma is_limit_limit alpha :
  is_limit alpha -> Omega_limit (canon alpha) alpha.
Proof.
  destruct alpha;  inversion 1.
  destruct n; [discriminate | unfold canon].
  split;  destruct n0; try discriminate.
  -    left; auto with arith.
  -  destruct beta; inversion_clear 1.
     exists (S n1).
     assert( H0: (n0 = n \/ n0 <  n)%nat) by lia.
     destruct H0.
     subst;  right; auto.
     left; auto.
     lia.    
Qed.

 Example Ex1 : is_limit omega.
 Proof. reflexivity.  Qed.



 (* A simplifier ? *)
 
Lemma limit_is_lub_0 : forall i alpha, (forall j, (i,j) < alpha) <->
                                 (S i, 0) <= alpha.
Proof.
  intros i (k,l) ;split; intro  H .
  -   destruct (lt_eq_lt_dec (S i, 0) (k,l)) as [[Hlt | Heq] | Hgt].
      + now left.
      + rewrite Heq; now right.
      + destruct (is_limit_limit (S i,0)) as [H1 H2].
        * red; trivial.
        * simpl in H1; destruct (H2 _ Hgt) as [x H0].
        simpl in H0.
        specialize (H x).
     destruct lt_strorder as [H3 H4].
     destruct (H3 (k,l)).        
     transitivity (i,x); auto.
  -    inversion_clear H.
    + inversion_clear H0.
   *    intro.  left.  lia.
   *    left; left; auto. 
     + left;left;auto. 
Qed.

Lemma limit_is_lub beta :
  is_limit beta -> forall alpha, 
    (forall i,  canon beta i < alpha) <-> beta <= alpha.
Proof.  
  destruct beta;intros H alpha;destruct n, n0; try discriminate.
  apply limit_is_lub_0.
Qed.

 Definition zero_succ_limit_dec :
  forall alpha, 
                ({alpha = zero} + {is_limit alpha }) + 
                {beta : t |  alpha = succ beta} .
 Proof.
   destruct alpha as (n,p); destruct p.
   - destruct n.
     + left; left;trivial.
     +  left; now right.
   - right; now exists (n,p).
 Defined.

 (*

Definition  plus (alpha beta : t) : t :=
  match alpha,beta with
  | (0, b), (0, b') => (0, b + b')
  |  (0,0), y  => y
  |  x, (0,0)  => x
  |   (0, b), (S n', b') => (S n', b')
  | (S n, b), (S n', b') => (S n + S n', b')
  | (S n, b), (0, b') => (S n, b + b')
 
  end.

Infix "+" := plus : o2_scope.

Definition mult_fin  (alpha : t) (p : nat): t :=
  match alpha, p with
 |  (0,0), _  => zero
 |  _, 0 => zero
 |  (0, n), p => (0, n * p)
 |  ( n, b),  n' => ( n *  n', b)
               end.
Infix "*" := mult_fin : o2_scope.

Fixpoint fin_mult (n:nat)(beta : t) : t :=
  match n, beta with
 |  0, _  => zero
 |  _, (0,0) => zero
 |   n , (0,n') => (0, (n*n')%nat)
 |  n, (n',p') => (n', (n * p')%nat)
 end.

Compute (fin_mult 3 (omega * 7 + 15)).


Compute (fin_mult 3 (omega * 1 + 15)).
Search (_ + _ + _)%nat.

Lemma plus_assoc alpha beta gamma :
  alpha + (beta + gamma) = alpha + beta + gamma.
  destruct alpha, beta, gamma.
  destruct n,  n0, n1, n2, n3, n4; cbn; auto; f_equal; lia.
Qed.


Lemma succ_is_plus_1  alpha : alpha + 1 = succ alpha.
Proof.
 unfold succ ;
simpl; 
 destruct alpha; cbn; destruct n, n0; try f_equal; lia.
Qed.
  *)
 
Lemma lt_omega alpha : alpha < omega <-> exists n:nat,  alpha = fin n.
Proof.
 destruct alpha; simpl.
 split.
 inversion_clear 1.
 inversion H0.
   exists n0.
   auto.
   inversion H1.
 inversion H0.
    destruct 1.
    injection H. intros; subst. left. auto.
Qed.


Lemma decompose (i j : nat): (i,j) = omega * i + j.
Proof.
  destruct i, j; cbn; (reflexivity || (try f_equal; lia)). 
Qed.

Lemma unique_decomposition alpha : exists! i j: nat,  alpha = omega * i + j.
Proof.
  destruct alpha as [i j]; exists i; split.
  -  exists j; split.
     + now rewrite decompose. 
     + intros x; repeat rewrite <- decompose; congruence.
  - intros x [y [Hy _]]; rewrite <- decompose in Hy; congruence.
Qed.

(** ** Additive principals *)

Definition ap (alpha : t) :=  alpha <> zero /\
  (forall beta gamma,  beta < alpha -> gamma < alpha -> beta + gamma < alpha).

Lemma omega_ap : ap omega.
Proof.
 split; [discriminate |];intros beta gamma H H0; destruct beta, gamma.
 inversion H; subst.
 -  inversion H0; subst.
  +  inversion H2; inversion H3; subst; try lia.
     *  unfold plus; destruct n0; left; auto with arith.
     +  lia.
 - lia.
Qed.


Lemma ap_cases alpha : ap alpha -> alpha = 1 \/ alpha = omega.
Proof.
  destruct (zero_succ_limit_dec alpha) as [[Hzero |  Hlim] | Hsucc].
  - subst alpha; intro H; elimtype False.
    destruct H as [H _]; auto.
  - destruct alpha; unfold ap.
    destruct n, n0; try discriminate.
    intros [_ H1]; destruct n.
    + now right.
    +  right; specialize (H1 (S n,0) (S n,0)).
       assert (H2:(S n, 0) < (S (S n), 0)) by (left; auto).
       specialize (H1 H2 H2).
       inversion H1; lia.
  -  intro H;  destruct Hsucc as [beta e]; subst.
     destruct H as [_ H].
      destruct (eq_dec beta zero).
       + subst; now left.
       +  specialize  (H beta 1 (lt_succ beta)).
          assert (1 < succ beta). {
            destruct beta;  destruct n0, n1.
            * now destruct n.
            * right; cbn; lia.
            * destruct n0; cbn.
              left; auto.
              left; simpl;lia.
            * left; simpl; lia.
          }
          *  specialize (H H0).
             rewrite <- succ_is_plus_1 in H.       
             destruct lt_strorder as [H3 H4].
             destruct (H3 _ H).        
Qed.




Compute (omega * 3).
Compute (omega * 3) * 6.

Compute (omega * 3 + 1) * 6.
Compute fin_mult 3 omega.
Compute (3,2)+(2,10).

Compute (2,2)+(3,10).

Compute (0,2)+(0,10).

Compute (0,2)+(1,10).

Goal omega * 2 + 2 + omega * 3 + 10 = omega * 5 + 10.
  reflexivity.
Qed.
 *)

