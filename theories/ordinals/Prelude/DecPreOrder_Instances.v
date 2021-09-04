(** Pierre Castéran, Univ. Bordeaux and LaBRI *)

From hydras Require Export DecPreOrder.
From Coq Require Import Arith ZArith List  Sets.Finite_sets  Sets.Ensembles.

Instance Nat_le_dec : RelDecision le := le_dec.

Instance Nat_le_TO : TotalPreOrder le.
Proof.
 split.
 - apply Nat.le_preorder.
 - intros a b; apply Nat.le_ge_cases.
Qed.

Instance Z_le_dec : RelDecision Z.le := Z_le_dec.

Instance Z_le_TO : TotalPreOrder Z.le.
split.
- apply Z.le_preorder.
- intros a b; destruct (Z_le_gt_dec a b).
    *  left;auto.
    *  right; auto with zarith.
Qed.

Import DecPreOrder.

(** Pre-order associated with an inverse function *)

Instance Inverse_fun {A B:Type}{f : A -> B}
         {leB: relation B}{PB: PreOrder leB}:
                     PreOrder (fun x y => leB (f x) (f y)).
Proof.
  split. 
  -  intros x; reflexivity.
  - intros x y z Hxy Hyz; now transitivity (f y).
Defined.


Instance Total_Inverse_fun {A B:Type}{f : A -> B}
         {leB: relation B}{TB: TotalPreOrder leB} :
                     TotalPreOrder (fun x y => leB (f x) (f y)).
Proof.
split.
- apply Inverse_fun.
- intros a b.
  destruct TB.
  destruct (total_pre_order_total (f a) (f b)).
  + now left.
  + now right.
Defined.

Instance RelDecision_Inverse_fun {A B:Type}{f : A -> B}
 {leB: relation B} {RDB : RelDecision leB} :
  RelDecision (fun x y => leB (f x) (f y)) :=
  fun x y => decide_rel leB (f x) (f y).

(** Pre-order associated with inclusion *)

Instance PrO_Included {U:Type}: PreOrder (Included U).
Proof.
split;unfold Included;auto.
Defined.


Arguments Included {U} _ _.

Definition Included_s {U}  (A B : Ensemble U) :=
  Included  A B /\ ~ Included  B A.

Infix "<:" := Included (at level 30).
Infix "'<s'" := Included_s (at level 30).


(** Example 
  Lists (pre-ordered by their length) *)

Instance  List_length {A:Type}: 
   TotalPreOrder (fun l l' : list A => List.length l <= List.length l')%nat.
apply Total_Inverse_fun.
Defined.

(** Non dependent lexicographic product *)

Section lexprod.
 Variables (A B : Type)
           (leA : relation A) 
           (leB : relation B).
 Context (TA : TotalPreOrder leA)
         (TB : TotalPreOrder leB)
         (DA : RelDecision leA)
         (DB : RelDecision leB).
 
 Definition PA := @total_pre_order_pre A leA TA.
 Definition PB := @total_pre_order_pre B leB TB.
 
 
Notation "x '<=A' y" := (leA x y) (at level 70, no associativity).
Notation "x '<A' y" := (@lt A leA PA x y) (at level 70, no associativity).
Notation "x '<=B' y" := (leB x y) (at level 70, no associativity).
Notation "x '<B' y" := (@lt B leB PB x y ) (at level 70, no associativity).
Notation "x =A= y" := (@preorder_equiv A leA PA x y) (at level 70, no associativity).
Notation "x =B= y" := (@preorder_equiv B leB PB x y) (at level 70, no associativity).

Inductive lex_prod (p p':A*B): Prop :=
| lex1 : (fst p) <A (fst p') -> lex_prod p p'
| lex2 :  (fst p) =A= (fst p') ->  (snd p) <=B (snd p') -> lex_prod p p'.


Notation "x '<=lex' y" := (lex_prod x y) (at level 70, no associativity).
Notation "x '<lex' y" := (@lt (A*B)  lex_prod _ x y) (at level 70, no associativity).

 Global Instance PO_lex_prod : PreOrder lex_prod.
 Proof.
 split.
 -   intro x; right;  reflexivity.
 -    intros x y z Hxy Hyz; destruct x,y,z.     
      destruct Hxy.
      +  left; simpl in * |- *.
         destruct Hyz; simpl in *.
         now transitivity a0.
         apply DecPreOrder.lt_le_trans with a0;auto.
         now destruct H0. 
      + destruct Hyz;  simpl in * |- *.
        left;auto.
        simpl; apply DecPreOrder.le_lt_trans with a0; auto.
        destruct H;auto.
       right.  simpl.   now transitivity a0.
       simpl;   now transitivity b0.
Defined.


Lemma lex_of_equiv (a a':A)(b b':B) :
     a =A= a' ->  b =B= b' -> preorder_equiv (a,b) (a',b').
Proof.
 intros H1 H2; destruct H1, H2;split;
  right;auto;   split;auto.
Qed.

Lemma lex_inv_left (a a':A)(b b':B) :
  ((a,b) <=lex (a',b')) -> a <=A a'.
Proof.
  destruct 1 as [H | H];
  destruct H; auto.
Qed.

Lemma lex_inv_right (a a':A)(b b':B) :
  ((a,b) <=lex (a',b')) ->  a =A=  a' -> b <=B b'.
Proof.
 intros [H|H].   
  - destruct 1. 
     absurd (a'  <A a').
     + apply lt_irreflexive.
     + apply DecPreOrder.le_lt_trans with a;auto.
 - auto.
Qed.

Lemma lex_strict_intro_right  (a a':A)(b b':B) :
  a =A= a' -> b <B b' -> (a,b) <lex (a',b').
Proof.  
  intros H H1.
  split.
  right;auto.  
  now destruct H1.
  intro H2.
  absurd (b <B b).
  apply lt_irreflexive;auto.
  apply DecPreOrder.lt_le_trans with b';auto.
  apply (lex_inv_right _ _ _ _ H2).
  now symmetry.
Qed.

Lemma lex_strict_intro_left  (a a':A)(b b':B) :
  a <A a'  -> (a,b) <lex (a',b').
Proof.
  split. now  constructor.
  intro H0.
  apply (@lt_irreflexive _ _ PA a).
  apply DecPreOrder.lt_le_trans with a'; auto.
  apply (lex_inv_left _ _ _ _ H0).
Qed.

Global Instance To_lex_prod : TotalPreOrder lex_prod.
Proof.
  split.
  - apply PO_lex_prod.
  - destruct TA as [Apre Atot].
    destruct TB as [Bpre Btot].
    intros x y; destruct x, y.
    destruct (Atot a a0) as [HAle|HAle].
    * destruct (le_lt_equiv_dec a a0 HAle) as [Ha|Ha].
      + left;left;auto.
      + destruct (Btot b b0).
        { left;right;auto. }
        { right; right; simpl. now symmetry. assumption. }
    * destruct (le_lt_equiv_dec a0 a HAle).
      + right;left. assumption.
      + destruct (Btot b0 b).
        { right; right; simpl; assumption. }
        { left;  right;[ now symmetry | assumption]. }
Qed.

Global Instance lex_prod_dec : RelDecision lex_prod.
Proof.
intros x y; destruct x, y.
destruct (decide (leA a a0)) as [HAle|Hale].
- destruct (le_lt_equiv_dec a a0 HAle) as [Ha|Ha].
  * left;left;auto.
  * destruct (decide (leB b b0)) as [HBle|HBle].
    + left;right;auto.
    + right; intro Hle.
      contradict HBle.
      destruct Hle as [Hle|Hle].
      { simpl in Hle.
        destruct Ha.
        destruct Hle.
        contradiction. }
      { simpl in Hle.
        simpl in H.
        assumption. }
- right. intro Hle.
  destruct Hle as [Hle|Hle].
  * simpl in Hle.
    destruct Hle.
    contradiction.
  * simpl in Hle.
    contradict Hale.
    destruct Hle.
    assumption.
Defined.

End lexprod.





