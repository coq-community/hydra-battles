(*  Pierre Casteran 
    LaBRI, Université Bordeaux 1, and Inria Futurs (Logical)
*)

Require Import Relations.
Section Sequences.
 Variable A : Set.

 Variable R : A -> A -> Prop. 

 Lemma not_acc : forall a b:A, R a b -> ~ Acc R a -> ~ Acc R b.
 Proof.
  intros a b H H0 H1.
  absurd (Acc R a); auto.
  generalize a H.
  elim H1; auto.
 Qed.

 Lemma acc_imp : forall a b:A, R a b -> Acc R b -> Acc R a.
 Proof.
  intros a b H H0.
  generalize a H. 
  elim H0; auto.
 Qed.


 Hypothesis W : well_founded R.
 Hint Resolve W : core.
	
 Section seq_intro.
  Variable seq : nat -> A. 

  Let is_in_seq (x:A) :=  exists i : nat, x = seq i.

  Lemma not_decreasing_aux : ~ (forall n:nat, R (seq (S n)) (seq n)). 
  Proof.
   unfold not in |- *; intro dec.
   cut (forall a:A, is_in_seq a -> ~ Acc R a).
   intro H.
   absurd (Acc R (seq 0)).
   apply H.
   exists 0; trivial. 
   apply W.
   intro a; pattern a in |- *.
   apply well_founded_ind with A R.
   assumption.
   intros x Hx H.
   elim H.
   intros i egi.  
   cut (R (seq (S i)) (seq i)).
   intro H1.
   rewrite egi.
   apply not_acc with (seq (S i)); auto.
   apply Hx.
   rewrite egi; auto.
   exists (S i); auto.
   auto.
 Qed.
 End seq_intro.

 Theorem not_decreasing :
  ~ (exists seq : nat -> A, (forall i:nat, R (seq (S i)) (seq i))).
 Proof.
  unfold not in |- *; intro H.
  case H; intros s Hs.
  absurd (forall i:nat, R (s (S i)) (s i)); auto.
  apply not_decreasing_aux.
 Qed.

End Sequences.

