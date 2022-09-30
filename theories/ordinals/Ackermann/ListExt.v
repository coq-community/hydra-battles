(**  Replaced some proofs with Stdlib's 
     Provisionally, we still export original names 
 *)



Require Import Coq.Lists.List.

Section List_Remove.

Variable A : Set.
Hypothesis Aeq_dec : forall a b : A, {a = b} + {a <> b}.

Definition list_remove (x : A) (l : list A) : list A :=
  list_rec (fun _ => list A) nil
    (fun (a : A) _ (recl : list A) =>
     match Aeq_dec a x with
     | left _ => recl
     | right _ => a :: recl
     end) l.

Lemma list_remove_compat x l  :
  list_remove x l = List.remove Aeq_dec x l.
Proof.
  induction l.
  - reflexivity. 
  -  simpl; case (Aeq_dec a x) ; simpl; intros; subst. 
     + case (Aeq_dec x x) ; now rewrite IHl. 
     + case (Aeq_dec x a).
       * subst; congruence. 
       * now rewrite IHl. 
Qed. 


Lemma In_list_remove1 :
 forall (a b : A) (l : list A), In a (list_remove b l) -> In a l.
Proof.
  intros a b l H; rewrite list_remove_compat in H.
  now destruct (in_remove _ _ _ _ H).
Qed.

Lemma In_list_remove2 :
 forall (a b : A) (l : list A), In a (list_remove b l) -> a <> b.
Proof.
  intros a b l H; rewrite list_remove_compat in H.
  now destruct (in_remove _ _ _ _ H).
Qed.




Lemma In_list_remove3 :
  forall (a b : A) (l : list A), In a l -> a <> b -> In a (list_remove b l).
  Proof. 
    intros; rewrite list_remove_compat; now apply in_in_remove. 
Qed. 

End List_Remove.

Section No_Duplicate.

Variable A : Set.
Hypothesis Aeq_dec : forall a b : A, {a = b} + {a <> b}.

Definition no_dup (l : list A) : list A :=
  list_rec (fun _ => list A) nil
    (fun (a : A) _ (rec : list A) =>
     match In_dec Aeq_dec a rec with
     | left _ => rec
     | right _ => a :: rec
     end) l.

Lemma nodup_compat (l: list A) :
  no_dup l = nodup Aeq_dec l.
Proof. 
  induction l. 
  - reflexivity. 
  - simpl; rewrite  IHl.
    case (in_dec Aeq_dec a (nodup Aeq_dec l)) .
    + destruct (nodup_In Aeq_dec l a) as [H H0].
      intro i; apply H in i; case (in_dec Aeq_dec a l).
        * auto. 
        * intro; contradiction.       
    + destruct (nodup_In Aeq_dec l a) as [H H0].
      case (in_dec Aeq_dec a l).
     * intro H1; apply H0 in H1; contradiction. 
     * reflexivity.
Qed. 



Lemma no_dup1 : forall (a : A) (l : list A),
    In a l -> In a (no_dup l).

Proof.
 intros a l H; rewrite nodup_compat; now rewrite  nodup_In.
Qed. 

Lemma no_dup2 : forall (a : A) (l : list A), In a (no_dup l) -> In a l.
Proof.
intros a l H; now rewrite nodup_compat, nodup_In in H.
Qed.


Lemma no_dup3 :
  forall (k l : list A) (a : A), no_dup k = a :: l -> ~ In a l.
Proof.
 intros k l a H. rewrite nodup_compat in H; apply (nodup_inv _ _ H). 
Qed. 


End No_Duplicate.
