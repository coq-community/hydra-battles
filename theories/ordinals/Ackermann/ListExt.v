(**  Replaced some proofs with Stdlib's 
     Provisionally, we still export original names 
 *)

Require Import Coq.Lists.List.

Section List_Remove.

Variable A : Set.
Hypothesis Aeq_dec : forall a b : A, {a = b} + {a <> b}.

Fixpoint list_remove (x : A) (l : list A) : list A :=
  match l with
    nil => l
  | a::l => match Aeq_dec a x with
            | left _ => list_remove x l
            | right _ => a :: list_remove x l
            end
  end.

Print List.remove. 

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


