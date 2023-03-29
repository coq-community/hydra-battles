(**  Replaced some proofs with Stdlib's 
     Provisionally, we still export original lemma names 
 *)

Require Import Coq.Lists.List.

Section List_Remove.

Variable A : Set.
Hypothesis Aeq_dec : forall a b : A, {a = b} + {a <> b}.

Lemma In_list_remove2 :
 forall (a b : A) (l : list A), In a (List.remove Aeq_dec b l) -> a <> b.
Proof.
  intros a b l H; now destruct (in_remove _ _ _ _ H).
Qed.

(* TO do : replace this lemma with in_in_remove (and permute the two new sub-goals) (see LNN2LNT, L 398) *)
Lemma In_list_remove3 :
  forall (a b : A) (l : list A), 
    In a l -> a <> b -> In a (List.remove Aeq_dec b l).
  Proof. 
    intros; now apply in_in_remove. 
Qed. 


End List_Remove.

