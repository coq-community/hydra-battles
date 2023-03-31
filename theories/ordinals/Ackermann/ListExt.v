(*  Replaced some proofs with Stdlib's *)

Require Import Coq.Lists.List.

Section List_Remove.

Variable A : Set.
Hypothesis Aeq_dec : forall a b : A, {a = b} + {a <> b}.

Lemma in_remove_neq:
 forall (a b : A) (l : list A), In a (List.remove Aeq_dec b l) -> a <> b.
Proof.
  intros a b l H; now destruct (in_remove _ _ _ _ H).
Qed.

End List_Remove.

#[deprecated(note="use ListExt.in_remove_neq instead")]
 Notation In_list_remove2 := in_remove_neq (only parsing).
