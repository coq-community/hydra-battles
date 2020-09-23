(** Contains axioms (Admitted) 

To develop in another branch, then merge

    



Require Import ListOmega.
From Coq Require Import  Logic.Eqdep_dec.

Definition t := {l: t | nf l}.

Search sig.

Lemma List_compare_eq_nf  (l l':list nat) :
  nf l \/ nf l' -> ListOmega.compare l l' = Eq -> l = l'.
Admitted.

Definition compare (alpha beta:t) := ListOmega.compare (proj1_sig alpha)
                                                       (proj1_sig beta).

Lemma compare_eq_eq  alpha beta  : compare alpha beta = Eq -> alpha = beta.
Proof.
  destruct alpha, beta; unfold compare;cbn.
  intro.
  assert (x = x0) . { eapply List_compare_eq_nf; eauto. }
  subst.
  f_equal.
  apply eq_proofs_unicity_on.
  destruct y, (nf x0); (auto ||  (right; discriminate)).
Qed.


 *)
