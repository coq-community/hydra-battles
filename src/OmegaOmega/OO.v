Require Import ListOmega.
From Coq Require Import  Logic.Eqdep_dec Wellfounded.
Require Import Arith.

Definition t := {l: t | nf l}.
Definition lt (w1 w2:t) := (wlt (proj1_sig w1) (proj1_sig w2)).

Lemma List_compare_eq_nf  (l l':list nat) :
  nf l -> nf l' -> ListOmega.compare l l' = Eq -> l = l'.
Proof.  
  destruct l.
  - destruct l'.    
    + trivial.
    + case n; discriminate.
  - case n.
    + discriminate.
    + intros n0 Hnfl. destruct l'.
      * discriminate.
      * destruct n1.
        -- discriminate.
        -- intro Hnfl'. simpl compare. case_eq (Nat.compare (length l) (length l')). 
           ++ intro. case_eq (Nat.compare n0 n1).
              ** intros. rewrite (Nat.compare_eq n0 n1 H0).
                 rewrite (compare_eq_len_eq l l').
                 --- trivial.
                 --- apply (Nat.compare_eq (length l) (length l') H).
                 --- assumption.
              ** discriminate.
              ** discriminate.
           ++ discriminate.
           ++ discriminate.
Qed.

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


Definition m : t -> list nat := fun x => proj1_sig x.

Lemma wf_lt : well_founded lt.
  apply (wf_measure t lt m); auto. 
Qed.
