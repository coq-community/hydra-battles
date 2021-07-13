(*  FIXME !!!

Require Import ListOmega.
From Coq Require Import  Logic.Eqdep_dec Wellfounded.
Require Import Arith.
Require Import RelationClasses.
Require Import ON_Generic.
Import Relation_Operators.

Definition t := {l: t | nf l}.
Definition lt (w1 w2:t) := (wlt (proj1_sig w1) (proj1_sig w2)).
Definition le := leq lt.

Instance lt_strorder : StrictOrder lt.
Proof.
  split.
  - unfold Irreflexive. unfold Reflexive. unfold complement.
    unfold lt. intro. apply wlt_irref.
  - unfold Transitive. unfold lt. intros. 
    apply wlt_trans with (w2:=(proj1_sig y)); assumption.
Qed.

Definition m : t -> list nat := fun x => proj1_sig x.

Lemma wf_lt : well_founded lt.
  apply (ListOmega.wf_measure t lt m); auto. 
Qed.

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
        -- intro Hnfl'; simpl compare.
           case_eq (Nat.compare (length l) (length l')). 
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

Lemma compare_lt_lt alpha beta : (compare alpha beta)=Lt -> (lt alpha beta).
Proof.
unfold compare. unfold lt. apply compare_lt_wlt.
Qed.

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

Lemma compare_gt_lt alpha beta : (compare alpha beta)=Gt -> (lt beta alpha).
Proof.
  unfold compare. unfold lt. apply compare_gt_wlt.
Qed.

Lemma compare_reflect alpha beta :
  match (compare alpha beta) with
    Lt => (lt alpha beta)
  | Eq => (alpha=beta)
  | Gt => (lt beta alpha)
  end.
Proof. 
case_eq (compare alpha beta).
- apply compare_eq_eq.
- apply compare_lt_lt.
- apply compare_gt_lt.
Qed.

Lemma compare_correct alpha beta :
  CompareSpec (alpha=beta) (lt alpha beta) (lt beta alpha) (compare alpha beta).
Proof.
  generalize (compare_reflect alpha beta).
  destruct (compare alpha beta); now constructor.
Qed.

Instance OO_comp : Comparable lt compare.
Proof.
  split.
  - apply lt_strorder.
  - apply compare_correct.
Qed.

Instance OmegaOmega : ON lt compare.
Proof.
  split.
  - apply OO_comp.
  - apply wf_lt.
Qed.


Definition plus (alpha beta: t): t.
Proof.
  destruct alpha as [a nfa]; destruct beta as [b nfb];
     exists (ListOmega.plus a b); apply nf_plus.
Defined.

Infix "+" := plus : oo_scope.

Definition mult (alpha beta: t): t.
Proof.
  destruct alpha as [a nfa]; destruct beta as [b nfb];
     exists (ListOmega.mult a b); apply nf_mult.
Defined.

Infix "*" := mult : oo_scope.


Definition zero: t.
Proof.
  exists ListOmega.zero; now compute.
Defined. 

Definition _omega: t.
Proof.
  exists (ListOmega.omega); reflexivity.
Defined.

Notation omega := _omega.

Definition finS (i:nat) : t.
Proof.
  exists (ListOmega.fin_list (S i)); now cbn.
Defined.


Definition fin (i:nat) : t :=
  match i with 0 => zero
          | S j =>  finS j
  end.
                            
Coercion fin: nat >-> t.

Example Ex42: (omega + 42 + omega * omega = omega * omega)%oo.
Proof. 
  now rewrite <-  Comparable.compare_eq_iff.
Qed.



 *)
