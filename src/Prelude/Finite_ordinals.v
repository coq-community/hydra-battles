Require Import Arith Relations Lia Logic.Eqdep_dec.
Coercion is_true: bool >-> Sortclass.


Search (nat->nat->bool).

Definition t (n:nat) := {i:nat | Nat.ltb i  n}.

Definition lt {n:nat} : relation (t n) :=
  fun alpha beta => Nat.ltb ( proj1_sig alpha) (proj1_sig beta).

Lemma t0_empty (alpha: t 0): False.
Proof.
  destruct alpha.
  destruct x; cbn in i; discriminate.
Qed.

Definition compare {n:nat} (alpha beta : t (S n)) :=
  Nat.compare (proj1_sig alpha) (proj1_sig beta).

(** Too long ! *)

Lemma compare_reflect {n:nat} (alpha beta : t (S n)) :
  match (compare alpha beta)
  with
    Lt => lt alpha  beta
  | Eq => alpha = beta
  | Gt => lt beta  alpha
  end.

  destruct alpha, beta; cbn. 
  case_eq (x ?= x0); cbn.
  rewrite Nat.compare_eq_iff. intro; subst.
  f_equal;   apply eq_proofs_unicity_on.
  destruct (x0 <? S n),y; auto. right; discriminate.
  unfold lt;cbn.  
  destruct x0.
  destruct x; cbn.
  discriminate.
  discriminate.
  rewrite Nat.compare_lt_iff .
  Search (_ <=? _).
  intro; apply leb_correct.
  lia.
  intro.
  unfold lt;cbn.  
  destruct x; cbn.
  destruct x0.
  discriminate.
  discriminate.
  rewrite Nat.compare_gt_iff in H.
  apply leb_correct.
  lia.
Qed.


(** Examples *)

Program Definition alpha : t 10 := 5.

Program Definition beta : t 10 := 8.

Goal lt  alpha beta.
  now compute. 
Qed.

Program Definition inj {i : nat} (j:nat) (H: i <= j) (alpha: t i) : t j :=
   alpha.
Next Obligation.
  destruct alpha0. cbn.
   Search (_ <? _).
   
red in i0;rewrite  Nat.ltb_lt  in i0.
destruct j.
lia.
apply leb_correct.
 lia.
Qed. 


Remark r12: (10 <= 12)%nat.
  lia.
Qed.
Check inj  12  r12 beta.

Lemma inj_ok (i j  :nat)(H : i <= j) : forall alpha beta,
    lt alpha beta <->
    lt (inj j H alpha) (inj j H beta).
  split;  unfold lt; simpl; auto.
Qed.

