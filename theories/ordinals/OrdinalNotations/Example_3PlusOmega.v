(** A proof of isomorhism between ordinal notations for 3+omega and omega *)

(** Pierre Castéran, Univ. Bordeaux and LaBRI *)

From hydras Require Import ON_plus ON_Finite ON_Omega.
Import ON_Generic.
From Coq Require Import Compare_dec Lia Logic.Eqdep_dec.



Definition O3O  :=  ON_plus (FinOrd 3) Omega.
Existing Instance O3O.

Arguments ON_t : clear implicits.
Arguments ON_t {A lt cmp} _.


Program Definition f (z: ON_t O3O) : ON_t Omega :=
  match z with inl i => i | inr j => 3+j end.


Program Definition g (a : ON_t Omega) : ON_t O3O :=
  match (le_lt_dec 3 a) with
    left _ => inr (a - 3)
  | right _ => inl a
  end.
Next Obligation.
  now apply Ltb_ij.
Defined.


Instance L_3_plus_omega :  ON_Iso _ _ f g.
Proof.
  split.
  - destruct x, y; cbn.
    +  destruct t0; unfold compare; cbn; destruct t; reflexivity.
    + cbn; destruct t.
      red in i; assert (x < 3) by (now rewrite PeanoNat.Nat.ltb_lt in i).
      rewrite PeanoNat.Nat.compare_lt_iff; simpl; lia.
    + cbn; destruct t.
      destruct x; auto.
      destruct x; auto.
      destruct x; auto.
      assert (S (S (S x)) < 3) by
       (red in i; rewrite PeanoNat.Nat.ltb_lt in i; lia);
        cbn; lia.
  +  reflexivity.
  - destruct a.
    + destruct t; cbn; unfold g;  destruct (le_lt_dec 3 x).
      exfalso; red in i; rewrite  PeanoNat.Nat.ltb_lt in i; lia.
      f_equal.
      f_equal.
      unfold g_obligation_1.
      red in i; apply eq_proofs_unicity_on.
      destruct y.
      * left; auto.
      * right; rewrite i; discriminate.
    + cbn; unfold g; destruct (le_lt_dec 3 (S (S (S n)))).
      f_equal; lia.
      lia.
  - unfold f, g; intro b; destruct (le_lt_dec 3 b).
    + lia.
    + auto.
Defined.


