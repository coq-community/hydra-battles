Require Import Arith.
Require Import Div2.
Require Import Even.
Require Import Lia.

Section Arith_lemmas.

Lemma nat_double_or_s_double :
  forall n, {exists p, n = double p} + {exists p, n = S (double p)}.
Proof.
  induction n.
  apply left.
  exists 0; auto with arith.
  induction IHn.
  apply right.
  destruct a.
  exists x.
  auto.
  apply left.
  destruct b.
  exists (S x).
  rewrite H.
  symmetry; apply double_S.
Qed.

Lemma div2_double_is_id :
  forall n : nat, div2 (double n) = n.
Proof.
  intro n.
  induction n.
  replace (double 0) with 0; auto.
  replace (double (S n)) with (S (S (double n))).
  replace (S n) with (S (div2 (double n))); auto.
  symmetry; apply double_S.
Qed.

Lemma double_inj :
  forall (m n : nat), double m = double n -> m = n.
Proof.
  intros m n double_eq.
  unfold double in double_eq.
  lia.
Qed.

Lemma double_is_even :
  forall n : nat, even (double n).
Proof.
  intro n.
  induction n.
  replace (double 0) with 0.
  apply even_O.
  auto.
  replace (double (S n)) with (S (S (double n))).
  apply even_S.
  apply odd_S.
  assumption.
  symmetry.
  apply double_S.
Qed.

Lemma not_double_is_s_double :
  forall (m n : nat), ~ (S (double m) = double n).
Proof.
  intros m n eq.
  apply (not_even_and_odd (double n)).
  apply double_is_even.
  rewrite <- eq.
  apply odd_S.
  apply double_is_even.
Qed.

Lemma even_prod :
  forall p q, even ((p + q + 1) * (p + q)).
Proof.
  intros p q.
  case (even_odd_dec (p + q)).
  intro Hev; apply even_mult_r; assumption.
  intro Hod; apply even_mult_l; replace (p + q + 1) with (S (p + q)).
  apply even_S; assumption.
  lia.
Qed.

Lemma plus_2 :
  forall n, S (S n) = n + 2.
Proof.
  intro n.
  replace 2 with (1 + 1).
  rewrite (plus_assoc n 1 1).
  cut (forall m, S m = m + 1).
  intro H.
  replace (S n) with (n + 1); auto with arith.
  intro m; rewrite (plus_comm m 1); auto with arith.
  auto with arith.
Qed.

Lemma div2_incr :
  forall n m, n <= m -> div2 n <= div2 m.
Proof.
  intros n m Hle.
  case le_lt_dec with (div2 n) (div2 m).
  trivial.
  intros Hlt.
  case lt_not_le with m n; try assumption.
  assert (Hd : double (div2 m) < double (div2 n)).
  unfold double; apply plus_lt_compat; assumption.

  case (even_odd_dec m);
    intro Hm; [rewrite even_double with m | rewrite odd_double with m]; try assumption;
    (case (even_odd_dec n);
    intros Hn; [rewrite even_double with n | rewrite odd_double with n]; try assumption).
  apply lt_trans with (double (div2 n)); auto with arith.
  unfold lt; rewrite <- double_S with (div2 m).
  rewrite odd_div2 with m; try assumption.
  unfold double; apply plus_le_compat;
    rewrite <- odd_div2 with m; assumption.
  auto with arith.
Qed.

Lemma div2_even_plus :
  forall n m, even n -> div2 n + m = div2 (n + (double m)).
Proof.
  intros n m even_n.
  apply double_inj.
  rewrite <- even_double with (n + double m).
  rewrite double_plus with (div2 n) m.
  rewrite <- even_double with n.
  trivial.
  assumption.
  apply even_even_plus; auto.
  apply double_is_even.
Qed.

Lemma mult_lt_lt :
  forall p p' k, p * k < p' * k -> p < p'.
Proof.
  intros p p' k Hin.
  case (le_lt_dec p' p).
  intros p_in.
  case lt_not_le with (p * k) (p' * k).
  assumption.
  apply mult_le_compat_r; assumption.
  trivial.
Qed.

Lemma minus_semi_assoc :
  forall a b c, b > c -> a + (b - c) = (a + b) - c.
Proof.
  intros a b c.
  lia.
Qed.

Lemma div_not_qlt :
  forall (a b : nat) (q q' r r' : nat),
    a = q * b + r -> a = q' * b + r' -> b > r -> b > r' -> ~ q < q'.
Proof.
  intros a b q q' r r' Hdiv Hdiv' Hrem Hrem' Hqlt.
  apply lt_not_le with r b.
  assumption.
  apply le_trans with (r - r').
  rewrite <- mult_1_l with b.
  replace (r - r') with ((q' - q) * b).
  apply mult_le_compat_r.
  lia.
  transitivity (q' * b - q * b).
  apply mult_minus_distr_r.
  apply plus_minus.
  rewrite minus_semi_assoc with r' (q' * b) (q * b).
  apply plus_minus.
  transitivity a.
  rewrite plus_comm with r' (q' * b); symmetry; assumption.
  assumption.
  unfold gt; apply mult_lt_compat_r.
  assumption.
  apply le_lt_trans with r; auto with arith.
  apply le_minus.
Qed.

Lemma div_eucl_unique :
  forall (a b : nat) (q q' r r' : nat),
    a = q * b + r -> a = q' * b + r' -> b > r -> b > r' -> q = q' /\ r = r'.
Proof.
  intros a b q q' r r' Hdiv Hdiv' Hrem Hrem'.
  assert (q_eq : q = q').
    case lt_eq_lt_dec with q q'; [intro Hq; case Hq; clear Hq | ]; intro Hin.

    (* q < q' *)
    case div_not_qlt with a b q q' r r'; assumption.
    (* q = q' *)
    assumption.
    (* q' < q *)
    case div_not_qlt with a b q' q r' r; assumption.

  split; try assumption.
  apply plus_reg_l with (q * b).
  transitivity a.
  symmetry; assumption.
  rewrite q_eq; assumption.
Qed.

End Arith_lemmas.
