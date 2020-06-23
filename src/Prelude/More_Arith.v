(* Florian Hatat, ENS-Lyon *)

(* Note by Pierre:

  Some lemmas of this file are possibly in Standard Library *)


Require Import Arith  Div2  Even  Omega Max.

Section Arith_lemmas.

Lemma nat_double_or_s_double :
  forall n, {exists p, n = double p} + {exists p, n = S (double p)}.
Proof.
  induction n as [| n IHn].
  -   left;  exists 0; auto with arith.
  -   induction IHn as [a | b].
   + right; destruct a as [x H]; exists x; now rewrite H.
   + left; destruct b as [x H]; exists (S x).
     rewrite H;  symmetry; apply double_S.
Qed.

Lemma div2_double_is_id :
  forall n : nat, div2 (double n) = n.
Proof.
  induction n as [ | n IHn].
  -  reflexivity.  
  -  replace (double (S n)) with (S (S (double n))).
     replace (S n) with (S (div2 (double n))); auto.
     symmetry; apply double_S.
Qed.

Lemma double_inj :
  forall (m n : nat), double m = double n -> m = n.
Proof.
  intros m n double_eq; unfold double in double_eq;  omega.
Qed.

Lemma double_is_even :
  forall n : nat, even (double n).
Proof.
  induction n.
 - constructor.   
 -  replace (double (S n)) with (S (S (double n))).
    +   now apply even_S, odd_S.
    +  symmetry; apply double_S.
Qed.

Lemma not_double_is_s_double :
  forall (m n : nat),  S (double m) <>  double n.
Proof.
  intros m n eq;  apply (not_even_and_odd (double n)).
  -   apply double_is_even.
  -   rewrite <- eq;  apply odd_S;  apply double_is_even.
Qed.

Lemma even_prod :
  forall p q, even ((p + q + 1) * (p + q)).
Proof.
  intros p q;  case (even_odd_dec (p + q)).
  -   intro Hev; now apply even_mult_r.
  -   intro Hod; apply even_mult_l; replace (p + q + 1) with (S (p + q)).
      + now apply even_S.
      +  omega.
Qed.

Lemma plus_2 :
  forall n, S (S n) = n + 2.
Proof.
  intro n;  now rewrite (plus_comm n 2).
Qed.

Lemma div2_incr :
  forall n m, n <= m -> div2 n <= div2 m.
Proof.
  intros n m Hle;  case le_lt_dec with (div2 n) (div2 m).
  -  trivial.
  -  intros Hlt; case lt_not_le with m n; try assumption.
     assert (Hd : double (div2 m) < double (div2 n)).
     {  unfold double; now apply plus_lt_compat.
     }
     case (even_odd_dec m);
       intro Hm; [rewrite even_double with m | rewrite odd_double with m];
       try assumption;
       (case (even_odd_dec n);
        intros Hn; [rewrite even_double with n | rewrite odd_double with n];
        try assumption).
     +   apply lt_trans with (double (div2 n)); auto with arith.
     +   unfold lt; rewrite <- double_S with (div2 m).
         rewrite odd_div2 with m; try assumption.
         unfold double; apply plus_le_compat;
         rewrite <- odd_div2 with m; assumption.
     + auto with arith.
Qed.

Lemma div2_even_plus :
  forall n m, even n -> div2 n + m = div2 (n + (double m)).
Proof.
  intros n m even_n; apply double_inj.
  rewrite <- even_double with (n + double m).
  -  rewrite double_plus with (div2 n) m.
     now rewrite <- even_double with n.
  -  apply even_even_plus; auto.
     apply double_is_even.
Qed.

Lemma mult_lt_lt :
  forall p p' k, p * k < p' * k -> p < p'.
Proof.
  intros p p' k Hin;  case (le_lt_dec p' p).
  - intros p_in;  case lt_not_le with (p * k) (p' * k).
    + assumption.
    +  apply mult_le_compat_r; assumption.
  -   trivial.
Qed.

Lemma minus_semi_assoc :
  forall a b c, b > c -> a + (b - c) = (a + b) - c.
Proof.
  intros a b c;  omega.
Qed.

Lemma div_not_qlt :
  forall (a b : nat) (q q' r r' : nat),
    a = q * b + r -> a = q' * b + r' -> b > r -> b > r' -> ~ q < q'.
Proof.
  intros a b q q' r r' Hdiv Hdiv' Hrem Hrem' Hqlt.
  apply lt_not_le with r b.
   -  assumption.
   -  apply le_trans with (r - r').
   +   rewrite <- mult_1_l with b.
       replace (r - r') with ((q' - q) * b).
       * apply mult_le_compat_r;   omega.
       *   transitivity (q' * b - q * b).
         {  apply mult_minus_distr_r. }
            apply plus_minus.
         rewrite minus_semi_assoc with r' (q' * b) (q * b).
         apply plus_minus.
         transitivity a.
         { rewrite plus_comm with r' (q' * b); symmetry; assumption. }
         {  assumption. }
         unfold gt; apply mult_lt_compat_r.
         assumption.
         apply le_lt_trans with r; auto with arith.
   + apply le_minus.
Qed.

Lemma div_eucl_unique :
  forall (a b : nat) (q q' r r' : nat),
    a = q * b + r -> a = q' * b + r' -> b > r -> b > r' -> q = q' /\ r = r'.
Proof.
  intros a b q q' r r' Hdiv Hdiv' Hrem Hrem'.
  assert (q_eq : q = q').
  {
    case lt_eq_lt_dec with q q'; [intro Hq; case Hq; clear Hq | ]; intro Hin.

    (* q < q' *)
    case div_not_qlt with a b q q' r r'; assumption.
    (* q = q' *)
    assumption.
    (* q' < q *)
    case div_not_qlt with a b q' q r' r; assumption.
  }
  split; try assumption.
  apply plus_reg_l with (q * b).
  transitivity a; congruence.
Qed.

Lemma max_le_plus (n p: nat) : Nat.max n p <= n + p.
Proof. 
  destruct (Nat.le_ge_cases n p). 
  - rewrite (max_r _ _ H); auto with arith.
  - rewrite (max_l _ _ H); auto with arith. 
Qed.    




Lemma max_le_regR : forall n p q, p <= q -> max p n <= max q n.
  intros; case (max_dec p n).
 intro e;rewrite e.
 apply le_trans with q.
 auto.
  apply le_max_l.
 intro e;rewrite e.
 apply le_max_r.
Qed.

Lemma max_le_regL :  forall n p q, p <= q -> max n p <= max n q.
  intros; rewrite (max_comm n p);rewrite (max_comm n q).
  apply max_le_regR.
  auto.
Qed.




Lemma lt_lt_Sn : forall a b c, a < b -> b < S c -> a < c.
 eauto with arith.
Qed.
End Arith_lemmas.


