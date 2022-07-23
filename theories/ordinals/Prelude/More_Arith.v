(*y  Florian Hatat, ENS-Lyon *)

(** Note by Pierre:

  Some lemmas of this file are possibly in Standard Library *)


From Coq Require Import Arith  Lia .
Import Nat.

Section Arith_lemmas.

  
Lemma nat_double_or_s_double :
  forall n, {exists p, n = double p} + {exists p, n = S (double p)}.
Proof.
  induction n as [| n IHn].
  -   left;  exists 0; auto with arith.
  -   induction IHn as [a | b].
   + right; destruct a as [x H]; exists x; now rewrite H.
   + left; destruct b as [x H]; exists (S x).
     rewrite H;  symmetry. cbn; unfold double; lia.
Qed.

Lemma div2_double_is_id :forall n : nat, div2 (double n) = n.
Proof. 
  induction n as [ | n IHn].
  -  reflexivity.  
  -  replace (double (S n)) with (S (S (double n))).
     replace (S n) with (S (div2 (double n))); auto.
     symmetry.  unfold double; lia.
Qed.

Lemma double_S (n:nat) : double (S n) = S (S (double n)).
Proof. unfold double; ring. Qed.

Lemma double_plus (x y: nat): double (x + y)= double x + double y.
Proof. rewrite !double_twice. ring. Qed. 
  
Lemma double_inj :
  forall (m n : nat), double m = double n -> m = n.
Proof.
  intros m n double_eq; unfold double in double_eq;  abstract lia.
Qed.

Lemma double_is_even :
  forall n : nat, Nat.Even (double n).
Proof. intro n; exists n; unfold double; ring. Qed.

Lemma not_double_is_s_double :
  forall (m n : nat),  S (double m) <> double n.
Proof. intros; unfold double; lia. Qed.


Lemma div2_of_Even n: Nat.Even n -> double (div2 n) = n.
Proof. intros [p Hp]; subst; now rewrite div2_double, double_twice.
Qed. 

Lemma even_prod :
  forall p q, Nat.Even ((p + q + 1) * (p + q)).
Proof.
  intros p q;  destruct (Even_or_Odd  (p + q)).
  - destruct H as [m Hm]; rewrite Hm; exists ((2 * m + 1) * m); ring.   - destruct H as [m Hm]; rewrite Hm; exists ((m + 1) * (2 * m + 1));     ring. 
Qed. 


Lemma plus_2 :
  forall n, S (S n) = n + 2.
Proof. intro n;  now rewrite (add_comm n 2). Qed.

Lemma div2_incr :
  forall n m, n <= m -> div2 n <= div2 m.
Proof.
  intros n m;
    destruct (nat_double_or_s_double n) as [[p Hp] | [p Hp]];
    subst;
    destruct (nat_double_or_s_double m) as [[q Hq] | [q Hq]];
    subst. 
  - rewrite !div2_double_is_id ;unfold double; lia.
  - rewrite !div2_double_is_id, !double_twice, div2_succ_double; lia.  - rewrite (double_twice p), div2_succ_double;                           rewrite !div2_double_is_id, double_twice; lia. 
  - rewrite !double_twice; rewrite !div2_succ_double. lia. 
Qed.

Lemma div2_even_plus :
  forall n m, Even n -> div2 n + m = div2 (n + (double m)).
Proof.
  intros n m [p Hp]; apply double_inj. subst. 
  rewrite <- !double_twice.
  replace  (double p + double m) with (double (p + m)).
   now rewrite !div2_double_is_id. 
   rewrite !double_twice; lia. 
Qed.

Lemma mult_lt_lt :
  forall p p' k, p * k < p' * k -> p < p'.
Proof.
  intros p p' k Hin;  case (le_lt_dec p' p); [| trivial].
  -  intros p_in; rewrite  lt_nge in Hin; contradict Hin.
         now apply Nat.mul_le_mono.
Qed.

Lemma minus_semi_assoc :
  forall a b c, b > c -> a + (b - c) = (a + b) - c.
Proof.
  intros a b c;  abstract lia.
Qed.

Lemma div_not_qlt :
  forall (a b : nat) (q q' r r' : nat),
    a = q * b + r -> a = q' * b + r' -> b > r -> b > r' -> ~ q < q'.
Proof.
  intros a b q q' r r' Hdiv Hdiv' Hrem Hrem' Hqlt.
  assert (Hle: b <= r).
  {  
   -  apply le_trans with (r - r').
   +   rewrite <- Nat.mul_1_l with b.
       replace (r - r') with ((q' - q) * b).
       * apply mul_le_mono_r; abstract lia.
       *   transitivity (q' * b - q * b).
           {  apply Nat.mul_sub_distr_r. }
           symmetry; apply Nat.add_sub_eq_l. 
           rewrite minus_semi_assoc with r' (q' * b) (q * b).
            apply Nat.add_sub_eq_l. 
            transitivity a.
            now symmetry.
          
         { now rewrite Nat.add_comm with r' (q' * b).   }
         unfold gt; apply mult_lt_compat_r.
         assumption.
         apply le_lt_trans with r; auto with arith.
   + apply le_minus.
  }
  rewrite   (Nat.lt_nge  r b ) in Hrem; contradiction.
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


(** From Cantor contrib *)

Notation power := Nat.pow (only parsing).

Lemma power_of_1 : forall p, power 1 p = 1.
 induction p; simpl.
 auto.
 rewrite IHp;auto.
Qed.
 
Goal forall a b, 0 < power (S a) b.
 induction b.
 simpl;auto.
 simpl.
 auto with arith.
Save power_positive.


Lemma pred_of_power : forall b e, pred (power (S b) (S e)) =
                                  (power (S b) e)*b  + 
                                  pred (power (S b) e).
 simpl.
 intros;generalize ((S b) ^e).
 destruct n.
 simpl.
 rewrite mult_0_r.
 simpl;auto.
 rewrite (Nat.mul_comm b (S n)).
simpl.
ring.
Qed.

(* some tools *)

(* this kind of argument must replace a lot of steps in proofs.
   must define the same for cpnf and ordinals *)



Lemma get_predecessor : forall (n:nat), 0 < n -> {p:nat | n = S p}.
 intro n; case n.
 intro ; absurd (0<0); auto with arith. 
 intro n0; exists n0;auto.
Qed.

Ltac pred_exhib H name := 
  match type of H
       with O < ?n =>
         case (get_predecessor  H); intro name; intro 
  end.




(* about euclidean division *)

Lemma Euc1 : forall b q  q' r r', 0 < b -> 
                                  q*b + r = q'*b + r' -> 
                                  r < b -> r' < b -> q = q'.
intros; case (lt_eq_lt_dec q q').
destruct 1.
assert (S q <= q').
auto with arith.
assert ((S q)*b + r <= q' *b + r).
apply plus_le_compat_r. 
apply mult_le_compat_r.
auto.
simpl in H4.
rewrite <- plus_assoc in H4.
rewrite H0 in H4.
lia.
auto.
intro.
assert (S q' <= q).
auto with arith.
assert ((S q')*b + r <= q *b + r).
apply plus_le_compat_r. 
apply mult_le_compat_r.
auto.
simpl in H4.
rewrite <- plus_assoc in H4.
rewrite H0 in H4.
lia.
Qed.
(*
Lemma Euc2 : forall b q  q' r r', 0 < b -> 
               q*b+r = q'*b+r' -> r < b -> r' < b -> r =r'.
 intros.
 rewrite (Euc1  q q' H H0 H1 H2) in H0.
 omega.
Qed.

*)

(*Lemma max_le_regR : forall n p q, p <= q -> max p n <= max q n.
  intros; case (max_dec p n).
 intro e;rewrite e.
 apply le_trans with q.
 auto.
  apply le_max_l.
 intro e;rewrite e.
 apply le_max_r.
Qed.
*)
(*Lemma max_le_regL :  forall n p q, p <= q -> max n p <= max n q.
  intros; rewrite (max_comm n p);rewrite (max_comm n q).
  apply max_le_regR.
  auto.
Qed.




Lemma lt_lt_Sn : forall a b c, a < b -> b < S c -> a < c.
 eauto with arith.
Qed.

*)


 
