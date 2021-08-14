(** Comparison between Hydra-battle's and Gaia's [T1]  

First experiments *)

From hydras Require T1.
From mathcomp Require Import all_ssreflect.
From gaia Require Import ssete9.

Set Implicit Arguments.
Unset Strict Implicit.

Fixpoint iota (alpha : T1.T1) : CantorOrdinal.T1 :=
  match alpha with
    T1.zero => zero
  | T1.ocons alpha n beta => cons (iota alpha) n (iota beta)
  end.

Fixpoint pi (alpha : CantorOrdinal.T1) : T1.T1 :=
  match alpha with
    zero => T1.zero
  | cons alpha n beta => T1.ocons (pi alpha) n (pi beta)
  end.


Lemma iota_pi alpha : iota (pi alpha) = alpha.
Proof.
elim: alpha => //=.
move => t1 IHalpha1 n t2 IHalpha2.
by rewrite IHalpha1 IHalpha2.
Qed.

Lemma pi_iota alpha:  pi (iota alpha) = alpha.
Proof.
elim: alpha => //=.
move => t1 IHalpha1 n t2 IHalpha2.
by rewrite IHalpha1 IHalpha2.
Qed.

Definition refines0 (x:T1.T1)(y:CantorOrdinal.T1) :=
y = iota x.

Definition refines1 (f:T1.T1 -> T1.T1)
 (f': CantorOrdinal.T1 -> CantorOrdinal.T1) :=
  forall x: T1.T1, f' (iota x) = iota (f x).

Definition refines2 (f:T1.T1 -> T1.T1 -> T1.T1)
 (f': CantorOrdinal.T1 -> CantorOrdinal.T1 -> CantorOrdinal.T1 ) :=
  forall x y : T1.T1, f' (iota x) (iota y) = iota (f x y).

Lemma refines1_R f f' :
  refines1 f f' ->
  forall y: CantorOrdinal.T1, f (pi y) = pi (f' y).
Proof.
move => Href y; rewrite -{2}(iota_pi y).
by rewrite Href pi_iota.
Qed.

Lemma phi0_ref x : refines0 (T1.phi0 x)  (CantorOrdinal.phi0 (iota x)).
Proof. by []. Qed.

Lemma one_ref : refines0 (T1.one) CantorOrdinal.one.
Proof. by []. Qed.

Lemma omega_ref : refines0 (T1.omega) CantorOrdinal.T1omega.
Proof. by []. Qed.

Lemma Finite_ref (n:nat) : refines0 (T1.fin n) (\F n).
Proof. by case: n. Qed.

Lemma ap_ref alpha : T1.ap alpha <-> CantorOrdinal.T1ap (iota alpha).
Proof.
split => Hap; first by case: Hap.
move: Hap; case: alpha => //=.
move => alpha n beta /andP [Hn Hz].
move/eqP: Hn Hz =>->; move/eqP.
by case: beta.
Qed.

Lemma T1eq_refl a : T1eq a a.
Proof. by apply/T1eqP. Qed.

Lemma compare_ref x :
  forall y, match T1.compare x y with
  | Lt => T1lt (iota x) (iota y)
  | Eq => iota x = iota y
  | Gt => T1lt (iota y) (iota x)
  end.
Proof.
elim: x => [|x1 IHx1 n x2 IHx2]; case => //= y1 n0 y2.
case H: (T1.compare x1 y1).
- specialize (IHx1 y1); rewrite H in IHx1.
  case H0: (PeanoNat.Nat.compare n n0).
  + have ->: (n = n0) by apply Compare_dec.nat_compare_eq.
    case H1: (T1.compare x2 y2).
    * rewrite IHx1; f_equal.
      by specialize (IHx2 y2); now rewrite H1 in IHx2.
    * case (iota x1 < iota y1); [trivial|].
      rewrite IHx1 eqxx /= eqxx ltnn.
      specialize (IHx2 y2).
      by rewrite H1 in IHx2.
    * rewrite IHx1 T1ltnn eqxx ltnn eqxx.
      specialize (IHx2 y2).
      by rewrite H1 in IHx2.
  + rewrite IHx1 T1ltnn eqxx.
    apply Compare_dec.nat_compare_Lt_lt in H0.
    by move/ltP: H0 =>->.
  + rewrite IHx1 T1ltnn eqxx.
     apply Compare_dec.nat_compare_Gt_gt in H0.
     by move/ltP: H0 =>->.
- specialize (IHx1 y1); rewrite H in IHx1; now rewrite IHx1.
- specialize (IHx1 y1); rewrite H in IHx1; now rewrite IHx1.
Qed.

Lemma plus_ref : refines2 T1.plus T1add.
Proof.
move => x; elim: x => [|x1 IHx1 n x2 IHx2]; case => //= y1 n0 y2.
case Hx1y1: (T1.compare x1 y1); move: (compare_ref x1 y1); rewrite Hx1y1 => H.
- by rewrite H T1ltnn /=; f_equal.
- by rewrite H /=; f_equal.
- replace (iota x1 < iota y1) with false.
    rewrite H /=; f_equal.
    change (cons (iota y1) n0 (iota y2)) with (iota (T1.ocons y1 n0 y2)).
    by rewrite IHx2.
  by apply T1lt_anti in H.
Qed.
