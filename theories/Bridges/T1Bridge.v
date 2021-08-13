(** Comparison between Hydra-battle's and Gaia's [T1]  

First experiments *)


From hydras Require  T1.
From gaia Require Import ssete9.

Coercion is_true: bool >-> Sortclass.

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


Lemma iota_pi alpha:  iota (pi alpha) = alpha.
Proof.
  induction alpha.
  - trivial.
  - cbn; now rewrite IHalpha1, IHalpha2. 
Qed.

Lemma pi_iota alpha:  pi (iota alpha) = alpha.
Proof.
  induction alpha.
  - trivial.
  - cbn; now rewrite IHalpha1, IHalpha2. 
Qed.

Definition refines1 (f:T1.T1 -> T1.T1)
           (f': CantorOrdinal.T1 -> CantorOrdinal.T1) :=
  forall x: T1.T1, f' (iota x) = iota (f x).

Definition refines0 (x:T1.T1)(y:CantorOrdinal.T1) :=
y = iota x.


Lemma refines1_R f f' :
  refines1 f f' ->
  forall y: CantorOrdinal.T1, f (pi y) = pi (f' y).
Proof.
  intros H y;  rewrite <- (iota_pi y) at 2; 
  now rewrite H, pi_iota.
Qed.

Lemma phi0_ref x : refines0 (T1.phi0 x)  (CantorOrdinal.phi0 (iota x)).
Proof. reflexivity. Qed.


Lemma one_ref : refines0 (T1.one) CantorOrdinal.one.
Proof. reflexivity. Qed.

Lemma omega_ref : refines0 (T1.omega) CantorOrdinal.T1omega.
Proof. reflexivity. Qed.

Lemma Finite_ref (n:nat) : refines0 (T1.fin n) (\F n).
Proof.  destruct n; reflexivity. Qed.

(* clumsy ! *)

Lemma ap_ref alpha : T1.ap alpha  <-> CantorOrdinal.T1ap (iota alpha).
Proof.
  split; intro H.
  -  now inversion_clear H.
  -  destruct alpha.
     + discriminate.
     + cbn in H; destruct (andb_prop _ _ H).
       destruct (@T1eqP (iota alpha2) zero); try discriminate.
       destruct (@ssrnat.eqnP n 0); try discriminate.
       subst;  assert (alpha2 = T1.zero) by
       (destruct alpha2; [trivial | discriminate]).
       subst; constructor.
Qed.

