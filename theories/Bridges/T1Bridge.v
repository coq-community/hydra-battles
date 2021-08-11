(** Comparison between Hydra-battle's and Gaia's [T1]  *)




From hydras Require  T1.
From gaia Require Import ssete9.


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
           (f': CantorOrdinal.T1 ->CantorOrdinal.T1) :=
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

Locate phi0.




Lemma phi0_ref x :  refines0 (T1.phi0 x)  (CantorOrdinal.phi0 (iota x)).
Proof.
   reflexivity. 
Qed.


