(**  The ordinal omega  *)

From Coq Require Import Arith Compare_dec Lia.
From hydras.OrdinalNotations  Require Import Generic ON_Finite.
From hydras Require Import Schutte.

Import Relations RelationClasses.

Global Instance Omega : ON  Peano.lt Nat.compare.
Proof.
 split.
 - apply Nat.lt_strorder.
 - apply Wf_nat.lt_wf.
 - apply Nat.compare_spec.
Qed.



Definition Zero_limit_succ_dec : ZeroLimitSucc_dec.
 - intro x; destruct x.
     + left; left. intro n; destruct n.
      * right.
      * left; auto with arith.
     + right; exists x. split.
       * auto with arith.
       * intros z H H0.  lia.
Defined.



Global Instance FinOrd_Omega (i:nat) :
  SubON (FinOrd i) Omega i 
             (fun alpha =>  proj1_sig alpha).
Proof.
  split.
  - reflexivity.
  - destruct x as [x H]; cbn;  now apply  Nat.ltb_lt in H. 
  - intros y H;  refine (ex_intro _ (exist _ y _) _).
    + reflexivity.
      Unshelve.
      now apply  Nat.ltb_lt in H.
Qed.


Require Import Schutte.


Instance omega_ok : ON_correct omega Omega finite.
Proof.
  split.
  - apply finite_lt_omega.
  - intros beta Hbeta; destruct (lt_omega_finite Hbeta) as [i Hi].
    exists i; now subst.
  -  intros n p; destruct (Nat.compare_spec n p).
     + now subst.
     + now apply finite_mono.
     + now apply finite_mono.
Qed.

