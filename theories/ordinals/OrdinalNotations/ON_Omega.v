(**  A notation system for the ordinal [omega]  *)
(** Pierre Castéran, Univ. Bordeaux and LaBRI *)


From Coq Require Import Arith Compare_dec Lia.
From hydras  Require Import ON_Generic ON_Finite.
From hydras Require Import Schutte.

Import Relations RelationClasses.

#[global]
Instance compare_nat : Compare nat := Nat.compare.

(* begin snippet OmegaDefa:: no-out *)
#[global]
 Instance Omega_comp : Comparable Peano.lt compare_nat.
Proof.
  split.
  - apply Nat.lt_strorder.
  - apply Nat.compare_spec.
Qed.

#[global]
 Instance Omega : ON Peano.lt compare_nat.
Proof.
 split.
 - apply Omega_comp.
 - apply Wf_nat.lt_wf.
Qed.
(* end snippet OmegaDefa *)

(* begin snippet OmegaDefb *)

#[local] Open Scope ON_scope.

Compute 6 o?= 9.
(* end snippet OmegaDefb *)


Definition Zero_limit_succ_dec : ZeroLimitSucc_dec.
 - intro x; destruct x.
     + left; left. intro n; destruct n.
      * right.
      * left; auto with arith.
     + right; exists x. split.
       * auto with arith.
       * intros z H H0; lia.
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



Instance omega_ok : ON_correct Schutte_basics.omega Omega finite.
Proof.
  split.
  - apply finite_lt_omega.
  - intros beta Hbeta; destruct (lt_omega_finite Hbeta) as [i Hi].
    exists i; now subst.
  -  intros n p; unfold compare_nat; destruct (Nat.compare_spec n p).
     + now subst.
     + now apply finite_mono.
     + now apply finite_mono.
Qed.

