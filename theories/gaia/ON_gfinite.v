(** ordinals a la mathcomp *)
From hydras Require Import DecPreOrder ON_Generic.
From mathcomp Require Import all_ssreflect zify.
From gaia Require Export ssete9.
From Coq Require Import Logic.Eqdep_dec.

Set Implicit Arguments.
Unset Strict Implicit.
Set Program Cases.

(* begin snippet finordLtDef *)
Definition finord_lt (n:nat) (alpha beta: 'I_n): bool :=
  (alpha < beta)%N.

#[global] Instance  finord_compare (n:nat) : Compare ('I_n) :=
  fun alpha beta => Nat.compare alpha beta. 
(* end snippet finordLtDef *)


Lemma finord_compare_correct (n:nat) (alpha beta : 'I_n) :
  CompSpec eq (@finord_lt n) alpha beta (compare alpha beta).
Proof.
  case  (PeanoNat.Nat.compare_spec alpha beta) => H.
  - move : H; rewrite /nat_of_ord /compare.
    destruct alpha, beta => ?; subst. 
    have Heq:i = i0. 
    + apply eq_proofs_unicity_on. decide equality.  
    + subst; rewrite /finord_compare PeanoNat.Nat.compare_refl. 
      constructor; reflexivity. 
  - replace (compare alpha beta) with Datatypes.Lt.
    + constructor; rewrite /finord_lt;  by apply /ltP. 
    + symmetry; by rewrite /compare PeanoNat.Nat.compare_lt_iff. 
  - replace (compare alpha beta) with Datatypes.Gt. 
    + constructor; rewrite /finord_lt; by apply /ltP. 
    + symmetry; by rewrite /compare PeanoNat.Nat.compare_gt_iff. 
Qed. 


#[global] Instance finord__sto n : StrictOrder (@finord_lt n).
Proof. 
 split.
 - move => x; by rewrite /complement /finord_lt ltnn. 
 - move => x y z; rewrite /finord_lt; apply ltn_trans.   
Qed.


#[global] Instance finord__comp n :
  Comparable (@finord_lt n) (@finord_compare n).
Proof. 
 split.
 - apply finord__sto.
 - apply finord_compare_correct. 
Qed.

Lemma finord_lt_wf n : well_founded (@finord_lt n).
Proof.
  pose m (n:nat) (x:'I_n) := nat_of_ord x. 
  move => x;  rewrite /finord_lt.
  apply Acc_incl with (fun x y => m _ x < m _ y)%N.
  - move => a b; by rewrite /m.
  - apply (Acc_inverse_image ('I_n) nat (fun n p=> (n < p)%N) (@m n) x), lt_wf. 
Qed. 

(* begin snippet finordON:: no-out *)
#[global] Instance finord_ON n : ON (@finord_lt n) (@finord_compare n).
(* end snippet finordON *)
Proof.
 split.
 - apply finord__comp.
 - apply finord_lt_wf.
Qed.

(** Examples *)

(* begin snippet Examples:: no-out *)
#[program] Example o_33_of_42: 'I_42 := @Ordinal 42 33 _.


#[program] Example o_36_of_42: 'I_42 :=  @Ordinal 42 36 _.
(* end snippet Examples *)
(* begin snippet Examplesb *)
Compute compare  o_33_of_42  o_36_of_42.
(* end snippet Examplesb *)



