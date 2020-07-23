(**  The ordinal omega  *)
Require Import Arith Compare_dec Lia  OrdinalNotations.Definitions
        Finite_ordinals.
Import Relations RelationClasses.
Locate lt.
Search (@StrictOrder nat).
Search @Nat.compare.
Search (@well_founded nat).


Global Instance Omega : ON  Peano.lt Nat.compare.
Proof.
 split.
 - apply Nat.lt_strorder.
 - apply Wf_nat.lt_wf.
 - apply Nat.compare_spec.
Qed.

Definition Zero_limit_succ_dec : ZeroLimitSucc_dec (on := Omega).
 - intro x; destruct x.
     + left; left. intro n; destruct n.
      * right.
      * left; auto with arith.
     + right; exists x. split.
       * auto with arith.
       * intros z H H0. Search Nat.lt. lia.
Defined.



Global Instance FinOrd_Omega (i:nat) :
  SubSegment (FinOrd i) Omega i 
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


