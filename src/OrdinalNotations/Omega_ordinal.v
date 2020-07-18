(**  The ordinal omega  *)
Require Import Arith Compare_dec Lia  OrdinalNotations.Definitions
        Finite_ordinals.
Import Relations RelationClasses.

Search (@StrictOrder nat).
Search @Nat.compare.
Search (@well_founded nat).


Instance Omega : OrdinalNotation Nat.lt_strorder Nat.compare.
Proof.
 split.
 - apply Wf_nat.lt_wf.
 - apply Nat.compare_spec.
 - intro x; destruct x.
     + left; left. intro n; destruct n.
      * right.
      * left; auto with arith.
     + right; exists x. split.
       * auto with arith.
       * lia.
Qed.



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


