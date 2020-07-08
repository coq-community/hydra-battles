(**  The ordinal omega  *)
Require Import Arith Compare_dec Lia Simple_LexProd Ordinal_generic
        Finite_ordinals.
Import Relations.

Search (@StrictOrder nat).
Search @Nat.compare.
Search (@well_founded nat).


Instance Omega : OrdinalNotation Nat.lt_strorder Nat.compare.
Proof.
 split.
 - apply Nat.compare_spec.
 - apply Wf_nat.lt_wf.
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


