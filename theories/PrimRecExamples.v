Require Import primRec.
Import extEqualNat.

Compute naryFunc 3.
(* = nat -> nat -> nat -> nat
     : Set
 *)

Check plus : naryFunc 2.



Remark R01 : 0 < 1.
  auto.
Qed.

Check composeFunc 1 2 (PRcons 1 1 (projFunc 1 0 R01)
                               (PRcons 1 0 (projFunc 1 0 R01)
                                       (PRnil 1)) ).

Definition exp2_aux  := iterate (fun i => i * 2)  .
Definition exp2 := fun n => exp2_aux n 1.
Compute exp2 5.

About compose2IsPR.

Check compose2 1.
Locate compose2.


Definition mystere :=  compose2 1 (fun n => S n) mult.
Check mystere. 
Compute mystere 3.
Compute mystere 6.



Lemma exp2PR n : isPR 1 (exp2_aux n).
Proof.
  unfold exp2.  apply iterateIsPR.
  Search isPR mult.
  Search isPR S.
Abort.

