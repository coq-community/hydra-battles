(** Proof that the Ackermann function is not primitive recursive *)


From hydras Require Import  primRec extEqualNat Ack.
Import Iterates. (* For masking [iterate] *)

(** Compatibility between Ackermann Library's [primrec.iterate]
 and [Prelude.Iterates.iterate] *)
 

Lemma iterate_compat {f : nat -> nat}(n:nat)(x:nat):
  Iterates.iterate f n x = primRec.iterate f n x.
Proof.
  induction n; cbn.
   - reflexivity.
   - now rewrite IHn.
Qed.



(** The Ackerman function is defined in the library 
   [hydras.Prelude.Iterates]  *)

Locate Ack.

(** 
<<
Fixpoint Ack (m:nat) : nat -> nat :=
  match m with 0 => S
          |   S n => fun k =>  iterate (Ack n) (S k) 1
  end.


Lemma ack_0_p p : Ack 0 p = S p.
Proof.
 reflexivity.
Qed.

Lemma ack_Sn_0  (n:nat) : Ack (S n) 0 = Ack n 1.
Proof.
reflexivity.
Qed.

Lemma ack_Sn_Sp (n p:nat): Ack (S n) (S p) =
                           Ack n (Ack (S n) p).
Proof.
 reflexivity.
Qed.
>>
*)


 
Theorem  Ackn_IsPR (n: nat) : isPR 1 (Ack n).
Admitted. (* exercise *)


Theorem AckIsntPR : isPR 2 Ack -> False.
  (*  Still in project. Not proved yet *)
Admitted.





