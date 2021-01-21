(** Proof that the Ackermann function is not primitive recursive *)


From hydras Require Import  primRec extEqualNat. 
Require Import Iterates. (* For masking [iterate] *)


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

(** _There are many other definitions in the litterature. So feel free to 
    use the one you prefer, but it must respect the "equations" above *)


Theorem AckIsntPR : isPR 2 Ack -> False.
Admitted.


(**
 _This is not a trivial exercise. You may have to prove several additional 
lemmas. 
 *)





