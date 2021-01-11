(**

   Prove that the Ackerman function [Ack] is not primitive recursive.
    One possible definition is as follows:
*)

Fixpoint iterate {A:Type}(f : A -> A) (n: nat)(x:A) :=
  match n with
  | 0 => x
  | S p => f (iterate  f p x)
  end.

Fixpoint Ack (m:nat) : nat -> nat :=
  match m with 0 => S
          |   S n => fun k =>  iterate (Ack n) (S k) 1
  end.



(** _There are many other definitions in the litterature. So feel free to 
    use the one you prefer *)

(**
<< 
Theorem AckIsntPR : ~ isPR 2 Ack.
Proof.
(* ... *)
Qed.
>>


 _This is not a trivial exercise. You may have to prove several additional 
lemmas_. 
 *)




