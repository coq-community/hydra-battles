(** Please Consider the following (tail-recursive) definition of the
 Fibonacci sequence *)

(** This function is also studied in #<a href="https://github.com/coq-community/coq-art">the exercises of coq-art</a># (chap 9) *)


Fixpoint general_fib (a0 a1 n:nat) {struct n} : nat :=
  match n with
  | O => a0
  | S p => general_fib a1 (a0 + a1) p
  end.

Definition fib_tail (n:nat) := general_fib 1 1 n.


(** Prove that [fib_tail] is primitive recursive.

<< 
Theorem fibIsPR : isPR 1 fib_tail.
Proof.
(* ... *)
Qed.
>>

 _This is not a trivial exercise. You may have to prove several additional 
lemmas_. 
 *)




