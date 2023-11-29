(** 

  Binary strategy, according to Bergeron, Brlek et al. 

  Let $n>3$ be a positive number. We associate to $n$ the half of $n$.
*)
 

From Coq Require Import Arith NArith Lia.
From additions Require Import  Pow Compatibility More_on_positive.
From additions Require Export Strategies.

Open Scope positive_scope.

(* begin snippet BinaryStrats:: no-out *)
Definition half (p:positive) :=
  match p with xH => xH
          |    xI q | xO q =>  q
  end.

Definition two (p:positive) := 2%positive.

#[ global ] Instance Binary_strat : Strategy half.
Proof.
  split; destruct p; unfold half; try lia.
Qed.

#[ global ] Instance Two_strat : Strategy two.
Proof.
  split;unfold two; lia.
Qed.
(* end snippet BinaryStrats *)
