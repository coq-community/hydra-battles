(** 

  Binary strategy, according to Bergeron, Brlek et al. 

  Let $n>3$ be a positive number. We associate to $n$ the half of $n$.
*)
 

Require Import Arith NArith Pow Compatibility More_on_positive Lia.
Require Export Strategies.

Open Scope positive_scope.

Definition half (p:positive) :=
  match p with xH => xH
          |    xI q | xO q =>  q
  end.



Instance Binary_strat : Strategy half.
Proof.
  split; destruct p; unfold half; try lia.
Qed.

