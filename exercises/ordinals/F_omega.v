Require Import Iterates F_alpha E0.
Require Import ArithRing Lia   Max Ack.
Import Exp2.
Require Import Mult.
Open Scope nat_scope.


Lemma F_vs_Ack n : 2 <= n -> Ack n n <= F_ omega  n.
Admitted. 


Require Import MoreVectors.
Import primRec extEqualNat VectorNotations.


Section F_alpha_notPR.

  Variable alpha: E0.
  Hypothesis H : omega o<= alpha.
  Hypothesis H0: isPR 1 (F_ alpha).

  Lemma F_alpha_not_PR: False.
  Admitted.

End F_alpha_notPR.


Theorem F_n_PR (n:nat)  : isPR 1 (F_  n).
Admitted.
