Require Import Iterates F_alpha E0.
Require Import ArithRing Lia   Max Ack.
Import Exp2.
Require Import Mult.
Open Scope nat_scope.


Lemma F_vs_Ack n : 2 <= n -> Ack n n <= F_ omega  n.
Admitted. 


Require Import MoreVectors.
Import primRec extEqualNat VectorNotations.


Section F_omega_notPR.

  Hypothesis F_omega_PR : isPR 1 (F_ omega).


  Lemma F_omega_not_PR : False.
  Admitted.

End F_omega_notPR.
