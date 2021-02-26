Require Import Iterates F_alpha E0.
Require Import ArithRing Lia   Max.
Import Exp2 Canon.
Require Import Mult.
Open Scope nat_scope.


Section S1.
  Hypothesis H : forall (alpha beta:E0), alpha o<= beta ->
                                         forall i,  2 <= i ->
                                                    F_ alpha i <= F_ beta i.

 

  Lemma Fake_thm : False.
  Admitted.

End S1.


