
Require Import Iterates F_alpha E0.
Require Import ArithRing Lia   Max.
Import Exp2.
Require Import Mult.
Open Scope nat_scope.


Lemma exp2_gt_id : forall n, n < exp2 n.
Admitted.

Lemma LF3 : dominates_from 2 (F_ 3) (fun  n => iterate exp2 n n).
Admitted.


Theorem F_alpha_Sn alpha : 3 o<= alpha ->
                   forall n, 2 <= n -> exp2 (F_ alpha n) <= F_ alpha (S n).
Admitted.
