Require Import Iterates F_alpha E0.
Require Import ArithRing Lia   Max Ack.
Import Exp2.
Require Import Mult.
Open Scope nat_scope.


Lemma F_vs_Ack n : 2 <= n -> Ack n n <= F_ omega  n.
Admitted. 
