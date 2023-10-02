(**  * Notations adapted from Mathcomp's ssrnat *)

Notation "n .+1" := (S n) (at level 2, left associativity,
  format "n .+1") : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2, left associativity,
  format "n .+2") : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2, left associativity,
  format "n .+3") : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2, left associativity,
  format "n .+4") : nat_scope.
Notation "n .+5" := n.+2.+3 (at level 2, left associativity,
  format "n .+5") : nat_scope.


Notation "n .-1" := (pred n) (at level 2, left associativity,
  format "n .-1") : nat_scope.
Notation "n .-2" := n.-1.-1 (at level 2, left associativity,
  format "n .-2") : nat_scope.
Notation "n .-3" := n.-2.-1 (at level 2, left associativity,
  format "n .-3") : nat_scope.
Notation "n .-4" := n.-3.-1 (at level 2, left associativity,
  format "n .-4") : nat_scope.
