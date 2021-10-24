Require Import T1.

Require Import T1Bridge.


Lemma L1 (a: T1):  omega * (a * omega) = omega * a * omega.
Proof.
   now rewrite multA.
Qed.
