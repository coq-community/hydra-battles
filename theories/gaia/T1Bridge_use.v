
Require Import T1Bridge.
Import T1. 

Lemma L1 (a: T1):  omega * (a * omega) = omega * a * omega.
Proof.
   now rewrite multA.
Qed.
