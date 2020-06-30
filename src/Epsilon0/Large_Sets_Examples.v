Require Import E0 Canon Paths  MoreLists Large_Sets.


(* naive proofs *)

Example ex_pathS1 : pathS omega (2::3::4::nil) 1.
Proof.
  do 2   ( eright;[esplit;[discriminate |reflexivity ] | ]).
  simpl. left. split ; simpl; auto with T1.
  discriminate. 
Qed.

Example ex_pathS2 : pathS omega (interval 3 6) 1.
Proof.
  do 3  ( eright;[esplit;[discriminate |reflexivity ] | ]).
  simpl.
  left. split ; simpl; auto with T1.
  discriminate.
Qed.





Example omega_omega_1_4 : gnaw (omega ^omega) (interval 1 4) = 0.
Proof. trivial. Qed.

Example omega_omega_1_3 : gnaw (omega ^omega) (interval 1 3) = 1.
Proof. trivial. Qed.



Inductive answer : Set := Ok | Too_far | Remaining (rest : ppT1).

Definition large_set_check alpha i j :=
  let beta := gnaw alpha (interval i (Nat.pred j))
  in match beta with
     | one => Ok
     | zero => Too_far
     |  _ => Remaining (pp (canon beta j))
     end.

Compute pp (gnaw (omega * omega) (interval 6 70)).

Compute  (gnaw (omega * omega) (interval 6 700)).

Compute pp (  gnaw (omega * omega) (interval 6 509)).

Hint Resolve iota_from_lt_not_In: core.

Example Ex1 : mlarge (omega * omega) (interval 6 510).
Proof with try (auto with arith || discriminate ).
  unfold interval; simpl Peano.minus. 
  do 2 rewrite iota_from_unroll.  rewrite mlarge_iff  ... 
  repeat rewrite not_in_cons ...  
Qed.  


Compute large_set_check omega 1 2.

Compute large_set_check omega 2 3.

Compute large_set_check omega 3 3.


Compute large_set_check omega 3 6.



Compute large_set_check omega 49 98.

Compute large_set_check (omega + 2) 49 (2 * (49 + 2)).

Compute large_set_check (omega + 10) 49 (2 * (49 + 10)).



Compute large_set_check (omega * 2) 2 10.

Compute large_set_check (omega * 2) 3 14.

Compute large_set_check (omega * 2) 4 18.




Compute large_set_check (omega ^ 2) 1 4.

Compute large_set_check (omega ^ 2) 2 5.

Compute large_set_check (omega ^ 2) 2 6.

Compute large_set_check (omega ^ 2) 2 14.

Compute large_set_check (omega ^ 2) 3 18.

Compute large_set_check (omega ^ 2) 3 38.

Compute large_set_check (omega ^ 2) 4 94.

Compute large_set_check (omega ^ 2) 5 222.

Compute large_set_check (omega ^ 2) 6 510.

Compute large_set_check (omega ^ 2) 7 1150.



Compute large_set_check (omega ^ omega) 1 4.

Compute large_set_check (omega ^ omega) 2 38.

Compute large_set_check (omega ^ omega) 3 1000.

Compute large_set_check (omega ^ omega) 3 1798.


Compute large_set_check (omega ^ omega) 3 1799.

Compute large_set_check (omega ^ omega) 3 5000.

Compute large_set_check (omega ^ (omega + 1)) 3 5000.
 

Compute pp (gnaw (omega ^ 2) (interval 2 5)).

Compute pp (gnaw (omega ^ 2) (interval 2 12)).

Compute large_set_check (omega ^ 2) 2 14.

Compute pp (gnaw (omega ^ 2) (interval 3 38)).

Compute large_set_check (omega ^ 2) 3  38.

Compute pp (gnaw (omega ^ 2) (interval 4 94)).

Compute large_set_check (omega ^ 2) 4  94.


Compute large_set_check (omega ^ omega) 1 6.

Compute large_set_check (omega ^ omega) 2 38.

Compute large_set_check omega 33 34.



Compute  pp (gnaw (omega * omega * 2)%t1 (interval 2 15)). (* omega * 15 *)

Compute  pp (gnaw (omega * omega * 2)%t1 (interval 2 32)). (* omega * 14 *)

Compute  pp (gnaw (omega * omega * 2)%t1 (interval 2 66)). (* omega * 13 *)

Compute  pp (gnaw (omega * omega * 2)%t1 (interval 2 134)). (* omega * 12 *)

Compute  pp (gnaw (omega * omega * 2)%t1 (interval 2 270)). (* omega * 11 *)

Compute  pp (gnaw (omega * omega * 2)%t1 (interval 2 542)). (* omega * 10 *)

Compute  pp (gnaw (omega * omega * 2)%t1 (interval 2 1086)). (* omega * 9 *)

Compute  pp (gnaw (omega * omega * 2)%t1 (interval 2 2174)). (* omega * 8 *)


