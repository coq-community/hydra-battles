From hydras Require Import E0 Canon Paths  MoreLists Large_Sets.


(* naive proofs *)

Example ex_pathS1 : pathS T1.omega (2::3::4::nil) 1.
Proof.
  do 2   ( eright;[esplit;[discriminate |reflexivity ] | ]).
  simpl. left. split ; simpl; auto with T1.
  discriminate. 
Qed.

Example ex_pathS2 : pathS T1.omega (interval 3 6) 1.
Proof.
  do 3  ( eright;[esplit;[discriminate |reflexivity ] | ]).
  simpl.
  left. split ; simpl; auto with T1.
  discriminate.
Qed.





Example omega_omega_1_4 : gnaw (T1.omega ^ T1.omega) (interval 1 4) = 0.
Proof. trivial. Qed.

Example omega_omega_1_3 : gnaw (T1.omega ^ T1.omega) (interval 1 3) = 1.
Proof. trivial. Qed.



Inductive answer : Set := Ok | Too_far | Remaining (rest : ppT1).

Definition large_set_check alpha i j :=
  let beta := gnaw alpha (interval i (Nat.pred j))
  in match beta with
     | one => Ok
     | zero => Too_far
     |  _ => Remaining (pp (canon beta j))
     end.

(* begin snippet gnawEx1 *)

Compute pp (gnaw (T1.omega * T1.omega) (interval 6 70)).

(* end snippet gnawEx1 *)

(* begin snippet gnawEx2 *)

Compute  (gnaw (T1.omega * T1.omega) (interval 6 700)).

(* end snippet gnawEx2 *)


Compute pp (  gnaw (T1.omega * T1.omega) (interval 6 509)).

Global Hint Resolve iota_from_lt_not_In: core.

(* begin snippet Ex1Lemma *)

(*| .. coq:: no-out |*)
Example Ex1 : mlarge (T1.omega * T1.omega) (interval 6 510).
Proof with try (auto with arith || discriminate ).
  unfold interval; simpl Peano.minus. 
  do 2 rewrite iota_from_unroll; rewrite mlarge_iff  ... 
  repeat rewrite not_in_cons ...  
Qed.  
(*||*)
(* end snippet Ex1Lemma *)

Compute large_set_check T1.omega 1 2.

Compute large_set_check T1.omega 2 3.

Compute large_set_check T1.omega 3 3.


Compute large_set_check T1.omega 3 6.



Compute large_set_check T1.omega 49 98.

Compute large_set_check (T1.omega + 2) 49 (2 * (49 + 2)).

Compute large_set_check (T1.omega + 10) 49 (2 * (49 + 10)).



Compute large_set_check (T1.omega * 2) 2 10.

Compute large_set_check (T1.omega * 2) 3 14.

Compute large_set_check (T1.omega * 2) 4 18.




Compute large_set_check (T1.omega ^ 2) 1 4.

Compute large_set_check (T1.omega ^ 2) 2 5.

Compute large_set_check (T1.omega ^ 2) 2 6.

Compute large_set_check (T1.omega ^ 2) 2 14.

Compute large_set_check (T1.omega ^ 2) 3 18.

Compute large_set_check (T1.omega ^ 2) 3 38.

Compute large_set_check (T1.omega ^ 2) 4 94.

Compute large_set_check (T1.omega ^ 2) 5 222.

Compute large_set_check (T1.omega ^ 2) 6 510.

Compute large_set_check (T1.omega ^ 2) 7 1150.



Compute large_set_check (T1.omega ^ T1.omega) 1 4.

Compute large_set_check (T1.omega ^ T1.omega) 2 38.

Compute large_set_check (T1.omega ^ T1.omega) 3 1000.

Compute large_set_check (T1.omega ^ T1.omega) 3 1798.


Compute large_set_check (T1.omega ^ T1.omega) 3 1799.

Compute large_set_check (T1.omega ^ T1.omega) 3 5000.

Compute large_set_check (T1.omega ^ (T1.omega + 1)) 3 5000.
 

Compute pp (gnaw (T1.omega ^ 2) (interval 2 5)).

Compute pp (gnaw (T1.omega ^ 2) (interval 2 12)).

Compute large_set_check (T1.omega ^ 2) 2 14.

Compute pp (gnaw (T1.omega ^ 2) (interval 3 38)).

Compute large_set_check (T1.omega ^ 2) 3  38.

Compute pp (gnaw (T1.omega ^ 2) (interval 4 94)).

Compute large_set_check (T1.omega ^ 2) 4  94.


Compute large_set_check (T1.omega ^ T1.omega) 1 6.

Compute large_set_check (T1.omega ^ T1.omega) 2 38.

Compute large_set_check T1.omega 33 34.



Compute  pp (gnaw (T1.omega * T1.omega * 2)%t1 (interval 2 15)). 

Compute  pp (gnaw (T1.omega * T1.omega * 2)%t1 (interval 2 32)). 

Compute  pp (gnaw (T1.omega * T1.omega * 2)%t1 (interval 2 66)). 

Compute  pp (gnaw (T1.omega * T1.omega * 2)%t1 (interval 2 134)).

Compute  pp (gnaw (T1.omega * T1.omega * 2)%t1 (interval 2 270)).

Compute  pp (gnaw (T1.omega * T1.omega * 2)%t1 (interval 2 542)).

Compute  pp (gnaw (T1.omega * T1.omega * 2)%t1 (interval 2 1086)).

Compute  pp (gnaw (T1.omega * T1.omega * 2)%t1 (interval 2 2174)).


