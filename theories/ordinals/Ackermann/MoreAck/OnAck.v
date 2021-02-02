Require Import primRec Arith ArithRing List Ack MoreVectors.
Import extEqualNat.

Check evalList.

Compute  evalList 2 (Vector.cons  7  (Vector.cons   9  (Vector.nil ))) plus.

Definition apply2 (f: naryFunc 2)
           (v: Vector.t nat 2) : nat :=
  evalList 2 v  f.
  
Goal forall f x y, apply2 f
                          (Vector.cons  x 
                                       (Vector.cons   y 
                                                     (Vector.nil )))
                   = f x y.
  intros; cbn.
  trivial.
Qed.

Require Import Compare_dec Max.


Fixpoint max_v {n:nat} : forall (v: Vector.t nat n) , nat :=
  match n as n0 return (Vector.t nat n0 -> nat)
  with
    0 => fun v => 0
  | S p => fun (v : Vector.t nat (S p)) =>
             (max (Vector.hd v) (max_v   (Vector.tl v)))
               end. 

Compute max_v  (Vector.cons  5  (Vector.cons  8  (Vector.nil ))).

Compute max_v
        (Vector.cons  17  (Vector.cons  5  (Vector.cons  8  Vector.nil ))).


Definition P n (f: naryFunc n) := exists (N:nat),
  forall (v: Vector.t nat n), evalList _ v f <= Ack N (max_v  v).



Definition P_PR n (x : PrimRec n) :=
  P _ (evalPrimRec _ x).
Locate map.
About map.

Definition Ps n m (fs : Vector.t (naryFunc n) m) :=
  exists N, forall (v: t nat n),
      max_v (map (fun f => evalList _ v f) fs) <= Ack N (max_v v).

Definition Ps_PR n m (x : PrimRecs n m) :=
  Ps _ _ (evalPrimRecs _ _ x).

About PrimRec_PrimRecs_ind.


  

Lemma P_PR_Succ : P_PR _ succFunc.
red.
exists 1.
intro v.
 replace v with (Vector.cons (Vector.hd v)  (Vector.nil)).
 simpl evalList.
 simpl max_v.
 rewrite max_0_r.
  rewrite Ack_1_n.
  auto with arith.
  now rewrite decomp1.
Qed.



Lemma P_PR_Zero : P_PR _ zeroFunc.
Proof.
  exists 0.
  intro v; rewrite  (zero_nil _ v), Ack_0. cbn; auto with arith.
 Qed.

Lemma L: forall n (x: PrimRec n),  P_PR n x.
  intros n x; induction x using PrimRec_PrimRecs_ind with
                  (P0 := fun n m y => Ps_PR n m y).
(*

7 subgoals (ID 103)
  
  ============================
  P_PR 1 succFunc

subgoal 2 (ID 104) is:
 P_PR 0 zeroFunc
subgoal 3 (ID 112) is:
 P_PR n (projFunc n m l)
subgoal 4 (ID 119) is:
 P_PR n (composeFunc n m g x)
subgoal 5 (ID 125) is:
 P_PR (S n) (primRecFunc n x1 x2)
subgoal 6 (ID 126) is:
 Ps_PR n 0 (PRnil n)
subgoal 7 (ID 133) is:
 Ps_PR n (S m) (PRcons n m x p)
 *)
  - apply P_PR_Succ.
  - apply P_PR_Zero.
  - 
red. cbn. red.
    exists 0.
    rewrite Ack_0.
    Search evalProjFunc.
    Search evalList.
    admit.
  - admit.
  - admit.
  - red. cbn.  red. exists 0.
    intro; rewrite Ack_0.
    cbn. auto with arith.
  - red; cbn. red.
    destruct IHx.
    destruct IHx0.
    exists (max x0 x1).
    admit.
Admitted.




