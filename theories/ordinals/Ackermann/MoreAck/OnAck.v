Require Import primRec Arith ArithRing List Ack MoreVectors Lia.
Require Import Compare_dec Max.
Import extEqualNat.


(** Maximum in a vector of nat *)

Fixpoint max_v {n:nat} : forall (v: Vector.t nat n) , nat :=
  match n as n0 return (Vector.t nat n0 -> nat)
  with
    0 => fun v => 0
  | S p => fun (v : Vector.t nat (S p)) =>
             (max (Vector.hd v) (max_v   (Vector.tl v)))
  end. 



Lemma evalList_Const : forall n (v:t nat n) x,
    evalList n v (evalConstFunc n x) = x.
Proof.
  induction n; cbn.
  - intros; cbn ; replace v with (@nil nat).
    + now  cbn.
    +  symmetry; apply zero_nil.
  - intros; cbn; rewrite (decomp _ _ v); cbn; auto.
Qed.

Lemma proj_le_max : forall n, forall v : t nat n, forall k (H: k < n),
        evalList n v (evalProjFunc n k H) <= max_v v.
Proof.
  induction n.
  -  cbn; intros; lia.
  - intros; specialize (IHn (tl v));  cbn.
    destruct (Nat.eq_dec k n).
    +  cbn;  rewrite (decomp _ _ v);  cbn; rewrite  evalList_Const;
         apply le_max_l.
    + destruct (le_lt_or_eq k n (lt_n_Sm_le k n H)).
     *  replace v with (cons (hd v) (tl v)) at 1; cbn.
       --   transitivity (max_v (tl v));  auto. 
            apply le_max_r.
       --  symmetry; apply decomp. 
     *  destruct( n0 e).
Qed. 


Lemma evalListComp : forall n  (v: t nat n) m (gs: t (naryFunc n) m)
                            (h: naryFunc  m),
    evalList n v (evalComposeFunc _ _ gs h) =
    evalList m (map (fun g =>  evalList _ v g) gs) h.
Proof.
  induction n.
  - intros; rewrite (zero_nil _ v); cbn.
    induction m.
    + rewrite (zero_nil _ gs); cbn; auto.  
    + rewrite (decomp _ _ gs);  cbn. 
      simpl naryFunc in *.
      specialize (IHm (tl gs) (h (vfst gs))); now rewrite IHm.
  -   intros; induction m.
      + rewrite (zero_nil _ gs);  cbn.
        rewrite (decomp _ _ v); cbn.   
        specialize (IHn (tl v) 0 (nil) h); rewrite IHn;  cbn;  auto.
      +  rewrite (decomp _ _ v).
         rewrite (decomp _ _ gs).
         specialize (IHm  (tl gs)).
         cbn.
         specialize (IHn (tl v)).
         rewrite IHn; cbn.
         f_equal.
         f_equal.
         generalize m gs.
         induction m0.
         * cbn; intros; rewrite (decomp1  gs0); cbn; auto.
         *   intros; replace gs0 with
                         (cons (hd gs0) (cons (hd (tl gs0)) (tl (tl gs0)))).
             -- cbn; cbn in *; specialize (IHm0  (tl gs0));  rewrite IHm0; auto.
             --  rewrite decomp;  f_equal.  now rewrite decomp.
Qed.


Lemma max_v_lub : forall n (v: t nat n) y,
    (Forall (fun x =>  x <= y) v) ->
    max_v v <= y.
Proof.
  induction n.  
  -  intros v; rewrite (zero_nil _ v); cbn.
     intros; auto with arith.
  -   intros v; rewrite (decomp _ _ v); cbn.
      intros;  destruct (Forall_inv _ _ _  _ H). apply max_lub; auto. 
Qed.

Definition P n (f: naryFunc n) := exists (N:nat),
    forall (v: Vector.t nat n), evalList _ v f <= Ack N (max_v  v).


Definition P_PR n (x : PrimRec n) :=  P _ (evalPrimRec _ x).

Definition Ps n m (fs : Vector.t (naryFunc n) m) :=
  exists N, forall (v: t nat n),
      max_v (map (fun f => evalList _ v f) fs) <= Ack N (max_v v).

Definition Ps_PR n m (x : PrimRecs n m) :=  Ps _ _ (evalPrimRecs _ _ x).


Lemma P_PR_Succ : P_PR _ succFunc.
Proof.
  exists 1; intro v.
  replace v with (Vector.cons (Vector.hd v)  (Vector.nil)).
  simpl evalList; simpl max_v; rewrite max_0_r.
  -   rewrite Ack_1_n; auto with arith.
  -  now rewrite decomp1.
Qed.



Lemma P_PR_Zero : P_PR _ zeroFunc.
Proof.
  exists 0;
  intro v; rewrite  (zero_nil _ v), Ack_0. cbn; auto with arith.
Qed.


Lemma L: forall n (x: PrimRec n),  P_PR n x.
Proof.
  intros n x; induction x using PrimRec_PrimRecs_ind with
                  (P0 := fun n m y => Ps_PR n m y).
  (*

2 remaining  subgoals (ID 103)
  

subgoal 4 (ID 119) is:
 P_PR n (composeFunc n m g x)
subgoal 5 (ID 125) is:
 P_PR (S n) (primRecFunc n x1 x2)
   *)
  - apply P_PR_Succ.
  - apply P_PR_Zero.
  - red; cbn; red; exists 0.
    rewrite Ack_0; intro v; transitivity (max_v v).
    + apply proj_le_max.
    + auto with arith.
  - (*
  n, m : nat
  g : PrimRecs n m
  x : PrimRec m
  IHx : Ps_PR n m      g
  IHx0 : P_PR m x      
  ===================== =======
  P_PR n (composeFunc n m g x)
     *)
    destruct IHx, IHx0.
    red.
eexists (2 + max x0 x1). 
intro v.
    specialize (H0 (map (fun f : naryFunc n => evalList n v f) (evalPrimRecs n m g))).
    pose (X:= (map (fun f : naryFunc n => evalList n v f) (evalPrimRecs n m g))).
     fold X in H0 ; fold X.

   admit. (* later *)
  - (*

  1 subgoal (ID 107)
  
  n : nat
  x1 : PrimRec n
  x2 : PrimRec (S (S n))
  IHx1 : P_PR n x1
  IHx2 : P_PR (S (S n)) x2
  ============================
  P_PR (S n) (primRecFunc n x1 x2)
    *)
    admit. (* later *)
  - red;cbn;  red; exists 0.
    intro; rewrite Ack_0.
    cbn; auto with arith.
  - red; cbn; red.
    destruct IHx, IHx0; exists (max x0 x1).
    intros v;  cbn.
    specialize (H0 v).
    pose (X :=
            (max_v (map (fun f : naryFunc n => evalList n v f)
                        (evalPrimRecs n m p)))).
    fold X ; fold X in H0.
    specialize (H v).
    pose (Y := evalList n v (evalPrimRec n x)).
    fold Y; fold Y in H.
    apply Nat.max_lub.
    + transitivity (Ack x0 (max_v v)); auto.
      apply Ack_mono_l.
      apply le_max_l.
    + transitivity (Ack x1 (max_v v)); auto.
      apply Ack_mono_l. 
      apply le_max_r.
Admitted.

Section Impossibility_Proof.

  Hypothesis HAck : isPR 2 Ack.
  
  
Lemma L1 : exists (n:nat), forall x y,  Ack x y <= Ack n (x + y).
destruct HAck as [x Hx].
generalize (L 2 x).
intros.
red in H.
red in H.
destruct H as [N HN].
exists N.
 intros; specialize (HN (cons x0 (cons y nil))).
 cbn in HN.
replace (evalPrimRec 2 x x0 y) with (Ack x0 y) in HN.
 rewrite max_0_r in HN.
transitivity  (Ack N (Nat.max x0 y)); auto.
apply Ack_n_mono_weak.
apply Ack_properties.
lia.

symmetry; apply Hx.
Qed.


Section Contrad.
  Variable n: nat.
  Hypothesis  Hn :  forall x y,  Ack x y <= Ack n (x + y) .

  Remark R01 : n <> 0.
  Proof.
    intro H;  subst; specialize (Hn 2 1).
    compute in Hn; lia.
  Qed.


  Remark R02: n <> 1.
  Proof. 
    intro H; subst; specialize (Hn 2 2).
    compute in Hn;  lia.
  Qed.

  Remark R03 : max 2 n = n.
  Proof.
    apply PeanoNat.Nat.max_r.
    case_eq  n; intro.
    -  destruct (R01 H).
    -  destruct n0.
       +  intro H; destruct (R02 H).
       + intro; subst. auto with arith.
  Qed.

  Remark R04 : Ack n (2 * n + 3) = Ack n (Ack 2 n).
  Proof.
    now rewrite Ack_2_n.
  Qed.
  
  Remark R05 : Ack n (2 * n + 3) <= Ack (n + 2) n.
  Proof.
    transitivity (Ack n (Ack 2 n)).
    -  now  rewrite  R04.
    - replace (n+2) with  (2 + max n 2).
      +  apply  Ack_Ack_le.
      + rewrite PeanoNat.Nat.add_comm;  now rewrite Max.max_comm, R03.
  Qed.  

  Remark R06 : Ack (n+ 2) n <= Ack n (2 * n + 2).
  Proof.
    specialize (Hn (n+2) n).
    replace (2* n + 2) with (n+2 + n) by lia;  auto.
  Qed.

  Remark R07 : Ack n (2 * n + 3) <= Ack n (2* n + 2).
  Proof.
    eapply Le.le_trans.
    - apply R05.
    - apply R06.
  Qed.


  Remark R08 :  Ack n (2* n + 2) < Ack n (2 * n + 3).
  Proof.
    destruct (Ack_properties n) as [H _]; apply H; lia.
  Qed.

  Lemma contrad : False.
  Proof.
    generalize R07, R08; intros; lia.
  Qed.

End Contrad.

Lemma Ack_not_PR : False.
  destruct L1 as [n Hn].
now apply contrad with n.
Qed.

End Impossibility_Proof.

Check Ack_not_PR.





