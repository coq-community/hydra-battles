(** Pierre Castéran, Univ. Bordeaux and LaBRI *)

From hydras Require Import Hydra_Lemmas  Epsilon0_Needed_Free
     Epsilon0_Needed_Std  Hydra_Termination L_alpha Battle_length.
Import E0 Large_Sets H_alpha Paths MoreLists  O2H Hydra_Definitions.

(** ** Liveness 

  If the hydra is not reduced to one  head, then Hercules can chop off 
  some head
 *)

Theorem Alive_free :   Alive free.
Proof.
  red;intros.
  destruct (next_round i h).
  -  destruct s as [h' H'];  exists h'; now  exists i. 
  - tauto.
Qed.


Theorem Alive_standard :   Alive standard.
Proof.
  red;intros.
  destruct (next_round i h).
  -  destruct s as [h' H'];  exists h'.
     assumption.
  - now destruct H.
Qed.

(** ** Termination of free battles 
 *)

Theorem Variant_LT_free_0 :  @Hvariant  _ _ T1_wf free Hydra_Termination.m.
Proof. split; intros; now apply round_decr. Qed.

Theorem Variant_lt_free:  @Hvariant _ _ E0.Lt_wf free Hydra_Termination.var.
Proof. split; intros; now apply round_decr. Qed.


Theorem Variant_LT_standard : @Hvariant _ _ T1_wf standard Hydra_Termination.m.
Proof.
 split; intros i h h' H H0; apply round_decr; now exists i.
Qed.


Theorem Variant_lt_standard : @Hvariant _ _ E0.Lt_wf standard Hydra_Termination.var.
Proof.
  split; intros i h h' H H0;  apply round_decr; now exists i.
Qed.

(*

Print Assumptions Variant_lt_standard.
 *)

(** ** Impossibility theorems 

  Termination of free battles cannot be proven with a variant from hydras into a segment $[0, alpha]$ with $alpha < \_epsilon0$ 

*)


(**  Impossiblity to define a variant bounded by some ordinal less than 
     [epsilon0] *)

Check Impossibility_free.
(*
Impossibility_free
     : BoundedVariant free -> False
 *)

Check Impossibility_std.




Theorem battle_length_std (alpha : E0)  :
  alpha <> Zero ->
  forall k, (1 <= k)%nat ->
            battle_length standard k (iota (cnf alpha))
                         (L_ alpha (S k) - k).

Proof.  apply battle_length_std.  Qed.

Open Scope nat_scope.

Theorem battle_length_std_Hardy (alpha : E0) :
  alpha <> Zero ->
  forall k , 1 <= k ->
             exists l: nat,  H_ alpha k - k <= l /\
                             battle_length standard k (iota (cnf alpha)) l.    
Proof.
  intros H k  H0; exists (L_ alpha (S k) - k).
  split.
  - generalize (H_L_ alpha k); lia.
  - now apply battle_length_std.
Qed.



(*
Print Assumptions battle_length_std.
 *)

(** ** Battle length is not PR *)

Require Import primRec F_alpha H_alpha AckNotPR PrimRecExamples.
  Require Import F_omega.

Section battle_lenght_notPR.

  About L_.
  Locate "omega".

  Let alpha := Phi0 omega%e0.

  Let h := iota (cnf alpha).

  Let l k := (L_ alpha (S k) - k)%nat.
  Let m k := L_ alpha (S k).

  Hypothesis H: isPR 1 l.

  Remark R : forall k, m k = (l k + k)%nat.
  Proof.
    intro k.
    assert (k <= L_ alpha (S k)).
    Search L_.
    assert (S k < L_ alpha (S k)).
    apply L_ge_S.
    unfold alpha.
   intro H0.
   compute in H0.
    injection H0.
    intro; discriminate.
    lia.

   unfold m.
   unfold l.
   lia.
Qed.



  Remark R1 : forall k,  F_ omega (S k) <= m (S k).
    intro.

    rewrite R.
    Search L_ H_.
    transitivity (H_ alpha (S k)).
    apply H_F.
    unfold l.
    Search H_ L_.
    generalize (H_L_ alpha (S k)); intro.
    lia.
  Qed.


  Search F_ omega.

  Remark R2: forall n, 2 <= n -> Ack.Ack (S n) (S n) <= m (S n).
  Proof.
    intros n H0. transitivity (F_ omega (S n)).
    apply F_vs_Ack.
    auto.
    apply R1.
  Qed.


  Remark R3 : forall n, 3 <= n -> Ack.Ack n n <= m n.
  Proof.  
    destruct n.
    lia.
    intro;apply R2.
    auto with arith.
  Qed.

  Search (isPR _ _ -> False).

  Remark R4 : Iterates.dominates (fun n =>  S (m n)) (fun n => Ack.Ack n n).
    red.
    exists 3.
    red.
    intros.
    apply Lt.le_lt_trans with (m p).
    apply R3.
    auto.
    auto with arith.
  Qed.

  Search Iterates.dominates Ack.Ack.

  Remark R5 : isPR 1 (fun n => S (m n)) -> False.
    intro; eapply dom_AckNotPR.
    apply R4; auto.
 auto.
  Qed.

  
  Remark R6: isPR 1 m.
    destruct H as [x Hx].

    About isPR_extEqual_trans.
    apply isPR_extEqual_trans with (fun k => (l k + k)%nat).
   apply compose1_2IsPR.
 auto.
 apply idIsPR.
 apply plusIsPR.
 intro k. unfold m, l.
assert (k <=  L_ alpha (S k))%nat.
 Search L_.
 transitivity (S k). 
auto with arith.
apply Lt.lt_le_weak.
 Search L_.
apply L_ge_S.
unfold alpha.
intro H0.
injection H0.
discriminate.

replace (L_ alpha ( S k) -k + k)%nat with (L_ alpha (S k)) by lia.
red.
auto.
  Qed.


  Theorem L_notPR : False.
    apply R5.
    apply compose1_1IsPR.
    apply R6.
    apply succIsPR.
  Qed.

End battle_lenght_notPR.

About L_notPR.

