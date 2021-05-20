(** Pierre Castéran, Univ. Bordeaux and LaBRI *)

From hydras Require Import Hydra_Lemmas  Epsilon0_Needed_Free
     Epsilon0_Needed_Std  Hydra_Termination L_alpha Battle_length Ack.
Import E0 Large_Sets Hprime Paths MoreLists  O2H Hydra_Definitions Iterates.


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


About battle_length_std.

(* Theorem battle_length_std (alpha : E0)  :
  alpha <> Zero ->
  forall k, (1 <= k)%nat ->
            battle_length standard k (iota (cnf alpha))
                         (L_ alpha (S k) - k).

Proof.  apply battle_length_std.  Qed.

Locate battle_length_std.
 *)

Open Scope nat_scope.

Theorem battle_length_std_Hardy (alpha : E0) :
  alpha <> Zero ->
  forall k , 1 <= k ->
             exists l: nat,  H'_ alpha k - k <= l /\
                             battle_length standard k (iota (cnf alpha)) l.    
Proof.
  intros H k  H0; exists (L_ alpha (S k) - k).
  split.
  - generalize (H'_L_ alpha k); lia.
  - now apply battle_length_std.
Qed.



(*
Print Assumptions battle_length_std.
 *)

(** ** Battle length is not PR *)

Require Import primRec F_alpha  AckNotPR PrimRecExamples.
Require Import F_omega.
Import E0.

Section battle_length_notPR.

  (** We assume that the function with computes the length 
      of standard battles is primitive recursive *)
  
  Hypothesis H: forall alpha, isPR 1 (l_std alpha).

  (** A counter example *)

  Let delta := Phi0 omega%e0.
  Let h := iota (cnf delta).

  (** let us get rid of the substraction ... *)
  
  Let m k := L_ delta (S k).

  Remark m_eqn : forall k, m k = (l_std delta k + k)%nat.
  Proof.
    intro k; assert (k <= L_ delta (S k)).
    { assert (S k < L_ delta (S k)).
      { apply L_ge_S; unfold delta; intro H0; injection H0.
        intro; discriminate.
      }
      lia.
    }
    unfold m,l_std ; lia.   
  Qed.

   Remark mIsPR : isPR 1 m.
  Proof.
    destruct (H delta) as [x Hx].
    apply isPR_extEqual_trans with (fun k => (l_std delta  k + k)%nat).
    - apply compose1_2IsPR; auto.
      + apply idIsPR.
      + apply plusIsPR.
    - intro k; unfold m, l_std; assert (k <=  L_ delta (S k))%nat.
      transitivity (S k). 
      + auto with arith.
      + apply Lt.lt_le_weak.
        apply L_ge_S.
        unfold delta; intro H0; injection H0; discriminate.
      + replace (L_ delta ( S k) -k + k)%nat with (L_ delta (S k)) by lia.
        now red.
  Qed.

  Remark m_ge_F_omega : forall k,  F_ omega (S k) <= m (S k).
  Proof.
    intro k; rewrite m_eqn.
    transitivity (H'_ delta (S k)).
    - apply H'_F.
    - unfold l_std;  generalize (H'_L_ delta (S k)); lia.
  Qed.

  (** We compare [m] with the Ackermann function *)
  
  Remark m_ge_Ack:  forall n, 2 <= n -> Ack (S n) (S n) <= m (S n).
  Proof.
    intros n H0; transitivity (F_ omega (S n)).
    - apply F_vs_Ack; auto.
    - apply m_ge_F_omega.
  Qed.


  Remark m_dominates_Ack_from_3 : forall n, 3 <= n -> Ack n n <= m n.
  Proof.  
    destruct n.
    - lia.
    - intro; apply m_ge_Ack; auto with arith.
  Qed.


  Remark m_dominates_Ack : dominates (fun n =>  S (m n)) (fun n => Ack.Ack n n).
  Proof.     
    exists 3; red; intros.
    apply Lt.le_lt_trans with (m p).
    - apply m_dominates_Ack_from_3; auto.
    - auto with arith.
  Qed.

  Remark SmNotPR : isPR 1 (fun n => S (m n)) -> False.
  Proof.
    intro; eapply dom_AckNotPR; eauto.
    apply m_dominates_Ack; auto.
  Qed.
 

  Theorem LNotPR : False.
  Proof.
    apply SmNotPR,  compose1_1IsPR.
    - apply mIsPR.
    - apply succIsPR.
  Qed.

End battle_length_notPR.

About LNotPR.




