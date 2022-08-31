  (** Pierre Castéran, Univ. Bordeaux and LaBRI *)

From hydras Require Import Hydra_Lemmas  Epsilon0_Needed_Free
     Epsilon0_Needed_Std  Hydra_Termination L_alpha Battle_length Ack.
Import E0 Large_Sets Hprime Paths MoreLists  O2H Hydra_Definitions Iterates.
Export Hydra_Definitions.

(** ** Liveness 

  If the hydra is not reduced to one  head, then Hercules can chop off 
  some head
 *)

(* begin snippet AliveThms *)
Corollary Alive_free : Alive free. (* .no-out *)
(*| .. coq:: none |*)
Proof.
  red;intros.
  destruct (next_round i h).
  -  destruct s as [h' H'];  exists h'; now  exists i. 
  - tauto.
Qed.
(*||*)

Corollary Alive_standard : Alive standard. (* .no-out *)
(*|
.. coq:: none 
|*)
Proof.
  red;intros.
  destruct (next_round i h).
  -  destruct s as [h' H'];  exists h'.
     assumption.
  - now destruct H.
Qed.
(*||*)

(* end snippet AliveThms *)

(** ** Termination of free battles 
 *)

Theorem Variant_LT_free_0 :  @Hvariant  _ _ T1_wf free Hydra_Termination.m.
Proof. split; intros; now apply round_decr. Qed.

Theorem Variant_lt_free:  @Hvariant _ _ E0lt_wf free Hydra_Termination.var.
Proof. split; intros; now apply round_decr. Qed.


Theorem Variant_LT_standard : @Hvariant _ _ T1_wf standard Hydra_Termination.m.
Proof.
 split; intros i h h' H H0; apply round_decr; now exists i.
Qed.


Theorem Variant_lt_standard : @Hvariant _ _ E0lt_wf standard Hydra_Termination.var.
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

About  battle_length_std.

Open Scope nat_scope.

(* begin snippet battleLengthStdHardy *)

(*| .. coq:: no-out |*)
Theorem battle_length_std_Hardy (alpha : E0) :
  alpha <> E0zero ->
  forall k , 1 <= k ->
             exists l: nat,
               H'_ alpha k - k <= l /\
               battle_length standard k (iota (cnf alpha)) l. 
Proof. 
  intros H k  H0; exists (L_ alpha (S k) - k); split. 
  - generalize (H'_L_ alpha k); lia.
  - now apply battle_length_std.
Qed.
(*||*)
(* end snippet battleLengthStdHardy *)



(*
Print Assumptions battle_length_std.
 *)

(** ** Battle length is not PR *)

Require Import primRec F_alpha  AckNotPR PrimRecExamples.
Require Import F_omega.
Import E0.

(* begin snippet battleLengthNotPRa *)

Section battle_length_notPR.

  Hypothesis H: forall alpha, isPR 1 (l_std alpha).

  (* end snippet battleLengthNotPRa *)
  

  (** A counter example *)

  (* begin snippet battleLengthNotPRb *)

  Let alpha := E0phi0 E0omega.
  Let h := iota (cnf alpha).

   (* end snippet battleLengthNotPRb *)

  (** let us get rid of the substraction ... *)

  (* begin snippet battleLengthNotPRc *)
  
  Let m k := L_ alpha (S k).

  Remark m_eqn : forall k, m k = (l_std alpha k + k)%nat. (* .no-out *)
  (* end snippet battleLengthNotPRc *)
  
  Proof.
    intro k; assert (k <= L_ alpha (S k)).
    { assert (S k < L_ alpha (S k)).
      { apply L_ge_S; unfold alpha; intro H0; injection H0.
        intro; discriminate.
      }
      lia.
    }
    unfold m,l_std ; lia.   
  Qed.

  (* begin snippet battleLengthNotPRd *)
  
  Remark mIsPR : isPR 1 m. (* .no-out *)

   (* end snippet battleLengthNotPRd *)
  Proof.
    destruct (H alpha) as [x Hx].
    apply isPR_extEqual_trans with (fun k => (l_std alpha  k + k)%nat).
    - apply compose1_2IsPR; auto.
      + apply idIsPR.
      + apply plusIsPR.
    - intro k; unfold m, l_std; assert (k <=  L_ alpha (S k))%nat.
      transitivity (S k). 
      + auto with arith.
      + apply Nat.lt_le_incl.
        apply L_ge_S.
        unfold alpha; intro H0; injection H0; discriminate.
      + now replace (L_ alpha ( S k) -k + k)%nat with (L_ alpha (S k))
          by lia.
  Qed.

  (* begin snippet mGeFOmega *)
  
  Remark m_ge_F_omega k: F_ E0omega (S k) <= m (S k). (* .no-out *)
  (* end snippet mGeFOmega *)
  
  Proof.
    rewrite m_eqn; transitivity (H'_ alpha (S k)).
    - apply H'_F.
    - unfold l_std;  generalize (H'_L_ alpha (S k)); lia.
  Qed.

  (** We compare [m] with the Ackermann function *)
  
  Remark m_ge_Ack:  forall n, 2 <= n -> Ack (S n) (S n) <= m (S n).
  Proof.
    intros n H0; transitivity (F_ E0omega (S n)).
    - apply F_vs_Ack; auto.
    - apply m_ge_F_omega.
  Qed.


  Remark m_dominates_Ack_from_3 : forall n, 3 <= n -> Ack n n <= m n.
  Proof.  
    destruct n.
    - lia.
    - intro; apply m_ge_Ack; auto with arith.
  Qed.

  (* begin snippet mDominatesAck *)
  
  Remark m_dominates_Ack :
    dominates (fun n =>  S (m n)) (fun n => Ack.Ack n n). (* .no-out *)

    (* end snippet mDominatesAck *)

  Proof.     
    exists 3; red; intros.
    apply Nat.le_lt_trans with (m p).
    - apply m_dominates_Ack_from_3; auto.
    - auto with arith.
  Qed.

  (* begin snippet SmNotPR *)
  
  Remark SmNotPR : isPR 1 (fun n => S (m n)) -> False. (* .no-out *)
 (* end snippet SmNotPR *)

  Proof.
    intro; eapply dom_AckNotPR; eauto.
    apply m_dominates_Ack; auto.
  Qed.
 

  (* begin snippet LNotPR *)
  
  (*| 
.. coq:: no-out 
|*)
  
  Theorem LNotPR : False.
  Proof.
    apply SmNotPR, compose1_1IsPR.
    - apply mIsPR.
    - apply succIsPR.
  Qed.

End battle_length_notPR.

(*||*)
Check l_std_ok.

Check LNotPR.

Search L_ F_.
(* end snippet LNotPR *)



