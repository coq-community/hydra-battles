(**

   "Computing" standard battle length

Pierre Castéran, LaBRI, University of Bordeaux



 *)

From hydras Require Import L_alpha.
From hydras  Require Import Hydra_Lemmas  Epsilon0_Needed_Free
     Epsilon0_Needed_Std Hydra_Termination O2H.
Import E0 Large_Sets Hprime Paths MoreLists.



Section Battle_length.

  Variable alpha : E0.
  Hypothesis Halpha : alpha <> Zero.
  Variable k : nat.
  Hypothesis Hk : (1 <= k)%nat.
  Let l := L_ alpha (S k).

  Remark R0 : (S k < l)%nat.
  Proof.
    unfold l. apply L_pos_inv with (cnf alpha).
    - intro; apply Halpha; orefl; now rewrite H.
    - apply L_correct.
  Qed.

  
  Remark R2 : mlarge (cnf alpha)  (interval (S k) (Nat.pred l)).
  Proof.
    unfold l; generalize (L_correct alpha).
    inversion 1; auto.
    destruct alpha; auto.
    - rewrite E0_eq_iff in Halpha; simpl in  Halpha, H0;
        subst cnf; now destruct Halpha.
  Qed.
  
  
  Remark R3 : path_toS zero
                       (unshift (interval (S k) (Nat.pred l)))
                       (cnf alpha).
  Proof.  apply path_to_path_toS, R2.  Qed.  

  Remark R4 :
    trace_to (O2H.iota zero)
             (unshift (interval (S k) (Nat.pred l)))
             (O2H.iota (cnf alpha)).
  Proof. 
    apply O2H.path_toS_trace; [apply R3 | auto with E0].
  Qed.

  Lemma R5 : trace_to (O2H.iota zero)
                      (interval  k (Nat.pred  (Nat.pred l)))
                      (O2H.iota (cnf alpha)).
  Proof.
    rewrite <- unshift_interval_pred.
    - apply R4.
    - unfold l; apply Nat.lt_le_trans with (S k).
      + lia. 
      + specialize (L_ge_S alpha Halpha (S k)); lia.
  Qed.

  Remark R6 : S (Nat.pred (Nat.pred l)) = (l-1)%nat.
  Proof.  generalize R0; abstract lia. Qed.

  Lemma L06:  battle standard k (iota (cnf alpha)) (l-1)%nat
                     (iota zero).
  Proof.
    rewrite <- R6; apply trace_to_std.
    generalize R0; abstract lia.
    apply R5.    
  Qed.

  (* begin snippet battleLengthStd *)
  
  Lemma battle_length_std:
    battle_length  standard k (iota (cnf alpha)) (l-k)%nat. (* .no-out *)
  (*| .. coq:: none |*)
  Proof.
    red; generalize L06.
    replace (l-1)%nat with (Init.Nat.pred (k + (l - k )))%nat; auto.
    generalize R0; abstract lia.
  Qed.
  (*||*)
  (* end snippet battleLengthStd *)
  
End Battle_length.

(* begin snippet BattleLength  *)

Definition l_std alpha k := (L_ alpha (S k) - k)%nat.

Lemma l_std_ok : forall alpha : E0,
    alpha <> Zero ->
    forall k : nat,
      1 <= k -> battle_length standard k (iota (cnf alpha))
                              (l_std alpha k). (* .no-out *)
(* end snippet BattleLength  *)

Proof. apply battle_length_std. Qed.







