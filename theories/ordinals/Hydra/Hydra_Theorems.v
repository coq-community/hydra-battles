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

