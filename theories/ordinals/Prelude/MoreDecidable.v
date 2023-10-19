(* orginal development by Russel O'Connor *)


From Coq Require Export Decidable Arith Lia.

Remark boundedCheck :
 forall P : nat -> Prop,
 (forall x : nat, decidable (P x)) ->
 forall c : nat,
 (forall d : nat, d < c -> ~ P d) \/ (exists d : nat, d < c /\ P d).
Proof.
  intros P H c. induction c as [| c Hrecc].
  - left; intros d H0. lia.
  - destruct (H c) as [e | e].
    + right. exists c. split; auto.
    + destruct Hrecc as [H0 | H0].
      * left. intros d H1. assert (d < c \/ d = c) as H2 by lia. destruct H2.
        -- eauto.
        -- congruence.
      * destruct H0 as (x, H0). right. exists x. split; try lia. tauto.
Qed.

(* move to Coq.Logic.Decidable ? *)
Remark smallestExists :
 forall P : nat -> Prop,
 (forall x : nat, decidable (P x)) ->
 forall c : nat,
 P c -> exists a : nat, P a /\ (forall b : nat, b < a -> ~ P b).
Proof.
  assert
   (H: forall P : nat -> Prop,
   (forall x : nat, decidable (P x)) ->
    forall d c : nat,
    c < d -> P c -> exists a : nat, P a /\ (forall b : nat, b < a -> ~ P b)).
  { intros P H d. induction d as [| d Hrecd].
    - intros c H0 H1. lia.
    - intros c H0 H1. assert (H2: c < d \/ c = d)  by lia. 
      destruct H2.
      + eauto.
      + destruct (boundedCheck P H c).
        * exists c. tauto.
        * destruct H3 as (x, H3). apply (Hrecd x).
          -- lia.
          -- tauto. }
  intros P H0 c H1. eapply H.
  - exact H0.
  - exact (Nat.lt_succ_diag_r c).
  - exact H1.
Qed.

