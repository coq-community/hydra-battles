(** 
 First_toggle 

Computes the first  [l]  between [n] and [p] (excluded) such that 
       [P l = true] and  [P (S l) = false].
 *)

(** Pierre Castéran, Univ. Bordeaux and LaBRI *)

From Coq Require Import Arith Lia.
From hydras Require Import DecPreOrder.

Section Hypos.
  Context (P : nat -> Prop) `{Pdec: forall n, Decision (P n)} (n p : nat).
 
  Hypotheses (Hnp : n < p) (Hn : P n) (Hp : ~ P p).

(* begin hide *)
  
  Let  search_toggle  (delta : nat)(H : 0 < delta /\ delta <= p - n)
             (invar : forall i, n <= i -> i <= p - delta -> P i) :
    {l : nat | n <= l  /\ l < p /\
               (forall i: nat, n <= i -> i <= l -> P i) /\ 
               (~ P (S l ))}.
  
  Proof.
    generalize delta H invar.
    clear delta H invar.
    intro delta; pattern delta; apply well_founded_induction with Nat.lt.
    - apply lt_wf.
    - intros d Hd; case_eq d.
      + intro;subst.
        intros H invar; destruct H.
        exfalso; inversion H.
      + intros; subst.
        destruct (decide (P (p - n0))) as [H|H].
        * destruct (Hd n0).
          -- auto with arith.
          -- destruct n0.
             ++ replace (p - 0) with p in H.
                ** now apply Hp in H. 
                ** auto with arith.
             ++ split; auto with arith.
                destruct H0; auto with arith.
          -- intros i H1 H2; assert (H3: i <= p - S n0 \/ i = p - n0) by lia.
             destruct H3.
          ++ apply invar; auto.
          ++ subst i; auto.
          -- exists x; split; auto; tauto.
        *  exists (p - S n0); repeat split.
           1, 2: abstract lia. 
           assumption.
           replace (S (p - S n0)) with (p - n0); [assumption | abstract lia].
  Defined.

  Let delta := p - n.

  Remark R1 : 0 < delta /\ delta <= p - n.
  Proof.   unfold delta.  clear search_toggle; abstract lia.  Qed.

  Remark R2 :  forall i, n <= i -> i <= p - delta -> P i.
  Proof.
    clear search_toggle; unfold delta; intros; replace i with n; [trivial | lia].
  Qed.

(* end hide *)
  
  Definition first_toggle :
  {l : nat |  n <= l /\ l < p /\
              (forall i : nat, n <= i -> i <= l -> P i) /\
              ~ P (S l)}.
  (* begin hide *)
  Proof.
    exact (search_toggle  (p-n) R1 R2).
  Defined.
  (* end hide *)
 
End Hypos.


Arguments first_toggle : clear implicits.
