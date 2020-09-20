(** 
 First_toggle 

Computes the first  [l]  between [n] and [p] (excluded) such that 
       [P l = true] and  [P (S l) = false].
*)


From Coq Require Import Arith Lia.

Section Hypos.
  Variables (P : nat -> bool)
            (n p : nat).
 
  Hypotheses (Hnp : n < p)
             (Hn : P n = true) (Hp : P p = false).

(* begin hide *)
  
  Let  search_toggle  (delta : nat)(H : 0 < delta /\ delta <= p - n)
             (invar : forall i, n <= i -> i <= p - delta -> P i = true) :
    {l : nat | n <= l  /\ l < p /\
               (forall i: nat, n <= i -> i <= l -> P i = true ) /\ 
               (P (S l ) = false)}.
  
  Proof.
    generalize delta H invar.
    clear delta H invar.
    intro delta; pattern delta; apply well_founded_induction with lt.
    apply lt_wf.
    
    intros d Hd.
    case_eq d.
    intro;subst.
    intros.
    destruct H.
    elimtype False. inversion H. intros; subst.
    
    case_eq (P (p - n0)). 
    intro.
    destruct (Hd n0).
    auto with arith.
    destruct n0.
    replace (p - 0) with p in H. rewrite Hp in H; discriminate.
    auto with arith.
    split; auto with arith.
    destruct H0; auto with arith.

    intros.
    assert (i <= p - S n0 \/ i = p - n0) by lia.
    destruct H3.
    apply invar; auto.
    subst i; auto.
    exists x; split; auto.
    tauto.
    tauto.
    intros.
    exists (p - S n0).
    repeat split.
    lia.
    lia.
    auto.
    replace (S (p - S n0)) with (p - n0);auto.
    lia.
  Defined.

  Let delta := p - n.

  Remark R1 : 0 < delta /\ delta <= p - n.
  Proof.   unfold delta.  clear search_toggle; lia.  Qed.

  Remark R2 :  forall i, n <= i -> i <= p - delta -> P i = true.
  Proof.
    clear search_toggle; unfold delta; intros; replace i with n; [trivial | lia].
  Qed.

(* end hide *)
  
  Definition first_toggle :
  {l : nat |  n <= l /\ l < p /\
              (forall i : nat, n <= i -> i <= l -> P i = true) /\
              P (S l) = false}.
  (* begin hide *)
  Proof.
    exact    (search_toggle  (p-n) R1 R2).
  Defined.
  (* end hide *)
 
End Hypos.


Arguments first_toggle : clear implicits.
