(** 
 First_toggle 

Computes the first  [l]  between [n] and [p] (excluded) such that 
       [P l = true] and  [P (S l) = false].
 *)

(** Pierre Castéran, Univ. Bordeaux and LaBRI *)

From Coq Require Import Arith Lia Inclusion Inverse_Image.
From hydras Require Import DecPreOrder.
Require Export STDPP_compat. 

Section Hypos.
  Context (P : nat -> Prop) `{Pdec: forall n, Decision (P n)} (n p : nat).
 
  Hypotheses (Hnp : n < p) (Hn : P n) (Hp : ~ P p).

  Let spec  := {l : nat | n <= l  /\ l < p /\
                          (forall i: nat, n <= i -> i <= l -> P i) /\ 
               (~ P (S l ))}.
(* begin hide *)

  Let R q' q :=  q < q' <= p.

  Lemma Rwf : well_founded R.
  Proof.
    eapply wf_incl.
    2: eapply wf_inverse_image with (f:= fun q =>  p - q).
    2: apply lt_wf.
    intros q q'; unfold R; lia. 
  Defined. 

  Let  search_toggle  (q:nat)(H : n <= q < p)
       (invar : forall i, n <= i -> i <= q -> P i) : spec. 
   
  Proof.
    revert q H invar; 
    intro q; pattern q; apply well_founded_induction with R.
    - apply Rwf.
    - intros x Hx H H0; destruct (decide (P (S x))) as [H1|H1].
     +  assert (S x < p).
        { assert (S x <= p) by (destruct H; auto). 
          destruct (le_lt_or_eq _ _ H2); auto.
          subst p; contradiction. 
        }
        destruct (Hx (S x)).
        * unfold R; lia.
        * lia.
        * intros i H3 H4; destruct (le_lt_or_eq _ _ H4); auto.
          apply H0; auto with arith. 
          now subst. 
        * exists x0; auto.
    + exists x; repeat split; trivial;  try lia. 
  Defined.


  
(* end hide *)
  
  Definition first_toggle : spec. 
  (* begin hide *)
  Proof.
    apply (search_toggle n).
    - lia. 
    - clear search_toggle;
        intros; now replace n with i in *  by lia. 
  Defined.
  (* end hide *)
 
End Hypos.


Arguments first_toggle : clear implicits.
