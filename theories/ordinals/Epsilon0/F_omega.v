(**  About [F_ omega] *)


From hydras Require Import Iterates F_alpha E0 Ack AckNotPR.
From Coq Require Import ArithRing Lia   Arith.
Import Exp2.
Open Scope nat_scope.

(** ** Rewriting lemmas *)

Lemma Ack_iterate_rw n p : Ack (S n) (S p) = iterate (Ack n) (S (S p)) 1.
Proof.  reflexivity. Qed.

Lemma F_iterate_rw n p : F_ (S n) (S p) = iterate (F_ n) (S (S p)) (S p).
Proof.
  rewrite <- FinS_eq, FinS_Succ_eq;
    now rewrite F_succ_eqn.
Qed.

(** ** Comparison between [Ack n] and [F_ n]  *)


Lemma L02 p: 2 <= p -> 2 * p + 3 <= exp2 p * p.
Proof.
  induction 1.
  - compute; auto with arith. 
  - cbn; rewrite PeanoNat.Nat.mul_succ_r; ring_simplify.
    remember (exp2 m) as X.
    rewrite (Nat.mul_comm X m)in IHle.
    rewrite <-  (Nat.mul_assoc); lia.
Qed.

Section inductive_step.
  Variable n: nat.
  Hypothesis Hn : forall p, 2 <= p -> Ack n p <= F_ n p.

  Lemma L: forall p, 2 <= p -> Ack (S n) p <= F_ (S n) p.
  Proof.
    intros p Hp; destruct p.
    - lia.
    - rewrite Ack_iterate_rw; rewrite F_iterate_rw.
      transitivity (iterate (Ack  n) (S (S p)) (S p)).
      + apply iterate_mono2.
        * apply Ack_mono_r.
        * lia.
      +  eapply iterate_mono_1; auto.
         * apply Ack_strict_mono.
         * apply le_S_Ack.
         * intros; apply Hn; eauto with arith.
  Qed.

End inductive_step.

Lemma L2 : forall n, 2 <= n -> forall p, 2 <= p ->
                                         Ack n p <= F_ n p.
Proof.
  induction 1.
  - intros;  rewrite Ack_2_n;  transitivity (exp2 p * p).
   + apply L02; auto.
   + apply PeanoNat.Nat.lt_le_incl; apply LF2.
  - intros; apply L; auto.
Qed.

(* begin snippet FVsAck *)
Lemma F_vs_Ack n : 2 <= n -> Ack n n <= F_ E0_omega n. (* .no-out *)
(* end snippet FVsAck *)

Proof.
  intros; rewrite F_lim_eqn.
  - rewrite Canon.Canon_Omega; apply L2; auto.
  - reflexivity.
Qed.

(** ** [F_ omega] is not primitive recursive *)

Import primRec extEqualNat.

Section F_omega_notPR.

  Context (F_omega_PR : isPR 1 (F_ E0_omega)).

  Lemma F_omega_not_PR : False.
  Proof.
    destruct (majorPR1 _ F_omega_PR) as [n Hn];
      specialize (Hn (S n)).
    assert (n <> 0).
    { intro; subst; cbn in Hn;
        rewrite F_lim_eqn in Hn.
      - rewrite Canon.Canon_Omega in Hn.
        rewrite LF1 in Hn; lia.
      - reflexivity.
    }
    specialize (F_vs_Ack (S n)).
    intros H0;  assert (H1: 2 <= S n) by lia.
    apply H0 in H1;  clear H0.
    assert(Ack n (S n) < Ack (S n) (S n)) by
        (apply Ack_strict_mono_l; auto).
    lia.
  Qed.

End F_omega_notPR.

(** ** [F_ alpha] is not primitive recursive, for [omega <= alpha] *)

Section F_alpha_notPR.

  Variable alpha: E0.
  Section case_lt.
    
    Hypothesis Halpha : E0_omega o< alpha.

    Remark R5: exists N, forall k, N <= k -> F_ E0_omega k < F_ alpha k.
    Proof.
      destruct (F_mono_l _ _ Halpha) as [x Hx]; exists x; auto.
    Qed.

    Context (H: isPR 1 (F_ alpha)).

    Remark R00 : F_ alpha >> fun n => Ack n n.
    Proof.
      destruct (F_mono_l alpha E0_omega Halpha) as [N HN];
        exists (Nat.max N 2);  intros p Hp.
      apply Nat.le_lt_trans with (F_ E0_omega p).    
      - apply F_vs_Ack; auto; lia.
      - apply HN; lia.
    Qed.

    Lemma FF : False.
    Proof.
      eapply dom_AckNotPR; eauto.
      apply R00.
    Qed.

  End case_lt.

  
  Hypothesis H : E0_omega o<= alpha.
  Context (H0: isPR 1 (F_ alpha)).

  Lemma F_alpha_not_PR: False.
  Proof.
    destruct (E0.le_lt_eq_dec H).
    - apply FF; auto.
    - subst; now apply F_omega_not_PR.
  Qed.

End F_alpha_notPR.

(**  ** On the other hand, [F_ n] is PR for any [n:nat]
 *)


#[export] Instance F_0_isPR : isPR 1 (F_ 0).
Proof.
  apply isPRTrans with S.
   - intro n; now rewrite F_zero_eqn.
  - apply succIsPR.
Qed.

Section step.
  Variable n: nat.
  Hypothesis Hn : isPR 1 (F_ n).

  (*  in order to use primRec's lemmas *)
  Let F := fun a b =>  nat_rec (fun _ => nat) a (fun x y  => F_ n y) b.
  
  Remark L00: forall i,  F_ (E0_succ n) i = F i (S i) .
  Proof.
    unfold F; intro i; rewrite F_succ_eqn.  
    now  rewrite iterate_compat3.
  Qed. 

  #[local] Instance R01 : isPR 2 F.
  Proof.
    assert (H: isPR 3 (fun x y _ => F_ n y)) by (apply filter010IsPR; auto).
    apply isPRTrans with (fun x y =>  F x y).
    - intros x y; reflexivity.
    - apply swapIsPR; unfold F; apply ind1ParamIsPR; auto.
       apply idIsPR.
  Qed.

  #[local] Instance R02 : isPR 1 (fun i  =>  F i (S i)).
  Proof.
    apply compose1_2IsPR. 
    - apply idIsPR.
    - apply succIsPR.
    - apply R01.
  Qed.

  #[local] Instance R03 : isPR 1 (F_ (S n)). 
  Proof.
    apply isPRTrans with (F_ (E0_succ n)).
 -  rewrite <- FinS_Succ_eq; rewrite FinS_eq.
       intro; reflexivity.
    -  eapply isPRextEqual.
       +  apply R02.
       +  intro i; red; now rewrite L00.
  Qed.

End step.


#[export] Instance F_n_PR (n:nat)  : isPR 1 (F_  n).
Proof.
  induction n.
  - apply F_0_isPR.
  - now apply R03.
Qed.

(**  Keep in mind that [isPR] is of sort [Set], so [not] and [iff]
     cannot be used *)

Lemma F_alpha_PR_inv: forall alpha,  isPR 1 (F_ alpha) -> alpha o< E0_omega.
Proof.
  intro alpha.
  destruct (E0_lt_ge alpha E0_omega); auto.
  intro H0;  destruct  ( F_alpha_not_PR _ H H0).
Qed.


Lemma F_alpha_notPR_inv: forall alpha,
    (isPR 1 (F_ alpha) -> False)  -> E0_omega o<= alpha.
Proof.
  intros alpha H; destruct (E0_lt_ge alpha E0_omega); auto.
  destruct (lt_omega_inv  H0) as [i Hi]; subst alpha.
  destruct H; apply F_n_PR.
Qed.


(* begin snippet lemmas *)
Check F_alpha_not_PR.
(* end snippet lemmas *)
Check F_alpha_PR_inv.
