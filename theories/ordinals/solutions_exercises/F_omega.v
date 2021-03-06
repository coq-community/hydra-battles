Require Import Iterates F_alpha E0.
Require Import ArithRing Lia   Max Ack AckNotPR.
Import Exp2.
Require Import Mult.
Open Scope nat_scope.


Lemma Ack_iterate_rw n p : Ack (S n) (S p) = iterate (Ack n) (S (S p)) 1.
  reflexivity.
Qed.

Lemma F_iterate_rw n p : F_ (S n) (S p) = iterate (F_ n) (S (S p)) (S p).
  ochange (Fin (S n)) (Succ n).
  now rewrite F_succ_eqn.
  cbn. 
  destruct n; reflexivity.
Qed.


Lemma L02 p: 2 <= p -> 2 * p + 3 <= exp2 p * p.
Proof.
  induction 1.
  compute.
  auto with arith. 
  cbn.
  rewrite     PeanoNat.Nat.mul_succ_r.
  ring_simplify.
  remember (exp2 m) as X.
  rewrite (Mult.mult_comm X m)in IHle.
  rewrite <-  (Mult.mult_assoc).
  lia.
Qed.

Section induc.
  Variable n: nat.
  Hypothesis Hn : forall p, 2 <= p -> Ack n p <= F_ n p.


  Lemma L: forall p, 2 <= p -> Ack (S n) p <= F_ (S n) p.
    intros p Hp; destruct p.
    - lia.
    - rewrite Ack_iterate_rw; rewrite F_iterate_rw.
      transitivity (iterate (Ack  n) (S (S p)) (S p)).
      + apply iterate_mono2.
        apply Ack_mono_r.
        lia.
      +  eapply iterate_mono_1.
         apply Ack_strict_mono.
         apply le_S_Ack.
         apply Hn.
         auto.
  Qed.


End induc.


Lemma L2 : forall n, 2 <= n -> forall p, 2 <= p ->
                                         Ack n p <= F_ n p.
  induction 1.
  intros.
  rewrite Ack_2_n.
  transitivity (exp2 p * p).
  apply L02.
  auto.
  apply PeanoNat.Nat.lt_le_incl.
  apply LF2.
  intros.
  apply L.
  auto.
  auto.
Qed.

Lemma F_vs_Ack n : 2 <= n -> Ack n n <= F_ omega n.
Proof.
  intros.
  rewrite F_lim_eqn.
  rewrite Canon.Canon_Omega.
  apply L2.
  auto.
  auto.
  reflexivity.
Qed.


Import primRec extEqualNat.



Section F_omega_notPR.

  Hypothesis F_omega_PR : isPR 1 (F_ omega).


  Lemma F_omega_not_PR : False.
    destruct (majorPR1 _ F_omega_PR) as [n Hn].
    specialize (Hn (S n)).
    assert (n <> 0).
    { intro; subst.
      cbn in Hn.
      rewrite F_lim_eqn in Hn.
      rewrite Canon.Canon_Omega in Hn.
      rewrite LF1 in Hn.
      lia.
      reflexivity.
    }
    specialize (F_vs_Ack (S n)).
    intros.
    assert (2 <= S n) by lia.
    apply H0 in H1.
    clear H0.
    assert(Ack n (S n) < Ack (S n) (S n)).
    apply Ack_strict_mono_l.
    auto.
    lia.
  Qed.

End F_omega_notPR.

Section F_alpha_notPR.

  Variable alpha: E0.
  Section case_lt.
    
    Hypothesis Halpha : omega o< alpha.

    Remark R5: exists N, forall k, N <= k -> F_ omega k < F_ alpha k.
      destruct (Propp284 _ _ Halpha).
      exists x; auto.
    Qed.

    Hypothesis H: isPR 1 (F_ alpha).

    Remark R00 : F_ alpha >> fun n => Ack n n.
    Proof.
      destruct ( Propp284 alpha omega Halpha) as [N HN];
        exists (Nat.max N 2);  intros p Hp.
      apply Lt.le_lt_trans with (F_ omega p).    
      - apply F_vs_Ack; auto; lia.
      - apply HN; lia.
    Qed.

    Lemma FF : False.
    Proof.
      eapply dom_AckNotPR; eauto.
      apply R00.
    Qed.

  End case_lt.

  Hypothesis H : omega o<= alpha.
  Hypothesis H0: isPR 1 (F_ alpha).

  Lemma F_alpha_not_PR: False.
  Proof.
    destruct (E0.le_lt_eq_dec H).
    - apply FF; auto.
    - subst; now apply F_omega_not_PR.
  Qed.

End F_alpha_notPR.


(** TODO : move to more generic libraries *)

Lemma isPR_trans n (f g : naryFunc n) : isPR n f ->
                                        extEqual _ f g ->
                                        isPR n g.
Proof.
  destruct 1 as [x Hx]; intros.
  exists x;eapply extEqualTrans; eauto.
Qed.




(**  ** On the other hand, [F_ n] is PR for any [n:nat]
 *)


Lemma F_0_isPR : isPR 1 (F_ 0).
Proof.
  apply isPR_trans with S.
  - apply succIsPR.
  - intro n; now rewrite F_zero_eqn.
Qed.

Section step.
  Variable n: nat.
  Hypothesis Hn : isPR 1 (F_ n).

  (*  in order to use primRec's lemmas *)
  Let F := fun a b =>  nat_rec (fun _ => nat) a (fun x y  => F_ n y) b.
  
  Remark L00: forall i,  F_ (Succ n) i = F i (S i) .
  Proof.
    unfold F; intro i; rewrite F_succ_eqn.  
    now  rewrite iterate_compat3.
  Qed. 

  Remark R01 : isPR 2 F.
  Proof.
    assert (H: isPR 3 (fun x y _ => F_ n y)) by (apply filter010IsPR; auto).
    apply isPR_trans with (fun x y =>  F x y).
    apply swapIsPR; unfold F; apply ind1ParamIsPR; auto.
    - apply idIsPR.
    - intros x y; reflexivity.
  Qed.

  Remark  R02 : isPR 1 (fun i  =>  F i (S i)).
  Proof.
    apply compose1_2IsPR. 
    - apply idIsPR.
    - apply succIsPR.
    - apply R01.
  Qed.

  Remark R03 : isPR 1 (F_ (S n)). 
  Proof.
    apply isPR_trans with (F_ (Succ n)).
    -  eapply isPR_trans.
       +  apply R02.
       +  intro i; red; now rewrite L00.
    -  rewrite <- FinS_Succ_eq; rewrite FinS_eq.
       intro; reflexivity.
  Qed.

End step.


Theorem F_n_PR (n:nat)  : isPR 1 (F_  n).
Proof.
  induction n.
  - apply F_0_isPR.
  - now apply R03.
Qed.




