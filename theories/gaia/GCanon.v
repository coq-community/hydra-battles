From hydras Require Import T1.
From mathcomp Require Import all_ssreflect zify.
Require Import T1Bridge.
Import ssete9.CantorOrdinal. 

From gaia Require Import ssete9.
From hydras Require Import Canon.
Import ssete9.CantorOrdinal. 
Set Bullet Behavior "Strict Subproofs".



#[global] Notation hcanon := canon. 

Definition gcanon (a: gT1) (i:nat) : gT1 :=
  h2g (hcanon (g2h a) i).

Compute gcanon (phi0 T1omega) 6 == (phi0 (\F 6))%brg.

Lemma gcanon_zero i:  gcanon zero i = zero. 
Proof.  unfold gcanon => //. Qed. 

Lemma nf_gcanon alpha i : T1nf alpha -> T1nf (gcanon alpha i).
Proof.  
 unfold gcanon; rewrite -nf_ref => Halpha; rewrite -(h2g2h alpha)in Halpha.
 rewrite -nf_ref in Halpha; by  apply nf_canon. 
Qed.


Lemma gcanon_succ i alpha: T1nf alpha -> gcanon (T1succ alpha) i = alpha.
Proof.
  rewrite -(h2g2h alpha). rewrite succ_ref. rewrite -nf_ref.
  unfold gcanon. rewrite g2h2g.
  move => Halpha; rewrite canon_succ => //.
Qed.

Lemma gcanonS_LE alpha n:
    T1nf alpha -> gcanon alpha n.+1 <= gcanon alpha n.+2.
Proof.
  rewrite -(h2g2h alpha) -nf_ref. 
  unfold gcanon; rewrite g2h2g =>  Hnf; by apply le_ref,  canonS_LE. 
Qed.

Lemma gcanon0_phi0_succ_eqn alpha:
  T1nf alpha -> gcanon (phi0 (T1succ alpha)) 0 = zero.
Proof.
  rewrite -(h2g2h alpha) -nf_ref;unfold gcanon => Hnf. 
  rewrite succ_ref phi0_ref g2h2g.
  rewrite canon0_phi0_succ_eqn => //.
Qed. 

Lemma gcanon0_LT alpha:
  T1nf alpha -> alpha <> zero -> T1lt (gcanon alpha 0) alpha.
Proof. 
  rewrite -(h2g2h alpha) -nf_ref;unfold gcanon => Hnf Hpos.  
  rewrite g2h2g; apply lt_ref, canon0_LT => //.
  move => H; apply Hpos; rewrite H => //.
Qed. 


Lemma gcanonS_lt  (i : nat) [alpha : gT1]:
  T1nf alpha -> alpha <> zero -> T1lt (gcanon alpha i.+1) alpha.
Proof.
  rewrite -(h2g2h alpha) -nf_ref;unfold gcanon => Hnf Hpos.
  rewrite g2h2g; apply lt_ref, canonS_LT => //.
  move => H; apply Hpos; rewrite H => //.
Qed. 


Lemma gcanonS_cons_not_zero  (i : nat) (alpha : gT1) (n : nat) (beta : gT1):
  alpha <> zero -> gcanon (cons alpha n beta) i.+1 <> zero.
Proof.
  rewrite -(h2g2h alpha) => Hdiff; unfold gcanon.
  rewrite g2h_cons_rw; change zero with (h2g hzero) => Heq.
  rewrite h2g_eq_iff in Heq.
  apply canonS_cons_not_zero  in Heq => //.
  move: Hdiff; rewrite zero_ref;  by rewrite g2h2g h2g_eq_iff. 
Qed.

Lemma glimit_canonS_not_zero i lambda:
  T1nf lambda -> T1limit lambda -> gcanon lambda i.+1 <> zero.
Proof.
  rewrite -(h2g2h lambda) => Hnf Hlim; unfold gcanon.
  change zero with (h2g hzero); rewrite h2g_eq_iff. 
  apply limitb_canonS_not_zero. 
  - rewrite g2h2g; now rewrite -nf_ref in Hnf. 
  - by rewrite limitb_ref h2g2h. 
Qed.

                                                           
(* TODO : port the following lemmas 
canon_limit_strong:
  forall [lambda : hT1],
  nf lambda ->
  hlimitb lambda ->
  forall beta : hT1, beta t1< lambda -> {i : nat | beta t1< hcanon lambda i}
canonS_phi0_succ_eqn:
  forall (i : nat) [gamma : hT1],
  nf gamma -> hcanon (T1.phi0 (hsucc gamma)) i.+1 = hcons gamma i hzero
canonS_zero_inv:
  forall (alpha : hT1) (i : nat),
  hcanon alpha i.+1 = hzero -> alpha = hzero \/ alpha = one
canonS_limit_strong:
  forall [lambda : hT1],
  nf lambda ->
  hlimitb lambda ->
  forall beta : hT1,
  beta t1< lambda -> {i : nat | beta t1< hcanon lambda i.+1}
canon0_ocons_succ_eqn2:
  forall (n : nat) [gamma : hT1],
  nf gamma ->
  hcanon (hcons (hsucc gamma) n.+1 hzero) 0 = hcons (hsucc gamma) n hzero
canonSSn:
  forall (i : nat) [alpha : hT1] (n : nat),
  nf alpha ->
  hcanon (hcons alpha n.+1 hzero) i = hcons alpha n (hcanon (T1.phi0 alpha) i)
canon_lim1:
  forall (i : nat) [lambda : hT1],
  nf lambda ->
  hlimitb lambda -> hcanon (T1.phi0 lambda) i = T1.phi0 (hcanon lambda i)
canonS_ocons_succ_eqn2:
  forall (i n : nat) [gamma : hT1],
  nf gamma ->
  hcanon (hcons (hsucc gamma) n.+1 hzero) i.+1 =
  hcons (hsucc gamma) n (hcons gamma i hzero)
canonS_lim1:
  forall (i : nat) [lambda : hT1],
  nf lambda ->
  hlimitb lambda ->
  hcanon (T1.phi0 lambda) i.+1 = T1.phi0 (hcanon lambda i.+1)
canon0_lim2:
  forall (n : nat) [lambda : hT1],
  nf lambda ->
  hlimitb lambda ->
  hcanon (hcons lambda n.+1 hzero) 0 =
  hcons lambda n (T1.phi0 (hcanon lambda 0))
canon_tail:
  forall [alpha : hT1] [n : nat] [beta : hT1] (i : nat),
  nf (hcons alpha n beta) ->
  beta <> 0 -> hcanon (hcons alpha n beta) i = hcons alpha n (hcanon beta i)
canon_lim2:
  forall (i n : nat) [lambda : hT1],
  nf lambda ->
  hlimitb lambda ->
  hcanon (hcons lambda n.+1 hzero) i =
  hcons lambda n (T1.phi0 (hcanon lambda i))
canonS_lim2:
  forall (i n : nat) [lambda : hT1],
  nf lambda ->
  hlimitb lambda ->
  hcanon (hcons lambda n.+1 hzero) i.+1 =
  hcons lambda n (T1.phi0 (hcanon lambda i.+1))
 *)
