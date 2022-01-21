From hydras Require Import T1.
From mathcomp Require Import all_ssreflect zify.
Require Import T1Bridge.
Import ssete9.CantorOrdinal. 

From gaia Require Import ssete9.
From hydras Require Import Canon.
Import ssete9.CantorOrdinal. 
Set Bullet Behavior "Strict Subproofs".

(** Importation of Ketonen-Solovay's  machinery into gaia's world
    (work in progress) 
*)

#[global] Notation hcanon := canon. 

Definition gcanon (a: gT1) (i:nat) : gT1 :=
  h2g (hcanon (g2h a) i).

Compute gcanon (phi0 T1omega) 6 == (phi0 (\F 6))%brg.

(** rewriting lemmas *)



Lemma gcanon_zero i:  gcanon zero i = zero. 
Proof.  unfold gcanon => //. Qed. 

Lemma hcanon_g2h_rw alpha i: hcanon (g2h alpha) i = g2h (gcanon alpha i). 
Proof.  by unfold gcanon;  rewrite g2h2g. Qed.


Lemma nf_gcanon alpha i : T1nf alpha -> T1nf (gcanon alpha i).
Proof.  
  unfold gcanon => Halpha. rewrite -nf_ref. 
  apply nf_canon. by rewrite nf_g2h. 
Qed.



Lemma gcanon_succ i alpha: T1nf alpha -> gcanon (T1succ alpha) i = alpha.
Proof.
  unfold gcanon => Halpha; rewrite g2h_succ_rw  canon_succ.
  - by rewrite h2g2h.
  - by rewrite nf_g2h. 
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
  rewrite succ_ref phi0_ref g2h2g canon0_phi0_succ_eqn => //.
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

Lemma gcanonS_phi0_succ_eqn (i : nat) (gamma : T1): 
  T1nf gamma -> gcanon (phi0 (T1succ gamma)) i.+1 = cons gamma i zero.
Proof.                                                            
  rewrite -(h2g2h gamma) => Hnf.
  unfold gcanon; rewrite succ_ref phi0_ref  g2h2g. 
  change zero with (h2g hzero); rewrite canonS_phi0_succ_eqn. 
  -  by rewrite h2g_cons_rw. 
  -  rewrite h2g2h in Hnf; unfold nf;  by rewrite nf_ref h2g2h.
Qed.

Lemma gcanonSSn (i : nat) (alpha : T1) (n : nat):
  T1nf alpha ->
  gcanon (cons alpha n.+1 zero) i = cons alpha n (gcanon (phi0 alpha) i).
Proof.
  rewrite -(h2g2h alpha) => Hnf;
                            unfold gcanon;
                            rewrite g2h_cons_rw g2h2g. 
  rewrite -h2g_cons_rw h2g2h canonSSn; f_equal. 
  by rewrite h2g2h -(h2g2h alpha) -nf_ref in Hnf.  
Qed.


Lemma gcanonS_zero_inv  (alpha : T1) (i : nat):
  gcanon alpha i.+1 = zero -> alpha = zero \/ alpha = one.
Proof.
  move => Halpha; have H: hcanon (g2h alpha) i.+1 = hzero. 
  {
    unfold gcanon in Halpha.
    change zero with (h2g hzero) in Halpha; by rewrite h2g_eq_iff in Halpha.    
  }
  case (canonS_zero_inv (g2h alpha) i) => // H0 .
  left; rewrite -(h2g2h alpha) H0 //.
  right; rewrite -(h2g2h alpha) H0 //.
Qed.

Lemma gcanon_lim1 i (lambda: T1) :
  T1nf lambda ->
  T1limit lambda -> gcanon (phi0 lambda) i = phi0 (gcanon lambda i).
Proof.
  move => Hnf Hlim.
  have H: hcanon (hphi0 (g2h lambda)) i = hphi0 (hcanon (g2h lambda) i).
  { rewrite -canon_lim1. 
    - f_equal. 
    - by rewrite -(h2g2h lambda) -nf_ref in Hnf. 
    - by rewrite limitb_ref h2g2h.
      }
     unfold gcanon; by rewrite phi0_ref H.
Qed. 


Lemma gcanon_tail alpha (n : nat) beta (i : nat):
  T1nf (cons alpha n beta) ->
  beta <> zero -> gcanon (cons alpha n beta) i = cons alpha n (gcanon beta i).
Proof.
  move => Hnf Hpos.
  rewrite -(h2g2h (T1Bridge.cons alpha n beta)).
  have H: hcanon (hcons (g2h alpha) n (g2h beta)) i =
            hcons (g2h alpha) n (hcanon (g2h beta) i).
  {
    rewrite -canon_tail => //. 
    rewrite -(h2g2h alpha) -(h2g2h beta)  - h2g_cons_rw in Hnf. 
    by rewrite -nf_ref in Hnf.
    move: Hnf Hpos; case:  beta => //.     
  }
  - unfold gcanon; rewrite g2h2g  g2h_cons_rw. rewrite H. 
    pattern alpha at 2. rewrite -(h2g2h alpha). 
    rewrite h2g_cons_rw.
    f_equal. 
    by rewrite h2g2h.
Qed.

Lemma gcanonS_ocons_succ_eqn2 i n (gamma: T1) :
  T1nf gamma ->
  gcanon (cons (T1succ gamma) n.+1 zero) i.+1 =
    cons (T1succ gamma) n (cons gamma i zero).
Proof.
move => Hnf; specialize  (@canonS_ocons_succ_eqn2 i n (g2h gamma)) => Hnf2. 
unfold gcanon; rewrite g2h_cons_rw.
- replace (g2h (T1succ gamma)) with (hsucc (g2h gamma)).
  + replace (g2h zero)  with hzero. 
    * rewrite Hnf2.
      rewrite h2g_cons_rw; f_equal. 
      specialize (succ_ref (g2h gamma)). 
      rewrite h2g2h => Heq => //.
      rewrite  h2g_cons_rw. 
      f_equal.
      by rewrite h2g2h.     
      specialize (nf_ref (g2h gamma)). 
      rewrite h2g2h  Hnf => //. 
    *  by rewrite zero_ref g2h2g.
  + specialize (succ_ref (g2h gamma)); rewrite h2g2h => Heq.
    by rewrite Heq g2h2g. 
Qed.

Lemma gcanon_lim2 i n (lambda : T1):
  T1nf lambda ->
  T1limit lambda ->
  gcanon (cons lambda n.+1 zero) i =
    cons lambda n (phi0 (gcanon lambda i)).
Proof. 
  move => Hnf Hlim.
  rewrite -g2h_eq_iff  -hcanon_g2h_rw  !g2h_cons_rw  canon_lim2.
  f_equal. 
  by rewrite -hcanon_g2h_rw. 
  by rewrite nf_g2h. 
  by rewrite limitb_ref h2g2h. 
Qed.

Lemma gcanon_limit_strong lambda :
  T1nf lambda -> T1limit lambda ->
  forall beta, T1nf beta ->
               T1lt beta  lambda -> {i : nat | T1lt beta (gcanon lambda i)}.
Proof.
  rewrite -(h2g2h lambda)  -nf_ref. 
  rewrite -limitb_ref => Hnf Hlim beta Hbeta Hbetalt.
  rewrite -(h2g2h beta) in Hbetalt; apply hlt_iff in Hbetalt. 
  destruct (@canon_limit_strong (g2h lambda) Hnf Hlim (g2h beta)) as [x Hx].
  split. 
  - red;  by rewrite nf_ref h2g2h.
  - split; auto.
  - exists x; rewrite -(h2g2h beta). 
  rewrite hcanon_g2h_rw in Hx;  rewrite !h2g2h.
  rewrite -T1ltiff in Hx => //.
  unfold gcanon; rewrite -nf_ref; apply nf_canon, Hnf. 
Qed.

