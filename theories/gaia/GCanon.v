(** Import canonical sequences from hydra-battles *)



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

Definition canon (a: T1) (i:nat) : T1 :=
  h2g (hcanon (g2h a) i).

Notation canonS a  := (fun i =>  canon a (S i)).

Example ex0: canon (phi0 T1omega) 6 == phi0 (\F 6).
Proof. reflexivity. Qed.

Example ex1: canonS (phi0 T1omega) 6 == phi0 (\F 7).
Proof. reflexivity. Qed.

(** rewriting lemmas *)

Lemma gcanon_zero i:  canon zero i = zero. 
Proof.  rewrite /canon => //. Qed. 

Lemma g2h_canon alpha i: g2h (canon alpha i) = hcanon (g2h alpha) i. 
Proof. by rewrite /canon g2h_h2g. Qed.

Lemma gcanon_succ i alpha (Halpha: T1nf alpha):
  canon (T1succ alpha) i = alpha.
Proof.
  rewrite -g2h_eq_iff g2h_canon g2h_succ canon_succ ?hnf_g2h => //.
Qed.


Lemma gcanonS_LE alpha n:
    T1nf alpha -> canon alpha n.+1 <= canon alpha n.+2.
Proof.
  rewrite -(h2g_g2h alpha) -nf_ref /canon g2h_h2g => Hnf. 
  by apply le_ref, canonS_LE. 
Qed.

Lemma gcanon0_phi0_succ_eqn alpha:
  T1nf alpha -> canon (phi0 (T1succ alpha)) 0 = zero.
Proof.
 rewrite -(h2g_g2h alpha) -nf_ref /canon => Hnf. 
  rewrite succ_ref phi0_ref g2h_h2g canon0_phi0_succ_eqn => //.
Qed. 

Lemma gcanon0_lt alpha:
  T1nf alpha -> alpha <> zero -> T1lt (canon alpha 0) alpha.
Proof. 
  rewrite -(h2g_g2h alpha) -nf_ref /canon => Hnf Hpos.  
  rewrite g2h_h2g; apply lt_ref, canon0_LT => //.
  move => H; apply Hpos; rewrite H => //.
Qed. 

Lemma gcanonS_lt  (i : nat) [alpha : T1]:
  T1nf alpha -> alpha <> zero -> T1lt (canon alpha i.+1) alpha.
Proof.
  rewrite -(h2g_g2h alpha) -nf_ref /canon => Hnf Hpos.
  rewrite g2h_h2g; apply lt_ref, canonS_lt => //.
  move => H; apply Hpos; rewrite H => //.
Qed. 

Lemma gcanon_lt  (i : nat) [alpha : T1]:
   T1nf alpha -> alpha <> zero -> T1lt (canon alpha i) alpha.
Proof. 
  case : i.   
  - apply gcanon0_lt. 
  - move => n Hnf Hpos; apply gcanonS_lt => //.
Qed. 



Lemma canonS_cons_not_zero  (i : nat) (alpha : T1) (n : nat) (beta : T1):
  alpha <> zero -> canon (cons alpha n beta) i.+1 <> zero.
Proof.
  rewrite -(h2g_g2h alpha) /canon => Hdiff.  
  rewrite g2h_cons; change zero with (h2g hzero) => Heq.
  rewrite h2g_eq_iff in Heq.
  apply canonS_cons_not_zero  in Heq => //.
  move: Hdiff; rewrite zero_ref;  by rewrite g2h_h2g h2g_eq_iff. 
Qed.

Lemma glimit_canonS_not_zero i lambda:
  T1nf lambda -> T1limit lambda -> canon lambda i.+1 <> zero.
Proof.
  rewrite -(h2g_g2h lambda) /canon => Hnf Hlim .
  change zero with (h2g hzero); rewrite h2g_eq_iff. 
  apply limitb_canonS_not_zero. 
  - rewrite g2h_h2g; now rewrite -nf_ref in Hnf. 
  - by rewrite limitb_ref h2g_g2h. 
Qed.

Lemma gcanonS_phi0_succ_eqn (i : nat) (gamma : T1): 
  T1nf gamma -> canon (phi0 (T1succ gamma)) i.+1 = cons gamma i zero.
Proof.                                                            
  rewrite -(h2g_g2h gamma) /canon succ_ref phi0_ref  g2h_h2g => Hnf.
  change zero with (h2g hzero); rewrite canonS_phi0_succ_eqn ?h2g_cons
  =>//. 
  - rewrite h2g_g2h in Hnf;  by rewrite /hnf nf_ref h2g_g2h.
Qed.

Lemma gcanonSSn (i : nat) (alpha : T1) (n : nat):
  T1nf alpha ->
  canon (cons alpha n.+1 zero) i = cons alpha n (canon (phi0 alpha) i).
Proof.
  rewrite -(h2g_g2h alpha) /canon g2h_cons g2h_h2g => Hnf;
  rewrite -h2g_cons h2g_g2h canonSSn; f_equal. 
  by rewrite h2g_g2h -(h2g_g2h alpha) -nf_ref in Hnf.  
Qed.


Lemma gcanonS_zero_inv  (alpha : T1) (i : nat):
  canon alpha i.+1 = zero -> alpha = zero \/ alpha = one.
Proof.
  move => Halpha; have H: hcanon (g2h alpha) i.+1 = hzero. 
  {
    change zero with (h2g hzero) in Halpha; by rewrite h2g_eq_iff in Halpha.    
  }
  case (canonS_zero_inv (g2h alpha) i) => // H0 ; [left | right];
                                          rewrite -(h2g_g2h alpha) H0 //.
Qed.

Lemma gcanon_lim1 i (lambda: T1) :
  T1nf lambda ->
  T1limit lambda -> canon (phi0 lambda) i = phi0 (canon lambda i).
Proof.
  move => Hnf Hlim; rewrite /canon.
  have H: hcanon (hphi0 (g2h lambda)) i = hphi0 (hcanon (g2h lambda) i).
  { rewrite -canon_lim1 => //. 
    - by rewrite -(h2g_g2h lambda) -nf_ref in Hnf. 
    - by rewrite limitb_ref h2g_g2h.
  }
  by rewrite phi0_ref H.
Qed. 


Lemma gcanon_tail alpha (n : nat) beta (i : nat):
  T1nf (cons alpha n beta) ->
  beta <> zero -> canon (cons alpha n beta) i = cons alpha n (canon beta i).
Proof.
  move => Hnf Hpos; rewrite -g2h_eq_iff g2h_canon !g2h_cons
                                        g2h_canon canon_tail //.
  rewrite -hnf_g2h !g2h_cons in Hnf => //.
  move: {Hnf} Hpos; case:  beta => //.     
Qed.

Lemma gcanonS_ocons_succ_eqn2 i n (gamma: T1) :
  T1nf gamma ->
  canon (cons (T1succ gamma) n.+1 zero) i.+1 =
    cons (T1succ gamma) n (cons gamma i zero).
Proof.
  move => Hnf.
  rewrite -g2h_eq_iff g2h_canon !g2h_cons  g2h_succ g2h_zero.
  by rewrite  canonS_ocons_succ_eqn2 ?hnf_g2h.
Qed. 


Lemma gcanon_lim2 i n (lambda : T1):
  T1nf lambda ->
  T1limit lambda ->
  canon (cons lambda n.+1 zero) i =
    cons lambda n (phi0 (canon lambda i)).
Proof. 
  move => Hnf Hlim;
  rewrite -g2h_eq_iff g2h_canon  !g2h_cons  canon_lim2; f_equal. 
  - by rewrite -g2h_canon. 
  - by rewrite hnf_g2h. 
  - by rewrite limitb_ref h2g_g2h. 
Qed.

Lemma gcanon_limit_strong lambda :
  T1nf lambda -> T1limit lambda ->
  forall beta, T1nf beta ->
               T1lt beta  lambda -> {i : nat | T1lt beta (canon lambda i)}.
Proof.
  rewrite -(h2g_g2h lambda)  -nf_ref
          -limitb_ref => Hnf Hlim beta Hbeta.
  rewrite -(h2g_g2h beta) =>Hbetalt; apply hlt_iff in Hbetalt.
  case (@canon_limit_strong (g2h lambda) Hnf Hlim (g2h beta)).
  - split => //; rewrite hnf_g2h => //.
  - move => x Hx; exists x; rewrite -(h2g_g2h beta). 
  rewrite -g2h_canon in Hx;  rewrite !h2g_g2h;
    rewrite -T1lt_iff in Hx => //.   
  rewrite /canon  -nf_ref; change (hnf (hcanon (g2h lambda) x));
    apply nf_canon => //.
Qed. 


Lemma T1nf_canon alpha i : T1nf alpha -> T1nf (canon alpha i).
Proof.  
   rewrite /canon -nf_ref => ?; apply nf_canon; by rewrite hnf_g2h. 
Qed.

Lemma gcanonS_limit_mono (alpha : T1) i j :
  T1nf alpha -> (i < j)%coq_nat -> T1limit alpha ->
  T1lt (canon alpha (S i)) (canon alpha (S j)). 
Proof.
  rewrite /canon -!g2h_canon !h2g_g2h => Hnf Hij Hlim.
  case (@canonS_limit_mono (g2h alpha) i j) => //.
  - by rewrite hnf_g2h.
  - rewrite limitb_ref h2g_g2h => //. 
  - move => Hnf2 ; rewrite hlt_iff; case; rewrite /canon => //.
Qed.



 Lemma canon_limit_v2   lambda: 
    T1nf lambda -> T1limit lambda ->
    limit_v2 (canon lambda) lambda.
 Proof.
   move => Hnf Hlim; split.
   - move => n; apply gcanon_lt => // H; subst; discriminate. 
   -  move => y Hnfy Hlt; 
              case (gcanon_limit_strong  lambda Hnf Hlim y Hnfy Hlt) => //.
      move => i Hi; exists i => //; by apply T1ltW. 
 Qed.
 
 Lemma  gcanon_limit_mono lambda i j (Hnf : T1nf lambda)
        (Hlim : T1limit lambda) (Hij : (i < j)%N) :
   T1lt (canon lambda i) (canon lambda j). 
 Proof.      
   rewrite /canon -hlt_iff. 
   case (@canon_limit_mono (g2h lambda)  i j) => //.
   - by rewrite hnf_g2h. 
   - by  rewrite limitb_ref h2g_g2h.
   - by apply /ltP . 
   -  move => _; case => //.
 Qed. 

 Lemma canon_limit_of lambda (Hnf : T1nf lambda) (Hlim : T1limit lambda) :
   limit_of (canon lambda) lambda.
  Proof.
    split => //.
    move => n m Hnm; apply gcanon_limit_mono => //.
   apply canon_limit_v2 => //.
  Qed.    


