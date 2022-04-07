(** Gaia-compatible canonical sequences  

(imported from [hydras.Epsilon0.Canon]) *)

From mathcomp Require Import all_ssreflect zify.
From hydras Require Import Canon.
Require Import T1Bridge.
From hydras Require Import T1.



From gaia Require Import ssete9.
Import CantorOrdinal. 

(** Importation of Ketonen-Solovay's  machinery into gaia's world
    (work in progress) 
    
  Note that a lemma [Foo] may mask [Canon.Foo]  
*)


(* begin snippet canonDef *)
#[global] Notation hcanon := canon. 

Definition canon (a: T1) (i:nat) : T1 :=
  h2g (hcanon (g2h a) i).
(* end snippet canonDef *)

Notation canonS a  := (fun i =>  canon a (S i)).

Example ex0: canon (phi0 T1omega) 6 == phi0 (\F 6).
Proof. reflexivity. Qed.

Example ex1: canonS (phi0 T1omega) 6 == phi0 (\F 7).
Proof. reflexivity. Qed.

(** rewriting lemmas *)

(* begin snippet gcanonZero:: no-out *)
Lemma gcanon_zero i:  canon zero i = zero. 
Proof.  rewrite /canon => //. Qed. 
(* end snippet gcanonZero *)

(* begin snippet g2hCanonRw:: no-out *)
Lemma g2h_canon alpha i: g2h (canon alpha i) = hcanon (g2h alpha) i. 
Proof. by rewrite /canon g2h_h2gK. Qed.
(* end snippet g2hCanonRw *)

(* begin snippet gcanonSucc:: no-out *)
Lemma canon_succ i alpha (Halpha: T1nf alpha):
  canon (T1succ alpha) i = alpha.
(* end snippet gcanonSucc *)
Proof.
  rewrite -g2h_eqE g2h_canon g2h_succ canon_succ ?hnf_g2h => //.
Qed.


Lemma canonS_LE alpha n:
    T1nf alpha -> canon alpha n.+1 <= canon alpha n.+2.
Proof.
  rewrite -(h2g_g2hK alpha) -nf_ref /canon g2h_h2gK => Hnf. 
  by apply le_ref, canonS_LE. 
Qed.


Lemma canon0_phi0_succ_eqn alpha:
  T1nf alpha -> canon (phi0 (T1succ alpha)) 0 = zero.
Proof.
 rewrite -(h2g_g2hK alpha) -nf_ref /canon => Hnf. 
  rewrite succ_ref phi0_ref g2h_h2gK Canon.canon0_phi0_succ_eqn => //.
Qed. 


Lemma canon0_lt alpha:
  T1nf alpha -> alpha <> zero -> T1lt (canon alpha 0) alpha.
Proof. 
  rewrite -(h2g_g2hK alpha) -nf_ref /canon => Hnf.  
  rewrite g2h_h2gK => Hpos.
  apply lt_ref, Canon.canon0_LT => // H. apply Hpos; by rewrite H.  
Qed. 

Lemma canonS_lt  (i : nat) [alpha : T1]:
  T1nf alpha -> alpha <> zero -> T1lt (canon alpha i.+1) alpha.
Proof.
  rewrite -(h2g_g2hK alpha) -nf_ref /canon => Hnf Hpos.
  rewrite g2h_h2gK; apply lt_ref, Canon.canon_lt => //.
  move => H; apply Hpos; rewrite H => //.
Qed. 

(* begin snippet gcanonLt:: no-out *)
Lemma canon_lt  (i : nat) [alpha : T1]:
   T1nf alpha -> alpha <> zero -> canon alpha i < alpha.
(* end snippet gcanonLt *)
Proof. 
  case: i => [| n Hnf Hpos].  
  - apply canon0_lt. 
  - apply canonS_lt => //.
Qed. 

Lemma canonS_cons_not_zero  (i : nat) (alpha : T1) (n : nat) (beta : T1):
  alpha <> zero -> canon (cons alpha n beta) i.+1 <> zero.
Proof.
  rewrite -(h2g_g2hK alpha) /canon => Hdiff.  
  rewrite g2h_cons; change zero with (h2g T1.zero). rewrite h2g_eqE.
  apply canonS_cons_not_zero => H0; apply Hdiff. 
  rewrite -(h2g_g2hK zero);  apply h2g_eqE. 
  move: H0; by rewrite g2h_h2gK. 
Qed.

(* begin snippet glimitCanonSNotZero:: no-out *)
Lemma limit_canonS_not_zero i lambda:
  T1nf lambda -> T1limit lambda -> canon lambda i.+1 <> zero.
(* end snippet glimitCanonSNotZero *)
Proof.
  rewrite -(h2g_g2hK lambda) /canon => Hnf Hlim .
  change zero with (h2g T1.zero); rewrite h2g_eqE. 
  apply Canon.limitb_canonS_not_zero. 
  - move: Hnf; by rewrite g2h_h2gK -nf_ref.  
  - by rewrite limitb_ref h2g_g2hK. 
Qed.


(* begin snippet gcanonSPhi0Succ:: no-out *)
Lemma canonS_phi0_succ_eqn (i : nat) (gamma : T1): 
  T1nf gamma -> canon (phi0 (T1succ gamma)) i.+1 = cons gamma i zero.
(* end snippet gcanonSPhi0Succ *)
Proof.
  rewrite -(h2g_g2hK gamma) /canon succ_ref phi0_ref  g2h_h2gK => Hnf.
  change zero with (h2g T1.zero); rewrite Canon.canonS_phi0_succ_eqn ?h2g_cons
  =>//. 
  - move: Hnf; rewrite h2g_g2hK;  by rewrite /T1.nf nf_ref h2g_g2hK.
Qed.

(* begin snippet gcanonSSn:: no-out *)
Lemma canon_SSn_zero (i : nat) (alpha : T1) (n : nat):
  T1nf alpha ->
  canon (cons alpha n.+1 zero) i = cons alpha n (canon (phi0 alpha) i).
(* end snippet gcanonSSn *)
Proof.
  rewrite -(h2g_g2hK alpha) /canon g2h_cons g2h_h2gK => Hnf;
  rewrite -h2g_cons h2g_g2hK canon_SSn_zero; f_equal. 
  move: Hnf; by rewrite h2g_g2hK hnf_g2h.  
Qed.


Lemma canonS_zero_inv  (alpha : T1) (i : nat):
  canon alpha i.+1 = zero -> alpha = zero \/ alpha = one.
Proof.
  move => Halpha; have H: hcanon (g2h alpha) i.+1 = T1.zero; last first.
  case (Canon.canonS_zero_inv (g2h alpha) i) => // H0 ; [left | right];
                                                rewrite -(h2g_g2hK alpha) H0 //.
   move: Halpha;change zero with (h2g T1.zero); by rewrite h2g_eqE.
Qed.

(* begin snippet gcanonLim1:: no-out *)
Lemma canon_lim1 i (lambda: T1) :
  T1nf lambda ->
  T1limit lambda -> canon (phi0 lambda) i = phi0 (canon lambda i).
(* end snippet gcanonLim1 *)
Proof.
  move => Hnf Hlim; rewrite /canon.
  have H: hcanon (T1.phi0 (g2h lambda)) i = T1.phi0 (hcanon (g2h lambda) i).
  { rewrite -Canon.canon_lim1 => //. 
    - move: Hnf; by rewrite hnf_g2h.
    - by rewrite limitb_ref h2g_g2hK.
  }
  by rewrite phi0_ref H.
Qed. 


Lemma canon_tail alpha (n : nat) beta (i : nat):
  T1nf (cons alpha n beta) ->
  beta <> zero -> canon (cons alpha n beta) i = cons alpha n (canon beta i).
Proof.
  move => Hnf Hpos; rewrite -g2h_eqE g2h_canon !g2h_cons
                                        g2h_canon canon_tail //.
  move: Hnf; rewrite -hnf_g2h !g2h_cons  => //.
  move: beta {Hnf} Hpos ; by case.  
Qed.

Lemma canonS_ocons_succ_eqn2 i n (gamma: T1)(Hnf : T1nf gamma) :
  canon (cons (T1succ gamma) n.+1 zero) i.+1 =
    cons (T1succ gamma) n (cons gamma i zero).
Proof.
  rewrite -g2h_eqE g2h_canon !g2h_cons  g2h_succ g2h_zero.
  by rewrite  canonS_cons_succ_eqn2 ?hnf_g2h.
Qed. 


(* begin snippet gCanonLim2:: no-out *)
Lemma canon_lim2 i n (lambda : T1) (Hnf: T1nf lambda) (Hlim: T1limit lambda):
  canon (cons lambda n.+1 zero) i = cons lambda n (phi0 (canon lambda i)).
(* end snippet gCanonLim2 *)
Proof. 
  rewrite -g2h_eqE g2h_canon  !g2h_cons  canon_lim2; f_equal. 
  - by rewrite -g2h_canon. 
  - by rewrite hnf_g2h. 
  - by rewrite limitb_ref h2g_g2hK. 
Qed.

(* begin snippet gCanonLim3:: no-out *)
Lemma canon_lim3 i n alpha lambda (Halpha: T1nf alpha)
      (Hlambda: T1nf lambda) (Hlim :T1limit lambda) :
  canon (cons alpha n lambda) i = cons alpha n (canon lambda i).
(* end snippet gCanonLim3 *)
Proof. 
  rewrite -g2h_eqE g2h_canon !g2h_cons canon_lim3. 
  by rewrite -g2h_canon. 
  1,2 : by rewrite hnf_g2h.   
  by rewrite limitb_ref h2g_g2hK.
Qed.


(* begin snippet gcanonLimitStrong:: no-out *)
Lemma canon_limit_strong lambda :
  T1nf lambda -> T1limit lambda ->
  forall beta, T1nf beta ->
               T1lt beta  lambda -> {i : nat | T1lt beta (canon lambda i)}.
(* end snippet gcanonLimitStrong *)
Proof.
  rewrite -(h2g_g2hK lambda)  -nf_ref
          -limitb_ref => Hnf Hlim beta Hbeta.
  rewrite -(h2g_g2hK beta) => Hbetalt; apply hlt_iff in Hbetalt.
  case (@canon_limit_strong (g2h lambda) Hnf Hlim (g2h beta)).
  - split => //; rewrite hnf_g2h => //.
  - move => x Hx; exists x; rewrite -(h2g_g2hK beta). 
  rewrite -g2h_canon in Hx;  rewrite !h2g_g2hK.
  move: Hx;   rewrite -T1lt_iff => //.   
  rewrite /canon  -nf_ref; change (T1.nf (hcanon (g2h lambda) x));
    apply nf_canon => //.
Qed.



Lemma T1nf_canon alpha i : T1nf alpha -> T1nf (canon alpha i).
Proof.  
   rewrite /canon -nf_ref => ?; apply nf_canon; by rewrite hnf_g2h. 
Qed.

(* begin snippet gcanonLimitV2:: no-out *)
Lemma gcanon_limit_v2 (lambda: T1):
  T1nf lambda -> T1limit lambda -> limit_v2 (canon lambda) lambda.
(* end snippet gcanonLimitV2 *)
Proof.
  move => Hnf Hlim; split.
  - move => n; apply canon_lt => // H; subst; discriminate. 
  -  move => y Hnfy Hlt; 
             case (canon_limit_strong  lambda Hnf Hlim y Hnfy Hlt) => //.
     move => i Hi; exists i => //; by apply T1ltW. 
Qed.

(* begin snippet gcanonLimitMono:: no-out *)
Lemma  canon_limit_mono lambda i j (Hnf : T1nf lambda)
        (Hlim : T1limit lambda) (Hij : (i < j)%N) :
  canon lambda i < canon lambda j.
(* end snippet gcanonLimitMono *)
 Proof.      
   rewrite /canon -hlt_iff. 
   case (@canon_limit_mono (g2h lambda)  i j) => //.
   - by rewrite hnf_g2h. 
   - by  rewrite limitb_ref h2g_g2hK.
   - by apply /ltP . 
   -  move => _; case => //.
 Qed. 

 (* begin snippet gcanonLimitOf:: no-out  *)
 Lemma canon_limit_of lambda (Hnf : T1nf lambda) (Hlim : T1limit lambda) :
   limit_of (canon lambda) lambda.
 (* end snippet gcanonLimitOf *)
Proof.
   split => // [n m Hnm|].
   apply canon_limit_mono => //.
   apply gcanon_limit_v2 => //.
 Qed.    
 
 

 (** *  Adaptation of [canon] to type E0 *)

 Definition E0Canon (alpha: E0) (i: nat): E0.
   refine (@mkE0 (canon (cnf alpha) i)  _);
     case: alpha => cnf i0;  rewrite T1nf_canon =>  //; 
       by apply /eqP. 
Defined.

 Lemma E0_canon_lt (alpha: E0) i:
   cnf alpha <> zero -> E0lt (E0Canon alpha i) alpha.
 Proof. 
   move: i; case : alpha => cnf Heq i Hpos; rewrite /E0Canon /E0lt => /=. 
   pattern cnf at 2; rewrite -(h2g_g2hK cnf) -hlt_iff h2g_g2hK;
     apply Canon.canon_lt. 
   - rewrite hnf_g2h;  by apply /eqP.
   - rewrite /Hpos -h2g_eqE h2g_g2hK => H0; 
     apply Hpos; subst; by rewrite -g2h_eqE.
 Qed.

