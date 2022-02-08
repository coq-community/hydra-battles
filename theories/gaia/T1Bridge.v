(**  * Bridge between Hydra-battle's and Gaia's [T1]  (Experimental) 
 *)

 From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder.
From hydras Require Import T1 E0.
From mathcomp Require Import all_ssreflect zify.
From gaia Require Export ssete9.
Set Bullet Behavior "Strict Subproofs".

(* begin snippet hT1gT1 *)

(** Hydra-Battles' type for ordinal terms below [epsilon0] *)

#[global] Notation hT1 := T1.T1.

(** Gaia's type for ordinal terms below [epsilon0] *)

#[local] Notation T1 := CantorOrdinal.T1.

(* end snippet hT1gT1 *)

Set Implicit Arguments.
Unset Strict Implicit.

(** From hydra to gaia and back *)

(* begin snippet MoreNotations *)
#[global] Notation hzero := T1.zero.
#[global] Notation hone := T1.one.
#[global] Notation hcons := T1.ocons.
#[global] Notation hfin := T1.fin.

#[global] Notation homega := T1.omega.
#[global] Notation hsucc := T1.succ.
#[global] Notation hphi0 alpha := (T1.phi0 alpha).
#[global] Notation hplus := T1.plus.
#[global] Notation hmult := T1.mult.

#[global] Notation hlt := T1.lt.
#[global] Notation hLT := T1.LT.
#[global] Notation hLE := T1.LE.
#[global] Notation hnfb := T1.nf_b.
#[global] Notation hlimitb := T1.limitb.
#[global] Notation his_succ := T1.succb.
#[global] Notation hnf := T1.nf.




#[global] Notation gLT := (restrict T1nf T1lt).
#[global] Notation gLE := (restrict T1nf T1le).

#[global] Notation hle := (MoreOrders.leq hlt). 
(* end snippet MoreNotations *)

(* begin snippet h2gG2hDef *)

Fixpoint h2g (alpha : hT1) : T1 :=
  match alpha with
    T1.zero => zero
  | hcons alpha n beta => cons (h2g alpha) n (h2g beta)
  end.

Fixpoint g2h (alpha : T1) : hT1 :=
  match alpha with
    zero => T1.zero
  | cons alpha n beta => hcons (g2h alpha) n (g2h beta)
  end.

(* end snippet h2gG2hDef *)

(* begin snippet h2gG2hRw:: no-out *)
Lemma h2g_g2h : cancel g2h h2g.
(* end snippet h2gG2hRw *)
Proof.
  move => alpha; elim: alpha => //= t1 IHalpha1 n t2 IHalpha2.
  by rewrite IHalpha1 IHalpha2.
Qed.

(* begin snippet g2hH2gRw:: no-out *)
Lemma g2h_h2g : cancel h2g g2h.
(* end snippet g2hH2gRw *)
Proof.
  move => alpha; elim: alpha => //= t1 IHalpha1 n t2 IHalpha2.
  by rewrite IHalpha1 IHalpha2.
Qed.


Lemma g2h_eq_iff a b :  g2h a = g2h b <-> a = b.
Proof. 
    split.
    - rewrite -(h2g_g2h a) -(h2g_g2h b)  !g2h_h2g => // Heq //; rewrite Heq => //.
    - move => H; by subst. 
Qed.

Lemma h2g_eq_iff (a b :hT1) :  h2g a = h2g b <-> a = b.
Proof. 
    split => Heq.
    - move : Heq; rewrite  -(g2h_h2g a) -(g2h_h2g b) !h2g_g2h  =>  // Heq.
     by rewrite Heq. 
    - by subst. 
Qed.

(** refinement of constants, functions, etc. *)

(* begin snippet refineDefs *)

Definition refines0 (x:hT1)(y:T1) :=
  y = h2g x.

Definition refines1 (f:hT1 -> hT1)
           (f': T1 -> T1) :=
  forall x: hT1, f' (h2g x) = h2g (f x).

Definition refines2 (f:hT1 -> hT1 -> hT1)
           (f': T1 -> T1 -> T1 ) :=
  forall x y : hT1, f' (h2g x) (h2g y) = h2g (f x y).

Definition refinesPred (hP: hT1 -> Prop) (gP: T1 -> Prop) :=
  forall x : hT1, hP x <-> gP (h2g x).

Definition refinesRel (hR: hT1 -> hT1 -> Prop)
           (gR: T1 -> T1 -> Prop) :=
  forall x y : hT1, hR x y <-> gR (h2g x) (h2g y).

(* end snippet refineDefs *)

Lemma refines1_R f f' :
  refines1 f f' ->
  forall y: T1, f (g2h y) = g2h (f' y).
Proof.
  move => Href y; rewrite -{2}(h2g_g2h y).
  by rewrite Href g2h_h2g.
Qed.


Lemma refines2_R f f' :
  refines2 f f' ->
  forall y z: T1, f (g2h y) (g2h z) = g2h (f' y z).
Proof.
  move => Href y z; by rewrite -{2}(h2g_g2h y) -{2}(h2g_g2h z) ?Href ?g2h_h2g. 
Qed.


(** Refinements of usual constants *)
(* begin snippet constantRefs:: no-out *)


Lemma zero_ref : refines0 hzero zero.
Proof. by []. Qed.


Lemma one_ref : refines0 hone one.
Proof. by []. Qed.



Lemma Finite_ref (n:nat) : refines0 (hfin n) (\F n).
Proof. by case: n. Qed.


Lemma omega_ref : refines0 homega T1omega.
Proof. by []. Qed.

(* end snippet constantRefs *)

(** unary functions *)
(* begin snippet unaryRefs:: no-out *)


Lemma succ_ref: refines1 hsucc T1succ.
(*| .. coq:: none |*)
Proof.
  elim => [//|//  x] => //.
  case: x => // x n y H p z H0 /=; by rewrite H0.
Qed.
(*||*)

Lemma phi0_ref x: refines0 (hphi0 x) (phi0 (h2g x)). (* .no-out *)
(*| .. coq:: none |*)
Proof. by []. Qed.
(* end snippet unaryRefs *)


Lemma ap_ref : refinesPred T1.ap T1ap. 
Proof.
  move => alpha; split => Hap; first by case: Hap.
  move: Hap; case: alpha => //= alpha n beta /andP [Hn Hz].
  move/eqP: Hn Hz =>->; move/eqP; by case: beta.
Qed.

Lemma T1eq_refl (a: T1) : T1eq a a.
Proof. by apply/T1eqP. Qed.

Lemma T1eq_rw a b: T1eq a b -> g2h a = g2h b.
Proof. by move => /T1eqP ->. Qed. 

Lemma T1eq_h2g (a b : hT1) : T1eq (h2g a) (h2g b) -> a = b.
Proof.
  move => H; rewrite <- (g2h_h2g a), <- (g2h_h2g b); by apply T1eq_rw.
Qed.

(* begin snippet compareRef:: no-out *)
Lemma compare_ref (x y: hT1) :
  match T1.compare_T1 x y with
  | Datatypes.Lt => T1lt (h2g x) (h2g y)
  |  Datatypes.Eq => h2g x = h2g y
  |  Datatypes.Gt => T1lt (h2g y) (h2g x)
  end.
(* end snippet compareRef *)
Proof.
  move: y; elim: x => [|x1 IHx1 n x2 IHx2]; case => //= y1 n0 y2.
  case H: (T1.compare_T1 x1 y1).
  - specialize (IHx1 y1); rewrite H in IHx1.
    case H0: (PeanoNat.Nat.compare n n0).
    + have ->: (n = n0) by apply Compare_dec.nat_compare_eq.
      case H1: (T1.compare_T1 x2 y2).
      * rewrite IHx1; f_equal.
        by specialize (IHx2 y2); now rewrite H1 in IHx2.
      * case (h2g x1 < h2g y1); [trivial|].
        rewrite IHx1 eqxx /= eqxx ltnn.
        specialize (IHx2 y2); by rewrite H1 in IHx2.
      * rewrite IHx1 T1ltnn eqxx ltnn eqxx.
        specialize (IHx2 y2); by rewrite H1 in IHx2.
    + rewrite IHx1 T1ltnn eqxx.
      apply Compare_dec.nat_compare_Lt_lt in H0.
      by move/ltP: H0 =>->.
    + rewrite IHx1 T1ltnn eqxx.
      apply Compare_dec.nat_compare_Gt_gt in H0.
      by move/ltP: H0 =>->.
  - specialize (IHx1 y1); rewrite H in IHx1; now rewrite IHx1.
  - specialize (IHx1 y1); rewrite H in IHx1; now rewrite IHx1.
Qed.

(* begin snippet ltRef:: no-out *)
Lemma lt_ref : refinesRel hlt T1lt.
(* end snippet ltRef *)
Proof.
  move=> a b; split.
  - rewrite /T1.lt /Comparable.compare; move => Hab. 
    generalize (compare_ref a b); now rewrite Hab.
  - move => Hab; red.
    case_eq (T1.compare_T1 a b).
    + move => Heq; generalize (compare_ref a b); rewrite Heq.
      move => H0; move: Hab; rewrite H0;
              move => Hb; by rewrite T1ltnn in Hb.
    + by [].     
    + move => HGt; generalize (compare_ref a b); rewrite HGt.
      move =>  H1; have H2: (h2g a < h2g a).
      * eapply T1lt_trans; eauto.
      * by rewrite T1ltnn in H2. 
Qed.

(* To simplify ! *)
Lemma le_ref : refinesRel (MoreOrders.leq hlt) T1le.
Proof.
  move=> a b; split.
  - rewrite /T1le /Comparable.compare; move => Hab;  elim: Hab. 
    + move => y Hy; generalize (lt_ref a y). 
      red in Hy; rewrite /hlt Hy. 
      move => H; apply /orP; right; by apply H. 
    + apply /orP; by left. 
  - rewrite T1le_eqVlt; move => /orP; destruct 1. 
    have H0: a = b. 
    { rewrite -(g2h_h2g a) -(g2h_h2g b). 
      move: H => /eqP Heq. 
      by rewrite Heq.
    }
    + subst; right.
    + left; by rewrite lt_ref. 
Qed. 


(* begin snippet decideHLtRw:: no-out *)
Lemma decide_hlt_rw (a b : hT1):
  bool_decide (hlt a b) = (h2g a < h2g b).
(* end snippet decideHLtRw *)
Proof.
  rewrite /T1.lt; generalize (compare_ref a b);
    rewrite /Comparable.compare /=.
  destruct (decide (T1.compare_T1 a b = Datatypes.Lt)).
  - have bd := e.
    apply (bool_decide_eq_true _) in bd.
    by rewrite bd e.
  - have bd := n.
    apply (bool_decide_eq_false _) in bd.
    rewrite bd.
    destruct (T1.compare_T1 a b).
    * by move => ->; rewrite T1ltnn.
    * by [].
    * move => Hlt.
      symmetry.
      apply/negP => Hlt'.
      have H1 : (h2g b < h2g b) by apply T1lt_trans with (h2g a).
      by rewrite T1ltnn in H1.
Qed.


(* begin snippet eqRef:: no-out *)
Lemma eqref : refinesRel eq eq.
(* end snippet eqRef *)
Proof.
  move => a b; split.
  - by move => ->.
  - move => Hab; apply T1eq_h2g; by rewrite Hab T1eq_refl.
Qed.




(* begin snippet plusRef:: no-out *)
Lemma plus_ref : refines2 hplus T1add.
(* end snippet plusRef *)
Proof.
  move => x; elim: x => [|x1 IHx1 n x2 IHx2]; case => //= y1 n0 y2.
  case Hx1y1: (T1.compare_T1 x1 y1); move: (compare_ref x1 y1);
    rewrite Hx1y1 => H.
  - rewrite /Comparable.compare H T1ltnn /=; f_equal.
    by rewrite Hx1y1 -H /=.
  - by rewrite /Comparable.compare H Hx1y1.
  - replace (h2g x1 < h2g y1) with false.
    rewrite /Comparable.compare H /= Hx1y1; f_equal.
    change (cons (h2g y1) n0 (h2g y2)) with (h2g (hcons y1 n0 y2)).
    by rewrite IHx2.
    by apply T1lt_anti in H.
Qed.



Section Proof_of_mult_ref.

  Lemma T1mul_eqn1 (c : T1) : c * zero = zero. 
  Proof. by []. Qed.

  Lemma mult_eqn1 c : hmult c hzero = hzero.
  Proof. case: c; cbn => //; by case. 
  Qed.


  Lemma T1mul_eqn3 n b n' b' : cons zero n b * cons zero n' b' =
                                 cons zero (n * n' + n + n') b'.      
  Proof. by [].  Qed. 


  Lemma mult_eqn3 n b n' b' :
    hmult (hcons hzero n b) (hcons hzero n' b') =
      hcons hzero (n * n' + n + n') b'.      
  Proof. cbn; f_equal; nia. Qed.


  Lemma T1mul_eqn4 a n b n' b' :
    a != zero -> (cons a n b) * (cons zero n' b') =
                   cons a (n * n' + n + n') b.
  Proof. 
    move => /T1eqP.  cbn.
    move =>  Ha'; have Heq: T1eq a zero = false.
    { move: Ha'; case: a => //. }
    rewrite Heq; by cbn.        
  Qed.

  Lemma mult_eqn4 a n b n' b' :
    a <> T1.zero ->
    T1.mult (hcons a n b) (hcons T1.zero n' b') =
      hcons a (n * n' + n + n') b.
  Proof. 
    cbn.  case: a => [//|alpha n0 beta _ ].
    f_equal; nia. 
  Qed.

  Lemma T1mul_eqn5 a n b a' n' b' :
    a' != zero ->
    (cons a n b) * (cons a' n' b') =
      cons (a + a') n' (T1mul (cons a n b) b').
  Proof. 
    move => H /=;  cbn;  have Ha' : T1eq a' zero = false. 
    { move: a' H; case => //. }
    case (T1eq a zero); cbn; by rewrite Ha'. 
  Qed.

  Lemma mult_eqn5 a n b a' n' b' :
    a' <>  hzero ->
    T1.mult (hcons a n b)  (hcons a' n' b') =
      hcons (hplus a  a') n' (hmult (hcons a n b) b').
  Proof.
    move => Ha'; cbn; case: a; move: Ha'; case: a' => //.
  Qed.

  Lemma h2g_cons a n b : h2g (hcons a n b)= cons (h2g a) n (h2g b). 
  Proof. by []. Qed.

  Lemma g2h_cons a n b : g2h (cons a n b) = hcons (g2h a) n (g2h b).
  Proof. by []. Qed.
  
  Lemma h2g_zero  : h2g hzero = zero. 
  Proof. by []. Qed.

  Lemma g2h_zero : g2h zero = hzero.
    Proof. by []. Qed. 

  Lemma mult_ref0 : refines2 hmult T1mul.
  Proof.
    move => x y;  move: x; induction y. 
    -   move => x; simpl h2g; rewrite T1mul_eqn1; case x => //.
        case => //.
    -  case.
       + simpl h2g => // /=.
       + move => alpha n0 beta.
         destruct (T1.T1_eq_dec  alpha T1.zero).
         *  subst; destruct (T1.T1_eq_dec y1 T1.zero).
            -- subst y1; simpl h2g; rewrite T1mul_eqn3; f_equal; nia.
            -- repeat rewrite !h2g_cons !h2g_zero.
               rewrite T1mul_eqn5.
               ++ rewrite mult_eqn5 => //.
                  ** simpl h2g; simpl T1add; f_equal.
                     destruct (T1.T1_eq_dec y2 T1.zero).
                     { subst; by cbn. }
                     { change (cons zero n0 (h2g beta)) with
                         (h2g (hcons T1.zero n0 beta)); now rewrite IHy2.
                     }
               ++  destruct y1; [now destruct n1| now compute].
         * destruct (T1.T1_eq_dec y1 T1.zero).
           --   subst; rewrite !h2g_cons !h2g_zero;
                  rewrite T1mul_eqn4.
                ++ by rewrite mult_eqn4. 
                ++ case :alpha n1 => //. 
           --   rewrite !h2g_cons. 
                ++ rewrite T1mul_eqn5.
                   ** rewrite  mult_eqn5 => //. 
                      simpl h2g; rewrite plus_ref; f_equal. 
                      change (cons (h2g alpha) n0 (h2g beta))
                        with (h2g (hcons alpha n0 beta)); now rewrite IHy2.
                   **  case: y1 n2 IHy1 => //.
  Qed.

End Proof_of_mult_ref.

(* begin snippet multRef:: no-out *)
Lemma mult_ref : refines2 hmult T1mul.
(* end snippet multRef *)
Proof mult_ref0.
(* begin snippet multA:: no-out *)
Lemma g2h_mult_rw (a b : T1) : g2h (a * b) = hmult (g2h a) (g2h b).
Proof. apply symmetry, refines2_R,  mult_ref. Qed.

Lemma hmultA : associative hmult.
Proof. 
  move => a b c.
   by rewrite -(g2h_h2g a) -(g2h_h2g b) -(g2h_h2g c) -!g2h_mult_rw mulA. 
Qed.
(* end snippet multA *)




(* begin snippet nfRef:: no-out *)

Lemma nf_ref (a: hT1)  : hnfb a = T1nf (h2g a).
(* end snippet nfRef *)
Proof.
  elim: a => //.
  - move => a IHa n b IHb; rewrite T1.nf_b_cons_eq; simpl T1nf. 
    rewrite IHa IHb;  change (phi0 (h2g a)) with (h2g (T1.phi0 a)).
    by rewrite andbA decide_hlt_rw.
Qed.

Lemma LT_ref : refinesRel  hLT  gLT.
Proof.
  split.   
  - destruct 1 as [H [H0 H1]]; split. 
    + by rewrite  -nf_ref.
    + by apply lt_ref. 
    + by rewrite -nf_ref. 
  -  case => H H0 H1; repeat  split. 
     +  red; by rewrite nf_ref.
     + by apply lt_ref. 
     +  red; by rewrite nf_ref.
Qed. 


Lemma LE_ref : refinesRel hLE gLE.
Proof. 
  split. 
  - case => a b.
    split. 
    rewrite -nf_ref => //.
    case: b => c _.    
    destruct c. 
    
    apply T1ltW. 
    rewrite - decide_hlt_rw => //.
    red;  rewrite bool_decide_eq_true => //.
    apply T1lenn. 
    case b => _ H.
    rewrite - nf_ref => //. 
  - case.
    rewrite /hLE. 
    red. 
    split. 
    rewrite -nf_ref in p p1 => //.
    split => //.
    rewrite T1le_eqVlt in p0. move : p0 => /orP.
    case => /eqP Heq; subst.  rewrite h2g_eq_iff in Heq; subst. 
    right. 
    left. 
    rewrite -decide_hlt_rw in Heq => //.
    move: Heq => /eqP H. rewrite bool_decide_eq_true in H => //.
    rewrite -nf_ref in p1 => //.
Qed.


(** Limits, successors, etc *)

(* begin snippet limitbRef:: no-out *)
Lemma limitb_ref (a:T1.T1) : hlimitb a = T1limit (h2g a).
(* ... *)
(* end snippet limitbRef *)
Proof.
  elim: a => /= //.
  move => alpha IHalpha n beta IHbeta; cbn; rewrite IHbeta. 
  move: IHalpha; case:alpha.
  by [].
  move => alpha n0 beta0 IH;  cbn.
  move: IHbeta; case: beta => //.
Qed.


Lemma is_succ_ref (a:T1.T1) : his_succ a = T1is_succ (h2g a).
Proof. 
  elim: a => /= //.
  move => alpha IHalpha n beta IHbeta; cbn; rewrite IHbeta.
  move: IHalpha; case:alpha => /= //. 
Qed.


(* rewriting lemmas *)

(* begin snippet rewritingRules:: no-out *) 
Lemma hnf_g2h alpha : hnf (g2h alpha) = T1nf alpha.
Proof.  by rewrite /hnf (nf_ref (g2h alpha)) h2g_g2h. Qed. 

Lemma g2h_succ (alpha : T1) : g2h (T1succ alpha) = hsucc (g2h alpha).
Proof.   by rewrite -(h2g_g2h alpha) succ_ref !g2h_h2g. Qed.

Lemma hlt_iff a b: hlt a b <-> h2g a < h2g b.
Proof. 
  specialize (lt_ref a b) => H;  rewrite H => //.
Qed.

Lemma T1lt_iff alpha beta: T1nf alpha -> T1nf beta ->
                          alpha < beta <->  g2h alpha t1<  g2h beta.
(* ... *)
(* end snippet rewritingRules *)
Proof.
  move => Halpha Hbeta; split. 
  - rewrite -(h2g_g2h alpha) -(h2g_g2h beta);  repeat split. 
    1, 3:  by rewrite g2h_h2g hnf_g2h. 
    + by rewrite !h2g_g2h hlt_iff.
    -  destruct 1 as [H0 [H1 H2]].
     apply lt_ref in H1; move: H1; by rewrite !h2g_g2h.
Qed.


(* begin snippet T1leIff:: no-out *)
Lemma T1le_iff (alpha beta: T1):
  alpha <= beta <->  hle (g2h alpha) (g2h beta).
(* end snippet T1leIff *)
Proof.
  split. 
  -  rewrite T1le_eqVlt => /orP; case.
     move =>  /eqP Heq; subst; right.
     move => Hlt; left; by rewrite hlt_iff !h2g_g2h.  
  -   rewrite le_ref; by rewrite !h2g_g2h.  
Qed.

(** *  Well formed ordinals as a structure *)

(* begin snippet E0Def:: no-out *)
Structure E0 := mkE0 { cnf :> T1 ; _ : T1nf cnf == true}.

#[global] Notation hE0 := E0.E0.
#[global] Notation hcnf := E0.cnf.

Definition E0_lt (alpha beta: E0) := cnf alpha < cnf beta.

Definition E0_eqb (alpha beta: E0):= cnf alpha == cnf beta.
(* end snippet E0Def *)

Definition E0zero: E0. refine (@mkE0 zero _) => //. Defined.

Definition E0succ (alpha: E0): E0.
  refine (@mkE0 (T1succ alpha) _).  rewrite nf_succ => //.
  destruct alpha. cbn. move: i => /eqP //.
Defined.

Fixpoint E0Fin (n:nat) : E0 :=
  match n with
    0 => E0zero
  | p .+1 => E0succ (E0Fin p)
  end.

Definition E0omega: E0.
Proof. refine (@mkE0 T1omega _) => //. Defined.


Lemma E0eq_intro alpha beta : cnf alpha = cnf beta -> alpha = beta. 
Proof.
  destruct alpha, beta; cbn. 
  move => H; subst; f_equal; apply eq_proofs_unicity_on. 
  case ; [left | right] => //.
     move :i =>  H. rewrite H => //.
Qed.

(* begin snippet gE0h2gG2h:: no-out *)
Definition E0_h2g (a: hE0): E0.
  esplit with (h2g (E0.cnf a)).
  rewrite -nf_ref; case: a => /= cnf cnf_ok;  by rewrite cnf_ok.
Defined.


Definition E0_g2h (a: E0): hE0.
  refine (@E0.mkord (g2h a) _); red.
  case: a  => /= cnf0 /eqP; by rewrite nf_ref h2g_g2h.  
Defined.
(* end snippet gE0h2gG2h *)

Lemma E0_h2g_nf (a:hE0) : T1nf (E0_h2g a).
Proof.
  case: a => /= cnf Hnf; by rewrite -nf_ref. 
Qed.



Require Import Logic.Eqdep_dec.

Lemma gE0_eq1 alpha beta : E0_eqb alpha beta -> alpha = beta.
Proof.
  case: alpha ; case: beta => x Hx y Hy /=; rewrite /E0_eqb => /= /eqP .
  move => Heq; subst.   
  have  H0: Hx = Hy; last first.
  -   by rewrite H0.   
  - apply eq_proofs_unicity_on; case; case (T1nf x); auto.
Qed. 

Lemma gE0_eq_iff alpha beta : E0_eqb alpha beta <-> alpha = beta.
Proof. 
  split.
  - apply gE0_eq1 => Heq.
  - move => ?  ; subst; rewrite /E0_eqb => //. 
Qed.

(* begin snippet E0EqP:: no-out *)
Lemma gE0_eqP alpha beta: reflect (alpha = beta) (E0_eqb alpha beta).
(* end snippet E0EqP *)
Proof.
  case_eq(E0_eqb alpha beta).
  - constructor;  by rewrite -gE0_eq_iff.
  - constructor => H0; subst.
    move : H => // /=; cbn; by rewrite T1eq_refl.
Qed.


From Coq Require Import Relations Basics
     Wellfounded.Inverse_Image Wellfounded.Inclusion.

(** TODO: simplify this proof !!! *)

(* begin snippet gE0LtWf:: no-out *)
Lemma gE0_lt_wf : well_founded E0_lt.
Proof.
  move => x; apply Acc_incl
            with (fun x y =>  E0.Lt (E0_g2h x) (E0_g2h y)).
  (* ... *)
  (* end snippet gE0LtWf *)
  - move => a b ; rewrite /E0_lt => Hab. 
    case: a Hab => cnf0 i0 Hb.
    case: b Hb => cnf1 i1 /= Hlt ; rewrite /E0.Lt => /=. 
    rewrite -(h2g_g2h cnf0) in Hlt i0;
      rewrite -(h2g_g2h cnf1) in Hlt i1;
      rewrite -decide_hlt_rw in Hlt;
      repeat split. 
    + rewrite -!nf_ref in i0 i1;  move: i0 => /eqP //.
    + red in Hlt; rewrite bool_decide_eq_true in Hlt => //.
    + rewrite /bool_decide -!nf_ref in  i1;  move: i1 => /eqP //.
  -  apply Acc_inverse_image, E0.Lt_wf. 
Qed. 



Declare Scope BrGaia_scope. (* Gaia to Bridge *)

Delimit Scope BrGaia_scope with brg.

Infix "*" := T1mul : BrGaia_scope.


Lemma L1' (a: T1) : (T1omega * (a * T1omega) = T1omega * a * T1omega)%brg.
Proof. by  rewrite mulA. Qed. 

(** Sequences and limits *)

Definition g2h_seq (s: nat-> T1) n := g2h (s n).
Definition h2g_seq (s: nat -> hT1) n := h2g (s n).


Definition gstrict_lub (s : nat -> T1) (lambda : T1) :=
  (forall i : nat, gLT (s i) lambda) /\
    (forall alpha : T1, (forall i : nat, gLE (s i) alpha) -> gLE lambda  alpha).


Lemma strict_lub_ref (s:nat-> hT1) (lambda: hT1) :
  strict_lub s lambda <-> gstrict_lub (h2g_seq s) (h2g lambda).
Proof. 
  rewrite /gstrict_lub; split. 
  -  case => Ha Hb;  split. 
     + move => i; rewrite -!LT_ref => //.
     + move => alpha Halpha; rewrite -(h2g_g2h alpha) -LE_ref.
       apply Hb => i; destruct (Halpha i) as [H H0 H1]; split. 
       * rewrite -hnf_g2h /h2g_seq g2h_h2g in H => //.
       * split. 
         --  rewrite T1le_iff /h2g_seq g2h_h2g in H0 => //.
         --  by rewrite hnf_g2h.
  -   destruct 1 as [H H0]; split. 
      + move => i; specialize  (H i); rewrite LT_ref =>//.
      +  move => alpha Halpha; rewrite LE_ref;  apply H0. 
         move => i; rewrite -LE_ref; apply Halpha. 
Qed.


  
