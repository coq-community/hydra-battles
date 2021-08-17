(**  * Bridge between Hydra-battle's and Gaia's [T1]  (Experimental) 
 *)






From hydras Require T1.
From mathcomp Require Import all_ssreflect zify.
From gaia Require Import ssete9.

(** Hydra-Battles' type for ordinal terms below [epsilon0] *)

#[global]Notation hT1 := T1.T1.

(** Gaia's type for ordinal terms below [epsilon0] *)

#[global]Notation gT1 := CantorOrdinal.T1. 

Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.

Fixpoint iota (alpha : hT1) : gT1 :=
  match alpha with
    T1.zero => zero
  | T1.ocons alpha n beta => cons (iota alpha) n (iota beta)
  end.

Fixpoint pi (alpha : gT1) : hT1 :=
  match alpha with
    zero => T1.zero
  | cons alpha n beta => T1.ocons (pi alpha) n (pi beta)
  end.


Lemma iota_pi alpha : iota (pi alpha) = alpha.
Proof.
elim: alpha => //=.
move => t1 IHalpha1 n t2 IHalpha2.
by rewrite IHalpha1 IHalpha2.
Qed.

Lemma pi_iota alpha:  pi (iota alpha) = alpha.
Proof.
elim: alpha => //=.
move => t1 IHalpha1 n t2 IHalpha2.
by rewrite IHalpha1 IHalpha2.
Qed.

Definition refines0 (x:hT1)(y:gT1) :=
y = iota x.

Definition refines1 (f:hT1 -> hT1)
 (f': gT1 -> gT1) :=
  forall x: hT1, f' (iota x) = iota (f x).

Definition refines2 (f:hT1 -> hT1 -> hT1)
 (f': gT1 -> gT1 -> gT1 ) :=
  forall x y : hT1, f' (iota x) (iota y) = iota (f x y).

Lemma refines1_R f f' :
  refines1 f f' ->
  forall y: gT1, f (pi y) = pi (f' y).
Proof.
move => Href y; rewrite -{2}(iota_pi y).
by rewrite Href pi_iota.
Qed.


Lemma refines2_R f f' :
  refines2 f f' ->
  forall y z: gT1, f (pi y) (pi z) = pi (f' y z).
Proof.
move => Href y z; rewrite -{2}(iota_pi y) -{2}(iota_pi z);
          by rewrite Href pi_iota.
Qed.

Lemma phi0_ref x : refines0 (T1.phi0 x)  (CantorOrdinal.phi0 (iota x)).
Proof. by []. Qed.

Lemma one_ref : refines0 (T1.one) CantorOrdinal.one.
Proof. by []. Qed.

Lemma omega_ref : refines0 T1.omega T1omega.
Proof. by []. Qed.

Lemma Finite_ref (n:nat) : refines0 (T1.fin n) (\F n).
Proof. by case: n. Qed.

Lemma ap_ref alpha : T1.ap alpha <-> T1ap (iota alpha).
Proof.
split => Hap; first by case: Hap.
move: Hap; case: alpha => //=.
move => alpha n beta /andP [Hn Hz].
move/eqP: Hn Hz =>->; move/eqP.
by case: beta.
Qed.

Lemma T1eq_refl a : T1eq a a.
Proof. by apply/T1eqP. Qed.

Lemma T1eq_rw a b: T1eq a b -> pi a = pi b.
Proof. by  move => /T1eqP ->. Qed. 

Lemma T1eq_iota_rw a b : T1eq (iota a) (iota b) -> a = b.
Proof.
  move => H; rewrite <- (pi_iota a), <- (pi_iota b); by apply T1eq_rw.
Qed.


Lemma compare_ref x :
  forall y, match T1.compare x y with
  | Lt => T1lt (iota x) (iota y)
  | Eq => iota x = iota y
  | Gt => T1lt (iota y) (iota x)
  end.

Proof.
elim: x => [|x1 IHx1 n x2 IHx2]; case => //= y1 n0 y2.
case H: (T1.compare x1 y1).
- specialize (IHx1 y1); rewrite H in IHx1.
  case H0: (PeanoNat.Nat.compare n n0).
  + have ->: (n = n0) by apply Compare_dec.nat_compare_eq.
    case H1: (T1.compare x2 y2).
    * rewrite IHx1; f_equal.
      by specialize (IHx2 y2); now rewrite H1 in IHx2.
    * case (iota x1 < iota y1); [trivial|].
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

Lemma lt_ref (a b : hT1): T1.lt a b <-> (iota a < iota b).
Proof.
  split.
  - unfold T1.lt; move => Hab; generalize (compare_ref a b); now rewrite Hab.
  - move => Hab; red.
    case_eq (T1.compare a b).
    + move => Heq; generalize (compare_ref a b); rewrite Heq.
      move => H0; move: Hab; rewrite H0;
                move => Hb; by rewrite T1ltnn in Hb.
    + by [].     
    + move => HGt; generalize (compare_ref a b); rewrite HGt.
      move =>  H1; have H2: (iota a < iota a).
      * eapply T1lt_trans; eauto.
      * by rewrite T1ltnn in H2. 
Qed.

Lemma eqref (a b : hT1):  a = b <-> (iota a = iota b).
Proof.
  split.
  - by move => ->.
  -  move => Hab ;   apply T1eq_iota_rw; by rewrite Hab T1eq_refl.
Qed.

Lemma plus_ref : refines2 T1.plus T1add.
Proof.
move => x; elim: x => [|x1 IHx1 n x2 IHx2]; case => //= y1 n0 y2.
case Hx1y1: (T1.compare x1 y1); move: (compare_ref x1 y1); rewrite Hx1y1 => H.
- by rewrite H T1ltnn /=; f_equal.
- by rewrite H /=; f_equal.
- replace (iota x1 < iota y1) with false.
    rewrite H /=; f_equal.
    change (cons (iota y1) n0 (iota y2)) with (iota (T1.ocons y1 n0 y2)).
    by rewrite IHx2.
  by apply T1lt_anti in H.
Qed.


(** Equations for multiplication (helpers for proving [mult_ref]) *)

Lemma T1mul_eqn1 (c : gT1) : c * zero = zero. 
Proof. by []. Qed.

Lemma mult_eqn1 c : T1.mult c T1.zero = T1.zero.
Proof. case: c; cbn => //; by case. 
Qed.


Lemma T1mul_eqn3 n b n' b' : cons zero n b * cons zero n' b' =
                     cons zero (n * n' + n + n') b'.      
Proof. by [].  Qed. 


Lemma mult_eqn3 n b n' b' :
  T1.mult (T1.ocons T1.zero n b) (T1.ocons T1.zero n' b') =
                     T1.ocons T1.zero (n * n' + n + n') b'.      
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
  a <> T1.zero -> T1.mult (T1.ocons a n b) (T1.ocons T1.zero n' b') =
               T1.ocons a (n * n' + n + n') b.
Proof. 
  cbn; move =>  Ha'. destruct a.
  - now destruct Ha'.
  - f_equal; nia. 
Qed.

Lemma T1mul_eqn5 a n b a' n' b' :
   a' != zero ->
  (cons a n b) * (cons a' n' b') =
  cons (a + a') n' (T1mul (cons a n b) b').
Proof. 
  move => H /=;  cbn.
   have Ha' : T1eq a' zero = false. 
   { move: a' H; case => //. }
   case (T1eq a zero); cbn; by rewrite Ha'. 
Qed.

Lemma mult_eqn5 a n b a' n' b' :
  a' <>  T1.zero ->
  T1.mult (T1.ocons a n b)  (T1.ocons a' n' b') =
  T1.ocons (T1.plus a  a') n' (T1.mult (T1.ocons a n b) b').
Proof.
  move => Ha'; cbn; destruct a. 
  - destruct a'.
    + now destruct Ha'.
    + reflexivity. 
  - destruct a'. 
    + now destruct Ha'.
    + reflexivity. 
Qed. 


Lemma iota_cons_rw a n b : iota (T1.ocons a n b)= cons (iota a) n (iota b). 
Proof. by []. Qed.

Lemma iota_zero_rw  : iota T1.zero = zero. 
Proof. by []. Qed.

(** ugky ! to simplify ! *)

Lemma mult_ref : refines2 T1.mult T1mul.
Proof.
  intros x y; revert x; induction y.
  -   move => x; simpl iota; rewrite T1mul_eqn1; case x => //.
      case => //.
  -  case.
     + simpl iota => //.
     + move => alpha n0 beta.
       destruct (T1.T1_eq_dec  alpha T1.zero).
       *  subst; destruct (T1.T1_eq_dec  y1 T1.zero).
          -- subst y1;  simpl iota; rewrite T1mul_eqn3; f_equal; nia.
          -- repeat rewrite iota_cons_rw iota_zero_rw.
             rewrite iota_cons_rw.
             rewrite T1mul_eqn5.  
             rewrite mult_eqn5.   
             simpl iota; simpl T1add; f_equal.
             destruct (T1.T1_eq_dec y2 T1.zero).
             ++  subst; by cbn. 
             ++ change (cons zero n0 (iota beta)) with
                    (iota (T1.ocons T1.zero n0 beta)); now rewrite IHy2.
             ++ assumption. 
             ++    destruct y1; [now destruct n1| now compute].
       * destruct (T1.T1_eq_dec y1 T1.zero).
         --     subst;
                  repeat rewrite iota_cons_rw iota_zero_rw.
                repeat rewrite iota_cons_rw.
                rewrite   iota_zero_rw.
                repeat rewrite iota_cons_rw iota_zero_rw.
                rewrite T1mul_eqn4.
                by rewrite mult_eqn4. 
                destruct alpha; [now destruct n1 | now compute].
         --  repeat rewrite iota_cons_rw iota_zero_rw.
             repeat rewrite iota_cons_rw iota_zero_rw.
             repeat rewrite iota_cons_rw iota_zero_rw.  
             repeat rewrite iota_cons_rw. 
             ++ rewrite T1mul_eqn5.
                ** rewrite  mult_eqn5; trivial.
                   simpl iota; rewrite plus_ref; f_equal. 
                   change (cons (iota alpha) n0 (iota beta))
                     with (iota (T1.ocons alpha n0 beta)); now rewrite IHy2.
                **  destruct y1; [now destruct n1| now compute].   
Qed.

Lemma mult_refR a b : T1.mult (pi a) (pi b) = pi (a * b).

Proof.
apply refines2_R; apply mult_ref. 
Qed. 

Lemma multA : associative T1.mult.
Proof. 
  move => a  b c;
  rewrite - (pi_iota a) -(pi_iota b) -(pi_iota c). 
  repeat rewrite mult_refR; now rewrite mulA. 
Qed.


