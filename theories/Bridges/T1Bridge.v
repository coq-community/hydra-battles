(** Comparison between Hydra-battle's and Gaia's [T1]  

First experiments *)
From gaia Require Import ssete9.

From Coq Require Import Arith Lia.
From hydras Require  T1.

Set Bullet Behavior "Strict Subproofs".

Coercion is_true: bool >-> Sortclass.

Fixpoint iota (alpha : T1.T1) : CantorOrdinal.T1 :=
  match alpha with
    T1.zero => zero
  | T1.ocons alpha n beta => cons (iota alpha) n (iota beta)
  end.

Fixpoint pi (alpha : CantorOrdinal.T1) : T1.T1 :=
  match alpha with
    zero => T1.zero
  | cons alpha n beta => T1.ocons (pi alpha) n (pi beta)
  end.


Lemma iota_pi alpha:  iota (pi alpha) = alpha.
Proof.
  induction alpha.
  - trivial.
  - cbn; now rewrite IHalpha1, IHalpha2. 
Qed.

Lemma pi_iota alpha:  pi (iota alpha) = alpha.
Proof.
  induction alpha.
  - trivial.
  - cbn; now rewrite IHalpha1, IHalpha2. 
Qed.

Definition refines1 (f:T1.T1 -> T1.T1)
           (f': CantorOrdinal.T1 -> CantorOrdinal.T1) :=
  forall x: T1.T1, f' (iota x) = iota (f x).

Definition refines0 (x:T1.T1)(y:CantorOrdinal.T1) :=
y = iota x.


Lemma refines1_R f f' :
  refines1 f f' ->
  forall y: CantorOrdinal.T1, f (pi y) = pi (f' y).
Proof.
  intros H y;  rewrite <- (iota_pi y) at 2; 
  now rewrite H, pi_iota.
Qed.

Lemma phi0_ref x : refines0 (T1.phi0 x)  (CantorOrdinal.phi0 (iota x)).
Proof. reflexivity. Qed.


Lemma one_ref : refines0 (T1.one) CantorOrdinal.one.
Proof. reflexivity. Qed.

Lemma omega_ref : refines0 (T1.omega) CantorOrdinal.T1omega.
Proof. reflexivity. Qed.

Lemma Finite_ref (n:nat) : refines0 (T1.fin n) (\F n).
Proof.  destruct n; reflexivity. Qed.

(* clumsy ! *)

Lemma ap_ref alpha : T1.ap alpha  <-> CantorOrdinal.T1ap (iota alpha).
Proof.
  split; intro H.
  -  now inversion_clear H.
  -  destruct alpha.
     + discriminate.
     + cbn in H; destruct (andb_prop _ _ H).
       destruct (@T1eqP (iota alpha2) zero); try discriminate.
       destruct (@ssrnat.eqnP n 0); try discriminate.
       subst;  assert (alpha2 = T1.zero) by
       (destruct alpha2; [trivial | discriminate]).
       subst; constructor.
Qed.

Lemma T1eq_refl a : T1eq a a.
Proof.
  destruct (@T1eqP a a).  
  - trivial.
  - now destruct n.
Qed.

Lemma ssrnat_eqn_refl n : ssrnat.eqn n n.
Proof.
 Search ssrnat.eqn .
 destruct (@ssrnat.eqnP n n).
 - trivial.    
 - now destruct n0.
Qed. 

(* Ugly !!! I should learn ssr ! *)

Lemma compare_ref x  :
  forall y,
    match T1.compare x y with
    | Lt => T1lt (iota x) (iota y)
    | Eq => iota x = iota y
    | Gt => T1lt (iota y) (iota x)
    end.
Proof.
  induction  x.  
  - destruct y.
    + reflexivity.
    + now cbn.
  - destruct y.
    + now cbn.
    + cbn.
      * case_eq (T1.compare x1 y1); intro H.
        -- specialize (IHx1 y1);  rewrite H in IHx1 .
           case_eq ( PeanoNat.Nat.compare n n0 ); intro H0.
           ++ assert (n = n0) by
                 (now apply Compare_dec.nat_compare_eq); subst n0.
              ** case_eq (T1.compare x2 y2); intro H1.
                 rewrite IHx1; f_equal.
                 specialize (IHx2 y2); now rewrite H1 in IHx2.
                 case (iota x1 < iota y1); [trivial|].
                 rewrite IHx1, T1eq_refl.
                 case (ssrnat.eqn (ssrnat.subn_rec (S n) n) 0); trivial.
                 rewrite ssrnat_eqn_refl.
                 specialize (IHx2 y2); now rewrite H1 in IHx2.
                 rewrite IHx1. rewrite T1ltnn, T1eq_refl. 
                 case ( ssrnat.eqn (ssrnat.subn_rec (S n) n) 0);[trivial|].
                 rewrite ssrnat_eqn_refl.
                 specialize (IHx2 y2). now rewrite H1 in IHx2.  
           ++ rewrite IHx1, T1ltnn, T1eq_refl.
              destruct (@ssrnat.eqnP (ssrnat.subn_rec (S n) n0) 0).
              ** now destruct (ssrnat.eqn (ssrnat.subn_rec (S n) n0) 0).
              ** destruct n1.
                 rewrite  <- ssrnat.subnE, <- ssrnat.minusE.
                 apply nat_compare_Lt_lt in H0; lia.
           ++ rewrite IHx1, T1ltnn, T1eq_refl; apply nat_compare_Gt_gt in H0.
              rewrite  <- ssrnat.subnE, <- ssrnat.minusE.
              destruct (@ssrnat.eqnP (S n0 - n)%nat 0). 
              ** trivial. 
              ** lia. 
        -- specialize (IHx1 y1); rewrite H in IHx1;  now rewrite IHx1.
        -- specialize (IHx1 y1); rewrite H in IHx1; now rewrite IHx1.
Qed. 




