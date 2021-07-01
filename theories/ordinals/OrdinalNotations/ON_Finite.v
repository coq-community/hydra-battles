(**  A notation system for finite ordinals *)
(** Pierre Castéran, Unviv. Bordeaux and LaBRI *)



From Coq Require Import Arith Relations Lia Logic.Eqdep_dec Ensembles
        Wellfounded.Inverse_Image Wellfounded.Inclusion
        RelationClasses.
From hydras Require Import ON_Generic.

Require Wf_nat.

Coercion is_true: bool >-> Sortclass.

(** The type of ordinals less than [n] *)

Definition t (n:nat) := {i:nat | Nat.ltb i  n}.

Definition lt {n:nat} : relation (t n) :=
  fun alpha beta => Nat.ltb (proj1_sig alpha) (proj1_sig beta).


Lemma t0_empty (alpha: t 0): False.
Proof.
  destruct alpha as [x H].
  destruct x; cbn in H; discriminate.
Qed.


Definition compare {n:nat} (alpha beta : t n) :=
  Nat.compare (proj1_sig alpha) (proj1_sig beta).

Lemma compare_correct {n} (alpha beta : t n) :
  CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
              (compare alpha beta).
Proof.
  destruct n. 
  - elimtype False;  now apply t0_empty.
  - destruct alpha, beta; cbn;  case_eq (x ?= x0); unfold lt; cbn.
    + rewrite Nat.compare_eq_iff; intro; subst; f_equal. 
      constructor 1. f_equal.  apply eq_proofs_unicity_on.
      destruct y, (x0 <? S n); auto; right; discriminate.    
    +  rewrite Nat.compare_lt_iff;  constructor 2.
       destruct x0; [  lia |  apply leb_correct; lia].
    +   rewrite Nat.compare_gt_iff; constructor 3.
        destruct x; [lia | apply leb_correct; lia].
Qed.

Lemma compare_reflect {n:nat} (alpha beta : t  n) :
  match (compare alpha beta)
  with
    Lt => lt alpha  beta
  | Eq => alpha = beta
  | Gt => lt beta  alpha
  end.
Proof.
 now destruct (compare_correct alpha beta).
Qed.


Lemma lt_wf (n:nat) : well_founded (@lt n).
Proof.
  intro x; apply Acc_incl with (fun alpha beta =>
                                  proj1_sig alpha < proj1_sig beta)%nat.
 - intros  [y Hy] [z Hz]; unfold lt; cbn; intro H.
   destruct z.
   + discriminate.
   +  apply leb_complete in H; lia.
  -  apply Acc_inverse_image, Wf_nat.lt_wf.
Qed.

Global Instance sto n : StrictOrder (@lt n).
Proof.
  split.
   - intro x; red;  unfold lt; destruct x; cbn.
     destruct x.
     + discriminate.
     +  destruct (Nat.leb_spec0 (S x) x).
      *  lia.
      *  discriminate.
  - intros x y z; destruct x,y,z; cbn; destruct n.
    +   cbn; red in i1.
        assert (x1 < 0)%nat by (now rewrite <- Nat.ltb_lt); lia.
    +   unfold lt; simpl; unfold is_true; repeat rewrite Nat.ltb_lt;  lia.
Qed.

(** We have now an ordinal notation *)

Global Instance comp n: Comparable (@lt n)  compare.
Proof.
  split.
   - apply sto.
   - apply compare_correct. 
Qed.

Global Instance FinOrd n : ON (@lt n)  compare. 
Proof.
  split.
  - exact (comp n).
  - apply lt_wf.
Qed.

Definition Zero_limit_succ_dec (n:nat) : ZeroLimitSucc_dec (on := FinOrd n).
Proof.
  - intros [i Hi]; destruct n.
    + discriminate.
    + destruct i.
      * left;left;red; destruct y; destruct x.
       --  replace Hi with i.
        ++ right. 
        ++ apply eq_proofs_unicity_on; 
             destruct y, (0 <? S n); auto; right; discriminate.    
       -- left; red; cbn; trivial.
      * right; refine (exist _ (exist _ i _) _).
        split.
        -- cbn; unfold lt; cbn;  apply Nat.leb_refl.
        -- intros z H H0; destruct z.
           unfold lt in H, H0; cbn in H, H0.
           destruct x.
           ++ discriminate.
           ++ red in H, H0; apply leb_complete in H .
              apply leb_complete in H0; lia.
              Unshelve.
              red; red in Hi; rewrite Nat.ltb_lt in *; lia.
Defined.

Lemma sig_eq_intro {n:nat} (x y : t n) :
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x, y; simpl; f_equal; intro; subst. 
  f_equal; apply eq_proofs_unicity_on.
  destruct y, (x0 <? n); auto.
  right; discriminate.
Qed.


Section Inclusion_ij.

  Variables i j : nat.
  Hypothesis Hij : (i < j)%nat.

  Remark Ltb_ij : Nat.ltb i j.
  Proof.
    red; now rewrite Nat.ltb_lt.
  Defined.

  Program Definition iota_ij  (alpha: t i) : t j :=
    alpha.
  
  Next Obligation.
    destruct alpha; cbn; red in i0;rewrite  Nat.ltb_lt  in i0.
    destruct j; [lia | apply leb_correct;  lia].
  Defined.

  Let b : t j := exist _ i Ltb_ij.

   
  Global Instance F_incl_ij  : SubON  (FinOrd i) (FinOrd j) b iota_ij.
  Proof.
    split.
    - intros; cbn.
      reflexivity. 
    -  unfold lt; simpl. intro x;  destruct x; assumption.
    -  intro y; destruct y as [x Hx].
       unfold b, lt;simpl. 
       intros H; exists (exist _ x H); apply sig_eq_intro; reflexivity.
  Qed.

  Lemma iota_compare_commute :
    forall alpha beta, compare alpha beta = compare (iota_ij   alpha)
                                                    (iota_ij   beta).
  Proof.
    reflexivity. 
  Qed.
  
  Lemma iota_mono  : forall alpha beta,
      lt alpha beta <->
      lt (iota_ij   alpha) (iota_ij   beta).
  Proof.
    split;  unfold lt; cbn; auto.
  Qed.

End Inclusion_ij.

Arguments iota_ij {i j}.

Program Example alpha1 : t 7 := 2.

Program Example beta1 : t 7 := 5.

Example i1 : lt  alpha1 beta1.
Proof. reflexivity.  Qed.

Program Example gamma1 : t 8 := 7.

Fail Goal lt alpha1 gamma1.

Example i2 : lt (iota_ij  (le_n 8) alpha1) gamma1.
Proof. reflexivity. Qed.

Example Ex1 : In  (bigO beta1) alpha1.
Proof. reflexivity. Qed.

(* Hide before compiling the module 

Program Definition bad : t 10 := 10.
Next Obligation.
  compute.
Abort.
 **)






