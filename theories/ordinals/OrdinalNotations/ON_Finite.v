(**  A notation system for finite ordinals *)
(** Pierre Castéran, Univ. Bordeaux and LaBRI *)



From Coq Require Import Arith Relations Lia Logic.Eqdep_dec Ensembles
        Wellfounded.Inverse_Image Wellfounded.Inclusion
        RelationClasses.
From hydras Require Import ON_Generic.

From Coq Require Wf_nat.




Coercion is_true: bool >-> Sortclass.

(* begin snippet Defs *)

Definition t (n:nat) := {i:nat | Nat.ltb i  n}.

Definition lt {n:nat} : relation (t n) :=
  fun alpha beta => Nat.ltb (proj1_sig alpha) (proj1_sig beta).

(* end snippet Defs *)

Open Scope ON_scope.

(* begin snippet t0Empty:: no-out *)

Lemma t0_empty (alpha: t 0): False. 
Proof. 
  destruct alpha ; discriminate. 
Qed.

(* end snippet t0Empty *)

(* begin snippet bad10  *)
Definition bad :  t 10. (* .no-out *)
exists 10. 
Abort. 
(* end snippet bad10  *)

(* begin snippet compareDef:: no-out *)

#[global] Instance compare_fin {n:nat} : Compare (t n) :=
  fun (alpha beta : t n) => Nat.compare (proj1_sig alpha) (proj1_sig beta).

Lemma compare_correct {n} (alpha beta : t n) :
  CompSpec eq lt alpha beta (compare alpha beta).
(* end snippet compareDef *)

Proof.
  destruct n. 
  - assert False by (now apply t0_empty); contradiction.
  - destruct alpha, beta; cbn;  case_eq (x ?= x0); unfold lt; cbn.
    + rewrite Nat.compare_eq_iff; intro; subst; f_equal. 
(* begin snippet compareCorrectb:: no-in unfold *)
      constructor 1.
(* end snippet compareCorrectb *)
(* begin snippet compareCorrectc *)
      f_equal.
(* end snippet compareCorrectc *)
(* begin snippet compareCorrectd *)
      apply eq_proofs_unicity_on; decide equality.
    (* ... *)
(* end snippet compareCorrectd *)
    + rewrite Nat.compare_lt_iff;  constructor 2.
      simpl; destruct x0; [  lia |  apply leb_correct; lia].
    + rewrite Nat.compare_gt_iff; constructor 3.
      simpl; destruct x; [lia | apply leb_correct; lia].
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

(* begin snippet ltWf *)

Lemma lt_wf (n:nat) : well_founded (@lt n). (* .no-out *)
(* end snippet ltWf *)

Proof.
  intro x; apply Acc_incl with (fun alpha beta =>
                                  proj1_sig alpha < proj1_sig beta)%nat.
 - intros  [y Hy] [z Hz]; unfold lt; cbn; intro H.
   destruct z.
   + discriminate.
   +  apply leb_complete in H; lia.
  -  apply Acc_inverse_image, Wf_nat.lt_wf.
Qed.

(* begin snippet ONInstance *)

#[global] Instance sto n : StrictOrder (@lt n). (* .no-out *)
(*|
.. coq:: none
|*)
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

(*||*)

#[global] Instance comp n: Comparable (@lt n) compare. (* .no-out *)
(*|
.. coq:: none
|*)
Proof.
  split.
   - apply sto.
   - apply compare_correct. 
Qed.
(*||*)

#[global] Instance FinOrd n : ON (@lt n) compare. (* .no-out *)
(*|
.. coq:: none
|*)
Proof.
  split.
  - exact (comp n).
  - apply lt_wf.
Qed.
(*||*)

(* end snippet ONInstance *)

Definition Zero_limit_succ_dec (n:nat) : ZeroLimitSucc_dec (on := FinOrd n).
Proof.
  - intros [i Hi]; destruct n.
    + discriminate.
    + destruct i.
      * left;left;red; destruct y; destruct x.
       --  replace Hi with i.
        ++ right. 
        ++ apply eq_proofs_unicity_on; decide equality.
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

(* begin snippet InclIJ:: no-out *)

Section Inclusion_ij.

  Variables i j : nat.
  Hypothesis Hij : i < j.

  Remark Ltb_ij : Nat.ltb i j. 
(* end snippet InclIJ:: no-out *)

  Proof.
    red; now rewrite Nat.ltb_lt.
  Defined.
  
  
  (* begin snippet InclIJa:: no-out *)
  #[program] Definition iota_ij  (alpha: t i) : t j :=  alpha. 
  (* end snippet InclIJa *)
  
  Next Obligation.
    destruct alpha; cbn; red in i0;rewrite  Nat.ltb_lt  in i0.
    destruct j; [lia | apply leb_correct;  lia].
  Defined.

  (* begin snippet InclIJb:: no-out *)
   Let b : t j := exist _ i Ltb_ij.

  #[global]
   Instance F_incl_ij: SubON (FinOrd i) (FinOrd j) b iota_ij. 
  (* end snippet InclIJb *)
  Proof.
    split.
    - intros; cbn.
      reflexivity. 
    -  unfold lt; simpl. intro x;  destruct x; assumption.
    -  intro y; destruct y as [x Hx].
       unfold b, lt;simpl. 
       intros H; exists (exist _ x H); apply sig_eq_intro; reflexivity.
  Qed.

  (* begin snippet InclIJc:: no-out *)
  Lemma iota_compare_commute alpha beta:
    compare alpha beta =
    compare (iota_ij alpha) (iota_ij beta). 
  (* end snippet InclIJc *)   

  Proof. reflexivity. Qed.

  (* begin snippet InclIJd:: no-out *)
  Lemma iota_mono  : forall alpha beta,
      lt alpha beta <->
      lt (iota_ij alpha) (iota_ij beta). 
 (* end snippet InclIJd *)

  Proof.
    split; unfold lt; cbn; auto.
  Qed.

  (* begin snippet InclIJz *)
End Inclusion_ij.
  (* end snippet InclIJz *)


Arguments iota_ij {i j}.

(* begin snippet Example1 *)

Program Example alpha1 : t 7 := 2.

Program Example beta1 : t 7 := 5.

Example i1 : lt  alpha1 beta1. (* .no-out *)
Proof. (* .no-out *) reflexivity.  Qed.

(* end snippet Example1 *)

(* begin snippet Example2 *)

Program Example gamma1 : t 8 := 7.

Fail Goal alpha1 o< gamma1.

(* end snippet Example2 *)

Example i2 : lt (iota_ij  (le_n 8) alpha1) gamma1.
Proof. reflexivity. Qed.

Example Ex1 : In  (bigO beta1) alpha1.
Proof. reflexivity. Qed.
