Require Import Arith Relations Lia Logic.Eqdep_dec Ensembles
        Coq.Wellfounded.Inverse_Image Coq.Wellfounded.Inclusion
         Ordinal_generic RelationClasses.

Require        Wf_nat.

Coercion is_true: bool >-> Sortclass.

Definition t (n:nat) := {i:nat | Nat.ltb i  n}.

Definition lt {n:nat} : relation (t n) :=
  fun alpha beta => Nat.ltb (proj1_sig alpha) (proj1_sig beta).

Definition bigO {n:nat} (alpha : t n): Ensemble (t n) := fun beta =>  lt beta alpha.


Lemma t0_empty (alpha: t 0): False.
Proof.
  destruct alpha.
  destruct x; cbn in i; discriminate.
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

(* useful ? *)


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



Program Definition cast {i j : nat}  (H: i < j) (alpha: t i) : t j :=
  alpha.

Next Obligation.
  destruct alpha; cbn; red in i0;rewrite  Nat.ltb_lt  in i0.
  destruct j; [lia | apply leb_correct;  lia].
Defined.


Lemma cast_compare_commute (i j  :nat)(H : i < j) :
  forall alpha beta, compare alpha beta = compare (cast  H alpha)
                                                  (cast  H beta).
Proof.
  reflexivity. 
Qed.
  
Lemma cast_mono (i j  :nat)(H : i < j) : forall alpha beta,
    lt alpha beta <->
    lt (cast  H alpha) (cast  H beta).
Proof.
  split;  unfold lt; cbn; auto.
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



Global Instance FinOrd (n:nat) : OrdinalNotation (sto n) compare.
Proof.
  split.
  - apply compare_correct.
  - apply lt_wf.
Qed.


Lemma sig_eq_intro {n:nat} (x y : t n) :
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x,y; simpl; f_equal; intro; subst. 
  f_equal; apply eq_proofs_unicity_on.
  destruct y, (x0 <? n); auto.
  right; discriminate.
Qed.

(** biggest element of t (S n) *)

Program Definition biggest_S (n:nat) : t (S n) :=n.
Next Obligation. 
  red;rewrite  Nat.ltb_lt; auto with arith.
Defined.


Instance F_incl n : SubNotation  (FinOrd n) (FinOrd (S n)) (biggest_S n)
                                 (cast (Nat.lt_succ_diag_r n)).
Proof.
  split.
  - intros; cbn.
    reflexivity. 
  -  unfold lt; simpl; destruct a; assumption.
  -  destruct b as [x Hx].
     unfold biggest_S.
     unfold lt;simpl. 
     intros.
     exists (exist _ x H).
     apply sig_eq_intro.     
     reflexivity.
Qed.

(** Examples:   5 and 8 considered as members of the segma,t [0,10[ *)

Program Example alpha1 : t 7 := 2.

Program Example beta1 : t 7 := 5.

Example i1 : lt  alpha1 beta1.
Proof. reflexivity.  Qed.

Program Example gamma1 : t 8 := 7.

Fail Goal lt alpha1 gamma1.


Example i2 : lt (cast (le_n 8) alpha1) gamma1.
Proof. reflexivity. Qed.

Example Ex1 : In _ (bigO beta1) alpha1.
Proof. reflexivity. Qed.

(** Hide before compiling the module 

Program Definition bad : t 10 := 10.
Next Obligation.
  compute.
Abort.
 **)






