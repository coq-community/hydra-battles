


(** * countable sets  (finite or infinite)  *)

(**  Florian Hatat, ENS-Lyon *)

Require Import Ensembles  Arith  ArithRing.
Require Import Even  Div2 Wellfounded Relations  Wf_nat.

Require Import PartialFun  GRelations  More_Arith (*Arith_lemmas*).
Require Import Coq.Logic.Epsilon MoreEpsilonIota.
Require Import Lia.


Require Import Coq.Sets.Image.
Require Import Finite_sets.

Set Implicit Arguments.
Arguments rel_injection [A B].
Arguments rel_surjection [A B].


Section Countable.

Section Definitions.
  Variable U : Type.
  Variable inhU : U.
  Variable A : Ensemble U.
  Let Dnat : Ensemble nat := Full_set nat.

  (** Predicate for relations which number the elements of A.

  These relations map each element of A to at least one integer, but they
  are not required to be functional (injectivity is only needed to ensure that
  A is countable). 

   *)
  
  Definition rel_numbers (R: GRelation U nat) := rel_injection A Dnat R.

  (** Predicate for relations which enumerate A. *)
  
  Definition rel_enumerates (R : GRelation nat U) := rel_surjection Dnat A R.

  (** A is countable if there exists an injection from [A] to [Full_set nat]. 
*)

  Definition countable : Prop := exists R, rel_numbers R.

      Theorem countable_surj :
      countable <-> exists R, rel_enumerates R.
    Proof.
      split.
      - destruct 1  as [R R_enum]; 
        exists (rel_inv A Dnat R);  red; now apply R_inv_surj.
      - intros [R R_surj];
        exists (rel_inv Dnat A R); red; now  apply R_inv_inj.
    Qed.

  End Definitions.

Lemma countable_image {A B : Type} (f : A -> B) (DA : Ensemble A):
  countable DA -> countable (image DA f).
Proof.
  destruct 1 as [R H].
  exists (fun y p => exists (x:A), In DA x /\ y = f x /\ R x p); split.
  - destruct H as [H H0 H1]; intros b Hb;  destruct Hb as [a [H2 H3]].
    destruct (H a H2) as [x H4]; exists x, a; repeat split; auto.
  - split.   
  - red; intros a a' b H0 H1 H2 H3.
    destruct H2 as [x [H4 [H5 H6]]]; subst.
    destruct H3 as [y [H7 [H8 H9]]]; subst.
    f_equal;  destruct H as [H H2 H3].  eapply H3 with b; eauto.
Qed.


Variable U : Type.

(** [Union _ A B] is countable if [A] and [B] are countable. *)
Section Countable_union.

  Section Countable_union_lemmas.

    Variables E F : Ensemble U.
    Variables RE RF : U -> nat -> Prop.

    Hypothesis RE_enum : rel_numbers E RE.
    Hypothesis RF_enum : rel_numbers F RF.

    Inductive R_union (x : U) : nat -> Prop :=
      from_E : forall n : nat, In E x -> RE x n -> R_union x (double n)
      | from_F : forall n : nat, In F x -> RF x n -> R_union x (S (double n)).

    Lemma R_union_domain : rel_domain (Union U E F) R_union.
    Proof.
      intros a aInUnion.
      induction aInUnion.
      red in RE_enum; destruct RE_enum as (Hdomain, _, _).
      red in Hdomain.
      destruct (Hdomain x).
      assumption.
      exists (double x0).
      apply from_E; assumption.

      red in RF_enum; destruct RF_enum as (Hdomain, _ , _).
      red in Hdomain.
      destruct (Hdomain x).
      assumption.
      exists (S (double x0)).
      apply from_F; assumption.
    Qed.

    Lemma R_union_codomain : rel_codomain (Union U E F) (Full_set nat) R_union.
    Proof.
      split.
    Qed.

    Remark R_union_double:
      forall (x : U) (n : nat), R_union x (double n) -> RE x n.
    Proof.
      intros x n R_x_2n.
      inversion R_x_2n.
      replace n with n0.
      assumption.
      apply double_inj.
      assumption.
      case (not_double_is_s_double _ _ H).
    Qed.

    Remark R_union_S_double :
      forall (x : U) (n : nat), R_union x (S (double n)) -> RF x n.
    Proof.
      intros x n R_x_s2n.
      inversion R_x_s2n.
      symmetry in H.
      case (not_double_is_s_double _ _ H).
      replace n with n0.
      assumption.
      apply double_inj.
      assumption.
    Qed.

    Lemma R_union_inj : rel_inj (Union U E F) R_union.
    Proof.
      intros a a' b a_In_Union a'_In_Union a_R_b a'_R_b.
      inversion a_R_b as [na a_In_E a_RE_na dna_b | na a_In_F a_RF_na sdna_b].
      inversion a'_R_b as [na' a'_In_E a'_RE_na' dna'_b | na' a'_In_F a'_RF_na' sdna'_b].
      destruct RE_enum as (_, _, RE_inj).
      apply RE_inj with na'; try assumption.
      replace na' with na; try assumption.
      apply double_inj.
      symmetry in dna'_b; transitivity b; assumption.
      rewrite <- dna_b in sdna'_b.
      case not_double_is_s_double with na' na; assumption.

      inversion a'_R_b as [na' a'_In_E a'_RE_na' dna'_b | na' a'_In_F a'_RF_nb sdna'_b].
      rewrite <- sdna_b in dna'_b.
      symmetry in dna'_b.
      case not_double_is_s_double with na na'; assumption.
      destruct RF_enum as (_, _, RF_inj).
      apply RF_inj with na'; try assumption.
      replace na' with na; try assumption.
      apply double_inj.
      symmetry in sdna'_b.
      rewrite <- sdna_b in sdna'_b.
      injection sdna'_b; trivial.
    Qed.

    Lemma R_union_enumerates : rel_numbers (Union U E F) R_union.
    Proof.
      split.
      apply R_union_domain.
      apply R_union_codomain.
      apply R_union_inj.
    Qed.

  End Countable_union_lemmas.

  Theorem countable_union (E : Ensemble U) (F : Ensemble U) : 
    countable E -> countable F -> countable (Union U E F).
  Proof.
    intros  E_den F_den.
    destruct E_den as (RE, RE_enum).
    destruct F_den as (RF, RF_enum).
    exists (R_union E F RE RF).
    apply R_union_enumerates; assumption.
  Qed.

End Countable_union.

Section Countable_inclusion.

  Variables E F : Ensemble U.

  Section Countable_inclusion_lemmas.

    Variable RE : U -> nat -> Prop.
    Hypothesis RE_enum : rel_numbers E RE.
    Hypothesis F_in_E : Included _ F E.

    Lemma R_inclusion_domain : rel_domain F RE.
    Proof.
      intros a a_In_F.
      destruct RE_enum as (RE_domain, _, _).
      apply RE_domain.
      apply F_in_E.
      assumption.
    Qed.

    Lemma R_inclusion_codomain : rel_codomain F (Full_set nat) RE.
    Proof.
      split.
    Qed.

    Lemma R_inclusion_inj : rel_inj F RE.
    Proof.
      intros a a' b a_In_F a'_In_F a_R_B a_'R_b.
      destruct RE_enum as (_, _, RE_inj).
      apply (RE_inj a a' b); try apply F_in_E; assumption.
    Qed.

    Lemma R_inclusion_enumerates : rel_numbers F RE.
    Proof.
      split.
      apply R_inclusion_domain.
      apply R_inclusion_codomain.
      apply R_inclusion_inj.
    Qed.
  End Countable_inclusion_lemmas.

  Theorem countable_inclusion :
    countable E -> Included _ F E -> countable F.
  Proof.
    intros E_denum F_in_E.
    destruct E_denum as (RE, RE_enum).
    exists RE.
    apply R_inclusion_enumerates; assumption.
  Qed.

End Countable_inclusion.


Section Countable_empty.

  Lemma countable_empty :
    countable (Empty_set U).
  Proof.
    (* Any relation would fit here... *)
    pose (R := fun (_ : U) (_ : nat) => False).
    exists R;  split.
    -  destruct 1.
    - split.
     - intros x x' n x_In_empty; destruct x_In_empty.
  Qed.

End Countable_empty.

Section Countable_singleton.

  Variable x : U.

  Lemma countable_singleton :
    countable (Singleton _ x).
  Proof.
    pose (R := fun (y : U) (n : nat) => y = x).
    exists R; split.
    - intros y y_In_s; exists 0; inversion y_In_s.
      rewrite <- H; unfold R; reflexivity.
    - split.
    - intros y y' n y_In_s y'_In_s _ _;
    inversion y_In_s ;inversion y'_In_s;  subst y; auto.
  Qed.

End Countable_singleton.


Definition seq_range (f : nat -> U) :=
  fun x => exists n : nat, f n = x.

Lemma seq_range_countable :
  forall f, countable (seq_range f).
Proof.
  intros f; pose (R := fun (x : U) (n : nat) => f n = x).
  exists R; split.
  - intros x Hx.   destruct Hx as [x0 Hx0]; exists x0; assumption.
  -  split.
  - intros x x' n x_In_sr x'_In_sr x_R_n x'_R_n.
  unfold R in x_R_n, x'_R_n; now subst.
Qed.


Section Countable_bijection.

  Variable V : Type.

  Variable A : Ensemble U.
  Variable B : Ensemble V.
  Variable g : U -> V.

  Hypothesis g_bij : fun_bijection A B g.

  Lemma countable_bij_fun : countable A -> countable B.
  Proof.
    intro HA; elim HA; intros Ru Ru_num.  
    pose (Rv := fun (y : V) (n : nat) =>
                  exists x : U, In A x /\ g x = y /\ Ru x n).
    exists Rv; split.
    -  intros y y_In_B;destruct Ru_num as (Ru_dom, _, _).
       unfold Rv; destruct g_bij as (_, g_onto, _).
       elim g_onto with y; try assumption.
       intros x (x_In_A, gx_eq_y).
       elim Ru_dom with x; try assumption.
       intros b x_Ru_b;
         exists b; exists x; repeat split; assumption.
    - split.
    -  intros y y' n y_In_B y'_In_B y_Rv_n y'_Rv_n.
       unfold Rv in y_Rv_n; unfold Rv in y'_Rv_n.
       elim y_Rv_n; intros x (x_In_A, (gx_eq_y, x_Ru_n)).
       elim y'_Rv_n; intros x' (x'_In_A, (gx'_eq_y', x'_Ru_n)).
       assert (x_eq : x = x').
       { destruct Ru_num as (_, _, Ru_inj).
         apply Ru_inj with n; assumption.
       }
       rewrite <- gx_eq_y; rewrite x_eq; assumption.
  Qed.

  Lemma countable_bij_funR :
    countable B -> countable A.
  Proof.
    intro B_denum; elim B_denum; intros Rv Rv_num.
    pose (Ru := fun (x : U) (n : nat) => Rv (g x) n).
    exists Ru; split.
    - intros x x_In_A; unfold Ru; destruct Rv_num.
      apply H.
      destruct g_bij.
      apply H2; assumption.
    -  split.
   - intros x x' n x_In_A x'_In_A x_Ru_n x'_Ru_n.
    unfold Ru in x_Ru_n; unfold Ru in x'_Ru_n.
    destruct Rv_num,  g_bij; auto.
    apply H4; auto; apply H1 with n; auto.
  Qed.

End Countable_bijection.

Section Countable_finite.


  Variable A : Ensemble U.
  Hypothesis A_finite : Finite _ A.

  Theorem countable_finite : countable A.
  Proof.
    elim A_finite.
    - apply countable_empty.
    - intros A0 A0_finite A0_denum x x_nIn_A0; unfold Add;
        apply countable_union.
     + assumption.
     + apply countable_singleton.
  Qed.

End Countable_finite.

End Countable.
