(** A formalization of denumerable sets. *)
(** by Florian Hatat and Stéphane Desarzens  *)


From Coq Require Import Ensembles  Arith ArithRing (* Even Div2 *)
     Wellfounded Relations  Wf_nat  Finite_sets
     Logic.Epsilon  Sets.Image Lia.

From ZornsLemma Require Import Classical_Wf CountableTypes Families.

From hydras Require Import MoreEpsilonIota PartialFun  GRelations
     Prelude.More_Arith.

Import Nat.

Set Implicit Arguments.

(** A is countable if there exists an injection from [A] to
  [Full_set nat]. *)

Section Countable.

  Section Definitions.
    Variable U : Type.
    Variable A : Ensemble U.

    (** Predicate for relations which number the elements of A.

  These relations map each element of A to at least one integer, but they
  are not required to be functional (injectivity is only needed to ensure that
  A is countable). *)

    Definition rel_numbers (R: GRelation U nat) := rel_injection A Full_set R.

    (** Predicate for relations which enumerate A. *)
    Definition rel_enumerates (R : GRelation nat U) := rel_surjection Full_set A R.

    Theorem countable_surj :
      Countable A <-> exists R, rel_enumerates R.
    Proof.
      split.
      - intros [f Hf].
        exists (fun (n : nat) (x : U) =>
             exists H : In A x,
               f (exist _ x H) = n).
        split.
        + intros n x _ [Hx0 Hx1].
          apply Hx0.
        + intros n x y _ [Hx0 Hx1] [Hy0 Hy1].
          subst. apply Hf in Hy1.
          inversion Hy1; subst; clear Hy1.
          reflexivity.
        + intros x H.
          exists (f (exist _ x H)).
          split; [constructor|].
          exists H. reflexivity.
      - intros [R HR].
        (* send each [p] to the least [n : nat] for which [R n (proj1_sig p)] *)
        assert (
            forall p : { x : U | In A x },
            exists ! x : nat,
              R x (proj1_sig p) /\
                (forall m : nat, R m (proj1_sig p) -> (x <= m)%nat))
          as Hrel.
        { destruct HR as [HR0 HR1 HR2].
          intros p.
          pose proof
            (WF_implies_MEP nat _ lt_wf_0
               (fun n : nat => R n (proj1_sig p))
            ) as Hwf.
          specialize (HR2 (proj1_sig p) (proj2_sig p))
            as [n' [_ Hn']].
          destruct Hwf as [n [Hn0 Hn1]].
          { exists n'. assumption. }
          clear n' Hn'.
          exists n. split; [split|].
          * assumption.
          * intros m Hm.
            specialize (Hn1 m Hm).
            lia.
          * intros m [Hm0 Hm1].
            specialize (Hn1 m Hm0).
            specialize (Hm1 n Hn0).
            lia.
        }
        exists (fun p : { x : U | In A x } =>
             proj1_sig
               (constructive_definite_description
                  _ (Hrel p))).
        intros p0 p1 Hp.
        pose proof
          (proj2_sig
             (constructive_definite_description
                _ (Hrel p0))) as [Hp0 _].
        pose proof
          (proj2_sig
             (constructive_definite_description
                _ (Hrel p1))) as [Hp1 _].
        rewrite Hp in Hp0.
        destruct HR as [_ HR _].
        specialize (HR _ _ _ ltac:(constructor) Hp0 Hp1).
        clear Hp Hp0 Hp1 Hrel.
        destruct p0 as [? H0], p1 as [? H1].
        simpl in HR. subst.
        destruct (proof_irrelevance _ H0 H1).
        reflexivity.
    Qed.

  End Definitions.

  Variable U : Type.

  Section Countable_seq_range.

    Definition seq_range (f : nat -> U) : Ensemble U :=
      image Full_set f.

    Lemma seq_range_countable :
      forall f, Countable (seq_range f).
    Proof.
      intros f.
      unfold seq_range.
      rewrite image_as_Im.
      apply countable_img.
      apply countable_type_ensemble.
      apply nat_countable.
    Qed.

  End Countable_seq_range.

  Section Countable_bijection.

    Variable V : Type.

    Variable A : Ensemble U.
    Variable B : Ensemble V.
    Variable g : U -> V.

    Hypothesis g_bij : fun_bijection A B g.

    Lemma countable_bij_fun :
      Countable A -> Countable B.
    Proof.
      intros H.
      apply surj_countable
        with (f := fun_restr (fun_bijection_codomain g_bij));
        auto.
      apply fun_bijection_is_ZL_bijection.
    Qed.

    Lemma countable_bij_funR :
      Countable B -> Countable A.
    Proof.
      intros H.
      apply inj_countable
        with (f := fun_restr (fun_bijection_codomain g_bij));
        auto.
      apply fun_bijection_is_ZL_bijection.
    Qed.

  End Countable_bijection.

End Countable.

Lemma countable_image : forall (U V:Type)(DA : Ensemble U)(f:U->V),
    Countable DA -> Countable (image DA f).
Proof.
  intros.
  rewrite image_as_Im.
  apply countable_img.
  assumption.
Qed.

