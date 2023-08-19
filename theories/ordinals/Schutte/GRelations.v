(** General relations  *)

(**  by  Florian Hatat, ENS-Lyon *)



From Coq Require Import Ensembles Classical  Lia Arith.
From hydras Require Import PartialFun.


Section General_Relations.

  Section Definitions.
    Variables A B : Type.

    (** domain *)

    Variable DA : Ensemble A.

    (** codomain *)

    Variable DB : Ensemble B.

    Definition GRelation := A -> B -> Prop.

    Variable R : GRelation.

    Inductive rel_injection : Prop :=
     rel_inj_i : rel_domain DA R ->
          rel_codomain DA DB R ->
          rel_inj DA R ->
          rel_injection.

    Inductive  rel_surjection : Prop :=
     rel_surj_i : rel_codomain DA DB R ->
          rel_functional DA R ->
          rel_onto DA DB R ->
          rel_surjection.
  End Definitions.

 Arguments rel_injection [A B].
 Arguments rel_surjection [A B].

  Variables A B : Type.
  Variable DA : Ensemble A.
  Variable DB : Ensemble B.

  Section injection2surjection.
    Variable R : GRelation A B.
    Hypothesis R_inj : rel_injection DA DB R.

    Lemma R_inv_surj : rel_surjection DB DA (rel_inv DA DB R).
    Proof.
    split.

    intros b a _ a_R_inv_b.
    repeat red in a_R_inv_b.
    tauto.
    intros b a a' _ b_Rf_a b_Rf_a'.
    destruct R_inj as (_, _, R_injec).
    destruct b_Rf_a as (a_In_DA, (_, a_R_b));
    destruct b_Rf_a' as (a'_In_DA, (_, a'_R_b));
    apply R_injec with b; assumption.

    intros a a_In_DB.
    destruct R_inj as (R_domain, R_codomain, _).
    elim (R_domain a a_In_DB).
    intros x a_R_x.
    exists x.
    split.
    apply R_codomain with a; assumption.
    repeat split; [idtac | apply R_codomain with a | idtac]; assumption.
    Qed.

  End injection2surjection.

  Section surjection2injection.
    Variable R : GRelation A B.
    Hypothesis R_surj : rel_surjection DA DB R.

    Definition R_inv := rel_inv DA DB R.

    Lemma R_inv_inj : rel_injection DB DA (rel_inv DA DB R).
    Proof.
    split.

    intros b b_In_DB.
    destruct R_surj as (R_codomain, _, R_surjec).
    elim (R_surjec b b_In_DB).
    intros x (x_In_DA, x_R_b).
    exists x.
    repeat split; [idtac | apply R_codomain with x | idtac]; assumption.

    intros b a b_in_DB b_R_inv_a.
    destruct b_R_inv_a as (a_In_DA, _).
    assumption.

    intros b b' a b_in_DB b'_in_DB b_Ri_a b'_Ri_a.
    destruct R_surj as (_, R_fun, _).
    red in R_fun.
    apply R_fun with a.
    destruct b_Ri_a as [a_In_DA _]; assumption.
    destruct b_Ri_a as [_ [_  a_R_b]]; assumption.
    destruct b'_Ri_a as [_ [_ a_R_b']]; assumption.
    Qed.
  End surjection2injection.

  Section elagage.
    (* Transforming a relation R to a function included in R *)
    Section to_nat_elagage.
      Variable R : GRelation A nat.

      Definition R_nat_elaguee (x : A) (n : nat) : Prop :=
        R x n /\ (forall p, R x p -> n <= p).


      Lemma R_nat_elaguee_fun :
        rel_functional DA R_nat_elaguee.
      Proof.
        intros a b b' aInDA a_Re_b a_Re_b'.
        destruct a_Re_b; destruct a_Re_b'.
        apply Nat.le_antisymm.
        now apply (H0 b').
        now apply (H2 b).
      Qed.


      Lemma R_nat_elaguee_domain :
        forall y n, R y n -> exists p, R_nat_elaguee y p.
      Proof.
        (* on pourrait faire une induction bien fondée, mais bon ... *)
        assert (forall (n : nat) (y : A), (exists q:nat, q <= n /\ R y q) ->
                 exists p : nat, R_nat_elaguee y p).
        induction n.
        intros y (q,(H1,H2)).
        exists 0.
        split; auto with arith.
        inversion H1.
        subst q; auto.
        intros y (q,(H1,H2)).
        case (classic (exists r, r <= n /\ R y r)).
        intro H';case (IHn y H').
        intros;exists x;auto.
        exists q.
        split.
        auto.
        intros.
        case (Compare_dec.le_lt_dec q p).
        auto.
        intro.
        case H.
        exists p.
        split;auto with arith.
        lia.
        intros.
        eapply H with n.
        exists n;auto with arith.
      Qed.

    End to_nat_elagage.
  End elagage.

End General_Relations.

Arguments rel_injection {A B}.
Arguments rel_surjection {A B}.
