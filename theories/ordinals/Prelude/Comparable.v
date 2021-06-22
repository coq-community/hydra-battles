From Coq Require Import Relations RelationClasses.

Class Comparable {A:Type} 
  (lt: relation A)
  (le: relation A)
  (compare : A -> A -> comparison) :=
  {
    lt_irrefl: forall a,
      ~ lt a a;
    lt_trans: forall a b c,
      lt a b -> lt b c -> lt a c;
      (* TODO formulé la cloture transitive de `le` 
        - reflexive
        - lt inclus dans le
      *)
    le_lt_eq: forall a b,
      le a b <-> lt a b \/ a = b;
    compare_correct :forall a b,
      CompareSpec (a = b) (lt a b) (lt b a) (compare a b);
  }.

Section Comparable.

  Context {A: Type}
          {lt: relation A}
          {le: relation A}
          {eq: relation A}
          {compare : A -> A -> comparison}
         {comparable : Comparable lt le compare}.

  (* Relation Lt *)
  Definition lt_b a b :=
    match compare a b with
    | Lt => true
    | _ => false
    end.

  Lemma lt_b_iff:
    forall a b,
    lt_b a b = true <-> lt a b.
  Proof.
    unfold lt_b.
    intros *.
    pose proof (compare_correct a b) as [Heq | Hlt | Hgt];
    only 1: subst;
    split; intro.
    - congruence.
    - now apply lt_irrefl in H.
    - assumption.
    - reflexivity.
    - congruence.
    - exfalso; now apply lt_irrefl with a, lt_trans with b.
  Qed.

  Lemma compare_lt_iff :
    forall a b,
    compare a b = Lt <-> lt a b.
  Proof.
    intros *.
    pose proof (compare_correct a b) as [Heq | Hlt | Hgt];
    only 1: subst;
    split; intro.
    - congruence.
    - now apply lt_irrefl in H.
    - assumption.
    - reflexivity.
    - congruence.
    - exfalso; now apply lt_irrefl with a, lt_trans with b.
  Qed.


  (* Relation Eq *)
  Definition eq_b a b :=
    match compare a b with
    | Eq => true
    | _ => false
    end.


  Lemma eq_b_iff:
    forall a b,
    eq_b a b = true <-> a = b.
  Proof.
    intros *.
    unfold eq_b.
    pose proof (compare_correct a b) as [Heq | Hlt | Hgt];
    only 1: subst;
    split; intro.
    - reflexivity.
    - reflexivity.
    - congruence.
    - subst.
      now apply lt_irrefl in Hlt.
    - congruence.
    - subst.
      now apply lt_irrefl in Hgt.
  Qed.

  Lemma compare_eq_iff:
    forall a b,
    compare a b = Eq <-> a = b.
  Proof.
    intros *.
    unfold eq_b.
    pose proof (compare_correct a b) as [Heq | Hlt | Hgt];
    only 1: subst;
    split; intro.
    - reflexivity.
    - reflexivity.
    - congruence.
    - subst.
      now apply lt_irrefl in Hlt.
    - congruence.
    - subst.
      now apply lt_irrefl in Hgt.
  Qed.

  Lemma compare_refl:
    forall a,
    compare a a = Eq.
  Proof.
    intro.
    pose proof (compare_correct a a) as [H | H | H].
    1: reflexivity.
    all: now apply lt_irrefl in H.
  Qed.

  (* Reflation Gt *)
  Lemma compare_gt_iff :
    forall a b,
    compare a b = Gt <-> lt b a.
  Proof.
    intros *.
    pose proof (compare_correct a b) as [Heq | Hlt | Hgt];
    only 1: subst;
    split; intro.
    - congruence.
    - now apply lt_irrefl in H.
    - congruence.
    - exfalso; now apply lt_irrefl with a, lt_trans with b.
    - assumption.
    - reflexivity.
  Qed.

  (* Relation Le *)
  Definition le_b a b :=
    negb (lt_b b a).

  Lemma le_b_iff:
    forall a b,
    le_b a b = true <-> le a b.
  Proof.
    intros *.
    unfold le_b, negb, lt_b.
    pose proof (compare_correct a b) as [Heq | Hlt | Hgt];
    only 1: subst;
    split; intro.
    - apply le_lt_eq; now right.
    - now rewrite compare_refl.
    - apply le_lt_eq; now left.
    - now apply compare_gt_iff in Hlt as ->.
    - apply compare_lt_iff in Hgt.
      rewrite Hgt in H.
      congruence.
    - exfalso.
      apply le_lt_eq in H as [Hlt | Heq]. 
      * exfalso; now apply lt_irrefl with a, lt_trans with b.
      * rewrite Heq in Hgt.
        now apply lt_irrefl in Hgt.
  Qed.





  (* other important lemmas *)
  Lemma compare_correct (alpha beta : A) :
    CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
                (compare alpha beta).
  Proof.
    generalize (compare_reflect alpha beta).
    destruct (compare alpha beta); now constructor.
  Qed.

  Lemma compare_trans :
    forall comp_res a b c,
      compare a b = comp_res -> compare b c = comp_res -> compare a c = comp_res.
  Admitted.

End Comparable.

Local Ltac compare_trans H1 H2 intropattern :=
  lazymatch type of (H1, H2) with
  | ((?compare ?a ?b = ?comp_res) * (?compare ?b ?c = ?comp_res))%type =>
    assert (compare a c = comp_res) as intropattern by
          (apply compare_trans with b;
           [ exact H1 | exact H2 ])
  | ((?compare ?a ?b = ?comp_res) * (?compare ?b ?c = Eq))%type =>
    assert (compare a c = comp_res) as intropattern by
          (assert (b = c) as -> by (apply compare_eq_iff; exact H2);
           exact H1)
  | ((?compare ?a ?b = Eq) * (?compare ?b ?c = ?comp_res))%type =>
    assert (compare a c = comp_res) as intropattern by
          (assert (a = b) as -> by (apply compare_eq_iff; exact H1);
           exact H2)
  | ((?compare _ _ = _) * (?compare _ _ = _))%type => fail "Not a supported case."
  | _ => fail "Did not find hypotheses talking about compare: did you declare an instance of Comparable?"
  end.

Tactic Notation "compare" "trans" constr(H1) constr(H2) "as" simple_intropattern(intropattern) :=
  compare_trans H1 H2 intropattern.
