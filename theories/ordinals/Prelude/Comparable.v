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
         - reflexive (* I have a proof ... *)
         - lt inclus dans le
      *)

    le_lt_eq: forall a b,
      le a b <-> lt a b \/ a = b;

    compare_correct: forall a b,
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
  Lemma lt_not_gt {a b: A}:
    lt a b -> ~lt b a.
  Proof.
    intros Hlt Hgt.
    now apply lt_irrefl with a, lt_trans with b.
  Qed.

  Lemma lt_not_ge {a b: A}:
    lt a b -> ~ le b a.
  Proof.
    intros Hlt Hle.
    apply le_lt_eq in Hle as [Hgt | Heq].
    - now apply lt_not_gt in Hlt.
    - subst. now apply lt_irrefl in Hlt.
  Qed.

  Definition lt_b (a b: A): bool :=
    match compare a b with
    | Lt => true
    | _ => false
    end.

  Lemma lt_b_iff {a b: A}:
    lt_b a b = true <-> lt a b.
  Proof.
    unfold lt_b.
    pose proof (compare_correct a b) as [Heq | H | H];
    split; intro; subst; try easy.
    - now apply lt_irrefl in H.
    - now apply lt_not_gt in H.
  Qed.

  Lemma compare_lt_iff {a b: A}:
    compare a b = Lt <-> lt a b.
  Proof.
    pose proof (compare_correct a b) as [Heq | H | H];
    split; intro; subst; try easy.
    - now apply lt_irrefl in H.
    - now apply lt_not_gt in H.
  Qed.

  Lemma compare_lt_trans {a b c: A}:
    compare a b = Lt -> compare b c = Lt -> compare a c = Lt.
  Proof.
    intros Hab Hbc.
    apply compare_lt_iff in Hab, Hbc; apply compare_lt_iff.
    now apply lt_trans with b.
  Qed.

  Lemma compare_lt_irrefl {a: A}:
    ~compare a a = Lt.
  Proof.
    intro H.
    now apply compare_lt_iff, lt_irrefl in H.
  Qed.

  (* Relation Eq *)
  Definition eq_b (a b: A): bool :=
    match compare a b with
    | Eq => true
    | _ => false
    end.


  Lemma eq_b_iff {a b: A}:
    eq_b a b = true <-> a = b.
  Proof.
    unfold eq_b.
    pose proof (compare_correct a b) as [Heq | H | H];
    split; intro; subst; try easy;
    now apply lt_irrefl in H.
  Qed.

  Lemma compare_eq_iff {a b: A}:
    compare a b = Eq <-> a = b.
  Proof.
    pose proof (compare_correct a b) as [Heq | H | H];
    split; intro; subst; try easy;
    now apply lt_irrefl in H.
  Qed.


  Lemma compare_refl {a: A}:
    compare a a = Eq.
  Proof.
    pose proof (compare_correct a a) as [H | H | H].
    1: reflexivity.
    all: now apply lt_irrefl in H.
  Qed.

  Lemma compare_eq_trans {a b c: A}:
    compare a b = Eq -> compare b c = Eq -> compare a c = Eq.
  Proof.
    intros Hab Hbc.
    apply compare_eq_iff in Hab, Hbc; apply compare_eq_iff.
    now subst.
  Qed.


  (* Reflation Gt *)
  Lemma compare_gt_iff {a b: A}:
    compare a b = Gt <-> lt b a.
  Proof.
    pose proof (compare_correct a b) as [Heq | Hlt | Hgt];
    split; intro; subst; try easy.
    - now apply lt_irrefl in H.
    - now apply lt_not_gt in H.
  Qed.


  Lemma compare_gt_irrefl {a: A}:
    ~compare a a = Gt.
  Proof.
    intro H.
    now apply compare_gt_iff, lt_irrefl in H.
  Qed.

  Lemma compare_gt_trans {a b c: A}:
    compare a b = Gt -> compare b c = Gt -> compare a c = Gt.
  Proof.
    intros Hab Hbc.
    apply compare_gt_iff in Hab, Hbc; apply compare_gt_iff.
    now apply lt_trans with b.
  Qed.


  Lemma compare_lt_not_gt {a b: A}:
    compare a b = Lt -> ~ compare a b = Gt.
  Proof.
    intros Hlt Hgt.
    apply compare_lt_iff in Hlt.
    apply compare_gt_iff in Hgt.
    now apply lt_not_gt in Hgt.
  Qed.


  Lemma compare_gt_not_lt {a b: A}:
    compare a b = Gt -> ~ compare a b = Lt.
  Proof.
    intros Hgt Hlt.
    apply compare_lt_iff in Hlt.
    apply compare_gt_iff in Hgt.
    now apply lt_not_gt in Hgt.
  Qed.

  (* Relation Le *)
  Definition le_b (a b: A): bool :=
    negb (lt_b b a).

  Lemma le_b_iff {a b: A}:
    le_b a b = true <-> le a b.
  Proof.
    unfold le_b, negb, lt_b.
    pose proof (compare_correct a b) as [Heq | Hlt | Hgt];
    split; intro; subst; try easy.
    - apply le_lt_eq; now right.
    - now rewrite compare_refl.
    - apply le_lt_eq; now left.
    - now apply compare_gt_iff in Hlt as ->.
    - apply compare_lt_iff in Hgt.
      rewrite Hgt in H.
      congruence.
    - exfalso.
      apply le_lt_eq in H as [Hlt | Heq].
      * now apply lt_not_gt in Hgt.
      * rewrite Heq in Hgt; now apply lt_irrefl in Hgt.
  Qed.


  Lemma le_refl {a: A}:
    le a a.
  Proof.
    apply le_lt_eq.
    now right.
  Qed.

  Lemma compare_le_iff_refl {a: A}:
    le a a <-> compare a a = Eq.
  Proof.
    split; intro.
    - apply compare_refl.
    - apply le_refl.
  Qed.

  Lemma compare_le_iff {a b: A}:
    le a b <-> compare a b = Lt \/ compare a b = Eq.
  Proof.
    split; intro.
    - apply le_lt_eq in H as [Hlt | Heq].
      * left; now apply compare_lt_iff.
      * right; now apply compare_eq_iff.
    - apply le_lt_eq; destruct H as [Hlt | Heq].
      * left; now apply compare_lt_iff.
      * right; now apply compare_eq_iff in Heq.
  Qed.


  Lemma compare_ge_iff {a b: A}:
    le b a <-> compare a b = Gt \/ compare a b = Eq.
  Proof.
    split; intro.
    - apply le_lt_eq in H as [Hlt | Heq].
      * left; now apply compare_gt_iff.
      * right; now apply compare_eq_iff.
    - apply le_lt_eq; destruct H as [Hlt | Heq].
      * left; now apply compare_gt_iff.
      * right; now apply compare_eq_iff in Heq.
  Qed.

  Lemma le_trans {a b c: A}:
    le a b -> le b c -> le a c.
  Proof.
    intros Hab Hbc.
    apply le_lt_eq.
    apply le_lt_eq in Hab as [Hlt_ab | Heq_ab];
    apply le_lt_eq in Hbc as [Hlt_bc | Heq_bc].
    - left; now apply lt_trans with b.
    - left; now subst.
    - left; now subst.
    - right; now subst.
  Qed.

  Lemma le_lt_trans {a b c: A}:
    le a b -> lt b c -> lt a c.
  Proof.
    intros Hle_ab Hlt_bc.
    apply le_lt_eq in Hle_ab as [Heq_ab | Hlt_ab].
    - now apply lt_trans with b.
    - now subst.
  Qed.


  Lemma lt_le_trans {a b c: A}:
    lt a b -> le b c -> lt a c.
  Proof.
    intros Hlt_ab Hle_bc.
    apply le_lt_eq in Hle_bc as [Heq_bc | Hlt_bc].
    - now apply lt_trans with b.
    - now subst.
  Qed.

  Lemma lt_incl_le {a b: A}:
    lt a b -> le a b.
  Proof.
    intro.
    apply le_lt_eq. now left.
  Qed.




  (* Max lemmas *)

  Definition max (a b : A): A :=
  match compare a b with 
  | Lt => b
  | _ => a
  end.

  Lemma max_dec {a b: A} :
   max a b = a \/ max a b = b.
  Proof.
    unfold max.
    pose proof (compare_correct a b) as [Hab | Hab | Hab]; tauto.
  Qed.

  Lemma max_comm {a b: A}:
    max a b = max b a.
  Proof.
    (** FIXME Cannot pose lemma max by or `pose proof (max_dec a b) as [Ha | Hb]`. **)
    unfold max.
    pose proof (compare_correct a b) as [Hab | Hab | Hab];
        pose proof (compare_correct b a) as [Hba | Hba | Hba].
        5,9: now apply lt_not_gt in Hab.
        all: easy.
  Qed.


  Lemma max_correct_a (a b: A):
    le b a <-> max a b = a.
  Proof.
    unfold max.
    split; intro H.
    - apply compare_ge_iff in H as [Hlt | Heq].
      + now rewrite Hlt.
      + rewrite Heq. now apply compare_eq_iff in Heq.
    - pose proof (compare_correct a b) as [Hab | Hab | Hab].
      + subst. apply le_refl.
      + exfalso.
        apply compare_lt_iff in Hab.
        rewrite Hab in H.
        subst.
        now apply compare_lt_irrefl in Hab.
      + now apply lt_incl_le.
  Qed.

  Lemma max_correct_b (a b: A):
    le a b <-> max a b = b.
  Proof.
    unfold max.
    split; intro H.
    - apply compare_le_iff in H as [Hlt | Heq].
      + now rewrite Hlt.
      + rewrite Heq. now apply compare_eq_iff in Heq.
    - pose proof (compare_correct a b) as [Hab | Hab | Hab].
      + subst. apply le_refl.
      + now apply lt_incl_le.
      + exfalso.
        apply compare_gt_iff in Hab.
        rewrite Hab in H.
        subst.
        now apply compare_gt_irrefl in Hab.
  Qed.


  Lemma max_comm_arg {a b: A}:
   max a b = b <-> max b a = b.
  Proof.
    split; intro H.
    - apply max_correct_a.
      now apply max_correct_b in H.
    - apply max_correct_b.
      now apply max_correct_a in H.

  Qed.

  Lemma max_refl {a b: A}:
    max a a = a.
  Proof.
    apply max_correct_a.
    apply le_refl.
  Qed.

  Lemma le_max_a {a b: A} :
    le a (max a b).
  Proof.
    unfold max.
    pose proof (compare_correct a b) as [Heq | Hlt | Hgt].
    1,3: now apply le_refl.
    now apply lt_incl_le.
  Qed.

  Lemma le_max_b {a b: A} :
    le b (max a b).
  Proof.
    rewrite max_comm.
    apply le_max_a.
  Qed.

  Lemma max_assoc {a b c: A}: (** TODO make this lemma **)
  max (max a b) c = max a (max b c).
  Proof.
    unfold max.
    pose proof (compare_correct a b) as [Hab | Hab | Hab];
    pose proof (compare_correct b c) as [Hbc | Hbc | Hbc];
    pose proof (compare_correct a c) as [Hac | Hac | Hac];
    subst; try rewrite compare_refl; try easy.
    1, 10: now apply lt_not_gt in Hbc.
    1, 7: now apply compare_lt_iff in Hac as ->.
    4, 5: now apply compare_lt_iff in Hab as ->.
    - now apply lt_not_gt in Hac.
    - exfalso.
      apply (lt_trans a b) in Hbc.
      2: assumption.
      now apply lt_not_gt in Hbc.
    - now apply compare_lt_iff in Hbc as ->.
    - now apply compare_gt_iff in Hac as ->.
    - exfalso.
      apply (lt_trans c b) in Hab.
      2: assumption.
      now apply lt_not_gt in Hab.
    - now apply compare_gt_iff in Hab as ->.
  Qed.

  (** TODO do min lemmas **)


  (* other important lemmas *)

  Lemma compare_trans {a b c: A} {comp_res: comparison}:
    compare a b = comp_res -> compare b c = comp_res -> compare a c = comp_res.
  Proof.
    destruct comp_res.
    - apply compare_eq_trans.
    - apply compare_lt_trans.
    - apply compare_gt_trans.
  Qed.


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
