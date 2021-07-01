From Coq Require Import Relations RelationClasses Setoid.
Require Export MoreOrders.

Class Comparable {A:Type} 
  (lt: relation A)
  (compare : A -> A -> comparison) :=
  {
  sto :> StrictOrder lt;
  compare_correct: forall a b,
      CompareSpec (a = b) (lt a b) (lt b a) (compare a b);
  }.

Section Comparable.

  Context {A: Type}
          {lt: relation A}
          {compare : A -> A -> comparison}
          {comparable : Comparable lt compare}.
  #[local] Notation le := (leq lt) . 

  (** For compatibility (provisionnal) *)
  Definition  lt_trans := StrictOrder_Transitive.
  Definition lt_irrefl := StrictOrder_Irreflexive.
  
  (* Relation Lt *)
  Lemma lt_not_gt (a b: A):
    lt a b -> ~lt b a.
  Proof.
    intros Hlt Hgt.
    apply StrictOrder_Irreflexive with a; now transitivity b.
  Qed.

  Lemma lt_not_ge (a b: A):
    lt a b -> ~ le b a.
  Proof.
    intros Hlt Hle.
    apply le_lt_eq in Hle as [Hgt | Heq].
    - now apply lt_not_gt in Hlt.
    - subst; now apply StrictOrder_Irreflexive in Hlt.
  Qed.

  #[using="All"]
  Definition lt_b (a b: A): bool :=
    match compare a b with
    | Lt => true
    | _ => false
    end.

  Lemma lt_b_iff (a b: A):
    lt_b a b = true <-> lt a b.
  Proof.
    unfold lt_b.
    pose proof (compare_correct a b) as [Heq | H | H];
    split; intro; subst; try easy.
    - now apply StrictOrder_Irreflexive  in H.
    - now apply lt_not_gt in H.
  Qed.

  Lemma compare_lt_iff (a b: A):
    compare a b = Lt <-> lt a b.
  Proof.
    pose proof (compare_correct a b) as [Heq | H | H];
    split; intro; subst; try easy.
    - now apply StrictOrder_Irreflexive  in H.
    - now apply lt_not_gt in H.
  Qed.

  Lemma compare_lt_trans (a b c: A):
    compare a b = Lt -> compare b c = Lt -> compare a c = Lt.
  Proof.
    intros Hab Hbc.
    apply compare_lt_iff in Hab, Hbc; apply compare_lt_iff.
    now transitivity b. 
  Qed.

  Lemma compare_lt_irrefl (a: A):
    ~compare a a = Lt.
  Proof.
    intro H.
    now apply compare_lt_iff, StrictOrder_Irreflexive in H.
  Qed.

  (* Relation Eq *)
  #[using="All"]
  Definition eq_b (a b: A): bool :=
    match compare a b with
    | Eq => true
    | _ => false
    end.


  Lemma eq_b_iff (a b: A):
    eq_b a b = true <-> a = b.
  Proof.
    unfold eq_b.
    pose proof (compare_correct a b) as [Heq | H | H];
    split; intro; subst; try easy;
    now apply StrictOrder_Irreflexive in H.
  Qed.

  Lemma compare_eq_iff (a b: A):
    compare a b = Eq <-> a = b.
  Proof.
    pose proof (compare_correct a b) as [Heq | H | H];
    split; intro; subst; try easy;
    now apply StrictOrder_Irreflexive in H.
  Qed.


  Lemma compare_refl (a: A):
    compare a a = Eq.
  Proof.
    pose proof (compare_correct a a) as [H | H | H].
    1: reflexivity.
    all: now apply StrictOrder_Irreflexive in H.
  Qed.

  Lemma compare_eq_trans (a b c: A):
    compare a b = Eq -> compare b c = Eq -> compare a c = Eq.
  Proof.
    intros Hab Hbc.
    apply compare_eq_iff in Hab, Hbc; apply compare_eq_iff.
    now subst.
  Qed.


  (* Reflation Gt *)
  Lemma compare_gt_iff (a b: A):
    compare a b = Gt <-> lt b a.
  Proof.
    pose proof (compare_correct a b) as [Heq | Hlt | Hgt];
    split; intro; subst; try easy.
    - now apply StrictOrder_Irreflexive in H.
    - now apply lt_not_gt in H.
  Qed.


  Lemma compare_gt_irrefl (a: A):
    ~compare a a = Gt.
  Proof.
    intros H.
    now apply compare_gt_iff, StrictOrder_Irreflexive in H.
  Qed.

  Lemma compare_gt_trans (a b c: A):
    compare a b = Gt -> compare b c = Gt -> compare a c = Gt.
  Proof.
    intros Hab Hbc.
    apply compare_gt_iff in Hab, Hbc; apply compare_gt_iff.
    now transitivity b.
  Qed.


  Lemma compare_lt_not_gt (a b: A):
    compare a b = Lt -> ~ compare a b = Gt.
  Proof.
    intros Hlt Hgt.
    apply compare_lt_iff in Hlt.
    apply compare_gt_iff in Hgt.
    now apply lt_not_gt in Hgt.
  Qed.


  Lemma compare_gt_not_lt (a b: A):
    compare a b = Gt -> ~ compare a b = Lt.
  Proof.
    intros Hgt Hlt.
    apply compare_lt_iff in Hlt.
    apply compare_gt_iff in Hgt.
    now apply lt_not_gt in Hgt.
  Qed.

  (* Relation Le *)
  #[using="All"]
  Definition le_b (a b: A): bool :=
    negb (lt_b b a).

  Lemma le_b_iff (a b: A):
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
      * rewrite Heq in Hgt; now apply StrictOrder_Irreflexive in Hgt.
  Qed.


  Lemma le_refl (a: A):
    le  a a.
  Proof.
    apply le_lt_eq.
    now right.
  Qed.

  Lemma compare_le_iff_refl (a: A):
    le  a a <-> compare a a = Eq.
  Proof.
    split; intros H.
    - apply compare_refl.
    - apply le_refl.
  Qed.

  Lemma compare_le_iff (a b: A):
    le  a b <-> compare a b = Lt \/ compare a b = Eq.
  Proof.
    split; intro H.
    - apply le_lt_eq in H as [Hlt | Heq].
      * left; now apply compare_lt_iff.
      * right; now apply compare_eq_iff.
    - apply le_lt_eq; destruct H as [Hlt | Heq].
      * left; now apply compare_lt_iff.
      * right; now apply compare_eq_iff in Heq.
  Qed.


  Lemma compare_ge_iff (a b: A):
    le  b a <-> compare a b = Gt \/ compare a b = Eq.
  Proof.
    rewrite compare_le_iff, compare_lt_iff, compare_gt_iff, !compare_eq_iff.
    intuition.
  Qed.

  Lemma le_trans (a b c: A):
    le  a b -> le  b c -> le  a c.
  Proof.
    rewrite !le_lt_eq.
    intros [Hlt_ab | Heq_ab] [Hlt_bc | Heq_bc].
    - left; now transitivity b.
    - left; now subst.
    - left; now subst.
    - right; now subst.
  Qed.

  Lemma le_lt_trans (a b c: A):
    le a b -> lt b c -> lt a c.
  Proof.
    intros Hle_ab Hlt_bc.
    apply le_lt_eq in Hle_ab as [Heq_ab | Hlt_ab].
    - now transitivity b.
    - now subst.
  Qed.


  Lemma lt_le_trans (a b c: A):
    lt a b -> le  b c -> lt a c.
  Proof.
    rewrite le_lt_eq.
    intros Hlt_ab [Heq_bc | Hlt_bc].
    - now transitivity b.
    - now subst.
  Qed.

  Lemma lt_incl_le (a b: A):
    lt a b -> le  a b.
  Proof.
    intro H.
    apply le_lt_eq; now left.
  Qed.

  Lemma le_not_gt (a b: A):
    le  a b -> ~ lt b a.
  Proof.
    intros Hlt Hle.
    now apply lt_not_ge in Hlt.
  Qed.

  (* Max lemmas *)
  #[using="All"]
  Definition max (a b : A): A :=
  match compare a b with
  | Gt => a
  | _ => b
  end.

  Lemma max_dec (a b: A):
    max a b = a \/ max a b = b.
  Proof.
    unfold max.
    pose proof (compare_correct a b) as [Hab | Hab | Hab]; tauto.
  Qed.

  Lemma max_comm (a b: A):
    max a b = max b a.
  Proof.
    unfold max.
    pose proof (compare_correct a b) as [Hab | Hab | Hab];
    pose proof (compare_correct b a) as [Hba | Hba | Hba].
    5,9: now apply lt_not_gt in Hab.
    all: easy.
  Qed.


  Lemma max_ge_a (a b: A):
    le  b a <-> max a b = a.
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
        rewrite Hab in H; subst; rewrite compare_refl in Hab; discriminate. 
      + now apply lt_incl_le.
  Qed.

  Lemma max_ge_b (a b: A):
    le  a b <-> max a b = b.
  Proof.
    unfold max.
    rewrite le_lt_eq, <- compare_lt_iff, <- compare_eq_iff.
    split; intro H.
    - now destruct H as [-> | ->].
    - pose proof (compare_correct a b) as [Hab | Hab | Hab].
      + now right.
      + now left.
      + exfalso.
        apply compare_gt_iff in Hab.
        rewrite Hab in H.
        subst.
        now apply compare_gt_irrefl in Hab.
  Qed.


  Lemma max_refl (a: A):
    max a a = a.
  Proof.
    apply max_ge_a, le_refl.
  Qed.

  Lemma le_max_a (a b: A):
    le  a (max a b).
  Proof.
    unfold max.
    pose proof (compare_correct a b) as [Heq | Hlt | Hgt].
    1,3: subst; now apply le_refl.
    now apply lt_incl_le.
  Qed.

  Lemma le_max_b (a b: A):
    le  b (max a b).
  Proof.
    rewrite max_comm.
    apply le_max_a.
  Qed.

  Lemma max_assoc (a b c: A):
    max (max a b) c = max a (max b c).
  Proof.
    unfold max.
    pose proof (compare_correct a b) as [Hab | Hab | Hab];
    pose proof (compare_correct b c) as [Hbc | Hbc | Hbc];
    pose proof (compare_correct a c) as [Hac | Hac | Hac];
    subst; try rewrite compare_refl; try easy.
    - now apply lt_not_gt in Hbc.
    - now apply lt_not_gt in Hab.
    - exfalso.
      assert (Hca: lt a c) by (now transitivity b). 
      now apply (lt_not_gt _ _  Hac Hca).
    - now apply compare_lt_iff in Hab as ->.
    - now apply compare_lt_iff in Hab as ->.
    - now apply compare_lt_iff in Hab as ->.
    - now apply lt_not_gt in Hbc.
    - exfalso.
      assert (Hca : lt c a) by  (now transitivity b). 
       apply lt_not_gt in Hac.  now apply Hac. 
    - now apply compare_gt_iff in Hab as ->.
  Qed.


  (* Min lemmas*)
  #[using="All"]
  Definition min (a b :A): A :=
  match compare a b with
  | Lt => a
  | _ => b
  end.

  Lemma min_max_iff (a b: A):
    min a b = a <-> max a b = b.
  Proof.
    unfold min, max.
    pose proof (compare_correct a b) as [Hab | Hab | Hab]; subst; easy.
  Qed.

  Lemma min_comm (a b: A):
    min a b = min b a.
  Proof.
    unfold min.
    pose proof (compare_correct a b) as [Hab | Hab | Hab];
        pose proof (compare_correct b a) as [Hba | Hba | Hba].
        5,9: now apply lt_not_gt in Hab.
        all: easy.
  Qed.

  Lemma min_dec (a b: A):
    min a b = a \/ min a b = b.
  Proof.
    rewrite min_max_iff, min_comm, min_max_iff, max_comm.
    now apply max_dec.
  Qed.



  Lemma min_le_ad (a b: A):
    le a b <-> min a b = a.
  Proof.
    rewrite min_max_iff.
    now apply max_ge_b.
  Qed.

  Lemma min_le_b (a b: A):
    le b a <-> min a b = b.
  Proof.
    rewrite min_comm, min_max_iff.
    now apply max_ge_b.
  Qed.

  Lemma min_refl (a:A):
    min a a = a.
  Proof.
    rewrite min_max_iff.
    apply max_refl.
  Qed.

 

  Lemma le_min_a (a b: A):
    le (min a b) a.
  Proof.
    unfold min.
    pose proof (compare_correct a b) as [Heq | Hlt | Hgt]; subst.
    1,2: now apply le_refl.
    now apply lt_incl_le.
  Qed.

  Lemma le_min_bd (a b: A):
    le (min a b) b.
  Proof.
    rewrite min_comm.
    apply le_min_a.
  Qed.

  Lemma min_assoc (a b c: A):
    min (min a b) c = min a (min b c).
  Proof.
    intros *.
    unfold min.
    pose proof (compare_correct a b) as [Hab | Hab | Hab];
    pose proof (compare_correct b c) as [Hbc | Hbc | Hbc];
    pose proof (compare_correct a c) as [Hac | Hac | Hac];
    subst; try rewrite compare_refl; try easy.
    - now apply lt_not_gt in Hbc.
    - now apply lt_not_gt in Hab.
    - now apply compare_lt_iff in Hab as ->.
    - exfalso.
      apply (StrictOrder_Transitive a b) in Hbc.
      2: assumption.
      now apply lt_not_gt in Hbc.
    - now apply lt_not_gt in Hab.
    - now apply compare_gt_iff in Hab as ->.
    - now apply compare_gt_iff in Hab as ->.
    - now apply compare_gt_iff in Hab as ->.
    - exfalso.
      apply (lt_trans c b) in Hab.
      2: assumption.
      now apply lt_not_gt in Hab.
  Qed.


  (* other important lemmas *)

  Lemma compare_trans (a b c: A) (comp_res: comparison):
    compare a b = comp_res -> compare b c = comp_res -> compare a c = comp_res.
  Proof.
    destruct comp_res.
    - apply compare_eq_trans.
    - apply compare_lt_trans.
    - apply compare_gt_trans.
  Qed.

  Lemma compare_reflect (a b: A):
    match compare a b with
    | Lt => lt a b
    | Eq => a = b
    | Gt => lt b a
    end.
  Proof.
    pose proof (compare_correct a b) as [Heq | Hlt | Hgt]; assumption.
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

Ltac compare_destruct_eqn a b H :=
  destruct (_ a b) eqn: H;
  [ apply compare_eq_iff in H as <-
  | apply compare_lt_iff in H
  | apply compare_gt_iff in H
  ].

Tactic Notation "compare" "destruct" constr(a) constr(b) "as" ident(H) :=
  compare_destruct_eqn a b H.
