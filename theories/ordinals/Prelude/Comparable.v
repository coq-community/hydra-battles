From Coq Require Import Relations RelationClasses.

Class Comparable {A:Type} (lt : relation A) (compare : A -> A -> comparison) :=
  { 
    compare_reflect : forall alpha beta,
      match compare alpha beta with
      | Lt => lt alpha beta
      | Eq => alpha = beta
      | Gt => lt beta alpha
      end;
    compare_refl: forall alpha, compare alpha alpha = Eq
  }.

Section Comparable.

  Context {A:Type} {lt : relation A} {compare : A -> A -> comparison}
          {comparable : Comparable lt compare}.

  (* Eq part *)
  Definition eq_b alpha beta :=
    match compare alpha beta with
    | Eq => true
    | _ => false
    end.

  Lemma eq_b_iff (alpha beta : A) :
    eq_b alpha beta = true <-> alpha = beta.
  Proof.
    split.
    - unfold eq_b.
      specialize (compare_reflect alpha beta).
      case (compare alpha beta); auto; try discriminate.
    - intro.
      subst.
      unfold eq_b.
      now rewrite compare_refl.
  Qed.

  Lemma compare_Eq_impl : forall a b, compare a b = Eq -> a = b.
  Proof.
    intros * H.
    pose proof (compare_reflect a b).
    now rewrite H in *; simpl.
  Qed.

  Lemma compare_eq_iff a b :  compare a b = Eq <-> a = b.
  Proof.
    split; intro H.
    - now apply compare_Eq_impl.
    - rewrite H.
      apply compare_refl.
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
