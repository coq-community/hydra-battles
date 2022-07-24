(** A formalization of denumerable sets. *)
(** by Florian Hatat, ENS-Lyon *)


From Coq Require Import Ensembles  Arith ArithRing (* Even Div2 *)
     Wellfounded Relations  Wf_nat  Finite_sets
     Logic.Epsilon  Sets.Image Lia.

From hydras Require Import MoreEpsilonIota PartialFun  GRelations
     Prelude.More_Arith.

Import Nat.

Set Implicit Arguments.

Arguments rel_injection {A B}.
Arguments rel_surjection {A B}.

Section Countable.

  Section Definitions.
    Variable U : Type.
    Variable A : Ensemble U.
    Let Dnat : Ensemble nat := Full_set nat.

    (** Predicate for relations which number the elements of A.

  These relations map each element of A to at least one integer, but they
  are not required to be functional (injectivity is only needed to ensure that
  A is countable). *)

   
    
    Definition rel_numbers (R: GRelation U nat) := rel_injection A Dnat R.

    (** Predicate for relations which enumerate A. *)
    Definition rel_enumerates (R : GRelation nat U) := rel_surjection Dnat A R.

     (** A is countable if there exists an injection from [A] to 
        [Full_set nat]. *)
    
    Definition countable : Prop := exists R, rel_numbers R.

    Section Equivalence_with_surjection.

      Theorem countable_surj :
        countable <-> exists R, rel_enumerates R.
      Proof.
        split.
        - intros   (R, R_enum).
          exists (rel_inv A Dnat R).
          red; apply R_inv_surj; trivial.
        - destruct 1 as [R R_surj].
        exists (rel_inv Dnat A R); red;  apply R_inv_inj; trivial.
      Qed.
    End Equivalence_with_surjection.

  End Definitions.

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
        - red in RE_enum; destruct RE_enum as (Hdomain, _, _).
          destruct (Hdomain x).
          + assumption.
          + exists (double x0); apply from_E; assumption.
         - destruct RF_enum as (Hdomain, _ , _);  destruct (Hdomain x).
           + assumption.
           + exists (S (double x0)); apply from_F; assumption.
      Qed.

      Lemma R_union_codomain :
        rel_codomain (Union U E F) (Full_set nat) R_union.
      Proof.
        split.
      Qed.

      Remark R_union_double:
        forall (x : U) (n : nat), R_union x (double n) -> RE x n.
      Proof.
        intros x n R_x_2n; inversion R_x_2n.
        - replace n with n0; trivial.
          apply double_inj; assumption.
        - destruct (not_double_is_s_double _ _ H).
      Qed.

      Remark R_union_S_double :
        forall (x : U) (n : nat), R_union x (S (double n)) -> RF x n.
      Proof.
        intros x n R_x_s2n; inversion R_x_s2n.
        - symmetry in H;  case (not_double_is_s_double _ _ H).
        - replace n with n0.
         + assumption.
         + apply double_inj; assumption.
      Qed.

      Lemma R_union_inj : rel_inj (Union U E F) R_union.
      Proof.
        intros a a' b a_In_Union a'_In_Union a_R_b a'_R_b.
        inversion a_R_b as [na a_In_E a_RE_na dna_b |
                            na a_In_F a_RF_na sdna_b].
        - inversion a'_R_b as
            [na' a'_In_E a'_RE_na' dna'_b |
             na' a'_In_F a'_RF_na' sdna'_b].
          + destruct RE_enum as (_, _, RE_inj);
              apply RE_inj with na'; try assumption.
            replace na' with na; try assumption.
            apply double_inj.
            symmetry in dna'_b; transitivity b; assumption.
          + rewrite <- dna_b in sdna'_b.
            case not_double_is_s_double with na' na; assumption.
        - inversion a'_R_b as
              [na' a'_In_E a'_RE_na' dna'_b |
               na' a'_In_F a'_RF_nb sdna'_b].
          + rewrite <- sdna_b in dna'_b.
            symmetry in dna'_b.
            case not_double_is_s_double with na na'; assumption.
          + destruct RF_enum as (_, _, RF_inj).
            apply RF_inj with na'; try assumption.
            replace na' with na; try assumption.
            apply double_inj.
            symmetry in sdna'_b;  rewrite <- sdna_b in sdna'_b.
            injection sdna'_b; trivial.
      Qed.

      Lemma R_union_enumerates : rel_numbers (Union U E F) R_union.
      Proof.
        split.
        - apply R_union_domain.
        - apply R_union_codomain.
        - apply R_union_inj.
      Qed.

    End Countable_union_lemmas.

    Theorem countable_union (E : Ensemble U) (F : Ensemble U) : 
      countable E -> countable F -> countable (Union U E F).
    Proof.
      intros E_den F_den;  destruct E_den as (RE, RE_enum);
       destruct F_den as (RF, RF_enum).
      exists (R_union E F RE RF); apply R_union_enumerates; assumption.
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
        intros a a_In_F; destruct RE_enum as (RE_domain, _, _).
        apply RE_domain, F_in_E; assumption.
      Qed.

      Lemma R_inclusion_codomain : rel_codomain F (Full_set nat) RE.
      Proof.
        split.
      Qed.

      Lemma R_inclusion_inj : rel_inj F RE.
      Proof.
        intros a a' b a_In_F a'_In_F a_R_B a_'R_b;
        destruct RE_enum as (_, _, RE_inj);
        apply (RE_inj a a' b); try apply F_in_E; assumption.
      Qed.

      Lemma R_inclusion_enumerates : rel_numbers F RE.
      Proof.
        split.
        - apply R_inclusion_domain.
        - apply R_inclusion_codomain.
        - apply R_inclusion_inj.
      Qed.

    End Countable_inclusion_lemmas.

    Theorem countable_inclusion :
      countable E -> Included _ F E -> countable F.
    Proof.
      intros E_denum F_in_E; destruct E_denum as (RE, RE_enum).
      exists RE; apply R_inclusion_enumerates; assumption.
    Qed.

  End Countable_inclusion.

  (* Union of all sets B with B in A. *)
  Section Infinite_union.

    Variable A : Ensemble (Ensemble U).

    Definition Infinite_union (x : U) : Prop :=
      exists b, In A b /\ In b x.

    Section Infinite_union_lemmas.

      Variable R : Ensemble U -> nat -> Prop.
      Variable R_n : nat -> U -> nat -> Prop.

      Hypothesis R_enums : rel_numbers A R.
      Hypothesis R_n_enums :
        forall n : nat, forall b : Ensemble U,
	    In A b -> R b n -> rel_numbers b (R_n n).

      Fixpoint K (n : nat) : nat * nat :=
        match n with
          0 => (0, 0)
        | S n => match K n with
                   (0, m) => (S m, 0)
                 | (S n, m) => (n, S m)
                 end
        end.

      Definition K_1 : nat * nat -> nat :=
        fun couple =>
          let (p, q) := couple in
          div2 ((p+q+1)*(p+q)) + q.

      Let K_rel (p1 : nat*nat) (p2 : nat*nat) : Prop :=
        let (p, q) := p1 in
        let (p', q') := p2 in
        (p + q < p' + q') \/ (p + q = p' + q' /\ p' < p).

      Let f : nat * nat -> sigT (fun _ : nat => nat) :=
        fun cpl =>
          let (p, q) := cpl in
          existT (fun _ : nat => nat) (p + q) q.
      
      Let R_K :=
        (fun x y => (lexprod _ (fun _ => nat) lt (fun _ => lt)) (f x) (f y)).

      Lemma lexof_wf :
        well_founded R_K.
      Proof.
        unfold R_K;
        apply wf_inverse_image with
            (R := lexprod _ (fun _ => nat) lt (fun _ => lt)).
        apply wf_lexprod; intros; apply Wf_nat.lt_wf.  
      Qed.

      Lemma K_rel_wf :  well_founded K_rel.
      Proof.
        apply wf_incl with R_K.
        - intros (p, q) (p', q') HK_rel.
          case HK_rel.
          + intros Hin; unfold R_K; unfold f; apply left_lex; assumption.
          + intros (Hdiag, Hin).
            unfold R_K, f; rewrite Hdiag; apply right_lex.
            case (le_lt_dec q' q).
            * intros Hqin; case (lt_irrefl (p + q)).
              pattern (p + q) at 1; rewrite Hdiag.
              apply plus_lt_le_compat; assumption.
            * trivial.
        - apply lexof_wf.
      Qed.

      Remark double_K_1 :
        forall p q, double (K_1 (p, q)) = ((p+q+1)*(p+q)) + double q.
      Proof.
        intros p q; unfold K_1. (* Here *)

        rewrite double_plus.  f_equal.
        rewrite div2_of_Even; trivial. 
        apply even_prod. 
      Qed. 

      Lemma K_bij :
        forall p q, K (K_1 (p, q)) = (p, q).
      Proof.
        intros p q;  generalize (p, q);
        intros p0; pattern p0; apply (well_founded_ind K_rel_wf).
        clear p q p0; intros (p, q) IH.
        induction q.
        - induction p.
          + trivial.
          + replace (K_1 (S p, 0)) with (S (K_1 (0, p))).
            simpl K; replace (K (div2 ((p + 1) * p) + p)) with (0, p).
            trivial.
            symmetry; unfold K_1 in IH; apply (IH (0, p)).
            left; auto with arith.
            apply double_inj.
            rewrite (double_S (K_1 (0, p))).
            rewrite (double_K_1 0 p).
            rewrite (double_K_1 (S p) 0).
            rewrite <- (plus_n_O (S p)).
            rewrite (plus_O_n p).
            unfold double.
            rewrite (plus_O_n 0); rewrite <- (plus_n_O ((S p + 1) * S p)).
            replace (S p) with (p + 1).
            rewrite (plus_2 ((p + 1) * p + (p + p))).
            ring.
            lia.
        - replace (K_1 (p, S q)) with (S (K_1 (S p, q))).
          unfold K; fold K.
          replace (K (K_1 (S p, q))) with (S p, q).
          + trivial.
          + symmetry; apply IH.
            right; split; lia.
          + apply double_inj.
            rewrite (double_S (K_1 (S p, q))).
            rewrite (double_K_1 (S p) q).
            rewrite (double_K_1 p (S q)).
            rewrite (plus_2 ((S p + q + 1) * (S p + q) + double q)).
            replace (S q) with (q + 1).
            replace (S p) with (p + 1).
            unfold double.
            ring.
            lia.
            lia.
      Qed.

      Lemma K_rel_dec :
        forall x y, {K_rel x y} + {x = y} + {K_rel y x}.
      Proof.
        intros (p, q) (p', q').
        case lt_eq_lt_dec with (p + q) (p' + q').
        - intros Hcp; case Hcp.

        (* p + q < p' + q' *)
        + intros Hlt; repeat left; assumption.

        (* p + q = p' + q' *)
        + intros Heq; case lt_eq_lt_dec with p p'.
          intros Hcpp; case Hcpp.
          intros Hlt; repeat right; split; [symmetry |]; assumption.
          intros Heqp; left; right; apply injective_projections; compute.
          assumption.
          apply plus_reg_l with p'; rewrite Heqp in Heq; assumption.
          intros Hlt; left; left; right; split; assumption.

        (* p' + q' < p + q *)
        - intros Hlt; right; left; assumption.
      Qed.

      Remark K_S_O :
        forall n, K (S n) <> (0, 0).
      Proof.
        intros n Heq; simpl in Heq; symmetry in Heq.
        case_eq (K n); intros p q Kn_pq.
        rewrite Kn_pq in Heq.
        case_eq p.
        (* p = 0 *)
        - intros p_eq; rewrite p_eq in Heq.
          case O_S with q.
          replace 0 with (fst (0, 0)); replace (S q) with (fst (S q, 0));
          try (compute; trivial; fail).
          apply (f_equal (fst (A := nat) (B := nat))); assumption.

        (* p = S r *)
        - intros r p_eq; rewrite p_eq in Heq.
          case O_S with q.
          replace 0 with (snd (0, 0)); replace (S q) with (snd (r, S q));
          try (compute; trivial; fail).
          apply (f_equal (snd (A := nat) (B := nat))); assumption.
      Qed.

      Lemma K_inj :
        forall n m, K n = K m -> n = m.
      Proof.
        intros n m; pattern n, m.
        apply nat_double_ind; clear n m.
        - intros n Heq; simpl in Heq; case_eq n.
        (* n = 0 *)
          + trivial.
        (* n = S m *)
          + intros m n_Sm; rewrite n_Sm in Heq; symmetry in Heq;
              case K_S_O with m; assumption.

        - intros n Heq; simpl in Heq; case K_S_O with n; assumption.
        - intros n m Hin Heq; apply eq_S; apply Hin.
          case_eq (K n); case_eq (K m).
          intros p' q' Km p q Kn.
          simpl in Heq; rewrite Km in Heq; rewrite Kn in Heq.
          case_eq p; case_eq p'.
        (* p = 0 ; p' = 0 *)
          + intros p'_eq p_eq; rewrite p_eq in Heq; rewrite p'_eq in Heq.
            apply injective_projections; compute; auto.
            injection Heq; auto.

        (* p = 0 ; p' = S r *)
          + intros r p'_eq p_eq; rewrite p_eq in Heq; rewrite p'_eq in Heq.
            case O_S with q'.
            replace 0 with (snd (S q, 0));
              replace (S q') with (snd (r, S q'));
          try (compute; trivial; fail).
            apply (f_equal (snd (A := nat) (B := nat))); assumption.

        (* p = S r ; p' = 0 *)
          + intros p'_eq r p_eq; rewrite p_eq in Heq; rewrite p'_eq in Heq.
            case O_S with q;  symmetry;  replace 0 with (snd (S q', 0));
              replace (S q) with (snd (r, S q));
              try (compute; trivial; fail).
            apply (f_equal (snd (A := nat) (B := nat))); assumption.

        (* p = S r ; p' = S r' *)
          + intros r' p'_eq r p_eq; rewrite p_eq in Heq;
              rewrite p'_eq in Heq.
        injection Heq; auto.
      Qed.

      Definition R_union_qcq (x : U) (n : nat) :=
        match K n with
	  (p, q) => exists b, (In A b /\ R b p) /\ (In b x /\ R_n p x q)
        end.

      Lemma R_union_qcq_domain :
        rel_domain Infinite_union R_union_qcq.
      Proof.
        intros a a_In_Union; elim a_In_Union.
        intros b (b_In_A, a_In_b).
        assert (ex_p: exists p, R b p).
        { destruct R_enums as (R_domain, _, _).
          now apply R_domain.
        }
        elim ex_p; intros p b_R_p.
        
        assert (ex_q : exists q, R_n p a q).  {
          destruct (R_n_enums b_In_A b_R_p) as (R_n_domain, _, _).
          apply R_n_domain.
          assumption...
        }
        elim ex_q; intros q a_Rn_q.
        exists (K_1 (p, q)).
        red; replace (K (K_1 (p, q))) with (p, q).
        exists b.
        repeat split; assumption...
        symmetry; apply K_bij...
      Qed.

      Lemma R_union_qcq_codomain :
        rel_codomain Infinite_union (Full_set nat) R_union_qcq.
      Proof.
        split.
      Qed.

      Lemma R_union_qcq_inj :
        rel_inj Infinite_union R_union_qcq.
      Proof.
        intros a a' n a_In_Union a'_In_Union a_Ru_n a'_Ru_n.
        red in a_Ru_n; generalize a_Ru_n; case_eq (K n).
        intros p q K_eq ex_b.
        red in a'_Ru_n; generalize a'_Ru_n; case_eq (K n).
        intros p' q' K'_eq.
        assert (p_eq : p = p').
        { transitivity (fst (K n));
          [rewrite K_eq | rewrite K'_eq]; compute; trivial.
        }
        assert (q_eq : q = q'). {
          transitivity (snd (K n));
          [rewrite K_eq | rewrite K'_eq]; compute; trivial.
        }
        rewrite <- p_eq; rewrite <- q_eq.
        intro ex_b';elim ex_b;
          intros b ((b_In_A, b_R_p), (b_In_a, a_Rnp_q)).
        elim ex_b'; intros b' ((b'_In_A, b'_R_p), (b'_In_a', a'_Rnp_q)).
        assert (b_eq : b = b'). {
          destruct R_enums as (_, _, R_inj).
          apply R_inj with p; assumption.
        }
        rewrite <- b_eq in b'_In_a'.
        destruct (R_n_enums b_In_A b_R_p) as (_, _, Rn_inj).
        apply Rn_inj with q; assumption.
      Qed.

      Lemma R_union_qcq_numbers :
        rel_numbers Infinite_union R_union_qcq.
      Proof.
        split.
        - apply R_union_qcq_domain.
        - apply R_union_qcq_codomain.
        - apply R_union_qcq_inj.
      Qed.

    End Infinite_union_lemmas.

    Section Indexed_union_lemmas_2.

      Variable R : GRelation (Ensemble U) nat.
      Hypothesis R_enum : rel_numbers A R.
      Hypothesis all_b_denum : forall b : Ensemble U, In A b -> countable b.


      
      Remark inh_U_sets : inhabited (Ensemble U).
      Proof inhabits  (Empty_set U).


      Let b_n (n : nat) :=
        epsilon inh_U_sets (fun b => In A b /\ R b n).

      Remark bn_R_n :
        forall n, (exists b, In A b /\ R b n) -> R (b_n n) n.
      Proof.
        intros n ex_b; pattern (b_n n); epsilon_elim.
        intros a (_, a_R_n); assumption.
      Qed.

      Remark inh_grel_U_nat : inhabited (GRelation U nat).
      Proof inhabits  (fun (u:U)(n:nat) => True).

      Let R_b (b : Ensemble U) :=
        epsilon inh_grel_U_nat (fun R => rel_numbers b R).

      Remark Rb_numbers_b :
        forall b, In A b -> rel_numbers b (R_b b).
      Proof. 
        intros b b_In_A;
        pattern (R_b b);  epsilon_elim.
        apply all_b_denum.
        assumption.
      Qed.

      Let R_n (n : nat) (x : U) (m : nat) :=
        (exists b, R b n) /\ R_b (b_n n) x m.

      Remark Rn_numbers_bn :
        forall n : nat, In A (b_n n) -> R (b_n n) n ->
                        rel_numbers (b_n n) (R_n n).
      Proof.
        intros n bn_In_A; split.
        intros x x_In_b.
        destruct (Rb_numbers_b bn_In_A) as (Rb_dom, _, _).
        - elim (Rb_dom x); try assumption.
          intros m x_Rb_m; exists m.
          split; [exists (b_n n) | idtac]; assumption.
        - split.
        - intros x x' m x_In_bn x'_In_bn (ex_b, x_Rb_m) (_, x'_Rb_m).
          destruct (Rb_numbers_b bn_In_A) as (_, _, Rb_inj).
          apply Rb_inj with m; assumption.
      Qed.
      

      Let b_p (b : Ensemble U) :=
        epsilon (inhabits 0) (fun p => b = b_n p).

      Remark b_is_nth :
        forall b : Ensemble U, In A b -> b = b_n (b_p b).
      Proof.
        intros b b_In_A;  pattern (b_p b); epsilon_elim.
        destruct R_enum as (R_dom, _, R_inj); elim (R_dom b b_In_A).
        intros p b_R_p; exists p; pattern (b_n p); epsilon_elim.
        exists b; split; assumption.
        intros a (a_In_A, a_R_p); apply R_inj with p; assumption.
      Qed.

      Lemma all_b_relation :
        exists R_n : nat -> U -> nat -> Prop,
        forall n : nat, forall b : Ensemble U,
            In A b -> R b n -> rel_numbers b (R_n n).
      Proof.
        exists R_n; intros n b b_In_A b_R_n.
        assert (b = b_n n). {
          pattern (b_n n); epsilon_elim.
          exists b; split; assumption.
          destruct R_enum as (_, _, R_inj).
          intros a (a_In_A, a_R_p).
          apply R_inj with n; assumption.
        }
        rewrite H; rewrite H in b_In_A; rewrite H in b_R_n.
        apply Rn_numbers_bn; assumption.
      Qed.

    End Indexed_union_lemmas_2.

    Theorem countable_union_qcq :
      countable A ->
      (forall b : Ensemble U, In A b -> countable b) ->
      countable Infinite_union.
    Proof.
      intros A_denum all_b_denum; elim A_denum; intros R R_enum.
      elim all_b_relation with R; try assumption.
      intros R_n R_n_enum; exists (R_union_qcq R R_n).
      apply R_union_qcq_numbers; assumption.
    Qed.

  End Infinite_union.

  Section Countable_empty.

    Lemma countable_empty :
      countable (Empty_set U).
    Proof.
      (* Any relation would fit here... *)
      pose (R := fun (_ : U) (_ : nat) => False).
      exists R; split.
      - intros x; destruct 1.
      -  split.
      - intros x x' n x_In_empty; case x_In_empty.
    Qed.

  End Countable_empty.

  Section Countable_singleton.

    Variable x : U.

    Lemma countable_singleton :
      countable (Singleton _ x).
    Proof.
      pose (R := fun (y : U) (n : nat) => y = x).
      exists R; split.
      - intros y y_In_s; exists 0.
        inversion y_In_s.
        rewrite <- H; unfold R; reflexivity.
      - split.
      - intros y y' n y_In_s y'_In_s _ _.
        inversion y_In_s.
        inversion y'_In_s.
        subst y; auto.
    Qed.

  End Countable_singleton.

  Section Countable_seq_range.



    Definition seq_range (f : nat -> U) : Ensemble U :=
      image (Full_set nat) f.

    Lemma seq_range_countable :
      forall f, countable (seq_range f).
    Proof.
      intros f; pose (R := fun (x : U) (n : nat) => f n = x).
      exists R; split.
      - intros x; destruct 1.
        exists x0; unfold R. tauto. 
      - split.
      -  intros x x' n x_In_sr x'_In_sr x_R_n x'_R_n.
         unfold R in x_R_n.
         unfold R in x'_R_n.
         subst x; auto.
    Qed.

  End Countable_seq_range.

  Section Countable_bijection.

    Variable V : Type.

    Variable A : Ensemble U.
    Variable B : Ensemble V.
    Variable g : U -> V.

    Hypothesis g_bij : fun_bijection A B g.

    Lemma countable_bij_fun :
      countable A -> countable B.
    Proof.
      intro A_denum; red in A_denum.
      elim A_denum; intros Ru Ru_num.
      pose (Rv := fun (y : V) (n : nat) =>
                    exists x : U, In A x /\ g x = y /\ Ru x n).
      exists Rv.
      split.
      - intros y y_In_B; destruct Ru_num as (Ru_dom, _, _).
        unfold Rv; destruct g_bij as (_, g_onto, _).
        elim g_onto with y; try assumption.
        intros x (x_In_A, gx_eq_y).
        elim Ru_dom with x; try assumption.
        intros b x_Ru_b.
        exists b; exists x; repeat split; assumption.
      - split.
      - intros y y' n y_In_B y'_In_B y_Rv_n y'_Rv_n.
        unfold Rv in y_Rv_n; unfold Rv in y'_Rv_n.
        elim y_Rv_n; intros x (x_In_A, (gx_eq_y, x_Ru_n)).
        elim y'_Rv_n; intros x' (x'_In_A, (gx'_eq_y', x'_Ru_n)).
        assert (x_eq : x = x'). {
          destruct Ru_num as (_, _, Ru_inj).
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
      - intros x x_In_A; unfold Ru.
        destruct Rv_num.
        apply H.
        destruct g_bij.
        apply H2; assumption.
      - split.
      - intros x x' n x_In_A x'_In_A x_Ru_n x'_Ru_n.
        unfold Ru in x_Ru_n; unfold Ru in x'_Ru_n.
        destruct Rv_num.
        destruct g_bij; auto.
        apply H4; auto.
        apply H1 with n; auto.
    Qed.

  End Countable_bijection.

  Section Countable_finite.



    Variable A : Ensemble U.
    Hypothesis A_finite : Finite _ A.

    Theorem countable_finite : countable A.
    Proof.
      elim A_finite.
      - apply countable_empty.
      - intros A0 A0_finite A0_denum x x_nIn_A0.
        unfold Add; apply countable_union.
        assumption.
        apply countable_singleton.
    Qed.

  End Countable_finite.

End Countable.

Lemma countable_image : forall (U V:Type)(DA : Ensemble U)(f:U->V),
    countable DA -> countable (image DA f).
Proof.
  intros U V DA f H; case H; intros R HR.
  case HR; intros H0 H1 H2.
  exists (fun y n => exists x, DA x /\ R x n /\ f x = y).
  split.
  -   intros a (a0,(Ha0,H'a0)); case (H0 a0).
      auto.
      intros; exists x.
      exists a0;auto.
  - split.
  -  intros a a' b (a0,(Ha0,H'a0)) (a1,(Ha1,H'a1)) (x,(Hx,(H'x,H''x)))
         (y,(Hy,(H'y,H''y))).
     generalize (H2 x y b Hx Hy H'x H'y);auto.
     intro;subst y.
     transitivity (f x);auto.
Qed.

