(** *  Hessenberg sum of ordinals (commutative and strictly monotonous)

Pierre Castéran, Labri, University of  Bordeaux *)

From Coq Require Import Arith  ArithRing Lia.
From hydras Require Import Prelude.More_Arith Prelude.Merge_Sort Epsilon0.T1.


Set Implicit Arguments.


Fixpoint oplus (alpha beta : T1) : T1 :=
  let fix oplus_aux beta {struct beta} :=
      match alpha, beta with
        | zero, _ => beta
        | _, zero => alpha
        | ocons a1 n1 b1, ocons a2 n2 b2 =>
          match compare a1 a2 with
            |  Gt => ocons a1 n1 (oplus b1 beta)
            |  Lt => ocons a2 n2 (oplus_aux b2)
            |  Eq => ocons a1 (S (n1 + n2)%nat) (oplus b1 b2)
          end
      end
  in oplus_aux beta.

Infix "o+" := oplus  (at level 50, left associativity).


(*
Functional Scheme oplus_ind := Induction for oplus Sort Prop.
*)



Fixpoint o_finite_mult n alpha :=
match n with
    0 => T1.zero
  | S p =>  alpha o+ (o_finite_mult p alpha)
                 end.

Open Scope t1_scope.

Lemma oplus_alpha_0 (alpha : T1) : alpha o+ zero = alpha.
Proof.
  destruct alpha; reflexivity.
Qed.

Lemma oplus_0_beta (beta : T1): zero o+ beta = beta.
Proof.
  destruct beta; reflexivity.
Qed.

Lemma oplus_compare_Lt:
  forall a n b a' n' b', compare a  a' = Lt ->
 	                 ocons a n b o+ ocons a' n' b' =
	                 ocons a' n' (ocons a n b o+  b').
Proof.
  intros a n b a' n' b' H; cbn ;now rewrite H.
Qed.

Lemma oplus_lt_rw :
  forall a n b a' n' b', T1.lt a  a' ->
 	                 ocons a n b o+ ocons a' n' b'=
	                 ocons a' n' (ocons a n b o+ b').
Proof.
  intros a n b a' n' b' H; cbn.
  generalize (compare_rw1  H); intro Hcomp; now rewrite Hcomp.
Qed.

Lemma oplus_eq_rw :
  forall a n b  n' b', 
    ocons a n b o+ ocons a n' b'=
    ocons a (S (n+n')%nat)  (b o+ b').
Proof.
  intros a n b  n' b'; generalize (compare_refl a); intro H;
  cbn ; now rewrite H. 
Qed.


Lemma oplus_gt_rw :
  forall a n b a' n' b', T1.lt a'  a ->
 	                 ocons a n b o+ ocons a' n' b'=
	                 ocons a n  (b o+ ocons a' n' b').
Proof.
  intros a n b a' n' b' H;  cbn; 
  generalize (compare_rw3  H);  intro Hcomp; now rewrite Hcomp.
Qed.


Lemma oplus_compare_Gt :
  forall a n b a' n' b', compare a a' = Gt -> 
 	                 ocons a n b o+ ocons a' n' b' =
	                 ocons a n  (b o+ ocons a' n' b').
Proof.
  intros a n b a' n' b' H; cbn ; now rewrite H.
Qed.


(*  useless ? 
Lemma oplus_rect:
  forall P: T1 -> T1 -> T1 -> Type, 
    (forall a:T1, P T1.zero a a) ->
    (forall a: T1, P a T1.zero a) ->
    (forall a1 n1 b1 a2 n2 b2 o,
       compare a1 a2 = Gt -> 
       P b1 (ocons a2 n2 b2) o ->
       P (ocons a1 n1 b1) (ocons a2 n2 b2)
         (ocons a1 n1 o)) ->
    (forall a1 n1 b1 a2 n2 b2 o,
       compare a1 a2 = Lt ->
       P (ocons a1 n1 b1) b2 o ->
       P (ocons a1 n1 b1) (ocons a2 n2 b2) 
         (ocons a2 n2 o)) ->
    (forall a1 n1 b1 a2 n2 b2 o,
       compare a1 a2 = Eq ->
       P b1 b2 o -> 
       P (ocons a1 n1 b1) (ocons a2 n2 b2)
         (ocons a1 (S (n1 + n2)%nat) o)) ->
    forall a b, P a b (a o+ b).
Proof with auto.
  induction a.
  -  intro; simpl; destruct b;auto.
  -  induction b.
      + apply X0.
      + case_eq (compare a1 b1).
        * intro Comp; unfold oplus; rewrite Comp.
          cbn; apply X3 ...
        * intro Comp; cbn; rewrite Comp; apply X2...
        * intro Comp; cbn; rewrite Comp ...
Defined.



Ltac oplus_induction a b:= pattern (a o+ b); apply oplus_rect.
 *)


Lemma oplus_eqn :
  forall a b, 
    a o+ b =
    match a, b with
        T1.zero, _ => b
      | _, T1.zero => a
      | ocons a1 n1 b1, ocons a2 n2 b2 =>
        match compare  a1 a2 with
            Gt => ocons a1 n1 (b1 o+ b)
          | Eq => ocons a1 (S (n1 + n2)) (b1 o+ b2)
          | Lt => ocons a2 n2 (a o+ b2)
        end
    end.
Proof.
  destruct a, b; now cbn. 
Qed.



Lemma oplus_cons_cons :
  forall a n b a' n' b',
    (ocons a n b) o+ (ocons a' n' b') =
    match compare a a' with
          | Gt => ocons a n (b o+ (ocons a' n' b') )
          | Eq => ocons a (S (n + n')%nat) (b o+ b')
          | Lt => ocons a'  n' (ocons a n b o+  b')
    end.
Proof.    
  intros; now rewrite oplus_eqn.  
Qed.


Lemma lt_phi0_oplus : forall gamma alpha beta,
                        lt_phi0 alpha gamma ->
                        lt_phi0 beta gamma ->
                        lt_phi0 (alpha o+ beta) gamma.
Proof with auto.
  induction gamma; destruct alpha, beta.  
  -     simpl; constructor.
  -  inversion 2; inversion H5;   now simpl.
  -  inversion 1; T1_inversion H4.
  -  inversion 1; T1_inversion H4.
  -  simpl; auto.  
  -  simpl; auto.
  -  simpl; auto.
  -   rewrite oplus_eqn;  case_eq (compare alpha1 beta1).
      + constructor; now inversion H0.
      + right; eapply lt_phi0_inv1;eauto.
      + right; eapply lt_phi0_inv1;eauto.
Qed.

Section Proof_of_plus_nf.

  Lemma oplus_nf_0 (gamma : T1):
    nf gamma ->  forall a b,  nf a -> nf b ->
                               T1.lt a gamma ->
                               T1.lt b gamma ->
                               nf (a o+ b).
  Proof with eauto with T1.                                               
    transfinite_induction gamma.
    -  clear gamma ;intros gamma IHgamma  H; destruct a, b.
      + simpl;constructor.
      + now simpl.
      + now simpl.
      +  intros; rewrite oplus_cons_cons;
           case_eq (compare a1 b1).
         * (* a1 = b1 *)
           intro H5;  generalize (compare_Eq_impl  _ _ H5);
           intro;subst b1;clear H5; specialize (IHgamma (phi0 a1)).
           intros; apply nf_intro; [eauto with T1 |idtac| eauto with T1].
            eapply IHgamma.
            repeat split; eauto with T1. 
            apply le_lt_trans with (ocons a1 n a2); [ | exact H2].
           apply le_phi0.  
           simple apply nf_phi0; simple eapply nf_inv1; exact H1.
           eapply nf_inv2, H0.
           eapply nf_inv2, H1.
           apply lt_phi0_phi0.
           eapply lt_phi0_intro, H0. 
           apply lt_phi0_phi0.  
           eapply lt_phi0_intro, H1.
           apply lt_phi0_oplus.  
           eapply lt_phi0_intro; trivial. 
           eapply lt_phi0_intro;eauto.
         * intros; apply nf_intro.
           eapply nf_inv1, H1.
           eapply IHgamma with (phi0 b1).
           repeat split.  eapply nf_phi0, nf_inv1, H1. 
           apply le_lt_trans with (ocons b1 n0 b2) ; [| assumption].
           apply le_phi0. 
           apply nf_phi0, H.
           eapply nf_phi0, nf_inv1, H1. 
           assumption.
           eapply nf_inv2, H1.
           apply head_lt.
           unfold T1.lt, lt_b; now  rewrite H4. 
           apply  lt_phi0_phi0.
           eapply lt_phi0_intro; eauto.
           apply lt_phi0_oplus;auto.
           apply lt_phi0_phi0R.
           apply head_lt.
           unfold T1.lt, lt_b; now  rewrite H4. 
           eapply lt_phi0_intro; eauto.
         *
           intros;  apply nf_intro.
           eauto with T1. 
           eapply IHgamma with (phi0 a1).
           repeat split; eauto with T1.
           apply le_lt_trans with (ocons a1 n a2);[| exact H2].
           apply le_phi0; eauto with T1.
           eapply nf_phi0, nf_inv1, H0.
           
           eauto with T1.
           assumption.
           apply  lt_phi0_phi0.
           eapply lt_phi0_intro; eauto.
           apply head_lt.
           unfold T1.lt, lt_b;rewrite compare_rev.
           rewrite H4. 
           reflexivity. 
           apply lt_phi0_oplus;auto.
           eapply lt_phi0_intro; eauto.
           constructor 2.
           now rewrite <- gt_iff.
  Unshelve.
  exact 0.
Qed.

  Lemma oplus_nf (alpha  beta : T1) :
      nf alpha ->  nf beta -> nf (alpha o+ beta). 
  Proof with auto with T1.
    intros  H H0;
    apply oplus_nf_0 with (phi0 (max alpha beta)) ; trivial. 
    - apply nf_phi0. apply max_nf; trivial.
    -  apply lt_le_trans with (phi0 alpha).
       apply lt_a_phi0_a.
       apply phi0_mono.
       apply max_le_1;auto.
    - rewrite max_comm.
      apply lt_le_trans with (phi0 beta).
      apply lt_a_phi0_a.
      apply phi0_mono.
      apply max_le_1;auto.
  Qed.

    
End Proof_of_plus_nf.

Lemma o_finite_mult_nf : forall a n, nf a -> nf (o_finite_mult n a).
Proof.
  induction n;simpl.
  - constructor.
  - intro;apply oplus_nf; auto.
Qed.

Section Proof_of_oplus_comm.
  
  Lemma oplus_comm_0 : forall gamma,
    nf gamma ->
    forall alpha beta,  nf alpha -> nf beta ->
                        T1.lt alpha gamma ->
                        T1.lt beta gamma ->
                        alpha o+ beta = beta o+ alpha.
  Proof with eauto with T1.
    intros gamma ; transfinite_induction gamma.
    intros x H0 H; destruct alpha, beta; try reflexivity.
    rewrite oplus_eqn.
    rewrite (oplus_eqn  (ocons beta1 n0 beta2) (ocons alpha1 n alpha2)).
    repeat rewrite (compare_rev alpha1 beta1).
    case_eq (compare alpha1 beta1);  simpl CompOpp.
    -  (* alpha1 = beta1 *)
      simpl; intro.
      intros; rewrite (compare_Eq_impl _ _ H1).
      repeat rewrite (Nat.add_comm n n0).
      f_equal.
      apply H0 with   (phi0 alpha1) ; trivial. 
      
      generalize (compare_Eq_impl _ _ H1).
      intro;subst beta1.
      apply LE_LT_trans with (ocons alpha1 n0 beta2).
      now apply LE_phi0 .
      repeat split; eauto with T1.
      eapply nf_phi0, nf_inv1, H2.
      eapply nf_phi0, nf_inv2, H2.
      eapply nf_inv2, H3.
      apply  lt_phi0_phi0.
      eapply lt_phi0_intro;eauto.
      generalize (compare_Eq_impl _ _ H1).
      intro;subst beta1;  apply  lt_phi0_phi0.
      eapply lt_phi0_intro;eauto.

    - (* alpha1 < beta1 *)
      simpl CompOpp;intro.
      rewrite <- oplus_compare_Lt;auto.
      rewrite  oplus_compare_Lt;auto.
      f_equal.
      intros;  f_equal; apply H0 with (phi0 beta1) ; trivial.
      
      apply LE_LT_trans with (ocons beta1 n0 beta2).
      apply LE_phi0; auto.
      repeat split; eauto with T1.
      eapply nf_phi0, nf_inv1, H3.
      eapply nf_inv2, H3.
      apply head_lt.
      unfold T1.lt, lt_b;now  rewrite H1. 
      apply  lt_phi0_phi0.
      eapply lt_phi0_intro ;eauto.

    -    (* alpha1 > beta1  *)
      simpl CompOpp; intro;  rewrite <- oplus_compare_Gt;auto.
      rewrite  oplus_compare_Gt;auto.
      f_equal.
      intros; f_equal; apply H0 with   (phi0 alpha1) ; trivial.
      apply LE_LT_trans with (ocons alpha1 n alpha2) ; info_eauto with T1.
      now apply LE_phi0.
      repeat split; eauto with T1; apply  lt_phi0_phi0.
      eapply nf_phi0, nf_inv1, H2.
      eapply nf_inv2, H2.
      apply lt_phi0_phi0.
      eapply  lt_phi0_intro; eauto.
      apply head_lt.
      unfold T1.lt, lt_b; now rewrite compare_rev, H1.
  Qed. 

  Lemma oplus_comm : forall alpha beta, nf alpha -> nf beta ->
                                        alpha o+ beta =  beta o+ alpha.
  Proof with eauto with T1.
    intros.
    apply oplus_comm_0 with (T1.succ (max alpha beta)) ; trivial. 
    -  apply succ_nf;  apply max_nf;auto.
    -  apply le_lt_trans with  (max alpha beta) ; trivial. 
       + apply max_le_1.
       + apply lt_succ. 
    - apply le_lt_trans with  (max alpha beta) ; trivial. 
      +  rewrite max_comm; apply max_le_1. 
      +  apply lt_succ. 
  Qed.

End Proof_of_oplus_comm.

Lemma oplus_lt_rw2 : forall a n b x, nf (ocons a n b) -> nf x ->
                                     lt_phi0 x a ->
                                     ocons a n b o+  x  =
                                     ocons a n (b o+ x).
Proof.
  destruct x.
  - now (intros; repeat rewrite oplus_alpha_0).
  - intros; rewrite (oplus_eqn  (ocons a n b) (ocons x1 n0 x2)).
    apply lt_phi0_phi0 in H1.
    destruct (lt_inv H1).
    + unfold T1.lt, lt_b in H2; rewrite compare_rev. 
      destruct (compare x1 a);auto; try discriminate. 
    + decompose [or and] H2.
      *  inversion H5.
      * T1_inversion H6.
Qed.


Section Proof_of_oplus_assoc.

  Ltac ass_rw Hrec alpha a b c :=
    match goal with |- context Gamma [oplus ?a (oplus ?b  ?c)] =>
                    erewrite Hrec with alpha  a b c end.

  Ltac ass_rw_rev Hrec alpha a b c :=
    match goal with |- context Gamma [oplus (oplus ?a  ?b)  ?c] =>
                          erewrite <- Hrec with alpha  a b c end.

  Lemma oplus_assoc_0 :
    forall alpha,
      nf alpha ->
      forall a b c,  nf a -> nf b -> nf c ->
                      T1.lt a alpha ->
                      T1.lt b alpha -> T1.lt c alpha ->
                      a o+ (b o+ c) = (a o+ b) o+ c.
  Proof with eauto with T1.
    intros alpha; transfinite_induction_lt alpha.
    clear alpha ; intros alpha Hrec Halpha .
    intros; destruct a, b, c; try reflexivity. 
    - repeat rewrite oplus_0_beta; repeat rewrite oplus_alpha_0; trivial.
    - now  repeat rewrite oplus_alpha_0.
    - {
        repeat rewrite oplus_cons_cons.
        case_eq (compare b1 c1); case_eq (compare a1 b1).
        - intro H5;  generalize (compare_Eq_impl _ _ H5); intro; subst b1.
          intro H6;  generalize (compare_Eq_impl _ _ H6); intro; subst c1.
          repeat rewrite oplus_cons_cons, H6.
          ass_rw Hrec (ocons a1 n a2) a2 b2 c2; trivial. 
          f_equal.
          abstract lia.
          eapply nf_inv2, H.
          eapply nf_inv2, H0.
          eapply nf_inv2, H1.
          apply tail_lt_ocons;auto.
          apply lt_le_trans with  (phi0 a1); trivial. 
          apply lt_phi0_phi0.
          apply lt_phi0_intro with n0;auto.
          apply le_phi0;auto.
          apply lt_le_trans with  (phi0 a1).
          apply lt_phi0_phi0.
          apply lt_phi0_intro with n1;auto.
          apply le_phi0;auto.
        -  intros H5 H6; repeat rewrite oplus_cons_cons.
           rewrite H5,H6; f_equal.
           ass_rw Hrec (ocons b1 n0 b2) (ocons a1 n a2) b2 c2; trivial.
           eapply nf_inv2, H0.
           eapply nf_inv2, H1.
           apply head_lt; unfold T1.lt, lt_b; now rewrite H5.          
           apply tail_lt_ocons;auto.
           generalize (compare_Eq_impl _ _ H6); intro; subst c1.
           apply lt_le_trans with (phi0 b1).
           apply lt_phi0_phi0.
           eapply lt_phi0_intro ;eauto.
           apply le_phi0;auto.
        - 
          intros H5 H6; generalize (compare_Eq_impl _ _ H6);
          intro; subst c1.
          repeat rewrite oplus_cons_cons.
          rewrite H5.
          f_equal.
          ass_rw_rev  Hrec (ocons a1 n a2) a2 (ocons b1 n0 b2)
                      (ocons b1 n1 c2) ; trivial.
          
          f_equal.
          now rewrite oplus_cons_cons, H6.
          eapply nf_inv2, H.
          apply tail_lt_ocons;auto.
           apply head_lt.
           unfold T1.lt, lt_b;rewrite compare_rev.
           now   rewrite H5. 
           apply head_lt.
           unfold T1.lt, lt_b;rewrite compare_rev.
           now   rewrite H5. 
        -  intros H5 H6;  intros.
           generalize (compare_Eq_impl _ _ H5); intro; subst b1.
           repeat rewrite oplus_cons_cons, H6.
           f_equal.
           ass_rw  Hrec (ocons c1 n1 c2) (ocons a1 n a2)
                   (ocons a1 n0 b2) c2 ; trivial. 
           f_equal.
           now repeat rewrite oplus_cons_cons, H5.
           eapply nf_inv2, H1.
           apply head_lt;   unfold T1.lt, lt_b.
           now   rewrite H6. 
           apply head_lt;   unfold T1.lt, lt_b.
           now   rewrite H6. 
           apply tail_lt_ocons;auto.
        -  intros; assert (compare a1 c1 = Lt).
           rewrite lt_iff.
           rewrite lt_iff in H5.
           rewrite lt_iff in H6.
           apply T1.lt_trans with b1;auto.
           repeat rewrite oplus_cons_cons.
           rewrite H7, H6;    f_equal.
           ass_rw  Hrec (ocons c1 n1 c2) (ocons a1 n a2)
                   (ocons a1 n0 b2) c2 ; trivial. 
           rewrite oplus_cons_cons, H5;   f_equal.
           eapply nf_inv2, H1.
           apply head_lt;  unfold T1.lt, lt_b.
           now   rewrite H7. 
           apply head_lt; unfold T1.lt, lt_b.
           now   rewrite H6. 
           apply tail_lt_ocons;auto.
        - intros;  repeat rewrite oplus_cons_cons. 
          case_eq (compare a1 c1); intro H7.
          + f_equal.
            generalize (compare_Eq_impl _ _ H7); intro; subst c1.
            ass_rw  Hrec (ocons a1 n a2) a2 (ocons b1 n0 b2) c2 ; trivial.
            eapply nf_inv2, H.
            eapply nf_inv2, H1.
            apply tail_lt_ocons;auto.
            apply head_lt;  unfold T1.lt, lt_b.
            now   rewrite H6. 
            apply lt_le_trans with (phi0 a1).
            apply lt_phi0_phi0.
            eapply lt_phi0_intro ;eauto.
            apply le_phi0;auto.
          +  f_equal.
             ass_rw  Hrec (ocons c1 n1 c2) (ocons a1 n a2)
                     (ocons b1 n0 b2) c2 ; trivial.
             now rewrite oplus_cons_cons, H5.
             eapply nf_inv2, H1.
             apply head_lt;  unfold T1.lt, lt_b.
             now   rewrite H7. 
             apply head_lt;  unfold T1.lt, lt_b.
             now   rewrite H6. 
             apply tail_lt_ocons;auto.
          +   f_equal.   
              ass_rw_rev  Hrec (ocons a1 n a2)  a2 (ocons b1 n0 b2)
                          (ocons c1 n1 c2) ; trivial. 
              now rewrite oplus_cons_cons,  H6.
              eapply nf_inv2, H.
              apply tail_lt_ocons;auto.
              apply head_lt.
              unfold T1.lt, lt_b;rewrite compare_rev.
              now   rewrite H5.
              apply head_lt.
              unfold T1.lt, lt_b;rewrite compare_rev.
              now   rewrite H7.
             -  intros.
               generalize (compare_Eq_impl _ _ H5); intro; subst b1.
               repeat rewrite oplus_cons_cons.
               rewrite H5, H6.
               f_equal.
               ass_rw_rev  Hrec (ocons a1 n a2)  a2 b2  (ocons c1 n1 c2) ;
                 trivial. 
               eapply nf_inv2, H.
               eapply nf_inv2, H0.
               apply tail_lt_ocons;auto.
               apply lt_le_trans with (phi0 a1).
               apply lt_phi0_phi0.
               eapply lt_phi0_intro ;eauto.
               apply le_phi0;auto.
               apply head_lt.
               unfold T1.lt, lt_b;rewrite compare_rev.
               now   rewrite H6.

             -  intros;   repeat rewrite oplus_cons_cons. 
                rewrite H5,H6.
                f_equal.
                ass_rw_rev  Hrec (ocons b1 n0 b2) (ocons a1 n a2)  b2
                            (ocons c1 n1 c2) ; trivial.
                eapply nf_inv2, H0.
                apply head_lt;  unfold T1.lt, lt_b.
                now   rewrite H5. 
                apply tail_lt_ocons;auto.
                apply head_lt.
                unfold T1.lt, lt_b;rewrite compare_rev.
                now   rewrite H6.

             - intros;repeat rewrite oplus_cons_cons.
               assert (compare a1 c1 = Gt).
               rewrite gt_iff.
               rewrite gt_iff in H5.
               rewrite gt_iff in H6.
               apply T1.lt_trans with b1;auto.
               rewrite H5, H7.
               f_equal.
               ass_rw_rev  Hrec (ocons a1 n a2) a2  (ocons b1 n0 b2)
                           (ocons c1 n1 c2) ; trivial. 
               f_equal.
               now rewrite oplus_cons_cons, H6.
                eapply nf_inv2, H.
               apply tail_lt_ocons;auto.
               apply head_lt.
               unfold T1.lt, lt_b;rewrite compare_rev.
               now   rewrite H5.
               apply head_lt.
               unfold T1.lt, lt_b;rewrite compare_rev.
               now   rewrite H7.
      }
  Qed.


  Lemma oplus_assoc : forall alpha beta gamma,
                        nf alpha -> nf beta -> nf gamma ->
                                    alpha o+ (beta o+ gamma) =
                                    alpha o+ beta o+ gamma.
  Proof with eauto with T1.
    intros.
    apply oplus_assoc_0 with (T1.succ (max alpha (max beta gamma))) ...
    apply succ_nf; repeat apply max_nf ...
    all: apply T1.le_lt_trans with (max alpha (max beta gamma));
      [| apply lt_succ] ...
    - apply max_le_1.
    - rewrite (max_comm alpha (max beta gamma)).
            rewrite  max_assoc;    apply max_le_1.
    -     rewrite  <- max_assoc. 
          rewrite (max_comm (max alpha beta) gamma); apply max_le_1.
  Qed.

End Proof_of_oplus_assoc.

Section Proof_of_oplus_lt1.
  Variables a1 a2: T1.  
  Variable n : nat.
  Hypothesis H0 : nf (ocons a1 n a2).

  Lemma oplus_lt_0 : forall b, nf b -> T1.lt b (b o+ (ocons a1 n a2)).
  Proof with eauto with T1.
    intros b ; transfinite_induction_lt b.
    intros x H1 H;  destruct x.
    -  simpl. auto with T1.
    - rewrite oplus_eqn;case_eq (compare x1 a1).
      +  auto with T1 arith. 
      +  intros H2; apply head_lt; unfold T1.lt, lt_b. now  rewrite H2. 
      + intro; apply tail_lt,  H1 ;  trivial.
        eapply nf_inv2, H.
        now  apply tail_lt_ocons.
        eapply nf_inv2, H.
  Qed.

End Proof_of_oplus_lt1.


Lemma oplus_lt1 : forall a b, nf a -> nf b ->  T1.lt T1.zero  a ->
                              T1.lt b  (b o+  a).
Proof. 
  destruct a.
  - intros b _ _ H; T1_inversion H. 
  - intros; now apply oplus_lt_0.
Qed.

Lemma oplus_lt2 : forall a b, nf a -> nf b ->  T1.lt T1.zero  b ->
                              T1.lt a  (b o+ a).
Proof.
  intros a b Ha Hb  HD. rewrite (oplus_comm Hb Ha); auto;
                        apply oplus_lt1;auto.
Qed.

Lemma oplus_le : forall a b, nf a -> nf b -> T1.le a (a o+ b).
Proof.
  intros; destruct b.
  -  rewrite oplus_alpha_0.   auto with T1. 
  - apply lt_le_incl;  apply oplus_lt1; auto with T1.   
Qed.

Lemma oplus_le2 : forall a b, nf a -> nf b -> T1.le b (a o+ b).
Proof.
  intros; rewrite (@oplus_comm a b);auto.
  now apply oplus_le.
Qed.


Lemma oplus_strict_mono_0 :
  forall alpha, nf alpha ->
                forall a (Ha:nf a) b (Hb: nf b) c (Hc : nf c),
                  T1.lt a alpha ->  T1.lt c alpha -> T1.lt b c ->
                  T1.lt (a o+ b) (a o+ c).
Proof with eauto with T1.
  intros alpha ; transfinite_induction_lt alpha.
  clear alpha ; intros alpha Hrec  Halpha; intros.
  destruct a. 
  {
    now  repeat rewrite  oplus_0_beta.
  }
  destruct b, c.
  - inversion H1.
  - rewrite  oplus_alpha_0.
    now apply oplus_lt1.
  - T1_inversion H1.
  -  rewrite ( oplus_eqn (ocons a1 n a2) (ocons b1 n0 b2)).
     rewrite ( oplus_eqn (ocons a1 n a2) (ocons c1 n1 c2)).
     
     case_eq (compare a1 b1).
     intro Ha1_b1.
     case_eq (compare a1 c1).
     {
       intro Ha1_c1.
       destruct (lt_inv H1). 
       {    generalize (compare_Eq_impl _ _ Ha1_b1).
            intro;subst b1.
            generalize (compare_Eq_impl _ _ Ha1_c1).
            intro;subst c1.
            destruct (lt_irrefl H2).
       }
       destruct H2.
       destruct H2;subst c1.
       apply coeff_lt. 
       auto with arith.
       decompose [and] H2; subst c1 n1.
       apply tail_lt. 

       generalize (compare_Eq_impl _ _ Ha1_b1).
       intro;subst b1. 
       apply Hrec with (phi0 a1); info_eauto with T1.
       apply le_lt_trans with (ocons a1 n a2) ; trivial. 
       apply le_phi0 ; info_eauto with T1.
       apply lt_phi0_phi0.
       eapply lt_phi0_intro ; info_eauto with T1.
       apply lt_phi0_phi0.
       eapply lt_phi0_intro ; info_eauto with T1.
     }
     {
       intro Ha1b1.
       rewrite lt_iff in Ha1b1.
       generalize (compare_Eq_impl _ _ Ha1_b1).
       intro;subst b1.
       apply head_lt; auto. 
     }
     {
       intro.
       generalize (compare_Eq_impl _ _ Ha1_b1).
       intro;subst b1.     
       absurd  (T1.lt (ocons a1 n0 b2) (ocons c1 n1 c2)).
       - apply lt_not_gt.
         apply head_lt.
         unfold T1.lt, lt_b;rewrite compare_rev. now   rewrite H2.
       -   auto.
     }
     {
       intro.
       rewrite lt_iff in H2.
       case_eq (compare a1 c1).
       { 
         intro.
         generalize (compare_Eq_impl _ _ H3).
         intro;subst c1.     
         absurd (T1.lt (ocons b1 n0 b2) (ocons a1 n1 c2));auto.
         apply lt_not_gt.
         apply head_lt; auto. 
       }
       {
         intro.
         rewrite lt_iff in H3.
         destruct (lt_eq_lt_dec b1 c1).
         destruct s.
         { apply head_lt; auto. }
         {
           subst c1.
           destruct (lt_inv_nb H1).
           { apply coeff_lt; auto.  }
           destruct a; subst n1.
           apply tail_lt; auto. 
           rewrite (oplus_eqn (ocons a1 n a2) b2).
           rewrite (oplus_eqn (ocons a1 n a2) c2).
           destruct b2,c2.
           T1_inversion H5.
           case_eq (compare a1 c2_1).
           intro.
           apply coeff_lt;  auto with arith. 
           intro H6; apply head_lt; unfold T1.lt, lt_b; now rewrite H6.
           intros; apply tail_lt. 
           apply oplus_lt1; trivial.
           eapply nf_inv2, Hc.
           eapply nf_inv2, Ha.
           T1_inversion H5.
           case_eq (compare a1 b2_1); case_eq (compare a1 c2_1); intros.
           {
             generalize (compare_Eq_impl _ _ H4).
             generalize (compare_Eq_impl _ _ H6).
             intros.
             subst b2_1 c2_1.
             destruct (lt_inv_nb H5).
             apply coeff_lt; auto with arith.
             destruct a;subst;
             apply tail_lt.
             apply Hrec with (phi0 a1); trivial.
             eapply nf_phi0, nf_inv1, Ha.
             apply le_lt_trans with (ocons a1 n a2);eauto with T1.
             apply le_phi0.
             eapply nf_phi0, nf_inv1, Ha.
           eapply nf_inv2, Ha.
          eapply nf_inv2, nf_inv2, Hb.
          eapply nf_inv2, nf_inv2, Hc.
          apply lt_phi0_phi0. eapply lt_phi0_intro; eauto with T1.
          apply lt_phi0_phi0. eapply lt_phi0_intro; eauto with T1.
           }
           { generalize (compare_Eq_impl _ _ H6).
             rewrite lt_iff in H4.
             intro;subst b2_1.
             clear H6.
             now apply head_lt. 
           }
           {
             generalize (compare_Eq_impl _ _ H6).
             rewrite gt_iff in H4.
             intro;subst; clear H6.
             absurd (T1.lt (ocons b2_1 n1 b2_2) (ocons c2_1 n2 c2_2));auto.
             apply lt_not_gt.
             now apply head_lt. 
           }
           { generalize (compare_Eq_impl _ _ H4). intro;subst c2_1; clear H4.
             rewrite lt_iff in H6.
             contradict H5; apply lt_not_gt;  now apply head_lt.
           }
           {
             destruct (lt_inv H5).
             now apply head_lt.
             destruct H7.
             destruct H7;subst c2_1.
             now apply coeff_lt. 
             decompose [and] H7.
             clear H7;  subst.
             apply tail_lt.
             apply Hrec with (phi0 b1) ; info_eauto with T1.
             apply le_lt_trans with   (ocons b1 n0 (ocons c2_1 n2 c2_2)) ;
               trivial. 
             apply le_phi0 ; info_eauto with T1.
             (* now apply head_lt. *)
             apply lt_trans with (ocons c2_1 n2 c2_2) ; info_eauto with T1.
             apply tail_lt_ocons  ; info_eauto with T1.

           }
           {
             rewrite lt_iff in H6. rewrite gt_iff in H4.
             generalize(lt_inv_b H1).
             intro.     
             contradict H7;  apply lt_not_gt; apply head_lt.
             eapply lt_trans;eauto.
           }
           { apply coeff_lt;auto with arith. }
           { apply head_lt; auto. rewrite lt_iff in H4.  auto. }
           { apply tail_lt. 
             apply Hrec with (phi0 a1) ; trivial.
             eapply nf_phi0, nf_inv1, Ha.
             apply le_lt_trans with   (ocons a1 n a2) ; info_eauto with T1.
             apply le_phi0; info_eauto with T1.
             eapply nf_phi0, nf_inv1, Ha.
             eapply nf_phi0, nf_inv2, Ha.
              eapply nf_inv2, Hb.
              eapply nf_inv2, Hc.
             apply     lt_phi0_phi0.
             eapply lt_phi0_intro ; info_eauto with T1.
             apply head_lt;    now rewrite gt_iff in H4.
           }
         }

         {
           contradict H1; apply lt_not_gt;   now apply head_lt.
         }
       }
       { intro H3;  rewrite gt_iff in H3.
         contradict H1.
         apply lt_not_gt.
         apply head_lt;  apply lt_trans with a1;auto.
       }
     }

     { intro.
       rewrite gt_iff in H2.
       case_eq  (compare a1 c1).
       intro.
       generalize  (compare_Eq_impl _ _ H3).
       intro;subst c1; clear H3.
       apply coeff_lt; auto with arith.
       intro H3; rewrite lt_iff in H3.
       apply head_lt ; info_eauto with T1.

       intro H3; rewrite gt_iff in H3.
       apply tail_lt.  
       apply Hrec with (phi0 a1) ; trivial.
       eapply nf_phi0, nf_inv1, Ha.
       apply le_lt_trans with   (ocons a1 n a2) ; info_eauto with T1.
       apply le_phi0 ; info_eauto with T1.
       eapply nf_phi0, nf_inv1, Ha.
       eapply nf_inv2, Ha.
       apply lt_phi0_phi0.
       eapply lt_phi0_intro;eauto with T1.
       auto with T1.        
     }
Qed. 



Lemma oplus_strict_mono_r : forall a b c, nf a -> nf b -> nf c ->
                                          T1.lt b c -> T1.lt (a o+ b) (a o+ c).
Proof with auto with T1.
  intros.
  apply oplus_strict_mono_0 with (phi0 (max a c)) ...
  apply nf_phi0;apply max_nf ...
  apply le_lt_trans with (max a c) ...
  apply max_le_1.
  apply lt_a_phi0_a ...
  apply le_lt_trans with (max a c) ...
  rewrite (max_comm a c); apply max_le_1 ...
  apply lt_a_phi0_a ...
Qed.  

Lemma oplus_strict_mono_l : forall a b c, nf a -> nf b -> nf c ->
                                          T1.lt a b  ->
                                          T1.lt (a o+ c) (b o+ c).
Proof.
  intros a b c Ha Hb Hc H.
  rewrite (oplus_comm  Ha Hc).
  rewrite (oplus_comm Hb Hc).
  now apply oplus_strict_mono_r.
Qed.


Lemma oplus_strict_mono_LT_l (alpha beta gamma : T1) :
  nf gamma   -> alpha  t1< beta ->
  alpha o+ gamma t1< beta o+ gamma.
Proof.
  intros  Hgamma H.
  generalize (LT_nf_l H), (LT_nf_r H); intros  Ha  Hb.
   repeat split.
  now apply oplus_nf.
  apply oplus_strict_mono_l; trivial.
  auto with T1.
  now apply oplus_nf.
Qed.


Lemma oplus_strict_mono_LT_r (alpha beta gamma : T1) :
  nf alpha -> beta t1< gamma ->
  alpha o+ beta t1< alpha o+ gamma.
Proof.
  intros  Halpha H.
  generalize (LT_nf_l H), (LT_nf_r H); intros  Hb  Hc.
  repeat split.
  now apply oplus_nf.
  apply oplus_strict_mono_r; trivial.
  auto with T1.
  now apply oplus_nf.
Qed.



Lemma oplus_strict_mono_bi : forall a b c d ,
    nf a -> nf b -> nf c -> nf d ->
    T1.lt a b  -> T1.lt c d -> T1.lt (a o+ c) (b o+ d).
Proof.
  intros a b c d Ha Hb Hc Hd H0 H1;
  apply lt_trans with (oplus a d).
  -  apply oplus_strict_mono_r; auto.
  -  apply oplus_strict_mono_l; auto.
Qed.

Lemma oplus_of_phi0_0 : forall a b,
                          phi0 a o+ phi0 b =
                          match compare (phi0 a) (phi0 b)
                          with Lt => ocons b 0 (ocons a 0 T1.zero)
                            |  Eq => ocons a 1 T1.zero
                            | Gt =>  ocons a 0 (ocons b 0 T1.zero)
                          end.
Proof.
  intros a b; rewrite oplus_eqn; cbn; now  destruct (compare a b).
Qed.


Lemma oplus_of_phi0 : forall a b,
                        phi0 a o+ phi0 b =
                        match compare a b
                        with Lt => ocons b 0 (ocons a 0 T1.zero)
                          |  Eq => ocons a 1 T1.zero
                          | Gt =>  ocons a 0 (ocons b 0 T1.zero)
                        end.
Proof.
  intros a b; now rewrite oplus_of_phi0_0, compare_of_phi0.
Qed.


Lemma o_finite_mult_rw : forall a n, o_finite_mult (S n) (phi0 a) =
                                     ocons a n T1.zero.
  induction n.
  reflexivity.
  change (phi0 a o+  (o_finite_mult (S n) (phi0 a)) = ocons a (S n) T1.zero).
  rewrite IHn;  rewrite oplus_eqn.
  simpl; now rewrite compare_refl.
Qed.


Lemma o_finite_mult_lt_phi0_1 : forall a b n,
                                  T1.lt a b ->
                                  T1.lt (o_finite_mult n (phi0 a)) (phi0 b).
Proof with auto with T1. 
  intros a b n H;destruct n.
  -  apply zero_lt. 
  - rewrite o_finite_mult_rw.
    now apply head_lt. 
Qed.


Lemma o_finite_mult_mono : forall a b n,  nf a -> nf b -> T1.lt a b ->
                                          T1.lt (o_finite_mult (S n) a)
                                             (o_finite_mult (S n) b).
Proof with auto with T1.
  induction n.
  -  simpl;   repeat rewrite oplus_alpha_0;auto.
  -  simpl; intros; 
     apply oplus_strict_mono_bi ...
     apply oplus_nf;auto.
     apply o_finite_mult_nf;auto.  
     apply oplus_nf;auto.
     apply o_finite_mult_nf;auto.  
Qed. 

Lemma oplus_lt_phi0 : forall a b c,  nf a -> nf b -> nf c ->
                                     T1.lt a c -> T1.lt b c ->
                                     T1.lt (phi0 a o+ phi0 b) (phi0 c).
Proof.
  intros;  rewrite oplus_cons_cons; case_eq (compare a b).
   rewrite oplus_alpha_0; cbn.
   all: intros;  apply head_lt; eauto with T1.
Qed.


