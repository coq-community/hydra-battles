(**  Pierre Casteran 
    LaBRI, University of Bordeaux 


   Class of ordinals less than epsilon0 


   [E0] is a class type for ordinal terms proved to be in normal form.
*)

From Coq Require Import Arith Max Bool Lia  Compare_dec  Relations Ensembles
     ArithRing  Wellfounded  Operators_Properties  Logic.Eqdep_dec.

From hydras Require Import Prelude.More_Arith  Prelude.Restriction
           Prelude.DecPreOrder  ON_Generic OrdNotations.

From hydras.Epsilon0 Require Export T1 Hessenberg.

Set Implicit Arguments.
Declare Scope E0_scope.

Delimit Scope E0_scope with e0.
Open Scope E0_scope.


(** ** Definitions *)


Class E0 : Type := mkord {cnf : T1; cnf_ok : nf cnf}.

Arguments cnf : clear implicits.

Global Hint Resolve cnf_ok : E0.

(** ** Lifting functions from [T1] to [E0] *)


Definition Lt (alpha beta : E0) := T1.LT (@cnf alpha) (@cnf beta).
Definition Le (alpha beta : E0) := T1.LE (@cnf alpha) (@cnf beta).

Infix "o<" := Lt : E0_scope.
Infix "o<=" := Le : E0_scope.

Instance Zero : E0 := @mkord zero refl_equal.

Definition Limitb (alpha : E0) : bool :=
  limitb (@cnf alpha).

Definition Succb (alpha : E0) : bool :=
  succb (@cnf alpha).


Instance _Omega : E0.
Proof.
  now exists omega%t1.  
Defined. 

Notation omega  := _Omega.

Instance Succ (alpha : E0) : E0.
Proof.
  refine (@mkord (T1.succ (@cnf alpha)) _); 
  apply succ_nf,  cnf_ok.
Defined.


  
Instance ord1 : E0.
Proof. 
  refine (@mkord (T1.succ zero) _);now compute. 
Defined.


Instance plus (alpha beta : E0) : E0.
Proof.
  refine (@mkord (T1.plus (@cnf alpha) (@cnf beta))_ );
    apply plus_nf; apply cnf_ok.
Defined.

Infix "+" := plus : E0_scope.


Instance Phi0 (alpha: E0) : E0.
Proof.
  refine (@mkord (phi0 (cnf alpha)) _).
  apply nf_phi0; apply cnf_ok.
Defined.

Instance Omega_term (alpha: E0) (n: nat) : E0.
Proof.
  refine (@mkord (ocons (cnf alpha) n zero) _).
  apply nf_phi0; apply cnf_ok.
Defined.

Instance Ocons (alpha : E0) (n: nat) (beta: E0) : E0
  := (Omega_term alpha n + beta)%e0.                                                          

Instance FinS (i:nat) : E0.
Proof.
  refine (@mkord (FS i)%t1 _);apply T1.nf_FS.
Defined.



Instance Fin (i:nat) : E0.
Proof.
  destruct i.
  - exact Zero.
  - exact (FinS i).
Defined.

Coercion Fin : nat >-> E0.


Instance Mult (alpha beta : E0) : E0.
Proof.
  refine (@mkord (cnf alpha * cnf beta)%t1 _).
  apply nf_mult; apply cnf_ok.
Defined.


Infix "*" := Mult : E0_scope.

Instance Mult_i  (alpha: E0) (n: nat) : E0.
Proof.
  refine (@mkord (cnf alpha * n)%t1  _).
  apply nf_mult_fin.  apply cnf_ok.
Defined.

(** ** Lemmas *)

(* begin hide *)

Lemma cnf_rw (alpha:T1)(H :nf alpha) : cnf (mkord H) = alpha.
Proof. reflexivity. Defined.

(* end hide *)


(** ** On equality on type [E0] *)

Lemma nf_proof_unicity :
  forall (alpha:T1) (H H': nf alpha), H = H'.
Proof.
  intros;  red in H, H';  apply eq_proofs_unicity_on.
  destruct y. 
  - rewrite H; auto. 
  - rewrite H; right; discriminate. 
Qed.


Lemma E0_eq_intro : forall alpha beta : E0,
    cnf alpha = cnf beta -> alpha = beta.
Proof.
  destruct alpha, beta;simpl;intros; subst;f_equal; auto.
  apply nf_proof_unicity.
Qed.


Lemma E0_eq_iff alpha beta : alpha = beta <-> cnf alpha = cnf beta.
Proof.
 split.
 -  intro; now f_equal.  
 - intro; now apply E0_eq_intro.
Qed.

Lemma Succb_Succ alpha : Succb alpha -> {beta : E0 | alpha = Succ beta}.
Proof.
  destruct alpha.
  cbn.
  intro H; destruct (succb_def cnf_ok0 H) as [beta [Hbeta Hbeta']]; subst.
  assert (nf (succ beta)) by eauto with T1.
  exists (@mkord  beta Hbeta).
  apply E0_eq_intro. now cbn.
Defined.

Global Hint Resolve E0_eq_intro : E0.

Ltac orefl := (apply E0_eq_intro; try reflexivity).

Ltac ochange alpha beta := (replace alpha with beta; [| orefl]).

Lemma E0_eq_dec : forall alpha beta: E0,
    {alpha = beta}+{alpha <> beta}.
Proof.
  destruct alpha, beta.
  destruct (T1_eq_dec cnf0 cnf1) as [e | n].
  - subst; left; auto with E0.
  - right; intro H; destruct n; now injection H.
Defined.

(** ** Adaptation to [E0] of lemmas about [T1]  *)

Lemma alpha_plus_zero alpha : alpha + Zero = alpha.
Proof.
  apply E0_eq_intro; simpl; now rewrite plus_zero_r.
Qed.

Hint Rewrite alpha_plus_zero : E0_rw.

Lemma cnf_Phi0 (alpha : E0) :
  cnf (Phi0 alpha) = phi0 (cnf alpha).
Proof.
 unfold Phi0. now rewrite cnf_rw.
Defined.

Lemma cnf_Succ (alpha : E0) :
  cnf (Succ alpha) = succ (cnf alpha).
Proof.
 unfold Succ. now rewrite cnf_rw.
Defined.

Lemma cnf_Omega_term (alpha: E0) (n: nat) :
  cnf (Omega_term alpha n) = omega_term (cnf alpha) n.
Proof.
  reflexivity.
Defined.

Lemma Limitb_Omega_term alpha i : alpha <> Zero ->
                                    Limitb (Omega_term alpha i).
Proof.
  intro H; unfold Limitb.
  destruct alpha; simpl; destruct cnf0.
   - destruct H; auto with E0.
   -  auto.
Qed.

Lemma Limitb_Phi0 alpha  : alpha <> Zero ->
                             Limitb (Phi0 alpha).
Proof.
  unfold Phi0; apply Limitb_Omega_term.
Qed.

Global Hint Resolve Limitb_Phi0 : E0.




Definition Zero_Limit_Succ_dec (alpha : E0) :
  {alpha = Zero} + {Limitb alpha = true} +
  {beta : E0  | alpha = Succ beta}.
  destruct alpha as [t Ht];  destruct (zero_limit_succ_dec  Ht).  
  -  destruct s. 
     + left; left. 
       unfold Zero; subst t; f_equal.
       apply nf_proof_unicity.
     + left;right; unfold Limitb; now simpl. 
  -  destruct s as [beta [H0 H1]]; right;  eexists (@mkord beta H0).
     subst t; unfold Succ; f_equal; apply nf_proof_unicity.
Defined.


Definition Pred (alpha: E0) : E0 :=
  match Zero_Limit_Succ_dec  alpha with
      inl _ => Zero
    | inr (exist _ beta _) => beta
  end.


Tactic Notation "mko" constr(alpha) := refine (@mkord alpha eq_refl).

Instance Two : E0 :=  ltac:(mko (fin 2)).

Instance Omega_2 : E0 :=ltac:(mko (T1.omega * T1.omega)%t1).


Instance Lt_sto : StrictOrder Lt.
Proof.
  split.
  - intro x ; destruct x; unfold Lt.  red.
    cbn; intro; eapply LT_irrefl; eauto.
  - intros [x Hx] [y Hy] [z Hz].
    unfold Lt; cbn.
    apply LT_trans.
 Qed.

Definition compare (alpha beta:E0): comparison :=
  T1.compare (cnf alpha) (cnf beta).

Lemma compare_correct alpha beta :
  CompareSpec (alpha = beta) (alpha o< beta) (beta o< alpha)
              (compare alpha beta).
Proof.
  destruct alpha, beta; unfold compare, Lt; cbn;
    destruct (T1.compare_correct cnf0 cnf1).
  -   constructor 1;  apply E0_eq_intro;  subst; reflexivity. 
  -   constructor; now split.
  -  constructor; split; auto.
Qed.

Lemma Lt_wf : well_founded Lt.
Proof.
  split; intros [t Ht] H;
    apply (Acc_inverse_image _ _ LT (@cnf) 
                             {| cnf := t; cnf_ok := Ht |} );
    now   apply T1.nf_Acc. 
Defined.

Global Hint Resolve Lt_wf : E0.

Lemma Lt_Succ_Le (alpha beta: E0):  beta o< alpha -> Succ beta o<= alpha.
Proof.
  destruct alpha, beta;simpl in *;  unfold le, Lt;simpl.
  intro. split; auto.
  - apply T1.succ_nf; auto.
  -  split; auto.
     + apply T1.lt_succ_le;auto.
       destruct H; tauto.
Qed.



Lemma Pred_of_Succ (alpha:E0) : Pred (Succ alpha) = alpha.
Proof.
  unfold Pred; destruct (Zero_Limit_Succ_dec (Succ alpha)).
  destruct s.
  - unfold Succ, Zero in e; injection  e .
    intro H; now   destruct (T1.succ_not_zero (cnf alpha)).
  -  unfold limitb, Succ in e; simpl in e;
       destruct (@T1.limitb_succ (cnf alpha)); auto.
        destruct alpha; simpl; auto. 
  -  destruct s.
    { unfold Succ in e;  injection e.
      destruct alpha, x;simpl; intros; apply T1.succ_injective in H; auto.
      -  subst; replace cnf_ok1 with cnf_ok0; trivial.
         eapply nf_proof_unicity.
    }
Qed.

Hint Rewrite Pred_of_Succ: E0_rw.

Lemma Succ_inj alpha beta : Succ alpha = Succ beta -> alpha = beta.
Proof.
  destruct alpha, beta; intros;  apply E0_eq_intro. 
  cbn;  unfold Succ in H; cbn in H; injection H. 
  intro; apply succ_injective; auto.
Qed.

Lemma  Pred_Lt (alpha : E0) : alpha <> Zero  ->  Limitb alpha = false ->
                       Pred alpha o< alpha.
Proof.
  unfold Limitb, Pred, Lt; destruct alpha; intros. simpl.
  destruct (T1.zero_limit_succ_dec cnf_ok0 ).
  destruct s.
  - subst. unfold Zero in H. destruct H. f_equal;apply nf_proof_unicity.
  - simpl in H0; rewrite i in H0; discriminate.
  - destruct s. destruct a. simpl. subst cnf0.
    apply LT_succ;auto.
Qed.

Global Hint Resolve Pred_Lt : E0.


Lemma Succ_Succb (alpha : E0) : Succb (Succ alpha).
destruct alpha; unfold Succb, Succ; cbn; apply T1.succ_succb.
Qed.

Global Hint Resolve Succ_Succb : E0.

Ltac ord_eq alpha beta := assert (alpha = beta);
      [apply E0_eq_intro ; try reflexivity|].


Lemma FinS_eq i : FinS i = Fin (S i).
Proof. reflexivity. Qed.

Lemma mult_fin_rw alpha (i:nat) : alpha * i = Mult_i alpha i.
Proof.
 orefl; cbn; f_equal; now destruct i.
 Qed.


Lemma FinS_Succ_eq : forall i, FinS i = Succ (Fin i).
Proof.
  intro i; compute. orefl; now destruct i.
Qed.

Hint Rewrite FinS_Succ_eq : E0_rw.

Lemma Limit_not_Zero alpha : Limitb alpha -> alpha <> Zero.
Proof.
  destruct alpha; unfold Limitb, Zero; cbn; intros H H0.
  injection H0;  intro ; subst cnf0; eapply T1.limitb_not_zero; eauto.
Qed.


Lemma Succ_not_Zero alpha:  Succb alpha -> alpha <> Zero.
Proof.
  destruct alpha;unfold Succb, Zero; cbn.
  intros H H0; injection H0; intro;subst; discriminate H.
Qed.

Lemma Lt_Succ : forall alpha, Lt alpha (Succ alpha).
Proof.
  destruct  alpha; unfold lt, Succ; cbn; apply LT_succ;auto.
Qed.


Lemma Succ_not_Limitb alpha : Succb alpha -> ~ Limitb alpha .
Proof. 
  red; destruct alpha; unfold Succb, Limitb; cbn.
  intros H H0. rewrite (succ_not_limit _ H) in H0. discriminate.  
Qed.

Global Hint Resolve Limit_not_Zero Succ_not_Zero Lt_Succ Succ_not_Limitb : E0.

Lemma lt_Succ_inv : forall alpha beta, beta o< alpha <->
                                       Succ beta o<= alpha.
Proof.
  destruct alpha, beta; unfold lt, le, Succ; cbn; split.
  -  intro; now  apply LT_succ_LE.
  - intro; now apply LT_succ_LE_R.  
Qed.

Lemma lt_Succ_le_2 (alpha beta: E0):
    alpha o< Succ beta -> alpha o<= beta.
Proof.
 destruct alpha, beta; cbn; intros.
 red in H; red. 
 cbn;  apply LT_succ_LE_2; auto.
Qed.

Lemma Succ_lt_Limitb alpha beta:
    Limitb alpha ->  beta o< alpha -> Succ beta o< alpha.
Proof.
  destruct alpha, beta;unfold Lt; cbn.
  intros; apply succ_lt_limit; auto. 
Qed.

Lemma le_lt_eq_dec : forall alpha beta, alpha o<= beta ->
                                        {alpha o< beta} + {alpha = beta}.
Proof.
  destruct alpha, beta.
  unfold Lt, Le; cbn.
  intro H; destruct (LE_LT_eq_dec  H).
  - now left.
  - right; subst; f_equal; apply nf_proof_unicity.
Qed.



Instance Epsilon0 : ON Lt compare.
Proof.
 split.
 - apply Lt_sto.
 - apply Lt_wf.
 - apply compare_correct.
Qed.


Definition Zero_limit_succ_dec : ZeroLimitSucc_dec .
  - intro alpha; destruct (Zero_Limit_Succ_dec alpha) as [[H | H] | [p Hp]].
    + subst alpha; left; left; intro beta. destruct beta as [cnf H].
      destruct cnf.
      replace  {| cnf := zero; cnf_ok := H |} with Zero.
      right.
      apply E0_eq_intro. reflexivity.
      left.
      unfold Lt.
      cbn.
      auto with T1.
    +
      destruct alpha as [a Ha]. unfold Limitb in H. cbn in H.
      left;right.
      split.  
      exists Zero.
      destruct a;try discriminate.
      constructor. 
      destruct a2; try discriminate.
      auto with T1.
      auto with T1.
      split.
      constructor.
      auto.

      intros. 
      exists (Succ y).
      split.
      apply Lt_Succ.
      destruct y as [y Hy]; split.
      unfold Lt, Succ; cbn.
      now apply LT_succ.
      unfold Lt, Succ in *.
      cbn in *.
      apply succ_lt_limit; auto.

    + 
      right.
      exists p;
        subst.
      red. 
      split.
      apply Lt_Succ.

      destruct p, z. unfold Lt, Succ; cbn in *; intros.
      destruct (@LT_irrefl cnf1).
      apply T1.LT_LE_trans with (succ cnf0); auto with T1.
      now apply LT_succ_LE.
Qed.





(** ** Rewriting lemmas *)

Lemma Succ_rw : forall alpha, cnf (Succ alpha) = T1.succ (cnf alpha).
Proof.
  now destruct alpha.
Qed.

Lemma Plus_rw : forall alpha beta, cnf (alpha + beta) =
                                   (cnf alpha + cnf beta)%t1.
Proof.
  now destruct alpha, beta.
Qed.


Lemma Lt_trans alpha beta gamma :
  alpha o< beta -> beta o< gamma -> alpha o< gamma.
Proof.
  destruct alpha, beta, gamma; simpl. unfold lt.
  simpl.
 intros; eauto with T1.
 eapply T1.LT_trans; eauto.
Qed.

Lemma Le_trans alpha beta gamma :
  alpha o<= beta -> beta o<= gamma -> alpha o<= gamma.
Proof.
  destruct alpha, beta, gamma; simpl. unfold le.
  simpl.
 intros; eauto with T1.
 eapply T1.LE_trans; eauto.
Qed.



Lemma Omega_term_plus alpha beta i :
  alpha <> Zero -> (beta o< Phi0 alpha)%e0 ->
  cnf (Omega_term alpha i + beta)%e0 = ocons (cnf alpha) i (cnf beta).
Proof.
  destruct alpha as [alpha Halpha]; destruct beta as [beta Hbeta].
  intros.
  unfold lt in H0. simpl in H0.
  unfold  Omega_term. unfold cnf.
  unfold plus.
  unfold cnf at 1 2.
  fold (omega_term alpha i ).
  rewrite omega_term_plus_rw.
  reflexivity.
  rewrite nf_LT_iff; tauto.
Qed.


Lemma cnf_Ocons (alpha beta: E0) n : alpha <> Zero -> beta o< Phi0 alpha ->
                                     cnf (Ocons alpha n beta) =
                                     ocons (cnf alpha) n (cnf beta).
Proof.
  intros. unfold Ocons. rewrite Omega_term_plus; auto.
Defined.

Lemma Limitb_plus alpha beta i:
  (beta o< Phi0 alpha)%e0 -> Limitb beta ->
  Limitb (Omega_term alpha i + beta)%e0.
Proof.
  intros H H0;  assert (alpha <> Zero).
  { intro; subst. 
    apply (Limit_not_Zero H0).
    destruct beta.
    red in H. simpl in H.
    apply LT_one in H. subst.
    now apply E0_eq_intro.
  }
  unfold Limitb; rewrite Omega_term_plus; auto.
  cbn;  case_eq (cnf alpha).
  -  intro H2; destruct H1.
     apply E0_eq_intro.
     apply H2.
  -  intros alpha0 n beta0 H2.
     unfold Limitb in H0;    destruct (cnf beta); auto.
Qed.


Lemma Succ_of_cons alpha gamma i : alpha <> Zero -> gamma o< Phi0 alpha ->
                                cnf (Succ (Omega_term alpha i + gamma)%e0) =
                                cnf (Omega_term alpha i + Succ gamma)%e0.
Proof.
  intros.
  rewrite Omega_term_plus; auto.
  rewrite Succ_rw.
  rewrite Omega_term_plus; auto.
  rewrite succ_cons, Succ_rw; auto.
  intro H1; apply H, E0_eq_intro.   assumption. 
  destruct H0.
  destruct H1.
  rewrite cnf_Phi0 in H1.
  apply nf_intro; auto.
  now apply nf_helper_phi0R. 
  red.  
  apply succ_lt_limit.
  rewrite cnf_Phi0.
  apply nf_phi0. apply cnf_ok.
  rewrite cnf_Phi0.
  simpl.
  case_eq (cnf alpha).
  intro.
  destruct H.
  apply E0_eq_intro. assumption.
  intros; trivial. 
  now red.   
  assumption.
Qed.


Instance Oplus (alpha beta : E0) : E0.
Proof.
  refine (@mkord (oplus (cnf alpha) (cnf beta) )_).
  apply oplus_nf; apply cnf_ok.
Defined.

Infix "O+" := Oplus (at level 50, left associativity): E0_scope.

Lemma Oplus_assoc (alpha beta gamma : E0) :
   (alpha O+ (beta O+ gamma) =  alpha O+ beta O+ gamma)%e0.
Proof.
  destruct alpha, beta, gamma. unfold Oplus.  cbn.
  apply E0_eq_intro. cbn. now   rewrite oplus_assoc.
Qed.



Lemma oPlus_rw (alpha beta : E0) :
  cnf (alpha O+ beta)%e0 = (cnf alpha o+ cnf beta)%t1.
Proof.
  now destruct alpha, beta.
Qed.


Example L_3_plus_omega :  3 + omega = omega.
Proof.
  now  apply compare_Eq_eq.
Qed.


(* to simplify ! *)

Lemma succ_correct alpha beta : cnf beta = succ (cnf alpha) <->
                                Successor beta alpha.
Proof.
  destruct alpha, beta; cbn; split.
  -  intro; subst.  
     split.
     +  unfold ON_lt; red; cbn; red; red; repeat split; auto.
        apply lt_succ.
     +  destruct z;  unfold Lt; cbn; intros.
        assert (cnf1 t1< cnf1)%t1.
        { repeat split; auto.
          apply lt_le_trans with (succ cnf0).
          destruct H0; auto with T1.
          now destruct H1.
          apply lt_succ_le; auto.
          apply H.
        }
        destruct H1.
        destruct H2.
        eapply lt_irrefl; eauto.
  - destruct 1.
    unfold Lt in H, H0. cbn in H, H0.
    destruct H.
    destruct H1.
    + apply lt_succ_le in H1; auto.
      * destruct (le_lt_or_eq _ _ H1); auto.
        specialize (H0 (Succ (mkord cnf_ok0))).
        cbn in H0; unfold LT in H0.
        exfalso.
        apply H0.
        -- split; auto with T1.
           split; auto with T1.
           ++ apply lt_succ;eauto with T1.
           ++ apply succ_nf; auto.
        -- split; auto with T1.
           apply succ_nf; auto.
Qed.


Lemma Le_refl alpha : alpha o<= alpha.
Proof.
  destruct alpha; split.
  - cbn; auto.
  - split; cbn; auto with T1.
Qed.

Lemma Lt_Le_incl alpha beta : alpha o< beta -> alpha o<= beta.
Proof.
  destruct alpha, beta; split.
  - cbn; auto.
  - split; cbn; auto.
    cbn in H; destruct H; cbn in *.
    apply lt_le_incl; tauto.
Qed.

Lemma E0_Lt_irrefl (alpha : E0) : ~ alpha o< alpha.
Proof.
  destruct alpha;unfold Lt;cbn;apply LT_irrefl.
Qed.

Lemma E0_Lt_Succ_inv (alpha beta: E0):
  alpha o< Succ beta -> alpha o< beta \/ alpha = beta.
Proof.
  destruct alpha, beta; unfold Lt; cbn; intros.
  destruct (LT_succ_LE_2 cnf_ok1 H) as [H0 [H1 H2]].
  destruct (T1.le_lt_or_eq _ _ H1) as [H3 | H3].
  - subst; right;apply E0_eq_intro;reflexivity. 
  - left; split; auto.
Qed.

Lemma E0_not_Lt_zero alpha : ~ alpha o< Zero.
Proof.
  destruct alpha; unfold Lt; cbn.
  intros [H [H0 H1]]; eapply not_lt_zero; eauto. 
Qed.

Lemma lt_omega_inv: forall alpha:E0,  alpha o< omega -> exists (i:nat),  alpha = Fin i.
Proof. 
  destruct alpha;  unfold _Omega; cbn in *; intro.
  destruct H.
  destruct H0.
  cbn in H0.
  assert (H2 : cnf0 t1< T1.omega%t1).
  {  split; cbn in H1; tauto. }
  destruct (lt_omega_inv H2).
  - exists 0; subst;  unfold Fin; apply E0_eq_intro;  reflexivity. 
  -  destruct H3; subst;  exists (S x); apply E0_eq_intro; reflexivity.
Qed.


Lemma E0_lt_eq_lt alpha beta : alpha o< beta \/ alpha = beta \/ beta o< alpha.
Proof.
  destruct (compare_correct alpha beta).
  - subst;right;now left.
  - now left.
  - right; now right.
Qed.

Lemma E0_lt_ge alpha beta : alpha o< beta \/ beta o<= alpha.
Proof.
  destruct (E0_lt_eq_lt alpha beta) as [H | [ | H]].
  - now left.
  - subst; right. apply Le_refl.
  - right; now apply Lt_Le_incl.
Qed.


Lemma Phi0_mono alpha beta : alpha o< beta -> Phi0 alpha o< Phi0 beta.
Proof.
  destruct alpha, beta; unfold Lt; cbn;  auto with T1.
Qed.
