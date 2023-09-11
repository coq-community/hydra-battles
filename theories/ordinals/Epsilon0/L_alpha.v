(** * Computing the length of paths from [alpha] to [zero] 

 After Wainer, Ketonen, Solovay, etc .

    Pierre Casteran, LaBRI, University of  Bordeaux *)

From hydras Require Import  Hprime  E0  Canon Paths
     Large_Sets.
From hydras Require Import  Simple_LexProd Iterates .
From Coq Require Import ArithRing Lia.
(* begin snippet LDef *)

From Equations Require Import Equations.
Import RelationClasses Relations.

#[global] Instance Olt : WellFounded E0lt := E0lt_wf.
#[export] Hint Resolve Olt : E0.

(** Using Coq-Equations for building a function which satisfies 
    [Large_sets.L_spec] *)

Equations  L_ (alpha: E0) (i:nat) : nat by wf alpha E0lt :=
  L_ alpha  i with E0_eq_dec alpha E0zero :=
    { | left _zero => i ;
      | right _nonzero
          with Utils.dec (E0limit alpha) :=
          { | left _limit =>  L_ (Canon alpha i)  (S i) ;
            | right _successor =>  L_ (E0pred alpha) (S i)}}.

(*| .. coq:: in messages |*)
Solve All Obligations with auto with E0. 

(*||*)
(* end snippet LDef *)

(* begin snippet AboutLEquation1 *)

About L__equation_1.
(* end snippet AboutLEquation1 *)

(** Paraphrase of equations generated by coq-equations *)

(* begin snippet Paraphrasesa:: no-out *)

Lemma L_zero_eqn : forall i, L_ E0zero i = i.
Proof. intro i; now rewrite L__equation_1. Qed.

Lemma L_eq2 alpha i :
  E0is_succ alpha -> L_ alpha i = L_ (E0pred alpha) (S i).
(* end snippet Paraphrasesa *)

Proof.
  intros; rewrite L__equation_1;  destruct (E0_eq_dec alpha E0zero).
  - subst; discriminate.
  - cbn; destruct (Utils.dec (E0limit alpha)) .
    apply Succ_not_T1limit in H; destruct H; auto.
    now cbn.
Qed.

(* begin snippet Paraphrasesb:: no-out *)
Lemma L_succ_eqn alpha i :
  L_ (E0succ alpha) i = L_ alpha (S i).
(* end snippet Paraphrasesb *)

Proof.
  intros;rewrite L_eq2;
    [autorewrite with E0_rw using trivial | auto with E0].
Qed.


#[export] Hint Rewrite L_zero_eqn L_succ_eqn : L_rw.

(* begin snippet Paraphrasesc:: no-out *)
Lemma L_lim_eqn alpha i :
  E0limit alpha ->
  L_ alpha i = L_ (Canon alpha i) (S i).
(* end snippet Paraphrasesc *)

Proof.
  intros;rewrite L__equation_1.
  destruct (E0_eq_dec alpha E0zero).
  - subst; discriminate.
  - cbn;  destruct (Utils.dec (E0limit alpha)) .
    + now cbn.    
    + red in H; rewrite e in H; discriminate.
Qed.


(* begin snippet LFiniteOmega *)

Lemma L_finite : forall i k :nat,  L_ i k = (i+k)%nat. (* .no-out *)
(*| .. coq:: none |*)
Proof.
  induction i.
  - simpl E0fin; intro; now rewrite L_zero_eqn.
  - simpl; rewrite FinS_Succ_eq; intro k; autorewrite with E0_rw L_rw.
    rewrite IHi.
   + abstract lia.
Qed.
(*||*)

Lemma L_omega : forall k, L_ E0omega k = S (2 * k)%nat. (* .no-out *)
(*| .. coq:: none |*)
Proof.
  intro k; rewrite L_lim_eqn.
  - replace (Canon  E0omega  k) with (E0fin k).
    + rewrite L_finite; abstract lia.
    +  cbn; unfold Canon; cbn.
       apply E0_eq_intro.
       destruct k;  reflexivity.
  - now cbn.
Qed.
(*||*)
(* end snippet LFiniteOmega *)

Lemma L_ge_id alpha : forall i,  i <= L_ alpha i.
Proof  with auto with E0.
     pattern alpha; apply well_founded_induction with E0lt ...
   clear alpha; intros alpha IHalpha.
  destruct (Zero_Limit_Succ_dec alpha).
  -  destruct s.
   +  subst alpha. intro; rewrite L_zero_eqn. auto with arith. 
   +   intros  k;  rewrite L_lim_eqn; auto.
     *  specialize (IHalpha (Canon alpha k)).
        destruct k;  simpl Canon.
        --  autorewrite with L_rw; auto. auto with arith.
        -- transitivity (S (S k)); [lia | apply IHalpha ]...
     -  destruct s as [beta e];  destruct (E0_eq_dec beta E0zero).
        +  subst  beta alpha.
           intros  k; autorewrite with L_rw; auto. 
        +   subst alpha; intros k; autorewrite with L_rw ...
              transitivity (S k); [lia |] ...
Qed.


(* begin snippet LGeS *)

Lemma L_ge_S alpha :
  alpha <> E0zero -> S <<= L_ alpha. (* .no-out *)
(*| .. coq:: none |*)
Proof  with auto with E0.
     pattern alpha; apply well_founded_induction with E0lt ...
   clear alpha; intros alpha IHalpha.
  destruct (Zero_Limit_Succ_dec alpha).
  -  destruct s.
   +  intro; contradiction. 
   +   intros H k;  rewrite L_lim_eqn; auto.
     *  specialize (IHalpha (Canon alpha k)).
        destruct k;  simpl Canon.
        apply L_ge_id.
        apply L_ge_id. 
     -  destruct s as [beta e];  destruct (E0_eq_dec beta E0zero).
        +  subst  beta alpha.
           intros H k; autorewrite with L_rw; auto. 
        +   subst alpha; intros H k; autorewrite with L_rw ...
              transitivity (S (S k)); [lia |] ...
              apply IHalpha ...
Qed.
(*||*)
(* end snippet LGeS *)

Lemma L_succ_ok  beta f :
  nf beta -> S <<= f -> L_spec beta f ->
  L_spec (succ beta)  (fun k =>  f (S k)).
Proof.
  intros; apply Large_Sets.L_succ_ok; auto.
Qed.


(** [L_] is correct w.r.t. its specification *)

Section L_correct_proof.

  Let P alpha :=  L_spec (cnf alpha) (L_ alpha).

  Lemma L_ok0 : P E0zero.
  Proof. red; simpl. left. intro k; now rewrite L_zero_eqn. Qed.

  Lemma L_ok_succ beta  : P beta -> P (E0succ beta).
  Proof with auto with E0.
    intro H; red;  rewrite Succ_rw.
    destruct (E0_eq_dec beta E0zero).
    -  subst; simpl; generalize (L_fin_ok 1); unfold L_fin.
       replace one with (T1nat 1); [simpl | trivial].
       intro; eapply L_spec_compat;  eauto.
       intros; rewrite L_eq2; auto with E0.
       rewrite E0pred_of_Succ, L_zero_eqn; trivial.
    -  apply L_spec_compat  with (L_succ (L_ beta));
         auto.
       + apply L_succ_ok; auto.
         * apply cnf_ok; auto.
         * intro k; apply L_ge_S; auto.
       + unfold L_succ; intro n0; now autorewrite with L_rw.
  Qed. 

  Lemma L_ok_lim  alpha  :
    (forall beta,  (beta o< alpha)%e0 -> P beta) ->
    E0limit alpha -> P alpha.
  Proof with eauto with E0.
    unfold P; intros.
    apply L_spec_compat with (fun k =>  L_ (Canon alpha k) (S k)).
    -   generalize L_lim_ok; intro H1; unfold L_lim in H1.
       assert (H2 : T1limit (cnf alpha)) by (now destruct alpha). 
       specialize (H1 (cnf alpha) cnf_ok H2 (fun k i => L_ (Canon alpha k) i)).
       apply H1; intro k; specialize (H (Canon alpha  (S k))).
       assert  (H3: (Canon alpha (S k) o< alpha)%e0 ).
       { apply CanonS_lt;  now apply Limit_not_Zero. }
       apply H in H3; apply L_spec_compat with (L_ (Canon alpha (S k))); auto.
    - intro n; rewrite (L_lim_eqn alpha); trivial.
  Qed.

  
  
  Lemma L_ok (alpha: E0) : P alpha.
  Proof with eauto with E0.
    apply well_founded_induction with E0lt ...
    clear alpha; intros alpha IHalpha.
    destruct (Zero_Limit_Succ_dec alpha) as [[H | H] | H].
    - subst; apply L_ok0.
    - apply L_ok_lim; auto.
    - destruct H as [beta Hbeta]; subst; apply L_ok_succ.
      apply IHalpha; auto with E0.
  Qed.

  
End L_correct_proof.

(* begin snippet LCorrect *)

Theorem L_correct alpha : L_spec (cnf alpha) (L_ alpha). (* .no-out *)
(*| .. coq:: none |*)
Proof. apply L_ok. Qed.
(*||*)
(* end snippet LCorrect *)

(** Comparison with Hardy's function H  *)

(* begin snippet HprimeL *)

Theorem H'_L_ alpha :
  forall i:nat,  (H'_ alpha i <= L_ alpha (S i))%nat. (* .no-out *)
(* end snippet HprimeL *)

Proof with auto with E0.
  pattern alpha ; apply well_founded_induction with E0lt ...
  clear alpha; intros alpha IHalpha i.
  destruct (Zero_Limit_Succ_dec alpha) as [[H | H] | H].
  - subst; rewrite H'_eq1, L_zero_eqn. abstract lia.
  - rewrite H'_eq3, L_lim_eqn ...
    apply Nat.lt_le_incl;
      apply Nat.lt_le_trans with (H'_ (Canon alpha (S i)) (S i)).
    apply H'_alpha_mono; auto with arith ...
    apply IHalpha ...
  -  destruct H as [beta e]; subst alpha;
       rewrite H'_eq2, L_succ_eqn ...
Qed.

Require Import Extraction.

Recursive Extraction L_.
