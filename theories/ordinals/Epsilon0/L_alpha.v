(** * Computing the length of paths from [alpha] to [zero] 

 After Wainer, Ketonen, Solovay, etc .

    Pierre Casteran, LaBRI, University of  Bordeaux *)

From hydras Require Import  H_alpha  E0  Canon Paths
     Large_Sets.
From hydras Require Import  Simple_LexProd Iterates .
From Coq Require Import ArithRing Lia.
From Equations Require Import Equations.
Import RelationClasses Relations.

Instance Olt : WellFounded Lt := Lt_wf.
Hint Resolve Olt : E0.

(** Using Coq-Equations for building a function which satisfies 
    [Large_sets.L_spec] *)

Equations  L_ (alpha: E0) (i:nat) :  nat  by wf  alpha Lt :=
  L_ alpha  i with E0_eq_dec alpha Zero :=
    { | left _ =>  i ;
      | right nonzero
          with Utils.dec (Limitb alpha) :=
          { | left _ =>  L_ (Canon alpha i)  (S i) ;
            | right notlimit =>  L_ (Pred alpha) (S i)}}.

Solve All Obligations with auto with E0.


(** Paraphrase of equations generated by coq-equations *)

Lemma L_zero_eqn : forall i, L_ Zero i = i.
Proof. intro i; now rewrite L__equation_1. Qed.

Lemma L_eq2 alpha i : Succb alpha -> L_ alpha i = L_ (Pred alpha) (S i).
Proof.
  intros; rewrite L__equation_1;  destruct (E0_eq_dec alpha Zero).
  - subst; discriminate.
  - cbn;  destruct (Utils.dec (Limitb alpha)) .
    apply Succ_not_Limitb in H; destruct H; auto.
    now cbn.
Qed.

Lemma L_succ_eqn alpha i :  L_ (Succ alpha) i = L_  alpha (S i).
Proof.
  intros;rewrite L_eq2;
    [autorewrite with E0_rw using trivial | auto with E0].
Qed.

Hint Rewrite L_zero_eqn L_succ_eqn : L_rw.

Lemma L_lim_eqn alpha i : Limitb alpha -> L_ alpha i =
                                        L_ (Canon alpha i) (S i).
Proof.
  intros;rewrite L__equation_1.
  destruct (E0_eq_dec alpha Zero).
  - subst; discriminate.
  - cbn;  destruct (Utils.dec (Limitb alpha)) .
    + now cbn.    
    + red in H; rewrite e in H; discriminate.
Qed.

Lemma L_finite : forall i k :nat,  L_ i k = (i+k)%nat.
Proof.
  induction i.
  - simpl Fin; intro; now rewrite L_zero_eqn.
  - simpl; rewrite FinS_Succ_eq; intro k; autorewrite with E0_rw L_rw.
    rewrite IHi.
   + abstract lia.
Qed.

Lemma L_omega : forall k, L_ omega%e0 k = S (2 * k)%nat.
Proof.
  intro k; rewrite L_lim_eqn.
  - replace (Canon  omega%e0 k) with (Fin k).
    + rewrite L_finite; abstract lia.
    +  cbn; unfold Canon; cbn.
       apply E0_eq_intro.
       destruct k;  reflexivity.
  - now cbn.
Qed.


Lemma L_ge_S alpha : alpha <> Zero -> S <<= L_ alpha.
Proof  with auto with E0.
     pattern alpha; apply well_founded_induction with Lt ...
   clear alpha; intros alpha IHalpha.
  destruct (Zero_Limit_Succ_dec alpha).
  -  destruct s.
   +  intro; contradiction. 
   +   intros H k;  rewrite L_lim_eqn; auto.
     *  specialize (IHalpha (Canon alpha k)).
        destruct k;  simpl Canon.
        --  autorewrite with L_rw; auto.
        -- transitivity (S (S (S k))); [lia | apply IHalpha ]...
     -  destruct s as [beta e];  destruct (E0_eq_dec beta Zero).
        +  subst  beta alpha.
           intros H k; autorewrite with L_rw; auto. 
        +   subst alpha; intros H k; autorewrite with L_rw ...
              transitivity (S (S k)); [lia |] ...
              apply IHalpha ...
Qed.



Lemma L_succ_ok  beta f :
  nf beta -> S <<= f -> L_spec beta f ->
  L_spec (succ beta)  (fun k =>  f (S k)).
Proof.
  intros; apply Large_Sets.L_succ_ok; auto.
Qed.


(** [L_] is correct w.r.t. its specification *)

Section L_correct_proof.

  Let P alpha :=  L_spec (cnf alpha) (L_ alpha).

  Lemma L_ok0 : P Zero.
  Proof. red; simpl. left. intro k; now rewrite L_zero_eqn. Qed.

  Lemma L_ok_succ beta  : P beta -> P (Succ beta).
  Proof with auto with E0.
    intro H; red;  rewrite Succ_rw.
    destruct (E0_eq_dec beta Zero).
    -  subst; simpl; generalize (L_fin_ok 1); unfold L_fin.
       replace one with (fin 1); [simpl | trivial].
       intro; eapply L_spec_compat;  eauto.
       intros; rewrite L_eq2; auto with E0.
       rewrite Pred_of_Succ, L_zero_eqn; trivial.
    -  apply L_spec_compat  with (L_succ (L_ beta));
         auto.
       + apply L_succ_ok; auto.
         * apply cnf_ok; auto.
         * intro k; apply L_ge_S; auto.
       + unfold L_succ; intro n0; now autorewrite with L_rw.
  Qed. 

  Lemma L_ok_lim  alpha  :
    (forall beta,  (beta o< alpha)%e0 -> P beta) ->
    Limitb alpha -> P alpha.
  Proof with eauto with E0.
    unfold P; intros.
    apply L_spec_compat with (fun k =>  L_ (Canon alpha k) (S k)).
    -   generalize L_lim_ok; intro H1; unfold L_lim in H1.
       assert (H2 : limitb (cnf alpha)) by (now destruct alpha). 
       specialize (H1 (cnf alpha) cnf_ok H2 (fun k i => L_ (Canon alpha k) i)).
       apply H1; intro k; specialize (H (CanonS alpha  k)).
       assert  (H3: (CanonS alpha k o< alpha)%e0 ).
       { apply CanonS_lt;  now apply Limit_not_Zero. }
       apply H in H3; apply L_spec_compat with (L_ (CanonS alpha k)); auto.
    - intro n; rewrite (L_lim_eqn alpha); trivial.
  Qed.

  
  
  Lemma L_ok (alpha: E0) : P alpha.
  Proof with eauto with E0.
    apply well_founded_induction with Lt ...
    clear alpha; intros alpha IHalpha.
    destruct (Zero_Limit_Succ_dec alpha) as [[H | H] | H].
    - subst; apply L_ok0.
    - apply L_ok_lim; auto.
    - destruct H as [beta Hbeta]; subst; apply L_ok_succ.
      apply IHalpha; auto with E0.
  Qed.

  
End L_correct_proof.

Theorem L_correct alpha : L_spec (cnf alpha) (L_ alpha).
Proof. apply L_ok. Qed.


(** Comparison with Hardy's function H  *)

Theorem H_L_ alpha :
  forall i:nat,  (H_ alpha i <= L_ alpha (S i))%nat.
Proof with auto with E0.
  pattern alpha ; apply well_founded_induction with Lt ...
  clear alpha; intros alpha IHalpha i.
  destruct (Zero_Limit_Succ_dec alpha) as [[H | H] | H].
  - subst; rewrite H_eq1, L_zero_eqn; abstract lia.
  - rewrite H_eq3, L_lim_eqn ...
    apply Nat.lt_le_incl;
      apply Nat.lt_le_trans with (H_ (Canon alpha (S i)) (S i)).
    apply H_alpha_mono; auto with arith ...
    apply IHalpha ...
  -  destruct H as [beta e]; subst alpha;
       rewrite H_succ_eqn, L_succ_eqn ...
Qed.




Require Import Extraction.

Recursive Extraction L_.
