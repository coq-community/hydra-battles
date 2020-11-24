(**  * A notation system for ordinals less than  Gamma0 *)

(**   Pierre Casteran 
    LaBRI, Université Bordeaux 1, and LaBRI  (CNRS, UMR 5800)
     with a contribution by Evelyne Contejean 
*)


From Coq Require Import Arith List Lia  Compare_dec  Relations
     Wellfounded  Max RelationClasses.


From hydras.ordinals.Epsilon0 Require Import Epsilon0.
From hydras.ordinals.Prelude Require Import More_Arith Restriction.
From hydras.ordinals Require Import OrdinalNotations.Generic. 
From hydras.ordinals.rpo Require Import term  rpo.
From hydras.ordinals.Gamma0 Require Import T2.

Import Datatypes.

Set Implicit Arguments.


Lemma nf_a : forall a b n c, nf (gcons a b n c) -> nf a.
Proof.
  inversion_clear 1;auto.
Qed.

Lemma nf_b : forall a b n c, nf (gcons a b n c) -> nf b.
Proof.
  inversion_clear 1;auto.
Qed.

Lemma nf_c : forall a b n c, nf (gcons a b n c) -> nf c.
Proof.
  inversion_clear 1;auto with T2.
Qed.

Hint Resolve nf_a nf_b nf_c : T2.

Ltac nf_inv := ((eapply nf_a; eassumption)|| 
                (eapply nf_b; eassumption)|| 
                (eapply nf_c; eassumption)).




Lemma zero_lt_succ : forall alpha, zero t2< succ alpha.
Proof.
  destruct  alpha;simpl.
  - auto with T2.
  - case alpha1;case alpha2;auto with T2.
Qed.


Lemma not_lt_zero : forall alpha, ~ alpha t2< zero. 
Proof.
  red; inversion 1.
Qed.


Lemma lt_irr : forall alpha, ~ alpha t2< alpha.
Proof.
  induction alpha.
  - apply not_lt_zero. 
  -  red; inversion_clear 1.
     + case (IHalpha1 H0).
     + case (IHalpha2 H0).
     + case (IHalpha1 H0).
     + case (IHalpha1 H0).
     + case (Arith.Lt.lt_irrefl _ H0).
     + case IHalpha3; auto.
Qed.

Ltac lt_clean := 
  try (match goal with 
         [ineq : lt ?a zero |- _ ] => case (not_lt_zero ineq);auto
       |[ineq : Peano.lt ?a 0 |- _ ] => case (lt_n_O a);auto
       |[ref : lt ?a ?a |- _] => case (lt_irr ref);auto
       |[ref : Peano.lt ?a ?a |- _] => case (lt_irr ref);auto
       end).


Lemma le_zero_alpha : forall alpha, zero t2<= alpha.
Proof.
  intro alpha; case alpha; auto with T2.
Qed.

Lemma psi_le_cons : forall alpha beta n gamma,
    [alpha, beta] t2<=  gcons alpha beta n gamma.
Proof.
  intros;case n; auto with arith T2.
  case gamma;auto with arith T2.
Qed.

Hint Resolve psi_le_cons le_zero_alpha: T2.

Lemma le_psi_term_le : forall alpha beta, alpha t2<= beta ->
                                          psi_term alpha t2<= psi_term beta.
Proof.
  destruct 1.
  -  subst beta;auto with T2.
  -  generalize H;case alpha;simpl.
   + auto with T2.
   +  case beta.
    *  intros;lt_clean.
    * simpl;inversion_clear 1; auto with T2.  
Qed.


Lemma le_inv_nc : forall a b n c  n' c',
    gcons a b n c t2<= gcons a b n' c' -> (n<n')%nat \/ n=n' /\ c t2<= c'.
Proof.
  inversion_clear 1.
  injection H0;intros;right;auto with T2.
  inversion_clear H0; try lt_clean;auto with T2.
Qed.


Lemma lt_than_psi : forall a b n c a' b',
    gcons a b n c t2< [a',b'] ->
    [a,b]t2<[a',b']. 
Proof.
  inversion_clear 1;try lt_clean;auto with T2.
Qed.



(**  in order to establish trichotomy, we first use a measure on pair of
    terms *)

Section lemmas_on_length.
  Open Scope nat_scope.
  
  Lemma tricho_lt_2 : forall a1 a2 b1 b2 n1 n2 r1 r2,
      t2_length a1 + t2_length a2 < 
      t2_length (gcons a1 b1 n1 r1) +
      t2_length (gcons a2 b2 n2 r2).
  Proof.
    intros.
    apply plus_lt_compat; apply length_a. 
  Qed.


  Lemma tricho_lt_2' : forall a1 a2 b1 b2 n1 n2 r1 r2,
      t2_length b1 + t2_length (gcons a2 b2 0 zero)  < 
      t2_length (gcons a1 b1 n1 r1) +
      t2_length (gcons a2 b2 n2 r2).
    Proof.
    intros;apply plus_lt_le_compat.
    -  apply length_b.
    - cbn; intros; apply le_lt_n_Sm.
    match goal with 
      [ |- ?a <= ?b + ?c + ?d] => rewrite (plus_comm (b + c) d) end.
    apply le_plus_trans.
    replace (Max.max (t2_length b2) 0) with (t2_length b2).
    + destruct (Max.max_dec (t2_length a2) (t2_length b2)).   
      rewrite  e; repeat rewrite plus_0_r.
      *  apply plus_le_compat; apply le_max_l.
      * repeat rewrite plus_0_r.
         apply plus_le_compat;apply  max_le_regL;  apply le_max_l.
    + rewrite max_l; auto with arith.
  Qed.



  Lemma tricho_lt_3 : forall a1 a2 b1 b2 n1 n2 r1 r2,
      t2_length b1 + t2_length b2  <   
      t2_length (gcons a1 b1 n1 r1) +  t2_length (gcons a2 b2 n2 r2).
  Proof.
    intros;apply plus_lt_compat; apply length_b.
  Qed.


  Lemma tricho_lt_4 : forall a1 a2 b1 b2 n1 n2 r1 r2,
      t2_length a2 + t2_length a1 < 
      t2_length (gcons a1 b1 n1 r1) +
      t2_length (gcons a2 b2 n2 r2).
  Proof.
    intros; rewrite plus_comm;  apply plus_lt_compat; apply length_a. 
  Qed.

  Lemma tricho_lt_4' : forall a1 a2 b1 b2 n1 n2 c1 c2,
      t2_length (gcons a1 b1 0 c1) + t2_length b2  < 
      t2_length (gcons a1 b1 n1 c1) +
      t2_length (gcons a2 b2 n2 c2).
  Proof.
    intros; apply plus_le_lt_compat.
    - case n1; auto.
      intros;apply lt_le_weak;apply length_n; auto with arith.
    -  apply length_b.
  Qed.

  Lemma tricho_lt_5 : forall a1 a2 b1  n1 n2 c1 c2,
      t2_length a2 + t2_length a1  < 
      t2_length (gcons a1 b1 n1 c1) +
      t2_length (gcons a2 (gcons a1 b1 0 zero)  n2 c2).
    intros; rewrite plus_comm;apply plus_lt_compat; apply length_a.
  Qed.

  Lemma tricho_lt_7 : forall a1 b1  n1  c1 c2,
      t2_length c1 + t2_length c2 < 
      t2_length (gcons a1 b1 n1 c1) +
      t2_length (gcons a1 b1 n1 c2).
  Proof.
    intros;    apply plus_lt_compat;  apply length_c. 
  Qed.


End lemmas_on_length.

Hint Resolve tricho_lt_7 tricho_lt_5 tricho_lt_4 tricho_lt_4' tricho_lt_3 tricho_lt_2 tricho_lt_2 : T2.

Open Scope T2_scope.

Lemma tricho_aux (l: nat) : forall t t': T2,
      t2_length t + t2_length t' < l  ->
      {t t2< t'} + {t = t'} + {t' t2<  t}.
Proof.
  induction l.
  - intros; elimtype False. 
    inversion H.
  -  intros t t'; case t;case t'.
     + left;right;auto with T2.
     + left;left;constructor.
     + right;constructor.
     + intros t0 t1 n t2 t3 t4 n0 t5 H.
       assert (H0 :(t2_length t3 + t2_length t0 < l)%nat).
       { eapply lt_lt_Sn.
         eapply tricho_lt_2.
         eauto with T2. }
       case (IHl _ _ H0).
       *  destruct 1.
          assert (t2_length t4 + t2_length (gcons t0 t1 0 zero) < l)%nat.
          { eapply lt_lt_Sn.
            eapply tricho_lt_2'.
            eauto. }
          case (IHl _ _ H1).
          -- destruct 1.
             ++ left;left; constructor 2;auto with T2.
             ++  subst t4; right;  constructor 5;auto with T2.
          --  intro H2; right; constructor 4;auto with T2.
          --  subst t3;
                assert (H1: (t2_length t4 + t2_length t1 < l)%nat).
              {  eapply lt_lt_Sn.
                 eapply tricho_lt_3.
                 eauto with T2. }
              case (IHl _ _ H1).
              ++  destruct 1.
                  ** left;left; constructor 3. 
                     auto with T2.
                  **  subst t4; case (Compare_dec.lt_eq_lt_dec n0 n).
                      destruct 1.
                      { left;left; constructor 6.
                        auto with T2. }
                      subst n; assert (H2:(t2_length t5 + t2_length t2 < l)%nat).
                      eapply lt_lt_Sn.
                      eapply tricho_lt_7.
                      eauto with T2.
                      case (IHl _ _ H2).
                      destruct 1.
                      left;left; constructor 7;auto with T2.
                      subst t2; left;right;trivial.
                      intro H3; right;constructor 7;auto with T2.
                      right; constructor 6;auto with T2.
              ++ intro H2; right;constructor 3;auto with T2.
       *  intro H1;
            assert (H2:(t2_length t1 + t2_length (gcons t3 t4 0 zero) < l)%nat).
          --  eapply lt_lt_Sn.
              ++  eapply tricho_lt_2'.
              ++  rewrite plus_comm;  eauto with T2.
          --  case (IHl _ _ H2).
              ++ destruct 1.
                 ** right;  constructor 2;auto with T2.
                 **  subst t1; left;left;constructor 5;auto with T2.
              ++  left;left;constructor 4;auto with T2.
Defined.


Definition lt_eq_lt_dec (t t': T2) : {t t2< t'}+{t = t'}+{t' t2<  t}.
Proof.
  eapply tricho_aux.
  eapply lt_n_Sn.
Defined.


Definition lt_ge_dec : forall t t', {t t2< t'}+{t' t2<= t}.
  intros t t'; case (lt_eq_lt_dec t t').
  destruct 1 ;[left;auto with T2| right;auto with T2].
  auto with T2.
Defined.

Definition compare (t1 t2 : T2) : comparison := 
  match lt_eq_lt_dec t1 t2 with
  | inleft (left _) => Lt
  | inleft (right _) => Eq
  | inright _ => Gt
  end.

Fixpoint nfb (alpha : T2) : bool :=
  match alpha with
    zero => true
  | gcons a b n zero => andb (nfb a) (nfb b)
  | gcons a b n ((gcons a' b' n' c') as c) =>
    match compare [a', b'] [a, b] with
           Lt => andb (nfb a) (andb (nfb b) (nfb c))
           | _ => false
           end
end.

Compute compare (gcons 2 1 42 epsilon0) [2,2].

Compute nfb  (gcons 2 1 42 epsilon0).

Compute nfb (gcons 2 1 42 (gcons 2 2 4 epsilon0)).


(* introduces an hypothesis Hname for t t2< t', t = t', and t' t2< t
    (3 subgoals) *)

Ltac tricho t t' Hname := case (lt_eq_lt_dec t t');
                          [intros [Hname|Hname] | intro Hname].


Section trans_proof.
  Variables a1 b1 c1 a2 b2 c2 a3 b3 c3:T2.
  Variables n1 n2 n3:nat.

  Hypothesis H12 : gcons a1 b1 n1 c1 t2<  gcons a2 b2 n2 c2.
  Hypothesis H23 : gcons a2 b2 n2 c2 t2<  gcons a3 b3 n3 c3.

  Hypothesis induc : forall t t' t'', 
      (t2_length t + t2_length t' + 
       t2_length t'' < 
       t2_length (gcons a1 b1 n1 c1) +
       t2_length (gcons a2 b2 n2 c2) + 
       t2_length (gcons a3 b3 n3 c3))%nat  ->
      lt t t' -> lt t' t'' -> lt t t''.


  Lemma trans_aux :  gcons a1 b1 n1 c1 t2< gcons a3 b3 n3 c3.
  Proof with eauto with T2.
    inversion H12.
    -  inversion H23.
       +  constructor 2.
          * apply induc with a2 ...
            generalize (length_a  a1 b1 n1 c1).
            generalize (length_a  a2 b2 n2 c2).
            generalize (length_a  a3 b3 n3 c3).
            clear induc;lia.
          * assert (lt (gcons a2 b2 0 zero) (gcons a3 b3 0 zero))
              by auto with T2.
            apply induc with (gcons a2 b2 0 zero) ...
            generalize (length_b  a1 b1 n1 c1).
            generalize (length_psi a2 b2 n2 c2).
            generalize (length_psi a3 b3 n3 c3).
            clear induc; lia.
       +  subst a3; constructor 2 ...
          apply induc with (gcons a2 b2 0 zero).
          2:auto with T2.
          2:constructor 3;auto with T2.
          generalize (length_b a1 b1 n1 c1);
            generalize (length_psi a2 b2 n2 c2);
            generalize (length_psi a2 b3 n3 c3);
            clear induc;lia.
       +  tricho a1 a3 H20.
          * constructor 2 ...
            apply induc with (gcons a2 b2 0 zero).
            2:auto with T2.
            generalize (length_b a1 b1 n1 c1);
              generalize(length_psi a2 b2 n2 c2);
              generalize (length_psi a3 b3 n3 c3);
              clear induc;lia.
            constructor 4 ...  
          * clear H;subst a1; constructor 3.
            apply induc with (gcons a2 b2 0 zero) ...
            generalize (length_b a3 b1 n1 c1); 
              generalize (length_b a3 b3 n3 c3); 
              generalize (length_psi a2 b2 n2 c2);
              clear induc;lia. 
          * constructor 4 ...
            apply induc with (gcons a2 b2 0 zero) ...
            generalize (length_psi a1 b1 n1 c1); 
              generalize (length_psi a2 b2 n2 c2); 
              generalize (length_b a3 b3 n3 c3);clear induc;lia.
       +  tricho a1 a3 H20.
          * constructor 2 ...
            apply induc with  (gcons a2 b2 0 zero) ...
            subst b3;
              generalize (length_b a1 b1 n1 c1); 
              generalize (length_psi a2 b2 n2 c2); 
              generalize (length_psi a3 (gcons a2 b2 0 zero) n3 c3);
              clear induc;lia. 
          * clear H15 H9 H11 H17 H18 ;subst a3; constructor 3 ...
          * constructor 4 ...
       + clear H9 H11 H4 H5; subst a3  b3; constructor 2 ...
       + clear H9 H11 H4 H5; subst a3  b3; constructor 2 ...
    -    clear H H1 H2 H3 H5 H6 H7 beta1 beta2 gamma1 gamma2.
         inversion H23.
         + constructor 2 ...
           apply induc with b2 ...
           generalize (length_b a1 b1 n1 c1); 
             generalize (length_b a2 b2 n2 c2); 
             generalize (length_psi a3 b3 n3 c3);clear induc;lia. 
         +  constructor 3 ...
            eapply induc with b2 ...
            generalize (length_b a1 b1 n1 c1); 
              generalize (length_b a2 b2 n2 c2); 
              generalize (length_b a3 b3 n3 c3);clear induc;lia. 
         +  constructor 4 ...
            apply induc with (gcons a2 b2 0 zero) ...
            pattern a2 at 1;rewrite <- H4.
            generalize (length_psi a1 b1 n1 c1); 
              generalize (length_psi a2 b2 n2 c2); 
              generalize (length_b a3 b3 n3 c3);clear induc;lia. 
         +  clear H;subst a2; constructor 4 ...
         + rewrite <- H7; constructor 3 ...
         + rewrite <- H7; constructor 3 ...
    - inversion H23 ...
      + assert (H20 :lt (gcons a1 b1 0 zero) (gcons a3 b3 0 zero)). {
          apply induc with b2 ...
          generalize (length_psi  a1 b1 n1 c1).
          generalize (length_b a2 b2 n2 c2).
          generalize (length_psi a3 b3 n3 c3);
            clear induc; lia. }
        inversion_clear H20 ...
        * inversion H21.
        * inversion H21.
      + subst a3; constructor 4 ...
        apply induc with b2 ...
        generalize (length_psi a1 b1 n1 c1);
          generalize (length_b a2 b2 n2 c2);
          generalize (length_b a2 b3 n3 c3);clear induc;lia.
      +  constructor 4 ...
         apply induc with a2 ...
         generalize (length_a a1 b1 n1 c1);
           generalize (length_a a2 b2 n2 c2);
           generalize (length_a a3 b3 n3 c3);clear induc; lia.
         apply induc with (gcons a2 b2 0 zero) ...
         generalize (length_psi a1 b1 n1 c1);
           generalize (length_psi a2 b2 n2 c2);
           generalize (length_b a3 b3 n3 c3);clear induc; lia.
      +  constructor 4 ...
         apply induc with a2 ...
         generalize (length_a a1 b1 n1 c1); 
           generalize (length_a a2 b2 n2 c2); 
           generalize (length_a a3 b3 n3 c3);clear induc;lia.
      +  clear H9 H11; subst b3; subst a3; constructor 4 ...
      + clear H9 H11;subst b3;subst a3; constructor 4 ...
    -    subst b2;  inversion H23 ...
         + inversion_clear H17 ...
           inversion H18.
           inversion H18.
         + subst a3; constructor 4 ...
         + constructor 4 ...
           apply induc with a2 ...
           generalize (length_a a1 b1 n1 c1); 
             generalize (length_a a2 (gcons a1 b1 0 zero) n2 c2); 
             generalize (length_a a3 b3 n3 c3);clear induc;lia.
           apply induc with (gcons a2 (gcons a1 b1 0 zero) 0 zero) ...
           generalize (length_psi  a1 b1 n1 c1); 
             generalize (length_psi a2 (gcons a1 b1 0 zero) n2 c2); 
             generalize (length_b a3 b3 n3 c3) ;clear induc;lia.
         + constructor 4 .
           apply induc with a2 ...
           generalize (length_a a1 b1 n1 c1); 
             generalize (length_a a2 (gcons a1 b1 0 zero) n2 c2); 
             generalize (length_a a3 b3 n3 c3);clear induc;lia.
           constructor 5;auto with T2.
         + subst a3.
           constructor 5.
           auto with T2.
         + subst a3.
           constructor 5;auto with T2.
    - subst a2; subst b2.
      inversion H23 ...
      + subst a3 b3;  constructor 6; eauto with T2 arith.
      + subst b3;subst a3;subst n3 ; constructor 6 ...
    - clear H H1;subst a1;subst b1 n2.
      inversion H23 ...
      constructor 7;   apply induc with c2 ...
      generalize (length_c a2 b2 n1 c1); 
        generalize (length_c a2 b2 n1 c2); 
        generalize (length_c a3 b3 n3 c3);clear induc;lia.
  Qed.


End trans_proof.

Lemma lt_trans0 : forall n, 
    forall t1 t2 t3, 
      (t2_length t1 + t2_length t2 + t2_length t3  < n)%nat -> 
      lt t1 t2 -> lt t2 t3 ->  lt t1 t3.
Proof.
  induction n.
  -  inversion 1.
  - destruct t1; destruct t2; destruct t3.
    + intros; trivial.
    + inversion 2.
    +  inversion 3.
    + auto with T2.
    + inversion 2.
    +  inversion 3.
       inversion H0.
    + inversion 3.
    + intros;   eapply trans_aux.
      * eexact H0.
      *  auto with T2.
      * intros; apply IHn with t'; auto with T2.
        --   lia.
Qed.

Theorem lt_trans : 
  forall t1 t2 t3, t1 t2< t2 -> t2 t2< t3 -> t1 t2< t3.
Proof.
  intros;
    apply lt_trans0 with (S (t2_length t1 + t2_length t2 + t2_length t3)) t2;
    auto with T2 arith.
Qed.

Theorem le_lt_trans alpha beta gamma:  alpha t2<= beta -> 
                                       beta t2< gamma -> 
                                       alpha t2< gamma.
Proof.
  destruct 1.
  - subst alpha;auto with T2.
  - intros; eapply lt_trans;eauto with T2.
Qed.

Theorem  lt_le_trans  alpha beta gamma :
  alpha t2< beta ->  beta t2<= gamma ->  alpha t2< gamma.
Proof.
  destruct 2.
  -  subst beta;auto with T2.
  -  eapply lt_trans;eauto with T2.
Qed.

Theorem le_trans : forall alpha beta gamma, alpha t2<= beta ->
                                            beta t2<= gamma ->
                                            alpha t2<= gamma.
Proof.
  destruct 1.
  -  subst beta;auto.
  -  intros;right;eapply lt_le_trans;eauto.
Qed.


Lemma psi_lt_head : forall alpha beta n gamma  alpha' beta' n' gamma',
    [alpha, beta] t2<  [alpha', beta'] ->
    gcons alpha beta n gamma t2<  gcons alpha' beta' n' gamma'.
Proof.
  inversion 1.
  - constructor 2;auto with T2.
  -  constructor 3;auto with T2.
  -  constructor 4;auto with T2.
  -  constructor 5;auto with T2.
  -  inversion H1.
  -  lt_clean. 
Qed.

Lemma nf_inv_tail : forall a b n c , nf (gcons a b n c) ->
                                     c t2< [a,b].
Proof.
  inversion_clear 1.
  - auto with T2.
  - apply psi_lt_head;auto with T2.
Qed.


Theorem lt_beta_psi : forall beta alpha, beta t2< [alpha, beta].
Proof.
  induction beta.
  -  auto with T2.
  -  intro alpha;
       assert (H : beta2 t2< [alpha, (gcons beta1 beta2 n beta3)]).
     { assert ([alpha, beta2] t2< [alpha, (gcons beta1 beta2 n beta3)]).
       {  constructor 3. 
          apply lt_le_trans with [beta1, beta2]; auto with T2.
       }
       eapply lt_trans; eauto with T2.
     }
     tricho beta1 alpha H0; auto with T2.
     +  subst alpha; constructor 3.
        apply lt_le_trans with [beta1, beta2];auto with T2.
     + case (psi_le_cons beta1 beta2 n beta3).
       * intro;  pattern (gcons beta1 beta2 n beta3) at 2;
           rewrite <- H1.
         unfold psi; constructor 5; auto with T2.
       * unfold psi; constructor 4; auto with T2. 
Qed.


Lemma lt_beta_cons :  forall alpha beta n gamma, 
    beta t2< gcons alpha beta n gamma.
Proof.
  intros;eapply lt_le_trans.
  - apply lt_beta_psi.
  - eapply psi_le_cons.
Qed.


Theorem lt_alpha_psi : forall alpha beta, alpha t2< [alpha, beta].
Proof.
  induction alpha.
  - unfold psi;auto with T2.
  -  intros beta; constructor 2.
     + apply lt_le_trans with [alpha1,alpha2];auto with T2.
     + apply lt_le_trans with [ alpha1,alpha2];auto with T2.
       * apply lt_beta_psi.
       * right;constructor 2.
         --   apply lt_le_trans with [alpha1,alpha2];auto with T2.
         --  apply lt_le_trans with [ alpha1,alpha2];auto with T2.
             ++  apply lt_beta_psi.
             ++ right;  constructor 2.
                **  apply lt_le_trans with [ alpha1,alpha2];auto with T2.
                **  apply lt_trans with [alpha2, beta];auto with T2.
                    constructor 2.
                    apply lt_beta_cons.
                    apply lt_beta_psi.
Qed.

Lemma lt_alpha_cons :  forall alpha beta n gamma, 
    alpha t2< gcons alpha beta n gamma.
Proof.
  intros;eapply lt_le_trans.
  - apply lt_alpha_psi.
  - eapply psi_le_cons.
Qed.

Hint Resolve lt_beta_cons lt_alpha_cons : T2.

Lemma le_cons_tail alpha beta n gamma gamma':
  gamma t2<= gamma' -> 
  gcons alpha beta n gamma t2<=  gcons alpha beta n gamma'.
Proof.
  destruct 1.
  -  subst gamma';left;auto with T2.
  -  right;auto with T2.
Qed.


(** ** terms in normal form *)



Lemma nf_fin_inv : forall gamma n, nf (gcons zero zero n gamma) -> 
                                      gamma = zero.
Proof.
  inversion 1;auto with T2.
  inversion H4; lt_clean; auto with T2.
Qed.

Lemma lt_tail0: forall c, nf c -> c <> zero -> gtail c t2< c.     
Proof.
  induction c.
  -  now destruct 2.
  - cbn; generalize IHc3; case c3;  auto with T2.
  +  intros; apply psi_lt_head;  inversion_clear H;  auto with T2.
Qed.


Lemma lt_tail: forall a b n c, nf (gcons a b n c) ->  c t2< gcons a b n c. 
Proof.
  intros a b n c H; change c with (gtail (gcons a b n c)). 
  apply lt_tail0.
   + cbn;auto with T2.
   +  discriminate. 
Qed.

Lemma le_one_cons : forall a b n c, one t2<= gcons a b n c.
Proof.
 
  intros. apply le_trans with [a,b];auto with T2.
  case a; case b; auto with T2.
Qed.

Hint Resolve le_one_cons : T2.

Lemma fin_lt_omega : forall n, fin  n t2<  omega.
Proof.
  destruct n;compute;auto with T2.
Qed.

Lemma omega_lt_epsilon0 : omega t2<  epsilon0.
Proof.
  compute; auto with T2.
Qed.

Lemma omega_lt_epsilon : forall alpha, omega t2< epsilon alpha.
Proof.
  compute;auto with T2.
Qed.


Lemma lt_one_inv : forall alpha, alpha t2< one -> alpha = zero.
Proof.
  inversion 1; lt_clean.
  auto with T2.
Qed.

Lemma lt_cons_omega_inv : forall alpha beta n gamma, 
    gcons alpha beta n gamma t2< omega ->
    nf (gcons alpha beta n gamma) ->
    alpha = zero /\ beta = zero /\ gamma = zero.
Proof.
  inversion_clear 1; lt_clean.
  - replace beta with zero.
    +  inversion 1; lt_clean;auto with T2.
       inversion  H5; lt_clean.
    + inversion H0;lt_clean;auto with T2.
  -  inversion H1; lt_clean;auto with T2.
Qed.

Lemma lt_omega_inv alpha :  nf alpha -> alpha t2< omega ->
                            {n:nat | alpha = fin n}.
Proof.
  destruct alpha.
  -  exists 0; reflexivity.
  - intros H H0;  case (lt_cons_omega_inv H0);auto with T2.
    destruct 2;intros; exists (S n);auto with T2.
    cbn; subst ; auto with T2.
Qed.

Lemma lt_omega_is_fin alpha:  nf alpha -> alpha t2< omega -> 
                                         is_finite alpha.
Proof.
  intros  N_alpha H; case (lt_omega_inv N_alpha H).
  destruct x; intro e;rewrite e; simpl; constructor.
Qed.

Theorem lt_compat (n p : nat):   fin n t2<  fin p -> 
                                (n < p)%nat.
Proof.
  destruct n;cbn.
  -  destruct p.
     + inversion 1.
     + auto with T2 arith.
  -  destruct p;cbn.
     +  inversion 1.
     +  inversion_clear 1;try lt_clean;auto with arith T2.
Qed.

Theorem lt_compatR (n p : nat):  (n <p)%nat -> 
                                 fin n t2< fin p.
Proof.
  destruct n; cbn.
  -   destruct p.
      + inversion 1.
        + cbn; auto with T2.
  -  destruct p.
   +  intros;lt_clean.
   +  simpl; auto with arith T2.
Qed.

Lemma finite_is_finite : forall n, is_finite (fin n).
Proof.
  destruct n;cbn;constructor.
Qed.

Lemma is_finite_finite : forall alpha, is_finite alpha ->
                                       {n : nat | alpha = fin n}.
Proof.
  destruct 1.
 -  exists 0;cbn;auto with T2.
 -  exists (S n);cbn;auto with T2.
Qed.


Lemma compare_reflect alpha beta : match compare alpha beta with
                                     | Lt => alpha t2< beta 
                                     | Eq => alpha = beta
                                     | Gt => beta t2< alpha
                                     end.
Proof.
  unfold compare.
  intros; case (lt_eq_lt_dec alpha beta);auto.
  destruct s;auto with T2.
Qed.


Lemma compare_correct alpha beta :
  CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
              (compare alpha beta).
Proof.
  generalize (compare_reflect alpha beta).
  destruct (compare alpha beta); now constructor. 
Qed.


Lemma compare_Lt : forall alpha beta, compare alpha beta = Lt -> 
                                         alpha t2< beta.
Proof.
  intros alpha beta; destruct (compare_correct alpha beta);
    trivial; discriminate. 
Qed.

(**  Compare with the proof of [T2.Ex6] *)

Example Ex6 : gcons 1 0 12 omega t2< [0,[2,1]].
Proof. now apply compare_Lt. Qed.

Lemma compare_Eq : forall alpha beta, compare alpha beta = Eq -> 
                                         alpha = beta.
Proof.
  intros alpha beta; destruct (compare_correct alpha beta); trivial;
    discriminate. 
Qed.

Lemma compare_Gt : forall alpha beta, compare alpha beta = Gt ->  
                                         beta t2< alpha.
Proof.
  intros alpha beta; destruct (compare_correct alpha beta); trivial;
    discriminate. 
Qed.

Arguments compare_Gt [alpha beta].
Arguments compare_Lt [alpha beta].
Arguments compare_Eq [alpha beta].


Hint Resolve compare_Eq compare_Lt compare_Gt : T2.

Lemma compare_rw_lt  alpha beta : alpha t2< beta ->
                                  compare alpha beta = Lt.
Proof.
  intros; generalize (compare_reflect alpha beta). 
  case (compare alpha beta); trivial.
  -  intro;subst beta;case (lt_irr H);auto with T2.
  - intro; case (lt_irr (alpha:=alpha)).  
    eapply lt_trans;eauto with T2.
Qed.

Lemma compare_rw_eq  alpha beta:  alpha = beta ->
                                  compare alpha beta = Eq.
  intros; subst beta; generalize (compare_reflect alpha alpha);
    case (compare alpha alpha); trivial.
  all : intro H0; destruct (lt_irr H0).
Qed.

Lemma compare_rw_gt  alpha beta:  beta t2< alpha ->
                                  compare alpha beta = Gt.
  intros; generalize (compare_reflect alpha beta). 
  case (compare alpha beta); trivial.
  -  intro H0;subst beta;case (lt_irr H).
  - intro; case (lt_irr (alpha:=alpha));
      eapply lt_trans;eauto with T2.
Qed.



(**  plus is defined here, because it requires decidable comparison *)

Fixpoint plus (t1 t2 : T2) {struct t1}:T2 :=
  match t1,t2 with
  |  zero, y  => y
  |  x, zero => x
  |  gcons a b n c, gcons a' b' n' c' =>
     (match compare (gcons a b 0 zero)
                    (gcons a' b' 0 zero) with
      | Lt => gcons a' b' n' c'
      | Gt => gcons a b n (c + gcons a' b' n' c')
      | Eq  => gcons a b (S(n+n')) c'
      end)
  end
where "alpha + beta" := (plus alpha beta): T2_scope.

Example Ex7 : 3 + epsilon0 = epsilon0.
Proof. trivial. Qed.



Lemma plus_alpha_0 : forall alpha:T2 ,  alpha + zero = alpha.
Proof.
  intro alpha; case alpha ;trivial.
Qed.

Lemma lt_succ alpha: alpha t2< succ alpha.
Proof.
  induction alpha;simpl;auto with T2.
  case alpha1;auto with arith T2.
  case alpha2; auto with arith T2.
Qed.

Theorem lt_succ_le : forall a b,   a t2< b -> nf b -> 
                                  succ a t2<= b.
Proof.
  induction a.
  - inversion 1; cbn;  auto with T2. 
  -  generalize IHa3; case a1; case a2.
   + cbn; inversion 2.
     *  right; constructor 2.
      --  auto with T2.
      --  auto with T2.
     *   right;constructor 3;auto with T2.
     * lt_clean.
     *  lt_clean.
     *  inversion H5.
        case gamma2.
        -- left;auto with T2.
        --  right;auto with T2.
        -- right;constructor 6.
         auto with arith T2.
     *  inversion 1.
        -- subst gamma2; inversion H5.
        -- inversion H11.
           inversion H17.
           inversion H16.
           inversion H24.
           inversion H16.
           inversion H16.
     + cbn; intros t t0 n0 t1 IHa0 b H H0;  inversion H.
       * right;constructor 2;auto with T2.
       * right;constructor 3;auto with T2.
       * inversion H5.
         inversion H5.
         inversion H6.
       * inversion H6.
       * inversion H6.
         right;constructor 6.
         auto with arith T2.
         right;constructor 6.
         auto with arith T2.
       * apply le_cons_tail.
         apply IHa0; auto.
         subst b;  inversion H0;auto with T2.
     + cbn; intros;  inversion H; auto.
       * right;constructor 2;auto with T2.
       * right;constructor 3;auto with T2.
       * right;constructor 4; auto.
       * right;constructor 5;auto with T2.
       * right;constructor 6;auto with T2.
       *  apply le_cons_tail;auto with T2.
          apply IHa0;auto with T2.
          subst b; inversion H0.
          constructor.
          auto with T2.
     +   intros; cbn ;  inversion H.
         * right;constructor 2;auto with T2.
         *  right;constructor 3;auto with T2.
         *  right;constructor 4;auto with T2.
         *  right;constructor 5;auto with T2.
         *  right; constructor 6;auto with T2. 
         *  apply le_cons_tail;auto with T2.
            -- apply IHa0;auto with T2.
            ++ subst b;  inversion H0;  auto with T2.
Qed.

Lemma succ_lt_le : forall a b, nf a -> nf b -> a t2< succ b -> a t2<= b.
 Proof.
  intros.
  tricho a b H2; auto with T2.
  -  generalize (lt_succ_le H2 H); intro; case (lt_irr (alpha:=succ b)).
     eapply le_lt_trans;eauto with T2.
Qed.


Lemma succ_of_cons : forall a b n c, zero t2< a \/ zero t2< b ->
                                     succ (gcons a b n c)= gcons a b n (succ c).
Proof.
  destruct a;destruct b;simpl;auto with T2.
  destruct 1 as [H|H];inversion H.
Qed.


(** * Well-foundedness (with rpo) (Evelyne Contejean) *)

Inductive subterm : T2 -> T2 -> Prop :=
| subterm_a : forall a b n c, subterm a (gcons  a b n c)
| subterm_b : forall a b n c, subterm b (gcons a b n c)
| subterm_c : forall a b n c, subterm c (gcons a b n c)
| subterm_trans : forall t t1 t2, subterm t t1 -> subterm t1 t2 ->
                                  subterm t t2.

Lemma nf_subterm alpha beta : subterm alpha beta ->
                              nf beta ->  nf alpha.
Proof.
  induction 1; intros; try nf_inv; auto.
Qed.

Theorem subterm_lt alpha beta:  subterm alpha beta -> nf beta ->
                                alpha t2< beta.
Proof.
  induction 1;auto with T2.
 -  intro;apply lt_tail;auto with T2.
 -  intro; apply lt_trans with t1;auto with T2.
  eapply IHsubterm1; eapply nf_subterm;eauto with T2.
Qed.


Ltac subtermtac :=
  match goal with 
    [|- subterm ?t1 (gcons ?t1 ?t2 ?n ?t3)] =>
    constructor 1
  | [|- subterm ?t2 (gcons ?t1 ?t2 ?n ?t3)] =>
    constructor 2
  | [|- subterm ?t3 (gcons ?t1 ?t2 ?n ?t3)] =>
    constructor 3
  | [|- subterm ?t4 (gcons ?t1 ?t2 ?n ?t3)] =>
    ((constructor 4 with t1; subtermtac)     ||
     (constructor 4 with t2; subtermtac)       ||
     (constructor 4 with t3; subtermtac))
  end.


Module  Gamma0_sig <: Signature.

  Inductive symb0 : Set := nat_0 | nat_S | ord_zero | ord_psi | ord_cons.

  Definition symb := symb0.

  Lemma eq_symbol_dec : forall f1 f2 : symb, {f1 = f2} + {f1 <> f2}.
  Proof.
    intros; decide equality.
  Qed.

  (** The arity of a symbol contains also the information about built-in theories as in CiME *)

  
  Inductive arity_type : Set :=
  | AC : arity_type
  | C : arity_type
  | Free : nat -> arity_type.

  Definition arity : symb -> arity_type :=
    fun f => match f with
             | nat_0 => Free 0
             | ord_zero => Free 0
             | nat_S => Free 1
             | ord_psi => Free 2
             | ord_cons => Free 3
             end.

End Gamma0_sig.


(** ** Module Type Variables. 
 There are almost no assumptions, except a decidable equality. *)


Module Vars <: Variables.

  Inductive empty_set : Set := .
  Definition var := empty_set.

  Lemma eq_variable_dec : forall v1 v2 : var, {v1 = v2} + {v1 <> v2}.
  Proof.
    intros; decide equality.
  Qed.

End Vars.

Module  Gamma0_prec <: Precedence.

  Definition A : Set := Gamma0_sig.symb.
  Import Gamma0_sig.

  Definition prec : relation A :=
    fun f g => match f, g with
               | nat_0, nat_S => True
               | nat_0, ord_zero => True
               | nat_0, ord_cons => True
               | nat_0, ord_psi  => True
               | ord_zero, nat_S => True
               | ord_zero, ord_cons => True
               | ord_zero, ord_psi => True
               | nat_S, ord_cons => True
               | nat_S, ord_psi => True
               | ord_cons, ord_psi => True
               | _, _ => False
               end.


  Inductive status_type : Set :=
  | Lex : status_type
  | Mul : status_type.

  Definition status : A -> status_type := fun f => Lex.

  Lemma prec_dec : forall a1 a2 : A, {prec a1 a2} + {~ prec a1 a2}.
  Proof.
    intros a1 a2; destruct a1; destruct a2;
      ((right; intro; contradiction)||(left;simpl;trivial)).
  Qed.

  Lemma prec_antisym : forall s, prec s s -> False.
  Proof.
    intros s; destruct s; simpl; trivial.
  Qed.

  Lemma prec_transitive : transitive A prec.
  Proof.
    intros s1 s2 s3; destruct s1; destruct s2; destruct s3;
      simpl; intros; trivial; contradiction.
  Qed.

End Gamma0_prec.

Module Gamma0_alg <: Term := term.Make (Gamma0_sig) (Vars).
Module Gamma0_rpo <: RPO := rpo.Make (Gamma0_alg) (Gamma0_prec).

Import Gamma0_alg  Gamma0_rpo  Gamma0_sig.


Fixpoint nat_2_term (n:nat) : term :=
  match n with 0 => (Term nat_0 nil)
          | S p => Term nat_S ((nat_2_term p)::nil)
  end.



(** ** Every (representation of a) natural number is less than
 a non zero ordinal *)

Lemma nat_lt_cons : forall (n:nat) t p  c ,
    rpo (nat_2_term n) 
        (Term ord_cons (t::p::c::nil)).
Proof.
  induction n;simpl.
  -  constructor 2.
     +   simpl; trivial.
     +  destruct 1.
  - constructor 2.
   +  simpl; trivial.
   + inversion_clear 1.
    *  subst s';apply IHn.
    *  case H0.
Qed.


Lemma nat_lt_psi : forall (n:nat) a b, rpo (nat_2_term n) 
                                           (Term ord_psi (a::b::nil)).
Proof.
  induction n;simpl.
  -  constructor 2.
   +  simpl; trivial.
   +  destruct 1.
  - constructor 2.
    +  simpl; trivial.
    +  inversion_clear 1.
       *  subst s';apply IHn.
       *  destruct H0.
Qed.

Theorem rpo_trans : forall t t1 t2, rpo t t1 -> rpo t1 t2 -> rpo t t2.
  intros; case (rpo_closure t2 t1 t);eauto with T2.
Qed.


Fixpoint T2_2_term (a:T2) : term := 
  match a with
    zero => Term ord_zero nil
  |gcons a b 0 zero => Term ord_psi (T2_2_term a :: T2_2_term b ::nil)
  |gcons a b n c =>
   Term ord_cons (Term ord_psi
                       (T2_2_term a :: T2_2_term b ::nil) ::nat_2_term n ::
                       T2_2_term c::nil)
  end.

Fixpoint T2_size (o:T2):nat :=
  match o with zero => 0
          | gcons a b n c => S (T2_size a + T2_size b + n + T2_size c)%nat
  end.


Lemma T2_size1 : forall a b n c, (T2_size zero < T2_size (gcons a b n c))%nat.
Proof.
  simpl;auto with T2 arith.
Qed.


Lemma T2_size2 : forall a b n c , (T2_size a < T2_size (gcons a b n c))%nat.
Proof.
  simpl; auto with arith T2.
Qed.


Lemma T2_size3 : forall a b n c , (T2_size b < T2_size (gcons a b n c))%nat.
Proof.
  simpl; auto with arith T2.
Qed.

Lemma T2_size4 : forall a b n c , (T2_size c < T2_size (gcons a b n c))%nat.
Proof.
  simpl; auto with arith T2.
Qed.



Hint Resolve T2_size1 T2_size2 T2_size3 T2_size4 : T2.


(** let us recall subterm properties on T2 *)


Lemma lt_subterm1 : forall a a'  n'  b' c', a t2< a' ->
                                            a t2< gcons a'  b' n' c'.
Proof.
  intros; apply lt_trans with (gcons a b' n' c');auto with T2 .
Qed.

Hint Resolve nat_lt_cons lt_subterm1 : T2.


Lemma nat_2_term_mono : forall n n', (n < n')%nat -> 
                                     rpo (nat_2_term n) (nat_2_term n').
Proof.
  induction 1.
  -  simpl; eapply Subterm.
     +  eleft; esplit.
     + constructor.
  - cbn; eapply Subterm.
    +  eleft;  esplit.
    + constructor; auto with T2.
Qed.


Lemma T2_size_psi : forall a b n c , 
    (T2_size [a,b] <= T2_size (gcons a b n c))%nat.
Proof.
  simpl; auto with arith T2; intros;lia.
Qed.


(* *** Lemmas for rpo *)

Lemma rpo_2_2 : forall ta1 ta2 tb1 tb2 ,
    rpo ta1 ta2 ->
    rpo tb1 (Term ord_psi (ta2:: tb2::nil)) ->
    rpo (Term ord_psi (ta1:: tb1 ::nil))
        (Term ord_psi (ta2:: tb2 ::nil)).
Proof.
  intros; apply Top_eq_lex.
  - cbn; auto with T2.
  - left.
    +  auto with T2.
    +  auto with T2.
  -   inversion_clear 1; try subst s'.
   +  apply rpo_trans with ta2;auto with T2.
      eapply Subterm; [| eleft].
      now left.

  +  destruct H2.
     * subst s'; auto with T2.
     * case H1.
Qed.


Lemma rpo_2_3 : forall ta1 ta2 tb1 tb2 n1 tc1,
    rpo ta1 ta2 ->
    rpo tb1 (Term ord_psi (ta2:: tb2::nil)) ->
    rpo tc1 (Term ord_psi (ta1:: tb1::nil)) ->
    rpo (Term ord_cons ((Term ord_psi (ta1:: tb1 ::nil))
                          ::(nat_2_term n1)::tc1::nil))
        (Term ord_psi (ta2:: tb2 ::nil)).
Proof.
  intros; apply Top_gt.
  - cbn;auto with T2.
  - inversion_clear 1.
    +  subst s';  apply rpo_2_2;auto with T2.
    + destruct H3 as [|[|[]]]; unfold In in H2; try subst s'.
      * apply nat_lt_psi.
      * apply rpo_trans with (Term ord_psi (ta1 :: tb1 :: nil));auto with T2.
        apply rpo_2_2;auto with T2.
Qed.

Lemma rpo_2_1 : forall ta1 ta2 tb1 tb2 n1 n2 tc1 tc2,
    rpo ta1 ta2 ->
    rpo tb1 (Term ord_psi (ta2:: tb2::nil)) ->
    rpo tc1 (Term ord_psi (ta1:: tb1::nil)) ->
    rpo (Term ord_cons
              ((Term ord_psi (ta1:: tb1 ::nil))::(nat_2_term n1) ::tc1::nil))
        (Term ord_cons ((Term ord_psi (ta2:: tb2 ::nil))
                          ::(nat_2_term n2) ::tc2::nil)).
Proof.
  intros;  apply rpo_trans with (Term ord_psi (ta2 :: tb2 :: nil)).
  -  apply rpo_2_3;auto with T2.
  -  eapply Subterm;[| eleft].
     left;auto with T2.
Qed.

Lemma rpo_2_4 : forall ta1 ta2 tb1 tb2  n2  tc2,
    rpo ta1 ta2 ->
    rpo tb1 (Term ord_psi (ta2:: tb2::nil)) ->
    rpo (Term ord_psi (ta1:: tb1 ::nil))
        (Term ord_cons
              ((Term ord_psi 
                     (ta2:: tb2 ::nil)):: (nat_2_term n2) ::tc2::nil)).
Proof.
  intros;  apply rpo_trans with (Term ord_psi (ta2 :: tb2 :: nil)). 
 -  apply rpo_2_2;auto with T2.
 -  eapply Subterm.
  + eleft; reflexivity.
  + left.
Qed.

Lemma rpo_3_2 : forall ta1  tb1 tb2 ,
    rpo tb1 tb2 ->
    rpo (Term ord_psi (ta1:: tb1 ::nil))
        (Term ord_psi (ta1:: tb2 ::nil)).
Proof.
  intros;  apply Top_eq_lex.
  -  cbn; auto with T2.
  -  right; left; auto with T2.
  -  inversion_clear 1; try subst s'.
   +  eapply Subterm.
    *  eleft; reflexivity.
   *  left; destruct H1; unfold In in H; try subst s'.
   + eapply rpo_trans with tb2;auto with T2.
    * inversion_clear H1; subst; auto.
      inversion H0.
  * eapply Subterm; [| eleft].
    right; now left.
Qed.


Lemma rpo_3_3 : forall ta1  tb1 tb2 n1 tc1,
    rpo tb1 tb2 ->
    rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
    rpo (Term ord_cons
              ((Term ord_psi (ta1:: tb1 ::nil))::(nat_2_term n1) ::tc1::nil))
        (Term ord_psi (ta1:: tb2 ::nil)).
Proof.
  intros; apply Top_gt.
  - cbn; auto with T2.
  -  inversion_clear 1; try subst s'.
   +  apply rpo_3_2;auto with T2.
   + destruct H2 as [<-|[<-|[]]].
    * apply nat_lt_psi.
    * apply rpo_trans with (Term ord_psi (ta1 :: tb1 :: nil)).
     --  auto with T2.
     --  apply rpo_3_2;auto with T2.
Qed.

Lemma rpo_3_1 : forall ta1  tb1 tb2 n1 n2 tc1 tc2,
    rpo tb1 tb2 ->
    rpo tc1 (Term ord_psi (ta1:: tb1::nil)) ->
    rpo (Term ord_cons
              ((Term ord_psi (ta1:: tb1 ::nil))::(nat_2_term n1) ::tc1::nil))
        (Term ord_cons
              ((Term ord_psi (ta1:: tb2 ::nil))::(nat_2_term n2) ::tc2::nil)).
Proof.
  intros;  apply rpo_trans with  (Term ord_psi (ta1 :: tb2 :: nil)).
  -  apply rpo_3_3;auto with T2.
  -  eapply Subterm.
   +  now eleft.
   + left;auto with T2.
Qed.


Lemma rpo_3_4 : forall ta1  tb1 tb2  n2  tc2,
    rpo tb1 tb2 ->
    rpo (Term ord_psi (ta1:: tb1 ::nil))
        (Term ord_cons 
              ((Term ord_psi (ta1:: tb2 ::nil))::
                                               (nat_2_term n2) ::tc2::nil)).
Proof.
  intros; apply rpo_trans with  (Term ord_psi (ta1 :: tb2 :: nil)).
  -  apply rpo_3_2;auto with T2.
  -  eapply Subterm.
     + now eleft.
     + left;auto with T2.
Qed.


Lemma rpo_4_2 : forall ta1 ta2  tb1 tb2 ,
    rpo (Term ord_psi (ta1:: tb1 ::nil)) tb2 ->
    rpo (Term ord_psi (ta1:: tb1 ::nil))
        (Term ord_psi (ta2:: tb2 ::nil)).
Proof.
  intros; apply rpo_trans with tb2;auto with T2.
  eapply Subterm.
  -  eright;eleft; reflexivity.
  -  left.
Qed.


Lemma rpo_4_3 : forall ta1  ta2 tb1 tb2 n1 tc1,
    rpo (Term ord_psi (ta1:: tb1 ::nil)) tb2 ->
    rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
    rpo (Term ord_cons
              ((Term ord_psi (ta1:: tb1 ::nil))::
                                               (nat_2_term n1) ::tc1::nil))
        (Term ord_psi (ta2:: tb2 ::nil)).
Proof.
  intros; apply Top_gt.
  -  cbn;auto with T2.
  -  inversion_clear 1; try subst s'.
   +  apply rpo_4_2;auto with T2.
   + destruct H2 as [<-|[<-|[]]].
     *  apply nat_lt_psi.
     *  apply rpo_trans with (Term ord_psi (ta1 :: tb1 :: nil));
          auto with T2.
        apply rpo_4_2;auto with T2.
Qed.

Lemma rpo_4_1 : forall ta1  ta2 tb1 tb2 n1 n2 tc1 tc2,
    rpo (Term ord_psi (ta1:: tb1 ::nil)) tb2 ->
    rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
    rpo 
      (Term ord_cons 
            ((Term ord_psi (ta1:: tb1 ::nil))::
                                             (nat_2_term n1) ::tc1::nil))
      (Term ord_cons 
            ((Term ord_psi (ta2:: tb2 ::nil))::
                                             (nat_2_term n2) ::tc2::nil)).
Proof.
  intros; apply rpo_trans with  (Term ord_psi (ta2 :: tb2 :: nil)).
  -  apply rpo_4_3;auto with T2.
  -  eapply Subterm.
   + now  eleft.
   + left;auto with T2.
Qed.

Lemma rpo_4_4 : forall ta1  ta2 tb1 tb2  n2  tc2,
    rpo (Term ord_psi (ta1:: tb1 ::nil)) tb2 ->
    rpo (Term ord_psi (ta1:: tb1 ::nil))
        (Term ord_cons 
              ((Term ord_psi (ta2:: tb2 ::nil))::
                                               (nat_2_term n2) ::tc2::nil)).
Proof.
  intros;  apply rpo_trans with  (Term ord_psi (ta2 :: tb2 :: nil)).
  -  apply rpo_4_2;auto with T2.
  -  eapply Subterm.
     + now   eleft.
     + left;auto with T2.
Qed.

Lemma rpo_5_2 : 
  forall ta1 ta2  tb1  ,
    rpo (Term ord_psi (ta1:: tb1 ::nil))
        (Term ord_psi (ta2:: (Term ord_psi (ta1::tb1::nil)) ::nil)).
Proof.
  intros; eapply Subterm.
  -  eright;now eleft.
  - left.
Qed.

Lemma rpo_5_3 : forall ta1  ta2 tb1  n1 tc1,
    rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
    rpo 
      (Term ord_cons 
            ((Term ord_psi (ta1:: tb1 ::nil))::
                                             (nat_2_term n1) ::tc1::nil))
      (Term ord_psi (ta2:: (Term ord_psi (ta1:: tb1 ::nil)) ::nil)).
Proof.
  intros; apply Top_gt.
  - cbn; auto with T2.
  -  inversion_clear 1; try subst s'.
   + apply rpo_5_2;auto with T2.
   + destruct H1 as [<-|[<-|[]]].
     * apply nat_lt_psi.
     * apply rpo_trans with (Term ord_psi (ta1 :: tb1 :: nil)).
       -- auto with T2.
       -- apply rpo_5_2;auto with T2.
Qed.

Lemma rpo_5_1 : forall ta1  ta2 tb1  n1 n2 tc1 tc2,
    rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
    rpo 
      (Term ord_cons 
            ((Term ord_psi (ta1:: tb1 ::nil))::
                                             (nat_2_term n1) ::tc1::nil))
      (Term ord_cons
            ((Term ord_psi (ta2:: 
                               (Term ord_psi (ta1:: tb1 ::nil))
                               ::nil))::
                                      (nat_2_term n2) ::tc2::nil)).
Proof.
  intros;
  apply rpo_trans with  
      (Term ord_psi (ta2 :: Term ord_psi (ta1 :: tb1 :: nil) :: nil)).
  -  apply rpo_5_3; auto with T2.
  -  eapply Subterm.
     + now eleft.
     + left;auto with T2.
Qed.


Lemma rpo_5_4 : forall ta1  ta2 tb1  n2  tc2,
    rpo (Term ord_psi (ta1:: tb1 ::nil))
        (Term ord_cons
              ((Term ord_psi (ta2:: 
                                 (Term ord_psi (ta1:: tb1 ::nil))
                                 ::nil))::
                                        (nat_2_term n2) ::tc2::nil)).
Proof.
  intros;
    apply rpo_trans with 
        (Term ord_psi (ta2 :: Term ord_psi (ta1 :: tb1 :: nil) :: nil)).
  -  eapply Subterm.
     +  eright; now eleft.
     + left.
  - eapply Subterm.
    + now eleft.
    +  left.
Qed.


Lemma rpo_6_1 : forall ta1 tb1 n1 n2 tc1 tc2,
    rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
    (n1 < n2)%nat ->
    rpo 
      (Term ord_cons
            ((Term ord_psi (ta1:: tb1 ::nil))::
                                             (nat_2_term n1) ::tc1::nil))
      (Term ord_cons 
            ((Term ord_psi (ta1:: tb1 ::nil)):: (nat_2_term n2) ::tc2::nil)).
Proof.
  intros; apply Top_eq_lex.
  -  simpl;auto with T2.
  -  right.
     left.
     + apply nat_2_term_mono;auto with T2.
     + auto with T2.
  -  inversion_clear 1; try subst s'.
     +  eapply Subterm; [| eleft].
        left;auto with T2.
     + destruct H2 as [<-|[<-|[]]].
       *  apply nat_lt_cons.
       *  eapply rpo_trans.
          --  eexact H.
          --   eapply Subterm; [| eleft].
               left;auto with T2.
Qed.

Lemma rpo_6_4 : forall ta1 tb1  n2  tc2,
    (0 < n2)%nat ->
    rpo (Term ord_psi (ta1:: tb1 ::nil))
        (Term ord_cons
              ((Term ord_psi (ta1:: tb1 ::nil))::
                                               (nat_2_term n2) ::tc2::nil)).
Proof.
  intros; eapply Subterm; [| eleft].
  now left. 
Qed.

Lemma rpo_7_1 : forall ta1 tb1 n1 tc1 tc2,
    rpo tc1 (Term ord_psi (ta1:: tb1 ::nil)) ->
    rpo tc1  tc2 ->
    rpo (Term ord_cons
              ((Term ord_psi (ta1:: tb1 ::nil))::
                                               (nat_2_term n1) ::tc1::nil))
        (Term ord_cons
              ((Term ord_psi (ta1:: tb1 ::nil))::
                                               (nat_2_term n1) ::tc2::nil)).
Proof.
  intros;  apply Top_eq_lex.
  -  simpl;auto with T2.
  -  right.
     right.
     left; auto with T2.
  - inversion_clear 1; try subst s'.
    + eapply Subterm; [| eleft].
      left;auto with T2.
    + destruct H2 as [<-|[<-|[]]].
      * apply nat_lt_cons.
      * eapply rpo_trans.
        -- eexact H.
        -- eapply Subterm; [| eleft].
           left;auto with T2. 
Qed.


(**  ** inclusion of the order [lt] in the rpo *)

Section lt_incl_rpo.
  Variable s :nat.
  Variables (a1 b1 c1 a2 b2 c2:T2)(n1 n2:nat).

  Hypothesis Hsize :
    ((T2_size (gcons a1 b1 n1 c1) + T2_size (gcons a2 b2 n2 c2)) = S s)%nat.

  Hypothesis Hrec :   forall o' o, (T2_size o + T2_size o' <= s)%nat->
                                   o t2< o' -> nf o -> nf o' -> 
                                   rpo (T2_2_term o) (T2_2_term o').

  Hypothesis nf1 : nf (gcons a1 b1 n1 c1).
  Hypothesis nf2 : nf (gcons a2 b2 n2 c2).

  Remark nf_a1 : nf a1.
  Proof.  nf_inv.  Qed.

  Remark nf_a2 : nf a2.
  Proof. nf_inv.  Qed.

  Remark nf_b1 : nf b1.
  Proof.  nf_inv. Qed.

  Remark nf_b2 : nf b2.
  Proof. nf_inv. Qed.

  Hint Resolve nf1 nf2 nf_a1 nf_a2 nf_b1 nf_b2 : T2.

  Remark nf_c1 : nf c1.
  Proof.  nf_inv.  Qed.

  Remark nf_c2 : nf c2.
  Proof. nf_inv.  Qed.

  Hint Resolve nf_c1 nf_c2 : T2.

  Hypothesis H : gcons a1 b1 n1 c1 t2< gcons a2 b2 n2 c2.


  Lemma cons_rw : forall a b n c, 
      (n=0 /\ c=zero /\ 
       (T2_2_term (gcons a b n c)=
        (Term ord_psi 
              ((T2_2_term a)::(T2_2_term b)::nil)))) \/
      (T2_2_term (gcons a b n c)=
       Term ord_cons 
            ((Term ord_psi ((T2_2_term a)::(T2_2_term b)::nil))
               ::(nat_2_term n)::(T2_2_term c)::nil)).
    destruct n. 
    -  destruct c.
       + left;simpl;auto with T2.
       + right;simpl;auto with T2.
    - right;simpl;auto with T2.
  Qed.


  
  Lemma lt_rpo_cons_cons : rpo (T2_2_term (gcons a1 b1 n1 c1)) 
                               (T2_2_term (gcons a2 b2 n2 c2)).
  Proof.
    inversion H.
    - assert (rpo (T2_2_term a1) (T2_2_term a2)).
      apply Hrec.
      + simpl in Hsize;lia.
      +  auto with T2.
      +  auto with T2.
      +  auto with T2.
      + assert (rpo (T2_2_term b1) 
                    (Term ord_psi ((T2_2_term a2):: ((T2_2_term b2)::nil)))).
        { change (rpo (T2_2_term b1) (T2_2_term (gcons a2 b2 0 zero))).
          apply Hrec.
          simpl;simpl in Hsize;lia.
          auto with T2.
          auto with T2.
          constructor;auto with T2.
        }
        assert (rpo (T2_2_term c1)
                    (Term ord_psi (T2_2_term a1 :: T2_2_term b1 :: nil))).
        {  change (rpo (T2_2_term c1) (T2_2_term (gcons a1 b1 0 zero))).
           apply Hrec.
           simpl;simpl in Hsize;lia.
           inversion_clear nf1.
           auto with T2.
           apply psi_lt_head;auto with T2.
           auto with T2.
           constructor;auto with T2.
        }
        case (cons_rw a1 b1 n1 c1).
        intros (H'2,(H'3,H'4)).
        rewrite H'2;rewrite H'3.
        case (cons_rw a2 b2 n2 c2).
        intros (H'5,(H'6,H'7)).
        rewrite H'5;rewrite H'6.
        simpl.
        apply rpo_2_2;auto with T2.
        intro H'6;rewrite H'6.
        simpl.
        apply rpo_2_4 ; auto with T2.
        intro H'6;rewrite H'6.
        case (cons_rw a2 b2 n2 c2).
        intros (H''5,(H''6,H''7)).
        rewrite H''7. 
        apply rpo_2_3;auto with T2.
        intro H'7;rewrite H'7.
        apply rpo_2_1;auto with T2.
    - subst a2.
      assert (rpo (T2_2_term b1) (T2_2_term b2)).
      {
        apply Hrec.
        simpl in Hsize;lia.
        auto with T2.
        auto with T2.
        eauto using nf_b.
      }
      assert (rpo (T2_2_term c1) 
                  (Term ord_psi (T2_2_term a1 :: T2_2_term b1 :: nil))).
      {    change (rpo (T2_2_term c1) (T2_2_term (gcons a1 b1 0 zero))).
           apply Hrec.
           simpl;simpl in Hsize;lia.
           inversion_clear nf1.
           auto with T2.
           apply psi_lt_head;auto with T2.
           auto with T2.
           constructor;auto with T2.
      }
      case (cons_rw a1 b1 n1 c1).
      intros (H'2,(H'3,H'4)).
      rewrite H'4.
      case (cons_rw a1 b2 n2 c2).
      intros (H'5,(H'6,H'7)).
      rewrite H'7.
      apply rpo_3_2;auto with T2.
      intro H'6;rewrite H'6.
      apply rpo_3_4 ; auto with T2.
      intro H'6;rewrite H'6.
      case (cons_rw a1 b2 n2 c2).
      intros (H''5,(H''6,H''7)).
      rewrite H''7.
      apply rpo_3_3;auto with T2.
      intro H'7;rewrite H'7.
      apply rpo_3_1;auto with T2.
    - assert  (rpo (Term ord_psi ((T2_2_term a1):: (T2_2_term b1) ::nil))
                   (T2_2_term b2)).
      { change  (rpo (T2_2_term (gcons a1 b1 0 zero))  (T2_2_term b2)).
        apply Hrec.
        simpl in Hsize. 
        simpl;lia.
        auto with T2.
        auto with T2.
        auto with T2.
      }
      assert (rpo (T2_2_term c1) 
                  (Term ord_psi (T2_2_term a1 :: T2_2_term b1 :: nil))).
      {
        change (rpo (T2_2_term c1) (T2_2_term (gcons a1 b1 0 zero))).
        apply Hrec.
        simpl;simpl in Hsize;lia.
        inversion_clear nf1.
        auto with T2.
        apply psi_lt_head;auto with T2.
        auto with T2.
        constructor;auto with T2.
      }
      case (cons_rw a1 b1 n1 c1).
      intros (H'2,(H'3,H'4)).
      rewrite H'4.
      
      case (cons_rw a2 b2 n2 c2).
      intros (H'5,(H'6,H'7)).
      rewrite H'7.
      apply rpo_4_2;auto with T2.
      intro H'6;rewrite H'6.
      apply rpo_4_4 ; auto with T2.
      intro H'6;rewrite H'6.
      case (cons_rw a2 b2 n2 c2).
      intros (H''5,(H''6,H''7)).
      rewrite H''7.
      apply rpo_4_3;auto with T2.
      intro H'7;rewrite H'7.
      apply rpo_4_1;auto with T2.
    - assert (rpo (T2_2_term c1) 
                  (Term ord_psi ((T2_2_term a1)::(T2_2_term b1)::nil))).
      {
        change (rpo (T2_2_term c1) (T2_2_term (gcons a1 b1 0 zero))).
        apply Hrec.
        simpl;simpl in Hsize;lia.
        inversion_clear nf1;auto with T2.
        apply psi_lt_head;auto with T2.
        auto with T2.
        constructor;auto with T2.
      }
      case (cons_rw a1 b1 n1 c1).
      intros (H'2,(H'3,H'4)).
      rewrite H'4.
      case (cons_rw a2 (gcons a1 b1 0 zero) n2 c2).
      intros (H''5,(H''6,H''7)).
      rewrite H''7.
      simpl;apply rpo_5_2;auto with T2.
      intro H'7;rewrite H'7.
      simpl;apply rpo_5_4.
      intro H'7;rewrite H'7.
      case (cons_rw a2 (gcons a1 b1 0 zero) n2 c2).
      intros (H''5,(H''6,H''7)).
      rewrite H''7.
      simpl;apply rpo_5_3.
      auto with T2.
      intro H''7;rewrite H''7.
      simpl;apply rpo_5_1.
      auto with T2.
    - subst a2.
      subst b2.
      assert (rpo (T2_2_term c1) 
                  (Term ord_psi ((T2_2_term a1):: (T2_2_term b1) ::nil))).  
      {
        change (rpo (T2_2_term c1) (T2_2_term (gcons a1 b1 0 zero))).
        apply Hrec.
        simpl; simpl in Hsize;lia.
        inversion nf1;auto with T2.
        apply psi_lt_head;auto with T2.
        auto with T2.
        constructor;auto with T2.
      }
      case (cons_rw a1 b1 n1 c1).
      intros (H'2,(H'3,H'4)).
      rewrite H'4.
      case (cons_rw a1 b1 n2 c2).
      intros (H''2,(H''3,H''4)).
      rewrite H''2 in H1.
      inversion H1.
      intro H'7;rewrite H'7.
      apply rpo_6_4.
      rewrite H'2 in H1;auto with T2.
      intro H'7;rewrite H'7.
      case (cons_rw a1 b1 n2 c2).
      intros (H''2,(H''3,H''4)).
      rewrite H''2 in H1.
      inversion H1.
      intro H''7;rewrite H''7.
      apply rpo_6_1.
      auto with T2.
      auto with T2.
    - assert (rpo (T2_2_term c1)
                  (Term ord_psi ((T2_2_term a1):: (T2_2_term b1) ::nil))).  
      {
        change (rpo (T2_2_term c1) (T2_2_term (gcons a1 b1 0 zero))).
        apply Hrec.
        simpl; simpl in Hsize;lia.
        inversion nf1;auto with T2.
        apply psi_lt_head;auto with T2.
        auto with T2.
        constructor;auto with T2.
      }
      assert (rpo (T2_2_term c1) (T2_2_term c2)).
      {
        apply Hrec.
        simpl; simpl in Hsize;lia.
        auto with T2.
        auto with T2.
        auto with T2.
      }
      case (cons_rw a2 b2 n2 c1).
      + intros (H'2,(H'3,H'4)).
        rewrite H'4.
        case (cons_rw a2 b2 n2 c2).
        *    intros (H''2,(H''3,H''4)).
             rewrite H''3 in H1.
             inversion H1.
        * intro H'7;rewrite H'7.
          eapply Subterm; [| eleft].
          left.
          auto with T2.
      + intro H'7;rewrite H'7.
        case (cons_rw a2 b2 n2 c2).
        *    intros (H''2,(H''3,H''4)).
             rewrite H''3 in H1;inversion H1.
        * intro H''7;rewrite H''7.
          apply rpo_7_1.
          auto with T2.
          subst a2;subst b2.
          auto with T2.
          auto with T2.
  Qed.


End lt_incl_rpo.

Lemma lt_inc_rpo_0 : forall n, 
    forall o' o, (T2_size o + T2_size o' <= n)%nat->
                 o t2< o' -> nf o -> nf o' -> 
                 rpo (T2_2_term o) (T2_2_term o').
Proof.
  induction n.
 - destruct o;destruct o'.
  + inversion 2.
  + cbn; inversion 1.
  + inversion 2.
  + cbn; inversion 1.
 - destruct o'.
  + inversion 2.
  + destruct o.
   *  intros; case (cons_rw o'1 o'2 n0 o'3).
      intros (H'1,(H'2,H'3)); rewrite H'3.
      simpl;apply Top_gt.
      simpl;auto with T2.
      destruct 1.
      intro H3;rewrite H3.
      simpl;apply Top_gt.
      simpl;auto with T2.
      destruct 1.
   * intros; case (Lt.le_lt_or_eq _ _ H).
     -- intros;apply IHn;auto with arith T2.
     --  intros;
    eapply lt_rpo_cons_cons;eauto with T2.
Qed.



Remark R1 : Acc P.prec nat_0. 
Proof.
  split; destruct y; try contradiction.
Qed.

Hint Resolve R1 : T2.

Remark R2 : Acc P.prec ord_zero.
Proof.
  split; destruct y; try contradiction; auto with T2.
Qed.

Hint Resolve R2 : T2.

Remark R3 : Acc P.prec nat_S.
Proof.
  split; destruct y; try contradiction;auto with T2.
Qed.


Hint Resolve R3 : T2.

Remark R4 : Acc P.prec ord_cons.
Proof.
  split; destruct y; try contradiction;auto with T2.
Qed.

Hint Resolve R4 : T2.

Remark R5 : Acc P.prec ord_psi.
Proof.
  split; destruct y; try contradiction;auto with T2.
Qed.

Hint Resolve R5 : T2.

Theorem well_founded_rpo : well_founded rpo.
Proof.
  apply wf_rpo.
  red. intro a; destruct a;auto with T2.
Qed.

Section  well_founded.
  
  Let R := restrict  nf lt.

  Hint Unfold restrict R : T2.

  Lemma R_inc_rpo : forall o o', R o o' -> rpo (T2_2_term o) (T2_2_term o').
  Proof.
    intros o o' (H,(H1,H2));  eapply lt_inc_rpo_0;auto with T2.
  Qed. 

  
  Lemma nf_Wf : well_founded_restriction _ nf lt.
  Proof.
    intros a H;
      assert(H0 := Acc_inverse_image _ _ rpo T2_2_term a
                                     (well_founded_rpo (T2_2_term a))).
    eapply  Acc_incl  with  (fun x y : T2 => rpo (T2_2_term x) (T2_2_term y)). 
    - red;     apply R_inc_rpo.
    -  auto with T2.
  Qed.


End well_founded.


Definition transfinite_induction :
  forall (P:T2 -> Type),
    (forall x:T2, nf x ->
                  (forall y:T2, nf y ->  y t2< x -> P y) -> P x) ->
    forall a, nf a -> P a.
Proof.
  intros; eapply well_founded_restriction_rect; eauto with T2.
  eexact nf_Wf;auto with T2.
Defined.


Definition transfinite_induction_Q :
  forall (P : T2 -> Type) (Q : T2 -> Prop),
    (forall x:T2, Q x -> nf x ->
                  (forall y:T2, Q y -> nf y ->  y t2< x -> P y) -> P x) ->
    forall a, nf a -> Q a -> P a.
Proof.
  intros P Q X a H H0.
  eapply well_founded_restriction_rect with (R:=lt)(E:=fun a => nf a /\ Q a)
                                            (a:=a).
  - red; intros a0 H1; apply Acc_incl with (restrict nf lt).
    + red; intros; unfold restrict in *; tauto.
    + apply nf_Wf; tauto.
  -  destruct 1; intros; eapply X; eauto.
     
  - red;auto. 
Defined.


(** *  the Veblen function phi *)

(** See Schutte.Critical.phi  *)

Definition  phi (alpha beta : T2) : T2 :=
  match beta with zero => [alpha, beta] 
             | [b1, b2] => 
               (match compare alpha b1
                with Datatypes.Lt => [b1, b2 ]
                | _ => [alpha,[b1, b2]]
                end)
             | gcons b1 b2 0 (gcons zero zero  n zero) => 
               (match compare alpha b1
                with  Datatypes.Lt => 
                      [alpha, (gcons b1 b2 0 (fin n))]
                | _ =>  [alpha, (gcons b1 b2 0 (fin (S n)))]
                end)
             | any_beta => [alpha, any_beta]
  end.


Example Ex8:  phi 1 (succ epsilon0) = [1, [1,0] + 1].
Proof. reflexivity. Qed.


(**  All epsilons are fixpoints of phi 0 *)

Theorem epsilon_fxp : forall beta, phi zero (epsilon beta) =
                                   epsilon beta.
Proof. reflexivity. Qed.


Theorem epsilon0_fxp : epsilon0 = phi zero epsilon0.
Proof. apply epsilon_fxp. Qed.


Theorem phi_of_psi  : forall a b1 b2, 
    phi a [b1, b2] =
    if (lt_ge_dec a b1) 
    then [b1, b2]
    else [a ,[b1, b2]].
Proof.
  cbn; intros;case (lt_ge_dec a b1).
  - intro H;  rewrite compare_rw_lt; auto with T2.
  - destruct 1.
   + subst b1; rewrite compare_rw_eq;auto with T2.
   + rewrite compare_rw_gt;auto with T2.
Qed.

Lemma phi_to_psi : forall alpha beta, 
    {alpha' : T2 & {beta' : T2 | phi alpha beta = [alpha', beta']}}.
Proof.
  destruct beta; cbn.
  -  now exists alpha, zero.
  -  case n.
   +  case beta3. 
      * case (compare alpha beta1). 
        -- exists alpha;exists  [beta1, beta2];trivial.
        --  exists beta1;exists beta2;trivial.
        --  exists alpha;exists  [beta1, beta2];trivial.
      *  destruct t.
         --   destruct t.
              ++ destruct n0.
                 ** destruct t.
                    case (compare alpha beta1).
                     now exists alpha, (gcons beta1 beta2 0 [zero, zero]).
                     now exists alpha, (gcons beta1 beta2 0 zero).
                     now exists alpha, (gcons beta1 beta2 0 [zero, zero]).
                     now exists alpha,
                         (gcons beta1 beta2 0
                                (gcons zero zero 0 (gcons t1 t2 n0 t3))).
                 **  destruct t.
                     case (compare alpha beta1).
                     now exists alpha,
                         (gcons beta1 beta2 0 (gcons zero zero (S n0) zero)).
                     now exists alpha, (gcons beta1 beta2 0 (fin (S n0))).
                     now exists alpha,
                         (gcons beta1 beta2 0 (gcons zero zero (S n0) zero)).
                     now exists alpha,
                         (gcons beta1 beta2 0 (gcons zero zero (S n0)
                                                     (gcons t1 t2 n1 t3))).
              ++ intros n1 t;
                   now exists alpha,
                       (gcons beta1 beta2 0
                                  (gcons zero (gcons t1 t2 n0 t3) n1 t)).
         --   exists alpha;
                exists (gcons beta1 beta2 0
                              (gcons (gcons t1 t2 n0 t3) t n1 t0));
                reflexivity.
   +  intro n0; now exists alpha; exists (gcons beta1 beta2 (S n0) beta3).
Qed.

Lemma phi_principal : forall alpha beta, ap (phi alpha beta).
Proof.
  intros alpha beta; case (phi_to_psi alpha beta);intros x (y,e);
    rewrite e;try constructor.
Qed.

Theorem phi_alpha_zero : forall alpha, phi alpha zero = [alpha, zero].
Proof.
  cbn; auto with T2.
Qed.

Theorem phi_of_psi_succ : forall a b1 b2 n, 
    phi a (gcons b1 b2 0 (fin (S n))) =
    if lt_ge_dec a b1
    then [a, (gcons b1 b2 0 (fin n))]
    else [a ,(gcons b1 b2 0 (fin (S n)))].
  Proof.
  cbn; intros;case (lt_ge_dec a b1).
  -  intro H; rewrite compare_rw_lt; auto with T2.
  -  destruct 1.
     +  subst b1; rewrite compare_rw_eq;auto with T2.
     +  rewrite compare_rw_gt;auto with T2.
Qed.


  Lemma phi_cases_aux : forall P : T2 -> Type,
      P zero ->
      (forall b1 b2, nf b1 -> nf b2 -> P [b1, b2]) ->
      (forall b1 b2 n, nf b1 -> nf b2 ->
                       P (gcons b1 b2 0 (fin (S n)))) ->
      (forall b1 b2 n c, nf (gcons b1 b2 n c) ->
                         omega t2<= c \/ (0 < n)%nat -> 
                         P (gcons b1 b2 n c)) ->
      forall alpha, nf alpha -> P alpha.
  Proof with auto with T2.
    intros until alpha; case alpha;  auto with T2.
    destruct n;intros until t1;case (lt_ge_dec t1 omega).
    -  intros l H ; assert (nf t1) by (inversion H ; auto with T2).
       case (lt_omega_inv  H0 l);  intro x;case x.
       + intro;subst t1; cbn.
         refine (X0 _ _ _ _).
         * inversion H ...
         *  inversion H ...
       +  intros;subst t1.
          apply X1; inversion H ...
    -   intros;apply X2 ...
    -   intros;apply X2 ...
        auto with arith.
    -   intros;apply X2 ...
  Qed.


Theorem phi_cases' :
  forall a b, nf b ->
              {b1 :T2 & {b2:T2 | b = [b1, b2] /\
                                 a t2< b1 /\ phi a b =  b}} +
              {phi a b = [a, b]} +
              {b1 :T2 & {b2:T2 &
                            {n: nat | b = gcons b1 b2 0 (fin (S n)) /\
                                      a t2< b1 /\ 
                                      phi a b =
                                      [a, (gcons b1 b2 0 (fin n))]}}}.
Proof with auto with T2.
  intros a b Hb; pattern b; apply phi_cases_aux; trivial.
  -  left;right; cbn ...
  - intros; case_eq (compare a b1); auto.
    + left;right; unfold phi; cbn; rewrite H1 ...
    + left;left; exists b1;exists b2; split ...
      split;simpl ...
      rewrite H1 ...
    + left;right; cbn; rewrite H1 ...
  -   intros; case_eq (compare a b1).
      + left;right; cbn; rewrite H1 ...
      +  right; exists b1, b2, n; repeat split ...
         cbn; rewrite H1 ...
      +  left;right; cbn; rewrite H1 ...
  -   intros;  left;right; cbn; case_eq n; trivial.
      + intro; subst n; case_eq c.
        *  intro; subst c; case H0.
           --   destruct 1.
                ++ discriminate H1.
                ++  inversion H1.
           --  inversion 1.
        *   intro t;case t ...
            -- intro t0;case t0 ...
               ++ intros until t1;case t1 ...
                  **  intro; subst c; case H0.
                      destruct 1.
                      discriminate H1.
                      inversion H1; lt_clean ...
                      inversion 1.
Qed.

Theorem phi_cases : forall a b, nf b ->
                                {phi a b = b} +
                                {phi a b = [a, b]} +
                                {b': T2 | nf b' /\ phi a b = [a, b']
                                          /\ succ  b' = b}.
Proof with auto with T2.
  intros a b Hb; pattern b;apply phi_cases_aux.
  -  left;right; cbn ...
  -  intros; generalize (phi_of_psi a b1 b2);
       case (lt_ge_dec a b1).
     +  left;left ...
     +  left;right ...
  -   intros; generalize (phi_of_psi_succ a  b1 b2 n);
        case (lt_ge_dec a b1).
      +   right; exists (gcons b1 b2 0 (fin n));  split.
          case n.
          *   cbn; constructor ...
          * cbn; repeat constructor ...
            apply le_lt_trans with a ...
          *  split ...
             cbn; generalize l;case b1.
             --   inversion 1.
             -- case n; cbn ...
      + left;right ...
  - left;right;cbn; case_eq n ...
    +  intro;subst n; case_eq c.
       *  intro; subst c;  case H0;intro H1.
          -- inversion H1.
             ++ discriminate.
             ++   lt_clean.
             --  lt_clean.
       *  intro t; case t ...
          -- intro t0;case t0 ...
           ++ intros n t1 e; subst c.
              case H0.
              ** destruct 1.
                 discriminate H1.
                 inversion H1; lt_clean ...
              ** inversion 1.
    -   auto with T2.
Qed.

Theorem phi_nf : forall alpha beta, nf alpha -> 
                                    nf beta -> 
                                    nf (phi alpha beta).
Proof.
  intros t1 t2 v1 v2; case (phi_cases t1 v2).
  -  destruct 1 as [e|e].
     + rewrite e;auto with T2.
     +  rewrite e;unfold psi;constructor;auto with T2.
  -  destruct 1 as (b', (H,(H0,H1))).
     rewrite H0; unfold psi;constructor;auto with T2.
Qed.

Lemma phi_of_any_cons : forall alpha beta1 beta2 n gamma, 
     omega t2<= gamma  \/ (0 < n)%nat ->
    phi alpha (gcons beta1 beta2 n gamma) = 
    [alpha, (gcons beta1 beta2 n gamma)].
Proof.
  cbn; intros until n; case n;  destruct 1; auto with T2.
  generalize H; case gamma; auto with T2.
  -  destruct 1.
     + discriminate H0.
     +   lt_clean.
  -  intro t;case t.
     + intro t0;case t0.
       *  destruct 1.
          discriminate H0.
          inversion H0; lt_clean; auto with T2.
       *  auto with T2.
   +  auto with T2.
    -  lt_clean; auto with T2.
Qed.


Lemma phi_fix alpha beta :
  phi alpha beta = beta ->
  {beta1 : T2 & {beta2 : T2 | beta = [beta1, beta2] 
                              /\ alpha t2< beta1}}.
Proof.
  destruct beta;simpl.
  discriminate 1.
  - case n.
    +  case beta3.
       *  case_eq (compare  alpha beta1).
          --  intros H H0; injection H0.
              intro;  absurd (lt beta2 [beta1, beta2]).
              ++  rewrite H1; apply lt_irr.
              ++ refine (lt_beta_psi _ _).
          --  exists beta1, beta2; split;auto with T2.
          --   intros H H0;  injection H0.
               intro H1;  absurd (beta2 t2< [beta1, beta2]).
               ++  rewrite H1;apply lt_irr.
               ++  refine (lt_beta_psi _ _).
       *  destruct t;simpl.
          destruct t;simpl.
          destruct t;simpl.
          case (compare alpha beta1).
          all: try discriminate 1.
    +  discriminate 1.
Qed.


Lemma phi_le : forall alpha beta alpha' beta', 
    nf beta -> 
    phi alpha beta = [alpha', beta'] -> alpha t2<= alpha'.
Proof.
  intros a b a' b' Hb;case (phi_cases a Hb).
  -  destruct 1.
     + case (phi_fix _  e); intros x (beta2,(H,H0)).
       rewrite e, H; injection 1; 
         intros; subst x; right;auto with T2.
     +  rewrite e;injection 1;left;auto with T2.
  -  intros (b0,(H1,(H2,H3))).
     rewrite H2; injection 1;left;auto with T2.
Qed.

Lemma phi_le_ge :
  forall alpha beta, nf alpha -> nf beta -> 
                     {alpha':T2 &
                             {beta':T2
                             | phi alpha beta = [alpha' ,beta'] /\  
                               alpha t2<= alpha' /\ 
                               beta' t2<= beta}}.
Proof.
  intros a b Va Vb; case (phi_cases' a Vb).
  - destruct 1.
    +  case s; intros b1 (b2,(H1,(H2,H3))).
       rewrite H1 in H3; subst b.
       exists b1;exists  b2;repeat split;auto with T2.
    +  exists a, b;auto with T2.
  -  intros (b1,(b2,(n,(H1,(H2,H3)))));
     exists a, (gcons b1 b2 0 (fin n));auto with T2.
     repeat split;auto with T2.
     subst b;case n;simpl; auto with T2.
     right;auto with T2.
Qed.

(**  [phi alpha beta] is a common fixpoint of all the [phi gamma], 
for any [gamma t2< alpha] as specified by Schutte *)

Theorem phi_spec1 : forall alpha beta gamma, 
    nf alpha -> nf beta -> nf gamma ->
    gamma t2< alpha ->
    phi gamma (phi alpha beta) = phi alpha beta.
Proof.
  intros; case (phi_le_ge H H0 ).
  -  intros alpha' (beta', (H'1,(H'2,H'3))); rewrite H'1; cbn.
     rewrite (compare_rw_lt);auto with T2.
    apply lt_le_trans with alpha;auto with T2.
Qed.


Theorem phi_principalR alpha beta :
  nf alpha -> nf beta ->
  {gamma:T2 | [alpha, beta] =  phi zero gamma}.
Proof.
  intros  Valpha Vbeta; case (phi_cases' alpha Vbeta).
  destruct 1.
  -  case s; intros b1 (b2,(H1,(H2,H3))).
     case (lt_ge_dec zero alpha).
     intro l; exists [alpha, beta]; cbn.
     +  rewrite (compare_rw_lt  l);auto with T2.
     + intro; assert(alpha = zero).
       { inversion l;auto with T2. lt_clean. }
       subst alpha beta;  exists (gcons b1 b2 0 (fin 1)).
       cbn; rewrite (compare_rw_lt  H2);auto with T2.
  - case (lt_ge_dec zero alpha). 
    +  exists (phi alpha beta).
       rewrite phi_spec1;auto with T2.
    +  intro;assert (alpha=zero).
       case l; auto with T2.
       intro;lt_clean.
       subst alpha; exists beta.
       auto with T2.
  -   intros (b1,(b2,(n,(H1,(H2,H3))))); subst beta.
      case (lt_ge_dec zero alpha).
   +  intro l; exists [alpha, (gcons b1 b2 0 (fin (S n)))].
      cbn; rewrite (compare_rw_lt l).
      reflexivity. 
   +  intro l;assert (alpha=zero).
      *  case l; auto with T2.
         intro;lt_clean.
      * subst alpha;  exists (gcons b1 b2 0 (fin (S (S n))));cbn;
          rewrite  (compare_rw_lt H2); auto with T2.
Defined.




Lemma phi_alpha_zero_gt_alpha : forall alpha, alpha t2< phi alpha zero.
Proof.
  induction alpha;simpl;auto with T2.
Qed.


Theorem le_b_phi_ab : forall a b, nf a -> nf b ->   b t2<= phi a b.
Proof.
  intros a b Ha Hb; case (phi_cases a  Hb).
  - destruct 1.
   +  rewrite e;left;auto with T2.
   +  rewrite e;right; auto with T2.
  -  intro x; case x;intros b' (e,(i,i'));  subst b;  rewrite i.
     apply lt_succ_le;auto with T2.
Qed.

Lemma phi_of_psi_plus_fin : forall a b1 b2 n, 
    a t2< b1 -> phi a (gcons b1 b2 0 (fin n)) t2<
              [a ,gcons b1 b2 0 (fin n)].
  Proof.
  cbn;  intros until n;case n.
  - cbn; intro H;rewrite (compare_rw_lt H);auto with T2.
  - cbn;  intros n0  H;rewrite (compare_rw_lt H).
    case n0;simpl; auto with T2.
Qed.


Lemma phi_mono_r : forall a b c, nf a -> nf b -> nf c ->
                                 b t2< c -> phi a b t2< phi a c.
Proof.
  intros a b c Ha Hb Hc H;  case (phi_cases' a Hb).
  -  destruct 1.
   +  case s; intros b1 (b2,(H1,(H2,H3))); rewrite H3.
      apply lt_le_trans with c;auto with T2.
      apply le_b_phi_ab;auto with T2.
   +  case (phi_cases' a Hc).
    *  destruct 1.
       -- case s; intros c1 (c2,(H'1,(H'2,H'3))).
          rewrite e.
          rewrite H'3.
          rewrite H'1.
          constructor 2;auto with T2.
          rewrite H'1 in H.
          auto with T2.
       --   rewrite e;rewrite e0;auto with T2. 
    * intros (c1,(c2,(n, (H1,(H2,H3))))); subst c.
      assert 
    ((gcons c1 c2 0 (fin (S n))) = (succ (gcons c1 c2 0 (fin n)))).
    {  simpl;auto with T2.
       case_eq c1.
       intro; subst c1; lt_clean.
       case n;auto with T2.
       }
    assert (nf (gcons c1 c2 0 (fin n))).
    {  case n.
       inversion Hc;auto with T2.
       inversion Hc;auto with T2.
       intro; cbn; constructor.
       constructor 2.
       apply le_lt_trans with a;auto with T2.
       auto with T2.
       inversion Hc;auto with T2.
       inversion Hc;auto with T2.
       repeat constructor.
    }  
    rewrite H0 in H;  case (succ_lt_le Hb H1 H).
      --  intro;subst b.
          case (lt_irr (alpha:=[a, (gcons c1 c2 0 (fin n))])).
          pattern  [ a, (gcons c1 c2 0 (fin n))] at 1;rewrite <- e.
          apply phi_of_psi_plus_fin.
          auto with T2.
      --   rewrite H3, e; auto with T2.
  -  intros (b1,(b2,(n,(H1,(H2,H3))))); case (phi_cases' a Hc).
    + destruct 1.
     *  case s;intros c1 (c2,(H'1,(H'2,H'3))).
        rewrite H3;rewrite H'3;rewrite H'1.
        subst b; subst c;case n;simpl;auto with T2.
      -- constructor 2;auto with T2.
       apply le_lt_trans with  (gcons b1 b2 0 (fin (S n))).
    ++ cbn;auto with arith T2.
    ++   auto with T2.
      --   constructor 2; auto with T2.
           inversion H; auto with T2.
           lt_clean. 
     *   rewrite H3; rewrite e.
         apply lt_trans with [a, (gcons b1 b2 0 (fin (S n)))].
         --   case n;simpl;auto with T2.
         --   subst b;auto with T2.
    +  intros (c1,(c2,(p,(H'1,(H'2,H'3))))); rewrite H'3;rewrite H3.
       subst c;subst b; generalize H;inversion 1;auto with T2. 
       constructor 3.
       constructor 7.
       apply lt_compatR.
       inversion H4;lt_clean; auto with T2.
Qed.

Lemma phi_mono_weak_r : forall a b c, nf a -> nf b -> nf c -> 
                                      b t2<= c -> phi a b t2<= phi a c. 
Proof.
  destruct 4.
  -  subst c;left;auto with T2.
  -  right; apply phi_mono_r;auto with T2.
Qed.

Lemma phi_inj_r : forall a b c, nf a -> nf b -> nf c ->
                                phi a b = phi a c -> b = c.
Proof.
  intros a b c Na Nb Nc E; tricho b c H; trivial.
 -  absurd (phi a b t2< phi a c). 
    +  rewrite E; apply lt_irr.
    +  apply phi_mono_r;auto.
 -  absurd (phi a c t2< phi a b).
  +  rewrite E; apply lt_irr.
  + apply phi_mono_r;auto.
Qed.


Lemma lt_a_phi_ab : forall a b, nf a -> nf b -> a t2< phi a b.
Proof.
  intros; apply lt_le_trans with (phi a zero).
  -  apply phi_alpha_zero_gt_alpha.
  -  apply phi_mono_weak_r;auto with T2.
Qed.

(* Expressing psi in terms of phi 
   (as in Lepper-Moser) *)

Lemma zero_not_lim : ~ is_limit zero.
Proof. red;inversion 1. Qed.

Lemma F_not_lim : forall n, ~ is_limit  (fin n).
Proof.
  destruct n;red;inversion 1.
  decompose [or] H3; lt_clean.
  case  zero_not_lim;auto.
Qed.

Lemma succb_not_lim  alpha: is_successor alpha -> ~ is_limit alpha.
Proof.
  induction alpha.
  - intro;apply zero_not_lim.
  -  inversion_clear 1.
     +  apply (F_not_lim (S n)).
     +  red;inversion 1.
        * subst alpha3;inversion H1. 
        * case IHalpha3;auto. 
Qed.


Lemma is_limit_not_succ alpha:  is_limit alpha -> ~ is_successor alpha.
Proof.
  induction 1.
  -  red;inversion 1.
   +  subst alpha beta; case H;intro;lt_clean.
   +  inversion H8.
  -  red;inversion 1.
   +  subst gamma; case zero_not_lim;auto.
   +  case IHis_limit; auto.
Qed.


(**
   limit_plus_fin alpha n beta  means :
   beta = alpha + fin n and (alpha is limit or alpha = zero)
 *)



Inductive limit_plus_fin : T2 -> nat -> T2 -> Prop :=
  limit_plus_F_0 : forall p, limit_plus_fin zero p (fin p)
 |limit_plus_F_cons : forall beta1 beta2 n gamma0 gamma p,
     zero t2< beta1 \/ zero t2< beta2 ->
     limit_plus_fin gamma0 p gamma ->
     limit_plus_fin (gcons beta1 beta2 n gamma0)
                  p (gcons beta1 beta2 n gamma).

Lemma limit_plus_fin_plus : forall alpha alpha' p,
    limit_plus_fin alpha p alpha' ->
    nf alpha ->
    alpha' = alpha + fin p.
Proof.
  induction alpha.
  -  inversion_clear 1.
     cbn;auto.
  -  inversion_clear 1; generalize (IHalpha3 gamma p).
     intros H H2; rewrite (H H1); cbn.
     case p;cbn.
     +  rewrite plus_alpha_0;trivial.
     +  case_eq (compare [alpha1, alpha2] [zero, zero]).
        *  intro H3; generalize (compare_Eq H3).
           injection 1;intros;subst alpha1;subst alpha2.
           decompose [or] H0; lt_clean.
        *  intro H3; generalize (compare_Lt H3).
           inversion_clear 1;try lt_clean.
  * auto.
  + nf_inv.
Qed.

Lemma limit_plus_fin_lim : forall alpha alpha' p,
                      limit_plus_fin alpha p alpha' ->
                      nf alpha ->
                      is_limit alpha \/ alpha=zero.
Proof.
 intro alpha; elim alpha.
 - auto.
 - intros alpha1 _ alpha2 _ alpha3; case alpha3.
 + left; inversion H0.
   case (H _ _ H9).
 *  nf_inv. 
 * constructor; auto.
 * intro H18;rewrite H18;constructor 1;auto.
    nf_inv.
    nf_inv.
 + left; inversion H0; case (H _ _ H9).
   *  nf_inv.
  *  constructor; auto.
* intro H10;rewrite H10;constructor;try nf_inv;auto.
Qed.



Lemma limit_plus_fin_inv0  alpha beta: 
  limit_plus_fin alpha 0 beta -> 
  nf alpha -> alpha = beta.
Proof.
 intros H H0; generalize (limit_plus_fin_plus H H0).
 cbn; now rewrite plus_alpha_0.
Qed.

Lemma is_limit_cons_inv : forall b1 b2 n c, nf (gcons b1 b2 n c) ->
                          is_limit (gcons b1 b2 n c) -> is_limit c \/ c = zero.
Proof.
 inversion_clear 1;auto.
 inversion 1;auto.
Qed.

 
Lemma is_limit_intro : forall b1 b2 n , nf b1 -> nf b2 ->
                       zero t2< b1 \/ zero t2< b2 ->
                       is_limit  (gcons b1 b2 n zero).
Proof.
 constructor;auto.
Qed.


Lemma lt_epsilon0_ok : forall alpha, nf alpha -> lt_epsilon0 alpha ->
                                     alpha t2< epsilon0.
Proof.
 induction 1;intros; compute;auto with T2.
 - inversion_clear H1; constructor 2.
   + auto with T2.
   + apply IHnf2;auto with T2.
  - inversion_clear H3; constructor 2;auto with T2.
Qed.


Derive Inversion_clear lt_01 with (forall (a b:T2),
                gcons a b 0 zero t2<  epsilon0) Sort Prop.

Derive Inversion_clear lt_02 with (forall (a b c:T2)(n:nat),
                gcons a b n c t2<  epsilon0) Sort Prop.

Lemma psi_lt_epsilon0 : forall a b, [a, b] t2< epsilon0 ->
                                    a = zero /\ b t2< epsilon0.
Proof.
  intros a b H; inversion H using lt_01.
  -  split.
     +  apply lt_one_inv;auto with T2.
     +  compute;auto with T2.
  - inversion 1.
  - inversion 2.
  -  inversion 1.
  - inversion 1.
Qed.

Lemma cons_lt_epsilon0 : forall a b n c, gcons a b n c t2< epsilon0 ->
                                         nf (gcons a b n c) ->
                                         a = zero /\ b t2< epsilon0 /\ c t2< epsilon0.
Proof.
  intros a b n c H; inversion H using lt_02.
  -  split.
     +  apply lt_one_inv;auto with T2.
     +  split.
        *  exact H1.
        * apply lt_trans with (gcons a b n c);auto with T2.
          apply lt_tail;auto with T2.
  -  inversion 1.
  -  inversion 2.
  -  inversion 1.
  - inversion 1.
Qed.

Lemma lt_epsilon0_okR: forall alpha, nf alpha -> alpha t2< epsilon0 ->
                                     lt_epsilon0 alpha.
Proof.
  induction alpha.
  -  constructor.
  -  intros; inversion H0.
     + rewrite (lt_one_inv H3).
       right.
       * apply IHalpha2.
         inversion H;auto with T2.
         compute;auto with T2.
       * apply IHalpha3.
         inversion H;auto with T2.
         compute;auto with T2.
         apply lt_trans with (gcons alpha1 alpha2 n alpha3).
         apply lt_tail.
         auto with T2.
         auto with T2.
     +  inversion H2.
     +  inversion H10.
     +  inversion H2.
     + inversion H2.
Qed.



Lemma T1_to_T2_inj : forall alpha beta : T1,
    T1_to_T2 alpha = T1_to_T2 beta -> alpha = beta.
Proof.
 induction alpha; destruct beta;simpl;auto with T2.
 - discriminate 1.
 - discriminate 1.
 -  injection 1;auto with T2.
   rewrite (IHalpha1 beta1),  (IHalpha2 beta2).
    +  destruct 2;auto with T2.
    +  injection H;auto with T2.
    +  injection H;auto with T2.
Qed.

 
Lemma T1_to_T2_lt : forall c, lt_epsilon0 (T1_to_T2 c).
Proof.
 induction c;simpl;constructor;auto with T2.
Qed.

Definition T1_to_T2_R : forall a, lt_epsilon0 a -> {c:T1 | T1_to_T2 c = a}.
Proof.
 induction a.
 - exists T1.zero;simpl;auto with T2.
 -  intro H; case IHa2.
  + inversion H;auto with T2.
  + intros c2 e2; case IHa3.
   * inversion H;auto with T2.
   * intros c3 e3; exists (T1.ocons c2 n c3).
     rewrite <- e3;rewrite <- e2.
     replace a1 with zero.
   --  simpl;auto with T2.
   --  inversion H;auto with T2.
Defined.



Lemma T1_to_T2_mono : forall alpha beta, T1.lt alpha beta ->
                                    T1_to_T2 alpha t2< T1_to_T2 beta.
Proof.
  induction alpha. 
  +  destruct beta. 
   *  intro H;  compute  in H;  discriminate. 
   * cbn;  constructor.
  +  destruct beta. 
     *  intro H;  compute  in H;  discriminate. 
     *  intro H; destruct (lt_inv H). 
     --   constructor 3; now apply IHalpha1.  
     --   decompose [or and] H0; clear H0; subst alpha1.
      ++  now constructor 6.
      ++   subst  n; constructor 7;  now apply IHalpha2.  
Qed.


Lemma T1_to_T2_monoR : forall c c', lt (T1_to_T2 c) (T1_to_T2 c') -> T1.lt c  c'.
Proof.
 intros c c' H; case (T1.lt_eq_lt_dec c c').
 -  destruct 1; auto.
   subst c'; case (lt_irr H).
 - intro l; generalize (T1_to_T2_mono l); intro H0;
     case (lt_irr (alpha:=T1_to_T2 c)).
   eapply lt_trans;eauto with T2.
Qed.


Lemma lt_epsilon0_trans : forall a, lt_epsilon0 a ->  nf a ->
     forall b, lt b a -> nf b -> lt_epsilon0 b.

Proof.
 intros; apply lt_epsilon0_okR; auto.
 apply lt_trans with a; auto.
 apply lt_epsilon0_ok;auto with T2.
Qed.

Lemma nf_coeff_irrelevance : forall a b n n' c, nf (gcons a b n c) -> 
                                                nf (gcons a b n' c).
Proof.
   inversion_clear 1; constructor;auto with T2.
Qed.


Lemma psi_principal : forall a b c d, nf c -> c t2< [a, b] 
                                           -> d t2< [a, b] -> 
                                          c + d t2< [a, b].
Proof.
 induction c;destruct d;simpl;auto with T2.
 case (compare [c1,c2][d1,d2]).
 -  intros;apply psi_lt_head; inversion_clear H0.
    + constructor 2;auto with T2.
    + constructor 3;auto with T2.
    + constructor 4;auto with T2.
    + constructor 5;auto with T2.
    + inversion H2.
    +inversion H2.
 - auto with T2.
 - intros H H0 H1.
 generalize (IHc3 (gcons d1 d2 n0 d3)); intros H2.
 assert (H5 : c3 t2< [a,b]).
 {  eapply lt_trans; [| eexact H0].
    apply lt_tail.
    auto with T2.
 }
 inversion_clear H0.
 + constructor 2;auto with T2.
 + constructor 3;auto with T2.
 + constructor 4;auto with T2.
 +  constructor 5;auto with T2.
 +  inversion H3.
  +  constructor 7;auto with T2.
     inversion H3.
Qed.


Lemma nf_intro : forall a b n c, nf a -> nf b -> 
                                  c t2< [a,b ] -> nf c -> nf (gcons a b n c).
Proof.
  destruct c;constructor;auto with T2.
  inversion_clear H1;auto with T2.
  -  inversion H3.
  - inversion H3.
Qed. 
 

Lemma plus_nf : forall alpha, nf alpha -> forall beta, nf beta -> 
                                                       nf (alpha + beta).
Proof.
  intros alpha Halpha; pattern alpha; apply transfinite_induction; trivial.
  -  destruct x.
     + cbn;auto with T2.
     + destruct beta.
       * cbn;auto with T2.
       *  intros; cbn;
            case_eq ( compare (gcons x1 x2 0 zero) (gcons beta1 beta2 0 zero)).
          -- intro;apply nf_intro.
          ++  nf_inv.
          ++ nf_inv.
          ++ generalize ( compare_Eq  H2); injection 1.
             intros; subst beta1; subst beta2; inversion_clear H1.
             auto with T2.
             apply psi_lt_head;auto with T2.
          ++ nf_inv.
          -- auto.
          --  intro;apply nf_intro.
              ++  nf_inv.
              ++  nf_inv.
              ++  apply psi_principal.
                  nf_inv.
                  **  inversion H;auto with T2.
                   apply psi_lt_head;auto with T2.
                  **  apply psi_lt_head;unfold psi;
                        apply compare_Gt;auto with T2.
              ++  eapply H0;auto with T2.
                  **  nf_inv.
                  **  apply lt_tail;auto with T2.
Qed.

Lemma succ_as_plus : forall alpha, nf alpha -> alpha + one = succ alpha.
Proof.
  intro alpha;elim alpha.
  - cbn;auto with T2.
  -  cbn; intros;  case t; case t0.
     +  cbn; rewrite plus_0_r;auto with T2.
     +  cbn; rewrite <- H1;  cbn;auto with T2.
        inversion H2;auto with T2.
     +  cbn; rewrite <- H1; cbn;auto with T2.
        inversion H2;auto with T2.
     +  cbn;  rewrite <- H1;  cbn;auto with T2.
        inversion H2;auto with T2.  
Qed.

Lemma succ_nf : forall alpha, nf alpha -> nf (succ alpha).
Proof.
  intros alpha Halpha;
  rewrite <- succ_as_plus;auto with T2.
  apply plus_nf;auto with T2.
 Qed.

Lemma lt_epsilon0_succ : forall a, lt_epsilon0 a -> lt_epsilon0  (succ a).
Proof.
 induction a.
 - cbn;repeat constructor.
 - cbn; case a1.
  +  case a2.
     *  repeat constructor.
     * constructor.
     --  inversion H;auto with T2.
     --  apply IHa3.
         inversion H;auto with T2.
  + inversion 1.
Qed.


Theorem epsilon0_as_lub : forall b, nf b -> 
                                    (forall a, lt_epsilon0 a -> lt a b) ->
                                    le epsilon0 b.
Proof.
 intros y Vy Hy; tricho epsilon0 y H.
 -  right;auto with T2.
 -  left;auto with T2.
 - assert (lt_epsilon0 y).
   { apply lt_epsilon0_okR;auto with T2. }
 generalize (Hy _ H0); intro; case (lt_irr (alpha:= y)); auto with T2.
Qed.



Definition lub (P: T2 -> Prop)(x:T2) :=
  nf x /\ 
  (forall y, P y -> nf y -> y t2<= x) /\
  (forall y, (forall x, P x -> nf x -> x t2<= y) -> nf y ->
                                    x t2<= y).

Theorem lub_unicity : forall P l l', lub P l -> lub P l' -> l = l'.
Proof.
 intros P l l' (H1,(H2,H3)) (H'1,(H'2,H'3)).
 tricho l l' H4; trivial.
 -  absurd (l t2< l).
    apply lt_irr.
    apply lt_le_trans with l';auto with T2.
 -  absurd (l' t2< l').
    apply lt_irr.
    apply lt_le_trans with l;auto with T2.
Qed.

Theorem lub_mono : forall (P Q :T2 -> Prop) l l', 
    (forall o, nf o -> P o -> Q o) ->
    lub P l -> lub Q l' -> l t2<= l'.
Proof.
 intros P Q l l' H (H1,(H2,H3)) (H'1,(H'2,H'3)).
 auto with T2.
Qed.


Lemma succ_limit_dec : forall a, nf a ->
         {a = zero} +{is_successor  a}+{is_limit a}.
Proof.
 intro a;elim a.
 - left;left;auto.
 -  intro alpha;case alpha;intro.
  +  intro beta;case beta;intro.
     * intros; assert (t=zero).
       { inversion H2;auto. 
         inversion H7;lt_clean. }
       subst t;left;right.
       constructor.
     *  destruct n0;destruct t2.
    --  right;constructor; auto with T2.
        nf_inv.
    --  intros H1 H2;case H1.
    ++  nf_inv.
    ++  destruct 1.
        discriminate e.
        left;right.
        constructor;auto with T2.
    ++ right; constructor; auto.
    --  right; constructor;auto with T2.
        nf_inv.
    -- intros H1 H2;case H1.
       ++  nf_inv.
       ++ destruct 1.
          discriminate e.
          left;right;constructor.
          auto with T2.
          auto with T2.
       ++  right;constructor;auto with T2.
  + intros; case H1.
  *  nf_inv.
  *  destruct 1.
     --  subst t3;right;constructor;auto with T2.
         nf_inv.
         nf_inv.
     --  left;right;constructor;auto with T2.
  * right;constructor;auto with T2.
Qed.

 
Lemma le_plus_r : forall alpha beta, nf alpha -> nf beta -> 
                                     alpha t2<= alpha + beta.
Proof.
  induction alpha.
  -  intros;apply le_zero_alpha.
  -  destruct beta.
     +  intros; rewrite plus_alpha_0;auto with T2.
     +  cbn; intros; 
          case_eq (compare (gcons alpha1 alpha2 0 zero)
                           (gcons beta1 beta2 0 zero)).
        *  right;constructor 6; lia.
        *  intros;right;apply psi_lt_head.
           apply compare_Lt; auto with T2.
        *  intro; apply le_cons_tail.
           apply IHalpha3.
           --  inversion H;auto with T2.
           --  auto with T2.
Qed.

Lemma le_plus_l : forall alpha beta, nf alpha -> nf beta -> 
                                     alpha t2<= beta +  alpha.
Proof.
 induction alpha.
 - intros;apply le_zero_alpha.
 -  destruct beta.
  + cbn;auto with T2.
  + cbn; intros; 
   case_eq(compare (gcons beta1 beta2 0 zero) (gcons alpha1 alpha2 0 zero)).
    * intros; generalize (compare_Eq  H1).
     injection 1.
     intros;subst beta1;subst beta2.
     right;constructor 6; lia.
    * left;auto with T2.
    * intros;right;apply psi_lt_head.
      apply compare_Gt; auto with T2.
Qed.


Lemma plus_mono_r : forall alpha , nf alpha -> forall beta gamma, nf beta ->
       nf gamma -> beta t2< gamma -> alpha + beta t2< alpha + gamma.
Proof.
 induction alpha.
 -  cbn; auto with T2.
 - cbn; destruct beta;destruct gamma;cbn.
   + inversion 3.
   + intros; 
       case_eq (compare (gcons alpha1 alpha2 0 zero)
                          (gcons gamma1 gamma2 0 zero)).
     * constructor 6; lia.
     * intros;apply psi_lt_head.
       apply compare_Lt;auto with T2.
     *  constructor 7.
        pattern alpha3 at 1; rewrite <- plus_alpha_0. 
        apply IHalpha3.
        inversion H;auto with T2.
        auto with T2.
        auto with T2.
        auto with T2.
   +  inversion 3.
   + case_eq (compare (gcons alpha1 alpha2 0 zero)
                      (gcons beta1 beta2 0 zero));
       case_eq (compare (gcons alpha1 alpha2 0 zero)
                        (gcons gamma1 gamma2 0 zero)).
     intros H0 H1 H2 H3 H4;  generalize (compare_Eq  H1);
     generalize (compare_Eq  H0).
     * injection 1.
       injection 3.
       subst gamma1;subst gamma2;intros; subst beta2;subst beta1.
       inversion_clear H4.
       case (lt_irr H6).
       case (lt_irr H6).
       case (lt_irr H6).
       case (lt_irr H6).
       constructor 6;lia.
       constructor 7;auto with T2.
       * intros H0 H1 H2 H3 H4;  generalize (compare_Lt  H0);
           generalize (compare_Eq  H1).
         intros;apply psi_lt_head.
         auto with T2.
         * intros.
           generalize (compare_Gt  H0).
           generalize (compare_Eq  H1).
           injection 1;intros.
           subst beta1;subst beta2.
           case (lt_irr (alpha := (gcons alpha1 alpha2 n0 beta3))).
           eapply lt_trans.
           eexact H4.
           apply psi_lt_head;auto with T2.
           * intros.
             generalize (compare_Lt  H1).
             generalize (compare_Eq  H0).
             injection 1;intros.
             subst gamma1;subst gamma2.
             case (lt_irr (alpha :=gcons beta1 beta2 n0 beta3)).
             eapply lt_trans.
             eexact H4.
             apply psi_lt_head;auto with T2.
           * auto with T2.
           * intros; case (lt_irr (alpha := (gcons beta1 beta2 n0 beta3))).
             eapply lt_trans.
             eexact H4.
             apply psi_lt_head.
             apply lt_trans with (gcons alpha1 alpha2 0 zero);auto with T2.
           * intros;  generalize (compare_Eq  H0).
             injection 1;intros;subst gamma1;subst gamma2.
             constructor 6;lia.
           * intros; apply psi_lt_head.
             auto with T2.
           * intros; constructor 7.
             apply IHalpha3.
             inversion H;auto with T2.
             auto with T2.
             auto with T2.
             auto with T2.
Qed.


Lemma plus_mono_l_weak: 
  forall o, nf o ->
    forall alpha,  nf alpha -> alpha t2< o -> 
                   forall beta,
                     nf beta -> beta t2< o ->
                     forall gamma , nf gamma -> 
                                    alpha t2< beta ->
                                    alpha + gamma t2<= beta + gamma.
Proof.
 intros o Ho;pattern o.
 apply transfinite_induction; [| auto with T2].
 clear o Ho; intros o NF0 Hreco. 
 intro x;case x.
 - cbn;  intros;apply le_plus_l;auto with T2.
 - intros alpha beta n gamma NF.
   intro; intro y;case y.
   + inversion 4.
   + intros alpha' beta' n' gamma' NF'  H1  z; case z.
     do 2 rewrite (plus_alpha_0).
     right;auto with T2.
       intros alpha'' beta'' n'' gamma''  NF'' H0.
       simpl (gcons alpha beta n gamma + gcons alpha'' beta'' n'' gamma'').
       case_eq ( compare [alpha, beta] [alpha'', beta'']).
       intro H'; generalize  (compare_Eq  H'); intro H''.
       injection H'';intros.
       subst alpha'';subst beta''.
       simpl (gcons alpha' beta' n' gamma' + gcons alpha beta n'' gamma'').
       case_eq ( compare [alpha', beta'] [alpha, beta]).
       intro H6; generalize  (compare_Eq  H6); intro H7.
       injection H7;intros;subst alpha';subst beta'.
       case (le_inv_nc (or_intror _ H0)).
     * right;constructor 6.
        auto with T2 arith.
     * intros (H8,H9);subst n';left;auto with T2.
     * intro H6; generalize  (compare_Lt  H6); intro H7.
       case (lt_irr (alpha := gcons alpha beta n gamma)).
       apply lt_trans with (gcons alpha' beta' n' gamma');auto with T2.
       apply psi_lt_head;auto with T2.
     * intros;right;apply psi_lt_head.
       apply compare_Gt;auto with T2.
     * intro H'; generalize  (compare_Lt  H'); intro H''.
       simpl (gcons alpha' beta' n' gamma' + gcons alpha'' beta'' n'' gamma'').
       case_eq (compare [alpha', beta'] [alpha'', beta'']).
      -- intro H6; generalize  (compare_Eq  H6); intro H7.
         injection H7;intros;subst alpha';subst beta'.
         right;constructor 6;auto with T2 arith.
      -- intro H6; generalize  (compare_Lt  H6); intro H7.
         left;auto with T2.
      -- intro H6; generalize  (compare_Gt  H6); intro H7.
         right;apply psi_lt_head;auto with T2.
     * intro H'; generalize  (compare_Gt  H'); intro H''.
       assert ([alpha'',beta''] t2< [alpha',beta']). {
         apply lt_le_trans with [alpha,beta];auto with T2.
         generalize (le_psi_term_le (or_intror _ H0)).
         cbn;auto with T2.
       }
       simpl ( gcons alpha' beta' n' gamma' +
               gcons alpha'' beta'' n'' gamma'').
       case_eq ( compare [alpha', beta'] [alpha'', beta'']).
      -- intro H6; generalize  (compare_Eq  H6); intro H7.
         rewrite H7 in H2.
         case (lt_irr H2).
      -- intro H6; generalize  (compare_Lt  H6); intro H7.
         case (lt_irr (alpha := [alpha'', beta''])).
         apply lt_trans with [alpha', beta'];auto with T2.
      -- intro H6; generalize  (compare_Gt  H6); intro H7.
         tricho [alpha, beta] [alpha', beta'] H8.
         ++ right;apply psi_lt_head;auto with T2.
         ++ injection H8;intros;subst alpha';subst beta'.
            case (le_inv_nc  (or_intror _ H0)).
            ** right;constructor 6;auto with T2.
            ** intros (e,H9);subst n'; case H9.
               intro;subst gamma'.
               left;auto with T2.
               intro H10;assert (nf gamma).
               { inversion NF;auto with T2. }
               assert (nf gamma').
               { inversion NF';auto with T2. }
               assert (gamma t2<  gcons alpha beta n gamma').
               apply lt_trans with gamma'.
               auto with T2.
               apply lt_tail;auto with T2.
               generalize
                 (Hreco  _ NF' H1 gamma H3 H5 gamma'
                         H4 (lt_tail NF')
                         (gcons alpha'' beta'' n'' gamma'') NF'' H10).
               destruct 1;auto with T2.
               rewrite H11;auto with T2.
         ++ case (lt_irr (alpha := gcons alpha beta n gamma)).
            apply lt_trans with (gcons alpha' beta' n' gamma');auto with T2.
            apply psi_lt_head;auto with T2.
Qed.


Remark R_pred_Sn : forall n, pred (fin (S n)) = Some (fin n).
Proof.
 destruct n;cbn;trivial.
Qed.

Lemma pred_of_cons : forall a b n c, 
                       zero t2< a \/ zero t2< b -> 
                       pred (gcons a b  n c) = match pred c with
                                             Some c' => 
                                               Some (gcons a b n c')
                                            | None => None
                                            end.
Proof.
  destruct a.
  -  destruct b;cbn.
    destruct 1;lt_clean.
    auto.
  -  cbn; auto.
Qed.

Lemma pred_of_cons' : forall a b n , 
                       zero t2< a \/ zero t2< b -> 
                       pred (gcons a b  n zero) = None.
Proof.
 intros a b n H; rewrite (pred_of_cons n zero H).
 cbn;auto.
Qed.


Lemma is_limit_ab : forall alpha beta n gamma,
    is_limit (gcons alpha beta n gamma)
    -> zero t2< alpha \/ zero t2< beta.
Proof.
  inversion 1; [trivial |].
  generalize H5 H2 ;case gamma.
  -  inversion 2.
  -  inversion_clear 1.
     inversion_clear H7.  
     + left;apply le_lt_trans with t;auto with T2.
     + right; apply le_lt_trans with t0;auto with T2.
     + right;  apply le_lt_trans with [t,t0];auto with T2.
     +  right;apply le_lt_trans with t;auto with T2.
     + lt_clean.
     + lt_clean.
Qed.
 

Lemma pred_of_limit : forall alpha,
    is_limit alpha -> nf alpha -> pred alpha = None.
Proof.
 induction 1.
 - rewrite (pred_of_cons' n H); trivial.
  - rewrite (pred_of_cons (a :=alpha)(b:=beta) n).
    + rewrite IHis_limit; auto.
       eapply nf_c;eauto.
    + apply is_limit_ab with n gamma; constructor;auto.
Qed.
 


Lemma pred_of_succ : forall alpha, nf  alpha -> 
            pred (succ alpha) = Some alpha.
Proof.
  induction alpha;cbn.
  - trivial. 
  - case alpha1;case alpha2.
    + cbn.
      inversion_clear 1;auto with T2.
      inversion H0.
      inversion H5.
      inversion H4.
      inversion H12.
      inversion H4.
      inversion H4.
    + cbn.
      intros;rewrite IHalpha3.
      auto with T2.
      inversion H;auto with T2.
    + cbn;  intros;rewrite IHalpha3.
      reflexivity. 
      inversion H;auto with T2.
    + cbn;  intros;rewrite IHalpha3; trivial.
      inversion H;auto with T2.
Qed.




Lemma limit_plus_fin_ok : forall alpha,  is_limit alpha ->
                           forall n, limit_plus_fin alpha n (alpha + fin n).
Proof.
induction alpha.
 - cbn;constructor 1.
 - cbn; inversion 1.
  + intro n1;case n1.
    *  cbn; constructor 2;auto.
      change (limit_plus_fin zero 0 (fin 0)).
      constructor 1.
    *  cbn; case_eq (compare [alpha1, alpha2] [zero, zero]).
       --  intro H7; generalize (compare_Eq H7).
           injection 1;intros;subst alpha1;subst alpha2.
           subst alpha;subst beta.
           case H3;intro;lt_clean.
       -- intro H7; generalize (compare_Lt H7).
          inversion 1;intros;try lt_clean.
       --  cbn; intros;
             change (limit_plus_fin (gcons alpha1 alpha2 n zero) (S n2)
                                  (gcons alpha1 alpha2 n (fin (S n2)))).
           constructor.
           auto.
           constructor.
  +  destruct n1.
     *  cbn; constructor 2.
        -- eapply is_limit_ab.
           eexact H.
        --  generalize H2; generalize (nf_c H5);  elim alpha3.
            intros; change ( limit_plus_fin zero 0 (fin 0));constructor.
            constructor.
            eapply is_limit_ab.
            eexact H10.
            case (is_limit_cons_inv H9 H10).
            intros; apply H8.
            nf_inv.
            auto.
            intro;subst t1;change (limit_plus_fin zero 0 (fin 0));constructor.
            * cbn; case_eq (compare [alpha1, alpha2] [zero, zero]).
              intro H7;generalize (compare_Eq H7);injection 1;intros.
              subst alpha1;subst alpha2;subst beta;subst alpha.
              generalize (is_limit_ab H).
              destruct 1;lt_clean.
              intro H7;generalize (compare_Lt H7);intros.
              inversion H6;lt_clean.
              intro.
              replace (gcons zero zero n1 zero) with (fin (S n1)).
              constructor 2.
              generalize (compare_Gt H6);intros.
              inversion_clear H7;auto with T2.
              lt_clean.
              lt_clean.
              apply IHalpha3.
              auto.
              auto.
Qed.

Section phi_to_psi.
 Variable alpha : T2.

 Lemma phi_to_psi_1 : forall beta1 beta2 n, 
     alpha t2< beta1 -> 
     [alpha, (gcons beta1 beta2 0 (fin n))] =
     phi alpha (gcons beta1 beta2 0 (fin (S n))).
 Proof.
   intros;  generalize (phi_of_psi_succ alpha beta1 beta2 n).
   case (lt_ge_dec alpha beta1).
   - auto with T2.
   - intro; absurd (alpha t2< alpha).
     apply lt_irr.
     eapply lt_le_trans;eauto with T2.
 Qed.

 Lemma phi_to_psi_2 : forall beta1 beta2 n, 
     beta1 t2<= alpha  -> 
     [alpha, (gcons beta1 beta2 0 (fin n))] =
     phi alpha (gcons beta1 beta2 0 (fin n)).
   Proof.
   intros; case n.
   -   simpl (fin 0);  generalize (phi_of_psi alpha beta1 beta2).
       case (lt_ge_dec alpha beta1). 
       intro; (absurd (alpha t2< alpha)). 
       + apply lt_irr.
       +   eapply lt_le_trans;eauto with T2.
       + auto with T2.
   - intro n0;generalize (phi_of_psi_succ alpha beta1 beta2 n0).
     case (lt_ge_dec alpha beta1).
     +    intro;  absurd (alpha t2< alpha).
          apply lt_irr.
          eapply lt_le_trans;eauto with T2.
      + auto with T2.
 Qed.

 Lemma phi_to_psi_3 : forall  beta1 beta2 , 
                             beta1 t2<= alpha  -> 
                             [alpha, [beta1, beta2]] =
                             phi alpha [beta1, beta2].
 Proof.
   intros; fold (fin 0); apply phi_to_psi_2; auto with T2.
Qed.

Lemma phi_to_psi_4 : [alpha, zero] = phi alpha zero.
Proof.
  rewrite phi_alpha_zero;auto with T2.
Qed.

Lemma phi_to_psi_5 :
   forall beta1 beta2 n gamma, omega t2<= gamma \/ (0 < n)%nat ->
           [alpha,gcons beta1 beta2 n gamma] =
           phi alpha (gcons beta1 beta2 n gamma).
Proof.
 intros; rewrite phi_of_any_cons;auto with T2.
Qed.

Lemma phi_to_psi_6 : forall beta, nf beta ->
                                  phi alpha beta = beta ->
                                  [alpha, beta] = phi alpha (succ beta).
Proof.  
 intros; case (phi_fix _ H0 ).
 intros beta1 (beta2,(H2,H3)); subst beta.
 generalize (phi_to_psi_1 beta2  0 H3).  
  simpl (succ (gcons beta1 beta2 0 zero)); generalize H3 ; case beta1.
  inversion 1.
  auto with T2.
Qed.


(* gamma = gamma0 + fin p, gamma0 = zero or gamma0 limit *)


 
Lemma phi_psi : forall  beta gamma n, nf gamma ->
  limit_plus_fin beta n gamma ->  phi alpha beta = beta ->
                           [alpha, gamma]  =  phi alpha (succ gamma).
Proof.
 intros; case (phi_fix _ H1).
  intros beta1 (beta2,(H2,H3)).
 assert (gamma = (gcons beta1 beta2 0 (fin n))).
 {
subst beta.
 inversion H0.
 inversion H9.
 auto with T2.
 inversion H10.
 auto with T2.
 inversion H10;auto with T2.
 }
 subst gamma.
   cbn; subst beta; generalize H3 H1.
   case beta1;case beta2.
   -   inversion 1.
   -   inversion 2.
       inversion H2.
   -   replace (succ (fin n)) with (fin (S n)).
       + intros;rewrite phi_to_psi_1; auto with T2.
       + induction n;cbn;auto with T2.
   -  replace (succ (fin n)) with (fin (S n)).
      intros;rewrite phi_to_psi_1; auto with T2.
   induction n;cbn;auto with T2.
Qed.

Theorem th_14_5 : forall alpha1 beta1 alpha2 beta2,
                   nf alpha1 -> nf beta1 -> nf alpha2 -> nf beta2 ->
                   phi alpha1 beta1 = phi alpha2 beta2 ->
                   {alpha1 t2< alpha2 /\ beta1 = phi alpha2 beta2} +
                   {alpha1 = alpha2 /\ beta1 =  beta2} +
                   {alpha2 t2< alpha1 /\ phi alpha1 beta1 = beta2}.
Proof.
 intros alpha1 beta1 alpha2 beta2 nfa1 nfb1 nfa2 nfb2 E.
 tricho alpha1 alpha2 H0.
 -  generalize (phi_to_psi alpha2 beta2).
    intros (gamma1, (gamma2, E')).
    assert (alpha2 t2<= gamma1). {
      eapply phi_le; [| eexact E'].
      auto.
    }
    left.
    left;split;auto.
    assert (phi alpha1 (phi alpha2 beta2) = phi alpha2 beta2).
    {
      repeat rewrite E'.
      cbn.
      generalize (lt_le_trans H0 H);intro H1.
      rewrite (compare_rw_lt H1).
      auto.
    }
    pattern (phi alpha2 beta2) at 2 in H1.
    rewrite <- E in H1.
    apply phi_inj_r with alpha1;auto.
    apply phi_nf;auto.
 - subst alpha2; left; right.
   split;auto.
   apply phi_inj_r with alpha1;auto.
 -  generalize (phi_to_psi alpha1 beta1).
    intros (gamma1, (gamma2, E')).
    assert (alpha1 t2<= gamma1). {
      apply phi_le with beta1 gamma2; auto.
    }
    right. 
    split;auto.
    assert (phi alpha2 (phi alpha1 beta1) = phi alpha1 beta1).
    { repeat rewrite E'.
      cbn; generalize (lt_le_trans H0 H);intro H1.
      rewrite (compare_rw_lt H1).
      auto.
    }
    pattern (phi alpha1 beta1) at 2 in H1.
    rewrite E in H1.
    apply phi_inj_r with alpha2;auto.
    apply phi_nf;auto.
Qed.

Lemma lt_not_gt : forall a b, a t2< b -> ~ (b t2< a).
Proof.
  intros a b H H0.
  case (lt_irr (alpha := a));auto.
  apply lt_trans with b;auto.
Qed.

Lemma phi_mono_RR : forall a b c, nf a -> nf b -> nf c ->
              phi a b t2< phi a c -> b t2< c.
 Proof.
  intros;tricho b c T;auto.
  subst c. case (lt_irr H2).
  case (lt_not_gt H2).
  apply phi_mono_r;auto.
 Qed.

Theorem th_14_6 : forall alpha1 beta1 alpha2 beta2,
                   nf alpha1 -> nf beta1 -> nf alpha2 -> nf beta2 ->
                   phi alpha1 beta1 t2< phi alpha2 beta2 ->
                   {alpha1 t2< alpha2 /\ beta1 t2< phi alpha2 beta2} +
                   {alpha1 = alpha2 /\ beta1 t2<  beta2} +
                   {alpha2 t2< alpha1 /\ phi alpha1 beta1 t2< beta2}.
Proof.
  intros alpha1 beta1 alpha2 beta2 nfa1 nfb1 nfa2 nfb2 E.
  tricho alpha1 alpha2 H0.
  -  generalize (phi_to_psi alpha2 beta2).
     intros (gamma1, (gamma2, E')).
     assert (alpha2 t2<= gamma1).
     { eapply phi_le; [| eexact E'].
       auto.
     }
     left.
     left;split;auto.
     apply le_lt_trans with (phi alpha1 beta1);auto.
     apply le_b_phi_ab;auto.
  - subst alpha2;left;right.
    split;auto.
    tricho beta1 beta2 H;auto.
   +  subst beta2;case (lt_irr E).
   + case (lt_not_gt E).
     apply phi_mono_r;auto.
  -  right;  split;auto. 
     generalize (phi_to_psi alpha1 beta1).
     intros (gamma1, (gamma2, E')).
     assert (alpha1 t2<= gamma1). {
       apply phi_le with beta1 gamma2;  auto.
     }
     assert (alpha2 t2< gamma1). {
       apply lt_le_trans with alpha1;auto.
    }
     assert (phi alpha2 (phi alpha1 beta1) = phi alpha1 beta1).
     {
       repeat rewrite E'.
       cbn.
       rewrite (compare_rw_lt H1).
       auto.
     }
     assert (phi alpha2 (phi alpha1 beta1) t2< phi alpha2 beta2).
     eapply le_lt_trans.
     eleft;eexact H2.
     auto.
     apply phi_mono_RR with alpha2;auto.
     apply phi_nf;auto.
Qed.


Definition moser_lepper (beta0 beta:T2)(n:nat) :=
 limit_plus_fin beta0 n beta /\ phi alpha beta0 = beta0.

Lemma ml_psi : forall beta0 beta n,
    moser_lepper beta0 beta n ->
    {t1 : T2 & {t2: T2| beta0 =
                        [t1,t2] /\ alpha t2< t1}}.
Proof.
 intros beta0 beta n (H1,H2).
 case (phi_fix  _  H2).
  intros x (y,(H3,H4)); exists x;exists y;auto.
Qed.

Lemma ml_1 : forall beta0 beta n, moser_lepper beta0 beta n ->
                                  nf beta -> nf beta0 ->
                               [alpha, beta] = phi alpha (succ beta).
 intros;eapply phi_psi;eauto.
 case H.
 -  intros;eassumption.
 - case H;intros; auto.
Qed.

End phi_to_psi.

Compute phi 0 (epsilon 2)= epsilon 2.

Example Ex9 : [zero, epsilon 2 + 4] = phi 0 (epsilon 2 + 5).
Proof. trivial. Qed.

Example Ex10 : phi omega [epsilon0, 5] = [epsilon0, 5].
Proof. reflexivity. Qed.


Declare Scope g0_scope.

Module G0.

  Definition LT := restrict nf lt.

  Lemma Lt_wf : well_founded LT.
  Proof.
    unfold LT; generalize nf_Wf; split; split.
    intros y0 H1; generalize (nf_Wf); intro H2.
    apply H2; now destruct H1.
  Defined.

(** ** Temporary compatibility  nf/nfb *)

Lemma zero_nfb : nfb zero.
Proof. reflexivity. Qed.



Lemma nfb_a a b n c: nfb (gcons a b n c) -> nfb a.
Proof. 
 cbn.
 destruct c.
 destruct (nfb b),  ( nfb a);cbn; auto.
 destruct (compare [c1, c2] [a, b]);try  discriminate.
  destruct (nfb a); cbn; auto. 
Qed.

Lemma nfb_equiv gamma : nfb gamma = true <-> nf gamma.
Proof.
  induction gamma.
  - cbn; split;auto.
    constructor.  
  - simpl; destruct gamma3; split.
    + case_eq (nfb gamma1); case_eq (nfb gamma2); try discriminate;  
        rewrite IHgamma1 , IHgamma2; try constructor; auto.
    +  inversion_clear 1;  rewrite <- IHgamma1 in H0; rewrite <- IHgamma2 in H1.
       now rewrite H0, H1.
    + case_eq (compare [gamma3_1, gamma3_2] [gamma1, gamma2]); intro Hcompare;
        try discriminate.
      generalize (compare_Lt Hcompare).
      constructor; auto.
      apply andb_prop in H0; destruct H0.
      apply andb_prop in H1; destruct H1.
      tauto.
      apply andb_prop in H0; destruct H0.
      apply andb_prop in H1; destruct H1.
      tauto.
      apply andb_prop in H0; destruct H0.
      apply andb_prop in H1; destruct H1.
      tauto.
    + inversion_clear 1.
      apply compare_rw_lt in H0.    
      rewrite H0.
      rewrite <- IHgamma1 in H1; rewrite H1.
      rewrite <- IHgamma2 in H2; rewrite H2.
      rewrite <- IHgamma3 in H3; rewrite H3.
      reflexivity.    
Qed.

Lemma nfb_proof_unicity :
  forall (alpha:T2) (H H': nfb alpha), H = H'.
Proof.
  intros;  red in H, H';  apply Eqdep_dec.eq_proofs_unicity_on.
  destruct y. 
  - rewrite H; auto. 
  - rewrite H; right; discriminate. 
Qed.

Class G0 := mkg0 {vnf : T2; vnf_ok : nfb vnf}.

Definition lt (alpha beta : G0) := T2.lt (@vnf alpha) (@vnf beta).

Definition compare alpha beta := Gamma0.compare (@vnf alpha) (@vnf beta).


Lemma lt_LT_incl  alpha beta : lt alpha beta -> LT (@vnf alpha) (@vnf beta).
Proof.
  destruct alpha, beta; split; auto; rewrite <- nfb_equiv; auto.
Qed.

Instance lt_sto : StrictOrder lt.
Proof.
  split.
  -  intro x; destruct x; unfold lt; simpl; apply lt_irr.
  -  intros x y z; destruct x, y, z; unfold lt; simpl; apply lt_trans.
Qed.


Lemma lt_wf : well_founded lt.
Proof.
  split; intros [t Ht] H.
  eapply Acc_incl with (fun x y =>  LT (@vnf x) (@vnf y)).
  intros x y H0;  apply lt_LT_incl; auto.
  apply (Acc_inverse_image _ _ LT (@vnf) 
                           {| vnf := t; vnf_ok := Ht |} ),  Lt_wf. 
Qed.


Lemma compare_correct alpha beta :
  CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
              (compare alpha beta).
Proof.
  destruct alpha, beta; cbn.
  destruct (Gamma0.compare_correct vnf0 vnf1);subst. 
  unfold compare; simpl.
  -  rewrite compare_rw_eq; auto.
   + constructor 1; f_equal; apply nfb_proof_unicity.
  - unfold compare; rewrite compare_rw_lt; auto.
  - unfold compare; rewrite compare_rw_gt; auto.
Qed. 

Instance Zero : G0.
Proof.
  refine (@mkg0 T2.zero _);  now compute. 
Defined.

Instance Omega : G0.
Proof.
  exists omega. reflexivity. 
Defined.

Notation "'omega'" := Omega : g0_scope.

Instance Gamma0: ON lt  compare.
Proof.
  split.
  - apply lt_sto.
  - apply lt_wf. 
  - apply compare_correct.
Qed.


Instance Finite (n:nat) : G0.
Proof.
  exists (fin n);  red; rewrite nfb_equiv;  apply nf_fin.
Defined.

Instance Plus (alpha beta : G0) : G0.
Proof.
  destruct alpha, beta. exists (vnf0 + vnf1).
  red in vnf_ok0, vnf_ok1. red. 
  rewrite nfb_equiv in *.
  now apply plus_nf.
Defined. 

Infix "+" := Plus : g0_scope.
  
Coercion Finite : nat >-> G0.

Local Open Scope g0_scope.

Example  L_3_plus_omega :   3 + omega = omega.
now apply compare_Eq_eq.
Qed.

End G0.


