(** * A hierarchy of rapidly growing functions
    After Hardy, Wainer, Ketonen, Solovay, etc .

    Pierre Casteran, LaBRI, University of  Bordeaux *)
From Coq Require Import ArithRing Lia.
From hydras Require Import  E0    Canon Paths.
From hydras Require Import Exp2 Iterates Simple_LexProd.
Import RelationClasses Relations .

From Equations Require Import Equations.

 Open Scope E0_scope.

(** ** The Hardy Wainer hierarchy *)


Instance Olt : WellFounded Lt := Lt_wf.


Equations H_ (alpha: E0) (i:nat) :  nat  by wf  alpha Lt :=
  H_ alpha  i with E0_eq_dec alpha Zero :=
    { | left _ =>  i ;
      | right nonzero
          with Utils.dec (Limitb alpha) :=
          { | left _ =>  H_ (Canon alpha (S i))  i ;
            | right notlimit =>  H_ (Pred alpha) (S i)}}.

Solve All Obligations with auto with E0.


(** Paraphrases of the equations for H_ *)

Lemma H_eq1 : forall i, H_ Zero i = i.
Proof.
  intro i; now rewrite H__equation_1. 
Qed.

Lemma H_eq2 alpha i : Succb alpha ->
                      H_ alpha i = H_ (Pred alpha) (S i).
Proof.
  intros;rewrite H__equation_1.
  destruct (E0_eq_dec alpha Zero).
  - subst; discriminate.
  - cbn;  destruct (Utils.dec (Limitb alpha)) .
    destruct (Succ_not_Limitb _ H); auto.
    + now cbn.
Qed.


Lemma H_eq3 alpha i : Limitb alpha ->
                      H_ alpha i =  H_ (Canon alpha (S i)) i.
Proof.
  intros;rewrite H__equation_1.
  destruct (E0_eq_dec alpha Zero).
 - subst; discriminate.
 - cbn;  destruct (Utils.dec (Limitb alpha)) .
  + now cbn.    
  + red in H; rewrite e in H; discriminate.
Qed.

Lemma H_succ_eqn  alpha i :  H_ (Succ alpha) i = H_ alpha (S i).
Proof.
  rewrite H_eq2.
  - now rewrite Pred_of_Succ.  
  - apply Succ_succb.
Qed.


Hint Rewrite H_eq1  H_succ_eqn : H_rw.

Ltac lim_rw alpha := (assert (Limitb alpha) by auto with E0);
                     rewrite (H_eq3 alpha); auto with E0.



(** Examples : First steps of the hierarchy *)

Lemma H_Fin : forall i k : nat,  H_  (Fin i) k = (i+k)%nat.
Proof with eauto with E0.
  induction i.
  - intros; simpl Fin; simpl; autorewrite with H_rw E0_rw ... 
  - intros ;simpl; autorewrite with H_rw E0_rw ... 
    rewrite IHi; abstract lia. 
Qed.


Lemma H_omega : forall k, H_ omega k = S (2 * k)%nat.
Proof with auto with E0.
  intro k; rewrite H_eq3 ...
  - replace (Canon omega (S k)) with (Fin (S k)).
    + rewrite H_Fin; abstract lia.
    + now autorewrite with E0_rw.
Qed.


Lemma H_Plus_Fin alpha : forall i k : nat,
    H_ (alpha + i)%e0 k = H_ alpha (i + k)%nat.
induction i.
- intro k; ochange (alpha +  0)%e0 alpha.
   + now simpl.
   + rewrite Plus_rw; simpl; auto with T1.
     now rewrite plus_a_zero.
 - intro k; ochange (alpha + (S i))%e0 (Succ (alpha + i))%e0.
   + rewrite H_succ_eqn, IHi; f_equal; abstract lia.
   + repeat rewrite Plus_rw; simpl.
     destruct i; simpl.
    *  rewrite plus_a_zero;  now rewrite succ_is_plus_one.
    *   simpl; replace (FS i) with (fin (S i)).
        -- rewrite succ_of_plus_finite.
           ++ f_equal.
           ++ apply cnf_ok.
        --  reflexivity.
Qed.

Lemma H_omega_double k : H_ (omega * 2)%e0 k =  (4 * k + 3)%nat.
Proof.
 rewrite H_eq3; simpl Canon.
 -   ochange  (CanonS  (omega * FinS 1)%e0 k)  (omega + (S k))%e0.
   
  + rewrite H_Plus_Fin, H_omega;  abstract lia.
  -  now compute.
Qed.

Lemma H_omega_3 k : H_ (omega * 3)%e0 k = (8 * k + 7)%nat.
Proof.
  rewrite H_eq3 ; [| reflexivity].
  ochange (Canon  (omega * 3)%e0 (S k)) (omega * 2 + FinS k)%e0.
  rewrite FinS_eq,  H_Plus_Fin, H_omega_double; abstract lia.  
Qed.

Lemma H_omega_4 k : H_ (omega * 4)%e0 k = (16 * k + 15)%nat.
Proof.
  rewrite H_eq3 ; [| reflexivity].
  ochange (Canon  (omega * 4)%e0 (S k)) (omega * 3 + FinS k)%e0.
  rewrite FinS_eq,  H_Plus_Fin, H_omega_3; abstract lia.
Qed.

Lemma H_omega_i (i:nat)  : forall k,
    H_ (omega * i)%e0 k = (exp2 i * k + Nat.pred (exp2 i))%nat.
Proof.
  induction i.
  - ochange (omega * 0)%e0 Zero; simpl.
    intro k; rewrite H_eq1; abstract lia.
  - intro k; rewrite H_eq3.
    +  ochange (Canon (omega * S i)%e0  (S k)) (omega * i + (S k))%e0.
       rewrite H_Plus_Fin, IHi.
        simpl (exp2 (S i)); abstract lia.
        simpl Canon;  destruct i;reflexivity.
    + reflexivity.
Qed.


(** Let us note that the square of omega can be expressed through the
    Phi0 function *)


Remark Phi0_def : Phi0 2 = ltac:(mko (omega * omega)%t1).
Proof. apply E0_eq_intro. reflexivity. Qed.


Lemma H_omega_sqr : forall k,
    H_ (Phi0  2)%e0 k = (exp2 (S k ) * (S k) - 1)%nat.
Proof.
  intro k; 
   rewrite H_eq3; auto with E0.
  - ochange (Canon (Phi0 2) (S k)) (omega * (S k))%e0.
    +  rewrite H_omega_i; simpl (exp2 (S k)).
       *  rewrite Nat.add_pred_r.
          -- abstract lia. 
          --   generalize (exp2_not_zero k);  abstract lia.
    + cbn; f_equal; abstract lia.
Qed.

(** Composition lemma *)

Section H_cons.
Variable alpha : E0.
Variable i : nat.
 
Lemma H_cons : forall beta,  (beta o< Phi0 alpha)%e0 ->
                             forall k,  H_ (Ocons alpha i beta) k=
                                        H_ (Omega_term alpha i) (H_ beta k).
Proof with auto with E0.
  unfold Ocons; intro beta; pattern beta; 
  apply well_founded_induction with Lt; clear beta.
  - exact E0.Lt_wf.
  -  intros beta Hbeta H;  destruct (Zero_Limit_Succ_dec beta).
     destruct s.
     + subst; intro k. autorewrite with H_rw E0_rw using trivial. 
     + intro k;  assert (CanonS  (Omega_term alpha i + beta)%e0 k =
                          (Omega_term alpha  i + (CanonS beta k))%e0).
       {  rewrite CanonS_plus_1; auto with E0.           
          intro; subst alpha; red in H;  simpl in H;  apply LT_one in H.
          unfold Limitb in e; rewrite H in e; discriminate e.
       }
       rewrite H_eq3, CanonS_Canon, H0.
       specialize (Hbeta (CanonS beta k)).
       assert (CanonS beta k o< beta)%e0 by auto with E0.
       assert (CanonS beta k o< Phi0 alpha)%e0 by (eapply Lt_trans; eauto).
       now rewrite (Hbeta H1 H2 k), (H_eq3 beta).
       apply Limitb_plus; auto.
     +   intro k; destruct s as [gamma Hgamma]; subst.
         specialize (Hbeta gamma).
         assert (gamma o< Succ gamma)%e0 by (apply Lt_Succ; auto).
         assert (gamma o< Phi0 alpha)%e0 .
         { apply Lt_trans with (Succ gamma); auto. }
         rewrite (H_succ_eqn gamma);
           replace (Omega_term alpha i + Succ gamma)%e0 with
               (Succ (Omega_term alpha i + gamma)%e0).
         rewrite H_succ_eqn, Hbeta;  auto.
         apply E0_eq_intro; rewrite Succ_cons; auto.
         intro; subst; red in H; simpl in H.
         destruct H as [H [H2 H3]]; apply lt_one in H2.
         destruct (succ_not_zero _ H2).
Qed.


Lemma H_Omega_term_1 : alpha <> Zero -> forall  k,  
    H_ (Omega_term alpha (S i)) k =
    H_ (Omega_term alpha i) (H_ (Phi0 alpha) k).
Proof with auto with E0.
  intros  H k;  rewrite H_eq3 ...
  rewrite CanonS_Canon.
  - ochange (CanonS (Omega_term alpha (S i)) k)
          (Ocons alpha i (CanonS  (Phi0 alpha) k)).
  +  rewrite H_cons ...
     *  f_equal; rewrite (H_eq3 (Phi0 alpha)) ...
  +  rewrite cnf_Ocons ...
           * unfold CanonS; repeat rewrite cnf_rw.
             rewrite cnf_Omega_term, cnf_Phi0.
             unfold Omega_term; simpl.
             destruct (cnf alpha) ...
             destruct (pred (ocons t1 n t2)) ...
  -   apply Limitb_Omega_term ...
Qed.

End H_cons.


Lemma H_Omega_term_0 (alpha : E0)  :
alpha <> Zero ->  forall i k, 
  H_ (Omega_term alpha i) k = iterate  (H_ (Phi0 alpha)) (S i) k.
Proof.
  induction i.
  - reflexivity.                                       
  - intros; rewrite H_Omega_term_1, IHi; trivial; now rewrite <- iterate_rw.
Qed.

Lemma H_Fin_iterate : forall i k,
    H_ (Fin (S i)) k = iterate (H_ (Fin 1)) (S i) k.
  
  intros; repeat rewrite H_Fin.
   replace (iterate (H_ 1) (S i) k) with (iterate S (S i) k).
  induction i; cbn.
   auto.
simpl Nat.add in IHi.    rewrite IHi.
 f_equal. 
 Search iterate.
apply iterate_ext.
intro; rewrite H_Fin.
auto. 
Qed.

Lemma H_Omega_term (alpha : E0)  :
  forall i k, 
    H_ (Omega_term alpha i) k = iterate  (H_ (Phi0 alpha)) (S i) k.
Proof.
  destruct (E0_eq_dec alpha Zero).
  - subst.
    intros; replace (Omega_term Zero i) with (Fin (S i)).
    replace (Phi0 Zero) with (Fin 1).
    now rewrite H_Fin_iterate.
    compute. now apply E0_eq_intro.
    compute. now apply E0_eq_intro.
  - intros; now apply  H_Omega_term_0.
Qed.

Definition H_succ_fun f k := iterate f (S k) k.

Lemma H_Phi0_succ_1 alpha  : alpha <> Zero -> forall k,
      H_ (Phi0 (Succ alpha)) k = H_succ_fun (H_ (Phi0 alpha)) k. 
Proof with auto with E0.
  intros; unfold H_succ_fun ;
    rewrite H_eq3, CanonS_Canon, CanonS_Phi0_Succ_eqn, H_Omega_term ...
Qed.

Lemma H_Phi0_succ_0 : forall k,
    H_ (Phi0 (Succ Zero)) k = H_succ_fun (H_ (Phi0 Zero)) k.
  Proof with auto with E0.
intros k.    
  replace (Phi0 Zero) with (Fin 1).
  Search H_ Phi0.
  replace (Phi0 (Succ Zero)) with omega.
   Search H_ omega.
 rewrite H_omega.
   unfold H_succ_fun.
   Search (H_ 1).
   transitivity (iterate S (S k) k).
   replace (S (2 * k))%nat with (S k + k)%nat.
   generalize (S k).   
 induction n.
  now cbn.
  cbn. now rewrite  IHn.
  lia.
  apply iterate_ext.
   intro x.
    
now rewrite H_Fin.
  apply E0_eq_intro.
  reflexivity. 
  apply E0_eq_intro.
  reflexivity. 
Qed.

  Lemma H_Phi0_succ alpha  : forall k,
      H_ (Phi0 (Succ alpha)) k = H_succ_fun (H_ (Phi0 alpha)) k. 
  destruct (E0_eq_dec alpha Zero).  
  subst.
apply H_Phi0_succ_0.

  now apply H_Phi0_succ_1.
  Qed.
  
  Lemma H_Phi0_Si : forall i k,
      H_ (Phi0 (S i)) k = iterate H_succ_fun i (H_ omega) k. 
Proof with auto with E0.
 induction i.
 - simpl;  replace (Phi0 (FinS 0)) with omega; auto;  orefl.   
 -  intro k;  rewrite <- FinS_eq, FinS_Succ_eq. (* lourd *)
   rewrite H_Phi0_succ, iterate_S_eqn.
   apply iterate_ext; auto.
Qed.

Lemma H_omega_cube : forall k,
    H_ (Phi0 3)%e0 k = iterate (H_ (Phi0 2))  (S k) k.
Proof.
  intro k; rewrite <-FinS_eq, -> FinS_Succ_eq, H_Phi0_succ; auto.
Qed.

Section H_omega_cube_3.
  
Let f k :=   (exp2 (S k ) * (S k) - 1)%nat.

Remark R0 k :  H_ (Phi0 3)%e0 k = iterate f (S k) k.
Proof.
  ochange (Phi0 3) (Phi0 (Succ 2)); rewrite H_Phi0_succ.
  unfold H_succ_fun; apply iterate_ext.
  - intro x; now rewrite H_omega_sqr.   
Qed.

Fact F0 : H_ (Phi0 3) 3 = f (f (f (f 3))).
 rewrite R0; reflexivity. 
Qed.

Let N := (exp2 64 * 64 - 1)%nat.

(*
# (2.0 ** 64.0 *. 64.0 -. 1.0);; 
- : float = 1.1805916207174113e+21
*)

Fact F1 : H_ (Phi0 3) 3 = f (f N).
Proof.
 rewrite F0; reflexivity. 
Qed.


Lemma F1_simpl : H_ (Phi0 3) 3 =
                 (exp2 (exp2 (S N) * S N) * (exp2 (S N) * S N) - 1)%nat.
Proof.
  rewrite F1; unfold f.
  assert (forall k,  k <> 0 -> (S  (k -1) = k)%nat) by lia.
  rewrite (H (exp2 (S N) * S N)%nat).
  - reflexivity. 
  - apply Nat.neq_mul_0; split.
    + apply  exp2_not_zero.
    + discriminate.
Qed.


 
End H_omega_cube_3.


Lemma H_Phi0_omega : forall k, H_ (Phi0 omega) k =
                               iterate H_succ_fun  k (H_ omega) k.
Proof with auto with E0.
  intro k; rewrite H_eq3,  <- H_Phi0_Si ...
  -  rewrite CanonS_Canon, CanonS_Phi0_lim;  f_equal ...
Qed.


Lemma H_Phi0_omega_closed_formula k :
  H_ (Phi0 omega) k =
  iterate (fun (f: nat -> nat) (l : nat) =>
                         iterate f (S l) l)
           k
           (fun k : nat => S (2 * k)%nat)
           k.
Proof.
  rewrite H_Phi0_omega; unfold H_succ_fun; apply iterate_ext2.
  - intro; now rewrite H_omega. 
  - intros; now apply iterate_ext.  
Qed.







Lemma H_omega_sqr_min : forall k,  0 <> k ->
                                   (exp2 (S k) <= H_ (Phi0 2) k)%nat.
Proof.
  intros k Hk; rewrite H_omega_sqr.
  generalize (exp2 (S k));  intro n;  destruct n;  abstract lia.
Qed.


Lemma H_omega_cube_min k : 0 <> k ->
                           (hyper_exp2 (1 + k) <= H_ (Phi0  3) k)%nat.
Proof.
  intros H; rewrite H_omega_cube; unfold hyper_exp2.
  transitivity (iterate exp2  (1+k) k).
  - apply iterate_mono2; [ | lia].
  intros x y H0; apply mono_weak; auto; apply exp2_mono.
  -   eapply iterate_mono_1 with 1.
   +  apply exp2_mono.
   +  apply exp2_ge_S.
   +  intros n Hn;  transitivity (exp2 (S n)).
      *  cbn ; abstract lia.
      * apply H_omega_sqr_min; abstract lia.
   +  abstract lia.
Qed.


Remark H_non_mono1 :
  ~ (forall alpha beta k, (alpha o<= beta)%e0 ->
                          (H_ alpha k <= H_ beta k)%nat).
Proof.
 intros H ;specialize (H 42 omega 3).
 assert (H0 :(42 o<= omega)%e0) by (repeat split; auto).  
 apply H in H0; rewrite H_Fin, H_omega  in H0; abstract lia.
Qed.

Section Proof_of_Abstract_Properties.
  Record P (alpha:E0) : Prop :=
    mkP {
        PA : strict_mono (H_ alpha);
        PB : alpha <> Zero -> forall n,  (n < H_ alpha n)%nat;
        PC : H_ alpha <<= H_ (Succ alpha);
        PD : dominates_from 1 (H_ (Succ alpha)) (H_ alpha);
        PE : forall beta n, Canon_plus n alpha beta -> 
                            (H_ beta n <= H_ alpha n)%nat}.

  
  Section The_induction.

    (* Base step : (sequential) proof of (P 0) *)
    
    Lemma PA_Zero : strict_mono (H_ Zero).
    Proof. 
      intros n p H; repeat rewrite H_eq1; auto with arith. 
    Qed. 
    
    Lemma PD_Zero : dominates_from 1 (H_ (Succ Zero)) (H_ Zero).
    Proof.
      red;intros; rewrite H_eq1, H_eq2, Pred_of_Succ, H_eq1. 
       - abstract lia.
       - apply Succ_succb.
    Qed.

    Local Hint Resolve PD_Zero PA_Zero : E0.

    Lemma PC_Zero :  H_ Zero <<= H_ (Succ Zero).
    Proof.
      intro n; destruct n;
        rewrite H_eq1, H_eq2;  auto with arith.
        rewrite Pred_of_Succ, H_eq1; auto with arith.
    Qed. 

    Local Hint Resolve  PC_Zero : core.

    Lemma PZero : P Zero.
    Proof. 
      split; auto with E0.
      -  now destruct 1.
      - unfold Canon_plus ; intros.
        unfold Zero in H; simpl in H.
        destruct n.
        + inversion H. 
        + destruct (const_pathS_zero  H). 
    Qed.   

    Variable alpha : E0.
    Hypothesis Halpha : forall beta, Lt beta alpha -> P beta.

    Section alpha_Succ.
      Variable beta: E0.
      Hypothesis alpha_def : alpha = Succ beta.

      Remark PA_Succ : strict_mono (H_ alpha).
      Proof.
        destruct (Halpha beta).
        - subst alpha; apply Lt_Succ.
        - red; intros; subst alpha;
            repeat rewrite H_succ_eqn; apply PA0; auto with arith.
      Qed.

      Remark RB : alpha <> Zero ->forall n, (n < H_ alpha n)%nat.
      Proof.
        intros _  n; subst  alpha; rewrite H_succ_eqn;
         destruct (E0_eq_dec beta Zero).
         - subst; rewrite H_eq1; auto with arith.
         - destruct (Halpha beta).
           + apply Lt_Succ.
           + transitivity (S n); auto with arith.
      Qed.
      
      Remark RD : dominates_from 1 (H_ (Succ alpha)) (H_ alpha).

        generalize PA_Succ; subst alpha.
        red; intros H k H0; rewrite (H_succ_eqn (Succ beta));
          apply H; auto with arith.     
      Qed.

      Remark RE : forall beta n, Canon_plus n alpha beta -> 
                                 (H_ beta n <= H_ alpha n)%nat.
      Proof.
        subst alpha; destruct n.
        -  simpl Canon_plus; tauto.
        - intro H;  destruct (Canon_plus_inv  H).
         + subst beta0;  destruct (Halpha beta).     
           * apply Lt_Succ.
           * rewrite Canon_Succ; apply PC0.
         + replace (Canon (Succ beta) (S n)) with beta in H0.
            * transitivity (H_ beta (S n)).
              -- destruct (Halpha beta).
               ++ apply Lt_Succ.
               ++ apply PE0; auto.
              -- destruct (Halpha beta).
                 ++  apply Lt_Succ.
                 ++ apply PC0.
            * now rewrite Canon_Succ.
      Qed.

      Remark RC : H_ alpha <<= H_ (Succ alpha).
      Proof.
        subst alpha; intro n; repeat rewrite H_succ_eqn.
        destruct (Halpha beta).
        -  apply Lt_Succ.
        - specialize (PA0 (S n) (S (S n))); abstract lia.
      Qed.

      Remark RP : P alpha.
        split.
        - apply PA_Succ.
        - apply RB.
        - apply RC.
        - apply RD.
        - apply RE.
      Qed.

    End alpha_Succ.


    Section alpha_limit.
      Hypothesis Hlim : Limitb alpha.

      Remark RBlim : forall n, (n < H_ alpha n)%nat.
      Proof.
        intro n;   rewrite H_eq3; auto.
        destruct (Halpha (Canon alpha (S n))).
        -  apply Canon_lt;  now apply Limit_not_Zero.
        -  eapply PB0; intro H.
        assert (H0 :cnf (Canon alpha (S n)) = cnf Zero) by (f_equal; auto).
        simpl in H0;   apply (@limitb_canonS_not_zero n (cnf alpha)); auto.
        +  apply cnf_ok.
      Qed.

      Remark RAlim : strict_mono (H_ alpha).
      Proof.
        intros m n H; rewrite (H_eq3); auto.
        -  rewrite (H_eq3 alpha); auto.
           +  destruct (Halpha (Canon alpha (S n))).
              *  apply CanonS_lt;  now  apply Limit_not_Zero.
              * apply Nat.lt_le_trans with (H_ (Canon alpha (S m)) (S m)).
                -- destruct (Halpha (Canon alpha (S m)) ).
                   ++ apply CanonS_lt;  now  apply Limit_not_Zero.
                   ++   apply PA1; abstract lia.
                -- apply Nat.le_trans with  (H_ (Canon alpha (S m)) n).
                   destruct  (Lt.le_lt_or_eq _ _ H).
                   ++ destruct (Halpha (Canon alpha (S m))).
                      apply CanonS_lt; now  apply Limit_not_Zero.
                      specialize (PA1 (S m) n H0); abstract lia.
                   ++ subst n; reflexivity.
                   ++  apply PE0;
                         specialize (KS_thm_2_4_E0 alpha Hlim  H);
                       intro H0;  destruct n.
                       inversion H.
                       apply Cor12_E0 with 0.
                       apply Canon_mono1; auto.
                       abstract lia.
                       abstract lia.
                       apply KS_thm_2_4_E0; auto.
      Qed.

      Remark RClim : H_ alpha <<= H_ (Succ alpha).
      Proof.
        intro n; rewrite H_succ_eqn; apply Nat.lt_le_incl, RAlim; abstract lia.
      Qed.

      Remark RDlim : dominates_from 1 (H_ (Succ alpha)) (H_ alpha).
      Proof.
        red;intros; rewrite H_succ_eqn; apply RAlim; abstract lia.
      Qed.

      Remark RElim : forall beta n, Canon_plus n alpha beta -> 
                                    (H_ beta n <= H_ alpha n)%nat.
      Proof.
        intros beta n H; destruct n.
        rewrite (H_eq3 alpha); auto.        
        - destruct H.
        - destruct (Canon_plus_inv H).
         + subst;  rewrite (H_eq3 alpha); auto.
          specialize (Halpha (Canon alpha (S (S n)))).
          destruct Halpha.
         *  apply Canon_lt,  Limit_not_Zero; auto.
         *  apply PE0; apply Cor12_E0 with 0.
          -- apply Canon_mono1; auto. 
          -- abstract lia.
          -- apply KS_thm_2_4_E0; auto.
        + destruct (Halpha  (Canon alpha (S n))).
          apply Canon_lt,  Limit_not_Zero; auto.
          rewrite (H_eq3 alpha); auto.
          specialize (PE0 _ _ H0);  auto.
          transitivity (H_ (Canon alpha (S n)) (S n)); auto.       
          destruct (Halpha  (Canon alpha (S (S n)))).
          * apply Canon_lt, Limit_not_Zero; auto.
          *  apply  (PE1 (Canon alpha (S n))); auto with arith.
             apply Cor12_E0 with 0; auto with arith E0.
             apply Canon_mono1; auto.
             apply KS_thm_2_4_E0; auto.
      Qed.

    End alpha_limit.

    Lemma P_alpha_0 : P alpha.
    Proof. 
      destruct (Zero_Limit_Succ_dec alpha).
      destruct s.
      - subst; apply PZero.
      - split.
        apply RAlim; auto.
        intro; apply RBlim; auto.
        apply RClim; auto.
        apply RDlim; auto.
        apply RElim; auto.
      - destruct s; split.
        eapply PA_Succ;eauto.
        eapply RB;eauto.
        eapply RC;eauto.
        eapply RD;eauto.
        eapply RE;eauto.
    Qed.

  End The_induction.


  Theorem P_alpha : forall alpha, P alpha.
  Proof.
    intro alpha; apply well_founded_induction with Lt.
    - exact E0.Lt_wf.
    - apply P_alpha_0.
  Qed.

End Proof_of_Abstract_Properties.

Section Abstract_Properties.

  Variable alpha : E0.


  Theorem H_alpha_mono : strict_mono (H_ alpha).
  Proof. now  destruct  (P_alpha alpha). Qed.

  Theorem H_alpha_gt : alpha <> Zero -> forall n, (n < H_ alpha n)%nat.
  Proof. now  destruct  (P_alpha alpha). Qed.

  Theorem H_alpha_Succ_le : H_ alpha <<= H_ (Succ alpha).
  Proof. now  destruct  (P_alpha alpha). Qed.

  Theorem H_alpha_dom : dominates_from 1 (H_ (Succ alpha)) (H_ alpha).
  Proof. now  destruct  (P_alpha alpha). Qed.

  Theorem H_alpha_beta : forall beta n, Canon_plus n alpha beta -> 
                                        (H_ beta n <= H_ alpha n)%nat.
  Proof. now  destruct  (P_alpha alpha). Qed.


  Lemma H_alpha_ge_id : id <<= H_ alpha.
  Proof.
    destruct (E0_eq_dec alpha Zero).
    - subst alpha; intro k; rewrite H_eq1; cbn;auto with arith.
    - intro k;unfold id; now apply Nat.lt_le_incl, H_alpha_gt. 
  Qed.

  Lemma H_alpha_mono_weak : forall k l, (k <= l)%nat ->
                                        (H_ alpha k <= H_ alpha l)%nat.
  Proof.
    intros.
    destruct (Lt.le_lt_or_eq k l H).
    - now apply Nat.lt_le_incl, H_alpha_mono.
    - subst; auto.
  Qed.

End Abstract_Properties.




(* To do : program tactics for a better interaction *)

Goal 
  (0 < H_ (ltac:(mko (omega * omega * omega)%t1)) 12)%nat.
  ochange {| cnf := (omega * omega * omega)%t1; cnf_ok := eq_refl |}
          (Phi0 3).
  transitivity 11.
  - abstract lia.
  - apply H_alpha_ge_id.
Qed.

