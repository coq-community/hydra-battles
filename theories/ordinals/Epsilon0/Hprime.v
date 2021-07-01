(** * A hierarchy of rapidly growing functions
    After Hardy, Wainer, Ketonen, Solovay, etc .

    Pierre Casteran, LaBRI, University of  Bordeaux *)

(** Remark

Some notations (mainly names of fast-growing functions) of our development 
 may differ slightly from the litterature. Although this fact does not affect 
our proofs, we are preparing a future version where the names
 [F_ alpha], [f_alpha], [H _alpha], etc., are fully consistent with the 
 cited articles. 
 This change will be provisionally made in a branch called [Hardy]
   (in reference to the Hardy hierarchy).

 *)


From Coq Require Import ArithRing Lia.
From hydras Require Import  E0    Canon Paths.
From hydras Require Import Exp2 Iterates Simple_LexProd.
Import RelationClasses Relations.

From Equations Require Import Equations.

 Open Scope E0_scope.

(** ** A variant of the Hardy Wainer hierarchy *)


Instance Olt : WellFounded Lt := Lt_wf.


Equations H'_ (alpha: E0) (i:nat) :  nat  by wf  alpha Lt :=
  H'_ alpha  i with E0_eq_dec alpha Zero :=
    { | left _ =>  i ;
      | right nonzero
          with Utils.dec (Limitb alpha) :=
          { | left _ =>  H'_ (Canon alpha (S i))  i ;
            | right notlimit =>  H'_ (Pred alpha) (S i)}}.

Solve All Obligations with auto with E0.


(** Paraphrases of the equations for H'_ *)

Lemma H'_eq1 : forall i, H'_ Zero i = i.
Proof.
  intro i; now rewrite H'__equation_1. 
Qed.

Lemma H'_eq2 alpha i : Succb alpha ->
                       H'_ alpha i = H'_ (Pred alpha) (S i).
Proof.
  intros;rewrite H'__equation_1.
  destruct (E0_eq_dec alpha Zero).
  - subst; discriminate.
  - cbn;  destruct (Utils.dec (Limitb alpha)) .
    destruct (Succ_not_Limitb _ H); auto.
    + now cbn.
Qed.


Lemma H'_eq3 alpha i : Limitb alpha ->
                      H'_ alpha i =  H'_ (Canon alpha (S i)) i.
Proof.
  intros;rewrite H'__equation_1.
  destruct (E0_eq_dec alpha Zero).
 - subst; discriminate.
 - cbn;  destruct (Utils.dec (Limitb alpha)) .
  + now cbn.    
  + red in H; rewrite e in H; discriminate.
Qed.

Lemma H'_succ_eqn  alpha i :  H'_ (Succ alpha) i = H'_ alpha (S i).
Proof.
  rewrite H'_eq2.
  - now rewrite Pred_of_Succ.  
  - apply Succ_Succb.
Qed.


Hint Rewrite H'_eq1  H'_succ_eqn : H'_rw.

Ltac lim_rw alpha := (assert (Limitb alpha) by auto with E0);
                     rewrite (H'_eq3 alpha); auto with E0.



(** Examples : First steps of the hierarchy *)

Lemma H'_Fin : forall i k : nat,  H'_  (Fin i) k = (i+k)%nat.
Proof with eauto with E0.
  induction i.
  - intros; simpl Fin; simpl; autorewrite with H'_rw E0_rw ... 
  - intros ;simpl; autorewrite with H'_rw E0_rw ... 
    rewrite IHi; abstract lia. 
Qed.


Lemma H'_omega : forall k, H'_ omega k = S (2 * k)%nat.
Proof with auto with E0.
  intro k; rewrite H'_eq3 ...
  - replace (Canon omega (S k)) with (Fin (S k)).
    + rewrite H'_Fin; abstract lia.
    + now autorewrite with E0_rw.
Qed.


Lemma H'_Plus_Fin alpha : forall i k : nat,
    H'_ (alpha + i)%e0 k = H'_ alpha (i + k)%nat.
Proof.
  induction i.
  - intro k; ochange (alpha +  0)%e0 alpha.
    + now simpl.
    + rewrite Plus_rw; simpl; auto with T1.
      now rewrite plus_zero_r.
  - intro k; ochange (alpha + (S i))%e0 (Succ (alpha + i))%e0.
    + rewrite H'_succ_eqn, IHi; f_equal; abstract lia.
    + repeat rewrite Plus_rw; simpl.
      destruct i; simpl.
      *  rewrite plus_zero_r;  now rewrite succ_is_plus_one.
      *   simpl; replace (FS i) with (fin (S i)).
          -- rewrite succ_of_plus_finite.
             ++ f_equal.
             ++ apply cnf_ok.
          --  reflexivity.
Qed.

Lemma H'_omega_double k : H'_ (omega * 2)%e0 k =  (4 * k + 3)%nat.
Proof.
 rewrite H'_eq3; simpl Canon.
 -   ochange  (CanonS  (omega * FinS 1)%e0 k)  (omega + (S k))%e0.
   
  + rewrite H'_Plus_Fin, H'_omega;  abstract lia.
  -  now compute.
Qed.

Lemma H'_omega_3 k : H'_ (omega * 3)%e0 k = (8 * k + 7)%nat.
Proof.
  rewrite H'_eq3 ; [| reflexivity].
  ochange (Canon  (omega * 3)%e0 (S k)) (omega * 2 + FinS k)%e0.
  rewrite FinS_eq,  H'_Plus_Fin, H'_omega_double; abstract lia.  
Qed.

Lemma H'_omega_4 k : H'_ (omega * 4)%e0 k = (16 * k + 15)%nat.
Proof.
  rewrite H'_eq3 ; [| reflexivity].
  ochange (Canon  (omega * 4)%e0 (S k)) (omega * 3 + FinS k)%e0.
  rewrite FinS_eq,  H'_Plus_Fin, H'_omega_3; abstract lia.
Qed.

Lemma H'_omega_i (i:nat)  : forall k,
    H'_ (omega * i)%e0 k = (exp2 i * k + Nat.pred (exp2 i))%nat.
Proof.
  induction i.
  - ochange (omega * 0)%e0 Zero; simpl.
    intro k; rewrite H'_eq1; abstract lia.
  - intro k; rewrite H'_eq3.
    +  ochange (Canon (omega * S i)%e0  (S k)) (omega * i + (S k))%e0.
       rewrite H'_Plus_Fin, IHi.
        simpl (exp2 (S i)); abstract lia.
        simpl Canon;  destruct i;reflexivity.
    + reflexivity.
Qed.


(** Let us note that the square of omega can be expressed through the
    Phi0 function *)


Remark Phi0_def : Phi0 2 = ltac:(mko (T1.omega * T1.omega)%t1).
Proof. apply E0_eq_intro. reflexivity. Qed.


Lemma H'_omega_sqr : forall k,
    H'_ (Phi0  2)%e0 k = (exp2 (S k ) * (S k) - 1)%nat.
Proof.
  intro k; rewrite H'_eq3; auto with E0.
  - ochange (Canon (Phi0 2) (S k)) (E0.omega * (S k))%e0.
    +  rewrite H'_omega_i; simpl (exp2 (S k)).
       *  rewrite Nat.add_pred_r.
          -- abstract lia. 
          --   generalize (exp2_not_zero k);  abstract lia.
    + cbn; f_equal; abstract lia.
Qed.

(** Composition lemma *)

Section H'_cons.
Variable alpha : E0.
Variable i : nat.
 
Lemma H'_cons : forall beta,  (beta o< Phi0 alpha)%e0 ->
                             forall k,  H'_ (Ocons alpha i beta) k=
                                        H'_ (Omega_term alpha i) (H'_ beta k).
Proof with auto with E0.
  unfold Ocons; intro beta; pattern beta; 
  apply well_founded_induction with Lt; clear beta.
  - exact E0.Lt_wf.
  -  intros beta Hbeta H;  destruct (Zero_Limit_Succ_dec beta).
     destruct s.
     + subst; intro k. autorewrite with H'_rw E0_rw using trivial. 
     + intro k;  assert (CanonS  (Omega_term alpha i + beta)%e0 k =
                          (Omega_term alpha  i + (CanonS beta k))%e0).
       {  rewrite CanonS_plus_1; auto with E0.           
          intro; subst alpha; red in H;  simpl in H;  apply LT_one in H.
          unfold Limitb in e; rewrite H in e; discriminate e.
       }
       rewrite H'_eq3, CanonS_Canon, H0.
       specialize (Hbeta (CanonS beta k)).
       assert (CanonS beta k o< beta)%e0 by auto with E0.
       assert (CanonS beta k o< Phi0 alpha)%e0 by (eapply Lt_trans; eauto).
       now rewrite (Hbeta H1 H2 k), (H'_eq3 beta).
       apply Limitb_plus; auto.
     +   intro k; destruct s as [gamma Hgamma]; subst.
         specialize (Hbeta gamma).
         assert (gamma o< Succ gamma)%e0 by (apply Lt_Succ; auto).
         assert (gamma o< Phi0 alpha)%e0 .
         { apply Lt_trans with (Succ gamma); auto. }
         rewrite (H'_succ_eqn gamma);
           replace (Omega_term alpha i + Succ gamma)%e0 with
               (Succ (Omega_term alpha i + gamma)%e0).
         rewrite H'_succ_eqn, Hbeta;  auto.
         apply E0_eq_intro; rewrite Succ_of_cons; auto.
         intro; subst; red in H; simpl in H.
         destruct H as [H [H2 H3]]; apply lt_one in H2.
         destruct (succ_not_zero _ H2).
Qed.


Lemma H'_Omega_term_1 : alpha <> Zero -> forall  k,  
    H'_ (Omega_term alpha (S i)) k =
    H'_ (Omega_term alpha i) (H'_ (Phi0 alpha) k).
Proof with auto with E0.
  intros  H k;  rewrite H'_eq3 ...
  rewrite CanonS_Canon.
  - ochange (CanonS (Omega_term alpha (S i)) k)
          (Ocons alpha i (CanonS  (Phi0 alpha) k)).
  +  rewrite H'_cons ...
     *  f_equal; rewrite (H'_eq3 (Phi0 alpha)) ...
  +  rewrite cnf_Ocons ...
           * unfold CanonS.  repeat rewrite cnf_rw.
             unfold canonS.
             rewrite cnf_Omega_term, cnf_Phi0.
             unfold Omega_term; simpl. unfold canonS.
             destruct (cnf alpha) ...
             destruct (pred (ocons t1 n t2)) ...
-   unfold canonS; apply Limitb_Omega_term ...
Qed.

End H'_cons.


Lemma H'_Omega_term_0 (alpha : E0)  :
alpha <> Zero ->  forall i k, 
  H'_ (Omega_term alpha i) k = iterate  (H'_ (Phi0 alpha)) (S i) k.
Proof.
  induction i.
  - reflexivity.                                       
  - intros; rewrite H'_Omega_term_1, IHi; trivial; now rewrite <- iterate_rw.
Qed.

Lemma H'_Fin_iterate : forall i k,
    H'_ (Fin (S i)) k = iterate (H'_ (Fin 1)) (S i) k.
Proof.
  intros; repeat rewrite H'_Fin.
  replace (iterate (H'_ 1) (S i) k) with (iterate S (S i) k).
  induction i; cbn.
  auto.
  simpl Nat.add in IHi.    rewrite IHi.
  f_equal. 
  apply iterate_ext.
  intro; rewrite H'_Fin.
  auto. 
Qed.

Lemma H'_Omega_term (alpha : E0)  :
  forall i k, 
    H'_ (Omega_term alpha i) k = iterate  (H'_ (Phi0 alpha)) (S i) k.
Proof.
  destruct (E0_eq_dec alpha Zero).
  - subst.
    intros; replace (Omega_term Zero i) with (Fin (S i)).
    replace (Phi0 Zero) with (Fin 1).
    now rewrite H'_Fin_iterate.
    compute. now apply E0_eq_intro.
    compute. now apply E0_eq_intro.
  - intros; now apply  H'_Omega_term_0.
Qed.

Definition H'_succ_fun f k := iterate f (S k) k.

Lemma H'_Phi0_succ_1 alpha  : alpha <> Zero -> forall k,
      H'_ (Phi0 (Succ alpha)) k = H'_succ_fun (H'_ (Phi0 alpha)) k. 
Proof with auto with E0.
  intros; unfold H'_succ_fun ;
    rewrite H'_eq3, CanonS_Canon, CanonS_Phi0_Succ_eqn, H'_Omega_term ...
Qed.

Lemma H'_Phi0_succ_0 : forall k,
    H'_ (Phi0 (Succ Zero)) k = H'_succ_fun (H'_ (Phi0 Zero)) k.
  Proof with auto with E0.
intros k.    
  replace (Phi0 Zero) with (Fin 1).
  replace (Phi0 (Succ Zero)) with omega.
 rewrite H'_omega.
   unfold H'_succ_fun.
   transitivity (iterate S (S k) k).
   replace (S (2 * k))%nat with (S k + k)%nat.
   generalize (S k).   
 induction n.
  now cbn.
  cbn. now rewrite  IHn.
  lia.
  apply iterate_ext.
   intro x.
    
now rewrite H'_Fin.
  apply E0_eq_intro.
  reflexivity. 
  apply E0_eq_intro.
  reflexivity. 
Qed.

  Lemma H'_Phi0_succ alpha  : forall k,
      H'_ (Phi0 (Succ alpha)) k = H'_succ_fun (H'_ (Phi0 alpha)) k. 
  destruct (E0_eq_dec alpha Zero).  
  subst.
apply H'_Phi0_succ_0.

  now apply H'_Phi0_succ_1.
  Qed.
  
  Lemma H'_Phi0_Si : forall i k,
      H'_ (Phi0 (S i)) k = iterate H'_succ_fun i (H'_ omega) k. 
Proof with auto with E0.
 induction i.
 - simpl;  replace (Phi0 (FinS 0)) with omega; auto;  orefl.   
 -  intro k;  rewrite <- FinS_eq, FinS_Succ_eq. (* lourd *)
   rewrite H'_Phi0_succ, iterate_S_eqn.
   apply iterate_ext; auto.
Qed.

Lemma H'_omega_cube : forall k,
    H'_ (Phi0 3)%e0 k = iterate (H'_ (Phi0 2))  (S k) k.
Proof.
  intro k; rewrite <-FinS_eq, -> FinS_Succ_eq, H'_Phi0_succ; auto.
Qed.

Section H'_omega_cube_3.
  
Let f k :=   (exp2 (S k ) * (S k) - 1)%nat.

Remark R0 k :  H'_ (Phi0 3)%e0 k = iterate f (S k) k.
Proof.
  ochange (Phi0 3) (Phi0 (Succ 2)); rewrite H'_Phi0_succ.
  unfold H'_succ_fun; apply iterate_ext.
  - intro x; now rewrite H'_omega_sqr.   
Qed.

Fact F0 : H'_ (Phi0 3) 3 = f (f (f (f 3))).
 rewrite R0; reflexivity. 
Qed.

Let N := (exp2 64 * 64 - 1)%nat.

(*
# (2.0 ** 64.0 *. 64.0 -. 1.0);; 
- : float = 1.1805916207174113e+21
*)

Fact F1 : H'_ (Phi0 3) 3 = f (f N).
Proof.
 rewrite F0; reflexivity. 
Qed.


Lemma F1_simpl : H'_ (Phi0 3) 3 =
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


 
End H'_omega_cube_3.


Lemma H'_Phi0_omega : forall k, H'_ (Phi0 omega) k =
                               iterate H'_succ_fun  k (H'_ omega) k.
Proof with auto with E0.
  intro k; rewrite H'_eq3,  <- H'_Phi0_Si ...
  -  rewrite CanonS_Canon, CanonS_Phi0_lim;  f_equal ...
Qed.


Lemma H'_Phi0_omega_closed_formula k :
  H'_ (Phi0 omega) k =
  iterate (fun (f: nat -> nat) (l : nat) =>
                         iterate f (S l) l)
           k
           (fun k : nat => S (2 * k)%nat)
           k.
Proof.
  rewrite H'_Phi0_omega; unfold H'_succ_fun; apply iterate_ext2.
  - intro; now rewrite H'_omega. 
  - intros; now apply iterate_ext.  
Qed.







Lemma H'_omega_sqr_min : forall k,  0 <> k ->
                                   (exp2 (S k) <= H'_ (Phi0 2) k)%nat.
Proof.
  intros k Hk; rewrite H'_omega_sqr.
  generalize (exp2 (S k));  intro n;  destruct n;  abstract lia.
Qed.


Lemma H'_omega_cube_min k : 0 <> k ->
                           (hyper_exp2 (1 + k) <= H'_ (Phi0  3) k)%nat.
Proof.
  intros H; rewrite H'_omega_cube; unfold hyper_exp2.
  transitivity (iterate exp2  (1+k) k).
  - apply iterate_mono2; [ | lia].
  intros x y H0; apply mono_weak; auto; apply exp2_mono.
  -   eapply iterate_mono_1 with 1.
   +  apply exp2_mono.
   +  apply exp2_ge_S.
   +  intros n Hn;  transitivity (exp2 (S n)).
      *  cbn ; abstract lia.
      * apply H'_omega_sqr_min; abstract lia.
   +  abstract lia.
Qed.


Remark H'_non_mono1 :
  ~ (forall alpha beta k, (alpha o<= beta)%e0 ->
                          (H'_ alpha k <= H'_ beta k)%nat).
Proof.
 intros H ;specialize (H 42 omega 3).
 assert (H0 :(42 o<= omega)%e0). { repeat split; auto.  
 compute. now left. }
 apply H in H0; rewrite H'_Fin, H'_omega  in H0; abstract lia.
Qed.

Section Proof_of_Abstract_Properties.
  Record P (alpha:E0) : Prop :=
    mkP {
        PA : strict_mono (H'_ alpha);
        PB : alpha <> Zero -> forall n,  (n < H'_ alpha n)%nat;
        PC : H'_ alpha <<= H'_ (Succ alpha);
        PD : dominates_from 1 (H'_ (Succ alpha)) (H'_ alpha);
        PE : forall beta n, Canon_plus n alpha beta -> 
                            (H'_ beta n <= H'_ alpha n)%nat}.

  
  Section The_induction.

    (* Base step : (sequential) proof of (P 0) *)
    
    Lemma PA_Zero : strict_mono (H'_ Zero).
    Proof. 
      intros n p H; repeat rewrite H'_eq1; auto with arith. 
    Qed. 
    
    Lemma PD_Zero : dominates_from 1 (H'_ (Succ Zero)) (H'_ Zero).
    Proof.
      red;intros; rewrite H'_eq1, H'_eq2, Pred_of_Succ, H'_eq1. 
       - abstract lia.
       - apply Succ_Succb.
    Qed.

    Local Hint Resolve PD_Zero PA_Zero : E0.

    Lemma PC_Zero :  H'_ Zero <<= H'_ (Succ Zero).
    Proof.
      intro n; destruct n;
        rewrite H'_eq1, H'_eq2;  auto with arith.
        rewrite Pred_of_Succ, H'_eq1; auto with arith.
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

      Remark PA_Succ : strict_mono (H'_ alpha).
      Proof.
        destruct (Halpha beta).
        - subst alpha; apply Lt_Succ.
        - red; intros; subst alpha;
            repeat rewrite H'_succ_eqn; apply PA0; auto with arith.
      Qed.

      Remark RB : alpha <> Zero ->forall n, (n < H'_ alpha n)%nat.
      Proof.
        intros _  n; subst  alpha; rewrite H'_succ_eqn;
         destruct (E0_eq_dec beta Zero).
         - subst; rewrite H'_eq1; auto with arith.
         - destruct (Halpha beta).
           + apply Lt_Succ.
           + transitivity (S n); auto with arith.
      Qed.
      
      Remark RD : dominates_from 1 (H'_ (Succ alpha)) (H'_ alpha).

        generalize PA_Succ; subst alpha.
        red; intros H k H0; rewrite (H'_succ_eqn (Succ beta));
          apply H; auto with arith.     
      Qed.

      Remark RE : forall beta n, Canon_plus n alpha beta -> 
                                 (H'_ beta n <= H'_ alpha n)%nat.
      Proof.
        subst alpha; destruct n.
        -  simpl Canon_plus; tauto.
        - intro H;  destruct (Canon_plus_inv  H).
         + subst beta0;  destruct (Halpha beta).     
           * apply Lt_Succ.
           * rewrite Canon_Succ; apply PC0.
         + replace (Canon (Succ beta) (S n)) with beta in H0.
            * transitivity (H'_ beta (S n)).
              -- destruct (Halpha beta).
               ++ apply Lt_Succ.
               ++ apply PE0; auto.
              -- destruct (Halpha beta).
                 ++  apply Lt_Succ.
                 ++ apply PC0.
            * now rewrite Canon_Succ.
      Qed.

      Remark RC : H'_ alpha <<= H'_ (Succ alpha).
      Proof.
        subst alpha; intro n; repeat rewrite H'_succ_eqn.
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

      Remark RBlim : forall n, (n < H'_ alpha n)%nat.
      Proof.
        intro n;   rewrite H'_eq3; auto.
        destruct (Halpha (Canon alpha (S n))).
        -  apply Canon_lt;  now apply Limit_not_Zero.
        -  eapply PB0; intro H.
        assert (H0 :cnf (Canon alpha (S n)) = cnf Zero) by (f_equal; auto).
        simpl in H0;   apply (@limitb_canonS_not_zero n (cnf alpha)); auto.
        +  apply cnf_ok.
      Qed.

      Remark RAlim : strict_mono (H'_ alpha).
      Proof.
        intros m n H; rewrite (H'_eq3); auto.
        -  rewrite (H'_eq3 alpha); auto.
           +  destruct (Halpha (Canon alpha (S n))).
              *  apply CanonS_lt;  now  apply Limit_not_Zero.
              * apply Nat.lt_le_trans with (H'_ (Canon alpha (S m)) (S m)).
                -- destruct (Halpha (Canon alpha (S m)) ).
                   ++ apply CanonS_lt;  now  apply Limit_not_Zero.
                   ++   apply PA1; abstract lia.
                -- apply Nat.le_trans with  (H'_ (Canon alpha (S m)) n).
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

      Remark RClim : H'_ alpha <<= H'_ (Succ alpha).
      Proof.
        intro n; rewrite H'_succ_eqn; apply Nat.lt_le_incl, RAlim; abstract lia.
      Qed.

      Remark RDlim : dominates_from 1 (H'_ (Succ alpha)) (H'_ alpha).
      Proof.
        red;intros; rewrite H'_succ_eqn; apply RAlim; abstract lia.
      Qed.

      Remark RElim : forall beta n, Canon_plus n alpha beta -> 
                                    (H'_ beta n <= H'_ alpha n)%nat.
      Proof.
        intros beta n H; destruct n.
        rewrite (H'_eq3 alpha); auto.        
        - destruct H.
        - destruct (Canon_plus_inv H).
         + subst;  rewrite (H'_eq3 alpha); auto.
          specialize (Halpha (Canon alpha (S (S n)))).
          destruct Halpha.
         *  apply Canon_lt,  Limit_not_Zero; auto.
         *  apply PE0; apply Cor12_E0 with 0.
          -- apply Canon_mono1; auto. 
          -- abstract lia.
          -- apply KS_thm_2_4_E0; auto.
        + destruct (Halpha  (Canon alpha (S n))).
          apply Canon_lt,  Limit_not_Zero; auto.
          rewrite (H'_eq3 alpha); auto.
          specialize (PE0 _ _ H0);  auto.
          transitivity (H'_ (Canon alpha (S n)) (S n)); auto.       
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

  Theorem H'_alpha_mono : strict_mono (H'_ alpha).
  Proof. now  destruct  (P_alpha alpha). Qed.

  Theorem H'_alpha_gt : alpha <> Zero -> forall n, (n < H'_ alpha n)%nat.
  Proof. now  destruct  (P_alpha alpha). Qed.

  Theorem H'_alpha_Succ_le : H'_ alpha <<= H'_ (Succ alpha).
  Proof. now  destruct  (P_alpha alpha). Qed.

  Theorem H'_alpha_dom : dominates_from 1 (H'_ (Succ alpha)) (H'_ alpha).
  Proof. now  destruct  (P_alpha alpha). Qed.

  (** [H'_] is not mononotonous in [alpha] in general. 
      Nevertheless, this lemma may help (from [KS]) *)
     

  Theorem H'_restricted_mono_l : forall beta n, Canon_plus n alpha beta -> 
                                        H'_ beta n <= H'_ alpha n.
  Proof. now  destruct  (P_alpha alpha). Qed.


  Lemma H'_alpha_ge_id : id <<= H'_ alpha.
  Proof.
    destruct (E0_eq_dec alpha Zero).
    - subst alpha; intro k; rewrite H'_eq1; cbn;auto with arith.
    - intro k;unfold id; now apply Nat.lt_le_incl, H'_alpha_gt. 
  Qed.

  Lemma H'_alpha_mono_weak : forall k l, k <= l ->
                                         H'_ alpha k <= H'_ alpha l.
  Proof.
    intros.
    destruct (Lt.le_lt_or_eq k l H).
    - now apply Nat.lt_le_incl, H'_alpha_mono.
    - subst; auto.
  Qed.

End Abstract_Properties.

(** ** Monotony of [H'] w.r.t. its first argument 

   Although Lemma [H'_non_mono1] tells us that [H'] is not monotonous
   with respect to its argument [alpha], we prove that, if [alpha<beta], then
   [H'_ alpha k < H'_ beta k] for large enough [k].
  For that purpose, we apply a few lemmas from the Ketonen-Solovay article.

*)


Lemma H'_mono_l_0 alpha beta :
  alpha o< beta ->
  {n : nat | forall p, n <= p -> H'_ alpha (S p) <= H'_ beta (S p)}.
Proof.
  intro H; destruct (Lemma2_6_1_E0 H) as [n Hn].
  exists (S n).
  intros; apply H'_restricted_mono_l.
  eapply Cor12_E0 with n; eauto.
  lia.
Qed.

Lemma H'_mono_l_1 alpha beta :
  alpha o<= beta ->
  {n : nat | forall p, n <= p -> H'_ alpha (S p) <= H'_ beta (S p)}.
Proof.
  intro H; destruct (le_lt_eq_dec H).
  - now apply H'_mono_l_0.
  -subst; exists 0; auto with arith.
Qed.

Section Proof_of_H'_mono_l.
  
  Variables alpha beta: E0.
  Hypothesis H_alpha_beta: alpha o< beta.

  Section Succ_case.
    Variable gamma: E0.  
    Hypothesis Hgamma : beta = Succ gamma.

    Remark R1 : alpha o<= gamma.
    Proof. subst; now apply lt_Succ_le_2.  Qed.

    Remark R2 : {n : nat | forall p, n <= p -> H'_ alpha (S p) <= H'_ gamma (S p)}.
    Proof.  apply  H'_mono_l_1, R1.  Qed.

    Remark R3 : {n: nat | forall p, n <= p ->
                                    H'_ alpha (S p) < H'_ beta (S p)}.
    Proof.
      destruct R2 as [n Hn]; exists (Max.max n 1).
      intros p H;  apply Lt.le_lt_trans with (H'_ gamma (S p)).
      - apply Hn; lia.
      - subst beta; apply (H'_alpha_dom gamma (S p)); auto with arith.
    Qed.

  End Succ_case.

  Section Limit_case.
    Hypothesis Hbeta: Limitb beta.

    Remark R4 : Succ alpha o< beta.
    Proof. now apply Succ_lt_Limitb. Qed.

    Remark R5 :  {n: nat | forall p, n <= p ->
                                     H'_ alpha (S p) < H'_ beta (S p)}.
    Proof.
      assert (Succ alpha o<= beta) by (apply Lt_Le_incl; apply R4).
      destruct   (H'_mono_l_1 _ _ H) as [x Hx].
      exists x; intros.
      apply Lt.lt_le_trans with (H'_ (Succ alpha) (S p)).
      -  apply (H'_alpha_dom alpha (S p)); auto with arith.
      - auto.
    Qed.

  End Limit_case.

  Lemma H'_mono_l : {n: nat | forall p, n <= p ->
                                        H'_ alpha (S p) < H'_ beta (S p)}.
  Proof.
    destruct (Zero_Limit_Succ_dec beta) as [[H0 | Hl] | [gamma Hgamma]].
    - subst; destruct (E0_not_Lt_zero H_alpha_beta).
    - now apply R5.
    -  eapply  R3; eauto.
  Qed.

  Theorem H'_dom : dominates_strong (H'_ beta) (H'_ alpha).
  Proof.
    destruct H'_mono_l as [x Hx]; exists (S x); red.
    intros p H; inversion_clear H; apply Hx; auto with arith.
  Qed.

End Proof_of_H'_mono_l.


(* To do : program tactics for a better interaction *)

Goal 
  (0 < H'_ (ltac:(mko (T1.omega * T1.omega * T1.omega)%t1)) 12)%nat.
  ochange {| cnf := (T1.omega * T1.omega * T1.omega)%t1; cnf_ok := eq_refl |}
          (Phi0 3).
  transitivity 11.
  - abstract lia.
  - apply H'_alpha_ge_id.
Qed.
