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
From hydras Require Import Compat815. 
From Equations Require Import Equations.

 Open Scope E0_scope.

(** ** A variant of the Hardy Wainer hierarchy *)


#[ global ] Instance Olt : WellFounded E0lt := E0lt_wf.

(* begin snippet HprimeDef *)

Equations H'_ (alpha: E0) (i:nat) :  nat  by wf  alpha E0lt :=
  H'_ alpha  i with E0_eq_dec alpha E0zero :=
    { | left _zero =>  i ;
      | right _nonzero
          with Utils.dec (E0limit alpha) :=
          { | left _limit =>  H'_ (Canon alpha (S i))  i ;
            | right _successor =>  H'_ (E0_pred alpha) (S i)}}.
(* end snippet HprimeDef *)

(* begin snippet HprimeDefb *)
Solve All Obligations with auto with E0.
(* end snippet HprimeDefb *)

(** Paraphrases of the equations for H'_ *)

(* begin snippet paraphrasesa:: no-out  *)
Lemma H'_eq1 : forall i, H'_ E0zero i = i.
Proof.
  intro i; now rewrite H'__equation_1. 
Qed.

(* end snippet paraphrasesa *)

(* begin snippet paraphrasesb:: no-out  *)
Lemma H'_eq2_0 alpha i :
  E0is_succ alpha ->
  H'_ alpha i = H'_ (E0_pred alpha) (S i).
(* end snippet paraphrasesb *)

Proof.
  intros;rewrite H'__equation_1.
  destruct (E0_eq_dec alpha E0zero).
  - subst; discriminate.
  - cbn;  destruct (Utils.dec (E0limit alpha)) .
    destruct (Succ_not_T1limit _ H); auto.
    + now cbn.
Qed.

(* begin snippet paraphrasesc:: no-out  *)
Lemma H'_eq3 alpha i :
  E0limit alpha ->  H'_ alpha i =  H'_ (Canon alpha (S i)) i.
(* end snippet paraphrasesc *)

Proof.
  intros;rewrite H'__equation_1.
  destruct (E0_eq_dec alpha E0zero).
 - subst; discriminate.
 - cbn;  destruct (Utils.dec (E0limit alpha)) .
  + now cbn.    
  + red in H; rewrite e in H; discriminate.
Qed.

(* begin snippet paraphrasesd:: no-out  *)
Lemma H'_eq2  alpha i :
  H'_ (E0_succ alpha) i = H'_ alpha (S i).
(* end snippet paraphrasesd  *)
Proof.
  rewrite H'_eq2_0.
  - now rewrite E0_pred_of_Succ.  
  - apply Succ_Succb.
Qed.

#[local] Hint Rewrite H'_eq1  H'_eq2 : H'_rw.

Ltac lim_rw alpha := (assert (E0limit  alpha) by auto with E0);
                     rewrite (H'_eq3 alpha); auto with E0.



(** Examples : First steps of the hierarchy *)

(* begin snippet HprimeFin *)

(*| .. coq:: no-out |*)
Lemma H'_Fin : forall i k : nat,  H'_  (E0fin i) k = (i+k)%nat.
Proof with eauto with E0.
  induction i.
  - intros; simpl E0fin; simpl; autorewrite with H'_rw E0_rw ... 
  - intros ;simpl; autorewrite with H'_rw E0_rw ... 
    rewrite IHi; abstract lia. 
Qed.
(*||*)
(* end snippet HprimeFin *)

(* begin snippet HprimeOmega *)

(*| .. coq:: no-out |*)
Lemma H'_omega : forall k, H'_ E0_omega k = S (2 * k)%nat.
Proof with auto with E0.
  intro k; rewrite H'_eq3 ...
  - replace (Canon E0_omega (S k)) with (E0fin (S k)).
    + rewrite H'_Fin; abstract lia.
    + now autorewrite with E0_rw.
Qed.
(*||*)
(* end snippet HprimeOmega *)

(* begin snippet HprimePlusFin:: no-out *)

Lemma H'_Plus_Fin alpha : forall i k : nat,
    H'_ (alpha + i)%e0 k = H'_ alpha (i + k)%nat. 
Proof. 
  induction i. 
  (* ... *)
  (* end snippet HprimePlusFin *)
  
  - intro k; ochange (alpha +  0)%e0 alpha.
    + now simpl.
    + rewrite Plus_rw; simpl; auto with T1.
      now rewrite plus_zero_r.
  - intro k; ochange (alpha + (S i))%e0 (E0_succ (alpha + i))%e0.
    + rewrite H'_eq2, IHi; f_equal; abstract lia.
    + repeat rewrite Plus_rw; simpl.
      destruct i; simpl.
      *  rewrite plus_zero_r;  now rewrite succ_is_plus_one.
      *   simpl; replace (FS i) with (\F (S i)).
          -- rewrite succ_of_plus_finite.
             ++ f_equal.
             ++ apply cnf_ok.
          --  reflexivity.
Qed.


(* begin snippet HprimeExamplesa:: no-out  *)
Lemma H'_omega_double k :
  H'_ (E0_omega * 2)%e0 k =  (4 * k + 3)%nat.
Proof.
  rewrite H'_eq3; simpl Canon; [ | now compute]. 
  ochange  (CanonS  (E0_omega * E0finS 1)%e0 k)  (E0_omega + (S k))%e0;
      rewrite H'_Plus_Fin, H'_omega;  abstract lia.
Qed.
(* end snippet HprimeExamplesa:: no-out  *)

(* begin snippet HprimeExamplesb:: no-out  *)
Lemma H'_omega_3 k : H'_ (E0_omega * 3)%e0 k = (8 * k + 7)%nat.
(* end snippet HprimeExamplesb *)
Proof.
  rewrite H'_eq3 ; [| reflexivity].
  ochange (Canon (E0_omega * 3)%e0 (S k)) (E0_omega * 2 + E0finS k)%e0.
  rewrite FinS_eq,  H'_Plus_Fin, H'_omega_double; abstract lia.  
Qed.

(* begin snippet HprimeExamplesc:: no-out  *)
Lemma H'_omega_4 k : H'_ (E0_omega * 4)%e0 k = (16 * k + 15)%nat.
(* end snippet HprimeExamplesc *)

Proof.
  rewrite H'_eq3 ; [| reflexivity].
  ochange (Canon  (E0_omega * 4)%e0 (S k)) (E0_omega * 3 + E0finS k)%e0.
  rewrite FinS_eq,  H'_Plus_Fin, H'_omega_3; abstract lia.
Qed.

(* begin snippet HprimeExamplesd:: no-out  *)
Lemma H'_omega_i (i:nat)  : forall k,
    H'_ (E0_omega * i)%e0 k =  (exp2 i * k + Nat.pred (exp2 i))%nat. 
Proof.
  induction i.
  (* ... *)
  (* end snippet HprimeExamplesd  *)
  
  - ochange (E0_omega * 0)%e0 E0zero; simpl.
    intro k; rewrite H'_eq1; abstract lia.
  - intro k; rewrite H'_eq3.
    +  ochange (Canon (E0_omega * S i)%e0  (S k)) (E0_omega * i + (S k))%e0.
       rewrite H'_Plus_Fin, IHi.
        simpl (exp2 (S i)); abstract lia.
        simpl Canon;  destruct i;reflexivity.
    + reflexivity.
Qed.


(** Let us note that the square of omega can be expressed through the
    Phi0 function *)


Remark Phi0_def : E0_phi0 2 = ltac:(mko (T1omega * T1omega)%t1).
Proof. apply E0_eq_intro. reflexivity. Qed.

(* begin snippet HprimeOmegaSqr *)

Lemma H'_omega_sqr : forall k,
    H'_ (E0_phi0  2)%e0 k = (exp2 (S k ) * (S k) - 1)%nat. (* .no-out *)
(*| .. coq:: none |*)
Proof.
  intro k; rewrite H'_eq3; auto with E0.
  - ochange (Canon (E0_phi0 2) (S k)) (E0_omega * (S k))%e0.
    +  rewrite H'_omega_i; simpl (exp2 (S k)).
       *  rewrite Nat.add_pred_r.
          -- abstract lia. 
          --   generalize (exp2_not_zero k);  abstract lia.
    + cbn; f_equal; abstract lia.
Qed.
(*||*)
(* end snippet HprimeOmegaSqr *)

(** Composition lemma *)

Section H'_cons.
Variable alpha : E0.
Variable i : nat.
 
Lemma H'_cons : forall beta,  (beta o< E0_phi0 alpha)%e0 ->
                             forall k,  H'_ (Cons alpha i beta) k=
                                        H'_ (Omega_term alpha i) (H'_ beta k).
Proof with auto with E0.
  unfold Cons; intro beta; pattern beta; 
  apply well_founded_induction with E0lt; clear beta.
  - exact E0lt_wf.
  -  intros beta Hbeta H;  destruct (Zero_Limit_Succ_dec beta).
     destruct s.
     + subst; intro k. autorewrite with H'_rw E0_rw using trivial. 
     + intro k;  assert (CanonS  (Omega_term alpha i + beta)%e0 k =
                          (Omega_term alpha  i + (CanonS beta k))%e0).
       {  rewrite CanonS_plus_1; auto with E0.           
          intro; subst alpha; red in H;  simpl in H;  apply LT_one in H.
          unfold E0limit in e; rewrite H in e; discriminate e.
       }
       rewrite H'_eq3, H0.
       specialize (Hbeta (CanonS beta k)).
       assert (CanonS beta k o< beta)%e0 by auto with E0.
       assert (CanonS beta k o< E0_phi0 alpha)%e0 by (eapply Lt_trans; eauto).
       now rewrite (Hbeta H1 H2 k), (H'_eq3 beta).
       apply T1limit_plus; auto.
     +   intro k; destruct s as [gamma Hgamma]; subst.
         specialize (Hbeta gamma).
         assert (gamma o< E0_succ gamma)%e0 by (apply Lt_Succ; auto).
         assert (gamma o< E0_phi0 alpha)%e0 .
         { apply Lt_trans with (E0_succ gamma); auto. }
         rewrite (H'_eq2 gamma);
           replace (Omega_term alpha i + E0_succ gamma)%e0 with
               (E0_succ (Omega_term alpha i + gamma)%e0).
         rewrite H'_eq2, Hbeta;  auto.
         apply E0_eq_intro; rewrite Succ_of_cons; auto.
         intro; subst; red in H; simpl in H.
         destruct H as [H [H2 H3]]; apply lt_one in H2.
         destruct (succ_not_zero _ H2).
Qed.

(* begin snippet HprimeOmegaTerm1 *)

Lemma H'_Omega_term_1 : alpha <> E0zero -> forall  k,  
    H'_ (Omega_term alpha (S i)) k =
    H'_ (Omega_term alpha i) (H'_ (E0_phi0 alpha) k). (* .no-out *)
(* end snippet HprimeOmegaTerm1 *)

Proof with auto with E0.
  intros  H k;  rewrite H'_eq3 ...
  - ochange (CanonS (Omega_term alpha (S i)) k)
          (Cons alpha i (CanonS  (E0_phi0 alpha) k)).
  +  rewrite H'_cons ...
     *  f_equal; rewrite (H'_eq3 (E0_phi0 alpha)) ...
  +  rewrite cnf_Cons ...
           * unfold CanonS.  repeat rewrite cnf_rw.
             rewrite cnf_Omega_term, cnf_phi0.
             unfold Omega_term; simpl. 
             destruct (cnf alpha) ...
             destruct (pred (cons t1 n t2)) ...
-  apply T1limit_Omega_term ...
Qed.

End H'_cons.


Lemma H'_Omega_term_0 (alpha : E0)  :
alpha <> E0zero ->  forall i k, 
  H'_ (Omega_term alpha i) k = iterate  (H'_ (E0_phi0 alpha)) (S i) k.
Proof.
  induction i.
  - reflexivity.                                       
  - intros; rewrite H'_Omega_term_1, IHi; trivial; now rewrite <- iterate_rw.
Qed.

Lemma H'_Fin_iterate : forall i k,
    H'_ (E0fin (S i)) k = iterate (H'_ (E0fin 1)) (S i) k.
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

(* begin snippet HprimeOmegaTerm:: no-out *)

Lemma H'_Omega_term (alpha : E0)  :
  forall i k, 
    H'_ (Omega_term alpha i) k =
    iterate  (H'_ (E0_phi0 alpha)) (S i) k. 
(* end snippet HprimeOmegaTerm *)

Proof.
  destruct (E0_eq_dec alpha E0zero).
  - subst.
    intros; replace (Omega_term E0zero i) with (E0fin (S i)).
    replace (E0_phi0 E0zero) with (E0fin 1).
    now rewrite H'_Fin_iterate.
    compute. now apply E0_eq_intro.
    compute. now apply E0_eq_intro.
  - intros; now apply  H'_Omega_term_0.
Qed.

(* begin snippet HprimeSuccFun *)

Definition H'_succ_fun f k := iterate f (S k) k.
(* end snippet HprimeSuccFun *)

Lemma H'_Phi0_succ_1 alpha  : alpha <> E0zero -> forall k,
      H'_ (E0_phi0 (E0_succ alpha)) k = H'_succ_fun (H'_ (E0_phi0 alpha)) k. 
Proof with auto with E0.
  intros; unfold H'_succ_fun ;
    rewrite H'_eq3, CanonS_Phi0_Succ_eqn, H'_Omega_term ...
Qed.

Lemma H'_Phi0_succ_0 : forall k,
    H'_ (E0_phi0 (E0_succ E0zero)) k = H'_succ_fun (H'_ (E0_phi0 E0zero)) k.
Proof with auto with E0.
  intros k.    
  replace (E0_phi0 E0zero) with (E0fin 1).
  replace (E0_phi0 (E0_succ E0zero)) with E0_omega.
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
    H'_ (E0_phi0 (E0_succ alpha)) k = H'_succ_fun (H'_ (E0_phi0 alpha)) k.
Proof.
  destruct (E0_eq_dec alpha E0zero).  
  - subst; apply H'_Phi0_succ_0.
  - now apply H'_Phi0_succ_1.
Qed.

(* begin snippet HprimePhi0SI:: no-out *)

Lemma H'_Phi0_Si : forall i k,
    H'_ (E0_phi0 (S i)) k = iterate H'_succ_fun i (H'_ E0_omega) k. 
(* end snippet HprimePhi0SI *)
Proof with auto with E0.
  induction i.
  - simpl;  replace (E0_phi0 (E0finS 0)) with E0_omega; auto;  orefl.   
  -  intro k;  rewrite <- FinS_eq, FinS_Succ_eq. (* lourd *)
     rewrite H'_Phi0_succ, iterate_S_eqn.
     apply iterate_ext; auto.
Qed.

(* begin snippet HprimeOmegaCube:: no-out *)
Lemma H'_omega_cube : forall k,
    H'_ (E0_phi0 3)%e0 k = iterate (H'_ (E0_phi0 2)) (S k) k. 
(* end snippet HprimeOmegaCube *)
Proof.
  intro k; rewrite <- FinS_eq, -> FinS_Succ_eq, H'_Phi0_succ; auto.
Qed.

Section H'_omega_cube_3.
  
(* begin snippet HprimeOmegaCube3a:: no-out *)

  Let f k :=   (exp2 (S k) * (S k) - 1)%nat.

  Remark R0 k :  H'_ (E0_phi0 3)%e0 k = iterate f (S k) k. 
   Proof.
    ochange (E0_phi0 3) (E0_phi0 (E0_succ 2)); rewrite H'_Phi0_succ.
    unfold H'_succ_fun; apply iterate_ext.
    - intro x; now rewrite H'_omega_sqr.   
   Qed.

  (* end snippet HprimeOmegaCube3a *)

  (* begin snippet HprimeOmegaCube3b:: no-out *)
   Fact F0 : H'_ (E0_phi0 3) 3 = f (f (f (f 3))). 
   Proof.  rewrite R0; reflexivity.   Qed.
     
   (* end snippet HprimeOmegaCube3b *)

   (** f (f 3)) *)
   (* begin snippet HprimeOmegaCube3c:: no-out *)
  
  Let N := (exp2 64 * 64 - 1)%nat. 

  (* end snippet HprimeOmegaCube3c *)

  Remark N_simpl: N = exp2 70 - 1.
  Proof. 
   change 70 with (64 + 6)%nat.
    assert (forall n p,  (exp2 (n + p) = exp2 n * exp2 p)%nat).
   { induction n; cbn.
     intro p; now rewrite Nat.add_0_r.
    intros p; rewrite !Nat.add_0_r.
     repeat rewrite IHn; ring.
   }
  rewrite H; unfold N; reflexivity. 
  Qed.
  
  (* begin snippet  HprimeOmegaCube3d:: no-out *)
  
  Fact F1 : H'_ (E0_phi0 3) 3 = f (f N).
  Proof.
    rewrite F0; reflexivity. 
  Qed.

  Fact  F1_simpl :
    H'_ (E0_phi0 3) 3 =
    (exp2 (exp2 (S N) * S N) * (exp2 (S N) * S N) - 1)%nat.
  
 (* end snippet HprimeOmegaCube3d *)
  
  Proof.
    rewrite F1; unfold f.
    assert (forall k,  k <> 0 -> (S  (k -1) = k)%nat) by lia.
    rewrite (H (exp2 (S N) * S N)%nat).
    - reflexivity. 
    - apply Nat.neq_mul_0; split.
      + apply  exp2_not_zero.
      + discriminate.
  Qed.
  (* begin snippet  HprimeOmegaCube3de:: no-out *)
  Fact F2 : H'_ (E0_phi0 3 + 3) 0 = f (f N).
  (* end snippet  HprimeOmegaCube3de *)
  rewrite H'_Plus_Fin, Nat.add_0_r, F1; reflexivity. 
  Qed. 

  Remark f_minoration n p : 0 < n -> n <= p -> exp2 n <= f p.
  Proof.
    intros ? ? ; unfold f; rewrite exp2S.
    pose (x := exp2 n); pose(y := exp2 p); fold x; fold y.
    assert (x <= y) by (now apply exp2_mono_weak).
    assert (2 <= S p) by lia.
    transitivity (2 * x * 2 - 1).
    -  lia.
    - apply Nat.sub_le_mono_r.
      transitivity (2 * y * 2)%nat.
      + lia.
      + now apply Nat.mul_le_mono_l. 
  Qed.

  (* begin snippet HprimeOmegaCube3e:: no-out *)
  Fact F3 : (exp2 (exp2 N) <= H'_ (E0_phi0 3 + 3) 0).
  (* end snippet HprimeOmegaCube3e *)
  Proof. 
    rewrite F2; apply f_minoration. 
    - apply exp2_positive. 
    - apply f_minoration; unfold N.
      assert (H0 := exp2_gt_id 64).
      + pose (x:= exp2 64); fold x in H0; fold x; lia.
      + left. 
  Qed. 

End H'_omega_cube_3.



(* begin snippet HprimePhi0Omega *)

Lemma H'_Phi0_omega :
  forall k, H'_ (E0_phi0 E0_omega) k =
            iterate H'_succ_fun  k (H'_ E0_omega) k. (* .no-out *)
(*| .. coq:: none |*)
Proof with auto with E0.
  intro k; rewrite H'_eq3, <- H'_Phi0_Si ...
  -  rewrite CanonS_phi0_lim;  f_equal ...
Qed.
(*||*)
(* end snippet HprimePhi0Omega *)

(* begin snippet HprimePhi0OmegaClosed:: no-out *)

Lemma H'_Phi0_omega_exact_formula k :
  H'_ (E0_phi0 E0_omega) k =
    let F f i := iterate f (S i) i
    in let g k := S (2 * k)%nat
       in iterate F k g k. 
(* end snippet HprimePhi0OmegaClosed *)
Proof. 
  rewrite H'_Phi0_omega; unfold H'_succ_fun; apply iterate_ext2.
  - intro; now rewrite H'_omega. 
  - intros; now apply iterate_ext.  
Qed.

Lemma H'_omega_sqr_min : forall k,  0 <> k ->
                                    (exp2 (S k) <= H'_ (E0_phi0 2) k)%nat.
Proof.
  intros k Hk; rewrite H'_omega_sqr.
  generalize (exp2 (S k));  intro n;  destruct n;  abstract lia.
Qed.

(* begin snippet HprimeHexp2:: no-out *)
Lemma H'_omega_cube_min k :
  0 <> k -> (hyper_exp2 (1 + k) <= H'_ (E0_phi0 3) k)%nat.
(* end snippet HprimeHexp2 *)
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

(* begin snippet HprimeNonMono1:: no-out *)
Remark H'_non_mono1 :
  ~ (forall alpha beta k,
        (alpha o<= beta)%e0 ->
        (H'_ alpha k <= H'_ beta k)%nat). 
Proof. 
  intros H ;specialize (H 42 E0_omega 3). 
  (* ... *)
(* end snippet HprimeNonMono1 *)
  assert (H0 :(42 o<= E0_omega)%e0).
  { repeat split; auto.  
    compute. now left. }
  apply H in H0; rewrite H'_Fin, H'_omega  in H0; abstract lia.
Qed.


(* begin snippet PAP *)

Section Proof_of_Abstract_Properties.
  
  Record P (alpha:E0) : Prop :=
    mkP {
        PA : strict_mono (H'_ alpha);
        PB : alpha <> E0zero -> forall n,  (n < H'_ alpha n)%nat;
        PC : H'_ alpha <<= H'_ (E0_succ alpha);
        PD : dominates_from 1 (H'_ (E0_succ alpha)) (H'_ alpha);
        PE : forall beta n, Canon_plus n alpha beta -> 
                            (H'_ beta n <= H'_ alpha n)%nat}.

  (*| .. coq:: none |*)
  Section The_induction.

    (* Base step : (sequential) proof of (P 0) *)
    
    Lemma PA_Zero : strict_mono (H'_ E0zero).
    Proof. 
      intros n p H; repeat rewrite H'_eq1; auto with arith. 
    Qed. 
    
    Lemma PD_Zero : dominates_from 1 (H'_ (E0_succ E0zero)) (H'_ E0zero).
    Proof.
      red;intros; rewrite H'_eq1, H'_eq2_0, E0_pred_of_Succ, H'_eq1. 
      - abstract lia.
      - apply Succ_Succb.
    Qed.

    #[local] Hint Resolve PD_Zero PA_Zero : E0.

    Lemma PC_Zero :  H'_ E0zero <<= H'_ (E0_succ E0zero).
    Proof.
      intro n; destruct n;
        rewrite H'_eq1, H'_eq2_0;  auto with arith.
      rewrite E0_pred_of_Succ, H'_eq1; auto with arith.
    Qed. 

    #[local] Hint Resolve  PC_Zero : core.

    Lemma PZero : P E0zero.
    Proof. 
      split; auto with E0.
      -  now destruct 1.
      - unfold Canon_plus ; intros.
        unfold E0zero in H; simpl in H.
        destruct n.
        + inversion H. 
        + destruct (const_pathS_zero  H). 
    Qed.   

    Variable alpha : E0.
    Hypothesis Halpha : forall beta, E0lt beta alpha -> P beta.

    Section alpha_Succ.
      Variable beta: E0.
      Hypothesis alpha_def : alpha = E0_succ beta.

      Remark PA_Succ : strict_mono (H'_ alpha).
      Proof.
        destruct (Halpha beta).
        - subst alpha; apply Lt_Succ.
        - red; intros; subst alpha;
            repeat rewrite H'_eq2; apply PA0; auto with arith.
      Qed.

      Remark RB : alpha <> E0zero ->forall n, (n < H'_ alpha n)%nat.
      Proof.
        intros _  n; subst  alpha; rewrite H'_eq2;
          destruct (E0_eq_dec beta E0zero).
        - subst; rewrite H'_eq1; auto with arith.
        - destruct (Halpha beta).
          + apply Lt_Succ.
          + transitivity (S n); auto with arith.
      Qed.
      
      Remark RD : dominates_from 1 (H'_ (E0_succ alpha)) (H'_ alpha).

        generalize PA_Succ; subst alpha.
        red; intros H k H0; rewrite (H'_eq2 (E0_succ beta));
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
          + replace (Canon (E0_succ beta) (S n)) with beta in H0.
            * transitivity (H'_ beta (S n)).
              -- destruct (Halpha beta).
                 ++ apply Lt_Succ.
                 ++ apply PE0; auto.
              -- destruct (Halpha beta).
                 ++  apply Lt_Succ.
                 ++ apply PC0.
            * now rewrite Canon_Succ.
      Qed.

      Remark RC : H'_ alpha <<= H'_ (E0_succ alpha).
      Proof.
        subst alpha; intro n; repeat rewrite H'_eq2.
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
      Hypothesis Hlim : E0limit alpha.

      Remark RBlim : forall n, (n < H'_ alpha n)%nat.
      Proof.
        intro n;   rewrite H'_eq3; auto.
        destruct (Halpha (Canon alpha (S n))).
        -  apply Canon_lt;  now apply Limit_not_Zero.
        -  eapply PB0; intro H.
           assert (H0 :cnf (Canon alpha (S n)) = cnf E0zero) by (f_equal; auto).
           simpl in H0;   apply (@T1limit_canonS_not_zero n (cnf alpha)); auto.
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
                   destruct  (Compat815.le_lt_or_eq _ _ H).
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

      Remark RClim : H'_ alpha <<= H'_ (E0_succ alpha).
      Proof.
        intro n; rewrite H'_eq2; apply Nat.lt_le_incl, RAlim; abstract lia.
      Qed.

      Remark RDlim : dominates_from 1 (H'_ (E0_succ alpha)) (H'_ alpha).
      Proof.
        red;intros; rewrite H'_eq2; apply RAlim; abstract lia.
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

  (*||*)
  
  Theorem P_alpha : forall alpha, P alpha. (* .no-out *)
  Proof. (* .no-out *)
    intro alpha; apply well_founded_induction with E0lt. 
  (* ... *) (*| .. coq:: none |*)
   - exact E0lt_wf.
   - apply P_alpha_0.
     (*||*)
  Qed.

End Proof_of_Abstract_Properties.

(* end snippet PAP *)

Section Abstract_Properties.

  Variable alpha : E0.

  Theorem H'_alpha_mono : strict_mono (H'_ alpha).
  Proof. now  destruct  (P_alpha alpha). Qed.

  Theorem H'_alpha_gt : alpha <> E0zero -> forall n, (n < H'_ alpha n)%nat.
  Proof. now  destruct  (P_alpha alpha). Qed.

  Theorem H'_alpha_Succ_le : H'_ alpha <<= H'_ (E0_succ alpha).
  Proof. now  destruct  (P_alpha alpha). Qed.

  Theorem H'_alpha_dom : dominates_from 1 (H'_ (E0_succ alpha)) (H'_ alpha).
  Proof. now  destruct  (P_alpha alpha). Qed.

  (** [H'_] is not mononotonous in [alpha] in general. 
      Nevertheless, this lemma may help (from [KS]) *)
  

  Theorem H'_restricted_mono_l : forall beta n, Canon_plus n alpha beta -> 
                                                H'_ beta n <= H'_ alpha n.
  Proof. now  destruct  (P_alpha alpha). Qed.


  Lemma H'_alpha_ge_id : id <<= H'_ alpha.
  Proof.
    destruct (E0_eq_dec alpha E0zero).
    - subst alpha; intro k; rewrite H'_eq1; cbn;auto with arith.
    - intro k;unfold id; now apply Nat.lt_le_incl, H'_alpha_gt. 
  Qed.

  Lemma H'_alpha_mono_weak : forall k l, k <= l ->
                                         H'_ alpha k <= H'_ alpha l.
  Proof.
    intros.
    destruct (Compat815.le_lt_or_eq k l H).
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
    Hypothesis Hgamma : beta = E0_succ gamma.

    Remark R1 : alpha o<= gamma.
    Proof. subst; now apply lt_Succ_le_2.  Qed.

    Remark R2 : {n : nat | forall p, n <= p -> H'_ alpha (S p) <= H'_ gamma (S p)}.
    Proof.  apply  H'_mono_l_1, R1.  Qed.

    Remark R3 : {n: nat | forall p, n <= p ->
                                    H'_ alpha (S p) < H'_ beta (S p)}.
    Proof.
      destruct R2 as [n Hn]; exists (Nat.max n 1).
      intros p H;  apply Nat.le_lt_trans with (H'_ gamma (S p)).
      - apply Hn; lia.
      - subst beta; apply (H'_alpha_dom gamma (S p)); auto with arith.
    Qed.

  End Succ_case.

  Section Limit_case.
    Hypothesis Hbeta: E0limit beta.

    Remark R4 : E0_succ alpha o< beta.
    Proof. now apply Succ_lt_T1limit. Qed.

    Remark R5 :  {n: nat | forall p, n <= p ->
                                     H'_ alpha (S p) < H'_ beta (S p)}.
    Proof.
      assert (E0_succ alpha o<= beta) by (apply Lt_Le_incl; apply R4).
      destruct   (H'_mono_l_1 _ _ H) as [x Hx].
      exists x; intros.
      apply Nat.lt_le_trans with (H'_ (E0_succ alpha) (S p)).
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

  
  Theorem H'_dom : dominates_strong (H'_ beta) (H'_ alpha). (* .no-out *)
  Proof.
    destruct H'_mono_l as [x Hx]; exists (S x); red.
    intros p H; inversion_clear H; apply Hx; auto with arith.
  Qed.

End Proof_of_H'_mono_l.

(* begin snippet HprimeDom *)
About H'_dom.
(* end snippet HprimeDom *)
  

(* To do : program tactics for a better interaction *)

Goal 
  (0 < H'_ (ltac:(mko (T1omega * T1omega * T1omega)%t1)) 12)%nat.
  ochange {| cnf := (T1omega * T1omega * T1omega)%t1; cnf_ok := eq_refl |}
          (E0_phi0 3).
  transitivity 11.
  - abstract lia.
  - apply H'_alpha_ge_id.
Qed.
