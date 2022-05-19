(** Injection from ordinals (less than epsilon0) in CNF into hydras.

 Pierre Castéran, LaBRI and Univ. Bordeaux 


We define a function [iota : T1 -> Hydra] such that if [alpha < beta], then there exists a battle from [iota beta] to [iota alpha].

Note that [iota] is not a bijection, but is sufficient for proving 
impossibility lemmas or minoration of battle lengths (see Hydra_Theorems).
*)

From Coq Require Import Relation_Operators.

From hydras Require Import Hydra_Lemmas Epsilon0 Canon Paths  .
Import Hydra_Definitions.

(** Let us transform any ordinal term into an hydra *)

(* begin snippet iotaDef *)

Fixpoint iota (a : T1) : Hydra :=
  match a with
  | zero => head
  | cons c n b => node (hcons_mult (iota c) (S n) (iotas b))
  end 
with iotas (a : T1) :  Hydrae :=
       match a with
       | zero => hnil
       | cons a0 n b  => hcons_mult (iota a0) (S n) (iotas b)
       end.
(* end snippet iotaDef *)

(**  We now prove  a lot of technical lemmas that relate Hydras and 
ordinals. *)

Lemma iota_iotas : forall alpha, nf alpha ->
                                 node (iotas alpha) =  iota alpha .
Proof. 
  induction alpha.
  - reflexivity.
  - intros; now cbn. 
Qed.

Lemma iotas_succ : forall alpha, nf alpha ->
                                 iotas (T1.succ alpha) =
                                 hy_app (iotas alpha) (hcons head hnil).
Proof.
  induction  alpha.
  - cbn; trivial.
  - destruct alpha1; intros.
    + T1_inversion H.
      subst alpha2;  replace (cons zero n zero) with (FS  n).
      * rewrite succ_compatS;   cbn;  clear  H;  induction n;simpl;auto.
        repeat f_equal;   injection IHn; auto.
      *  reflexivity.
    +   rewrite succ_rw1; simpl hy_app.
          simpl iotas; repeat f_equal; rewrite <- hcons_mult_app;
          rewrite IHalpha2; auto. 
       *  eauto with T1.
       *  discriminate.
Qed.



Lemma hy_app_l_nil : forall l, hy_app l hnil = l.
Proof.
  induction l;cbn; auto;  rewrite IHl;auto.
Qed.


Lemma iota_succ_R1 : forall  o, nf o -> R1 (iota (T1.succ o)) (iota o).
Proof.
  intros; repeat rewrite <- iota_iotas; auto.
  -   rewrite iotas_succ; auto ;   constructor.  
      replace  (iotas o) with (hy_app (iotas o) hnil) at 2.
      +   apply S0_app ;   constructor.
      +   now rewrite hy_app_l_nil.
  -  now apply succ_nf.
Qed.


Lemma iota_succ_round_n : forall  i alpha,
    nf alpha ->  round_n i (iota (T1.succ alpha)) (iota alpha).
Proof.
   left;  now apply iota_succ_R1.
Qed.


Lemma iota_succ_round : forall  o, nf o -> iota (T1.succ o) -1-> iota o.
Proof.
  intros; exists 0; left; now apply iota_succ_R1.
Qed.

Lemma iota_rw1 :
  forall i alpha,  nf alpha -> T1limit alpha = true ->
                   iota (canonS (cons alpha 0 zero) i) =
                   hyd1 (iota (canonS alpha i)).
Proof.                        
  intros i alpha H H0; unfold canonS; rewrite  canonS_lim1; auto.
Qed.

Lemma iota_rw2 :
  forall i n alpha,  nf alpha -> T1limit alpha = true ->
                     iota (canonS (cons alpha (S n) zero) i) =
                     node (hcons_mult (iota alpha) (S n) 
                                      (hcons
                                         (iota (canonS alpha i)) hnil)).
Proof.                        
  intros i n alpha H H0; unfold canonS; rewrite  canonS_lim2; auto.
Qed.


Lemma iota_rw3 :
  forall i  alpha,  nf alpha -> 
                    iota (canonS (cons (T1.succ alpha) 0 zero) i) =
                    node (hcons_mult (iota alpha) (S i) hnil).
Proof.                        
  intros i  alpha H; unfold canonS;  rewrite  canonS_phi0_succ_eqn; auto.
Qed.


Lemma iota_rw4 :
  forall i n  alpha ,  nf alpha -> 
                       iota (canonS (cons (T1.succ alpha) (S n) zero) i) =
                       node (hcons_mult (iota (T1.succ alpha)) (S n) 
                                        (hcons_mult (iota alpha) (S i) hnil)).
Proof.
  intros i  n alpha H; unfold canonS;  rewrite  canonS_cons_succ_eqn2; auto.
Qed.


Lemma iota_tail :
  forall i   alpha n beta,
    nf (cons alpha n beta) ->
    beta <> zero ->
    iota (canonS (cons alpha n beta) i) =
    node (hcons_mult (iota alpha) (S n) (iotas (canonS beta i)) ).
Proof.                                  
  intros i   alpha n beta H H0; unfold canonS; rewrite  canon_tail; auto.
Qed.


Lemma R1_hcons : forall h s1 s2, R1 (node s1) (node s2) ->
                                 R1 (node (hcons h s1)) (node (hcons h s2)).
Proof. inversion 1;split;now right. Qed.

Lemma R1_hcons_mult  : forall n h s1 s2,
    R1 (node s1) (node s2) ->
    R1 (node (hcons_mult  h n s1))
       (node (hcons_mult  h n s2)).
Proof. inversion 1; split; now apply hcons_mult_S0. Qed.


Lemma R1_R2 : forall h h', R1 h h' -> R2 0 (hyd1 h) (hyd1  h').
Proof.
  intros; destruct h, h'; left;
    change (hcons (node h0) hnil) with (hcons_mult (node h0) 1 hnil);
    now left.
Qed.

(* The sequence s contains a head *)

Inductive mem_head : Hydrae -> Prop :=
  hh_1 : forall s, mem_head (hcons head s)
| hh_2 : forall h s, mem_head s -> mem_head (hcons h s).


Lemma S0_mem_head : forall s s', S0 s s' -> mem_head s.
Proof.
  induction 1.
  -  left.
  -  now right.
Qed.

Lemma mem_head_mult_inv : forall n h s, mem_head (hcons_mult h n s) ->
                                        h = head \/ mem_head s.
Proof. 
  induction n; cbn ; auto. 
  inversion 1;  auto.
Qed. 


Lemma R1_mem_head : forall l l', R1 (node l) (node l') -> mem_head l.
Proof.
  inversion 1;   eapply S0_mem_head; eauto.
Qed.

Lemma limit_no_head : forall alpha, nf alpha -> T1limit alpha = true ->
                                    ~ mem_head (iotas alpha).
Proof. 
  induction alpha.
  - discriminate.
  - intros; simpl;  destruct (T1limit_cases H).
    +  auto.
    +  destruct a;  subst; intro H2;  inversion H2.
       destruct alpha1.
       *    destruct H1;auto.
       *    discriminate H4.
       *  destruct  (mem_head_mult_inv _ _ _ H4).
          destruct alpha1.
          { destruct H1;   auto.  }
          discriminate H6.
          inversion H6.
    +  intro H7;
         change
           (hcons (iota alpha1) (hcons_mult (iota alpha1) n (iotas alpha2)))
           with   (hcons_mult (iota alpha1) (S n) (iotas alpha2)) in H7.
       destruct  (mem_head_mult_inv _ _ _ H7).
       *    destruct alpha1.
            destruct a.
            destruct H2;auto.
            discriminate.
       *   destruct IHalpha2;  eauto with T1.
           tauto. 
Qed.


Lemma limit_no_R1 : forall alpha, nf alpha ->
                                  T1limit alpha = true ->
                                  forall h', ~ R1 (iota alpha) h'.
Proof.
  intros alpha H H0 h' H1; generalize ( limit_no_head _ H H0).
  intro H2; case_eq  (iota alpha); case_eq h';intros.
  subst h';rewrite <- iota_iotas in H1; auto. 
  generalize (R1_mem_head _ _ H1).
  tauto.
Qed.


Lemma iota_of_succ :
  forall beta, nf beta ->
               iota (T1.succ beta) =
               match (iota beta) with
                 node s => node (hy_app s (hcons head hnil))
               end.
Proof.
  intros;  rewrite <- iota_iotas; auto.
  rewrite (iotas_succ); auto.
  rewrite <- iota_iotas; auto.    
  apply succ_nf;auto.
Qed.

(* begin hide *)

Section DS_iota.
  Variable alpha : T1.
  Variable i : nat.
  Hypothesis Halpha : nf alpha.
  Hypothesis nonzero : alpha <> zero.  

  Remark alpha_pos : LT zero  alpha. 
  Proof.   now apply not_zero_lt.   Qed.

  Hypothesis Hrec : forall beta,
      beta <> zero -> LT beta  alpha ->
      forall gamma,  gamma = canonS beta i ->
                     round_n i (iota beta) (iota gamma).
  
  Lemma DS_iota_1 : forall gamma, nf gamma -> alpha = T1.succ gamma ->
                                  round_n i (iota alpha)
                                          (iota (canonS alpha i)).
  Proof.
    intros; subst alpha; rewrite canonS_succ; auto.
    now apply iota_succ_round_n.
  Qed. 

  Lemma iota_phi0 : forall alpha, nf alpha ->
                                  iota (T1.phi0 alpha)= hyd1 (iota alpha).
  Proof.
    intros; now simpl.
  Qed.
  
  Lemma DS_iota_2 : forall lambda,
      nf lambda -> alpha = T1.phi0 lambda ->
      T1limit lambda ->
      round_n i (iota alpha) (iota (canonS alpha i)).                             
  Proof. 
    intros;subst alpha.
    repeat rewrite iota_phi0; trivial.
    assert (nz : lambda <> zero).
    { eapply T1limit_not_zero; eauto. }
    right;  specialize (Hrec lambda nz (head_LT_cons  Halpha)).
    (* unfold T1.phi0; *) rewrite iota_rw1; trivial.
    right; left;  destruct (Hrec (canonS lambda i)); auto.
    elimtype False;  eapply limit_no_R1; eauto.
  Qed.

  Lemma DS_iota_3 : forall  gamma,   nf gamma ->
                                     alpha = T1.phi0 (T1.succ gamma) ->
                                     round_n i (iota alpha)
                                             (iota (canonS alpha i)).
  Proof.
    intros; subst alpha; (* unfold T1.phi0; *) rewrite iota_rw3; auto.
    -  simpl iota;  rewrite (iota_of_succ gamma); auto.
       case_eq (iota gamma).
       right;  left;  simpl hy_app;  left.
       split; clear H0 ; induction h; auto.
       +  simpl; left.
       +  simpl; right;  auto. 
  Qed.

  Section Proof_case_4.
    Variable lambda: T1.
    Hypothesis Hlambda : nf lambda.
    Hypothesis Hlim : T1limit lambda.
    Variable n : nat.
    Hypothesis Hn : alpha = cons lambda (S n) zero.

    Remark rem1 : canonS alpha i = cons lambda n (T1.phi0 (canonS lambda i)).
    Proof.
      subst alpha;  unfold canonS; rewrite canonS_lim2; auto.
    Qed.

    Lemma canonS_iota_4 :  round_n i (iota alpha) (iota (canonS alpha i)).
    Proof.
      rewrite rem1;  subst alpha;  simpl. 
      right;  right ;  right; rewrite <- hcons_mult_comm.
      apply hcons_mult_S2.  
      left;  specialize (Hrec lambda).
      assert (lambda t1< cons lambda (S n) zero)%t1.
      {  apply head_LT_cons; auto with T1. }
      specialize (Hrec (T1limit_not_zero Hlambda Hlim)
                       H  (canonS lambda i) (refl_equal _)).
      destruct Hrec; [| trivial];
        elimtype False;
        eapply limit_no_R1; eauto.
    Qed.

  End Proof_case_4.

  Section Proof_case_5.
    Variable gamma: T1.
    Hypothesis Hgamma : nf gamma.
    Variable n : nat.
    Hypothesis Hn : alpha = cons (T1.succ gamma) (S n) zero.
    
    Remark rem2 : canonS alpha i =
                  cons (T1.succ gamma)  n (cons gamma i zero).
    Proof.
      subst alpha;  unfold canonS; now rewrite canonS_cons_succ_eqn2.
    Qed.
    
    Remark rem3 : iota (canonS alpha i) =
                  node (hy_app (hcons_mult (iota (T1.succ gamma)) (S n) hnil)
                               (hcons_mult (iota gamma) (S i) hnil)).
    Proof.
      rewrite rem2; simpl; rewrite (iota_of_succ gamma); [| trivial].
      - case_eq (iota gamma).
        +  intros;  rewrite <- hcons_mult_comm; f_equal.
           rewrite <-  hcons_mult_app; simpl; rewrite  hcons_mult_comm;
             f_equal.
    Qed. 

    Lemma canonS_iota_5 :  round_n i (iota alpha) (iota (canonS alpha i)).
    Proof.
      rewrite rem3;  subst alpha.
      simpl (iota (cons (T1.succ gamma) (S n) zero)); simpl hy_app.
      assert (R1 (iota (T1.succ gamma)) (iota  gamma)).
      {    apply iota_succ_R1; auto. }
      assert (S1 i (hcons (iota (T1.succ gamma)) hnil)
                 (hcons_mult (iota gamma) (S i) hnil)).
      {  left; auto. }
      generalize (S1_app i (hcons_mult (iota (T1.succ gamma)) n hnil) _ _ H0);
        intro H2; right.
      left; apply S1_next.
      simpl in H2; simpl.
      rewrite <- hcons_mult_app in H2.
      replace (hcons_mult (iota (T1.succ gamma)) n
                          (hy_app hnil (hcons (iota (T1.succ gamma)) hnil)))
        with
          (hy_app (hcons_mult (iota (T1.succ gamma)) n hnil)
                  (hcons (iota (T1.succ gamma)) hnil))
        in H2.
      - replace (hcons (iota (T1.succ gamma))
                       (hcons_mult (iota (T1.succ gamma)) n hnil))
          with (hy_app (hcons_mult (iota (T1.succ gamma)) n hnil)
                       (hcons (iota (T1.succ gamma)) hnil)).
        + apply S1_app;  auto.
        + generalize (iota (T1.succ gamma)) as h;intro.
          rewrite <- hcons_mult_app.
          simpl hy_app.
          now rewrite  <-  hcons_mult_comm.
      -  generalize (iota (T1.succ gamma)) as h;intro.
         simpl hy_app;  rewrite <- hcons_mult_app.
         simpl hy_app; auto.
    Qed.

  End Proof_case_5.

  Section Proof_case_6.
    Variables beta gamma: T1.
    Hypothesis Hbeta : nf beta.
    Hypothesis Hgamma : nf gamma.
    Hypothesis gamma_pos : gamma <> zero.
    Variable n : nat.
    Hypothesis Hn : alpha = cons  beta n gamma.
    
    
    Remark rem6 : canonS alpha i = cons beta n (canonS gamma i).
    Proof.
      subst alpha;  unfold canonS; rewrite canon_tail; auto with T1.    
    Qed.
    
    Remark rem61 : gamma t1< alpha.
    Proof.
      subst alpha;  now apply tail_LT_cons.
    Qed. 
    
    Remark rem62 : round_n i (iota gamma) (iota  (canonS gamma i)).
    Proof.
      eapply Hrec; auto;  apply rem61.
    Qed.
    
    Lemma canonS_iota_6 :  round_n i (iota alpha) (iota (canonS alpha i)).
    Proof.
      rewrite rem6;  destruct rem62; subst alpha.
      -  simpl iota; left; apply R1_hcons; apply R1_hcons_mult;
           repeat rewrite iota_iotas.
         +  assumption.
         + apply nf_canon;auto.
         +  auto.
      -  right;  simpl; destruct n.
         +  simpl;
              replace  (hcons (iota beta) (iotas gamma)) with
                  (hy_app (hcons (iota beta) hnil) (iotas gamma)).
            replace  (hcons (iota beta) (iotas (canonS gamma i))) with
                (hy_app (hcons (iota beta)hnil) (iotas (canonS gamma i))).
            apply R2_app; repeat  rewrite iota_iotas; auto.
            eapply nf_canon;auto.
            simpl; auto.
            simpl; auto.
         + replace
             (hcons (iota beta) (hcons_mult (iota beta) (S n0) (iotas gamma)))
             with
               (hy_app (hcons (iota beta) (hcons_mult (iota beta) (S n0) hnil))
                       (iotas gamma)).
           replace
             (hcons (iota beta) (hcons_mult (iota beta) (S n0)
                                            (iotas (canonS gamma i))))
             with
               (hy_app (hcons (iota beta) (hcons_mult (iota beta) (S n0) hnil))
                       (iotas (canonS gamma i))).
           * apply R2_app;repeat  rewrite iota_iotas; auto.
             eapply nf_canon;auto.
           *  simpl; auto.
              simpl; auto.
              repeat f_equal.                
              rewrite <- hcons_mult_app;  now simpl hy_app.
           * rewrite <- hcons_mult_comm; simpl; f_equal.
             rewrite  hcons_mult_comm; simpl; f_equal. 
             now rewrite  <- hcons_mult_app.
    Qed.

  End Proof_case_6.

  Remark all_cases : exists beta n gamma,
      nf beta /\ nf gamma /\ alpha = cons beta n gamma.
  Proof.
    destruct alpha as [|  beta n gamma].
    - destruct nonzero; auto.
    - exists beta, n, gamma; split;eauto with T1.
  Qed.

  Lemma canonS_iota_final :  round_n i (iota alpha) (iota (canonS alpha i)).
  Proof.
    destruct all_cases as [beta [n [gamma Heq]]]; decompose [and] Heq.
    destruct (zero_limit_succ_dec Halpha).
    -   destruct s.
        +  contradiction.
        +  destruct n.
           * destruct (zero_limit_succ_dec H).
             { destruct s.
               -  subst beta; rewrite H2 in Halpha.
                  generalize (nf_of_finite Halpha).
                  intro; subst gamma alpha.
                  simpl iota;  left.
                  split; left.
               - destruct gamma.
                 + eapply DS_iota_2 with beta; auto.
                 + eapply canonS_iota_6.
                   eexact H1.
                   discriminate.
                   eexact H2.
             }
             destruct gamma.     
             { destruct s as [gamma' [H3 H4]].
               subst beta;  eapply DS_iota_3 ; eauto.
             }
             eapply canonS_iota_6.
             eexact H1.
             discriminate.
             eauto.
           *  
             destruct gamma.
             { destruct(zero_limit_succ_dec H).
               - destruct s.  
                 + subst beta  alpha;  left.
                   split.
                   simpl (hcons_mult head (S (S n)) hnil).
                   left.
                 + eapply canonS_iota_4.
                   eexact H.
                   auto.
                   eauto. 
               -  destruct s as [gamma [H3 H4]].
                  subst beta; eapply canonS_iota_5.
                  eexact H3.
                  eauto. 
             }
             eapply canonS_iota_6.
             eexact H1.
             discriminate. 
             eauto.
    -  destruct s as [delta [H3 H4]].
       eapply DS_iota_1; eauto.
  Qed.    

End DS_iota.

(* end hide *)

Lemma canonS_iota_i : forall i alpha , nf alpha ->  alpha <> zero ->
                                round_n i (iota alpha) (iota (canonS alpha i)).
Proof.
  intros i alpha ; transfinite_induction_lt alpha.
  intros; eapply canonS_iota_final;eauto.
  intros beta H2 H3 gamma H4; rewrite H4; apply H; eauto with T1.
Qed.

(* begin snippet canonSIota *)

Lemma canonS_iota i a :
  nf a -> a <> 0 -> iota a -1-> iota (canon a (S i)). (* .no-out *)
(*| .. coq:: none |*)
Proof.
  intros;  destruct (canonS_iota_i i a  H H0).
  - exists 0; now left.
  - exists i; now right.
Qed.
  (*||*)
  (* end snippet canonSIota *)
  
  Lemma canonS_rel_rounds : forall n alpha beta,
      nf alpha -> nf beta ->
      alpha <> zero ->
      beta = canonS alpha n -> 
      iota alpha -+-> iota beta.
  Proof.
    inversion 4; subst; left; apply canonS_iota; auto.
  Qed.

Lemma trace_to_round_plus h' : forall t h,  trace_to h' t h -> round_plus h h'. 
Proof.
 induction 1.
 - left; exists n; auto.
 - right with h'0. exists n; auto.
   apply IHtrace_to.
Qed.

Import MoreLists.
(* begin hide *)

Lemma trace_to_std_0 h' : forall l i h,
    trace_to h' (iota_from i (S l)) h ->
    rounds standard  i h (S l + i) h'.
Proof.
  induction l.
  simpl.
  intros.  
  left.
  red.
  simpl.
  inversion H.
  auto. 
  inversion H4.
  intros.
  inversion H. subst. 
  
  right with h'0.
  simpl.
  auto.
  specialize (IHl (S i) h'0 H4).
  simpl.
  rewrite Nat.add_succ_r in IHl. auto.
Qed.

(* end hide *)

Lemma trace_to_std i h j h': (i <= j)%nat ->
                             trace_to h' (interval i j) h ->
                             rounds standard  i h (S j) h'.
Proof.
 unfold interval. intro H.
 simpl in H.  replace (S j - i)%nat with (S (j - i))%nat by lia.
 intro.
  apply trace_to_std_0 in H0.
   replace (S (j - i) + i)%nat with (S j) in H0 by lia. auto.
Qed.


Lemma path_toS_trace alpha s beta :
  path_toS beta s alpha -> nf alpha -> trace_to (iota beta) s (iota alpha).
Proof.
  induction 1.
  - destruct H.
    intro; left. 
    subst.
    apply canonS_iota_i; auto.
  - intro.
    right with (iota gamma).
    destruct H.
    subst.
    apply   canonS_iota_i; auto.
    apply IHpath_toS.
    destruct H.
    subst.
    apply nf_canon.
    auto.
Qed.   

  Lemma path_toS_round_plus alpha s beta :
    path_toS beta s alpha -> nf alpha ->
    iota alpha -+-> iota beta.
    intros; apply trace_to_round_plus with s.
    now apply path_toS_trace.
  Qed.

  (* begin snippet pathToRoundPlus *)
  
  Lemma path_to_round_plus a s b :
    path_to b s a -> nf a -> iota a -+-> iota b. (* .no-out *)
  (*| .. coq:: none |*)
  Proof.
    intros H H0; apply path_to_path_toS in H.
    now apply  path_toS_round_plus with (MoreLists.unshift s).
  Qed.
  (*||*)
  (* end snippet pathToRoundPlus *)
  
  
  Lemma acc_from_to_round_plus alpha beta :
    nf alpha -> nf beta -> alpha <> 0 ->
    acc_from alpha beta -> iota alpha -+-> iota beta.
  Proof.
    destruct 4.
    rewrite path_to_path_toS_iff in H2.
    eapply   path_toS_round_plus; eauto.
    eapply path_to_not_In_zero; eauto.
  Qed.

  (** Any strict inequality on [T1] can be converted into a (free) battle *)

  (* begin snippet LTToRoundPlus *)
  
  Lemma LT_to_round_plus a b : b t1< a ->  iota a -+-> iota b. (* .no-out *)
  (*| .. coq:: none |*)
  Proof.
    intros H; apply acc_from_to_round_plus; eauto with T1.
    - intro; subst; apply (not_LT_zero H).
    - apply LT_acc_from; eauto with T1.
  Qed.
 (*||*)
 (* end snippet LTToRoundPlus *)
