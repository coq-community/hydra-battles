(** Abstract machine for following an Euclidean addition chain *)
(** adapted from the old contrib coq-additions *)

(** Work in progress 

*)

Require Import Monoid_def Monoid_instances List PArith Relations.
Require Import Strategies Lia.
Generalizable All Variables.
Import Morphisms.
Import Monoid_def.
Require Import Recdef Wf_nat.
Require Import More_on_positive.
Require  Import Pow.
Require Import Euclidean_Chains.

(** basic instructions *)
(* begin snippet AMDef *)
Inductive instr : Set :=
| MUL : instr
| SQR : instr
| PUSH : instr
| SWAP : instr.       

Definition code := list instr.
(* end snippet AMDef *)

(* statistics *)

Definition  mults_squares  c :=
  let fix count (c: code) mults squares  :=
    match c with
      nil => (mults, squares)
    | PUSH :: c' | SWAP :: c' => count c' mults squares
    | SQR :: c' => count c' mults (S squares)
    | MUL :: c' => count c' (S mults) squares
    end  in count c 0%nat 0%nat.
            
                                 
(* semantics *)
(*************)
(* begin snippet AMSem:: no-out  *)
Section Semantics.

 Variable A : Type.
 Variable mul : A -> A -> A.
 Variable one : A.

 Definition stack := list A.
 Definition config := (A * list A)%type.

 Fixpoint exec (c : code) (x:A) (s: stack) : option config :=
   match c, s with
     nil, _ => Some (x,s)
   | MUL::c, y::s => exec c (mul x y) s
   | SQR::c, s => exec c (mul x x) s
   | PUSH::c, s => exec c x (x::s)
   | SWAP::c, y::z::s => exec c x (z::y::s)
   | _,_ => None
   end.

 Lemma exec_app :
   forall (c c' : code) x s ,
     exec (c ++ c') x s =
     match exec c x s  with
     | None => None
     | Some (y,s') => exec c' y s'
     end.
 (* end snippet AMSem *)
 Proof.
   induction c; cbn.
   - trivial.
   - intros c' x s; destruct a.
     + destruct s.  
       * auto.
       *  rewrite IHc. auto.
     + rewrite IHc.
       auto.
     + rewrite IHc; auto.
     + destruct s; auto.
       * destruct s; auto.
 Qed.

 (* begin snippet AMSemb *)
 
(** Main well-formed chains *)
Definition F1 : code := nil.

(** raises x to its cube *)

Definition F3 := PUSH::SQR::MUL::nil.

(** chain for raising x to its (2 ^ q)th power *)

Fixpoint F2q_of_nat q := match q with
                  | 0%nat => nil
                  | S p => SQR:: F2q_of_nat  p
                  end.

Definition F2q (p:positive) :=
  F2q_of_nat (Pos.to_nat p). 

(** for computing x^(pq+r) passing by  x^p *)

Definition KFF (kpr mq:code) : code := 
  kpr++(mq++MUL::nil).

(** for computing x^p and x^(pq) *)

Definition FFK (mp mq: code) := mp ++ PUSH :: mq. 

(** for computing x^p then x^(pq + r)  *)

Definition KFK (kpr mq: code) :=
  kpr ++ PUSH::SWAP :: (mq ++ MUL :: nil). 

Definition FK (fn: code) := PUSH::fn. 

End Semantics.

Definition chain_apply c {A:Type}
           {op:A->A->A}{one:A}{equ: Equiv A}
           (M: EMonoid op one equ) x
  := exec _ op c x nil.


(** Example code for 7 via 3 *)
Example  M7_3 := PUSH::PUSH::SQR::MUL::PUSH::SQR::SWAP::MUL::nil.

Compute chain_apply  M7_3 Natplus 1%nat .

(** Example code for 31 via 7 *)
Example C31_7 := KFF M7_3 (F2q 2).

Compute chain_apply C31_7 Natplus 1%nat.

(* end snippet AMSemb *)

Require Import NArith.

Compute chain_apply C31_7 NMult 2%N.


Compute chain_apply (FFK F3 (F2q 3)) Natplus %nat. (** 24, 3 *)

(** For 99 and 24 *)
Example K99_24 := KFK (FFK F3 (F2q 3)) (F2q 2).
Compute K99_24.

Compute chain_apply (KFK (FFK F3 (F2q 3)) (F2q 2)) Natplus 1%nat.


(** Specification and generation of correct chains *)

(** We have to build equivalences between configurations *)

Inductive stack_equiv {A}`{M : @EMonoid A op one equ}:
  list A -> list A -> Prop
  :=
  stack_equiv0 : stack_equiv  nil nil
  | stack_equivn: forall x y s s',  x == y -> stack_equiv s s' ->
                                  stack_equiv (x::s) (y:: s').


Definition config_equiv  {A}`{M : @EMonoid A op one equ}
           (c c' : config A): Prop := 
  fst c == fst c'  /\ stack_equiv (snd c) (snd c').



Inductive result_equiv`{M : @EMonoid A op one equ}: relation (option (config A)):= 
  result_equiv_fail : result_equiv None None
| result_equiv_success : forall x s y s',
    config_equiv  (x,s) (y, s') ->
    result_equiv (Some (x,s)) (Some (y,s')).

Definition Fchain_correct (p: positive) (c: code) :=
  (forall  A op one equ (M: @EMonoid A op one equ) (x:A) s,
        result_equiv (M:=M) (exec A op c x s)
                     (Some (Pow.Pos_bpow x p, s))) .


Definition Kchain_correct  n p c :=
   (forall   A op one equ (M: @EMonoid A op one equ) (x:A) s,
        result_equiv (exec A op c x s)
                     (Some (Pow.Pos_bpow  x n, Pow.Pos_bpow  x p ::s))).


Definition correctness_statement (s: signature) : code -> Prop :=
match s  with
  | gen_F p => fun c => Fchain_correct p c
  | gen_K p d   => fun c => Kchain_correct  (p + d) p c
end.



#[ global ] Instance Stack_equiv_refl {A}`{M : @EMonoid A op one equ} :
  Reflexive stack_equiv.
Proof.
  red; intros. induction x.
  - now left.
  - right; [reflexivity | assumption].
Qed.

#[ global ] Instance Stack_equiv_equiv {A}`{M : @EMonoid A op one equ}:
  Equivalence stack_equiv.
Proof.
 split.
 - apply Stack_equiv_refl.
 - red. induction x; destruct y.
   + now left.
   + inversion 1.
   +  inversion 1.
   + inversion 1; subst; right.
     * now symmetry.
     * now apply IHx.
 - red; induction x.
   + inversion 1; auto.
   + destruct y.
     * inversion 1.
     *  inversion 1; subst.
        destruct z.
        -- inversion 1.
        -- inversion 1; subst; right.
           transitivity a0; trivial.
           eapply IHx;eauto.
Qed.

#[ global ] Instance result_equiv_equiv `{M : @EMonoid A op one equ}:
  Equivalence result_equiv.
Proof.
  split.
  - red; destruct x.
   + destruct c; right; split; reflexivity.
   + left.
  - red; destruct x, y.
    + inversion 1; subst; destruct H2; right; split; now symmetry.
    + inversion 1.
    + inversion 1.
    + left.
  - red; destruct x.
    + destruct y.
      *  inversion 1; subst.
         destruct H2, z.
         -- destruct c; inversion 1; subst; right.
            destruct H4; split.
            ++ now transitivity y.
            ++ now transitivity s'.
         -- inversion 1.
      * inversion 1.
    + destruct y.
     * inversion 1.
     * auto.
Qed.



Lemma exec_equiv `{M : @EMonoid A op one equ} :
  forall c x s y s' , config_equiv (x, s) (y, s') ->
                      result_equiv (exec A op c x s) (exec A op c y s').
Proof.
  induction c.
  - simpl; now constructor.
  -  destruct a.
     + destruct s.
       * inversion 1.  inversion H1.  cbn in *; subst;simpl; constructor.
       *  inversion 1; cbn in *; inversion H1; subst;  simpl; apply IHc.
          constructor; trivial.
          cbn.  now apply Monoid_def.Eop_proper.
     +  intros;simpl; apply IHc.
        destruct H; split; auto.
        cbn;apply  Monoid_def.Eop_proper; auto.
     + intros; simpl;  apply IHc.
       destruct H; split; auto.
       right; auto.
     + destruct s; simpl.
       *  destruct s'.
          -- constructor.
          -- inversion 1.
             inversion H1.
       * destruct s'.
         inversion 1.
         inversion H1.  destruct s, s'.
         -- constructor.
         -- inversion 1; inversion H1.
            inversion H1.
            inversion H7.
         -- inversion 1.
            inversion H1.
            inversion H7.
         --   intros; apply IHc; auto.
              inversion H.
              inversion H1; subst.
              inversion H7; subst. 
              constructor; auto; right; auto.
              right; auto.
Qed.


#[ global ] Instance exec_Proper `{M : @EMonoid A op one equ} :
  Proper (Logic.eq ==> equiv ==> stack_equiv ==> result_equiv) (@exec A op) .
Proof.
 intros c c' Hx x x' Hequiv s s' Hs; subst.
 apply exec_equiv;split; auto.
Qed.



Lemma F1_correct : Fchain_correct  1  F1.
Proof.
  constructor; intros. cbn. split; reflexivity.
Qed.

(** F3 is correct *)


Lemma F3_correct : Fchain_correct  3 F3.
Proof.
  constructor; intros. cbn.
  fold mult_op.
  constructor.
  - cbn; now rewrite Eop_assoc.
  - apply Stack_equiv_refl. 
Qed.

Import Pow.


Lemma F2q_correct_0: forall `{M : @EMonoid A op one equ} (n:nat) x s,
    result_equiv (exec A op (F2q_of_nat n) x s)
                 (Some(Pow.power x (2 ^ n), s)).
  induction n.
  -  simpl.
     intros; f_equal; right; split.
     + cbn; rewrite Eone_right.
       reflexivity.
     + reflexivity.
  - intro x; simpl; intro s; rewrite IHn.
    right; split;auto.
    + cbn.   replace (2 ^ n + (2 ^ n + 0))%nat with (2 * ( 2 ^ n) )%nat.
      * fold mult_op;  assert (x * x == x ^2) by (now rewrite  sqr_eqn).
        transitivity ((x ^ 2) ^2 ^ n).
        now apply power_proper.
        rewrite  power_of_power.
        apply power_proper.
        reflexivity.
        lia.
      * lia.
    + reflexivity.
Qed.


Lemma F2q_correct_1 (n:nat)  : Fchain_correct (Pos.of_nat (2 ^ n))
                                              (F2q_of_nat n). 
Proof.
  red;intros;  intros; rewrite F2q_correct_0.
  right; split.
  -  cbn;rewrite Pos_bpow_ok_R.
     + reflexivity.
     + apply Nat.pow_nonzero.
       discriminate.
  - reflexivity.
Qed.

Remark Pos_to_nat_diff_0 n : Pos.to_nat n <> 0%nat.
Proof.
   rewrite Nat.neq_0_lt_0; apply Pos2Nat.is_pos.
Qed.



Lemma  F2q_correct (n:positive)  : Fchain_correct (2 ^ n) (F2q n). 
Proof.
  unfold F2q.
  replace (2 ^n)%positive with (Pos.of_nat (2 ^ Pos.to_nat n)%nat).
  apply F2q_correct_1.
  rewrite   Compatibility.Pos_pow_power.
  rewrite <- Pos_bpow_ok_R.
  -  rewrite Pos_bpow_ok.
     + rewrite Nat2Pos.id.
       *  generalize (Pos.to_nat n).
          intros; rewrite Compatibility.nat_power_ok.
          induction n0; simpl; auto.
          rewrite  Nat2Pos.inj_mul.
         --  rewrite IHn0; simpl (Pos.of_nat 2).
             f_equal.
             unfold mult_op;  unfold P_mult_op.
             f_equal.
         -- discriminate.
         --  clear IHn0; induction n0;simpl.
             ++  discriminate.
             ++  remember (2%nat ^ n0) as n1.
                 unfold mult_op. 
                 unfold nat_mult_op.
                 lia.
       * apply Pos_to_nat_diff_0.
  -  apply Pos_to_nat_diff_0.
Qed.


Section CompositionProofs.

  Section FK.
    Variable n : positive.
    Variable cn : code.
    Hypothesis Hn : Fchain_correct n cn.

    Lemma FK_correct : Kchain_correct n 1 (FK cn).
    Proof.
      intros A op one equ M x s;     
        specialize (Hn _ _ _ _ M x (x::s)).
      inversion Hn; subst; cbn.
      rewrite Hn; right; split; reflexivity.
    Qed.

    End FK.

  Section App.
    Variables n p:  positive.
    Variables cn cp: code.
    Hypothesis Hn : Fchain_correct n cn .
    Hypothesis Hp : Fchain_correct p cp. 

    Lemma correct_app : Fchain_correct (n * p) (cn ++ cp).
    Proof.
      intros A op one equ M x s.
      rewrite exec_app.
      specialize (Hn _ _ _ _ M x s); inversion Hn; subst.
      specialize (Hp _ _ _ _ M x0 s0); inversion Hp; subst.
      right; destruct H3.
      split.
      - rewrite H2; destruct H1.
        cbn in *;rewrite H1, Pos_bpow_of_bpow; now rewrite Pos.mul_comm. 
      -  transitivity s0;auto.
         inversion H1;auto.
    Qed.

  End App.

  Section FFK.
    Variables p q:  positive.
    Variables cp cq: code.
    Hypothesis Hp : Fchain_correct p cp.
    Hypothesis Hq : Fchain_correct q cq.

    Lemma FFK_correct : Kchain_correct (p * q) p (FFK cp cq).
    Proof.
    red; intros; unfold  FFK; cbn; rewrite exec_app.
    specialize (Hp A op one equ M x s); inversion Hp; subst; cbn.
    inversion H1; subst.
    specialize (Hq A op one equ M x0 (x0::s0));inversion Hq; subst.
    rewrite H3, Hq;  right; inversion H5; split.  
    - cbn in *; rewrite H0; repeat rewrite Pos_bpow_ok; 
        rewrite power_of_power.
      apply power_proper; auto.  
      + reflexivity.
      + rewrite Pos2Nat.inj_mul; now rewrite mult_comm.
    - transitivity s1;auto.
      + inversion H5;auto.
        now  symmetry.
      + transitivity (x0::s0); auto. 
        right; auto.
  Qed.

  End FFK.
  

  Section KFK.
    Variables p q r : positive.
    Variables kpr mq : code.
    Hypothesis Hpr : Kchain_correct p r kpr.
    Hypothesis Hq : Fchain_correct q mq.

    Lemma KFK_correct : Kchain_correct (p * q + r)  p (KFK kpr mq).
    Proof.
      red; unfold KFK.  intros; cbn.
      generalize (Eop_proper M); intros Hprop.
      rewrite exec_app.     
      specialize (Hpr _ _ _ _ M x s); inversion Hpr; subst; cbn.
      inversion H1;subst; cbn in *.
      destruct s0; [ inversion H2|].   
      inversion H2;subst; rewrite exec_app.
      specialize (Hq _ _ _ _ M x0 (a::x0::s0)).
      inversion Hq;subst.
      inversion H5. cbn in H4, H7.
      transitivity (Some (Pos_bpow x0 q * a, x0  :: s0)). 
      - cbn; inversion H7; subst.
        right.
        split.
        * cbn; fold mult_op; cbn.
          rewrite H12, H4; reflexivity.  
        * cbn; assumption. 
      - right; split.
       +  cbn; rewrite Pos_bpow_of_plus, H6.
      rewrite Pos.mul_comm, <- Pos_bpow_of_bpow, H0; reflexivity.
       + cbn; right; auto.
    Qed.

    Lemma KFF_correct: Fchain_correct (p * q + r)  (KFF kpr mq).
    Proof.
      red; unfold KFF; intros; cbn.
      generalize (Eop_proper M); intros Hprop.
      rewrite exec_app.     
      specialize (Hpr _ _ _ _ M x s).
      inversion Hpr; subst.
      inversion H1;subst; cbn in *.
      inversion H2;subst; rewrite exec_app.
      specialize (Hq _ _ _ _ M x0 (x1::s1)).
      inversion Hq;subst.
      inversion H5; cbn in H4, H8; cbn.
      inversion H8; subst; right; split.
      - cbn; fold mult_op;
          rewrite Pos_bpow_of_plus, H4, H0, Pos.mul_comm, Pos_bpow_of_bpow,
          H12, H6; reflexivity.
      - cbn; now transitivity s1.
    Qed.

  End KFK.

  End CompositionProofs.

(** *  Euclidean chain generation *)

Require Import Dichotomy BinaryStrat.

Definition  OK (s: signature) 
  := fun c: code => correctness_statement s c.



Section Gamma.

Variable gamma: positive -> positive.
Context (Hgamma : Strategy gamma).


Function chain_gen  (s:signature) {measure signature_measure}
  :  code :=
  match s with
    gen_F i =>
    if pos_eq_dec i 1 then F1 else
      if pos_eq_dec i 3
      then F3
      else 
        match exact_log2 i with
          Some p => F2q p
        | _ => 
          match N.pos_div_eucl i (Npos (gamma i))
          with
          | (q, 0%N) => 
            (chain_gen (gen_F (gamma i))) ++
                                          (chain_gen (gen_F (N2pos q)))
          | (q,r)  => KFF (chain_gen
                             (gen_K (N2pos r)
                                    (gamma i - N2pos r)))
                          (chain_gen (gen_F (N2pos q)))
                          
          end 
        end
  | gen_K p d =>
    if pos_eq_dec p 1 then FK (chain_gen (gen_F (1 + d)))
    else
      match N.pos_div_eucl (p + d)  (Npos p) with
      | (q, 0%N) => FFK (chain_gen (gen_F p))
                          (chain_gen (gen_F (N2pos q)))
      | (q,r)  => KFK (chain_gen (gen_K (N2pos r)
                                        (p - N2pos r)))
                      (chain_gen (gen_F (N2pos q)))
      end
  end.

- intros; eapply PO1; eauto.
- intros; eapply PO2; eauto.
- intros; eapply PO3;eauto.
- intros; eapply PO4;eauto.
- intros; unfold signature_measure; subst p; lia.
- intros; eapply PO6; eauto.
- intros; unfold signature_measure; pos2nat_inj_tac; lia.
- intros; eapply PO8; eauto.
- intros; eapply PO9; eauto.
Defined.

Definition make_chain (n:positive) : code :=
 (chain_gen (gen_F n)).

(** Proof of correctness *)

Lemma chain_gen_OK : forall s:signature, OK  s (chain_gen  s).
Proof.
  intro s; functional induction chain_gen s.
  red.
  - cbn. apply F1_correct.
  - cbn; apply F3_correct.
  - cbn; rewrite (exact_log2_spec _ _ e2).
    apply F2q_correct.
  - cbn.
    generalize (N_pos_div_eucl_divides _ _ _ e3); intro eq_i.
    rewrite <- eq_i at 1; apply correct_app.
    + apply IHc.
    + apply IHc0.
  - cbn; pattern i at 1;
      replace i with (gamma i * (N2pos q) + N2pos r).
    + cbn in *. 
      *  apply KFF_correct;auto.
         replace (gamma i) with  
             (N2pos r + (gamma i - N2pos r)) at 1.
         -- apply IHc.
         -- rewrite Pplus_minus;auto with chains.
            apply Pos.lt_gt;   rewrite  N2pos_lt_switch2. 
            generalize 
           (N.pos_div_eucl_remainder i (N.pos (gamma i) )); 
           rewrite e3;  simpl;auto with chains.
            destruct r; [ contradiction | auto with chains].
    + apply  N_pos_div_eucl_rest; auto with chains.
      destruct r;try contradiction; auto with chains. 
      apply (div_gamma_pos   _ _ _ e3); auto with chains.
      apply pos_gt_3;auto with chains.
      destruct (exact_log2 i); [contradiction | reflexivity].
  - apply FK_correct, IHc. 
  - cbn in *; red; replace (p + d)%positive with (p * N2pos q)%positive.
    * apply FFK_correct; auto with chains.
    *  generalize  (N.pos_div_eucl_spec   (p + d) (N.pos p));
         rewrite e1;    rewrite N.add_0_r ; intro  H3;
           case_eq (q * N.pos p)%N.
       intro H4;  rewrite H4 in H3 ; discriminate.
       intros p0 H4; rewrite H4 in H3; injection H3;
         intro H5;   rewrite H5.
       N2pos_destruct q q.
       injection H4;auto with chains.
       rewrite  Pos.mul_comm;  auto with chains.
  - cbn; red; replace (p+d) with (p * N2pos q + N2pos r).
      + apply KFK_correct;auto with chains.
        cbn in *; replace (N2pos r + (p - N2pos r))%positive with p in IHc.
        apply IHc.  
        rewrite Pplus_minus;  auto.
        generalize  (N.pos_div_eucl_remainder (p + d) (N.pos p));
          rewrite e1; cbn;  intro H3.
        apply Pos.lt_gt;  rewrite  N2pos_lt_switch2;auto with chains.
        destruct r; [contradiction | auto with chains].

      + generalize  (N.pos_div_eucl_spec   (p + d) (N.pos p)). 
          rewrite e1; intros H3. 
          case_eq q.
          { intro; generalize (pos_div_eucl_quotient_pos _ _ _ _ e1).
           destruct 1;auto with chains.
           rewrite pos2N_inj_add;  apply N.le_add_r.
          }
          { intros p0 Hp0;subst q; cbn; destruct r; [ contradiction | ].
            simpl;  simpl in H3;  injection H3.
            rewrite Pos.mul_comm; auto with chains.
          }
Qed.



Section All_OK.
  Variables (n:positive).
  Let c := chain_gen (gen_F n).    


  Lemma L0: Fchain_correct n c.
  Proof.
    assert (H: OK (gen_F n) c) by apply chain_gen_OK.
    red;  intros;  destruct (H A op one equ M x s).
    - left.
    - now right.
  Qed.

End All_OK.

Definition AM_power {A : Type}
           `(M: @EMonoid A E_op E_one E_eq) (x:A) (n:positive) :=
  exec A E_op (chain_gen (gen_F n))  x nil.

Lemma AM_power_Ok {A : Type} 
            `(M: @EMonoid A E_op E_one E_eq) (x:A) (n:positive):
    result_equiv (AM_power M x n) (Some  (Pos_bpow x n, nil)).
Proof.
  intros;eapply L0.
Qed.


End Gamma.

Arguments chain_gen gamma {Hgamma} _.



Compute chain_gen dicho (gen_F 24).

(* begin snippet F87:: unfold *)
Compute chain_gen dicho (gen_F 87).
(* end snippet F87 *)

Compute chain_apply (chain_gen  dicho (gen_F 87)) Natplus 1%nat.

Definition F197887 := chain_gen  dicho (gen_F 197887).

Time Compute chain_apply   F197887  NPlus 1%N.

Time Compute chain_apply   F197887  NPlus 1%N.

