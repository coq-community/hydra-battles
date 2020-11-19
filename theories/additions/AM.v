(** Abstract machine for following an Euclidean addition chain *)
(** adapted from the old contrib coq-additions *)

(** Work in progress 

Clean the import issues !!! 
*)

Require Import Monoid_def Monoid_instances List PArith Relations.
Require Import Strategies Lia.
Generalizable All Variables.
Import Morphisms.
Import Monoid_def.
Require Import Recdef Wf_nat.
Require Import More_on_positive.
Require  Pow.
(** basic instructions *)

Inductive instr : Set :=
  | MUL : instr
  | SQR : instr
  | PUSH : instr
  | SWAP : instr.       

Definition code := list instr.

(* semantics *)
(*************)

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
 
(** Main well-formed chains *)
Definition M1 : code := nil.

(** raises x to its cube *)

Definition M3 := PUSH::SQR::MUL::nil.

(** chain for raising x to its (2 ^ q)th power *)

Fixpoint M2q_of_nat q := match q with
                  | 0%nat => nil
                  | S p => SQR:: M2q_of_nat  p
                  end.

Definition M2q (p:positive) :=
  M2q_of_nat (Pos.to_nat p). 

(** for computing x^(pq+r) passing by  x^p *)

Definition KMC (kpr mq:code) : code := 
  kpr++(mq++MUL::nil).

(** for computing x^p and x^(pq) *)

Definition MMK (mp mq: code) := mp ++ PUSH :: mq. 

(** for computing x^p then x^(pq + r)  *)

Definition KMK (kpr mq: code) :=
  kpr ++ PUSH::SWAP :: (mq ++ MUL :: nil). 

Definition FK (fn: code) := PUSH::fn. 

End Semantics.


Definition chain_apply c {A:Type}{op:A->A->A}{one:A}{equ: Equiv A}
           (M: EMonoid op one equ) x := exec _ op c x nil.


(** Example code for 7 via 3 *)
Example  M7_3 := PUSH::PUSH::SQR::MUL::PUSH::SQR::SWAP::MUL::nil.

Compute chain_apply  M7_3   Natplus 1%nat .

(** Example code for 31 via 7 *)
Example C31_7 := KMC M7_3 (M2q 2).

Compute chain_apply C31_7 Natplus 1%nat.
(*
     = Some (31, nil)
     : option (config nat)
 *)

Require Import NArith.

Compute chain_apply C31_7 NMult 2%N.


Compute chain_apply (MMK M3 (M2q 3)) Natplus %nat. (** 24, 3 *)

(** For 99 and 24 *)
Example K99_24 := KMK (MMK M3 (M2q 3)) (M2q 2).
Compute K99_24.

Compute chain_apply (KMK (MMK M3 (M2q 3)) (M2q 2)) Natplus 1%nat.


(** Specification and generation of correct chains *)
(** Should be shared with Euclidean.v *)

Inductive signature : Type :=
| gen_F (n:positive) (** Fchain for the exponent n *)
| gen_K (p d: positive) (** Kchain for the exponents p+d  and p *) . 

(** Termination measure *)

Definition signature_measure (s : signature) : nat :=
match s with
  | gen_F n => 2 * Pos.to_nat n 
  | gen_K  p d => 2 * Pos.to_nat (p + d) +1
end.


Definition signature_exponent (s:signature) : positive :=
 match s with 
| gen_F n => n 
| gen_K p d  =>  p + d
 end.


(** We have to buid equivalences between configurations *)

Inductive stack_equiv {A}`{M : @EMonoid A op one equ}:
  list A -> list A -> Prop
  :=
  stack_equiv0 : stack_equiv  nil nil
| stack_equivn: forall x y s s',  x == y -> stack_equiv s s' ->
                                  stack_equiv (x::s) (y:: s').



Definition config_equiv  {A}`{M : @EMonoid A op one equ}
           (x :A)(s:stack A)(y:A)(s':stack A) :=
  x == y /\ stack_equiv s s'.



Inductive result_equiv {A}`{M : @EMonoid A op one equ}: relation (option (config A)):= 
  result_equiv_fail : result_equiv None None
| result_equiv_success : forall x s y s',
    config_equiv  x s y s' ->
    result_equiv (Some (x,s)) (Some (y,s')).


Inductive  chain_correct : signature ->  code -> Prop :=
  ccF : forall p c,
    (forall A `{M: @EMonoid A op one equ} (x:A) s,
        result_equiv (M:=M) (exec A op c x s)
                     (Some (Pow.Pos_bpow x p, s))) ->
    chain_correct (gen_F p) c

| ccK : forall p d c,
    (forall  `{M: @EMonoid A op one equ} (x:A) s,
        result_equiv (exec A op c x s)
                     (Some (Pow.Pos_bpow  x (p+d), Pow.Pos_bpow  x p ::s))) ->
    chain_correct (gen_K p d) c.



Instance Stack_equiv_refl {A}`{M : @EMonoid A op one equ} :
  Reflexive stack_equiv.
Proof.
  red; intros. induction x.
  - now left.
  - right; [reflexivity | assumption].
Qed.

Instance Stack_equiv_equiv {A}`{M : @EMonoid A op one equ}:
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

Instance result_equiv_equiv `{M : @EMonoid A op one equ}:
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
  forall c x s y s' , config_equiv x s y s' ->
                      result_equiv (exec A op c x s) (exec A op c y s').
Proof.
  induction c.
  - simpl; now constructor.
  -  destruct a.
     + destruct s.
       * inversion 1; inversion H1; subst;simpl; constructor.
       *  inversion 1; inversion H1; subst;  simpl; apply IHc.
          constructor; trivial.
          now apply Eop_proper.
     +  intros;simpl; apply IHc.
        destruct H; split; auto.
        apply Eop_proper; auto.
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



Lemma M3_correct : chain_correct (gen_F 3) M3.
Proof.
  constructor.
  intros.
  simpl.
  constructor.
  simpl.
  split.
  generalize (Eop_assoc (EMonoid:=M)).
  intro.
   rewrite H.
  reflexivity.
  apply Stack_equiv_refl.
Qed.

Import Pow.


Lemma L: forall `{M : @EMonoid A op one equ} (n:nat) x s,
    result_equiv (exec A op (M2q_of_nat n) x s)
                 (Some(power x (2 ^ n), s)).
  induction n.
  simpl.
  intros; f_equal.
  right.
  split.
  destruct M.
  rewrite Eone_right.
  reflexivity.
  reflexivity.

  intro x.
  simpl.
  intro s; rewrite IHn.
  right.
  split;auto.
  replace (2 ^ n + (2 ^ n + 0))%nat with (2 * ( 2 ^n) )%nat.
  fold mult_op.
  assert (x * x == x ^2).
  now rewrite  sqr_def.
  transitivity ((x ^ 2) ^2 ^n).
  apply power_proper.
  auto.
  auto.
  rewrite <- power_of_power.
  rewrite power_of_power_comm.
  reflexivity.
  lia.
  reflexivity.

Qed.


Lemma L' (n:nat)  : chain_correct (gen_F (Pos.of_nat (2 ^ n))) (M2q_of_nat n). 
  left.
  intros. rewrite L.
  right.
  split.
  rewrite Pos_bpow_ok_R.
  reflexivity.
  apply Nat.pow_nonzero.
  discriminate.
  reflexivity.
Qed.

Lemma  L'' (n:positive)  : chain_correct (gen_F  (2 ^ n)) (M2q n). 

  unfold M2q.
  replace (2 ^n)%positive with (Pos.of_nat (2 ^ Pos.to_nat n)%nat).
  apply L'.
  rewrite   Compatibility.Pos_pow_power.
  rewrite <- Pos_bpow_ok_R.
  rewrite Pos_bpow_ok.
  rewrite Nat2Pos.id.

  generalize (Pos.to_nat n).
  intros. rewrite Compatibility.nat_power_ok.
  simpl. induction n0; simpl; auto.
  simpl. 
  rewrite  Nat2Pos.inj_mul.
  rewrite IHn0.
  simpl (Pos.of_nat 2).
  f_equal.
  unfold mult_op.
  unfold P_mult_op.
  f_equal.
  discriminate.
  clear IHn0.
  induction n0;simpl.
  discriminate.
  remember (2%nat ^ n0) as n1.
  simpl.  
  unfold mult_op.
  unfold Demo.nat_mult_op.
  lia.

  assert (H:= Pos2Nat.is_pos n).
  lia.
  assert (H:= Pos2Nat.is_pos n).
  lia.
Qed.


(** TO do :
    Corrections of composition (append), M2q, MMK, etc . *)

(** *  Euclidean chain generation 

    To do: share some stuff with Euclidean.v *)


Section Gamma.

Variable gamma: positive -> positive.
Context (Hgamma : Strategy gamma).


Function chain_gen  (s:signature) {measure signature_measure}
  :  code :=
  match s with
    gen_F i =>
    if pos_eq_dec i 1 then M1 else
      if pos_eq_dec i 3
      then M3
      else 
        match exact_log2 i with
          Some p => M2q p
        | _ => 
          match N.pos_div_eucl i (Npos (gamma i))
          with
          | (q, 0%N) => 
            (chain_gen (gen_F (gamma i))) ++
                                          (chain_gen (gen_F (N2pos q)))
          | (q,r)  => KMC (chain_gen
                             (gen_K (N2pos r)
                                    (gamma i - N2pos r)))
                          (chain_gen (gen_F (N2pos q)))
                          
          end 
        end
  | gen_K p d =>
    if pos_eq_dec p 1 then FK (chain_gen (gen_F (1 + d)))
    else
      match N.pos_div_eucl (p + d)  (Npos p) with
      | (q, 0%N) => MMK   (chain_gen (gen_F p))
                          (chain_gen (gen_F (N2pos q)))
      | (q,r)  => KMK (chain_gen (gen_K (N2pos r)
                                        (p - N2pos r)))
                      (chain_gen (gen_F (N2pos q)))
      end
  end.

(** Same script as in Euclidean.v ???? *)

- intros. unfold signature_measure.
  generalize (N.pos_div_eucl_spec i (N.pos (gamma i)));
    rewrite teq3; N2pos_destruct q p.
  subst r; repeat rewrite  N.add_0_r.
  injection 1.  intro H0; rewrite H0.
  gamma_bounds gamma i H12 H14.
  assert (H13 : p <> 1).
  
  +  intro Hp ; subst p; simpl in H0.
     destruct (Pos.lt_irrefl i).
     now rewrite H0 at 1.

  +  assert (H11 := pos_lt_mul p (gamma i) H12).
     rewrite Pos2Nat.inj_lt in  H11.
     rewrite  Pos2Nat.inj_mul in *;  lia.
- intros; unfold signature_measure.
  apply Coq.Arith.Mult.mult_lt_compat_l ;
    [ apply Pos2Nat.inj_lt; apply gamma_lt|] ;  auto with chains.
- intros; unfold signature_measure.
  gamma_bounds gamma i H12 H14; quotient_small teq3 H.
  apply Coq.Arith.Mult.mult_lt_compat_l; [ | auto with arith chains].
  apply Pos2Nat.inj_lt.
  destruct q; simpl in *.
  transitivity (gamma i);auto.
  now rewrite pos2N_inj_lt.
-  intros; unfold signature_measure.
   apply lt_S_2i;  rewrite Pplus_minus. 
   gamma_bounds gamma i H5 H6.
   +  apply Pos2Nat.inj_lt;  auto.
   +  rest_small teq3 H; now  apply Pos.lt_gt.
- intros; unfold signature_measure;
    subst p;  lia.
- intros; unfold signature_measure.
  quotient_small teq1 H.
  destruct p; (discriminate || reflexivity).
  N2pos_destruct q q.
  +       destruct (pos_div_eucl_quotient_pos _ _ _ _ teq1);auto with chains.
          rewrite pos2N_inj_add; apply N.le_add_r.
  +  simpl; rewrite <- pos2N_inj_lt in H;
       rewrite Pos2Nat.inj_lt in H.
     lia.
- intros; unfold signature_measure; pos2nat_inj_tac; lia.

- intros; unfold signature_measure.
  assert (N2pos q < p+d)%positive.
  quotient_small teq1 H.
  generalize anonymous; 
    destruct p; simpl; try reflexivity.
  now destruct 1.
  generalize (pos_div_eucl_quotient_pos  _ _ _ _ teq1).
  intros H0;  destruct q;auto.
  destruct H0;auto with chains.
  rewrite pos2N_inj_add;  apply N.le_add_r;auto with chains.
  + revert H; pos2nat_inj_tac; intros;lia.
- intros; unfold signature_measure. 
  apply Coq.Arith.PeanoNat.Nat.add_lt_mono_r;
    apply Arith.Mult.mult_S_lt_compat_l;auto with chains.
  rewrite Pplus_minus.
  +  apply Pos2Nat.inj_lt; apply Pos.lt_add_diag_r; cbn.
  +  generalize (N.pos_div_eucl_remainder (p + d) (N.pos p) );
       rewrite teq1; cbn; unfold N.lt ; intro H; red.
     simpl in H; now rewrite Pos.compare_antisym, H.
Defined.




End Gamma.

Arguments chain_gen gamma {Hgamma} _.
Require Import Dichotomy.


Compute chain_gen dicho (gen_F 24) .
Compute chain_gen  dicho  (gen_F 87) .

Compute chain_apply (chain_gen  dicho (gen_F 87)) Natplus 1%nat.

Definition M197887 := chain_gen  dicho (gen_F 197887).

Time Compute chain_apply   M197887  NPlus 1%N.

Time Compute chain_apply   M197887  NPlus 1%N.

