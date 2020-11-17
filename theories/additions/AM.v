(** Abstract machine for following an addition chain *)
(** adapted from the old contrib coq-additions *)


Require Import Monoid_def Monoid_instances List PArith.
Require Import Strategies Lia.

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
 
End Semantics.


Definition chain_apply c {A:Type}{op:A->A->A}{one:A}{equiv: Equiv A}
           (M: EMonoid op one equiv) x := exec _ op c x nil.


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


(** Chain generation 

    To do: share some stuff with Euclidean.v *)

Require Import Recdef Wf_nat.
Require Import More_on_positive.

Section Gamma.

Variable gamma: positive -> positive.
Context (Hgamma : Strategy gamma).

Inductive signature : Type :=
| gen_F (n:positive) (** Fchain for the exponent n *)
| gen_K (p d: positive) (** Kchain for the exponents p+d  and p *) . 


Definition signature_measure (s : signature) : nat :=
match s with
  | gen_F n => 2 * Pos.to_nat n 
  | gen_K  p d => 2 * Pos.to_nat (p + d) +1
end.


(** Unifying  statements about chain generation *)

Definition signature_exponent (s:signature) : positive :=
 match s with 
| gen_F n => n 
| gen_K p d  =>  p + d
end.

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

