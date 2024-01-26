(** Pierre Castéran, University of Bordeaux and LaBRI *)



From Coq Require Import   Arith Lia.
From hydras Require Import Hydra_Lemmas ON_Generic ON_Omega.
Open Scope nat_scope.

#[global] Instance height_var : Hvariant Omega free height.
Proof.
  split;intros.
(*
  1 focused subgoal

  i : nat
  h, h' : Hydra
  H : reachable free i h
  H0 : h <> head
  H1 : free i h h'
  ============================
  height h' < height h


 *)
(* begin show *)
Abort.
(* end show *)

Lemma height_bad :  ~ Hvariant Omega free height.
Proof.
  intros [H];
  specialize (H 1 (hyd1 (hyd2 head head))  (hyd1 (hyd1 head)));
     apply (Nat.lt_irrefl 2), H.

  -  discriminate.
  -  exists 0; right; repeat constructor. 
Qed.



(** There is no measure into omega for proving termination
of all hydra battles *)

(* begin snippet omegaSmalla *)

Section Impossibility_Proof.

  (** Let us assume there exists a variant from Hydra  into nat 
      for proving the termination of all hydra battles 
      [Omega] is an ordinal notation for the least infinite ordinal
      [omega], whose members are the natural numbers.
*)
 
  Variable m : Hydra -> nat.
  Context (Hvar : Hvariant Omega free m).
  
(* end snippet omegaSmalla *)
  
(* begin snippet iotaDef *)
  
  Let iota (i: nat) := hyd_mult head (S i).

(* end snippet iotaDef *)

(* begin snippet bigHDef *)
  
  Let big_h := hyd1 (hyd1 head).

(* end snippet bigHDef *)  

(* begin snippet smallHDef *)
  
  Let small_h := iota (m big_h).
  
  Fact big_to_small: forall i,  battle_rel free i big_h small_h. (* .no-out *)
  (*|
.. coq:: no-out 
|*)
  Proof.
    exists (m big_h); right;  repeat constructor.     
  Qed.

(* end snippet smallHDef *)

  #[local] Hint Resolve big_to_small : hydra.


  (* begin snippet mLt *)
  
  (*|
.. coq:: no-out 
|*)
  
  Lemma m_lt : m small_h < m big_h.
  Proof.
    apply (variant_decr  0); auto with hydra.
    discriminate.
  Qed.

  (*||*)
  
  (* end snippet mLt *)
  
  (**  In order to find a contradiction, we  prove the inequality
       m big_h <= m small_h, i.e.  m big_h <= m (iota (m h)) 
      
       For that purpose, we prove the inequality i <= m (iota i) for any i 
   *)
  
  Lemma round_S: forall i n, battle_rel free n (iota (S i)) (iota i).
  Proof.
    intros i n; exists 0; constructor 1; constructor;  induction i.
    - right;left.
    - cbn;  constructor 2; trivial.
  Qed.


  (* begin snippet mGea:: no-out  *)
  Lemma m_ge : m big_h <= m small_h. 
  (* end snippet mGea *)
  Proof. 
    unfold small_h; generalize (m big_h) as i.
  (* begin snippet mGeb:: no-out *)
    induction i.
    - auto with arith.
    - apply Nat.le_lt_trans with (m (iota i)). 
      (* ... *) 
     (* end snippet mGeb *)  
       + assumption.
       + apply (variant_decr  0).
          * discriminate.
          * cbn; apply round_S; exact 0.
 (* begin snippet mGez:: no-out  *)
  Qed.     
  (* end snippet mGez *)
  
(* begin snippet omegaSmallz:: no-out *)
  Theorem Contradiction : False. 
  Proof. generalize m_lt, m_ge; intros; lia. Qed. 

End Impossibility_Proof.
(* end snippet omegaSmallz *)



