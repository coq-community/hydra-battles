(**  * Bridge between Hydra-battle's and Gaia's [T1]  (Experimental) 
 *)

(* begin snippet Requirements:: no-out  *)
From mathcomp Require Import all_ssreflect zify.
From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder ON_Generic  T2 Gamma0.

From gaia Require Export ssete9.
Import Gamma0. 
(* end snippet Requirements *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

(* begin snippet hT2gT2 *)

(** Hydra-Battles' type for ordinal terms below [Gamma00] *)
Check Gamma0.T2.T2. 
Print Gamma0.T2.T2.
#[global] Notation hT2 := hydras.Gamma0.T2.T2.

(** Gaia's type for ordinal terms below [epsilon0] *)
#[global] Notation T2 := ssete9.Gamma0.T2.
(* end snippet hT2gT2 *)


#[global] Notation hcons := gcons. 
#[global] Notation hzero := hydras.Gamma0.T2.zero. 

(*
#[global] Notation zero := Gamma0.zero. 
#[global] Notation cons := Gamma0.cons. 
*)
Fixpoint h2g (alpha : hT2) : T2 :=
  match alpha with
    hzero => zero
  | hcons a b n c => cons (h2g a) (h2g b) n (h2g c)
  end.

Fixpoint g2h (alpha : T2) : hT2 :=
  match alpha with
    zero => hzero
  | cons a b n c => hcons (g2h a)(g2h b)  n (g2h c)
  end.


Lemma h2g_g2hK : cancel g2h h2g.
Proof. elim => // => t Ht t0 Ht0 n t1 Ht1 /=; by rewrite Ht Ht0 Ht1.  Qed.

Lemma g2h_h2gK : cancel h2g g2h.
Proof. elim => // => t Ht t0 Ht0 n t1 Ht1 /=; by rewrite Ht Ht0 Ht1.  Qed.


Lemma g2h_eq_iff (a b: T2) :  g2h a = g2h b <-> a = b.
Proof. 
    split . 
    - rewrite -(h2g_g2hK a) -(h2g_g2hK b) !g2h_h2gK
              => // -> //.  
    - by move => -> .
Qed. 


Lemma h2g_eq_iff (a b :hT2) :  h2g a = h2g b <-> a = b.
Proof. 
  split.
    -  rewrite  -(g2h_h2gK a) -(g2h_h2gK b) !h2g_g2hK  =>  // -> //.
    - move => -> //. 
Qed.

(* TODO 
  Prove the equivalence of comparison and test for normal form in both 
  libraries: import well-foundedness *)


Check (fun a b : hT2 => compare a b).

About T2lt.

