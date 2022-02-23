(** Import canonical sequences from hydra-battles *)

From hydras Require Import T1.
From mathcomp Require Import all_ssreflect zify.
From hydras Require Import Canon Paths.
Require Import T1Bridge GCanon.

From gaia Require Import ssete9.
Import CantorOrdinal. 

Set Bullet Behavior "Strict Subproofs".

(** Importation of Ketonen-Solovay's  machinery into gaia's world
    (work in progress) 
*)

#[global] Notation htransition := transition.

Definition transition i (alpha beta: T1) :=
  [/\ i != 0 , alpha != zero & beta == canon alpha (S i)]. 

#[global] Notation hbounded_transition := bounded_transition.

Definition bounded_transition n (alpha beta: T1) :=
  exists i, (i <= n)%N /\ transition (S i) alpha beta.

#[global] Notation hpath_to := path_to. 

Definition path_to (to: T1)(s: seq nat) (from:T1) : Prop :=
  hpath_to (g2h to) s (g2h from).

#[global] Notation hpath := path. 

Notation path from s to :=
  (path_to to s from).

Definition acc_from alpha beta := exists s,  path alpha s beta.


#[global] Notation hpathS from s to := (path_toS to s from).

Definition pathS (from: T1)(s: seq nat) (to: T1) : Prop :=
  hpathS (g2h from) s (g2h to).


#[global] Notation hKP_arrow  := KP_arrow.

Definition KP_arrow n :=
  Relation_Operators.clos_trans_1n T1 (bounded_transition n).

#[global] Notation hconst_pathS  := const_pathS.
#[global] Notation hconst_path  := const_path.

Definition const_pathS i alpha beta  :=
  hconst_pathS i (g2h alpha) (g2h beta).



Definition const_path i alpha beta :=
   hconst_path i (g2h alpha) (g2h beta).


#[global] Notation hgnawS := gnawS.
#[global] Notation hgnaw := gnaw.

Definition gnawS alpha s := h2g (hgnawS (g2h alpha) s).
Definition gnaw alpha s := h2g (hgnaw (g2h alpha) s).

#[global] Notation hstandard_gnaw := standard_gnaw.
Definition standard_gnaw i alpha l := h2g (hstandard_gnaw i (g2h alpha) l).


Lemma iota_adapt i l: iota i l = MoreLists.iota_from i l. 
Proof.   elim: i => /= //. Qed. 


Lemma standard_gnaw_iota_from i alpha l :
  i <> 0 -> standard_gnaw i alpha l = gnaw alpha (iota i l).
  Proof. 
   move: l i alpha ; elim => // /=. 
   rewrite !/standard_gnaw => n Hn i alpha Hi.
   specialize (Hn (S i) (canon alpha i)); rewrite /canon g2h_h2gK in Hn.
    rewrite Hn /gnaw ?g2h_h2gK => // /=.  
    move: Hi Hn; case :i => //.  
  Qed. 
 


(** * Examples *)

Example ex_path1 : path (T1omega * (\F 2)) [:: 2; 2; 2] T1omega.
Proof. rewrite /path_to;  path_tac. Qed.

Example ex_path2: path (T1omega * \F 2) [:: 3; 4; 5; 6] T1omega.
Proof. rewrite /path_to;  path_tac. Qed.

Example ex_path3: path (T1omega * \F 2) (index_iota 3 15) zero.
Proof. rewrite /path_to /index_iota => /=.  path_tac. Qed.

Example ex_path4: path (T1omega * \F 2) (List.repeat 3 8) zero.
Proof. rewrite /path_to => /=. path_tac. Qed.

Example ex_path5: pathS (T1omega * \F 2) (List.repeat 2 8) zero.
Proof. rewrite /pathS path_toS_path_to => /=; path_tac. Qed.

(* 
Compute ppT1 (gnaw (phi0 T1omega) [:: 2; 3; 4; 5]).

Compute ppT1 (gnaw (phi0 T1omega) (index_iota 2 10)).

Compute ppT1 (gnaw (phi0 T1omega) (index_iota 2 19)).

Compute ppT1 (gnaw (phi0 T1omega) (index_iota 2 38)).

Compute ppT1 (gnawS (phi0 T1omega) (index_iota 1 37)).

Compute ppT1 (standard_gnaw  2 (phi0 T1omega * \F 2) 22).

Compute ppT1 (standard_gnaw  2 (phi0 T1omega * \F 2) 37).

Compute ppT1 (standard_gnaw  2 (phi0 T1omega * \F 2) 75).
 
*)


Lemma gLemma2_6_1 (alpha:T1) :
T1nf alpha ->
  forall beta, T1nf beta -> 
    T1lt beta  alpha  ->
    {n:nat | const_pathS n alpha beta}.
Proof.
  rewrite -hnf_g2h => Hnf beta Hbeta Hlt.
  have H: hnf (g2h beta) by rewrite hnf_g2h. 
  have H'lt : g2h beta t1< g2h alpha; repeat split => //.
  rewrite T1lt_iff in Hlt => //.
  case: Hlt => ? [? ?] //.  
  by rewrite -hnf_g2h. 
  case (Lemma2_6_1 Hnf H'lt) => x Hx; exists x. 
  by rewrite /const_pathS. 
Qed. 
