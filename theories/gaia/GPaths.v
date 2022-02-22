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


#[global] Notation hgnawS := gnawS.
#[global] Notation hgnaw := gnaw.

Definition gnawS alpha s := h2g (hgnawS (g2h alpha) s).
Definition gnaw alpha s := h2g (hgnaw (g2h alpha) s).


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
Proof.
  rewrite /pathS path_toS_path_to => /=; path_tac.
Qed.

Compute ppT1 (gnaw (phi0 T1omega) [:: 2; 3; 4; 5]).

Compute ppT1 (gnaw (phi0 T1omega) (index_iota 2 10)).

Compute ppT1 (gnaw (phi0 T1omega) (index_iota 2 19)).

Compute ppT1 (gnaw (phi0 T1omega) (index_iota 2 38)).

Compute ppT1 (gnawS (phi0 T1omega) (index_iota 1 37)).











