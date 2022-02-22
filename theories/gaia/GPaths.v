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


#[global] Notation hpath_to := path_to. 

Definition path_to (to: T1)(s: seq nat)  (from:T1) : Prop :=
  hpath_to (g2h to) s (g2h from).


