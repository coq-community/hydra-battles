
(** Gaia-compatible [L_ alpha] fast growing functions  

(imported from [hydras.Epsilon0.Hprime] )
*)


(* begin snippet Requirements:: no-out  *)
From mathcomp Require Import all_ssreflect zify.
From gaia Require Export ssete9.
From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder.
From hydras Require Import T1 E0.
From hydras Require Paths L_alpha.
From hydras Require Import primRec PrimRecExamples. 
From hydras Require Import  L_alpha.
From gaia_hydras Require Import T1Bridge GCanon GPaths.
(* end snippet Requirements *)

Set Implicit Arguments.
Unset Strict Implicit.

Locate L_.

