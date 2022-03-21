
(** Gaia-compatible [H'_ alpha] fast growing functions  

(imported from [hydras.Epsilon0.Hprime] )
*)


(* begin snippet Requirements:: no-out  *)
From mathcomp Require Import all_ssreflect zify.
From gaia Require Export ssete9.
From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder.
From hydras Require Import T1 E0.
From hydras Require Paths.
From hydras Require Import primRec PrimRecExamples. 
From hydras Require Import  Hprime.
From gaia_hydras Require Import T1Bridge GCanon GPaths.
(* end snippet Requirements *)

Set Implicit Arguments.
Unset Strict Implicit.

Notation hH'_ := Hprime.H'_. 

Definition H'_ alpha i := hH'_ (E0_g2h alpha) i. 




