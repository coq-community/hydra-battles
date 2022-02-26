From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder ON_Generic.
From hydras Require Import T1 E0 Hessenberg.
From mathcomp Require Import all_ssreflect zify.
From gaia Require Export ssete9.
Set Bullet Behavior "Strict Subproofs".

Require Import T1Bridge GCanon GHessenberg GLarge_Sets. 
Set Implicit Arguments.
Unset Strict Implicit.


Example α : T1 :=
 T1omega +  phi0 T1omega * \F 3 + phi0 (\F 5) * \F 4 + T1omega * T1omega.

Example β : T1 :=  phi0 (phi0 (\F 2)).

Compute g2h β. 

Compute g2h α.


(** pretty printing *)

Compute ppT1 α. 

Compute compare α β.

(** Hessenberg's sum *)

Print oplus. 

Compute ppT1 (\F 5 + T1omega). 

Compute ppT1 (\F 5 o+ T1omega).

Search (_ o+ ?x < _ o+ ?x).

Search (?x < ?x  o+ _)%ca. 

Search oplus.

Search Hessenberg.oplus hlt.

(** Canonical sequences *)

