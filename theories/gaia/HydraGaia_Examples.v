From mathcomp Require Import all_ssreflect zify.

From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder ON_Generic.
From hydras Require Import T1 E0 Hessenberg.
From gaia Require Export ssete9.

Require Import T1Bridge GCanon GHessenberg GLarge_Sets. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* begin snippet Demoa *)
Check \F 42.

Fail Check (42 : T1).
(* end snippet Demoa *)

(* begin snippet Demob *)
Compute (T1limit T1omega, T1is_succ (omega_tower 2), T1is_succ (\F 42)).
(* end snippet Demob *)

(* begin snippet ExamplesG2H *)
Example α : T1 :=
 T1omega +  phi0 T1omega * \F 3 + phi0 (\F 5) * \F 4 + T1omega * T1omega.

Example β : T1 :=  phi0 (phi0 (\F 2)).

Compute g2h α.

Compute α == h2g (g2h α). 
(* end snippet ExamplesG2H *)

(* begin snippet T1pp *)
Compute  β + α. 

Compute T1pp (β + α).
(* end snippet T1pp *)




Compute compare α β.

(** Hessenberg's sum *)

Print oplus. 

Compute T1pp (\F 5 + T1omega). 

Compute T1pp (\F 5 o+ T1omega).

Search (_ o+ ?x < _ o+ ?x).

Search (?x < ?x  o+ _)%ca. 

Search oplus.

Search Hessenberg.oplus hlt.




(** Canonical sequences *)

