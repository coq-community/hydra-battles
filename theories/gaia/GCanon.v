From hydras Require Import T1.
From mathcomp Require Import all_ssreflect zify.
Require Import T1Bridge.
Import ssete9.CantorOrdinal. 

From gaia Require Import ssete9.
Import ssete9.CantorOrdinal. 
Set Bullet Behavior "Strict Subproofs".

From hydras Require Import Canon.

#[global] Notation hcanon := canon. 

Definition gcanon (a: gT1) (i:nat) : gT1 :=
  iota (hcanon (pi a) i).



Compute gcanon (g_phi0 T1omega) 6 == (g_phi0 (\F 6))%brg.





