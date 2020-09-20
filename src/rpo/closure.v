(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* by Evelyne Contejean *)


(* Note by Pierre :
  May be already in standard library ?
 *)

Set Implicit Arguments. 

From  Coq Require Import Relations.

Inductive trans_clos (A : Set) (R : relation A) : relation A:=
  | t_step : forall x y, R x y -> trans_clos R x y
  | t_trans : forall x y z, R x y -> trans_clos R y z -> trans_clos R x z.

Lemma trans_clos_is_trans :
  forall (A :Set) (R : relation A) a b c, 
  trans_clos R a b -> trans_clos R b c -> trans_clos R a c.
Proof.
  intros A R a b c Hab; generalize c;
  clear c; induction Hab as [a b Hab | a b c Hab Hbc].
  intros c Hbc; apply t_trans with b; trivial.
  intros d Hcd; apply t_trans with b; trivial.
  apply IHHbc; trivial.
Qed.

Lemma acc_trans :
 forall (A : Set) (R : relation A) a, Acc R a -> Acc (trans_clos R) a.
Proof.
  intros A R a Acc_R_a.
  induction Acc_R_a as [a Acc_R_a IH].
  apply Acc_intro.
  intros b b_Rp_a; induction b_Rp_a.
  apply IH; trivial.
  apply Acc_inv with y.
  apply IHb_Rp_a; trivial.
  apply t_step; trivial.
Qed.

Lemma wf_trans :
  forall (A : Set) (R : relation A) , well_founded R ->
                                      well_founded (trans_clos R).
Proof.
  unfold well_founded; intros A R WR.
  intro; apply acc_trans; apply WR; trivial.
Qed.

Lemma inv_trans :
  forall (A : Set) (R : relation A) (P : A -> Prop),
  (forall a b, P a -> R a b -> P b) -> 
  forall a b, P a -> trans_clos R a b -> P b.
Proof.
   intros A R P Inv a b Pa a_Rp_b; induction a_Rp_b.
   apply Inv with x; trivial.
   apply IHa_Rp_b; apply Inv with x; trivial.
Qed.

