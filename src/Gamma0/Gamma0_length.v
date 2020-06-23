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


(*  Pierre Casteran 
    LaBRI, Université Bordeaux 1, and Inria Futurs (Logical)
*)
Require Import Arith.
Require Import Lia.
Require Import Compare_dec.
Require Import Relations.
Require Import Wellfounded.
Require Import Max.

Require Import More_Arith.
Require Import Restriction.
Require Import T2.

Set Implicit Arguments.
 
Section on_length.

 Open Scope nat_scope.

(* length of ordinal terms *)
(* from Schütte, Proof theory, used in proofs of transitivity
   and total ordering *)
   
Fixpoint nbterms (t:T2) : nat :=
  match t with zero => 0
             | gcons a b n v => (S n) + nbterms v
  end.

(* is the multiplication by 2 useful ? *)

Fixpoint t2_length (t:T2) : nat :=
  match t  with zero => 0
             | gcons a b n v => 
                 nbterms (gcons a b n v) + 
                  2 * (max (t2_length a) (max (t2_length b) (t2_length_aux v)))
  end
with t2_length_aux (t:T2) : nat :=
 match t with zero => 0
            | gcons a b n v =>
               max (t2_length a) (max (t2_length b) (t2_length_aux v))
 end.


Lemma length_a : forall a b n v, t2_length a < 
                                 t2_length (gcons a b n v).
Proof.
 simpl.
 intros; apply le_lt_n_Sm.
 match goal with
     [ |- ?a <= ?b + ?c + ?d] => rewrite (plus_comm (b + c) d) end.
 apply le_plus_trans.
 apply le_plus_trans.
 apply le_max_l.
Qed.

Lemma length_b : forall a b n v, t2_length b < 
                                 t2_length (gcons a b n v).
Proof.
 simpl.
 intros; apply le_lt_n_Sm.
 match goal with 
  [ |- ?a <= ?b + ?c + ?d] => rewrite (plus_comm (b + c) d) end.
 apply le_plus_trans.
 apply le_plus_trans.
 eapply le_trans.
 2:eapply le_max_r.
 apply le_max_l.
Qed.

Lemma length_c : forall a b n v, t2_length v < 
                                    t2_length (gcons a b n v).
Proof.
 simpl.
 intros; apply le_lt_n_Sm.
 case v.
 simpl.
 auto with arith.
 intros.
 simpl (t2_length (gcons t t0 n0 t1)).
 simpl (nbterms (gcons t t0 n0 t1)).
 match goal with  
  [ |- ?a <= ?b + ?c + ?d] => rewrite <- (plus_assoc b c d) end.
 simpl (t2_length_aux (gcons t t0 n0 t1)).
 match goal with [ |- ?a <= ?b + ?c ] => assert (a <= c) end.
 pattern (max (t2_length t) (max (t2_length t0) (t2_length_aux t1))).
 generalize (max (t2_length t) (max (t2_length t0) (t2_length_aux t1))).
 intro n1.
 simpl.
 apply le_n_S.
 apply plus_le_compat_l.
 repeat rewrite plus_0_r.
 apply plus_le_compat;
 apply le_trans with (max (t2_length b) n1);
 apply le_max_r.
 lia.
Qed.




Lemma length_n : forall a b r n p, n < p ->
                        t2_length (gcons a b n r) <
                        t2_length (gcons a b p r).
Proof.
 induction 1.
 simpl.
 auto with arith.
 simpl;auto with arith.
Qed.


Lemma length_psi : forall a b n c,
                      t2_length [a, b] <= t2_length (gcons a b n c).
Proof.
 simpl.
 intros; apply le_lt_n_Sm.
 match goal with 
    [ |- ?a <= ?b + ?c + ?d] => rewrite (plus_comm (b + c) d) end.
 apply le_plus_trans.
 replace (max (t2_length b) 0) with (t2_length b).
 -  repeat  rewrite plus_0_r;  apply plus_le_compat. 
   +  apply max_le_regL,  le_max_l; auto.
   +  apply Nat.max_le_compat; auto.
      apply le_max_l.
 - rewrite max_l;auto with arith.
Qed.


Lemma length_ab : forall a b, t2_length a + t2_length b <= t2_length (gcons a b 0 zero).
Proof.
 simpl.
 intros.
 repeat rewrite (max_l (t2_length b) 0);auto with arith.
 case (le_lt_dec (t2_length a) (t2_length b)).
 intro;repeat rewrite max_r;auto.
 lia.
 intro;repeat rewrite max_l;auto.
 lia.
 auto with arith.
Qed.

Lemma length_abnc : forall a b n c, 
   t2_length a + t2_length b <= t2_length (gcons a b n c).
Proof.
 intros.
 eapply Le.le_trans.
 eapply length_ab.
 apply length_psi.
Qed.


End on_length.





