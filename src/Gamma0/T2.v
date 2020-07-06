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


(**  Pierre Casteran 
    LaBRI, Université Bordeaux 1, and Inria Futurs (Logical)
*)

(** Data-type for Veblen normal form 
   (ordinals below Gamma0)   *)


Require Import Arith. 
Require Import Compare_dec.
Require Import Relations.
Require Import Wellfounded.
Require Import Max Lia.

Require Import More_Arith.
Require Import Restriction.
Require Import not_decreasing.
Require Import T1.

Set Implicit Arguments.


(************************)
(*   Definitions        *)
(************************)


(* cons a b n r is : psi(a,b)*(S n)+ r  *)

Inductive T2 : Set :=
  zero : T2
| gcons : T2 -> T2  -> nat -> T2 -> T2.

Declare Scope g0_scope.

Notation "[ x , y ]" := (gcons x y 0 zero) (at level 0): g0_scope.

Open Scope g0_scope.

Definition psi alpha beta  := [alpha, beta].

Definition psi_term alpha :=
  match alpha with zero => zero
                 | gcons a b n c => [a, b]
  end.

Notation  "'one'"  := [zero,zero] : g0_scope.


Lemma psi_eq : forall a b, psi a b = [a,b].
Proof.
 trivial.
Qed.

Ltac fold_psi :=  rewrite <- psi_eq.
Ltac fold_psis := repeat fold_psi.


Definition finite  p := match p with 
                             0 => zero
                           | S q => gcons zero zero q zero
                           end.

Notation "'F' n" := (finite n)(at level 29) : g0_scope.

Inductive is_finite:  T2 ->  Set := 
 zero_finite : is_finite zero
|succ_finite : forall n, is_finite (gcons zero zero n zero).

Hint Constructors is_finite : T2.

Notation "'omega'"  := [zero,one] : g0_scope.

Definition epsilon0  := [one,zero].

Definition epsilon alpha := [one, alpha].


(* injection from Cantor Normal Form *)

Fixpoint T1_inj (alpha :T1) : T2 :=
  match alpha  with
            | T1.zero => zero
            | T1.ocons a n b => gcons zero (T1_inj a) n (T1_inj b)
 end.



(* additive principals *)


Inductive ap : T2 -> Prop :=
ap_intro : forall alpha beta, ap [alpha, beta].

(* strict order on terms *)

(* Note : try to use psi as often as possible in the constructors
  premises *)

Inductive lt : T2 -> T2 -> Prop :=
| (* 1 *) 
 lt_1 : forall alpha beta n gamma,  zero < gcons alpha beta n gamma
| (* 2 *)
 lt_2 : forall alpha1 alpha2 beta1 beta2 n1 n2 gamma1 gamma2, 
                alpha1 < alpha2 ->
                beta1 < gcons alpha2 beta2 0 zero ->
               gcons alpha1 beta1 n1 gamma1 <
               gcons alpha2 beta2 n2 gamma2
| (* 3 *)
 lt_3 : forall alpha1  beta1 beta2 n1 n2 gamma1 gamma2, 
               beta1 < beta2 ->
               gcons alpha1 beta1 n1 gamma1 <
               gcons alpha1 beta2 n2 gamma2

| (* 4 *)
 lt_4 : forall alpha1 alpha2 beta1 beta2 n1 n2 gamma1 gamma2, 
               alpha2 < alpha1 ->
               gcons alpha1 beta1 0 zero < beta2 ->
               gcons alpha1 beta1 n1 gamma1 <
               gcons alpha2 beta2 n2 gamma2

| (* 5 *)
lt_5 : forall alpha1 alpha2 beta1 n1 n2 gamma1 gamma2, 
               alpha2 < alpha1 ->
               gcons alpha1 beta1 n1 gamma1 <
               gcons alpha2  (gcons alpha1 beta1 0 zero) n2 gamma2

| (* 6 *)
lt_6 : forall alpha1 beta1  n1  n2 gamma1 gamma2,  (n1 < n2)%nat ->
                                    gcons alpha1 beta1 n1 gamma1 < 
                                    gcons alpha1 beta1 n2 gamma2

| (* 7 *)
  lt_7 : forall alpha1 beta1 n1   gamma1 gamma2,  gamma1 < gamma2 ->
                                      gcons alpha1 beta1 n1 gamma1 <
                                      gcons alpha1 beta1 n1 gamma2
where  "o1 < o2" := (lt o1 o2): g0_scope.
Hint Constructors lt : T2.





Definition le t t' := t = t' \/ t < t'.
Hint Unfold le : T2.

Notation "o1 <= o2" := (le o1 o2): g0_scope.

Definition tail c := match c with | zero => zero 
                                  | gcons a b n c => c
                             end.
(* Veblen Normal Form *)

Inductive nf : T2 -> Prop :=
| zero_nf : nf zero
| single_nf : forall a b n, nf a ->  nf b -> nf (gcons a b n zero)
| gcons_nf : forall a b n a' b' n' c', 
                             [a', b'] < [a, b]  -> 
                             nf a -> nf b -> 
                             nf(gcons a' b' n' c')-> 
                             nf(gcons a b n (gcons a' b' n' c')).
Hint  Constructors nf : T2. 


Inductive is_successor : T2 -> Prop :=
  finite_succ : forall  n  , is_successor (gcons zero zero n zero)
 |cons_succ : forall a b n c, nf (gcons a b n c) -> is_successor c ->
                              is_successor (gcons  a b n c).




Inductive is_limit : T2 -> Prop :=
|is_limit_0 : forall alpha beta n, zero < alpha \/ zero < beta ->
                                   nf alpha -> nf beta ->
                                   is_limit (gcons alpha beta n zero)
| is_limit_cons : forall alpha  beta n gamma,
    is_limit gamma ->
    nf (gcons alpha beta n gamma) ->
    is_limit (gcons alpha beta n gamma).



Fixpoint succ (a:T2) : T2 :=
 match a with zero => finite 1
             | gcons zero zero n c => finite (S (S n))
             | gcons a b n c => gcons a b n (succ c)
 end.


Fixpoint pred  (a:T2) : option T2 :=
 match a  with zero => None
             | gcons zero zero 0 zero => Some zero
             | gcons zero zero (S n) zero => 
                  Some (gcons zero zero n zero)
             | gcons a b n c => (match (pred c) with
                                   Some c' => Some (gcons a b n c')
                                  | None => None
                                  end)
 end.

Inductive lt_epsilon0 : T2 -> Prop :=
  zero_lt_e0 : lt_epsilon0 zero 
| gcons_lt_e0 : forall  b n c,   lt_epsilon0 b ->
                                lt_epsilon0 c -> 
                                lt_epsilon0 (gcons zero b n c).


(* end of main definitions *)


(** * length (as in Schutte) *)



 
(*
Require Import Arith.
Require Import Lia.
Require Import Compare_dec.
Require Import Relations.
Require Import Wellfounded.


Require Import More_Arith.
Require Import Restriction.
Require Import T2.

Set Implicit Arguments.
 *)

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
                  2 * (Max.max (t2_length a) (Max.max (t2_length b) (t2_length_aux v)))
  end
with t2_length_aux (t:T2) : nat :=
 match t with zero => 0
            | gcons a b n v =>
               Max.max (t2_length a) (Max.max (t2_length b) (t2_length_aux v))
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
 eapply Le.le_trans.
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
 pattern (Max.max (t2_length t) (Max.max (t2_length t0) (t2_length_aux t1))).
 generalize (Max.max (t2_length t) (Max.max (t2_length t0) (t2_length_aux t1))).
 intro n1.
 simpl.
 apply le_n_S.
 apply plus_le_compat_l.
 repeat rewrite plus_0_r.
 apply plus_le_compat;
 apply Le.le_trans with (Max.max (t2_length b) n1);
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
 replace (Max.max (t2_length b) 0) with (t2_length b).
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





