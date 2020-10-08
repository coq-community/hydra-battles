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
    LaBRI, University of Bordeaux
    
    Evelyne Contejean
    LRI.
*)


(** Cantor "pre" Normal form
 After Manolios and Vroon work on ACL2 *)

From Coq Require Import Arith  Lia  Compare_dec  Relations  Wellfounded
     Wf_nat  List Bool Eqdep_dec Ensembles ArithRing Logic.

From hydras Require Import More_Arith Restriction   
     DecPreOrder  rpo.term  rpo.rpo Epsilon0.T1.

Set Implicit Arguments.

Module Alt.
  
Module  Eps0_sig <: Signature.


Inductive symb0 : Set := nat_0 | nat_S | ord_zero | ord_cons.

Definition symb := symb0.

Lemma eq_symbol_dec : forall f1 f2 : symb, {f1 = f2} + {f1 <> f2}.
Proof.
intros; decide equality.
Qed.

(** The arity of a symbol contains also the information about built-in theories as in CiME *)

Inductive arity_type : Set :=
  | AC : arity_type
  | C : arity_type
  | Free : nat -> arity_type.

Definition arity : symb -> arity_type :=
  fun f => match f with
                  | nat_0 => Free 0
                  | ord_zero => Free 0
                  | nat_S => Free 1
                  | ord_cons => Free 3
                  end.

End Eps0_sig.

(** * Module Type Variables. 
 There are almost no assumptions, except a decidable equality. *)

Module Vars <: Variables.

Inductive empty_set : Set := .
Definition var := empty_set.

Lemma eq_variable_dec : forall v1 v2 : var, {v1 = v2} + {v1 <> v2}.
Proof.
intros; decide equality.
Qed.

End Vars.

Module  Eps0_prec <: Precedence.

Definition A : Set := Eps0_sig.symb.
Import Eps0_sig.

Definition prec : relation A :=
   fun f g => match f, g with
                      | nat_0, nat_S => True
                      | nat_0, ord_zero => True
                      | nat_0, ord_cons => True
                      | ord_zero, nat_S => True
                      | ord_zero, ord_cons => True
                      | nat_S, ord_cons => True
                      | _, _ => False
                      end.


Inductive status_type : Set :=
  | Lex : status_type
  | Mul : status_type.

Definition status : A -> status_type := fun f => Lex.

Lemma prec_dec : forall a1 a2 : A, {prec a1 a2} + {~ prec a1 a2}.
Proof.
  intros a1 a2; destruct a1; destruct a2;
    ((right; intro; contradiction)||(left;simpl;trivial)).
Qed.

Lemma prec_antisym : forall s, prec s s -> False.
Proof.
  intros s; destruct s; simpl; trivial.
Qed.

Lemma prec_transitive : transitive A prec.
Proof.
  intros s1 s2 s3; destruct s1; destruct s2; destruct s3; simpl; intros;
    trivial; contradiction.
Qed.

End Eps0_prec.

Module Eps0_alg <: Term := term.Make (Eps0_sig) (Vars).
Module Eps0_rpo <: RPO := rpo.Make (Eps0_alg) (Eps0_prec).

Import Eps0_alg.
Import Eps0_rpo.
Import Eps0_sig.


Fixpoint nat_2_term (n:nat) : term :=
  match n with 0 => (Term nat_0 nil)
             | S p => Term nat_S ((nat_2_term p)::nil)
  end.



(** * 
Every (representation of a) natural number is less than
 a non zero ordinal *)

Lemma nat_lt_cons : forall (n:nat) a p  b , rpo (nat_2_term n) 
                                     (Term ord_cons (a::p::b::nil)).
 induction n;simpl.
 constructor 2.
 simpl; trivial.
 destruct 1.
 constructor 2.
 simpl; trivial.
 inversion_clear 1.
 subst s';apply IHn.
 case H0.
Qed.



Theorem rpo_trans : forall t t1 t2, rpo t t1 -> rpo t1 t2 -> rpo t t2.
 intros.
 case (rpo_closure t2 t1 t);eauto.
Qed.


Fixpoint T1_2_term (a:T1) : term := 
match a with
 zero => Term ord_zero nil
|ocons a n b => Term ord_cons (T1_2_term a :: nat_2_term n ::T1_2_term b::nil)
end.

Fixpoint T1_size (o:T1):nat :=
 match o with zero => 0
            | ocons a n b => S (T1_size a + n + T1_size b)%nat
         end.

Lemma T1_size1 : forall a n b, (T1_size zero < T1_size (ocons a n b))%nat.
Proof.
 simpl.
 intros.
 auto with arith.
Qed.

Lemma T1_size2 : forall a n b , (T1_size a < T1_size (ocons a n b))%nat.
Proof.
 simpl; auto with arith.
Qed.

Lemma T1_size3 : forall a n b , (T1_size b < T1_size (ocons a n b))%nat.
Proof.
 simpl; auto with arith.
Qed.

Hint Resolve T1_size2 T1_size3 : rpo.


(** let us recall subterm properties on T1 *)
Lemma lt_subterm1 : forall a a'  n'  b', lt a  a' ->
                                         lt a  (ocons a' n' b').
Proof.
 intros.
 apply lt_trans with (ocons a n' b');auto with T1.
 apply head_lt_ocons.
Qed.

Lemma lt_subterm2 : forall a a' n n' b b', lt a  a' ->
                                           nf (ocons a n  b) ->
                                           nf (ocons a' n' b') ->
                                           lt b ( ocons a' n' b').
Proof.
 intros.
 apply le_lt_trans with (ocons a n b).
apply  lt_le_incl.
 apply tail_lt_ocons;auto.
 auto with T1.
Qed.


Hint Resolve nat_lt_cons : rpo.
Hint Resolve lt_subterm2 lt_subterm1 : rpo.
Hint Resolve T1_size3 T1_size2 T1_size1 : rpo.


Lemma nat_2_term_mono : forall n n', (n < n')%nat -> 
                                      rpo (nat_2_term n) (nat_2_term n').
Proof.
 induction 1.
 simpl.
 eapply Subterm.
 eleft.
 esplit.
 constructor.
 simpl.
 eapply Subterm.
 eleft.
 esplit.
 constructor.
 auto.
Qed.

                       
Theorem lt_inc_rpo_0 : forall n, 
                           forall o' o, (T1_size o + T1_size o' <= n)%nat->
                              lt o  o' -> nf o -> nf o' -> 
                                  rpo (T1_2_term o) (T1_2_term o').
Proof.
 induction n.
 - destruct o'.
 +   intros; destruct (not_lt_zero H0). 
 + 
 destruct o.
  *  simpl.
 inversion 1.
  *  simpl;inversion 1.
 -  intros.
    destruct o, o'.
    + destruct (lt_irrefl H0).
    +  simpl. apply Top_gt.
       simpl.       trivial.
       inversion 1.        
   + 
     destruct (not_lt_zero H0).
 + 
 destruct (lt_inv H0).
 simpl; intros; apply Top_eq_lex.
 simpl;trivial.
 left.
 apply IHn.
(* subst o;subst o'. *)
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (T1_size (ocons o1 n0 o2) + T1_size (ocons o'1 n1 o'2))%nat.
 simpl;
 auto with arith rpo.
 abstract lia.
 auto.
 auto.
 eauto with T1.
 eauto with T1. 

 simpl;auto with rpo.
 inversion_clear 1.
 subst s'.
 change (rpo (T1_2_term o1) (T1_2_term (ocons o'1 n1 o'2))).
 apply IHn;auto with rpo.
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (T1_size (ocons o1 n0 o2) + T1_size (ocons o'1 n1 o'2))%nat.
 auto with arith rpo.
 auto with rpo.
 eauto with T1 rpo.
 destruct H5 as [|[|H8]].
 subst s'.
 apply nat_lt_cons.
 subst s'.
 change (rpo (T1_2_term o2) (T1_2_term (ocons o'1 n1 o'2))).
 apply IHn;auto with rpo.

 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (T1_size (ocons o1 n0 o2) + T1_size (ocons o'1 n1 o'2))%nat.
 auto with arith rpo.
 auto with rpo.
 eauto with rpo.
 eauto with T1.
 case H8.
 intros.
 simpl;apply Top_eq_lex.
 decompose [or and] H3.
 auto with rpo.
 subst. 
   auto.
 decompose [or and] H3.
 subst. 
constructor 2.
 constructor 1.
 apply nat_2_term_mono.
 auto.
 auto.
 subst.
    decompose [or and] H3.

    destruct (Nat.lt_irrefl _ H6).
 subst. 

apply List_eq.
apply List_eq.
apply List_gt.
 eapply IHn; eauto. 
simpl in H.
ring_simplify in H.
 clear IHn. 
 simpl in H; abstract lia. 
 eauto with T1.
 eauto with T1.
 trivial.
decompose [or and] H3.
clear H3. subst.  

 inversion_clear 1.
 subst s'.
 change (rpo (T1_2_term o'1) (T1_2_term (ocons o'1 n1 o'2))).
 apply IHn;auto.

 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (T1_size (ocons o'1 n0 o2) +
                            T1_size (ocons o'1 n1 o'2))%nat.
 
 auto with arith rpo.
 auto with rpo.
 apply head_lt_ocons.
  eauto with T1.
 destruct H4 as [|[|H8]].
 subst s'.
 apply nat_lt_cons.
 subst s'.
 change (rpo (T1_2_term o2) (T1_2_term (ocons o'1 n1 o'2))).
 apply IHn;auto with rpo.

 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (T1_size (ocons o'1 n0 o2) + T1_size (ocons o'1 n1 o'2))%nat.
 auto with arith rpo.
 auto with rpo.

 apply lt_le_trans with (ocons o'1 0 zero).



 apply lt_phi0_phi0.

 eapply lt_phi0_intro. 
 eauto. 


 auto with T1 rpo.
 auto with T1 rpo.
 apply lt_le_incl.
 apply LT3.
 eauto with T1.
 eauto with T1.
 eauto with arith.
  eauto with T1. 
  inversion H8. 
 subst o'1 n1.
 clear H3.

 inversion_clear 1.
 subst. 
   change (rpo (T1_2_term o1) (T1_2_term (ocons o1 n0 o'2))).
  apply IHn; auto. 
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (T1_size (ocons o1 n0 o2) + T1_size (ocons o1 n0 o'2))%nat.
 auto with arith rpo.
 auto with rpo.
apply head_lt_ocons. 
eauto with T1 rpo.
inversion_clear H4. subst s'.

apply nat_lt_cons.
inversion_clear H3.
subst s'.



apply Eps0_rpo.rpo_trans with (T1_2_term o'2).

apply Subterm with (T1_2_term o'2).
simpl. 
right. 
right. 
now left.

apply Eq.
apply IHn; eauto with T1 rpo.
simpl in H. 
clear IHn. 
abstract lia. 
inversion H4. 
Qed. 


 
Remark R1 : Acc P.prec nat_0. 
 split.
 destruct y; try contradiction.
Qed.

Hint Resolve R1 : rpo.

Remark R2 : Acc P.prec ord_zero. 
 split.
 destruct y; try contradiction; auto with rpo.
Qed.

Hint Resolve R2 : rpo.

Remark R3 : Acc P.prec nat_S.
 split.
 destruct y; try contradiction;auto with rpo.
Qed.


Hint Resolve R3 : rpo.

Remark R4 : Acc P.prec ord_cons.
 split.
 destruct y; try contradiction;auto with rpo.
Qed.

Hint Resolve R4 : rpo.

Theorem well_founded_rpo : well_founded rpo.
Proof.
 apply wf_rpo.
 red.
 destruct a;auto with rpo.
Qed.

Section  well_founded.
 
  Let R := restrict  nf lt.

  Hint Unfold restrict R : rpo.

 Lemma R_inc_rpo : forall o o', R o o' -> rpo (T1_2_term o) (T1_2_term o').
 Proof.
  intros o o' (H,(H1,H2)).
  eapply lt_inc_rpo_0;auto.
 Qed. 

 
 Lemma nf_Wf : well_founded_restriction _ nf lt.
Proof.
 unfold well_founded_restriction.
 intros.
 unfold restrict.
 generalize (Acc_inverse_image _ _ rpo T1_2_term a (well_founded_rpo (T1_2_term a))).
  intro.
 eapply  Acc_incl  with  (fun x y : T1 => rpo (T1_2_term x) (T1_2_term y)). 
 red.
 apply R_inc_rpo.
 auto.
Qed.


(** For compatibility with T1 *)
Lemma nf_Acc : forall alpha, nf alpha -> Acc LT alpha.
Proof nf_Wf.



 End well_founded.


Definition transfinite_recursor_lt :
 forall (P:T1 -> Type),
   (forall x:T1, nf x -> 
                   (forall y:T1, nf y ->  lt y  x -> P y) -> P x) ->
    forall a, nf a -> P a.
Proof.
 intros; eapply well_founded_restriction_rect; eauto;
 eexact nf_Wf;auto.
Defined.

Definition transfinite_recursor :
 forall (P:T1 -> Type),
   (forall x:T1, nf x -> 
                   (forall y:T1, y  t1< x -> P y) -> P x) ->
    forall a, nf a -> P a.
Proof.
 intros; apply transfinite_recursor_lt; auto.
 intros;  apply X;auto.
 destruct 1 as [H1 [H2 H3]];auto.
Defined.


Ltac transfinite_induction_lt a :=
  pattern a; apply transfinite_recursor_lt ;[ | try assumption].

Ltac transfinite_induction a :=
  pattern a; apply transfinite_recursor;[ | try assumption].

End Alt.
