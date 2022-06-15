(** Experimental !!!! *)
(** This file is a draft !!! *)

(*
https://math-comp.github.io/htmldoc_1_14_0/mathcomp.ssreflect.choice.html

https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/order.v
 *)


From mathcomp Require Import all_ssreflect zify.
From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder ON_Generic  T1 E0.
From gaia Require Export ssete9.
Require Import T1Bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(**  Type [T1] vs generic trees *)

Fixpoint T12Tree (a: T1): GenTree.tree nat :=
  if a is cons b n c
  then GenTree.Node n [:: T12Tree b; T12Tree c]
  else GenTree.Leaf 0.                                        

Fixpoint Tree2T1 (t: GenTree.tree nat): option T1 :=
  match t with
  | GenTree.Leaf 0 => Some zero
  | GenTree.Node n [:: t1; t2] =>
      match Tree2T1 t1, Tree2T1 t2 with
      | Some b, Some c => Some (cons b n c)
      | _, _ => None
      end
  | _ => None
  end.

Lemma TreeT1K : pcancel T12Tree Tree2T1. 
Proof. 
  elim => //.
  move => t Ht n t0 Ht0 /=; by rewrite Ht0 Ht. 
Qed.                                              

(** to remove (useless) *)
Lemma  T12Tree_inj: injective T12Tree.   
Proof.
  move => t1 t2 Heq.
  have H: Some t1 = Some t2 by rewrite -!TreeT1K Heq. 
  by injection H. 
Qed.

Definition T1mixin :
  Countable.mixin_of T1 := PcanCountMixin TreeT1K.

Canonical T1Choice :=
  Eval hnf in ChoiceType T1 (CountChoiceMixin T1mixin).

Example ex_pos: exists alpha: T1, zero != alpha. 
Proof. exists (cons zero 0 zero) => //. Qed. 

Example some_pos: T1 := xchoose ex_pos. 

Example some_pos' : T1 := choose (fun p : T1 => zero != p)
                                 T1omega.

Goal (zero: T1Choice) != some_pos'.
  pose p a := (zero != a); move: (@chooseP _ p T1omega).
  rewrite /p /some_pos' => H; by apply: H. 
Qed.

Compute  [eqType of T1].
(**    = EqType T1 (EqMixin (@T1eqP))
     : eqType *)

Compute  [choiceType of T1]. 

(**
   = Choice.Pack
         {|
           Choice.base := EqMixin (@T1eqP);
           Choice.mixin := PcanChoiceMixin (pcan_pickleK TreeT1K)
         |}
     : choiceType

*)

Definition T1_le_Mixin := leOrderMixin T1Choice.

Definition T1min a b := if T1lt a b then a else b. 
Definition T1max a b := if T1lt a b then b else a. 

Lemma T1ltE x y : T1lt x y = (y != x) && T1le x y.
Proof. by rewrite T1lt_neAle eq_sym. Qed. 

Lemma T1minE x y : T1min x y = (if T1lt x y then x else y).
Proof. done. Qed. 

Lemma T1maxE x y : T1max x y = (if T1lt x y then y else x).
Proof. done. Qed. 

Lemma T1le_asym: ssrbool.antisymmetric T1le.
Proof. move => x y;  by rewrite -T1eq_le =>/eqP. Qed.


Definition T1leOrderMixin : leOrderMixin T1Choice :=
  LeOrderMixin T1ltE T1minE T1maxE T1le_asym T1le_trans T1le_total.

Canonical T1orderType :=
  @OrderOfChoiceType tt T1Choice T1leOrderMixin.

Goal @Order.le tt T1orderType T1omega T1omega.
by rewrite Order.POrderTheory.lexx.
Qed.


Notation "x <= y" := (@Order.le _ T1orderType  x y).

Notation "x < y" := (@Order.lt _ T1orderType  x y).

About Order.le. 


Goal @Order.le tt T1orderType T1omega T1omega.
apply Order.POrderTheory.lexx. 
Qed. 
Import Order.POrderTheory.

Goal T1omega <= T1omega. 
Set Printing All.
apply lexx. 
Qed.

Goal T1omega < T1succ T1omega.
by [].
Qed. 



Fail Goal  ~~ (<%O T1omega T1omega).

Goal  ~~ (<%O (T1omega:T1orderType) (T1omega:T1orderType)).
by cbn. Qed.


Goal ~~(T1omega < T1omega).
by cbn.   
Qed. 


Compute Order.POrder.sort T1orderType. 
Goal ~~ @Order.lt tt (T1orderType) T1omega T1omega.
Search (~~ _).
by cbn. 
Qed. 


Goal T1omega <= T1omega. 
by []. 
Qed. 

Fail Goal Order.max T1omega T1omega == T1omega.

Check T1omega: T1Choice. 

Check T1omega: T1orderType.


