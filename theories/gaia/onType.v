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

Definition restrict {A} (p: A -> bool)
  (r: A -> A -> bool):=
  fun x y => [&& (p x), (p y) & r x y].


Module ONDef.

  Section Defs. 
  Variable T: orderType tt.
  Variable nf : ssrbool.pred T.

  Definition limit_v2 (f: nat -> T)(x: T) :=
    (forall (n:nat), (f n < x)%O) /\
      (forall y : T, nf y -> (y < x)%O ->
                     exists n : nat, (y <= f n)%O).


  Definition limit_of (f: nat -> T) x := 
    [/\ forall n m : nat, (n < m)%nat -> (f n < f m)%O,
       limit_v2  f x & nf x].
  
  Definition is_successor_of  (x y: T):=
    restrict nf <%O x y /\
      (forall z,  nf z -> (x < z)%O ->  (z <  y)%O -> False).

  End Defs. 
  Record mixin_of (T: orderType tt)  :=
    Mixin {
        nf : T -> bool;
        wf : well_founded (restrict nf <%O);
        limitb : T -> bool;
        succb : T -> bool;
        zerob : T -> bool;
        _ : forall z, zerob z -> nf z;
        _ : forall z, zerob z <-> forall a, nf a -> (z <= a)%O;
        _ : forall a, nf a -> reflect (exists f, limit_of nf f a)
                                (limitb a);
        _ : forall a , nf a ->
                       reflect  (exists b, is_successor_of nf a b)
                         (succb a)
      }.
  
  (* to complete *)


  About mixin_of.
  Section Packing.
    Structure pack_type : Type :=
      Pack{ type: orderType tt; _ : mixin_of type}.

     Local Coercion type : pack_type >-> orderType .

     Variable cT: pack_type. 

     Definition on_struct: mixin_of cT :=
       let: Pack _ c := cT return mixin_of cT in c.

     Definition is_zero := zerob on_struct. 
    End Packing.    

  Module Exports. 

  Notation on := pack_type. 
  Notation ONMixin := Mixin. 
  Notation ON T m := (@Pack T m).
  Notation nf := (nf (on_struct _)).
  Notation zerob := is_zero.
  Coercion type : pack_type >-> orderType.
  
  Section Lemmas.

    Variable U: on.

Lemma nf_zero (a: U) : zerob a -> nf a.
  case: U a => t r a. rewrite /zerob. rewrite /nf => //=.
  move: r a; case => //=. 
Qed. 

About restrict. 
Lemma wf : @well_founded U (restrict (nf )  <%O). 
Proof. case: U => t [h w *] a; apply: w. Qed. 

  End Lemmas. 
  End Exports.
  End ONDef.



  
