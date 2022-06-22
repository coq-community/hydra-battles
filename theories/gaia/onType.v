(** Experimental !!!! *)
(** This file is a draft !!! *)

(*
https://math-comp.github.io/htmldoc_1_14_0/mathcomp.ssreflect.choice.html

https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/order.v
 *)


From mathcomp Require Import all_ssreflect zify.
From Coq Require Import Logic.Eqdep_dec.
Require Import Wellfounded.Inclusion Wf_nat. 



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition restrict {A} (p: A -> bool)
  (r: A -> A -> bool):=
  fun x y => [&& (p x), (p y) & r x y].


(** An Ordinal  Notation is just a well-founded ordered type, with 
    a trichotomic comparison 

    Notions of successor and limits shold be defined in substructures *)

Section MoreOrderType.
  Variable disp: unit.
  Variable T: orderType disp. 
  
  Variable nf : ssrbool.pred T.

  Definition limit_v2 (f: nat -> T)(x: T) :=
    (forall (n:nat), (f n < x)%O) /\
      (forall y : T, nf y -> (y < x)%O ->
                     exists n : nat, (y <= f n)%O).

  Definition limit_of (f: nat -> T) x := 
    [/\ forall n m : nat, (n < m)%nat -> restrict nf <%O (f n) (f m),
       limit_v2 f x & nf x].
  
  Definition is_successor_of  (x y: T):=
    restrict nf <%O x y /\
      (forall z,  nf z -> (x < z)%O ->  (z <  y)%O -> False).

  
  Section Succ_no_limit.
    Variables (x y: T) (s: nat -> T).
    Hypothesis Hsucc : is_successor_of x y.
    Hypothesis Hlim : limit_of s  y.

    Lemma nf_s : forall n, nf (s n).
    Proof. 
      move => n; case Hlim => H _ _.
      move: (H _ _  (ltnSn n));
        rewrite /restrict; move /andP; by case. 
    Qed. 
    Remark R0 : nf x. 
    Proof. case Hsucc ;rewrite /restrict => /andP; by case. Qed. 

    Remark R1 : nf y. 
    Proof.
      case Hsucc ; rewrite /restrict => /andP;
                                        case => _ /andP;
                                                  by case.
    Qed. 

    Remark R2: exists (n:nat), (x <= (s n))%O. 
    Proof.
      case Hlim => H1 [H2 H3] _ . 
      apply H3 .  apply R0. case Hsucc. rewrite /restrict.
      move /andP.  case => _; move /andP. by case.
    Qed. 

    Remark R3: exists z, (x < z < y)%O /\ nf z. 
    Proof. 
      case R2 => n Hn. exists (s (S n)). split. 
      apply /andP; split.
      apply Order.POrderTheory.le_lt_trans with (s n) => //.
      case: Hlim => H H0 _.
      move: (H _ _  (ltnSn n));
        rewrite /restrict; move /andP; case => _; move /andP. 
      by case. 
      case: Hlim => _.  case => H H0  _. by apply: H.
      apply nf_s. 
    Qed. 


    Lemma F: False.
      case Hsucc => _ H. case R3 => n [Hn Hn'] => //.
      apply H with n. 
      done. 
      move: Hn => /andP. by case. 
      move: Hn => /andP. by case. 
    Qed. 
    
  End Succ_no_limit.




End MoreOrderType.


Module ONDef.


  Record mixin_of disp (T: orderType disp)  :=
    Mixin {
        nf : T -> bool;
        wf : well_founded (restrict nf <%O);
        cmp: T -> T -> comparison;
        zerob : T -> bool; 
        _ : forall z, zerob z -> nf z;
        _ : forall z, zerob z <-> forall a, nf a -> (z <= a)%O;
        _ : forall a b : T,
          nf a -> nf b ->
          CompareSpec (a == b) (a < b)%O (b < a)%O (cmp a b);
        
      }.
  
  Section Packing.
    Variable disp: unit. 
    Structure pack_type : Type :=
      Pack{ type: orderType disp; _ : mixin_of type}.

    Local Coercion type : pack_type >-> orderType .

    Variable cT: pack_type. 

    Definition on_struct: mixin_of cT :=
      let: Pack _ c := cT return mixin_of cT in c.

    Definition is_zero := zerob on_struct. 
  End Packing.    

  Module Exports. 

    Notation on := (pack_type ).
    Notation ONMixin := Mixin. 
    Notation ON T m := (@Pack T m).
    Notation nf := (nf (on_struct _)).
    Notation zerob := is_zero.
    Notation cmp := (cmp (on_struct _)).
    Coercion type : pack_type >-> orderType.
    
    Section Lemmas.
      Variable disp: unit.
      Variable U: @on disp.

      Lemma nf_zero (a: U) : zerob a -> nf a.
      Proof.
        case: U a => t r a. rewrite /zerob. rewrite /nf => //=.
        move: r a; case => //=. 
      Qed. 

      Lemma zeroE (a: U) : zerob a <-> forall b, nf b -> (a <= b)%O.
      Proof.     
        case: U a =>  t [nf w l i i0 i1] a.  apply: i1. 
      Qed. 

      Lemma compareP (a b: U) :
        nf a -> nf b ->
        CompareSpec (a == b) (a < b)%O (b < a)%O (cmp a b).
      Proof. 
        case: U a b => t [nf w l i i0 i1 i2] a b;  apply: i2. 
      Qed.

      
      Lemma wf : @well_founded U (restrict (nf )  <%O). 
      Proof. case: U => t [h w *] a; apply: w. Qed. 

    End Lemmas. 
  End Exports.
End ONDef.

Export ONDef.Exports.

Notation omegaType := Order.NatOrder.orderType. 

Section OmegaON. 

  Definition nf (x: omegaType) := true. 
  Definition zerob (x: omegaType) := x == 0.
  Definition cmp (x y: omegaType) := Nat.compare x y. 
  
  Lemma nf_zero (z:omegaType): zerob z -> nf z. 
  Proof. by rewrite  /nf. Qed.

  Lemma OmegazerobP:
    forall z, zerob z <-> forall a, nf a -> (z <= a)%O. 
  Proof.
    move => z; rewrite /zerob /nf /le => //=; split. 
    - move /eqP => -> //=.  
    - move => H. move: (H 0) => {H}; case :z => //=. 
      move => n; cbn => //= H; by apply H. 
  Qed. 

  Lemma OmegacmpP (a b: omegaType):
    nf a -> nf b ->
    CompareSpec (a == b) (a < b)%O (b < a)%O (cmp a b).
  Proof.
    case_eq (cmp a b) => H; constructor.
    - apply /eqP; by apply Compare_dec.nat_compare_eq. 
    - apply /ltP; by apply Compare_dec.nat_compare_lt. 
    - apply /ltP; by apply Compare_dec.nat_compare_gt. 
  Qed. 

  Lemma OmegaWf: well_founded (restrict nf <%O). 
  Proof.  
    move => x; apply Acc_incl with (2:= lt_wf x). 
    move => a b; rewrite /restrict => /andP.
    case => _ ;move /andP ; case => _ ?; by apply :ltP.
  Qed. 

  
  Definition OmegaMixin :=
    ONMixin OmegaWf nf_zero OmegazerobP OmegacmpP.

  Canonical onOmegaType :=
    ON _ omegaType  OmegaMixin. 

  Check @Order.SeqLexiOrder.orderType  Order.NatOrder.nat_display tt
    Order.NatOrder.orderType. 

End OmegaON.

Compute cmp 7 9. 


(** To move elsewhere ??? *)


(*   Lemma limitP (a:U) : nf a -> reflect (exists f, limit_of nf f a)
                                (limitb a).
    Proof.       
      case: U a => t [nf w l s z Hz Hz' Hl r a *];  by apply: (Hl a).    Qed.

    Lemma succP (a:U) :
      nf a ->
      reflect  (exists b, is_successor_of nf a b) (succb a).
      Proof.       
        case: U a => t [nf w l s z Hz Hz' Hl r a *]. by apply: (r a).    Qed. 
 *)
