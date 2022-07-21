(** Ordinal Notations (Experimental !!!!) *)
(** Warning:  This file is a draft !!! *)

(*
https://math-comp.github.io/htmldoc_1_14_0/mathcomp.ssreflect.choice.html

https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/order.v
 *)


From mathcomp Require Import all_ssreflect zify.
From mathcomp Require Import fintype. 
From Coq Require Import Logic.Eqdep_dec.
Require Import Wellfounded.Inclusion Wf_nat. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Preliminaries *)
(** restriction of a decidable relation *)

Definition restrict {A} (p: A -> bool) (r: A -> A -> bool):=
  fun x y => [&& (p x), (p y) & r x y].

(** ** Complements on orderType *)

Section MoreOrderType.
  Variable disp: unit.
  Variable T: orderType disp. 
  
  (* adapted from gaia's ssete9 *)
  
  Definition limit_v2 (f: nat -> T)(x: T) :=
    (forall (n:nat), (f n < x)%O) /\
      (forall y : T,  (y < x)%O -> exists n : nat, (y <= f n)%O).

  (* adapted from gaia's ssete9 *)
  
  Definition limit_of (f: nat -> T) x := 
    (forall n m : nat, (n < m)%nat -> (f n < f m)%O) /\ limit_v2 f x.
  
  Definition is_successor_of  (x y: T):= 
    (x < y)%O /\ forall z,  (x < z)%O ->  ~~ (z <  y)%O. 

  Section Succ_no_limit.
    Variables (x y: T) (s: nat -> T).
    Hypothesis Hsucc : is_successor_of x y.
    Hypothesis Hlim : limit_of s  y.

    Remark R0: exists (n:nat), (x <= (s n))%O. 
    Proof. case Hlim => _ [H H']; apply H'; by case Hsucc. Qed. 

    Remark R1: exists z, (x < z < y)%O.
    Proof. 
      case R0 => n Hn. exists (s (S n)). 
      apply /andP; split.
      apply Order.POrderTheory.le_lt_trans with (s n) => //.
      case: Hlim => H H0.  apply: H => //.
      case: Hlim => _ [H'' _]  //.
    Qed. 

    Lemma F: False.
      case Hsucc => _ H. move: R1 ;case => x0 Hx0.
      move: (H x0) => //; move: Hx0.
      move /andP => //. 
      case; move => H' H'' => H'''.
      by move: (H''' H') => // /negP.  
    Qed. 
    
  End Succ_no_limit.

End MoreOrderType.


(** An Ordinal  Notation is just a well-founded ordered type, with 
    a trichotomic comparison 

    Notions of successor and limits should be defined in substructures
 *)






Module ONDef.
  Record mixin_of disp (T: orderType disp)  :=
    Mixin {
        _ : @well_founded T <%O;
      }.
  
  Section Packing.
    Variable disp: unit. 
    Structure pack_type : Type :=
      Pack{ type: orderType disp; _ : mixin_of type}.

    Local Coercion type : pack_type >-> orderType .

    Variable cT: pack_type. 

    Definition on_struct: mixin_of cT :=
      let: Pack _ c := cT return mixin_of cT in c.

  End Packing.    

  Module Exports.

    Notation on := (pack_type ).
    Notation ONMixin := Mixin. 
    Notation ON T m := (@Pack T m).
    Coercion type : pack_type >-> orderType.
    
    Section Lemmas.
      Variable disp: unit. 
      Variable U: @on  disp.

      Definition tricho (a b: U) := if (a == b)%O then Eq
                                    else if (a < b)%O then Lt
                                         else Gt.
  
      Lemma trichoP (a b: U) :
        CompareSpec (a == b) (a < b)%O (b < a)%O (tricho a b).
      Proof. 
        rewrite /tricho; case Hab:  (a == b) => //.
        by constructor.
        case H'ab: (a < b)%O; constructor => //. 
        rewrite Order.POrderTheory.lt_def. 
        apply /andP; split.
        by rewrite /negb Hab.
        have diff : a != b by rewrite Hab.  move: diff. 
        rewrite Order.TotalTheory.neq_lt H'ab Bool.orb_false_l.
        by apply: Order.POrderTheory.ltW. 
      Qed.

      
      Lemma wf : @well_founded U <%O. 
      Proof. case: U => t [  w *] a.  apply: w. Qed. 

    End Lemmas. 
  End Exports.
End ONDef.

Export ONDef.Exports. 

(* The Ordinal notation for 'I_i *)
Require Import Inverse_Image.


Lemma wf_ltn: well_founded (fun n => [eta ltn n]).
  move => n; apply Acc_incl with lt. 
  - by move => i j /ltP.
  - apply lt_wf. 
Qed.


Section onFiniteDef. 

  Variable i: nat. 

 
 (* Error in  (mathcomp/mathcomp:1.12.0-coq-8.13) 
          and build (mathcomp/mathcomp:1.12.0-coq-8.14) 

    Works : build (mathcomp/mathcomp:1.13.0-coq-8.14) 
            build (coqorg/coq:dev-ocaml-4.13.1-flambda) 
            build (mathcomp/mathcomp:1.14.0-coq-8.15) 
            build (mathcomp/mathcomp:1.13.0-coq-8.13) 

*)

(* The term "alpha" has type "'I_i" while it is expected to have type
  -  "Order.POrder.sort ?T".

 *)
  
    (** possibly useless ???? *)
  
  Definition rel2Rel {T} (r: rel T) := (fun x y => r x y: Prop).
  Coercion rel2Rel : rel >-> Funclass.
  
  
  Lemma I_i_wf: @well_founded 'I_i (<%O).
  Proof.
    case => m Hm; rewrite ltEord.
    apply (Acc_inverse_image 'I_i nat (rel2Rel ltn)
             (nat_of_ord (n:=i))  _ (wf_ltn (Ordinal Hm))).
  Qed. 

Definition onFiniteMixin := ONMixin I_i_wf.
Canonical onFiniteType := ON _ _ onFiniteMixin.


End onFiniteDef.

(** Tests 
Definition O12_33: onFiniteType 33. 
by exists 12.
Defined. 

Compute tricho O12_33 O12_33.


Goal (O12_33 <= O12_33)%O. 
by [].
Qed. 


Definition L11: 'I_33. 
Proof. by exists 11. Defined. 

Compute tricho L11 O12_33.

*)



Section onOmegaDef.

 Lemma omega_lt_wf : @well_founded Order.NatOrder.orderType <%O. 
 Proof. exact: wf_ltn. Qed.

 
Definition onOmegaMixin := ONMixin omega_lt_wf.
Canonical onOmegaType := ON _ _ onOmegaMixin. 


End onOmegaDef.

Example om12 : onOmegaType := 12. 
Example om67 : onOmegaType := 67. 

Compute tricho om67 om12. 

Require Import T1Bridge.

Section ONEpsilon0Def. 

 (*
 Search E0.
  *)
  
  (* Todo: Build an orderType over E0 *)

End ONEpsilon0Def.
