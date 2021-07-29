Require Import primRec Arith ArithRing List.
Import extEqualNat.


(** ** Solution to an exercise  *)

Definition double n := n * 2.

Lemma doubleIsPR : isPR 1 double.
Proof.
  unfold double; apply compose1_2IsPR.
  - apply idIsPR.
  - apply const1_NIsPR.
  - apply multIsPR.
Qed.

(* begin snippet expDef *)

Fixpoint exp n p :=
  match p with
    0 => 1
  | S m =>  exp n m * n
  end.

(* end snippet expDef *)

Definition exp_alt := fun a b => nat_rec (fun _ => nat)
                                     1
                                     (fun _ y =>  y * a)
                                     b.


Remark  exp_alt_ok : extEqual 2 exp_alt exp. 
Proof.
  intros x y; induction y; cbn; auto.
Qed.



Lemma exp_alt_PR : isPR 2 exp_alt.
Proof.
  unfold exp_alt.
    apply swapIsPR.
    apply ind1ParamIsPR.
    + apply filter011IsPR.
      apply multIsPR.
    + apply const1_NIsPR.
Qed.

Lemma expIsPR : isPR 2 exp.
Proof.
  destruct exp_alt_PR as [x Hx].
  exists x.
  apply extEqualTrans with exp_alt; auto.
  apply exp_alt_ok.
Qed.

(* begin snippet tower2Def *)

Fixpoint tower2 n :=
  match n with
    0 => 1
  | S p => exp 2 (tower2 p)
  end.

(* end snippet tower2Def *)

Definition tower2_alt h : nat :=  nat_rec (fun n => nat)
                                1
                                (fun _  y =>  exp 2 y)
                                h.

Remark tower2_alt_ok  : extEqual 1 tower2_alt tower2.
Proof. intro x; induction x; cbn; auto. Qed.

Lemma tower2_alt_PR : isPR 1 tower2_alt.
Proof.
unfold tower2_alt;  apply indIsPR.
    +  apply filter01IsPR.
       eapply compose1_2IsPR.
       * apply const1_NIsPR.
       * apply idIsPR.
       * apply expIsPR.
         Qed.

Lemma tower2IsPR : isPR 1 tower2.
Proof.
 destruct tower2_alt_PR as [x Hx].
 exists x.
 apply extEqualTrans with tower2_alt; [auto | apply tower2_alt_ok].
Qed.

(* begin snippet factDef *)    
Fixpoint fact n :=
  match n with 0 => 1
          |   S p  => n * fact p
  end.
(* end snippet factDef *)    

Definition fact_alt
  : nat -> nat :=
  fun a => nat_rec _ 1 (fun x y =>  S x * y) a.

Remark fact_alt_ok : extEqual 1 fact_alt fact.
Proof.
  intro x;induction x; cbn; auto.
Qed.

Lemma fact_altIsPR : isPR 1 fact_alt.
Proof.
  unfold fact_alt; apply indIsPR.
  apply compose2_2IsPR.
  +  apply filter10IsPR; apply succIsPR.
  +  apply filter01IsPR; apply idIsPR.
  +  apply multIsPR.
Qed.

Lemma factIsPR : isPR 1 fact.
Proof.
  destruct fact_altIsPR as [x Hx].
  exists x; apply extEqualTrans with fact_alt; [trivial | ].
  apply fact_alt_ok.
Qed.


