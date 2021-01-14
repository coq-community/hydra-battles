Require Import primRec Arith ArithRing.
Import extEqualNat.

(**
Compute naryFunc 3.

= nat -> nat -> nat -> nat
  : Set


Compute naryRel 2.

  = nat -> nat -> bool
     : Set

*)
Compute extEqual 2.
(*
    = fun a b : naryFunc 3 => forall x x0 x1 : nat, a x x0 x1 = b x x0 x1
     : naryFunc 3 -> naryFunc 3 -> Prop
 *)

Example extEqual_ex1 : extEqual 2 mult (fun x y =>  y * x + x - x).
Proof.
  intros x y.
(*
  x, y : nat
  ============================
  extEqual 0 (x * y) (y * x)
 *)
  cbn. 
  rewrite <- Nat.add_sub_assoc, Nat.sub_diag.
  - ring.
  - apply le_n.  
Qed.


(** ** Understanding some constructions ...

 These lemmas are trivial and theoretically useless, but they may help to 
   make the construction more   concrete *)

Remark compose2_0 (a:nat) (g: nat -> nat)  : compose2 0 a g = g a.
Proof.   reflexivity. Qed.

Remark compose2_1 (f: nat -> nat) (g : nat -> nat -> nat) x
  : compose2 1 f g x = g (f x) x.
Proof. reflexivity. Qed.


Remark compose2_2  (f: naryFunc 2) (g : naryFunc 3) x y
  : compose2 2 f g x y = g (f x y) x y.
Proof. reflexivity. Qed.

Remark compose2_3  (f: naryFunc 3) (g : naryFunc 4) x y z 
  : compose2 3 f g x y z = g (f x y z) x y z.
Proof. reflexivity. Qed.

Remark PrimRec_0_0 (a:nat)(g : nat -> nat -> nat) :
  evalPrimRecFunc 0 a g 0 = a.
Proof. reflexivity. Qed.

Remark PrimRec_0_S (a : nat) (g : nat -> nat -> nat) (i:nat):
  evalPrimRecFunc 0 a g (S i)  = g i (evalPrimRecFunc 0 a g  i).
Proof. reflexivity. Qed.


Remark PrimRec_1_0 (f : nat->nat)(g : nat -> nat -> nat-> nat) :
  forall x,  evalPrimRecFunc 1 f g 0 x = f x.
Proof. reflexivity. Qed.

Remark PrimRec_1_S (f: nat->nat)
       (g : nat -> nat -> nat -> nat) (i:nat):
  forall x, evalPrimRecFunc 1  f g (S i) x = g i (evalPrimRecFunc 1 f g  i x) x.
Proof. reflexivity. Qed.



Remark PrimRec_2_0 (f : naryFunc 2) (g : naryFunc 4) :
  forall x y, evalPrimRecFunc 2 f g 0 x y = f x y.
Proof. reflexivity. Qed.

Remark PrimRec_2_S  (f: naryFunc 2) (g : naryFunc 4) (i:nat) :
  forall x y, evalPrimRecFunc 2  f g (S i) x y =
              g i (evalPrimRecFunc 2 f g  i x y) x y.
Proof. reflexivity. Qed.

(** ** Examples *)


Definition double n := n * 2.


Definition fact : nat -> nat :=
  fun a => nat_rec _ 1 (fun x y =>  S x * y) a.


Definition exp := fun a b => nat_rec (fun _ => nat)
                                     1
                                     (fun _ y =>  y * a)
                                     b.

Definition tower2 h : nat :=  nat_rec (fun n => nat)
                                1
                                (fun _  y =>  exp 2 y)
                                h.

Remark tower2_S h : tower2 (S h) = exp 2 (tower2 h).
Proof. reflexivity. Qed.

Lemma doubleIsPR : isPR 1 double.
Proof.
  unfold double; apply compose1_2IsPR.
  - apply idIsPR.
  - apply const1_NIsPR.
  - apply multIsPR.
Qed.


Lemma factIsPR : isPR 1 fact.
Proof.
  unfold fact; apply indIsPR.
  apply compose2_2IsPR.
  -  apply filter10IsPR; apply succIsPR.
  -  apply filter01IsPR; apply idIsPR.
  -  apply multIsPR.
Qed.


Lemma expIsPR : isPR 2 exp.
Proof.
  unfold exp.
  apply swapIsPR.
  apply ind1ParamIsPR.
  -  apply filter011IsPR.
     apply multIsPR.
  - apply const1_NIsPR.
Qed.

Lemma exp2IsPR : isPR 1 (exp 2).
Proof.
unfold exp; refine (compose2IsPR 1 (fun _ => 2) _ exp _).
 - apply const1_NIsPR.
 - apply expIsPR.
Qed.


Lemma tower2IsPR : isPR 1 tower2.
Proof.
  unfold tower2; apply indIsPR.
  apply filter01IsPR.
  apply exp2IsPR.
Qed.



