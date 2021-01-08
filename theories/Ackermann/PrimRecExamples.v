Require Import primRec.
Import extEqualNat.



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

Definition fact : nat -> nat :=
  fun a => nat_rec _ 1 (fun x y =>  S x * y) a.

Lemma factIsPR : isPR 1 fact.
Proof.
  unfold fact; apply indIsPR.
  apply compose2_2IsPR.
  -  apply filter10IsPR; apply succIsPR.
  -  apply filter01IsPR; apply idIsPR.
  -  apply multIsPR.
Qed.


Definition double n := n * 2.
Definition exp2 := fun a => nat_rec (fun n => nat)
                                    1
                                    (fun _  y =>  double y)
                                    a.
Definition tower2 h : nat :=  nat_rec (fun n => nat)
                                1
                                (fun _  y =>  exp2 y)
                                h.

Lemma doubleIsPR : isPR 1 double.
Proof.
  unfold double; apply compose1_2IsPR.
  - apply idIsPR.
  - apply const1_NIsPR.
  - apply multIsPR.
Qed.

Lemma exp2IsPR : isPR 1 exp2.
  unfold exp2; apply indIsPR.
  apply filter01IsPR.
  apply doubleIsPR.
Qed.



Remark tower2_S h : tower2 (S h) = exp2 (tower2 h).
Proof. reflexivity. Qed.

Lemma tower2IsPR : isPR 1 tower2.
Proof.
  unfold tower2; apply indIsPR.
  apply filter01IsPR.
  apply exp2IsPR.
Qed.



