Require Import primRec Arith ArithRing List.
Import extEqualNat.
Require Import Vector.
Import VectorNotations.
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


(** ** Examples of terms of type [PrimRec n] and their interpretation *)

Example Ex1 : evalPrimRec 0 zeroFunc = 0.
Proof. reflexivity. Qed.

Example Ex2 a : evalPrimRec 1 succFunc a = S a.
Proof. reflexivity. Qed.

Example Ex3 a b c d e f: forall (H: 2 < 6),
    evalPrimRec 6
                (projFunc 6 2 H) a b c d e f = d.
Proof. reflexivity. Qed.


Example Ex4 (x y z : PrimRec 2) (t: PrimRec 3):
  let u := composeFunc 2 3
                       (PRcons 2 2 x
                               (PRcons 2 1 y
                                       (PRcons 2 0 z
                                               (PRnil 2))))
                       t in
  let f := evalPrimRec 2 x in
  let g := evalPrimRec 2 y in
  let h := evalPrimRec 2 z in
  let i := evalPrimRec 3 t in
  let j := evalPrimRec 2 u in
  forall a b, j a b = i (f a b) (g a b) (h a b).
Proof. reflexivity. Qed.

Example Ex5 (x : PrimRec 2)(y: PrimRec 4):
  let g := evalPrimRec _ x in
  let h := evalPrimRec _ y in
  let f := evalPrimRec _ (primRecFunc _ x y) in
  forall a b,  f 0 a b = g a b.
Proof. reflexivity.   Qed.                          

Example Ex6 (x : PrimRec 2)(y: PrimRec 4):
  let g := evalPrimRec _ x in
  let h := evalPrimRec _ y in
  let f := evalPrimRec _ (primRecFunc _ x y) in
  forall n a b,  f (S n) a b = h n (f n a b) a b.
Proof. reflexivity.   Qed.                          



Example bigPR : PrimRec 1 :=
primRecFunc 0
  (composeFunc 0 1 (PRcons 0 0 zeroFunc (PRnil 0)) succFunc)
  (composeFunc 2 2
    (PRcons 2 1
      (composeFunc 2 1
         (PRcons 2 0 (projFunc 2 1 (le_n 2))
                 (PRnil 2))
         succFunc)
      (PRcons 2 0
        (composeFunc 2 1
          (PRcons 2 0
             (projFunc 2 0
                       (le_S 1 1 (le_n 1)))
             (PRnil 2))
          (projFunc 1 0 (le_n 1))) (PRnil 2)))
    (primRecFunc 1 (composeFunc 1 0 (PRnil 1) zeroFunc)
       (composeFunc 3 2
         (PRcons 3 1
            (projFunc 3 1 (le_S 2 2 (le_n 2)))
            (PRcons 3 0 (projFunc 3 0
                          (le_S 1 2
                                (le_S 1 1 (le_n 1))))
                    (PRnil 3)))
         (primRecFunc 1 (projFunc 1 0 (le_n 1))
                      (composeFunc 3 1
                          (PRcons 3 0
                                  (projFunc 3 1 (le_S 2 2 (le_n 2)))
                                  (PRnil 3))
                          succFunc))))). 

Example  mystery_fun : nat -> nat := evalPrimRec 1 bigPR.


Compute map mystery_fun [0;1;2;3;4;5;6] : t nat _.


(** ** Understanding some constructions ...

 These lemmas are trivial and theoretically useless, but they may help to 
   make the construction more   concrete *)

Definition PRcompose1 (g f : PrimRec 1) : PrimRec 1 :=
  composeFunc 1  _ (PRcons _  _  f  (PRnil _) ) g.

Goal forall f g x, evalPrimRec 1 (PRcompose1 g f) x =
                 evalPrimRec 1 g (evalPrimRec 1 f x).
reflexivity. 
Qed.

(** Note : see lemma compose1_1IsPR  *)



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
  let phi :=  evalPrimRecFunc 0 a g
  in phi (S i)  = g i (phi i).
Proof. reflexivity. Qed.


Remark PrimRec_1_0 (f : nat->nat)(g : nat -> nat -> nat-> nat) :
  forall x,  evalPrimRecFunc 1 f g 0 x = f x.
Proof. reflexivity. Qed.

Remark PrimRec_1_S (f: nat->nat)
       (g : nat -> nat -> nat -> nat) (i:nat):
  let phi := evalPrimRecFunc 1  f g
  in forall x,  phi (S i) x = g i (phi i x) x.
Proof. reflexivity. Qed.

Remark PrimRec_2_0 (f : naryFunc 2) (g : naryFunc 4) :
  forall x y, evalPrimRecFunc 2 f g 0 x y = f x y.
Proof. reflexivity. Qed.

Remark PrimRec_2_S  (f: naryFunc 2) (g : naryFunc 4) (i:nat) :
  let phi := evalPrimRecFunc 2  f g
  in  forall x y,  phi (S i) x y = g i (phi i x y) x y.
Proof. reflexivity. Qed.


(** * First proofs of isPR statements 
      
  The module [Alt] presents proofs of lemma alreday proven in [primRec.v]
  We just hope that such a redundancy will help the reader to get familiar 
  with the various patterns allowed by that library.

*)

Lemma isPR_extEqual_trans n : forall f g, isPR n f ->
                                    extEqual n f g ->
                                    isPR n g.
Proof.
 intros f g [x Hx]; exists x.
 apply extEqualTrans with f; auto.
Qed.


Module Alt.
  
Lemma zeroIsPR : isPR 0 0.
Proof.
  exists zeroFunc.
  cbn.
  reflexivity.
Qed.  

Lemma SuccIsPR : isPR 1 S.
Proof.
  exists succFunc; cbn; reflexivity.
Qed.

Lemma pi2_5IsPR : isPR 5 (fun a b c d e => b).
Proof.
 assert (H: 3 < 5) by auto.
 exists (projFunc 5 3 H).
 cbn; reflexivity.
Qed.

Check composeFunc 0 1.

Fact compose_01 :
    forall (x:PrimRec 0) (t : PrimRec 1),
    let c := evalPrimRec 0 x in
    let f := evalPrimRec 1 t in
    evalPrimRec 0 (composeFunc 0 1
                               (PRcons 0 0 x (PRnil 0))
                               t)  =
     f c.
Proof. reflexivity. Qed.


Lemma  const0_NIsPR n : isPR 0 n. 
Proof.
  induction n.
 - apply zeroIsPR.
 - destruct IHn as [x Hx].
   exists (composeFunc 0 1 (PRcons 0 0 x (PRnil 0)) succFunc). 
   cbn in *; intros; now rewrite Hx.
Qed.


Search (isPR 2 (fun _ _ => nat_rec _ _ _ _)).

Definition plus_alt x y  :=
              nat_rec  (fun n : nat => nat)
                       y
                       (fun z t =>  S t)
                       x.

Lemma plus_alt_ok:
  extEqual 2 plus_alt plus.
Proof.
  intro x; induction x; cbn; auto.
  intros y; cbn; now rewrite <- (IHx y).
Qed.



Lemma plusIsPR : isPR 2 plus.
Proof.
  apply isPR_extEqual_trans with plus_alt.
  - unfold plus_alt; apply ind1ParamIsPR.
    + apply filter010IsPR, succIsPR.
    + apply idIsPR.
  - apply plus_alt_ok. 
Qed.







    







End Alt.


