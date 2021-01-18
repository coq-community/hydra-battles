Require Import primRec Arith ArithRing List.
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


Example weirdPR : PrimRec 1 :=
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

Example  mystery_fun : nat -> nat := evalPrimRec 1 weirdPR.

Compute List.map mystery_fun (0::1::2::3::4::5::6::nil) : list nat.

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


(** * First proofs of isPR statements *)

Lemma zeroIsPR : isPR 0 0.
Proof.
  exists zeroFunc; reflexivity.
Qed.  

Lemma SIsPR : isPR 1 S.
Proof.
  exists succFunc; cbn; reflexivity.
Qed.

Lemma pi2_5IsPR : isPR 5 (fun a b c d e => b).
Proof.
 assert (H: 3 < 5) by auto.
 exists (projFunc 5 3 H).
 cbn; reflexivity.
Qed.




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
Defined.


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



