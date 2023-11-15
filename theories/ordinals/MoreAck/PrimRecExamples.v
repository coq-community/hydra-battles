Require Import Arith ArithRing List.
Require Import Vector.
Require Import Utf8.
Import VectorNotations.

Require Import primRec cPair.
Import extEqualNat.
Import PRNotations.
(* begin snippet naryFunc3 *)
Compute naryFunc 3.
(* end snippet naryFunc3 *)



(* begin snippet naryRel2 *)
Check leBool : naryRel 2.

Compute leBool 4 5.

Compute charFunction 2 leBool 4 5.

Compute charFunction 2 ltBool 7 7.

(* end snippet naryRel2 *)

(* begin snippet checknaryFunc *)

(*|
.. coq:: no-out
|*)

Check plus: naryFunc 2.

Check 42: naryFunc 0.

Check (fun n p q : nat =>  n * p + q): naryFunc 3.

(*||*)

(* end snippet checknaryFunc *)

(* begin snippet extEqual2a *)
Compute extEqual 2.


Example extEqual_ex1: extEqual 2 Nat.mul (fun x y =>  y * x + x - x). (* .no-out *)
Proof. 
  intros x y; cbn.
(* end snippet extEqual2a *)
  
(* begin snippet extEqual2b *)  
  rewrite <- Nat.add_sub_assoc, Nat.sub_diag.
  - (* .no-out *) ring.
  - (* .no-out *) apply le_n.  
Qed.
(* end snippet extEqual2b *)

(** ** Examples of terms of type [PrimRec n] and their interpretation *)

(* begin snippet evalPrimRecEx  *)
(*|
.. coq:: no-out
|*)

Example Ex1 : PReval zeroFunc = 0.
Proof. reflexivity. Qed.

Example Ex2 a : PReval succFunc a = S a.
Proof. reflexivity. Qed.

Example Ex3 a b c d e f: forall (H: 2 < 6),
    PReval (projFunc 6 2 H) a b c d e f = d.
Proof. reflexivity. Qed.

Example Ex4 : extEqual 4 (fun a b c d: nat => 0)
                         (PReval (PRcomp zeroFunc (PRnil _))). 
Proof.  simpl; reflexivity. Qed. 

Section Composition.

  Variables (x y z : PrimRec 2) (t: PrimRec 3).
  Let u : PrimRec 2 := composeFunc 2 3 [x; y; z]%pr t.
  Let f := PReval x.
  Let g := PReval y.
  Let h := PReval z.
  Let k := PReval t.
 Goal forall n p, PReval u n p = k (f n p) (g n p) (h n p).
 Proof. reflexivity. Qed.

  Let v := (PRcomp t  [ pi1_2 ; pi1_2; pi2_2 ])%pr.

  Eval simpl in PReval v. 

End Composition.

Section Primitive_recursion. 
 Variables (x: PrimRec 2)(y: PrimRec 4).
 Let z := (primRecFunc _ x y).
 Let g := PReval x.
 Let h := PReval y.  
 Let f := PReval z.
 Goal forall a b, f 0 a b = g a b.
 Proof. reflexivity. Qed. 

 Goal forall n a b, f n.+1 a b = h n (f n a b) a b.
 Proof. reflexivity. Qed. 

End Primitive_recursion. 

(* end snippet evalPrimRecEx  *)  

Section compose2Examples.
Variables (f: naryFunc 1) (g: naryFunc 2).
Eval simpl in compose2 1 f g.
Variable (h: naryFunc 3). 
Eval simpl in compose2 2 g h. 
Variables (f': naryFunc 4) (g': naryFunc 5).
Eval simpl in compose2 _ f' g'.
End compose2Examples.


(* begin snippet FirstExamples *)
Module MoreExamples. 

(** The constant function which returns 0 *)
Definition cst0 : PrimRec 1 := (PRcomp zeroFunc (PRnil _))%pr.

(** The constant function which returns i *)
Fixpoint cst (i: nat) : PrimRec 1 :=
  match i with
    0 => cst0
  | S j => (PRcomp succFunc [cst j])%pr
end.

Compute cst 7.

(** Addition *)
Definition plus : PrimRec 2 := 
  (PRrec pi1_1 (PRcomp succFunc [pi2_3]))%pr.

(** Multiplication *)
Definition mult : PrimRec 2 :=
  PRrec cst0
    (PRcomp plus [pi2_3; pi3_3]%pr).

(** Factorial function *)
Definition fact : PrimRec 1 := 
  (PRrec
     (PRcomp succFunc [zeroFunc])
     (PRcomp mult [pi2_2; PRcomp succFunc [pi1_2]]))%pr.

End MoreExamples.
(* end snippet FirstExamples *)

Import MoreExamples.

(* begin snippet tests *)

Compute  PReval pi2_3 10 20 30.

Compute  Vector.map (fun f => f 10 20 30)  (PRevalN [pi2_3; pi1_3]%pr).

Compute PReval cst0 42.

Compute PReval (cst 7) 19.

Compute PReval plus 9 4.

Compute PReval mult 9 4.

Compute PReval fact 5.

(* end snippet tests *)

(* begin snippet correctness:: no-out *)
Lemma cst0_correct (i:nat) :
  forall p:nat, PReval cst0 p = 0.
Proof. intro p; reflexivity. Qed.

Lemma cst_correct (i:nat) :
  forall p:nat, PReval (cst i) p = i.
Proof.
  induction i as [| i IHi]; simpl; intros p .
  - reflexivity. 
  - now rewrite IHi. 
Qed. 

Lemma plus_correct: 
  forall n p, PReval plus n p = n + p. 
Proof. 
  induction n as [ | n IHn]. 
  - reflexivity. 
  - intro p; cbn in IHn |- *; now rewrite IHn. 
Qed. 

Remark mult_eqn1 n p: 
    PReval mult (S n) p = 
      PReval plus (PReval mult n p) p.
Proof. reflexivity. Qed.

Lemma mult_correct n p: PReval mult n p = n * p.
Proof. 
 revert p; induction n as [ | n IHn].
 - intro p; reflexivity. 
 - intro p; rewrite mult_eqn1, IHn, plus_correct; ring.
Qed.      


Lemma fact_correct n : PReval fact n  = Coq.Arith.Factorial.fact n.
(* ... *)
(* end snippet correctness *)
Proof. 
  assert (fact_eqn1: forall n, PReval fact (S n)  = 
                                 PReval mult
                                   (PReval fact n) (S n))
    by  reflexivity. 
  induction n as [| n IHn].
  - reflexivity. 
  - rewrite fact_eqn1, mult_correct, IHn; cbn; ring. 
Qed. 




(** ** Understanding some constructions ...

 These lemmas are trivial and theoretically useless, but they may help to 
   make the construction more   concrete *)

Definition PRcompose1 (g f : PrimRec 1) : PrimRec 1 :=
  PRcomp g [f]%pr.  

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
      
  The module [Alt] presents proofs of lemmas already proven in [primRec.v]
  We just hope that such a redundancy will help the reader to get familiar 
  with the various patterns allowed by that library.
*)

Module Alt.
  
(* begin snippet zeroIsPR *)

#[export] Instance zeroIsPR : isPR 0 0. (* .no-out *)
Proof. (* .no-out *)
  exists zeroFunc.
  cbn.
  reflexivity.
Qed.  

(* end snippet zeroIsPR *)

(* begin snippet SuccIsPR *)

(*|
.. coq:: no-out
|*)

#[export] Instance succIsPR : isPR 1 S.
Proof.
  exists succFunc; cbn; reflexivity.
Qed.

#[export] Instance addIsPR : isPR 2 Nat.add. 
Proof. exists plus; intros n p; apply plus_correct. Qed.

(* end snippet SuccIsPR *)



  
(* begin snippet pi25IsPR *)

(*|
.. coq:: no-out
|*)

#[export] Instance pi2_5IsPR : isPR 5 (fun a b c d e => b).
Proof.
 assert (H: 3 < 5) by auto.
 exists (projFunc 5 3 H).
 cbn; reflexivity.
Qed.

(*||*)

(* end snippet pi25IsPR *)

Check composeFunc 0 1.

(* begin snippet compose01 *)

(*| 
.. coq:: no-out 
|*)

Remark compose_01  (x:PrimRec 0) (t : PrimRec 1) :
    PReval (PRcomp t [x])%pr = PReval t (PReval x).
Proof. reflexivity. Qed.
(*||*)

(* end snippet compose01 *)

(* begin snippet const0NIsPR  *)

#[export] Instance  const0_NIsPR n : isPR 0 n. (* .no-out *)
Proof. (* .no-out *)
  induction n. (* .no-out *)
   - apply zeroIsPR. (* .no-out *)
   - destruct IHn as [x Hx].
     exists (PRcomp succFunc [x])%pr; cbn in *; intros; 
       now rewrite Hx.
Qed.
(* end snippet const0NIsPR  *)



(* begin snippet PRnatRecSearch *)
Search (isPR 2 (fun _ _ => nat_rec _ _ _ _)).
(* end snippet PRnatRecSearch *)

(* begin snippet isPRextEqual *)
Check isPRextEqual.
(* end snippet isPRextEqual *)

(* begin snippet checkFilter0101IsPR *)

(*|
.. coq:: unfold no-in 
|*)

Check filter010IsPR.

(*||*)

(* end snippet checkFilter0101IsPR *)

(* begin snippet plusIsPRa *)
Definition add' x y :=
  nat_rec (fun n : nat => nat)
    y
    (fun z t =>  S t)
    x.

(*| 
.. coq:: no-out 
|*)
Lemma add'_ok:
  extEqual 2 add' Nat.add.
Proof.
  intro x; induction x; cbn; auto.
  intro y; cbn; now rewrite <- (IHx y).
Qed.

(* end snippet plusIsPRa *)

(* begin snippet plusIsPRa1 *)
#[export] Instance addIsPR' : isPR 2 Nat.add. (* .no-out *)
Proof. 
(* end snippet plusIsPRa1 *)
  
(* begin snippet plusIsPRa2 *)
  apply isPRextEqual with add'. 
  - unfold add'; apply ind1ParamIsPR.
(* end snippet plusIsPRa2 *)

(* begin snippet plusIsPRa3 *)
    + Search (isPR 1 _ -> isPR 3 _). 
      apply filter010IsPR, succIsPR.
(* end snippet plusIsPRa3 *)

(* begin snippet plusIsPRb:: no-out *)
    + apply idIsPR.
  - apply add'_ok. 
Qed.

(*||*)
(* end snippet plusIsPRb *)

(* begin snippet xpred *)
Definition xpred := primRecFunc 0 zeroFunc pi1_2.
  
Compute evalPrimRec 1 xpred 10.

#[export] Instance predIsPR : isPR 1 Nat.pred. (* .no-out *)
Proof. (* .no-out *)
  exists xpred; intro n; induction n; now cbn. 
Qed.
(* end snippet xpred *)

End Alt.

(* begin snippet doubleIsPRa *)

Definition double (n:nat) := 2 * n.

#[export] Instance doubleIsPR : isPR 1 double. (* .no-out *)
Proof. (* .no-out *)
  unfold double; apply compose1_2IsPR. 
  (* end snippet doubleIsPRa *)
  
(* begin snippet doubleIsPRb:: no-out *)  
  - apply const1_NIsPR.
  - apply idIsPR.
  - apply multIsPR.
Qed.
(* end snippet doubleIsPRb *)

(** using cPair *)

(* Move to MoreAck *)

Section Exs. (* Todo: exercise *)
Let f: naryFunc 2 := fun x y => x + pred (cPairPi1 y).

  (* To prove !!! *)
  
  Let ffib : naryFunc 2 :=
        fun c A =>
          match c with
            0 | 1 => 1
          | _ => codeNth 0 A + codeNth 1 A
          end.
  (* begin snippet fdiv2Def *)
  Let fdiv2 : naryFunc 2 :=
        fun (n acc: nat) =>
          match n with
            0 | 1 => 0
          | _ => S (codeNth 1 acc)
          end.
    (* end snippet fdiv2Def *)

  (* begin snippet fdiv2Examples *)
  Compute evalStrongRec _ fdiv2 0.
  Compute evalStrongRec _ fdiv2 2.
  Compute evalStrongRec _ fdiv2 3.
  Compute evalStrongRec _ fdiv2 4.
  (* end snippet fdiv2Examples *)
  
  Compute evalStrongRec _ ffib 1.
  Compute evalStrongRec _ ffib 2.
  Compute evalStrongRec _ ffib 3.
  
  
  Compute  listValues ffib 4.
   
End Exs.

