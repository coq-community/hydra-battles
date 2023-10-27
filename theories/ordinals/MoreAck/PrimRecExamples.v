Require Import Arith ArithRing List.
Require Import Vector.
Require Import Utf8.
Import VectorNotations.

(* begin snippet naryFunc3 *)

Require Import primRec cPair.
Import extEqualNat.
Import PRNotations.
Compute naryFunc 3.

(* end snippet naryFunc3 *)



(* begin snippet naryRel2 *)

Compute naryRel 2.

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


Example extEqual_ex1: extEqual 2 mult (fun x y =>  y * x + x - x). (* .no-out *)
Proof. (* .no-out *)
  intros x y.
  cbn.
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

Example Ex1 : evalPrimRec 0 zeroFunc = 0.
Proof. reflexivity. Qed.

Example Ex2 a : evalPrimRec 1 succFunc a = S a.
Proof. reflexivity. Qed.

Example Ex3 a b c d e f: forall (H: 2 < 6),
    evalPrimRec 6
                (projFunc 6 2 H) a b c d e f = d.
Proof. reflexivity. Qed.


Example Ex4 (x y z : PrimRec 2) (t: PrimRec 3):
  let u := composeFunc 2 3 [x; y; z]%pr t                   
  in  forall a b, evalPrimRec 2 u a b =
                    evalPrimRec  _ t 
                      (evalPrimRec _ x a b)
                      (evalPrimRec _ y a b)
                      (evalPrimRec _ z a b) .
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
  forall n a b, f (S n) a b = h n (f n a b) a b.
Proof. reflexivity.   Qed.                          
(* end snippet evalPrimRecEx  *)  


Module MoreExamples. 
(* begin snippet cst0 *)

(** The constant function which returns 0 *)
Definition cst0 : PrimRec 1 := composeFunc 1 0 []%pr zeroFunc.

Compute evalPrimRec _ cst0 42.

(* end snippet cst0 *)

(** Addition *)
(* begin snippet addition *)

Check (projFunc 3 1).

Compute fun H : 1 < 3 => evalPrimRec _ (projFunc 3 1 H).

Compute (evalPrimRec _ pi2_3) 1 2 3.
(*| 
.. coq:: no-out 
|*)

Check  [pi2_3]%pr.

Definition plus := (PRrec pi1_1
                      (PRcomp succFunc [pi2_3]))%pr.

Compute evalPrimRec _ plus 3 6.

Lemma plus_correct: 
  forall n p, evalPrimRec _ plus n p = n + p. (* .no-out *)
Proof. (* .no-out *) 
  induction n as [ | n IHn]. (* .no-out *) 
  - reflexivity. 
  - intro p; cbn in IHn |- *; now rewrite IHn. 
Qed. 
(* end snippet addition *)

(* begin snippet multiplication:: no-out *)
                   
Definition mult := PRrec cst0
                      (PRcomp plus 
                         [pi2_3; pi3_3]%pr).

Compute evalPrimRec _ mult 4 5.
Compute evalPrimRec _ mult 4 9.

Lemma mult_eqn1 n p: 
    evalPrimRec _ mult (S n) p = 
      evalPrimRec _ plus (evalPrimRec _ mult n p) p.
Proof. reflexivity. Qed.

Lemma mult_correct n p: evalPrimRec _ mult n p = n * p.
Proof. 
 revert p; induction n as [ | n IHn].
 - intro p; reflexivity. 
 - intro p; rewrite mult_eqn1, IHn, plus_correct; ring.
Qed.      

(* end snippet multiplication *)

(* begin snippet factorial:: no-out *)
Remark R23 : 2 < 3.
Proof. auto. Qed. 

Remark R02 : 0 < 2.
Proof. auto. Qed.

Remark R12 : 1 < 2. 
Proof. auto. Qed.


Definition fact := (PRrec
                      (PRcomp succFunc [zeroFunc])
                      (PRcomp mult [pi2_2; PRcomp succFunc [pi1_2]]))%pr.

(** A test *)
Compute evalPrimRec _ fact 5.

(** A correction proof *)
Fixpoint usual_fact n :=
 match n with 
 | 0 => 1
 | S p => n * usual_fact p
end.

Lemma fact_correct n : evalPrimRec _ fact n  = usual_fact n.
Proof. 
  assert (fact_eqn1: forall n, evalPrimRec _ fact  (S n)  = 
                                 evalPrimRec _ mult
                                   (evalPrimRec _ fact n) (S n))
    by  reflexivity. 
  induction n as [ | n IHn].
  - reflexivity. 
  - rewrite fact_eqn1, mult_correct, IHn; cbn; ring. 
Qed. 
(* end snippet factorial *)

End MoreExamples.

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

Fact compose_01 :
    forall (x:PrimRec 0) (t : PrimRec 1),
    let c := evalPrimRec 0 x in
    let f := evalPrimRec 1 t in
    evalPrimRec 0 (PRcomp t [x])%pr
    = f c. 
Proof. reflexivity. Qed.
(*||*)

(* end snippet compose01 *)

(* begin snippet const0NIsPR  *)

(*| 
.. coq:: no-out 
|*)


#[export] Instance  const0_NIsPR n : isPR 0 n. 
Proof.
  induction n.
 - apply zeroIsPR.
 - destruct IHn as [x Hx].
   exists (PRcomp succFunc [x])%pr.
   cbn in *; intros; now rewrite Hx.
Qed.

(*||*)

(* end snippet const0NIsPR  *)

(* begin snippet plusAlt  *)

(*| 
.. coq:: no-out 
|*)

Definition plus_alt x y  :=
              nat_rec  (fun n : nat => nat)
                       y
                       (fun z t =>  S t)
                       x.

Lemma plus_alt_ok:
  extEqual 2 plus_alt Nat.add.
Proof.
  intro x; induction x; cbn; auto.
  intros y; cbn; now rewrite <- (IHx y).
Qed.

(*||*)

(* end snippet plusAlt *)


(* begin snippet PrimRecExamplesSearch *)

Search (isPR 2 (fun _ _ => nat_rec _ _ _ _)).

(* end snippet PrimRecExamplesSearch *)

(* begin snippet checkFilter0101IsPR *)

(*|
.. coq:: unfold no-in 
|*)

Check filter010IsPR.

(*||*)

(* end snippet checkFilter0101IsPR *)

(* begin snippet plusIsPRa *)

#[export] Instance plusIsPR : isPR 2 Nat.add. (* .no-out *)
Proof. (* .no-out *)
  apply isPRextEqual with plus_alt.
  - (* .no-out *)  unfold plus_alt; apply ind1ParamIsPR.
    
(* end snippet plusIsPRa *)

(* begin snippet plusIsPRb *)
    
(*|
.. coq:: no-out 
|*)

    + apply filter010IsPR, succIsPR.
    + apply idIsPR.
  - apply plus_alt_ok. 
Qed.

(*||*)

(* end snippet plusIsPRb *)



Remark R02 : 1 < 2.
Proof. auto. Qed.

Definition xpred := primRecFunc 0 zeroFunc (projFunc 2 1 R02).
  
Compute evalPrimRec 1 xpred 10.



#[export] Instance predIsPR : isPR 1 pred.
Proof.
  exists xpred.
  intro n; induction n; now cbn. 
Qed.


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

