(** Languages :  Definitions of [LNT] and [LNN]

   Original development by Russel O'Connor *)

(** TO do : reorganize Alectryon snippets *)

From Coq Require Import Arith List.
Require Import fol primRec.

(**  * Language of Number Theory: [LNT] *)

(* begin snippet LNTDef1 *)
Inductive LNTFunction : Set :=
  | Plus_ : LNTFunction
  | Times_ : LNTFunction
  | Succ_ : LNTFunction
  | Zero_ : LNTFunction.


Inductive LNTRelation : Set :=.

Definition LNTFunctionArity (x : LNTFunction) : nat :=
  match x with
  | Plus_ => 2
  | Times_ => 2
  | Succ_ => 1
  | Zero_ => 0
  end.
(* end snippet LNTDef1 *)

(* begin snippet LNTDef2 *)

Definition LNTRelationR (x :  LNTRelation) : nat :=
  match x with bot => LNTRelation_rec (fun _ => nat) bot end.

Definition LNT : Language := language LNTRelation  LNTFunction LNTRelationR LNTFunctionArity.
(* end snippet LNTDef2 *)

(** * Language of Natural Numbers: [LNN] 
     Its functions are also [LNT]'s 
*)

(* begin snippet LNNDef *)

Inductive LNNRelation : Set :=
    LT_ : LNNRelation.

Definition LNNArityR (x : LNNRelation) : nat :=
 match x with LT_ => 2 end.

Definition LNNArityF (f : LNTFunction) :=
     LNTFunctionArity f.

Definition LNN : Language := language LNNRelation LNTFunction 
                               LNNArityR LNNArityF.

(* end snippet LNNDef *)

(** * Goedel encoding for LNT *)

(** This function is also used as encoding for [LNN]  *)

Definition codeLNTFunction (f : LNTFunction) : nat :=
  match f with
  | Plus_ => 0
  | Times_ => 1
  | Succ_ => 2
  | Zero_ => 3
  end.

Definition codeLNTRelation (R : LNTRelation) : nat :=
  match R return nat with
  end.

Lemma codeLNTFunctionInj :
 forall f g : LNTFunction, codeLNTFunction f = codeLNTFunction g -> f = g.
Proof.
  intros f g H; destruct f; destruct g; reflexivity || discriminate H.
Qed.


Lemma codeLNTRelationInj :
 forall R S : LNTRelation, codeLNTRelation R = codeLNTRelation S -> R = S.
Proof.
  intros R S H;
    destruct R; destruct S; reflexivity || discriminate H.
Qed.

Definition codeArityLNTR (r : nat) := 0.

Lemma codeArityLNTRIsPR : isPR 1 codeArityLNTR.
Proof.
  unfold codeArityLNTR; apply const1_NIsPR.
Qed.

Lemma codeArityLNTRIsCorrect1 :
 forall r : Relations LNT,
 codeArityLNTR (codeLNTRelation r) = S (arityR LNT r).
Proof. simple induction r. Qed.

Lemma codeArityLNTRIsCorrect2 :
 forall n : nat,
 codeArityLNTR n <> 0 -> exists r : Relations LNT, codeLNTRelation r = n.
Proof.  destruct 1; easy. Qed.

Definition codeArityLNTF (f : nat) :=
  switchPR f
    (switchPR (pred f)
       (switchPR (pred (pred f)) (switchPR (pred (pred (pred f))) 0 1) 2) 3)
    3.

Lemma codeArityLNTFIsPR : isPR 1 codeArityLNTF.
Proof.
  set
    (f :=
       list_rec (fun _ => nat -> nat -> nat) (fun _ _ : nat => 0)
         (fun (a : nat) (l : list nat) (rec : nat -> nat -> nat) (n f : nat) =>
            switchPR (iterate pred n f) (rec (S n) f) a)) 
    in *.
  assert (H: forall (l : list nat) (n : nat), isPR 1 (f l n)). 
  { induction l as [| a l Hrecl]; intros.
    - simpl; apply const1_NIsPR.
    - simpl; apply
               compose1_3IsPR
        with
        (f1 := fun f0 : nat => iterate pred n f0)
        (f2 := fun f0 : nat => f l (S n) f0)
        (f3 := fun f0 : nat => a).
      + apply iterateIsPR with (g := pred) (n := n).
        apply predIsPR.
      + apply Hrecl with (n := S n).
      + apply const1_NIsPR.
      + apply switchIsPR.
  } apply (H (3 :: 3 :: 2 :: 1 :: nil) 0).
Qed.

Lemma codeArityLNTFIsCorrect1 :
 forall f : Functions LNT,
 codeArityLNTF (codeLNTFunction f) = S (arityF LNT f).
Proof. induction f; reflexivity. Qed.

Lemma codeArityLNNFIsCorrect1 :
 forall f : Functions LNN,
 codeArityLNTF (codeLNTFunction f) = S (arityF LNN  f).
Proof. apply codeArityLNTFIsCorrect1. Qed.

Lemma codeArityLNTFIsCorrect2 :
 forall n : nat,
 codeArityLNTF n <> 0 -> 
 exists f : Functions LNT, codeLNTFunction f = n.
Proof.
  intros n H; destruct n as [| n].
  - exists Plus_; easy. 
  - destruct n as [| n].
    + exists Times_; easy.
    + destruct n as [| n].
      * exists Succ_; easy.
      * destruct n as [| n].
        -- exists Zero_; easy.
        -- destruct H; reflexivity.
Qed.


(** * Goedel encoding for LNN  *)

Definition codeLNNRelation (R : LNNRelation) : nat := 0.

Lemma codeLNNRelationInj :
 forall R S : LNNRelation, codeLNNRelation R = codeLNNRelation S -> R = S.
Proof.
  intros R S H;
    destruct R; destruct S; reflexivity || discriminate H.
Qed.

Definition codeArityLNNR (r : nat) := switchPR r 0 3.

Lemma codeArityLNNRIsPR : isPR 1 codeArityLNNR.
Proof.
  unfold codeArityLNNR in |- *;
    apply compose1_3IsPR with
    (f1 := fun r : nat => r)
    (f2 := fun r : nat => 0)
    (f3 := fun r : nat => 3).
  - apply idIsPR.
  - apply const1_NIsPR.
  - apply const1_NIsPR.
  - apply switchIsPR.
Qed.

Lemma codeArityLNNRIsCorrect1 :
  forall r : Relations LNN,
    codeArityLNNR (codeLNNRelation r) = S (arityR LNN r).
Proof. destruct r; reflexivity. Qed.

Lemma codeArityLNNRIsCorrect2 :
 forall n : nat,
 codeArityLNNR n <> 0 -> exists r : Relations LNN, codeLNNRelation r = n.
Proof.
  intros n H; destruct n.
  - exists LT_; reflexivity.
  - now destruct H.
Qed.

Lemma codeArityLNNFIsCorrect2 :
  forall n : nat,
    codeArityLNTF n <> 0 -> exists f : Functions LNN, codeLNTFunction f = n.
Proof.
  apply codeArityLNTFIsCorrect2.
Qed.





