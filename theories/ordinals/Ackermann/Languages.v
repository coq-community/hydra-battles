
Require Import Arith.
Require Import fol.
Require Import primRec.
Require Import Coq.Lists.List.
Require Import cPair.
Import CodeAbbreviations.

(* begin snippet LNTDef1 *)
Inductive LNTFunction : Set :=
  | Plus : LNTFunction
  | Times : LNTFunction
  | Succ : LNTFunction
  | Zero : LNTFunction.

Inductive LNNRelation : Set :=
    LT : LNNRelation.

Definition LNTFunctionArity (x : LNTFunction) : nat :=
  match x with
  | Plus => 2
  | Times => 2
  | Succ => 1
  | Zero => 0
  end.
(* end snippet LNTDef1 *)

(* begin snippet LNTDef2 *)
Definition LNTArity (x : Empty_set + LNTFunction) : nat :=
  match x return nat with
  | inl bot => Empty_set_rec (fun _ => nat) bot
  | inr y => LNTFunctionArity y
  end.


Definition LNNArity (x : LNNRelation + LNTFunction) : nat :=
  match x return nat with
  | inl y => match y with
             | LT => 2
             end
  | inr y => LNTFunctionArity y
  end.

Definition LNT : Language := language Empty_set LNTFunction LNTArity.

Definition LNN : Language := language LNNRelation LNTFunction LNNArity.
(* end snippet LNTDef2 *)



Definition codeLNTFunction (f : LNTFunction) : nat :=
  match f with
  | Plus => 0
  | Times => 1
  | Succ => 2
  | Zero => 3
  end.

Definition codeLNTRelation (R : Empty_set) : nat :=
  match R return nat with
  end.

Definition codeLNNRelation (R : LNNRelation) : nat := 0.

Lemma codeLNTFunctionInj :
 forall f g : LNTFunction, codeLNTFunction f = codeLNTFunction g -> f = g.
Proof.
  intros f g H; destruct f; destruct g; reflexivity || discriminate H.
Qed.

Lemma codeLNTRelationInj :
 forall R S : Empty_set, codeLNTRelation R = codeLNTRelation S -> R = S.
Proof.
  intros R S H;
    destruct R; destruct S; reflexivity || discriminate H.
Qed.

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
    codeArityLNNR (codeLNNRelation r) = S (arity LNN (inl _ r)).
Proof. destruct r; reflexivity. Qed.

Lemma codeArityLNNRIsCorrect2 :
 forall n : nat,
 codeArityLNNR n <> 0 -> exists r : Relations LNN, codeLNNRelation r = n.
Proof.
  intros n H; destruct n.
  - exists LT; reflexivity.
  - now destruct H.
Qed.

Definition codeArityLNTR (r : nat) := 0.

Lemma codeArityLNTRIsPR : isPR 1 codeArityLNTR.
Proof.
  unfold codeArityLNTR; apply const1_NIsPR.
Qed.

Lemma codeArityLNTRIsCorrect1 :
 forall r : Relations LNT,
 codeArityLNTR (codeLNTRelation r) = S (arity LNT (inl _ r)).
Proof. simple induction r. Qed.

Lemma codeArityLNTRIsCorrect2 :
 forall n : nat,
 codeArityLNTR n <> 0 -> exists r : Relations LNT, codeLNTRelation r = n.
Proof.  destruct 1; easy. Qed.

Definition codeArityLNTF (f : nat) :=
  switchPR f
    (switchPR (pred f)
       (switchPR (pred2 f) (switchPR (pred3 f) 0 1) 2) 3)
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
 codeArityLNTF (codeLNTFunction f) = S (arity LNT (inr _ f)).
Proof. induction f; reflexivity. Qed.

Lemma codeArityLNNFIsCorrect1 :
 forall f : Functions LNN,
 codeArityLNTF (codeLNTFunction f) = S (arity LNN (inr _ f)).
Proof. apply codeArityLNTFIsCorrect1. Qed.

Lemma codeArityLNTFIsCorrect2 :
 forall n : nat,
 codeArityLNTF n <> 0 -> exists f : Functions LNT, codeLNTFunction f = n.
Proof.
  intros n H; destruct n as [| n].
  - exists Plus; easy. 
  - destruct n as [| n].
    + exists Times; easy.
    + destruct n as [| n].
      * exists Succ; easy.
      * destruct n as [| n].
        -- exists Zero; easy.
        -- destruct H; reflexivity.
Qed.

Lemma codeArityLNNFIsCorrect2 :
  forall n : nat,
    codeArityLNTF n <> 0 -> exists f : Functions LNN, codeLNTFunction f = n.
Proof.
  apply codeArityLNTFIsCorrect2.
Qed.





