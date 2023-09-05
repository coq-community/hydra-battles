Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import code.
Require Import folProp.
Require Import folProof.
Require Import Languages.
Require LNN. 
Require LNT.

Definition natToTermLNN := LNN.natToTerm.

Definition natToTermLNT := LNT.natToTerm.

Fixpoint codeNatToTerm (n: nat) : nat :=
 match n with
  0 => cPair 4 0
| S p => cPair 3 (S (cPair (codeNatToTerm p) 0))
end. 

#[global] Instance LcodeLNN : Lcode LNN codeLNTFunction codeLNNRelation.
Proof.
  split.
  - apply codeLNTFunctionInj.
  - apply codeLNNRelationInj.   
Defined.  


#[global] Instance LcodeLNT : Lcode LNT codeLNTFunction codeLNTRelation.
Proof.
  split.
  - apply codeLNTFunctionInj.
  - apply codeLNTRelationInj.   
Defined.  

Lemma codeNatToTermCorrectLNN n :
 codeNatToTerm n = codeTerm (natToTermLNN n).
Proof.
  induction n as [| n Hrecn].
  - reflexivity.
  - simpl; now rewrite Hrecn.
Qed.

Lemma codeNatToTermCorrectLNT n :
 codeNatToTerm n = codeTerm  (natToTermLNT n).
Proof.
  induction n as [| n Hrecn].
  - reflexivity.
  - simpl; now rewrite Hrecn.
Qed.

Lemma codeNatToTermIsPR : isPR 1 codeNatToTerm.
Proof.
  unfold codeNatToTerm in |- *.
  apply indIsPR with 
    (f := fun _ rec : nat => cPair 3 (S (cPair rec 0))) 
    (g := cPair 4 0).
  apply filter01IsPR with 
    (g := fun rec : nat => cPair 3 (S (cPair rec 0))).
  apply compose1_2IsPR with 
    (f := fun _ : nat => 3)
    (f' := fun rec : nat => S (cPair rec 0)).
  - apply const1_NIsPR.
  - apply compose1_1IsPR with (f := fun rec : nat => cPair rec 0).
    + apply compose1_2IsPR with 
        (f := fun rec : nat => rec) 
        (f' := fun _ : nat => 0).
      * apply idIsPR.
      * apply const1_NIsPR.
      * apply cPairIsPR.
    + apply succIsPR.
  - apply cPairIsPR.
Qed.
