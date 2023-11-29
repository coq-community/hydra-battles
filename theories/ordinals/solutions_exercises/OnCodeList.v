(* begin snippet membersDef:: no-out *)
From hydras.Ackermann Require Import primRec cPair.
From Coq Require Import Arith.
From Equations Require Import  Equations.

Equations members (a:nat): list nat by wf a:=
  members 0 := List.nil;
  members (S z) := cPairPi1 z:: members (cPairPi2 z).
(* end snippet membersDef *)
Next Obligation.
  apply Nat.le_lt_trans with z.
  apply cPairLe2A.
  apply le_n.
Defined.

Lemma membersOk n : n = codeList (members n).
Proof.
     pattern n, (members n); apply members_elim. 
      -  reflexivity. 
      -  intros; simpl; f_equal; rewrite <- H. 
         now rewrite cPairProjections.
Qed. 

Lemma membersOk' l : l = members (codeList l).
Proof.
  induction l. 
  - reflexivity.
   - cbn; rewrite IHl. 
     rewrite members_equation_2. 
     now rewrite cPairProjections1, cPairProjections2, <- !IHl.
Qed. 



  
