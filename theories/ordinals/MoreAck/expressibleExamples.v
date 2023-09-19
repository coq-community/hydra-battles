From hydras.Ackermann Require Import expressible.

Require Import NN. 
Require Import NewNotations NNtheory. 
Import NNnotations.

Goal forall n, RepresentableHalf1 NN 0 n (v#0 = natToTerm n)%nn. 
Proof. 
  intro n; red; apply impRefl. 
Qed. 

Goal  RepresentableHalf1 NN 1 (fun n => n + n) 
  (v#0 = v#1 + v#1)%nn. 
Proof. 
  intro a; simpl. 
   pose (H:= natPlus a a). 
   unfold substF; simpl.
   apply impI.   
   apply eqTrans with (natToTerm a + natToTerm a)%nn. 
   - apply sysExtend with (Ensembles.Singleton _
                           (v#0 = natToTerm a + natToTerm a)%nn).
     + right; assumption.
     +  apply Axm; split. 
   - eapply sysExtend with NN.
     + left; assumption. 
     + apply H.
Qed. 


 
