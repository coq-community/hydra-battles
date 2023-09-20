From hydras.Ackermann Require Import expressible.

Require Import NN. 
Require Import NewNotations NNtheory. 
Import NNnotations.
From Coq Require Import Lia. 

Goal forall n, RepresentableHalf1 NN 0 n (v#0 = natToTerm n)%nn. 
Proof. 
  intro n; red; apply impRefl. 
Qed. 

Lemma L1:   RepresentableHalf1 NN 1 (fun n => n + n) 
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

Lemma L2:  RepresentableHalf2 NN 1 (fun n => n + n) 
  (v#0 = v#1 + v#1)%nn. 
Proof. 
  intro a; simpl. 
   pose (H:= natPlus a a). 
   unfold substF; simpl.
   apply impI.   
   apply eqTrans with (natToTerm (a + a)).
   - apply sysExtend with (Ensembles.Singleton _
                           (v#0 = natToTerm (a + a))%nn).
     + right.  assumption.
     +  apply Axm; split. 
   - eapply sysExtend with NN.
     + left; assumption. 
     + apply eqSym. apply H.
Qed. 

Lemma L3:  Representable NN 1 (fun n => n + n)   (v#0 = v#1 + v#1)%nn. 
Proof.  
 split. 
 simpl. 
 lia.
  apply RepresentableHalfHelp.  
  apply L1. 
   apply L2.
 Qed. 

Lemma L4 : Representable NN 1 (fun n => n * 2)  (v#0 = v#1 + v#1)%nn.
Proof. 
 split. 
  simpl; lia.
   apply Representable_ext with (fun n => n + n). 
   - intro n.  simpl. lia. 
   - apply L3.
Qed. 
