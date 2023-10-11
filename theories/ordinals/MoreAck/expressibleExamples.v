From hydras.Ackermann Require Import expressible.

Require Import NN. 
Require Import NewNotations NNtheory. 
Import NNnotations.
From Coq Require Import Lia. 

Goal forall n, RepresentableHalf1 NN 0 n (v#0 = natToTerm n)%fol. 
Proof. 
  intro n; red; apply impRefl. 
Qed. 

Lemma L1:   RepresentableHalf1 NN 1 (fun n => n + n) 
  (v#0 = v#1 + v#1)%fol. 
Proof. 
  intro a; simpl. 
   pose (H:= natPlus a a). 
   unfold substF; simpl.
   apply impI.   
   apply eqTrans with (natToTerm a + natToTerm a)%fol. 
   - apply sysExtend with (Ensembles.Singleton _
                           (v#0 = natToTerm a + natToTerm a)%fol).
     + right; assumption.
     +  apply Axm; split. 
   - eapply sysExtend with NN.
     + left; assumption. 
     + apply H.
Qed. 

Lemma L2:  RepresentableHalf2 NN 1 (fun n => n + n) 
  (v#0 = v#1 + v#1)%fol. 
Proof. 
  intro a; simpl. 
   pose (H:= natPlus a a). 
   unfold substF; simpl.
   apply impI.   
   apply eqTrans with (natToTerm (a + a)).
   - apply sysExtend with (Ensembles.Singleton _
                           (v#0 = natToTerm (a + a))%fol).
     + right.  assumption.
     +  apply Axm; split. 
   - eapply sysExtend with NN.
     + left; assumption. 
     + apply eqSym. apply H.
Qed. 

Lemma L3:  Representable NN 1 (fun n => n + n)   (v#0 = v#1 + v#1)%fol. 
Proof.  
 split. 
 simpl. 
 lia.
  apply RepresentableHalfHelp.  
  apply L1. 
   apply L2.
 Qed. 

Lemma L4 : Representable NN 1 (fun n => n * 2)  (v#0 = v#1 + v#1)%fol.
Proof. 
 split. 
  simpl; lia.
   apply Representable_ext with (fun n => n + n). 
   - intro n.  simpl. lia. 
   - apply L3.
Qed. 

(** Mind the order of variables [v#1 ... v#n]  
 [f v#n ... v#1 = v#0]

 *)

(** [v#2] is bound to n *)

Lemma L5:   RepresentableHalf1 NN 2 (fun n p => n) (v#0 = v#2)%fol. 
Proof. 
  intros a b; simpl. 
   unfold substF; simpl.  Search substT . rewrite subProp.subTermNil. 
    Search (SysPrf _ (?A -> ?A)%fol). 
   apply impRefl.
   induction a.  
    simpl. 
    tauto.    
   simpl. simpl.
   Search freeVarT (S_ _).

    now rewrite freeVarSucc.
Qed.

(** [v#1] is bound to p *)
Lemma L6:   RepresentableHalf1 NN 2 (fun n p => p) (v#0 = v#1)%fol. 
Proof. 
  intros a b; simpl. 
   unfold substF; simpl.  Search substT . 
   apply impRefl.
Qed.
