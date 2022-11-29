(* To do: share this prelude *)

From Coq Require Import Arith Lists.List.

Require Import fol folProp folProof  Languages folLogic.
Require Import primRec.

Require Import FOL_notations.
Import FOL_notations. 

#[local] Arguments Ensembles.In {_} .
#[local] Arguments Ensembles.Add {_} .
Import Ensembles. 

Lemma In_add1 {T:Type}(a:T)(S: Ensemble T):
  In (Add  S a) a.
Proof.  right; auto with sets. Qed.

Lemma In_add2 {T:Type}(a b:T)(S : Ensemble T):
  In S a -> In (Add  S b) a.
Proof.  left; auto with sets. Qed.

#[local] Hint Unfold mem: sets. 

#[local] Hint Resolve In_add1 In_add2: sets. 

Section Proofs.

Variable L : Language. 

Remark R0: SysPrf L (Empty_set _) (v_ 0 = v_ 0)%fol.
Proof. 
 exists nil;  eexists ; [refine (EQ1  _)|].   
 inversion 1.  
Qed. 

Remark R1 i : SysPrf L (Empty_set _) (allH i (v_ 0 = v_ 0))%fol.
  apply forallI.
  - red; inversion 1.
    destruct H0 as [_ H1]; inversion H1. 
  - apply R0.   
Qed. 

Remark R2 t: SysPrf L (Empty_set _) (t = t)%fol.
Proof. 
  change (t = t)%fol with 
    (substituteFormula L (v_ 0 = v_ 0)%fol 0 t). 
  eapply forallE, R1.
Qed.   

Remark R3 T t: SysPrf L T (t = t)%fol.
Proof. 
 apply sysExtend with (Empty_set _).
 - red; inversion 1. 
 - apply R2. 
Qed.   

Remark R4 T i: SysPrf L T (exH i (v_ i = v_ i)%fol).
Proof. 
 apply sysExtend with (Empty_set _).
 - red; inversion 1. 
 - eapply existI with (v_ 0)%fol. 
   cbn; destruct (Nat.eq_dec i i). 
   + apply R0. 
   + destruct n; easy.
Qed. 


End Proofs.
