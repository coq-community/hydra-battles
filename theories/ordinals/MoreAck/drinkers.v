(* draft draft draft draft draft draft draft draft draft draft draft draft *)

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

Module Drinkers. 

  Inductive Rel: Set := _D.
  Inductive Fun : Set := . 

  Definition arity (x : Rel + Fun): nat :=
    match x with
      inl _D => 1
    | inr _ => 0
    end. 

  Definition L := language Rel Fun arity.

  Notation D t := 
    (atomic  (_D: Relations L) (Tcons _ _ t (Tnil _))). 

  Arguments Empty_set {U}. 
  Arguments Add {U} _ _. 
 
Section Drinkers_theorem. 

 Lemma D0 : forall i, 
      SysPrf _ Empty_set 
        ( ~ allH i (D (v_ i)) -> exH i (~ (D (v_ i))))%fol. 
Proof.
    intro i; apply cp2, impI, forallI. 
    - intros [f [H H0]]; inversion H0. 
      subst; inversion H1; subst. 
      inversion H1; subst; simpl in H. 
      destruct (Nat.eq_dec i i). 
      + inversion H. 
      + now destruct n. 
    - apply nnE; 
        assert (H:(~ ~ (D (v_ i)))%fol = (* clumsy *)
                  (substituteFormula _ (~ ~ (D (v_ i))) i (v_ i))%fol). 
      { cbn; destruct (Nat.eq_dec i) as [_ | n].
        auto. 
        now destruct n. 
      } 
    rewrite H; apply forallE; rewrite <- H; apply Axm.  
    right; split. 
  Qed. 
  
  Lemma D01 T i : SysPrf _ T
                    ( ~ allH i (D (v_ i)) -> exH i (~ (D (v_ i))))%fol. 
  Proof. 
    apply sysExtend with Empty_set. 
    - red; destruct 1.   
    - intros; apply D0. 
  Qed. 

  Let f : Formula L :=
        (exH 0 (D (v_ 0) -> allH 1 (D (v_ 1))))%fol. 

  Theorem drinkers_thm : SysPrf L Empty_set f. 
  Proof with auto with sets.  
    pose (F := allH 1 (D (v_ 1))%fol).
    unfold f; eapply orE with (notH F) F; [apply noMiddle | | ].
    - apply impI;
      assert (SysPrf L (Add Empty_set (~ F)%fol) 
                (exH 1 (~ (D (v_ 1))))%fol).  
      { replace (exH 1 (~ (D (v_ 1))))%fol  
          with (~ (allH 1 (~ (~  (D (v_ 1))))))%fol. 
        - unfold F; eapply impE. 
          + eapply D01. 
          + apply Axm; right; split. 
        - auto. 
      }      
      + eapply existE with (v:=1). 
        * unfold F; intro H0; destruct H0. 
          destruct H0 as [H0 H1]; inversion H1. 
          --  inversion H2. 
          -- subst. 
             inversion H2. 
             subst; now simpl in H0. 
        * cbn; auto. 
        * eapply H. 
        * apply impI; eapply existI with (v_ 1)%fol.
          cbn; apply impI. 
          eapply contradiction with (D (v_ 1))%fol.  
          -- apply Axm; red ...
          -- apply Axm; red ...   
    - apply impI; apply existI with (v_ 0)%nat. 
      cbn;  apply impI. 
      apply Axm; red; auto with sets. 
  Qed. 


End Drinkers_theorem. 

Import CFOL_notations. 
About drinkers_thm.

End Drinkers. 
