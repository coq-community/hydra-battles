
(** Experimental *)

From Coq Require Import Arith Lists.List.

Require Import fol folProp folProof  Languages folLogic.
Require Import primRec.
Import ListNotations. 
Require Import FOL_notations.
Import FolNotations. 

#[local] Arguments Ensembles.In {_} .
#[local] Arguments Ensembles.Add {_} .
Import Ensembles. 

Lemma In_add1 {T:Type}(a:T)(S: Ensemble T):
  In (Add  S a) a.
Proof.  right; auto with sets. Qed.

Lemma In_add2 {T:Type}(a b:T)(S : Ensemble T):
  In S a -> In (Add  S b) a.
Proof.  left; auto with sets. Qed.

#[local] Hint Unfold mem:  core. 

#[local] Hint Resolve In_add1 In_add2: core. 


#[local] Hint Resolve AXM: core. 

(* begin snippet ToyDef *)
Module Toy. 
  Inductive Rel: Set := _A | _B | _C | _P | _R.
  Inductive Fun : Set := _a | _b | _f. 
 
  Definition arity (x : Rel + Fun): nat := 
    match x with 
      inl _P => 1
    | inl _R => 2 
    | inl _ => 0
    | inr _f => 1
    | inr _ => 0
    end.

  Definition L := language Rel Fun arity.
(* end snippet ToyDef *)

(* begin snippet toyNotation *)
  (** Abreviations for the toy language L *)
  Notation A := (@atomic L  _A Tnil).
  Notation B := (@atomic L _B Tnil). 
  Notation C := (@atomic L _C Tnil). 
  Notation P t := (@atomic L _P (Tcons t Tnil)).
  Notation R t1 t2 :=
    (@atomic L _R (Tcons t1 (Tcons t2 Tnil))).

  Notation a := (@apply L _a Tnil).
  Notation b := (@apply L _b Tnil).
  Notation f t := (@apply L _f (Tcons t Tnil)).
(* end snippet toyNotation *)

(* begin snippet smallTerms *)
(** a **)              
Check (@apply L _a Tnil).

(** f a **)
Check (@apply L _f  (Tcons  (@apply L _a Tnil) Tnil)).

(** f (f v1) **)
Check (@apply L _f 
         (Tcons (@apply L _f  
                       (Tcons (var 1) Tnil))
            Tnil )).

Check (f (f (v_ 1)))%fol. 
(* end snippet smallTerms *)



Check (f a)%fol. 



Lemma MP' f g H1 H2 H: H = H1 ++ H2 -> Prf L H1 (impH f g) ->
                        Prf L H2 f ->  Prf L H g.
Proof. 
  intros; subst; eapply MP; eauto. 
Qed. 

Ltac eat G :=
  match goal with 
 |- Prf ?L ?H  ?F =>  eapply MP' with (H1 := G); 
[simpl; reflexivity | try apply AXM | try apply AXM ] end. 



Lemma Pf1:  Prf L [A -> B -> C; A; A -> B; A]%fol C. 
Proof.
  eat  [A -> B -> C; A]%fol.
  eat  [A -> B -> C]%fol. 
  eat [(A -> B)%fol].
Qed. 

Print Pf1. 

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

(* begin snippet PeirceProof:: no-out *)
Definition Peirce : Formula L := (((A -> B) -> A) -> A)%fol.

Lemma peirce : SysPrf  L (Empty_set _)  Peirce. 
Proof with auto with sets. 
(* end snippet PeirceProof *)
  unfold Peirce; apply impI. 
  
  eapply orE with (notH A) A; [apply noMiddle | | apply impRefl].
  
  apply impI; eapply impE with (A -> B)%fol.

  - apply Axm ...
  - apply impI; apply contradiction with A; apply Axm ...       
Qed. 
  
(* begin snippet boundVars *)
Goal forallH (L:= L) 1 (equal (var 1) (var 1)) <>
       forallH  2 (equal (var 2) (var 2)). 
  discriminate. 
Qed. 
(* end snippet boundVars *)


  
Section Drinkers_theorem. 

 Lemma D0 : forall i, 
      SysPrf _ (Empty_set _)
        ( ~ forallH i (P (v_ i)) -> exH i (~ (P (v_ i))))%fol. 
Proof.
    intro i; apply cp2, impI, forallI. 
    - intros [f [H H0]]; inversion H0. 
      subst; inversion H1; subst. 
      inversion H1; subst; simpl in H. 
      destruct (Nat.eq_dec i i). 
      + inversion H. 
      + now destruct n. 
    - apply nnE; 
        assert (H:(~ ~ (P (v_ i)))%fol = (* clumsy *)
                  (substituteFormula _ (~ ~ (P (v_ i))) i (v_ i))%fol). 
      { cbn; destruct (Nat.eq_dec i) as [_ | n].
        auto. 
        now destruct n. 
      } 
    rewrite H; apply forallE; rewrite <- H; apply Axm.  
    right; split. 
  Qed. 
  
  Lemma D01 T i : SysPrf _ T
                    (~ forallH i (P (v_ i)) -> 
                      exH i (~ (P (v_ i))))%fol. 
  Proof. 
    apply sysExtend with (Empty_set _).
    - red; destruct 1.   
    - intros; apply D0. 
  Qed. 

  Let f : Formula L :=
        (exH 0 (P (v_ 0) -> forallH 1 (P (v_ 1))))%fol. 

  Theorem drinkers_thm : SysPrf L (Empty_set _) f. 
  Proof with auto with sets.  
    pose (F := forallH 1 (P (v_ 1))%fol).
    unfold f; eapply orE with (notH F) F; [apply noMiddle | | ].
    - apply impI;
      assert (SysPrf L (Add (Empty_set _) (~ F)%fol) 
                (exH 1 (~ (P (v_ 1))))%fol).  
      { replace (exH 1 (~ (P (v_ 1))))%fol  
          with (~ (forallH 1 (~ (~  (P (v_ 1))))))%fol. 
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
          eapply contradiction with (P (v_ 1))%fol.  
          -- apply Axm; red ...
          -- apply Axm; red ...   
    - apply impI; apply existI with (v_ 0)%nat. 
      cbn;  apply impI. 
      apply Axm; red; auto with sets. 
  Qed. 


End Drinkers_theorem. 

End Toy.

