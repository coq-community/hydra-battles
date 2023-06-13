(**  Use of FOL notations (Experimental)  *)

From Coq Require Import Arith Lists.List.

Require Import fol folProp folProof  Languages folLogic.
Require Import primRec.
Import ListNotations. 
Import FolNotations. 

(** ** Preliminary lemmas *)

#[local] Arguments Ensembles.In {_} .
#[local] Arguments Ensembles.Add {_} .
#[local] Arguments atomic _ _ _ : clear implicits. 
#[local] Arguments apply _ _ _ : clear implicits. 

Import Ensembles. 

Lemma In_add1 {T:Type}(a:T)(S: Ensemble T):
  In (Add  S a) a.
Proof.  right; auto with sets. Qed.

Lemma In_add2 {T:Type}(a b:T)(S : Ensemble T):
  In S a -> In (Add  S b) a.
Proof.  left; auto with sets. Qed.

#[local] Hint Unfold mem:  core. 
#[local] Hint Resolve In_add1 In_add2 AXM: core. 

(** [fol_scope] allows us to read and write FOL terms and formulas 
    in a syntax close to Coq's *)

Remark R1 L (t: Term L): (equal t t) = (t = t)%fol. 
Proof. trivial. Qed. 

(* begin snippet eqRefl:: no-out *)
Lemma eq_refl : forall L (t:Term L), Prf L nil (t = t)%fol.
(* end snippet eqRefl *)
Proof. 
  intros L t.
  assert (H: Prf L nil (forallH 0 (v#0 = v#0))%fol). 
  {
    apply GEN.
    - cbn; auto. 
    - apply EQ1.
  }
  change (nil:(list (Formula L))) with (nil++nil: list(Formula L)).
  eapply MP.
  2: apply H.
  generalize (FA1 _ (v#0 = v#0)%fol 0 t).
  intro; assumption.   
Qed. 

(** A small variation on MP (without appending contexts) *)

(* begin snippet MPDiag:: no-out *)
Lemma MPdiag L (G: System L) (A B: Formula L) : 
  SysPrf L G (A -> B)%fol ->
  SysPrf L G A ->
  SysPrf L G B.
(* end snippet MPDiag *)
Proof.
  destruct 1 as [x [HAB Hx]]. 
  destruct 1 as [y [HA Hy]]. 
  exists (x ++ y). eexists. 
  refine (MP L x y A B _ _). 
  apply HAB. 
  apply HA. 
  intros g Hg; destruct (in_app_or _ _ _ Hg); auto. 
Qed. 

(** A small language *)

(* begin snippet ToyDef *)
Module Toy. 
  Inductive Rel: Set := A_ | B_ | C_ | P_ | R_.
  Inductive Fun : Set := a_ | b_ | f_ | g_ | h_.
 
  Definition arityR (x : Rel): nat := 
    match x with 
       P_ => 1 | R_ => 2 | _ => 0
    end.

 Definition arityF (x : Fun): nat := 
    match x with  f_ |  g_ => 1 | h_ => 2 | _ => 0  end.

 Definition L := language Rel Fun arityR arityF.
(* end snippet ToyDef *)





(* begin snippet termAbbreviations:: no-out *)
Notation a := (apply L a_ Tnil).
Notation b := (apply L b_ Tnil).
Notation f t := (apply L f_ (Tcons t Tnil)).
Notation g t := (apply L g_ (Tcons t Tnil)).
Notation h t1 t2 := (apply L h_ (Tcons t1 (Tcons t2 Tnil))).
(* end snippet termAbbreviations *)

(* begin snippet TermExamples1 *)
Example t0 : Term L :=  a.

Example t1 : Term L := f t0.

Example t2 : Term L := h t1 t0.

Example t3 : Term L := h (f (var 0)) (g (var 1)).

Fail Example t4 : Term L := h t0.
(* end snippet TermExamples1 *)


Goal t0 = a. Proof. reflexivity. Qed. 
Goal t1 = f a. Proof. reflexivity. Qed. 
Goal t2 = h (f a) a. Proof. reflexivity. Qed. 


(* begin snippet NowItsBetter *)
Compute t2. 
(* end snippet NowItsBetter *)



(** Abreviations for the toy language L *)
(*  (atomic _A Tnil) (causes further errors ) *)

(* begin snippet toyNotationForm *)
  Notation A := (atomic L A_ Tnil).
  Notation B := (atomic L B_ Tnil). 
  Notation C := (atomic L C_ Tnil). 
  Notation P t := (atomic L P_ (Tcons t Tnil)).
  Notation R t1 t2 := (@atomic L R_ (Tcons t1 (Tcons t2 Tnil))).
(* end snippet toyNotationForm *)

(* begin snippet FormExamples *)
Example F1 : Formula L :=  R a b.

Example F2 : Formula L := 
  forallH 0 (forallH 1 
               (impH (R (var 0) (var 1)) (R (var 1) (var 0)))).

Example F3 : Formula L := 
  forallH 0 (orH (equal (var 0) a) 
               (existH 1 (equal (var 0) (f (var 1))))).

Example F4: Formula L :=
  orH (forallH 1 (equal (var 0) (var 1)))
    (existH 0 (existH 1 (notH (equal (var 0) (var 1))))).

Example F5: Formula L := (v#0 = a \/ v#0 = f v#1)%fol. 

Example F6: Formula L:= (allH 0, exH 1, v#0 = f v#1 /\ v#0 <> v#1)%fol.

(* end snippet FormExamples *)

(* begin snippet freeVarEx *)
Compute freeVarF L (allH 0, v#0 = v#1)%fol.
Compute freeVarF L (v#0 = v#1 \/ allH 0, v#0 = v#1)%fol.
(* end snippet freeVarEx *)

(* begin snippet freeVarDup *)
Compute freeVarF L (v#0 = v#1 <-> v#1 = v#0)%fol. 
Compute nodup Nat.eq_dec (freeVarF L (v#0 = v#1 <-> v#1 = v#0)%fol). 
(* end snippet freeVarDup *)


(* begin snippet toyNotationForm2 *)
Print F1.

Print F2. 

Print F3.

(* end snippet toyNotationForm2 *)

(** The following computation expands some derived connectives and 
    quantifiers. Within [fol_scope], we print them with a 
    similar syntax (with primed symbols) *)

(* begin snippet toyNotationForm3 *)
Section PrimedSymbols. 

Compute (F3 /\ F1)%fol.

Goal (F3 /\ F1)%fol = (~(~ ~ F3 -> ~ F1))%fol.
 reflexivity. 
Qed. 
(* end snippet toyNotationForm3 *)

(* begin snippet toyNotationForm4 *)
Print F6. 

Compute F6. 

#[local] Unset Printing Notations. 
Print F6. 
Compute F6. 

End PrimedSymbols. 
(* end snippet toyNotationForm4 *)


(* begin snippet boundVars:: no-out *)
Goal forallH 1 (equal (var 1) a) <> forallH 0 (equal (var 0) a).
  discriminate. 
Qed. 
(* end snippet boundVars *)


(* begin snippet smallTerms *)
(** a **)              
Goal apply L a_ Tnil = a.
Proof. reflexivity. Qed. 

(** f a **)
Goal apply L f_  (Tcons  (apply L a_ Tnil) Tnil) = f a. 
Proof. reflexivity. Qed. 

(** f (f v1) **)
Goal apply L f_ 
         (Tcons (apply L f_  
                       (Tcons (var 1) Tnil))
            Tnil ) = (f (f (var  1))).
Proof. reflexivity. Qed. 

(* end snippet smallTerms *)

Definition Ldec : language_decidable L. 
Proof.   
  split; destruct x, y; 
    ((left; reflexivity) || (right; discriminate)).  
Defined.

(** Formula_eqdec is opaque ! *)
Compute match formula_eqdec L Ldec (~ (v#1 = v#0  \/ P v#1))%fol 
                      (v#1 <> v#0 /\ ~ (P v#1))%fol
        with left _ => true | _ => false end.




Check (f a)%fol. 

(* begin snippet DepthCompute *)
Goal lt_depth L (v#0 = v#1 \/ exH 2, v#1 = f v#2)%fol
                (v#0 = v#1 /\ exH 2, v#1 = f v#2)%fol. (* .no-out *)
  red; simpl.
  auto with arith.
Qed. 
(* end snippet DepthCompute *)

(* begin snippet ltDepth1:: no-out *)
Goal lt_depth _ F1 F2. 
cbn. red.  compute; auto with arith. 
Qed.
(* end snippet ltDepth1 *)


Compute substF L F5 0 (f a).



Locate f. 



Section OnSubstF.
(* begin snippet substExample1 *)
  Let F : Formula L := (exH 2, v#1 <> f v#2)%fol.
  Let F' := substF L F 1 (f v#2)%fol. 
  Compute F'.
(* end snippet substExample1 *)
(* begin snippet substExample2 *)
  Let H : Formula L := (v#1 <> f v#2)%fol.
  Goal F' <> (exH 2, substF L H 1 (f v#2) )%fol.
  discriminate. 
  Qed. 

  Let G : Formula L := (v#1 <> f v#3)%fol.
  Goal F' = (exH 3, substF L G 1 (f v#2) )%fol.
    reflexivity.
  Qed.
(* end snippet substExample2 *)
End OnSubstF.  


Lemma MP' f g H1 H2 H: H = H1 ++ H2 -> Prf L H1 (f -> g)%fol ->
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

(* begin snippet step1 *)
  unfold Peirce; apply impI. 
(* end snippet step1 *)

(* begin snippet step2 *)
  eapply orE with (notH A) A%fol; 
       [apply noMiddle | | apply impRefl].
(* end snippet step2 *)
(* begin snippet step3 *)
   apply impI; eapply impE with (A -> B)%fol. 
(* end snippet step3 *)
(* begin snippet step4:: no-out *)
    - apply Axm ...
    - apply impI; apply contradiction with A; apply Axm ...
Qed.
(* end snippet step4 *)

  


  
Section Drinkers_theorem. 

 Lemma D0 : forall i, 
      SysPrf _ (Empty_set _)
        ( ~ forallH i (P (v#i)) -> exH i, (~ (P (v#i))))%fol. 
Proof.
    intro i; apply cp2, impI, forallI. 
    - intros [f [H H0]]; inversion H0. 
      subst; inversion H1; subst. 
      inversion H1; subst; simpl in H. 
      destruct (Nat.eq_dec i i). 
      + inversion H. 
      + now destruct n. 
    - apply nnE; 
        assert (H:(~ ~ (P (v#i)))%fol = (* clumsy *)
                  (substF _ (~ ~ (P (v#i))) i (v#i))%fol). 
      { cbn; destruct (Nat.eq_dec i) as [_ | n].
        auto. 
        now destruct n. 
      } 
    rewrite H; apply forallE; rewrite <- H; apply Axm.  
    right; split. 
  Qed. 
  
  Lemma D01 T i : SysPrf _ T
                    (~ forallH i (P (v#i)) -> 
                      exH i, (~ (P (v#i))))%fol. 
  Proof. 
    apply sysExtend with (Empty_set _).
    - red; destruct 1.   
    - intros; apply D0. 
  Qed. 

  Let f : Formula L :=
        (exH 0, (P (v#0) -> forallH 1 (P (v#1))))%fol. 

  Theorem drinkers_thm : SysPrf L (Empty_set _) f. 
  Proof with auto with sets.  
    pose (F := forallH 1 (P (v#1))%fol).
    unfold f; eapply orE with (notH F) F; [apply noMiddle | | ].
    - apply impI;
      assert (SysPrf L (Add (Empty_set _) (~ F)%fol) 
                (exH 1, (~ (P (v#1))))%fol).  
      { replace (exH 1, (~ (P (v#1))))%fol  
          with (~ (forallH 1 (~ (~  (P (v#1))))))%fol. 
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
        * apply impI; eapply existI with (v#1)%fol.
          cbn; apply impI. 
          eapply contradiction with (P (v#1))%fol.  
          -- apply Axm; red ...
          -- apply Axm; red ...   
    - apply impI; apply existI with (v#0)%fol. 
      cbn;  apply impI. 
      apply Axm; red; auto with sets. 
  Qed. 


End Drinkers_theorem. 



End Toy.

(* Examples with LNN *)

(* begin snippet arityTest *)
Compute arityF LNT Plus_. 
Compute arityF LNN Succ_. 
Compute arityR LNN LT_. 
Fail Compute arityF LNT LT.
(* end snippet arityTest *)

(* begin snippet v1Plus0 *)
(** v1 + 0 *)
Example t1_0: Term LNN := 
 apply LNN Plus_ 
   (Tcons  (var 1)
     (Tcons  (apply LNN Zero_ Tnil) Tnil )). 
(* end snippet v1Plus0 *)
Print t1_0. 

(** forall v0, v0 = 0 \/ exists v1,  v0 = S v1 *)
(* begin snippet f1Example *)
Example f1 : Formula LNN :=
  forallH 0 
    (orH  (equal  (var 0) (apply LNN Zero_ Tnil ))
       (existH 1 (equal  (var 0)
                    (apply LNN Succ_ 
                       (Tcons  (var 1) Tnil))))).

Example f2 : Formula LNN :=
  (existH 1 (equal  (var 0)
               (apply LNN Succ_ 
                  (Tcons (var 1) Tnil )))).

Example f3 := (orH  (equal  (var 0) (apply LNN Zero_ Tnil))
                 (existH 1 (equal  (var 0)
                              (apply LNN Succ_ 
                                 (Tcons (var 1) Tnil))))).
(* end snippet f1Example *)


(* begin snippet FormulaRect *)
About Formula_rect.
(* end snippet FormulaRect *)

(** depth-order vs structural order *)

Section depth_rec_demo. 
Variable L: Language.
Variable P: fol.Formula L -> Prop. 
Variable a: fol.Formula L. 
Goal P a. 
  eapply  Formula_depth_rec_rec with (depth L a); [| apply le_n].
  (* begin snippet depthRecDemo:: unfold no-in *)
 clear a; intros a Ha.
  (* end snippet depthRecDemo *)
Abort.
Goal P a. 
 (* begin snippet depthRecDemo2:: unfold no-in *)
 apply Formula_depth_ind2.
 (* end snippet depthRecDemo2 *)
Abort. 




End depth_rec_demo. 
