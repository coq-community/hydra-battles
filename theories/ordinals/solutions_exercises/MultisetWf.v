Set Implicit Arguments.
Require Import Relations List Sorted Arith.
From hydras Require Import Restriction.
Require Import Lia.


(* begin snippet tDef *)
Definition t (A:Type) := list (A * nat).
(* end snippet tDef *)

(* begin snippet AGiven *)

Section A_given.

  Variable A: Type.
  Variable LtA : relation A.
  (* end snippet AGiven *)

  (* begin snippet lexpowerDef *)


  Inductive lexpower: relation (t A) :=
    lex1: forall a n l,  lexpower nil ((a,n)::l)
  | lex2: forall a n p l l',  n < p -> lexpower ((a,n)::l) ((a,p)::l')
  | lex3: forall a b n p l l',  LtA a b -> lexpower ((a,n)::l) ((b,p)::l')
  | lex4: forall a n l l',  lexpower l l' -> lexpower ((a,n)::l) ((a,n)::l').
  
End A_given.
(* end snippet lexpowerDef *)

(* begin snippet notWfa:: no-out *)
Section Counter_Example.
  Let R := lexpower  lt.
  Hypothesis Hwf : well_founded R.
  
  Definition seq (n:nat) := repeat (0,0) n ++ ((2,0)::nil).

  Lemma decr_seq : forall n, R (seq (S n)) (seq n).
  (* end snippet notWfa *)
  Proof.
    induction n.
    -  constructor 3; auto with arith. 
    - constructor 4; apply IHn.
  Qed. 

  Lemma not_acc : forall a b, R a b -> ~ Acc R a -> ~ Acc R b.
  Proof.
    intros a b H H0 H1; absurd (Acc R a); auto.
  Qed.

  (* begin snippet notWfb:: no-out *)
  Let is_in_seq l := exists i, l = seq i.

  Lemma is_in_seq_not_Acc : forall x,  is_in_seq x -> ~ Acc R x.
  Proof. 
    intro x; pattern x; apply well_founded_ind with R; [assumption | ].
    (* ... *)
    (* end snippet notWfb *)
    clear x; intros x IHx [i Hi]; subst x.
    specialize (IHx _  (decr_seq i)); destruct IHx.
    exists (S i);auto.
    apply Hwf.
  Qed. 

  (* begin snippet notWfc:: no-out *)
  Lemma contrad: False.
  Proof. 
    apply (@is_in_seq_not_Acc (seq 0)).
    exists 0; trivial.
    apply Hwf.
  Qed. 
  
End Counter_Example.
(* end snippet notWfc *)

(** Lists in normal form *)

(* begin snippet lexnfDef *)
Definition lexnf {A: Type}(ltA : relation A) (l: t A)
  := LocallySorted (Basics.flip ltA) (map fst l).
(* end snippet lexnfDef *)

(* begin snippet lexltDef *)
Definition lexlt {A}(ltA : relation A) :=
  restrict (lexnf ltA) (lexpower ltA).
(* end snippet lexltDef *)

(* begin snippet bigProofa:: no-out *)
Section ProofOfLexwf.
  Variables (A: Type)
            (ltA : relation A).
  Hypothesis HwfA : well_founded ltA.
  
  #[local] Notation NF := (lexnf ltA).
  #[local] Notation LT := (lexlt ltA).
  (* end snippet bigProofa *)

  (* begin snippet theStatement:: no-out *)
  Theorem lexwf:
    forall l,  NF l -> Acc LT l.
  (* end snippet theStatement *)

  (* begin snippet BadProof:: no-out *)
  Proof.
    induction l.
    - split; destruct 1 as [_ [H1 _]]. inversion H1.
      (* end snippet BadProof *)
     (* begin snippet BadProofb:: -.h#A -.h#ltA -.h#A -.h#H  *)
    - (* .no-out *) split; split; intros; destruct a as [a n].
      (* end snippet BadProofb *)
      (* begin snippet BadProofc *)
  Abort.
  (* end snippet BadProofc *)



  (* begin snippet NFInv1:: no-out *)
  Lemma NF_inv1 : forall a n l, NF ((a,n)::l) -> NF l.
  (* end snippet NFInv1 *)
  Proof.
    destruct l.
    - constructor.
    - inversion_clear 1; assumption. 
  Qed. 

  (* begin snippet NFInv2:: no-out *)
  Lemma NF_inv2 : forall a n b p l,  NF((a,n)::(b,p)::l) -> ltA b a.
    (* end snippet NFInv2 *)
    inversion_clear 1. assumption.
  Qed.

  (* begin snippet LTInv:: no-out *)
  Lemma LT_inv : forall a n l l',
      LT l' ((a,n)::l) ->
      l' = nil \/
      (exists b p l'', l'= ((b,p)::l'') /\ ltA b a) \/
      (exists l'',  l'=(a,n)::l'' /\ LT l'' l) \/
      (exists  p l'', l'= ((a,p)::l'') /\ p < n).
  (* end snippet LTInv *)
  Proof.
    destruct 1.
    destruct l'.
    - now left.
    - right.
      destruct H0 as [H0 H1]; inversion H0. 
      + subst; right; right; exists n0, l'; split; auto. 
      + subst; left; exists a0, n0, l'; split; auto. 
      + subst; right;left; exists l'; split; auto. 
        split; auto. 
        eapply NF_inv1 ; eauto.
        split; auto. 
        eapply NF_inv1 ; eauto.
  Qed. 

  (* begin snippet AccsDef *)
  Let Accs (a:A) := forall n l, NF ((a,n)::l) ->
                                Acc LT ((a,n)::l).
  (* end snippet AccsDef *)
  
  (* begin snippet AccNil:: no-out *)
  Lemma Acc_nil : Acc LT nil.
  Proof.  
    split; destruct 1 as [_ [H _]]; inversion H.
  Qed.
  (* end snippet AccNil *)

  (* begin snippet LAccsa *)
  Lemma Accs_all: forall a:A, Accs a. (* .no-out *)
  Proof. (* .no-out *)
    unfold Accs; intros a; pattern a; 
      eapply  well_founded_induction with (R:= ltA); [assumption|];
        clear a ; intros a  IHa.
    (* end snippet LAccsa *)
    
    (** let us prepare an induction on l *)
    (* begin snippet Laccsb:: no-out *)
    assert (Hl: forall n l, NF ((a,n)::l) -> Acc LT l).
    (* we skip the proof of Hl ... *)
    (* end snippet Laccsb *)
    {
      destruct l. 
      - intro; apply Acc_nil.
      - destruct p as [a0 n0]; intro H; apply IHa.
        + now inversion_clear H. 
        + eapply NF_inv1; eauto.
          (* begin snippet Laccsg:: no-in unfold -.h#* .h#IHa  .h#Hl *)
    }
    (* end snippet Laccsg *)
    (* begin snippet Laccsc:: no-out  *)
    intro n; pattern n; apply (well_founded_induction lt_wf).
    (* end snippet Laccsc *)
    (* begin snippet Laccsd:: -.h#A -.h#ltA -.h#Accs -.h#HwfA  *)
    clear n; intros n Hn l H0.
    (* end snippet Laccsd *)
    
    (* begin snippet Laccse:: -.h#A -.h#ltA -.h#HwfA -.h#Accs -.h#Hl  *)
    assert (H1: Acc LT l) by (eapply Hl; eauto); 
      revert H0; pattern l; eapply Acc_ind with LT; [| eauto];
        intros x0 H0 H2 H3.
    (* end snippet Laccse *)
    (* begin snippet Laccsf:: -.h#* .h#IHa .h#Hn .h#H0 .h#H2 .h#H2 .h#H3 .h#H4 *)
    split; intros y H4. 
    destruct (LT_inv H4) as [H5 | [H6 | [H7 | H8]]]. (* .no-out *)
    (* end snippet Laccsf *)
    (* begin snippet case1:: -.h#* .h#H5  *)
    + (* .no-in .unfold *) subst; apply Acc_nil. (* .no-out *)
    (* end snippet case1 *)
      
    + (* begin snippet case2:: -.h#* .h#IHa .h#H7  .h#H4 *)
      destruct H6 as [b [p [l'' [H6 H7]]]];  subst y. (* .no-in .unfold *)
      apply IHa;  auto.
      now destruct H4.
    (* end snippet case2 *)
    + (* begin snippet case3:: -.h#*  .h#H7  .h#H4 .h#H6 .h#H2 *)
      destruct H7 as [l'' [H6 H7]];  subst. (* .no-in .unfold *)
      apply H2; auto. 
      now destruct H4.
    (* end snippet case3 *)        
    + (* begin snippet case4:: -.h#*  .h#H7  .h#Hn .h#H4 .h#H6  *)
      destruct H8 as [p [l'' [H6 H7]]]; subst; apply Hn; auto. 
      (* end snippet case4 *)   
      now destruct H4.
  Qed. 

(* begin snippet NFAcc:: no-out  *)
  Lemma NF_Acc : forall l: t A, NF l -> Acc LT l.
  Proof.
    destruct l. 
    -  intro; apply Acc_nil.
    -  destruct p; intro;  now apply Accs_all.
  Qed.
  
End ProofOfLexwf.
(* end snippet NFAcc  *)

(* begin snippet lexwf:: no-out  *)
Theorem lexwf {A}( ltA : relation A) :
  well_founded ltA ->
  forall l,  lexnf ltA l -> Acc (lexlt ltA) l. (* .no-out *)
Proof. apply NF_Acc.  Qed.
(* end snippet lexwf  *)

(* begin snippet Examples:: no-out *)

Example Ex1 : lexpower  lt  ((2,7)::nil) ((3,0):: nil).
Proof.
  constructor 3; auto with arith.
Qed.

Example Ex2 : lexpower  lt  ((2,7)::(1,0)::(0,33)::nil) ((2,7)::(1,6)::nil).
Proof.
  constructor 4.
  constructor 2; auto with arith.
Qed.

Example Ex3 : lexnf lt ((2,7)::(1,0)::(0,33)::nil).
Proof.
  repeat constructor.
Qed.

(* end snippet Examples *)

(* begin snippet Impossibility1:: no-out *)
Section Impossibility1.
  Variable m : t nat -> nat.
  Hypothesis mDecr : forall l l': t nat,  lexlt lt l l' -> m l <  m l'.

  Definition iota (n:nat) := (0, n)::nil.
  Let x := m ((1,0)::nil).
  Let y := m (iota x).
  
  Fact F1 : y < x.
  (* end snippet Impossibility1 *)
  Proof.
    apply mDecr; unfold x,iota; cbn.    
    split.
    - red; constructor. 
    - split. 
      + constructor; auto with arith. 
      + red; constructor. 
  Qed. 
(* begin snippet Impossibility1a:: no-out *)  
  Fact F2 : x <= y.
  (* end snippet Impossibility1a *)
  Proof.
    unfold y in *; clear y; induction x.
    - auto with arith.
    -  assert (m (iota n) < m (iota (S n))).  
       { apply mDecr; unfold iota; simpl.
         split.   
         - constructor.
         - split.
           + constructor 2; auto with arith. 
           + constructor.
       }
       lia.
  Qed.

  (* begin snippet Impossibility1b:: no-out *)  
  Lemma impossible_nat : False.
  Proof.  generalize F1, F2; lia.   Qed. 
  
End Impossibility1.
(* end snippet Impossibility1b *)



