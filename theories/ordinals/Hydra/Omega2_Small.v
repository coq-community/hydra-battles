(** Pierre Castéran, University of Bordeaux and LaBRI *)


From Coq Require Import Arith Peano_dec Lia Relations Relation_Operators.
From hydras Require Import  Hydra_Lemmas Simple_LexProd ON_Omega2.
Import ON_Generic.

(** There is no measure into omega^2  for proving termination
of all hydra battles *)


(* begin snippet Impossibility *)

Section Impossibility_Proof.
(* end snippet Impossibility *)

  (** Let us assume there is a variant from [Hydra] into [omega^2] 
  for proving the termination of all hydra battles *)
  
  (* begin snippet Impossibilitya *)
  
  Variable m : Hydra -> ON_Omega2.t.
  Context
    (Hvar: Hvariant Omega2 free m).

  (* end snippet Impossibilitya *)

  (* begin snippet Impossibilityb *)
  
  Let big_h := hyd1 (hyd2 head head).

  (* end snippet Impossibilityb *)
  
  (** To every pair $(i,j)$ of natural numbers we associate an hydra 
        with $i$ branches of length 2 and $j$ branches of length 1 *)

  (* begin snippet Impossibilityc *)

  Let iota (p: ON_Omega2.t) := 
    node (hcons_mult (hyd1 head) (fst p)
                     (hcons_mult head (snd p) hnil)).
  

  (* end snippet Impossibilityc *)

  (* begin snippet Impossibilityd *)
  
  Let small_h := iota (m big_h).
  (* end snippet Impossibilityd *)
  

  (** *** Proof of the inequality [m small_h o< m big_h] 
   *)

  #[local] Hint Constructors R1 S1 S2 : hydra.

  Lemma m_big_h_not_null : m big_h <> zero.
  Proof.
    intro H; pose (h1 := hyd1 (hyd1 head)).
    assert (first_round : big_h -+-> h1).
    {
      left; exists 0; right; left; constructor 1 with (n:=0).
      split; left.
    }
    specialize (m_strict_mono m Hvar first_round).   
    rewrite H; inversion_clear 1; lia.
  Qed. 
  
  (* begin snippet bigToSmall *)
  
  Lemma big_to_small : big_h -+-> small_h. (* .no-out *)

  (* end snippet bigToSmall *)
  
  Proof.
    unfold small_h; case_eq  (m big_h); intros i j Hj;  destruct i.
    
    (*  i = 0 *)
    - unfold big_h; right with (hyd1 (hyd1 head)).
      exists 0; right; left.
      left with (n:=0);  split; left.
      destruct j.
      + now destruct m_big_h_not_null.
      + unfold iota;cbn;left.
        exists j;right; left; constructor 1;  split;  left.
        
    (* i > 0 *)
    - unfold iota; cbn;  destruct j.
      +   left; unfold iota, big_h; cbn.
          exists i; right; left; left;   split; left.
      +  right with (iota (S (S i), 0)). 
         unfold iota;  simpl fst ; simpl snd;   cbn; exists (S i); right.
         left; left;  split; left.
         left;  exists j; right; left;   right. 
         rewrite <- hcons_mult_comm;  apply hcons_mult_S1.
         left; split; left.
  Qed.

  (* begin snippet mLt *)

  (*|
.. coq:: no-out
|*)
  
  Corollary m_lt : m small_h o< m big_h.
  Proof. apply m_strict_mono with (1:=Hvar) (2:=big_to_small). Qed.
  (*||*)

  (* end snippet mLt *)
  
  (** *** Proof of the inequality [m big_h o<= m small_h]  *)

  (** *** Let us decompose any inequality p o< q into elementary steps *)

  (* begin snippet stepDef *)

  Inductive step : t -> t -> Prop :=
  | succ_step : forall i j,  step (i, S j) (i, j)
  | limit_step : forall i j, step (S i, 0) (i, j).

  (* end snippet stepDef *)
  
  Lemma succ_rounds : forall i j,  iota (i,S j) -+-> iota (i, j).
  Proof.
    unfold iota;  left; exists 0;  left;   split; 
      apply hcons_mult_S0;  constructor.
  Qed.

  Lemma limit_rounds_0 :
    forall i j, round_n j (iota (S i, 0)) (iota (i, S j)).
  Proof.
    intros i j;  destruct i.
    - unfold iota;   right;  left;
        change  (hcons head (hcons_mult head j hnil))
          with (hcons_mult head (S j) hnil).
      left; split;  left.
    -   right; left; cbn;  rewrite <- hcons_mult_comm; right.
        apply hcons_mult_S1; left; split; constructor.
  Qed.
  
  Lemma limit_rounds : forall i j, iota (S i, 0) -+-> iota (i, j).
  Proof.
    intros i j;  apply round_plus_trans with (iota (i, S j)).
    - left; exists j; apply limit_rounds_0.
    - apply succ_rounds.
  Qed.

  #[local] Hint Constructors step clos_trans_1n : hydra.
  #[local] Hint Resolve lex_1 lex_2: hydra.
  #[local] Hint Unfold lt : hydra.


  (* begin snippet stepToBattle *)
  
  Lemma step_to_battle : forall p q, step p q -> iota p -+-> iota q. (* .no-out *)

  (* end snippet stepToBattle *)
  
  Proof.
    destruct 1; [ apply succ_rounds |  apply limit_rounds].
  Qed.

  #[local] Hint Resolve step_to_battle : hydra.

  (* begin snippet mGe *)


  
  Lemma m_ge : m big_h o<= m small_h. (* .no-out *)
  Proof. (* .no-out *)
    unfold small_h;
    pattern (m big_h);
      apply  well_founded_induction with (R := ON_lt) (1:= ON_wf);
      intros (i,j) IHij.

    (* end snippet mGe *)

    (* begin snippet mGeb *)
       (*|
.. coq:: none
|*)
    destruct j as [|k].
    - destruct i as [| l].
      +  apply le_0. 
      +  assert (is_true (limitb (S l, 0))) by  reflexivity.
        specialize (limit_is_lub (S l, 0) H (m (iota (S l, 0)))).
        intros <- k; eapply Comparable.le_lt_trans.  
        apply IHij;left; auto.
        red; apply (m_strict_mono m Hvar); auto with hydra.
        simpl canon. 
        apply step_to_battle.  apply limit_step. 
    - change (i, S k) with (succ (i,k)) at 1.
      rewrite <- (lt_succ_le (i,k) (m (iota (i, S k)))).
      eapply (Comparable.le_lt_trans).
      instantiate (1:= (m (iota (i, k)))). 
      apply IHij; right; auto.      
      apply (m_strict_mono m Hvar); auto with hydra.
      (*||*)
      (* ... *)
  Qed.

    (* end snippet mGeb *)

  (* begin snippet Impossible *)

  (*|
.. coq:: no-out
|*)
  
  Theorem Impossible : False.
  Proof.
    destruct (StrictOrder_Irreflexive (R:=ON_lt) (m big_h));
      eapply le_lt_trans; [apply m_ge | apply m_lt].
  Qed. 

End Impossibility_Proof.

(*||*)


  (* end snippet Impossible *)
