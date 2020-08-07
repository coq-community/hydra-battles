(** Pierre Castéran, University of Bordeaux and LaBRI *)


Require Import Hydra_Lemmas Simple_LexProd Relations Relation_Operators
Arith Peano_dec Lia ON_Omega2.

(** There is no measure into omega^2  for proving termination
of all hydra battles *)


Section Impossibility_Proof.

   (** Let us assume there is a variant from [Hydra] into nat*nat (with the
   lexicographic oordering)  for proving the   termination of all hydra 
   battles *)
 

  Variable m : Hydra -> ON_Omega2.t.
  
  Context (Hvar : Hvariant lt_wf free m).
   
  Let big_h := hyd1 (hyd2 head head).
  
  (** To every pair $(i,j)$ of natural numbers we associate an hydra 
        with $i$ branches of length 2 and $j$ branches of length 1 *)

  Let iota (p: ON_Omega2.t) := 
    node (hcons_mult (hyd1 head) (fst p)
                     (hcons_mult head (snd p) hnil)).
  
 
  Let small_h := iota (m big_h).

    (** *** Proof of the inequality [m small_h < m big_h] 
     *)

  Hint Constructors R1 S1 S2 : hydra.

  Lemma m_big_h_not_null : m big_h <> (0,0).
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
    
      
  Lemma big_to_small : big_h -+-> small_h. 
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
  
  Corollary m_lt : m small_h o< m big_h.
  Proof.
    apply m_strict_mono with (1:=Hvar) (2:=big_to_small) .  
  Qed.
    
    (** *** Proof of the inequality [m big_h <= m small_h]  *)

    (** *** Let us decompose any inequality p < q into elementary steps *)

    Inductive step : t -> t -> Prop :=
    | succ_step : forall i j,  step (i, S j) (i, j)
    | limit_step : forall i j, step (S i, 0) (i, j).

    
   
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

   

 (*m_strict_mono m Hvar*) 


Hint Constructors step clos_trans_1n : hydra.
Hint Resolve lex_1 lex_2: hydra.
Hint Unfold   lt : hydra.


Lemma step_to_round_plus : forall p q, step p q -> iota p -+-> iota q.
Proof.
  destruct 1; [ apply succ_rounds |  apply limit_rounds].
Qed.

 Hint Resolve step_to_round_plus : hydra. 


 Lemma m_ge : m big_h o<= m small_h.
 Proof.
   unfold small_h; pattern (m big_h) .   
   apply  well_founded_induction with
       (R := lt) (1:= lt_wf);
     intros (i,j) IHij.  
   destruct j as [|k].
   - destruct i as [| l].
     +  (* p = (0,0) *)
       apply le_0. 
     +  (* p = (S i, 0) *)
       rewrite <- limit_is_lub.  intro k.
       apply le_lt_trans with (m (iota (l, k))); auto with hydra. 
       red.  apply (m_strict_mono m Hvar); auto with hydra.
       reflexivity.
   - change (i, S k) with (succ (i,k)) at 1.
     rewrite <- lt_succ_le.
     apply le_lt_trans with (m (iota (i, k))); auto with hydra.
     apply (m_strict_mono m Hvar); auto with hydra.
 Qed.


Theorem Impossible : False.
Proof.
  destruct (StrictOrder_Irreflexive  (m big_h));
    apply le_lt_trans with (m small_h).
  -  apply m_ge.
  -  apply m_lt. 
Qed. 

End Impossibility_Proof.

