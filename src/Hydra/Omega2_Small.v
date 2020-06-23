(** Pierre Castéran, University of Bordeaux and LaBRI *)


Require Import Hydra_Lemmas Simple_LexProd Relations Relation_Operators
Arith Peano_dec Lia.

(** There is no measure into omega^2  for proving termination
of all hydra battles *)

(** * Order structure on nat * nat *)

Definition  t := (nat * nat)%type. 

(** non-dependent lexicographic strict ordering on nat*nat *)

Definition lt2 : relation t := lexico Peano.lt Peano.lt.
Infix "<" := lt2.

(** reflexive closure of lt2 *)

Definition le2 := clos_refl _ lt2.
Infix "<=" := le2.

(** ** Properties of lt2 and le2 
 *)

Hint Constructors clos_refl lexico : hydra.
Hint Unfold lt2 le2 : hydra.


Instance Sto_lt2 : StrictOrder lt2.
Proof. apply Strict_lex; apply Nat.lt_strorder. Qed.

Lemma lt2_wf : well_founded lt2.
Proof. apply wf_lexico; apply lt_wf. Qed.

Lemma le2_introl :
  forall i j k:nat, (j <= k)%nat -> (i,j) <= (i,k).
Proof.
  intros i j k H; destruct (Lt.le_lt_or_eq j k H); auto with hydra.
  - subst k; now right.
Qed.

Lemma le2_0 : forall p: t,  (0,0) <= p.
Proof.
  destruct p, n ; auto with arith hydra.
  - apply le2_introl;  auto with arith hydra.
Qed.

Lemma le2_1 : forall i j p,  (i,j) < p -> (i, S j) <= p.
Proof.
  intros i j p H; destruct p as (k,l).
  -  inversion_clear H; auto with hydra.
     + destruct (Lt.le_lt_or_eq _ _ H0); auto with hydra.
       * subst l; now right.
Qed.

Lemma le2_lt2_trans : forall p q r, p <= q -> q < r -> p < r.
Proof.
  destruct 1; try trivial. 
  intro; now transitivity y.  
Qed.   

Lemma lt2_le2_trans : forall p q r, p < q -> q <= r -> p < r.
Proof.
  destruct 2; try trivial; now  transitivity q.
Qed.   


Lemma limit_is_lub : forall i p, (forall j, (i,j) < p) <->
                            (S i, 0) <= p.
Proof.
  intros i (k,l) ;split; intro  H .
  -   destruct (Nat.eq_dec (S i) k).
    + subst k;  destruct l.
      *  now right.
      *   left;  right;  auto with arith.
    +  generalize (H (S l));   inversion_clear 1.
       destruct l.
      *  destruct (Lt.le_lt_or_eq _ _ H1); auto with hydra.
           subst k; now right.
      * left; left; lia.
      *  now destruct (Nat.nlt_succ_diag_l l).
 -   intro j; apply lt2_le2_trans with (S i, 0); auto with hydra.
Qed.


Section Impossibility_Proof.

   (** Let us assume there is a variant from [Hydra] into nat*nat (with the
   lexicographic oordering)  for proving the   termination of all hydra 
   battles *)
 

  Variable m : Hydra -> t.
  
  Context (Hvar : Hvariant lt2_wf free m).
   
  Let big_h := hyd1 (hyd2 head head).
  
  (** To every pair $(i,j)$ of natural numbers we associate an hydra 
        with $i$ branches of length 2 and $j$ branches of length 1 *)

  Let iota (p: t) := 
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
  
  Corollary m_lt : m small_h < m big_h.
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

   




Hint Constructors step clos_trans_1n : hydra.
Hint Resolve lex_1 lex_2 (m_strict_mono m Hvar) : hydra.
Hint Unfold   lt2 : hydra.


Lemma step_to_round_plus : forall p q, step p q -> iota p -+-> iota q.
Proof.
  destruct 1; [ apply succ_rounds |  apply limit_rounds].
Qed.

 Hint Resolve step_to_round_plus : hydra. 


Lemma m_ge : m big_h <= m small_h.
Proof.
  unfold small_h; pattern (m big_h) .   
  apply  well_founded_induction with
      (R := lt2) (1:= lt2_wf);
    intros (i,j) IHij.  
  destruct j as [|k].
  - destruct i as [| l].
    +  (* p = (0,0) *)
      apply le2_0. 
    +  (* p = (S i, 0) *)
      apply limit_is_lub; intro k.
        apply le2_lt2_trans with (m (iota (l, k))); auto with hydra.
  - apply le2_1; apply le2_lt2_trans with (m (iota (i, k))); auto with hydra.
Qed.


Theorem Impossible : False.
Proof.
  destruct (StrictOrder_Irreflexive  (m big_h));
    apply le2_lt2_trans with (m small_h).
  -  apply m_ge.
  -  apply m_lt. 
Qed. 

End Impossibility_Proof.

