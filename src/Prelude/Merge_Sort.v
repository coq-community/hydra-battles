(** P. Casteran, S. Salvati *)

(** Maybe already done in StdLib ???? *)


Require Import List  Wf_nat  Recdef  Compare_dec  Arith  Peano_dec  Omega 
        RelationClasses DecPreOrder DecPreOrder_Instances Div2 Sorting.Sorted.
Import Relations Morphisms.

Require Import Sort_spec Coq.Sorting.Permutation.
Section Generic.
  Variables (A:Type).
  
  Section Splitting.

    (** A function that splits any list in two lists of (almost) the same length
     *)


    Function split (l:list A):=
      match l with
        | nil 
        | _::nil => (l,nil)
        | a::b::l =>
          let (l1,l2):= split l in (a::l1,b::l2)
      end.

    Function split'_aux (l l':list A) :=
      match l,l' with
      | x::l,_::_::l' =>
        let (l1,l2) := split'_aux l l' in
        (x::l1, l2)
      | _,_ => (nil,l)
      end.

    Function split' (l:list A) := split'_aux l l.

    
    
    (** Applying split  to a list l returns a pair of two strictly shorter lists *)


    Lemma split_decr:
      forall l1 l2 a b, l1 = a::b::l2 ->
                        length (fst(split l1)) < length l1 /\ 
                        length (snd(split l1)) < length l1.
    Proof.
      intro l1; functional induction (split l1).
      -  discriminate.
      -  discriminate.
      - injection 1; intros; subst.
        rewrite e0 in IHp; simpl in IHp; simpl.
        destruct l3.
        inversion e0; omega.
        destruct l3; [inversion e0; simpl;omega|].
        specialize (IHp l3 a a1 (eq_refl _));  omega.
    Qed.

    Lemma split_permutation:
      forall l, Permutation ((fst(split l))++snd(split l)) l.
    Proof with auto.
      intro l; functional induction (split l).
      - simpl; auto.
      - simpl; auto.
      - simpl; constructor  ...
        transitivity ((b::l2)++l1); [apply Permutation_app_comm|].
        +  simpl; constructor ...
           transitivity (l1++l2); [apply Permutation_app_comm|].
           now rewrite e0 in IHp; simpl in IHp.
    Qed.

    
    Lemma split'_aux_length_preserve:
      forall l l',
        length(fst(split'_aux l l')) + length(snd (split'_aux l l'))  =
        length l.
    Proof.
      intros; functional induction (split'_aux l l'); simpl.
      + rewrite e1 in IHp; simpl in IHp.
        now rewrite IHp.
      + trivial.
    Qed.


    Lemma split'_aux_length_fst:
      forall l l',
        length(fst(split'_aux l l')) = min (div2(length l')) (length l).
    Proof.
      intros; functional induction (split'_aux l l'); simpl.
      + rewrite e1 in IHp; simpl in IHp.
        omega.
      + destruct l; destruct l'; simpl; auto.
        now rewrite Nat.min_0_r.
        destruct l'; simpl; auto.
        contradiction.
    Qed.

    
    
    
    Lemma split'_decr:
      forall l1 l2 a b, l1 = a::b::l2 ->
                        length (fst(split' l1)) < length l1 /\
                        length (snd(split' l1)) < length l1.
    Proof.
      split.
      + intros; unfold split'; rewrite H.
        apply Nat.le_lt_trans with (m:=div2(length (a::b::l2))).
        rewrite split'_aux_length_fst.
        apply Min.le_min_l.
        simpl; apply lt_n_S.
        destruct (length l2); auto.
        apply lt_trans with (m:=S n); auto.
        apply lt_div2; omega.
      + intros.
        rewrite <- (split'_aux_length_preserve l1 l1).
        assert(0<length (fst (split'_aux l1 l1)) ).
        { rewrite H.
          rewrite split'_aux_length_fst.
          apply Nat.min_glb_lt; simpl; omega.
        }
      unfold split'; omega.
    Qed.

    Lemma split'_aux_eq:
      forall l l', ((fst(split'_aux l l'))++snd(split'_aux l l')) = l.
    Proof.
      intros; functional induction (split'_aux l l'); trivial.
      rewrite e1 in IHp; simpl in IHp.
      now simpl; rewrite IHp.
    Qed.

    Lemma split'_permutation:
      forall l, Permutation ((fst(split' l))++snd(split' l)) l.
    Proof.
      intro; unfold split'; rewrite split'_aux_eq; trivial.
    Qed.          
  End Splitting.

  Section Merging.
  
    Fixpoint merge  (leb : A -> A ->bool) l1 l2:=
      let fix merge_aux l2 {struct l2}:=
          match l1,l2 with
            | nil,_ => l2
            | _,nil => l1
            | a1::l1',a2::l2' =>
              if leb a1  a2 then a1 :: merge  leb l1' l2 else a2 :: merge_aux l2'
          end
      in merge_aux l2.

    Variable le : relation A.

    Context (le_total : TotalDecPreOrder le ).

    Notation "a <= b" := (le a b).
    Notation "a <=? b" := (leb le a b).

    Lemma merge_rect:
      forall P: list A -> list A -> list A -> Type,
        (forall l:list A, P nil l l) ->
        (forall l: list A, P l nil l) ->
        (forall a1 l1 a2 l2 p,
           dec_dec a1 a2 = left p ->
           P l1 (a2::l2) (merge (leb le) l1 (a2::l2)) ->
           P (a1::l1) (a2::l2) (a1::(merge (leb le)l1 (a2::l2)))) ->
        (forall a1 l1 a2 l2 p,
           dec_dec a1 a2 = right p ->
           P (a1::l1) l2 (merge (leb le)(a1::l1) l2) ->
           P (a1::l1) (a2::l2) (a2::(merge (leb le) (a1::l1) l2))) ->
        forall l1 l2, P l1 l2 (merge (leb le) l1 l2).
    Proof with auto.
      induction l1.
      - intros; simpl; destruct  l2; apply X.
      - induction l2.
        + apply X0.
        + case_eq (dec_dec a a0); intros Eq Comp.
          * simpl. le_2_leb Eq H1. rewrite H1; simpl.
            eapply X1.   eexact Comp. apply IHl1.  
          * simpl.  assert (a <=? a0 = false).
            rewrite  leb_false.
            apply not_le_gt; auto.
            rewrite H.  eapply X2;eauto. 
    Qed.

    Definition merge_ind ( P: list A -> list A -> list A -> Prop) :=
      merge_rect P.
    
    Definition merge_rec( P: list A -> list A -> list A -> Set) :=
      merge_rect P.


    Ltac induction_merge l1 l2:= pattern (merge (leb le) l1 l2 ); apply merge_rect.
    
    Lemma merge_equation:
      forall l1 l2,
        merge (leb le) l1 l2 =
        match l1,l2 with
          | nil,_ => l2
          | _,nil => l1
          | a1::l1',a2::l2' =>
            if dec_dec a1  a2 then a1 :: merge (leb le) l1' l2
            else a2 :: merge (leb le) l1 l2'
        end.
    Proof.
      intros l1 l2.
      induction_merge l1 l2; trivial.
      - now intros l; destruct l.
      - intros a1 l1' a2 l2' Comp Eq .  rewrite Eq; reflexivity.
      - intros a1 l1' a2 l2' Comp Eq; rewrite Eq; reflexivity.
    Qed.


    Section Correctness.
      
      
  
      
 
      Lemma merge_Forall:
        forall  (f:A->Prop) l1 l2,
          List.Forall f l1 ->
          List.Forall f l2  ->
          List.Forall f (merge (leb le) l1 l2) .
      Proof with auto.
        intros f l1 l2.
        induction_merge l1 l2; intros ...
        - inversion_clear H1.
          constructor ...
        - inversion_clear H2.
          constructor ...
      Qed.
      

      Lemma merge_LocallySorted:
        forall l1 l2, LocallySorted  le l1 -> LocallySorted le  l2 ->
                      LocallySorted le (merge (leb le) l1 l2).
      Proof with auto.
        intros l1 l2; induction_merge l1 l2; intros ...
        - rewrite <- (LocallySorted_cons' A le).
          split.
          + apply (merge_Forall (le a1) l0 (a2::l3)).
            * rewrite <- LocallySorted_cons' in H1; intuition.
            * rewrite <- LocallySorted_cons' in H2; intuition.
              apply forall_weak with a2 ...
              apply le_total.
              now constructor.
          + eapply H0 ...
            rewrite <- LocallySorted_cons' in H1; intuition.
          + apply le_total.
- rewrite <- LocallySorted_cons'.
          split.
          +  apply (merge_Forall (le a2) (a1::l0) l3).
             * rewrite <- LocallySorted_cons' in H1; intuition.
               apply forall_weak with a1 ...
               apply le_total.
               apply le_lt_weak.
               apply not_le_gt;auto.
               now constructor.
             * rewrite <- LocallySorted_cons' in H2; intuition.
          +  eapply H0 ...
             rewrite <- LocallySorted_cons' in H2; intuition.
      + apply le_total.
Qed.

      Lemma merge_permutation:
        forall l1 l2, Permutation (l1++l2) (merge (leb le) l1 l2).
      Proof with auto.
        intros l1 l2;  induction_merge l1 l2; intros. 
        - reflexivity.
        - now rewrite app_nil_r.
        - simpl.  now constructor. 
        - transitivity ((a2::l3)++a1::l0).
          + apply Permutation_app_comm.
          + constructor. 
            transitivity  (a1::l0++l3) ...
            apply Permutation_app_comm ...
      Qed.

      Section merge_sort.
        Variable split: list A -> (list A * list A).

        Hypothesis split_decr:
          forall l1 l2 a b, l1 = a::b::l2 ->
                        length (fst(split l1)) < length l1 /\
                        length (snd(split l1)) < length l1.

        Hypothesis split_permutation:
          forall l, Permutation ((fst(split l))++snd(split l)) l.
        
        
        Function merge_sort (leb : A -> A ->bool) (l:list A) {measure length l} :=
          match l with
          | nil | _ :: nil => l
          | _::_::_ =>
            let (l1,l2) := split l in
            merge  leb (merge_sort leb l1) (merge_sort leb l2)
          end.
        - intros.
          replace l3 with (snd (split (a::a0::l1))).
          now destruct (split_decr (a::a0::l1)   l1 a a0).
          now rewrite teq1.
        - intros.
          replace l2 with (fst (split (a::a0::l1))).
          now destruct  (split_decr (a::a0::l1) l1 a a0).
          now rewrite teq1.
        Defined.
        
        Theorem merge_sort_correct: sort_correct A le (merge_sort (leb le)).
        Proof with auto with lists.
          intro l;   functional induction (merge_sort (leb le) l) ...
          - split...
          - split ...      
          -  destruct IHl0, IHl1. split ...
             apply (merge_LocallySorted (merge_sort (leb le) l1) (merge_sort (leb le) l2)); trivial.
             transitivity (l1++l2).
             generalize (split_permutation (_x :: _x0 :: _x1)).
             rewrite e0.
             intro;symmetry...       
             transitivity ((merge_sort (leb le) l1) ++ (merge_sort (leb le) l2)).
             rewrite <- H0, <- H2 ...
             apply merge_permutation; trivial.
        Qed.
      End merge_sort.
    End Correctness.

    
    Definition sp_merge_sort:= merge_sort split split_decr.

    Definition stable_merge_sort := merge_sort split' split'_decr.
    
  End Merging.


End Generic.

Check (sp_merge_sort: sort_fun_t).
Check (stable_merge_sort: sort_fun_t).

Theorem sp_mergesort_OK : sort_spec sp_merge_sort.
Proof.
  red; intros.  now destruct  (merge_sort_correct A le P
                                                  (split _) (split_decr _)
                                                  (split_permutation _)
                                                  l).
Qed.

Theorem stable_mergesort_OK : sort_spec stable_merge_sort.
Proof.
  red; intros.  now destruct  (merge_sort_correct A le P
                                                  (split' _) (split'_decr _)
                                                  (split'_permutation _)
                                                  l).
Qed.



(*

Recursive Extraction merge_sort.
About List_length.

 *)




