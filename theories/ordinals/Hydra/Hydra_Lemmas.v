(**   Pierre Casteran 
      LaBRI, Université de Bordeaux
*)

From Coq Require Import Arith Lia  List  Relation_Operators
     Operators_Properties Peano_dec Wellfounded.Inverse_Image
     Wellfounded.Inclusion.
     
From hydras Require Import More_Arith Epsilon0  Hessenberg
     Simple_LexProd.

From hydras Require Export Hydra_Definitions.
Import Relations.
Open Scope nat_scope.



(** ** Properties of the  [hydra] data type 
 *)

Lemma add_r_0 : forall h: Hydra, add_r h 0 = h.
  now destruct h.
Qed.

Lemma hy_app_assoc :
  forall (s1 s2 s3 : Hydrae) ,
    hy_app s1 (hy_app s2 s3) = hy_app (hy_app s1 s2) s3.
Proof.
  induction s1.
  - reflexivity.
  - intros s2 s3; cbn; now rewrite IHs1.
Qed.

Lemma hcons_mult_app : forall (h: Hydra) (n :nat) (s s': Hydrae),
    hcons_mult h n (hy_app s s') =
    hy_app (hcons_mult h n s) s'.
Proof.
  induction n.
  - now cbn. 
  - cbn; intros; now rewrite IHn.
Qed.

Lemma hcons_mult_comm :
  forall i h s,
    hcons_mult h i (hcons h s) = hcons h (hcons_mult h i s).
Proof.
   induction i as [| i IHi]; simpl; auto.
   intros; now rewrite IHi.
Qed.

(* Properties of R1, R2, S0, S1 and S2 *)

Lemma R1_iff s s' : R1 (node s) (node s') <->  S0 s s'.
Proof.
 split.
   - now inversion 1.
   - now constructor.
Qed.

Lemma R2_iff i s s' : R2 i (node s) (node s') <->
                      S1 i s s' \/ S2 i s s'.
Proof.
  split.
  - inversion 1; auto.
  - destruct 1; [left| right];trivial.  
Qed.


Lemma S2_iff : forall n h h' s s',
    S2 n (hcons h s) (hcons h' s') <->
    R2 n h h' /\ s = s' \/
                 h = h' /\ S2 n s s'.
Proof.
  split.  
  - inversion 1.
  +  subst s; auto.
  +   right;auto.
  -   intros [[H0 H1] | [H0 H1]].
      +  subst s; now left.
      +  subst h'; now right.
Qed. 

Lemma S0_app : forall s1 s2 s3, S0 s2 s3 ->
                                S0 (hy_app s1 s2)
                                   (hy_app s1 s3).
Proof.
  induction s1.
  - cbn; auto.  
  - intros; cbn;  constructor;auto.
Qed.

Lemma R1_app : forall s1 s2 s3,
    R1 (node s2) (node s3) ->
    R1 (node (hy_app s1 s2)) (node (hy_app s1 s3)).
Proof.
  constructor; inversion  H; now apply S0_app.
Qed.

Lemma S1_app n : forall s1 s2 s3,
    S1 n s2 s3 -> S1 n (hy_app s1 s2) (hy_app s1 s3).
Proof.
  induction s1; simpl hy_app.
  - trivial.  
  - intros s2 s3 H; constructor; auto.
Qed.

    
(** Induction Schemes for R2 *)

Scheme R2_ind2 := Induction for R2 Sort Prop
                  with
                  S2_ind2 := Induction for S2 Sort Prop.

Lemma S2_app : forall  n  s1 s2 ,
    S2 n s1 s2 ->
    forall l,  S2 n (hy_app l s1) (hy_app l s2).
Proof.
  intros n s1 s2 h;
    eapply  S2_ind2 with
        (P := fun h1 h2 _ => match h1, h2 with
                               node s1, node s2 =>
                               forall l, R2 n (node (hy_app l s1))
                                            (node (hy_app l s2)) 
                             end).
  - intros; constructor.
    apply S1_app; auto.
    intros;  eauto. 
  - constructor 2.
    induction l.
    + cbn; auto.
    + cbn; now constructor 2.
  -  intros h0 h' s r  H l;  destruct h0, h';  induction l.   
     + simpl;auto.
     +  simpl;auto; constructor 2;auto.
  - auto.
  -  eexact h.
Qed.



Lemma R2_app n : forall  s1 s2 ,
    R2 n (node s1) (node  s2) ->
    forall l,  R2 n (node (hy_app l s1))
                  (node (hy_app l s2)).
Proof.
      intros s1 s2 H;  inversion  H.
      - intros; constructor.
        apply S1_app; auto.
      -  constructor 2; now apply S2_app.
Qed.


Lemma hcons_mult_S0 : forall h  i s s' , 
                             S0 s s' ->
                             S0 (hcons_mult h i s)
                                (hcons_mult h i s').
Proof.
    induction i.
    - now  simpl.
    - right; auto.
Qed.


Lemma hcons_mult_S1 n : forall h i  s s' , S1 n s s' ->
                                         S1  n (hcons_mult h i s)
                                              (hcons_mult h i s').
Proof.
  induction i.
  - now  simpl.
 -  right;auto.
Qed.

Lemma hcons_mult_S2 n : forall h  i s s' , S2 n s s' ->
                                            S2 n (hcons_mult h i s)
                                               (hcons_mult h i s').
Proof.
  induction i.
  - now  simpl.
  - right;auto.
Qed.



(**  ** Properties of single rounds *)

Lemma head_no_round_n : forall i h, ~ round_n i head h.
Proof.
  intros i h  H; destruct H.
  - inversion H.  
    inversion H1.
  -  inversion H.  
     +  inversion H1.
     +  inversion H1.
Qed. 

Lemma head_no_round : forall h, ~ round head h.
Proof.
  intros h H; destruct H as [i Hi].
  now apply (head_no_round_n i h).  
Qed.


(** ** Properties of [battle] *)

(* begin snippet battleTrans *)

Lemma battle_trans {b:Battle} :
  forall i h j h', battle b i h j h' ->
                   forall k h0,  battle b k h0 i h ->
                                 battle b k h0 j h'. (* .no-out *)
(*|
.. coq:: no-out
|*)
Proof. 
  induction 2. 
  - now right with h'0.
  - right with h'';auto.
Qed.
(*||*)

(* end snippet battleTrans *)

(** ** Properties of standard and free battle classes *)


Lemma standard_incl_free : forall i h h',
     battle_rel standard   i h  h'-> battle_rel  free  i h h' .
Proof.
  -   intros; red.  red in H. now  exists i.
Qed.                          

Lemma standard_battle_head :
  forall i h j h',
    @battle standard  i h j h' ->  h <> head.
Proof.
  induction 1;  intro; subst h; eapply head_no_round_n ; eauto.
Qed.



(** **  Generic properties of round_plus *)

Lemma round_plus_trans : forall h h' h'', h -+-> h' ->
                                      h' -+-> h'' ->
                                      h -+-> h''. 
Proof.
  unfold round_plus.
  intros h h' h''; repeat rewrite <- clos_trans_t1n_iff.
  econstructor 2; eauto. 
Qed.




Lemma S0_remove_r : forall l , S0 (add_head_r l) l.
  induction l; simpl.
  - left.
 - now right.
Qed.


Lemma S0_remove_r_i : forall i l, S0 (add_head_r_plus l (S i))
                                     (add_head_r_plus l i).
Proof.
  simpl;  intros; apply S0_remove_r.
Qed.

Lemma R1_remove_r_i : forall i h,
                       R1 (add_r h (S i)) (add_r h i).
Proof.
  destruct h; constructor; apply S0_remove_r_i.
Qed.

Lemma round_n_remove_h : forall i j h,
    round_n j  (add_r h (S i)) (add_r h i).
Proof.
  intros; left;apply R1_remove_r_i.
Qed.

Lemma remove_heads_r : forall i h j, battle standard 
                                       j
                                       (add_r h (S i))
                                       (S i+j)%nat
                                       h.
Proof.
  induction i.
 -   simpl;  intros; left;auto.
     simpl; replace  h with (add_r  h 0) at 2.
     +  left;  apply R1_remove_r_i.
     +  now rewrite add_r_0.
 - intros h j;  specialize (IHi h (S j)).
    apply battle_trans with (S j) (add_r h (S i)).
    +    replace (S (S i) + j)%nat with (S i + S j)%nat;  auto.
         lia.
    +   left.
        * apply round_n_remove_h.
Qed.


Lemma remove_heads_r_free: forall i h j, battle free
                                       j
                                       (add_r h (S i))
                                       (S i+j)%nat
                                       h.
Proof.
  intros; specialize (remove_heads_r i h j).
 induction 1.
 left. now apply standard_incl_free.
  auto. 
  right with h''.
  now apply standard_incl_free.
  auto. 
Qed.

Lemma variant_mono_free  {A:Type} {Lt: relation A}{Tr : Transitive Lt}
      {Wf: well_founded Lt} m {V: Hvariant Wf free m}:
  forall i h j h', battle free i h j h' -> Lt (m h') (m h).
Proof.
  induction 1;auto. 
  -  apply (variant_decr 0).
     + intro; subst; eapply head_no_round; eauto. 
     + auto. 
  - transitivity (m h''); auto.
    apply (variant_decr  0).
    +  intro; subst; eapply head_no_round; eauto. 
    + auto.
Qed.

Lemma m_strict_mono  {A:Type} {Lt: relation A}{St: StrictOrder  Lt}
      {Wf: well_founded Lt} m (V: @Hvariant _ _ Wf free m){h h':Hydra}:
  h -+->  h' -> Lt (m h') (m h).
 Proof.
      induction 1;auto.
      apply (variant_decr 0).
      - intro; subst; eapply head_no_round; eauto. 
      - auto. 
      - transitivity (m y); auto.
        apply (variant_decr  0).
      +  intro; subst; eapply head_no_round; eauto. 
      + auto.
    Qed.


 
(** companion lemmas for R1 and R2 *)

Lemma round_n_inv i h h' : round_n i h h' -> R1 h h' \/ R2 i h h'.
Proof.
  destruct 1;auto.
Qed.


Lemma battle_free_equiv1 : forall i j h h',
    battle free i h j h' ->
    h -+-> h'.
Proof.
  induction 1.
  - now  left.
  - now  right with h''.
 Qed.

Lemma battle_free_equiv2 : forall h h',
     h -+-> h' ->
    forall i, exists j,  battle  free i h j h'.
Proof.
  induction 1 as [h h' H | h h'' h' H H0 Hind].
  - intro i; exists (S i); left;auto.
  - intros i. destruct (Hind (S i)) as [j Hj].
    exists j; eright; eauto.    
 Qed.




Lemma Termination_strong (B:Battle) :
   Termination -> B_termination B.
Proof.
  intro H; red; apply wf_incl  with (R2:=(transp _ round)). 
  - intros h' h;   destruct 1 as [i Hi]; 
     now  generalize (battle_ok _ _ _ Hi).
  -  apply H.
Qed.

Lemma Hvariant_Termination {A : Type} {lt : relation A}
      (Hwf : well_founded lt) (m : Hydra -> A) :
  @Hvariant _ _ Hwf  free m ->  Termination.
Proof.
  destruct 1.
  intro x; apply Acc_incl with (fun h' h =>  lt (m h') (m h)).
  - intros h' h H; destruct H; apply variant_decr with x0.
    + intro ; subst h;  apply (head_no_round_n _ _ H).
    + exists x0; easy.
  -  apply Acc_inverse_image, Hwf.
Qed.


(* begin snippet nextRoundDec *)

(** If the hydra is not reduced to a head, there exists at 
    least one head that  Hercules can chop off  *)

Definition  next_round_dec n (h: Hydra) :
  (h = head) + {h' : Hydra & {R1 h h'} + {R2  n h  h'}}. (* .no-out *)
(*|
.. coq:: none 
|*)

Proof.
induction h using   Hydra_rect2 with
(P0 :=
   (fun hs =>
      (hs = hnil) +
      { hs' : Hydrae & ( S0 hs hs') + {S1 n hs hs'} + {S2 n hs hs'}})%type).
rename h into s.
- destruct s.
  + now left.
  + right.
    destruct IHh.
    * discriminate.

    * destruct s0 as [hs' [s0 | s0]].
      { destruct s0.
        (** chose  a lowest head *)
        exists (node hs').
        left;   now constructor.
        exists (node hs').
        right; now left.
      }
      {  exists (node hs').
         right;now right.
      }
- now left.
- destruct IHh.
  +  right;  exists h0 ; left ; left.
  (* choose the leftmost head *)
  subst h; left.
  +  right;   destruct s as [h' [H1 | H1]].
   *   exists (hcons_mult h' (S n)  h0).
       left; right ;   now constructor.           
   *   exists (hcons h' h0);  right ;  now constructor.
Defined.
(*||*)

(* end snippet nextRoundDec *)

Definition  next_round  n :
 forall h , round_spec h n.
Proof.
  intro h; destruct (next_round_dec n h).
  - now right.
  - destruct s as [h' [H | H]].
    + left; exists h'; now left.
    + left; exists h'; now right.
Defined.


Definition next_step (f : forall n h, round_spec h n) n h :=
  match f n h with
      inright _ => head
    | inleft (exist _ h' _) =>  h'
  end.


Definition classic_battle f t h :=
  let fix go n t h := 
      match h, t with head, _ => h
                   |   _, 0 => h
                | _, S t' => go (S n) t' (next_step f n h)
      end
  in go 1 t h.


