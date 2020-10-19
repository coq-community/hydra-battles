(** Complements on lists

   Pierre Castéran, Univ. Bordeaux and LaBRI *)


From Coq  Require Export List Arith Relations Lia.
Require Import Sorting.Sorted  Compare_dec  Sorting.Sorted.

(** *  Sets of natural numbers as lists *)


(** ** Definitions *)


(** numbers from i to i+n-1  *)

Fixpoint iota_from i n :=
  match n with 0 => nil
            | S p =>  i :: iota_from (S i) p
  end.

Definition interval i j := iota_from i (S j - i).

Definition bounded_by (n:nat)(s: list nat) :=
  List.Forall (fun i => i<=n)%nat s.

(*  shift and unshift lists of nats *)

Definition shift (l: list nat) := List.map S l.

Fixpoint unshift (l : list nat) : list nat :=
  match l with
      nil => nil
    | 0 :: l' => unshift l'
    | S i :: l' => i :: unshift l'
  end.

 (** sorted list of elements greater or equal than n *)

Inductive sorted_ge (n: nat) : list nat -> Prop :=
| sorted_ge_nil : sorted_ge n nil
| sorted_ge_one : forall p, n<=p -> sorted_ge n (p::nil)
| sorted_ge_cons: forall p q s,
    n <= p -> p < q -> sorted_ge p (q::s) ->
    sorted_ge n (p::q::s).


(** simpler than StdLib's last *)

Fixpoint simple_last {A} (x:A) s :=
  match s with
      nil => x
    | i::s' => simple_last  i s'
  end.

(** the list (x::s) without its last item *)

Fixpoint but_last {A:Type}(x:A) (s : list A) :=
  match s with
  | nil => nil
  | y::s' => x :: but_last  y s' 
  end.



Lemma but_last_iota_from : forall l i,
      but_last i (iota_from (S i) (S l)) = i::iota_from (S i) l.
induction l; simpl. 
reflexivity. 
intros.
repeat f_equal.
simpl.
specialize (IHl (S i)).
simpl in IHl.
injection IHl. intros. rewrite H. auto.
Qed.


Lemma interval_length i j : length (interval i j) = S j - i.
Proof.
  unfold interval.
 generalize (S j - i). intro.   revert i.
 induction n; simpl; auto.
Qed.

Lemma but_last_interval i j:
  i < j ->
  but_last i (interval (S i) (S j)) = i:: interval (S i) j.        
Proof.
  intros.
  unfold interval.    
  specialize (but_last_iota_from (S j - S i) i).
 intro.
  replace (S (S j) - S i) with (S (S j - S i)).
  replace (S j) with (i + S (S j - S i)) at 3.
 2: lia.

  2:lia.
 auto.
Qed.


Lemma but_last_shift'   s : forall x,
     but_last (S x) (shift  s) = shift (but_last x s).
Proof.
  induction s; cbn.
  - auto.
  - intros;f_equal.  rewrite IHs.  cbn;  reflexivity.
Qed.


Lemma unshift_but_last   s : forall x,
    ~ In 0 (x::s) ->
    unshift (but_last  x s) = but_last (Nat.pred x) (unshift s).
Proof.
  induction s; cbn.
  - auto.
  - intros;f_equal. destruct x.
    destruct H; auto.
    simpl.
    specialize (IHs  a).  simpl in IHs.
     destruct a.
      destruct H; auto.
     simpl.
     simpl in IHs.
      f_equal.
    apply IHs.
    tauto.
Qed.

Lemma unshift_app : forall s t,  unshift (s ++ t) = unshift s ++ unshift t.
Proof.
  induction s; cbn.
  - reflexivity.
  - intro; destruct a; auto.
    now rewrite (IHs t).
Qed.


Lemma unshift_not_nil : forall s, ~ In 0 s -> s <> nil -> unshift s <> nil.
Proof.
  destruct  s.  
  - destruct 2; auto.
  - cbn. destruct n.
     + destruct 1; now left.
     +  discriminate.
 Qed.


Lemma but_last_app {A} : forall s (x:A),
  but_last x s ++  simple_last x s :: nil = x::s.
Proof.
  induction s; simpl; auto.
  intros; simpl; now rewrite IHs.
Qed.

(* useful ??? *)
Lemma but_last_iota_from' j : forall i, but_last i (iota_from (S i) (S j)) =
                                       iota_from i (S j). 
 intros; rewrite but_last_iota_from.
 reflexivity.
Qed.


Definition ptwise_le: list nat -> list nat -> Prop := Forall2 le.

(** ** Lemmas *)

Lemma empty_interval i j : (j < i)%nat -> interval i j = nil.
Proof.
 unfold interval.
  intro H; replace (S j - i)%nat with 0.
  reflexivity.
  abstract lia.
Qed.

Lemma shift_iota_from : forall i l,  shift (iota_from i l) = iota_from (S i) l.
Proof.
  intros i l; revert i;induction l.
  - trivial.
  - cbn; intro; now rewrite IHl.
Qed.

Lemma shift_interval (i j: nat): shift (interval i j) = interval (S i) (S j).
Proof.
  unfold interval; rewrite shift_iota_from; f_equal.
Qed.

Lemma unshift_iota_from : forall i l,  unshift (iota_from (S i) l) =
                                       iota_from i l.
Proof.
  intros i l; revert i;induction l.
  - trivial.
  - cbn. intro; now rewrite IHl.
Qed.

Lemma unshift_interval (i j: nat): unshift (interval (S i) (S j)) =
                                   interval  i  j.
Proof.
 unfold interval;rewrite unshift_iota_from;f_equal.
Qed.

Lemma unshift_interval_pred (i j:nat) : 0 < j ->
  unshift (interval (S i) j) = interval i (Nat.pred j).
  Proof.
    destruct j.
   inversion 1.
   intro; simpl.
   now   rewrite unshift_interval.
  Qed.
  
Lemma shift_no_zero l : ~ In 0 (shift l).
Proof.
  induction l; destruct 1; [discriminate | auto].
Qed.



Lemma shift_unshift l : unshift (shift l) = l.
Proof.
  induction l; simpl in *; [trivial | now rewrite IHl].
Qed.

Lemma unshift_shift l (H: ~ In 0 l): shift (unshift l) = l.
Proof.
  induction l.
- reflexivity.
- simpl. destruct a.
 contradiction H; now left.
  simpl;  rewrite IHl; auto.
  intro; apply H; now right.
Qed.

Lemma unshift_pred : forall (s: list nat),  ~ In 0 s ->
                                            unshift s = List.map Nat.pred s.
Proof.
induction s.
 -  trivial.
 -  destruct a.
   +   destruct 1; now  left.
   +  simpl;  intro;  rewrite IHs; auto.
 Qed.

 
Lemma sorted_ge_Forall (n:nat) : forall l, sorted_ge n l ->
                                           Forall (fun x =>  n <= x) l.
Proof.
  induction 1.
  - left.
  - now right.
  - right.
   + assumption.
   +  eapply Forall_impl  with (P := (fun x: nat => p <= x)); [|trivial].
     intros; abstract lia.
Qed.


Lemma sorted_ge_trans n p l : n <= p -> sorted_ge p l -> sorted_ge n l.
induction 2.  
- constructor 1.
- constructor 2; eauto with arith.
- constructor 3; [eauto with arith |assumption | assumption].
Qed.


Lemma sorted_ge_not_In (n:nat) : forall l, sorted_ge (S n) l ->
                                           ~ In n l.
Proof.
 intros l H; generalize (sorted_ge_Forall _ _ H); intros H0 H1.
 rewrite Forall_forall in H0. generalize (H0 n).
 intro H2; generalize (H2 H1). 
 abstract lia.
Qed.



Hint Constructors sorted_ge : lists.


Lemma sorted_inv_gt : forall n p s, sorted_ge n (p::s) ->
                                    (p < n)%nat -> False.
Proof.
 inversion_clear 1 ; intro;abstract lia.
Qed.

Lemma iota_from_app n p :
  iota_from n (S p) = iota_from n p ++ (n+p::nil)%nat.
Proof.
  revert n; induction p; simpl.
  -  intros; f_equal; abstract lia.
  -  intros;  f_equal; replace (n + S p)%nat with (S n + p)%nat.
     +  rewrite  <- IHp; auto.
     +  abstract lia.
Qed.

Lemma iota_from_plus : forall k i j, iota_from i (k+j) =
                                     iota_from i k ++ iota_from (k+i) j.
Proof.
  induction k; simpl.
  - trivial.    
  - intros; rewrite IHk; repeat  f_equal; abstract lia.
Qed.

Lemma interval_not_empty : forall i j, i <= j -> interval i j <> nil.
Proof.
  induction 1.
  - unfold interval.
    case_eq (S i -  i).
    + intro; abstract lia.
    + simpl. destruct i; discriminate.
  -  cbn.
     destruct i.
     cbn; discriminate.
     destruct i; cbn.
     discriminate.
     case_eq (m - i).
     intro; abstract lia.
     cbn; discriminate.
Qed.

Lemma interval_not_empty_iff (n p : nat) :
  interval n p <> nil <-> (n <= p)%nat.
Proof.
  split.
  - intro H; destruct (le_lt_dec n p); [trivial| ].

   apply empty_interval in l.
   contradiction.
    - apply interval_not_empty.
Qed.

Lemma interval_singleton (i:nat) : interval i i = i::nil.
Proof.
  unfold interval; replace (S i - i) with 1;  [reflexivity | lia].
Qed.

Lemma interval_app (i j k:nat):
  (i <= j)%nat -> (j <= k)%nat ->
  interval i k = interval i j ++ interval (S j) k.
Proof.
  unfold interval;intros.
  replace (S k - i)%nat with ((S j - i) + (S k - S j))%nat.
  - rewrite iota_from_plus;repeat f_equal; lia.
  - abstract lia.
Qed.

Lemma iota_from_unroll i l : iota_from i (S l) = i :: iota_from (S i) l.
Proof. reflexivity. Qed.

Lemma interval_unroll : forall i j:nat , (i < j)%nat ->
                                       interval i j = i :: interval (S i) j.
Proof.
  intros.
  change (interval i j = (i :: nil) ++ interval (S i) j).
  replace (i::nil) with (interval i i).
  rewrite  interval_app with i i j.
  reflexivity.
  auto with arith.
  auto with arith.
  unfold interval.
  replace (S i - i)%nat with 1.
  reflexivity.
  abstract lia.
Qed.


Lemma iota_from_sorted_ge : forall p n q : nat,
    (q <= n)%nat  ->
    sorted_ge q (iota_from n p).
Proof.
  induction p.  
  - constructor.
  - simpl; destruct p.
     + constructor 2 ; auto.
     +  simpl; simpl in IHp;  constructor 3; auto.
Qed.

Lemma interval_sorted_ge: forall p n q : nat,  (q <= n)%nat ->
                                                sorted_ge q (interval n p).
 unfold interval; intros; now apply iota_from_sorted_ge.
Qed.

Lemma iota_from_lt_not_In i j l : i < j -> ~ In i (iota_from j l).
Proof.
   intros; generalize (iota_from_sorted_ge l j (S i) H ).
   intros; now apply sorted_ge_not_In.
Qed.

Lemma interval_lt_not_In :
  forall i j k,  i < j -> ~ In i (interval j k).
Proof.
  intros; unfold interval; now apply iota_from_lt_not_In.
Qed.


Section Forall2_right_induction.

Inductive Forall2R {A B: Type} (R: A -> B -> Prop) : list A -> list B -> Prop :=
  Forall2R_nil : Forall2R R nil nil
| Forall2R_last : forall l l' x y l1 l'1, Forall2R R l l' ->
                                          R x y ->
                                          l1 = l++(x::nil) ->
                                          l'1 = l' ++ (y::nil) ->
                                          Forall2R R l1 l'1.

Remark Forall2R_cons {A B: Type} (R: A -> B -> Prop):
  forall l l',  Forall2R R l l' -> forall x y, R x y -> Forall2R R (x::l) (y:: l').
  induction 1.
  - intros.
    eright with nil nil x y ; auto.
    left.          
  -  intros; subst;  right with (x0::l) (y0::l') x y; auto.
Qed. 

     
Remark Forall2_R  {A B: Type} (R: A -> B -> Prop) :
  forall l l', Forall2 R l l' -> Forall2R R l l'.
  induction 1.
  - constructor. 
  - inversion IHForall2.
     + eright with nil nil x y;auto.
       now left.     
     + subst; apply Forall2R_cons; auto.
Qed.


Remark Forall2_RR  {A B: Type} (R: A -> B -> Prop) :
  forall l l', Forall2R R l l' -> Forall2 R l l'.
Proof.
  induction 1.
  - constructor. 
  - subst; apply Forall2_app; auto.
Qed.

Lemma Forall2R_iff {A B: Type} (R: A -> B -> Prop) :
  forall l l', Forall2R R l l' <-> Forall2 R l l'.
Proof. 
  split.
  - intro;now  apply Forall2_RR .
  - intro;now  apply Forall2_R .
Qed. 


Lemma Forall2_indR {A B : Type} (R : A -> B -> Prop) (P : list A -> list B -> Prop):
P nil nil ->
(forall (l : list A) (l' : list B) (x : A) (y : B) 
   (l1 : list A) (l'1 : list B),
 Forall2 R l l' -> P l l' ->
 R x y -> l1 = l ++ x :: nil -> l'1 = l' ++ y :: nil -> P l1 l'1) ->
  forall (l : list A) (l0 : list B), Forall2 R l l0 -> P l l0.
Proof. 
  intros; rewrite  <- Forall2R_iff in  H1.
  eapply Forall2R_ind; eauto.
  intros; subst.
  eapply H0 with l1 l' x y; auto.  
  now  rewrite  <- Forall2R_iff .
Qed.    

End  Forall2_right_induction.






Lemma sorted_le : forall i j X, i <= j ->
                                sorted_ge j X ->
                                sorted_ge i X.
Proof.
  induction 2; eauto with arith lists. 
Qed.



  
Lemma sorted_tail : forall i j X, sorted_ge i (j::X) ->
                                  sorted_ge i X.
Proof.   
  inversion 1.
  -   constructor.
  -   destruct s; auto. 
      all:  inversion H4;eauto with arith lists.
Qed.

Lemma sorted_tail' : forall i j X, sorted_ge i (j::X) ->
                                   sorted_ge j X.
Proof.
  inversion_clear  1; auto with lists.
Qed. 

Lemma sorted_head : forall n m s, sorted_ge n (m::s)
                                  -> n<=m.
Proof.
  induction s. 
  - inversion 1; auto. 
  - inversion_clear 1.
    apply IHs.
  inversion_clear H2.   
  +   constructor; auto with arith.
  +  constructor; eauto with arith.
     eapply sorted_le;eauto.
Qed.



Lemma Sorted_mono {A:Type}(R S : relation A)
      (Hincl : forall x y, R x y -> S x y):
  forall l, Sorted R l -> Sorted S l.
Proof.   
  induction 1; auto. 
  constructor; auto. 
  destruct H0;auto. 
Qed.



Lemma sorted_ge_iff0 : forall l n, sorted_ge n l <->
                                    LocallySorted Peano.lt l /\
                                    List.Forall (fun i => n <= i) l.
Proof.
  induction l.
  - split; auto with lists.
    split; auto with lists; constructor.
  - destruct l.    
    + split.
      * split; auto with lists.
        constructor.
        constructor.        
        eapply  sorted_head; eauto.
        constructor.    
      *   destruct 1;  constructor;  inversion H0;auto.
    +  repeat  split.
      *  inversion_clear H; auto.     
         rewrite IHl in H2.
         constructor;tauto.
      *   inversion_clear H.
          rewrite IHl in H2.
          constructor; auto.
          destruct H2.
          eapply Forall_impl.
          2:eapply H2.
          intros;   transitivity a.
          auto. 
          apply H3.
      *  destruct 1.
         constructor.
           inversion_clear H0; auto. 
           inversion_clear H; auto.
           inversion_clear H.
           rewrite IHl.
           split; auto.
           constructor;  auto with arith.
           apply Sorted_extends.
           intros x y z Hxy Hyz.
           eauto with arith.
           apply Sorted_mono with Peano.lt.
           eauto with arith. 
           rewrite <- Sorted_LocallySorted_iff in H1.
           inversion_clear H1.
           constructor;auto.
           induction H3.
           constructor.
           constructor. 
           eauto with arith. 
Qed. 

Lemma sorted_ge_iff : forall l n, sorted_ge n l <->
                                    Sorted lt l /\
                                    List.Forall (fun i => n <= i) l.
Proof.  
 intros.
 rewrite Sorted_LocallySorted_iff.
 apply sorted_ge_iff0.
Qed.


Lemma sorted_ge_prefix :
  forall  l1 n l2, sorted_ge n (l1 ++ l2) -> sorted_ge n l1.
  induction l1.
  - constructor.
  - 
    destruct l1.
    constructor.
    cbn in H.
    eapply sorted_head; eauto.
    constructor.
    cbn in H.
    eapply sorted_head; eauto.
    inversion_clear H.
    auto. 
    eapply IHl1.
    inversion_clear H.
    eauto. 
Qed. 


Lemma sorted_In : forall i X, Sorted lt (i::X) -> forall j, In j X -> i < j.
Proof.
  intros.
  apply Sorted_StronglySorted in H.
  apply StronglySorted_inv in H.
  destruct H.
  rewrite Forall_forall in H1.
  auto.
  red. 
  intros; abstract lia.
Qed.

Lemma sorted_not_in_tail : forall  i j X, Sorted lt (i::X)   -> j<=i ->
                                           ~ (In j X).
Proof.
 intros. 
 red; intro. 
 specialize (sorted_In _ _ H j H1).
 intro; abstract lia.
Qed.

Remark simple_last_correct {A}: forall s (x:A), simple_last x s = last s x.
  induction s. 
  - now cbn.
  -  cbn.   
     destruct s.
     now cbn.
     auto.
Qed.

Lemma In_sorted_ge_inv : forall x y s,
                             In x (y::s) ->
                             sorted_ge y s ->
                             y < x /\ In x s \/ y = x.
Proof.
  intros x y s H H0;  destruct H.
  -    subst; auto. 
  -  destruct (lt_eq_lt_dec x y) as [[H1 | H2] | H3].
   +  rewrite   sorted_ge_iff in H0;  destruct H0.
     rewrite Forall_forall in H2;  specialize (H2 x H);  elimtype False.
     abstract lia.
   +   subst; auto. 
   +  auto. 
Qed. 


Lemma incl_inv : forall x y l1 l2,  Sorted lt (x::l1) ->
                                    Sorted lt (y::l2)  ->
                                    incl (x::l1)(y::l2) ->
                                    y <= x /\ incl l1 l2.
Proof. 
  intros.
  red in H1.
  assert (y <= x).
  {
    specialize (H1 x (in_eq x  l1)).   
    destruct H1.
    subst; auto with arith.   

    specialize (sorted_In _ _ H0 _ H1).
    auto with arith.
  }   
  split;auto.
  intros z Hz.
  assert (x < z). {

    specialize (sorted_In _ _ H _ Hz).
    auto.
  }
  assert (y < z).
  eauto with arith. 

  specialize (H1 z).
  destruct H1.
  right;auto.
  subst.
  elimtype False.
  abstract lia.
  auto.
Qed.


Lemma incl_decomp : forall l1 l2,  Sorted lt l1 ->
                                   Sorted lt l2  ->
                                   incl l1 l2 ->
                                   exists l3 l4,  l2 = l3 ++ l4 /\
                                                  ptwise_le l3 l1.
  induction l1.
  intros; exists nil, l2.
  split.
  reflexivity.
  constructor.
  destruct l2.
  intros.
  red in H1.
  destruct (H1 a) ;auto.
  now left.
  intros.   
  destruct (incl_inv a n l1 l2);auto.
  destruct (IHl1 l2).
  now inversion_clear H.
  now inversion_clear H0.
  auto. 
  destruct H4 as [l4 [H5 H6]].
  subst.
  exists (n::x), l4.
  split;auto. 
  constructor.
  auto.
  
  auto.
Qed.


  Lemma simple_last_app {A}: forall l l1 (x y:A), simple_last x (l++(y::l1))  =
                                     simple_last y l1 .
  induction l; cbn.
  - reflexivity.     
  - intros; now rewrite IHl.
Qed.


Lemma simple_last_app1 {A}: forall l (x y:A), simple_last x (l++(y::nil))  = y.
Proof.
  intros; now rewrite simple_last_app. 
Qed.


Lemma sorted_max_1 : forall s n, sorted_ge n s ->
                                 (n <= simple_last n s)%nat.
  induction s; cbn.
  - auto with arith. 
  -  intros; destruct s.
    + now inversion_clear H.
    + inversion_clear H; transitivity a; auto.  
Qed.


Lemma sorted_cut :forall l1 n x l2, sorted_ge n (l1++(x::l2)) ->
                                    simple_last n l1 <= x.
  induction l1.
  - cbn;  eapply sorted_head; eauto. 
  - cbn; intros; eapply IHl1 with l2.
    cbn in H;    inversion_clear H; auto with lists.
Qed.

Lemma sorted_max_2 : forall s n, sorted_ge n s ->
                                 Forall (fun i =>
                                           (i <= simple_last n s)%nat)
                                        s.
Proof.
  induction s; cbn.
  - intros; simpl; constructor.
  -     constructor.
       +  apply sorted_max_1; inversion H;auto with lists. 
       + apply IHs; eapply sorted_tail'; eauto with lists.
Qed. 


Lemma sorted_ge_suffix :
  forall  l1 n l2, sorted_ge n (l1 ++ l2) -> sorted_ge (simple_last n l1) l2.
  induction l1.
  -  intros; cbn. assumption. 
  -  destruct l1.
    + cbn; inversion_clear 1; auto with lists.
    + inversion_clear 1; cbn in *; eauto with lists.
Qed. 

