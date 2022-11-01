(** To do : Is it a clone of ListSet ? *)

(** Evelyne Contejean, LRI *)

(** * Sets built with lists *)

Set Implicit Arguments. 

From Coq Require Import List Arith Lia.

From hydras Require Import more_list list_permut.


Module Type S.

Declare Module DS : decidable_set.S.

Definition elt := DS.A.
Definition eq_elt_dec := DS.eq_A_dec.

Fixpoint without_red (l : list elt) {struct l} : Prop :=
  match l with
  | nil => True
  | e :: le => if (In_dec eq_elt_dec e le) then False else without_red le
  end.

Record t : Set :=
  mk_set 
  {
     support : list elt;
     is_a_set : without_red support
  }.

Definition cardinal s := List.length s.(support).

Definition subset s1 s2 : Prop :=
  forall e, In e s1.(support) -> In e s2.(support).

Axiom cardinal_subset :
  forall s1 s2, subset s1 s2 -> cardinal s1 <= cardinal s2.

End S.

(** ** Definition of sets using lists. *)
Module Make (DS1 : decidable_set.S) <: S with Module DS:= DS1.

Module DS := DS1.
Import DS1.
Module LP := list_permut.Make (DS1).

Definition elt := DS.A.
Definition eq_elt_dec : forall t1 t2 : elt, {t1 = t2} + {t1 <> t2} := DS.eq_A_dec.

(*** Property of being without redundancy for lists of elements, intended as sets. *)
Fixpoint without_red (l : list elt) {struct l} : Prop :=
  match l with
  | nil => True
  | e :: le => if (In_dec eq_elt_dec e le) then False else without_red le
  end.

(*** Definition of sets as lists without redundancy and a proof of this fact. *)
Record t : Set :=
  mk_set 
  {
     support : list elt;
     is_a_set : without_red support
  }.

Definition mem e s := In e s.(support).

Lemma mem_dec : forall e s, {mem e s}+{~mem e s}.
Proof.
intros e s; unfold mem; apply (In_dec eq_elt_dec).
Qed.

Lemma add_prf :
  forall e l, without_red l -> ~In e l -> without_red (e :: l).
Proof.
intros e l Wl e_not_in_l; simpl; 
destruct (In_dec eq_elt_dec e l) as [e_in_l | _]; trivial;
apply e_not_in_l; trivial.
Qed.

Definition add e s :=
  match In_dec eq_elt_dec e s.(support) with
  | left _ => s
  | right R => mk_set (e :: s.(support)) (add_prf e s.(support) s.(is_a_set) R)
  end.

Lemma add_1 : forall e s, mem e (add e s).
Proof.
intros e s; unfold mem, add; simpl;
destruct (In_dec eq_elt_dec e (support s)) as [e_in_s | e_not_in_s].
trivial.
left; trivial.
Qed.

Lemma add_2 : forall e e' s, mem e s -> mem e (add e' s).
Proof.
intros e e' s; unfold mem, add; simpl; 
destruct (In_dec eq_elt_dec e' (support s)) as [e'_in_s | e'_not_in_s].
trivial.
right; trivial.
Qed.

Lemma add_12 : forall e e' s, mem e (add e' s) -> e = e' \/ mem e s.
Proof.
intros e e' s; unfold mem, add; simpl;
destruct (In_dec eq_elt_dec e' (support s)) as [e'_in_s | e'_not_in_s].
right; trivial.
intros [e'_eq_e | e_in_s]; [left; subst | right]; trivial.
Qed.

Fixpoint filter_aux (P : elt -> Prop) (P_dec : forall e, {P e}+{~ P e})
   (l : list elt) {struct l} : list elt :=
  match l with
  | nil => nil
  | e :: le => 
           if (P_dec e)
           then e :: (filter_aux P P_dec le) 
           else filter_aux P P_dec le
   end.

(*** Properties of filter. *)
Lemma included_filter_aux : 
forall P P_dec e l, In e (filter_aux P P_dec l) -> In e l.
Proof.
intros P P_dec x l; induction l as [ | e le ].
contradiction.
simpl; destruct (P_dec e) as [ _ | _].
intros [x_eq_e | x_in_rrle]; simpl.
left; trivial.
right; apply IHle; trivial.
intro; right; apply IHle; trivial.
Qed.

Lemma without_red_filter_aux :  
  forall P P_dec l, without_red l -> without_red (filter_aux P P_dec l).
Proof.
intros P P_dec l; induction l as [ | e le]; simpl; trivial.
destruct (P_dec e) as [ _ | _ ];
destruct (In_dec eq_elt_dec e le) as [ in_e_le | not_in_e_le]; 
trivial; try contradiction.
simpl;
destruct (In_dec eq_elt_dec e (filter_aux P P_dec le)) as [ in_e_rrle | _]; 
trivial;
absurd (In e le); trivial.
apply included_filter_aux with P P_dec; trivial.
Qed.

Definition filter P P_dec s := 
   mk_set (filter_aux P P_dec s.(support))
               (without_red_filter_aux P P_dec _ s.(is_a_set)).

Lemma filter_1_list :
  forall (P : elt -> Prop) P_dec l e, In e l -> P e -> In e (filter_aux P P_dec l).
Proof.
intros P P_dec l; induction l as [ | e' l ].
contradiction.
intros e [e_eq_e' | e_in_l] Pe.
subst e'; simpl.
destruct (P_dec e) as [ _ | not_Pe].
left; trivial.
absurd (P e); trivial.
simpl; destruct (P_dec e') as [ _ | _ ]; [ right | idtac ]; apply IHl; trivial.
Qed.

Lemma filter_1 :
  forall (P : elt -> Prop) P_dec s e, mem e s -> P e -> mem e (filter P P_dec s).
Proof.
unfold mem, support; 
intros P P_dec [l wr] e e_in_s P_e; simpl;  apply filter_1_list; trivial.
Qed.

Lemma filter_2_list :
 forall (P : elt -> Prop) P_dec l e, In e (filter_aux P P_dec l) ->
                In e l /\ P e.
Proof.
intros P P_dec l; induction l as [ | e' l].
contradiction.
intros e; simpl; destruct (P_dec e') as [ Pe' | not_Pe' ].
intros [e_eq_e' | e_in_fltl].
subst; split; trivial; left; trivial.
generalize (IHl _ e_in_fltl); intros [e_in_l Pe]; split; trivial; right; trivial.
intro e_in_fltl;
generalize (IHl _ e_in_fltl); intros [e_in_l Pe]; split; trivial; right; trivial.
Qed.

Lemma filter_2 :
 forall (P : elt -> Prop) P_dec s e, mem e (filter P P_dec s) ->
                mem e s /\ P e.
Proof.
unfold mem, support; 
intros P P_dec [l wr] e e_in_l_and_P_e; apply filter_2_list with P_dec; trivial.
Qed.

(*** How to remove redundancies from a list with remove_red. *)
Fixpoint remove_red (l : list elt) : list elt :=
  match l with
  | nil => nil
  | e :: le => 
           if (In_dec eq_elt_dec e le) 
           then remove_red le 
           else e :: (remove_red le)
   end.

Lemma included_remove_red : 
forall e l, In e (remove_red l) -> In e l.
Proof.
intros x l; induction l as [ | e le ].
contradiction.
simpl; destruct (In_dec eq_elt_dec e le) as [ _ | _].
intro; right; apply IHle; trivial.
intros [x_eq_e | x_in_rrle]; simpl.
left; trivial.
right; apply IHle; trivial.
Qed.

Lemma remove_red_included : forall e l, In e l -> In e (remove_red l).
Proof.
intros x l; induction l as [ | e le ].
contradiction.
intros [x_eq_e | x_in_le]; simpl.
subst x; destruct (In_dec eq_elt_dec e le) as [ in_e_le | not_in_e_le];
[ apply IHle | left ]; trivial.
destruct (In_dec eq_elt_dec e le) as [ in_e_le | not_in_e_le];
[ idtac | right]; apply IHle; trivial.
Qed.

Lemma without_red_remove_red :  forall l, without_red (remove_red l).
Proof.
intro l; induction l as [ | e le]; simpl; trivial.
destruct (In_dec eq_elt_dec e le) as [ in_e_le | not_in_e_le]; trivial.
simpl; 
destruct (In_dec eq_elt_dec e (remove_red le)) as [ in_e_rrle | _]; 
trivial;
absurd (In e le); trivial; apply included_remove_red; trivial.
Qed.

Lemma without_red_remove :
  forall e l1 l2, without_red (l1 ++ e :: l2) -> without_red (l1 ++ l2).
Proof.
intros e l1; generalize e; clear e; induction l1 as [ | e1 l1];
intros e l2; simpl.
destruct (In_dec eq_elt_dec e l2); trivial; contradiction.
destruct (In_dec eq_elt_dec e1 (l1 ++ e :: l2)) as [ | not_in_e1].
contradiction.
destruct (In_dec eq_elt_dec e1 (l1 ++ l2)) as [ in_e1 | _].
intros _; apply not_in_e1;
generalize (@in_app_or _ _ _ _ in_e1); clear in_e1; intros [ in_e1 | in_e1];
apply in_or_app; [left | right; right]; trivial.
intro; apply (IHl1 e l2); trivial.
Qed.

Lemma without_red_add :
  forall e l1 l2, without_red (l1 ++ l2) -> ~In e (l1 ++ l2) ->
  without_red (l1 ++ e :: l2).
Proof.
intros e l1; generalize e; clear e; induction l1 as [ | e1 l1];
intros e l2 wr12 e_not_in_l1_l2.
simpl; destruct (In_dec eq_elt_dec e l2) as [e_in_l2 | _]; trivial.
absurd (In e l2); trivial.
simpl.
destruct (In_dec eq_elt_dec e1 (l1 ++ e :: l2)) 
    as [e1_in_l1_e_l2 | e_not_in_l1_e_l2].
destruct (in_app_or _ _ _ e1_in_l1_e_l2) as [e1_in_l1 | [e1_eq_e | e1_in_l2]].
simpl in wr12; 
destruct (In_dec eq_elt_dec e1 (l1 ++ l2)) as [e1_in_l1_l2 | e1_not_in_l1_l2].
trivial.
absurd (In e1 (l1 ++ l2)); trivial; apply in_or_app; left; trivial.
subst e; absurd (In e1 ((e1 :: l1) ++ l2)); trivial; left; trivial.
simpl in wr12; 
destruct (In_dec eq_elt_dec e1 (l1 ++ l2)) as [e1_in_l1_l2 | e1_not_in_l1_l2].
trivial.
absurd (In e1 (l1 ++ l2)); trivial; apply in_or_app; right; trivial.

apply IHl1.
apply (without_red_remove e1 nil (l1 ++ l2)); trivial.
intro e_in_l1_l2; apply e_not_in_l1_l2; right; trivial.
Qed.

(*** Empty set. *)
Lemma without_red_nil : without_red nil.
Proof.
simpl; trivial.
Qed.

Definition empty : t :=
  mk_set nil without_red_nil.

(*** Singleton *)
Lemma without_red_singleton : forall e : elt, without_red (e :: nil).
Proof.
intro e; simpl; destruct (In_dec eq_elt_dec e nil); trivial.
Qed.

Definition singleton (e : elt) : t :=
  mk_set (e :: nil) (without_red_singleton e).

(*** How to build a set from a list of elements. *)
Definition make_set (l : list elt) : t :=
  mk_set (remove_red l) (without_red_remove_red l).

(*** Union of sets. *)
Fixpoint add_without_red (acc l : list elt) {struct l} : list elt :=
  match l with
  | nil => acc
  | e :: le =>
     if (In_dec eq_elt_dec e acc)
     then add_without_red acc le
     else add_without_red (e :: acc) le
  end.

Lemma without_red_add_without_red :
  forall l1 l2, without_red l1 -> without_red (add_without_red l1 l2).
Proof.
intros l1 l2; generalize l1; clear l1; induction l2 as [ | e le]; 
intros l1 wr1; simpl; trivial.
destruct (In_dec eq_elt_dec e l1) as [ _ | not_in_e_l1];
apply IHle; trivial.
simpl; destruct (In_dec eq_elt_dec e l1) as [ in_e_l1 | _]; trivial;
absurd (In e l1); trivial.
Defined.

Definition union s1 s2 :=
  mk_set (add_without_red s1.(support) s2.(support))
               (without_red_add_without_red s1.(support) s2.(support) s1.(is_a_set)).

Lemma union_1_aux :
forall (l1 l2 : list elt) (e : elt), In e l1 -> In e (add_without_red l1 l2).
Proof.
intros l1 l2; generalize l1; clear l1; induction l2 as [ | e2 l2].
intros; trivial.
intros l1 e e_in_l1; simpl; case ( In_dec eq_elt_dec e2 l1); intro; apply IHl2; trivial.
right; trivial.
Qed.

Lemma union_1 : forall s1 s2 e, mem e s1 -> mem e (union s1 s2).
Proof.
unfold mem; intros [l1 wr1] [l2 wr2] e; simpl; apply union_1_aux. 
Qed.

Lemma union_2_aux :
forall (l1 l2 : list elt) (e : elt), In e l2 -> In e (add_without_red l1 l2).
Proof.
intros l1 l2; generalize l1; clear l1; induction l2 as [ | e2 l2];
intros l1 e e_in_e2l2.
contradiction.
simpl; destruct (In_dec eq_elt_dec e2 l1) as [ e2_in_l1 | e2_not_in_l1];
destruct e_in_e2l2 as [e_eq_e2 | e_in_l2].
subst; apply union_1_aux; trivial.
apply IHl2; trivial.
subst; apply union_1_aux; left; trivial.
apply IHl2; trivial.
Qed.

Lemma union_2 : forall s1 s2 e, mem e s2 -> mem e (union s1 s2).
Proof.
unfold mem; intros [l1 wr1] [l2 wr2] e; simpl; apply union_2_aux.
Qed.

Lemma union_12_aux :
forall (l1 l2 : list elt) (e : elt), In e (add_without_red l1 l2) -> In e l1 \/ In e l2.
Proof.
intros l1 l2; generalize l1; clear l1; induction l2 as [ | e2 l2]; 
intros l1 e; simpl.
intro; left; trivial.
destruct (In_dec eq_elt_dec e2 l1) as [ e2_in_l1 | e2_not_in_l1 ].
intro H; generalize (IHl2 _ _ H); intuition.
intro H; generalize (IHl2 _ _ H); simpl; intuition.
Qed.

Lemma union_12 : 
  forall s1 s2 e, mem e (union s1 s2) -> mem e s1 \/ mem e s2.
Proof.
unfold mem; intros [l1 wr1] [l2 wr2] e; simpl; apply union_12_aux.
Qed.

Fixpoint remove_not_common (acc l1 l2 : list elt) {struct l2} : list elt :=
  match l2 with
  | nil => acc
  | e :: l => 
      if In_dec eq_elt_dec e l1 
      then remove_not_common (e :: acc) l1 l
      else remove_not_common acc l1 l
  end.

Lemma without_red_remove_not_common_aux :
  forall acc l1 l2, (forall e, In e acc /\ In e l2 -> False) ->
                           without_red acc -> without_red l1 -> without_red l2 -> 
                           without_red (remove_not_common acc l1 l2).
Proof.
intros acc l1 l2; generalize acc l1; clear acc l1; induction l2 as [ | e2 l2].
intros; trivial.
intros acc l1 H wra wr1 wr2; simpl;
destruct (In_dec eq_elt_dec e2 l1) as [ e2_in_l1 | e2_not_in_l1 ];
apply IHl2; trivial.
intros e [[e_eq_e2 | e_in_acc] e_in_l2].
subst e; simpl in wr2;
destruct (In_dec eq_elt_dec e2 l2) as [ _ | e2_not_in_l2]; trivial;
absurd (In e2 l2); trivial.
apply (H e); split; trivial; right; trivial.
simpl; destruct (In_dec eq_elt_dec e2 acc) as [ e2_in_acc | _]; trivial.
apply (H e2); split; trivial; left; trivial.
apply (without_red_remove e2 nil l2); trivial.
intros e [e_in_acc e_in_l2]; apply (H e); split; trivial; right; trivial.
apply (without_red_remove e2 nil l2); trivial.
Qed.

Lemma without_red_remove_not_common :
  forall l1 l2, without_red l1 -> without_red l2 ->
                    without_red (remove_not_common nil l1 l2).
Proof.
intros l1 l2 wr1 wr2; 
apply without_red_remove_not_common_aux; trivial.
intros e [ H _ ]; contradiction.
simpl; trivial.
Qed.

Definition inter s1 s2 :=
  mk_set (remove_not_common nil s1.(support) s2.(support)) 
               (without_red_remove_not_common _ _ s1.(is_a_set) s2.(is_a_set)).

Lemma inter_1_aux : 
  forall acc l1 l2 e, In e (remove_not_common acc l1 l2) -> In e acc \/ In e l1.
Proof.
intros acc l1 l2; generalize acc l1; clear acc l1; induction l2 as [ | e2 l2].
intros acc l1; simpl; intros; left; trivial.
intros acc l1 e; simpl;
destruct (In_dec eq_elt_dec e2 l1) as [ e2_in_l1 | e2_not_in_l1 ].
intros H; destruct (IHl2 _ _ _ H) as [[ e2_eq_e | e_in_acc ] | e_in_l1 ]; clear H.
subst; right; trivial.
left; trivial.
right; trivial.
intros H; apply IHl2; trivial.
Qed.

Lemma inter_1 : forall s1 s2 e, mem e (inter s1 s2) -> mem e s1. 
Proof.
intros [l1 wr1] [l2 wr2] e H; simpl.
generalize (inter_1_aux nil l1 l2 e H).
intros [ H' | H']; trivial; contradiction.
Qed.

Lemma inter_2_aux : 
  forall acc l1 l2 e, In e (remove_not_common acc l1 l2) -> In e acc \/ In e l2.
Proof.
intros acc l1 l2; generalize acc l1; clear acc l1; induction l2 as [ | e2 l2].
intros acc l1; simpl; intros; left; trivial.
intros acc l1 e; simpl;
destruct (In_dec eq_elt_dec e2 l1) as [ e2_in_l1 | e2_not_in_l1 ].
intros H; destruct (IHl2 _ _ _ H) as [[ e2_eq_e | e_in_acc ] | e_in_l2 ]; clear H.
right; left; trivial.
left; trivial.
right; right; trivial.
intros H; destruct (IHl2 _ _ _ H) as [ e_in_acc  | e_in_l2 ]; clear H.
left; trivial.
right; right; trivial.
Qed.

Lemma inter_2 : forall s1 s2 e, mem e (inter s1 s2) -> mem e s2.
Proof.
intros [l1 wr1] [l2 wr2] e H; simpl.
generalize (inter_2_aux nil l1 l2 e H).
intros [ H' | H']; trivial; contradiction.
Qed.

Lemma inter_12_aux :
  forall acc l1 l2 e,  In e l1 -> In e l2 -> In e (remove_not_common acc l1 l2).
Proof.
assert (H : forall acc l1 l2 e, In e acc -> In e (remove_not_common acc l1 l2)).
intros acc l1 l2; generalize acc l1; clear acc l1; induction l2 as [ | e2 l2].
intros; simpl; trivial.
intros acc l1 e e_in_acc; simpl;
destruct (In_dec eq_elt_dec e2 l1) as [ _ | e2_not_in_l1 ].
apply IHl2; right; trivial.
apply IHl2; trivial.

intros acc l1 l2; generalize acc l1; clear acc l1; induction l2 as [ | e2 l2].
intros; contradiction.
intros acc l1 e e_in_l1 [ e_eq_e2 | e_in_l2 ]; simpl;
destruct (In_dec eq_elt_dec e2 l1) as [ _ | e2_not_in_l1 ].
subst e; apply H; left; trivial.
subst e; absurd (In e2 l1); trivial.
apply IHl2; trivial.
apply IHl2; trivial.
Qed.

Lemma inter_12 : 
  forall s1 s2 e, mem e s1 -> mem e s2 -> mem e (inter s1 s2).
Proof.
intros [l1 wr1] [l2 wr2] e e_in_l1 e_in_l2; 
refine (inter_12_aux nil l1 l2 e _ _); trivial.
Qed.

(*** Subset. *)
Definition subset s1 s2 : Prop :=
  forall e, mem e s1 -> mem e s2.

Lemma subset_dec : forall s1 s2, {subset s1 s2} + {~ subset s1 s2}.
Proof.
intros [l1 wr1]; induction l1 as [ | e1 l1]; intros [l2 wr2].
left; intro e; contradiction.
destruct (In_dec eq_elt_dec e1 l2) as [ e1_in_l2 | e1_not_in_l2 ].
assert (wr1' := without_red_remove e1 nil l1 wr1); simpl in wr1'.
destruct (IHl1 wr1' (mk_set l2 wr2)) as [ s1_incl_s2 | s1_not_incl_s2 ].
left; intros e [e_eq_e1 | e_in_l1]; [subst | apply s1_incl_s2]; trivial.
right; intro H; apply s1_not_incl_s2; intros e e_in_l1; apply H; right; trivial.
right; intro H; apply e1_not_in_l2; apply H; left; trivial.
Qed.

Lemma subset_union_1 :
  forall s1 s2, subset s1 (union s1 s2).
Proof.
intros s1 s2 e; apply union_1.
Qed.

Lemma subset_union_2 :
  forall s1 s2, subset s2 (union s1 s2).
Proof.
intros s1 s2 e; apply union_2.
Qed.

Lemma subset_inter_1 :
  forall s1 s2, subset (inter s1 s2) s1.
Proof.
intros s1 s2 e; apply inter_1.
Qed.

Lemma subset_inter_2 :
  forall s1 s2, subset (inter s1 s2) s2.
Proof.
intros s1 s2 e; apply inter_2.
Qed.

(*** Equality of sets. *)
Definition eq_set s1 s2 :=
  forall e, mem e s1 <-> mem e s2.

Lemma eq_set_dec : forall s1 s2, {eq_set s1 s2} + {~eq_set s1 s2}.
Proof.
intros s1 s2; destruct (subset_dec s1 s2) as [ s1_incl_s2 | s1_not_incl_s2 ].
destruct (subset_dec s2 s1) as [ s2_incl_s1 | s2_not_incl_s1 ].
left; intro e; intuition.
right; intro s1_eq_s2; apply s2_not_incl_s1; intros e e_in_s2; 
generalize (s1_eq_s2 e); intuition.
right; intro s1_eq_s2; apply s1_not_incl_s2; intros e e_in_s1;
generalize (s1_eq_s2 e); intuition.
Qed.

Lemma eq_set_refl : forall s, eq_set s s.
Proof.
intros s e; split; trivial.
Qed.

Lemma eq_set_sym :
  forall s1 s2, eq_set s1 s2 -> eq_set s2 s1.
Proof.
intros s1 s2 H e; generalize (H e); intuition.
Qed.

Lemma eq_set_trans :
  forall s1 s2 s3, eq_set s1 s2 -> eq_set s2 s3 -> eq_set s1 s3.
Proof.
intros s1 s2 s3 s1_eq_s2 s2_eq_s3 e; 
generalize (s1_eq_s2 e) (s2_eq_s3 e); intuition.
Qed.

Lemma add_comm :
  forall e1 e2 s, eq_set (add e1 (add e2 s)) (add e2 (add e1 s)).
Proof.
intros e1 e2 s e; split; intro H.
destruct (add_12 _ _ _ H) as [e_eq_e1 | e_in_e2_s].
apply add_2; subst; apply add_1.
destruct (add_12 _ _ _ e_in_e2_s) as [e_eq_e2 | e_in_s].
subst; apply add_1.
do 2 apply add_2; trivial.
destruct (add_12 _ _ _ H) as [e_eq_e2 | e_in_e1_s].
apply add_2; subst; apply add_1.
destruct (add_12 _ _ _ e_in_e1_s) as [e_eq_e1 | e_in_s].
subst; apply add_1.
do 2 apply add_2; trivial.
Qed.

Lemma union_empty_1 :
  forall s, eq_set s (union empty s).
Proof.
intros s e; generalize (union_12_aux nil (support s) e); simpl.
intuition.
apply union_2; trivial.
Qed.

Lemma union_empty_2 :
  forall s, eq_set s (union s empty).
Proof.
intros s e; simpl; intuition.
Qed.

Lemma union_comm :
  forall s1 s2, eq_set (union s1 s2) (union s2 s1).
Proof.
intros s1 s2 e; 
generalize (union_12 s1 s2 e) (union_1 s1 s2 e) (union_2 s1 s2 e)
(union_12 s2 s1 e)  (union_1 s2 s1 e) (union_2 s2 s1 e); intuition.
Qed.

Lemma union_assoc :
  forall s1 s2 s3, eq_set (union s1 (union s2 s3)) (union (union s1 s2) s3).
Proof.
intros s1 s2 s3 e; 
generalize (union_12 s1 (union s2 s3) e) (union_1 s1 (union s2 s3) e) 
 (union_2 s1 (union s2 s3) e)
(union_12 s2 s3 e) (union_1 s2 s3 e) (union_2 s2 s3 e)
(union_12 (union s1 s2) s3 e) (union_1 (union s1 s2) s3 e) 
  (union_2 (union s1 s2) s3 e)
(union_12 s1 s2 e)  (union_1 s1 s2 e) (union_2 s1 s2 e); intuition.
Qed.

Lemma filter_union :
  forall P P_dec s1 s2, 
  eq_set (filter P P_dec (union s1 s2))  (union (filter P P_dec s1) (filter P P_dec s2)).
Proof.
intros P P_dec [l1 wr1] [l2 wr2] e; split;
unfold mem, union, support; simpl; generalize l1 e; clear l1 wr1 wr2 e;
induction l2 as [ | e2 l2];
intros l1 e; trivial.
intro H; simpl in H; destruct (In_dec eq_elt_dec e2 l1) as [e2_in_l1 | e2_not_in_l1].
simpl; destruct (P_dec e2) as [P_e2 | not_P_e2].
simpl; destruct (In_dec eq_elt_dec e2 (filter_aux P P_dec l1)) 
 as [e2_in_l1_and_P_e2 | not_e2_in_l1_and_P_e2].
intros; apply IHl2; trivial.
absurd (In e2 (filter_aux P P_dec l1)); trivial; refine (filter_1_list _ _ _ _ _ _); trivial.
intros; apply IHl2; trivial.
generalize (IHl2 _ _ H); simpl; destruct (P_dec e2) as [P_e2 | not_P_e2].
simpl; destruct (In_dec eq_elt_dec e2 (filter_aux P P_dec l1)) 
 as [e2_in_l1_and_P_e2 | not_e2_in_l1_and_P_e2]; [idtac | trivial].
absurd (In e2 l1); trivial; generalize (filter_2_list _ _ _ _ e2_in_l1_and_P_e2); intuition.
trivial.

simpl; destruct (P_dec e2) as [P_e2 | not_P_e2].
destruct (In_dec eq_elt_dec e2 l1) as [e2_in_l1 | e2_not_in_l1].
simpl; destruct (In_dec eq_elt_dec e2 (filter_aux P P_dec l1)) 
 as [e2_in_l1_and_P_e2 | not_e2_in_l1_and_P_e2].
intros; apply IHl2; trivial.
absurd (In e2 (filter_aux P P_dec l1)); trivial; refine (filter_1_list _ _ _ _ _ _); trivial.
generalize (IHl2 (e2 :: l1) e); simpl; destruct (P_dec e2) as [_ | not_P_e2].
destruct (In_dec eq_elt_dec e2 (filter_aux P P_dec l1)) 
 as [e2_in_l1_and_P_e2 | not_e2_in_l1_and_P_e2]; [idtac | trivial].
absurd (In e2 l1); trivial; generalize (filter_2_list _ _ _ _ e2_in_l1_and_P_e2); intuition.
absurd (P e2); trivial.
destruct (In_dec eq_elt_dec e2 l1) as [ e2_in_l1 | e2_not_in_l1 ].
intro; apply IHl2; trivial.
intro H; refine (IHl2 (e2 :: l1) e _);
destruct (union_12_aux _ _ _ H) as [ H1 | H2 ].
apply union_1_aux; simpl; destruct (P_dec e2) as [ P_e2 | _]; trivial;
absurd (P e2); trivial.
apply union_2_aux; trivial.
Qed.

Lemma subset_filter :
  forall (P1 P2 : elt -> Prop) P1_dec P2_dec s1 s2, subset s1 s2 ->
  (forall e, P1 e -> P2 e) -> subset (filter P1 P1_dec s1) (filter P2 P2_dec s2).
Proof.
intros P1 P2 P1_dec P2_dec s1 s2 Hs HP e H;
generalize (filter_2 _ _ _ _ H); intros [e_in_s1 P1_e].
apply filter_1; [ apply (Hs e) | apply HP ]; trivial.
Qed.

Lemma subset_compat_1 :
  forall s1 s1' s2, eq_set s1 s1' -> subset s1 s2 -> subset s1' s2.
Proof.
intros s1 s1' s2 s1_eq_s1' H e e_in_s1';
apply H; generalize (s1_eq_s1' e); intuition.
Qed.

Lemma subset_compat_2 :
  forall s1 s2 s2', eq_set s2 s2' -> subset s1 s2 -> subset s1 s2'.
Proof.
intros s1 s2 s2' s2_eq_s2' H e e_in_s1;
generalize (s2_eq_s2' e) (H e e_in_s1);
intuition.
Qed.

Lemma subset_compat :
   forall s1 s1' s2 s2', eq_set s1 s1' -> eq_set s2 s2' -> 
                                    subset s1 s2 -> subset s1' s2'.
Proof.
intros s1 s1' s2 s2' s1_eq_s1' s2_eq_s2' H e e_in_s1';
generalize (s1_eq_s1' e) (s2_eq_s2' e) (H e);
intuition.
Qed.

Lemma union_compat_subset_1 :
  forall s1 s2 s, subset s1 s2 -> subset (union s1 s)  (union s2 s).
Proof.
intros [l1 wr1] [l2 wr2] [l wr]; unfold subset; simpl;
intros H e e_in_ll1.
generalize (union_12_aux _ _ _ e_in_ll1); intros [ e_in_l | e_in_l1]; trivial.
apply union_1; apply H; trivial.
apply union_2; trivial.
Qed.

Lemma union_compat_subset_2 :
  forall s1 s2 s, subset s1 s2 -> subset (union s s1)  (union s s2).
Proof.
intros [l1 wr1] [l2 wr2] [l wr]; unfold subset; simpl;
intros H e e_in_ll1.
generalize (union_12_aux _ _ _ e_in_ll1); intros [ e_in_l | e_in_l1]; trivial.
apply union_1; trivial.
apply union_2; apply H; trivial.
Qed.

Lemma union_compat_eq_set :
  forall s1 s1' s2 s2', eq_set s1 s1' -> eq_set s2 s2' -> 
    eq_set (union s1 s2) (union s1' s2').
Proof.
intros s1 s1' s2 s2' s1_eq_s1' s2_eq_s2' e; split; intro H.
generalize (union_12 s1 s2 e H); intros [e_in_s1 | e_in_s2].
apply union_1; generalize (s1_eq_s1' e); intuition.
apply union_2; generalize (s2_eq_s2' e); intuition.
generalize (union_12 s1' s2' e H); intros [e_in_s1' | e_in_s2'].
apply union_1; generalize (s1_eq_s1' e); intuition.
apply union_2; generalize (s2_eq_s2' e); intuition.
Qed.

Lemma  subset_subset_union :
  forall s1 s2 s, subset s1 s -> subset s2 s -> subset (union s1 s2) s.
Proof.
intros s1 s2 s H1 H2 e H.
destruct (union_12 _ _ _ H); [ apply H1 | apply H2]; trivial.
Qed.

(*** Cardinal. *)
Definition cardinal s := List.length s.(support).

Lemma cardinal_subset :
  forall s1 s2, subset s1 s2 -> cardinal s1 <= cardinal s2.
Proof.
intros [l1 wr1]; induction l1 as [ | e le];
intros s2 H; unfold cardinal; simpl.
apply Nat.le_0_l.
assert (In_e_s2 : In e s2.(support)). apply H; left; trivial.
generalize (split_list_app_cons eq_elt_dec _ _ In_e_s2).
destruct (split_list eq_elt_dec (support s2) e) as [l2' l2'']; clear In_e_s2;
destruct s2 as [ l2 wr2]; simpl; intro; subst l2.
rewrite list_app_length; rewrite Nat.add_comm; simpl; 
  rewrite Nat.add_comm;
rewrite <- list_app_length; apply le_n_S.
assert (wr1' := without_red_remove e nil le wr1); simpl in wr1'.
assert (wr2' := without_red_remove e l2' l2'' wr2).
assert (H' : subset (mk_set le wr1') (mk_set (l2' ++ l2'') wr2')).
unfold subset; simpl; intros x in_x.
assert (x_diff_e : x <> e).
intro x_eq_e; subst x;
(* Hack pour dejouer un bug de coq : destruct (In_dec eq_elt_dec e le). *)
generalize wr1; simpl; case (In_dec eq_elt_dec e le); intros; contradiction.
generalize (H x); simpl; intro H';
generalize (H' (or_intror _ in_x)); clear H'; intro H';
generalize (in_app_or _ _ _ H'); clear H'; intros [ H' | [e_eq_x | H']];
unfold mem; simpl; apply in_or_app.
left; trivial.
absurd (x = e); trivial; apply sym_eq; trivial.
right; trivial.
generalize (IHle wr1' _ H'); unfold cardinal; simpl; trivial.
Qed.

Lemma cardinal_union_1 :
  forall s1 s2, cardinal s1 <= cardinal (union s1 s2).
Proof.
intros s1 s2; apply cardinal_subset; apply subset_union_1.
Qed.

Lemma cardinal_union_2 :
  forall s1 s2, cardinal s2 <= cardinal (union s1 s2).
Proof.
intros s1 s2; apply cardinal_subset; apply subset_union_2.
Qed.


Lemma cardinal_union_inter_12 :
  forall s1 s2, cardinal (union s1 s2) + cardinal (inter s1 s2) = cardinal s1 + cardinal s2.
Proof.
assert (H : forall acc l1 l2, length (remove_not_common acc l1 l2) =
                       length acc + length (remove_not_common nil l1 l2)).
intros acc l1 l2; generalize acc l1; clear acc l1; 
induction l2 as [ | e2 l2]; intros acc l1; trivial.
simpl; destruct (In_dec eq_elt_dec e2 l1) as [ e2_in_l1 | e2_not_in_l1 ].
rewrite (IHl2 (e2 :: acc) l1); rewrite (IHl2 (e2 :: nil) l1);
simpl; apply sym_eq; rewrite Nat.add_comm; 
simpl; rewrite Nat.add_comm; trivial.
apply IHl2.

assert (H' : forall acc l1 l2 e, ~In e l1 -> ~ In e l2 ->
                       remove_not_common acc (e :: l1) l2 =
                       remove_not_common acc l1 l2).
intros acc l1 l2; generalize acc l1; clear acc l1; induction l2 as [ | e2 l2].
simpl; intros acc l1 e e_not_in_l1 _;
destruct (In_dec eq_elt_dec e l1) as [ e_in_l1 | _ ]; trivial.
intros acc l1 e e_not_in_l1 e_not_in_e2l2; simpl;
destruct (eq_elt_dec e e2) as [e_eq_e2 | e_diff_e2];
destruct (In_dec eq_elt_dec e2 l1) as [ e2_in_l1 | e2_not_in_l1 ].
apply IHl2; trivial; intro; apply e_not_in_e2l2; right; trivial.
subst e; absurd (In e2 (e2 :: l2)); trivial; left; trivial.
apply IHl2; trivial; intro; apply e_not_in_e2l2; right; trivial.
apply IHl2; trivial; intro; apply e_not_in_e2l2; right; trivial.

intros [l1 wr1] [l2 wr2]; unfold cardinal; simpl; generalize l1 wr1; clear l1 wr1; 
induction l2 as [ | e2 l2];
intros l1 wr1; trivial; 
simpl; destruct (In_dec eq_elt_dec e2 l1) as [ e2_in_l1 | e2_not_in_l1 ].
rewrite H; simpl;
rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; rewrite IHl2; trivial.
apply (without_red_remove e2 nil l2); trivial.
assert (wr1' : without_red (e2 :: l1)).
simpl; destruct (In_dec eq_elt_dec e2 l1) as [ e2_in_l1 | _ ]; trivial.
absurd (In e2 l1); trivial.
assert (wr2' := without_red_remove e2 nil l2 wr2); simpl in wr2'.
assert (H'' := IHl2 wr2' _ wr1').
rewrite H' in H''; trivial.
rewrite H''; apply sym_eq; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; trivial.
simpl in wr2; destruct (In_dec eq_elt_dec e2 l2); trivial; contradiction.
Qed.

Lemma cardinal_union:
  forall s1 s2, cardinal (union s1 s2) = cardinal s1 + cardinal s2 -cardinal (inter s1 s2).
Proof.
intros s1 s2; assert (H := cardinal_union_inter_12 s1 s2).
symmetry;apply Nat.add_sub_eq_l.
 rewrite <- H; now rewrite Nat.add_comm.
Qed.

Lemma cardinal_eq_set : forall s1 s2, eq_set s1 s2 -> cardinal s1 = cardinal s2.
Proof.
intros s1 s2 s1_eq_s2; apply Nat.le_antisymm; apply cardinal_subset;
intros e e_in_si; generalize (s1_eq_s2 e); intuition.
Qed.


Lemma subset_cardinal_not_eq_not_eq_set  :
 forall s1 s2 e, subset s1 s2 -> ~mem e s1 -> mem e s2  -> 
  cardinal s1 < cardinal s2.
Proof.
intros s1 [l2 wr2]; generalize s1; clear s1.
assert (forall l2', l2' = l2 -> length l2' = length l2).
intros; subst; trivial.
generalize (length l2) H; clear H; intros n H; generalize (H _ (refl_equal _)) wr2;
generalize l2; clear l2 wr2 H; induction n;
destruct l2 as [ | e2 l2].
contradiction.
intro; discriminate.
intro; discriminate.
intros L wr2 s1 e s1_in_e2_l2 e_not_in_s1 [e_eq_e2 | e_in_l2].

assert (wr2' := without_red_remove e2 nil l2 wr2); simpl in wr2'.
injection L; clear L; intro L; generalize (IHn _ L wr2'); clear IHn; intro IHn; subst e.
assert (subset s1 (mk_set l2 wr2')).
intros e e_in_s1; destruct (s1_in_e2_l2 e e_in_s1) as [e_eq_e2 | e_in_l2]; trivial.
absurd (mem e2 s1); subst; trivial.
apply Nat.le_lt_trans with (cardinal (mk_set l2 wr2')).
apply cardinal_subset; trivial.
unfold cardinal; simpl; apply Nat.lt_succ_diag_r.
generalize (split_list_app_cons eq_elt_dec _ _ e_in_l2).
destruct (split_list eq_elt_dec l2 e) as [l2' l2'']; clear e_in_l2.
intro; subst l2; assert (wr2' := without_red_remove e (e2 :: l2') l2'' wr2).

assert (L' : length (e2 :: l2' ++ l2'') = n).
simpl in L; injection L; clear L;
rewrite list_app_length; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm;
rewrite <- list_app_length; trivial.
generalize (IHn _ L' wr2'); clear IHn; intro IHn.
assert (subset s1 (mk_set _ wr2')).
intros e' e'_in_s1; destruct (s1_in_e2_l2 e' e'_in_s1) as [e'_eq_e2 | e'_in_l2].
subst; left; trivial.
destruct (in_app_or _ _ _ e'_in_l2) as [e'_in_l2' | e'_in_e_l2''].
simpl; right; apply in_or_app; left; trivial.
destruct e'_in_e_l2'' as [e'_eq_e | e'_in_l2''].
subst e'; absurd (mem e s1); trivial.
simpl; right; apply in_or_app; right; trivial.
apply Nat.le_lt_trans with (cardinal (mk_set _ wr2')).
apply cardinal_subset; trivial.
unfold cardinal; simpl; apply Nat.succ_lt_mono. 
do 2 rewrite list_app_length. simpl.  lia. 
Qed.

Lemma eq_set_list_permut_support :
  forall s1 s2,  eq_set s1 s2 -> 
                 LP.list_permut s1.(support) s2.(support).
Proof.
intros [l1 wr1]; induction l1 as [ | e1 l1].
intros [[ | e2 l2] wr2].
intros _; simpl; apply LP.list_permut_refl.
intro H; assert (H' := cardinal_eq_set H); discriminate.
intros [l2 wr2] H;
assert (e1_in_l2 := proj1 (H e1) (or_introl _ (refl_equal _))).
generalize (split_list_app_cons eq_elt_dec _ _ e1_in_l2).
simpl; destruct (split_list eq_elt_dec l2 e1) as [l2' l2'']; clear e1_in_l2.
intro; subst l2; assert (wr2' := without_red_remove e1 l2' l2'' wr2).
apply LP.list_permut_add_cons_inside.
assert (wr1' := without_red_remove e1 nil l1 wr1); simpl in wr1'.
apply (IHl1 wr1' (mk_set _ wr2')).
intro e; split; [intro e_in_l1 | intro e_in_l2'_l2''].
assert (e_in_l2'_e1_l2'' := (proj1 (H e)) (or_intror _ e_in_l1)).
destruct (in_app_or _ _ _ e_in_l2'_e1_l2'') as [e_in_l2' | [e_eq_e1 | e_in_l2'']].
unfold mem; simpl; apply in_or_app; left; trivial.
subst e; generalize wr1; simpl; destruct (eq_elt_dec e1 e1) as [ _ | e1_diff_e1];
[idtac | absurd (e1 = e1); trivial].
destruct (In_dec eq_elt_dec e1 l1) as [ _ | e1_not_in_l1].
contradiction.
absurd (In e1 l1); trivial.
unfold mem; simpl; apply in_or_app; right; trivial.

assert (e_in_l2'_e1_l2'' : In e (l2' ++ e1 :: l2'')).
destruct (in_app_or _ _ _ e_in_l2'_l2'') as [e_in_l2' | e_in_l2''].
apply in_or_app; left; trivial.
apply in_or_app; right; right; trivial.
generalize ((proj2 (H e)) e_in_l2'_e1_l2''); intros [e_eq_e1 | e_in_l1]; [idtac | trivial].
assert False.
subst; unfold mem in e_in_l2'_l2''; simpl in e_in_l2'_l2''.
clear e_in_l2'_e1_l2'' H wr1 wr2' wr1' IHl1 l1;
generalize l2'' wr2 e_in_l2'_l2''; clear l2'' wr2 e_in_l2'_l2'';
induction l2' as [ | e2 l2'].
simpl; intro l2'';
destruct (In_dec eq_elt_dec e l2'') as [e_in_l2'' | e_not_in_l2'']; trivial;
intros; absurd (In e l2''); subst; trivial.
intros l2'' wr2 e_in_e2_l2'_l2'';
destruct (in_app_or _ _ _ e_in_e2_l2'_l2'') as [[e_eq_e2 | e_in_l2'] | e_in_l2''].
subst; generalize wr2; simpl;
destruct (In_dec eq_elt_dec e (l2' ++ e :: l2'')) as [ _ | e_not_in_l2'_e_l2''];
trivial.
absurd (In e (l2' ++ e :: l2'')); trivial; apply in_or_app; right; left; trivial.
apply (IHl2' l2'').
apply (without_red_remove e2 nil (l2' ++ e :: l2'') wr2).
apply in_or_app; left; trivial.
apply (IHl2' l2'').
apply (without_red_remove e2 nil (l2' ++ e :: l2'') wr2).
apply in_or_app; right; trivial.
contradiction.
Qed.

Lemma without_red_permut :
 forall l1 l2, without_red l1 -> LP.list_permut l1 l2 -> without_red l2.
Proof.
intro l1; induction l1 as [ | e1 l1].
intros l2 _ P; rewrite (LP.list_permut_nil (LP.list_permut_sym P)); simpl; trivial.
intros l2 wr1 P; assert (e1_in_l2 : In e1 l2).
apply LP.in_permut_in with (e1 :: l1); trivial; left; trivial.
generalize (split_list_app_cons eq_elt_dec _ _ e1_in_l2).
simpl; destruct (split_list eq_elt_dec l2 e1) as [l2' l2'']; clear e1_in_l2.
intro; subst; apply without_red_add.
apply IHl1.
apply (without_red_remove e1 nil l1); trivial.
apply LP.list_permut_remove_hd with e1; trivial.
intro H; simpl in wr1; destruct (In_dec eq_elt_dec e1 l1) as [_ | e1_not_in_l1];
[contradiction | idtac].
apply e1_not_in_l1; apply LP.in_permut_in with (l2' ++ l2''); trivial.
apply LP.list_permut_sym;
apply LP.list_permut_remove_hd with e1; trivial.
Qed.

(*


Lemma without_red_nil : without_red nil.
Proof.
simpl; trivial.
Qed.

Lemma without_red_rec : forall e l, ~In e l -> without_red l -> without_red (e :: l).
Proof.
intros e l not_in_e_l IHl; simpl; 
destruct (In_dec eq_elt_dec e l) as [ in_e_l | _]; trivial;
absurd (In e l); trivial.
Qed.


Fixpoint make_set (l : list elt) : t :=

  match l with
  | nil => mk_set nil without_red_nil
  | e :: le =>
       match (In_dec eq_elt_dec e le) with
       | left _ => make_set le 
       | right prf => 
           let le_as_set := 
Proof.
intro l.
induction l.
*)
End Make.
