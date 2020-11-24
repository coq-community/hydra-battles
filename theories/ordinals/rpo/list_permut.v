(** by Evelyne Contejean, LRI *)

(** * Permutation over lists, and finite multisets. *)

Set Implicit Arguments. 

From Coq Require Import  List Multiset Arith Setoid.
From hydras Require Import decidable_set more_list.


Module Type Permut.

Declare Module DS : decidable_set.S.

Definition elt := DS.A.
Definition eq_elt_dec := DS.eq_A_dec.

Fixpoint list_to_multiset (l : list elt) {struct l} : multiset elt :=
  match l with
  | nil => EmptyBag elt
  | h :: tl =>
      munion (SingletonBag _ eq_elt_dec h) (list_to_multiset tl)
  end.

Definition list_permut (l1 l2:list elt) : Prop :=
  meq (list_to_multiset l1) (list_to_multiset l2).

End Permut.

(** ** Definition of permutation over lists. *)
Module Make (DS1 : decidable_set.S) <: Permut with Module DS:= DS1.

Module DS := DS1.
Import DS1.

Definition elt := DS.A.
Definition eq_elt_dec : forall t1 t2 : elt, {t1 = t2} + {t1 <> t2} := DS.eq_A_dec.

Fixpoint list_to_multiset (l : list elt) {struct l} : multiset elt :=
  match l with
  | nil => EmptyBag elt
  | h :: tl =>
      munion (SingletonBag _ eq_elt_dec h) (list_to_multiset tl)
  end.

Definition list_permut (l1 l2:list elt) : Prop :=
  meq (list_to_multiset l1) (list_to_multiset l2).

(** Properties over the multiplicity. *)
Lemma multiplicity_app :
 forall (l1 l2:list elt) (t : elt),
   multiplicity (list_to_multiset (l1 ++ l2)) t =
   multiplicity (list_to_multiset l1) t + multiplicity (list_to_multiset l2) t.
Proof.
induction l1; intros; trivial.
simpl; intros; rewrite (IHl1 l2 t); auto with arith.
Qed.

Lemma out_mult_O :
  forall (t : elt) (l:list elt), ~ In t l -> multiplicity (list_to_multiset l) t = 0.
Proof.
intro t; unfold list_to_multiset; induction l.
intros _; trivial.
intro H; simpl; elim (eq_elt_dec a t).
intro; subst t; absurd (In a (a :: l)); trivial; left; trivial.
intros _; apply IHl;
unfold not; intros; apply H;
simpl; right; assumption.
Qed.

Lemma in_mult_S :
 forall (t : elt) (l : list elt), In t l -> multiplicity (list_to_multiset l) t >= 1.
Proof.
intro t; unfold list_to_multiset; induction l.
contradiction.
simpl; intro H; elim H; clear H.
intro H; subst t; elim (eq_elt_dec a a).
intros _ ; auto with arith.
intro; absurd (a=a); trivial.
elim (eq_elt_dec a t).
intros _ _; auto with arith. 
intros; simpl; apply IHl; assumption.
Qed.


(** ** Permutation is a equivalence relation. 
Reflexivity. *)
Theorem list_permut_refl :
 forall (l : list elt), list_permut l l.
Proof.
unfold list_permut, meq; intros; trivial.
Qed.

(** Symetry. *)
Theorem list_permut_sym :
 forall l1 l2 : list elt, list_permut l1 l2 -> list_permut l2 l1.
Proof.
unfold list_permut, meq; intros; apply sym_eq; trivial.
Qed.

Hint Immediate list_permut_refl : core.
Hint Resolve list_permut_sym : core.

(** Transitivity. *)
Theorem list_permut_trans :
  forall l1 l2 l3 : list elt, list_permut l1 l2 -> list_permut l2 l3 -> list_permut l1 l3.
Proof.
unfold list_permut, meq; intros;
apply trans_eq with (multiplicity (list_to_multiset l2) a); trivial.
Qed.

Add Relation (list elt) list_permut 
reflexivity proved by list_permut_refl
symmetry proved by list_permut_sym
transitivity proved by list_permut_trans as LP.

(** Permutation of an empty list. *)
Lemma list_permut_nil :
 forall l, list_permut l nil -> l = nil.
Proof.
intro l; destruct l as [ | e l ]; trivial.
intros Abs; absurd (list_permut (e :: l) nil); trivial.
unfold not; unfold list_permut, meq; intro H; 
generalize (H e); simpl; elim (eq_elt_dec e e).
intros _; discriminate.
intro; absurd (e=e); trivial.
Qed.


(** ** Compatibility Properties. 
 Permutation is compatible with In. *)
Lemma in_permut_in :
  forall l1 l2 e, In e l1 -> list_permut l1 l2 -> In e l2.
Proof.
unfold list_permut, meq; intros l1 l2 e Inel1 Pl1l2.
elim (In_dec eq_elt_dec e l2).
intros; trivial.
intro notInel2; generalize (Pl1l2 e);
rewrite (out_mult_O e l2 notInel2);
intro M0; generalize (in_mult_S e l1 Inel1);
rewrite M0; unfold ge;
intro Abs; absurd (1<=0); trivial; inversion Abs.
Qed.
Add Morphism (In (A :=elt)) with signature (eq ==> list_permut ==> iff) as in_morph.
Proof.
 intros y x1 x2; split; intros.
 - apply in_permut_in with x1; trivial.
 - apply in_permut_in with x2; trivial; apply list_permut_sym; trivial.
Qed.

Lemma cons_permut_in :
  forall l1 l2 e, list_permut (e :: l1) l2 -> In e l2.
Proof.
intros l1 l2 e P; setoid_rewrite <- P; left; trivial.
Qed.

(** Permutation is compatible with adding an element. *)
Lemma context_list_permut_cons :
  forall e l1 l2, list_permut l1 l2 -> list_permut (e :: l1) (e :: l2).
Proof.
intros e l1 l2; unfold list_permut, meq; simpl.
intros H a; rewrite (H a); trivial.
Qed.

Add Morphism (List.cons (A:=elt)) with signature (eq ==> list_permut ==> list_permut) 
 as add_elt_morph.
Proof.
intros; apply context_list_permut_cons; trivial.
Qed.

Lemma list_permut_add_inside :
forall a l1 l2 l3 l4, 
  list_permut (l1 ++ l2) (l3 ++ l4) ->
  list_permut (l1 ++ a :: l2) (l3 ++ a :: l4).
Proof.
intros a l1 l2 l3 l4; unfold list_permut, meq; simpl;
intros H b; generalize (H b); clear H;
repeat rewrite multiplicity_app; simpl;
intro H; rewrite plus_comm; rewrite <- plus_assoc; apply sym_eq;
rewrite plus_comm; rewrite <- plus_assoc; 
apply (f_equal (fun n => match eq_elt_dec a b with 
                         | left _ => 1 
                         | right _ => 0 end + n));
rewrite plus_comm; rewrite <- H; apply plus_comm.
Qed.

Lemma list_permut_add_cons_inside :
forall a l l1 l2, 
  list_permut l (l1 ++ l2) ->
  list_permut (a :: l) (l1 ++ a :: l2).
Proof.
intros;
 replace (a :: l) with (nil ++ a :: l); trivial;
 apply list_permut_add_inside; trivial.
Qed.

(** Permutation is compatible with append. *)
Lemma context_list_permut_app1 :
  forall l l1 l2, list_permut l1 l2 -> list_permut (l ++ l1) (l ++ l2).
Proof.
intros l l1 l2; unfold list_permut, meq; simpl.
intros H a; 
rewrite (multiplicity_app l l1);
rewrite (multiplicity_app l l2);
rewrite (H a); 
trivial.
Qed.

Lemma context_list_permut_app2 :
  forall l l1 l2, list_permut l1 l2 -> list_permut (l1 ++ l) (l2 ++ l).
Proof.
intros l l1 l2; unfold list_permut, meq; simpl; intros H a; 
rewrite (multiplicity_app l1 l);
rewrite (multiplicity_app l2 l);
rewrite (H a); 
trivial.
Qed.

Add Morphism (List.app (A:=elt)) 
with signature (list_permut ==> list_permut ==> list_permut) as app_morph.
Proof.
  intros x y H1 x' y' H2;
   apply list_permut_trans with (x ++ y').
   - apply context_list_permut_app1; trivial.
   - apply context_list_permut_app2; trivial.
Qed.

Lemma list_permut_app_app :
 forall l1 l2, list_permut (l1 ++ l2) (l2 ++ l1).
Proof.
intros l1 l2;
unfold list_permut, meq; 
intro a; rewrite multiplicity_app; rewrite multiplicity_app;
apply plus_comm.
Qed.

(** Permutation is compatible with removal of common elements *)
Lemma remove_context_list_permut_cons :
  forall e l1 l2, list_permut (e :: l1) (e :: l2) -> list_permut l1 l2.
Proof.
intros e l1 l2; unfold list_permut, meq; simpl; intros H a;
generalize (H a); apply plus_reg_l.
Qed.

Lemma remove_context_list_permut_app2 :
  forall l l1 l2, list_permut (l1 ++ l) (l2 ++ l) -> list_permut l1 l2.
Proof.
intros l l1 l2; unfold list_permut, meq; simpl;
intros H a; generalize (H a);
rewrite (multiplicity_app l1 l);
rewrite (multiplicity_app l2 l); 
intros; apply plus_reg_l with (multiplicity (list_to_multiset l) a).
rewrite plus_comm; rewrite H0; rewrite plus_comm.
trivial.
Qed.

Lemma list_permut_remove_hd :
  forall l l1 l2 a,   
  list_permut (a :: l) (l1 ++ a :: l2) -> list_permut l (l1 ++ l2).
Proof.
intros l l1 l2 a; unfold list_permut, meq; simpl; intros H a0; generalize (H a0);
rewrite multiplicity_app; rewrite multiplicity_app;
simpl; intro H1; 
apply plus_reg_l with (match eq_elt_dec a a0 with left _ => 1 | right _ => 0 end);
rewrite H1; repeat rewrite plus_assoc;
apply (f_equal (fun n => n + multiplicity (list_to_multiset l2) a0));
apply plus_comm.
Qed.

(** Permutation is compatible with length. *)
Lemma list_permut_length :
 forall l1 l2, list_permut l1 l2 -> length l1 = length l2.
Proof.
induction l1; intros l2 H.
rewrite (list_permut_nil (list_permut_sym H)); auto.
elim (In_dec eq_elt_dec a l2).
intro Inal2; generalize (split_list_app_cons eq_elt_dec a l2 Inal2);
destruct (split_list eq_elt_dec l2 a); intro; subst l2.
rewrite list_app_length; simpl;
rewrite (IHl1 _ (list_permut_remove_hd l l0 H));
rewrite list_app_length; auto with arith.
intro notInal2; absurd (In a l2); trivial;
apply in_permut_in with (a :: l1); trivial;
left; trivial.
Qed.


Add Morphism (length (A:=elt)) with signature (list_permut ==> eq) as length_morph.
Proof.
apply list_permut_length.
Qed.

(** Permutation is compatible with size. *)
Lemma list_permut_size :
  forall size l1 l2, list_permut l1 l2 -> list_size size l1 = list_size size l2.
Proof.
intro size; induction l1.
intros l2 P; 
rewrite (list_permut_nil (list_permut_sym P));
trivial.
intros l2 P; 
generalize (split_list_app_cons eq_elt_dec _ _ (cons_permut_in P));
destruct (split_list eq_elt_dec l2 a); intro; subst l2;
rewrite list_size_app; simpl;
rewrite (IHl1 _ (list_permut_remove_hd _ _ P));
rewrite list_size_app;
rewrite plus_comm; rewrite <- plus_assoc;
apply (f_equal (fun n => list_size size l + n));
apply plus_comm.
Qed.

Add Parametric Morphism size : (@list_size elt size) with signature (list_permut ==> @eq nat) as list_size_morph.
Proof.
apply list_permut_size.
Qed.

(** Permutation is compatible with map. *)
Lemma list_permut_map :
  forall f l1 l2, list_permut l1 l2 -> list_permut (map f l1) (map f l2).
Proof.
intros f l1; induction l1.
intros l2 P; rewrite (list_permut_nil (list_permut_sym P)); apply list_permut_refl.
intros l2 P;
generalize (split_list_app_cons eq_elt_dec _ _ (cons_permut_in P));
destruct (split_list eq_elt_dec l2 a); intro; subst l2.
rewrite map_app; simpl;
apply list_permut_add_cons_inside; rewrite <- map_app; 
apply (IHl1 _ (list_permut_remove_hd l l0 P)).
Qed.

Add Parametric Morphism f : (map f) with signature list_permut ==> list_permut as map_morph.
Proof.
intros; apply list_permut_map; trivial.
Qed.

(** ** Permutation for short lists. *)

Lemma list_permut_length_1:
 forall a b, list_permut (a :: nil) (b :: nil)  -> a = b.
Proof.
intros a b; unfold list_permut, meq; intro P;
generalize (P a); clear P; simpl.
elim (eq_elt_dec a a).
intros _; elim (eq_elt_dec b a).
intros b_eq_a _; apply sym_eq; trivial.
intros _ Abs; simpl in Abs; absurd (1=0); trivial; discriminate.
intro; absurd (a=a); trivial.
Qed.

Lemma list_permut_length_2 :
 forall a1 b1 a2 b2, list_permut (a1 :: b1 :: nil) (a2 :: b2 :: nil) ->
 (a1=a2 /\ b1=b2) \/ (a1=b2 /\ a2=b1).
Proof.
intros a1 b1 a2 b2 P; elim (cons_permut_in P).
intro; subst a2; left; split; trivial.
apply list_permut_length_1; apply remove_context_list_permut_cons with a1; trivial.
intro H; elim H; clear H. 
intro; subst b2; right; split; trivial.
apply sym_eq; apply list_permut_length_1;
apply (list_permut_remove_hd (a2 :: nil) nil P).
intro;  contradiction.
Qed.

(** ** Link with AC syntactic decomposition.*)
Lemma ac_syntactic_aux :
 forall (l1 l2 l3 l4 : list elt),
 list_permut (l1 ++ l2) (l3 ++ l4) ->
 (exists u1, exists u2, exists u3, exists u4, 
 list_permut l1 (u1 ++ u2) /\
 list_permut l2 (u3 ++ u4) /\
 list_permut l3 (u1 ++ u3) /\
 list_permut l4 (u2 ++ u4)).
Proof.
induction l1.
intros l2 l3 l4 P;
exists (nil : list elt); exists (nil : list elt); exists l3; exists l4; 
simpl; intuition. 

intros l2 l3 l4 P; rewrite <- app_comm_cons in P;
elim (in_app_or l3 l4 a (cons_permut_in P)); intro In_a;
generalize (split_list_app_cons eq_elt_dec a _ In_a).
destruct (split_list eq_elt_dec l3 a); intro; subst l3;
rewrite app_ass in P; rewrite <- app_comm_cons in P;
generalize (list_permut_remove_hd _ _ P); clear P; 
intro P; rewrite <- app_ass in P; 
elim (IHl1 l2 (l ++ l0) l4 P); clear IHl1 P;
intros u1 H; elim H; clear H; 
intros u2 H; elim H; clear H;
intros u3 H; elim H; clear H;
intros u4 P; elim P; clear P;
intros P1 P; elim P; clear P;
intros P2 P; elim P; clear P;
intros P3 P4;
exists (a :: u1); exists u2; exists u3; exists u4; intuition; simpl; trivial.
(* setoid_rewrite <- P1. *)
apply context_list_permut_cons; trivial.
apply list_permut_sym; apply list_permut_add_cons_inside;
apply list_permut_sym; trivial.

destruct (split_list eq_elt_dec l4 a); intro; subst l4;
rewrite <- app_ass in P; 
generalize (list_permut_remove_hd _ _ P); clear P;
intro P; rewrite app_ass in P; 
elim (IHl1 l2 l3 (l ++ l0) P); clear IHl1 P;
intros u1 H; elim H; clear H; 
intros u2 H; elim H; clear H;
intros u3 H; elim H; clear H;
intros u4 P; elim P; clear P;
intros P1 P; elim P; clear P;
intros P2 P; elim P; clear P;
intros P3 P4;
exists u1; exists (a :: u2); exists u3; exists u4; intuition; simpl; trivial.
apply list_permut_add_cons_inside; trivial.
apply list_permut_sym; apply list_permut_add_cons_inside; 
apply list_permut_sym; trivial.
Qed.

Lemma ac_syntactic :
 forall (l1 l2 l3 l4 : list elt),
 list_permut (l2 ++ l1) (l4 ++ l3) ->
 (exists u1, exists u2, exists u3, exists u4, 
 list_permut l1 (u1 ++ u2) /\
 list_permut l2 (u3 ++ u4) /\
 list_permut l3 (u1 ++ u3) /\
 list_permut l4 (u2 ++ u4)).
Proof.
intros l1 l2 l3 l4 P; apply ac_syntactic_aux.
apply list_permut_trans with (l2 ++ l1).
apply list_permut_app_app.
apply list_permut_trans with (l4 ++ l3); trivial.
apply list_permut_app_app.
Qed.

Lemma list_permut_dec : forall l1 l2, {list_permut l1 l2}+{~list_permut l1 l2}.
Proof.
intro l1; induction l1 as [ | e1 l1].
destruct l2 as [ | e2 l2].
left; apply list_permut_refl.
right; intro P; assert (H := list_permut_length P); discriminate.
intro l2; destruct (In_dec eq_elt_dec e1 l2) as [e1_in_l2 | e1_not_in_l2].
generalize (split_list_app_cons eq_elt_dec _ _ e1_in_l2); clear e1_in_l2;
destruct (split_list eq_elt_dec l2 e1) as [l2' l2'']; intro; subst.
destruct (IHl1 (l2' ++ l2'')) as [P | nP].
left; apply list_permut_add_cons_inside; trivial.
right; intro P; apply nP; apply list_permut_remove_hd with e1; trivial.
right; intro P; apply e1_not_in_l2; apply in_permut_in with (e1 :: l1); trivial;
left; trivial.
Qed.

End Make.

(* With section instead of module, and then polymorph use 
Section LP.
Variable elt : Set.
Parameter eq_elt_dec : forall t1 t2 : elt, {t1 = t2} + {t1 <> t2}.
...
End LP.

Add Relation list list_permut 
reflexivity proved by list_permut_refl
symmetry proved by list_permut_sym
transitivity proved by list_permut_trans as LP_poly.

Add Morphism In with signature  eq ==> list_permut ==> iff as in_morph_poly.
Proof.
intros; split; intros.
apply in_permut_in with x1; trivial.
apply in_permut_in with x2; trivial; apply list_permut_sym; trivial.
Qed.

Goal forall (a b:nat), list_permut (a::b::nil) (b::a::nil) -> 
In a (b :: a :: nil).
intros a b P.
setoid_rewrite <- P.
left; trivial.
Qed.
*)

(*
Extract Constant eq_element_dec => eq.
Extract Constant o_element_dec => le.
Extract Constant element => int.
Extraction split_list.
Extraction partition.
Extraction NoInline partition.
Extraction quicksort.
*)

