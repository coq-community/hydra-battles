(**  by Evelyne Contejean *)

(**  * Dickson Lemma: the multiset extension of a well-founded ordering is well-founded.
 *)

Set Implicit Arguments. 

From Coq Require Import Relations List Setoid Multiset.
From hydras Require Import closure more_list list_permut.


Module Make (DS1 : decidable_set.S).

Module DS := DS1.
Module LP := list_permut.Make (DS1).
Import LP.

(** ** Definition of the multiset extension of a relation. *)
Inductive multiset_extension_step (R : relation elt) : list elt -> list elt -> Prop :=
  | rmv_case : 
     forall l1 l2 l la a, (forall b, In b la -> R b a) -> 
      list_permut l1 (la ++ l) -> list_permut l2 (a :: l) ->
      multiset_extension_step R l1 l2.

(** If [n << {a} U m] , then 
      either, there exists n' such that n = {a} U n' and [n' << m],
      or, there exists k, such that n = k U m, and [k << {a}]. *)

Lemma two_cases :
 forall R a m n, 
 multiset_extension_step R n (a :: m) ->
 (exists n', list_permut n (a :: n') /\ 
             multiset_extension_step R n' m) \/
 (exists k, (forall b, In b k -> R b a) /\ 
            list_permut n (k ++ m)).
Proof.
intros R a m n M; inversion_clear M as [x1 x2 l la a0 H H0 H1];
elim (eq_elt_dec a a0); intro a_eq_a0; subst.

assert (H2 : list_permut m l).
apply remove_context_list_permut_cons with a0; trivial.
right; exists la; split; trivial; setoid_rewrite H0; setoid_rewrite H2; auto.

left; elim (In_dec eq_elt_dec a0 m); intro In_a0.
generalize (split_list_app_cons eq_elt_dec _ _ In_a0); clear In_a0;
destruct (split_list eq_elt_dec m a0); intro; subst.
assert (H2 : list_permut (a :: l0 ++ l1) l).
apply remove_context_list_permut_cons with a0;
setoid_rewrite <- H1; pattern a at 1; do 2 rewrite app_comm_cons;
apply list_permut_add_cons_inside; auto.
exists (la ++ l0 ++ l1); split.
setoid_rewrite H0; setoid_rewrite <- H2; apply list_permut_sym;
apply list_permut_add_cons_inside; auto.
apply (rmv_case (l1:=la ++ l0 ++ l1) (l2:= l0 ++ a0 :: l1) (l:= l0 ++ l1) R la H); auto; 
apply list_permut_sym; apply list_permut_add_cons_inside; auto.

absurd (In a0 (a :: m)).
intro H2; elim H2; clear H2; intro H2; subst;
[ absurd (a0 = a0) | absurd (In a0 m) ]; trivial.
setoid_rewrite H1; left; trivial.
Qed.

(** [multiset_extension_step] is compatible with permutation. *)
Lemma list_permut_multiset_extension_step_1 :
  forall R l1 l2 l, list_permut l1 l2 -> 
  multiset_extension_step R l1 l -> multiset_extension_step R l2 l.
Proof.
intros R l1 l2 l P M1; inversion M1; subst.
apply (rmv_case (l1:=l2) (l2:=l) (l:=l4) R la H); trivial;
setoid_rewrite <- P; trivial.
Qed.

Lemma list_permut_multiset_extension_step_2 :
  forall R l1 l2 l, list_permut l1 l2 -> 
  multiset_extension_step R l l1 -> multiset_extension_step R l l2.
Proof.
intros R l1 l2 l P M1; inversion M1; subst.
apply (rmv_case (l1:=l) (l2:=l2) (l:=l4) R la H); trivial;
setoid_rewrite <- P; trivial.
Qed.

Lemma context_multiset_extension_step_app1 :
  forall R l1 l2 l, multiset_extension_step R l1 l2 ->
                         multiset_extension_step R (l ++ l1) (l ++ l2).
Proof.
intros R l1 l2 l H; destruct H as [l1 l2 l12 la a H P1 P2].
apply (@rmv_case R (l++l1) (l++l2) (l++l12) la a); trivial.
apply list_permut_trans with (l ++ la ++ l12).
apply context_list_permut_app1; trivial.
do 2 rewrite <- app_ass; apply context_list_permut_app2; trivial.
apply list_permut_app_app.
apply list_permut_trans with (l ++ a :: l12).
apply context_list_permut_app1; trivial.
apply list_permut_sym; apply list_permut_add_cons_inside; 
apply list_permut_refl.
Qed.

Lemma context_trans_clos_multiset_extension_step_app1 :
  forall R l1 l2 l, trans_clos (multiset_extension_step R) l1 l2 ->
                         trans_clos (multiset_extension_step R) (l ++ l1) (l ++ l2).
Proof.
intros R l1 l2 l H; induction H.
apply t_step; apply context_multiset_extension_step_app1; trivial.
apply t_trans with (l ++ y); trivial.
apply context_multiset_extension_step_app1; trivial.
Qed.

Lemma context_multiset_extension_step_app2 :
  forall R l1 l2 l, multiset_extension_step R l1 l2 ->
                         multiset_extension_step R (l1 ++ l) (l2 ++ l).
Proof.
intros R l1 l2 l H; destruct H as [l1 l2 l12 la a H P1 P2].
apply (@rmv_case R (l1++l) (l2++l) (l12++l) la a); trivial.
rewrite <- app_ass; apply context_list_permut_app2; trivial.
rewrite app_comm_cons; apply context_list_permut_app2; trivial.
Qed.

Add Parametric Morphism R : (@multiset_extension_step R) with signature (list_permut ==> list_permut ==> iff) as mult_morph.
Proof.
intros l1 l2 P12 l3 l4 P34; split; [intro R13 | intro R24].
apply list_permut_multiset_extension_step_2 with l3; trivial.
apply list_permut_multiset_extension_step_1 with l1; trivial.
apply list_permut_multiset_extension_step_2 with l4; auto;
apply list_permut_multiset_extension_step_1 with l2; auto.
Qed.

(** *** Accessibility lemmata. *)
Lemma list_permut_acc :
  forall R l1 l2, list_permut l2 l1 -> 
  Acc (multiset_extension_step R) l1 -> Acc (multiset_extension_step R) l2.
Proof.
intros R l1 l2 Meq A1; apply Acc_intro; intros l M2;
inversion A1; apply H; subst;
setoid_rewrite <- Meq; trivial.
Qed.

Add Parametric Morphism R : (Acc (multiset_extension_step R)) with signature (list_permut ==> iff) as acc_morph.
Proof.
intros l1 l2 P; split; [intro A1 | intro A2].
apply list_permut_acc with l1; trivial; setoid_rewrite <- P; auto.
apply list_permut_acc with l2; trivial.
Qed.

Lemma dickson_aux1 :
forall (R : relation elt) a,
 (forall b, R b a -> 
  forall m, Acc (multiset_extension_step R) m -> 
            Acc (multiset_extension_step R) (b :: m)) ->
 forall m, Acc (multiset_extension_step R) m -> 
 (forall m', (multiset_extension_step R) m' m -> 
             Acc (multiset_extension_step R) (a :: m')) ->
 Acc (multiset_extension_step R) (a :: m).
Proof. 
intros R a IH2_a m Acc_m IHa_M; apply Acc_intro;
intros n H; elim (two_cases H); clear H.
intros [n' [P M]]; refine (list_permut_acc P _); apply IHa_M; trivial.
intros [k [M P]]; refine (list_permut_acc P _); clear P; induction k; trivial; simpl;
apply IH2_a.
apply M; left; trivial.
apply IHk; intros; apply M; right; trivial.
Qed.

Lemma dickson_aux2 :
forall R m,
  Acc (multiset_extension_step R) m ->
  forall a, (forall b, R b a -> 
             forall m, Acc (multiset_extension_step R) m -> 
                       Acc (multiset_extension_step R) (b :: m)) ->
   Acc (multiset_extension_step R) (a :: m). 
Proof.
intros R m Acc_m a IH2_a;
apply (Acc_iter  (R:= multiset_extension_step R)
(fun m => Acc (multiset_extension_step R) m -> 
Acc (multiset_extension_step R) (a :: m))); trivial;
clear m Acc_m;
intros m H Acc_m; apply dickson_aux1; trivial;
intros; apply H; trivial;
apply Acc_inv with m; trivial.
Qed.

Lemma dickson_aux3 :
forall R a, Acc R a -> forall m, Acc (multiset_extension_step R) m ->
Acc (multiset_extension_step R) (a :: m).
Proof.
intros R a Acc_a;
apply (Acc_iter  (R:= R)
(fun a => Acc R a -> forall m, Acc (multiset_extension_step R) m -> 
Acc (multiset_extension_step R) (a :: m))); trivial;
clear a Acc_a;
intros a H Acc_a m Acc_m; apply dickson_aux2; trivial;
intros; apply H; trivial;
apply Acc_inv with a; trivial.
Qed.

(** Main lemma. *)
Lemma dickson : 
  forall R, well_founded R -> well_founded (multiset_extension_step R).
Proof.
intros R Wf_R; unfold well_founded in *;
intros m; induction m as [ | a m].
apply Acc_intro; intros m H; inversion_clear H;
absurd (a :: l = nil);
[ discriminate | apply list_permut_nil; setoid_rewrite H2; auto].
apply dickson_aux3; trivial.
Qed.

Lemma multiset_closure :
  forall R p q, transitive _ R ->
  closure.trans_clos (multiset_extension_step R) p q -> 
	exists p', exists q', exists pq,
   	list_permut p (p' ++ pq) /\
   	list_permut q (q' ++ pq) /\
   	q' <> nil /\
   	(forall a, In a p' -> exists b, In b q' /\ R a b).
Proof.
intros R p q trans_R p_lt_q; induction p_lt_q as [p q p_lt_q | p q r p_lt_q q_lt_r].
destruct p_lt_q as [p q pq la a H Pp Pq].
exists la; exists (a :: nil); exists pq; simpl; split; trivial.
split; trivial.
split; trivial.
discriminate.
intros b b_in_la; exists a; split; [left; trivial | apply H; trivial].
destruct p_lt_q as [p q pq la a la_lt_a Pp Pq].
generalize IHq_lt_r; clear IHq_lt_r.
intros [q' [r' [qr [Pq' [Pr [r'_diff_nil q'_lt_r']]]]]].
assert (a_in_q'_qr : In a (q' ++ qr)).
apply in_permut_in with q; trivial.
apply in_permut_in with (a :: pq); [left | apply list_permut_sym]; trivial.
destruct (in_app_or _ _ _ a_in_q'_qr) as [a_in_q' | a_in_qr]; clear a_in_q'_qr.
generalize (split_list_app_cons eq_elt_dec _ _ a_in_q'); 
destruct (split_list eq_elt_dec q' a) as [q1' q2']; intro; subst.
exists (la ++ q1' ++ q2'); exists r'; exists qr; split.
refine (list_permut_trans Pp _).
do 2 rewrite app_ass; apply context_list_permut_app1.
apply list_permut_remove_hd with a.
refine (list_permut_trans (list_permut_sym Pq) _).
rewrite app_comm_cons; rewrite <- app_ass; trivial.
split; trivial.
split; trivial.
intros b b_in_la_q1'_q2'; 
destruct (in_app_or _ _ _ b_in_la_q1'_q2') as [b_in_la | b_in_q1'_q2']; 
clear b_in_la_q1'_q2'; [idtac | 
destruct (in_app_or _ _ _ b_in_q1'_q2') as [b_in_q1' | b_in_q2']; clear b_in_q1'_q2'].
destruct (q'_lt_r' a a_in_q') as [c [c_in_r' a_lt_c]]; exists c; split; trivial.
apply trans_R with a; trivial; apply la_lt_a; trivial.
apply q'_lt_r'; apply in_or_app; left; trivial.
apply q'_lt_r'; apply in_or_app; right; right; trivial.

generalize (split_list_app_cons eq_elt_dec _ _ a_in_qr); 
destruct (split_list eq_elt_dec qr a) as [qr1 qr2]; intro; subst.
exists (la ++ q'); exists (a :: r'); exists (qr1 ++ qr2); split.
refine (list_permut_trans Pp _).
rewrite app_ass; apply context_list_permut_app1.
rewrite <- app_ass; apply list_permut_remove_hd with a.
refine (list_permut_trans (list_permut_sym Pq) _).
rewrite app_ass; trivial.
split.
refine (list_permut_trans Pr _); rewrite <- app_ass;
apply list_permut_sym; simpl; apply list_permut_add_cons_inside;
rewrite ass_app; apply list_permut_refl.
split.
discriminate.
intros b b_in_la_q'; 
destruct (in_app_or _ _ _ b_in_la_q') as [b_in_la | b_in_q']; clear b_in_la_q'.
exists a; split; [left | apply la_lt_a]; trivial.
destruct (q'_lt_r' _ b_in_q') as [c [c_in_r' b_lt_c]].
exists c; split; trivial; right; trivial.
Qed.


End Make.

