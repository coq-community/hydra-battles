(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* by Evelyne Contejean *)


Require Import List.
Require Import more_list.
Require Import list_permut.
Require Import dickson.
Require Import Relations.
Require Import Wellfounded.
Require Import Arith.
Require Import Wf_nat.
Require Import term.

(** A non-dependant version of lexicographic extension. *)
Definition lex (A B : Set) (eq_A_dec : forall a1 a2, {a1=a2}+{a1<>a2}) 
(o1 : relation A) (o2 : relation B) (s t : _ * _) :=
  match s with
  | (s1,s2) =>
    match t with
    | (t1,t2) => 
       if eq_A_dec s1 t1
       then o2 s2 t2
       else o1 s1 t1
     end
   end.

(** Transitivity of  lexicographic extension. *)
Lemma lex_trans :
 forall (A B : Set) eq_A_dec o1 o2, 
 antisymmetric A o1 -> transitive A o1 -> transitive B o2 ->
 transitive _ (lex _ _ eq_A_dec o1 o2).
Proof.
unfold transitive, lex; 
intros A B eq_A_dec o1 o2 A1 T1 T2 p1 p2 p3; 
destruct p1 as [a1 b1]; destruct p2 as [a2 b2]; destruct p3 as [a3 b3];
elim (eq_A_dec a1 a2); intro eq1.
subst a2; elim (eq_A_dec a1 a3); intro eq2; trivial; apply T2.
intro lt1; elim (eq_A_dec a1 a3); intro eq3.
subst a3; elim (eq_A_dec a2 a1); intro eq2.
subst a2; absurd (a1=a1); trivial.
intro lt2; generalize (A1 _ _ lt1 lt2); contradiction.
elim (eq_A_dec a2 a3); intro eq4.
subst a3; trivial.
intro lt2; apply T1 with a2; trivial.
Qed.

(** Well-foundedness of  lexicographic extension. *)
Lemma wf_lex :
  forall A B eq_A_dec o1 o2, well_founded o1 -> well_founded o2 ->
  well_founded (lex A B eq_A_dec o1 o2).
Proof.
intros A B eq_A_dec o1 o2 W1 W2; unfold well_founded in *; destruct a.
generalize b; clear b; pattern a; refine (well_founded_ind W1 _ _ a);
clear a; intros a IH1 b; pattern b; refine (well_founded_ind W2 _ _ b).
clear b; intros b IH2; apply Acc_intro.
destruct y; simpl; elim (eq_A_dec a0 a); intro a0_eq_a.
subst a0; apply IH2.
intro; apply IH1; trivial.
Qed.

(** ** Module Type Precedence, 
** Definition of a precedence. *)
Module Type Precedence.
Parameter A : Set.
Parameter prec : relation A.

Inductive status_type : Set :=
  | Lex : status_type
  | Mul : status_type.

Parameter status : A -> status_type.

Axiom prec_dec : forall a1 a2 : A, {prec a1 a2} + {~ prec a1 a2}.
Axiom prec_antisym : forall s, prec s s -> False.
Axiom prec_transitive : transitive A prec.

End Precedence.

(** ** Module Type RPO, 
** Definition of RPO from a precedence on symbols. *)

Module Type RPO.

Declare Module T : term.Term.
Declare Module P : Precedence with Definition A:= T.symbol.

Import T.
Import P.
Declare Module LP : list_permut.Permut with Definition DS.A:=term.
Import LP.

(** ** Definition of rpo.*)
Inductive rpo : term -> term -> Prop :=
  | Subterm : forall f l t s, In s l -> rpo_eq t s -> rpo t (Term f l)
  | Top_gt : 
       forall f g l l', prec g f -> 
       (forall s', In s' l' -> rpo s' (Term f l)) -> 
       rpo (Term g l') (Term f l)
  | Top_eq_lex : 
        forall f l l', status f = Lex -> rpo_lex l' l -> 
        (forall s', In s' l' -> rpo s' (Term f l)) ->
        rpo (Term f l') (Term f l)

  | Top_eq_mul : 
        forall f l l', status f = Mul -> rpo_mul l' l -> 
        rpo (Term f l') (Term f l)

with rpo_eq : term -> term -> Prop :=
  | Eq : forall t, rpo_eq t t
  | Lt : forall s t, rpo s t -> rpo_eq s t

with rpo_lex : list term -> list term -> Prop :=
  | List_gt : 
      forall s t l l', rpo s t -> length l = length l' -> 
      rpo_lex (s :: l) (t :: l')
  | List_eq : forall s l l', rpo_lex l l' -> rpo_lex (s :: l) (s :: l')

with rpo_mul : list term -> list term -> Prop :=
  | List_mul : 
       forall a lg ls lc l l', 
       list_permut l' (ls ++ lc) ->
       list_permut l (a :: lg ++ lc) ->
       (forall b, In b ls -> exists a', In a' (a :: lg) /\ rpo b a') ->
       rpo_mul l' l.

(** ** rpo is a preorder, and its reflexive closure is an ordering. *)
Axiom rpo_closure :
  forall s t u, 
  (rpo t s -> rpo u t -> rpo u s) /\
  (rpo s t -> rpo t s -> False) /\
  (rpo s s -> False) /\
  (rpo_eq s t -> rpo_eq t s -> s = t).

Axiom rpo_trans : forall s t u, rpo t s -> rpo u t -> rpo u s.

(** ** Main theorem: when the precedence is well-founded, so is the rpo. *)
Axiom wf_rpo : well_founded prec -> well_founded rpo.

(** ** RPO is compatible with the instanciation by a substitution. *)
Axiom rpo_subst :
  forall t s, rpo s t -> 
  forall sigma, rpo (apply_subst sigma s) (apply_subst sigma t).

(** ** RPO is compatible with adding context. *)
Axiom rpo_add_context :
 forall p ctx s t, rpo s t -> is_a_pos ctx p = true -> 
  rpo (replace_at_pos ctx s p) (replace_at_pos ctx t p).

End RPO.

Module Make (T1: term.Term) 
                    (P1 : Precedence with Definition A := T1.symbol)
<: RPO. (* with Module T := T1 with Module P:=P1. *)

Module T := T1.
Module P := P1.

Import T.
Import P.

Module LP := list_permut.Make (Term_eq_dec).
Import LP.

(** ** Definition of size-based well-founded orderings for induction.*)
Definition o_size s t := size s < size t.

Lemma wf_size :  well_founded o_size.
Proof.
generalize (well_founded_ltof _ size); unfold ltof; trivial.
Qed.

Definition size2 s := match s with (s1,s2) => (size s1, size s2) end.
Definition o_size2 s t := lex _ _ eq_nat_dec lt lt (size2 s) (size2 t).
Lemma wf_size2 : well_founded o_size2.
Proof.
refine (wf_inverse_image _ _ (lex _ _ eq_nat_dec lt lt) size2 _);
apply wf_lex; apply lt_wf.
Qed.

Definition size3 s := match s with (s1,s2) => (size s1, size2 s2) end.
Definition o_size3 s t := 
  lex _ _ eq_nat_dec lt (lex _ _ eq_nat_dec lt lt) (size3 s) (size3 t).
Lemma wf_size3 : well_founded o_size3.
Proof.
refine (wf_inverse_image _ _ 
  (lex _ _ eq_nat_dec lt (lex _ _ eq_nat_dec lt lt)) size3 _);
apply wf_lex; [ idtac | apply wf_lex ]; apply lt_wf.
Qed.

Lemma lex1 : 
 forall s f l t1 u1 t2 u2, In s l -> o_size3 (s,(t1,u1)) (Term f l,(t2,u2)).
Proof.
intros s f l t1 u1 t2 u2 In_s; unfold o_size3, size3, size2, lex;
elim (eq_nat_dec (size s) (size (Term f l))).
intro eq1; absurd (size (Term f l) < size (Term f l)); auto with arith;
generalize (size_direct_subterm s (Term f l) In_s); rewrite eq1; trivial.
intros; apply (size_direct_subterm s (Term f l) In_s).
Qed.

Lemma lex1_bis : 
 forall a f l t1 u1 t2 u2, o_size3 (Term f l,(t1,u1)) (Term f (a::l),(t2,u2)).
Proof.
intros a f l t1 u1 t2 u2; unfold o_size3, size3, size2, lex;
elim (eq_nat_dec (size (Term f l)) (size (Term f (a :: l)))); intro eq1.
do 2 rewrite size_unfold in eq1; injection eq1; clear eq1; intro eq1;
absurd (list_size size l < list_size size l); auto with arith;
generalize (plus_le_compat_r _ _ (list_size size l) (size_ge_one a));
rewrite <- eq1; trivial.
do 2 rewrite size_unfold;
simpl; apply lt_n_S; apply lt_le_trans with (1 + list_size size l);
auto with arith; 
apply plus_le_compat_r; apply size_ge_one.
Qed.

Lemma lex2 :
  forall t f l s u1 u2, In t l -> o_size3 (s,(t,u1)) (s,(Term f l, u2)).
Proof.
intros t f l s u1 u2 In_t;
unfold o_size3, size3, size2, lex;
elim (eq_nat_dec (size s) (size s)); intro eq1.
elim (eq_nat_dec (size t) (size (Term f l))); intro eq2.
absurd (size (Term f l) < size (Term f l)); auto with arith;
generalize (size_direct_subterm t (Term f l) In_t); rewrite eq2; trivial.
apply (size_direct_subterm t (Term f l) In_t).
absurd (size s = size s); trivial.
Qed.

Lemma lex3 :
  forall u f l s t, In u l -> o_size3 (s,(t,u)) (s,(t,Term f l)).
Proof.
intros u f l s t In_u;
unfold o_size3, size3, size2, lex;
elim (eq_nat_dec (size s) (size s)); intro eq1.
elim (eq_nat_dec (size t) (size t)); intro eq2.
apply (size_direct_subterm u (Term f l) In_u).
absurd (size t = size t); trivial.
absurd (size s = size s); trivial.
Qed.

Lemma o_size3_trans : transitive _ o_size3.
Proof.
generalize (lex_trans _ _ eq_nat_dec lt (lex _ _ eq_nat_dec lt lt));
unfold transitive, o_size3, size3, o_size2; intros H x y z lt1 lt2;
destruct x; destruct p; rename t into x1; rename t0 into x2; rename t1 into x3;
destruct y; destruct p; rename t into y1; rename t0 into y2; rename t1 into y3;
destruct z; destruct p; rename t into z1; rename t0 into z2; rename z1 into z3.
apply H with (size y1, size2 (y2,y3)); trivial.
unfold antisymmetric; 
intros n m lt' lt''; generalize (lt_asym n m lt' lt''); contradiction.
apply lt_trans.
fold transitive; apply lex_trans.
unfold antisymmetric; 
intros n m lt' lt''; generalize (lt_asym n m lt' lt''); contradiction.
unfold transitive; apply lt_trans.
unfold transitive; apply lt_trans.
Qed.

(** ** Definition of rpo.*)

Inductive rpo : term -> term -> Prop :=
  | Subterm : forall f l t s, In s l -> rpo_eq t s -> rpo t (Term f l)
  | Top_gt : 
       forall f g l l', prec g f -> 
       (forall s', In s' l' -> rpo s' (Term f l)) -> 
       rpo (Term g l') (Term f l)
  | Top_eq_lex : 
        forall f l l', status f = Lex -> rpo_lex l' l -> 
        (forall s', In s' l' -> rpo s' (Term f l)) ->
        rpo (Term f l') (Term f l)

  | Top_eq_mul : 
        forall f l l', status f = Mul -> rpo_mul l' l -> 
        rpo (Term f l') (Term f l)

with rpo_eq : term -> term -> Prop :=
  | Eq : forall t, rpo_eq t t
  | Lt : forall s t, rpo s t -> rpo_eq s t

with rpo_lex : list term -> list term -> Prop :=
  | List_gt : 
      forall s t l l', rpo s t -> length l = length l' -> 
      rpo_lex (s :: l) (t :: l')
  | List_eq : forall s l l', rpo_lex l l' -> rpo_lex (s :: l) (s :: l')

with rpo_mul : list term -> list term -> Prop :=
  | List_mul : 
       forall a lg ls lc l l', 
       list_permut l' (ls ++ lc) ->
       list_permut l (a :: lg ++ lc) ->
       (forall b, In b ls -> exists a', In a' (a :: lg) /\ rpo b a') ->
       rpo_mul l' l.

Lemma rpo_lex_same_length :
  forall l l', rpo_lex l l' -> length l = length l'.
Proof.
induction l; intros l' rpo_lex_l; inversion rpo_lex_l.
simpl; rewrite H3; trivial.
simpl; rewrite (IHl l'0); trivial.
Qed.

Lemma rpo_subterm :
 forall s t, rpo t s -> forall tj, direct_subterm tj t -> rpo tj s.
Proof.
intros s t;
cut (forall p : term * term,
       match p with
       | (s,t) => rpo t s -> forall tj, direct_subterm tj t -> rpo tj s
       end).
intros H; apply (H (s,t)).
clear s t; intro p; pattern p; refine (well_founded_ind wf_size2 _ _ _); 
clear p; intro p; destruct p; rename t into s; rename t0 into t;
intros IH H tj In_tj; inversion H; clear H.
subst s t0; inversion H1; clear H1.
subst s0 t0; apply (Subterm f l tj t); trivial;
apply Lt; destruct t; try contradiction;
apply (Subterm s l0 tj tj); trivial; apply Eq; trivial.
subst t t0; apply (Subterm f l tj s0); trivial;
apply Lt; refine (IH (s0, s) _ _ tj _); trivial.
unfold o_size2, size2, lex; 
elim (eq_nat_dec (size s0) (size (Term f l))); intro eq1.
absurd (size (Term f l) < size (Term f l)); auto with arith;
generalize (size_direct_subterm s0 (Term f l) H0); rewrite eq1; trivial.
apply size_direct_subterm; trivial.

subst t s; apply H1; trivial.

subst t s; apply H2; trivial.

subst t s; inversion H1; clear H1.
subst l'0 l0; simpl in In_tj;
elim (in_app_or _ _ _ (in_permut_in tj In_tj H)); clear In_tj; intro In_tj.
elim (H3 tj In_tj); intros a' H4; elim H4; clear H4; intros H4 H5.
apply (Subterm f l tj a');
[ refine (in_permut_in a' _ (list_permut_sym H2));
rewrite app_comm_cons; apply in_or_app;  left
| apply Lt; apply H5 ]; trivial.
apply (Subterm f l tj tj);
[ refine (in_permut_in tj _ (list_permut_sym H2)); right; 
apply in_or_app; right
| apply Eq ]; trivial.
Qed.

(** ** rpo is a preorder, and its reflexive closure is an ordering. *)
Lemma rpo_closure :
  forall s t u, 
  (rpo t s -> rpo u t -> rpo u s) /\
  (rpo s t -> rpo t s -> False) /\
  (rpo s s -> False) /\
  (rpo_eq s t -> rpo_eq t s -> s = t).
Proof.
intros s t u;
cut (forall triple : term * (term * term),
       match triple with
       | (s,(t,u)) =>
         (rpo t s -> rpo u t -> rpo u s) /\
         (rpo s t -> rpo t s -> False) /\
         (rpo s s -> False) /\
         (rpo_eq s t -> rpo_eq t s -> s = t)
       end).
intros H; apply (H (s,(t,u))).
clear s t u; intro triple; pattern triple; 
refine (well_founded_ind wf_size3 _ _ triple); clear triple.
intros x IH; destruct x; rename t into s; destruct p; rename t0 into u;
destruct s.
intuition.
inversion H.
inversion H0.
inversion H.
inversion_clear H0; trivial; inversion H1.

rename s into f; cut (rpo (Term f l)  (Term f l) -> False).
intro Anti0; cut (rpo (Term f l) t -> rpo t (Term f l) -> False).
intro Anti; intuition.

inversion H.
subst t0 f0 l0; inversion H5; clear H5.
subst t t0; apply (Subterm f l u s); trivial; apply Lt; trivial.
subst s0 t0; apply (Subterm f l u s); trivial; elim (IH (s,(t,u))); intuition.
apply Lt; trivial.
apply lex1; trivial.

subst t f0 l0; inversion H0.
subst u f0 l0; inversion H7; clear H7.
subst t t0; apply (rpo_subterm _ _ H); trivial.
subst s0 t0; elim (IH (Term f l,(s,t))); intuition; apply lex2; trivial.

subst u f0 l0; rename g0 into h; rename l'0 into l''; apply Top_gt.
apply prec_transitive with g; trivial.
intros; elim (IH (Term f l,(Term g l',s'))); intuition;  apply lex3; trivial.

subst f0 l0 u; rename l'0 into l''; apply Top_gt; trivial.
intros; elim (IH (Term f l, (Term g l',s'))); intuition; apply lex3; trivial.
subst u f0 l0; rename l'0 into l''; apply Top_gt; trivial.
inversion H7; subst l0 l'0.
intros s' In_s'; generalize (in_permut_in s' In_s' H1); clear In_s'; 
intro In_s'; elim (in_app_or _ _ _ In_s'); clear In_s'; 
intro In_s'.
elim (IH (Term f l, (Term g l', s'))); intuition.
apply H11; elim (H3 s' In_s'); intros tj H'; elim H'; clear H'; 
intros In_tj H'; apply (Subterm g l' s' tj);
[ refine (in_permut_in tj _ (list_permut_sym H2));
  rewrite app_comm_cons; apply in_or_app; left
| apply Lt ]; trivial.
apply lex3; refine (in_permut_in s' _ (list_permut_sym H1)); 
apply in_or_app; left; trivial.
apply (rpo_subterm _ _ H); 
refine (in_permut_in s' _ (list_permut_sym H2)); 
rewrite app_comm_cons; apply in_or_app; right; trivial.

subst f0 l0 t; inversion H0.
subst t f0 l0; inversion H8; clear H8.
subst s t; apply H6; trivial.
subst s s0; elim (IH (Term f l, (t,u))); intuition; apply lex2; trivial.
subst u f0 l0; rename l'0 into l''; apply Top_gt; trivial;
intros; elim (IH (Term f l, (Term f l', s'))); intuition; apply lex3; trivial.
subst f0 l0 u; rename l'0 into l''; apply Top_eq_lex; trivial.
generalize l' l'' H5 H8 IH; clear l' l'' H3 H5 H6 Anti Anti0 H H4 H8 H9 IH H0; 
induction l; intros l' l'' H4 H6 IH; inversion H4.
subst l' t l'0; inversion H6.
subst l'' t l0; apply List_gt; elim (IH (a,(s,s0))); intuition.
apply lex1; trivial; left; trivial.
rewrite H7; trivial.
apply lex1; trivial; left; trivial.
apply List_gt; trivial.
subst l'' s0 l'; rewrite (rpo_lex_same_length _ _ H1); trivial.
subst l' l'0 s; inversion H6.
apply List_gt; trivial; rewrite H5; apply rpo_lex_same_length; trivial.
subst l'' s l'; apply List_eq; apply IHl with l0; trivial;
intros; apply IH; 
apply o_size3_trans with (Term f l, (Term f l0, Term f l1)); trivial;
apply lex1_bis.
intros; elim (IH (Term f l,(Term f l', s'))); intuition; apply lex3; trivial.

absurd (Lex = Mul); [ discriminate | rewrite <- H3; rewrite <- H7; trivial ].

subst t f0 l0; inversion H0.
subst t f0 l0; inversion H7; clear H7.
subst s t; apply (rpo_subterm _ _ H); trivial.
subst s0 t; elim (IH (Term f l, (s, u))); intuition;
[ apply H2; trivial; apply (rpo_subterm _ _ H) | apply lex2 ]; trivial.
apply Top_gt; trivial;
subst u l0 f0; intros s' In_s'; 
elim (IH (Term f l, (Term f l', s'))); intuition; apply lex3; trivial.
absurd (Lex = Mul); [ discriminate | rewrite <- H3; rewrite <- H4; trivial ].
subst u f0 l0; apply Top_eq_mul; trivial;
inversion H5; subst l'1 l0; inversion H7; subst l'1 l0; rename l'0 into l'';
rewrite app_comm_cons in H9;
elim (ac_syntactic _ _ _ _ (list_permut_trans (list_permut_sym H1) H9));
intros lcc H'; elim H'; clear H';
intros lcg H'; elim H'; clear H';
intros lsc H'; elim H'; clear H';
intros lsg H'; elim H'; clear H';
intros P1 H'; elim H'; clear H';
intros P2 H'; elim H'; clear H';
intros P3 P4; apply (List_mul a (lg ++ lcg) (ls0 ++ lsc) lcc).
rewrite <- ass_app; apply list_permut_trans with (ls0 ++ lc0); trivial;
apply context_list_permut_app1; trivial.
apply list_permut_trans with (lcc ++ lsc); trivial; apply list_permut_app_app.
apply list_permut_trans with (a :: lg ++ lc); trivial;
apply context_list_permut_cons; rewrite <- ass_app; 
apply context_list_permut_app1;
apply list_permut_trans with (lcc ++ lcg); trivial; apply list_permut_app_app.
intros b In_b; elim (in_app_or _ _ _ In_b); clear In_b; intro In_b.
elim (H10 b In_b); intros a' H'; elim H'; clear H'; 
intros In_a' H'; elim (in_app_or _ _ _ (in_permut_in a' In_a' P4)); clear In_a'; 
intro In_a'.
exists a'; split; trivial; rewrite app_comm_cons; apply in_or_app; right; trivial.
assert (In a' ls).
refine (in_permut_in a' _ (list_permut_sym P2)); apply in_or_app; right; trivial.
elim (H3 a' H11); intros a'' H''; elim H''; intros; exists a''; 
assert (In a'' (a :: lg ++ lcg)).
rewrite app_comm_cons; apply in_or_app; left; trivial.
split; trivial; 
elim (IH (a'',(a',b))); intuition; apply lex1;
refine (in_permut_in a'' _ (list_permut_sym H2)); trivial;
rewrite app_comm_cons; apply in_or_app; left; trivial.
assert (In b ls).
refine (in_permut_in b _ (list_permut_sym P2));
apply in_or_app; left; trivial.
elim (H3 b H11); intros a'' H''; elim H''; intros; exists a''; split; trivial.
rewrite app_comm_cons; apply in_or_app; left; trivial.

inversion_clear H; trivial;
inversion_clear H0; trivial;
generalize (Anti H1 H); contradiction.

intros lt_s_t lt_t_s; inversion lt_t_s; clear lt_t_s.
subst t0 f0 l0; inversion H3; clear H3.
subst t t0; elim (IH (s, (Term f l, u))); intuition;
[ apply H1; trivial; apply (Subterm f l s s); trivial; apply Eq
| apply lex1 ]; trivial.
subst s0 t0; elim (IH (s,(t,(Term f l)))); intuition.
apply Anti0; apply (Subterm f l (Term f l) s); trivial; apply Lt; trivial.
apply lex1; trivial.
subst t f0 l0; inversion lt_s_t; clear lt_s_t.
subst t f0 l0; inversion H5; clear H5.
subst t s; apply Anti0; apply H3; trivial.
subst s s0; elim (IH (Term f l, (t,u))); intuition; apply lex2; trivial.
subst g0 l'0 f0 l0; apply prec_antisym with f; trivial;
apply prec_transitive with g; trivial.
subst f0 l'0 g l0; apply prec_antisym with f; trivial.
subst f0 l'0 g l0; apply prec_antisym with f; trivial.
subst t f0 l0; inversion lt_s_t; clear lt_s_t.
subst t f0 l0; inversion H6; clear H6.
subst s t; apply Anti0; trivial; apply H4; trivial.
subst s s0; elim (IH (Term f l, (t,u))); intuition; apply lex2; trivial.
apply prec_antisym with f; trivial.
generalize l' IH H3 H6; subst f0 l'0 l0; clear Anti0 H1 H3 H4 IH H5 H6 H7;
induction l; intros; inversion H3; clear H3.
subst t l'0 l'1; inversion H6; clear H6.
subst s0 l1 t l0; elim (IH (a,(s,u))); intuition; apply lex1; left; trivial.
subst s; elim (IH (a, (Term f (a::l0),u))); intuition; apply lex1; left; trivial.
subst s l'0 l'1; inversion H6; clear H6.
elim (IH (a, (Term f (a::l0),u))); intuition; apply lex1; left; trivial.
subst l'0 s l1; apply IHl with l0; trivial;
intros; apply IH;
apply o_size3_trans with (Term f l, (Term f l0, u)); trivial; apply lex1_bis.

absurd (Lex = Mul); [ discriminate | rewrite <- H1; rewrite <- H5; trivial ].

subst t f0 l0; inversion lt_s_t.
subst t f0 l0; inversion H3; subst l0 l'0.
elim (in_app_or _ _ _ (in_permut_in s H4 H)); intro In_s.
elim (H1 s In_s); intros a' H'; elim H'; clear H'; 
intros In_a' H'; apply Anti0; apply (Subterm f l (Term f l) a').
refine (in_permut_in a' _ (list_permut_sym H0)); 
 rewrite app_comm_cons; apply in_or_app; left; trivial.
inversion H5; subst s; apply Lt; trivial;
elim (IH (a',(t,(Term f l)))); intuition; apply lex1;
refine (in_permut_in a' _ (list_permut_sym H0));
rewrite app_comm_cons; apply in_or_app; left; trivial.
apply Anti0; apply (Subterm f l (Term f l) s); trivial;
refine (in_permut_in s _ (list_permut_sym H0)); 
 rewrite app_comm_cons; apply in_or_app; right; trivial.
apply prec_antisym with f; trivial.
absurd (Lex = Mul); [ discriminate | rewrite <- H2; rewrite <- H4; trivial ].

subst f0 l'0 l0; apply Anti0; apply Top_eq_mul; trivial;
inversion H3; subst l'0 l0; inversion H5; subst l'0 l0.
rewrite app_comm_cons in H7;
elim (ac_syntactic _ _ _ _ (list_permut_trans (list_permut_sym H) H7));
intros lcc H'; elim H'; clear H';
intros lcg H'; elim H'; clear H';
intros lsc H'; elim H'; clear H';
intros lsg H'; elim H'; clear H';
intros P1 H'; elim H'; clear H';
intros P2 H'; elim H'; clear H';
intros P3 P4; apply (List_mul a (lg ++ lcg) (ls0 ++ lsc) lcc).
rewrite <- ass_app; apply list_permut_trans with (ls0 ++ lc0); trivial;
apply context_list_permut_app1; trivial;
apply list_permut_trans with (lcc ++ lsc); trivial; apply list_permut_app_app.
apply list_permut_trans with (a :: lg ++ lc); trivial;
apply context_list_permut_cons; rewrite <- ass_app; 
apply context_list_permut_app1;
apply list_permut_trans with (lcc ++ lcg); trivial; apply list_permut_app_app.
intros b In_b; elim (in_app_or _ _ _ In_b); clear In_b; intro In_b.
elim (H8 b In_b); intros a' H'; elim H'; clear H'; 
intros In_a' H'; elim (in_app_or _ _ _ (in_permut_in a' In_a' P4)); clear In_a'; 
intro In_a'.
exists a'; split; trivial; rewrite app_comm_cons; apply in_or_app; right; trivial.
assert (In a' ls).
refine (in_permut_in a' _ (list_permut_sym P2)); apply in_or_app; right; trivial.
elim (H1 a' H9); intros a'' H''; elim H''; intros; exists a''; 
assert (In a'' (a :: lg ++ lcg)).
rewrite app_comm_cons; apply in_or_app; left; trivial.
split; trivial; 
elim (IH (a'',(a',b))); intuition; apply lex1;
refine (in_permut_in a'' _ (list_permut_sym H0)); trivial;
rewrite app_comm_cons; apply in_or_app; left; trivial.
assert (In b ls).
refine (in_permut_in b _ (list_permut_sym P2));
apply in_or_app; left; trivial.
elim (H1 b H9); intros a'' H''; elim H''; intros; exists a''; split; trivial.
rewrite app_comm_cons; apply in_or_app; left; trivial.

intro lt_s_s; inversion lt_s_s; clear lt_s_s.
inversion H3; clear H3.
subst t0 f0 l0 t1 s;
absurd (size (Term f l) < size (Term f l)); auto with arith;
apply (size_direct_subterm (Term f l) (Term f l) H2).
subst t0 f0 l0 s0 t1.
elim (IH (s,(Term f l, s))); intuition.
apply H1; trivial; apply (Subterm f l s s); trivial; apply Eq; trivial.
apply lex1; trivial.
apply prec_antisym with f; trivial.
subst f0 l' l0; clear H4; induction l; inversion H3.
elim (IH (a,(t,u))); intuition; apply lex1; left; trivial.
subst s l0 l'; apply IHl; trivial; intros; apply IH;
apply o_size3_trans with (Term f l, (t, u)); trivial; apply lex1_bis.

subst f0 l0 l'; inversion H3.
subst l' l0; assert (list_permut ls (a :: lg)).
apply remove_context_list_permut_app2 with lc; rewrite <- app_comm_cons; 
apply list_permut_trans with l; trivial;
apply list_permut_sym; trivial.
assert (forall b, In b ls -> (exists a', In a' ls /\ rpo b a')).
intros b In_b; elim (H1 b In_b); intros a' H'; exists a'; intuition;
refine (in_permut_in _ _ (list_permut_sym H4)); trivial.
assert (forall v, In v ls -> In v l).
intros; refine (in_permut_in _ _ (list_permut_sym H));
apply in_or_app; left; trivial.
assert (1 <= length ls). 
rewrite (list_permut_length H4); simpl; auto with arith.
generalize H5 H6; clear a lg H4 H5 H6 H2 H3 H0 H1 H;
induction ls; intros.
absurd (1 <= 0); auto with arith.
destruct ls.
elim (H5 a (or_introl _ (refl_equal _))); intros a' H'; 
elim H'; clear H'; intros In_a' lt_a_a'; elim In_a'; clear In_a'; intro In_a'.
subst a'; elim (IH (a,(t,u))); intuition; apply lex1; apply H6; left; trivial.
contradiction.
apply IHls.
simpl; auto with arith.
intros b In_b; elim (H5 b).
intros a' H'; elim H'; clear H'; 
intros In_a' lt_b_a'; elim In_a'; clear In_a';
intro In_a'.
subst a'; elim (H5 a (or_introl _ (refl_equal _))); 
intros a'' H''; elim H''; clear H''; 
intros In_a'' lt_a_a''; elim In_a''; clear In_a'';
intros In_a''.
subst a''; elim (IH (a,(t,u))); intuition; apply lex1; apply H6; left; trivial.
exists a''; split; trivial.
elim (IH (a'',(a,b))); intuition; apply lex1; apply H6; right; trivial.
exists a'; split; trivial.
right; trivial.
intros; apply H6; right; trivial.
Qed.

Lemma rpo_trans : forall s t u, rpo t s -> rpo u t -> rpo u s.
Proof.
intros s t u lt_t_s lt_u_t; elim (rpo_closure s t u); intuition.
Qed.

Record SN_term : Set := 
  mk_sn 
  {
    tt : term; 
    sn : Acc rpo tt
    }.

(** ** Well-foundedness of rpo. 
How to build a built a list of pairs (terms, proof of accessibility) from
a global of accessibility on the list. *)
Definition build_list_of_SN_terms :
 forall l (proof : forall t, In t l -> Acc rpo t), list SN_term.  
Proof.
intro l; induction l.
intros _; exact nil.
intro Acc_subterm; assert (Acc rpo a).
apply Acc_subterm; left; trivial.
assert (forall t, In t l -> Acc rpo t).
intros; apply Acc_subterm; right; trivial.
exact ((mk_sn a H) :: (IHl H0)).
Defined.

(** Projection on the first element of the pairs after building the
pairs as above is the identity. *)
Lemma projection_list_of_SN_terms :
  forall l proof, map tt (build_list_of_SN_terms l proof) = l.
Proof.
intro l; induction l; simpl; trivial.
intros proof; apply (f_equal (fun l => a :: l)); apply IHl.
Qed.

Lemma in_sn_sn : 
 forall l s, In s (map tt l) -> Acc rpo s.
Proof.
intro l; induction l.
contradiction.
intros s In_s; elim In_s; clear In_s; intro In_s.
subst s; destruct a; trivial.
apply IHl; trivial.
Qed.

(** Definition of rpo on accessible terms. *)
Definition rpo_rest := fun s t => rpo (tt s) (tt t).

(** Extension of [rpo_lex] to the accessible terms. *)
Inductive rpo_lex_rest : list SN_term -> list SN_term -> Prop :=
  | List_gt_rest : 
       forall s t l l', rpo_rest s t -> length l = length l' -> 
       rpo_lex_rest (s :: l) (t :: l')
  | List_eq_rest : forall s t l l', tt s = tt t -> rpo_lex_rest l l' -> 
        rpo_lex_rest (s :: l) (t :: l').

(** A triviality: rpo on accessible terms is well-founded. *)
Lemma wf_on_rest : well_founded rpo_rest.
Proof.
unfold well_founded, rpo_rest; intro s;
apply (Acc_inverse_image SN_term term rpo tt).
destruct s; simpl; trivial.
Qed.

Lemma rpo_lex_rest_same_length :
  forall l l', rpo_lex_rest l l' -> length l = length l'.
Proof.
induction l; intros l' rpo_lex_l; inversion rpo_lex_l.
simpl; rewrite H3; trivial.
simpl; rewrite (IHl l'0); trivial.
Qed.

(** Proof of accessibility does not actually matter, provided at least 
one exists. *)
Lemma acc_lex_drop_proof :
  forall s t l, tt s = tt t -> Acc rpo_lex_rest (s::l) -> Acc rpo_lex_rest (t::l).
Proof.
intros s t l s_eq_t Acc_s.
apply Acc_intro; intros l' lt_l'_l;
apply Acc_inv with (s :: l); trivial; inversion lt_l'_l.

subst l' t0 l'0; apply List_gt_rest; trivial;
unfold rpo_rest in *; rewrite s_eq_t; trivial.

subst l' t0 l'0; apply List_eq_rest; trivial;
rewrite s_eq_t; trivial.
Qed.

(** Lexicographic extension of rpo on accessible terms lists is well-founded. *)
Lemma wf_on_lex_rest : well_founded rpo_lex_rest.
Proof.
unfold well_founded; intro a; pattern a; apply list_rec2; clear a; 
induction n;
intros l L; destruct l.
apply Acc_intro; intros l' lt_l'_l; inversion lt_l'_l.
simpl in L; absurd (S(length l) <= 0); auto with arith.
apply Acc_intro; intros l' lt_l'_l; inversion lt_l'_l.
simpl in L; generalize (le_S_n _ _ L); clear L; intro L.
generalize l L; clear l L; pattern s;
apply (well_founded_induction_type wf_on_rest);
clear s; intros s IH l L.
generalize (IHn l L); intro Acc_l; induction Acc_l; rename x into l.
apply Acc_intro; intros l' lt_l'_l; inversion lt_l'_l.
subst l' t l'0; apply IH; trivial; rewrite H5; trivial.
subst l' t l'0; apply acc_lex_drop_proof with s.
apply sym_eq; trivial.
apply H0; trivial; rewrite (rpo_lex_rest_same_length _ _ H5); trivial.
Qed.

(** Extension of [rpo_mul] to the accessible terms. *)
Inductive rpo_mul_rest : list SN_term -> list SN_term -> Prop :=
  | List_mul_rest : 
       forall a lg ls lc l l', 
       list_permut (map tt l') (map tt (ls ++ lc)) ->
       list_permut (map tt l) (map tt (a :: lg ++ lc)) ->
       (forall b, In b ls -> exists a', In a' (a :: lg) /\ rpo_rest b a') ->
       rpo_mul_rest l' l.

(** Definition of a finer grain for multiset extension. *)
Inductive rpo_mul_rest_step : list SN_term -> list SN_term -> Prop :=
  | List_mul_rest_step : 
       forall a ls lc l l', 
       list_permut (map tt l') (map tt (ls ++ lc)) ->
       list_permut (map tt l) (map tt (a :: lc)) ->
       (forall b, In b ls -> rpo_rest b a) ->
       rpo_mul_rest_step l' l.

(** The plain multiset extension is in the transitive closure of
the finer grain extension. *)
Lemma rpo_mul_trans_clos :
  inclusion _ rpo_mul_rest (clos_trans _ rpo_mul_rest_step).
Proof.
unfold inclusion; intros l' l H; inversion H; clear H; subst l0 l'0;
generalize l' l a ls lc H0 H1 H2; clear l' l a ls lc H0 H1 H2;
induction lg.
intros l' l a ls lc H0 H1 H2;
apply t_step; apply (List_mul_rest_step a ls lc); trivial;
intros b In_b; elim (H2 b In_b); 
intros a' H'; elim H'; clear H';
intros In_a' lt_b; elim In_a'; clear In_a'; 
intro In_a'; [subst a'; trivial | contradiction ].
intros l' l a0 ls lc H0 H1 H2.
assert (exists ls1, exists ls2, 
 list_permut (map tt ls) (map tt (ls1 ++ ls2)) /\
 (forall b, In b ls1 -> rpo_rest b a0) /\
 (forall b, In b ls2 -> exists a', In a' ( a:: lg) /\ rpo_rest b a')).
clear H0; induction ls.
exists (nil : list SN_term); exists (nil : list SN_term); intuition.
contradiction.
contradiction.
elim IHls.
intros ls1 H; elim H; clear H;
intros ls2 H; elim (H2 a1 (or_introl _ (refl_equal _)));
intros a' H'; elim H'; clear H';
intros In_a' H'; elim In_a'; clear In_a'; 
intro In_a'.
subst a'; exists (a1 :: ls1); exists ls2; intuition.
rewrite <- app_comm_cons; simpl; apply context_list_permut_cons; trivial.
elim H3; clear H3; intro H3.
subst b; trivial.
apply H; trivial.
exists ls1; exists (a1 :: ls2); intuition.
rewrite map_app; simpl; apply (list_permut_add_cons_inside);
rewrite <- map_app; trivial.
elim H3; clear H3; intro H3.
subst b; exists a'; intuition.
apply H4; trivial.
intros; apply H2; trivial; right; trivial.
elim H; clear H;
intros ls1 H; elim H; clear H; 
intros ls2 H; apply t_trans with (a0 :: ls2 ++ lc). 
apply t_step; apply (List_mul_rest_step a0 ls1 (ls2 ++ lc)).
apply list_permut_trans with (map tt (ls ++ lc)); trivial.
rewrite <- app_ass; do 2 rewrite map_app; apply context_list_permut_app2; intuition.
apply list_permut_refl.
intuition.
apply (IHlg (a0 :: ls2 ++ lc) l a ls2 (a0 :: lc)).
rewrite map_app; simpl; apply list_permut_add_cons_inside;
rewrite map_app; apply list_permut_refl.
apply list_permut_trans with (map tt (a0 :: (a :: lg) ++ lc)); trivial.
do 2 rewrite app_comm_cons; generalize (a :: lg); intro l0.
do 2 rewrite map_app; simpl; apply list_permut_add_cons_inside;
apply list_permut_refl.
intuition.
Qed.

(** Splitting in two disjoint cases. *)
Lemma two_cases_rpo :
 forall a m n, 
 rpo_mul_rest_step n (a :: m) ->
 (exists n', list_permut (map tt n) (map tt (a :: n')) /\ 
             rpo_mul_rest_step n' m) \/
 (exists k, (forall b, In b k -> rpo_rest b a) /\ 
            list_permut (map tt n) (map tt (k ++ m))).
Proof.
intros a m n M; inversion_clear M;
destruct a; destruct a0; elim (eq_term_dec tt0 tt1).
intro; subst tt1; right; exists ls; intuition;
apply list_permut_trans with (map tt (ls ++ lc)); trivial;
do 2 rewrite map_app; apply context_list_permut_app1;
apply remove_context_list_permut_cons with tt0; 
apply list_permut_sym; trivial.
intro a_diff_a0; left;
elim (In_dec eq_term_dec tt1 (map tt m)); intro In_a0.
generalize (split_list_app_cons eq_term_dec _ _ In_a0); clear In_a0;
destruct (split_list eq_term_dec (map tt m) tt1).
intro; assert (forall s, In s l -> Acc rpo s).
intros s In_s; apply in_sn_sn with m; rewrite H2; apply in_or_app; left; trivial.
assert (forall s, In s l0 -> Acc rpo s).
intros s In_s; apply in_sn_sn with m; rewrite H2; apply in_or_app; do 2 right; trivial.
exists ((build_list_of_SN_terms l H3) ++ ls ++ (build_list_of_SN_terms l0 H4)); 
intuition.
apply list_permut_trans with (map tt (ls ++ lc)) ; trivial;
apply remove_context_list_permut_cons with tt1;
apply list_permut_trans with ((map tt ls) ++ tt1 :: (map tt lc)).
apply list_permut_add_cons_inside; rewrite map_app; apply list_permut_refl.
apply list_permut_trans with (map tt ls ++ (tt0 :: l ++ tt1 :: l0)).
apply context_list_permut_app1; apply list_permut_sym; rewrite <- H2; trivial.
rewrite app_comm_cons; rewrite <- app_ass; apply list_permut_sym;
apply list_permut_add_cons_inside;
rewrite app_ass; rewrite <- app_comm_cons; simpl;
apply list_permut_add_cons_inside;
do 2 rewrite map_app; do 2 rewrite projection_list_of_SN_terms;
do 2 rewrite <- app_ass; apply context_list_permut_app2;
apply list_permut_app_app.
apply (List_mul_rest_step (mk_sn tt1 sn1) ls 
(build_list_of_SN_terms l H3 ++ build_list_of_SN_terms l0 H4)); intuition.
do 2 rewrite ass_app; do 4 rewrite map_app; 
apply context_list_permut_app2; apply list_permut_app_app.
rewrite H2; simpl; rewrite map_app; do 2 rewrite projection_list_of_SN_terms;
apply list_permut_sym; apply list_permut_add_cons_inside; 
apply list_permut_refl.
absurd (In tt1 (map tt (mk_sn tt0 sn0 :: m))).
unfold not; intro H2; elim H2; clear H2; intro H2.
apply a_diff_a0; trivial.
apply In_a0; trivial.
refine (in_permut_in tt1 _ (list_permut_sym H0)); left; trivial.
Qed.

Lemma list_permut_map_acc :
 forall l l', list_permut (map tt l) (map tt l') ->
 Acc rpo_mul_rest_step l ->  Acc rpo_mul_rest_step l'.
Proof.
intros l l' P A1; apply Acc_intro; 
intros l'' M2.
inversion A1; apply H; inversion M2.
subst l'0 l0; apply (List_mul_rest_step a ls lc); trivial.
apply list_permut_trans with (map tt l'); trivial.
Qed.

(** Multiset extension of rpo on accessible terms lists is well-founded. *)
Lemma wf_on_mul_rest : well_founded rpo_mul_rest.
Proof.
apply wf_incl with (clos_trans _ rpo_mul_rest_step).
apply rpo_mul_trans_clos.
apply wf_clos_trans.
unfold well_founded; intro a; induction a.
apply Acc_intro; intros m H; inversion_clear H.
generalize (list_permut_length H1); intro Abs; simpl in Abs;
absurd (0 = S (length (map tt (a :: lc)))); trivial; discriminate.
generalize a0 IHa; clear a0 IHa; pattern a;
refine (well_founded_ind wf_on_rest _ _ a); clear a.
intros;
apply (Acc_iter  (R:= rpo_rest)
(fun a => Acc rpo_rest a -> forall m, Acc rpo_mul_rest_step m -> 
Acc rpo_mul_rest_step (a :: m))); trivial.
destruct x; rename tt0 into s; rename sn0 into Acc_s; 
clear a0 IHa; intros b IH Acc_b m Acc_m.
apply (Acc_iter  (R:= rpo_mul_rest_step) 
        (fun m => Acc rpo_mul_rest_step m -> Acc rpo_mul_rest_step (b :: m))); trivial.
clear m Acc_m; intros m IHm Acc_m; apply Acc_intro.
intros y lt_y; elim (two_cases_rpo _ _ _ lt_y); clear lt_y; intro lt_y.
elim lt_y; clear lt_y;
intros n' H'; elim H'; clear H';
intros P M; apply list_permut_map_acc with (b :: n').
apply list_permut_sym; trivial.
apply IHm; trivial; apply Acc_inv with m; trivial.
elim lt_y; clear lt_y;
intros k H'; elim H'; clear H';
intros M P; apply list_permut_map_acc with (k ++ m).
apply list_permut_sym; trivial.
clear P; induction k; trivial.
simpl; apply IH.
apply M; left; trivial.
apply Acc_inv with b; trivial; apply M; left; trivial.
apply IHk;
intros; apply M; right; trivial.
apply wf_on_rest.
apply wf_on_rest.
Qed.

(** Another definition of rpo, only on scheme of accessible terms. *)
Definition rpo_term : relation (symbol * list SN_term) :=
 fun f_l g_l' => 
  match f_l with
  | (f,l) =>
  match g_l' with
  | (g,l') =>
    if F.eq_symbol_dec f g
    then
      match status f with
      | Lex => rpo_lex_rest l l'
      | Mul => rpo_mul_rest l l'
      end
    else prec f g
  end
  end.

Lemma  wf_rpo_term : well_founded prec -> well_founded rpo_term.
Proof.
intro wf_prec; unfold well_founded in *; destruct a; rename s into f;
generalize l; clear l; pattern f; refine (well_founded_ind wf_prec _ _ f);
clear f; intros f IHf l; pattern l;
assert (forall g, f=g -> status g = status f).
intros; subst f; trivial.
destruct (status f); generalize (H f (refl_equal _)); clear H; intro H.
pattern l; refine (well_founded_ind wf_on_lex_rest _ _ l); clear l; 
intros l IHl; apply Acc_intro; intros y; destruct y; simpl;
elim (F.eq_symbol_dec s f); intro eq1.
subst s; rewrite H; intros; apply IHl; trivial.
intros; apply IHf; trivial.
pattern l; refine (well_founded_ind wf_on_mul_rest _ _ l); clear l; 
intros l IHl; apply Acc_intro; intros y; destruct y; simpl;
elim (F.eq_symbol_dec s f); intro eq1.
subst s; rewrite H; intros; apply IHl; trivial.
intros; apply IHf; trivial.
Qed.

Lemma acc_build :
  well_founded prec -> forall f l, 
  Acc rpo (Term f (map (fun sn_tt => tt sn_tt) l)).
Proof.
intros wf_prec f l;
refine (well_founded_induction_type (wf_rpo_term wf_prec)
(fun f_l =>  
  match f_l with
  | (f,l) => Acc rpo (Term f (map (fun sn_tt : SN_term => tt sn_tt) l))
  end) _ (f,l)).
clear f l; intros x IH; destruct x; rename s into f.
apply Acc_intro; intros t; pattern t; apply term_rec3; clear t.
intros v _; apply Acc_intro; intros u lt_u_t; inversion lt_u_t.
intros g l' IH' lt_t_s; inversion lt_t_s.

subst t f0 l0; assert (Acc rpo s).
apply (in_sn_sn _ _ H2).
inversion H3; subst s; trivial; apply Acc_inv with t; trivial.

subst g0 l'0 f0 l0; assert (forall s', In s' l' -> Acc rpo s').
intros s' In_s'; apply IH'; trivial; apply H4; trivial.
rewrite <- (projection_list_of_SN_terms l' H); 
apply (IH (g,(build_list_of_SN_terms l' H)));
simpl; elim (F.eq_symbol_dec g f); intro eq1; trivial;
subst g; generalize (prec_antisym _ H2); contradiction.

subst f0 l'0 g l0; assert (forall s', In s' l' -> Acc rpo s').
intros s' In_s'; apply IH'; trivial; apply H5; trivial.

rewrite <- (projection_list_of_SN_terms l' H); 
apply (IH (f,(build_list_of_SN_terms l' H)));
simpl; elim (F.eq_symbol_dec f f); intro eq1.
rewrite H3; generalize l' H H4; clear l' H H4 H5 IH IH' lt_t_s eq1; 
induction l; intros l' H H4; inversion H4; clear H4.
subst l' t l'0; simpl; apply List_gt_rest.
unfold rpo_rest; trivial.
rewrite <- (projection_list_of_SN_terms l0 
              (fun (t : term) (H0 : In t l0) => H t (or_intror (s = t) H0))) in H6;
do 2 rewrite length_map in H6; trivial.

subst l' s l'0; simpl; apply List_eq_rest; trivial;
apply IHl; trivial.

absurd (f=f); trivial.

subst f0 l'0 g l0; assert (forall s', In s' l' -> Acc rpo s').
intros s' In_s'; apply IH'; trivial; apply (rpo_subterm _ _ lt_t_s); simpl; trivial.

rewrite <- (projection_list_of_SN_terms l' H); 
apply (IH (f,(build_list_of_SN_terms l' H)));
simpl; elim (F.eq_symbol_dec f f); intro eq1.
rewrite H2; inversion H4; subst l'0 l0; assert (Acc rpo a).
apply in_sn_sn with l; refine (in_permut_in a _ (list_permut_sym H1)); 
left; trivial.
assert (forall t, In t lg -> Acc rpo t).
intros; apply in_sn_sn with l; refine (in_permut_in _ _ (list_permut_sym H1));
right; apply in_or_app; left; trivial.
assert (forall t, In t ls -> Acc rpo t).
intros; apply H; refine (in_permut_in _ _ (list_permut_sym H0));
apply in_or_app; left; trivial.
assert (forall t, In t lc -> Acc rpo t).
intros; apply H; refine (in_permut_in _ _ (list_permut_sym H0));
apply in_or_app; right; trivial.
apply (List_mul_rest (mk_sn a H5) (build_list_of_SN_terms lg H6)
(build_list_of_SN_terms ls H7) (build_list_of_SN_terms lc H8)).
rewrite map_app; do 3 rewrite projection_list_of_SN_terms; trivial.
simpl; rewrite map_app; do 2 rewrite projection_list_of_SN_terms; trivial.
intros b In_b; destruct b; elim (H3 tt0).
intros x H'; elim H'; clear H'; intros In_x H'; 
elim In_x; clear In_x; intro In_x.
subst x; exists (mk_sn a H5); intuition.
assert (exists a', In a' (build_list_of_SN_terms lg H6) /\ tt a' = x).
generalize lg H6 In_x; clear lg H1 H3 H6 In_x; induction lg.
contradiction.
intros H6 In_x; elim In_x; clear In_x; intro In_x; simpl.
subst a0; econstructor; intuition.
elim (IHlg (fun (t : term) (H1 : In t lg) => H6 t (or_intror (a0 = t) H1)) In_x);
intros a' H''; elim H''; clear H''; intros In_a' H''.
exists a'; split; trivial; right; trivial.
elim H9; clear H9; 
intros a' H9; elim H9; clear H9; 
intros In_a' H9; exists a'; split;
[ right | unfold rpo_rest; simpl; rewrite H9 ]; trivial.
clear H0 H3; induction ls.
contradiction.
elim In_b; clear In_b; intro In_b;
[ left; injection In_b; trivial | right; refine (IHls _ In_b)].

absurd (f=f); trivial.
Qed.

(** ** Main theorem: when the precedence is well-founded, so is the rpo. *)
Lemma wf_rpo : well_founded prec -> well_founded rpo.
Proof.
intro wf_prec;
unfold well_founded; intro t; pattern t; apply term_rec3; clear t.
intro v; apply Acc_intro; intros t lt_t_s; inversion lt_t_s.
intros f l Acc_subterm;
rewrite <- (projection_list_of_SN_terms l Acc_subterm). 
apply acc_build; trivial.
Qed.

(** ** RPO is compatible with the instanciation by a substitution. *)
Lemma rpo_subst :
  forall t s, rpo s t -> 
  forall sigma, rpo (apply_subst sigma s) (apply_subst sigma t).
Proof.
intro t; pattern t; apply term_rec3; clear t.
intros v s H; inversion H.
intros f l IHl s; simpl; pattern s; apply term_rec3; clear s.
(* case s = Var v; rpo by Subterm *)
intros v R; inversion R as [ f' l' s' t In_t_l R' H1 H2 | | | ]; subst; 
intro sigma; simpl; apply Subterm with (apply_subst sigma t).
apply in_in_map; trivial.
inversion R' as [ s' R'' | s' t' R'' ]; subst; simpl;
[ apply Eq| apply Lt; refine (IHl _ In_t_l _ R'' sigma) ].
(* case s = Term f l *)
intros g k IHl' R sigma; 
inversion R as [ f' l' s' t In_t_l R' H1 H2 
                       | f' g' l' l'' R' R'' H1 H2
                       | g' l' k' f_lex Rlex R' H2 H3
                       | g' l' k' f_mul Rmul R' H2 ]; subst.
(* case Subterm *)
apply Subterm with (apply_subst sigma t).
apply in_in_map; trivial.
inversion R' as [ s' R'' | s' t' R'' ]; subst; 
[ apply Eq | apply Lt; apply IHl; trivial ].
(* case Top_gt *)
simpl; apply Top_gt; trivial.
intros s' In_s'; elim (in_map_in _ s' _ In_s'); intros s [H1 H2]; subst.
apply IHl'; trivial; apply R''; trivial.
(* case Top_eq_lex *)
simpl; apply Top_eq_lex; trivial.
generalize l Rlex IHl; clear l R Rlex R' IHl IHl';
induction k as [ | s' k ]; intros l Rlex IHl; inversion Rlex; subst; simpl.
apply List_gt; [ apply IHl; trivial; left | do 2 (rewrite length_map) ]; trivial.
apply List_eq; apply IHk; trivial;
intros; apply IHl; trivial; right; trivial.
intros s' In_s'; elim (in_map_in _ s' _ In_s'); 
intros s [In_s H1]; subst; apply IHl'; trivial;
apply rpo_trans with (Term f k); trivial;
apply Subterm with s; trivial; apply Eq.
(* case Top_eq_mul *)
simpl; apply Top_eq_mul; trivial.
inversion Rmul as [ a lg ls lc l0 k0 Pk Pl H]; subst.
apply (List_mul (apply_subst sigma a) (map (apply_subst sigma) lg)
(map (apply_subst sigma) ls) (map (apply_subst sigma) lc)).
rewrite <- map_app; apply list_permut_map; trivial.
rewrite <- map_app;
generalize (list_permut_map (apply_subst sigma) Pl); simpl; trivial.
intros b' In_b'; elim (in_map_in _ b' _ In_b'); 
intros b [In_b H1]; subst; elim (H b In_b); intros a' [ In_a' H1 ];
exists (apply_subst sigma a'); split.
generalize (in_in_map (apply_subst sigma) _ _ In_a'); simpl; trivial.
apply IHl; trivial;
apply in_permut_in with (a :: lg ++ lc).
elim In_a'; clear In_a'; intro In_a'; subst.
left; trivial.
right; apply in_or_app; left; trivial.
apply list_permut_sym; trivial.
Qed.

(** ** RPO is compatible with adding context. *)
Lemma rpo_add_context :
 forall p ctx s t, rpo s t -> is_a_pos ctx p = true -> 
  rpo (replace_at_pos ctx s p) (replace_at_pos ctx t p).
Proof.
intro p; induction p as [ | i p ]; intros ctx s t R H; trivial;
destruct ctx as [ v | f l ].
discriminate.
assert (Status : forall g, g = f -> status g = status f).
intros; subst; trivial.
do 2 (rewrite replace_at_pos_unfold);
destruct (status f); generalize (Status f (refl_equal _)); clear Status; 
intro Status.
apply Top_eq_lex; trivial.
generalize l i H; clear l i H; induction l as [ | u1 l ]; intros i H.
destruct i; discriminate.
destruct i; simpl in H; simpl.
apply List_gt; trivial; apply IHp; trivial.
apply List_eq; apply IHl; trivial.
intros s' In_s'; 
assert (H' : exists t', In t' (replace_at_pos_list l t i p) /\ rpo_eq s' t').
generalize l i H In_s'; clear l i H In_s'; 
induction l as [ | u1 l ]; intros i H In_s'.
destruct i; discriminate.
destruct i; elim In_s'; clear In_s'; intro In_s'; subst.
exists (replace_at_pos u1 t p); split; [ left | apply Lt; apply IHp ]; trivial.
exists s'; split; [ right; trivial | apply Eq ].
exists s'; split; [ left; trivial | apply Eq ].
elim (IHl i H In_s'); intros t' [H1 H2]; exists t'; split; [ right | idtac ]; trivial.
elim H'; clear H'; intros t' [H1 H2]; apply Subterm with t'; trivial.

apply Top_eq_mul; trivial.
assert (H' : exists l1, exists ui, exists l2, l = l1 ++ ui :: l2 /\ length l1 = i).
generalize i H; clear i H; induction l as [ | u1 l ]; intros i H.
destruct i; discriminate.
destruct i as [ | i ].
exists (nil (A:= term)); exists u1; exists l; split; trivial.
elim (IHl i H); intros l1 [ ui [ l2 [ H1 H2]]].
exists (u1 :: l1); exists ui; exists l2; split; subst; trivial.
elim H'; clear H';  intros l1 [ ui [ l2 [ H1 H' ]]]; subst l.
do 2 (rewrite replace_at_pos_list_replace_at_pos_in_subterm; trivial).
apply (List_mul (replace_at_pos ui t p) nil (replace_at_pos ui s p :: nil) 
          (l1 ++ l2)).
simpl; apply list_permut_sym; 
apply list_permut_add_cons_inside; apply list_permut_refl.
simpl; apply list_permut_sym; 
apply list_permut_add_cons_inside; apply list_permut_refl.
intros b In_b; elim In_b; clear In_b; intro In_b; subst.
exists (replace_at_pos ui t p); split; [ left | apply IHp ]; trivial.
induction l1 as [ | u1 l1 ]; trivial; apply IHl1; trivial.
contradiction.
Qed.

End Make.








