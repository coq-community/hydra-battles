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

(** * Term algebra defined as functor from a Module Signature and a Module Variable.*)

Require Import List.
Require Import more_list.
Require Import list_permut.
Require Import list_set.
Require Import Arith.

Set Implicit Arguments.

(** * Module Type Signature. 
 There are almost no assumptions, except a decidable equality 
and an arity function. *)
Module Type Signature.

  Parameter symb : Set.
  Axiom eq_symbol_dec : forall f1 f2 : symb, {f1 = f2} + {f1 <> f2}.

  (** The arity of a symbol contains also the information about built-in theories as in CiME *)
  Inductive arity_type : Set :=
  | AC : arity_type
  | C : arity_type
  | Free : nat -> arity_type.

  Parameter arity : symb -> arity_type.
End Signature.

(** * Module Type Variables. 
 There are almost no assumptions, except a decidable equality. *) 
Module Type Variables.

  Parameter var : Set.
  Axiom eq_variable_dec : forall v1 v2 : var, {v1 = v2} + {v1 <> v2}.

End Variables.

(** * Module Type Term built from a signature and a set of variables. *)
Module Type Term.

  Declare Module F : Signature.
  Declare Module X : Variables.

  Definition symbol := F.symb.
  Definition variable := X.var.

  Import F.
  Import X.

  (* Declare Module VSet : list_set.S with Definition DS.A := variable. *)

  Ltac destruct_arity f n Af :=
    generalize (refl_equal (arity f)); pattern f at 1; destruct (arity f) as [ |  | n]; intro Af.


  (** Definition of terms. 
Arity is not taken into account, and terms may be hill-formed. *)
  Inductive term : Set :=
  | Var : variable -> term
  | Term : symbol -> list term -> term.

  Definition direct_subterm t1 t2 : Prop :=
    match t2 with
    | Var _ => False
    | Term _ l => In t1 l
    end.

  (** Definition and a few properties of the size of a term.*)
  Fixpoint size (t:term) : nat :=
    match t with
    | Var v => 1
    | Term f l => 1 + fold_left (fun size_acc e => size_acc + size e) l 0
    end.

  Axiom size_unfold :
    forall t, size t = match t with
                       | Var _ => 1
                       | Term f l => 1 + list_size size l
                       end.

  Axiom size_ge_one : forall t, 1 <= size t.

  Axiom size_direct_subterm :
    forall t1 t2, direct_subterm t1 t2 -> size t1 < size t2.

  (** ** Recursion on terms. *)
  Section Recursion.
    Variable P : term -> Type.
    Variable Pl : list term -> Type.

    Axiom term_rec2 : (forall n t, size t <= n -> P t) -> forall t, P t.
    Axiom term_rec3 :
      (forall v, P (Var v)) -> (forall f l, (forall t, In t l -> P t) -> P (Term f l)) -> forall t, P t.
    Axiom term_rec4 :
      (forall v, P (Var v)) -> (forall f l, Pl l -> P (Term f l)) ->
      (forall l, (forall t, In t l -> P t) -> Pl l) -> forall t, P t.
  End Recursion.

  (** ** Double recursion on terms. *)
  Section DoubleRecursion.
    Variable P2 : term -> term -> Type.
    Variable Pl2 : list term -> list term -> Type.

    Axiom term_rec7 :
      (forall v1 t2, P2 (Var v1) t2) ->
      (forall t1 v2, P2 t1 (Var v2)) ->
      (forall f1 f2 l1 l2, Pl2 l1 l2 -> P2 (Term f1 l1) (Term f2 l2)) ->
      (forall l1 l2, (forall t1 t2, In t1 l1 -> In t2 l2 -> P2 t1 t2) -> Pl2 l1 l2) ->
      forall t1 t2, P2 t1 t2.

    Axiom term_rec8 :
      (forall v1 t2, P2 (Var v1) t2) ->
      (forall t1 v2, P2 t1 (Var v2)) ->
      (forall f1 f2 l1 l2, Pl2 l1 l2 -> P2 (Term f1 l1) (Term f2 l2)) ->
      (forall l1 l2, (forall t1 t2, In t1 l1 -> In t2 l2 -> P2 t1 t2) -> Pl2 l1 l2) ->
      forall l1 l2, Pl2 l1 l2.
  End DoubleRecursion.

  (** ** Equality on terms is decidable. *)
  Axiom eq_term_dec :  forall t1 t2:term, {t1 = t2} + {t1 <> t2}.
  Declare Module Term_eq_dec : decidable_set.S with Definition A:= term 
    with Definition eq_A_dec := eq_term_dec.

  (** ** Well-formedness of terms, according to the arity. *)
  Fixpoint well_formed (t:term) : Prop :=
    match t with
    | Var _ => True
    | Term f l =>
      let well_formed_list :=
          (fix well_formed_list (l:list term) : Prop :=
             match l with
             | nil => True
             | h :: tl => well_formed h /\ well_formed_list tl
             end) in
      well_formed_list l /\
      (match arity f with
       | Free n => length l = n 
       | _ => length l = 2
       end)
    end.

  Axiom well_formed_unfold :
    forall t, well_formed t ->
              match t with 
              | Var _ => True
              | Term f l =>
                (forall u, In u l -> well_formed u) /\
                (match arity f with
                 | Free n => length l = n
                 | _ => length l = 2
                 end)
              end.

  Axiom well_formed_fold :
    forall t,
      match t with 
      | Var _ => True
      | Term f l =>
        (forall u, In u l -> well_formed u) /\
        (match arity f with
         | Free n => length l = n
         | _ => length l = 2
         end)
      end -> well_formed t.

  Fixpoint well_formed_list (l : list term) : Prop :=
    match l with
    | nil => True
    | h :: tl => well_formed h /\ well_formed_list tl
    end.

  (** ** Substitutions. *)
  Definition substitution := list (variable * term).

  Fixpoint apply_subst (sigma : substitution) (t : term) {struct t} : term :=
    match t with
    | Var v => 
      match find eq_variable_dec v sigma with
      | None => t
      | Some v_sigma => v_sigma
      end
    | Term f l => Term f (map (apply_subst sigma) l)
    end.

  Axiom empty_subst_is_id : forall t, apply_subst nil t = t.
  Axiom empty_subst_is_id_list : forall l, map (apply_subst nil) l = l.

  (** Composition of substitutions. *)
  Definition map_subst (f : variable -> term -> term) sigma :=
    map (fun x =>
           match (x : variable * term) with
           | (v, v_sigma) => (v, f v v_sigma)
           end)
        sigma.

  Definition subst_comp sigma1 sigma2 :=
    (map_subst (fun _ t => apply_subst sigma1 t) sigma2)
      ++ 
      (map_subst (fun v t =>
                    match find eq_variable_dec v sigma2 with
                    | None => t
                    | Some v_sigma2 => apply_subst sigma1 v_sigma2
                    end)
                 sigma1).

  Axiom subst_comp_is_subst_comp_aux1 :
    forall v sigma f,
      find eq_variable_dec v (map_subst f sigma) =
      match find eq_variable_dec v sigma with
      | None => None
      | Some t => Some (f v t)
      end.

  Axiom subst_comp_is_subst_comp :
    forall sigma1 sigma2 t,
      apply_subst (subst_comp sigma1 sigma2) t =
      apply_subst sigma1 (apply_subst sigma2 t).

  (** Well-formed substitutions. *)
  Definition well_formed_subst sigma :=
    forall v, match find eq_variable_dec v sigma with
              | None => True
              | Some t => well_formed t 
              end.

  Axiom well_formed_apply_subst :
    forall sigma, well_formed_subst sigma -> 
                  forall t, well_formed t -> well_formed (apply_subst sigma t).

  (** ** Positions in a term.*)
  Fixpoint is_a_pos (t : term) (p : list nat) {struct p}: bool :=
    match p with
    | nil => true
    | i :: q =>
      match t with
      | Var _ => false
      | Term _ l => 
        match nth_error l i with
        | Some ti => is_a_pos ti q
        | None => false
        end
      end
    end.

  Fixpoint subterm_at_pos (t : term) (p : list nat) {struct p}: option term :=
    match p with
    | nil => Some t
    | i :: q =>
      match t with
      | Var _ => None
      | Term _ l => 
        match nth_error l i with
        | Some ti => subterm_at_pos ti q
        | None => None
        end
      end
    end.

  Axiom size_subterm_at_pos :
    forall t i p, match subterm_at_pos t (i :: p) with
	          | Some u => size u < size t
	          | None => True
	          end.

  Axiom is_a_pos_exists_subtem :
    forall t p, is_a_pos t p = true -> exists u, subterm_at_pos t p = Some u.

  Fixpoint replace_at_pos (t u : term) (p : list nat) {struct p} : term :=
    match p with
    | nil => u
    | i :: q =>
      match t with
      | Var _ => t
      | Term f l =>
        let replace_at_pos_list :=
            (fix replace_at_pos_list j (l : list term) {struct l}: list term :=
               match l with
               | nil => nil
               | h :: tl =>
                 match j with
                 | O => (replace_at_pos h u q) :: tl
                 | S k => h :: (replace_at_pos_list k tl)
                 end
               end) in
        Term f (replace_at_pos_list i l)
      end
    end.

  Fixpoint replace_at_pos_list (l : list term) (u : term) (i : nat) (p : list nat) 
           {struct l}: list term :=
    match l with
    | nil => nil
    | h :: tl =>
      match i with
      | O => (replace_at_pos h u p) :: tl
      | S j => h :: (replace_at_pos_list tl  u j p)
      end
    end.

  Axiom replace_at_pos_unfold :
    forall f l u i q,
      replace_at_pos (Term f l) u (i :: q) = Term f (replace_at_pos_list l u i q).

  Axiom replace_at_pos_is_replace_at_pos1 :
    forall t u p, is_a_pos t p = true ->
                  subterm_at_pos (replace_at_pos t u p) p = Some u.

  Axiom replace_at_pos_is_replace_at_pos2 :
    forall t p u, subterm_at_pos t p = Some u -> replace_at_pos t u p = t. 

  Axiom subterm_at_pos_apply_subst_apply_subst_subterm_at_pos :
    forall t p sigma, 
      match subterm_at_pos t p with
      | Some u =>
        subterm_at_pos (apply_subst sigma t) p = Some (apply_subst sigma u)
      | None => True
      end.

  Axiom replace_at_pos_list_replace_at_pos_in_subterm :
    forall l1 ui l2 u i p, length l1 = i ->
                           replace_at_pos_list (l1 ++ ui :: l2) u i p = 
                           l1 ++ (replace_at_pos ui u p) :: l2.

End Term.


(** * A functor building a Term Module from a Signature and a set of Variables.*)

Module Make (F1 : Signature) (X1 : Variables) <: 
  Term with Module F := F1 with Module X := X1.

  Module F := F1.
  Module X := X1.

  Definition symbol := F.symb.
  Definition variable := X.var.

  Import F.
  Import X.

  Module DecVar <: decidable_set.S.
    Definition A := variable.

    Lemma eq_A_dec : forall x y : A, { x = y } + { x <> y }.
    Proof.
      apply eq_variable_dec.
    Qed.

  End DecVar.

  Module VSet <: list_set.S with Definition DS.A := variable :=
    list_set.Make (DecVar).

  (** Definition of terms. 
Arity is not taken into account, and terms may be ill-formed. *)
  Inductive term : Set :=
  | Var : variable -> term
  | Term : symbol -> list term -> term.

  Definition direct_subterm t1 t2 : Prop :=
    match t2 with
    | Var _ => False
    | Term _ l => In t1 l
    end.

  (** Definition and a few properties of the size of a term.*)
  Fixpoint size (t:term) : nat :=
    match t with
    | Var v => 1
    | Term f l => 1 + fold_left (fun size_acc e => size_acc + size e) l 0
    end.

  Lemma size_unfold :
    forall t,
      size t = match t with
               | Var _ => 1
               | Term f l => 1 + list_size size l
               end.
  Proof.
    intro t; destruct t as [x | f l]; trivial.
    simpl; rewrite list_size_fold; trivial.
  Qed.

  Lemma size_ge_one : forall t, 1 <= size t.
  Proof.
    destruct t as [ x | f l ]; trivial.
    rewrite size_unfold; auto with arith.
  Qed.

  Lemma size_direct_subterm :
    forall t1 t2, direct_subterm t1 t2 -> size t1 < size t2.
  Proof.
    intros t1 t2; unfold direct_subterm; destruct t2 as [ x | f l ].
    contradiction.
    rewrite (size_unfold (Term f l)).
    induction l as [ | t l]; simpl; intuition.
    subst; auto with arith.
    apply lt_le_trans with (1 + list_size size l); trivial;
      simpl; auto with arith.
  Qed.

  (** ** Recursion on terms. *)
  Section Recursion.
    Variable P : term -> Type.
    Variable Pl : list term -> Type.

    Definition term_rec2 : (forall n t, size t <= n -> P t) -> forall t, P t.
    Proof.
      intros H t; apply (H (size t) t); apply le_n.
    Qed.

    Definition term_rec3 :
      (forall v, P (Var v)) -> (forall f l, (forall t, In t l -> P t) -> P (Term f l)) -> forall t, P t.
    Proof.
      intros Hvar Hterm; apply term_rec2; induction n; intros t Size_t.
      absurd (1 <= 0); auto with arith; 
        apply le_trans with (size t); trivial; apply size_ge_one.
      destruct t as [ x | f l ]; trivial;
        apply Hterm; intros; apply IHn;
          apply lt_n_Sm_le;
          apply lt_le_trans with (size (Term f l)); trivial;
            apply size_direct_subterm; trivial.
    Qed.

    Definition term_rec4 :
      (forall v, P (Var v)) -> (forall f l, Pl l -> P (Term f l)) ->
      (forall l, (forall t, In t l -> P t) -> Pl l) -> forall t, P t.
    Proof.
      intros Hvar Hterm Hlist; apply term_rec2; 
        induction n; intros t Size_t.
      absurd (1<=0); auto with arith;
        apply le_trans with (size t); trivial; apply size_ge_one.
      destruct t as [ x | f l ]; trivial;
        apply Hterm; apply Hlist; intros t In_t; apply IHn;
          apply lt_n_Sm_le;
          apply lt_le_trans with (size (Term f l)); trivial;
            apply size_direct_subterm; trivial.
    Qed.
  End Recursion.

  (** ** Double recursion on terms. *)
  Section DoubleRecursion.
    Variable P2 : term -> term -> Type.
    Variable Pl2 : list term -> list term -> Type.

    Definition term_rec7 :
      (forall v1 t2, P2 (Var v1) t2) ->
      (forall t1 v2, P2 t1 (Var v2)) ->
      (forall f1 f2 l1 l2, Pl2 l1 l2 -> P2 (Term f1 l1) (Term f2 l2)) ->
      (forall l1 l2, (forall t1 t2, In t1 l1 -> In t2 l2 -> P2 t1 t2) -> Pl2 l1 l2) ->
      forall t1 t2, P2 t1 t2.
    Proof.
      intros Hvt Htv Hterm Hlist.
      intro t1; pattern t1; apply term_rec2; induction n; clear t1;
        intros t1 Size_t1.
      absurd (1<=0); auto with arith;
        apply le_trans with (size t1); trivial; apply size_ge_one.
      destruct t1 as [ x1 | f1 l1 ]; trivial. 
      destruct t2 as [ x2 | f2 l2 ]; trivial.
      apply Hterm; apply Hlist; intros t1 t2 In_t1 In_t2; apply IHn;
        apply lt_n_Sm_le;
        apply lt_le_trans with (size (Term f1 l1)); trivial;
          apply size_direct_subterm; trivial.
    Qed.

    Definition term_rec8 :
      (forall v1 t2, P2 (Var v1) t2) ->
      (forall t1 v2, P2 t1 (Var v2)) ->
      (forall f1 f2 l1 l2, Pl2 l1 l2 -> P2 (Term f1 l1) (Term f2 l2)) ->
      (forall l1 l2, (forall t1 t2, In t1 l1 -> In t2 l2 -> P2 t1 t2) -> Pl2 l1 l2) ->
      forall l1 l2, Pl2 l1 l2.
    Proof.
      intros Hvt Htv Hterm Hlist l1 l2;
        apply Hlist;
        intros; apply term_rec7; trivial.
    Defined.
  End DoubleRecursion.

  (** ** Equality on terms is decidable. *)
  Theorem eq_term_dec : 
    forall t1 t2:term, {t1 = t2} + {t1 <> t2}.
  Proof.
    intro t1; pattern t1; apply term_rec3.
    intro x1; destruct t2 as [ x2 | f2 l2].
    destruct (eq_variable_dec x1 x2) as  [x1_eq_x2 | x1_diff_x2].
    left; subst; trivial.
    right; intro H; apply x1_diff_x2; inversion H; trivial.
    right; discriminate.
    intros f1 l1 Hrec t2; destruct t2 as [x2 | f2 l2].
    right; discriminate.
    destruct (eq_symbol_dec f1 f2) as  [f1_eq_f2 | f1_diff_f2].

    subst; assert (Hrec_list : forall l2, {l1 = l2} + {l1 <> l2}).
    clear f2 l2; induction l1 as [ | a1 l1].
    intro l2; destruct l2 as [ | a2 l2]; [left; trivial | right; discriminate].
    intro l2; destruct l2 as [ | a2 l2].
    right; discriminate.
    assert (In_a1 : In a1 (a1 :: l1)). left; trivial.
    destruct (Hrec a1 In_a1 a2) as  [a1_eq_a2 | a1_diff_a2].
    assert (Hrec_l1 : forall t, In t l1 -> forall t2, {t = t2} + {t <> t2}).
    intros; apply Hrec; right; trivial.
    subst; destruct (IHl1 Hrec_l1 l2) as  [l1_eq_l2 | l1_diff_l2];
      [ left; subst
      | right; intro H; apply l1_diff_l2; inversion H] ; trivial.
    right; intro H; apply a1_diff_a2; inversion H; trivial.

    destruct (Hrec_list l2) as  [l1_eq_l2 | l1_diff_l2];
      [ left; subst
      | right; intro H; apply l1_diff_l2; inversion H] ; trivial.
    right; intro H; apply f1_diff_f2; inversion H; trivial.
  Qed.

  Module Term_eq_dec : decidable_set.S with Definition A:= term 
    with Definition eq_A_dec := eq_term_dec.
    Definition A := term.
    Definition eq_A_dec := eq_term_dec.
  End Term_eq_dec.

  (** ** Well-formedness of terms, according to the arity. *)
  Fixpoint well_formed (t:term) : Prop :=
    match t with
    | Var _ => True
    | Term f l =>
      let well_formed_list :=
          (fix well_formed_list (l:list term) : Prop :=
             match l with
             | nil => True
             | h :: tl => well_formed h /\ well_formed_list tl
             end) in
      well_formed_list l /\
      (match arity f with
       | Free n => length l = n 
       | _ => length l = 2
       end)
    end.

  Lemma well_formed_unfold :
    forall t, well_formed t ->
              match t with 
              | Var _ => True
              | Term f l =>
                (forall u, In u l -> well_formed u) /\
                (match arity f with
                 | Free n => length l = n
                 | _ => length l = 2
                 end)
              end.
  Proof.
    intros t; destruct t as [ x | f l ]; trivial.
    intros [Wl A]; split; trivial.
    clear A; induction l as [ | t l].
    contradiction.
    generalize Wl; clear Wl; intros [Wa Wl] u [Eq_u_a | In_u].
    subst u; trivial.
    apply IHl; trivial.
  Qed.

  Lemma well_formed_fold :
    forall t,
      match t with 
      | Var _ => True
      | Term f l =>
        (forall u, In u l -> well_formed u) /\
        (match arity f with
         | Free n => length l = n
         | _ => length l = 2
         end)
      end -> well_formed t.
  Proof.
    intros t; destruct t as [ x | f l ]; trivial.
    intros [Wl A]; split ; trivial; clear A; induction l as [ | t l]; trivial; split.
    apply Wl; left; trivial.
    apply IHl; intros; apply Wl; right; trivial.
  Qed.

  Fixpoint well_formed_list (l : list term) : Prop :=
    match l with
    | nil => True
    | h :: tl => well_formed h /\ well_formed_list tl
    end.

  (** ** Substitutions. *)
  Definition substitution := list (variable * term).

  Fixpoint apply_subst (sigma : substitution) (t : term) {struct t} : term :=
    match t with
    | Var v => 
      match find eq_variable_dec v sigma with
      | None => t
      | Some v_sigma => v_sigma
      end
    | Term f l => Term f (map (apply_subst sigma) l)
    end.

  Lemma empty_subst_is_id : forall t, apply_subst nil t = t.
  Proof.
    intro t; pattern t; apply term_rec3; clear t; trivial.
    intros f l IH; simpl; apply (f_equal (fun l => Term f l));
      induction l as [ | t l]; trivial; simpl; rewrite (IH t).
    rewrite IHl; trivial.
    intros; apply IH; right; trivial.
    left; trivial.
  Qed.

  Lemma empty_subst_is_id_list : forall l, map (apply_subst nil) l = l.
  Proof.
    intro l; induction l as [ | t l]; simpl; 
      [idtac | rewrite empty_subst_is_id; rewrite IHl];
      trivial.
  Qed.

  (** Composition of substitutions. *)
  Definition map_subst (f : variable -> term -> term) sigma :=
    map (fun x =>
           match (x : variable * term) with
           | (v, v_sigma) => (v, f v v_sigma)
           end)
        sigma.

  Definition subst_comp sigma1 sigma2 :=
    (map_subst (fun _ t => apply_subst sigma1 t) sigma2)
      ++ 
      (map_subst (fun v t =>
                    match find eq_variable_dec v sigma2 with
                    | None => t
                    | Some v_sigma2 => apply_subst sigma1 v_sigma2
                    end)
                 sigma1).

  Lemma subst_comp_is_subst_comp_aux1 :
    forall v sigma f,
      find eq_variable_dec v (map_subst f sigma) =
      match find eq_variable_dec v sigma with
      | None => None
      | Some t => Some (f v t)
      end.
  Proof.
    intros v sigma f; induction sigma as [ | [v1 a1] sigma ].
    simpl; trivial.
    simpl; elim (eq_variable_dec v v1); intro v_eq_v1; trivial;
      subst v; trivial.
  Qed.

  Lemma subst_comp_is_subst_comp_aux2 :
    forall v sigma1 sigma2,
      find (B:= term) eq_variable_dec v (sigma1 ++ sigma2)  =
      match find eq_variable_dec v sigma1 with
      | Some _ => find eq_variable_dec v sigma1
      | None => find eq_variable_dec v sigma2
      end.
  Proof.
    intros v sigma1 sigma2; 
      induction sigma1 as [ | [v1 a1] sigma1] ; trivial.
    simpl; elim (eq_variable_dec v v1); intro v_eq_v1; trivial.
  Qed.

  Theorem subst_comp_is_subst_comp :
    forall sigma1 sigma2 t,
      apply_subst (subst_comp sigma1 sigma2) t =
      apply_subst sigma1 (apply_subst sigma2 t).
  Proof.
    intros sigma1 sigma2 t; pattern t; apply term_rec3; clear t.
    intro v; unfold subst_comp;
      simpl; rewrite subst_comp_is_subst_comp_aux2;
        do 2 rewrite subst_comp_is_subst_comp_aux1;
        destruct (find eq_variable_dec v sigma2); trivial; simpl;
          destruct (find eq_variable_dec v sigma1); trivial.
    intros f l IH; simpl; apply (f_equal (fun l => Term f l));
      induction l as [ | a l]; trivial.
    simpl; rewrite (IH a).
    rewrite IHl; trivial.
    intros; apply IH; right; trivial.
    left; trivial.
  Qed.

  (** Well-formed substitutions. *)
  Definition well_formed_subst sigma :=
    forall v, match find eq_variable_dec v sigma with
              | None => True
              | Some t => well_formed t 
              end.

  Theorem well_formed_apply_subst :
    forall sigma, well_formed_subst sigma -> 
                  forall t, well_formed t -> well_formed (apply_subst sigma t).
  Proof.
    intros sigma W_sigma t; pattern t; 
      apply term_rec3.
    intros v _; simpl; generalize (W_sigma v); 
      destruct (find eq_variable_dec v sigma); trivial.
    intros f l Hrec [Wl A]; split.
    clear A; induction l as [ | a l]; simpl; trivial;
      inversion_clear Wl as [Wa Wl']; split.
    apply Hrec; trivial; left; trivial.
    apply IHl; trivial; intros; apply Hrec; trivial; right; trivial.
    rewrite length_map; trivial.
  Qed.

  (** ** Positions in a term.*)
  Fixpoint is_a_pos (t : term) (p : list nat) {struct p}: bool :=
    match p with
    | nil => true
    | i :: q =>
      match t with
      | Var _ => false
      | Term _ l => 
        match nth_error l i with
        | Some ti => is_a_pos ti q
        | None => false
        end
      end
    end.

  Fixpoint subterm_at_pos (t : term) (p : list nat) {struct p}: option term :=
    match p with
    | nil => Some t
    | i :: q =>
      match t with
      | Var _ => None
      | Term _ l => 
        match nth_error l i with
        | Some ti => subterm_at_pos ti q
        | None => None
        end
      end
    end.

  Lemma size_subterm_at_pos :
    forall t i p, match subterm_at_pos t (i :: p) with
	          | Some u => size u < size t
	          | None => True
	          end.
  Proof.
    intros t i p; generalize t i; clear t i; induction p as [ | j p].
    intros [ v | f l ] j; simpl subterm_at_pos; cbv iota beta; trivial.
    generalize (nth_error_ok_in j l); destruct (nth_error l j) as [tj | ]; [idtac | trivial].
    intro H; apply size_direct_subterm; simpl; apply H; trivial.
    intros [ v | f l ] i; simpl subterm_at_pos; cbv iota beta; trivial.
    generalize (nth_error_ok_in i l); destruct (nth_error l i) as [ti | ]; [idtac | trivial].
    intro ti_in_l; generalize (IHp ti j); simpl subterm_at_pos; 
      destruct ti as [vi | fi li]; trivial.
    generalize (nth_error_ok_in j li); destruct (nth_error li j) as [tij | ]; [idtac | trivial].
    intro tij_in_li; destruct (subterm_at_pos tij p) as [ u | ]; trivial.
    intro H; apply lt_trans with (size (Term fi li)); trivial.
    apply size_direct_subterm; simpl; apply ti_in_l; trivial.
  Qed.

  Lemma is_a_pos_exists_subtem :
    forall t p, is_a_pos t p = true -> exists u, subterm_at_pos t p = Some u.
  Proof.
    intros t p; generalize t; clear t; induction p as [ | i q ].
    intros t _; exists t; trivial.
    intros t; destruct t as [ x | f l ]; simpl.
    intros; discriminate.
    destruct (nth_error l i) as [ ti | ].
    intro; apply IHq; trivial.
    intros; discriminate.
  Qed.

  Fixpoint replace_at_pos (t u : term) (p : list nat) {struct p} : term :=
    match p with
    | nil => u
    | i :: q =>
      match t with
      | Var _ => t
      | Term f l =>
        let replace_at_pos_list :=
            (fix replace_at_pos_list j (l : list term) {struct l}: list term :=
               match l with
               | nil => nil
               | h :: tl =>
                 match j with
                 | O => (replace_at_pos h u q) :: tl
                 | S k => h :: (replace_at_pos_list k tl)
                 end
               end) in
        Term f (replace_at_pos_list i l)
      end
    end.

  Fixpoint replace_at_pos_list (l : list term) (u : term) (i : nat) (p : list nat) 
           {struct l}: list term :=
    match l with
    | nil => nil
    | h :: tl =>
      match i with
      | O => (replace_at_pos h u p) :: tl
      | S j => h :: (replace_at_pos_list tl  u j p)
      end
    end.

  Lemma replace_at_pos_unfold :
    forall f l u i q,
      replace_at_pos (Term f l) u (i :: q) = Term f (replace_at_pos_list l u i q).
  Proof.
    intros f l u i q; simpl; apply (f_equal (fun l => Term f l)); 
      generalize u i q; clear u i q; 
        induction l as [| t l]; intros u i q; trivial.
    simpl; destruct i as [ | i ]; trivial.
    rewrite <- IHl; trivial.
  Qed.

  Lemma replace_at_pos_is_replace_at_pos1 :
    forall t u p, is_a_pos t p = true ->
                  subterm_at_pos (replace_at_pos t u p) p = Some u.
  Proof.
    intro t; pattern t; apply term_rec3; clear t.
    intros x u p; destruct p as [ | i q ]; trivial;
      intros; discriminate.
    intros f l IHl u p; destruct p as [ | i q ]; trivial.
    rewrite replace_at_pos_unfold; simpl; generalize i q; clear i q; 
      induction l as [ | t l ]; intros i q.
    destruct i as [ | i ]; simpl; intros; discriminate.
    destruct i as [ | i ]; simpl.
    intros; apply (IHl t); trivial; left; trivial.
    intros; apply IHl0; intros; trivial; apply IHl; trivial; right; trivial.
  Qed.


  Lemma replace_at_pos_is_replace_at_pos2 :
    forall t p u, subterm_at_pos t p = Some u -> replace_at_pos t u p = t. 
  Proof.
    intro t; pattern t; apply term_rec3; clear t.
    intros v p u; destruct p as [ | i q ]; intro H; inversion_clear H; trivial.
    intros f l IHl p; destruct p as [ | i q ]. 
    intros u H; inversion_clear H; trivial.
    intros u H; rewrite replace_at_pos_unfold; 
      apply (f_equal (fun l => Term f l)); generalize i q u H; clear i q u H;
        induction l as [ | t l ]; intros i q u H.
    destruct i as [ | i ]; simpl; intros; discriminate.
    destruct i as [ | i ]; simpl.
    rewrite IHl; trivial; left; trivial.
    rewrite IHl0; trivial; intros; apply IHl; trivial; right; trivial.
  Qed.

  Lemma subterm_at_pos_apply_subst_apply_subst_subterm_at_pos :
    forall t p sigma, 
      match subterm_at_pos t p with
      | Some u =>
        subterm_at_pos (apply_subst sigma t) p = Some (apply_subst sigma u)
      | None => True
      end.
  Proof.
    intro t; pattern t; apply term_rec3; clear t.
    intros v p; destruct p as [ | i q ]; simpl; trivial.
    intros f l IHl p; destruct p as [ | i q ]; simpl; trivial.
    assert (H : forall (l : list term) i, 
               match nth_error l i with
               | Some li => In li l
               | None => True end).
    clear IHl l i; intro l;
      induction l as [ | t l ]; intro i; destruct i as [ | i ]; simpl; trivial.
    left; trivial.
    generalize (IHl i); destruct (nth_error l i); trivial; intros; right; trivial.
    generalize i; clear i; induction l as [ | l ll ]; 
      intros i; destruct i as [ | i ]; simpl; trivial.
    intros; apply IHl; left; trivial.
    intro sigma; apply IHll; intros; apply IHl; right; trivial.
  Qed.

  Lemma replace_at_pos_list_replace_at_pos_in_subterm :
    forall l1 ui l2 u i p, length l1 = i ->
                           replace_at_pos_list (l1 ++ ui :: l2) u i p = 
                           l1 ++ (replace_at_pos ui u p) :: l2.
  Proof.
    intros l1; induction l1 as [ | u1 l1 ]; intros ui l2 u i p L; simpl in L.
    subst i; trivial.
    destruct i as [ | i ].
    discriminate.
    simpl; rewrite IHl1; trivial.
    inversion L; trivial.
  Qed.

End Make.

