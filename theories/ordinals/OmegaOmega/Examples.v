From Coq Require Import  Arith.
From Coq Require Import List.
From hydras.ordinals Require Import ListOmega.

(** TO do : verify (and prove !) the following examples 
    really need omega^omega (and not a finite power of omega) 

    translate the comments into english  and make them coqdoc compatible

*)

(** To do : make it generic (any ordinal notation) *)

(* Utilitaire pour la définition des ordres *)

Definition make_mwlt (A:Set) (m : A -> t) (a1 a2:A) :=
  (wlt (m a1) (m a2)).
 
(** Un ordre basé sur une mesure ordinale est bien fondé *)
Lemma Acc_wlt_eq : 
  forall (A:Set) (m: A -> t) (w:t) (x:A) , 
    w = (m x) -> (Acc (fun x1 x2 : A => wlt (m x1) (m x2)) x).
induction w using wlt_wf_ind. intros. apply Acc_intro. intros.
  apply H with (w2:=(m y)).
    rewrite H0. assumption.    
    trivial.
Qed.

Lemma Acc_mwlt : forall (A:Set) (m: A -> t),
  forall (x:A), (Acc (fun x1 x2 => (wlt (m x1) (m x2))) x).
intros. apply Acc_wlt_eq with (w:=(m x)). trivial.
Qed.

(**
  Applications avec Program Fixpoint
*)
Require Coq.Program.Wf.

(* Tactique pour les preuves de bonne fondation. *)
Ltac by_Acc_mwlt mwlt := 
  unfold Wf.MR; unfold well_founded; intros; unfold mwlt; apply Acc_mwlt.


(** This example is more adapted to omega^2  *)

(* Ordre lexicographique sur les entiers *)
Definition wm_natxnat (xy:nat*nat) :=
  match xy with
    (x,y) => (cons x (cons y nil))
  end.

Definition lex_natxnat :=
  (make_mwlt (nat*nat) wm_natxnat).

Lemma lex_natxnat_fst : forall (x1 y1 x2 y2:nat),
  (lt x1 x2) -> (lex_natxnat (x1,y1) (x2,y2)).
intros. unfold lex_natxnat. unfold make_mwlt. simpl.
apply wlt_lt_gen; auto.
Qed.

Lemma lex_natxnat_snd : forall (x y1 y2:nat),
  (lt y1 y2) -> (lex_natxnat (x,y1) (x,y2)). 
intros. unfold lex_natxnat. unfold make_mwlt. simpl.
apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto.
Qed.


(* TO do : use omega*omega ? *)

(* Ordre lexicographique sur les longueurs des listes *)
Definition wm_listxlist (A:Set) (xys: list A * list A) :=
  match xys with
    (xs,ys) => (wm_natxnat (length xs, length ys))
  end.

Definition lex_listxlist (A:Set) :=
  (make_mwlt (list A * list A) (wm_listxlist A)).

Section Ltb.

Variable ltb : nat -> nat -> bool.

Program Fixpoint merge (xys: t * t) {wf (lex_listxlist nat) xys} : t :=
  match xys with
      (nil, ys) => ys
    | (xs, nil) => xs
    | (cons x xs, cons y ys) =>
      if (ltb x y) then (cons x (merge (xs, (cons y ys))))
      else (cons y (merge ((cons x xs), ys)))
  end.

Obligation 1.
unfold lex_listxlist. unfold make_mwlt. simpl. 
apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
unfold lex_listxlist. unfold make_mwlt. simpl. apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto with arith.
Qed.

Obligation 4.
by_Acc_mwlt lex_natxnat.
Defined.

(* Ordre sur les listes d'entiers:
     ordre lexicographique sur la taille et le premier élément *)
Definition m_list (xs:t) :=
  match xs with
      nil => nil
    | (cons x xs) => cons (S (length xs)) (cons x nil)
  end.

Definition lt_list  :=
  (make_mwlt t m_list).
 
Program Fixpoint sum_list (xs:t) {wf lt_list xs} : nat :=
  match xs with
      nil => 0
    | (cons 0 xs) => (sum_list xs)
    | (cons (S x) xs) => S (sum_list (cons x xs))
  end.

Obligation 1.
unfold lt_list. unfold make_mwlt. simpl. destruct xs.
  simpl. apply wlt_nil.
  simpl. apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
unfold lt_list. unfold make_mwlt. simpl. apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto with arith.
Qed.

Obligation 3.
by_Acc_mwlt lex_natxnat.
Defined.

(* Analogue sur les listes de listes *)
Definition m_listlist (A:Set) (xss : list (list A)) :=
  match xss with
      nil => nil
    | (cons xs _) => (cons (length xss) (cons (length xs) nil))
  end.

Definition lt_listlist (A:Set) (xss yss : list (list A)) :=
  (wlt (m_listlist A xss) (m_listlist A yss)).


Variable A:Set.

Program Fixpoint list_concat (xss : list (list A))
        {wf (lt_listlist A) xss} : list A :=
  match xss with
      nil => nil
    | (cons nil xss) => (list_concat xss)
    | (cons (cons x xs) xss) => (cons x (list_concat (cons xs xss)))
  end.

Obligation 1.
unfold lt_listlist. destruct xss.
  simpl. apply wlt_nil.
  simpl. apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
unfold lt_listlist. simpl. apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto with arith.
Qed.

Obligation 3.
by_Acc_mwlt lex_natxnat.
Defined.

(* Sur la longueur des listes *)
Definition mw_list (A:Set) (xs: list A) :=
  (cons (length xs) nil).

Definition lt_len_list (A:Set) :=
  (make_mwlt (list A) (mw_list A)).

Program Fixpoint bubble (xs:t) {wf (lt_len_list nat) xs} : t :=
  match xs with
      nil => nil
    | (cons x nil) => (cons x nil)
    | (cons x1 (cons x2 xs)) =>
      if (ltb x1 x2) then (cons x1 (bubble (cons x2 xs)))
      else (cons x2 (bubble (cons x1 xs)))
  end.

Obligation 1.
unfold lt_len_list. unfold make_mwlt. unfold mw_list. simpl. 
apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
unfold lt_len_list. unfold make_mwlt. unfold mw_list. simpl. 
apply wlt_lt_gen; auto with arith.
Qed.

Obligation 3. 
by_Acc_mwlt lt_len_list.
Defined.

(* Le peigne *)
Inductive btree (A:Set) : Set :=
  Empty : (btree A)
| Node : (btree A) -> A -> (btree A) -> (btree A).

Arguments  Empty {A}.
Arguments Node {A} _ _ _.

Fixpoint btree_size (A:Set) (bt:btree A) :=
  match bt with
      Empty => 0
    | (Node bt1 x bt2) => S ((btree_size A bt1) + (btree_size A bt2))
  end.

Definition m_btree (A:Set) (bt:btree A) :=
  match bt with
      Empty => nil
    | (Node bt1 x bt2) => (btree_size A bt)::(btree_size A bt1)::nil
  end.

Definition lt_btree (A:Set) (bt1 bt2:btree A) :=
  (wlt (m_btree A bt1) (m_btree A bt2)).

Program Fixpoint to_list (bt:btree A)
        {wf (lt_btree A) bt} : list A :=
  match bt with
      Empty => nil
    | (Node Empty x bt) => (cons x (to_list bt))
    | (Node (Node bt1 x1 bt2) x2 bt3) => (to_list (Node bt1 x1 (Node bt2 x2 bt3)))
  end.

Obligation 1.
unfold lt_btree. destruct bt.
  simpl. apply wlt_nil.
  simpl. apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
unfold lt_btree. simpl. rewrite <- plus_Snm_nSm. simpl.
rewrite plus_assoc. apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto with arith.
Qed.

Obligation 3.
by_Acc_mwlt lt_btree.
Defined.

(* Theory *)
Variable g1 : nat -> nat.
Variable g2 : nat -> nat -> nat.
Variable g3 : nat -> nat -> nat.
Variable g4 : nat -> nat -> nat.
Variable g5 : nat -> nat -> nat -> nat.
Variable g6 : nat -> nat -> nat -> nat.
Variable g7 : nat -> nat -> nat -> nat.
Variable h1 : nat -> nat -> nat -> nat.
Variable h2 : nat -> nat -> nat -> nat.
Variable h3 : nat -> nat -> nat -> nat -> nat -> nat.

Definition wm_nat3 (xyz:nat * nat * nat) :=
  match xyz with
      (0, y, 0) => nil
    | (0, y, S z) => (cons (S z) nil)
    | (S x, 0, z) => (cons (S x) (cons 0 nil))
    | (S x, S y, z) => (cons (S x) (cons (S y) nil))
  end.

Definition rlex_nat3 :=
  (make_mwlt (nat * nat * nat) wm_nat3).

Program Fixpoint f (xyz : nat * nat * nat) {wf rlex_nat3 xyz} : nat :=
  match xyz with
      (0, y, 0) => (g1 y)
    | (0, y, S z) => (h1 y z (f (0, (g2 y z), z)))
    | (S x, 0, z) => (h2 x z (f (x, (g3 x z), (g4 x z))))
    | (S x, S y, z) =>
         (h3 x y z (f (x, (g5 x y z), (g6 x y z)))
                   (f (S x, y, (g7 x y z))))
  end.

Lemma rlex_nat3_1 : forall (y z m : nat),
  (rlex_nat3 (0, y, z) (0, m, S z)).
intros. unfold rlex_nat3. unfold make_mwlt. destruct z.
  simpl. apply wlt_nil.
  simpl. apply wlt_lt; auto with arith.
Qed.

Lemma rlex_nat3_2 : forall (x z m1 m2 : nat),
  (rlex_nat3 (x, m1, m2) (S x, 0, z)).
unfold rlex_nat3. unfold make_mwlt. destruct x.
  destruct m2.
    simpl. apply wlt_nil.
    simpl. apply wlt_len; auto with arith.
  intros. destruct m1.
    simpl. apply wlt_lt; auto with arith.
    simpl. apply wlt_lt; auto with arith.
Qed.

Lemma rlex_nat3_3 : forall (x y z m1 m2 : nat),
  (rlex_nat3 (x, m1, m2) (S x, S y, z)).
unfold rlex_nat3. unfold make_mwlt. destruct x.                     
  intros. destruct m2.
    simpl. apply wlt_nil.
    simpl. apply wlt_len; auto with arith.
  intros. destruct m1.
    simpl. apply wlt_lt; auto with arith.
    simpl. apply wlt_lt; auto with arith.
Qed.

Lemma rlex_nat3_4 : forall (x y z m : nat),
  (rlex_nat3 (S x, y, m) (S x, S y, z)).
unfold rlex_nat3. unfold make_mwlt. destruct y.
  intros. simpl. apply wlt_wlt. 
    auto with arith.
    simpl. apply wlt_0_w. apply wlt_nil.
  intros. simpl. apply wlt_wlt.
    auto with arith.
    apply wlt_lt; auto with arith.
Qed.

Obligation 1.
apply rlex_nat3_1. 
Qed.

Obligation 2.
apply rlex_nat3_2.
Qed.

Obligation 3.
apply rlex_nat3_3.
Qed.

Obligation 4.
apply rlex_nat3_4.
Qed.
 
Obligation 5.
by_Acc_mwlt wm_nat3.
Defined.

(* Bootstrap *)


Variable eqb : nat -> nat -> bool.

(** To do : specify this function *)

Program Fixpoint listordi (xsys : t * t)
        {wf (lex_listxlist nat) xsys} : bool :=
  match xsys with
    (_, nil) => false
  | (xs, (cons 0 ys)) => (listordi (xs, ys))
  | (nil, (cons (S y) ys)) => true
  | ((cons 0 xs), (cons (S y) ys)) => (listordi (xs, (cons (S y) ys)))
  | ((cons (S x) xs), (cons (S y) ys)) =>
     (orb (ltb (length xs) (length ys))
	  (andb (eqb (length xs) (length ys))
		(orb (ltb x y) (listordi (xs, ys)))))
  end.

Obligation 1.
unfold lex_listxlist. unfold make_mwlt. simpl.
apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
unfold lex_listxlist. unfold make_mwlt. simpl.
apply wlt_lt_gen; auto with arith.
Qed.

Obligation 3.
unfold lex_listxlist. unfold make_mwlt. simpl.
apply wlt_lt_gen; auto with arith.
Qed.
 
Obligation 4.  
by_Acc_mwlt lex_natxnat.
Defined.


(* Dershowitz/Manna: "counting tips of binary trees" *)

Fixpoint list_btree_size (A:Set) (bts:list (btree A)) : nat :=
  match bts with
      nil => 0
    | (cons bt bts) => (btree_size A bt) + (list_btree_size A bts)
  end.

Definition wm_list_btree (A:Set) (bts:list (btree A)) : t :=
  (list_btree_size A bts)::(length bts)::nil.

Definition lt_list_btree (A:Set) :=
  (make_mwlt (list (btree A)) (wm_list_btree A)).

Program Fixpoint count_tips (bts:(list (btree A))) 
        {wf (lt_list_btree A) bts} : nat :=
  match bts with
      nil => 0
    | (cons Empty bts) => S (count_tips bts)
    | (cons (Node bt1 x bt2) bts) => (count_tips (cons bt1 (cons bt2 bts)))
  end.

Obligation 1.
unfold lt_list_btree. unfold make_mwlt. unfold wm_list_btree. 
simpl. apply wlt_wlt_gen.
  auto.
  apply wlt_lt_gen; auto with arith.
Qed.

Obligation 2.
unfold lt_list_btree. unfold make_mwlt. unfold wm_list_btree.
apply wlt_lt_gen.
  auto.
  simpl. rewrite plus_assoc. auto with arith.
Qed.

Obligation 3.
by_Acc_mwlt lt_list_btree.
Defined.

End Ltb.





