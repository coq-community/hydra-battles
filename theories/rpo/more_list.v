(** by Evelyne Contejean, LRI *)

(** * Some additional properties for the Coq lists. *)

Set Implicit Arguments.

From Coq Require Import List Arith.


(** ** Relations between length, map, append, In and nth. *)

Lemma map_map :
  forall (A B C : Set) (l : (list A)) (f : B -> C) (g : A ->B),
  map f (map g l) = map (fun x => f (g x)) l.
Proof.
intros A B C l f g; induction l as [ | x l].
trivial.
simpl; rewrite IHl; trivial.
Qed.

Lemma list_app_length :
 forall A, forall l1 l2 : list A, length (l1 ++ l2) = length l1 + length l2.
Proof.
induction l1 as [ | a1 l1 ]; trivial.
intros; simpl; rewrite IHl1; trivial.
Qed.

Lemma length_map :
 forall (A B : Set) (f : A -> B) (l : list A), length (map f l) = length l.
Proof.
intros; induction l as [ | a l ]; trivial.
simpl; rewrite IHl; trivial.
Qed.

Lemma map_app :
 forall (A B : Set) (f : A -> B) l1 l2, map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
induction l1 as [ | a1 l1 ]; trivial.
intros; simpl; rewrite IHl1; trivial.
Qed.


Lemma in_in_map :
  forall (A B : Set) (f : A -> B) a l, In a l -> In (f a) (map f l).
Proof.
intros A B f a l; induction l as [ | b l ]; trivial.
intro In_a; elim In_a; clear In_a; intro In_a.
subst; left; trivial.
right; apply IHl; trivial.
Qed.

Lemma in_map_in :
  forall (A B : Set) (f : A -> B) b l, In b (map f l) ->
  exists a, In a l /\ f a = b.
Proof.
intros A B f b l; induction l as [ | a l ].
contradiction.
intro In_b; elim In_b; clear In_b; intro In_b.
exists a; split; trivial; left; trivial.
elim (IHl In_b); intros a' [H1 H2]; exists a'; split; trivial; right; trivial.
Qed.

Lemma nth_error_map :
  forall (A B : Set) (f : A -> B) (l : list A) i,
  match nth_error (map f l) i with
  | Some f_li => 
           match nth_error l i with
            | Some li => f_li = f li
            | None => False
            end
  | None =>
            match nth_error l i with
            | Some li => False
            | None => True
            end
end.
Proof.
induction l as [ | a l ]; 
intro i; destruct i as [ | i ]; simpl; trivial.
apply IHl; trivial.
Qed.

(** ** A measure on lists based on a measure on elements. *)

Fixpoint list_size (A : Set) (size : A -> nat) (l : list A) {struct l} : nat :=
  match l with
  | nil => 0
  | h :: tl => size h + list_size size tl
  end.

Lemma list_size_tl_compat :
  forall (A : Set) (size : A -> nat) a b l, size a < size b -> 
    list_size size (a :: l) < list_size size (b :: l).
Proof.
intros A size a b l H; simpl; apply plus_lt_compat_r; trivial.
Qed.

Lemma list_size_app:
 forall (A : Set) (size : A -> nat) l1 l2,
 list_size size (l1 ++ l2) = list_size size l1 + list_size size l2.  
Proof. 
induction l1 as [ | a1 l1 ]; trivial.
intros; simpl; rewrite IHl1; auto with arith.
Qed.

Lemma list_size_fold :
  forall (A : Set) (size : A -> nat) l n,
  fold_left (fun (size_acc : nat) (a : A) => size_acc + size a) l n =
  n + list_size size l.
Proof.
intros A size l; induction l; trivial.
intro n; simpl; rewrite plus_assoc; apply IHl.
Qed.

Lemma list_size_size_eq :
  forall (A : Set) (size1 : A -> nat) (size2 : A -> nat) l,
 (forall a, In a l -> size1 a = size2 a) -> list_size size1 l = list_size size2 l.
Proof.
intros A size1 size2 l; induction l as [ | a l]; simpl; trivial.
intros size1_eq_size2.
rewrite (size1_eq_size2 a (or_introl _ (refl_equal _))).
apply (f_equal (fun n => size2 a + n)); apply IHl;
intros; apply size1_eq_size2; right; trivial.
Qed.

(** ** Induction principles for list. 
 Induction on the length. *)
Definition list_rec2 :
  forall A, forall P : list A -> Type,
    (forall (n:nat) (l : list A), length l <= n -> P l) -> 
    forall l : list A, P l.
Proof.
intros A P H l; apply (H (length l) l); apply le_n.
Defined.

Definition o_length (A : Set) (l1 l2 : list A) : Prop := length l1 < length l2.

Theorem well_founded_length : forall A, well_founded (o_length (A := A)).
Proof.
intro A; assert (Acc_nil : Acc (o_length (A:=A)) (@nil A)).
apply Acc_intro; intros l H; absurd (o_length l nil); trivial; 
unfold o_length; simpl; auto with arith.

unfold well_founded, o_length; 
intros l; pattern l; apply list_rec2; clear l;
induction n; intro l; destruct l; intros H; trivial.
simpl in H; absurd (S (length l) <= 0); trivial; auto with arith.
apply Acc_intro; intros l' H'; apply IHn;
apply le_trans with (length l);
simpl in H; simpl in H'; auto with arith.
Defined.

(** Induction on the the size. *)
Definition list_rec3 (A : Set) (size : A -> nat) :
  forall P : list A -> Type,
    (forall (n:nat) (l : list A), list_size size l <= n -> P l) -> 
    forall l : list A, P l.
Proof.
intros P H l; apply (H (list_size size l) l); apply le_n.
Defined.

(** ** How to remove an element in a list, whenever it is present. *)
Fixpoint split_list (A : Set)
  (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) 
  (l : list A) (t : A) {struct l} : list A * list A :=
  match l with
  | nil => (nil, nil)
  | a :: l' =>
      if eqA t a
      then (nil, l')
      else let (l1,l2) := split_list eqA l' t in (a :: l1, l2)
  end.

Lemma split_list_app_cons :
 forall (A : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) t l,
   In t l -> let (l1, l2) := split_list eqA l t in l = l1 ++ t :: l2.
Proof.
induction l as [ | a l ].
contradiction.
simpl; elim (eqA t a); intro eq_t_a.
intros _; subst; trivial.
intros [eq_t_a' | In_t].
absurd (t = a); auto.
generalize (IHl In_t); destruct (split_list eqA l t); intro; subst; auto.
Defined.

Fixpoint remove (A : Set) (eqA : forall a1 a2 : A, {a1=a2}+{a1<>a2}) 
  (a : A) (l : list A) {struct l} : (option (list A)) :=
  match l with
  | nil => None 
  | h :: tl =>
    if eqA a h
    then Some tl
    else 
      match remove eqA a tl with
      | Some rmv => Some (h :: rmv)
      | None => None 
      end
  end.

Lemma in_remove :
  forall (A : Set) (eqA : forall a1 a2 : A, {a1=a2}+{a1<>a2}) a l,  
  match remove eqA a l with
  | None => ~In a l
  | Some l' => In a l /\ let (l1, l2) := split_list eqA l a in l' = l1 ++ l2
  end.
Proof.
induction l as [ | a1 l]; simpl; auto;
elim (eqA a a1); intro eq_a_a1; intuition.
destruct (remove eqA a l) as [ rmv |  ]; intuition; 
destruct (split_list eqA l a); subst; auto.
Qed.

Fixpoint remove_list (A : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
(la l : list A) {struct l} : option (list A) :=
  match la with
  | nil => Some l
  | a :: la' => 
	match l with 
	| nil => None
	| b :: l' => 
	   if eqA a b
	   then remove_list eqA la' l'
	   else 
	     match remove_list eqA la l' with
	     | None => None
	     | Some rmv => Some (b :: rmv)
	     end
        end
  end.


(** ** Iterators. *) 
Fixpoint fold_left2 (A B C : Set) (f : A -> B -> C -> A) (a : A) (l1 : list B) (l2 : list C)  
  {struct l1} : option A :=
  match l1, l2 with
  | nil, nil => Some a
  | b :: t1, c :: t2 => fold_left2 f (f a b c) t1 t2
  | _, _ => None
  end.

(** ** more properties on the nth element. *)
Lemma nth_error_ok_in :
  forall (A : Set) n (l : list A) (a : A),
  nth_error l n = Some a -> In a l.
Proof.
intros A n l; generalize n; clear n; induction l as [ | a' l].
intros [ | n] a; simpl; discriminate.
intros [ | n] a; simpl.
intro H; injection H; subst; left; trivial.
intro; right; apply IHl with n; trivial.
Qed.

(** ** Association lists. 
*** find. *)
Fixpoint find (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
(a : A) (l : list (A * B)) {struct l} : option (B) :=
 match l with
 | nil => None
 | (a1,b1) :: l =>
     if eqA a a1
     then Some b1
     else find eqA a l
  end.

Lemma find_not_mem :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
  (a : A) (b : B) (l : list (A * B)) (dom : list A),
  ~In a dom -> (forall a', In a' dom -> find eqA a' ((a,b) :: l) = find eqA a' l).
Proof.
intros A B eqA a b l dom a_not_in_dom a' a'_in_dom; simpl;
destruct (eqA a' a) as [a'_eq_a | a'_diff_a].
subst a'; absurd (In a dom); trivial.
trivial.
Qed.

(** *** number of occurences of the first element of a pair. *)
Fixpoint nb_occ (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
  (a : A) (l : list (A * B)) {struct l} : nat :=
  match l with
  | nil => 0
  | (a',_) :: tl =>
     if (eqA a a') then S (nb_occ eqA a tl) else nb_occ eqA a tl
  end.

Lemma none_nb_occ_O :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
  (a : A) (l : list (A * B)),
  find eqA a l = None -> nb_occ eqA a l = 0.
Proof.
intros A B eqA a l; induction l as [ | [a1 b1] l]; trivial; simpl.
destruct (eqA a a1) as [a_eq_a1 | a_diff_a1]; intros.
discriminate.
apply IHl; trivial.
Qed.

Lemma some_nb_occ_Sn :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
  (a : A) (l : list (A * B)) b,
  find eqA a l = Some b -> 1 <= nb_occ eqA a l.
Proof.
intros A B eqA a l; induction l as [ | [a1 b1] l].
intros; discriminate.
intro b; simpl; destruct (eqA a a1) as [_ | _].
auto with arith.
intros; apply IHl with b; trivial.
Qed.

Lemma nb_occ_app :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2})
  a (l1 l2 : list (A * B)), 
  nb_occ eqA a (l1++l2) = nb_occ eqA a l1 + nb_occ eqA a l2.
Proof.
intros A B eqA a l1; induction l1 as [ | [a1 b1] l1]; simpl; trivial.
intro l2; rewrite IHl1; destruct (eqA a a1) as [_ | _]; trivial.
Qed.

Lemma reduce_assoc_list :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}),
  forall (l : list (A * B)), exists l', 
 (forall a, nb_occ eqA a l' <= 1) /\ (forall a, find eqA a l = find eqA a l').
Proof.
intros A B eqA l; induction l as [ | [a1 b1] l].
exists (nil : list (A * B)); split; trivial; auto.
elim IHl; intros l' [H1 H2].
assert (In_a1 : forall a, a = a1 -> find eqA a l' = find eqA a1 l').
intros; subst; trivial.
destruct (find eqA a1 l') as [ b | ]; 
generalize (In_a1 _ (refl_equal _)); clear In_a1; intro In_a1.
assert (In_a1' : exists l1, exists  l2, l' = l1 ++ (a1,b) :: l2).
clear H1 H2; induction l' as [ | [a' b'] l'].
discriminate.
simpl in In_a1; destruct (eqA a1 a') as [a1_eq_a' | _].
subst; inversion In_a1; exists (nil : list (A * B)); exists l'; simpl; trivial.
elim (IHl' In_a1); intros l1 [l2 H]; 
exists ((a',b') :: l1); exists l2; subst; trivial.
elim In_a1'; intros l1 [l2 H]; exists ((a1,b1) :: l1 ++ l2); split.
intro a; generalize (H1 a); subst l'; rewrite nb_occ_app; 
simpl; destruct (eqA a a1) as [a_eq_a1 | _]; subst; rewrite nb_occ_app;
[ rewrite plus_comm; simpl; rewrite plus_comm | idtac ]; trivial.
intro a; simpl; destruct (eqA a a1) as [a_eq_a1 | a_diff_a1]; trivial.
rewrite H2; subst l'; clear H1 H2 In_a1 In_a1'; 
induction l1 as [ | [a1' b1'] l1]; simpl.
destruct (eqA a a1); trivial; absurd (a = a1); trivial.
rewrite IHl1; trivial.
exists ((a1,b1) :: l'); split; trivial; intro a; simpl.
destruct (eqA a a1) as [a_eq_a1 | a_diff_a1]; trivial.
rewrite none_nb_occ_O; subst; trivial.
rewrite (H2 a); trivial.
Qed.

(** map_without_repetition applies a function to the elements of a list,
but only a single time when there are several consecutive occurences of the
same element. Moreover, the function is supposed to return an option as a result,
in order to simulate exceptions, and the abnormal results are discarted.
 *)

Fixpoint map_without_repetition (A B : Set) 
  (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) 
  (f : A -> option B) (l : list A) {struct l} : list B :=
    match l with
    | nil => (nil : list B)
    | h :: nil => 
      match f h with
      | None => nil
      | Some f_h => f_h :: nil
      end
    | h1 :: ((h2 :: tl) as l1) =>
    if (eqA h1 h2)
    then map_without_repetition eqA f l1
    else 
      match f h1 with
      | None => map_without_repetition eqA f l1
      | Some f_h1 => f_h1 :: (map_without_repetition eqA f l1)
      end
end.

Lemma prop_map_without_repetition :
 forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) 
  (P : B -> Prop) f l,
  (forall a, In a l -> 
   match f a with 
   | None => True 
   | Some f_a => P f_a
   end) ->
   (forall b, In b (map_without_repetition eqA f l) -> P b).
Proof.
induction l as [ | a1 l].
contradiction.
assert (In_a1 : In a1 (a1 :: l)).
left; trivial.
intros H; generalize (H a1 In_a1); simpl; destruct l as [ | a2 l].
destruct (f a1) as [ f_a1 |  ]; simpl; intuition; subst; trivial.
elim (eqA a1 a2); intro eq_a1_a2.
intros; apply IHl; trivial; intros; apply H; right; trivial.
destruct (f a1) as [ f_a1 |  ].
intros P_f_a1 b [eq_f_a1_b | In_b].
subst; apply P_f_a1; left; trivial.
apply IHl; trivial; intros; apply H; right; trivial.
intros; apply IHl; trivial; intros; apply H; right; trivial.
Qed.

Lemma exists_map_without_repetition :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) 
  (P : B -> Prop) f l,
  (exists a,  In a l /\ match f a with 
                        | None => False
                        | Some f_a => P f_a
                        end) ->
  (exists b, In b (map_without_repetition eqA f l) /\ P b).
Proof.
intros A B eqA P f.
assert (In_map_right : forall b a l, 
In b (map_without_repetition eqA f l) ->
In b (map_without_repetition eqA f (a :: l))).
intros b a1 l In_b; simpl; destruct l as [ | a2 l].
contradiction.
elim (eqA a1 a2); trivial;
destruct (f a1) as [ b1 | ]; trivial; intros _; right; trivial.
induction l as [ | a1 l].
intros [a [In_a _]]; contradiction.
intros [a [[Eq_a_a1 | In_a] P_f_a]].
simpl; subst a1; destruct l as [ | a2 l]; intuition.
destruct (f a) as [b | ]; [ exists b; intuition | contradiction ].
elim (eqA a a2).
intro; subst a; apply IHl; exists a2; intuition.
intros _; 
destruct (f a) as [ b | ]; [exists b; intuition | contradiction].
assert (H: exists b : B, In b (map_without_repetition eqA f l) /\ P b).
apply IHl; exists a; intuition.
generalize H; intros [b H_b]; exists b; intuition.
Qed.

(** map12_without_repetition is similar to map_without_repetition, but the 
applied function returns two optional results instead of one.
*)

Fixpoint map12_without_repetition (A B : Set) 
  (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) 
  (f : A -> option B * option B) (l : list A) {struct l} : list B :=
    match l with
    | nil => (nil : list B)
    | h :: nil => 
      match f h with
      | (None, None) => nil
      | (Some f_h1, None) => f_h1 :: nil
      | (None, Some f_h1) => f_h1 :: nil
      | (Some f_h1, Some f_h2) => f_h1 :: f_h2 :: nil
      end
    | h :: ((h' :: tl) as l1) =>
    if (eqA h h')
    then map12_without_repetition eqA f l1
    else 
      match f h with
      | (None, None) => map12_without_repetition eqA f l1
      | (Some f_h1, None) => f_h1 :: (map12_without_repetition eqA f l1)
      | (None, Some f_h1) => f_h1 :: (map12_without_repetition eqA f l1)
      | (Some f_h1, Some f_h2) => f_h2 :: f_h1 :: (map12_without_repetition eqA f l1)
      end
end.

Lemma prop_map12_without_repetition :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) 
  (P : B -> Prop) f l,
  (forall a, In a l -> 
   match f a with 
   | (None, None) => True 
   | (Some f1_a, None) => P f1_a
   | (None, Some f2_a) => P f2_a
   | (Some f1_a, Some f2_a) => P f1_a /\ P f2_a
   end) ->
 (forall b, In b (map12_without_repetition eqA f l) -> P b).
Proof.
intros A B eqA P f; induction l as [ | a1 l].
contradiction.
assert (In_a1 : In a1 (a1 :: l)).
left; trivial.
intros H b; 
assert (Hrec : 
forall b : B, In b (map12_without_repetition eqA f l) -> P b).
intros; apply IHl; trivial; intros; apply H; right; trivial.
clear IHl; simpl; generalize (H a1 In_a1).
destruct l as [ | a2 l].
destruct (f a1) as [o1 o2]; 
destruct o1 as [ f1_a1 | ];
destruct o2 as [ f2_a1 | ];
[ intros [P_f1_a1 P_f2_a1] | intros P_f1_a1 | intros P_f2_a1 | idtac].
intros [Eq_b_f1_a1 | [Eq_b_f2_a1 | In_b]]; subst; trivial; contradiction.
intros [Eq_b_f1_a1 | In_b]; subst; trivial; contradiction.
intros [Eq_b_f2_a1 | In_b]; subst; trivial; contradiction.
contradiction.
elim (eqA a1 a2).
intros; apply Hrec; trivial.
destruct (f a1) as [o1 o2]; 
destruct o1 as [ f1_a1 | ];
destruct o2 as [ f2_a1 | ];
[ intros _ [P_f1_a1 P_f2_a1] 
| intros _ P_f1_a1 | intros _ P_f2_a1 | intros _].
intros [Eq_b_f1_a1 | [Eq_b_f2_a1 | In_b]]; 
subst; trivial; apply Hrec; trivial.
intros [Eq_b_f1_a1 | In_b]; subst; trivial; apply Hrec; trivial.
intros [Eq_b_f2_a1 | In_b]; subst; trivial; apply Hrec; trivial.
intros; apply Hrec; trivial.
Qed.

Lemma exists_map12_without_repetition :
  forall (A B : Set) (eqA : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) 
  (P : B -> Prop) f l,
  ((exists a, In a l /\ match f a with 
                        | (None, None) => False
                        | (None, Some f2_a) => P f2_a
                        | (Some f1_a, None) => P f1_a
                        | (Some f1_a, Some f2_a) => P f1_a \/ P f2_a
                        end) ->
  (exists b, In b (map12_without_repetition eqA f l) /\ P b)).
Proof.
intros A B eqA P f; induction l as [ | a1 l].
intros [a [In_a _]]; contradiction.
destruct l as [ | a2 l].
intros [a [[Eq_a_a1 | In_a] P_f_a]]; simpl.
subst a; destruct (f a1) as [o1 o2];
destruct o1 as [f1_a1 | ];
destruct o2 as [f2_a1 | ].
generalize P_f_a; clear P_f_a; intros [P_f1_a1 | P_f2_a1].
exists f1_a1; intuition.
exists f2_a1; intuition.
exists f1_a1; intuition.
exists f2_a1; intuition.
contradiction.
contradiction.
intros [a [[Eq_a_a1 | In_a] P_f_a]].
subst a; simpl; elim (eqA a1 a2).
intro; subst a1; apply IHl; exists a2; intuition.
destruct (f a1) as [o1 o2];
destruct o1 as [f1_a1 | ];
destruct o2 as [f2_a1 | ].
generalize P_f_a; clear P_f_a; intros [P_f1_a1 | P_f2_a1].
exists f1_a1; intuition.
exists f2_a1; intuition.
exists f1_a1; intuition.
exists f2_a1; intuition.
contradiction.
assert (Hrec : exists b : B, 
In b (map12_without_repetition eqA f (a2 :: l)) /\ P b).
apply IHl; exists a; split; trivial.
generalize Hrec; intros [b [In_b P_b]]; exists b; split; trivial.
simpl; elim (eqA a1 a2).
intro; subst a1; trivial.
intros _; destruct (f a1) as [o1 o2];
destruct o1 as [P_f1_a1 | ];
destruct o2 as [P_f2_a1 | ].
right; right; trivial.
right; trivial.
right; trivial.
trivial.
Qed.
