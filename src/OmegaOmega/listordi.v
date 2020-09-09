(** An implementation of [omega ^ omega]
    Pascal Manoury et al. *)

(** Proof bulletization by Pierre Casteran (in progress) *)


Require Import Arith.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Require Import List.
Require Import Recdef Lia.
Require Import  Coq.Wellfounded.Inverse_Image Coq.Wellfounded.Inclusion.

(**
  Arithmetic ( should be moved elsewhere) 
*)

Lemma minus_Sn_n : forall (n:nat), S n - n = 1.
Proof. lia. Qed.



Lemma minus_lt_S : forall (n1 n2:nat),
    (lt n1 n2) -> exists (n:nat), (minus n2 n1) = (S n).
Proof.
  destruct n2.
  - lia.
  - exists (n2 - n1); lia.
 Qed.


(**
  Sur les listes
*)

(* Sur la longueur. *)
Lemma length_0_nil : forall w:list nat, length w =0 -> w=nil.
destruct w.
 - trivial.
 - intro; discriminate.
Qed.

Lemma length_Sn_cons : forall (w:list nat) (n:nat),
  length w=S n -> exists (a:nat) (w':(list nat)), w = (cons a w').
Proof.
  destruct w as [| p w].
 - intros; discriminate.
 - intros; now exists p, w. 
Qed.

Definition t := list nat.

Declare Scope oo_scope.
Delimit Scope oo_scope with oo.
Open Scope oo_scope.

Notation  "'omega'" := (1::0::nil) : oo_scope.
Definition fin (i:nat) : t := (i::nil).

Coercion fin : nat >-> t.

Check (1::0::nil).

Check (fin 42).


(* Induction on list length  *)
Lemma list_length_ind_S :
  forall P : t -> Prop,
    P nil ->
    (forall n : nat,
        (forall xs : t, length xs < S n -> P xs) ->
        forall xs : t, length xs = S n -> P xs) ->
    forall (n : nat) (xs : t), length xs < S n -> P xs.
Proof.
  intros P P0 Plt; induction n.
  - intros; assert (H0: xs=nil).
    { apply length_0_nil, Nat.lt_1_r; assumption. }
    now rewrite H0.
  -  intros xs H;  assert ( length xs <= (S n)). {
       destruct (lt_n_Sm_le (length xs) (S n) H); auto. }
     destruct (le_lt_or_eq _ _ H0);eauto.
Qed.

Lemma list_length_ind :
  forall P : t -> Prop,
    P nil ->
    (forall n : nat,
        (forall xs : t, length xs < S n -> P xs) ->
        forall xs : t, length xs = S n -> P xs) ->
    forall xs : t, P xs.
Proof.
  intros; apply list_length_ind_S with (n:=(length xs)); auto with arith.
Qed.

(** list of zeroes *)

Definition zeroes (n:nat) : t := repeat 0 n.


Definition dist (w1:t) (w2:t) :=
  length w1 - length w2.

Definition padd (w1:t) (w2:t) :=
  zeroes (dist w2 w1) ++  w1.


Lemma padd_len_lt_cons :
forall w1 w2 : t,
  length w1 < length w2 -> exists w : t, padd w1 w2 = 0 :: w.
Proof.
  intros w1 w2 H; unfold padd, dist. 
  destruct (minus_lt_S (length w1) (length w2) H) as [x Hx].
  rewrite Hx; cbn;  now exists (zeroes x ++ w1). 
Qed.


Lemma padd_len_le_len : forall (w1 w2:t),
  length w1 <= length w2 ->
  length (padd w1 w2) = length w2.
Proof.
  intros w1 w2 H; unfold padd, dist, zeroes;
    rewrite app_length, repeat_length; lia.  
Qed.

Lemma padd_cons_0 : forall (w1 w2:t) (a:nat),
  length w1 = length w2 -> padd w1 (cons a w2) =  0 :: w1.
Proof.
  intros. unfold padd, dist; rewrite H. simpl length.
  rewrite (minus_Sn_n (length w2)); reflexivity.  
Qed.

(**
  On accessibility 
  Tribute to P. Casteran: 
      http://www.labri.fr/perso/casteran/Cantor/HTML/AccP.html#AccElim3
*)
Theorem AccElim2 :
  forall (A B : Type) (RA : A -> A -> Prop) (RB : B -> B -> Prop)
    (P : A -> B -> Prop),
  (forall (x : A) (y : B),
   (forall t : A, RA t x -> forall y' : B, Acc RB y' -> P t y') ->
   (forall t : B, RB t y -> P x t) -> P x y) ->
  forall (x : A) (y : B), Acc RA x -> Acc RB y -> P x y.
Proof.
 intros A B RA RB P H x y Ax; generalize y; clear y.
 elim Ax; clear Ax x; intros x HAccx Hrecx y Ay.
 elim Ay; clear Ay y; intros y HAccy Hrecy; apply H; auto.
Qed.

(**
  Order on restricted Cantor normal forms (with finite exponents)
 *)


Inductive wlt : t -> t -> Prop :=
  wlt_nil : forall (a:nat)(w:t), (wlt nil (cons (S a) w))
| wlt_0_w : forall (w1 w2:t), (wlt w1 w2) -> (wlt (cons 0 w1) w2)
| wlt_w_0 : forall (w1 w2:t), (wlt w1 w2) -> (wlt w1 (cons 0 w2))
| wlt_len : forall (w1 w2:t) (a1 a2:nat),
   (length w1 < length w2) -> (wlt (cons (S a1) w1) (cons (S a2) w2))
| wlt_lt :  forall (w1 w2:t) (a1 a2:nat),
  (length w1 = length w2) -> (lt a1 a2) 
    -> (wlt (cons (S a1) w1) (cons (S a2) w2))
| wlt_wlt : forall (w1 w2:t) (a:nat),
  (length w1 = length w2) ->  (wlt w1 w2) 
    -> (wlt (cons (S a) w1) (cons (S a) w2)).


Lemma not_wlt_nil : forall w:t,  ~ wlt w nil.
Proof.
induction w as [ | a w H].
 - red; inversion 1.
 -  intro.  inversion H0; auto.
Qed.

(**  Inversion lemmas *)

Lemma wlt_0_w_inv: forall (w1 w2:t),
  wlt (cons 0 w1) w2 -> wlt w1 w2.
Proof.
  induction w2.
  - intros H; absurd (wlt (cons 0 w1) nil).
   +  apply (not_wlt_nil (cons 0 w1));  assumption.
   +  inversion H; assumption.
  -    inversion 1. auto.
       apply wlt_w_0; auto.
Qed.

Lemma wlt_w_0_inv: forall (w1 w2: t),
  wlt w1 (cons 0 w2) -> (wlt w1 w2).
Proof.
  induction w1.
  - intros w2 H; now inversion H. 
  - intros w2 H; inversion H. 
    + apply wlt_0_w;  auto.
    + assumption.
Qed.


Lemma not_wlt_len_left : forall (w1 w2:t) (a:nat),
  length w2 <= length w1 -> ~ wlt (cons (S a) w1) w2.
Proof.
  induction w2.
   - intros; apply not_wlt_nil.
   - intros; destruct a.
    + intro; absurd (wlt (cons (S a0) w1) w2).
     * apply IHw2. 
        apply le_trans with (m:=(length (cons 0 w2))).
         --  auto with arith.
         --  assumption.
     *  apply wlt_w_0_inv; assumption.
    + intro H0; inversion H0.
      assert (length (S a :: w2) < length w2).
       { apply le_lt_trans with (m := (length w1)); assumption. }
       apply (Nat.nlt_succ_diag_l (length w2)); assumption.      
       rewrite H4 in H; apply (Nat.nle_succ_diag_l (length w2)); assumption.
       rewrite H4 in H; apply (Nat.nle_succ_diag_l (length w2)); assumption.
Qed.

Lemma not_wlt_Sn_0 : forall (w1 w2:t) (a:nat),
  length w1 = length w2 ->  ~ wlt (cons (S a) w1) (cons 0 w2).
Proof.
  intros w1 w2 a H H0; inversion H0. 
  apply (not_wlt_len_left w1 w2 a). 
  - rewrite H; auto with arith.
  -  now apply wlt_w_0_inv. 
Qed.

Lemma not_wlt_len: forall (w1 w2:t) (a:nat),
    length w2 <= length w1  -> ~ wlt (cons (S a) w1) w2.
Proof.
  induction w2.
  -  intros a _ H;  now apply (not_wlt_nil (cons (S a) w1)). 
  -  intro a0; case a.
   +  intros H H0; apply IHw2 with (a:=a0).
     * apply le_trans with (m:=(length (cons 0 w2))); auto.
        cbn; auto with arith.
     * apply wlt_w_0_inv.
       -- assumption.
   +    intros n H H0; inversion H0.
        apply (lt_irrefl (length w1)).
        simpl in H; apply lt_trans with (m:=(length w2)); assumption.
        rewrite H4 in H; apply (le_Sn_n (length w2)); assumption.
        rewrite H4 in H; apply (le_Sn_n (length w2)); assumption.
Qed. 


Lemma wlt_wlt_zeroes_right : forall (n:nat) (w1 w2:t),
  wlt w1 w2 -> wlt w1 (app (zeroes n) w2).
Proof.
  induction n.
  -  auto.
  - intros; cbn;  now apply wlt_w_0, IHn. 
Qed.




Lemma wlt_zeroes_wlt_right : forall (n:nat) (w1 w2:t),
  wlt w1 (zeroes n ++  w2) -> wlt w1 w2.
Proof.
  induction n; auto.
  - cbn; intros; now apply IHn, wlt_w_0_inv. 
Qed.

Lemma wlt_wlt_zeroes_left : forall (n:nat) (w1 w2:t),
    (wlt w1 w2) -> (wlt (app (repeat 0 n) w1) (w2)).
Proof. 
  induction n; auto.
  intros; cbn; apply wlt_0_w; auto.
Qed.     

(* Caractérisation en fonction de la longueur:
   si '(wlt w1 w2)' et '#w2 < #w1' alors 'w1' commence par des 0 *)

Lemma wlt_gt_length : forall (w1 w2:t),
    wlt w1 w2 -> lt (length w2) (length w1)
    -> exists (n:nat) (w:t),
        w1 = zeroes n ++  w /\ length w = length w2  /\ wlt w w2.
Proof.
  induction w1 as [| a w1 IHw1].
  - intros; exfalso; apply (lt_n_0 (length w2)); auto.
  - intros w2 H H0; cbn in H0.  assert (H1: length w2 <= length w1).
    { apply lt_n_Sm_le; assumption. }
    +  destruct a as [| a].
       *  elim (le_lt_or_eq (length w2) (length w1) H1).
          --  intro H2; elim IHw1 with (w2:=w2).
              ++ intros z H3; elim H3; intros w1' H4; decompose [and] H4.
                               exists (S z), w1'; split.
                               subst; trivial.
                               tauto.
              ++  apply wlt_0_w_inv; assumption. 
              ++  assumption.
          -- exists 1, w1.  split.
          ++  trivial.
          ++   split. 
               ** now symmetry.
               **   now apply wlt_0_w_inv. 
       *  exfalso;  apply (not_wlt_len w1 w2 a); assumption.
Qed.


(**
   Restriction de l'ordre aux listes de même longueur.
   (avec complémentation possible à 0): 
   c'est l'ordre lexicographique.
*)
(* La relation sur les listes de même longueur *)


Inductive wlt_pad : t -> t -> Prop :=
  wlt_pad_len : forall (a:nat) (w1 w2: t),
    length w1 <= length w2 ->
     wlt_pad (padd  w1 (S a :: w2)) (S a :: w2)
| wlt_pad_lt : forall (a1 a2:nat) (w1 w2:t),
    length w1 = length w2 -> a1 < a2 ->
     wlt_pad (S a1 :: w1) (S a2 :: w2)
| wlt_pad_wlt_pad : forall (a:nat) (w1 w2: t),
    length w1 = length w2 -> wlt_pad w1 w2 ->
     wlt_pad (a :: w1) (a :: w2).

(* Relations entre l'ordre sur toute liste et l'ordre restreint. *)

Lemma wlt_wlt_pad : forall (w1 w2:t),
    length w1 = length w2 -> wlt w1 w2 -> wlt_pad w1 w2.
Proof.
  intros w1 w2 ; generalize w1; clear w1;  induction w2.
  -  intros w1 H H0; exfalso; now apply (not_wlt_nil w1). 
  - destruct w1.
   + intro; discriminate. 
   + intros H H0; inversion H0.
    (* 1: wlt_0_w *)
    *  destruct a.
     --  apply wlt_pad_wlt_pad.
         ++ auto.
         ++ apply IHw2.
          **  auto.
          ** now  apply wlt_w_0_inv. 
      -- rewrite <- (padd_cons_0 w1 w2 a). 
       ++ apply wlt_pad_len; injection H. intro H5;rewrite H5; auto with arith.
       ++ auto.
    (* 2: wlt_w_0 *)
    * destruct n.    
      --  apply wlt_pad_wlt_pad.
          ++ auto with arith.
          ++ apply IHw2.
             ** auto with arith.
             ** apply wlt_w_0_inv;  apply wlt_0_w_inv; now rewrite <- H1 in H0. 
      -- exfalso; apply (not_wlt_Sn_0 w1 w2 n). 
         auto with arith.
         now rewrite <- H1 in H0. 
    (* 3 *)
    * exfalso; apply (lt_irrefl (length w2)); injection H.
      intro H6; now rewrite H6 in H2. 
    (* 4 *)
    * apply wlt_pad_lt; auto with arith.
      
    (* 5 *)
    * apply wlt_pad_wlt_pad; auto with arith.
Qed.

Lemma wlt_wlt_pad_zeroes : forall (w1 w2: t),
  length w1 < length w2 -> wlt w1 w2 -> wlt_pad (padd w1 w2) w2.
Proof.
  intros; apply wlt_wlt_pad. 
 - apply padd_len_le_len; auto with arith.
 - now apply wlt_wlt_zeroes_left. 
Qed.


(** Here Proof bulletization (Pierre) *)

(**
  Accessibilité pour l'ordre restreint.
*)
Lemma Acc_wlt_pad_ind : forall (n:nat),
    (forall (w:t), length w < S n -> Acc wlt_pad w) 
    -> forall (w: t), length w = S n -> Acc wlt_pad w.
Proof.  
  intros; elim (length_Sn_cons w n H0); intros a H1; elim H1;clear H1.
  intros w' H1; rewrite H1; rewrite H1 in H0; clear H1; generalize H0. 
  pattern a, w'; apply AccElim2 with (RA:=lt) (RB:=wlt_pad).
  -  intros a' w'' H1 H2 H3; apply Acc_intro; intros w''' H4; inversion H4.   
     elim (padd_len_lt_cons  w1 (cons (S a0) w'')).
     + intros w0 H9; rewrite H9; apply H1.  
       *  subst;  auto with arith.    
       * apply H; assert (H10 : length (0 :: w0) < S (S n)).        
         {  rewrite <- H9. rewrite padd_len_le_len.
            rewrite H5.  rewrite H3; auto with arith.
            transitivity (length w'');  auto with arith.
         }
         auto with arith.
       * rewrite <- H9; rewrite padd_len_le_len. 
         now rewrite H5. 
         simpl;  auto with arith.
     + simpl; auto with arith.
     + apply H1.
       * rewrite <- H5; auto with arith.
       * apply H; rewrite H8; rewrite <- H3; auto with arith.
       * simpl; rewrite H8; auto.
     + apply H2.
       *  assumption.
       *  simpl; rewrite H8; auto.
  - apply lt_wf.
  - apply H.
    rewrite <- H0; auto with arith.
Qed.


Lemma Acc_wlt_pad_nil : Acc wlt_pad nil.
Proof. apply Acc_intro.  inversion 1. Qed.

Lemma Acc_wlt_pad : forall (w:t), (Acc wlt_pad w).
Proof.
  induction w using list_length_ind.
  - apply Acc_wlt_pad_nil.
  - apply Acc_wlt_pad_ind with (n:=n); assumption.
Qed.

(**
  De l'accessibilté pour l'ordre restreint à l'accessibilité
  pour l'ordre sur tout liste.
*)
Lemma Acc_wlt_zeroes_Acc_wlt : forall (n:nat) (w: t),
    Acc wlt (zeroes n ++ w) -> Acc wlt w.
Proof.  
  intros; apply Acc_intro; intros w' H0; apply H.
  now apply wlt_wlt_zeroes_right. 
Qed.

Lemma Acc_wlt_Acc_wlt_zeroes : forall (n:nat) (w:t),
  Acc wlt w -> Acc wlt (zeroes n ++ w).
Proof.
  split. intros w' H0; apply H. 
  now apply wlt_zeroes_wlt_right with (n:=n). 
Qed.

Lemma Acc_wlt_pad_Acc_wlt : forall (w: t),
  Acc wlt_pad w -> Acc wlt w.
Proof.
  induction 1.   split. 
intros w'' H2. elim (Nat.lt_trichotomy (length w'') (length x)).

  - intro H1; apply Acc_wlt_zeroes_Acc_wlt with (n:=(dist x w'')).
     apply H0. apply wlt_wlt_pad_zeroes; assumption.
  - destruct 1.
   + apply H0. apply wlt_wlt_pad; assumption.
   +  elim (wlt_gt_length w'' x H2 H1); intros a H5.
    destruct H5 as [w H6]; decompose [and] H6.
    subst;  apply Acc_wlt_Acc_wlt_zeroes; auto. 
    apply wlt_wlt_pad in H7; auto. 
Qed.

(**
  L'ordre sur toute liste est bien fondé !
*)
Theorem Acc_wlt : forall (w:t), Acc wlt w.
Proof.
 intro; apply Acc_wlt_pad_Acc_wlt; apply Acc_wlt_pad.
Qed.

(**
   Sur wlt
*)

Lemma wlt_len_gen : forall (w1 w2:t) (a:nat),
  length w1 < length (S a :: w2) -> wlt w1 (S a :: w2).
Proof.
induction w1.
 -  intros; apply wlt_nil.
 -  intros; destruct a. 
    + apply wlt_0_w;  apply IHw1; apply lt_trans with (m:=(length (cons 0 w1))).
     * auto with arith.
     * assumption.
    +  apply wlt_len; auto with arith.
Qed.

Lemma wlt_lt_gen : forall (a1 a2:nat) (w1 w2:t),
  length w1 = length w2 ->  a1 < a2 -> wlt (a1 :: w1) (a2 :: w2).
Proof.
  intros; destruct a2.
  -  exfalso; now apply (lt_n_0 a1). 
  - destruct a1.
   + apply wlt_0_w, wlt_len_gen; rewrite H; auto with arith.
   + apply wlt_lt; auto with arith.
Qed.

Lemma wlt_wlt_gen : forall (a:nat) (w1 w2:t),
    length w1 = length w2 -> wlt w1 w2 -> wlt (a :: w1) (a :: w2).
Proof.           
  destruct a.
  -  intros; apply wlt_0_w,  wlt_w_0; assumption.
  -  intros; apply wlt_wlt; assumption.
Qed.


Lemma wlt_wf_ind : forall (P: t -> Prop),
  (forall (w1:t), (forall (w2:t), (wlt w2 w1) -> P w2) -> P w1)
  -> forall (w:t), P w.
Proof.
 intros; apply well_founded_ind with (R:=wlt).
 - red; apply Acc_wlt.
 - intros; now apply H. 
Qed.


(** Note by Pierre 
  The rest of the module should be moved to example files 
*)

Section Example_of_use.
  Variables (A: Type)
            (RA : A -> A -> Prop)
            (X: A -> Type)
            (m : A -> t).
  Hypothesis decr : forall a b, RA a b -> wlt (m a) (m b).

  Lemma wf_measure : well_founded RA.
  Proof.
   intro a; apply Acc_incl with (fun x y  => wlt (m x) (m y)).
   - assumption.
   - apply Acc_inverse_image, Acc_wlt.
  Qed.

  End Example_of_use.







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

Program Fixpoint ack_like (xy:nat*nat) {wf lex_natxnat xy} : nat :=
  match xy with
    (0, y) => (S y)
  | (S x, 0) => (ack_like (x, S 0))
  | (S x, S y) => (ack_like (x, (x + y))) +  (ack_like (S x, y))
  end.

Obligation 1.
apply lex_natxnat_fst.
auto with arith.
Qed.

Obligation 2.
apply lex_natxnat_fst.
auto with arith.
Qed.

Obligation 3. 
apply lex_natxnat_snd.
auto with arith.
Qed.

Obligation 4.
by_Acc_mwlt lex_natxnat.
Defined.

Program Fixpoint ack (xy:nat*nat) {wf lex_natxnat xy} : nat :=
  match xy with
    (0, y) => (S y)
  | (S x, 0) => (ack (x, S 0))
  | (S x, S y) => (ack (x, ack (S x, y)))
  end.
 
Obligation 1.
apply lex_natxnat_fst.
auto with arith.
Qed.

Obligation 2.
apply lex_natxnat_snd.
auto with arith.
Qed.

Obligation 3.
apply lex_natxnat_fst. inversion Heq_xy. auto with arith.
Qed.

Obligation 4.
by_Acc_mwlt lex_natxnat.
Defined.

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
    | (Node bt1 x bt2) => S (plus (btree_size A bt1) (btree_size A bt2))
  end.

Definition m_btree (A:Set) (bt:btree A) :=
  match bt with
      Empty => nil
    | (Node bt1 x bt2) => (cons (btree_size A bt) (cons (btree_size A bt1) nil))
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

Program Fixpoint listordi (xsys : t * t) {wf (lex_listxlist nat) xsys} : bool :=
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
    | (cons bt bts) => (plus (btree_size A bt) (list_btree_size A bts))
  end.

Definition wm_list_btree (A:Set) (bts:list (btree A)) : t :=
  (cons (list_btree_size A bts) (cons (length bts) nil)).

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





