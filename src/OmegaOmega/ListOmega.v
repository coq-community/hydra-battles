(** An implementation of [omega ^ omega]
    Pascal Manoury et al. *)

(** Proof bulletization by Pierre Casteran (in progress) *)
(** To do : translate the comments into english (and make them coqdoc compatible) *)


Require Import Arith.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Require Import List.
Require Import Recdef Lia.
Require Import  Coq.Wellfounded.Inverse_Image Coq.Wellfounded.Inclusion.

Coercion is_true : bool >-> Sortclass.

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


Declare Scope lo_scope.
Delimit Scope lo_scope with lo.
Open Scope lo_scope.

Definition t := list nat.

Notation  "'omega'" := (1::0::nil) : lo_scope.
Definition fin (i:nat) : t := (i::nil).

Coercion fin : nat >-> t.

Check (1::0::nil).

Check (fin 42).

Definition nf (alpha : t) :bool :=
  match alpha with
    nil | S _ :: _ => true
  | _ => false
  end.

Fixpoint succ (alpha: t) :=
  match alpha with
  | nil => 1::nil
  | n:: nil => S n :: nil
  | n :: l => n :: succ l
  end.

Compute succ (succ omega).

(* incorrect if not nf alpha *)

Fixpoint limitb (alpha: t) :=
  match alpha with
  |  nil | S _ :: nil => false
  |  _ :: 0 :: nil => true
  |  _ :: w => limitb w
  end.


Compute limitb omega.
Compute limitb (3::4::0::0::1::0::nil).
Compute succ (3::4::0::0::1::0::nil).
Compute limitb (3::0::0::0::0::0::nil).

(** to do : addition, commutative addition  *)
  
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
 - intro.  inversion H0; auto.
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

(** wlt is a strict order *)

Lemma wlt_eq : forall a:nat, forall w1 w2:t,
      (length w1)=(length w2) -> (wlt (a::w1) (a::w2)) -> (wlt w1 w2).
Proof.
  destruct a.
  - intros. apply wlt_0_w_inv. apply wlt_w_0_inv. assumption.
  - intros. inversion H0.
    * exfalso. apply lt_irrefl with (x:=length w2). rewrite H in H2. assumption.
    * exfalso. apply lt_irrefl with (x:=a). assumption.
    * assumption.
Qed.

Lemma wlt_irref : forall w:t, ~ wlt w w.
Proof. 
  induction w.
  - apply not_wlt_nil.
  - case a.
    + intro. apply IHw. apply wlt_0_w_inv. apply wlt_w_0_inv. assumption.
    + intros. intro. inversion H.  
      * apply lt_irrefl with (x:=length w). assumption.
      * apply lt_irrefl with (x:=n). assumption.
      * apply IHw. apply wlt_eq with (a:=S n); assumption.
Qed.

Lemma wlt_trans : forall w1 w2 w3:t, (wlt w1 w2) -> (wlt w2 w3) -> (wlt w1 w3).
Proof. 
  intros w1 w2 w3. generalize w3 w2 w1.
  induction w0.
  - intros. exfalso. apply (not_wlt_nil w0). assumption.
  - case a.
    + intros. apply wlt_w_0. apply IHw0 with (w2:=w4).
      * assumption.
      * apply wlt_w_0_inv. assumption.    

    + induction w4.
      * intros. exfalso. apply (not_wlt_nil w4). assumption.
      * case a0.
        -- intros. apply IHw4.
           ++ apply wlt_w_0_inv. assumption.
           ++ apply wlt_0_w_inv. assumption.
        -- induction w5.
           ++ intros. apply wlt_nil.
           ++ case a1.
              ** intros. apply wlt_0_w. apply IHw5.
                 --- apply wlt_0_w_inv. assumption.
                 --- assumption.
              ** intros. inversion H.
                 --- inversion H0.
                     +++ apply wlt_len. apply lt_trans with (m:=length w4);
                         assumption.
                     +++ apply wlt_len. rewrite H9 in H2. assumption.
                     +++ apply wlt_len. rewrite H9 in H2. assumption.
                 --- inversion H0.
                     +++ apply wlt_len. rewrite <- H4 in H8. assumption.
                     +++ apply wlt_lt.
                         *** rewrite H4. assumption.
                         *** apply lt_trans with (m:=n0); assumption.
                     +++ apply wlt_lt.
                         *** rewrite H4. assumption.
                         *** rewrite <- H9. assumption.
                 --- inversion H0.
                     +++ apply wlt_len. rewrite H4. assumption.
                     +++ apply wlt_lt.
                         *** rewrite <- H4 in H10. assumption.
                         *** assumption.
                     +++ apply wlt_wlt.
                         *** rewrite <- H4 in H10. assumption.
                         *** apply IHw0 with (w2:=w4); assumption.
Qed.                       

Require Import RelationClasses.

Instance wlt_strorder : StrictOrder wlt.
Proof.
  split.
  - unfold Irreflexive. unfold Reflexive. unfold complement. apply wlt_irref.
  - unfold Transitive. intros. apply wlt_trans with (w2:=y); assumption.
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

(** Compare *)
Fixpoint compare (w1 w2 : t) : comparison :=
  match w1 with
    nil =>
    let fix compare2 w2 := 
        match w2 with
          nil => Eq
        | 0::w2 => (compare2 w2)
        | _ => Lt
        end
    in (compare2 w2)
  | 0::w1 => (compare w1 w2)
  | a1::w1 =>
    let fix compare2 w2 :=
        match w2 with
          nil => Gt
        | 0::w2 => (compare2 w2)
        | a2::w2 =>
          match (Nat.compare (length w1) (length w2)) with
            Eq =>
            match (Nat.compare a1 a2) with
              Eq => (compare w1 w2)
            | x => x
            end
          | x => x
          end
        end
    in (compare2 w2)
  end.

Lemma compare_nil_nil : (compare nil nil) = Eq.
Proof.
  auto.
Qed.

Lemma compare_nil_S : forall (n:nat) (w:t), (compare nil ((S n)::w)) = Lt.
Proof.
  auto.
Qed.

Lemma compare_S_nil : forall (n:nat) (w:t), (compare ((S n)::w) nil) = Gt.
Proof.
  auto.
Qed.

Lemma compare_0_w : forall (w1 w2:t), (compare (0::w1) w2) = (compare w1 w2). 
Proof.
  auto.
Qed.

Lemma compare_w_0 : forall (w1 w2:t), (compare w1 (0::w2)) = (compare w1 w2).
Proof.
  induction w1.
  - intro. simpl. trivial.
  - intro. case a.
    + simpl. rewrite IHw1. trivial.
    + intro. simpl. trivial.
Qed.

Fixpoint nf_of (w:t) : t :=
  match w with
    nil => nil
  | 0::w => (nf_of w)
  | _ => w
  end.

Inductive Wnf : t -> Prop :=
  Wnf_nil : (Wnf nil)
| Wnf_cons : forall (n:nat) (w:t), (Wnf (S n::w)).

Lemma nf_of_correct : forall (w:t), (Wnf (nf_of w)).
Proof.
  induction w.
  - apply Wnf_nil.
  - case a.
    * apply IHw.
    * intro. apply Wnf_cons.
Qed.

Lemma compare_nf : forall (w1 w2:t), (compare (nf_of w1) (nf_of w2))=(compare w1 w2).
Proof.
  induction w1.
  - induction w2.
    + auto.
    + case a.
      * simpl nf_of. rewrite compare_w_0. trivial.
      * auto.
  - case a.
    + auto.
    + induction w2.
      * auto.
      * case a0.
        -- auto.
        -- auto.
Qed.

Lemma compare_eq_len_nf : forall (w1 w2:t),
    (Wnf w1) -> (Wnf w2) -> (compare w1 w2)=Eq -> (compare (length w1) (length w2))=Eq.
Proof.
  intros w1 w2 H. induction H.
  - intro H. induction H.
    + auto.
    + discriminate.
  - intro H. induction H.
    + discriminate.
    + case_eq ((length w) ?= (length w0)).
      * intros. simpl. rewrite H. trivial.
      * intro. simpl. rewrite H. auto.
      * intro. simpl. rewrite H. auto.
Qed.

Inductive weq : t -> t -> Prop :=
  weq_nil : weq nil nil
| weq_0_w : forall (w1 w2:t), (weq w1 w2) -> (weq (0::w1) w2)
| weq_w_0 : forall (w1 w2:t), (weq w1 w2) -> (weq w1 (0::w2))
| weq_S : forall (a:nat) (w1 w2:t), (weq w1 w2) -> (weq (S a::w1) (S a::w2)).



Lemma eq_eq_nat : forall (n1 n2:nat), (n1 ?= n2)=Eq -> n1 = n2.
Proof.
  intros; destruct (Nat.compare_spec n1 n2); auto;  discriminate.
Qed.

Lemma lt_lt_nat : forall (n1 n2:nat), (n1 ?= n2)=Lt -> n1 < n2 .
Proof.
    intros; destruct (Nat.compare_spec n1 n2); auto;  discriminate.
Qed.

Lemma gt_lt_nat : forall (n1 n2:nat), (n1 ?= n2)=Gt -> (lt n2 n1).
Proof.
    intros; destruct (Nat.compare_spec n1 n2); auto;  discriminate.
Qed.

Lemma compare_eq_head : forall (n1 n2:nat) (w1 w2:t),
    (compare (S n1::w1) (S n2::w2))=Eq -> n1=n2.
Proof.
  intros n1 n2 w1 w2. simpl. case_eq (length w1 ?= length w2).
  - intro. case_eq (n1 ?= n2).
    + intros. apply eq_eq_nat. assumption.
    + discriminate.
    + discriminate.
  - discriminate.
  - discriminate.
Qed.
    
Lemma compare_eq_tail : forall (n1 n2:nat) (w1 w2:t),
    (compare (S n1::w1) (S n2::w2))=Eq -> (compare w1 w2)=Eq.
Proof.
  intros n1 n2 w1 w2. simpl. case_eq (length w1 ?= length w2).
  - intro. case_eq (n1 ?= n2).
    + trivial.
    + discriminate.
    + discriminate.
  - discriminate.
  - discriminate.
Qed.
    
Lemma compare_eq : forall (w1 w2:t), (compare w1 w2) = Eq -> (weq w1 w2).
Proof.
  induction w1.
  - induction w2.
    + intro. apply weq_nil.
    + case a.
      * intro. apply weq_w_0. apply IHw2. rewrite compare_w_0 in H. assumption.
      * intros. simpl in H. discriminate.
  - case a.
    + intros. apply weq_0_w. apply IHw1. rewrite compare_0_w in H. assumption.
    + induction w2.
      * discriminate.
      * case a0.
        -- intro. apply weq_w_0. apply IHw2. rewrite compare_w_0 in H. assumption.
        -- intros. rewrite (compare_eq_head n n0 w1 w2 H).
           apply weq_S. apply IHw1. apply compare_eq_tail with (n1:=n) (n2:=n0).
           assumption.
Qed.

Lemma compare_lt_wlt : forall (w1 w2:t), (compare w1 w2)=Lt -> (wlt w1 w2).
Proof.
  induction w1.
  - induction w2.
    + discriminate.
    + case a.
      * rewrite compare_w_0. intro. apply wlt_w_0. auto.
      * intros. apply wlt_nil.
  - case a.
    + intros. apply wlt_0_w. apply IHw1.
      rewrite compare_0_w in H. assumption.
    + induction w2.
      * discriminate.
      * case a0.
        -- intro. apply wlt_w_0. apply IHw2.
           rewrite compare_w_0 in H. assumption.
        -- intro. simpl. case_eq (length w1 ?= length w2).
           ++ intro. case_eq (n ?= n0).         
              ** intros. rewrite (eq_eq_nat n n0 H0). apply wlt_wlt.
                 --- apply eq_eq_nat. assumption.
                 --- apply IHw1. assumption.
              ** intros. apply wlt_lt. 
                 --- apply eq_eq_nat. assumption.
                 --- apply lt_lt_nat. assumption.
              ** discriminate.
           ++ intros. apply wlt_len. apply lt_lt_nat. assumption.
           ++ discriminate.
Qed.

Lemma compare_gt_wlt : forall (w1 w2:t), (compare w1 w2)=Gt -> (wlt w2 w1).
Proof.
  induction w1.
  - induction w2.
    + discriminate.
    + case a.
      * intro. apply wlt_0_w. apply IHw2. rewrite compare_w_0 in H. assumption.
      * discriminate.
  - case a.
    + intros. apply wlt_w_0. apply IHw1. rewrite compare_0_w in H. assumption.
    + induction w2.
      * intro. apply wlt_nil.
      * case a0.
        -- intro. apply wlt_0_w. apply IHw2. rewrite compare_w_0 in H. assumption.
        -- intro. simpl. case_eq (length w1 ?= length w2).
           ++ intro. case_eq (n ?= n0). 
              ** intros. rewrite (eq_eq_nat n n0 H0). apply wlt_wlt.
                 --- rewrite (eq_eq_nat (length w1) (length w2) H). trivial.
                 --- apply IHw1. assumption.
              ** discriminate.
              ** intros. apply wlt_lt.
                 --- rewrite (eq_eq_nat (length w1) (length w2) H). trivial.
                 --- apply gt_lt_nat. assumption.
           ++ discriminate.
           ++ intros. apply wlt_len.
              apply gt_lt_nat. assumption.
Qed.
                   
Lemma compare_reflect w1 w2 :
  match (compare w1 w2) with
    Lt => (wlt w1 w2)
  | Eq => (weq w1 w2)
  | GT => (wlt w2 w1)
  end.
Proof.
case_eq (compare w1 w2).
+ intro. apply compare_eq. assumption.
+ intro. apply compare_lt_wlt. assumption.
+ intro. apply compare_gt_wlt. assumption.
Qed.

Lemma compare_correct (w1:t) (w2:t) :
  CompareSpec (weq w1 w2) (wlt w1 w2) (wlt w2 w1) (compare w1 w2).
Proof.
  generalize (compare_reflect w1 w2).
  destruct (compare w1 w2); now constructor.
Qed.
  
(**
  Ordinal notation

Require Import OrdinalNotations.Generic.

Instance OmegaOmega : ON wlt compare.
Proof.
  split.
  - apply wlt_strorder.
  - unfold well_founded. exact Acc_wlt.
  - Abort.

 *)
 
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
            (m : A -> t).
  Hypothesis decr : forall a b, RA a b -> wlt (m a) (m b).

  Lemma wf_measure : well_founded RA.
  Proof.
   intro a; apply Acc_incl with (fun x y  => wlt (m x) (m y)).
   - assumption.
   - apply Acc_inverse_image, Acc_wlt.
  Qed.

  End Example_of_use.


