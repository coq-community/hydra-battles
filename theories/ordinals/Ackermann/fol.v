(******************************************************************************)

(* Author: Russell O'Connor *)
(* This file is Public Domain *)

From Coq Require Import Lists.List  Ensembles  Peano_dec  Eqdep_dec
  Arith Compare_dec.

Require Import misc  Compat815 (* provisional *).

(* begin snippet LanguageDef *)
Record Language : Type := language
 { Relations : Set; 
   Functions : Set; 
   arity : Relations + Functions -> nat}.
(* end snippet LanguageDef *)

(* begin snippet TermDef *)
Section First_Order_Logic.

Variable L : Language.

Inductive Term : Set :=
  | var : nat -> Term
  | apply : forall f : Functions L, Terms (arity L (inr _ f)) -> Term
with Terms : nat -> Set :=
  | Tnil : Terms 0
  | Tcons : forall n : nat, Term -> Terms n -> Terms (S n).
 (* end snippet TermDef *)



Scheme Term_Terms_ind := Induction for Term Sort Prop
  with Terms_Term_ind := Induction for Terms Sort Prop.

Scheme Term_Terms_rec := Minimality for Term Sort Set
  with Terms_Term_rec := Minimality for Terms Sort Set.

Scheme Term_Terms_rec_full := Induction for Term  Sort Set
  with Terms_Term_rec_full := Induction for Terms Sort Set.

(* begin snippet FormulaDef *)
Inductive Formula : Set :=
  | equal : Term -> Term -> Formula
  | atomic : forall r : Relations L, 
      Terms (arity L (inl _ r)) -> Formula
  | impH : Formula -> Formula -> Formula
  | notH : Formula -> Formula
  | forallH : nat -> Formula -> Formula.
(* end snippet FormulaDef *)

(* begin snippet SystemDef *)
Definition Formulas := list Formula.
Definition System := Ensemble Formula.
Definition mem := Ensembles.In.
(* end snippet SystemDef *)

(* begin snippet FolFull *)
Definition orH (A B : Formula) := impH (notH A) B.
Definition andH (A B : Formula) := notH (orH (notH A) (notH B)).
Definition iffH (A B : Formula) := andH (impH A B) (impH B A).
Definition existH (x : nat) (A : Formula) := notH (forallH x (notH A)).

(* end snippet FolFull *)

(* begin snippet FolPlus *)
Definition ifThenElseH (A B C : Formula) := andH (impH A B) (impH (notH A) C).
(* end snippet FolPlus *)


(* begin snippet formDec1:: no-out *)
Section Formula_Decidability.

Definition language_decidable :=
  ((forall x y : Functions L, {x = y} + {x <> y}) *
   (forall x y : Relations L, {x = y} + {x <> y}))%type.

Hypothesis language_dec : language_decidable.
(* end snippet formDec1 *)

Let nilTermsHelp : forall n : nat, n = 0 -> Terms n.
Proof. 
  intros n H; induction n as [| n Hrecn].
  - apply Tnil.
  - discriminate H.
Defined.

Lemma nilTerms : forall x : Terms 0, Tnil = x.
Proof.
  assert (H: forall (n : nat) (p : n = 0) (x : Terms n), 
             nilTermsHelp n p = x).
  { intros n p x; induction x as [| n t x Hrecx].
    - reflexivity.
    - discriminate p.
  }
  replace Tnil with (nilTermsHelp 0 (refl_equal 0)).
  - apply H.
  - auto.
Qed.

(** Decomposition Lemma for [Terms] *)
Let consTermsHelp : forall n : nat, Terms n -> Set.
Proof. 
  intros n H; case n.
  - exact
      (forall p : 0 = n, 
          {foo : unit | eq_rec _ (fun z => Terms z) Tnil _ p = H}).
  - intros n0;
      exact
        (forall p : S n0 = n,
            {t : Term * Terms n0 |
              eq_rec _ (fun z => Terms z) (Tcons n0 (fst t) (snd t)) _ p = H}).
Defined.

Lemma consTerms :
 forall (n : nat) (x : Terms (S n)),
 {t : Term * Terms n | Tcons n (fst t) (snd t) = x}.
Proof.
  assert (H: forall (n : nat) (x : Terms n), consTermsHelp n x).
  { intros n x; induction x as [| n t x Hrecx].
    - simpl in |- *; intros p; exists tt.
      elim p using K_dec_set.
      + apply eq_nat_dec.
      + reflexivity.
    - simpl in |- *; intro p; exists (t, x).
      elim p using K_dec_set.
      + apply eq_nat_dec.
      + simpl in |- *; reflexivity.
  }
  intros n x; assert (H0: consTermsHelp _ x) by apply H.
  simpl in H0; apply (H0 (refl_equal (S n))).
Qed.

Arguments Term_Terms_rec_full P P0: rename.

(* TODO --> term_eqdec *)
(* begin snippet formDec2:: no-out *)
Lemma term_dec : forall x y : Term, {x = y} + {x <> y}.
(* end snippet formDec2 *)
Proof.
  destruct language_dec as [a b].
  assert
    (H: forall (f g : Functions L) (p : f = g) 
               (ts : Terms (arity L (inr _ f)))
               (ss : Terms (arity L (inr _ g)))
               (q : arity L (inr _ f) = arity L (inr _ g)),
        eq_rec _ (fun x => Terms x) ts _ q = ss <-> 
          apply f ts = apply g ss).
  { intros f g p;  eapply eq_ind
      with
      (x := g)
      (P := 
         fun a =>
           forall (ts : Terms (arity L (inr (Relations L) a)))
                  (ss : Terms (arity L (inr (Relations L) g)))
                  (q : arity L (inr (Relations L) a) =
                         arity L (inr (Relations L) g)),
             eq_rec (arity L (inr (Relations L) a)) 
               (fun x : nat => Terms x) ts
               (arity L (inr (Relations L) g)) q = ss <-> 
               apply a ts = apply g ss).
    - intros ts ss q; 
        apply
          K_dec_set
        with
        (x := arity L (inr (Relations L) g))
        (P := fun z =>
                eq_rec (arity L (inr (Relations L) g))
                  (fun x : nat => Terms x) ts
                  (arity L (inr (Relations L) g)) z = ss <->
                  apply g ts = apply g ss).
      apply eq_nat_dec; simpl in |- *.
      split.
      + intros H; rewrite <- H; auto.
      + intros H; inversion H as [H1].
        eapply
          inj_right_pair2 with
          (P := 
             fun f : Functions L =>
               Terms (arity L (inr (Relations L) f))); assumption.
    - auto.
  }
  intro x; elim x using
             Term_Terms_rec_full
    with
    (P0 := fun (n : nat) (ts : Terms n) =>
             forall ss : Terms n, {ts = ss} + {ts <> ss}).
  intros n y; induction y as [n0| f t].
  induction (eq_nat_dec n n0) as [a0 | b0].
  + rewrite a0; left; auto.
  + right; intro H0; inversion H0; contradiction.
  + right; discriminate.
  + intros f t H0 y; induction y as [n| f0 t0].
    * right; discriminate.
    * induction (a f f0).
      assert (H1: arity L (inr (Relations L) f0) = 
                    arity L (inr (Relations L) f)).
      { rewrite a0. reflexivity. }
      set (ss' := eq_rec _ (fun z : nat => Terms z) t0 _ H1) in *.
      assert (H2: f0 = f) by auto.
      induction (H0 ss').
      -- left; induction (H _ _ H2 t0 t H1).
         symmetry  in |- *; apply H3; symmetry  in |- *.
         apply a1.
      -- right.
         intros H3.  induction (H _ _ H2 t0 t H1) as [H4 H5].
         elim b0;  symmetry  in |- *; apply H5.
         symmetry  in |- *; assumption.
      -- right. intro H1; inversion H1.
         contradiction. 
  + left; apply nilTerms.
  + intros n t H0 t0 H1 ss.
    induction (consTerms _ ss).
    induction x0 as (a0, b0); simpl in p.
    induction (H1 b0)  as [a1 | b1].
    * induction (H0 a0).
      -- left; rewrite a1, a2; assumption.
      -- right; intro H2.
         elim b1.
         rewrite <- p in H2; inversion H2; reflexivity. 
    * right; intro H2; elim b1.
      rewrite <- p in H2; inversion H2.
      eapply inj_right_pair2 with (P := fun n : nat => Terms n).
      apply eq_nat_dec.
      assumption.
Qed.

(* TODO -> terms_eqdec *)
(* begin snippet formDec3:: no-out *)
Lemma terms_dec n  (x y : Terms n): {x = y} + {x <> y}.
(* end snippet formDec3 *)
Proof.
  induction x as [| n t x Hrecx].
  - left; apply nilTerms.
  - induction (consTerms _ y) as [(a,b) p].
    simpl in p.
    induction (Hrecx b) as [a0 | b0].
    + induction (term_dec t a) as [a1| b0].
      * left; now rewrite a1, a0.
      * right. intro H; elim b0.
        rewrite <- p in H.
        inversion H; reflexivity.
    + right. intro H; elim b0.
      rewrite <- p in H.
      inversion H.
      eapply inj_right_pair2 with (P := fun n : nat => Terms n).
      * apply eq_nat_dec.
      * assumption.
Qed.

(*  -> formula_eqdec *)

(* begin snippet formDec4:: no-out *)
Lemma formula_dec : forall x y : Formula, {x = y} + {x <> y}.
(* end snippet formDec4 *)
Proof.
  induction language_dec as [a b].
  simple induction x; simple induction y;
    (right; discriminate) || intros.
  - induction (term_dec t t1) as [a0 | b0].
    + induction (term_dec t0 t2) as [a1 | b0].
      * left; now rewrite a0, a1.
      * right; unfold not in |- *. intros H. elim b0.
        inversion H; reflexivity.
    + right; unfold not in |- *; intros H; elim b0.
      inversion H; reflexivity.
  - induction (b r r0) as [a0 | b0].
    assert
 (H: forall (f g : Relations L) (p : f = g) 
            (ts : Terms (arity L (inl _ f)))
            (ss : Terms (arity L (inl _ g)))
            (q : arity L (inl _ f) = arity L (inl _ g)),
     eq_rec _ (fun x => Terms x) ts _ q = ss <-> 
       atomic f ts = atomic g ss).
    { intros f g p; eapply eq_ind with
        (x := g)
        (P := 
           fun a =>
             forall (ts : Terms (arity L (inl _ a)))
                    (ss : Terms (arity L (inl _ g)))
                    (q : arity L (inl _ a) = arity L (inl _ g)),
               eq_rec _ (fun x => Terms x) ts _ q = ss <->
                 atomic a ts = atomic g ss).
      - intros ts ss q; elim q using K_dec_set.
        + apply eq_nat_dec.
        + simpl in |- *; split.
          * intros H; rewrite H; reflexivity.
          * intros H; inversion H.
            eapply inj_right_pair2 with
              (P := 
                 fun f : Relations L =>
                   Terms (arity L (inl (Functions L) f))).
            -- assumption.
            -- assumption.
      - auto.
    } 
    assert (H0: arity L (inl (Functions L) r) =
                  arity L (inl (Functions L) r0))
    by (rewrite a0; reflexivity). 
    induction
      (terms_dec _
         (eq_rec (arity L (inl (Functions L) r)) (fun x : nat => Terms x) t
            (arity L (inl (Functions L) r0)) H0) t0) as [a1 | b1].
    + left; induction (H _ _ a0 t t0 H0); auto.
    + right; induction (H _ _ a0 t t0 H0); tauto.
    + right. intro H; inversion H; auto.
  - destruct (H f1) as [a0 | b0].
    + destruct (H0 f2) as [a1 | b1].
      * left; now rewrite a0, a1.
      * right; intro H3; inversion H3; auto.
    + right;  intro H3; inversion H3; auto.
  - destruct (H f0) as [e | ne].
    + left; now rewrite e.
    + right; intro H1; inversion H1; auto.
  - destruct (eq_nat_dec n n0) as [e | ne]. 
    + destruct (H f0) as [a0 | b0].
      * left; now rewrite a0, e. 
      * right;  intro H1; inversion H1; auto.
    + right; inversion 1; auto.
Qed.

(* begin snippet formDec5:: no-out *)
End Formula_Decidability.
(* end snippet formDec5 *)

Section Formula_Depth_Induction.

(* begin snippet depthDef *)
Fixpoint depth (A : Formula) : nat :=
  match A with
  | equal _ _ => 0
  | atomic _ _ => 0
  | impH A B => S (Nat.max (depth A) (depth B))
  | notH A => S (depth A)
  | forallH _ A => S (depth A)
  end.

Definition lt_depth (A B : Formula) : Prop := depth A < depth B.
(* end snippet depthDef *)

Lemma depthImp1 : forall A B : Formula, lt_depth A (impH A B).
Proof.
  intros A B; red; apply Nat.lt_succ_r, Nat.le_max_l.
Qed.

Lemma depthImp2 : forall A B : Formula, lt_depth B (impH A B).
Proof.
  intros A B; red; apply Nat.lt_succ_r, Nat.le_max_r.
Qed.

Lemma depthNot : forall A : Formula, lt_depth A (notH A).
Proof. intro A; red; auto. Qed.

Lemma depthForall : forall (A : Formula) (v : nat), 
    lt_depth A (forallH v A).
Proof. intros A v; red; auto. Qed.

Lemma eqDepth :
 forall A B C : Formula, depth B = depth A ->
                         lt_depth B C -> lt_depth A C.
Proof. intros A B C H; red; now rewrite <- H. Qed.

(* Todo: upgrade to Type/rect  *)
Definition Formula_depth_rec_rec :
  forall P : Formula -> Set,
  (forall a : Formula, (forall b : Formula, lt_depth b a -> P b) -> P a) ->
  forall (n : nat) (b : Formula), depth b <= n -> P b.
Proof. 
 intros P H n; induction n as [| n Hrecn].
 - intros b H0; apply H.
   intros b0 H1; unfold lt_depth in H1.
   rewrite Nat.le_0_r in H0; rewrite H0 in H1. 
   apply Nat.nlt_0_r in H1. contradiction.
 - intros b H0; apply H.
   intros b0 H1; apply Hrecn; apply Nat.lt_succ_r .
   apply Nat.lt_le_trans with (depth b).
   + apply H1.
   + apply H0.
Defined.

(* Todo: upgrade to Type/rect  *)
Definition Formula_depth_rec (P : Formula -> Set)
  (rec : forall a : Formula, 
      (forall b : Formula, lt_depth b a -> P b) -> P a)
  (a : Formula) : P a :=
  Formula_depth_rec_rec P rec (depth a) a (le_n (depth a)).

(* solves a compatibility issue *)

(* Todo: upgrade to Type/rect  *)
Lemma Formula_depth_rec_indep :
 forall (Q P : Formula -> Set)
   (rec : forall a : Formula,
          (forall b : Formula, lt_depth b a -> Q b -> P b) -> Q a -> P a),
 (forall (a : Formula)
    (z1 z2 : forall b : Formula, lt_depth b a -> Q b -> P b),
  (forall (b : Formula) (p : lt_depth b a) (q : Q b), z1 b p q = z2 b p q) ->
  forall q : Q a, rec a z1 q = rec a z2 q) ->
 forall (a : Formula) (q : Q a),
 Formula_depth_rec (fun x : Formula => Q x -> P x) rec a q =
 rec a
   (fun (b : Formula) _ =>
    Formula_depth_rec (fun x : Formula => Q x -> P x) rec b) q.
Proof.
  intros Q P rec H.
  unfold Formula_depth_rec in |- *.
  set (H0 := Formula_depth_rec_rec (fun x : Formula => Q x -> P x) rec) 
    in *.
  assert
    (H1: forall (n m : nat) (b : Formula) (l1 : depth b <= n) 
                (l2 : depth b <= m) (q : Q b), H0 n b l1 q = H0 m b l2 q).
  { simple induction n.
    - simpl in |- *.
      intros m b l1 l2 q; induction m as [| m Hrecm].
      + simpl in |- *; apply H.
        intros b0 p q0. 
        induction  (* Warning to fix *)
          (Nat.nlt_0_r (depth b0)
             (eq_ind_r (fun n0 : nat => depth b0 < n0) p
                (Compat815.le_n_0_eq (depth b) l1))).
      + intros; simpl ; apply H.
        intros b0 p q0.
        induction (* warning to fix *)
          (Nat.nlt_0_r (depth b0)
             (eq_ind_r (fun n0 : nat => depth b0 < n0) p
                (Compat815.le_n_0_eq (depth b) l1))).
    - simple induction m.
      + intros b l1 l2 q; simpl in |- *; apply H.
        intros  b0 p q0.
        induction (*warning to fix *)
          (Nat.nlt_0_r  (depth b0)
             (eq_ind_r (fun n1 : nat => depth b0 < n1) p
                (Compat815.le_n_0_eq (depth b) l2))).
      + intros n1 H2 b l1 l2 q;  simpl in |- *; apply H.
        intros  b0 p q0.
        apply H1.
  } 
  intros a q;
    replace (H0 (depth a) a (le_n (depth a)) q) with
    (H0 (S (depth a)) a (Nat.le_succ_diag_r (depth a)) q).
  - simpl in |- *; apply H.
    intros; apply H1.
  - apply H1.
Qed.

(* Todo: upgrade to Type/rect  *)
Definition Formula_depth_rec2rec (P : Formula -> Set)
  (f1 : forall t t0 : Term, P (equal t t0))
  (f2 : forall (r : Relations L) 
               (t : Terms (arity L (inl (Functions L) r))),
        P (atomic r t))
  (f3 : forall f : Formula, P f -> forall f0 : Formula, P f0 -> P (impH f f0))
  (f4 : forall f : Formula, P f -> P (notH f))
  (f5 : forall (v : nat) (a : Formula),
        (forall b : Formula, lt_depth b (forallH v a) -> P b) ->
        P (forallH v a)) (a : Formula) :
  (forall b : Formula, lt_depth b a -> P b) -> P a :=
  match a return ((forall b : Formula, lt_depth b a -> P b) -> P a) with
  | equal t s => fun _ => f1 t s
  | atomic r t => fun _ => f2 r t
  | impH f g =>
      fun hyp => f3 f (hyp f (depthImp1 f g)) g (hyp g (depthImp2 f g))
  | notH f => fun hyp => f4 f (hyp f (depthNot f))
  | forallH n f => fun hyp => f5 n f hyp
  end.

(* Todo: upgrade to Type/rect  *)
Definition Formula_depth_rec2 (P : Formula -> Set)
  (f1 : forall t t0 : Term, P (equal t t0))
  (f2 : forall (r : Relations L) (t : Terms (arity L (inl (Functions L) r))),
        P (atomic r t))
  (f3 : forall f : Formula, P f -> forall f0 : Formula, P f0 -> P (impH f f0))
  (f4 : forall f : Formula, P f -> P (notH f))
  (f5 : forall (v : nat) (a : Formula),
        (forall b : Formula, lt_depth b (forallH v a) -> P b) ->
        P (forallH v a)) (a : Formula) : P a :=
  Formula_depth_rec P (Formula_depth_rec2rec P f1 f2 f3 f4 f5) a.

(* Todo: upgrade to Type/rect  *)
Remark Formula_depth_rec2rec_nice :
 forall (Q P : Formula -> Set)
   (f1 : forall t t0 : Term, Q (equal t t0) -> P (equal t t0))
   (f2 : forall (r : Relations L) 
                (t : Terms (arity L (inl (Functions L) r))),
         Q (atomic r t) -> P (atomic r t))
   (f3 : forall f : Formula,
         (Q f -> P f) ->
         forall f0 : Formula,
         (Q f0 -> P f0) -> Q (impH f f0) -> P (impH f f0)),
 (forall (f g : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall z3 z4 : Q g -> P g,
  (forall q : Q g, z3 q = z4 q) ->
  forall q : Q (impH f g), f3 f z1 g z3 q = f3 f z2 g z4 q) ->
 forall f4 : forall f : Formula, (Q f -> P f) -> Q (notH f) -> P (notH f),
 (forall (f : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall q : Q (notH f), f4 f z1 q = f4 f z2 q) ->
 forall
   f5 : forall (v : nat) (a : Formula),
        (forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b) ->
        Q (forallH v a) -> P (forallH v a),
 (forall (v : nat) (a : Formula)
    (z1 z2 : forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b),
  (forall (b : Formula) (q : lt_depth b (forallH v a)) (r : Q b),
   z1 b q r = z2 b q r) ->
  forall q : Q (forallH v a), f5 v a z1 q = f5 v a z2 q) ->
 forall (a : Formula)
   (z1 z2 : forall b : Formula, lt_depth b a -> Q b -> P b),
 (forall (b : Formula) (p : lt_depth b a) (q : Q b), z1 b p q = z2 b p q) ->
 forall q : Q a,
 Formula_depth_rec2rec (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 a z1 q =
 Formula_depth_rec2rec (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 a z2 q.
Proof.
  intros Q P f1 f2 f3 H f4 H0 f5 H1 a z1 z2 H2 q.
  induction a as [t t0| r t| a1 Hreca1 a0 Hreca0| a Hreca| n a Hreca].
  - auto.
  - auto.
  - simpl in |- *; apply H.
    + intros q0; apply H2.
    + intros q0; apply H2.
  - simpl in |- *; apply H0; intros q0; apply H2.
  - simpl in |- *; apply H1, H2.
Qed.

(* Todo: upgrade to Type/rect  *)
Lemma Formula_depth_rec2_imp :
  forall (Q P : Formula -> Set)
         (f1 : forall t t0 : Term, Q (equal t t0) -> P (equal t t0))
         (f2 : forall (r : Relations L) 
                      (t : Terms (arity L (inl (Functions L) r))),
             Q (atomic r t) -> P (atomic r t))
         (f3 : forall f : Formula,
             (Q f -> P f) ->
             forall f0 : Formula,
               (Q f0 -> P f0) -> Q (impH f f0) -> P (impH f f0)),
    (forall (f g : Formula) (z1 z2 : Q f -> P f),
        (forall q : Q f, z1 q = z2 q) ->
        forall z3 z4 : Q g -> P g,
          (forall q : Q g, z3 q = z4 q) ->
          forall q : Q (impH f g), f3 f z1 g z3 q = f3 f z2 g z4 q) ->
    forall f4 : forall f : Formula, (Q f -> P f) -> Q (notH f) -> P (notH f),
      (forall (f : Formula) (z1 z2 : Q f -> P f),
          (forall q : Q f, z1 q = z2 q) ->
          forall q : Q (notH f), f4 f z1 q = f4 f z2 q) ->
      forall
        f5 : forall (v : nat) (a : Formula),
        (forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b) ->
        Q (forallH v a) -> P (forallH v a),
        (forall (v : nat) (a : Formula)
                (z1 z2 : forall b : Formula, 
                    lt_depth b (forallH v a) -> Q b -> P b),
            (forall (b : Formula) (q : lt_depth b (forallH v a)) (r : Q b),
                z1 b q r = z2 b q r) ->
            forall q : Q (forallH v a), f5 v a z1 q = f5 v a z2 q) ->
        forall (a b : Formula) (q : Q (impH a b)),
          Formula_depth_rec2 (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 
            (impH a b) q =
            f3 a (Formula_depth_rec2 (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 a) b
              (Formula_depth_rec2 (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 b) q.
Proof.
  intros; unfold Formula_depth_rec2 at 1 in |- *; 
    rewrite Formula_depth_rec_indep.
  - simpl in |- *; reflexivity.
  - intros; apply Formula_depth_rec2rec_nice; auto.
Qed.

(* Todo: upgrade to Type/rect  *)
Lemma Formula_depth_rec2_not :
 forall (Q P : Formula -> Set)
   (f1 : forall t t0 : Term, Q (equal t t0) -> P (equal t t0))
   (f2 : forall (r : Relations L) 
                (t : Terms (arity L (inl (Functions L) r))),
         Q (atomic r t) -> P (atomic r t))
   (f3 : forall f : Formula,
         (Q f -> P f) ->
         forall f0 : Formula,
         (Q f0 -> P f0) -> Q (impH f f0) -> P (impH f f0)),
 (forall (f g : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall z3 z4 : Q g -> P g,
  (forall q : Q g, z3 q = z4 q) ->
  forall q : Q (impH f g), f3 f z1 g z3 q = f3 f z2 g z4 q) ->
 forall f4 : forall f : Formula, (Q f -> P f) -> Q (notH f) -> P (notH f),
 (forall (f : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall q : Q (notH f), f4 f z1 q = f4 f z2 q) ->
 forall
   f5 : forall (v : nat) (a : Formula),
        (forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b) ->
        Q (forallH v a) -> P (forallH v a),
 (forall (v : nat) (a : Formula)
    (z1 z2 : forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b),
  (forall (b : Formula) (q : lt_depth b (forallH v a)) (r : Q b),
   z1 b q r = z2 b q r) ->
  forall q : Q (forallH v a), f5 v a z1 q = f5 v a z2 q) ->
 forall (a : Formula) (q : Q (notH a)),
 Formula_depth_rec2 
   (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 (notH a) q =
   f4 a (Formula_depth_rec2 (fun x : Formula => Q x -> P x) 
           f1 f2 f3 f4 f5 a) q.
Proof.
  intros; unfold Formula_depth_rec2 at 1; rewrite Formula_depth_rec_indep.
  - reflexivity.
  - apply Formula_depth_rec2rec_nice; auto.
Qed.

(* Formula_depth_rec2_forall is used in
codeSubFormula.v:917: (Formula_depth_rec2_forall L) (in a Proof) 
codeSubFormula.v:6279: (Formula_depth_rec2_forall L)
folProp.v:558: (Formula_depth_rec2_forall L)
*)

(* Todo: upgrade to Type/rect  *)
Lemma Formula_depth_rec2_forall :
 forall (Q P : Formula -> Set)
   (f1 : forall t t0 : Term, Q (equal t t0) -> P (equal t t0))
   (f2 : forall (r : Relations L) (t : Terms (arity L (inl (Functions L) r))),
         Q (atomic r t) -> P (atomic r t))
   (f3 : forall f : Formula,
         (Q f -> P f) ->
         forall f0 : Formula,
         (Q f0 -> P f0) -> Q (impH f f0) -> P (impH f f0)),
 (forall (f g : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall z3 z4 : Q g -> P g,
  (forall q : Q g, z3 q = z4 q) ->
  forall q : Q (impH f g), f3 f z1 g z3 q = f3 f z2 g z4 q) ->
 forall f4 : forall f : Formula, (Q f -> P f) -> Q (notH f) -> P (notH f),
 (forall (f : Formula) (z1 z2 : Q f -> P f),
  (forall q : Q f, z1 q = z2 q) ->
  forall q : Q (notH f), f4 f z1 q = f4 f z2 q) ->
 forall
   f5 : forall (v : nat) (a : Formula),
        (forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b) ->
        Q (forallH v a) -> P (forallH v a),
 (forall (v : nat) (a : Formula)
    (z1 z2 : forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b),
  (forall (b : Formula) (q : lt_depth b (forallH v a)) (r : Q b),
   z1 b q r = z2 b q r) ->
  forall q : Q (forallH v a), f5 v a z1 q = f5 v a z2 q) ->
 forall (v : nat) (a : Formula) (q : Q (forallH v a)),
 Formula_depth_rec2 (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5
   (forallH v a) q =
 f5 v a
   (fun (b : Formula) _ (q : Q b) =>
    Formula_depth_rec2 (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 b q) q.
Proof. 
  intros Q P f1 f2 f3 H f4 H0 f5 H1 v a q. 
  unfold Formula_depth_rec2 at 1 in |- *; 
    rewrite Formula_depth_rec_indep.
  - simpl in |- *; apply H1; reflexivity. 
  - apply Formula_depth_rec2rec_nice; auto.
Qed.

(* Todo: use the Type version (when done)  *)
Definition Formula_depth_ind :
  forall P : Formula -> Prop,
  (forall a : Formula, (forall b : Formula, lt_depth b a -> P b) -> P a) ->
  forall a : Formula, P a.
Proof.
  intros P H a; 
    assert (H0: forall (n : nat) (b : Formula), depth b <= n -> P b).
  { induction n as [| n Hrecn].
    - intros b H0; apply H.
      intros b0 H1; unfold lt_depth in H1.
      rewrite  (Nat.le_0_r) in H0; rewrite H0 in H1.
      destruct (Nat.nlt_0_r _ H1).
    - intros b H0; apply H; intros b0 H1.
      apply Hrecn.
      apply Nat.lt_succ_r.
      apply Nat.lt_le_trans with (depth b).
      + apply H1.
      + apply H0.
  }
  eapply H0; apply le_n.
Qed.

Lemma Formula_depth_ind2 :
 forall P : Formula -> Prop,
 (forall t t0 : Term, P (equal t t0)) ->
 (forall (r : Relations L) 
         (t : Terms (arity L (inl (Functions L) r))),
     P (atomic r t)) ->
 (forall f : Formula, P f -> forall f0 : Formula, P f0 -> P (impH f f0)) ->
 (forall f : Formula, P f -> P (notH f)) ->
 (forall (v : nat) (a : Formula),
  (forall b : Formula, lt_depth b (forallH v a) -> P b) -> P (forallH v a)) ->
 forall f : Formula, P f.
Proof.
  intros P H H0 H1 H2 H3 f; apply Formula_depth_ind.
  simple induction a; auto.
  - intros f0 H4 f1 H5 H6; apply H1.
    + apply H6, depthImp1.
    + apply H6, depthImp2.
  - intros f0 H4 H5; apply H2, H5.
    apply depthNot.
Qed.

End Formula_Depth_Induction.

End First_Order_Logic.


Arguments Term_Terms_ind  L P P0 : rename.
Arguments Terms_Term_ind L P P0 : rename.

Arguments Term_Terms_rec L P P0 : rename.
Arguments Terms_Term_rec L P P0 : rename.

Arguments Term_Terms_rec_full L P P0 : rename.
Arguments Terms_Term_rec_full L P P0 : rename.

(** experiments by PC *)

Arguments impH {L} _ _.
Arguments notH {L} _.
Arguments forallH {L} _ _.
Arguments orH {L} _ _.
Arguments andH {L} _ _.
(* To compile *)
Arguments iffH {L} _ _.


