(******************************************************************************)
From Coq Require Import Wf_nat Arith Lists.List Peano_dec. 

Require Import ListExt. 
Require Export fol.
Import FolNotations.

Section Fol_Properties.

Variable L : Language.

Notation Formula := (Formula L) (only parsing).
Notation Formulas := (Formulas L) (only parsing).
Notation System := (System L) (only parsing).
Notation Term := (Term L) (only parsing).
Notation Terms := (Terms L) (only parsing).
  
Let lt_depth := lt_depth L.

Section Free_Variables.
(* begin snippet freeVarT *)
Fixpoint freeVarT (s : fol.Term L) : list nat :=
  match s with
  | var v => v :: nil
  | apply f ts => freeVarTs (arityF L f) ts
  end
with freeVarTs (n : nat) (ss : fol.Terms L n) {struct ss} : list nat :=
       match ss with
       | Tnil => nil (A:=nat)
       | Tcons m t ts => freeVarT t ++ freeVarTs m ts
       end.
(* end snippet freeVarT *)

Lemma freeVarTApply :
  forall (f : Functions L) (ts : fol.Terms L _),
    freeVarT (apply f ts) = freeVarTs _ ts.
Proof. reflexivity. Qed.

(* begin snippet freeVarF *)
Fixpoint freeVarF (A : fol.Formula L) : list nat :=
  match A with
  | equal t s => freeVarT t ++ freeVarT s
  | atomic r ts => freeVarTs _ ts
  | impH A B => freeVarF A ++ freeVarF B
  | notH A => freeVarF A
  | forallH v A => remove  eq_nat_dec v (freeVarF A)
  end.
(* end snippet freeVarF *)

Definition ClosedSystem (T : fol.System L) :=
  forall (v : nat) (f : fol.Formula L),
    mem _ T f -> ~ In v (freeVarF f).

(* begin snippet closeDef *)
(* added by PC *)
Definition closed (a : fol.Formula L):=
  forall v: nat, ~ In v (freeVarF a).


Fixpoint closeList (l: list nat)(a : fol.Formula L) :=
 match l with
   nil => a
|  cons v l =>  (forallH v (closeList l a))
end.

Definition close (x : fol.Formula L) : fol.Formula L :=
  closeList (nodup eq_nat_dec (freeVarF x)) x.
(* end snippet closeDef *)

Lemma freeVarClosedList1 :
  forall (l : list nat) (v : nat) (x : fol.Formula L),
    In v l -> ~ In v (freeVarF (closeList l x)).
Proof.
  intro l; induction l as [| a l Hrecl].
  - intros v x H; elim H.
  - intros v x H; induction H as [H| H].
    + simpl in |- *; rewrite H.
      unfold not in |- *; intros H0;
        elim (in_remove_neq _ _ _ _ _ H0); reflexivity.
    + simpl in |- *.  intro H0. 
      assert (H1: In v (freeVarF (closeList l x))).
      { eapply in_remove.   apply H0. }
      apply (Hrecl _ _ H H1).
Qed.

Lemma freeVarClosedList2 :
  forall (l : list nat) (v : nat) (x : fol.Formula L),
    In v (freeVarF (closeList l x)) ->
    In v (freeVarF x).
Proof.
  intro l; induction l as [| a l Hrecl].
  - simpl; intros v x H; apply H.
  - simpl; intros v x H; apply Hrecl; eapply in_remove;  apply H.
Qed.

Lemma freeVarClosed :
  forall (x : fol.Formula L) (v : nat), ~ In v (freeVarF (close x)).
Proof.
  intros x v; unfold close;
  destruct (In_dec eq_nat_dec v (nodup eq_nat_dec (freeVarF x)))
    as [i | n]. 
  - apply freeVarClosedList1; assumption.
  - intro H; elim n. rewrite nodup_In.  
    eapply freeVarClosedList2; apply H.
Qed.

Fixpoint freeVarListFormula (l : fol.Formulas L) : list nat :=
  match l with
  | nil => nil (A:=nat)
  | f :: l => freeVarF f ++ freeVarListFormula l
  end.

Lemma freeVarListFormulaApp :
  forall a b : fol.Formulas L,
    freeVarListFormula (a ++ b) =
      freeVarListFormula a ++ freeVarListFormula b.
Proof.
  intros a b; induction a as [| a a0 Hreca].
  - reflexivity.
  - simpl in |- *; rewrite Hreca; now rewrite app_assoc. 
Qed.

Lemma In_freeVarListFormula :
  forall (v : nat) (f : fol.Formula L) (F : fol.Formulas L),
    In v (freeVarF f) -> In f F -> In v (freeVarListFormula F).
Proof.
  intros v f F H H0; induction F as [| a F HrecF].
  - elim H0.
  - destruct H0 as [H0| H0]; simpl in |- *.
    + apply in_or_app; left; now rewrite H0.
    + apply in_or_app; auto.
Qed.

Lemma In_freeVarListFormulaE :
  forall (v : nat) (F : fol.Formulas L),
    In v (freeVarListFormula F) ->
    exists f : fol.Formula L, In v (freeVarF f) /\ In f F.
Proof.
  intros v F H; induction F as [| a F HrecF].
  - destruct H.
  - destruct (in_app_or _ _ _ H) as [H0 | H0].
    + exists a; simpl in |- *; auto.
    + destruct (HrecF H0) as [x Hx]; exists x; cbn; tauto.
Qed.

Definition In_freeVarSys (v : nat) (T : fol.System L) :=
  exists f : fol.Formula L, In v (freeVarF f) /\ mem _ T f.

Lemma notInFreeVarSys :
  forall x, ~ In_freeVarSys x (Ensembles.Empty_set (fol.Formula L)).
Proof.
  intros x; unfold In_freeVarSys in |- *.
  intros [? [? H0]]; destruct H0. 
Qed.

End Free_Variables.

Section Substitution.


(* later abbreviated into substT and substTs *)

(* begin snippet subsTdef *)
Fixpoint substT (s : fol.Term L) (x : nat) 
  (t : fol.Term L) {struct s} : fol.Term L :=
  match s with
  | var v =>
      match eq_nat_dec x v with
      | left _ => t
      | right _ => var v
      end
  | apply f ts => apply f (substTs _ ts x t)
  end
with substTs (n : nat) (ss : fol.Terms L n) 
       (x : nat) (t : fol.Term L) {struct ss} : fol.Terms L n :=
       match ss in (fol.Terms _ n0) return (fol.Terms L n0) with
       | Tnil => Tnil
       | Tcons m s ts =>
           Tcons  (substT s x t) (substTs m ts x t)
       end.
(* end snippet subsTdef *)

Lemma subTermVar1 :
  forall (v : nat) (s : fol.Term L), substT (var v) v s = s.
Proof.
  intros v s;  unfold substT in |- *.
  destruct  (eq_nat_dec v v) as [e | b].
  - reflexivity.
  - now destruct b.
Qed.

Lemma subTermVar2 :
  forall (v x : nat) (s : fol.Term L),
    v <> x -> substT (var x) v s = var x.
Proof.
  intros v x s H; unfold substT in |- *.
  destruct (eq_nat_dec v x); [contradiction | reflexivity].
Qed.

Lemma subTermApply :
  forall (f : Functions L) (ts : fol.Terms L (arityF L f)) 
         (v : nat) (s : fol.Term L),
    substT (apply f ts) v s = apply f (substTs _ ts v s).
Proof. reflexivity. Qed.

Definition newVar (l : list nat) : nat := 
  fold_right Nat.max 0 (map S l).

Lemma newVar2 : forall (l : list nat) (n : nat), In n l -> n < newVar l.
Proof.
  induction l as [| a l Hrecl].
  - destruct 1.
  - destruct 1 as [H| H].
    + rewrite H; unfold newVar in |- *; simpl in |- *.
      induction (fold_right Nat.max 0 (map S l)).
      * apply Nat.lt_succ_diag_r .
      * apply Nat.lt_succ_r;  apply Nat.le_max_l.
    + unfold newVar in Hrecl |- *; simpl. 
      assert
        (H0: fold_right Nat.max 0 (map S l) = 0 \/
               (exists n : nat, fold_right Nat.max 0 (map S l) = S n)).
      { induction (fold_right Nat.max 0 (map S l)) as [| n0 IHn0].
        - auto.
        - right; now exists n0.
      }
      destruct H0 as [H0| [x0 H0]].
      * rewrite H0; rewrite H0 in Hrecl.
        elim (Nat.nlt_0_r n (Hrecl _ H)).
      * rewrite H0; rewrite H0 in Hrecl.
        -- apply Nat.lt_le_trans with (S x0).
           ++ now apply Hrecl.
           ++ apply le_n_S, Nat.le_max_r.
Qed.

Lemma newVar1 : forall l : list nat, ~ In (newVar l) l.
Proof.
  intros l ?; elim (Nat.lt_irrefl (newVar l)); now apply newVar2.
Qed.

Definition substituteFormulaImp (f : fol.Formula L)
  (frec : nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L f})
  (g : fol.Formula L)
  (grec : nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L g})
  (p : nat * fol.Term L) :
  {y : fol.Formula L | depth L y = depth L (impH f g)} :=
  match frec p with
  | exist f' prf1 =>
      match grec p with
      | exist g' prf2 =>
          exist
            (fun y : fol.Formula L =>
               depth L y = S (Nat.max (depth L f) (depth L g))) 
            (impH f' g')
            (eq_ind_r
               (fun n : nat =>
                  S (Nat.max n (depth L g')) =
                    S (Nat.max (depth L f) (depth L g)))
               (eq_ind_r
                  (fun n : nat =>
                     S (Nat.max (depth L f) n) =
                       S (Nat.max (depth L f) (depth L g)))
                  (refl_equal (S (Nat.max  (depth L f) (depth L g))))
                  prf2) prf1)
      end
  end.

Remark substituteFormulaImpNice :
  forall (f g : fol.Formula L)
         (z1 z2 : nat * fol.Term L ->
                  {y : fol.Formula L | depth L y = depth L f}),
    (forall q : nat * fol.Term L, z1 q = z2 q) ->
    forall
      z3 z4 : nat * fol.Term L ->
              {y : fol.Formula L | depth L y = depth L g},
      (forall q : nat * fol.Term L, z3 q = z4 q) ->
      forall q : nat * fol.Term L,
        substituteFormulaImp f z1 g z3 q =
          substituteFormulaImp f z2 g z4 q.
Proof.
  intros f g z1 z2 H z3 z4 H0 q; unfold substituteFormulaImp in |- *.
  rewrite H, H0; reflexivity. 
Qed.

Definition substituteFormulaNot (f : fol.Formula L)
  (frec : nat * fol.Term L ->
          {y : fol.Formula L | depth L y = depth L f})
  (p : nat * fol.Term L) :
  {y : fol.Formula L | depth L y = depth L (notH f)} :=
  match frec p with
  | exist f' prf1 =>
      exist (fun y : fol.Formula L => depth L y = S (depth L f)) 
        (notH f')
        (eq_ind_r (fun n : nat => S n = S (depth L f))
           (refl_equal (S (depth L f))) prf1)
  end.

Remark substituteFormulaNotNice :
  forall (f : fol.Formula L)
         (z1 z2 : nat * fol.Term L ->
                  {y : fol.Formula L | depth L y = depth L f}),
    (forall q : nat * fol.Term L, z1 q = z2 q) ->
    forall q : nat * fol.Term L,
      substituteFormulaNot f z1 q = substituteFormulaNot f z2 q.
Proof.
  intros ? ? ? H ?; unfold substituteFormulaNot in |- *;
    now rewrite H.
Qed.
    
Definition substituteFormulaForall (n : nat) (f : fol.Formula L)
  (frec : forall b : fol.Formula L,
      lt_depth b (forallH n f) ->
      nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L b})
  (p : nat * fol.Term L) :
  {y : fol.Formula L | depth L y = depth L (forallH n f)} :=
  match p with
  | (v, s) =>
      match eq_nat_dec n v with
      | left _ =>
          exist (fun y : fol.Formula L => depth L y = S (depth L f))
            (forallH n f) (refl_equal (depth L (forallH n f)))
      | right _ =>
          match In_dec eq_nat_dec n (freeVarT s) with
          | left _ =>
              let nv := newVar (v :: freeVarT s ++ freeVarF f) in
              match frec f (depthForall L f n) (n, var nv) with
              | exist f' prf1 =>
                  match
                    frec f'
                      (eqDepth L f' f (forallH n f) 
                         (sym_eq prf1) (depthForall L f n)) p
                  with
                  | exist f'' prf2 =>
                      exist
                        (fun y : fol.Formula L => depth L y = S (depth L f))
                        (forallH nv f'')
                        (eq_ind_r (fun n : nat => S n = S (depth L f))
                           (refl_equal (S (depth L f))) 
                           (trans_eq prf2 prf1))
                  end
              end
          | right _ =>
              match frec f (depthForall L f n) p with
              | exist f' prf1 =>
                  exist (fun y : fol.Formula L => depth L y = S (depth L f))
                    (forallH n f')
                    (eq_ind_r (fun n : nat => S n = S (depth L f))
                       (refl_equal (S (depth L f))) prf1)
              end
          end
      end
  end.

Remark substituteFormulaForallNice :
  forall (v : nat) (a : fol.Formula L)
         (z1 z2 : forall b : fol.Formula L,
             lt_depth b (forallH v a) ->
             nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L b}),
    (forall (b : fol.Formula L) (q : lt_depth b (forallH v a))
            (r : nat * fol.Term L), z1 b q r = z2 b q r) ->
    forall q : nat * fol.Term L,
      substituteFormulaForall v a z1 q = substituteFormulaForall v a z2 q.
Proof.
  intros v a z1 z2 H [a0 b]; unfold substituteFormulaForall in |- *.
  destruct (eq_nat_dec v a0) as [e | n] ; simpl in |- *.
  - reflexivity.
  - induction (In_dec eq_nat_dec v (freeVarT b)); simpl in |- *.
    + rewrite H;
        destruct
          (z2 a (depthForall L a v)
             (v, var (newVar
                        (a0 :: freeVarT b ++ freeVarF a)))). 
         now rewrite H.  
    + now rewrite H.
Qed.
(* begin snippet substFHelp:: no-out *)
Definition substituteFormulaHelp (f : fol.Formula L) 
  (v : nat) (s : fol.Term L) : 
  {y : fol.Formula L | depth L y = depth L f}.
(* end snippet substFHelp *)
Proof.
  apply
    (Formula_depth_rec2 L
       (fun f : fol.Formula L =>
          nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L f})).
  - intros t t0 H; induction H as (a, b).
    exists (equal (substT t a b) (substT t0 a b)); auto.
  - intros r t H; induction H as (a, b).
    exists (atomic r (substTs _ t a b)); auto.
  - exact substituteFormulaImp.
  - exact substituteFormulaNot.
  - exact substituteFormulaForall.
  - exact (v, s).
Defined.

(* begin snippet substFDef:: no-out *)
Definition substF (f : fol.Formula L) (v : nat) (s : fol.Term L) :
  fol.Formula L := proj1_sig (substituteFormulaHelp f v s).
(* end snippet substFDef:: no-out *)

(* begin snippet subFormulaEqual:: no-out *)
Lemma subFormulaEqual :
  forall (t1 t2 : fol.Term L) (v : nat) (s : fol.Term L),
    substF (t1 = t2)%fol v s =
      (substT t1 v s = substT t2 v s)%fol.
Proof. reflexivity. Qed.
(* end snippet subFormulaEqual *)

(* begin snippet subFormulaRelation:: no-out *)
Lemma subFormulaRelation :
  forall (r : Relations L) (ts : fol.Terms L (arityR L r)) 
         (v : nat) (s : fol.Term L),
    substF (atomic r ts) v s =
      atomic r (substTs (arityR L r) ts v s).
Proof. reflexivity. Qed.
(* end snippet subFormulaRelation *)

(* begin snippet subFormulaImp:: no-out *)
Lemma subFormulaImp :
  forall (f1 f2 : fol.Formula L) (v : nat) (s : fol.Term L),
    substF (f1 -> f2)%fol v s =
      (substF f1 v s -> substF f2 v s)%fol.
Proof.
(* ... *)
(* end snippet subFormulaImp *)
  intros f1 f2 v s. 
  unfold substF, substituteFormulaHelp in |- *.
  rewrite
    (Formula_depth_rec2_imp L)
    with
    (Q := 
       fun _ : fol.Formula L =>
         (nat * fol.Term L)%type)
    (P := 
       fun x : fol.Formula L =>
         {y : fol.Formula L | depth L y = depth L x}).
  unfold substituteFormulaImp at 1 in |- *.
  - induction
      (Formula_depth_rec2 L
         (fun x : fol.Formula L =>
            nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L x})
         (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
            prod_rec
              (fun _ : nat * fol.Term L =>
                 {y : fol.Formula L | depth L y = depth L (equal  t t0)})
              (fun (a : nat) (b : fol.Term L) =>
                 exist
                   (fun y : fol.Formula L => 
                      depth L y = depth L (equal t t0))
                   (equal (substT t a b) (substT t0 a b))
                   (refl_equal (depth L (equal t t0)))) H)
         (fun (r : Relations L) 
              (t : fol.Terms L (arityR L r))
              (H : nat * fol.Term L) =>
            prod_rec
              (fun _ : nat * fol.Term L =>
                 {y : fol.Formula L | depth L y = depth L (atomic r t)})
              (fun (a : nat) (b : fol.Term L) =>
                 exist
                   (fun y : fol.Formula L => depth L y = 
                                               depth L (atomic r t))
                   (atomic r (substTs (arityR L r) 
                                t a b))
                   (refl_equal (depth L (atomic r t)))) H)
         substituteFormulaImp
         substituteFormulaNot substituteFormulaForall f1 
         (v, s)).
    induction
      (Formula_depth_rec2 L
         (fun x0 : fol.Formula L =>
            nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L x0})
         (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
            prod_rec
              (fun _ : nat * fol.Term L =>
                 {y : fol.Formula L | depth L y = depth L (equal t t0)})
              (fun (a : nat) (b : fol.Term L) =>
                 exist
                   (fun y : fol.Formula L => 
                      depth L y = depth L (equal t t0))
                   (equal (substT t a b) (substT t0 a b))
                   (refl_equal (depth L (equal t t0)))) H)
         (fun (r : Relations L) 
              (t : fol.Terms L (arityR L r))
              (H : nat * fol.Term L) =>
            prod_rec
              (fun _ : nat * fol.Term L =>
                 {y : fol.Formula L | depth L y = depth L (atomic r t)})
              (fun (a : nat) (b : fol.Term L) =>
                 exist
                   (fun y : fol.Formula L => 
                      depth L y = depth L (atomic r t))
                   (atomic r (substTs (arityR L r) 
                                t a b))
                   (refl_equal (depth L (atomic r t)))) H) 
         substituteFormulaImp
         substituteFormulaNot substituteFormulaForall f2 
         (v, s)).
    reflexivity.
  - apply substituteFormulaImpNice.
  - apply substituteFormulaNotNice.
  - apply substituteFormulaForallNice.
Qed.

(* begin snippet subFormulaNot:: no-out *)
Lemma subFormulaNot :
  forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
    substF (~ f)%fol v s = (~ substF f v s)%fol.
(* end snippet subFormulaNot *)
Proof.
  intros f v s; 
  unfold substF, substituteFormulaHelp.
  rewrite (Formula_depth_rec2_not L) with
    (Q := fun _ : fol.Formula L => (nat * fol.Term L)%type)
    (P := fun x : fol.Formula L =>
         {y : fol.Formula L | depth L y = depth L x}).
  - unfold substituteFormulaNot at 1 in |- *.
    induction
      (Formula_depth_rec2 L
         (fun x : fol.Formula L =>
            nat * fol.Term L -> {y : fol.Formula L | depth L y = depth L x})
         (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
            prod_rec
              (fun _ : nat * fol.Term L =>
                 {y : fol.Formula L | depth L y = depth L (equal t t0)})
              (fun (a : nat) (b : fol.Term L) =>
                 exist
                   (fun y : fol.Formula L => depth L y = 
                                               depth L (equal t t0))
                   (equal (substT t a b) (substT t0 a b))
                   (refl_equal (depth L (equal t t0)))) H)
         (fun (r : Relations L) 
              (t : fol.Terms L (arityR L r))
              (H : nat * fol.Term L) =>
            prod_rec
              (fun _ : nat * fol.Term L =>
                 {y : fol.Formula L | depth L y = depth L (atomic r t)})
              (fun (a : nat) (b : fol.Term L) =>
                 exist
                   (fun y : fol.Formula L =>
                      depth L y = depth L (atomic r t))
                   (atomic r
                      (substTs (arityR L r) t a b))
                   (refl_equal (depth L (atomic r t)))) H)
         substituteFormulaImp
         substituteFormulaNot substituteFormulaForall f 
         (v, s)); reflexivity.
  - apply substituteFormulaImpNice.
  - apply substituteFormulaNotNice.
  - apply substituteFormulaForallNice.
Qed.
    
(* begin snippet subFormulaForall:: no-out *)
Lemma subFormulaForall :
  forall (f : fol.Formula L) (x v : nat) (s : fol.Term L),
    let nv := newVar (v :: freeVarT s ++ freeVarF f) in
    substF (allH x, f)%fol v s =
      match eq_nat_dec x v with
      | left _ => forallH x f
      | right _ =>
          match In_dec eq_nat_dec x (freeVarT s) with
          | right _ => (allH x, substF f v s)%fol
          | left _ => (allH nv, substF (substF f x (v# nv) ) v s)%fol

          end
      end.
(* end snippet subFormulaForall *)
Proof.
  intros f x v s nv.
  unfold substF at 1 in |- *.
  unfold substituteFormulaHelp in |- *.
  rewrite (Formula_depth_rec2_forall L)
    with
    (Q := 
       fun _ : fol.Formula L =>
         (nat * fol.Term L)%type)
    (P := 
       fun x : fol.Formula L =>
         {y : fol.Formula L | depth L y = depth L x}).
  - simpl in |- *; induction (eq_nat_dec x v); simpl in |- *.
    + reflexivity.
    + induction (In_dec eq_nat_dec x (freeVarT s)); simpl in |- *.
      fold nv in |- *.
      unfold substF at 2 in |- *; 
        unfold substituteFormulaHelp in |- *;
        simpl in |- *.
      * induction
          (Formula_depth_rec2 L
             (fun x0 : fol.Formula L =>
                nat * fol.Term L -> 
                {y : fol.Formula L | depth L y = depth L x0})
             (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
                prod_rec
                  (fun _ : nat * fol.Term L => 
                     {y : fol.Formula L | depth L y = 0})
                  (fun (a0 : nat) (b0 : fol.Term L) =>
                     exist (fun y : fol.Formula L => depth L y = 0)
                       (equal (substT t a0 b0) 
                          (substT t0 a0 b0))
                       (refl_equal 0)) H)
             (fun (r : Relations L) 
                  (t : fol.Terms L (arityR L r))
                  (H : nat * fol.Term L) =>
                prod_rec
                  (fun _ : nat * fol.Term L => 
                     {y : fol.Formula L | depth L y = 0})
                  (fun (a0 : nat) (b0 : fol.Term L) =>
                     exist (fun y : fol.Formula L => depth L y = 0)
                       (atomic r (substTs
                                    (arityR L r) t a0 b0))
                       (refl_equal 0)) H) substituteFormulaImp
             substituteFormulaNot
             substituteFormulaForall f (x, var nv)).
        unfold substF in |- *; unfold substituteFormulaHelp in |- *;
          simpl in |- *.
        induction
          (Formula_depth_rec2 L
             (fun x1 : fol.Formula L =>
                nat * fol.Term L -> 
                {y : fol.Formula L | depth L y = depth L x1})
             (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
                prod_rec
                  (fun _ : nat * fol.Term L => 
                     {y : fol.Formula L | depth L y = 0})
                  (fun (a0 : nat) (b0 : fol.Term L) =>
                     exist (fun y : fol.Formula L => depth L y = 0)
                       (equal (substT t a0 b0) 
                          (substT t0 a0 b0))
                       (refl_equal 0)) H)
             (fun (r : Relations L) 
                  (t : fol.Terms L (arityR L r))
                  (H : nat * fol.Term L) =>
                prod_rec
                  (fun _ : nat * fol.Term L => 
                     {y : fol.Formula L | depth L y = 0})
                  (fun (a0 : nat) (b0 : fol.Term L) =>
                     exist (fun y : fol.Formula L => depth L y = 0)
                       (atomic r (substTs 
                                    (arityR L r) t a0 b0))
                       (refl_equal 0)) H) substituteFormulaImp 
             substituteFormulaNot
             substituteFormulaForall x0 (v, s)).
        simpl in |- *; reflexivity.
      * unfold substF in |- *; unfold substituteFormulaHelp in |- *;
          simpl in |- *.
        induction
          (Formula_depth_rec2 L
             (fun x0 : fol.Formula L =>
                nat * fol.Term L -> 
                {y : fol.Formula L | depth L y = depth L x0})
             (fun (t t0 : fol.Term L) (H : nat * fol.Term L) =>
                prod_rec
                  (fun _ : nat * fol.Term L => 
                     {y : fol.Formula L | depth L y = 0})
                  (fun (a : nat) (b1 : fol.Term L) =>
                     exist (fun y : fol.Formula L => depth L y = 0)
                       (equal (substT t a b1) (substT t0 a b1))
                       (refl_equal 0)) H)
             (fun (r : Relations L) 
                  (t : fol.Terms L (arityR L r))
                  (H : nat * fol.Term L) =>
                prod_rec
                  (fun _ : nat * fol.Term L => 
                     {y : fol.Formula L | depth L y = 0})
                  (fun (a : nat) (b1 : fol.Term L) =>
                     exist (fun y : fol.Formula L => depth L y = 0)
                       (atomic r (substTs
                                    (arityR L r) t a b1))
                       (refl_equal 0)) H) substituteFormulaImp
             substituteFormulaNot
             substituteFormulaForall f (v, s)).
        simpl in |- *; reflexivity.
  - apply substituteFormulaImpNice.
  - apply substituteFormulaNotNice.
  - apply substituteFormulaForallNice.
Qed.


Section Extensions.


Lemma subFormulaOr :
  forall (f1 f2 : fol.Formula L) (v : nat) (s : fol.Term L),
    substF (f1 \/ f2)%fol v s =
      (substF f1 v s \/ substF f2 v s)%fol.
Proof.
  intros f1 f2 v s; unfold orH;
    now rewrite subFormulaImp, subFormulaNot.
Qed.

(* begin snippet subFormulaAnd:: no-out *)
Lemma subFormulaAnd :
  forall (f1 f2 : fol.Formula L) (v : nat) (s : fol.Term L),
    substF (f1 /\ f2)%fol v s =
      (substF f1 v s /\ substF f2 v s)%fol.
Proof.
  intros ? ? ? ?; unfold andH in |- *.
  rewrite subFormulaNot, subFormulaOr; 
    now repeat rewrite subFormulaNot.
Qed.
(* end snippet subFormulaAnd:: no-out *)

(* begin snippet subFormulaExist:: no-out *)
Lemma subFormulaExist :
  forall (f : fol.Formula L) (x v : nat) (s : fol.Term L),
    let nv := newVar (v :: freeVarT s ++ freeVarF f) in
    substF (existH x f) v s =
      match eq_nat_dec x v with
      | left _ => existH x f
      | right _ =>
          match In_dec eq_nat_dec x (freeVarT s) with
          | right _ => existH x (substF f v s)
          | left _ =>
              existH nv (substF 
                           (substF f x (var nv)) v s)
          end
      end.
(* end snippet subFormulaExist:: no-out *)
Proof.
  intros ? ? ? ? nv; unfold existH.
  rewrite subFormulaNot, subFormulaForall.
  destruct (eq_nat_dec x v).
  - reflexivity.
  - induction (In_dec eq_nat_dec x (freeVarT s));
      now repeat rewrite subFormulaNot.
Qed.

Lemma subFormulaIff :
  forall (f1 f2 : fol.Formula L) (v : nat) (s : fol.Term L),
    substF (iffH f1 f2) v s =
      iffH (substF f1 v s) (substF f2 v s).
Proof.
  intros ? ? v s; unfold iffH in |- *.
  rewrite subFormulaAnd; now repeat rewrite subFormulaImp.
Qed.

Lemma subFormulaIfThenElse :
  forall (f1 f2 f3 : fol.Formula L) (v : nat) (s : fol.Term L),
    substF (ifThenElseH f1 f2 f3) v s =
      ifThenElseH (substF f1 v s) (substF f2 v s)
        (substF f3 v s).
Proof.
  intros ? ? ? ? ?; unfold ifThenElseH.
  now rewrite subFormulaAnd, !subFormulaImp,  subFormulaNot.
Qed.

End Extensions.

Lemma subFormulaDepth :
  forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
    depth L (substF f v s) = depth L f.
Proof.
  intros f v s; unfold substF in |- *.
  induction (substituteFormulaHelp f v s) as [x p]; now simpl. 
Qed.

Section Substitution_Properties.

Lemma subTermId :
  forall (t : fol.Term L) (v : nat), substT t v (var v) = t.
Proof.
  intros ? ?; 
    elim t using Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             substTs n ts v (var v) = ts).
  - simpl in |- *; intros n.
    induction (eq_nat_dec v n) as [a | b].
    + now rewrite a.
    + reflexivity.
  -  intros f t0 H; simpl in |- *; now rewrite H.
  -  reflexivity.
  -  intros ? ? H t1 H0; simpl in |- *; now rewrite H, H0. 
Qed.

Lemma subTermsId :
  forall (n : nat) (ts : fol.Terms L n) (v : nat),
    substTs n ts v (var v) = ts.
Proof.
  intros n ts v; induction ts as [| n t ts Hrects].
  - reflexivity. 
  - simpl in |- *;  now rewrite Hrects,  subTermId.
Qed.

Lemma subFormulaId :
  forall (f : fol.Formula L) (v : nat), substF f v (var v) = f.
Proof.
  intros f v.
  induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf].
  - now rewrite subFormulaEqual, !subTermId.
  - now rewrite subFormulaRelation, subTermsId.
  - now rewrite subFormulaImp, Hrecf1,  Hrecf0.
  - now rewrite subFormulaNot, Hrecf.
  - rewrite subFormulaForall; destruct  (eq_nat_dec n v) as [e|ne].
    + reflexivity.
    + induction (In_dec eq_nat_dec n (freeVarT (var v))) as [a|b].
      * elim ne; destruct a as [H| H].
        -- now subst.
        -- destruct H.
      * now rewrite Hrecf.
Qed.

Lemma subFormulaForall2 :
  forall (f : fol.Formula L) (x v : nat) (s : fol.Term L),
  exists nv : nat,
    ~ In nv (freeVarT s) /\
      nv <> v /\
      ~ In nv (remove  eq_nat_dec x (freeVarF f)) /\
      substF (forallH x f) v s =
        match eq_nat_dec x v with
        | left _ => forallH x f
        | right _ =>
            forallH nv (substF (substF f x (var nv)) v s)
        end.
Proof.
  intros f x v s; rewrite subFormulaForall.
  induction (eq_nat_dec x v) as [a | b].
  - set
      (A1 :=
         v :: freeVarT s ++ remove eq_nat_dec x (freeVarF f)) 
      in *.
    exists (newVar A1); repeat split.
    + unfold not in |- *; intros; elim (newVar1 A1).
      unfold A1 in |- *; right.
      apply in_or_app; auto.
    + unfold not in |- *; intros; elim (newVar1 A1).
      rewrite H; left; auto.
    + unfold not in |- *; intros; elim (newVar1 A1).
      right; apply in_or_app; auto.
  - induction (In_dec eq_nat_dec x (freeVarT s)) as [a | b0].
    + set (A1 := v :: freeVarT s ++ freeVarF f) in *.
      exists (newVar A1); repeat split.
      * unfold not in |- *; intros; elim (newVar1 A1); right.
        apply in_or_app; auto.
      * unfold not in |- *; intros; elim (newVar1 A1); rewrite H; left; auto.
      * unfold not in |- *; intros; elim (newVar1 A1); right;  apply in_or_app.
        right; eapply in_remove; apply H.
    + exists x; repeat split; auto.
      intro H; eapply (in_remove_neq _ _ _ _ _ H).
      * reflexivity.
      * now rewrite subFormulaId.
Qed.


Lemma subFormulaExist2 :
  forall (f : fol.Formula L) (x v : nat) (s : fol.Term L),
  exists nv : nat,
    ~ In nv (freeVarT s) /\
      nv <> v /\
      ~ In nv (remove eq_nat_dec x (freeVarF f)) /\
      substF (existH x f) v s =
        match eq_nat_dec x v with
        | left _ => existH x f
        | right _ =>
            existH nv (substF (substF f x (var nv)) v s)
        end.
Proof.
  intros f x v s; rewrite subFormulaExist.
  induction (eq_nat_dec x v) as [a | b].
  - set
      (A1 :=
         v :: freeVarT s ++ remove eq_nat_dec x (freeVarF f)) 
      in *.
    exists (newVar A1); repeat split.
    + unfold not in |- *; intros; elim (newVar1 A1).
      unfold A1 in |- *; right; apply in_or_app; auto.
    + unfold not in |- *; intros; elim (newVar1 A1); rewrite H; now left.
    + unfold not in |- *; intros; elim (newVar1 A1); right; apply in_or_app; 
        auto.
  - induction (In_dec eq_nat_dec x (freeVarT s)) as [a | b0].
    + set (A1 := v :: freeVarT s ++ freeVarF f) in *.
      exists (newVar A1);  repeat split.
      * unfold not in |- *; intros; elim (newVar1 A1); right; apply in_or_app; auto.
      * unfold not in |- *; intros; elim (newVar1 A1); rewrite H; left; auto.
      * unfold not in |- *; intros; elim (newVar1 A1); right;  apply in_or_app.
        right; eapply in_remove; apply H.
    + exists x; repeat split; auto.
      intros H; eapply (in_remove_neq _ _ _ _ _ H).
      * reflexivity.
      * rewrite subFormulaId; auto.
Qed.

End Substitution_Properties.

End Substitution.
  
Definition Sentence (f:Formula) := 
   (forall v : nat, ~ In v (freeVarF f)).

End Fol_Properties.

Arguments closed {L} _.

#[global] Arguments substF {L} _ _.
#[global] Arguments substT {L} _ _.
#[global] Arguments substTs {L n} _ _ _ .
(** compatibility with older names *)

#[deprecated(note="use substF")]
 Notation substituteFormula := substF  (only parsing).
(* to do *)

#[deprecated(note="use substT")]
 Notation substituteTerm := substT (only parsing).

#[deprecated(note="use substTs")]
 Notation substituteTerms := substTs (only parsing).

#[deprecated(note="use freeVarF")]
 Notation freeVarFormula := freeVarF (only parsing).

#[deprecated(note="use freeVarT")]
 Notation freeVarTerm := freeVarT (only parsing).

#[deprecated(note="use freeVarTs")]
 Notation freeVarTerms := freeVarTs (only parsing).

(* begin snippet substLemmas *)
About substF.
Search substF.
(* end snippet substLemmas *)

(** to replace with a single recursive custom notation ? *)

#[global] Notation substF2 e v1 t1 v2 t2 :=
  (substF (substF e v1 t1) v2 t2).

#[global] Notation substF3 e v1 t1 v2 t2 v3 t3 :=
  (substF (substF2 e v1 t1 v2 t2) v3 t3).

#[global] Notation substF4 e v1 t1 v2 t2 v3 t3 v4 t4 :=
  (substF (substF3 e v1 t1 v2 t2 v3 t3) v4 t4).

#[global] Notation substF5 e v1 t1 v2 t2 v3 t3 v4 t4 v5 t5 :=
  (substF (substF4 e v1 t1 v2 t2 v3 t3 v4 t4) v5 t5).

#[global] Notation substF6 e v1 t1 v2 t2 v3 t3 v4 t4 v5 t5 v6 t6 :=
  (substF (substF5 e v1 t1 v2 t2 v3 t3 v4 t4 v5 t5) v6 t6).

#[global] Notation substF7 e v1 t1 v2 t2 v3 t3 v4 t4 v5 t5 v6 t6 v7 t7:=
  (substF (substF6 e v1 t1 v2 t2 v3 t3 v4 t4 v5 t5 v6 t6) v7 t7).

#[global] Notation
  substF8 e v1 t1 v2 t2 v3 t3 v4 t4 v5 t5 v6 t6 v7 t7 v8 t8 :=
  (substF2 (substF6 e v1 t1 v2 t2 v3 t3 v4 t4 v5 t5 v6 t6)
     v7 t7 v8 t8).

#[global] Notation
  substF9 e v1 t1 v2 t2 v3 t3 v4 t4 v5 t5 v6 t6 v7 t7 v8 t8 v9 t9:=
  (substF3 (substF6 e v1 t1 v2 t2 v3 t3 v4 t4 v5 t5 v6 t6)
     v7 t7 v8 t8 v9 t9).

About freeVarF.

#[global] Arguments freeVarF {L} _.

