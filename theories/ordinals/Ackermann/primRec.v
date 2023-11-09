(** Primitive Recursive functions *)
(** Russel O'Connor *)

Require Import Arith.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Coq.Lists.List.
Require Import Eqdep_dec.
Require Import Utf8.
From hydras Require Import extEqualNat misc Compat815.
Require Vector.

Require Export Bool.
Require Export EqNat.
Require Import Lia. 


(** * Definitions *)

(** [PrimRec n] : data type of primitive recursive functions of arity [n] 
    [PrimRec n m] : m-tuples of [PrimRec n] *)

(* begin snippet PrimRecDef *)

Inductive PrimRec : nat -> Set :=
  | succFunc : PrimRec 1
  | zeroFunc : PrimRec 0
  | projFunc : forall n m : nat, m < n -> PrimRec n
  | composeFunc :
      forall (n m : nat) (g : PrimRecs n m) (h : PrimRec m),
        PrimRec n
  | primRecFunc :
      forall (n : nat) (g : PrimRec n) (h : PrimRec (S (S n))),
        PrimRec (S n)
with PrimRecs : nat -> nat -> Set :=
  | PRnil : forall n : nat, PrimRecs n 0
  | PRcons : forall n m : nat, PrimRec n -> PrimRecs n m ->
                               PrimRecs n (S m).

(* end snippet PrimRecDef *)

(* begin snippet PRNotations *)

Module PRNotations.
  Declare Scope pr_scope.
  Delimit Scope pr_scope with pr.
  (* Notation "[ ]" := (PRnil _) : pr_scope. *)
  Notation "h :: t" := (PRcons _ _ h t) (at level 60, right associativity)
  : pr_scope.
  Notation "[ x ]" := (PRcons _ _ x  (PRnil _)) : pr_scope.

  Notation "[ x ; y ; .. ; z ]" := 
    (PRcons _ _ x  (PRcons _ _ y .. (PRcons _ _ z  (PRnil _)) ..)) : pr_scope.


  Notation PRcomp f v := (composeFunc _ _ v f).
  
  Notation PRrec f0 fS := (primRecFunc _ f0 fS).

  Notation "f '=x=' g" := (extEqual _ f g) (at level 70, no associativity).
(** Popular projections *)


Notation pi1_1 := (projFunc 1 0 (le_n 1)).

Notation pi1_2 := (projFunc 2 1 (le_n 2)).
Notation pi2_2 := (projFunc 2 0 (le_S 1 1 (le_n 1))).

Notation pi1_3 := (projFunc 3 2 (le_n 3)).
Notation pi2_3 := (projFunc 3 1 (le_S 2 2 (le_n 2))).
Notation pi3_3 := (projFunc 3 0 (le_S 1 2 (le_S 1 1 (le_n 1)))).


End PRNotations. 

(* end snippet PRNotations *)

Import PRNotations.


Scheme PrimRec_PrimRecs_rec := Induction for PrimRec Sort Set
  with PrimRecs_PrimRec_rec := Induction for PrimRecs  Sort Set.

Arguments PrimRec_PrimRecs_rec P P0 : rename.
Arguments PrimRecs_PrimRec_rec P P0 : rename.

(* begin snippet SchemePrimRecInd *)

Scheme PrimRec_PrimRecs_ind := Induction for PrimRec Sort Prop
    with PrimRecs_PrimRec_ind := Induction for PrimRecs  Sort Prop.

Arguments PrimRec_PrimRecs_ind P P0 : rename.
Arguments PrimRecs_PrimRec_ind P P0 : rename.
(* end snippet SchemePrimRecInd *)

(* begin snippet SchemePrimRecInda *)
Check PrimRec_PrimRecs_ind.
(* end snippet SchemePrimRecInda *)


(** ** Semantics *)

(** *** Constants *)

Fixpoint evalConstFunc (n m : nat) {struct n} : naryFunc n :=
  match n return (naryFunc n) with
  | O => m
  | S n' => fun _ => evalConstFunc n' m
  end.

(** *** Projections 
   The parameters are number in opposite order.
   So proj(2,0)(a,b) = b. *)

Fixpoint evalProjFunc (n : nat) :
  forall m : nat, m < n -> naryFunc n :=
  match n return (forall m : nat, m < n -> naryFunc n) with
  | O => fun (m : nat) (l : m < 0) => False_rec _ (Nat.nlt_0_r _ l)
  | S n' =>
      fun (m : nat) (l : m < S n') =>
      match eq_nat_dec m n' with
      | left _ => fun a : nat => evalConstFunc _ a
      | right l1 =>
          fun _ =>
          evalProjFunc n' m
            match Compat815.le_lt_or_eq _ _
                    (Compat815.lt_n_Sm_le _ _ l) with
            | or_introl l2 => l2
            | or_intror l2 => False_ind _ (l1 l2)
            end
      end
  end.

(** Irrelevance of the proof that [m < n] *)

Lemma evalProjFuncInd :
 forall (n m : nat) (p1 p2 : m < n),
 evalProjFunc n m p1 = evalProjFunc n m p2.
Proof.
induction n as [| n Hrecn].
- intros; destruct (Nat.nlt_0_r _ p1).
- intros; cbn in |- *; destruct (eq_nat_dec m n) as [e|ne].
  + reflexivity.
  + rewrite
      (Hrecn _
             match Compat815.le_lt_or_eq m n (Compat815.lt_n_Sm_le m n p1) with
             | or_introl l2 => l2
             | or_intror l2 => False_ind (m < n) (ne l2)
             end
             match Compat815.le_lt_or_eq m n (Compat815.lt_n_Sm_le m n p2) with
             | or_introl l2 => l2
             | or_intror l2 => False_ind (m < n) (ne l2)
             end);
      reflexivity.
Qed.

(**  Applies an m-ary function to the vector l *)

(* begin snippet evalListDef *)

Fixpoint evalList (m : nat) (l : Vector.t nat m) {struct l} :
  naryFunc m -> nat :=
  match l  in (Vector.t _ m) return (naryFunc m -> nat) with
  | Vector.nil => fun x : naryFunc 0 => x
  | Vector.cons a n l' =>
    fun x : naryFunc (S n) => evalList n l' (x a)
  end.

(* end snippet evalListDef *)


Fixpoint evalOneParamList (n m a : nat) (l : Vector.t (naryFunc (S n)) m)
 {struct l} : Vector.t (naryFunc n) m :=
  match l in (Vector.t _ m) return (Vector.t (naryFunc n) m) with
  | Vector.nil  => Vector.nil  (naryFunc n)
  | Vector.cons f m' l' =>
      Vector.cons _ (f a) m' (evalOneParamList n m' a l')
  end.

(** *** Function composition *)

Fixpoint evalComposeFunc (n : nat) :
  forall m : nat,
    Vector.t (naryFunc n) m -> naryFunc m -> naryFunc n :=
  match
    n
    return
    (forall m : nat,
        Vector.t (naryFunc n) m -> naryFunc m -> naryFunc n)
  with
  | O => evalList
  | S n' =>
      fun (m : nat) (l : Vector.t (naryFunc (S n')) m) 
          (f : naryFunc m) (a : nat) =>
        evalComposeFunc n' m (evalOneParamList _ _ a l) f
  end.

Fixpoint compose2 (n : nat) :
  naryFunc n -> naryFunc (S n) -> naryFunc n :=
  match n return (naryFunc n -> naryFunc (S n) -> naryFunc n) with
  | O => fun (a : nat) (g : nat -> nat) => g a
  | S n' =>
      fun (f : naryFunc (S n')) (g : naryFunc (S (S n'))) (a : nat) =>
        compose2 n' (f a) (fun x : nat => g x a)
  end.

(** *** Primitive recursion *)

Fixpoint evalPrimRecFunc (n : nat) (g : naryFunc n) 
 (h : naryFunc (S (S n))) (a : nat) {struct a} : naryFunc n :=
  match a with
  | O => g
  | S a' => compose2 _ (evalPrimRecFunc n g h a') (h a')
  end.

(**  The interpretation function *)

(* begin snippet evalPrimRecDef *)

Fixpoint evalPrimRec (n : nat) (f : PrimRec n) {struct f} : 
 naryFunc n :=
  match f in (PrimRec n) return (naryFunc n) with
  | succFunc => S
  | zeroFunc => 0
  | projFunc n m pf => evalProjFunc n m pf
  | composeFunc n m l f =>
      evalComposeFunc n m (evalPrimRecs _ _ l) (evalPrimRec _ f)
  | primRecFunc n g h =>
      evalPrimRecFunc n (evalPrimRec _ g) (evalPrimRec _ h)
  end
 
 with evalPrimRecs (n m : nat) (fs : PrimRecs n m) {struct fs} :
 Vector.t (naryFunc n) m :=
  match fs in (PrimRecs n m) return (Vector.t (naryFunc n) m) with
  | PRnil a => Vector.nil  (naryFunc a)
  | PRcons a b g gs =>
    Vector.cons _ (evalPrimRec _ g) _ (evalPrimRecs _ _ gs)
  end.

Notation PReval f := (evalPrimRec _ f).
Notation PRevalN fs := (evalPrimRecs _ _ fs).

(* end snippet evalPrimRecDef *)

Definition extEqualVectorGeneral (n m : nat) (l : Vector.t (naryFunc n) m) :
  forall (m' : nat) (l' : Vector.t (naryFunc n) m'), Prop.
  induction l as [| a n0 l Hrecl].
  - intros  m' [| a n0 v]; [exact True | exact False].
  - intros m' [| a0 n1 v]. 
    + exact False.
    + exact (extEqual n a a0 /\ Hrecl _ v).
Defined.

(** Every element of l is extensionally equal to the element of l' at the same position *)

Definition extEqualVector n:
  forall m (l l' : Vector.t (naryFunc n) m), Prop.
Proof.
  refine (@Vector.rect2 _ _ _ _ _); intros.
  - exact True.
  - exact (a =x= b /\ X).
Defined.

Lemma extEqualVectorRefl (n m: nat):
  forall (l : Vector.t (naryFunc n) m), extEqualVector n m l l.
Proof.
  induction l as [| a n0 l Hrecl].
  - now simpl.
  - split; [apply extEqualRefl | apply Hrecl].
Qed.

Lemma extEqualOneParamList :
  forall (n m : nat) (l1 l2 : Vector.t (naryFunc (S n)) m) (c : nat),
    extEqualVector (S n) m l1 l2 ->
    extEqualVector n m (evalOneParamList n m c l1)
      (evalOneParamList n m c l2).
Proof.
  intro n; refine (@Vector.rect2 _ _ _ _ _); simpl; [trivial|].   
  - intros ? ? ? H ? ? ?  [H0 H1]; split; [apply H0 | now apply H].
Qed.

Lemma extEqualCompose :
  forall (n m : nat) (l1 l2 : Vector.t (naryFunc n) m)
         (f1 f2 : naryFunc m),
    extEqualVector n m l1 l2 ->
    f1 =x= f2 ->
    evalComposeFunc n m l1 f1 =x= evalComposeFunc n m l2 f2.
Proof.
  induction n; refine (@Vector.rect2 _ _ _ _ _); simpl; intros.
  - assumption.
  - destruct H0; now (apply H; [|subst a]). 
  - rewrite H0; apply extEqualRefl.
  - destruct H0 as (Hi, Hj).
    + apply IHn; [split | auto]. 
      * apply Hi.
      * now apply extEqualOneParamList.
Qed.

Lemma extEqualCompose2 :
  forall (n : nat) (f1 f2 : naryFunc n),
     f1 =x= f2 ->
    forall g1 g2 : naryFunc (S n),
       g1 =x= g2 ->
       compose2 n f1 g1 =x= compose2 n f2 g2.
Proof.
  induction n as [| n Hrecn]; simpl in |- *; intros.
  - rewrite H; apply H0.
  - apply Hrecn; simpl in |- *; intros; auto.
Qed.

Lemma extEqualPrimRec :
  forall (n : nat) (g1 g2 : naryFunc n) (h1 h2 : naryFunc (S (S n))),
     g1 =x= g2 -> h1 =x= h2 ->
       (evalPrimRecFunc n g1 h1: naryFunc (S n)) =x=
         evalPrimRecFunc n g2 h2.
Proof.
  intros;  simpl in |- *;  intros.
  induction c as [| c Hrecc].
  - simpl in |- *; auto.
  - simpl in |- *.
    cut (extEqual n (evalPrimRecFunc n g1 h1 c)
           (evalPrimRecFunc n g2 h2 c)).
    + cut (extEqual (S n) (h1 c) (h2 c)).
      * generalize (h1 c) (h2 c) (evalPrimRecFunc n g1 h1 c)
                   (evalPrimRecFunc n g2 h2 c).
        fold (naryFunc (S n)) in |- *.
        clear Hrecc H0 h1 h2 g1 g2 H.
        induction n as [| n Hrecn].
        -- simpl in |- *; intros; rewrite H0; apply H.
        -- simpl in |- *; intros; apply Hrecn.
           ++ simpl in |- *;  intros; apply H.
           ++  apply H0.
      * simpl in |- *; intros; apply H0.
    + auto.
Qed.

(** ** Predicates "to be primitive recursive"  *)

(* begin snippet isPRDef *)
Class isPR (n : nat) (f : naryFunc n) : Set :=
  is_pr : {p : PrimRec n | extEqual n (PReval p) f}.

Definition fun2PR {n:nat}(f:  naryFunc n)
  {p: isPR _ f}: PrimRec n := proj1_sig p.

Class isPRrel (n : nat) (R : naryRel n) : Set :=
  is_pr_rel: isPR n (charFunction n R).
(* end snippet isPRDef *)





(* begin snippet SuccIsPR:: no-out *)
#[export] Instance succIsPR : isPR 1 S.
Proof. exists succFunc; cbn; reflexivity. Qed.
(* end snippet SuccIsPR *)

#[export] Instance const0_NIsPR (n:nat): isPR 0 n.
Proof.
  induction n as [|n [x Hx]].
  - exists zeroFunc; reflexivity. 
  - exists (PRcomp succFunc [x]%pr)%pr; cbn; now rewrite Hx.
Qed.

#[export] Instance const1_NIsPR n: isPR 1 (fun _ => n).
Proof.
  destruct (const0_NIsPR n) as [x Hx]. 
  exists (PRcomp x (PRnil 1))%pr;  cbn in *; auto.
Qed.

(** ** Usual projections (in curried form) are primitive recursive *)

(* begin snippet idIsPR:: no-out *)
#[export] Instance idIsPR : isPR 1 (fun x : nat => x).
Proof.
  exists pi1_1; cbn; reflexivity.
Qed.
(* end snippet idIsPR *)

#[export] Instance pi1_2IsPR : isPR 2 (fun a b : nat => a).
Proof.
  exists pi1_2; cbn; reflexivity.
Qed.

#[export] Instance pi2_2IsPR : isPR 2 (fun a b : nat => b).
Proof.
  assert (H: 0 < 2) by auto.
  exists (projFunc _ _ H); cbn; reflexivity.
Qed.

#[export] Instance pi1_3IsPR : isPR 3 (fun a b c : nat => a).
Proof.
  assert (H: 2 < 3) by auto.
  exists (projFunc _ _ H); cbn in |- *; reflexivity.
Qed.

#[export] Instance pi2_3IsPR : isPR 3 (fun a b c : nat => b).
Proof.
  assert (H: 1 < 3) by auto.
  exists (projFunc _ _ H); cbn; reflexivity.
Qed.

#[export] Instance pi3_3IsPR : isPR 3 (fun a b c : nat => c).
Proof.
  assert (H: 0 < 3) by auto.
  exists (projFunc _ _ H);  cbn; reflexivity.
Qed.

#[export] Instance pi1_4IsPR : isPR 4 (fun a b c d : nat => a).
Proof.
  assert (H: 3 < 4) by auto.
  exists (projFunc _ _ H); cbn ; reflexivity.
Qed.

#[export] Instance pi2_4IsPR : isPR 4 (fun a b c d : nat => b).
Proof.
  assert (H: 2 < 4) by auto.
  exists (projFunc _ _ H); cbn ; reflexivity.
Qed.

#[export] Instance pi3_4IsPR : isPR 4 (fun a b c d : nat => c).
Proof.
  assert (H: 1 < 4) by auto.
  exists (projFunc _ _ H); cbn; reflexivity.
Qed.

#[export] Instance pi4_4IsPR : isPR 4 (fun a b c d : nat => d).
Proof.
  assert (0 < 4) by auto.
  exists (projFunc _ _ H); cbn; reflexivity.
Qed.

(** ** Composition lemmas *)

#[export] Instance filter01IsPR (g : nat -> nat) (H : isPR 1 g):
  isPR 2 (fun a b : nat => g b).
Proof.
  destruct H as [x p]; cbn in p.
  assert (H: isPR 2 (fun a b : nat => b)) by apply pi2_2IsPR.
  destruct H as [x0 p0]; cbn in p0. 
  exists (PRcomp x [x0])%pr.
  simpl in |- *; intros.
  replace (g c0) with (g (PReval x0 c c0)); auto.  
Qed.

#[export] Instance filter10IsPR (g : nat -> nat) (H: isPR 1 g):
  isPR 2 (fun a b : nat => g a).
Proof.
  destruct H as [x p]; cbn in p. 
  assert (H: isPR 2 (fun a b : nat => a)) by apply  pi1_2IsPR.
  destruct  H as [x0 p0]; cbn in p0.
  exists (PRcomp x [x0])%pr.
  cbn; intros; replace (g c) with (g (PReval x0 c c0)); auto. 
Qed.

#[export] Instance filter100IsPR(g : nat -> nat)(H: isPR 1 g) :
  isPR 3 (fun a b c : nat => g a).
Proof.
  destruct H as [x p]; cbn in p.
  assert (H: isPR 3 (fun a b c : nat => a)) by apply pi1_3IsPR.
  destruct H as [x0 p0]; cbn in p0.
  exists (PRcomp x [x0])%pr.
  cbn; intros c c0 c1;
    replace (g c) with (g (PReval x0 c c0 c1)); auto. 
Qed.


#[export] Instance filter010IsPR (g : nat -> nat)(H: isPR 1 g):
  isPR 3 (fun a b c : nat => g b).
Proof.
  destruct H as  [x p]; cbn in p.
  assert (H:isPR 3 (fun a b c : nat => b)) by apply pi2_3IsPR.
  destruct H as [x0 p0]; cbn in p0.
  exists (PRcomp x [x0])%pr.
  red; intros; replace (g c0) with (g (PReval x0 c c0 c1)).
  - rewrite <- p; auto.
  - rewrite p0; auto.
Qed.

#[export] Instance filter001IsPR (g:nat -> nat)(H: isPR 1 g) :
 isPR 3 (fun a b c : nat => g c).
Proof.
  destruct H as [x p]; cbn in p. 
  assert (H: isPR 3 (fun a b c : nat => c)) by apply pi3_3IsPR.
  destruct H as [x0 p0]; cbn in p0.
  exists (PRcomp x [x0])%pr.
  cbn; intros; replace (g c1) with (g (evalPrimRec 3 x0 c c0 c1)).
  - rewrite <- p; auto.
  - rewrite p0; auto.
Qed.

#[export] Instance filter011IsPR (g: nat -> nat -> nat)(H: isPR 2 g):
   isPR 3 (fun a b c : nat => g b c).
Proof.
   destruct H as [x p]; cbn in p. 
   assert (H: isPR 3 (fun a b c : nat => b)) by apply pi2_3IsPR.
   destruct H as [x0 p0]; cbn  in p0.
   assert (H: isPR 3 (fun a b c : nat => c)) by apply pi3_3IsPR.
   destruct  H as [x1 p1]; cbn in p1. 
   exists (PRcomp x [x0; x1]%pr).
   cbn in *; intros;
     replace (g c0 c1) with
     (g (evalPrimRec 3 x0 c c0 c1) (evalPrimRec 3 x1 c c0 c1));
     auto. 
Qed.

#[export] Instance filter110IsPR(g : nat -> nat -> nat) :
  isPR 2 g -> isPR 3 (fun a b c : nat => g a b).
Proof.
   intros [x p]; cbn in p. 
   assert (H: isPR 3 (fun a b c : nat => a)) by apply pi1_3IsPR.
   destruct H as [x0 p0]; cbn in p0.
   assert (H: isPR 3 (fun a b c : nat => b)) by apply pi2_3IsPR.
   destruct H as [x1 p1]; cbn in p1.
   exists (PRcomp x [x0; x1])%pr.
   cbn; intros; 
     replace (g c c0) with
         (g (evalPrimRec 3 x0 c c0 c1) (evalPrimRec 3 x1 c c0 c1)).
   - rewrite <- p; auto.
   - rewrite p0, p1; auto.
Qed.


#[export] Instance filter101IsPR :
  forall g : nat -> nat -> nat, isPR 2 g ->
                                isPR 3 (fun a b c : nat => g a c).
Proof.
  intros g [x p]; cbn in p.
  assert (H: isPR 3 (fun a b c : nat => a)) by apply pi1_3IsPR.
  destruct  H as [x0 p0]; cbn in p0.
  assert (H: isPR 3 (fun a b c : nat => c)) by apply pi3_3IsPR.
  destruct H as [x1  p1]; cbn in p1. 
  exists (PRcomp x [x0; x1])%pr.
  cbn; intros;
    replace (g c c1) with
        (g (evalPrimRec 3 x0 c c0 c1) (evalPrimRec 3 x1 c c0 c1)).
  - rewrite <- p; auto.
  - rewrite p0, p1; auto. 
Qed.

#[export] Instance filter0011IsPR (g : nat -> nat -> nat) :
  isPR 2 g -> isPR 4 (fun a b c d : nat => g c d).
Proof.
  intros [x p]; cbn in p.
  assert (H: isPR 4 (fun a b c d : nat => c)) by apply pi3_4IsPR.
  destruct  H as [x0 p0]; cbn in p0.
  assert (H: isPR 4 (fun a b c d : nat => d)) by apply pi4_4IsPR.
  destruct  H as [x1 p1]; cbn in p1.
  exists (PRcomp x [x0; x1])%pr.
  cbn; intros; replace (g c1 c2) with
    (g (evalPrimRec 4 x0 c c0 c1 c2) (evalPrimRec 4 x1 c c0 c1 c2)).
  - rewrite <- p; auto.
  - rewrite p0, p1; auto.
Qed.

#[export] Instance filter1000IsPR (g : nat -> nat):
  isPR 1 g -> isPR 4 (fun a b c d : nat => g a).
Proof.
  intros [x p]; cbn  in p.
  assert (H:isPR 4 (fun a b c d : nat => a)) by apply pi1_4IsPR.
  destruct H as [x0 p0]; cbn  in p0.
  exists (PRcomp x [x0])%pr.
  cbn; intros; replace (g c) with (g (evalPrimRec 4 x0 c c0 c1 c2)).
  - rewrite <- p; auto.
  - rewrite p0; auto.
Qed.


#[export] Instance filter1011IsPR (g : nat -> nat -> nat -> nat) :
 isPR 3 g -> isPR 4 (fun a b c d : nat => g a c d).
Proof.
  intros [x p]; cbn  in p.
  assert (H: isPR 4 (fun a b c d : nat => a)) by apply pi1_4IsPR.
  assert (H0: isPR 4 (fun a b c d : nat => c)) by apply pi3_4IsPR.
  assert (H1 :isPR 4 (fun a b c d : nat => d)) by apply pi4_4IsPR.
  destruct H as [x0 p0];
    destruct H0 as [x1 p1];
     destruct H1 as [x2 p2]; cbn in p0, p1, p2.
  exists (PRcomp x [x0; x1; x2])%pr.  
  cbn; intros; 
    replace (g c c1 c2) with
        (g (evalPrimRec 4 x0 c c0 c1 c2) (evalPrimRec 4 x1 c c0 c1 c2)
           (evalPrimRec 4 x2 c c0 c1 c2)).
  - rewrite <- p; auto.
  - rewrite p0; auto.
Qed.

#[export] Instance filter1100IsPR (g : nat -> nat -> nat) :
  isPR 2 g -> isPR 4 (fun a b c d : nat => g a b).
Proof.
  intros [x p]; cbn in p.
  assert (H: isPR 4 (fun a b c d : nat => a)) by apply pi1_4IsPR.
  assert (H0: isPR 4 (fun a b c d : nat => b)) by apply pi2_4IsPR.
  destruct  H as [x0 p0]; cbn in p0.
  destruct  H0 as [x1 p1]; cbn in p1.
  exists (PRcomp x [x0; x1])%pr.
  cbn; intros.
  replace (g c c0) with
      (g (evalPrimRec 4 x0 c c0 c1 c2) (evalPrimRec 4 x1 c c0 c1 c2)).
  - rewrite <- p; auto.
  - auto.
Qed.

#[export] Instance compose1_1IsPR (f : nat -> nat):
  isPR 1 f ->
  forall g : nat -> nat, isPR 1 g -> isPR 1 (fun x : nat => g (f x)).
Proof.
  intros [x p] g [x0 p0]; cbn in *;
  exists (PRcomp x0 [x])%pr. 
  cbn; intros; now rewrite <- p, p0.
Qed.

#[export] Instance compose1_2IsPR :
  forall f : nat -> nat,
    isPR 1 f ->
    forall f' : nat -> nat,
      isPR 1 f' ->
      forall g : nat -> nat -> nat,
        isPR 2 g -> isPR 1 (fun x : nat => g (f x) (f' x)).
Proof.
  intros f [x p] f' [x0 p0] g [x1 p1]; cbn in p, p0, p1.
  exists (PRcomp x1 [x; x0])%pr; cbn in *.
  intros; now rewrite <- p, p0, p1.
Qed.

#[export] Instance compose1_3IsPR :
 forall f1 : nat -> nat,
 isPR 1 f1 ->
 forall f2 : nat -> nat,
 isPR 1 f2 ->
 forall f3 : nat -> nat,
 isPR 1 f3 ->
 forall g : nat -> nat -> nat -> nat,
 isPR 3 g -> isPR 1 (fun x : nat => g (f1 x) (f2 x) (f3 x)).
Proof.
  intros f1 [x p] f2 [x0 p0] f3 [x1 p1] g [x2 p2];
    cbn in p, p0, p1, p2.
  exists (PRcomp x2 [x; x0; x1])%pr; cbn in |- *.
  intros; now rewrite <- p, p0, p1, p2.
Qed.

#[export] Instance compose2_1IsPR :
  forall f : nat -> nat -> nat,
    isPR 2 f ->
    forall g : nat -> nat, isPR 1 g ->
                           isPR 2 (fun x y : nat => g (f x y)).
Proof.
  intros f [x p] g [x0 p0]; cbn in p, p0.
  exists (PRcomp x0 [x])%pr; cbn.
  intros; now rewrite <- p, p0.
Qed.

#[export] Instance compose2_2IsPR :
 forall f : nat -> nat -> nat,
 isPR 2 f ->
 forall g : nat -> nat -> nat,
 isPR 2 g ->
 forall h : nat -> nat -> nat,
 isPR 2 h -> isPR 2 (fun x y : nat => h (f x y) (g x y)).
Proof.
  intros f [x p] g [x0 p0] h [x1 p1]; cbn in p, p0, p1.
  exists (PRcomp x1 [x; x0])%pr; 
  cbn in *; intros; now rewrite <- p, p0, p1. 
Qed.

#[export] Instance compose2_3IsPR :
  forall f1 : nat -> nat -> nat,
    isPR 2 f1 ->
    forall f2 : nat -> nat -> nat,
      isPR 2 f2 ->
      forall f3 : nat -> nat -> nat,
        isPR 2 f3 ->
        forall g : nat -> nat -> nat -> nat,
          isPR 3 g ->
          isPR 2 (fun x y : nat => g (f1 x y) (f2 x y) (f3 x y)).
Proof.
  intros  f1 [x p] f2 [x0 p0] f3 [x1 p1] g [x2 p2]; cbn in p, p0, p1, p2.
  exists
    (PRcomp x2 [x; x0; x1])%pr; cbn in *; 
    intros; now rewrite <- p, p0, p1, p2. 
Qed.

#[export] Instance compose2_4IsPR :
 forall f1 : nat -> nat -> nat,
 isPR 2 f1 ->
 forall f2 : nat -> nat -> nat,
 isPR 2 f2 ->
 forall f3 : nat -> nat -> nat,
 isPR 2 f3 ->
 forall f4 : nat -> nat -> nat,
 isPR 2 f4 ->
 forall g : nat -> nat -> nat -> nat -> nat,
 isPR 4 g -> 
 isPR 2 (fun x y : nat => g (f1 x y) (f2 x y) (f3 x y) (f4 x y)).
Proof.
  intros  f1 [x p] f2 [x0 p0] f3 [x1 p1] f4 [x2 p2] g [x3 p3];
    cbn in p, p0, p1, p2, p3.
  exists
    (PRcomp x3 [x; x0; x1; x2])%pr; cbn in *; intros.
  now rewrite <- p, p0, p1, p2, p3.
Qed.

#[export] Instance compose3_1IsPR :
  forall f : nat -> nat -> nat -> nat,
    isPR 3 f ->
    forall g : nat -> nat, isPR 1 g ->
                           isPR 3 (fun x y z : nat => g (f x y z)).
Proof.
  intros f [x p] g [x0 p0]; cbn in p, p0.
  exists (PRcomp x0 [x])%pr;
  cbn in *; intros; now rewrite <- p, p0.
Qed.

#[export] Instance compose3_2IsPR :
  forall f1 : nat -> nat -> nat -> nat,
    isPR 3 f1 ->
    forall f2 : nat -> nat -> nat -> nat,
      isPR 3 f2 ->
      forall g : nat -> nat -> nat,
        isPR 2 g -> isPR 3 (fun x y z : nat => g (f1 x y z) (f2 x y z)).
Proof.
  intros f1 [x p] f2 [x0 p0] g [x1 p1]; cbn in p, p0, p1.
  exists (PRcomp x1 [x; x0])%pr;
    cbn; intros;  now rewrite <- p, p0, p1.
Qed.

#[export] Instance compose3_3IsPR :
 forall f1 : nat -> nat -> nat -> nat,
 isPR 3 f1 ->
 forall f2 : nat -> nat -> nat -> nat,
 isPR 3 f2 ->
 forall f3 : nat -> nat -> nat -> nat,
 isPR 3 f3 ->
 forall g : nat -> nat -> nat -> nat,
 isPR 3 g -> isPR 3 (fun x y z : nat => g (f1 x y z) (f2 x y z) (f3 x y z)).
Proof.
  intros  f1 [x p] f2 [x0 p0] f3 [x1 p1] g [x2 p2];
    cbn in p, p0, p1, p2.
  exists (PRcomp x2 [x; x0; x1])%pr.
  cbn in *; intros; now rewrite <- p, p0, p1, p2.  
Qed.

#[export] Instance compose4_2IsPR :
 forall f1 : nat -> nat -> nat -> nat -> nat,
 isPR 4 f1 ->
 forall f2 : nat -> nat -> nat -> nat -> nat,
 isPR 4 f2 ->
 forall g : nat -> nat -> nat,
 isPR 2 g -> isPR 4 (fun w x y z : nat => g (f1 w x y z) (f2 w x y z)).
Proof.
  intros f1 [x p] f2 [x0 p0] g [x1 p1]; cbn in p, p0, p1.
  exists (PRcomp x1 [x; x0])%pr. 
  cbn in *; intros; now rewrite <- p, p0, p1. 
Qed.

#[export] Instance compose4_3IsPR :
 forall f1 : nat -> nat -> nat -> nat -> nat,
 isPR 4 f1 ->
 forall f2 : nat -> nat -> nat -> nat -> nat,
 isPR 4 f2 ->
 forall f3 : nat -> nat -> nat -> nat -> nat,
 isPR 4 f3 ->
 forall g : nat -> nat -> nat -> nat,
 isPR 3 g ->
 isPR 4 (fun w x y z : nat => g (f1 w x y z) (f2 w x y z) (f3 w x y z)).
Proof.
  intros  f1 [x p] f2 [x0 p0] f3 [x1 p1] g [x2 p2];
    cbn in p, p0, p1, p2.
  exists (PRcomp x2 [x; x0; x1])%pr;
  cbn in *; intros; now rewrite <- p, p0, p1, p2. 
Qed.

#[export] Instance swapIsPR :
  forall f : nat -> nat -> nat, isPR 2 f -> isPR 2 (fun x y : nat => f y x).
Proof.
  intros.
  apply compose2_2IsPR with (f := fun a b : nat => b)
                            (g := fun a b : nat => a).
  - apply pi2_2IsPR.
  - apply pi1_2IsPR.
  - apply H.
Qed.

#[export] Instance indIsPR :
  forall f : nat -> nat -> nat,
    isPR 2 f ->
    forall g : nat,
      isPR 1
           (fun a : nat => nat_rec (fun _ : nat => nat) g 
                             (fun x y : nat => f x y) a).
Proof.
  intros f [x p] g; cbn in p.
  destruct  (const0_NIsPR g) as [x0 p0]; cbn in p0.
  exists (primRecFunc _ x0 x).
  cbn in |- *.
  simple induction c.
  - simpl in |- *; now rewrite <- p0.
  - intros; cbn in |- *;  now rewrite <- p, H.
Qed.

#[export] Instance ind1ParamIsPR :
  forall f : nat -> nat -> nat -> nat,
    isPR 3 f ->
    forall g : nat -> nat,
      isPR 1 g ->
      isPR 2 
           (fun a b : nat =>
              nat_rec (fun n : nat => nat) (g b) (fun x y : nat => f x y b) a).
Proof.
  intros f [x p] g [x0 p0]; cbn in p, p0.
  exists (primRecFunc _ x0 x); cbn in *; intros.
  induction c as [| c Hrecc].
  - cbn in |- *;  apply p0.
  - cbn  in |- *; now rewrite p, Hrecc.
Qed.

#[export] Instance ind2ParamIsPR :
  forall f : nat -> nat -> nat -> nat -> nat,
    isPR 4 f ->
    forall g : nat -> nat -> nat,
      isPR 2 g ->
      isPR 3
        (fun a b c : nat =>
           nat_rec (fun n : nat => nat) (g b c) (fun x y : nat => f x y b c) a).
Proof.
  intros f [x p] g [x0 p0]; cbn in p, p0.
  exists (primRecFunc _ x0 x); cbn in *.
  simple induction c.
  - intros; cbn; now rewrite p0.
  - intros; cbn in *; now rewrite p, H.
Qed.

#[export] Instance plusIndIsPR : isPR 3 (fun n fn b : nat => S fn).
Proof. apply (filter010IsPR _ succIsPR). Qed.

#[export] Instance plusIsPR : isPR 2 plus.
Proof.
  assert
    (H: isPR 2
          (fun a b : nat =>
             nat_rec (fun n : nat => nat) b (fun x y : nat => S y) a))
    by  apply (ind1ParamIsPR _ plusIndIsPR _ idIsPR).
  destruct H as [x  p]; cbn in p.
  exists x; cbn  in *.
  intros c c0; rewrite p.
  induction c as [| c Hrecc].
  - auto.
  - cbn in *; now rewrite Hrecc.
Qed.

#[export] Instance multIndIsPR : isPR 3 (fun n fn b : nat => fn + b).
Proof. apply (filter011IsPR _ plusIsPR). Qed.

#[export] Instance multIsPR : isPR 2 mult.
Proof.
  assert
    (H: isPR 2
             (fun a b : nat =>
                nat_rec (fun n : nat => nat) 0 (fun x y : nat => y + b) a)).
  {
    assert (H0: isPR 1 (fun _ => 0))
      by apply const1_NIsPR.
    apply (ind1ParamIsPR _ multIndIsPR _ H0).
  }
  destruct  H as [x  p]; cbn in p.
  exists x; cbn  in |- *.
  intros;rewrite p;induction c as [| c Hrecc].
  - auto.
  - simpl in |- *; rewrite Hrecc; apply Nat.add_comm.
Qed.

#[export] Instance predIsPR : isPR 1 pred.
Proof.
  assert
    (H: isPR 1
             (fun a : nat =>
                nat_rec (fun n : nat => nat) 0 (fun x y : nat => x) a))
    by apply (indIsPR _ pi1_2IsPR 0).
  destruct  H as [x p]; cbn  in p.
  exists x; cbn in |- *.
  intros c; rewrite p.
  induction c as [| c Hrecc]; trivial.
Qed.

#[export] Instance minusIndIsPR : isPR 3 (fun n fn b : nat => pred fn).
Proof. apply (filter010IsPR _ predIsPR). Qed.

#[export] Instance minusIsPR : isPR 2 minus.
Proof.
  assert
    (H: isPR 2
             (fun b a : nat =>
                nat_rec (fun n : nat => nat) b (fun x y : nat => pred y) a)).
  { apply
      swapIsPR
      with
        (f := fun a b : nat =>
                nat_rec (fun n : nat => nat) b (fun x y : nat => pred y) a).
    apply (ind1ParamIsPR _ minusIndIsPR _ idIsPR).
  }
  destruct  H as [x p]; cbn  in p.
  exists x; cbn in *.
  intros c c0; rewrite p.
  induction c0 as [| c0 Hrecc0].
  - cbn  in |- *; now rewrite Nat.sub_0_r.
  - cbn in |- *; rewrite Hrecc0.
    generalize c c0.
    intro c1; induction c1 as [| c1 Hrecc1].
    + auto.
    + intros; cbn in *; induction c2 as [| c2 Hrecc2].
      * cbn in |- *; now rewrite  Nat.sub_0_r.
      * apply Hrecc1.
Qed.

Definition notZero (a : nat) :=
  nat_rec (fun n : nat => nat) 0 (fun x y : nat => 1) a.

#[export] Instance notZeroIsPR : isPR 1 notZero.
Proof.
  unfold notZero; apply indIsPR with (f := fun _ _ : nat => 1).
  apply filter10IsPR with (g := fun _ : nat => 1).
  apply const1_NIsPR.
Qed.

Definition ltBool (a b : nat) : bool :=
  if le_lt_dec b a then false else true. 


Lemma ltBoolTrue : forall a b : nat, ltBool a b = true -> a < b.
Proof.
  intros a b H; unfold ltBool in H.
  destruct  (le_lt_dec b a); [discriminate | assumption].
Qed.

Lemma ltBoolFalse : forall a b : nat, ltBool a b = false -> ~ a < b.
Proof. 
  intros a b H; unfold ltBool in H.
  destruct  (le_lt_dec b a).
  - unfold not ; intros; lia.
  - discriminate.
Qed.

#[export] Instance ltIsPR : isPRrel 2 ltBool.
Proof.
  unfold isPRrel in |- *.
  assert (H: isPR 2 (fun a b : nat => notZero (b - a))).
  { apply swapIsPR with (f := fun a b : nat => notZero (a - b)).
    apply compose2_1IsPR.
    - apply minusIsPR.
    - apply notZeroIsPR.
  }
  destruct H as [x p]; cbn in p.
  exists x; cbn in *; intros.
  rewrite p; unfold ltBool in |- *.
  destruct (le_lt_dec c0 c) as [a | b].
  - revert c a. 
      induction c0 as [| c0 Hrecc0].
      + intros; reflexivity.
      + intros; induction c as [| c Hrecc].
       * elim (Nat.nle_succ_0 _ a).
       * cbn  in |- *; apply Hrecc0; apply le_S_n; auto.
  - revert c b; induction c0 as [| c0 Hrecc0].
      * intros; elim (Nat.nlt_0_r _ b).
      * intros; induction c as [| c Hrecc].
        -- simpl in |- *; reflexivity.
        -- simpl in |- *.
           apply Hrecc0; now rewrite Nat.succ_lt_mono.
Qed.


#[export] Instance maxIsPR : isPR 2 max.
Proof.
  assert (H: isPR 2 (fun a b : nat => a + (b - a))).
  { apply
      compose2_2IsPR
      with (h := plus) (f := fun a b : nat => a) (g := fun a b : nat => b - a).
    - apply pi1_2IsPR.
    - apply swapIsPR,  minusIsPR.
    - apply plusIsPR.
  }
  destruct H as [x p]; exists x; eapply extEqualTrans.
  - apply p.
  - clear x p; cbn in |- *;  intros c c0;
      destruct (Nat.le_gt_cases c c0).
    + rewrite Nat.max_r; [| trivial].
      * symmetry  in |- *; now rewrite Nat.add_comm, Nat.sub_add. 
    +   replace (c0 - c) with 0 by lia. 
      * rewrite Nat.add_comm, max_l.
        -- reflexivity.
        -- now apply Nat.lt_le_incl.
Qed.


#[export] Instance gtIsPR : isPRrel 2 (fun a b : nat => ltBool b a).
Proof.
  unfold isPRrel in |- *; cbn.
  apply swapIsPR with (f := fun a0 a : nat => if ltBool a0 a then 1 else 0);
  apply ltIsPR.
Qed.


Remark replaceCompose2 :
 forall (n : nat) (a b a' b' : naryFunc n) (c c' : naryFunc 2),
 extEqual n a a' ->
 extEqual n b b' ->
 extEqual 2 c c' ->
 extEqual 
   n
   (evalComposeFunc _ _
                    (Vector.cons _ a _ 
                                 (Vector.cons _ b _
                                              (Vector.nil  (naryFunc n)))) c)
   (evalComposeFunc _ _
                    (Vector.cons _ a' _
                                 (Vector.cons _ b' _
                                              (Vector.nil  (naryFunc n)))) c').
Proof.
  intros;apply extEqualCompose; auto;
    unfold extEqualVector in |- *; cbn; auto.
Qed.

Definition orRel (n : nat) (R S : naryRel n) : naryRel n.
Proof. 
  induction n as [| n Hrecn].
  - apply (R || S).
  - cbn in |- *;intros H; apply Hrecn.
    + apply (R H).
    + apply (S H).
Defined.

Lemma orRelPR :
  forall (n : nat) (R R' : naryRel n),
    isPRrel n R -> isPRrel n R' -> isPRrel n (orRel n R R').
Proof.
  intros n R R' [x p] [x0 p0];
    assert (H: isPR 2 (fun a b : nat => notZero (a + b))).
  {
    apply compose2_1IsPR.
    - apply plusIsPR.
    - apply notZeroIsPR.
  }
  destruct  H as (x1, p1);
  exists (PRcomp x1 [x; x0])%pr; cbn in |- *.
  apply
    extEqualTrans
    with
    (evalComposeFunc n 2
       (Vector.cons (naryFunc n) (charFunction n R) 1
          (Vector.cons (naryFunc n) 
             (charFunction n R') 0
             (Vector.nil  (naryFunc n))))
       (fun a b : nat => notZero (a + b))).
  - apply replaceCompose2; auto.
  - clear x p x0 p0 x1 p1; induction n as [| n Hrecn].
    + simpl in |- *; destruct  R.
      * reflexivity.
      * destruct  R'; reflexivity.
    + cbn in |- *; fold (naryFunc n) in |- *.
      intro c; apply (Hrecn (R c) (R' c)).
Qed.



Definition andRel (n : nat) (R S : naryRel n) : naryRel n.
Proof. 
  induction n as [| n Hrecn].
  - exact (R && S).
  - simpl in |- *; intros; apply Hrecn.
    + apply (R H).
    + apply (S H).
Defined.

Lemma andRelPR :
  forall (n : nat) (R R' : naryRel n),
    isPRrel n R -> isPRrel n R' -> isPRrel n (andRel n R R').
Proof.
  intros n R R' [x p]  [x0 p0];
    assert (H: isPR 2 mult) by apply multIsPR.
  destruct  H as [x1 p1].
  exists (PRcomp x1 [x; x0])%pr; 
  cbn  in |- *;
    apply
      extEqualTrans
      with
        (evalComposeFunc n 2
                         (Vector.cons (naryFunc n) (charFunction n R) 1
                                      (Vector.cons (naryFunc n)
                                                   (charFunction n R') 0
                                                   (Vector.nil  (naryFunc n))))
                         mult).
  - apply replaceCompose2; auto.
  - clear x p x0 p0 x1 p1;induction n as [| n Hrecn].
    + simpl in |- *; induction R.
      * induction R'; reflexivity.
      * reflexivity.
    + simpl in |- *; fold (naryFunc n) in |- *; intros c;
      apply (Hrecn (R c) (R' c)).
Qed.


Definition notRel (n : nat) (R : naryRel n) : naryRel n.
Proof. 
  induction n as [| n Hrecn].
  - exact (negb R).
  - cbn in |- *; intros p; apply Hrecn, (R p).
Defined.

Lemma notRelPR  (n : nat) (R : naryRel n):
  isPRrel n R -> isPRrel n (notRel n R).
Proof.
  intros [x p];
    assert (H: isPR 1 (fun x : nat => 1 - x)).
  {
    apply compose1_2IsPR with (f := fun x : nat => 1)
                              (f' := fun x : nat => x).
    - apply const1_NIsPR.
    - apply idIsPR.
    - apply minusIsPR.
  }
  destruct H as [x0 p0];
    exists (PRcomp x0 [x])%pr;
  cbn in |- *; apply extEqualTrans with
    (evalComposeFunc n 1 (Vector.cons _ (charFunction n R) _ (Vector.nil  _))
       (fun x : nat => 1 - x)).
  - apply extEqualCompose.
    + unfold extEqualVector; simpl; auto.
    + auto.
  - clear p0 x0 p x; induction n as [| n Hrecn].
    + simpl in |- *; induction R; reflexivity.
    + simpl; intros c; fold (naryFunc n) in |- *; apply Hrecn.
Qed.

Fixpoint bodd (n : nat) : bool :=
  match n with
  | O => false
  | S n' => negb (bodd n')
  end.

#[export] Instance boddIsPR : isPRrel 1 bodd.
Proof.
  assert (H: isPR 2 (fun _ rec : nat => 1 - rec)).
  { apply filter01IsPR with (g := fun rec : nat => 1 - rec).
    apply compose1_2IsPR with (f := fun _ : nat => 1) (f' := fun x : nat => x).
    - apply const1_NIsPR.
    - apply idIsPR.
    - apply minusIsPR.
  }
  destruct  H as [x p]; exists (primRecFunc 0 zeroFunc x).
  cbn in |- *; intros; induction c as [| c Hrecc].
  - cbn in |- *;  auto.
  - cbn in |- *; rewrite p;   cbn in |- *;   rewrite Hrecc.
    clear Hrecc; induction (bodd c); reflexivity.
Qed.

Lemma nat_eqb_false (a b: nat) : a <> b -> Nat.eqb a b = false.
Proof. now rewrite <- Nat.eqb_neq. Qed.


#[local] Instance neqIsPR : isPRrel 2 (fun a b : nat => negb (Nat.eqb a b)).
Proof.
  intros.
  assert (H: isPRrel 2 (orRel 2 ltBool (fun a b : nat => ltBool b a))).
  { apply orRelPR.
    - apply ltIsPR.
    - apply gtIsPR.
  }
  destruct H as [x p].
  exists x; cbn in *. 
  intros;rewrite p;clear p.
  unfold ltBool; destruct  (eq_nat_dec c c0) as [a | b].
  - rewrite a; rewrite  Nat.eqb_refl; cbn in |- *.
    destruct (le_lt_dec c0 c0).
    + reflexivity.
    + elim (Nat.lt_irrefl _ l).
  - rewrite nat_eqb_false; cbn in |- *.
    destruct  (le_lt_dec c0 c).
    + destruct (le_lt_dec c c0); [ | reflexivity].
      * rewrite Nat.lt_gt_cases  in b; destruct b; exfalso; lia. 
    + reflexivity.
    + assumption.
Qed.


#[export] Instance eqIsPR : isPRrel 2 Nat.eqb.
Proof.
  assert (H: isPRrel 2
               (notRel 2 (fun a b : nat => negb (Nat.eqb a b))))
    by (apply notRelPR, neqIsPR).
  cbn in H; destruct H as [x  p]; exists x; cbn in *.
  intros c c0; rewrite p; clear p; destruct (Nat.eqb c c0); auto.
Qed.

Definition leBool (a b : nat) : bool :=
  if le_lt_dec a b then true else false.

#[export] Instance leIsPR : isPRrel 2 leBool.
Proof.
  assert (H: isPRrel 2 (orRel 2 ltBool Nat.eqb)).
  { apply orRelPR.
    - apply ltIsPR.
    - apply eqIsPR.
  }
  destruct  H as (x, p); exists x ; cbn in *.
  intros; rewrite p.
  clear p x;  unfold leBool, ltBool  in |- *.
  induction (le_lt_dec c0 c).
  + destruct (le_lt_dec c c0).
    * simpl in |- *.
      replace c0 with c.
      --  now rewrite Nat.eqb_refl.
      -- destruct (eq_nat_dec c c0).
         ++ auto.
         ++ rewrite Nat.lt_gt_cases in n; destruct n;
             rewrite  Nat.lt_nge in H; contradiction.
    * rewrite nat_eqb_false; cbn in |- *.
      -- reflexivity.
      -- unfold not in |- *; intros H; rewrite H in l.
         elim (Nat.lt_irrefl _ l).
  + cbn in |- *;  destruct  (le_lt_dec c c0).
    * reflexivity.
    * elim (Nat.lt_irrefl c).
      apply Nat.lt_trans with c0; auto.
Qed.

Section Ignore_Params.

  Fixpoint ignoreParams (n m : nat) (f : naryFunc n) {struct m} :
    naryFunc (m + n) :=
    match m return (naryFunc (m + n)) with
    | O => f
    | S x => fun _ => ignoreParams n x f
    end.

  Definition projectionListPR (n m : nat) (p : m <= n) : PrimRecs n m.
  Proof.
  induction m as [| m Hrecm].
    - exact (PRnil n).
    - assert (H: m < n) by
        apply Compat815.lt_S_n,  Compat815.le_lt_n_Sm,  p.
      apply (PRcons _ m (projFunc _ _ H)).
      apply Hrecm,  le_S_n, le_S, p.
  Defined.

  Definition projectionList (n m : nat) (p : m <= n) : 
    Vector.t (naryFunc n) m := evalPrimRecs n m (projectionListPR n m p).

  Lemma projectionListInd :
    forall (n m : nat) (p1 p2 : m <= n),
      projectionList n m p1 = projectionList n m p2.
  Proof.
    intros; unfold projectionList in |- *.
    induction m as [| m Hrecm].
    - reflexivity.
    - simpl in |- *.
      rewrite (Hrecm (le_S_n m n
                        (le_S (S m) n p1))
                     (le_S_n m n (le_S (S m) n p2))).
      now rewrite
        (evalProjFuncInd _ _
           (Compat815.lt_S_n m n
              (Compat815.le_lt_n_Sm (S m) n p1))
           (Compat815.lt_S_n m n (Compat815.le_lt_n_Sm (S m) n p2))).
  Qed.

  Lemma projectionListApplyParam :
    forall (m n c : nat) (p1 : m <= n) (p2 : m <= S n),
      extEqualVector _ _ (projectionList n m p1)
                     (evalOneParamList n m c (projectionList (S n) m p2)).
  Proof.
    unfold extEqualVector, projectionList in |- *.
    simple induction m.
    - simpl in |- *; auto.
    - intros; simpl  in |- *.
      destruct (eq_nat_dec n n0).
      + elim (Compat815.lt_not_le n (S n)).
        apply Nat.lt_succ_diag_r .
        rewrite <- e in p1; auto.
      + split.
        rewrite
          (evalProjFuncInd _ _ 
             (Compat815.lt_S_n n n0 (Compat815.le_lt_n_Sm (S n) n0 p1))
             match
               Compat815.le_lt_or_eq n n0
                 (Compat815.lt_n_Sm_le n n0 (Compat815.lt_S_n n (S n0)
                                               (Compat815.le_lt_n_Sm
                                                  (S n)
                                                  (S n0)
                                                  p2)))
             with
             | or_introl l2 => l2
             | or_intror l2 => False_ind (n < n0) (n1 l2)
             end).
        * apply extEqualRefl.
        * apply H.
  Qed.


  Lemma projectionListId :
    forall (n : nat) (f : naryFunc n) (p : n <= n),
      extEqual n f (evalComposeFunc n n (projectionList n n p) f).
  Proof.
    intros; induction n as [| n Hrecn].
    - cbn in |- *; reflexivity.
    - cbn in |- *; intros; fold (naryFunc n) in |- *.
      destruct (eq_nat_dec n n) as [a | b].
      + apply
          extEqualTrans
          with
            (evalComposeFunc n (S n)
               (Vector.cons (naryFunc n) (evalConstFunc n c) n
                  (projectionList n n (le_n n))) f).
        *  apply extEqualTrans with
             (evalComposeFunc n n (projectionList n n (le_n n)) (f c)).
           -- apply Hrecn.
           -- clear Hrecn a p; generalize (projectionList n n (le_n n)).
              generalize f c; clear f c.
              assert
                (H: forall (m : nat) (f : naryFunc (S m)) (c : nat)
                           (v : Vector.t (naryFunc n) m),
                    extEqual n (evalComposeFunc n m v (f c))
                      (evalComposeFunc n (S m)
                         (Vector.cons
                            (naryFunc n)
                            (evalConstFunc n c) m v) f)).
              ++ intros; induction n as [| n Hrecn].
                 ** cbn in |- *; reflexivity.
                 ** cbn in |- *; intros; fold (naryFunc n) in |- *.
                    apply Hrecn.
              ++ apply H.
        *   apply extEqualCompose.
            -- unfold extEqualVector in |- *.
               cbn; split.
               ++ apply extEqualRefl.
               ++ apply
                    (projectionListApplyParam n n c 
                       (le_n n)
                       (le_S_n n (S n) (le_S (S n) (S n) p))).
            -- apply extEqualRefl.
      + now destruct b.
  Qed.
    
  #[export] Instance ignoreParamsIsPR :
    forall (n m : nat) (f : naryFunc n),
      isPR _ f -> isPR _ (ignoreParams n m f).
  Proof.
    assert
      (H: forall (n m : nat) (pr : m <= n) (f : naryFunc m) 
                 (p : n - m + m = n),
          extEqual _ (eq_rec (n - m + m) naryFunc 
                        (ignoreParams m (n - m) f) _ p)
            (evalComposeFunc _ _ (projectionList n m pr) f)).
    { unfold projectionList in |- *.
      induction n as [| n Hrecn]; intros.
      - destruct m as [| n].
        + cbn in |- *.
          elim p using K_dec_set.
          * apply eq_nat_dec.
          * reflexivity.
        + elim (Nat.nle_succ_0 _ pr).
      - induction (Compat815.le_lt_or_eq _ _ pr).
        + assert (H0: m <= n) by (apply Compat815.lt_n_Sm_le; auto).
          generalize p; rewrite Nat.sub_succ_l; clear p.
          * intros.
            cbn in |- *.
            intros.
            assert (H1: n - m + m = n).
            { cbn in p; injection p.
              auto.
            }
            replace
            (eq_rec (S (n - m + m)) naryFunc
                    (fun _ : nat => ignoreParams m (n - m) f)
                    (S n) p c)
              with
              (eq_rec (n - m + m) naryFunc (ignoreParams m (n - m) f) n H1).
            -- apply extEqualTrans
                 with (evalComposeFunc n m (projectionList n m H0) f).
               ++ unfold projectionList in |- *.
                  apply Hrecn.
               ++ apply extEqualCompose.
                  ** apply (projectionListApplyParam m n c H0 pr).
                  ** apply extEqualRefl.
            -- generalize H1, p.
               cbn in |- *; generalize (ignoreParams m (n - m) f).
               rewrite H1; intros.
               elim H2 using K_dec_set.
               apply eq_nat_dec.
               elim p0 using K_dec_set.
               apply eq_nat_dec.
               cbn in |- *.
               reflexivity.
          * auto.
        + generalize p, pr.
          rewrite <- H.
          clear H p.
          replace (m - m) with 0.
          * cbn in |- *.
            intros.
            elim p using K_dec_set.
            -- apply eq_nat_dec.
            -- cbn in |- *.
               clear p pr.
               apply (projectionListId m f pr0).
          * now rewrite Nat.sub_diag. 
    }
    intros.
    unfold projectionList in H.
    destruct H0 as [x p].
    exists (composeFunc (m + n) n 
              (projectionListPR _ _ (Compat815.le_plus_r _ _)) x).
    apply extEqualSym.
    assert (H0: m + n - n + n = m + n) by (now rewrite Nat.add_sub).
    assert
    (H1: 
      extEqual (m + n)
        (eq_rec (m + n - n + n) naryFunc
           (ignoreParams n (m + n - n) f) 
           (m + n) H0)
        (evalComposeFunc (m + n) _
           (evalPrimRecs (m + n) n
              (projectionListPR
                 (m + n) n
                 (Compat815.le_plus_r m n)))
           f)) by apply H. 
    replace (ignoreParams n m f) with
      (eq_rec (m + n - n + n)
         naryFunc (ignoreParams n (m + n - n) f) (m + n) H0).
    - cbn in |- *.
      apply extEqualTrans with
        (evalComposeFunc (m + n) _
           (evalPrimRecs (m + n) n
              (projectionListPR
                 (m + n) n (Compat815.le_plus_r m n)))
                           f).
      + apply H1.
      + apply extEqualCompose.
        * generalize
            (evalPrimRecs (m + n) n 
               (projectionListPR (m + n) n (Compat815.le_plus_r m n))).
          generalize (m + n).
          intros n0 t; apply extEqualVectorRefl.
        * apply extEqualSym.
          auto.
    - generalize H0; replace (m + n - n) with m.
      + intros.
        elim H2 using K_dec_set.
        *  apply eq_nat_dec.
        * cbn in |- *;  reflexivity.
      + now rewrite Nat.add_sub. 
  Qed.

End Ignore_Params.

Lemma reduce1stCompose :
  forall (c n m : nat) (v : Vector.t (naryFunc n) m) (g : naryFunc (S m)),
    extEqual n
      (evalComposeFunc n _ (Vector.cons (naryFunc n)
                              (evalConstFunc n c) _ v) g)
      (evalComposeFunc n _ v (g c)).
Proof.
  induction n as [| n Hrecn].
  - cbn in |- *; auto.
  - cbn in |- *; fold (naryFunc n) in |- *; intros; apply Hrecn.
Qed.

Lemma reduce2ndCompose :
  forall (c n m : nat) (v : Vector.t (naryFunc n) m) (n0 : naryFunc n)
         (g : naryFunc (S (S m))),
    extEqual n
      (evalComposeFunc n _
         (Vector.cons
            (naryFunc n) n0 _
            (Vector.cons (naryFunc n)
               (evalConstFunc n c) _ v))
         g)
      (evalComposeFunc n _ (Vector.cons (naryFunc n) n0 _ v)
         (fun x : nat => g x c)).
Proof.
  induction n as [| n Hrecn].
  - cbn in |- *; auto.
  - cbn in |- *; fold (naryFunc n) in |- *; intros; apply Hrecn.
Qed.

Lemma evalPrimRecParam :
  forall (n c d : nat) (g : naryFunc (S n)) (h : naryFunc (S (S (S n)))),
     evalPrimRecFunc n (g d) (fun x y : nat => h x y d) c =x=
      evalPrimRecFunc (S n) g h c d.
Proof.
induction c as [| c Hrecc].
- intros; cbn in |- *; apply extEqualRefl.
- intros; cbn in |- *; apply extEqualCompose2; auto.
  apply extEqualRefl.
Qed.


#[export] Instance compose2IsPR :
  forall (n : nat) (f : naryFunc n) (p : isPR n f) (g : naryFunc (S n))
         (q : isPR (S n) g), isPR n (compose2 n f g).
Proof.
  intros.
  destruct p as (x, p).
  destruct q as (x0, p0).
  exists (composeFunc _ _ (PRcons _ _ x (projectionListPR n n (le_n n))) x0).
  simpl in |- *.
  apply
    extEqualTrans
    with
      (evalComposeFunc n (S n)
                       (Vector.cons (naryFunc n) f n
                                    (evalPrimRecs n n (projectionListPR n n
                                                         (le_n n)))) g).
  - apply extEqualCompose.
    + unfold extEqualVector; simpl; split.
      * auto.
      * apply extEqualVectorRefl.
    + auto.
  - clear p0 x0 p x.
    induction n as [| n Hrecn].
    * simpl in |- *; auto.
    * simpl in |- *.
      fold (naryFunc n) in |- *.
      induction (eq_nat_dec n n).
      -- intros; apply  extEqualTrans with
           (evalComposeFunc n (S (S n))
              (Vector.cons (naryFunc n) (f c) (S n)
                 (Vector.cons (naryFunc n) (evalConstFunc n c) n
                    (projectionList n n (le_n n)))) g).
         ++ apply extEqualSym.
            apply extEqualCompose.
            unfold extEqualVector in |- *.
            simpl in |- *.
            repeat split.
            ** apply extEqualRefl.
            ** apply extEqualRefl.
            ** apply
                 (projectionListApplyParam 
                    n n c (le_n n)
                    (le_S_n n (S n) (le_S (S n) (S n) (le_n (S n))))).
            ** apply extEqualRefl.
         ++ apply extEqualTrans with
              (evalComposeFunc n (S n)
                 (Vector.cons (naryFunc n) (f c) n
                    (evalPrimRecs n n (projectionListPR n n (le_n n))))
                 (fun x : nat => g x c)).
            ** clear a Hrecn.
               generalize (f c).
               fold (naryFunc n) in |- *.
               fold (projectionList n n (le_n n)) in |- *.
               generalize (projectionList n n (le_n n)).
               intros t n0;
               apply (reduce2ndCompose c n n t n0).
            ** apply Hrecn.
      -- elim b; auto.
Qed.

#[export] Instance compose1_NIsPR :
  forall (n : nat) (g : naryFunc (S n)),
    isPR (S n) g ->
    forall f : naryFunc 1, isPR 1 f ->
                           isPR (S n) (fun x : nat => g (f x)).
Proof.
  intros n g [x p] f [x0 p0].
  exists 
    (PRcomp x
       (PRcomp x0 [projFunc (S n) n (Nat.lt_succ_diag_r n)]
          :: projectionListPR (S n) n (Nat.le_succ_diag_r n))%pr).
   cbn in |- *; fold (naryFunc n) in |- *; destruct (eq_nat_dec n n).
  - intros.
    apply
      extEqualTrans
      with
      (evalComposeFunc n (S n)
         (Vector.cons (naryFunc n) (evalConstFunc n (f c)) n
            (projectionList n n (le_n n))) g).
    + apply extEqualSym.
      apply extEqualCompose.
      * unfold extEqualVector in |- *.
        cbn in |- *.
        split.
        -- apply extEqualSym.
           apply
             extEqualTrans
             with
             (evalComposeFunc n 1
                (Vector.cons (naryFunc n) (evalConstFunc n c) 0 
                   (Vector.nil  (naryFunc n))) f).
           ++ apply extEqualCompose.
              ** apply extEqualVectorRefl.
              ** auto.
           ++ clear  p0 x0 p x g.
              induction n as [| n Hrecn].
              ** cbn in |- *.
                 reflexivity.
              ** cbn in |- *.
                 intros.
                 apply Hrecn.
                 reflexivity. 
        -- apply (projectionListApplyParam n n c (le_n n) (Nat.le_succ_diag_r n)).
      *  apply extEqualSym.
         auto.
    + clear p0 x0 p x .
      eapply extEqualTrans.
      * apply reduce1stCompose.
      * apply extEqualSym.
        apply (projectionListId n (g (f c)) (le_n n)).
  - elim n0; auto.
Qed.

Definition switchPR : naryFunc 3 :=
  fun n x y => match n with 0 => y | _ => x end.

#[export] Instance switchIsPR : isPR 3 switchPR.
Proof.
  assert (H: isPR 3
                  (fun a b c : nat =>
                     nat_rec (fun _ : nat => nat) c
                             (fun (n : nat)
                                  (_ : (fun _ : nat => nat) n) => b) a)).
  - apply
      ind2ParamIsPR with (f := fun _ _ b c : nat => b) 
                         (g := fun b c : nat => c).
    + apply pi3_4IsPR.
    + apply pi2_2IsPR.
  - destruct H as (x, p).
    exists x.
    apply
      extEqualTrans  with
        (fun a b c : nat =>
           nat_rec (fun _ : nat => nat) c (fun _ _ : nat => b) a).
    + apply p.
    + unfold switchPR in |- *; cbn in |- *.
      intros.
      induction c; reflexivity.
Qed.



Fixpoint boundedSearchHelp (P : naryRel 1) (b : nat) {struct b} : nat :=
  match b with
  | O => 0
  | S b' => let q := boundedSearchHelp P b'
            in 
      match eq_nat_dec q  b' with
      | left _ => match P b' with
                  | true => b'
                  | false => S b'
                  end
      | right _ => q 
      end
  end.

(** If there exists some [x <= b] such that [(P b x)], returns [x]
    Otherwise, returns [b]
*)
 
Definition boundedSearch (P : naryRel 2) (b : nat) : nat :=
  boundedSearchHelp (P b) b.

Module Examples.

  Definition sqrtHelp (n: nat) :=
    boundedSearch (fun _ x => Nat.eqb (x * x) n) (S (n / 2)).

  Definition exact_sqrt  (n: nat) :=
    let q := sqrtHelp n
    in if  Nat.eqb (q * q) n then Some q else None.

  Compute exact_sqrt 36.
  Compute exact_sqrt 35.  
  Compute exact_sqrt 0.
  Compute exact_sqrt 2.

  End Examples.

  Lemma boundedSearch1 :
    forall (P : naryRel 2) (b x : nat), x < boundedSearch P b ->
                                        P b x = false.
Proof.
  unfold boundedSearch in |- *.
  intros P b.
  generalize (P b).
  intros b0 x H.
  clear P; induction b as [| b Hrecb].
  - cbn in H; elim (Nat.nlt_0_r _ H).
  - cbn in H.
    induction (eq_nat_dec (boundedSearchHelp b0 b) b).
    + rewrite a in Hrecb.
      induction (eq_nat_dec x b).

      * rewrite a0.
        induction (b0 b).
        -- elim (Nat.lt_irrefl b).
           rewrite a0 in H.
           auto.
        -- auto.
      * apply Hrecb.
        induction (b0 b).
        -- auto.
        -- assert (H0:x <= b).
           { apply Compat815.lt_n_Sm_le; auto. }
           induction (Compat815.le_lt_or_eq _ _ H0).
           ++ auto.
           ++ elim b1.
              ** auto.
    + apply Hrecb; auto.
Qed.

Lemma boundedSearch2 :
  forall (P : naryRel 2) (b : nat),
    boundedSearch P b = b \/ P b (boundedSearch P b) = true.
Proof.
  unfold boundedSearch in |- *; intros P b.
  assert
    (H: forall P : naryRel 1,
        boundedSearchHelp P b = b \/ P (boundedSearchHelp P b) = true).
  { clear P; intros; induction b as [| b Hrecb].
    - cbn in |- *; auto.
    - cbn in |- *.
      assert (H: P b = true \/ P b = false)
        by (destruct (P b); auto).
      induction (eq_nat_dec (boundedSearchHelp P b) b).
      induction H as [H| H]; rewrite H; auto.
      induction Hrecb as [H0| H0].
      + elim b0; auto.
      + auto.
  }
  apply H.
Qed.


#[export] Instance boundSearchIsPR :
  forall P : naryRel 2,
    isPRrel 2 P -> isPR 1 (boundedSearch P).
Proof.
  intros; unfold boundedSearch in |- *.
  assert
    (H0: isPR 2
              (fun b c : nat =>
                 nat_rec (fun _ : nat => nat) 0
                         (fun b0 Hrecb : nat =>
                            sumbool_rec
                              (fun _ : {Hrecb = b0} + {Hrecb <> b0} => nat)
                              (fun _ : Hrecb = b0 =>
                                 bool_rec
                                   (fun _ : bool => nat) b0 (S b0) (P c b0))
                              (fun _ : Hrecb <> b0 => Hrecb)
                              (eq_nat_dec Hrecb b0)) b)).
  { apply  ind1ParamIsPR
      with
        (g := fun _ : nat => 0)
        (f := fun b0 Hrecb c : nat =>
                sumbool_rec (fun _ : {Hrecb = b0} + {Hrecb <> b0} => nat)
                            (fun _ : Hrecb = b0 =>
                               bool_rec
                                 (fun _ : bool => nat) b0 (S b0) (P c b0))
                            (fun _ : Hrecb <> b0 => Hrecb)
                            (eq_nat_dec Hrecb b0)).
    - unfold isPRrel in H.
      assert
        (H0: isPR 3
                  (fun b0 Hrecb c : nat =>
                     switchPR (charFunction 2 Nat.eqb Hrecb b0)
                              (bool_rec (fun _ : bool => nat) b0 (S b0)
                                        (P c b0)) Hrecb)).
      { apply
          compose3_3IsPR
          with
            (g := switchPR)
            (f1 := fun b0 Hrecb c : nat => charFunction 2 Nat.eqb Hrecb b0)
            (f2 := fun b0 Hrecb c : nat =>
                     bool_rec (fun _ : bool => nat) b0 (S b0) (P c b0))
            (f3 := fun b0 Hrecb c : nat => Hrecb).
        - apply filter110IsPR
            with (g := fun b0 Hrecb : nat => charFunction 2 Nat.eqb Hrecb b0).
          apply swapIsPR.
          apply eqIsPR.
        - apply
            filter101IsPR
            with
              (g := fun b0 c : nat => bool_rec
                                        (fun _ : bool => nat) b0 (S b0)
                                        (P c b0)).
          assert
            (H0: isPR 2 (fun b0 c : nat => switchPR
                                             (charFunction 2 P c b0)
                                             b0 (S b0))).
          { apply
              compose2_3IsPR
              with
                (g := switchPR)
                (f1 := fun b0 c : nat => charFunction 2 P c b0)
                (f2 := fun b0 c : nat => b0)
                (f3 := fun b0 c : nat => S b0).
            - apply swapIsPR.
              apply H.
            - apply pi1_2IsPR.
            - apply filter10IsPR.
              apply succIsPR.
            - apply switchIsPR.
          }
          induction H0 as (x, p).
          exists x.
          apply
            extEqualTrans
            with (fun b0 c : nat => switchPR (charFunction 2 P c b0) b0 (S b0)).
          + auto.
          + cbn in |- *.
            intros.
            induction (P c0 c); reflexivity.
        - apply pi2_3IsPR.
        - apply switchIsPR.
      }
      induction H0 as (x, p).
      exists x.
      apply
        extEqualTrans
        with
          (fun b0 Hrecb c : nat =>
             switchPR (charFunction 2 Nat.eqb Hrecb b0)
                      (bool_rec (fun _ : bool => nat) b0 (S b0)
                                (P c b0)) Hrecb).
      * auto.
      * cbn in |- *.
        intros c c0 c1;
        destruct (eq_nat_dec c0 c) as [a| b ].
        -- cbn; rewrite <- a.
           rewrite  Nat.eqb_refl; reflexivity.
        -- rewrite nat_eqb_false.
           ++ reflexivity.
           ++ assumption.
    - apply const1_NIsPR.
  }
  assert
  (H1: isPR 1
            (fun b : nat =>
               nat_rec (fun _ : nat => nat) 0
                       (fun b0 Hrecb : nat =>
                          sumbool_rec
                            (fun _ : {Hrecb = b0} + {Hrecb <> b0} => nat)
                            (fun _ : Hrecb = b0 =>
                               bool_rec
                                 (fun _ : bool => nat) b0 (S b0) (P b b0))
                            (fun _ : Hrecb <> b0 => Hrecb)
                            (eq_nat_dec Hrecb b0)) b)).
  { apply
      compose1_2IsPR
      with
        (g := fun b c : nat =>
                nat_rec (fun _ : nat => nat) 0
                        (fun b0 Hrecb : nat =>
                           sumbool_rec
                             (fun _ : {Hrecb = b0} + {Hrecb <> b0} => nat)
                                       (fun _ : Hrecb = b0 =>
                                          bool_rec
                                            (fun _ : bool => nat) b0
                                            (S b0) (P c b0))
                                       (fun _ : Hrecb <> b0 => Hrecb)
                                       (eq_nat_dec Hrecb b0)) b)
        (f := fun b : nat => b)
        (f' := fun b : nat => b).
    - apply idIsPR.
    - apply idIsPR.
    - auto.
  }
  clear H0.
  induction H1 as (x, p).
  exists x.
  apply
    extEqualTrans
    with
      (fun b : nat =>
         nat_rec (fun _ : nat => nat) 0
                 (fun b0 Hrecb : nat =>
                    sumbool_rec (fun _ : {Hrecb = b0} + {Hrecb <> b0} => nat)
                                (fun _ : Hrecb = b0 =>
                                   bool_rec (fun _ : bool => nat) b0 (S b0)
                                            (P b b0))
                                (fun _ : Hrecb <> b0 => Hrecb)
                                (eq_nat_dec Hrecb b0)) b).
  auto.
  clear H x p.
  cbn in |- *.
  intros c;  generalize (P c).
  intros b; clear P.
  induction c as [| c Hrecc].
  - cbn in |- *; easy. 
  - cbn in |- *; rewrite Hrecc.
    destruct (eq_nat_dec (boundedSearchHelp b c) c) as [e | n ].
    + cbn in |- *.
      induction (b c);  auto.
    + cbn in |- *; reflexivity.
Qed.


Definition iterate (g : nat -> nat) :=
  nat_rec (fun _ => nat -> nat) (fun x : nat => x)
          (fun (_ : nat) (rec : nat -> nat) (x : nat) => g (rec x)).

#[export] Instance iterateIsPR :
  forall g : nat -> nat, isPR 1 g ->
                         forall n : nat, isPR 1 (iterate g n).
Proof.
  intros g Hg.
  induction n as [| n Hrecn]; cbn  in |- *.
  - apply idIsPR.
  - apply compose1_1IsPR; assumption.
Qed.


#[export] Instance isPRTrans (n:nat) (f g : naryFunc n):
  f =x= g -> isPR n f -> isPR n g. 
Proof.
  intros H [x Hx]; exists x; apply extEqualTrans with f; auto.
Qed.

(* begin snippet isPRextEqual:: no-out *)
#[export] Instance isPRextEqual (n:nat) (f g : naryFunc n):
  isPR n f -> f =x= g ->  isPR n g. 
(* end snippet isPRextEqual *)
Proof.
  intros; eapply isPRTrans; eauto. 
Qed.
