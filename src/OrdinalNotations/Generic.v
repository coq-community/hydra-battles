Require Import RelationClasses Relation_Operators Ensembles OrdNotations.
Import Relation_Definitions.
Require Export MoreOrders
  Coq.Wellfounded.Inverse_Image Coq.Wellfounded.Inclusion.
Require Import Schutte_basics.



Generalizable All Variables.
Declare Scope ON_scope.
Delimit Scope ON_scope with on.
Local Open Scope ON_scope.

(**
  Ordinal notation system on type [A] :

*)

Class ON {A:Type}(lt: relation A)
      (compare : A -> A -> comparison)  :=
  {
  sto :> StrictOrder lt;
  wf : well_founded lt;
  compare_correct :
    forall alpha beta:A,
      CompareSpec (alpha=beta) (lt alpha beta) (lt beta alpha)
                  (compare alpha beta);
  }.

(** Selectors *)

Definition on_t  {A:Type}{lt: relation A}
            {compare : A -> A -> comparison}
            {on : ON lt compare} := A.

Definition on_compare {A:Type}{lt: relation A}
            {compare : A -> A -> comparison}
            {on : ON lt compare} := compare.


Definition on_lt {A:Type}{lt: relation A}
           {compare : A -> A -> comparison}
           {on : ON lt compare} := lt.
Infix "o<" := on_lt : ON_scope.

Definition on_le  {A:Type}{lt: relation A}
           {compare : A -> A -> comparison}
           {on : ON lt compare} :=
  clos_refl _ on_lt.

Infix "o<=" := on_le : ON_scope.

Definition m_lt {A:Type}{lt: relation A}
            {compare : A -> A -> comparison}
            {on : ON lt compare}
            {B : Type}
  (m : B -> A) : relation B :=
  fun x y =>  on_lt (m x) (m y).
            
Lemma wf_measure  {A:Type}(lt: relation A)
            {compare : A -> A -> comparison}
            {on : ON lt compare}
            {B : Type}
            (m : B -> A) :
  well_founded (m_lt m). 
Proof.
  intro x. eapply Acc_incl  with (fun x y =>  on_lt (m x) (m  y)).
  intros y z H.
  apply H.
  eapply Acc_inverse_image.
  apply wf.
Defined.

Hint Resolve wf_measure : core.

Definition ZeroLimitSucc_dec {A:Type}{lt: relation A}
           {compare : A -> A -> comparison}
           {on : ON lt compare} :=
  forall alpha,
    {Least alpha} +
    {Limit alpha} +
    {beta: A | Successor alpha beta}.



(** The segment called [O alpha] in Schutte's book *)

Definition bigO `{nA : @ON A ltA compareA}
           (a: A) : Ensemble A :=
  fun x: A => x o< a.


(** The segment associated with nA is isomorphic to
    the interval [0,b[ *)

Class  SubON 
       `(OA : @ON A ltA  compareA)
       `(OB : @ON B ltB  compareB)
       (alpha :  B)
       (iota : A -> B):=
  {
  subon_compare :forall x y : A,  compareB (iota x) (iota y) =
                                 compareA x y;
  subon_incl : forall x, ltB (iota x) alpha;
  subon_onto : forall y, ltB y alpha  -> exists x:A, iota x = y}.


Class  ON_Iso 
       `(OA : @ON A ltA compareA)
       `(OB : @ON B ltB  compareB)
       (f : A -> B)
       (g : B -> A):=
  {
  iso_compare :forall x y : A,  compareB (f x) (f y) =
                                compareA x y;
  iso_inv1 : forall a, g (f a)= a;
  iso_inv2 : forall b, f (g b) = b}.







(** OA is an ordinal notation for alpha (in Schutte's model) *)

Class ON_for `(alpha : Ord)
     `(OA : @ON A ltA  compareA)
      (iota : A -> Ord) :=
  { ON_for_inj : forall a, lt (iota a) alpha;
    ON_for_onto : forall beta, lt beta alpha ->
                                exists b, iota b = beta;
    On_compare_spec : forall a b:A,
        match compareA a b with
          Datatypes.Lt => lt (iota a) (iota b)
        | Datatypes.Eq => iota a = iota b
        | Datatypes.Gt => lt (iota b) (iota a)
        end}.





Definition SubON_same_cst  `{OA : @ON A ltA  compareA}
       `{OB : @ON B ltB  compareB}
       {iota : A -> B} 
       {alpha: B}
       {_ : SubON OA OB alpha iota}
       (a : A)
       (b : B)
  := iota a = b.



Definition SubON_same_fun  `{OA : @ON A ltA  compareA}
       `{OB : @ON B ltB  compareB}
       {iota : A -> B} 
       {alpha: B}
       {_ : SubON OA OB alpha iota}
       (f : A -> A)
       (g : B -> B)
  :=
    forall x,  iota (f x) = g (iota x).


Definition SubON_same_op  `{OA : @ON A ltA  compareA}
       `{OB : @ON B ltB  compareB}
       {iota : A -> B} 
       {alpha: B}
       {_ : SubON OA OB alpha iota}
       (f : A -> A -> A)
       (g : B -> B -> B)
  :=
  forall x y,  iota (f x y) = g (iota x) (iota y).



Definition ON_cst_ok  {alpha: Ord} `{OA : @ON A ltA  compareA}
       `{OB : @ON B ltB  compareB}
       {iota : A -> Ord} 
       {_ : ON_for alpha OA iota}
       (a : A)
       (b : Ord)
  := iota a = b.



Definition ON_fun_ok  {alpha: Ord} `{OA : @ON A ltA  compareA}
       `{OB : @ON B ltB  compareB}
       {iota : A -> Ord} 
       {_ : ON_for alpha OA iota}
       (f : A -> A)
       (g : Ord  -> Ord)
  :=
    forall x,  iota (f x) = g (iota x).

Definition ON_op_ok  {alpha: Ord} `{OA : @ON A ltA  compareA}
       `{OB : @ON B ltB  compareB}
       {iota : A -> Ord} 
       {_ : ON_for alpha OA iota}
       (f : A -> A -> A)
       (g : Ord  -> Ord -> Ord)
  :=
    forall x y,  iota (f x y) = g (iota x) (iota y).


Definition Iso_same_cst  `{OA : @ON A ltA  compareA}
       `{OB : @ON B ltB  compareB}
       {f : A -> B} {g : B -> A}
       {_ : ON_Iso  OA OB f g}
       (a : A)
       (b : B)
  := f a = b.



Definition Iso_same_fun  `{OA : @ON A ltA  compareA}
           `{OB : @ON B ltB  compareB}
           {f : A -> B} {g : B -> A}
           {_ : ON_Iso  OA OB f g}
           (fA : A -> A)
           (fB : B -> B)
  :=
    forall x,  f (fA x) = fB (f x).


Definition Iso_same_op  `{OA : @ON A ltA  compareA}
           `{OB : @ON B ltB  compareB}
           {f : A -> B} {g : B -> A}
           {_ : ON_Iso  OA OB f g}
           (opA : A -> A -> A)
           (opB : B -> B -> B)
     
  :=
  forall x y,  f (opA x y) = opB (f x) (f y).


(** Technical lemmas *)

Lemma compare_Eq_eq  `{OA : @ON A ltA  compareA} alpha beta :
  compareA alpha beta = Eq -> alpha = beta.
 Proof.
  intro H; destruct (compare_correct alpha beta); auto; discriminate.
 Qed.

Lemma compare_Lt_lt  `{OA : @ON A ltA  compareA} alpha beta :
  compareA alpha beta = Lt -> alpha o< beta.
 Proof.
  intro H; destruct (compare_correct alpha beta); auto; discriminate.
 Qed.


 Lemma compare_Gt_gt  `{OA : @ON A ltA  compareA} alpha beta :
  compareA alpha beta = Gt -> beta o< alpha.
 Proof.
  intro H; destruct (compare_correct alpha beta); auto; discriminate.
 Qed.


 
