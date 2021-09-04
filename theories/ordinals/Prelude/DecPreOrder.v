(**  

 Decidable, Total Pre-orders 

 Pierre Castéran, Univ. Bordeaux and LaBRI 
*)

From Coq Require Export Relations RelationClasses Setoid.

Class Total {A:Type}(R: relation A) :=
  totalness : forall a b:A, R a b \/ R b a.

(** Decision typeclasses following Spitters and van der Weegen *)

Class Decision (P : Prop) := decide : {P} + {~P}.
#[export] Hint Mode Decision ! : typeclass_instances.
Arguments decide _ {_} : simpl never, assert.

Class RelDecision {A B} (R : A -> B -> Prop) :=
  decide_rel x y :> Decision (R x y).
#[export] Hint Mode RelDecision ! ! ! : typeclass_instances.
Arguments decide_rel {_ _} _ {_} _ _ : simpl never, assert.

Notation EqDecision A := (RelDecision (@eq A)).

Definition bool_decide (P : Prop) {dec : Decision P} : bool :=
  if dec then true else false.

Instance Total_Reflexive{A:Type}{R: relation A}(rt : Total R):
  Reflexive R.
Proof. intros a ; now destruct (rt a a). Qed.

Module Semibundled.

Class TotalDec {A:Type}(R: relation A):=
  { total_dec :> Total R ;
    dec_dec :> RelDecision R}.

(** A class of decidable total pre-orders *)

Class TotalDecPreOrder {A:Type}(le: relation A) :=
  {
    total_dec_pre_order :> PreOrder le;
    total_dec_total  :> TotalDec le
  }.

End Semibundled.

(** when applied to a pre-order relation le, returns the equivalence and
    the strict order associated to le *)

Definition preorder_equiv {A:Type}{le:relation A} `{P:@PreOrder A le }(a b : A) :=
  le a b /\ le b a.

Definition lt {A:Type}{le:relation A} `{P:@PreOrder A le }(a b : A) :=
  le a b /\ ~ le b a.

(** A class of total pre-orders *)

Class TotalPreOrder {A} (R : relation A) : Prop := {
  total_pre_order_pre :> PreOrder R;
  total_pre_order_total :> Total R
}.

(** Properties of decidable total pre-orders *)
Lemma lt_irreflexive  {A:Type}{le:relation A}{P:PreOrder le}:
  forall a, ~ lt  a a.
Proof.
 destruct 1; contradiction. 
Qed.

Lemma lt_not_ge {A:Type}{le:relation A}{P:PreOrder le}:
  forall a b,  lt  a b -> ~ le b a.
Proof.
   intros a b [H H0]; assumption.
Qed.

Lemma not_le_ge {A} {le:relation A} {P0 : TotalPreOrder le} :
  forall a b, ~ le a b -> le b a.
Proof.
  intros a b H. destruct P0.
  destruct (totalness a b).
  - contradiction.
  - assumption.
Qed.

Lemma le_not_gt {A:Type}{le:relation A}{P:PreOrder le}:
  forall a b,  le  a b -> ~ lt b a.
Proof.
   intros a b H H0;  now destruct (lt_not_ge b a). 
Qed.


Lemma lt_not_equiv  {A:Type}{le:relation A}{P:PreOrder le}:
  forall a b, lt  a b -> ~ preorder_equiv a b.
Proof.
 intros a b H H0; destruct H, H0; contradiction.
Qed.  

Lemma equiv_not_lt  {A:Type}{le:relation A}{P:PreOrder le}:
  forall a b,  preorder_equiv a b -> ~ lt a b.
Proof.
 intros a b H H0; destruct H, H0; contradiction.
Qed.  


Lemma lt_le_trans {A:Type}{le:relation A}{P:PreOrder le}: 
 forall a b c, lt  a b -> le b c -> lt  a c.
Proof.
  intros a b c [Hab H'ab]  Hbc;  split.
  - now transitivity b.
  - intro H; destruct H'ab; now transitivity c.
Qed.

Lemma le_lt_trans {A:Type}{le:relation A}{P:PreOrder le}: 
 forall a b c, le a b -> lt  b c -> lt  a c.
Proof.
  intros a b c Hab [Hbc H'bc];  split.
  - now transitivity b.
  - intro H; destruct H'bc; now transitivity a.
Qed.

Lemma le_lt_weak {A:Type}{le:relation A}{P:PreOrder le}: 
 forall a b, lt  a b -> le a b.
Proof.  now destruct 1. Qed.


Instance  lt_transitive  {A:Type}{le:relation A}{P:PreOrder le}:
  Transitive lt. 
Proof.
 intros x y z [Hxy H'xy] [Hyz H'yz];  split.
 -    now transitivity y.
 -   intro H; destruct H'yz; now transitivity x.
 Qed.

Instance equiv_equiv {A:Type}{le:relation A} `{P:@PreOrder A le }: Equivalence preorder_equiv.
Proof. 
split.
- intro x;split;reflexivity.
- intros x y Hxy;destruct Hxy;split;auto.
- intros x y z Hxy Hyz; destruct Hxy, Hyz; split; transitivity y;auto.
Qed.

Lemma le_lt_equiv_dec  {A:Type} {le : relation A}
 {P0: TotalPreOrder le} {dec : RelDecision le} (a b:A) :
 le a b -> {lt a b}+{preorder_equiv a b}.
Proof.
  intro H; destruct (decide (le b a)).
  - right;split;auto.
  - left;split;auto.
Defined.

Lemma not_le_gt {A:Type}(le : relation A)
      (P0: TotalPreOrder le) (a b:A) : ~ le a b -> lt b a.
Proof.
  intro H. destruct (totalness b a).
  - split; auto.   
  - contradiction.
Qed.

