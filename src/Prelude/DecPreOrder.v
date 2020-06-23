(**  

 Decidable, Total Pre-orders 

*)

Require Export Relations RelationClasses Setoid.

Class Total {A:Type}(R: relation A) :=
  totalness : forall a b:A, R a b \/ R b a.             

Class Decidable {A:Type}(R: relation A) :=
  rel_dec : forall a b, {R a b} + {~ R a b}.


Instance Total_Reflexive{A:Type}{R: relation A}(rt : Total R):
  Reflexive R.
Proof. intros a ; now destruct (rt a a). Qed.

Class TotalDec {A:Type}(R: relation A):=
  { total_dec :> Total R ;
    dec_dec :> Decidable R}.

Definition left_right_dec {A:Type}{R: relation A}{T : Total R}{D: Decidable R}:
  forall a b, {R a b}+{R b a}.
Proof.  
  intros a b; destruct (D a b).
  - now left.
  - right; destruct (T a b);[contradiction|trivial].
Defined.


(** when applied to a pre-order relation le , return the equivalence and
    the strict order associated to le *)

Definition preorder_equiv {A:Type}{le:relation A} `{P:@PreOrder A le }(a b : A) :=
  le a b /\ le b a.

Definition lt {A:Type}{le:relation A} `{P:@PreOrder A le }(a b : A) :=
  le a b /\ ~ le b a.

Definition strict  {A:Type}(R:relation A) := fun x y => R x y /\ x <> y.



(** A class of decidable total pre-orders *)

Class TotalDecPreOrder {A:Type}(le: relation A) :=
  {
    total_dec_pre_order :> PreOrder le;
    total_dec_total  :> TotalDec le 
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

Lemma not_le_ge {A:Type}{le:relation A}{P0: TotalDecPreOrder le}:
  forall a b,  ~ le  a b ->  le b a.
Proof.
  intros a b H; destruct P0. destruct (left_right_dec b a).
  - assumption.
  -  contradiction.
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

(** weakening of le_dec *)

Definition leb {A:Type}(le : relation A)
      {P0: TotalDecPreOrder le} (a b : A) :=
   if rel_dec a b then true else false.

Lemma leb_true {A:Type}(le : relation A)
      (P0: TotalDecPreOrder le) (a b:A) :
  leb le a b = true <-> le a b.
Proof.
  unfold leb;split.
  -   destruct (rel_dec a b);auto; discriminate.
  -  intro;  destruct (rel_dec a b);auto.
      contradiction.
Qed.   

(** if Hle assumes (le a b), asserts  (H: leb le a b = true) *)

Ltac le_2_leb  Hle H:=
  match goal with [Q : @TotalDecPreOrder ?A ?R, Hle: ?R ?x ?b |- _] => 
                  let HH := fresh in
                  let hypo := fresh H in
                  destruct (@leb_true _ _ Q x b ) as
                      [_ HH]; generalize (HH Hle); clear HH; intro  hypo
  end.

(** if Hlen assumes (leb a b = true), asserts  (H: le a b ) *)

Ltac leb_2_le Hleb H:=
 match goal with [Q : @TotalDecPreOrder ?A ?R,
                      Hleb : @leb ?A ?R ?Q ?x ?b = true |- _] => 
                 let HH := fresh in
                 let hypo := fresh H in
                 destruct (@leb_true _ _ Q x b ) as
                     [HH _]; generalize (HH Hleb); clear HH; intro  hypo
 end.


Lemma leb_false {A:Type}(le : relation A)
      (P0: TotalDecPreOrder le) (a b:A) :
  leb le a b = false <-> lt  b a.
Proof.
  unfold leb, lt;split.
  -   destruct (rel_dec a b);auto.  
      + discriminate.
      +   intros _; destruct (rel_dec b a); auto.
          split;auto.
          { destruct (left_right_dec a b);try contradiction. }
  -  destruct (rel_dec a b).
     + destruct 1; contradiction.   
     +   auto . 
Qed.   


Lemma le_lt_equiv_dec  {A:Type}(le : relation A)
      (P0: TotalDecPreOrder le) (a b:A) :
   le a b -> {lt a b}+{preorder_equiv a b}.
Proof.
  intro H;  destruct (rel_dec b a).
 -   right;split;auto.
 -  left;split;auto.
Defined.


Lemma not_le_gt {A:Type}(le : relation A)
      (P0: TotalDecPreOrder le) (a b:A) : ~ le a b -> lt b a.
Proof.
  intro H; destruct (left_right_dec b a).
  - split; auto.   
  - contradiction.
Qed.

