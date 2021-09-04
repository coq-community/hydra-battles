(** Formal specification of list sorting functions *)


From Coq Require Export List RelationClasses  Relations Sorting.Permutation
     Sorting.Sorted.
From hydras Require Export DecPreOrder.
From hydras Require Import DecPreOrder_Instances.


Definition sort_fun_t := forall A, (A -> A -> bool) -> list A -> list A.

     
Section R_given.
  
  Variables (A: Type)(R : relation A).

  
  Lemma LocallySorted_cons:
        forall  l a b,  LocallySorted R (b::l) /\ R a b <-> 
                  LocallySorted R (a::b::l).
  Proof with auto.
    intros  l a; split.
    -destruct l; intros H; destruct H as [Eq S].
     + now constructor.
     + constructor; trivial.
    - generalize dependent a.  destruct l.  intros a0 H.
      + split; auto. 
        now inversion_clear  H.
        now inversion H.            
      + 
        inversion  1.
        split;auto.
  Qed.



Definition sort_rel (l l': list A) := 
  LocallySorted R l' /\ Permutation   l l'.

Definition sort_correct  (f: list A -> list A) : Prop :=
  forall l:list A, sort_rel l (f l).



(** already defined in DecPreOrder ? *)

Definition equiv (x y : A) := R x  y /\ R y  x.


Global Instance equiv_equiv (P: PreOrder R): Equivalence equiv.
Proof. 
split.
- intro x;split;reflexivity.
- intros x y Hxy;destruct Hxy;split;auto.
- intros x y z Hxy Hyz; destruct Hxy, Hyz; split; transitivity y;auto.
Qed.



(** Abstract properties *)
(** TODO: look into StdLib's Order whether some lemmas are already
    proved *)

Lemma forall_weak (H: Transitive R):
  forall (l:list A) (a b:A),  R a  b  ->
                         List.Forall (R b) l ->
                         List.Forall (R a) l.
Proof with auto.
  induction 2. 
  - constructor.
  - constructor ...
    transitivity b...  
Qed. 

      
 
(** To remove when it compiles again *)

     Lemma LocallySorted_cons' (Htrans : Transitive R):
        forall l a, List.Forall (R a) l /\ LocallySorted R l <-> 
              LocallySorted R (a::l).
      Proof with auto.
        induction l.
        - split.
          + constructor.
          + split; constructor.
        - split.
         + intros;apply LocallySorted_cons.
           split.
           * now destruct H.
           * destruct H as [H _].
             now inversion H.          
         + inversion 1;split;auto.
           constructor.
           * auto.
           * rewrite <- IHl in H2.
             destruct H2.
             apply forall_weak with a;auto.
      Qed.
      


      Lemma LocallySorted_trans (Htrans : Transitive R):
        forall l a x, LocallySorted R (a::l) -> R x  a ->
                 LocallySorted R (x::l).
      Proof.
        inversion_clear 1.
        -  constructor.
        - intro.  refine (LSorted_consn  x   H0 _).
          + now   transitivity a. 
      Qed.

      
      Lemma LocallySorted_inv_In (Htrans : Transitive R):
        forall l x, LocallySorted R (x::l) ->
               forall y, In y l -> R x y. 
      Proof.
        induction l.
        -  inversion 2.
        -  intros x H y H0; case  (in_inv H0). 
           + intro;subst y;inversion_clear H;auto.
           +   intros; eapply IHl;auto.
               inversion H;  apply LocallySorted_trans with a;auto.
      Qed.

End R_given.


Arguments LocallySorted {A} _ _.
Global Hint Constructors LocallySorted : lists.

(** A sort must work on any decidable total pre-order *)

Definition sort_spec (f : sort_fun_t) :=
 forall (A:Type) (le:relation A) (P:TotalPreOrder le) (dec:RelDecision le) (l:list A),
 let l' := f A (fun x y => bool_decide (le x y)) l in Permutation l l' /\ LocallySorted le l'.

(** A prototype for using TotalDecPreOrder type class *)

Definition sort (f:sort_fun_t)
 {A} {le : relation A} {P: TotalPreOrder le} {dec:RelDecision le}
 (l: list A) :=
  f A (fun x y => bool_decide (le x y)) l.



(** stability *)

Inductive marked {A B : Type}(leA : relation A)(leB : relation B)
          {pA : PreOrder leA}
          {pB : PreOrder leB}:
list (A * B) -> Prop :=
| marked0 : marked leA leB nil
| marked1 : forall a b l, marked leA leB  l ->
            (forall a' b', In (a',b') l ->
                           leA a a' -> lt  b b') ->
            marked leA leB ((a,b)::l).

Definition stable (f : sort_fun_t) : Prop :=
  forall (A B : Type) leA leB
    (PA : TotalPreOrder leA) (PB : TotalPreOrder leB)
    (dec : RelDecision leA) (l : list (A * B)),
         marked leA leB l ->
         marked leA leB (sort f  (P:= Total_Inverse_fun
                                (f:= fst : A * B -> A))
                      l).
                           
(** for testing only *)

Fixpoint mark {A}(l:list A)(from:nat) : list (A * nat) :=
match l with
| nil => nil
| (a::l') => (a,from)::mark l' (S from)
end.


Definition stable_test (f : sort_fun_t)
      {A} {le : relation A}{P: TotalPreOrder le} {dec:RelDecision le}
           (l: list A) : list (A  * nat)                                                               :=
    let m := mark l 0 in
      sort f  (P:= @Total_Inverse_fun (A * nat) A fst le P) m.







