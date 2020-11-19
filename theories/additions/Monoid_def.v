Require Import RelationClasses.
Require Import Relations Morphisms.
Require Import String.

Set Implicit Arguments.

(** ** The [Monoid] type class (with Operational Type Classes) *)


Declare Scope M_scope.

Class Mult_op (A:Type) := mult_op : A -> A -> A.
Print Mult_op.
(*
Mult_op = fun A : Type => A -> A -> A
     : Type -> Type
*)

Print mult_op.
Goal forall A (op: Mult_op A), @mult_op A op = op.
reflexivity.
Qed.

Delimit Scope M_scope with M.
Infix "*" := mult_op : M_scope.
Open Scope M_scope.

(*
Module Demo.
  
  Instance nat_mult_op : Mult_op nat := Nat.mul.

  Set Printing All.

  Check 3 * 4.

   Unset Printing All.

   Compute 3 * 4.

End Demo.
 *)

Instance string_op : Mult_op string := append.
Open Scope string_scope.

Example ex_string : "ab" * "cde" = "abcde".
Proof. reflexivity. Qed.

Instance bool_and_binop : Mult_op bool := andb.

Example ex_bool : true * false = false.
Proof. reflexivity. Qed.

(*

mult_op : forall (A : Type) (_ : Mult_op A) (_ : A) (_ : A), A

Arguments A, Mult_op are implicit and maximally inserted
*)
(** within M_scope, a term of the form (x * y) is an abbreviation of
(mult_op A op x y) where op : Mult_op A and x, y : A.
*)


Class Monoid {A:Type}(op : Mult_op A)(one : A) : Prop :=
{
    op_assoc : forall x y z, x * (y * z) = x * y * z;
    one_left : forall x, one * x = x;
    one_right : forall x, x * one = x
}.


(** *** Exercice

Define a class for semi-groups, and re-define monoids as semi-groups with a neutral element

*)



(** *** Monoids and Equivalence Relations 

In some situations, the previous definition may be too restrictive.
For instance, consider the computation of  $x^n \mod{m}$ where
$x$ and $m$ are positive integers, and $1<m$.

Although it could possible to compute with values of the dependent 
type %\linebreak% [{n:N | n < m}], it looks simpler to compute with numbers of type
[N], and consider the multiplication $x \times y \mod{m}$.

It is easy to prove that this operation is associative, using library
 %\texttt{NArith}%. Unfortunately, it is not possible to prove the 
following proposition,
required for building an instance of [Monoid]:

[[
forall x:N, 1 * x  mod m = x.
]]

Thus, we define a more general class, parameterized by an equivalence
relation [Aeq] on type [A], compatible with the multiplication $\bullet$. 
The laws of associativity and neutral element
are not expressed as Leibniz equalities but as equivalence statements:
*)


Class Equiv A := equiv : relation A.

Infix "==" := equiv (at level 70) : type_scope.
(*
equiv : forall A : Type, Equiv A -> relation A
*)

Class EMonoid (A:Type)(E_op : Mult_op A)(E_one : A) 
      (E_eq: Equiv A): Prop :=
  {
    Eq_equiv :> Equivalence equiv;
    Eop_proper :> Proper (equiv ==> equiv ==> equiv) E_op;
    Eop_assoc : forall x y z, x * (y * z) == x * y * z;
    Eone_left : forall x,  E_one * x == x;
    Eone_right : forall x,  x * E_one ==  x
  }.


Instance Equiv_Equiv (A:Type)(E_op : Mult_op A)(E_one : A) 
      (E_eq: Equiv A)(M :EMonoid E_op E_one E_eq) :
   Equivalence E_eq.
destruct M;auto.
Qed.

Instance Equiv_Refl (A:Type)(E_op : Mult_op A)(E_one : A) 
      (E_eq: Equiv A)(M :EMonoid E_op E_one E_eq) :
   Reflexive E_eq.
destruct (Equiv_Equiv   M);auto.
Qed.

Instance Equiv_Sym (A:Type)(E_op : Mult_op A)(E_one : A) 
      (E_eq: Equiv A)(M :EMonoid E_op E_one E_eq) :
   Symmetric E_eq.
destruct (Equiv_Equiv   M);auto.
Qed.

Instance Equiv_Trans (A:Type)(E_op : Mult_op A)(E_one : A) 
      (E_eq: Equiv A)(M :EMonoid E_op E_one E_eq) :
   Transitive E_eq.
destruct (Equiv_Equiv   M);auto.
Qed.




Generalizable All Variables.


(** *** Coercion from Monoid to EMonoid 

Every instance of class  [Monoid] can be transformed into an instance of
[EMonoid], considering Leibniz' equality [eq].
*)

Global Instance eq_equiv {A} : Equiv A := eq.

Global Instance Monoid_EMonoid `(M:@Monoid A op one) :
        EMonoid  op one eq_equiv.
Proof.
split; unfold eq_equiv, equiv in *.
 - apply eq_equivalence.
 - intros x y H z t H0;  now subst.
 - intros;now rewrite (op_assoc).
 - intro; now rewrite one_left.
 - intro;now rewrite one_right.
Qed.


(** We can now register [Monoid_EMonoid] as a _coercion_:
*)

Coercion Monoid_EMonoid : Monoid >-> EMonoid.


(** *** Commutative Monoids 

The following type class definitions allow to take advantage of
  the possible commutativity of the $\bullet$ operation 
 
*)

Class Abelian_EMonoid `(M:@EMonoid A op one Aeq ):= {
  Eop_comm : forall x y, op x  y ==  op y  x}.


Class Abelian_Monoid `(M:Monoid ):= {
  op_comm : forall x y, op x  y = op y  x}.


Ltac add_op_proper M H := 
 let h := fresh H in
   generalize (@Eop_proper _ _ _ _ M); intro h.

