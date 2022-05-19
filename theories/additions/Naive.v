

(** ** Naïve  and Monomorphic  Functions for Computing Powers. *)



(** *** Exponentiation of integers 

Let us define a function [Z.power : Z -> nat -> Z] by structural recursion
on the exponent [n]:
*)

Require Import ZArith.
Open Scope Z_scope. 

Module Z.

Fixpoint power (x:Z)(n:nat) :=
match n with 
| 0%nat => 1
| S p => x *  power x p
end.


(* begin show *)
Compute power 2 10.
(* end show *)  
(** %{\color{lookcolor}
\begin{verbatim}
= 1024 : Z 
\end{verbatim}
}%
*)


(** *** Some basic properties of [Z.power] 

*)

Lemma power_S  : forall (x:Z)(n:nat), power x (S n) = x * power x n.
Proof. reflexivity. Qed.

Lemma power_of_plus (x:Z) :
  forall n p, power x (n + p) = power x n * power x p.
Proof.
 induction n as [ | m IHm].  
 - intro p; simpl (0 + p)%nat ; simpl  power; ring.   
 - intro p; cbn; rewrite IHm; ring.
Qed.   

End Z.


(** *** Exponentiation modulo [m] 

 Let [m] be some natural number. We can compute for any number [x]
and exponent [n] the number $x^n \mod{m}$.

 Since [m] and [x] can be arbitrary large numbers, we give them the type 
[N] of binary natural number. Following our naïve approach, the exponent [n]
is still of type [nat].


*)

Module N_mod.
#[local] Open Scope N_scope.

Section m_fixed.

  Variable m: N.
  
  Definition mult_mod (x y : N) := (x * y) mod m.
  
  Fixpoint power (x: N) (n : nat) : N :=
    match n with
      | 0%nat => 1 mod m
      | S p => mult_mod x (power x p)
    end.
End m_fixed.
End N_mod.

(* begin show *)
Compute N_mod.power 14555553%N 5689%N 27.
(* end show *)

(** %{\color{lookcolor}%
[[
   = 9086410
     : N
]]
%\color{black}%
*)

(** *** Exponentiation of $2\times 2$ matrices

Our last example is a definition of $M^n$ where $M$ is a $2\times 2$ matrix
over any scalar type $A$, assuming one can provide $A$ with a semi-ring structure.

*)
Module M2.
Section Definitions.
  
  Variables (A: Type)
           (zero one : A) 
           (plus mult  : A -> A -> A).
  
  Variable rt : semi_ring_theory  zero one plus mult   (@eq A).
  Add Ring Aring : rt.

  Notation "0" := zero.  
  Notation "1" := one.
  Notation "x + y" := (plus x y).  
  Notation "x * y " := (mult x y).
  
  Structure t : Type := mat{c00 : A;  c01 : A;
                            c10 : A;  c11 : A}.
  
  Definition Id2 : t := mat 1 0 0 1.
  
  Definition M2_mult (M M':t) : t :=
    mat (c00 M * c00 M' + c01 M * c10 M')
        (c00 M * c01 M' + c01 M * c11 M')
        (c10 M * c00 M' + c11 M * c10 M')
        (c10 M * c01 M' + c11 M * c11 M').
  
  Infix "**" := M2_mult (at level 40, left associativity).

  Fixpoint power (M : t) (n : nat) : t :=
    match n with
      | 0%nat => Id2
      | S p =>  M ** (power M p)
    end.

  
  (** **** 
   The [ring] tactic, applied to inhabitants of type [A], allows us to
   prove associativity of matrix multiplication, then a law of 
   distributivity of [power] upon [**]
   *)

  Lemma Id2_neutral : forall M:t, Id2 ** M = M.
  Proof.
    destruct M;unfold Id2, M2_mult;simpl;f_equal; ring.
  Qed.

  Lemma M2_mult_assoc : forall M M' M'':t,  M ** (M' ** M'') =
                                            (M ** M') ** M''.
  Proof.
   destruct M, M', M''; simpl;unfold M2_mult;f_equal;simpl; ring.
  Qed.  

  Lemma power_of_plus (M:t) :
  forall n p, power M (n + p) =  power M n **  power M p.
  Proof.
    induction n as [ | m IHm].  
    - intro p; simpl (0 + p)%nat; simpl (power M 0); now rewrite Id2_neutral.
    - intro p; cbn;  now rewrite IHm, M2_mult_assoc. 
  Qed.   
  
End Definitions.
End M2.


Definition fibonacci (n:nat) :=
  M2.c00 N (M2.power N 0%N 1%N Nplus Nmult (M2.mat _ 1 1 1 0)%N  n).

Compute fibonacci 20.

