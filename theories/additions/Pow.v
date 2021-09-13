(** * Exponentiation   in a Monoid 

In this section, we give two polymorphic functions for computing
 $x^n$: the  naive (%\emph{i.e.}% linear) one and the aforementionned 
binary method, that takes less than $2\times \log_2(n)$ multiplications.

 Both functions require an instance of [EMonoid]. Their code use the 
 multiplication of the monoid, and sometimes  its  unity. 
  Correctness proofs require the "axioms" of monoid structure.
 *)



Set Implicit Arguments.

Require Export ZArith  Div2.
Require Export Recdef.
Require Import Relations Morphisms.

Require Import Monoid_def.
Require Import Arith Lia.

Open Scope M_scope.


(** ** Two functions for computing powers 

 The  module defines two functions for exponentiation on any [Emonoid] 
  on carrier $A$.
 
  - The function [power] has type [A -> nat -> A]; it is linear with respect to 
    the exponent. Its simplicity and the fact that the exponent has type [nat] 
    make it adequate for being the reference for any other definition, and for 
    easily proving laws like $x^{n+p}=x^n \times x^p$.
    %\footnote{Cite : Refinement for free!}%

 - The function [Pos_bpow] has type [A -> positive -> A] and is logarithmic
   with respect to its exponent. This function should be used for effective
   computations. Its variant [N_bpow] allows the exponent to be $0$.

*)

(** *** The "naive" reference function *)
Generalizable Variables  A E_op E_one E_eq.


(* begin snippet powerDef *)
Fixpoint power `{M: @EMonoid A  E_op E_one E_eq}
         (x:A)(n:nat) :=
  match n with 0%nat => E_one
             | S p =>   x *  x ^ p
  end
where "x ^ n" := (power x n) : M_scope.
(* end snippet powerDef *)

(* begin snippet powerEqns:: no-out *)

Lemma power_eq1  `{M: @EMonoid A  E_op E_one E_eq}(x:A) :
  x ^ 0 = E_one.
Proof. reflexivity. Qed.


Lemma power_eq2  `{M: @EMonoid A  E_op E_one E_eq}(x:A) (n:nat) :
 x ^ (S n)  = x * x ^ n.
Proof. reflexivity. Qed.

Lemma power_eq3  `{M: @EMonoid A  E_op E_one E_eq}(x:A) :
 x ^ 1 == x.
Proof. cbn;  rewrite Eone_right; reflexivity. Qed.
(* end snippet powerEqns *)

(* end snippet powerEqns *)

(** *** The binary exponentiation function (exponents in  [positive])  *)

  (**  *** 

The auxiliary function below computes  $acc \times x ^p$, where
the "accumulator" [acc] is intented to be an already computed power of [x]:

*) 

(* begin snippet binaryPowerMult *)
Fixpoint binary_power_mult  `{M: @EMonoid A E_op E_one E_eq} 
         (x a:A)(p:positive) : A 
  :=
  match p with
    | xH =>  a * x
    | xO q => binary_power_mult (x * x) a q
    | xI q =>  binary_power_mult  (x * x) (a * x) q
  end.
(* end snippet binaryPowerMult *)

 (** *** 

The  following function decomposes the exponent [p]
  into $2 ^ k \times q$ , then calls [binary_power_mult]
   with $x^{2^k}$ and $q$.

*)

(* begin snippet PosBpow *)
Fixpoint Pos_bpow  `{M: @EMonoid A E_op E_one E_eq}
         (x:A)(p:positive) :=
 match p with
  | xH => x
  | xO q => Pos_bpow  (x * x) q
  | xI q => binary_power_mult  (x * x) x q
end.
(* end snippet PosBpow *)

(** ***
  It is straightforward to adapt [Pos_bpow]
 for accepting exponents of type [N] :
*)

(* begin snippet NBpow *)
Definition N_bpow  `{M: @EMonoid A E_op E_one E_eq} x (n:N) := 
  match n with 
  | 0%N => E_one
  | Npos p => Pos_bpow x p
  end.

Infix "^b" := N_bpow (at level 30, right associativity) : M_scope.
(* end snippet NBpow *)

(** ** Properties of the power function 

 Taking [power] as a reference, it remains to prove two kinds of properties
  - Mathematical properties of exponentiation, _i.e_ the function [power],

  - proving  correctness of functions [Pos_bpow] and [N_bpow]

First, let us consider some [Emonoid] and define some useful notations and tactics:
*)

(* begin snippet MGiven *)
Section M_given.
  
  Variables (A:Type) (E_one:A) .
  Context (E_op : Mult_op A) (E_eq : Equiv A)
          (M:EMonoid  E_op E_one E_eq).
(* end snippet MGiven *)

Global Instance Eop_proper : Proper (equiv ==> equiv ==> equiv) E_op.
Proof.
  apply  Eop_proper.
Qed.

(* begin snippet monoidRw *)
Ltac monoid_rw :=
    rewrite Eone_left  ||
    rewrite Eone_right  || 
    rewrite Eop_assoc.

Ltac monoid_simpl := repeat monoid_rw.
(* end snippet monoidRw *)

(* *** Properties of the classical exponentiation  *)

(* begin snippet powerProper:: no-out *)
Global Instance power_proper :
  Proper (equiv ==> eq ==> equiv) power.
(* end snippet powerProper *)
Proof.
  intros x y Hxy n p Hnp;  subst p; induction n.
  - reflexivity.
  - cbn; now rewrite IHn, Hxy.
Qed.

(* begin snippet powerOfPlus:: no-out *)
Lemma power_of_plus :
  forall x n p, x ^ (n + p) ==  x ^ n *  x ^ p.
(* end snippet powerOfPlus *)
Proof.
  induction n; cbn; intro.
  - monoid_simpl; reflexivity.
  - rewrite IHn.
    monoid_simpl; reflexivity.
Qed.

(* begin snippet powerSimpl *)
Ltac power_simpl := repeat (monoid_rw || rewrite <- power_of_plus).
(* end snippet powerSimpl *)

(* begin snippet powerCommute:: no-out *)
Lemma power_commute x n p: 
  x ^ n * x ^ p ==  x ^ p * x ^ n. 
Proof.
 power_simpl; now rewrite (plus_comm n p).
Qed.

Lemma power_commute_with_x x n:
  x * x ^ n == x ^ n * x.
Proof.
  induction n; cbn.
  - now monoid_simpl.
  - rewrite IHn at 1; now monoid_simpl.
Qed.

Lemma power_of_power x n p:
  (x ^ n) ^ p == x ^ (p * n).
Proof.
  induction p; cbn.
  - reflexivity.
  - rewrite IHp; now power_simpl. 
Qed.
(* end snippet powerCommute *)


Lemma power_of_power_comm x n p : (x ^ n) ^ p == (x ^ p) ^ n.
Proof.
  repeat rewrite power_of_power.
  now rewrite Nat.mul_comm.
Qed.

(* begin snippet sqrEqn:: no-out *)
Lemma sqr_eqn : forall x, x ^ 2 ==  x * x.
(* end snippet sqrEqn *)
Proof.
  intros; cbn;  now monoid_simpl.
Qed.


Ltac factorize := repeat (
                rewrite <- power_commute_with_x ||
                rewrite  <- power_of_plus  ||
                rewrite <- sqr_eqn ||
                rewrite <- power_eq2 ||
                rewrite power_of_power).

(* begin snippet powerOfSquare:: no-out *)
Lemma power_of_square x n : (x * x) ^ n ==  x ^ n * x ^ n.
Proof.
  induction n; cbn; monoid_simpl.
  - reflexivity.
  - rewrite IHn; now factorize.
Qed.
(* end snippet powerOfSquare *)

(** ** Correctness of the binary algorithm 

Correctness of the "concrete" functions [Pos_bpow] and [N_bpow]
with respect to the more abstract function [power] is expressed 
by  extensional equalities, taking into account the conversion between 
various representations of natural numbers.

*)



Lemma binary_power_mult_ok :
  forall p a x,   binary_power_mult  x a p  ==  a * x ^ Pos.to_nat p.
Proof.
  induction p as [q IHq | q IHq|].
  (**  %\textcolor{red}{\it rest of proof skipped}  *)
  - (* 2 * q + 1 *)
    intros; cbn.
    rewrite Pos2Nat.inj_xI, IHq.
    rewrite power_eq2, Eop_assoc.
    rewrite <- power_of_power, sqr_eqn, power_of_square; reflexivity.
  - (* 2 * q *)
    intros; cbn.
    rewrite Pos2Nat.inj_xO, IHq.
    rewrite <- power_of_power, sqr_eqn, power_of_square; reflexivity.
  - (* 1 *)
    intros; cbn.
    simpl (x ^ Pos.to_nat 1).
    now monoid_rw.
Qed.


Lemma Pos_bpow_ok : 
  forall p x, Pos_bpow x p == x ^ Pos.to_nat p.
Proof.
  induction p; cbn; intros.
  - rewrite binary_power_mult_ok, Pos2Nat.inj_xI.
    factorize.
    apply power_proper; [reflexivity | lia].
  - rewrite IHp, Pos2Nat.inj_xO.
    factorize.
    apply power_proper; [reflexivity | lia].
  - simpl.
    now monoid_rw.
Qed.

Global Instance Pos_bpow_proper :
  Proper  (equiv ==> eq ==> equiv) Pos_bpow.
Proof.
  intros x y Hxy n p Hnp. subst n. revert  x y Hxy.
  induction p; cbn; intros; trivial.
  - repeat rewrite binary_power_mult_ok.  
    factorize.
    apply power_proper; auto.
  - apply IHp. now apply Eop_proper.
Qed.

(* begin snippet NBpowOk:: no-out *)
Lemma N_bpow_ok : 
  forall n x, x ^b n == x ^ N.to_nat n.
(* end snippet NBpowOk *)
Proof.
  destruct n.
  - (* 0 *) reflexivity.
  - apply Pos_bpow_ok.
Qed.


Lemma N_bpow_ok_R : 
  forall n x, x ^b  (N.of_nat n) == x ^ n.
Proof.
  intros; rewrite N_bpow_ok; now rewrite Nnat.Nat2N.id.
Qed.


Lemma Pos_bpow_ok_R : 
  forall p x, p <> 0 ->
              Pos_bpow x (Pos.of_nat p)   ==  x ^  p.
Proof.
  intros; rewrite Pos_bpow_ok; now rewrite Nat2Pos.id.
Qed.


Lemma N_bpow_commute : forall x n p,  
                        x ^b n *  x ^b p ==  
                        x ^b p *  x ^b n.
Proof.
  intros x n p; repeat rewrite N_bpow_ok.
  apply power_commute.
Qed.

Lemma Pos_bpow_of_plus : forall x n p, Pos_bpow x  (n + p)%positive ==
                                       Pos_bpow x  n *  Pos_bpow x  p.
Proof.
  intros; repeat rewrite Pos_bpow_ok.
  rewrite Pos2Nat.inj_add.
  now rewrite power_of_plus.
Qed.

Lemma Pos_bpow_of_bpow : forall (x:A) n p,
    Pos_bpow (Pos_bpow x n) p == Pos_bpow x (p * n)%positive.
Proof.
  intros; repeat rewrite Pos_bpow_ok.
  rewrite Pos2Nat.inj_mul.
  now rewrite power_of_power.
Qed.



(** ** Remark

Iw we normalize exponentiation functions with a given exponent, we notice
that the obtained functions do not execute the same computations, but it is
hard to visualize why the binary method is more efficient than the naive one.


*)
(* begin show *)

Eval simpl in     fun (x:A) => x ^b 17.
(** [[ 
  = fun x : A =>
       x *
       (x * x * (x * x) * (x * x * (x * x)) *
        (x * x * (x * x) * (x * x * (x * x))))
     : A -> A
]]
*)
Eval simpl in   fun x => x ^ 17.

(** [[
= fun x : A =>
       x * (x *  (x *  (x *  (x *   (x *  (x *  (x *
           (x * (x * (x * (x * (x * (x * (x * (x * (x * one))))))))))))))))
     : A -> A
]]
*)

(* end show *)

Definition pow_17  (x:A) :=
  let x2 := x * x in
  let x4 := x2 * x2 in
  let x8 := x4 * x4 in
  let x16 := x8 * x8 in
  x16 * x.

Eval cbv  zeta beta delta [pow_17]  in  pow_17.
(**
 = fun x : A =>
       x * x * (x * x) * (x * x * (x * x)) *
       (x * x * (x * x) * (x * x * (x * x))) * x
     : A -> A
*)

(**
In order to compare the real computations needed to raise some $x$ to its $n$-th
power, we need to make more explicit how intermediate values are used during 
some computation. 
This is described in the module %\texttt{Chains}% (see %\vref{chains-section}%).

*)

(** ** Properties of Abelian Monoids 
 
 Some equalities hold in the restricted context of abelian (a.k.a. commutative)
 monoids. 
*)

Section Power_of_op.
 Context  {AM:Abelian_EMonoid M}.
 
Theorem power_of_mult :
   forall n x y,  (x * y)  ^ n ==  x ^ n *  y ^ n. 
Proof.
 induction n;simpl.
 -  intros;rewrite Eone_left;auto.
    reflexivity.
-  intros; rewrite IHn; repeat rewrite Eop_assoc.
    rewrite <- (Eop_assoc  x y (power x n)); rewrite (Eop_comm y (power x n)).
    repeat rewrite Eop_assoc;reflexivity. 
Qed.

End Power_of_op.



End M_given.

Infix "^" := power : M_scope.


   
Ltac monoid_simpl M := generalize (Eop_proper M); intro; 
  repeat ( rewrite (Eone_left ) || 
    rewrite (Eone_right  ) || 
    rewrite (Eop_assoc )).

  Ltac power_simpl M := generalize (Eop_proper M); intro; 
  repeat ( rewrite Eone_left  ||  rewrite Eone_right ||  rewrite Eop_assoc 
     || rewrite power_of_plus).

