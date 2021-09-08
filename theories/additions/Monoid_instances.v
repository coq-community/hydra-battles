(** ** Some useful instances of Monoid classes 

File %\href{../Powers/SRC/Monoid_instances.v}{Powers/SRC/Monoid\_instances}
defines various instances of [Monoid] and [EMonoid].
*)

Require Export Monoid_def.
Require Import RelationClasses Morphisms.

Require Import ZArith PArith.
Require Import Arith.
Require Import NArith.
Require Import Ring31.

Open Scope Z_scope.

(** *** Multiplicative monoid on [Z] *)

(* begin snippet ZMultDef *)
Instance Z_mult_op : Mult_op Z := Z.mul.

Instance ZMult : Monoid  Z_mult_op 1. (* .no-out *)
Proof. (* .no-out *)
  split.
    all: unfold Z_mult_op, mult_op;intros;ring.
Qed.
(* end snippet ZMultDef *)


Instance ZMult_Abelian : Abelian_Monoid ZMult.
Proof.
  split; exact Zmult_comm.
Qed.


(** *** Multiplicative monoid on [nat] *)

(* begin snippet natMult:: no-out *)

Instance nat_mult_op : Mult_op nat | 5 := Nat.mul.

Instance  Natmult : Monoid nat_mult_op  1%nat | 5.
Proof.
   split;unfold nat_mult_op, mult_op; intros; ring.
Qed.
(* end snippet natMult *)

(** *** Additive monoid on [nat] 

The following monoid is useful for proving the correctness of complex
exponentiation algorithms. In effect, the $n$-th "power" of $1$ is
equal to $n$. See Sect.%~\ref{chains-exponent}.
*)

(* begin snippet natPlus:: no-out *)
Instance nat_plus_op : Mult_op nat | 12 := Nat.add.

Instance Natplus : Monoid nat_plus_op  0%nat | 12.
Proof.
   split;unfold nat_plus_op, mult_op; intros; ring.
Qed.

(* end snippet natPlus *)


Open Scope N_scope.

Instance N_mult_op  : Mult_op N | 5 := N.mul.

Instance NMult : Monoid N_mult_op 1 | 5.
Proof.
  split;unfold N_mult_op, mult_op; intros; ring.
Qed.


(* begin snippet CheckCoercion *)
Check NMult : EMonoid  N.mul 1%N eq.
(* end snippet CheckCoercion *)


Instance N_plus_op  : Mult_op N | 12 := N.add.

Instance NPlus : Monoid N_plus_op 0 | 12.
Proof.
  split;unfold N_plus_op, mult_op; intros; ring.
Qed.


(** Multiplicative Monoid on [positive] 
*)

Instance P_mult_op : Mult_op positive | 5  := Pos.mul .

Instance PMult : Monoid P_mult_op xH | 5.
Proof.
 split;unfold P_mult_op, Mult_op;intros.  
 -  now rewrite Pos.mul_assoc.
 - reflexivity.
 - now rewrite Pos.mul_1_r.
Qed.


Import Int31.
Open Scope int31_scope.

(** ***  Multiplicative monoid on 31-bits integers 

Cyclic numeric types are  good candidates for testing exponentiations
with big exponents, since the size of data is bounded.


The type [int31] is defined in Standard Library in Module
[Coq.Numbers.Cyclic.Int31.Int31].
*)

(* begin snippet int31:: no-out *)
Instance int31_mult_op : Mult_op int31 := mul31.

Instance  Int31mult : Monoid int31_mult_op  1.
Proof.
   split;unfold int31_mult_op, mult_op; intros; ring.
Qed.
(* end snippet int31 *)



  (* begin snippet BadFact *)
Module Bad.
  
  Fixpoint int31_from_nat (n:nat) :=
    match n with
    | O => 1
    | S p => 1 + int31_from_nat p
    end.
  
  Coercion int31_from_nat : nat >-> int31.
  
  Fixpoint fact (n:nat) := match n with
                             O => 1
                           | S p => n * fact p
                           end.
  Compute fact 40. 

End Bad. 
(* end snippet BadFact *)


Close Scope int31_scope.


(** *** Monoid of 2x2 matrices 

Let $A$ be some type, provided with a ring structure. We define the multiplication 
of $2\times 2$-matrices, the coefficients of which have type $A$.

*)

(* begin snippet M2Defsa *)

Section M2_def.
Variables (A:Type)
           (zero one : A) 
           (plus mult  : A -> A -> A).

 Notation "0" := zero.  
 Notation "1" := one.
 Notation "x + y" := (plus x y).  
 Notation "x * y " := (mult x y).

 Variable rt : semi_ring_theory  zero one plus mult (@eq A).
 Add  Ring Aring : rt.


Structure M2 : Type := {c00 : A;  c01 : A;
                        c10 : A;  c11 : A}.

Definition Id2 : M2 := Build_M2 1 0 0 1.

Definition M2_mult (m m':M2) : M2 :=
 Build_M2 (c00 m * c00 m' + c01 m * c10 m')
          (c00 m * c01 m' + c01 m * c11 m')
          (c10 m * c00 m' + c11 m * c10 m')
          (c10 m * c01 m' + c11 m * c11 m').

(* end snippet M2Defsa *)


Lemma M2_eq_intros : forall a b c d a' b' c' d',
  a=a' -> b=b' -> c=c' -> d=d' ->
   Build_M2 a b c d = Build_M2 a' b' c' d'.
Proof. 
 intros; now f_equal.
Qed.

(* begin snippet M2Defsb:: no-out *)

Global Instance M2_op : Mult_op M2 := M2_mult.

Global Instance M2_Monoid : Monoid   M2_op Id2.
(* ... *)
(* end snippet M2Defsb *)
Proof. 
 unfold M2_op, mult_op; split.
 - destruct x;destruct y;destruct z;simpl.
   unfold M2_mult; apply M2_eq_intros; simpl; ring.
 - destruct x;simpl;
   unfold M2_mult; apply M2_eq_intros; simpl; ring. 
 - destruct x;simpl;
   unfold M2_mult;apply M2_eq_intros;simpl;ring. 
Qed.

End M2_def.

Arguments M2_Monoid {A zero one plus mult} rt.
Arguments Build_M2 {A} _ _ _ _.

(** Matrices over N *)
Definition M2N := M2_Monoid Nth.


(** *** Integers modulo m

The following instance of [EMonoid] describes the set of integers modulo
$m$, where $m$ is some integer greater or equal than $2$.
For simplicity's sake, we represent such values using the type [N],
and consider "equivalence modulo $m$" instead of equality.
*)


Section Nmodulo.
  Variable m : N.
  Hypothesis m_gt_1 : 1 < m.
  
  Remark m_neq_0 : m <> 0.
    intro H;subst m. discriminate. 
  Qed.
  
  Local Hint Resolve m_neq_0 : chains.
  
  Definition mult_mod ( x y : N) := (x * y) mod m.
  Definition mod_eq ( x y: N) := x mod m = y mod m.
  
  Local Instance mod_equiv : Equiv N := mod_eq.

  Local Instance mod_op : Mult_op N := mult_mod.
  
  Local Instance mod_Equiv : Equivalence mod_equiv.
  Proof.
    split.
    - intros x; reflexivity.
    - intros x y H; now symmetry.  
    - intros x y z Hxy Hyz; transitivity (y mod m) ; auto.
  Qed.
  
    
  Global Instance mult_mod_proper :
    Proper (mod_equiv ==> mod_equiv ==> mod_equiv) mod_op.
  Proof.
    unfold mod_equiv, mod_op, mult_mod, mod_eq.
    intros x y Hxy z t Hzt.
    repeat rewrite N.mod_mod; auto with chains.
    rewrite (N.mul_mod x z);auto with chains.
    rewrite (N.mul_mod y t);auto with chains.
    rewrite Hxy, Hzt; reflexivity.
   Qed.


  Local  Open Scope M_scope.

  Lemma mult_mod_associative :  forall x y z,
                                  x * (y * z) = x * y * z.
  Proof.
    intros  x y z.
    unfold mod_op, mult_op, mult_mod.
    rewrite N.mul_mod_idemp_r;auto with chains.
    rewrite N.mul_mod_idemp_l;auto with chains.
    now rewrite  N.mul_assoc.
  Qed.

  
  Lemma one_mod_neutral_l  : forall x, 1 * x == x.
  Proof.
    unfold equiv, mod_equiv, mod_eq, mult_op, mod_op, mult_mod.
    intro x; rewrite N.mul_1_l, N.mod_mod; auto with chains.
   Qed.

  Lemma one_mod_neutral_r  : forall x, x * 1 == x.
  Proof.
    unfold equiv, mod_equiv, mod_eq, mult_op, mod_op, mult_mod.
    intro x; rewrite N.mul_1_r, N.mod_mod; auto with chains.
   Qed.


  Global Instance Nmod_Monoid : EMonoid  mod_op 1 mod_equiv.
  Proof.
    unfold equiv, mod_equiv, mod_eq, mult_op, mod_op, mult_mod.
    split.
    - exact mod_Equiv.
    - exact mult_mod_proper.
    - intros; rewrite mult_mod_associative; reflexivity.
    - exact one_mod_neutral_l.
    - exact one_mod_neutral_r.
  Defined.
 

End Nmodulo.

Section S256.

Let mod256 :=  mod_op 256.

Local Existing Instance mod256 | 1.

Compute (211 * 67)%M.

(** = 57 : N *)
End S256.

Compute (211 * 67)%M.
(** = 14137 : N *)


Close Scope N_scope.
Close Scope positive_scope.



