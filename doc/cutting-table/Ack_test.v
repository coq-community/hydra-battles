(* begin snippet AckIntro *)
(*|
==============================
 The famous Ackermann function 
==============================

--------------------------------
   Definitions and properties
--------------------------------

|*)

From hydras Require Export Iterates Exp2.
From Coq Require Import Lia.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.Arith.

(* end snippet AckIntro *)

(* begin snippet AckDefinition *)
(*|

Various definitions
===================


A first try ...
---------------


The following definition fails, because Coq cannot guess a  decreasing argument.
|*)



Fail
  Fixpoint Ack (m n : nat) : nat :=
  match m, n with
  | 0, n => S n
  | S m, 0 => Ack m 1
  | S m0, S p => Ack m0 (Ack m p)
  end.



(*| 

Fortunately, there are still several ways to define the Ackermnn function in Coq. We present a few of them, using the module system to mask all these definitions but one.


Definition with inner fixpoint
------------------------------

|*)


Module Alt.
  
  Fixpoint Ack (m n : nat) : nat :=
    match m with
    | O => S n
    | S p => let fix Ackm (n : nat) :=
                 match n with
                 | O => Ack p 1
                 | S q => Ack p (Ackm q)
                 end
             in Ackm n
    end.

  Compute Ack 3 2.
  
End Alt.


(*| 

Definition using the ``iterate`` functional
--------------------------------------------

   ``iterate : forall {A : Type}, (A -> A) -> nat -> A -> A``


This definition allows  us to to prove monotony properties of ``Ack  m`` by induction on ``m`` (using lemmas from our library ``Prelude.Iterates``). 

|*)

Fixpoint Ack (m:nat) : nat -> nat :=
  match m with
  | 0 => S
  | S n => fun k =>  iterate (Ack n) (S k) 1
  end.

Compute Ack 3 2.


(*| 

Using the lexicographic ordering 
---------------------------------

   (post by Anton Trunov in stackoverflow (May 2018))
|*)

(*| .. coq:: none |*)

Definition lex_nat (ab1 ab2 : nat * nat) : Prop :=
  match ab1, ab2 with
  | (a1, b1), (a2, b2) => 
    (a1 < a2) \/ ((a1 = a2) /\ (b1 < b2))
  end.


(* This is defined in stdlib, but unfortunately it is opaque *)
Lemma lt_wf_ind :
  forall n (P:nat -> Prop),
    (forall n, (forall m, m < n -> P m) -> P n) ->
    P n.
Proof. 
  (* begin snippet inside_lt_wf *)
intro p; intros; elim (lt_wf p); auto with arith. 
  (* end snippet inside_lt_wf *)
Defined.

(* This is defined in stdlib, but unfortunately it is opaque too *)


(* end snippet AckDefinition *)

Lemma lt_wf_double_ind :
  forall P:nat -> nat -> Prop,
    (forall n m,
        (forall p (q:nat), p < n -> P p q) ->
        (forall p, p < m -> P n p) -> P n m) ->
    forall n m, P n m.
Proof.
  intros P Hrec p. pattern p. apply lt_wf_ind.
  intros n H q. pattern q. apply lt_wf_ind. auto.
Defined.

(*||*)

Lemma lex_nat_wf : well_founded lex_nat.
(*| .. coq:: none |*)
Proof.
  intros (a, b); pattern a, b; apply lt_wf_double_ind.
  intros m n H1 H2.
  constructor; intros (m', n') [G | [-> G]].
  - now apply H1.
  - now apply H2.
Defined.
