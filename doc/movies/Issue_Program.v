From Coq Require Import Lia.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.Arith.


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
Proof. intro p; intros; elim (lt_wf p); auto with arith. Defined.

(* This is defined in stdlib, but unfortunately it is opaque too *)



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


Lemma lex_nat_wf : well_founded lex_nat.
Proof.
  intros (a, b); pattern a, b; apply lt_wf_double_ind.
  intros m n H1 H2.
  constructor; intros (m', n') [G | [-> G]].
  - now apply H1.
  - now apply H2.
Defined.

  
  Program Fixpoint Ack (ab : nat * nat) {wf lex_nat ab} : nat :=
    match ab with
    | (0, b) => b + 1
    | (S a, 0) => Ack (a, 1)
    | (S a, S b) => Ack (a, Ack (S a, b))
    end.
  Next Obligation.
    injection Heq_ab; intros; subst.
    left; auto with arith.
  Defined.
  Next Obligation.
    apply lex_nat_wf.
  Defined.
  
  Example test1 : Ack (1, 2) = 4 := refl_equal.  


  Example test2 : Ack (3, 4) = 125 := eq_refl.
  (* this may take several seconds *)
  
