(**

  Complements to Coq.Logic.Epsilon


  Pierre Casteran,
  LaBRI, University of Bordeaux
*)

From Coq Require Export  Ensembles  Logic.Epsilon.

(* begin snippet EpsilonStatement  *)
Print epsilon_statement.
(* end snippet EpsilonStatement  *)

(* begin snippet epsilonDef *)
Print epsilon.

Check constructive_indefinite_description.
(* end snippet epsilonDef *)

(* begin snippet iotaDef *)
Check iota_statement.

Print iota.

Print iota_spec.
(* end snippet iotaDef *)

Set Implicit Arguments.
Arguments In {U} _ _.


 Lemma epsilon_ind {A:Type} (inh : inhabited A) (P Q : A -> Prop):
   (ex P ) -> (forall a, P a -> Q a) -> Q (epsilon inh P).
 Proof.
   intros exP P_Q;  apply P_Q,  epsilon_spec.
   case exP ;intros x H; exists x;assumption.
 Qed.


Theorem epsilon_equiv  {A:Type}(a: inhabited A)(P:A->Prop):
  (ex P)<-> P (epsilon a P).
Proof.
 split.
 - intros; apply epsilon_ind; auto.
 - exists (epsilon a P); auto.
Qed.

Ltac epsilon_elim_aux :=
  match goal with [ |- (?P (epsilon (A:=?X) ?a ?Q))] =>
           apply epsilon_ind; auto
  end.

Ltac epsilon_elim := epsilon_elim_aux ||
  match goal with
  [ |- (?P (?k ?d))] =>
   (let v := eval cbv zeta beta delta [k]  in (k d) in
     (match v with (epsilon ?w ?d) => change (P v); epsilon_elim_aux end))
  | [ |- (?P (?k ?arg ?arg1))] =>
   (let v := eval cbv zeta beta delta [k]  in (k arg arg1) in
     (match v with (epsilon ?w ?d) => change (P v); epsilon_elim_aux end))
  | [ |- (?P ?k)] =>
   (let v := eval cbv zeta beta delta [k]  in k in
     (match v with (epsilon ?w ?d) => change (P v); epsilon_elim_aux end))
  end.


Section On_Iota.
  Variables (A:Type)(P: A -> Prop).
  Hypothesis  inhA : inhabited A.
  Hypothesis unique_P : exists ! x, P x.

  Lemma iota_spec_1 : unique P (iota inhA P).
  Proof.
    generalize  (iota_spec inhA P unique_P).
    destruct unique_P as [x H]; intro H0;split;auto.
    intros x' Hx'; destruct H;  transitivity x; auto.
    now rewrite (H1 _ H0).
  Qed.

  Lemma iota_eq : forall a, P a -> a = iota inhA P.
  Proof.
    intros a Ha; destruct unique_P as [x Hx], Hx as [H H0]; transitivity x.
    - symmetry;auto.
    - apply H0; now apply iota_spec.
  Qed.


  Lemma iota_ind (Q:A -> Prop) :
    (forall a, unique P a -> Q a) ->  Q (iota inhA P).
  Proof.
    intro H;apply H; now apply iota_spec_1.
  Qed.

End On_Iota.

Ltac iota_elim :=
  match goal with |- context c [(iota ?b ?P)] =>
  apply iota_ind end.


(* begin snippet Defs *)

Class InH (A: Type) : Prop :=
   InHWit : inhabited A.

Definition some {A:Type} {H : InH A} (P: A -> Prop)
  := epsilon (@InHWit A H) P.

Definition the {A:Type} {H : InH A} (P: A -> Prop)
  := iota (@InHWit A H) P.
(* end snippet Defs *)


#[ global ] Instance inhNat : InH nat.
 split;  exact 42.
Qed.


(** A small example *)

(* begin show *)

Definition some_pos := some (fun i => 0 < i).


Example Ex1 : 1 <= some_pos.
    unfold some_pos, some; epsilon_elim.
    exists 42;   auto with arith.
Qed.

(* end show *)
