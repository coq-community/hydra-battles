(* Trace of a chain *)
(** Solution to an exercise *)

From Coq Require Import List.
Import ListNotations.
Require Import Addition_Chains PArith.


Fixpoint fusion  {A} (compare : A -> A -> comparison)(l1 l2 : list A) :=
      let fix aux l2 {struct l2}:=
          match l1,l2 with
            | nil,_ => l2
            | _,nil => l1
            | a1::l1',a2::l2' =>
              match compare a1 a2 with
                Lt => a2 :: aux  l2'
              | Eq => a1 :: fusion compare l1' l2'
              | Gt => a1 :: fusion compare l1' l2
              end
          end
      in aux l2.

Open Scope positive_scope.

(** Traces with full information *)

Inductive info : Set :=
  Init
| Add (p q : positive).

Definition trace_compare (t t' : positive * info) :=
  match t, t' with
    (x,_),(y,_) => Pos.compare x y end.

Definition trace_mult (l l' : list (positive * info)):=
    match l, l' with
    nil, _ | _,nil => l
  | ((x,_)::l1),((y,_)::l'1) => (x+y,Add x y):: fusion trace_compare l l'
  end.


Definition chain_trace c :=
  List.rev (chain_execute c  trace_mult  ((1,Init)::nil)).

Definition exponents c := List.map fst (chain_trace c).

(* begin snippet traceC87 *)
Compute chain_trace C87.
(* end snippet  traceC87 *)
Compute exponents C87.

Compute chain_trace (binary_chain 87).

