

From Coq Require Import NArith Ring.

From additions Require Import Monoid_instances Euclidean_Chains Pow
        Strategies Dichotomy BinaryStrat.
Import Addition_Chains. 
Open Scope N_scope.


(* begin snippet FibDef *)
Fixpoint fib (n:nat) : N :=
  match n with
    0%nat | 1%nat => 1
  | (S ((S p) as q)) => fib p + fib q
  end.


Compute fib 20.
(* end snippet FibDef *)

Lemma fib_ind (P:nat->Prop) :
  P 0%nat -> P 1%nat -> (forall n, P n -> P (S n) -> P(S (S n))) ->
  forall n, P n.
Proof.
intros H0 H1 HS n; assert (P n /\ P (S n)).
{ induction n.
  - split;auto.
  - destruct IHn; split; auto.
}
 tauto.
Qed.

Lemma fib_SSn : forall (n:nat) , fib (S (S n)) = (fib n + fib (S n)).
Proof.
  intro n; pattern n; apply fib_ind; try reflexivity.
Qed.


(** Yves' encoding *)

(* begin snippet mul2Def *)
Definition mul2 (p q : N * N) :=
  match p, q with
    (a, b),(c,d) => (a*c + a*d + b*c, a*c + b*d)
  end.
(* end snippet mul2Def *)

Lemma neutral_l p : mul2 (0,1) p = p.
  unfold mul2. destruct p; f_equal; ring.
Qed.

Lemma neutral_r p : mul2 p (0,1)  = p.
  unfold mul2.  destruct p; f_equal; ring.
Qed.

(* begin snippet mul2Monoid  *)
#[ global ] Instance Mul2 : Monoid  mul2 (0,1).
(* end snippet mul2Monoid  *)

Proof.
  split.
  destruct x,y,z; unfold mul2;  cbn; f_equal; ring.
  intro x; now rewrite neutral_l.
  intro  x; now rewrite neutral_r.
Qed.

(* begin snippet nextFib:: no-out *)
Lemma next_fib (n:nat) : mul2 (1,0) (fib (S n), fib n) =
                         (fib (S (S n)), fib (S n)).
(* end snippet nextFib *)
Proof.
  unfold mul2; f_equal; ring_simplify.
  -  rewrite fib_SSn. ring.
  - reflexivity.
Qed.

(* begin snippet fibMul2Def *)
Definition fib_mul2 n := let (a,b) := power (M:=Mul2) (1,0) n
                         in (a+b).

Compute fib_mul2 20.
(* end snippet fibMul2Def *)

(* begin snippet fibMul2OK0:: no-out *)
Lemma fib_mul2_OK_0 (n:nat) :
  power (M:=Mul2) (1,0) (S (S n)) =
  (fib (S n), fib n).
Proof.
  induction n.
  (* ... *)
  (* end snippet fibMul2OK0 *)
  - reflexivity. 
  - now rewrite power_eq2, IHn, next_fib.
Qed.

(* begin snippet fibMul2OK:: no-out *)
Lemma fib_mul2_OK n : fib n = fib_mul2 n.
(* end snippet fibMul2OK *)
Proof.
 unfold fib_mul2; pattern n;apply fib_ind; try reflexivity.
 - intros; rewrite fib_mul2_OK_0; now rewrite fib_SSn, N.add_comm.
Qed.

(* begin snippet TimeFibMul2 *)
Time Compute fib_mul2 87.
(* end snippet TimeFibMul2 *)

(* begin snippet fibPos *)
Definition fib_pos n :=
  let (a,b) := Pos_bpow (M:= Mul2) (1,0) n in
  (a+b).

Compute fib_pos xH.
Compute fib_pos 10%positive. 

Time Compute fib_pos 153%positive.
(* end snippet fibPos *)

Locate chain_apply.
About chain_apply.

(* begin snippet fibEuclDemo *)
Definition fib_eucl gamma `{Hgamma: Strategy gamma} n :=
  let c := make_chain gamma  n
  in let r := chain_apply c (M:=Mul2) (1,0) in
       fst r + snd r.

Time Compute fib_eucl dicho  153.
Time Compute fib_eucl two  153.
Time Compute fib_eucl half 153.
(* end snippet fibEuclDemo *)


(*  68330027629092351019822533679447
     : N 
Finished transaction in 0.002 secs (0.002u,0.s) (successful)
*)

From additions Require Import AM.

Definition fib_with_chain c :=
  match chain_apply c  Mul2 (1,0) with
    Some ((a,b), nil) => Some (a+b) | _ => None end.

Definition c153 := chain_gen dicho (gen_F 153%positive).

Compute c153.

(*
  = (PUSH :: SQR :: SQR :: SQR :: MUL :: PUSH :: 
     SQR :: SQR :: SQR :: SQR :: MUL :: nil)%list
     : code

*)
(* number of multiplications and squares *)

Compute mults_squares c153.


Compute fib_with_chain c153 .

(*
 = Some 68330027629092351019822533679447
     : option N
*)

Compute mults_squares (chain_gen dicho (gen_F 30000%positive)).

(*   = (6%nat, 13%nat)
     : nat * nat  *)






