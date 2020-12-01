

Require Import NArith Ring Monoid_instances Euclidean_Chains Pow AM
        Strategies Dichotomy.

Open Scope N_scope.



Fixpoint fib (n:nat) : N :=
  match n with
    0%nat | 1%nat => 1%N
  | (S ((S p) as q)) => (fib p + fib q)%N
  end.


Lemma fib_ind (P:nat->Prop) :
  P 0%nat -> P 1%nat -> (forall n, P n -> P (S n) -> P(S (S n))) ->
  forall n, P n.
intros.
assert (P n /\ P (S n)).
{ induction n.
  split;auto.
   destruct IHn; split; auto.
}
 tauto.
Qed.

Lemma fib_SSn : forall (n:nat) , fib (S (S n)) = (fib n + fib (S n))%N.
Proof.
  intro n; pattern n; apply fib_ind; try reflexivity.
Qed.


(** Yves' encoding *)


Definition mul2 (p q : N * N) :=
  match p, q with (a, b),(c,d) => (a*c + a*d + b*c, a*c + b*d) end.
  
Lemma neutral_l p : mul2 (0,1)%N p = p.
  unfold mul2. destruct p; f_equal; ring.
Qed.

Lemma neutral_r p : mul2 p (0,1)%N  = p.
  unfold mul2.  destruct p; f_equal; ring.
Qed.

Instance Mul2 : Monoid  mul2 (0,1)%N.
Proof.
  split.
  destruct x,y,z; unfold mul2;  cbn; f_equal; ring.
  intro x; now rewrite neutral_l.
  intro  x; now rewrite neutral_r.
Qed.

Lemma next_fib (n:nat) : mul2 (1,0)%N (fib (S n), fib n) =
                         (fib (S (S n)), fib (S n)).
unfold mul2.
f_equal; ring_simplify.
-  rewrite fib_SSn. ring.
- reflexivity.
Qed.



Lemma fib_power_0 (n:nat) : power (M:=Mul2) (1,0)%N (S (S n)) =
                          (fib (S n), fib n).

Proof.
  induction n.
  - reflexivity. 
  - now rewrite power_eq2, IHn, next_fib.
Qed.

Compute  power (M:=Mul2) (1,0)%N 0%nat.
Compute  power (M:=Mul2) (1,0)%N 1%nat.


Lemma fib_power n : fib n = let (a,b) := power (M:=Mul2) (1,0)%N n
                            in (a+b)%N.
Proof.
pattern n;apply fib_ind; try reflexivity.
- intros; rewrite fib_power_0; now rewrite fib_SSn, N.add_comm.
Qed.

(** Connexion with matrices  (for documentation only) *)


Definition phi (p:N * N) : M2 N :=
  let (a,b) := p in Build_M2 (a+b) a a b.



Lemma phi_morph (p q : N * N) :
  phi (mul2 p q) == (M2_mult N (N.add) (N.mul) (phi p) (phi q))%M.
 Proof.
   destruct p, q; cbn;unfold M2_mult;apply M2_eq_intros; cbn; try ring.
 Qed.


 Lemma power_commute : forall n x,  phi (power (M:= Mul2) x n) =
                                    power (M:=M2N) (phi x) n.
  Proof.
    induction n.
   - reflexivity.
   -  cbn; intro x;  rewrite phi_morph.
      unfold mult_op,  M2_op; now rewrite IHn. 
  Qed.

  (** End of matrices *)


Definition fib_pos n :=
  let (a,b) := Pos_bpow (M:= Mul2) (1,0)%N n in
  (a+b)%N.

Compute fib_pos xH.
Compute fib_pos 10%positive. 

Compute fib_pos 153%positive.
(*  68330027629092351019822533679447
     : N *)


Definition fib_with_chain c :=
  match chain_apply c  Mul2 (1,0)%N with
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






