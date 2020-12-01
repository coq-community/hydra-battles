Require Import NArith Ring Monoid_instances Euclidean_Chains Pow AM
        Strategies Dichotomy.

Open Scope N_scope.

(** Yves' encoding *)

Definition phi (p:N * N) : M2 N :=
  let (a,b) := p in Build_M2 (a+b) a a b.


Definition mul2 (p q : N * N) :=
  match p, q with (a, b),(c,d) => (a*c + a*d + b*c, a*c + b*d) end.
  
Lemma neutral_l p : mul2 (0,1)%N p = p.
  unfold mul2. destruct p; f_equal; ring.
Qed.

Lemma neutral_r p : mul2 p (0,1)%N  = p.
  unfold mul2.  destruct p; f_equal; ring.
Qed.

Instance mul2_Mono : Monoid  mul2 (0,1)%N.
Proof.
  split.
  destruct x,y,z; unfold mul2;  cbn; f_equal; ring.
  intro x; now rewrite neutral_l.
  intro  x; now rewrite neutral_r.
Qed. 

Existing Instance M2N.

Lemma phi_morph (p q : N * N) :
  phi (mul2 p q) == (M2_mult N (N.add) (N.mul) (phi p) (phi q))%M.
 Proof.
   destruct p, q; cbn;unfold M2_mult;apply M2_eq_intros; cbn; try ring.
 Qed.


 Lemma power_commute : forall n x,  phi (power (M:= mul2_Mono) x n) =
                                    power (M:=M2N) (phi x) n.
  Proof.
    induction n.
   - reflexivity.
   -  cbn; intro x;  rewrite phi_morph.
      unfold mult_op,  M2_op; now rewrite IHn. 
  Qed.
  


Definition fib_pos n :=
  let (a,b) := Pos_bpow (M:= mul2_Mono) (1,0)%N n in
  (a+b)%N.

Compute fib_pos 10%positive. 

Compute fib_pos 153%positive.
(*  68330027629092351019822533679447
     : N *)


Definition fib_with_chain c :=
  match chain_apply c  mul2_Mono (1,0)%N with
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





