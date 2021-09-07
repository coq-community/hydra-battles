(** Polymorphic versions of exponentiation functions *)

Require Import Arith ZArith.
Require Import String.

(** 
  Polymorphic exponentiation functions 
 *)

(* begin snippet Defs *)
Section Definitions.

 Variables (A : Type)
           (mult : A -> A -> A)
           (one : A).

Local Infix "*" := mult.
Local Notation "1" := one.

(**  Naive (linear) implementation *)

Fixpoint power (x:A)(n:nat) : A :=
  match n with
    | 0%nat => 1
    | S p =>   x * x ^ p
  end
where "x ^ n" := (power x n).
(* end snippet Defs *)


(** Logarithmic implementation (with exponents in [N])  *)

(* begin snippet bpowDef *)

Fixpoint binary_power_mult (x a:A)(p:positive) : A 
  :=
  match p with
    | xH =>  a * x
    | xO q => binary_power_mult  (x * x) a q
    | xI q =>  binary_power_mult  (x * x) (a * x) q
  end.

Fixpoint Pos_bpow   (x:A)(p:positive) :=
 match p with
  | xH => x
  | xO q => Pos_bpow  (x * x) q
  | xI q => binary_power_mult   (x * x) x q
end.


Definition N_bpow  x (n:N) := 
  match n with 
  | 0%N => 1
  | Npos p => Pos_bpow x p
  end.

(* end snippet bpowDef *)

(* begin snippet EndDefs *)
End Definitions.

Arguments N_bpow  {A}.
Arguments power  {A}.
(* end snippet EndDefs *)



(** **  Examples *)

(* begin snippet PowerCompute *)
Compute power Z.mul 1%Z 2%Z 10.

Compute N_bpow Z.mul 1%Z 2%Z 10.

Open Scope string_scope.

Compute power append  "" "ab"  12.

Compute N_bpow append  "" "ab"  12.
(* end snippet PowerCompute *)

(** Exponentiation on 2x2 matrices *)

(* begin snippet M2a *)

Module M2.
Section M2_Definitions.
  
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

(* end snippet M2a *)

(* begin snippet M2Mult *)
  Definition M2_mult (M M':t) : t :=
    mat (c00 M * c00 M' + c01 M * c10 M')
        (c00 M * c01 M' + c01 M * c11 M')
        (c10 M * c00 M' + c11 M * c10 M')
        (c10 M * c01 M' + c11 M * c11 M').

End M2_Definitions.
End M2.

Import M2.

Arguments M2_mult {A} plus mult  _  _.
Arguments mat {A} _ _ _ _.
Arguments Id2 {A}  _ _.
(* end snippet M2Mult *)

Definition fibonacci (n:N) :=
 c00 N  (N_bpow  (M2_mult Nplus Nmult) (Id2  0%N 1%N)(mat  1 1 1 0)%N n).

 Compute fibonacci 20.


(* begin snippet powerTDef *)
Definition power_t := forall (A:Type)
                             (mult : A -> A -> A)
                             (one:A)
                             (x:A)
                             (n:N), A.
(* end snippet powerTDef *)

(** * A wrong definition of correctness *)

(* begin snippet Bada *)
Module Bad.

  Definition correct_expt_function (f : power_t) : Prop :=
    forall A (mult : A -> A -> A) (one:A)
           (x:A) (n:N), power mult one x (N.to_nat n) =
                        f A mult one x n.
  (* end snippet Bada *)
  
(* begin snippet Badb:: no-out *)
  Section CounterExample.
    Let mul (n p : nat) := n + 2 * p.
    Let one := 0.

    (** With our fake definition, [N_bpow] is not correct! *)
    
    Remark mul_not_associative :
      exists  n p q,  mul n (mul p q) <> mul (mul n p) q.
    Proof.
      exists 1, 1, 1; discriminate. 
    Qed.

    Remark one_not_neutral  :
      exists n : nat, mul one n <> n.
    Proof.
      exists 1; discriminate.
    Qed.

    Lemma correct_exp_too_strong : ~ correct_expt_function (@N_bpow).
    Proof.
      intro H; specialize (H _ mul one 1  7%N).
      discriminate H.
    Qed.

  End CounterExample.

End Bad.
(* end snippet Badb *)

(** Fibonacci matrices *)
(*

Open Scope Z_scope. 
Definition encode (p: Z*Z) := let (a,b) := p in  mat (a+b)%Z a a b.

Definition id2 := (0,1).
Definition matfib2 := (1, 0).
Definition mul2 (m m' : Z*Z) := let (a,b) := m in
                        let (c,d) := m' in
                        ((a+b)*c + a*d, a*c + b*c).


Compute mul2 id2 matfib2.
Compute mul2 matfib2 id2.


Lemma mul2_assoc (m m' m'': Z*Z):
      mul2 (mul2 m m') m'' = mul2 m (mul2 m' m'').
destruct m,m',m''.
  unfold mul2.
 f_equal. ring_simplify.
Abort.

Definition yves_fib (n:nat) := let p := power mul2 id2 matfib2 n in
                               fst p + snd p.

Compute yves_fib 10.
Compute yves_fib 0.
Compute yves_fib 20.

Compute power mul2 id2 matfib2 4%nat.

*)
