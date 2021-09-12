
(** * Compatibility with StdLib exponentiation functions  

Function for computing powers already  exist in %\coq%'s standard library. We provide
equivalence theorems with functions defined in our module [Pow].


 *)

Require Import Monoid_def Lia Monoid_instances
     ArithRing  Pow.


(** ** really logarithmic versions of N.pow, Pos.pow and Z.pow 
 
We propose three functions that are extensionnaly equivalent to functions
of the standard library.
These functions are defined in the %\href{../Powers/SRC/Pow.v}{Powers/SRC/Pow.v}% module;  we just rename them for readability's sake.

*)

Definition N_pow (a n: N) :=Pow.N_bpow a n.

Definition Pos_pow (a n : positive) := Pow.Pos_bpow a  n.

Definition Z_pow (x y : Z) :=
 match y with 
| 0%Z => 1%Z
| Z.pos p => Pow.N_bpow x (Npos  p)
| Z.neg _ => 0%Z
end.

(** **  Equivalence between StdLib definitions and ours *)

Section Equivalence.
Variable (A: Type)
         (op : Mult_op A)
         (one : A).

Context (M : Monoid  op one).
Open Scope M_scope.

Check fun x y:A =>  x * y.


Ltac monoid_rw :=
    rewrite (@one_left A op one M) || 
    rewrite (@one_right A op one M)|| 
    rewrite (@op_assoc A op one M).

  Ltac monoid_simpl := repeat monoid_rw.

 Ltac power_simpl := repeat (monoid_rw || rewrite <- power_of_plus).


 Let pos_iter_M x := Pos.iter (op x).

 (**
  
  During an execution of the binary exponentiation algorithm
  through the function [binary_power_mult],
  the  "accumulator" [acc] is always a power of $x$. Thus, even if the 
  considered monoid is not abelian, the accumulator commutes with any 
  other power of $x$.
 

 *)
 Let is_power_of (x acc:A) := exists i, acc = x ^ i.


Lemma  Pos_iter_op_ok_0 : 
  forall p x acc, is_power_of x acc ->
                  pos_iter_M x acc  p = binary_power_mult x acc p .
Proof.
  induction p.
  -  simpl.
     intros;  rewrite IHp.
     rewrite (IHp x acc).
     repeat rewrite (binary_power_mult_ok M).
     rewrite <- (sqr_eqn M x).
     rewrite power_of_power.
     rewrite (mult_comm  (Pos.to_nat p) 2)%nat. 
     destruct H as [i e].
     repeat rewrite  (op_assoc (Monoid:=M)). 
     subst acc.
     rewrite  <- (power_commute_with_x ).
     replace (2* Pos.to_nat p)%nat with (Pos.to_nat p + Pos.to_nat p)%nat.

     + rewrite power_of_plus.
       now rewrite (op_assoc (Monoid:=M)). 
     + ring.
     + assumption.
     +  rewrite IHp;auto.
        rewrite (binary_power_mult_ok M).
        destruct H as [i Hi].
        exists (i + Pos.to_nat p)%nat.
        rewrite power_of_plus.
        subst acc;auto.

  - simpl;  intros;   rewrite IHp.
    rewrite (IHp  x acc).
    repeat rewrite (binary_power_mult_ok M); rewrite  <- (sqr_eqn M).
    repeat (rewrite (op_assoc (Monoid:=M))).
    rewrite power_of_power.
    rewrite (mult_comm  (Pos.to_nat p) 2)%nat. 
    replace (2* Pos.to_nat p)%nat with (Pos.to_nat p + Pos.to_nat p)%nat.  
    + rewrite power_of_plus;now  rewrite op_assoc.
    + ring.
    + assumption.
    + rewrite IHp, (binary_power_mult_ok M).
      destruct H as [i Hi].
      exists (i + Pos.to_nat p)%nat.
      rewrite power_of_plus.
      subst acc;auto.
      auto.
  -   intros; simpl. change (op x acc) with (x * acc). 
      destruct H as [i Hi]; subst acc.
      apply power_commute_with_x.
Qed.

Lemma  Pos_iter_op_ok:
  forall p x,  
    pos_iter_M x one  p = binary_power_mult   x one p .
Proof.
 intros p x; rewrite Pos_iter_op_ok_0;auto.
 now exists 0%nat.
Qed.

Lemma  Pos_iter_ok: forall p x,  N_bpow x (Npos p) = pos_iter_M x one   p.
Proof.
  intros p x; rewrite Pos_iter_op_ok_0.
  unfold N_bpow.   
  rewrite Pos_bpow_ok.
  generalize  (binary_power_mult_ok M (E_eq := eq_equiv)).
  unfold equiv, eq_equiv.
  intro H; rewrite H. 
  now  rewrite (one_left (Monoid := M)).
  exists 0%nat.
  reflexivity.
Qed.

End Equivalence.

Lemma Pos_pow_power : forall n a : positive ,
                        (a  ^ n )%positive  = power a  (Pos.to_nat n).
Proof.
 intros n a; unfold Pos.pow.
 rewrite (Pos_iter_op_ok _ _ _ PMult).
 generalize  (binary_power_mult_ok  (E_one := xH) (E_eq := eq_equiv)).
 intro H; rewrite H. 
 rewrite one_left.
 reflexivity.
Qed.

Lemma Npos_power_compat : forall (n:nat)(a:positive),
                            Npos (power a  n) = power (Npos a)  n.
Proof. 
  induction n.
 - now compute.
 -  intros;  repeat rewrite  power_eq2; now rewrite <- IHn.
Qed.

Lemma N_pow_power : forall n a , (a  ^ n )%N  = power a (N.to_nat n).
Proof.
 intros n a; unfold N.pow.
 destruct n as [ | p].
-   compute; reflexivity.
-   simpl; destruct a.
  +   assert (0 <> Pos.to_nat p)%nat.
      { generalize (Pos2Nat.is_pos p).
        intro;lia.
      }
      generalize H;  clear H; generalize (Pos.to_nat p).
       intro n;induction n;simpl;auto.
       destruct 1;auto.
   + rewrite Pos_pow_power;now rewrite Npos_power_compat.
Qed.

Lemma N_pow_compat : forall n (a:N),   (a  ^ n )%N = N_pow a n.
Proof. 
 intros. unfold N_pow;  rewrite N_bpow_ok; now rewrite  N_pow_power.
Qed.


Lemma Pos_pow_compat : forall n (a:positive),  (a  ^ n )%positive = Pos_pow  a n.
Proof.
 unfold Pos_pow; intros;rewrite Pos_bpow_ok; now rewrite  Pos_pow_power.
Qed.


Lemma nat_power_ok : forall a b:nat, (a ^ b)%nat = (a ^ b)%M.
induction b;simpl.
 trivial.
  rewrite IHb;auto.
Qed.

  Lemma Pos2Nat_morph : forall (n:nat)(a : positive), 
     Pos.to_nat (a ^ n)%M = Pos.to_nat a ^ n.
  induction n.
  intro;simpl; reflexivity.    
  intro; simpl.
   rewrite Pos2Nat.inj_mul.
   rewrite IHn.
    reflexivity.
  Qed.

Lemma Z_pow_compat_pos : forall (p:positive) (x:Z), 
        Z.pow_pos x p = N_bpow x (Npos  p).
Proof. 
 intros; unfold Z.pow_pos.
 rewrite (Pos_iter_op_ok _ _ _ ZMult).
  rewrite (binary_power_mult_ok (E_one := 1%Z) (E_eq := eq_equiv)).
 rewrite N_bpow_ok.
 rewrite (one_left  (Monoid := ZMult)) . 
 reflexivity.
Qed.

Lemma Z_pow_compat : forall x y: Z, Z_pow x y = (x ^ y)%Z.
Proof.
 intros x y; unfold Z_pow, Z.pow.
 destruct y; [ | rewrite Z_pow_compat_pos | ]; reflexivity.
Qed.

(** ** Tests 

Let us chose a big exponent, and a computation that does not create 
big numbers. So, the following computation time will be proportional to
 the number of recursive calls, hence to the number of multiplications

*)

(** Time consuming !
[[
Time Compute (1 ^ 56666667)%Z.
]]
*)
Time Compute (1 ^ 56666667)%Z.
(** 
[[
Finished transaction in 3.604 secs (3.587u,0.007s) 
]]
*)


Time Compute (Z_pow 1 56666667)%Z.
(** 
[[
Finished transaction in 0. secs (0.u,0.s) (successful)
]]
*)


(** *** Adapting lemmas from Standard Library 

Standard library already contains many lemmas about 
[N.pow], [Pos.pow] and [Z.pow]. By using our extensional equivalence properties, one can 
  easily prove the same properties for our implementation of the same functions.

We just give a simple example of this adaptation.

*)
Section Adaptation.


Lemma N_size_gt : forall n : N, (n < N_pow 2 (N.size n))%N.
Proof. 
  intro n; rewrite  <- N_pow_compat.
  apply N.size_gt.  
Qed.

End Adaptation.
 
(** Comments on Stdlib's exponentiation *)

Print Z.pow.

Print Z.pow_pos.
(*
Z.pow_pos = fun z : Z => Pos.iter (Z.mul z) 1%Z
     : Z -> positive -> Z
 *)

(*

Pos.iter = 
fun (A : Type) (f : A -> A) =>
fix iter_fix (x : A) (n : positive) {struct n} : A :=
  match n with
  | (n'~1)%positive => f (iter_fix (iter_fix x n') n')
  | (n'~0)%positive => iter_fix (iter_fix x n') n'
  | 1%positive => f x
  end
     : forall A : Type, (A -> A) -> A -> positive -> A
*)

Eval simpl in   fun  (x:nat) => Pos.iter S x 12%positive.


(* The computation of iter_fix x n  needs n calls to f 
   Thus, iter_fix is linear and not logarithmic ! 
 *)




