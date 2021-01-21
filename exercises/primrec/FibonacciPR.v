From hydras Require Import primRec cPair extEqualNat.

(** The famous Fibonacci function is primitive recursive *)

Fixpoint fib (n:nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | S ((S p) as q) => fib q + fib p
  end.


Section Proof_of_FibIsPR.

  (** let us consider another definition of fib, as an application of
      [nat_rec]
   *)


  Let fib_step (p: nat * nat) := (fst p + snd p, fst p).

  Let fib_iter n p:= (nat_rec (fun _ => (nat*nat)%type)
                              p
                              (fun _ p => fib_step p)
                              n).
  Definition fib_alt n := snd (fib_iter n (1,1)).

  Compute fib_alt 10.

  (** The theory of primitive functions deals only with functions
    of type [naryFunc n]. So, let us define a variant of [fib_alt] 
   *)


  Let fib_step_cPair p := cPair (cPairPi1 p + cPairPi2 p)
                                (cPairPi1 p).

  Let fib_iter_cPair n p := nat_rec (fun _ => nat)
                                    p
                                    (fun _ p => fib_step_cPair p)
                                    n.

  Definition fibPR n := cPairPi2 (fib_iter_cPair n (cPair 1 1)).


  (** Let us prove that [fibPR] is PR *)

  Lemma fibPRIsPR: isPR 1 fibPR.
  Admitted.
  
  
  Lemma L2 : extEqual 1 fib_alt fibPR.
  Admitted.

  Lemma fib_altIsPR : isPR 1 fib_alt.
  Admitted.


  (** It remains to prove that fib_alt is equivalent to the "classical" fib *)
  
  Lemma fib_OK0 : forall n,
      fib_iter n (1,1) = (fib (S n), fib n).
   Admitted.

  Lemma fib_alt_Ok : extEqual 1 fib fib_alt.
  Admitted.

  Theorem fibIsPR : isPR 1 fib.
  Admitted.

End Proof_of_FibIsPR.


(**  * More work!

    This example is an instance of a more general scheme:
    define a function by linear recursion with various base cases,
    _e.g_, 0, 1.

    More generally, we may define primitive recursive functions with the 
    help of [n] functions of type [naryFunc n]
 *)
