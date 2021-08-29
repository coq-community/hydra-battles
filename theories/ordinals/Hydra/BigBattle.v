(** * A long hydra battle

  Pierre Castéran, LaBRI, Univ Bordeaux 

 *)


From Coq Require Import Arith Relations Lia.
From hydras Require Import Hydra_Definitions Hydra_Lemmas Iterates Exp2.


(** Let us consider a small hydra [hinit] *)

(* begin snippet hinitDef *)
Notation  h3 := (hyd_mult head 3).
Definition hinit := hyd3 h3  head head.
(* end snippet hinitDef *)


(** 
the first steps of a standard battle (Hercules chops off the rightmost head)
*)





(* begin snippet L02 *)
(*| .. coq:: no-out |*)
Lemma L_0_2 : battle standard 0 hinit 2 (hyd1 h3). 
Proof. 
  eapply battle_trans with (h := hyd2 h3 head) (i:=1).
  (* ... *) (*| .. coq:: none |*)
  - left; trivial.
    red. cbn. chop_off 1.
  - left; trivial.
    red; left;  trivial.
    split; repeat constructor. 
(*||*)
Qed.
(* end snippet L02 *)

(** In the next round, there is a replication of h3 into 3 copies of h2 

More generally,  all the future hydras will be composed of several copies
of h2, then several copies of h1, then several heads *)

(* begin snippet Notations *)

Notation h2 := (hyd_mult head 2).
Notation h1 := (hyd1 head).

Notation hyd a b c := 
  (node (hcons_mult h2  a
             (hcons_mult h1  b
                         (hcons_mult head c hnil)))).

(* end snippet Notations *)

(* begin snippet L23L03 *)
(*| .. coq:: no-out |*)
Lemma L_2_3 : battle standard 2 (hyd1 h3)  3 (hyd 3 0 0).
Proof.  
  left; trivial; right ;  simpl;  left; left.
  split; right; right; left.
Qed.

Lemma L_0_3 : battle standard 0 hinit 3 (hyd 3 0 0).
Proof.
  eapply battle_trans.
  - apply L_2_3.
  - apply L_0_2.
Qed.
(*||*)
(* end snippet L23L03 *)

(** From now on, we abstract the configurations of the battle
  as tuples (round number, n2, n1, nh) where n2 (resp. n1, nh) is the number of 
  sub-hydras h2 [resp. h1, heads] *)

(* begin snippet stateDef *)

Record state : Type :=
  mks {round : nat ; n2 : nat ; n1 : nat ; nh : nat}.

(* end snippet stateDef *)

(* begin snippet nextDef *)

Definition next (s : state) :=
  match s with
  | mks round a b (S c) => mks (S round) a b c
  | mks round a (S b) 0 => mks (S round) a b (S round)
  | mks round (S a) 0 0 => mks (S round) a (S round) 0
  | _ => s
  end.

(* end snippet nextDef *)


(** returns the state at the n-th round *)

(* begin snippet testDefTests *)

Definition test n := iterate next (n-3)  (mks 3 3 0 0).

Compute test 3.

Compute test 4.

Compute test 5.

Compute test 2000.

(* end snippet testDefTests *)

(* begin snippet smartTest *)


Compute test 10.

(* end snippet smartTest *)

(* begin snippet smartTestb *)

Compute test 22.

Compute test 46.

Compute test 94.

(* end snippet smartTestb *)

(* begin snippet smartTestc *)

Compute test 95.

(* end snippet smartTestc *)


(* begin snippet doubleS *)

Definition doubleS (n : nat) := 2 * (S n).

Compute test (doubleS 95).


Compute test (iterate doubleS 2 95).

(* end snippet doubleS *)



(** OK, instead of tests based on the function next, we consider now
    relations (which allow us to consider accessibility predicates)  *)



(** steps  i a b c j a' b' c' has  almost the same meaning as
    iterate test (j - i) (mks t a b c) = (mks t' a' b' c')

 *)

(* begin snippet oneStep *)

Inductive one_step (i: nat) :
  nat -> nat -> nat -> nat -> nat -> nat -> Prop :=
| step1: forall a b c,  one_step i a b (S c) a b c
| step2: forall a b ,  one_step i a (S b) 0 a b (S i)
| step3: forall a, one_step i (S a) 0 0 a (S i) 0.

(* end snippet oneStep *)

(* begin snippet stepBattle *)

Lemma step_battle : forall i a b c a' b' c',
    one_step i a b c a' b' c' ->
    battle standard i (hyd  a b c)
           (S i) (hyd a' b' c'). (* .no-out *)
(*|
.. coq:: none
|*)
Proof.
  
  destruct 1.
  - left; trivial;  left;  split.
    apply hcons_mult_S0.   
    apply hcons_mult_S0. 
    simpl; now left. 
  - left; trivial; right.
    left.       
    apply hcons_mult_S1; simpl.
    rewrite <- hcons_mult_comm.
    apply hcons_mult_S1.
    unfold hyd_mult; cbn.
    left;  split; constructor.

  - left; trivial;  right; left.
    simpl; rewrite  <- hcons_mult_comm;  apply hcons_mult_S1.
    left; split;  simpl;  right; constructor.
Qed.

(*||*)

(* end snippet stepBattle *)

(* begin snippet steps *)

Inductive steps : nat -> nat -> nat -> nat ->
                  nat -> nat -> nat -> nat -> Prop :=
| steps1 : forall i a b c a' b' c',
    one_step i a b c a' b' c' -> steps i a b c (S i) a' b' c'
| steps_S : forall i a b c j a' b' c' k a'' b'' c'',
    steps i a b c j a' b' c' ->
    steps j a' b' c' k a'' b'' c'' ->
    steps i a b c k  a'' b'' c''.

(**  reachability (for i > 0) *)

Definition reachable (i a b c : nat) : Prop :=
  steps 3 3 0 0 i a b c.

(* end snippet steps *)

(* begin snippet stepsBattle *)

Lemma steps_battle : forall i a b c j  a' b' c',
    steps i a b c j a' b' c' ->
    battle standard i (hyd  a b c) j (hyd a' b' c'). (* .no-out *)
(*|
.. coq:: none 
|*)
Proof.
  induction 1.
  - now apply step_battle.
  - eapply battle_trans.
   +   apply IHsteps2.
   +  assumption.
Qed.
(*||*)

(* end snippet stepsBattle *)

(**  From now on, we play again the same tests as above, but instead of plain uses of Compute, we prove and register lemmas that we will be used later *)

(* begin snippet L4 *)

(*|
.. coq:: no-out 
|*)
Lemma L4 : reachable 4 2 4 0.
Proof.
  left; constructor.
Qed.
(*||*)
(* end snippet L4 *)


(** Now we prove some laws we observed in our test phase *)

(* begin snippet LS *)

(*|
.. coq:: no-out
|*)
Lemma LS : forall c a b i,  steps i a b (S c) (i + S c) a b 0.
Proof.
  induction c.
 -  intros;  replace (i + 1) with (S i).
    + repeat constructor.
    + ring.
 -  intros; eapply  steps_S.
    +  eleft;   apply step1.
    + replace (i + S (S c)) with (S i + S c) by ring;  apply IHc.
Qed.


(**   The law that relates two consecutive events with  (nh = 0)  *)


Lemma doubleS_law : forall  a b i, steps i a (S b) 0 (doubleS i) a b 0.
Proof.
  intros;  eapply steps_S.
  +   eleft;   apply step2.
  +   unfold doubleS; replace (2 * S i) with (S i + S i) by ring; 
        apply LS.
Qed.

Lemma reachable_S  : forall i a b, reachable i a (S b) 0 ->
                                   reachable (doubleS i) a b 0.
Proof.
  intros; right with  (1 := H); apply doubleS_law.
Qed.

(* end snippet LS *)

(* begin snippet L10To95 *)

(*|
.. coq:: no-out
|*)

Lemma L10 : reachable 10 2 3 0.
Proof.
  change 10 with (doubleS 4).
  apply reachable_S, L4.
Qed.

Lemma L22 : reachable 22 2 2 0.
Proof.
  change 22 with (doubleS 10).
  apply reachable_S, L10.
Qed.


Lemma L46 : reachable 46 2 1 0.
Proof.
  change 46 with (doubleS 22); apply  reachable_S, L22.
Qed.

Lemma L94 : reachable 94 2 0 0.
Proof.
  change 94 with (doubleS 46); apply reachable_S, L46.
Qed.

Lemma L95 : reachable 95 1 95 0.
Proof.
  eapply steps_S.
  -  eexact L94.
  -  repeat constructor.
Qed.

(*||*)

(* end snippet L10To95 *)

Lemma L0_95 : battle standard 3 (hyd 3 0 0) 95 (hyd 1 95 0).
Proof.
  apply steps_battle.
  apply L95.
Qed.

  
(** No more tests ! we are going to build bigger transitions *)


(* begin snippet Bigstep *)

(*|
.. coq:: no-out
|*)

Lemma Bigstep : forall b i a , reachable i a b 0 ->
                               reachable (iterate doubleS b i) a 0 0.
 Proof.
  induction b.
  -  trivial.
  -  intros;  simpl;   apply reachable_S in H.
     rewrite <- iterate_comm; now apply IHb.
 Qed.

 (*||*)

(* end snippet Bigstep *)

 
 (** From all the lemmas above, we now get a pretty big step *)


 (* begin snippet MDef *)
 
Definition M := iterate doubleS 95 95.

Lemma L2_95 : reachable M 1 0 0. (* .no-out *)
Proof. (* .no-out *)
  apply Bigstep,  L95.
Qed.

(* end snippet MDef *)

(** the next step creates (M+1) copies of h1 *)

(* begin snippet L295S  *)

(*|
.. coq:: no-out
|*)

Lemma L2_95_S : reachable (S M) 0 (S M) 0.
Proof.
  eright.
 - apply L2_95.
 -  left; constructor 3.
Qed.

(*||*)

(* end snippet L295S  *)

(* begin snippet NDef *)

Definition N :=   iterate doubleS (S M) (S M).

Theorem   SuperbigStep : reachable N  0 0 0. (* .no-out *)
Proof.  (* .no-out *)
  apply Bigstep, L2_95_S.
Qed.

(* end snippet NDef *)


(** We can  ow apply our study based on abstract states to "real" hydras *)


(** transforming our relation one_step into standard battles *)




(** We get now statements about hydras and battles *)

(* begin snippet Done *)

(*|
.. coq:: no-out
|*)

Lemma Almost_done :
  battle standard 3 (hyd 3 0 0) N (hyd 0 0 0).
Proof. 
  apply steps_battle, SuperbigStep.
Qed.

Theorem Done :
  battle standard 0 hinit N head.
Proof.
  eapply battle_trans.
  - apply Almost_done.
  - apply L_0_3.
Qed.

(*||*)

(* end snippet Done *)

(** The natural number N is expressed in terms of the (iterate doubleS)
   function.  The rest of this file is dedicated to get an intuition of how it is huge .
     Our idea is to get a minoration by exponentials of base 2 

 *)

(* begin snippet minorationLemmas *)
Lemma minoration_0 : forall n,  2 * n <= doubleS n. (* .no-out *)
(*| .. coq:: none |*)
Proof.
  unfold doubleS;intros; abstract lia.
Qed.
(*||*)

Lemma minoration_1 : forall n x, exp2 n * x <= iterate doubleS n x. (* .no-out *)
(*| .. coq:: none |*)
Proof.
  induction n; simpl.
  -  intro;  abstract lia.
  -  intros; unfold doubleS. 
     transitivity (2 * iterate doubleS n x).
    +  specialize (IHn x). ring_simplify. lia. 
    +  unfold doubleS; abstract lia.
Qed.
(*||*)

Lemma minoration_2 : exp2 95 * 95 <= M. (* .no-out *)
(*| .. coq:: none |*)
Proof. apply minoration_1. Qed.
(*||*)

Lemma minoration_3 : exp2 (S M) * S M <= N. (* .no-out *)
(*| .. coq:: none |*)
Proof. apply minoration_1.  Qed.
(*||*)

(*| .. coq:: none |*)
Lemma exp2_mono1 : forall n p,  n <= p ->  exp2 n  <= exp2 p .
Proof.
  induction 1.
  - reflexivity.   
  -  rewrite exp2S;  abstract lia.
Qed.
(*||*)

Lemma minoration : exp2 (exp2 95 * 95) <= N. (* .no-out *)
(*| .. coq:: none |*)
Proof.
  transitivity (exp2 (S M) * S M).
  -   replace (exp2 (exp2 95 * 95)) with ((exp2 (exp2 95 * 95) * 1)).
      apply mult_le_compat.
      +   apply exp2_mono1.
          transitivity M.
          * apply minoration_2.
          * right; left.
      + auto with arith.
      + apply Nat.mul_1_r.
  -  apply minoration_3.
Qed.
(*||*)
(* end snippet minorationLemmas *)


(** Hence, the length of the battle is greater or equal than 
  exp2 (exp2 95 * 95), a number whose representation in base 10 has 
  at least 10 ^ 30 digits ! *)

(** from OCAML
 
let exp2 x = 2.0 ** x;;

let _ = exp2 95.0 *. 95.0;;

float = 3.76333771942755604e+30

N >= 2 ** 3.7e+30

log10 N >= 3.7e+30 * log10 2 >= 1.0e+30 

N >= 10 ** (10 ** 30)

 *)











