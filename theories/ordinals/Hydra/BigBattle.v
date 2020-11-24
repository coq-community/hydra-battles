(** * A long hydra battle

  Pierre Castéran, LaBRI, Univ Bordeaux 

 *)


From Coq Require Import Arith Relations Lia.
From hydras Require Import Hydra_Definitions Hydra_Lemmas Iterates.


(** Let us consider a small hydra [hinit] *)


Definition  h3 := (hyd_mult head 3).
Definition hinit := hyd3 h3  head head.


(** 
the first steps of a standard battle (Hercules chops off the rightmost head)
*)


Definition h2 := (hyd_mult head 2).
Definition h1 := (hyd1 head).



Lemma L_0_2 : battle standard 0 hinit 2 (hyd1 h3). 
Proof.
  eapply battle_trans with (h := hyd2 h3 head)(i:=1).
  left; trivial.
   red. cbn. chop_off 1.
   left; trivial.
   red.
  left.  trivial.
    split.  repeat constructor. 
Qed.

(** In the next round, there is a replication of h3 into 3 copies of h2 

More generally,  all the future hydras will be composed of several copies
of h2, then several copies of h1, then several heads *)


Definition hyd (a b c : nat) := 
  node (hcons_mult h2  a
             (hcons_mult h1  b
                         (hcons_mult head c hnil))).


Lemma L_2_3 : battle standard 2 (hyd1 h3)  3 (hyd 3 0 0).
Proof.  
  left; trivial; right ; unfold  hyd; simpl;  left; left.
  split; right; right; left.
Qed.

Lemma L_0_3 : battle standard 0 hinit 3 (hyd 3 0 0).
Proof.
  eapply battle_trans.
  - apply L_2_3.
  - apply L_0_2.
Qed.

(** From now on, we abstract the configurations of the battle
  as tuples (round number, n2, n1, nh) where n2 [resp. n1, nh) is the number of 
  sub-hydras h2 [resp. h1, heads] *)

Record state : Type := mks {round : nat ; n2 : nat ; n1 : nat ; nh : nat}.

Definition next (s : state) :=
  match s with
  | mks round a b (S c) => mks (S round) a b c
  | mks round a (S b) 0 => mks (S round) a b (S round)
  | mks round (S a) 0 0 => mks (S round) a (S round) 0
  | _ => s
  end.

(*
Fixpoint iterate {A:Type} (f : A -> A) (n:nat) (x: A) :=
  match n with
    | 0 => x
    | S p => f (iterate f p x)
  end.
*)

(** returns the state at the n-th round *)

Definition test n := iterate next (n-3)  (mks 3 3 0 0).

Compute test 3.
   (**

     = {| round := 3; n2 := 3; n1 := 0; nh := 0 |}
     : state
    *)

Compute test 4.
 (*

  = {| round := 4; n2 := 2; n1 := 4; nh := 0 |}
     : state
 *)


Compute test 2000.

Compute test 5.
 (*
   = {| round := 5; n2 := 2; n1 := 3; nh := 5 |}
     : state
 
  It's now obvious that, 5 rounds later, the field nh will be zero *)

Compute test 10.
(*

    = {| round := 10; n2 := 2; n1 := 3; nh := 0 |}
     : state

OK, (1 + 11) rounds later, the n1 field will be equal to 2, and nh will equal to 0  *)

Compute test 11.
(*

    = {| round := 11; n2 := 2; n1 := 2; nh := 11 |}
     : state

OK, (1 + 11) rounds later, the n1 field will be equal to 2, and nh will equal to 0  *)







Compute test 22.
(*

 = {| round := 22; n2 := 2; n1 := 2; nh := 0 |}
     : state


It looks like that, if we have the state 
{| round := t; n2 := a; n1 := S b; nh := 0 |}

we will have the state {| round := 2(t+1); n2 := a; n1 := b; nh := 0 |}

*)

Compute test 46.
(*

 = {| round := 46; n2 := 2; n1 := 1; nh := 0 |}
     : state

*)

Compute test 94.

(*

 = {| round := 94; n2 := 2; n1 := 0; nh := 0 |}
     : state

At the next round, we get :
*)

Compute test 95.

(*

  = {| round := 95; n2 := 1; n1 := 95; nh := 0 |}
     : state

*)


(** It's now time to abstract our tests 

First, we notice the importance of the following function *)


Definition doubleS (n : nat) := 2 * (S n).


Compute test (doubleS 95).

(**

 = {| round := 192; n2 := 1; n1 := 94; nh := 0 |}
     : state

 *)


Compute test (iterate doubleS 2 95).

(*

  = {| round := 386; n2 := 1; n1 := 93; nh := 0 |}
     : state

*)



(** OK, instead of tests based on the function next, we consider now
    relations (which allow us to consider accessibility predicates)  *)



(** steps  i a b c j a' b' c' has  almost the same meaning as
    iterate test (j - i) (mks t a b c) = (mks t' a' b' c')

*)

Inductive one_step (i: nat) :
  nat -> nat -> nat -> nat -> nat -> nat -> Prop :=
| step1: forall a b c,  one_step i a b (S c) a b c
| step2: forall a b ,  one_step i a (S b) 0 a b (S i)
| step3: forall a, one_step i (S a) 0 0 a (S i) 0.


Lemma step_round_plus : forall i a b c a' b' c', one_step i a b c a' b' c' ->
                                            battle standard i (hyd  a b c)
                                                  (S i) (hyd a' b' c').
  destruct 1.
  - left; trivial;   unfold hyd; left;  split.
    apply hcons_mult_S0.   
    apply hcons_mult_S0. 
    simpl; now left. 
  - left; trivial; right.
    unfold hyd; left.       
    apply hcons_mult_S1; simpl.
    rewrite <- hcons_mult_comm.
    apply hcons_mult_S1.
    unfold hyd_mult; cbn.
    left;  split; constructor.

  - left; trivial;  right;   unfold hyd;   left.
    simpl; rewrite  <- hcons_mult_comm;  apply hcons_mult_S1.
    left; split;  simpl;  right; constructor.
Qed.




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


Lemma steps_battle : forall i a b c j  a' b' c',
    steps i a b c j a' b' c' ->
    battle standard i (hyd  a b c) j (hyd a' b' c').
Proof.
  induction 1.
  - now apply step_round_plus.
  - eapply battle_trans.
   +   apply IHsteps2.
   +  assumption.
Qed.


(**  From now on, we play again the same tests as above, but instead of plain uses of Compute, we prove and register lemmas that we will be used later *)


Lemma L4 : reachable 4 2 4 0.
Proof.
  left; constructor.
Qed.



(** Now we prove some laws we observed in our test phase *)

Lemma LS : forall c a b i,  steps i a b (S c) (i + S c) a b 0.
Proof.
  induction c.
 -   intros;  replace (i + 1) with (S i).
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


Lemma L0_95 : battle standard 3 (hyd 3 0 0) 95 (hyd 1 95 0).
Proof.
  apply steps_battle.
  apply L95.
Qed.

  
(** No more tests ! we are going to build bigger transitions *)

Lemma iterate_comm {A: Type} f n (x:A)
  : iterate f n (f x) = f (iterate f n x).
Proof.
  induction n;  simpl.
  - trivial.   
  - simpl;  now f_equal. 
Qed. 

Lemma Bigstep : forall b i a , reachable i a b 0 ->
                               reachable (iterate doubleS b i) a 0 0.
 Proof.
  induction b.
  -  trivial.
  -  intros;  simpl;   apply reachable_S in H.
     rewrite <- iterate_comm; now apply IHb.
 Qed.

 (** From all the lemmas above, we now get a pretty big step *)
 
Definition M := iterate doubleS 95 95.

Lemma L2_95 : reachable M 1 0 0.
Proof.
  apply Bigstep,  L95.
Qed.

(** the next step creates (M+1) copies of h1 *)


Lemma L2_95_S : reachable (S M) 0 (S M) 0.
Proof.
  eright.
 - apply L2_95.
 -  left; constructor 3.
Qed.


Definition N :=   iterate doubleS (S M) (S M).

Theorem   SuperbigStep : reachable N  0 0 0 .
Proof.
  apply Bigstep, L2_95_S.
Qed.



(** We can  ow apply our study based on abstract states to "real" hydras *)


(** transforming our relation one_step into standard battles *)




(** We get now statements about hydras and battles *)

Lemma Almost_done :
  battle standard 3 (hyd 3 0 0) N (hyd 0 0 0).
Proof. 
  apply steps_battle, SuperbigStep.
Qed.

Theorem Done :
  battle standard 0 hinit N head.
Proof.
  eapply battle_trans.
  -   apply Almost_done.
  -  apply L_0_3.
Qed.

(** The natural number N is expressed in terms of the (iterate doubleS)
   function.  The rest of this file is dedicated to get an intuition of how it is huge .
     Our idea is to get a minoration by exponentials of base 2 

*)


Definition exp2 n := iterate (fun n => 2 * n) n 1.

Lemma exp2S : forall n, exp2 (S n) = 2 * exp2 n.
Proof.
  unfold exp2;  intros; simpl; ring. 
Qed. 


Lemma minoration_0 : forall n,  2 * n <= doubleS n.
Proof.
  unfold doubleS;intros; abstract lia.
Qed.

Lemma minoration_1 : forall n x, exp2 n * x <= iterate doubleS n x.
Proof.
  induction n; simpl.
  -  intro;  abstract lia.
  -  intros; unfold doubleS;  rewrite exp2S.
     transitivity (2 * iterate doubleS n x).
    +  rewrite <- mult_assoc; apply   mult_le_compat_l; auto.   
    +  unfold doubleS; abstract lia.
Qed.


Lemma minoration_2 : exp2 95 * 95 <= M.
Proof.  apply minoration_1. Qed.


Lemma minoration_3 : exp2 (S M) * S M <= N.
Proof.   apply minoration_1.  Qed.

Lemma exp2_mono1 : forall n p,  n <= p ->  exp2 n  <= exp2 p .
Proof.
  induction 1.
  - reflexivity.   
  -  rewrite exp2S;  abstract lia.
Qed.

Lemma minoration : exp2 (exp2 95 * 95) <= N.
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











