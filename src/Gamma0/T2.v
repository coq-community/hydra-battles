
(**  Pierre Casteran 
    LaBRI, University of Bordeaux, laBRI UMR 5800 )
*)

(** Data-type for Veblen normal form 
   (ordinals below Gamma0)   *)


From Coq Require Import Arith  Compare_dec Relations Wellfounded Max Lia.
From hydras Require Import More_Arith  Restriction T1 OrdNotations.

Set Implicit Arguments.



(** *   Definitions        *)


(**  [gcons alpha beta n gamma] is : [psi(alpha,beta)*(S n)+ gamma]  *)

Inductive T2 : Set :=
| zero : T2
| gcons : T2 -> T2  -> nat -> T2 -> T2.

Declare Scope T2_scope.
Delimit Scope T2_scope with t2.

Notation "[ alpha , beta ]" := (gcons alpha beta 0 zero)
                                 (at level 0): T2_scope.

Open Scope T2_scope.


Definition psi alpha beta  := [alpha, beta].

Definition psi_term alpha :=
  match alpha with zero => zero
                 | gcons a b n c => [a, b]
  end.




Lemma psi_eq : forall a b, psi a b = [a,b].
Proof.
 trivial.
Qed.

Ltac fold_psi :=  rewrite <- psi_eq.
Ltac fold_psis := repeat fold_psi.

Notation  "'one'"  := [zero,zero] : T2_scope.

Notation "'FS' n" := (gcons zero zero n zero) (at level 10) : T2_scope.


(** the [n]-th ordinal  *)

Definition fin (n:nat) := match n with 0 => zero | S p => FS p end.

Coercion fin  : nat >-> T2.




Compute fin 42.

Inductive is_finite:  T2 ->  Set := 
 zero_finite : is_finite zero
|succ_finite : forall n, is_finite (gcons zero zero n zero).

Hint Constructors is_finite : T2.

Notation "'omega'"  := [zero,one] : T2_scope.

Notation "'epsilon0'"  := ([one,zero]) : T2_scope.

Definition epsilon alpha := [one, alpha].


(* injection from T1 *)

Fixpoint T1_to_T2 (alpha :T1) : T2 :=
  match alpha  with
  | T1.zero => zero
  | T1.ocons a n b => gcons zero (T1_to_T2 a) n (T1_to_T2 b)
  end.

(** additive principals *)


Inductive ap : T2 -> Prop :=
ap_intro : forall alpha beta, ap [alpha, beta].

(** strict order on terms *)


Reserved Notation "x 't2<' y" (at level 70, no associativity).
Reserved Notation "x 't2<=' y" (at level 70, no associativity).
Reserved Notation "x 't2>=' y" (at level 70, no associativity).
Reserved Notation "x 't2>' y" (at level 70, no associativity).


Reserved Notation "x 't2<=' y 't2<=' z" (at level 70, y at next level).
Reserved Notation "x 't2<=' y 't2<' z" (at level 70, y at next level).
Reserved Notation "x 't2<' y 't2<' z" (at level 70, y at next level).
Reserved Notation "x 't2<' y 't2<=' z" (at level 70, y at next level).


Inductive lt : T2 -> T2 -> Prop :=
| (* 1 *) 
 lt_1 : forall alpha beta n gamma,  zero t2< gcons alpha beta n gamma
| (* 2 *)
 lt_2 : forall alpha1 alpha2 beta1 beta2 n1 n2 gamma1 gamma2, 
                alpha1 t2< alpha2 ->
                beta1 t2< gcons alpha2 beta2 0 zero ->
               gcons alpha1 beta1 n1 gamma1 t2<
               gcons alpha2 beta2 n2 gamma2
| (* 3 *)
 lt_3 : forall alpha1  beta1 beta2 n1 n2 gamma1 gamma2, 
               beta1 t2< beta2 ->
               gcons alpha1 beta1 n1 gamma1 t2<
               gcons alpha1 beta2 n2 gamma2

| (* 4 *)
 lt_4 : forall alpha1 alpha2 beta1 beta2 n1 n2 gamma1 gamma2, 
               alpha2 t2< alpha1 ->
               [alpha1, beta1] t2< beta2 ->
               gcons alpha1 beta1 n1 gamma1 t2<
               gcons alpha2 beta2 n2 gamma2

| (* 5 *)
lt_5 : forall alpha1 alpha2 beta1 n1 n2 gamma1 gamma2, 
               alpha2 t2< alpha1 ->
               gcons alpha1 beta1 n1 gamma1 t2<
               gcons alpha2  [alpha1, beta1] n2 gamma2

| (* 6 *)
lt_6 : forall alpha1 beta1  n1  n2 gamma1 gamma2,  (n1 < n2)%nat ->
                                    gcons alpha1 beta1 n1 gamma1 t2< 
                                    gcons alpha1 beta1 n2 gamma2

| (* 7 *)
lt_7 : forall alpha1 beta1 n1   gamma1 gamma2,
    gamma1 t2< gamma2 ->
    gcons alpha1 beta1 n1 gamma1 t2< gcons alpha1 beta1 n1 gamma2
where  "o1 t2< o2" := (lt o1 o2): T2_scope.

Hint Constructors lt : T2.

Definition le t t' := t = t' \/ t t2< t'.
Hint Unfold le : T2.

Notation "o1 t2<= o2" := (le o1 o2): T2_scope.

(** *** Examples *)

Example Ex1: 0 t2< epsilon0.
Proof.  constructor 1. Qed.

Example Ex2: omega t2< epsilon0.
Proof. info_auto with T2. (* uses lt_1 and lt_2 *) Qed.

Example Ex3: gcons omega 8 12 56 t2<  gcons omega 8 12 57.
Proof.
  constructor 7; constructor 6; auto with arith.
Qed.


Example Ex4: epsilon0 t2< [2,1].
Proof.
  apply lt_2; auto with T2.
  - apply lt_6; auto with arith.
Qed.

Example Ex5 : [2,1] t2< [2,3].
Proof.
  constructor 3; auto with T2.
  - constructor 6; auto with arith.
Qed.

Example Ex6 : gcons 1 0 12 omega t2< [0,[2,1]].
Proof.
  constructor 4.
  - constructor 1.
  - constructor 2.
    + constructor 6; auto with arith.
    + constructor 1.
Qed.


Example Ex7 : gcons 2 1 42 epsilon0 t2< [1, [2,1]].
Proof.
 constructor 5.
 constructor 6; auto with arith.
Qed.





Definition gtail c := match c with
                      | zero => zero 
                      | gcons a b n c => c
                      end.

(* Veblen Normal Form *)

Inductive nf : T2 -> Prop :=
| zero_nf : nf zero
| single_nf : forall a b n, nf a ->  nf b -> nf (gcons a b n zero)
| gcons_nf : forall a b n a' b' n' c', 
                             [a', b'] t2< [a, b]  -> 
                             nf a -> nf b -> 
                             nf(gcons a' b' n' c')-> 
                             nf(gcons a b n (gcons a' b' n' c')).
Hint Constructors nf : T2. 

Lemma  nf_fin i : nf (fin i).
Proof.
  destruct i.
  - auto with T2.
  - constructor 2; auto with T2.
Qed.

Lemma nf_omega : nf omega.
Proof.  compute; auto with T2. Qed.


Lemma nf_epsilon0 : nf epsilon0.
Proof. constructor 2; auto with T2. Qed.

Lemma nf_epsilon : forall alpha, nf alpha -> nf (epsilon alpha).
Proof. compute; auto with T2. Qed.

Example Ex8: nf (gcons 2 1 42 epsilon0).
Proof.
  constructor 3; auto with T2.
  - apply Ex4.
  - apply nf_fin.
  - apply nf_fin.
Qed.


Inductive is_successor : T2 -> Prop :=
  finite_succ : forall  n  , is_successor (gcons zero zero n zero)
 |cons_succ : forall a b n c, nf (gcons a b n c) -> is_successor c ->
                              is_successor (gcons  a b n c).

Inductive is_limit : T2 -> Prop :=
| is_limit_0 : forall alpha beta n, zero t2< alpha \/ zero t2< beta ->
                                   nf alpha -> nf beta ->
                                   is_limit (gcons alpha beta n zero)
| is_limit_cons : forall alpha  beta n gamma,
    is_limit gamma ->
    nf (gcons alpha beta n gamma) ->
    is_limit (gcons alpha beta n gamma).



Fixpoint succ (a:T2) : T2 :=
 match a with zero => one
             | gcons zero zero n c => fin (S (S n))
             | gcons a b n c => gcons a b n (succ c)
 end.


Fixpoint pred  (a:T2) : option T2 :=
 match a  with zero => None
             | gcons zero zero 0 zero => Some zero
             | gcons zero zero (S n) zero => 
                  Some (gcons zero zero n zero)
             | gcons a b n c => (match (pred c) with
                                   Some c' => Some (gcons a b n c')
                                  | None => None
                                  end)
 end.

Inductive lt_epsilon0 : T2 -> Prop :=
  zero_lt_e0 : lt_epsilon0 zero 
| gcons_lt_e0 : forall  b n c,  lt_epsilon0 b ->
                                lt_epsilon0 c -> 
                                lt_epsilon0 (gcons zero b n c).


(* end of main definitions *)


(** ** Length (as in Schutte) *)

Section on_length.

 Open Scope nat_scope.

(* length of ordinal terms *)
(* from Schütte, Proof theory, used in proofs of transitivity
   and total ordering *)
   
Fixpoint nbterms (t:T2) : nat :=
  match t with zero => 0
             | gcons a b n v => (S n) + nbterms v
  end.


Fixpoint t2_length (t:T2) : nat :=
  match t  with zero => 0
             | gcons a b n v => 
                 nbterms (gcons a b n v) + 
                 2 * (Max.max (t2_length a)
                              (Max.max (t2_length b) (t2_length_aux v)))
  end
with t2_length_aux (t:T2) : nat :=
 match t with zero => 0
            | gcons a b n v =>
               Max.max (t2_length a) (Max.max (t2_length b) (t2_length_aux v))
 end.


Lemma length_a : forall a b n v, t2_length a < 
                                 t2_length (gcons a b n v).
Proof.
 simpl; intros; apply le_lt_n_Sm.
 match goal with
     [ |- ?a <= ?b + ?c + ?d] => rewrite (plus_comm (b + c) d) end.
 apply le_plus_trans, le_plus_trans, le_max_l.
Qed.

Lemma length_b : forall a b n v, t2_length b < 
                                 t2_length (gcons a b n v).
Proof.
  simpl; intros; apply le_lt_n_Sm.
  match goal with 
    [ |- ?a <= ?b + ?c + ?d] => rewrite (plus_comm (b + c) d) end.
  apply le_plus_trans, le_plus_trans.
  eapply Le.le_trans.
  2:eapply le_max_r.
  apply le_max_l.
Qed.

Lemma length_c : forall a b n v, t2_length v < 
                                 t2_length (gcons a b n v).
Proof.
  simpl; intros; apply le_lt_n_Sm; case v.
  - simpl; auto with arith.
  - intros; simpl (t2_length (gcons t t0 n0 t1)).
    simpl (nbterms (gcons t t0 n0 t1)).
  match goal with  
    [ |- ?a <= ?b + ?c + ?d] => rewrite <- (plus_assoc b c d) end.
  simpl (t2_length_aux (gcons t t0 n0 t1)).
  match goal with [ |- ?a <= ?b + ?c ] => assert (a <= c) end.
  { pattern (Max.max (t2_length t) (Max.max (t2_length t0) (t2_length_aux t1))).
    generalize (Max.max (t2_length t)
                      (Max.max (t2_length t0) (t2_length_aux t1))).
    intro n1; simpl;  apply le_n_S,  plus_le_compat_l.
    repeat rewrite plus_0_r.
    apply plus_le_compat;
    apply Le.le_trans with (Max.max (t2_length b) n1);
    apply le_max_r.
  }
  abstract lia.
Qed.




Lemma length_n : forall a b r n p, n < p ->
                        t2_length (gcons a b n r) <
                        t2_length (gcons a b p r).
Proof.
 induction 1.
 simpl.
 auto with arith.
 simpl;auto with arith.
Qed.


Lemma length_psi : forall a b n c,
                      t2_length [a, b] <= t2_length (gcons a b n c).
Proof.
 simpl.
 intros; apply le_lt_n_Sm.
 match goal with 
    [ |- ?a <= ?b + ?c + ?d] => rewrite (plus_comm (b + c) d) end.
 apply le_plus_trans.
 replace (Max.max (t2_length b) 0) with (t2_length b).
 -  repeat  rewrite plus_0_r;  apply plus_le_compat. 
   +  apply max_le_regL,  le_max_l; auto.
   +  apply Nat.max_le_compat; auto.
      apply le_max_l.
 - rewrite max_l;auto with arith.
Qed.


Lemma length_ab : forall a b,
    t2_length a + t2_length b <= t2_length (gcons a b 0 zero).
Proof.
 simpl; intros.
 repeat rewrite (max_l (t2_length b) 0);auto with arith.
 case (le_lt_dec (t2_length a) (t2_length b)).
  -  intro;repeat rewrite max_r;auto.
     abstract lia.
  -  intro;repeat rewrite max_l;auto.
     abstract lia.
     auto with arith.
Qed.

Lemma length_abnc : forall a b n c, 
   t2_length a + t2_length b <= t2_length (gcons a b n c).
Proof.
 intros; eapply Le.le_trans.
 -  eapply length_ab.
 - apply length_psi.
Qed.


End on_length.

Compute t2_length (gcons 2 1 42 epsilon0).
