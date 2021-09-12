
(** *  Addition Chains
Pierre Casteran, LaBRI, University of Bordeaux

*)

Require Export Monoid_instances Pow Lia List.
Require Import Relations RelationClasses.


Declare ML Module "paramcoq".  
 
Require Import More_on_positive.
Generalizable Variables A op one Aeq.
Infix "==" := Monoid_def.equiv (at level 70) : type_scope.
Open Scope nat_scope.
Open Scope M_scope.

Generalizable All Variables.

(** ** Computations composed of multiplications over type  A 
  (in Continuation Passing Style) *)

Inductive computation {A:Type}  : Type :=
| Return (a : A)
| Mult (x y : A) (k : A -> computation).


(** *** Monadic Notation for computations 
*)

Notation "z '<---'  x 'times' y ';' e2 " :=
  (Mult x y  (fun z => e2))
    (right associativity, at level 60).

Example comp7 : computation  :=
  x <--- 2 times 2;
  y <--- x times 2;
  z <--- y times y ;
  t <--- 2 times z ;
  Return t.

(** *** Definition

An _addition chain_ (in short a _chain_) is a function that maps
 any type $A$ and any value $a$ of type $A$ into a computation on $A$.
*)

Definition chain := forall A:Type, A -> @computation A.


(** The chain associated with the empty computation 
   (raising to the first power) *)

Definition C1 : chain :=  (@Return).

(** Chain associated with the 7-th power *)

Example C7 : chain :=
 fun (A:Type) (x:A) =>
 x2 <--- x times x;
 x3 <--- x2 times x;
 x6 <--- x3 times x3 ;
 x7 <--- x6 times x;
 Return x7.

(** *** Our Favorite example
  
  The chain below is intented to compute 87-th power in any EMonoid.
*)

Example  C87 : chain :=
 fun A (x : A)=>
  x2 <--- x times x ;
  x3 <--- x2 times x ;
  x6 <--- x3 times x3 ;
  x7 <--- x6 times x ;
  x10 <--- x7 times x3 ;
  x20 <--- x10 times x10 ;
  x40 <--- x20 times x20 ;
  x80 <--- x40 times x40 ;  
  x87 <--- x80 times x7 ;
  Return x87.

(** *** Chain length (number of mutiplications)
*)

Fixpoint computation_length  {A} (a:A) (m : @computation A) : nat :=
match m with
  | Mult _ _ k => S (computation_length a (k a))
  | _ => 0%nat
end.

Definition chain_length (c:chain) := computation_length tt (c _ tt).

(* begin show *)
Compute chain_length C87. 
(* end show *)
(** [[ = 9 : nat ]]
*)

(** *** Execution of chains

Chains are designed for effectively computing powers. 

First, we define recursively the _evaluation_  of a computation, then 
the _execution_ of a chain.
*)


Fixpoint computation_execute  {A:Type} (op: Mult_op A) 
         (c : computation) :=
  match c with 
    | Return x => x 
    | Mult x y k => computation_execute op (k (x * y))
  end.


Definition computation_eval `{M:@EMonoid A E_op E_one E_eq}
           (c : computation) : A :=
  computation_execute E_op c.


Definition chain_execute (c:chain) {A} op  (a:A) :=
  computation_execute op (c A a).



Definition chain_apply (c:chain) `{M:@EMonoid A E_op E_one E_eq} a : A :=
   computation_eval (c A a).


Lemma computation_eval_rw `{M:@EMonoid A E_op E_one E_eq} c :
         computation_eval c  =  computation_execute E_op c.
Proof. reflexivity. Qed.


(* begin show *)
Time Compute  chain_apply C87 3%Z.
(* end show *)

(** [[
 = 323257909929174534292273980721360271853387%Z
     : Z
]]
*)

(* begin show *)
Time Compute chain_apply  (M:=M2N) C87  (Build_M2 1 1 1 0)%N.
(* end show *)

(** [[
 = {|
       c00 := 1100087778366101931%N;
       c01 := 679891637638612258%N;
       c10 := 679891637638612258%N;
       c11 := 420196140727489673%N |}
     : M2 N
]]
*)


(** ** Chain correctness

In this section, we define formally the correctness of a given chain 
 with respect to  some given exponent,
and more generally the correctness of a chain generator, i.e.  a function that,
given any positive integer $p$, returns a chain that is correct with respect to  $p$.

*)

Definition chain_correct_nat (n:nat) (c: chain) := n <> 0 /\ 
forall `(M:@EMonoid  A E_op E_one E_eq) (x:A), 
   chain_apply c x ==   x  ^  n.

Definition chain_correct (p:positive) (c: chain) :=
  chain_correct_nat (Pos.to_nat p) c. 

Definition optimal (p:positive) (c : chain) :=
 forall c', chain_correct p c' -> (chain_length c <= chain_length c')%nat.

(** A slow tactic for proving a chain's correctness *)

Ltac slow_chain_correct_tac :=
  match goal with 
      [ |- chain_correct ?p ?c ] =>
      let A := fresh "A" in
      let op := fresh "op" in
      let one := fresh "one" in
      let eqv := fresh "eqv" in
      let M := fresh "M" in
      let x := fresh "x"
      in  split;[discriminate | 
                 unfold c, chain_apply, computation_eval; simpl;
                 intros A op one eq M x; monoid_simpl M; reflexivity]
  end.

Example C7_ok : chain_correct 7 C7.
Proof.
 slow_chain_correct_tac.
Qed.


(** The following proof takes a very long time. Happily, C87's correctness 
will be proved  more  efficiently, using  reflection or parametricity. 
*)

(** Remove the comment if you can wait ...

Example C87_ok : chain_correct 87 C87.
Proof.
 Time  slow_chain_correct_tac. 
(*
Finished transaction in 62.808 secs (62.677u,0.085s) (successful)
*)
Qed.

Print C87_ok.
*)



(** * Correctness Proof by Reflection
  See chap 16 of Coq'Art *)

(** Binary trees of multiplications over A *)

Inductive Monoid_Exp (A:Type) : Type :=
 Mul_node (t t' : Monoid_Exp A) | One_node | A_node (a:A).

Arguments Mul_node {A} _ _.
Arguments One_node {A} .
Arguments A_node {A} _ .


(** Linearization functions *)

Fixpoint flatten_aux {A:Type}(t fin : Monoid_Exp A) : Monoid_Exp A :=
match t with Mul_node  t t' => flatten_aux t (flatten_aux t' fin)
           | One_node  => fin
           |  x => Mul_node  x fin
end.

Fixpoint flatten {A:Type} (t: Monoid_Exp A) : Monoid_Exp A :=
match t with
| Mul_node t t' => flatten_aux t (flatten t')
| One_node => One_node
| X => Mul_node X One_node
end.

(** Interpretation function *)

Function eval {A:Type} {op one eqv} (M: @EMonoid A op one eqv)
         (t: Monoid_Exp A) : A :=
match t with Mul_node t1 t2 => (eval M t1 * eval M t2)%M
            | One_node => one
            | A_node a => a
end.


Lemma flatten_aux_valid {A} `(M: @EMonoid A op one eqv):
forall t t', (eval M t * eval M t')%M ==
             (eval M (flatten_aux t t')).
Proof.
 add_op_proper M HM.
 induction t;simpl.
 - intro t'; rewrite <- IHt1;   rewrite <- IHt2; monoid_simpl M;reflexivity.
 - intro t';monoid_simpl M; reflexivity.
 - reflexivity.
Qed.

Lemma flatten_valid {A} `(M: @EMonoid A op one eqv):
forall t , eval M t == eval M (flatten t).
Proof.
 add_op_proper M HM; induction t;simpl.
 - rewrite <- flatten_aux_valid, <- IHt2; reflexivity.
 - reflexivity.
 - monoid_simpl M;reflexivity.
Qed.

Lemma flatten_valid_2 {A} `(M: @EMonoid A op one eqv):
forall t t' , eval  M (flatten t) == eval M (flatten t')  ->
     eval M t == eval M t'.
Proof.
  intros t t' H; now repeat  rewrite <- flatten_valid in H.  
Qed.

(** "Quote" tactic *)

Ltac model A  op one v :=
match v with 
| (?x  * ?y)%M => let r1 := model A op one x
                  with r2 :=(model A op one y) 
                  in  constr:(@Mul_node A r1 r2)
| one => constr:(@One_node A)
| ?x => constr:(@A_node A x)
end.



Ltac monoid_eq_A A op one E_eq M  :=
match goal with 
| [ |- E_eq  ?X ?Y ] =>
  let tX := model A op one X with
      tY := model A op one Y in
      (change (E_eq (eval M tX) (eval M tY)))
end.



Ltac reflection_correct_tac :=
match goal with
[ |- chain_correct ?n ?c ] =>
 split; [try discriminate |
         let A := fresh "A"
         in let op := fresh "op"
         in let one := fresh "one" 
         in let E_eq := fresh "eq" 
         in let M := fresh "M"
         in let x := fresh "x" 
         in  (try unfold c); unfold chain_apply;
           simpl; red; intros  A op one E_eq M x;
           unfold computation_eval;simpl;
           monoid_eq_A A op one E_eq M;
           apply flatten_valid_2;try reflexivity
        ]
end. 
 


Example C87_ok : chain_correct 87 C87.
Proof.
  Time reflection_correct_tac.
(** Finished transaction in 0.038 secs (0.038u,0.s) (successful) *)
Qed. 


(** * Correctness and parametricity 

In this section, we show some tools for proving automatically the
correctness of a given chain, and try to avoid spending time
while proceeding to a lot of setoid rewritings 


First, we notice that any chain is able to compute its associated exponent:
*)

Definition the_exponent_nat (c:chain) : nat :=
 chain_apply c (M:=Natplus) 1%nat.

Definition the_exponent (c:chain) : positive :=
  chain_execute c Pos.add  1%positive.

Compute the_exponent C87.



(** 
Roughly, if cA is a computation on A and cB a computation on B,
cA and cB are related through (computation_R A B R) if, during  their execution,
the corresponding variables of type A  and B are always bound to related
(w.r.t. [R] ) values. 

*)



Parametricity computation.

Print computation_R.
(* by plugin 

Inductive
computation_R (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type)
  : computation -> computation -> Type :=
    computation_R_Return_R : forall (a₁ : A₁) (a₂ : A₂),
                             A_R a₁ a₂ ->
                             computation_R A₁ A₂ A_R (Return a₁) (Return a₂)
  | computation_R_Mult_R : forall (x₁ : A₁) (x₂ : A₂),
                           A_R x₁ x₂ ->
                           forall (y₁ : A₁) (y₂ : A₂),
                           A_R y₁ y₂ ->
                           forall (k₁ : A₁ -> computation)
                             (k₂ : A₂ -> computation),
                           (forall (H : A₁) (H0 : A₂),
                            A_R H H0 -> computation_R A₁ A₂ A_R (k₁ H) (k₂ H0)) ->
                           computation_R A₁ A₂ A_R 
                             (z <--- x₁ times y₁; k₁ z)
                             (z <--- x₂ times y₂; k₂ z)

For computation_R: Argument scopes are [type_scope type_scope function_scope _
                     _]
For computation_R_Return_R: Argument scopes are [type_scope type_scope
                              function_scope _ _ _]
For computation_R_Mult_R: Argument scopes are [type_scope type_scope
                            function_scope _ _ _ _ _ _ function_scope
                            function_scope function_scope]
*)


(** We say that a chain [c] is _parametric_ if
   [c A a] and [c B b] are equivalent with respect to any  relation that
   contains  the pair [(a,b)].
*)



Definition parametric (c:chain) :=
  forall A B (R: A -> B -> Type) (a:A) (b:B),
   R a b -> computation_R  A B R (c A a) (c B b).

(**  The following statement cannot be proven in Coq (AFAIK) *)

Definition any_chain_parametric : Type :=
 forall c:chain, parametric c.

Goal any_chain_parametric.
Proof.
intros c A B R a b ; induction (c A a);  destruct (c B b).
Abort.



(** 
 Nevertheless, if we don't want to assume [any_chain_parametric], 
 we can use the  following tactic for proving a given that a given chain [c] 
 is parametric. 
*)

Ltac parametric_tac  := 
 match goal with [ |- parametric ?c] =>
   red ; intros;
  repeat (right;[assumption | assumption | ]);  left; assumption
end.

Example P87 : parametric C87.
Proof. Time parametric_tac.
 Qed. 


(** **  computation of $a^n$ compared to computation of $n$

The following section is dedicated to prove that, if a chain $c$ is parametric,
it computes powers of the form $a^n$, where $n$ is obtained by applying the
function [the_exponent_nat] to $c$.

Basically, we proceed by an induction on the hypothesis 
[equiv gamma_A gamma_nat l] where [gamma] is a computation on [A],
gamma_nat a computation on [nat] (with respect to the additive monoid on [nat]),
and [l] is a list of pairs of the form $(a^i,i)$.

*)
 
Section Refinement_proof.
 Variable A: Type.
 Variable E_op : Mult_op A.
 Variable E_one : A.
 Variable E_eq : Equiv A.
 Context (M : EMonoid E_op E_one E_eq).


(**  Let us characterise the lists of pairs of the form $(a^i,i)$, for a given 
$a$ and $i\not=0$.
*)

Definition power_R  (a:A) :=
  fun (x:A)(n:nat) => n <> 0 /\ x == a ^ n.

Remark power_R_Mult : forall a x y i j, 
    power_R a x i  -> power_R a y j ->
    power_R a (x * y) (i+j)%nat.
Proof. 
  simpl; intros  a x y i j  H H0; destruct H, H0; split. 
 -   lia.
 - add_op_proper M H;   
   rewrite H1, H2, power_of_plus; reflexivity.
Qed.

Remark power_R_1 : forall a, power_R a a 1%nat.
Proof.
  simpl; intros a; red; simpl; rewrite  (Eone_right (EMonoid:=M));split.
  - discriminate.
  - reflexivity.
Qed.

Lemma  power_R_is_a_refinement (a:A) :
  forall(gamma : @computation A)
        (gamma_nat : @computation nat),
    computation_R _ _  (power_R a) gamma gamma_nat -> 
     power_R a (computation_eval gamma)
               (computation_eval (M:= Natplus) gamma_nat).
Proof.
  induction 1;simpl;[auto | ].
  apply H; destruct x_R, y_R;  split.
  unfold mult_op, nat_plus_op.  
  + lia. 
  + apply power_R_Mult; split;auto.
Qed.


Lemma param_correctness_aux :
  forall (c:chain)(a:A),
    computation_R A  nat (power_R a ) (c A a) (c nat 1%nat)  ->
     power_R  a (computation_eval (c A a)) (the_exponent_nat c) .
Proof.
  intros c a Hc;   now apply power_R_is_a_refinement.
Qed.


End Refinement_proof.



(** ** Correctness Theorem

From our study of the [computation\_R] predicate, we infer that any parametric chain $c$
is correct with respect to the number [the_exponent_nat c]

*)

Lemma exponent_nat_neq_0 : forall c: chain,  parametric c -> 
                                             the_exponent_nat c <> 0.
Proof.
  intros c Hc;  red in Hc;  unfold the_exponent_nat. 
  generalize (param_correctness_aux nat _ _  eq Natplus c 1).  
  destruct 1.
  -   apply Hc.
      split;auto.
      now compute. 
  -  unfold chain_apply; rewrite H0.  
     induction (the_exponent_nat c).
     + now destruct H. 
     +  discriminate.  
Qed.

Lemma exponent_pos2nat : forall c: chain,  parametric c -> 
  the_exponent_nat c = Pos.to_nat (the_exponent c).
Proof.
 intros c X;
 generalize  (X nat positive
                (fun n p => n = Pos.to_nat p) 1 xH
                (refl_equal 1)).
 unfold the_exponent, the_exponent_nat, chain_execute, chain_apply.
 generalize (c nat 1), (c _ 1%positive); induction 1.
 - cbn; assumption. 
 -  apply (H (x₁ + y₁)%nat (x₂ + y₂)%positive); rewrite Pos2Nat.inj_add;
    now subst.
Qed.

Lemma exponent_pos_of_nat : forall c: chain,  parametric c -> 
  the_exponent c = Pos.of_nat (the_exponent_nat c).
Proof.
 intros c Hc; rewrite exponent_pos2nat;auto.
 now rewrite Pos2Nat.id.
Qed.


Lemma param_correctness_nat (c: chain) :
  parametric c ->  chain_correct_nat (the_exponent_nat c)  c.
Proof.
 intros Hc  ; split. 
 -  now apply  exponent_nat_neq_0.
 -  intros A  op one Aeq M  a ;  unfold chain_apply.  
    apply  param_correctness_aux, Hc.
    split.
    + discriminate.
    +  simpl; rewrite (Eone_right (EMonoid:=M)); reflexivity. 
Qed. 

Lemma param_correctness :
  forall (p:positive) (c:chain), p = the_exponent c -> parametric c -> 
      chain_correct p  c. 
Proof.
  intros; subst p; rewrite  exponent_pos_of_nat; auto.
  red;  rewrite  exponent_pos2nat;auto.
  rewrite Pos2Nat.id,  <- exponent_pos2nat;auto.
  apply param_correctness_nat; auto.
Qed.

(** *** Remark 

If we admit that any chain is parametric, we infer the correctness of every chain.
 

%\textbf{Cite again PHOAS and Refinement for free! }%
*)

Lemma param_correctness_for_free :
  any_chain_parametric  ->
      forall p (c : chain) ,
p = the_exponent c -> chain_correct p c.
Proof.
  intros H p c H0. rewrite H0. apply param_correctness; trivial. 
Qed.


(** *** Back to 87 

We present two new-proofs of consistency of [C87].
The first one uses the [parametric_tac] tactic, the other one 
using the "free refinement" method 

*)




Ltac param_chain_correct :=
match goal with 
  [|- chain_correct ?p ?c ] =>
  let H := fresh "H" in assert (p = the_exponent c) by reflexivity;
                        apply param_correctness;[trivial | parametric_tac]
end.

Lemma C87_ok' : chain_correct 87  C87.
 Time  param_chain_correct.
(* Finished transaction in 0.005 secs (0.005u,0.s) (successful) *)
Qed.


Lemma L87'' : any_chain_parametric -> chain_correct 87 C87.
Proof.
 intro H; apply param_correctness;auto.
Qed.

(** ** Correct by construction chains  *)

Definition chain_generator := positive -> chain.

Definition correct_generator (gen : positive -> chain) :=
 forall p, chain_correct p (gen p).


(** Computing $x^n$ using a chain generator *)

Definition cpower_pos (g : chain_generator)  p
           `{M:@EMonoid A E_op E_one E_eq} a :=
  chain_apply (g p) (M:=M) a.


Definition cpower (g : chain_generator)  n
           `{M:@EMonoid A E_op E_one E_eq} a :=
  match n with 0%N => E_one 
             | Npos p => cpower_pos  g p a
  end.





(** *** Definition
A chain generator is _optimal_ if it returns chains whose length are less or 
equal than the chains returned by any correct generator.
 *)

Definition optimal_generator (g : positive -> chain ) :=
 forall p:positive, optimal p (g p).



(** ** Some chain generators 

We reinterpret the naïve and binary exponentiation algorithms in the framework 
of addition chains.

Instead of directly computing $x^n$ for some base $x$ and exponent $n$,
we build chains that describe the computations associated with both methods.
Not surprisingly, this chain generation will be described in terms of recursive
functions, once the underlying monoid is fixed.
*)


(** ** Chains associated to the well-known binary exponentiation algorithm *)

(** *** computation of $a*x^p$ 

As for the "classical" binary exponentiation algorithm,
we define an auxiliary computation generator for computing the
product of an accumulator $a$ with an arbitrary power of some value $x$

*)

Fixpoint axp_scheme  {A} p : A -> A -> @computation A   :=
 match p with
   | xH =>  (fun a x => y <--- a  times x ; Return y)
   | xO q => (fun a x => x2 <--- x times  x ; axp_scheme q a x2)
   | xI q => (fun a x => ax <--- a times x ;
                         x2 <--- x times x ;
                         axp_scheme q ax x2)
end.

(** *** computation of $x^p$ 

*)

Fixpoint  bin_pow_scheme {A} (p:positive)  : A -> @computation A:=
  match p with  |  xH => fun x => Return x
             | xI q  => fun x => x2 <--- x times x; axp_scheme q x x2
             | xO q => fun x => x2 <--- x times x ; bin_pow_scheme q x2
  end.

(** *** Chain generator associated with the binary algorithm 

*)

Definition binary_chain (p:positive) : chain :=
  fun A => bin_pow_scheme p.


(* begin show *)
Compute binary_chain 87.
(* end show *)
(** [[
fun (A : Type) (x : A) =>
       x0 <--- x times x;
       x1 <--- x0 times x0;
       x2 <--- x0 times x1;
       x3 <--- x1 times x1; x4 <--- x2 times x3; Return x4
     : chain
]]

Notice that %\texttt{Coq}% does not respect our naming convention for bound variables .

*)

(** ** Correctness of the binary method *)

Section binary_power_proof.

Variables (A: Type)
         (E_op : Mult_op A)
         (E_one : A)
         (E_eq: Equiv A).

Context (M : EMonoid  E_op E_one E_eq).




(** 
 As for linear chains, we first establish the correctness of the auxiliary
  function [axp_scheme].
 *)

Existing Instance Eop_proper.

Lemma axp_correct : forall p a x,
    computation_eval (axp_scheme p a x) == a *  x ^ (Pos.to_nat p).
Proof.
  induction p.
  -   intros a x; simpl axp_scheme.
      replace (Pos.to_nat p~1) with (S (Pos.to_nat p + Pos.to_nat p)%nat).
      cbn.   
      rewrite <- computation_eval_rw, IHp.
      unfold equiv in *. 
      destruct M; rewrite power_of_square, power_of_plus.
      unfold mult_op in *; repeat rewrite Eop_assoc.  
      destruct Eq_equiv.  reflexivity.
      rewrite  Pnat.Pos2Nat.inj_xI;lia.
  - intros a x; simpl  axp_scheme.
    replace (Pos.to_nat p~0 ) with (Pos.to_nat p + Pos.to_nat p)%nat.
    unfold computation_eval in *.
    destruct M;
      simpl;  rewrite IHp, power_of_square,  <- power_of_plus.  reflexivity. 
    rewrite  Pnat.Pos2Nat.inj_xO;lia.
  - simpl; destruct M; intros; now rewrite  (Eone_right x).
Qed.



Lemma binary_correct : forall p x,
                         computation_eval  (bin_pow_scheme p (A:=A) x) ==
                          x ^ (Pos.to_nat p).
Proof.
  intros p ; induction  p.
  - simpl. intro a.
    unfold computation_eval in *;    simpl. 
    rewrite <- computation_eval_rw.
    rewrite axp_correct.
    replace (Pos.iter_op Init.Nat.add p 2%nat)
    with (Pos.to_nat p + Pos.to_nat p)%nat.
    destruct M;rewrite  power_of_plus;  auto.  
    f_equal.
    now rewrite <- power_of_square.
    now rewrite ZL6.
  - simpl.
    intro a.  unfold computation_eval in *; simpl; rewrite IHp;  unfold mult_op.
    generalize (sqr_eqn M a); unfold mult_op.
    intro H; generalize (power_proper M);   intro H0;
    rewrite Pos2Nat.inj_xO.
    transitivity ((a^2) ^ Pos.to_nat p).
    apply H0.
    red in H.
    destruct M; destruct Eq_equiv. 
    symmetry;auto.
    reflexivity. 
    rewrite   (power_of_power M).
    now rewrite mult_comm.
  - simpl.
    intros; now monoid_simpl M.
Qed.


End  binary_power_proof.



Lemma binary_generator_correct : correct_generator binary_chain.
Proof.
  red;unfold chain_correct; intros; unfold binary_chain, chain_apply;
  split;[auto with chains| intros;  apply  binary_correct].
Qed.


(** ** The binary method is not optimal 

    We use the function [chain_length] and proofs of correctness 
  for showing that [binary_chain], although correct, is not an optimal 
  chain generator.
 
   Our proof  is structured as a proof by contradiction, under the 
   hypothesis that [binary_chain] is optimal.
*)

Section non_optimality_proof.

 Hypothesis binary_opt : optimal_generator binary_chain.

(* begin show *)
Compute chain_length (binary_chain 87).
(* end show *)

(** [[
   = 10 : nat ]]
*)



(* begin show *)
Compute chain_length (C87).
(* end show *)

(** [[
   = 9 : nat ]]
*)


Lemma binary_generator_not_optimal : False.
Proof.
  generalize (binary_opt  _ _ C87_ok); compute; lia.
Qed. 

End non_optimality_proof.


Open Scope nat_scope.
Open Scope M_scope.

Section S1.
 Fixpoint clog2 (p:positive) : nat :=
 match p with xH => 1%nat
            | xO xH => 2%nat
            | xO p => S (clog2 p)
            | xI p => S (clog2 p)
  end.

Fixpoint exp2 (n:nat) : positive :=
  match n with O => 1
             | S p => 2 * exp2 p
 end.
 Lemma exp2_Plus : forall n p, exp2 (n + p) = (exp2 n * exp2 p)%positive.
 Proof.
   induction n; cbn.
   - reflexivity. 
   - intro p; now  rewrite IHn.
 Qed.

Lemma axp_scheme_length1 :
  forall p, (computation_length  tt (axp_scheme  p tt tt  ) <= 2 * clog2 p)%nat.
  induction p;    cbn. lia.
  -  destruct p. 
     + lia.
     + lia.
     + simpl in IHp; simpl; lia.
  -   lia.
Qed.

Lemma bin_pow_scheme_length1 :
  forall p, (computation_length tt (bin_pow_scheme  p tt  ) <= 2 * clog2 p)%nat.
 Proof.
  induction p; cbn.
  generalize (axp_scheme_length1 p); intro H; lia.
  destruct p; try lia. cbn. lia.
  lia.
Qed.

Lemma binary_chain_length : forall p,
                              (chain_length (binary_chain p) <= 2 * clog2 p)%nat.
 Proof.
  intro p; unfold binary_chain, chain_length.
  apply bin_pow_scheme_length1.  
 Qed.

Lemma optimal_upper_bound: forall p c, optimal p c -> 
   (chain_length c <= 2 * clog2 p)%nat.
Proof.
  unfold optimal;intros p c H.
  transitivity (chain_length (binary_chain p)).
  - apply H;  apply binary_generator_correct.
  -   apply binary_chain_length.
 Qed.

End S1.




(** * How to prove chain correctness in general ? 

 In previous sections, we showed proofs of correctness of two chain generators.
 By definition, every chain returned by these generators is correct w.r.t. 
 the given exponent.

 The problem with [C87] is quite different. This chain 
 has been given by hand, and we had to prove its correctness. 

 Although the proof script for lemma [L87] is quite short, the resulting 
 proof  is quite clumsy, consisting in a long chain of equivalences using
 associativity of the multiplication.
 
 The reader can easily be convinced of this fact, just by the command 
[Print L87.]

In a similar way, it may happen that a correct chain generator is hard
to certify in %\texttt{Coq}%. In this case, one may chose to prove the 
correctness of various chains returned by the generator.
 
In the rest of this section, we investigate some ways of proving 
the correctness of given chains.

*)







Section S2.
(** Difficult and unfinished (conjecture)

 We would like to prove that for  any parametric chain c for p,
c's length is greater or equal than  log2(p).

*)

Variables A B : Type.
Variables (a:A)(b:B).
Let R_true := fun (x:A)(y:B) => True.
Lemma  L :
  forall(gammaA : @computation A)
        (gammaB : @computation B),
    computation_R  _ _ R_true gammaA gammaB -> 
     @computation_length A a gammaA = @computation_length B b gammaB.
Proof.
induction 1.
- reflexivity.  
- simpl; now rewrite (H a b).
Qed.

Lemma L2 : forall c : chain, parametric c ->
    computation_length a (c A a) = computation_length b (c B b).
Proof.
  intros c Hc;apply L;   apply Hc; now  red. 
Qed.


End S2.

Extraction Language Scheme.
Recursive Extraction chain_apply.
 






