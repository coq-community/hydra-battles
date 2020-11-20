
(** *   Euclidean chains *)

(** ** Introduction

  In this module, we study a way to build efficiently efficient chains.
  Our approach is recursive (compositional?). Chains associated with big exponents are built by composition of smaller chains. Thus, the construction of a 
small computation may be parameterized by the context in which it will be 
  used. In other terms, we shall use Continuation Passing Style 

  Euclidean chains are introduced by %\textbf{Add reference to litterature by Srecko, Pierre et al.}.  


*)



Require Import Inverse_Image  Inclusion  Wf_nat.
Require Import Addition_Chains  NArith  Arith PArith  Compatibility.  
Require Import More_on_positive.
Import Monoid_def  Pow.
Require Import Recdef Wf_nat.
Require Import  More_on_positive .
Require Import Wf_transparent Lexicographic_Product  Dichotomy.
Generalizable All Variables.
Import Morphisms.
Import Monoid_def.



Ltac add_op_proper M H := 
 let h := fresh H in
   generalize (@Eop_proper _ _ _ _ M); intro h.


(**  * CPS chain construction
*)

(** Type of chain continuations *)

Definition Fkont (A:Type) := A -> @computation A.

Definition Fchain := forall A, Fkont A -> A -> @computation A.

(** [F3 k x] computes $z = x^3$, then executes the computation associated
   with [k z] *)

Definition F3 : Fchain := 
 fun  A k  (x:A) =>
  y <--- x times x ;
  z <--- y times x ;
  k  z.


Definition F1 : Fchain := 
 fun A k (x:A) => k x.

Definition F2 : Fchain := 
fun  A k  (x:A) =>
  y <--- x times x ;
  k  y.



(** An Fchain [f] can be considered as a function that takes as 
    argument another chain [c] for continueing the computation.
*)

Definition Fapply (f : Fchain) (c: chain) : chain  :=
 fun (A:Type) (x: A)  =>  f A (c A) x.

Definition Fcompose (f1 f2: Fchain) : Fchain  :=
 fun   A k x =>  f1  A (fun y => f2 A k y) x.


(** Any Fchain can be transformed into a plain chain *)


Definition F2C (f : Fchain) : chain :=
 fun (A:Type) => f A Return .

Compute the_exponent (F2C F3).

(** Composition of Fchains 

Fchains are used for building correct exponentiation schemes by composition 
of correct components. So, we have to define composition of Fchains.

*)

Example F9 := Fcompose F3 F3.

(** Fchains associated with powers of 2 *)


(** computes $x^{2^n}$ then send this value to $k$ *)

(** The neutral element for Fcompose *)



Lemma F1_neutral_l : forall f, Fcompose F1 f = f.
Proof. reflexivity. Qed.

Lemma F1_neutral_r : forall f, Fcompose f F1 = f.
Proof. reflexivity. Qed.



Fixpoint  Fexp2_of_nat (n:nat) : Fchain :=
 match n with O => F1
            | S p => Fcompose F2 (Fexp2_of_nat p)
 end.

Definition Fexp2 (p:positive) : Fchain :=
  Fexp2_of_nat (Pos.to_nat p). 

Compute Fexp2 4.

Compute the_exponent (F2C (Fexp2 4)).



(*
Compute F9.

= fun (A : Type) (x : Fkont A) (x0 : A) =>
       x1 <--- x0 times x0;
       x2 <--- x1 times x0; x3 <--- x2 times x2; x4 <--- x3 times x2; x x4
     : Fchain

*)

Remark F9_correct :chain_correct (F2C F9) 9.
param_chain_correct.
Qed.



Compute the_exponent (F2C F9).
(*
= 9
     : nat

*)







(** A first attempt to define Fchain correctness *)
Module Bad.
  
Definition Fchain_correct (fc : Fchain) (n:nat) :=
  forall A `(M : @EMonoid A op E_one E_equiv) k (a:A),
    computation_execute op (fc A k  a)==
    computation_execute op (k  (a ^ n)).


Theorem F3_correct : Fchain_correct F3 3.
Proof.  
  intros    A op E_one E_equiv M k  a ; cbn.
   monoid_simpl M. 
 
(*
 A : Type
  op : Mult_op A
  E_one : A
  E_equiv : Equiv A
  M : EMonoid op E_one E_equiv
  k : Fkont A
  a : A
  H : Proper (equiv ==> equiv ==> equiv) op
  ============================
  computation_execute op (k (a * a * a)) ==
   computation_execute op (k (a * (a * (a * E_one))))

Unfortunately, we don't know wether [k] respects the equivalence
associated with M
 *)
Abort.

End Bad.


(** Equivalence on computations *)

Definition computation_equiv {A:Type} (op: Mult_op A)
           (equiv : Equiv A)
           (c c': @computation A) :=
   computation_execute op c == computation_execute op c'.


Instance Comp_equiv {A:Type} (op: Mult_op A) (equiv : Equiv A):
  Equiv (@computation A) :=
  @computation_equiv A op equiv.

Instance comp_equiv_equivalence {A:Type} (op: Mult_op A)
           (equiv : Equiv A) : Equivalence  equiv ->
                               Equivalence (computation_equiv op equiv).   
Proof.
intro H; split; red in equiv.
 - intro c; red;reflexivity.
 - intros x y H0; red; symmetry; auto.
 -intros x y z H0 H1; red;  transitivity (computation_execute op y);auto. 
 Qed.



(** Fkonts that respect E_equiv *)

Class Fkont_proper
      `(M : @EMonoid A op E_one E_equiv) (k: Fkont A )  :=
  Fkont_proper_prf:
    Proper (equiv ==> computation_equiv op E_equiv) k.




Instance Return_proper `(M : @EMonoid A op E_one E_equiv) :
  Fkont_proper M (@Return A).
Proof.
 intros x y Hxy; assumption.
Qed.



(** Fchain correctness (for exponent of type [nat] *)

Definition Fchain_correct_nat (f : Fchain) (n:nat) :=
 forall A `(M : @EMonoid A op E_one E_equiv) k
        (Hk :Fkont_proper M k)
        (a : A) ,
 computation_execute op (f A k  a) ==
 computation_execute op (k  (a ^ n)).

(** Fchain correctness (for exponent of type [positive] *)

Definition Fchain_correct (f : Fchain) (p:positive) :=
 Fchain_correct_nat f (Pos.to_nat p).




Lemma F1_correct : Fchain_correct F1 1.
Proof.
  intros until M ; intros k Hk a ; unfold F1; simpl.
  apply Hk; monoid_simpl M; reflexivity.
Qed.

Theorem F3_correct : Fchain_correct F3 3.
Proof. 
  intros until M; intros k Hk a; simpl. apply Hk.
  monoid_simpl M;  reflexivity.
Qed.

Theorem F2_correct : Fchain_correct F2 2.
Proof. 
  intros until M; intros k Hk a; simpl;
  apply  Hk;  monoid_simpl M;  reflexivity.
Qed.






(** F2C preserves correctness *)

Lemma F2C_correct (fc : Fchain) (p:positive) :
  Fchain_correct fc p ->  chain_correct (F2C fc) p.
Proof.
  split;auto with chains;  intros until M;intro x; unfold F2C;
  specialize (H _ _ _ _ M (@Return A));
  unfold  Fapply, C1; red; unfold chain_apply;
  rewrite computation_eval_rw;
  apply H; apply Return_proper.
Qed.




Module Bad2.

Lemma Fcompose_correct :
  forall f1 f2 n1 n2, Fchain_correct f1 n1 ->
                        Fchain_correct f2 n2 ->
                        Fchain_correct (Fcompose f1 f2)
                                       (n1 * n2).
Proof.
 unfold Fchain_correct, Fcompose, Fchain_correct_nat; intros.
 specialize (H _  _ _ _ M (fun y : A => f2 A k y) ).  
 specialize (H0 _ _ _ _ M).
 rewrite  H.
 rewrite H0.
 apply Hk.
 rewrite Pos2Nat.inj_mul.
 rewrite power_of_power.  rewrite Nat.mul_comm;reflexivity.
 auto.
 intros x y Hxy .
 red.
Abort.

End Bad2.


Definition Fkont_equiv  `(M : @EMonoid A op E_one E_equiv)
 (k k': Fkont A )  := 
 forall x y : A, x == y ->
                 computation_equiv op E_equiv  (k x) (k' y).


(** Fisrt attempt to define Fchain_proper *)


Module Bad3.
  
Class Fchain_proper (fc : Fchain) := Fchain_proper_bad_prf : 
 forall  `(M : @EMonoid A op E_one E_equiv) k  ,
    Fkont_proper M k ->
    forall x y, x == y ->
               @computation_equiv _ op E_equiv
                                  (fc A k x)
                                  (fc A k y).

Instance Fcompose_proper (f1 f2 : Fchain)
         (_ : Fchain_proper f1)
         (_ : Fchain_proper f2) :
  Fchain_proper (Fcompose f1 f2).
Proof. 
 intros until M;intros k Hk x y Hxy; unfold Fcompose;cbn. 
 apply (H _ _ _ _ M); auto.
 intros u v Huv;apply (H0 _ _ _ _ M);auto.
Qed.

End Bad3.


(** Correct definition *)

Class Fchain_proper (fc : Fchain) := Fchain_proper_prf : 
 forall  `(M : @EMonoid A op E_one E_equiv) k k' ,
    Fkont_proper M k -> Fkont_proper M k' ->    
    Fkont_equiv M k k' ->
   forall x y,  x == y ->
               @computation_equiv _ op E_equiv
                                  (fc A k x)
                                  (fc A k' y).


Instance F1_proper : Fchain_proper F1.
Proof.
  intros until M ; intros k k' Hk Hk' H a b H0; unfold F1; cbn;
  now apply H.  
Qed.

Instance F3_proper : Fchain_proper F3.
Proof.
  intros  A op one equiv M  k k' Hk Hk'  Hkk' x y Hxy;  
  apply Hkk'; add_op_proper M H; repeat rewrite Hxy;
  reflexivity.
Qed.

Instance F2_proper : Fchain_proper F2.
Proof.
  intros  A op one equiv M  k k' Hk Hk'  Hkk' x y Hxy;  
  apply Hkk'; add_op_proper M H; repeat rewrite Hxy;
  reflexivity.
Qed.




(**  Fcompose respects correctness and proper-ness *)

Lemma Fcompose_correct_nat : forall fc1 fc2 n1 n2,
                           Fchain_correct_nat fc1 n1 ->
                           Fchain_correct_nat fc2 n2 ->
                           Fchain_proper fc2 -> 
                           Fchain_correct_nat (Fcompose fc1 fc2)
                                          (n1 * n2)%nat.
Proof.
 unfold  Fcompose, Fchain_correct_nat; intros.
 assert (Fkont_proper M (fun y : A => fc2 A k y)).
 -  intros x y Hxy; apply H1 with E_one M;auto.
 - rewrite  (H _  _ _ _ M (fun y : A => fc2 A k y) H2 a).  
   + rewrite (H0 _ _ _ _ M k Hk).
     * apply  Hk.  
       rewrite power_of_power;auto;
       rewrite Nat.mul_comm;reflexivity.
Qed.


Lemma Fcompose_correct : forall fc1 fc2 n1 n2,
                           Fchain_correct fc1 n1 ->
                           Fchain_correct fc2 n2 ->
                           Fchain_proper fc2 -> 
                           Fchain_correct (Fcompose fc1 fc2)
                                          (n1 * n2).
Proof.
 unfold Fchain_correct; intros.
 rewrite Pos2Nat.inj_mul.
  apply Fcompose_correct_nat;auto.
Qed.


Instance Fcompose_proper (fc1 fc2: Fchain)
                         (_ : Fchain_proper fc1)
                         (_ : Fchain_proper fc2) :
                          Fchain_proper (Fcompose fc1 fc2).
Proof.
  unfold Fcompose; red;  intros. 
  apply   (H _  _ _ _ M);
    (assumption || 
                intros u v Huv;  apply (H0 _ _ _ _ M);auto).
Qed.


Instance Fexp2_nat_proper (n:nat) : 
                           Fchain_proper (Fexp2_of_nat n).
Proof.
  induction n; cbn.
   - apply F1_proper.
   - apply Fcompose_proper ; [apply F2_proper | apply IHn].
Qed.



Lemma  Fexp2_nat_correct (n:nat) : 
                           Fchain_correct_nat (Fexp2_of_nat n) 
                                              (2  ^ n).
Proof.
  induction n; cbn.
 - apply F1_correct.
 -  rewrite Nat.add_0_r;
   replace (2 ^ n + 2 ^ n)%nat with (2 * 2 ^n)%nat by  lia;
   apply Fcompose_correct_nat;auto.
   +  apply F2_correct.
   +  apply  Fexp2_nat_proper.
Qed.


Lemma  Fexp2_correct (p:positive) : 
                           Fchain_correct (Fexp2 p) (2  ^ p).
Proof.
 intros;red.
  rewrite Pos_pow_power, Pos2Nat_morph.
 generalize (Fexp2_nat_correct (Pos.to_nat p)).
 unfold Fexp2.
 change (Pos.to_nat 2) with 2%nat.
  replace (2 ^ Pos.to_nat p)%nat with (2%nat ^ Pos.to_nat p)%M.
 auto.
 now rewrite nat_power_ok.
Qed.

Instance  Fexp2_proper (p:positive) : Fchain_proper (Fexp2 p).
Proof.
  unfold  Fexp2; apply Fexp2_nat_proper.
Qed.
(** ** Remark


We are now  able to build chains for any exponent of the form 
$2^k.3^p$, using Fcompose and previous lemmas.

Let us look at a simple example *)


Hint Resolve F1_correct F1_proper
     F3_correct F3_proper Fcompose_correct Fcompose_proper
     Fexp2_correct Fexp2_proper : chains.

Example F144:  {f : Fchain | Fchain_correct f 144 /\
                                Fchain_proper f}.
 change 144 with ( (3 * 3) * (2 ^ 4))%positive.
 exists (Fcompose (Fcompose F3 F3) (Fexp2 4)); auto with chains.
Defined.

(* 
Compute proj1_sig F144.

= fun (A : Type) (x : Fkont A) (x0 : A) =>
       x1 <--- x0 times x0;
       x2 <--- x1 times x0;
       x3 <--- x2 times x2;
       x4 <--- x3 times x2;
       x5 <--- x4 times x4;
       x6 <--- x5 times x5; x7 <--- x6 times x6; x8 <--- x7 times x7; x x8
     : Fchain


*)

(*** K chains 

 Not every chain can be built efficiently  with [Fcompose]
 For instance, consider the exponent $n=87 = 3 \times 29$. 
29 is a prime 
  number, thus it cannot be decomposed  as a product 
  $p\times q$. 
  On the other hand, consider the equality  $87 = 10 \times 8 + 7$.  We can plan to build a chain $c_1$ for computing $y = x^10$, then
 compose it with a chain $c_2$ for computing $y^8$, and finally 
 multiply the result by $x^7$.
 But, if the chain $c_1$ contains also a computation of $x^7$,
 this value can be used for computing $x^{87} = x^{80}\times x^7$.
 
 In simpler words, we want to build computation schemes that 
 compute two distinct powers of a given value $x$. 
  Like in some programming languages
 that allow  "multiple values", we chosed to express this feature 
 in terms of continuations that accept two arguments

*)


(** Bad solution *)

Definition Fplus (f1 f2 : Fchain) : Fchain :=
  fun A k x => f1 A (fun y => f2 A (fun z => t <--- z times y; k t) x) x.

Example F23 := Fplus F3 (Fplus (Fexp2 4) (Fexp2 2)).


Lemma  F23_ok : chain_correct (F2C F23) 23.
Proof. 
 param_chain_correct.
Qed.


(** Continuations with two arguments *)

Definition Kkont A:=  A -> A -> @computation A.

(** CPS chain builder for  two exponents  *)

Definition Kchain :=  forall A, Kkont A -> A -> @computation A.

(** Kchain for $x^3$ and $x$ *)

Example k3_1 : Kchain := fun A (k:Kkont A) (x:A) =>
  x2 <--- x times x ;
  x3 <--- x2 times x ;
  k x3 x.

(** Kchain for $x^37$ and $x^3$ *)

Example k7_3 : Kchain := fun A (k:Kkont A)   (x:A) =>
  x2 <--- x times x;
  x3 <--- x2 times x ;
  x6 <--- x3 times x3 ;
  x7 <--- x6 times x ;
  k  x7 x3.

(** The Definition of correct chains and proper chains and 
  continuations are adapted to Kchains *)

Definition Kkont_proper `(M : @EMonoid A op E_one E_equiv)
           (k : Kkont A) :=
 Proper (equiv ==> equiv ==> computation_equiv op E_equiv) k . 

Definition Kkont_equiv  `(M : @EMonoid A op E_one E_equiv)
           (k k': Kkont A )  := 
 forall x y : A, x == y -> forall z t, z == t -> 
         computation_equiv op E_equiv   (k  x z) (k' y t).



(** A Kchain is correct with respect to two exponents $n$ and $p$ 
  if it computes $a ^ n$ and $a ^ p$ for every $a$ *)

About EMonoid.

Definition Kchain_correct_nat (kc : Kchain) (n p : nat) :=
  forall  (A : Type) (op : Mult_op A) (E_one : A) (E_equiv : Equiv A)
          (M : EMonoid op E_one E_equiv)
          (k : Kkont A),
    Kkont_proper M k ->
    forall  (a : A) ,
      computation_execute op (kc  A k  a) ==
      computation_execute op (k  (a ^ n) (a ^ p)).


Definition Kchain_correct (kc : Kchain) (n p : positive) :=
  Kchain_correct_nat kc (Pos.to_nat n) (Pos.to_nat p).

Class Kchain_proper (kc : Kchain) :=
Kchain_proper_prf : 
 forall `(M : @EMonoid A op E_one E_equiv) k k' x y ,
   Kkont_proper M k ->
   Kkont_proper M k' -> 
   Kkont_equiv M k k' ->
   E_equiv x y ->
   computation_equiv op E_equiv (kc A k x) (kc A k' y).


Instance k7_3_proper : Kchain_proper k7_3.
Proof.
  intros until M; intros; red; unfold k7_3; cbn;
  add_op_proper M H3; apply H1;  rewrite H2;   reflexivity. 
Qed.

Lemma k7_3_correct : Kchain_correct k7_3 7 3.
Proof.
intros until M; intros; red; unfold k7_3; simpl.
  apply H;  monoid_simpl M;  reflexivity.
Qed. 


 (** conversion between several definitions of correctness *)

Lemma Kchain_correct_conv (kc : Kchain) (n p : nat) :
  0%nat <> n -> 0%nat <> p ->
  Kchain_correct_nat kc n p ->
  Kchain_correct kc (Pos.of_nat n) (Pos.of_nat p).
Proof.
  red; intros; repeat rewrite Nat2Pos.id; auto.
Qed.

(** ** More chain combinators 

  Since we are working with two types of functional chains, we have to define
  several ways of composing them. Each of these operators is certified to
 preserve correctnes and properness *)


(** Conversion of Kchains into Fchains *)

Definition K2F (knp : Kchain) : Fchain :=
  fun A (k:Fkont A) => knp A (fun  y _ => k y).


Lemma K2F_correct_nat :
  forall knp n p, Kchain_correct_nat knp n p ->
                 Fchain_correct_nat (K2F knp) n.
Proof.
 red;intros; unfold K2F;
 apply  (H _ _ _ _ M (fun x y => k x));
 intros x1 y1 H1 x2 y2 H2; apply Hk;  auto.
Qed.

Lemma K2F_correct :
  forall kc n p, Kchain_correct kc n p ->
                 Fchain_correct (K2F kc) n.
Proof.
 red;intros; unfold K2F, Fchain_correct. 
 apply K2F_correct_nat with (Pos.to_nat p);
 apply H.
Qed.

Instance K2F_proper (kc : Kchain)(_ : Kchain_proper kc) :
                               Fchain_proper (K2F kc).
Proof.
 red;intros; unfold K2F;red.  
 apply (H _ _ _ _ M).  
 - red;intros; red;intros.
   intros x1 y1 Hx1 x2 y2 Hx2; now apply H0.
 - intros x1 y1 Hx1 x2 y2 Hx2; now apply H1.
 - red;intros;now apply H2.
 -  assumption.
Qed. 


(** 
  Using [kbr] for  computing $x^b$ and $x^r$, then using [Cq] for
  computing $x^{bq}$, then sending $x^{bq+r}$ and $x^b$ to the continuation
*)

Definition KFK (kbr : Kchain) (fq : Fchain) : Kchain  :=
  fun A k a =>
    kbr A  (fun xb xr =>
              fq A (fun y =>
                      z <--- y times xr; k z xb) xb) a.


Definition KFF (kbr : Kchain) (fq : Fchain) : Fchain :=
  K2F (KFK kbr fq).


Definition FFK (fp fq : Fchain) : Kchain :=
  fun A k a =>  fp A (fun xb  => fq A (fun y => k y xb) xb) a. 

Definition FK (f : Fchain) : Kchain :=
  fun (A : Type) (k : Kkont A) (a : A) =>
    f A (fun y => k y a) a.


Example k17_7 := KFK k7_3 (Fexp2 1).


(** In the following section, we prove that the constructions KFK and KFF
   respect properness and correctness *)

Section KFK_proof.
 Variables b q r: nat.
 Variable kbr : Kchain.
 Variable fq : Fchain.
 Hypothesis Hbr : Kchain_correct_nat kbr b r.
 Hypothesis Hq : Fchain_correct_nat fq q.
 Hypothesis Hbr_prop : Kchain_proper kbr.
 Hypothesis Hq_prop : Fchain_proper fq.

 Lemma KFK_correct_nat : Kchain_correct_nat (KFK kbr fq)
                                            (b * q + r)%nat b.
 Proof.
  intros until M; intros k H a;  unfold KFK;   simpl.
  add_op_proper M Hop.
  
  (** simplifying the hypotheses *)
  specialize (Hq _ _ _ _ M).
  specialize (Hbr_prop _ _ _ _ M).
  specialize (Hq_prop _ _ _ _ M).
  specialize (Hbr _ _ _ _ M (fun xb xr : A =>
          fq A (fun y : A => z <--- y times xr; k z xb) xb)).

  assert
    (Kkont_proper M
                  (fun xb xr : A =>
                     fq A
                        (fun y : A => z <--- y times xr; k z xb)
                        xb)).
 - intros x y Hxy z t Hzt;simpl; red;simpl.
   assert
     (forall X Y,
        X == Y ->
        computation_equiv op E_equiv
                          ((fun y0 : A =>
                              z0 <--- y0 times z; k z0 x) X)
                               ((fun y0 : A =>
                                   z0 <--- y0 times t; k z0 y) Y)).
   +  intros;  simpl;  red;  simpl;   apply H; auto.
      rewrite H0, Hzt; reflexivity.
   +  specialize (H0 x y Hxy); red in H0; simpl; simpl in H0.
      assert (Proper (computation_equiv op E_equiv  ==> equiv)
                     (computation_execute op)).
     *  intros X Y HXY; red in HXY; auto.
     *   apply H1; red;apply Hq_prop.
        red;intros;simpl;red;simpl; intros x1 y1 Hx1;  apply H.
        rewrite Hzt, Hx1;reflexivity. 
        reflexivity.
        intros x1 y1 Hx1 ;apply H.
        rewrite Hx1;reflexivity. 
        reflexivity.
        intros x1 y1 Hx1;simpl;red;simpl.
        apply H.
        rewrite Hx1, Hzt; reflexivity.
        assumption.
        assumption.
   -  specialize (Hbr H0 a); rewrite Hbr.
      specialize (Hq
                    (fun y : A =>
                       z <--- y times a ^ r; k z (a ^ b))).
      assert ( Fkont_proper M
                            (fun y : A =>
                               z <--- y times a ^ r; k z (a ^ b))).
   +  red; intros  x y Hxy; red; simpl.
       apply H.
       rewrite Hxy;reflexivity.
       reflexivity. 
   + rewrite  (Hq  H1);simpl;apply H.
     monoid_simpl M.
     rewrite  (power_of_power M a b q).
     rewrite (Nat.mul_comm q b). 
     rewrite power_of_plus; reflexivity.
     reflexivity.
Qed.


 Lemma KFF_correct_nat : Fchain_correct_nat (KFF kbr fq)
                                            (b * q + r)%nat .
 Proof.
   apply K2F_correct_nat with b;  apply KFK_correct_nat.
 Qed.

Lemma KFK_proper : Kchain_proper (KFK kbr fq).
 Proof.
   intros until M; intros k k' x y Hk Hk' ;  unfold KFK;   simpl.
   add_op_proper M Hop.
   specialize (Hbr_prop _ _ _ _ M).
   specialize (Hq_prop _ _ _ _ M).
    red; simpl; intros; apply Hbr_prop;auto.
    - intros  x1 y1 Hx1 x2 y2 Hx2; apply Hq_prop;auto.
      + red; intros;simpl; intros x' y' H'; red;simpl; apply Hk.
        rewrite H';reflexivity.
        reflexivity.
      +  intros x' y' H'; red;simpl; apply Hk.
         rewrite H';reflexivity.
         reflexivity. 
      + intros y0 y3 H3;red;simpl; apply Hk.
        rewrite H3,Hx2;reflexivity.
        assumption.
    -  red;intros;intros u v Huv w t Hwt.
       apply Hq_prop;auto.
       + intros X Y HXY;red;simpl; apply Hk'.
         * rewrite HXY;reflexivity.
         * reflexivity.
       + intros X Y HXY;red;simpl; apply Hk'.
         * rewrite HXY;reflexivity.
         * reflexivity.
       + red;intros;red;simpl; apply Hk';auto.
         rewrite H1, Hwt; reflexivity.
    -  red;intros;apply Hq_prop;auto.
       + intros X Y HXY;red;simpl;  apply Hk.
         * rewrite HXY;reflexivity.
         * reflexivity. 
       + intros X Y HXY;red;simpl;  apply Hk'.
         * rewrite HXY;reflexivity.
         * reflexivity. 
       + red;intros;red;simpl;  apply H; auto.
         * rewrite H2, H3;reflexivity. 
Qed.

Global Instance KFF_proper : Fchain_proper (KFF kbr fq).
 Proof.
   intros until M; intros k k' Hk Hk' H x y Hxy;
   unfold KFF;   simpl.
   add_op_proper M Hop.
   specialize (Hbr_prop _ _ _ _ M).
   specialize (Hq_prop _ _ _ _ M).
    red; simpl; intros; apply Hbr_prop;auto.
    - intros  x1 y1 Hx1 x2 y2 Hx2; apply Hq_prop;auto.
      + red; intros;simpl; intros x' y' H'; red;simpl.  apply Hk.
        rewrite H';reflexivity.
      +   intros x' y' H'; red;simpl; apply Hk.
         rewrite H';reflexivity.
      +  intros y0 y3 H3;red;simpl; apply Hk.
        rewrite H3,Hx2;reflexivity.
    -  red;intros;intros u v Huv w t Hwt.
       apply Hq_prop;auto.
       + intros X Y HXY;red;simpl; apply Hk'.
         * rewrite HXY;reflexivity.
       + intros X Y HXY;red;simpl; apply Hk'.
         * rewrite HXY;reflexivity.
       + red;intros;red;simpl; apply Hk';auto.
         rewrite H0, Hwt; reflexivity.
    -  red;intros;apply Hq_prop;auto.
       + intros X Y HXY;red;simpl;  apply Hk.
         * rewrite HXY;reflexivity.
       + intros X Y HXY;red;simpl;  apply Hk'.
         * rewrite HXY;reflexivity.
       + red;intros;red;simpl;  apply H; auto.
         * rewrite H2, H1;reflexivity. 
Qed.

End KFK_proof.  

Lemma KFK_correct :
  forall (b q r : positive) (kbr : Kchain) (fq : Fchain),
    Kchain_correct kbr b r ->
    Fchain_correct fq q ->
    Kchain_proper kbr ->
    Fchain_proper fq -> Kchain_correct (KFK kbr fq) (b * q + r) b.
Proof.
 red; intros; rewrite Pos2Nat.inj_add, Pos2Nat.inj_mul;
 apply KFK_correct_nat;assumption.
Qed.

Lemma KFF_correct :
  forall (b q r : positive) (kbr : Kchain) (fq : Fchain),
    Kchain_correct kbr b r ->
    Fchain_correct fq q ->
    Kchain_proper kbr ->
    Fchain_proper fq -> Fchain_correct (KFF kbr fq) (b * q + r).
Proof.
  red; intros;  rewrite Pos2Nat.inj_add, Pos2Nat.inj_mul;
  apply KFF_correct_nat;assumption.
Qed.


Lemma FFK_correct_nat :
  forall (p q  : nat) (fp fq : Fchain),
    Fchain_correct_nat fp p  ->
    Fchain_correct_nat fq q ->
    Fchain_proper fp ->
    Fchain_proper fq -> Kchain_correct_nat (FFK fp fq) (p * q) p.
Proof.
intros.   
red;intros.
 unfold FFK;   simpl.
  add_op_proper M Hop.
  
  (** simplifying the hypotheses *)
  specialize (H _ _ _ _ M).
  specialize (H0 _ _ _ _ M).  
  specialize (H1 _ _ _ _ M).
  specialize (H2 _ _ _ _ M).
  specialize (H (fun xb : A => fq A (fun y : A => k y xb) xb)).
  assert (Fkont_proper M
                        (fun xb  : A => fq A
                                             (fun y : A =>  k y xb)
                                             xb)).
 - intros x y Hxy ;simpl; red;simpl.
   apply H2.
   +   intros  u v Huv; apply H3; (assumption || reflexivity).  
   + intros  u v Huv; apply H3; (assumption || reflexivity). 
   + intros  u v Huv; apply H3; (assumption || reflexivity). 
   + assumption. 

 -  specialize (H  H4 a); rewrite H.
    specialize (H0  (fun y => k y (a ^ p))).
    assert (Fkont_proper M (fun y : A => k y (a ^ p))).
      +  red; intros  x y Hxy; red; simpl;  apply H3;
         (assumption || reflexivity). 
      + rewrite (H0 H5);  apply H3; [| reflexivity].
        rewrite  (power_of_power M a p q), (Nat.mul_comm q p);
       reflexivity.
Qed.


Lemma FFK_correct :
  forall (p q  : positive) (fp fq : Fchain),
    Fchain_correct fp p  ->
    Fchain_correct fq q ->
    Fchain_proper fp ->
    Fchain_proper fq -> Kchain_correct (FFK fp fq) (p * q ) p.
Proof.
 intros;red; rewrite  Pos2Nat.inj_mul; now apply FFK_correct_nat. 
Qed.


Instance FFK_proper 
   (fp: Fchain) (fq : Fchain)
    (_ :   Fchain_proper fp)
    (_ :  Fchain_proper fq) :  Kchain_proper (FFK fp fq) .
Proof.
 red;intros;
 specialize (H _ _ _ _ M); specialize (H0 _ _ _ _ M).
  add_op_proper M Hop; unfold FFK;simpl.
  red; simpl; intros;  apply H;auto.
 - intros  x1 y1 Hx1 ; apply H0;auto.
      +  intros x' y' H'; red;simpl;  apply H1;
        (assumption || reflexivity). 
      +   intros x' y' H'; red;simpl; apply H1;
          (assumption || reflexivity).
      +  intros y0 y3 H5;red;simpl; apply H1; auto.
 -  intros u v Huv ;  apply H0;auto.
    + intros X Y HXY;red;simpl; apply H2;
      (assumption || reflexivity).
    + intros X Y HXY;red;simpl; apply H2;
      (assumption || reflexivity).
    + red;intros;red;simpl; apply H2;auto.
 -  red;intros; apply H0;auto.
    + intros X Y HXY;red;simpl;  apply H1;
      (assumption || reflexivity).
    + intros X Y HXY;red;simpl;  apply H2;
      (assumption || reflexivity).
    + red;intros;red;simpl; apply H3; auto.
Qed.



Lemma FK_correct : forall (p: positive) (Fp : Fchain),
                     Fchain_correct  Fp p ->
                     Fchain_proper Fp ->
                     Kchain_correct (FK Fp) p 1.
Proof.
  intros;red; unfold FK;  red; intros until M;intros k H1 a.
  specialize (H _ _ _ _ M (fun y : A => k y a)).
  specialize (H0 _ _ _ _ M);
  add_op_proper M Hop.
  assert (Fkont_proper M (fun y : A => k y a)).
 -   intros x y Hxy; apply H1; (assumption || reflexivity).
 -  specialize (H H2 a);rewrite H;apply H1.
    + reflexivity.
    + generalize (power_eq3 a);simpl;now symmetry.
Qed.

Instance  FK_proper  (Fp : Fchain) (_ : Fchain_proper Fp):
  Kchain_proper (FK Fp).
Proof.
  unfold FK; intros until M; intros k k' x y  H0 H1 H2 H3. 
  apply (H _ _ _ _ M).  
  -  intros u v Huv;  apply H0; (assumption || reflexivity). 
  - intros u v Huv;  apply H1; (assumption || reflexivity).     
  - intros  u v Huv; apply H2; auto.
  -  assumption.
Qed.


Hint Resolve KFF_correct KFF_proper KFK_correct KFK_proper : chains.

Lemma k3_1_correct : Kchain_correct k3_1 3 1.
Proof.
  intros until M;intros k H a.
  unfold k3_1; simpl;  apply H; monoid_simpl M;reflexivity.
Qed.

Lemma k3_1_proper : Kchain_proper k3_1.
Proof.
  intros until M; intros k k' x y H H0 H1 H2.
  unfold k3_1;simpl.
  apply H1;auto.
  add_op_proper M H3; rewrite H2; reflexivity.
Qed.

Hint Resolve k3_1_correct k3_1_proper : chains.          

(** an example of correct chain construction  *)


Definition F87 :=
 let k7_3 :=  KFK k3_1 (Fexp2 1) in
 let k10_7 := KFK k7_3 F1 in
 KFF k10_7 (Fexp2 3).

Compute the_exponent (F2C F87).


Lemma OK87 : Fchain_correct F87 87.
Proof.
 unfold F87; change 87 with (10 * (2 ^ 3) + 7)%positive.
 apply KFF_correct;auto with chains.
 change 10 with (7 * 1 + 3); apply KFK_correct;auto with chains.
 change 7 with (3 * 2 ^ 1 + 1)%positive;  apply KFK_correct;auto with chains.
Qed.

Ltac compute_chain ch := 
   let X := fresh "x" in 
   let Y := fresh "y" in
   let X := constr:(ch) in 
   let Y := (eval vm_compute in  X) 
   in exact Y.


Definition C87' := ltac:( compute_chain C87 ).


Print C87'.

Lemma PF87:  parametric C87'.
Proof. parametric_tac. Qed.

(** *** Automatic generation of correct euclidean chains 

We want to define a function that builds a correct chain
for any positive exponent, using the previously defined
and certified composition operators : Fcompose, KFK, etc.

Obviously, we have to define total mutually recursive functions:

 - A function that builds an Fchain for any positive exponent p
 - A function that builds a Kchain for any pair of exponents
   (n,p) where $1<p<n$

 In Coq, various ways of building functions are available:
  - Structural [mutual] recursion with [Fixpoint]
  - Using [Program Fixpoint]  
  - Using [Function]

 For simplicity's sake, we chosed to avoid dependent elimination
 and used [Function] with a decreasing measure.
 For this purpose, we define a single data-type for associated with
 the generation of F- and K-chains.

For specifying the computation of a Kchain for $n$ and $p$
where $p<n$, we use the pair of positive numbers $(p,n-p)$,
thus avoiding to propagate the constraint $p<n$ in 
our definitions.
*)


Inductive signature : Type :=
| gen_F (n:positive) (** Fchain for the exponent n *)
| gen_K (p d: positive) (** Kchain for the exponents p+d  and p *) . 




(** Unifying  statements about chain generation *)

Definition signature_exponent (s:signature) : positive :=
 match s with 
| gen_F n => n 
| gen_K p d  =>  p + d
end.

Definition kont_type (s: signature)(A:Type) : Type :=
match s with 
| gen_F _  => Fkont A 
| gen_K _ _   => Kkont A
end.

Definition chain_type (s: signature) : Type :=
 match s with 
| gen_F _   => Fchain
|  gen_K _ _  => Kchain
end.

Definition correctness_statement (s: signature) : 
chain_type s -> Prop :=
match s  with
  | gen_F p => fun ch => Fchain_correct ch p
  | gen_K p d   => fun ch => Kchain_correct ch (p + d) p
end.


Definition proper_statement (s: signature) : 
chain_type s -> Prop :=
match s  with
  | gen_F p => fun ch => Fchain_proper ch 
  | gen_K p d   => fun ch => Kchain_proper ch 
end.

(** ** Full correctness *)

Definition  OK (s: signature) 
  := fun c: chain_type s => correctness_statement s c /\
                            proper_statement s c.


Hint Resolve pos_gt_3 : chains.

Section Gamma.

Variable gamma: positive -> positive.
Context (Hgamma : Strategy gamma).

Definition signature_measure (s : signature) : nat :=
match s with
  | gen_F n => 2 * Pos.to_nat n 
  | gen_K  p d => 2 * Pos.to_nat (p + d) +1
end.

(* Proof obligations for chain generation (generated by Function) *)
(* These lemmas are also applied in AM *)

 Lemma PO1 :forall (s : signature) (i : positive),
  s = gen_F i ->
  forall anonymous : i <> 1,
  pos_eq_dec i 1 = right anonymous ->
  forall anonymous0 : i <> 3,
  pos_eq_dec i 3 = right anonymous0 ->
  exact_log2 i = None ->
  forall q r : N,
  r = 0%N ->
  N.pos_div_eucl i (N.pos (gamma i)) = (q, 0%N) ->
  (signature_measure (gen_F (N2pos q)) < signature_measure (gen_F i))%nat.

   intros; unfold signature_measure.
     generalize (N.pos_div_eucl_spec i (N.pos (gamma i))).
      rewrite H4; N2pos_destruct q p. (*destruct q; [discriminate | ].*)

    subst r; repeat rewrite  N.add_0_r.
    injection 1.  intro H5 ;rewrite H5.
    gamma_bounds gamma i H12 H14.
    assert (H13 : p <> 1).
 
   +  intro Hp ; subst p.  simpl in H5.
       destruct (Pos.lt_irrefl i).
       now rewrite H5 at 1.

   +  assert (H11 := pos_lt_mul p (gamma i) H12).
      rewrite Pos2Nat.inj_lt in  H11.
      rewrite  Pos2Nat.inj_mul in *;  lia.
      Qed. 

 Lemma PO2 :  forall (s : signature) (i : positive),
     s = gen_F i ->
     forall anonymous : i <> 1,
       pos_eq_dec i 1 = right anonymous ->
       forall anonymous0 : i <> 3,
         pos_eq_dec i 3 = right anonymous0 ->
         exact_log2 i = None ->
         forall q r : N,
           r = 0%N ->
           N.pos_div_eucl i (N.pos (gamma i)) = (q, 0%N) ->
           (signature_measure (gen_F (gamma i)) < signature_measure (gen_F i))%nat.
 Proof.
   intros; unfold signature_measure.
   apply mult_lt_compat_l ;
     [ apply Pos2Nat.inj_lt; apply gamma_lt|] ;  auto with chains.
 Qed.


 Lemma PO3 :  forall (s : signature) (i : positive),
  s = gen_F i ->
  forall anonymous : i <> 1,
  pos_eq_dec i 1 = right anonymous ->
  forall anonymous0 : i <> 3,
  pos_eq_dec i 3 = right anonymous0 ->
  exact_log2 i = None ->
  forall (q r : N) (p : positive),
  r = N.pos p ->
  N.pos_div_eucl i (N.pos (gamma i)) = (q, N.pos p) ->
  (signature_measure (gen_F (N2pos q)) < signature_measure (gen_F i))%nat.
 Proof.
    intros; unfold signature_measure.
    gamma_bounds gamma i H12 H14.  quotient_small H4  H5.
    apply mult_lt_compat_l; [ | auto with arith chains].
    apply Pos2Nat.inj_lt.
      destruct q; simpl in *.
      transitivity (gamma i);auto.
      now rewrite pos2N_inj_lt.
      Qed.


 Lemma PO4 : forall (s : signature) (i : positive),
  s = gen_F i ->
  forall anonymous : i <> 1,
  pos_eq_dec i 1 = right anonymous ->
  forall anonymous0 : i <> 3,
  pos_eq_dec i 3 = right anonymous0 ->
  exact_log2 i = None ->
  forall (q r : N) (p : positive),
  r = N.pos p ->
  N.pos_div_eucl i (N.pos (gamma i)) = (q, N.pos p) ->
  (signature_measure (gen_K (N2pos (N.pos p)) (gamma i - N2pos (N.pos p))) <
   signature_measure (gen_F i))%nat.
intros; unfold signature_measure.
    apply lt_S_2i;  rewrite Pplus_minus. 
    gamma_bounds gamma i H5 H6.
    +  apply Pos2Nat.inj_lt;  auto.
    +  rest_small H4 H5; now  apply Pos.lt_gt.
Qed.

 Lemma PO6: forall (s : signature) (p d : positive),
  s = gen_K p d ->
  forall anonymous : p <> 1,
  pos_eq_dec p 1 = right anonymous ->
  forall q r : N,
  r = 0%N ->
  N.pos_div_eucl (p + d) (N.pos p) = (q, 0%N) ->
  (signature_measure (gen_F (N2pos q)) < signature_measure (gen_K p d))%nat.
Proof.
intros; unfold signature_measure.
    quotient_small H2 H5.
    destruct p; (discriminate || reflexivity).
    N2pos_destruct q q.
    +       destruct (pos_div_eucl_quotient_pos _ _ _ _ H2);auto with chains.
           rewrite pos2N_inj_add; apply N.le_add_r.
    +  simpl; rewrite <- pos2N_inj_lt in H5;
       rewrite Pos2Nat.inj_lt in H5.
       lia.
Qed.       

Lemma PO8 :forall (s : signature) (p d : positive),
  s = gen_K p d ->
  forall anonymous : p <> 1,
  pos_eq_dec p 1 = right anonymous ->
  forall (q r : N) (p0 : positive),
  r = N.pos p0 ->
  N.pos_div_eucl (p + d) (N.pos p) = (q, N.pos p0) ->
  (signature_measure (gen_F (N2pos q)) < signature_measure (gen_K p d))%nat.
Proof.
  intros; unfold signature_measure.
     assert (N2pos q < p+d)%positive.
    quotient_small H2 H5.
    generalize anonymous; 
      destruct p; simpl; try reflexivity.
    now destruct 1.
    generalize (pos_div_eucl_quotient_pos  _ _ _ _ H2).
    intros H6;  destruct q;auto.
    destruct H6;auto with chains.
    rewrite pos2N_inj_add;  apply N.le_add_r;auto with chains.
    + revert H3; pos2nat_inj_tac; intros;lia.
Qed.

 Lemma PO9 :forall (s : signature) (p d : positive),
  s = gen_K p d ->
  forall anonymous : p <> 1,
  pos_eq_dec p 1 = right anonymous ->
  forall (q r : N) (p0 : positive),
  r = N.pos p0 ->
  N.pos_div_eucl (p + d) (N.pos p) = (q, N.pos p0) ->
  (signature_measure (gen_K (N2pos (N.pos p0)) (p - N2pos (N.pos p0))) <
   signature_measure (gen_K p d))%nat.
Proof.
intros; unfold signature_measure.
    apply Nat.add_lt_mono_r; apply mult_S_lt_compat_l;auto with chains.
    rewrite Pplus_minus.
    +  apply Pos2Nat.inj_lt; apply Pos.lt_add_diag_r; cbn.
    +  generalize (N.pos_div_eucl_remainder (p + d) (N.pos p) );
      rewrite H2; cbn; unfold N.lt ; intro H5; red.
       simpl in H5; now rewrite Pos.compare_antisym, H5.
Qed.

Function chain_gen  (s:signature) {measure signature_measure}
:  chain_type s :=
  match s  return chain_type s with
    | gen_F i =>
      if pos_eq_dec i 1 then F1 else
        if pos_eq_dec i 3
        then F3
        else 
          match exact_log2 i with
              Some p => Fexp2 p
            | _ =>
              match N.pos_div_eucl i (Npos (gamma i))
              with
                | (q, 0%N) => 
                  Fcompose  (chain_gen (gen_F (gamma i)))
                            (chain_gen (gen_F (N2pos q)))
                | (q,r)  => KFF (chain_gen
                                   (gen_K (N2pos r)
                                          (gamma i - N2pos r)))
                                (chain_gen (gen_F (N2pos q)))
                                
              end end
    | gen_K p d =>
      if pos_eq_dec p 1 then FK (chain_gen (gen_F (1 + d)))
      else
        match N.pos_div_eucl (p + d)  (Npos p) with
          | (q, 0%N) => FFK   (chain_gen (gen_F p))
                              (chain_gen (gen_F (N2pos q)))
          | (q,r)  => KFK (chain_gen (gen_K (N2pos r)
                                            (p - N2pos r)))
                          (chain_gen (gen_F (N2pos q)))
        end
  end.
Proof.
  - intros; eapply PO1; eauto. 
  - intros; eapply PO2; eauto. 
  - intros; eapply PO3; eauto.
  - intros; eapply PO4; eauto.
  - intros; unfold signature_measure; subst p;  lia.
  - intros; eapply PO6; eauto.
  - intros; unfold signature_measure; pos2nat_inj_tac; lia.
  - intros; eapply PO8; eauto.
  - intros; eapply PO9; eauto.
Defined.

Definition make_chain (n:positive) : chain :=
 F2C (chain_gen (gen_F n)).


Lemma chain_gen_OK : forall s:signature, OK  s (chain_gen  s).
intro s; functional induction chain_gen s.

 - split; [apply F1_correct | apply F1_proper].

 - split; [apply F3_correct | apply F3_proper].

- generalize (exact_log2_spec _ _ e2);intro; subst i; split;
  [apply Fexp2_correct | apply Fexp2_proper].

-  destruct IHc, IHc0.
   generalize (N_pos_div_eucl_divides _ _ _ e3); intro eq_i.
    split.
   + cbn;  rewrite <- eq_i at -1 ; apply Fcompose_correct;auto.
   +  pattern i at 1 ; rewrite <- eq_i at 1; apply Fcompose_proper;auto.


-  pattern i at 1;
  replace i with (gamma i * (N2pos q) + N2pos r).
   + destruct IHc, IHc0;split.
     *  apply KFF_correct;auto.
        simpl; simpl in H; 
        replace (gamma i) with  
        (N2pos r + (gamma i - N2pos r)) at 2.
        apply H.
        rewrite Pplus_minus;auto with chains.
        apply Pos.lt_gt;   rewrite  N2pos_lt_switch2. 
        generalize 
          (N.pos_div_eucl_remainder i (N.pos (gamma i) )); 
          rewrite e3;  simpl;auto with chains.
        destruct r; [ contradiction | auto with chains].
     *  apply KFF_proper;auto with chains.

   + apply  N_pos_div_eucl_rest; auto with chains.
     destruct r;try contradiction; auto with chains. 
   apply (div_gamma_pos   _ _ _ e3); auto with chains.
    apply pos_gt_3;auto with chains.
    destruct (exact_log2 i); [contradiction | reflexivity].


- destruct IHc; split.
  +   apply FK_correct; auto with chains.
  +  apply FK_proper; auto with chains.
  

- destruct IHc, IHc0;split.
   +   red; replace (p + d)%positive with (p * N2pos q)%positive.
       * apply FFK_correct; auto with chains.
       *  generalize  (N.pos_div_eucl_spec   (p + d) (N.pos p));
         rewrite e1;    rewrite N.add_0_r ; intro  H3;
         case_eq (q * N.pos p)%N.
          intro H4;  rewrite H4 in H3 ; discriminate.
          intros p0 H4; rewrite H4 in H3; injection H3;
          intro H5;   rewrite H5.
          N2pos_destruct q q.
          injection H4;auto with chains.
          rewrite  Pos.mul_comm;  auto with chains.
   +   apply FFK_proper;auto with chains.

-   destruct IHc, IHc0; split.
    + red; replace (p+d) with (p * N2pos q + N2pos r).
      * apply KFK_correct;auto with chains.
        red in H;   replace (N2pos r + (p - N2pos r))%positive with p in H.
        apply H.  
        rewrite Pplus_minus;  auto.
        generalize  (N.pos_div_eucl_remainder (p + d) (N.pos p));
          rewrite e1; cbn;  intro H3.
        apply Pos.lt_gt;  rewrite  N2pos_lt_switch2;auto with chains.
        destruct r; [contradiction | auto with chains].

      *   generalize  (N.pos_div_eucl_spec   (p + d) (N.pos p));
        rewrite e1; intros H3; clear H H0 H1 H2.
          case_eq q.
          {intro;   generalize (pos_div_eucl_quotient_pos _ _ _ _ e1).
            destruct 1;auto with chains.
            rewrite pos2N_inj_add;  apply N.le_add_r.
          }
          {
           intros p0 Hp0;subst q; cbn; destruct r; [ contradiction | ].
           simpl;  simpl in H3;  injection H3.
          rewrite Pos.mul_comm; auto with chains.
          }
    +   apply KFK_proper;  auto with chains.
Qed. 


Theorem make_chain_correct : forall p, chain_correct (make_chain p) p.
Proof.
  intro p; destruct (chain_gen_OK (gen_F p)).
  unfold make_chain; apply F2C_correct; apply H.
Qed.

End Gamma.

Arguments make_chain {gamma _} _ _ _ .
Compute the_exponent (make_chain  87).


(** cf Coq workshop 2014 by Jason Grosss *)

Module  Examples.

Import Int31.
Compute cpower make_chain 0 12.
Compute cpower make_chain 87 12.

Definition fast_int31_power (x :positive)(n:N) : Z :=
  Int31.phi (cpower make_chain n (snd (positive_to_int31 x))).

Definition slow_int31_power (x :positive)(n:N) : Z :=
  Int31.phi (power (snd (positive_to_int31 x)) (N.to_nat n) ).

Definition binary_int31_power (x :positive)(n:N) : Z :=
Int31.phi (N_bpow (snd (positive_to_int31 x)) n ).





(** long computations ... *)

Definition big_chain := ltac:(compute_chain  (make_chain 6145319)).

Print big_chain.

(*
big_chain = 
fun (A : Type) (x : A) =>
x0 <--- x times x;
x1 <--- x0 times x0;
x2 <--- x1 times x1;
x3 <--- x2 times x1;
x4 <--- x3 times x3;
x5 <--- x4 times x;
x6 <--- x5 times x5;
x7 <--- x6 times x6;
x8 <--- x7 times x1;
x9 <--- x8 times x5;
x10 <--- x9 times x8;
x11 <--- x10 times x9;
x12 <--- x11 times x11;
x13 <--- x12 times x11;
x14 <--- x13 times x10;
x15 <--- x14 times x14;
x16 <--- x15 times x11;
x17 <--- x16 times x16;
x18 <--- x17 times x17;
x19 <--- x18 times x18;
x20 <--- x19 times x19;
x21 <--- x20 times x20;
x22 <--- x21 times x21;
x23 <--- x22 times x22;
x24 <--- x23 times x23;
x25 <--- x24 times x24;
x26 <--- x25 times x25;
x27 <--- x26 times x26; x28 <--- x27 times x14; Return x28
     : forall A : Type, A -> computation

Arguments big_chain _%type_scope
 *)






Remark RM : (1 < 56789)%N. Proof. reflexivity. Qed.

Definition M := Nmod_Monoid _ RM.

Definition exp56789 x := chain_apply big_chain (M:=M) x.



Time Compute chain_apply big_chain (M:=M) 13%N.


Eval cbv iota  match delta [big_chain chain_apply computation_eval  ]  zeta beta in  fun x => chain_apply  big_chain (M:=M) x.


Definition C87' := ltac:( compute_chain C87 ).


Print big_chain.
Time   Compute  Int31.phi
   (chain_apply big_chain (snd (positive_to_int31  67777))) .


Compute  Int31.phi (chain_apply big_chain (snd (positive_to_int31  67777))) .

Compute chain_length  big_chain.





Goal parametric (make_chain 45319).
Time parametric_tac.
Qed.


Remark big_correct :chain_correct (make_chain 45319) 45319.
Time param_chain_correct.
(* Finished transaction in 4.054 secs (4.051u,0.s) (successful) *)
Qed.

Remark big_correct' : chain_correct (make_chain 453) 453.
Time reflection_correct_tac.
Qed.

(*** Too long :-(
Remark big_correct'' : chain_correct (make_chain 45319) 45319.
Time reflection_correct_tac.


That's normal. The reflection tactic builds a linear term w.r.t. the exponent !

*)


Remark big_correct''' : chain_correct (make_chain 453) 453.
Time apply make_chain_correct.
(* Finished transaction in 0. secs (0.u,0.s) (successful)
*)
Qed.


Compute make_chain 87.

End Examples.

Require Import Extraction.
Locate exp56789.
Extraction Language OCaml.
Extraction "bigmod" Examples.exp56789.





Recursive Extraction cpower.
Recursive Extraction make_chain.
