(** Copy of gaia's ssete9.v (for experimenting Alectryon documentation) *)

(** * Ordinals in Pure Coq 
  Copyright INRIA (2013-2013) Marelle Team (José Grimm).
  After a work of Castéran
*)


From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import fintype bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * prelude *)

(** Useful lemmas missing in ssreflect *)

Lemma if_simpl (p: bool): (if p then true else false) = p.
Proof. by case: p. Qed.


Lemma ltn_simpl1 n n': ((n' + n).+1 < n) =  false.
Proof. by rewrite - addSn - {2} (add0n n) ltn_add2r. Qed.

Lemma eqn_simpl1 n n': ((n' + n).+1 == n) = false.
Proof. by rewrite - addSn - {2} (add0n n) eqn_add2r. Qed.


Lemma ltn_simpl2 n n' n'':
  (n * n' + n + n' < n * n'' + n + n'') =  (n' < n'').
Proof.  by rewrite addnAC (addnAC _ _ n'') ltn_add2r - ! mulSnr ltn_mul2l. Qed.

Lemma eqn_simpl2 n n' n'':
   (n * n' + n + n' == n * n'' + n + n'') =  (n' == n'').
Proof. by  rewrite addnAC (addnAC _ _ n'') eqn_add2r - ! mulSnr eqn_mul2l. Qed.

Lemma ltn_add_le m1 m2 n1 n2: m1 < n1 -> m2 <= n2 -> m1 + m2 < n1 + n2.
Proof. by move => pa pb; move: (leq_add pa pb); rewrite addSn. Qed.

Lemma ltn_add_el m1 m2 n1 n2: m1 <= n1 -> m2 < n2 -> m1 + m2 < n1 + n2.
Proof. by move => pa pb; move: (leq_add pa pb); rewrite addnS. Qed.

Lemma ltn_add_ll m1 m2 n1 n2: m1 < n1 -> m2 < n2 -> m1 + m2 < n1 + n2.
Proof. by move => pa pb; exact: (ltn_add_el (ltnW pa) pb). Qed.

(** The ssreflect comparison on nat is WF *)

Lemma lt_wf: well_founded (fun (a b:nat) => a < b).
Proof.
move => n; split;elim: n; first by move => y ; rewrite ltn0.
move => n H y; rewrite ltnS leq_eqVlt; case /orP; first by move => /eqP ->.
by apply: H.
Defined.


(** ** Example 1 *)

(** An example of function defined by transfinite induction using [Fix] *)
Module Wf_ex.


Definition f_spec f n := 
   if n is m.+2 then  (f (f m.+1).+1 ).+1 else 0.

Lemma f_spec_simp f n: (forall n, f n = f_spec f n) -> f n = n.-1.
Proof.
move => H; case: n; first by rewrite H.
elim; first by rewrite H.
by move => n Hr; rewrite H /f_spec Hr Hr /=.
Qed.
    

Lemma f0 n p: p <= n -> p.+2 <= n.+2.
Proof. by rewrite ltnS ltnS. Qed.

Definition f1 :
  forall x, (forall z, z < x -> {y:nat |y <= z.-1}) ->
  {y:nat | y <= x.-1}.
Proof.
case; [by exists 0 | case; first by exists 0 ].
move => n Hr.
move: (Hr _ (ltnSn n.+1)) => [y1 h1].
move: (Hr _ (f0 h1)) =>  [y2 h2].
exists y2.+1; apply: (leq_trans h2 h1).
Defined.

Definition f2 := Fix lt_wf _ f1.
Definition f (x:nat): nat := sval (f2 x).

Lemma f_eqn x: f2 x =  f1  (fun y _ => f2 y).
Proof.
move: x; apply: (Fix_eq lt_wf).
case => //; case => //n p p' Hp.
rewrite /f1 Hp; case: (p' n.+1 (ltnSn n.+1)) => y Hy /=.
by rewrite Hp.
Qed.


Lemma f_correct n: f n = f_spec f n. 
Proof.
case: n => //; case => // n.
rewrite /f_spec /f f_eqn /f1.
by case: (f2 n.+1) => y1 H1; case: (f2 y1.+1) => y2 H2.
Qed.


End Wf_ex.

(** ** Example 2 *)

(** Second example, $ f(n) = 1 + \sum_ {i<n} f(i)$ 
  #f(n) = 1 + \sum<sub>(i &lt; n)</sub> f(i)# *)

Module Wfsum.

Definition psum (f: nat -> nat) n := \sum_(i< n) (f i).
Definition f_spec f:= forall n, f n = (psum f n).+1.


Lemma f_spec_simp f n: f_spec f -> f n = 2 ^ n.
Proof.
move => fs.
elim: n; first by rewrite fs /f_spec /psum big_ord0.
move => n Hrec. 
rewrite fs /f_spec /psum big_ord_recr /= addnC - addnS.
by rewrite -/(psum f n) - fs Hrec addnn expnS mul2n.
Qed.

Lemma psum_exten n f g :
   (forall k, k < n -> f k = g k) -> (psum f n).+1 = (psum g n).+1.
Proof.
move => h; rewrite /psum; congr S; apply: eq_big => // [] [i lin] _ /=.
by apply: h.
Qed.


Lemma lt_dec n m: {n <m} + {~~ (n < m) }. 
Proof. by case: (n<m);  [ left | right ]. Qed.

Definition extension  (n : nat) (p : forall k : nat, k < n -> nat) k :=
  match lt_dec k n with
    | left x =>  p k x
    | _ => 0 end.

Definition f1 (n : nat) (h : forall z : nat, z < n -> nat) :=
    (psum (extension h) n).+1.

Definition f2 := Fix lt_wf _ f1.


Lemma f_eqn x: f2 x =  f1 (n:=x) (fun y _ => f2 y).
Proof.
move: x; apply: (Fix_eq lt_wf) => n A B Hp; apply: psum_exten.
move => k _; rewrite /extension;case: (lt_dec k n) => // a; apply: Hp.
Qed.

Definition f (x:nat): nat := f2 x.

Lemma f_correct: f_spec f. 
Proof.
move => n; rewrite /f f_eqn /f1; apply: psum_exten => k kn.
by rewrite /extension; case: (lt_dec k n) => //; rewrite kn.
Qed.

End Wfsum.

(** ** Example 3 *)

(** We consider here only even numbers, show that comparison is WF, define a
 function by transfinite induction and show it is correct. *)

Module Wf_ex3.

Definition lte n m := [&& ~~ odd n, ~~ odd m & n < m]. 


Lemma lte_wf: well_founded lte.
Proof.
suff: forall n, Acc lte n /\ Acc lte n.+1.
  by move => h n; move: (h n) => [].
elim.
  by split; split => y; rewrite /lte /= ? ltn0 andbF.
move => n [sa sb]; split; first by exact.
split => y; rewrite /lte /=; move => /and3P[oy on].
rewrite  ltnS leq_eqVlt; case /orP; first by move => /eqP ->.
rewrite  ltnS leq_eqVlt; case /orP; first by move => /eqP ->.
by move => yn; case sa; apply; rewrite /lte /= oy yn (negbNE on).
Qed.

Definition f_spec f n := 
   if n is m.+4 then  (f (f (m.+2)).*2.+2 ).+1 else 0.

Lemma f_spec_simp f n: ~~ odd n -> (forall n, ~~odd n -> f n = f_spec f n) 
   -> f n = (n.-1)./2.
Proof.
move => on h1.
have h2: forall n, f (n.*2) = f_spec f (n.*2).
  by move => h; apply: h1; rewrite odd_double.
move: (odd_double_half n); rewrite (negbTE on) add0n => <-.
set m := (n./2).
move: m; case; first by rewrite h2.
elim; first by  rewrite h2 /=.
move => k hk.
rewrite h2 /f_spec doubleS doubleS - (doubleS k) hk.
by rewrite doubleS /= uphalf_double - (doubleS k) hk doubleS /= uphalf_double.
Qed.
    
Lemma f_spec_simp1 f n: (forall n, ~~odd n -> f n = f_spec f n) 
   -> f (n.*2.+2) = n.
Proof. by move => h; rewrite  f_spec_simp //= ?uphalf_double // odd_double. Qed.


Lemma f_spec_simp2 f n: (forall n,  f n = f_spec f n) ->  f(n.*2.+3) = n.
Proof. 
move => h.
have hh: forall n, f (n.*2.+2) = n.
   move => m; apply: f_spec_simp1 => k _; apply: h.
by elim: n; [ by rewrite h | move => n Hr; rewrite h /= Hr hh].
Qed.

Lemma f0a y n: odd n = false ->  odd n.+2 \/ y <= (n.+2)./2.-1 -> 
   y <= n./2 /\ lte (y.*2).+2 n.+4.
Proof.
rewrite /lte /=; move =>h; rewrite h /= odd_double; case => // eq.
split => //=. 
move: eq. rewrite - ltnS - ltn_double ltnS ltnS.
rewrite - {2} (odd_double_half n) h add0n //.
Qed.

Lemma f0b a b: odd a.*2.+2 \/ b <= (a.*2.+2)./2.-1 -> b <= a.
Proof. by rewrite /= odd_double doubleK; case. Qed.

Lemma f0c n:  odd n = false -> lte n.+2 n.+4. 
Proof. by move => h; rewrite /lte ltnS ltnS ltnS leqnSn /= h. Qed.

Lemma odd_dec n : {odd n} + {odd n = false}. 
Proof. by case h: (odd n); [ left | right ]. Qed.


Definition f1 :
  forall x, (forall z, lte z x -> {y:nat | odd z \/ y <= (z./2).-1}) ->
  {y:nat | odd x \/ y <= (x./2).-1}.
Proof.
case; first by exists 0; right.
case; first by exists 0; left.
case; first by exists 0; right.
case; first by exists 0; left.
move => n  Hr.
case (odd_dec n) => on; first by exists 0; left; rewrite /= on.
move: (Hr _ (f0c on)) => [y1 h1].
move: (f0a on h1) => [sa sb].
move: (Hr _ sb) => [y2 h2].
exists y2.+1; right;  apply: (leq_trans (f0b h2) sa).
Defined.


Definition f2 := Fix lte_wf _ f1.
Definition f (x:nat): nat := sval (f2 x).

Lemma f_eqn x: f2 x =  f1  (fun y _ => f2 y).
Proof.
move: x; apply: (Fix_eq lte_wf).
case => //; case => //; case => //; case => //.
move => n p p' Hp; rewrite /f1; case: (odd_dec n) => // on.
rewrite Hp; case: (p' n.+2 (f0c on)) => y Hy /=. 
by case: (f0a on Hy) => a b; rewrite Hp.
Qed.

Lemma f_correct n: ~~odd n ->  f n = f_spec f n. 
Proof.
case: n;first by rewrite  /f /= f_eqn.
case => //; case; first by rewrite  /f /= f_eqn.
case => // n; rewrite /f_spec /f f_eqn /f1 /=. 
case: (odd_dec n) => a b.
 by  move: (negbNE (negbNE b)); move /negP; case.
by case:(f2 n.+2) => x p /=;case: (f0a a p) => y q; case:(f2 x.*2.+2).
Qed.


End Wf_ex3.


(** ** More on accessiblity *)

(** We show that there is no striclty decreasing function with domain [nat] *)
Section Sequences.

Variable A : Set.
Variable R : A -> A -> Prop. 

Lemma acc_rec a b: R a b -> Acc R b -> Acc R a.
Proof.  by move => rab arb;move: a rab; case: arb. Qed.

Hypothesis W : well_founded R.

Theorem not_decreasing :
  ~ (exists f : nat -> A, (forall i:nat, R (f i.+1) (f i))).
Proof. 
case => f dec.
pose p a := Acc R a -> ~ exists i, a = f i.
have H: forall a, p a.
  move => a; apply: (well_founded_ind W p) => x Hx ax [i egi].
  move: (dec i); rewrite - egi => H1; move: (Hx _ H1 (acc_rec H1 ax)).
  by case; exists (i.+1).
move: (H _ (W (f 0))); case; by exists 0.
Qed.

End Sequences.

(** We show here an induction principle;  we could use it for ordinals in NF 
form.  *)

(* begin snippet restrictedRecursion:: no-out *)
Section restricted_recursion.

Variables (A:Type)(P:A->Prop)(R:A->A->Prop).

Definition restrict a b := [/\ P a,  R a b & P b].

Definition well_founded_P := forall a, P a -> Acc restrict a.
(* end snippet restrictedRecursion *)

(* begin snippet restrictedRecursiona:: no-out *)
Lemma P_well_founded_induction_type :
       well_founded_P  ->
       forall Q : A -> Type,
       (forall x : A, P x -> (forall y : A, P y -> R y x -> Q y) -> Q x) ->
       forall a : A, P a -> Q a.
(*| .. coq:: none |*)
Proof.
move => W Q Ha a.
have wfr: well_founded restrict by move => b; split => y [ra _ _]; apply: W.
apply: (well_founded_induction_type wfr (fun x => P x -> Q x)).
by move => x Hb px; apply: Ha => // y py ry; apply: Hb. 
Qed.
(*||*)
End restricted_recursion.
(* end snippet restrictedRecursiona *)
Module CantorOrdinal.


(** * The type T1 *)

(** This type represents all ordinals less that $\epsilon_0$ 
  #&epsilon; <sub>0</sub> #,
 via the 
Cantor Normal Form. More exactly [cons a n b] represents 
 $\omega^ A * (n.+1) + B$ #&omega; <sup> A</sup> * (n.+1) + B#
 if [a] represents A and  [b] represents B. *)

Inductive T1 : Set :=
  zero : T1
| cons : T1 -> nat -> T1 -> T1.



(** ** Equality *)

(** we define a boolean equality, the use the mechanism of canonical
 structures provided by ssreflect *)


Fixpoint T1eq x y {struct x} :=
  match x, y with 
  | zero, zero  => true
  | cons a n b, cons a' n' b' => [&& T1eq a a', n== n' & T1eq b b' ] 
  | _, _ => false
end.

Lemma T1eqP : Equality.axiom T1eq.
Proof.
move=> n m; apply: (iffP idP) => [|<-].
  elim: n m; first by case  => [ // | a n b //].
  move => a H1 n b H2 [] // a' n' b' /= /andP [/H1 -> /andP []].
  by move => /eqP -> /H2 ->.
by elim: n => // t ct n a caa /=;rewrite ct caa eqxx.
Qed.


Canonical T1_eqMixin := EqMixin T1eqP.
Canonical T1_eqType := Eval hnf in EqType T1 T1_eqMixin.

Arguments T1eqP {x y}.
Prenex Implicits T1eqP.


Lemma T1eqE a n b a' n' b':
  (cons a n b == cons a' n' b') = [&& a == a', n== n' &  b == b' ].
Proof. by []. Qed.


Declare Scope cantor_scope.
Delimit Scope cantor_scope with ca.
Open Scope cantor_scope.

(** Some definitions
  - $\phi_0(x)$ #&phi;<sub>0</sub>(x)# is [ cons x 0 zero ], 
    it represents $\omega ^x$  #&omega; <sup>x</sup>#
  - one is $\phi_0(0)$  #&phi;<sub>0</sub>(0)#
  - omega is $\phi_0(1)$  #&phi;<sub>0</sub>(1)#
  - bad is an example of an ordinal not in normal form
  - [ fun n := \F n] is the canonical injection of [nat] into [T1]
  - the log of [cons a n b] is [a]
  - an ordinal is AP if it is in the image of $\phi_0$ #&phi;<sub>0</sub>#.
*)


Definition phi0 a := cons a 0 zero.
Definition one := cons zero 0 zero.
Definition T1omega := phi0 (phi0 zero).
Definition T1bad := cons zero 0 T1omega.
Definition T1nat (n:nat) : T1 :=
  if n is p.+1 then cons zero p zero else zero.
Definition T1log a := if a is cons a _ _ then a else zero.
Definition T1ap x := if x is cons a n b then ((n==0) && (b==zero)) else false.

Notation "\F n" := (T1nat n)(at level 29) : cantor_scope.


Lemma T1F_inj: injective T1nat.
Proof. 
case; first by case => //; discriminate.
move => n; case; [discriminate | by move => m; case => ->].
Qed.

Lemma T1phi0_zero : phi0 zero = \F 1.      Proof. by []. Qed.
Lemma T1phi0_zero' : phi0 zero = one.      Proof. by []. Qed.
Lemma T1log_phi0 x : T1log (phi0 x) = x.   Proof. by []. Qed.
Lemma T1ap_phi0 x: T1ap (phi0 x).          Proof. by []. Qed.

(** **  Order on T1 *)

(** We give here a recursion definition of comparison.
Essentially, $\phi_0$ #&phi;<sub>0</sub>(x)# is strictly increasing, 
*)


Fixpoint T1lt x y {struct x} :=
  if x is cons a n b then
    if y is cons a' n' b' then 
      if a < a' then true 
      else if  a == a' then 
         if (n < n')%N then true 
         else if (n == n')  then b < b' else false
         else false 
      else false 
  else if y is cons a' n' b' then true else false
where  "x < y" := (T1lt x y) : cantor_scope.

Definition T1le (x y :T1) := (x == y) || (x < y).
Notation "x <= y" := (T1le x y) : cantor_scope.
Notation "x >= y" := (y <= x) (only parsing) : cantor_scope.
Notation "x > y"  := (y < x) (only parsing)  : cantor_scope.

Lemma T1lenn x: x <= x.   
Proof. by rewrite /T1le eqxx. Qed.

#[local] Hint Resolve T1lenn : core.

Lemma T1ltnn x: (x < x) = false.
Proof. by elim:x => //= a -> n b ->; rewrite ltnn ! if_same. Qed.

Lemma T1lt_ne a b : a < b -> (a == b) = false.
Proof. by case h: (a== b) => //; rewrite (eqP h) T1ltnn. Qed.

Lemma T1lt_ne' a b : a < b -> (b == a) = false.
Proof. rewrite eq_sym; apply /T1lt_ne. Qed.

Lemma T1ltW a b : (a < b) -> (a <= b). 
Proof. by rewrite /T1le => ->; rewrite orbT. Qed.

Lemma T1le_eqVlt a b : (a <= b) = (a == b) || (a < b).
Proof. by []. Qed.

Lemma T1lt_neAle a b : (a < b) = (a != b) && (a <= b).
Proof.  
by rewrite T1le_eqVlt; case h: (a < b);[ rewrite (T1lt_ne h) | case(a==b) ].
Qed.

Lemma T1ltn0 x: (x < zero) = false.         Proof. by case: x. Qed.
Lemma T1le0n x: zero <= x.                  Proof. by case: x. Qed.
Lemma T1len0 x: (x <= zero) = (x == zero).  Proof. by case: x. Qed.
Lemma T1lt0n x: (zero < x) = (x != zero).   Proof. by case: x. Qed.

Lemma T1ge1 x:  (one <= x) = (x != zero).
Proof. by case: x  => // [] // [] // [] // []. Qed.

Lemma T1lt1 x: (x < one) = (x==zero).
Proof.  by case: x  => // [] // [] // [] // []. Qed.

Lemma T1nat_inc n p : (n < p)%N = (\F n < \F p).
Proof.
case: p => //; first by rewrite T1ltn0 ltn0.
by case: n => // n p //=; rewrite ltnS if_same if_simpl. 
Qed.

(** This is an alternative version of less-or-equal *)

Lemma T1le_consE  a n b a' n' b':
 (cons a n b <= cons a' n' b') =
    if a < a' then true 
      else if  a == a' then 
         if (n < n')%N then true 
         else if (n == n')  then b <= b' else false
         else false. 
Proof.
rewrite /T1le T1eqE /=.
case pa: (a<a');first by rewrite orbT.
case pb: (a==a') => //; case pc: (n<n')%N;first by rewrite orbT.
by case pd: (n==n'). 
Qed.

(** We have exactly one of: [a] is less than, greater than, or equal to [b] *)

Lemma T1lt_trichotomy a b: [|| (a< b), (a==b) | (b < a)].
Proof.
elim: a b; first by case; [rewrite eqxx // | move => a n b].
move => a Ha n b Hb [] // a' n' b' /=.
case /or3P: (Ha a'); [by move => -> | | by move => ->; rewrite !orbT ].
move => h; rewrite h (eqP h) T1ltnn eqxx.
case : (ltngtP n n'); [done | by rewrite !orbT | move => -> ]. 
by rewrite T1eqE  !eqxx /= Hb.
Qed.

Lemma T1lt_anti b a: a < b -> (b < a) = false.
Proof.
elim: a b; first by move => b; rewrite T1ltn0.
move => a Ha n b Hb [] // a' n' b' /=.
case pa: (a < a'). 
  rewrite (Ha _ pa); case aa: (a' == a) => // _.
  by move: pa; rewrite (eqP aa) T1ltnn.
case aa: (a== a') => //.
rewrite (eqP aa) eqxx T1ltnn; rewrite (eq_sym n'); case: (ltngtP n n') => //.
by move => _; apply:Hb.
Qed.

Lemma T1leNgt a b:  (a <= b) = ~~ (b < a).
Proof.
case /or3P: (T1lt_trichotomy a b).
- by move => h; rewrite (T1lt_anti h) (T1ltW h).
- by move /eqP ->; rewrite T1ltnn T1lenn.
- by move => h; rewrite h /T1le (T1lt_anti h) (T1lt_ne' h).
Qed.

Lemma T1ltNge a b:  (a < b) = ~~ (b <= a).
Proof. by rewrite T1leNgt negbK. Qed.

Lemma T1eq_le m n : (m == n) = ((m <= n) && (n <= m)).
Proof.
rewrite /T1le (eq_sym n m);case eqmn: (m == n) => //=.
by case lt1: (m < n) => //; rewrite (T1lt_anti lt1).
Qed.

Lemma T1le_total m n : (m <= n) || (n <= m).
Proof. 
by rewrite /T1le;case /or3P: (T1lt_trichotomy m n) => -> //; rewrite !orbT.
Qed.

(** The next three definitions are similar to to those defined in ssrnat.
we shall use [T1ltgtP] a lot.
*)

CoInductive T1ltn_xor_geq m n : bool -> bool -> Set :=
  | T1LtnNotGeq of m < n  : T1ltn_xor_geq m n false true
  | T1GeqNotLtn of n <= m : T1ltn_xor_geq m n true false.

CoInductive T1leq_xor_gtn m n : bool -> bool -> Set :=
  | T1GeqNotGtn of m <= n : T1leq_xor_gtn m n true false
  | T1GtnNotLeq of n < m  : T1leq_xor_gtn m n false true.


CoInductive compare_T1 m n : bool -> bool -> bool -> Set :=
  | CompareT1Lt of m < n : compare_T1 m n true false false
  | CompareT1Gt of m > n : compare_T1 m n false true false
  | CompareT1Eq of m = n : compare_T1 m n false false true.


Lemma T1leP x y : T1leq_xor_gtn x y (x <= y) (y < x).
Proof.
by rewrite T1ltNge; case le_xy: (x <= y); constructor;rewrite // T1ltNge le_xy.
Qed.

Lemma T1ltP m n : T1ltn_xor_geq m n (n <= m) (m < n).
Proof. by case T1leP; constructor. Qed.

Lemma T1ltgtP m n : compare_T1 m n (m < n) (n < m) (m == n).
Proof.
rewrite T1lt_neAle T1eq_le;case: T1ltP; first by constructor.
by rewrite T1le_eqVlt orbC; case: T1leP; constructor; first exact /eqP.
Qed.

(** We show here transitivity of comparison, using [T1ltgtP ].  *)

Lemma T1lt_trans b a c: a < b -> b < c -> a < c.
Proof.
elim: c a b => [a [] // | a'' Ha n'' c'' Hc a [] ]; rewrite ? T1ltn0 //.
move => a' n' b'; case: a => // a n b /=.
case: (T1ltgtP a a') => h1 //.
  case: (T1ltgtP a' a'') => h2 //; first by rewrite (Ha _ _ h1 h2).
  by rewrite - h2 h1.
rewrite h1; case: (T1ltgtP a' a'') => // _; case: (ltngtP n n')%N => // h2.
  case: (ltngtP n' n'') => h3 //; first by rewrite (ltn_trans h2 h3).
  by rewrite - h3 h2.
by rewrite h2; case: (ltngtP n' n'') => h3 //; apply: Hc.
Qed.


Lemma T1lt_le_trans b a c: a < b -> b <= c -> a < c.
Proof.
by move => lab; case /orP;[ move /eqP => <- | apply:T1lt_trans].
Qed.

Lemma T1le_lt_trans b a c: a <= b -> b < c -> a < c.
Proof. by case /orP;[  move /eqP => <- |apply:T1lt_trans]. Qed.

Lemma T1le_trans b a c: a <= b -> b <= c -> a <= c.
Proof.
case /orP; first by move /eqP => ->. 
by move => l1 l2; rewrite /T1le (T1lt_le_trans l1 l2) orbT.
Qed.

(** The following lemma implies 
#x &lt; &omega; <sup> x</sup>#$x <\omega ^x$,  so all ordinals are less than 
$\epsilon_0$ #&epsilon; <sub>0</sub> # *)

Lemma head_lt_cons a n b: a < cons a n b.
Proof. by elim : a n b  => // a Ha n b _ n' b' /=; rewrite (Ha n b). Qed.

Lemma T1lt_cons_le a n b a' n' b': (cons a n b < cons a' n' b') -> (a <= a').
Proof. by rewrite /T1le /=; case (T1ltgtP a a'). Qed.

Lemma T1le_cons_le a n b a' n' b': (cons a n b <= cons a' n' b') -> (a <= a').
Proof.
case /orP; [ by case /eqP => -> | apply:T1lt_cons_le ].
Qed.

Lemma phi0_lt a b: (phi0 a < phi0 b) = (a < b).
Proof. by rewrite /phi0 /= if_same if_simpl.  Qed.

Lemma phi0_le a b:  (phi0 a <= phi0 b) = (a <= b).
Proof. by rewrite /T1le phi0_lt /phi0 T1eqE eqxx andbT. Qed.

Lemma phi0_lt1 a n b a': (cons a n b < phi0 a') = (a < a'). 
Proof. by rewrite /phi0/= T1ltn0 !if_same if_simpl. Qed.


(** ** Normal form *)

(** There exists a strictly infinite  decreasing sequence of ordinals, 
so the order is not well founded *)

Theorem lt_not_wf : ~ (well_founded T1lt).
Proof. 
set f := (fix f i := if i is n.+1 then  cons zero  0 (f n) else T1omega).
by case/not_decreasing; exists f; elim. 
Qed.

(** We say that [cons a n b] is NF if 
$b<\phi_0(a$)#b &lt;&phi;<sub>0</sub>(a)#.
If [b] is [cons a' n' b'], this says that [b] is less than [b']. 
If [a] is zero,  this says that [b=0].
*)

Fixpoint T1nf x :=
  if x is cons a _ b then [&& T1nf a, T1nf b & b < phi0 a ]
  else true.

Lemma T1nf_cons0 a n: T1nf a -> T1nf (cons a n zero).
Proof. by rewrite /= andbT. Qed.

Lemma T1nf_cons_cons a n a' n' b' : T1nf (cons a n (cons a' n' b')) -> a' < a.
Proof. by rewrite /= T1ltn0 !if_same if_simpl => /and3P [_ _]. Qed.

Lemma T1nf_consa a n b: T1nf (cons a n b) -> T1nf a.
Proof. by move /and3P => []. Qed.

Lemma T1nf_consb a n b: T1nf (cons a n b) -> T1nf b.
Proof. by move /and3P => []. Qed.

Lemma T1nf_finite1 n b: T1nf (cons zero n b) = (b == zero).
Proof. by case: b => // a n' b /=; rewrite !T1ltn0 !if_same andbF. Qed.

Lemma T1nf_finite n b: T1nf (cons zero n b) -> (b = zero).
Proof. by rewrite T1nf_finite1 => /eqP. Qed.

Lemma T1nfCE: ~~(T1nf T1bad).  Proof. by  []. Qed.

(** We show here that the restriction of [T1lt] to NF ordinals is well-founded,
  then prove two induction principles. Note that [nf_Wf'] says every 
 NF [x] is accessible by the relation: [u<v], [u] and [v] NF.
 If [x] is not NF it is trivially accessible. The proof is a bit tricky *)

(* begin snippet nfWfProofa:: no-out *)
Lemma nf_Wf : well_founded (restrict T1nf T1lt).
Proof. 
have az: Acc (restrict T1nf T1lt) zero by split => y [_]; rewrite T1ltn0.
elim;[ exact az | move => a Ha n b _].
pose (LT:= (restrict (fun x : T1 => T1nf x) (fun x y : T1 => x < y))). 
fold LT in az , Ha  |- . (* .goals *)
(* end snippet nfWfProofa *)

(* begin snippet nfWfProofb:: no-out  *)
elim:{a} Ha n b => a Ha Hb n b.
(* end snippet nfWfProofb *)

(* begin snippet nfWfProofc:: no-in  unfold *)
fold LT in Hb   |- *.
(* end snippet nfWfProofc *)

case nx: (T1nf (cons a n b)); last by split => y [_ _]; rewrite nx.
move/and3P: (nx);rewrite -/T1nf; move => [na nb lba].
have aca: Acc (restrict T1nf T1lt) a by split.
have Hc: forall b, Acc (restrict T1nf T1lt) b ->
  T1nf (cons a 0 b)-> Acc (restrict T1nf T1lt) (cons a 0 b).
  move => c; elim => {} c qa qb qc; split; case; first by move => _; apply: az.
  move => a'' n'' b'' [] sa /= ua /and3P [_ nc _];move/and3P:(sa) => [ra rb _].
  move: ua;case: (T1ltgtP a'' a) => ua ub.
  - by apply: Hb.
  - by case ub.
  - by move: ub sa; case ee:(n''==0); [rewrite ua (eqP ee) => ub; apply: qb | ].
have Hd: forall b, T1nf b -> b < phi0 a -> Acc (restrict T1nf T1lt)  b.
  case; [by move => _ _ ; apply: az | move => a' n' b' nx'].
  rewrite phi0_lt1 => aa'.
  (* begin snippet nfWfProofd:: no-in unfold -.g#* .g#1 -.h#* .h#Ha .h#Ha .h#Hb  .h#aa'   *)
 fold LT in aca, Hc |- *.
  (* end snippet nfWfProofd *)
  
  by apply: Hb; unfold LT; rewrite /restrict  (T1nf_consa nx') na aa'. 
elim: n b {nb lba} (Hd _ nb lba) nx => [ // | n He b]; elim.
move => c _ qb np; split; case; first by move => _; apply: az.
move => a'' n'' b'' [sa /= sb _];move /and3P: (sa) =>  [ra rb rc].
move: sb; case: (T1ltgtP a'' a) => sc sb; [ by apply: Hb | by case sb |].
move: sb; case: (ltngtP n'' n.+1); [rewrite ltnS leq_eqVlt | done | move ->].
  rewrite sc in rc; move => sb _; move: sa; case /orP: sb.
    move => /eqP ->; rewrite sc; apply: (He b'' (Hd _ rb rc)).
  move => qd qe.
  have nc0: T1nf (cons a n zero) by rewrite /= andbT. 
  apply: (acc_rec (And3 qe _ nc0) (He _ az nc0)). 
  by rewrite /= qd sc eqxx T1ltnn. 
move => sb; move/and3P: np => [pa pb pc].
rewrite sc;apply: (qb _ (And3 rb sb pb)); rewrite -sc //.
Qed.

Lemma nf_Wf' : well_founded_P T1nf T1lt.
Proof. move => x /= nx; apply: nf_Wf. Qed.


Lemma T1transfinite_induction P:
  (forall x, T1nf x -> (forall y, T1nf y ->  y < x -> P y) -> P x) ->
  forall a, T1nf a -> P a.
Proof.
move => H; exact: (P_well_founded_induction_type nf_Wf' H).
Qed.

Lemma T1transfinite_induction_Q (P: T1 -> Type) (Q: T1 -> Prop):
  (forall x:T1, Q x -> T1nf x ->
                (forall y:T1, Q y -> T1nf y ->  y < x -> P y) -> P x) ->
  forall a, T1nf a -> Q a -> P a.
Proof.
pose q a:=  T1nf a /\ Q a; pose lt x y :=  x < y.
move => H a pa pb; move: {pa pb} a (conj pa pb).
have wf1: well_founded_P q lt.
  move => a qa; elim: (nf_Wf' (proj1 qa)). 
  by move => b _ h2; split => c [ [na _] la [nb _]]; apply: h2. 
have H': forall x, q x -> (forall y, q y -> lt y x -> P y) -> P x.
  by move => x [pa pb] ha; apply: H => // y ya yb; apply: ha.
exact: (P_well_founded_induction_type wf1 H').
Qed.


Lemma T1nf_rect (P : T1 -> Type):
   P zero ->
   (forall n: nat,  P (cons zero n zero)) ->
   (forall a n b n' b', T1nf (cons a n b) ->
                        P (cons a n b) ->
                        b' < phi0 (cons a n b) ->
                        T1nf b' ->
                        P b' ->
                        P (cons (cons a n b) n' b')) ->
   forall a, T1nf a -> P a.
Proof.
move =>H0 Hfinite Hcons; elim => // a IH1 n t IH2;case: a IH1.
  by rewrite  T1nf_finite1; move => _ /eqP ->.
move => a' n' c pa =>/and3P [pc pd pe]; auto.
Qed.

(** ** Successor *)

(** We say that [cons a n b] is
    - limit if [a] is non-zero, [b] is limit or zero
    - finite if [a] is zero
    - a successor if [a] is zero or [b] is a successor
   and define its 
    - successor as [\F (n+2)] or [cons a n (succ b)]
    - predecessor as [\F n] or [cons a n (pred b)]
    - split [u,v] as [cons a n x, y] if [b] split as [x,y] and [a] is non-zero;
      and as [0,n+1] if [a] is zero
Note that if [a=0], the quantity [b] is ignored; but when [x] is NF, 
then [b] is zero. *)

Fixpoint T1limit x := 
  if x is cons a n b then 
    if a==zero then false else (b== zero) || T1limit b 
  else false.

Definition T1finite x := if x is cons a n b then a == zero else true.

Fixpoint T1is_succ x := 
  if x is cons a n b then  (a==zero) || T1is_succ b  else false.

Fixpoint T1succ (c:T1) : T1 :=
  if c is cons a n b 
     then if a == zero then cons zero n.+1 zero else cons a n (T1succ b)
  else one.

Fixpoint T1pred (c:T1) : T1 :=
  if c is cons a n b then
     if (a==zero) then \F n else (cons a n (T1pred b)) 
  else zero.

Fixpoint T1split x:=
 if x is cons a n b then
      if a==zero then (zero, n.+1) else
     let: (x, y) := T1split b in (cons a n x,y)
   else (zero,0).

Lemma split_limit x: ((T1split x).2 == 0) = ((x==zero) || T1limit x). 
Proof.  
elim: x => // a _ n b Hb /=.
case pa: (a==zero) => //; rewrite - Hb; by case: (T1split b).
Qed.

Lemma split_is_succ x: ((T1split x).2 != 0) = (T1is_succ x).
Proof.  
elim: x => // a _ n b Hb /=.
case pa: (a==zero) => //; rewrite - Hb; by case: (T1split b).
Qed.

Lemma split_finite x: ((T1split x).1 == zero) = T1finite x.
Proof.
by case: x => // a n b /=; case pa: (a==zero) => //; case: (T1split b).
Qed.

Lemma split_succ x: let:(y,n):= T1split x in T1split (T1succ x) = (y,n.+1).
Proof.  
elim: x => // a _ n b /=.
by case pa: (a==zero) => //=; rewrite pa /=; case: (T1split b) => u v ->.
Qed.


Lemma split_pred x: let:(y,n):= T1split x in T1split (T1pred x) = (y,n.-1).
Proof.  
elim: x => // a _ n b /=.
case pa: (a==zero) => //=; first by case: n.
by rewrite pa /=; case:(T1split b) => // u v ->.
Qed.


Lemma split_le x :  (T1split x).1 <= x.
Proof.
elim: x => // a _ n b Hb /=.
case pa: (a==zero) => //; move: Hb; case: (T1split b) => y m /=.
by rewrite T1le_consE !eqxx /= => ->; rewrite !if_same.
Qed.

Lemma nf_split x : T1nf x -> T1nf (T1split x).1.
Proof.
elim: x => // a _ n b Hb /=.
case pa: (a==zero) => // /and3P [sa /Hb sb sc] /=.
move: (T1le_lt_trans (split_le b) sc).
by move: sb; case (T1split b) => y m /= -> ->; rewrite sa.
Qed.

Lemma T1finite1 n: T1finite (\F n).  
Proof. by case:n. Qed.

Lemma T1finite2 x: T1finite x -> T1nf x -> x = \F ((T1split x).2).
Proof. by case: x => // a n b /eqP -> /T1nf_finite ->. Qed.

Lemma T1finite2CE: T1finite T1bad /\ forall n, T1bad <> \F n.
Proof. by split => //; case. Qed.

Lemma T1finite_succ x: T1finite x -> T1finite (T1succ x).
Proof. elim: x => // a Ha n b Hb; move /eqP => -> //. Qed.

Lemma T1succ_nat n: T1succ (\F n) = \F (n.+1).
Proof. by case: n. Qed.

Lemma nf_omega : T1nf T1omega.             Proof. by []. Qed. 
Lemma nf_finite n: T1nf (\F n).            Proof. by case: n. Qed.
Lemma nf_phi0 a: T1nf (phi0 a) = T1nf a.   Proof. by rewrite /= andbT. Qed.
Lemma nf_log a: T1nf a -> T1nf (T1log a). 
Proof. by case: a => // a n b /T1nf_consa. Qed.

(** An ordinal is zero, limit or a successor, exclusively. When we split [x]
the first component is zero or limit, the second is a natural number  *)


Lemma limit_pr1 x: (x == zero) (+) (T1limit x (+) T1is_succ x).
Proof.
elim: x => //a _ n b Hb /=; case az: (a== zero) => //.
by case bz: (b == zero); [ rewrite (eqP bz) | move: Hb; rewrite bz].
Qed.

Lemma split_limit1 x (y:= (T1split x).1): (y == zero) || (T1limit y).
Proof.
rewrite /y;elim x => // a _ n b Hb /=.
by case pa: (a==zero) => //; move: Hb; case (T1split b) => u v /=; rewrite pa.
Qed.

(** If [x] is limit, if [y] is less than [x], so is the successor of [y] *)

Lemma limit_pr x y: T1limit x -> y < x -> T1succ y < x.
Proof.
elim: x y; [ by [] |move => a _ n b Hb y /= H1].
case: y; [ by move => _; move: H1; case: a |move => a' n' b' /=].
have aux: b' < b -> T1succ b' < b.
   case: (a==zero) H1 => // /orP []; first by move => /eqP ->; rewrite T1ltn0. 
   by apply: Hb.
case a'; first by rewrite /T1succ; move => _;move: H1; case: a. 
move => a'' n'' b''; case: a H1;  [ done | move => u v w _ ].
simpl; rewrite T1eqE;case: (a'' < u) => //; case: eqP => // _.
case:(n'' < v)%N => //; case e2: (n'' == v) => //; case: (b'' < w) => //.
by case: eqP => //= _; case: (n' <n)%N => //; case: eqP.
Qed.

Lemma pred_le a: T1pred a <= a.
Proof.
elim: a => // a _ n b Hb /=; case az: (a==zero).
  by rewrite (eqP az); case: n => // m /=; rewrite T1le_consE /= ltnS leqnn.
by rewrite T1le_consE /= Hb !eqxx !if_same.
Qed.
  
Lemma pred_lt a: T1is_succ a -> T1pred a < a.
Proof.
elim: a => // a _ n b Hb /=; case az: (a==zero).
  by rewrite (eqP az); case: n => // m /=; rewrite ltnS leqnn.
by move /Hb;rewrite /=T1ltnn ltnn !eqxx.
Qed.

Lemma succ_lt a: a < T1succ a.
Proof. 
elim: a => // a asa n b bb;move: asa; case: a; first by rewrite /= ltnSn.
by move => u v w h /=; rewrite bb ! eqxx !ltnn if_same.
Qed.

Lemma nf_succ a: T1nf a -> T1nf (T1succ a).
Proof.
elim:a => // a _ n b Hb /and3P [pa /Hb pb pc] /=.
case az: (a== zero) => //; apply /and3P;split => //.
by apply:limit_pr => //=; rewrite az.
Qed.

Lemma nf_pred a: T1nf a -> T1nf (T1pred a).
Proof.
elim:a => // a _ n b Hb /and3P [pa /Hb pb pc] /=.
case az: (a== zero) => //; first by apply: nf_finite.
by rewrite /= (T1le_lt_trans (pred_le b) pc) pb !andbT.
Qed.


Lemma succ_pred x: T1nf x -> T1is_succ x -> x = T1succ (T1pred x).
Proof.
elim: x => // a _ n b Hb; case az: (a==zero).
  by rewrite (eqP az) T1nf_finite1 => /eqP ->; case: n.
by move => /T1nf_consb /Hb h /=;rewrite /= az /= az => h'; rewrite - h.
Qed.

Lemma succ_predCE: T1is_succ T1bad /\ forall y, T1bad <> T1succ y.
Proof. by split => //; case => //; case. Qed.

Lemma succ_p1 x: T1is_succ (T1succ x).
Proof. 
by elim: x => // a _ n b Hb /=; case pa: (a==zero) => //=; rewrite pa.
Qed.

Lemma pred_succ x: T1nf x -> T1pred (T1succ x) = x.
Proof.
elim: x => // a _ n b Hb nx /=; case az: (a==zero).
  by move: nx; rewrite (eqP az) T1nf_finite1 => /eqP ->.
by rewrite /= az (Hb (T1nf_consb nx)).
Qed.

Lemma pred_succ_CE: T1pred (T1succ T1bad) <>  T1bad.
Proof. discriminate. Qed.

Lemma succ_inj x y: T1nf x -> T1nf y -> (T1succ x == T1succ y) = (x==y).
Proof.
move => nx ny;case h: (T1succ x == T1succ y).
  by rewrite - (pred_succ nx) (eqP h) (pred_succ ny) eqxx.
by case hh: (x==y) => //; rewrite -h (eqP hh) eqxx.
Qed.

Lemma succ_injCE: one  <> T1bad /\ (T1succ one = T1succ T1bad).
Proof. done. Qed.


Lemma lt_succ_succ x y: T1succ x < T1succ y -> x < y. 
Proof.
elim: x y; first by case; [ rewrite T1ltnn | move => a n b _ ].
move => a _ n b Hb; case; [ by case a | move => a' n' b']. 
case a;case a' => //; first  by rewrite /= ltnS if_same; case: (n < n')%N.
move => a'' n'' b'' a''' n''' b'''; rewrite /= T1eqE.
case (T1ltgtP a''' a'') => //;case (ltngtP n''' n'') => //.
case (T1ltgtP b''' b'') => //;case (ltngtP n n') => //= _ _ _ _; apply: Hb.
Qed.

Lemma le_succ_succ x y: x <= y -> T1succ x <= T1succ y.
Proof. rewrite !T1leNgt; apply: contra; exact:lt_succ_succ.  Qed.

Lemma lt_succ2CE: one < T1bad /\ T1bad < T1succ one.
Proof. done. Qed.

Lemma lt_succ_succE x y:  
  T1nf x -> T1nf y ->  (T1succ x < T1succ y) = (x < y).
Proof.
move => nx ny.
case (T1ltgtP (T1succ x) (T1succ y)).  
+ by move/lt_succ_succ => ->.
+ by move /lt_succ_succ => /T1lt_anti.
+ by move /eqP; rewrite   (succ_inj nx ny) => /eqP ->; rewrite T1ltnn.
Qed.

(** Some properties of comparison and successor *)


Lemma le_succ_succE x y: 
  T1nf x -> T1nf y -> (T1succ x <= T1succ y) = (x <= y).
Proof.
by move => na nb; rewrite /T1le (succ_inj na nb) (lt_succ_succE na nb).
Qed.

Lemma lt_succ_le_1 a b : T1succ a <= b ->  a < b.
Proof. apply: T1lt_le_trans (succ_lt a). Qed.

Lemma lt_succ_le_2 a b:  T1nf a -> a < T1succ b ->  a <= b.
Proof.
elim: a b; first by move => b;rewrite T1le0n.
move => a' _ n' b' Hb; case; first by rewrite /= ! T1ltn0 ! if_same.
case.
   case a' => // n b; move /T1nf_finite ->.
   rewrite /= if_same if_simpl ltnS T1le_consE T1le0n T1ltnn eqxx leq_eqVlt.
   case: (ltngtP n' n) => //.
move => a'' n'' b'' n b /T1nf_consb H; rewrite T1le_consE /=. 
case: (T1ltgtP a' (cons a'' n'' b'')) => //.
by case: (ltngtP n' n) => //= _ _;  apply: Hb.
Qed.

Lemma lt_succ_le_3 a b:  T1nf a -> (a < T1succ b) = (a <= b).
Proof.
move => na; case h:(a < T1succ b). 
  by rewrite (lt_succ_le_2 na  h).
rewrite - h; case: (T1ltP b a) => // ab; exact: (T1le_lt_trans ab (succ_lt b)).
Qed.

Lemma lt_succ_le_4 a b: T1nf b ->  (a < b) = (T1succ a <= b).
Proof.
move => nb.
case: (T1ltP a b).
  rewrite T1leNgt T1ltNge; case h: (b < T1succ a) => //. 
  by rewrite(lt_succ_le_2 nb h).
by move /le_succ_succ => /(T1lt_le_trans  (succ_lt b)); rewrite T1leNgt => ->.
Qed.


Lemma phi0_log a: a < phi0 (T1succ (T1log a)).
Proof. by case: a => // a n b /=; rewrite succ_lt. Qed.


Lemma tail_lt_cons a n b: b < phi0 a -> b < cons a n b.
Proof.
case b => // a' n' b' /=.
by case: (T1ltgtP a' a) => //; rewrite T1ltn0 if_same.
Qed.


(** ** Addition *)

(** The definition of addition and subtraction given here are straightforward
given our interpretation of [cons]*)

Fixpoint T1add x y :=
  if x is cons a n b then
    if y is cons a' n' b' then 
       if a < a' then  cons a' n' b'
       else if a' < a then (cons a n (b +  (cons a' n' b')))
       else  (cons a (n+n').+1 b')
    else x      
  else  y
where "a + b" := (T1add a b) : cantor_scope.


Fixpoint T1sub x y :=
 if x is cons a n b then
    if y is cons a' n' b' then 
      if  x < y then zero 
      else if a' < a then cons a n b 
      else if (n < n')%N then zero
      else if (a==zero) then
         if (n ==n') then zero else cons zero ((n-n').-1) zero
      else if (n == n') then b - b' else cons a (n-n').-1 b
    else x      
  else  zero
where  "x - y" := (T1sub x y):cantor_scope.

(** Easy properties *)

Lemma succ_is_add_one a: T1succ a = a + one.
Proof.
by elim:a => // a _ n b Hb /=; rewrite T1ltn0 addn0 Hb; case a. 
Qed.

Lemma add1Nfin a:  ~~ T1finite a  -> one + a = a.
Proof. by case a => // u v w /=; case u. Qed.

Lemma sub1Nfin a:  ~~ T1finite a  -> a - one  = a.
Proof. by case: a => // u v w /=; case:u. Qed.

Lemma sub1a x: x != zero -> T1nf x -> x = one + (x - one). 
Proof.
move => na nb;case fb:(T1finite x).
  move: na fb nb ; case: x => // a' n' b' /= _ /eqP ->.
  by rewrite T1lt1 => /and3P [_ _ /eqP ->]; case: n'.
rewrite sub1Nfin ?fb // add1Nfin // fb //.
Qed.

Lemma sub1b x: T1nf x -> x = (one + x) - one. 
Proof.
case:x => // a n b; case: a => //; rewrite T1nf_finite1 => /eqP -> //.
Qed.

Lemma sub_1aCE (a:=  cons zero 0 T1bad) : one + (a - one) != a.
Proof.  done.  Qed.

Lemma sub_1bCE (a:=  cons zero 0 T1bad) : (one + a - one) != a.
Proof. done.  Qed.

Lemma T1add0n : left_id zero T1add.    Proof. by []. Qed. 
Lemma T1addn0: right_id zero T1add.    Proof. by case. Qed.

Lemma T1subn0 x: x - zero = x.
Proof. by case: x.  Qed.

Lemma T1subnn x: x - x = zero.
Proof. 
by elim:x => // a _ n b Hb /=; rewrite !T1ltnn ltnn !eqxx Hb if_same.
Qed.

Lemma add_int n m : \F n + \F m = \F (n +m)%N.
Proof.
case: n m => // n; case; first by rewrite addn0 T1addn0.
by move => m /=; rewrite - addnS.
Qed.

Lemma sub_int n m : \F n - \F m = \F (n -m)%N.
Proof.
case: n m => // n [] // m /=. 
rewrite subSS /T1nat; case (ltngtP n m) => pa.
- by rewrite (eqP (ltnW pa)).
- by rewrite -(subnSK pa).
- by rewrite pa subnn.
Qed.

Lemma add_fin_omega n: \F n + T1omega = T1omega.
Proof. by case: n. Qed.

Lemma fooCE (x:= T1bad):
   ~~T1limit x  /\(forall u v, T1limit u -> x <> u + \F v.+1).
Proof. by split => // u v; case u => // a n b; case a. Qed.


Lemma split_add x: let: (y,n) :=T1split x in T1nf x ->
   (x == y + \F n) && ((y==zero) || T1limit y ).
Proof.
elim: x => //a _ n b Hb /=.
case pa: (a==zero).
  by rewrite (eqP pa) T1lt1 => /and3P [_ _ /eqP ->]; rewrite !eqxx.
move: Hb; case: (T1split b) => y s h /and3P [_ /h/andP [/eqP -> sb] _].
rewrite orFb /T1limit pa sb andbT; case: {h} s => //=; first by rewrite T1addn0.
by move => m; move: pa; case: a.
Qed.

Lemma add_to_cons a n b: 
  b < phi0 a -> cons a n zero + b = cons  a n b.
Proof.
by case: b => // u v w; rewrite phi0_lt1 /= => h; rewrite h (T1lt_anti h).
Qed.


Lemma addC_CE (a := one) (b := T1omega):
  [/\ T1nf a, T1nf b & a + b  <> b + a].
Proof. by split.  Qed.

(** We say that [x] is AP is the sum of two ordinals less than [x] is 
less than [x]. This conditionq holds if [x] has the form 
$\phi_0(a$)#&phi;<sub>0</sub>(a)#; the converse is true when [x] is non-zero.
We may also assume everything NF.
*)

Lemma ap_pr0 a (x := phi0 a) b c:
     b < x -> c < x -> b + c < x.
Proof.
case: b c; [by move => c |move => a1 n b].
case; [by move => H  _ | move => a' n' c'].
by rewrite ! (fun_if  (fun z =>  z < x))  !phi0_lt1 if_same; case: (a1 < a'). 
Qed.

Lemma ap_pr1 c: 
   (forall a b,  a < c -> b < c -> a + b < c)  ->
   (c== zero) || T1ap c.
Proof.
case: c => // a n b.
case: n b => [b H | n b H]; last first.
  have l2: (cons a n b) < (cons a n.+1 b) by rewrite /= eqxx ltnS leqnn if_same.
  move: (H _ _ l2 l2); rewrite /= !T1ltnn /= !T1ltnn eqxx if_same.
  by rewrite ltnS -{3}(add0n n) ltn_add2r.
case bz: (b == zero) => //.
have pa: cons a 0 zero < cons a 0 b by move: bz;rewrite /= !T1ltnn eqxx; case b.
by move: (H _ _ pa pa); rewrite /= T1ltnn /= T1ltnn if_same.
Qed.

Lemma ap_pr2 c: 
   T1nf c -> c <> zero ->
   (forall a b, T1nf a -> T1nf b ->  a < c -> b < c -> a + b < c)  ->
   T1ap c.
Proof.
case: c => // a n b nc _ Hr.
have {Hr} H: forall u, T1nf u -> u < cons a n b -> u + u < cons a n b.
  by move => u ua ub; apply: Hr.
case: n b H nc => [b H /T1nf_consa na | n b H nc].
  have nc: T1nf (cons a 0 zero) by rewrite /= andbT.
  move: (H _ nc); rewrite /= T1ltnn eqxx /= if_same T1ltnn.
 by case b => // u v w; apply.
have l2: (cons a n b) < (cons a n.+1 b) by rewrite /= T1ltnn eqxx ltnSn.
move: (H (cons a n b) nc l2). 
by rewrite /= T1ltnn /= !T1ltnn /= eqxx if_same ltnS -{3}(add0n n) ltn_add2r.
Qed.


Lemma ap_pr2CE (c := cons T1bad 1 zero):
   (forall a b, T1nf a -> T1nf b ->  a < c -> b < c -> a + b < c).
Proof.
move => a b na nb; rewrite /c.
move: na nb;case: a; first by rewrite T1add0n.
move => a' n' b' HA; case: b; first by rewrite T1addn0.
move => a'' n'' b'' HB.
have pa: (a' == T1bad) = false.
  by apply /negP => /eqP ba; move: HA; rewrite ba /=.
have pb: (a'' == T1bad) = false.
  by apply /negP => /eqP ba; move: HB; rewrite ba /=.
rewrite /= !(fun_if (fun z =>  z < cons T1bad 1 zero)) /= pa pb => sa sb.
by case (T1ltgtP a' a'').
Qed.



(** Alternate definition of an AP: if [a<x] then [a+x=x]. 
*)

Lemma add_simpl1 a n b n' b': a != zero ->
   cons a n b + cons zero n' b' =  cons  a n (b + cons zero n' b').
Proof. by case: a. Qed.

Lemma add_simpl2  n b a' n' b': a' != zero ->
   cons zero n b + cons a' n' b' = cons a' n' b'.
Proof. by case: a'. Qed.


Lemma ap_pr3 a b (x := phi0 a): b < x -> b + x = x.
Proof.
by rewrite /x /phi0; case: b => // a' n' b'; rewrite phi0_lt1 /= => ->.
Qed.

Lemma ap_pr4 x: (forall b, b < x -> b + x = x) -> (x == zero) || T1ap x.
Proof.
case: x => // a; case; [ case => // a' n' b' H | move => n b H].
  have: cons a 0 zero < cons a 0 (cons a' n' b') by rewrite /= T1ltnn eqxx.
  move /H;rewrite /= T1ltnn; discriminate.
have: cons a n zero < cons a n.+1 b  by rewrite /= T1ltnn eqxx ltnSn.
by move /H; rewrite /= T1ltnn - {3} (addn0 n); case => /eqP; rewrite eqn_add2l.
Qed.

(** It follows tthat the sum of two NF ordinals is NF *)

Lemma nf_add a b: T1nf a -> T1nf b -> T1nf (a + b).
Proof.
elim: a b => // a Ha n b Hb [] // a' n' b' ha hb /=.
case (T1ltgtP a a') => //;last by move => ->; move: hb.
rewrite -(phi0_lt1 _ n' b') => pb.
by move: ha => /= /and3P [-> sb sc]; rewrite (Hb _ sb hb) ap_pr0.
Qed.

(** Results anbout addition subtraction comparison *)

Lemma T1add_eq0 m n:  (m + n == zero) = (m == zero) && (n == zero).
Proof. 
case: m; [by rewrite T1add0n | move => a' n' b'; rewrite andFb].
by case: n => // a n b /=; case (T1ltgtP a a').
Qed.

Lemma add_le1 a b: a <= a + b.
Proof.
elim:a b; first by rewrite /T1le /=; case;[ rewrite eqxx | ].
move => a' _ n' b' Hb [] // a n b /=.
case: (T1ltgtP a' a) => h;rewrite T1le_consE ?h // ? ltnn T1ltnn !eqxx //=.
by rewrite ltnS leq_addr. 
Qed.

Lemma add_le2 a b: b <= a + b.
Proof.
case: a => // a' n' b'; case: b ; [done | move => a n b /=].
case: (T1ltgtP a' a) => // h;rewrite T1le_consE ?h // ltnS leq_addl /= eqxx.
by rewrite if_same.
Qed.

Lemma minus_lt a b: a < b -> a - b = zero.
Proof.
elim: a b => // a' _ n' b' Hb [] // a'' n'' b'' h.
by rewrite /T1sub h.
Qed.

Lemma minus_le a b: a <= b -> a - b = zero.
Proof.
rewrite T1le_eqVlt;case /orP; [move /eqP ->; apply: T1subnn| apply: minus_lt].
Qed.

Lemma T1sub0 a: a - zero = a.
Proof. by case: a => // a n b; case: a. Qed.

Lemma nf_sub a b: T1nf a -> T1nf b -> T1nf (a - b).
Proof.
elim: a b => // a' _ n' b' Hb []; [ by rewrite T1sub0 | move => a n b /= sa sb].
have sc: T1nf (b' - b).
  by move/and3P: sa => [_ nb _]; move/and3P: sb => [_ nb' _];  apply: Hb.
by rewrite 11!fun_if /= sa sc !if_same.
Qed.

Lemma sub_le1 a b : T1nf a -> (a - b) <= a. 
Proof.
elim: a b => [b // | a' _ n' b' Hb].
case; [by rewrite T1sub0 T1lenn | move => a n b /and3P [_ /Hb la lb] /=].
set u := if a' <a then _ else _; case: u => //.
case: (a < a') => //; case: (ltngtP n' n) => // nn.
  have hh: ((n' - n).-1 < n')%N.
    move: nn; by case: n' => // n' h; rewrite subSn // ltnS leq_subr.
  rewrite (fun_if (fun z => (z <= _))) !T1le_consE T1ltnn hh eqxx (eq_sym _ a').
  by case (T1ltgtP a' zero).
case :eqP => // _.
apply: (T1le_trans (la b));exact:(T1ltW (tail_lt_cons n' lb)).
Qed.


Lemma sub_pr a b: T1nf b -> (a + b) - a = b.
Proof.
elim: a b; first by move => b _; rewrite T1sub0. 
move => a' _ n' b' Hb; case; first by rewrite T1addn0 T1subnn.
move => a n b nb /=.
case (T1ltgtP a' a) => pa.
    by rewrite /= pa (T1lt_anti pa) (T1lt_ne' pa).
  have hh: a' == zero = false by move: pa; case a' => //; rewrite T1ltn0.
  by rewrite /= !T1ltnn ltnn !eqxx /= T1ltNge add_le1 hh /= Hb.
rewrite /= T1ltnn eqxx - addnS addKn  addnC eqn_simpl1 ltn_simpl1 pa.
by move: nb; case: eqP => // -> nb; rewrite (T1nf_finite nb).
Qed.

Lemma add_inj a b c : T1nf b -> T1nf c -> a + b = a + c -> b = c.
Proof.
move => sb sc h.
by rewrite - (sub_pr a sb) - (sub_pr a sc) h.
Qed.

Lemma sub_pr1 a b: T1nf b -> a <= b -> b = a + (b - a).
Proof.
move => nb; rewrite /T1le.
case: (altP (a =P b)) => [-> | _ /=]; first by rewrite T1subnn T1addn0.
move: nb; elim: a b; first by  move => b nb; rewrite T1sub0 //.
move => a' _ n' b' Hb; case; [by rewrite T1ltn0 | move => a n b].
case: a; [  move => hb hc | move => a'' n'' b''].
  move: hb hc => /=;rewrite T1lt1 => /andP [_ /eqP ->].
  case a'=> //; rewrite !T1ltn0 eqxx if_same if_simpl => le1.
  by rewrite (ltnNge) (ltnW le1) (gtn_eqF le1) /= - addSn - subnS (subnKC le1).
move => /and3P [_ sb sc]. 
move: (Hb _ sb) (T1le_lt_trans (sub_le1 b' sb) sc) => ha hb /=.
case (T1ltgtP  a' (cons a'' n'' b'')) => //.
   case a' => // a3 n3 b3 /=; rewrite T1eqE (eq_sym a'' a3) (eq_sym n'' n3).
   case (T1ltgtP a3 a'') => //= pa; first by rewrite pa.
   case (ltngtP n3 n'') => //= pb; first by rewrite pa T1ltnn eqxx pb.
   by move => h; rewrite (T1lt_anti h) (T1lt_ne' h) pa pb T1ltnn ltnn ! eqxx h.
move ->;rewrite !T1ltnn ltnn !eqxx (eq_sym n n');case (ltngtP  n' n) => //. 
  by rewrite T1ltnn => le1; rewrite - addSn - subnS (subnKC le1).
move => -> hw; rewrite (T1lt_anti hw); move: (ha hw) hb; clear hw.
case (b - b'); first by rewrite T1addn0  => ->.
by move => u v w; rewrite phi0_lt1 => <- ua; rewrite ua (T1lt_anti ua). 
Qed.


Lemma sub_pr1CE: (one <= T1bad) &&  (T1bad != one + (T1bad - one)). 
Proof. done. Qed.

Lemma sub_pr1r a b: T1nf a -> a - b = zero -> a <= b.
Proof.
move => nn h; case /orP: (T1le_total a b) => // h1.
by move: (sub_pr1 nn h1); rewrite h T1addn0 => ->. 
Qed.


Lemma omega_minus_one : T1omega - one = T1omega. 
Proof. by []. Qed.

Lemma sub_nz a b: T1nf b -> a < b -> (b - a) != zero.
Proof.
move => nb lab; apply/negP => h.
by move: (sub_pr1r nb (eqP h)); rewrite T1leNgt lab.
Qed.


Lemma sub_nzCE (a := one) (b := (cons zero 0 one)):
   (a < b) && (b-a == zero). 
Proof. done. Qed.


(** Associativity of addition *)

Lemma T1addA c1 c2 c3: c1 + (c2 + c3) = (c1 + c2) + c3.
Proof.
elim: c1 c2 c3 => // a1 _ n1 b1 H; case.
   by move => c3;rewrite !T1add0n T1addn0.
move => a2 n2 b2; case;[ by rewrite ! T1addn0 | move => a3 n3 b3 /=].
case (T1ltgtP a2 a3).
+ case (T1ltgtP a1 a2) => pa pb /=.
   - by rewrite (T1lt_trans pa pb) /= pb.
   - by case (T1ltgtP a1 a3) => //; rewrite - H /= pb.
   - by rewrite  pa pb.
+ case (T1ltgtP a1 a2) => pa pb /=; move: (T1lt_anti pb) => pc.
   - by rewrite pb pc.
   - by move:(T1lt_trans pb pa) => h; rewrite h (T1lt_anti h) - H /= pb pc.
   - by rewrite pa pb pc.
+ move => <-; case (T1ltgtP a1 a2) => pb /=.
   - by rewrite !T1ltnn. 
   - by rewrite pb (T1lt_anti pb) - H /=  !T1ltnn.
   - by rewrite pb !T1ltnn addSn addnS addnA.
Qed.

Lemma T1addS a b : (a + T1succ b) = T1succ (a+ b).
Proof. by rewrite ! succ_is_add_one T1addA. Qed.

Lemma T1le_add2l  p m n : (p + m <= p + n) = (m <= n).
Proof.
elim:p m n => // a  Ha n b Hb.
case; first by move => n1; rewrite T1addn0 T1le0n add_le1.
move => a' n' b'; case.
   rewrite T1addn0 /=; case (T1ltgtP a a').
     move => h; rewrite T1le_consE (T1lt_ne' h) (T1lt_anti h) => //.
   move: (Hb (cons a' n' b') zero).
   by rewrite T1le_consE T1addn0 T1ltnn ltnn ! eqxx => ->.
  by rewrite T1le_consE T1ltnn eqxx addnC ltn_simpl1 eqn_simpl1.
move => a'' n'' b'' /=.
case (T1ltgtP a a');case (T1ltgtP a a'') =>// pa pb; 
  rewrite ? pa -? pa  !T1le_consE ? (T1lt_anti pb) ? eqxx ? T1ltnn.
- move: (T1lt_trans pa pb) => pc.
  by rewrite (T1lt_ne' pb) (T1lt_ne' pc) (T1lt_anti pc).
- by rewrite (T1lt_ne' pb).
- by rewrite pa (T1lt_trans pb pa).
- by rewrite Hb ltnn T1le_consE. 
- by rewrite pb ltnS leq_addr.
- by rewrite -pb pa.
- by rewrite -pb addnC ltn_simpl1 eqn_simpl1 (T1lt_anti pa) (T1lt_ne' pa).
- by rewrite pb eqxx T1ltnn /= ltnS ltn_add2l - !addSn eqn_add2l. 
Qed.

Lemma T1lt_add2l  p m n : (p + m < p + n) = (m < n).
Proof. by rewrite !T1ltNge T1le_add2l. Qed.

Lemma T1lt_add2r  p m n : (m + p  < n + p ) ->  (m < n).
Proof.
elim: m p n. 
  by move => p n; rewrite T1add0n; case: n => //;rewrite T1add0n T1ltnn.
move => a Ha n b Hb; case; first by move => u; rewrite ! T1addn0.
move => a' n' b'; case.
  simpl;case (T1ltgtP a a') => pa /=.
  + by rewrite !T1ltnn ltnn !if_same.
  + by rewrite (T1lt_anti pa) (T1lt_ne' pa).
  + by rewrite pa T1ltnn eqxx ltn_simpl1 eqn_simpl1.
move => a'' n'' b'' /=.
case (T1ltgtP a a'); case (T1ltgtP a a'') => pa pb //.
- by rewrite (T1lt_trans pa pb) T1ltnn.
- by rewrite -pa pb T1ltnn.
- case (T1ltgtP a'' a') => pc /=; rewrite ? pc.
  + by rewrite (T1lt_anti pb) (T1lt_ne' pb).
  + by rewrite (T1lt_anti pa) (T1lt_ne' pa).
  + by rewrite (T1lt_anti pb) (T1lt_ne' pb).
- rewrite - pa pb (T1lt_anti pb) /= T1ltnn  eqxx. 
  by case (ltngtP n n'') => // _; apply: Hb.
- by rewrite - pb pa /= T1ltnn eqxx ltn_simpl1 eqn_simpl1.
- by rewrite -pa -pb /= !T1ltnn eqxx ltnS ltn_add2r if_same if_simpl=> ->.
Qed.

Lemma T1le_add2r  p m n : (m <=n) -> (m + p  <= n + p).
Proof. rewrite !T1leNgt; apply: contra; apply: T1lt_add2r.  Qed.

Lemma T1eq_add2l  p m n : (p + m == p + n) = (m == n).
Proof. by rewrite ! T1eq_le ! T1le_add2l. Qed.

Lemma add_le3 a b: a = a + b -> b = zero.
Proof. move /eqP;rewrite -{1} (T1addn0 a) T1eq_add2l => /eqP -> //. Qed.

Lemma add_le4 a b: b != zero -> a < a + b.
Proof.
move: (add_le1 a b); rewrite T1le_eqVlt.
by case: (a<a+b); rewrite ? orbT // orbF => /eqP /add_le3 ->.
Qed.


Lemma sub_pr1rCE (a := T1bad) (b := one) :  (a - b == zero) && (b < a).
Proof. done. Qed.


(** ** Limits *)

(** A limit ordinal is the supremum of a sequence of ordinals. We first show 
  that some sequences are unbounded. We then show that, if the sequence is 
  bounded, there is a least upper bound, more preciselly, if a property is 
  satisfied for some NF ordinal, it is satisfied for a least NF aordinal.
  This requires teh excluded middel principle.
 *)


Fixpoint omega_tower (n:nat) : T1 :=
  if n is p.+1 then phi0 (omega_tower p) else one.

Lemma omega_tower_nf n: T1nf (omega_tower n).
Proof. by elim: n ; [ | move => n H; rewrite /= andbT ]. Qed.

Lemma omega_tower_unbounded x: ~ (forall n, (omega_tower n) < x).
Proof.
elim :x; first by  move => h; move: (h 0); rewrite T1ltn0.
move => a Ha n b _ c; case Ha => m.
move: (c m.+2); move /T1lt_cons_le;apply: T1lt_le_trans;apply: head_lt_cons.
Qed.



Definition ex_middle:=
  forall (P: T1 -> Prop),  let Q :=  exists x, (T1nf x /\ P x) in  Q \/ ~Q. 

Lemma ex_middle_pick (P: T1 -> Prop):  ex_middle ->
     (exists x, (T1nf x /\ P x))  \/ (forall x, T1nf x -> ~ (P x)).
Proof.
move => h. 
by case (h P); [left |move => nq; right => x nx px; case nq; exists x ].
Qed.

Lemma min_exists (P: T1 -> Prop) x: ex_middle ->
   T1nf x -> (P x) -> 
   exists y, T1nf y /\ P y /\ forall z, T1nf z -> P z -> y <= z.
Proof.
move => EM;move: x; apply: T1transfinite_induction.
move => x nx H px.
case (ex_middle_pick (fun z => (P z /\ ~ (x <= z))) EM).
  move =>  [z [pa [pb pc]]]. 
  have zx: z < x by rewrite (T1ltNge z x); apply /negP.
  exact: (H _ pa zx pb).
move => qf.
exists x; split => //; split => // z pa pb; case xz: (x <= z) => //.
by case (qf _ pa); rewrite xz.
Qed.

(** *** Definition *)

(** We say that [x] is the limit of [f], or the supremum of the [f(i)] if 
[f(i)<x] (we could use less-or-equal here as [f] will be strictly increasing)
and if moreover, every ordinal less than [x] is bounded by some [f(i)].
Note that [x] is then the least upper bound. The trouble is that each [f(i)]  
may be NF and [x] is not. Thus , we give an  alternate definition. 
Trouble is: a function may have more then one limit (at most one of them 
being NF).
*)

Notation Tf := (nat -> T1).

Definition limit_v1 (f: Tf) x := 
    (forall n, f n < x) /\ (forall y, y < x -> (exists n, y <= f n)).
Definition limit_v2 (f: Tf) x := 
    (forall n, f n < x) /\ (forall y, T1nf y -> y < x -> (exists n, y <= f n)).
 

Lemma limit_unique1 (f: Tf) x x' :limit_v1 f x -> limit_v1 f x' ->
  x = x'.
Proof.
move => [pa pb] [pc pd]; case: (T1ltgtP x x') => //.
  by move /pd => [n]; rewrite T1leNgt (pa n).
by move /pb => [n]; rewrite T1leNgt (pc n).
Qed.


Lemma limit_unique2 (f: Tf) x x' : limit_v2 f x -> limit_v2 f x' ->
  T1nf x -> T1nf x'->  x = x'.
Proof.
move => [pa pb] [pc pd] nx nx'; case: (T1ltgtP x x') => //.
  by move /(pd _ nx) => [n]; rewrite T1leNgt (pa n).
by move /(pb _ nx') => [n]; rewrite T1leNgt (pc n).
Qed.


Definition omega_plus_n n := cons one 0 (cons zero n zero).

Lemma nf_omega_plus_n n : T1nf ( omega_plus_n n).
Proof. by []. Qed.
 

Lemma limit_CE1: limit_v1 omega_plus_n (cons one 0 T1omega).
Proof.
split; first by move => n.
move => y ;case: y => //; first by exists 0; rewrite T1le0n.
move => a n b /=; case: (T1ltgtP a one) => //.
  by rewrite T1lt1 => /eqP -> _; exists 0.
move => ->; case: eqP => // ->; case: b => //; first by exists 0.
move => a' n' b' /=; rewrite /phi0 T1lt1 T1ltn0 !if_same if_simpl.
move /eqP ->; exists (n'.+1); rewrite T1le_consE T1ltnn !eqxx ltnn.
by rewrite T1le_consE T1ltnn !eqxx ltnSn.
Qed.


Lemma limit_CE2: limit_v2 omega_plus_n (cons one 1 zero).
Proof.
split; first by move => n.
move => y;case: y => //; first by exists 0; rewrite T1le0n.
move => a n b /=; case: (T1ltgtP a one) => //.
  by rewrite T1lt1 => /eqP -> _ _; exists 0.
move => ->; rewrite T1ltn0 if_same if_simpl; case n => // /and3P [_ nb ltb] _.
move:nb ltb; case b => //; first by  move => _ _; exists 0. 
move => a' n' b' /and3P [_ _ ltb] /=.
rewrite T1lt1 T1ltn0 !if_same  if_simpl => /eqP az.
move: ltb; rewrite az /phi0 T1lt1 => /eqP ->.
by exists n'; rewrite   T1le_consE  T1ltnn ltnn ! eqxx T1lenn.
Qed.

Lemma limit_CE3: limit_v2 omega_plus_n (cons one 0 T1omega).
Proof. by move: limit_CE1 => [sa sb]; split => // y _; apply: sb. Qed.

(** *** The normal form *)
(** To each ordinal, one can associate another ordinal that is NF.
However,  this is in general incompatible with other operations  *)


Fixpoint toNF x :=
  if x is cons a n b then (cons (toNF a) n zero) + toNF b else zero.

Lemma nf_toNF x: T1nf (toNF x).
Proof. 
by elim:x => //a Ha n b Hb; apply: nf_add => //=; rewrite -/toNF Ha.
Qed.

Lemma toNF_nz x : toNF x = zero -> x = zero. 
Proof.
case x => // a n b /=; case (toNF b) => // a' n' b'.
by case (T1ltgtP (toNF a) a').
Qed.


Lemma toNF_nf x: T1nf x -> toNF x = x.
Proof. 
elim:x => //a Ha n b Hb /and3P [/Ha sa /Hb sb etc].
by rewrite /toNF -/toNF sa sb add_to_cons.
Qed.

Lemma toNF_mon x : x <= toNF x.
Proof.
elim:x => //.
move => a Ha n b Hb /=; rewrite -/toNF.
have aux: if a < toNF a then true else if a == toNF a then true else false.
  by case /orP: Ha => -> //; rewrite  if_same.
move: Hb; case: (toNF b) => //.
  by move => sa; rewrite T1le_consE ltnn eqxx sa aux.
move => a' n' b' sa; case: (T1ltgtP (toNF a) a') => sb.
+ by rewrite T1le_consE (T1le_lt_trans Ha sb).
+ by rewrite T1le_consE ltnn eqxx sa aux.
+ by rewrite T1le_consE ltnS leq_addr aux.
Qed.

Lemma toNF_ex1 x: toNF (cons zero 0 x) = one + toNF x.
Proof. by case: x. Qed.

Lemma toNF_ex2: toNF (cons one 0 T1omega) = cons one 1 zero. 
Proof. by []. Qed.

Lemma toNF_succ (x := cons zero 0 one): toNF (T1succ x) != T1succ (toNF x). 
Proof. by []. Qed.


Lemma toNF_pred (x := cons zero 0 one): toNF (T1pred x) != T1pred (toNF x). 
Proof. by []. Qed.

(** *** Realizing the limit *)
(** This is a simplification of the code given for the type T3 below.
We define a function [F(x)]; so that for any limit ordinal [x], if [f= F(x)],
then [f] is stictly increasing (of type [nat -> T1]), and its limit is [x].
*)

Lemma fincP (f: Tf) :
  (forall n, f n < f n.+1) -> 
  (forall n m, (n < m)%N -> f n < f m).
Proof.
move => h n; elim => //.
move => m Hm;rewrite ltnS leq_eqVlt; case /orP;first by move => /eqP ->.
move /Hm => sa; exact: (T1lt_trans sa (h m)).
Qed.

Definition limit_of (f: Tf) x :=
  [/\ (forall n m, (n < m)%N -> f n < f m), limit_v2 f x & T1nf x].

Lemma limit_unique f x y: limit_of f x -> limit_of f y  -> x = y.
Proof. by move => [_ pa pb] [_ pc pd]; apply: (limit_unique2 pa pc pb pd). Qed.


Lemma limit_lub f x y: limit_of f x -> (forall n, f n <= y) -> T1nf y ->
  x <= y.
Proof.
move => [pa [pb pc] pd ] hy; case (T1ltP y x) => // ha hb.
move: (pc _ hb ha) => [n ny].
by move: (T1le_lt_trans ny (pa _ _ (ltnSn n))); rewrite T1ltNge (hy n.+1).
Qed.


Definition phi1 a (f:Tf) := fun n => a + f n.
Definition phi2 (f:Tf) := fun n => phi0 (f n).
Definition phi3 a:= fun n => cons a n zero.

Lemma limit1 a b f: T1nf a -> limit_of f b -> limit_of (phi1 a f) (a + b).
Proof.  
move => na [sa [sb sc] nb].
move: (nf_add na nb) => ns.
split => //; first by move => n m / sa => h; rewrite T1lt_add2l.
split; first by move => n; rewrite T1lt_add2l (sb n).
move => y ny hy.
case: (T1ltP a y) => cp; last first.
  by exists 0; apply: (T1le_trans cp); rewrite add_le1.
move: (sub_pr1 ny (T1ltW cp)) => yv.
have ha: y - a < b by move: hy; rewrite {1} yv T1lt_add2l.
have [n nv] := (sc _ (nf_sub ny na) ha).
by exists n; rewrite yv  T1le_add2l nv.
Qed.

Lemma limit2 b f: limit_of f b -> limit_of (phi2 f) (phi0 b).
Proof. 
move => [sa [sb sc] nb]; rewrite /limit_of nf_phi0.
split => //; first by move => n m nm /=; rewrite  (sa _ _ nm).
split => //; first by move => n; rewrite /= sb.
case => //; first by exists 0; rewrite T1le0n.
move => a' n' b' /and3P [na _ _] /=; rewrite T1ltn0 !if_same if_simpl => h.
move: (sc _ na h) => [n yn].
by exists n.+1; rewrite T1le_consE (T1le_lt_trans yn (sa _ _ (ltnSn n))).
Qed.

Lemma limit3 a: T1nf a -> limit_of (phi3 a) (phi0 (T1succ a)).
Proof.
move => na.
rewrite /limit_of nf_phi0 nf_succ //; split => //.
  by move => n l nm /=; rewrite nm eqxx T1ltnn.
split; first by move => n; rewrite /= succ_lt.
case => //; first by  exists 0; rewrite T1le0n.
move => a' n b /and3P [na' _ _] /=. 
rewrite T1ltn0 !if_same if_simpl lt_succ_le_3 // T1le_eqVlt => aa.
by exists n.+1; move: aa; rewrite T1le_consE ltnSn; case (T1ltgtP  a a').
Qed.

(** *** Normal functions *)
(** We say that [f:T2 -> T2] is a normal function  if it is striclly increasing
and the suppremum of all [f(y)], for [y<x] is [f(x)] whenever [x] is limit.
Everything is assumed NF. *)


Fixpoint limit_fct x :=
if x is cons a n b then
  if (b==zero) then 
     if(a==zero) then phi3 a
     else if (T1is_succ a) 
        then if (n==0) then phi3 (T1pred a) else 
         phi1 (cons a n.-1 zero) (phi3 (T1pred a))
     else if(n==0) then (phi2 (limit_fct a)) 
     else phi1 (cons a n.-1 zero)  (phi2 (limit_fct a))
  else phi1 (cons a n zero) (limit_fct b)
else phi3 zero.


Lemma limit_prop x: T1nf x -> T1limit x -> limit_of (limit_fct x) x.
Proof.
elim:x => // a Ha n b Hb np /=.
move/and3P: np => [sa sb sc].
have nc: forall m, T1nf (cons a m zero) by move => m; rewrite /= andbT.
have Hc: forall m, (cons a m.+1 zero) =  (cons a m zero) + phi0 a.
   by move => m;  rewrite /phi0 /= T1ltnn addn0.
case pa: (a==zero) => //; case bz: (b==zero); last first.
  by move /(Hb sb) => sd; rewrite -(add_to_cons n sc); apply: limit1. 
rewrite (eqP bz) => _.
case isa: (T1is_succ a).
  have aux: (limit_of (phi3 (T1pred a)) (phi0 a)).
    by rewrite {2} (succ_pred sa isa); apply: limit3; apply: nf_pred.
  by case n => //= m; rewrite Hc; apply:limit1. 
move: (limit_pr1 a); rewrite pa isa /= addbF => la.
have aux: (limit_of (phi2 (limit_fct a)) (phi0 a)) by apply: limit2; apply: Ha.
by case n => //= m; rewrite Hc; apply:limit1. 
Qed.


Definition sup (f: T1-> T1) x z :=
  [/\ T1nf z,
      (forall y, T1nf y -> y < x -> f y <= z) &
      (forall z', T1nf z' -> z' < z -> exists y, 
          [&& T1nf y, y < x & z' < f y])].


Definition normal f:=
  [/\ forall x, T1nf x -> T1nf (f x),
      (forall x y, T1nf x -> T1nf y -> x < y -> f x < f y)&
      (forall x, T1nf x -> T1limit x -> sup f x (f x)) ].



Lemma sup_unique f x z z': sup f x z -> sup f x z' -> z = z'.
Proof. 
move => [pa pb pc] [pa' pb' pc']; case (T1ltgtP z z') => //.
  move/(pc' _ pa) => [y /and3P [qa qb qc]].
  by move: (pb _ qa qb); rewrite T1leNgt qc.
move/(pc _ pa') => [y /and3P [qa qb qc]].
by move: (pb' _ qa qb); rewrite T1leNgt qc.
Qed.


Lemma sup_Oalpha_zero: sup id zero zero.
Proof.
by split; [ done | by move => y _; rewrite T1ltn0 | move => z; rewrite T1ltn0]. 
Qed.

Lemma sup_Oalpha_succ x: T1nf x -> sup id (T1succ x) x.
Proof.
move => nx;split. 
- done.
- by move => y nf; rewrite lt_succ_le_3.
- by move => z nz zx; exists x => //; rewrite nx zx succ_lt.
Qed.

Lemma sup_Oalpha_limit x: T1nf x -> T1limit x -> sup id x x.
Proof.
move => nx lx ;split; [done | by move => y _ /T1ltW | ].
move => z nz zx; move: (limit_pr lx zx) => h.
by exists (T1succ z); rewrite h nf_succ // (succ_lt z).
Qed.

(**  Identity is normal, composition of normal functions is normal, 
addition is normal when the firtst argument is fixed. A normal function maps limit ordinals to limit ordinls *)

Lemma normal_id: normal id.
Proof. split => //; apply: sup_Oalpha_limit. Qed.

Lemma normal_limit f x: normal f -> T1nf x -> T1limit x -> T1limit (f x).
Proof.
move => [pa pb pc] nx lx.
move: (pc _ nx lx) => [sa sb sc].
move: (limit_pr1 (f x)); case fz: (f x == zero).
  have zx:  zero < x by move: lx; case x. 
  have nz: T1nf zero by [].
  by move: (pb zero x nz nx zx);  rewrite (eqP fz) T1ltn0.
case: (T1limit (f x)) => //= sf.
move:(succ_pred  (pa _ nx) sf) => eq1.
move: (sc _ (nf_pred sa) (pred_lt sf)) => [y /and3P [ny yx]].
by rewrite T1ltNge - (lt_succ_le_3 _ (pa _ ny)) - eq1 (pb _ _ ny nx yx).
Qed.



Lemma add_normal a:  T1nf a -> normal (T1add a).
Proof.
move => na;split.
    by move => x nx; apply: nf_add.
  by move => x y nx ny; rewrite T1lt_add2l. 
move => x nx lx; split.
    by apply: nf_add.
  by move  => y _ /T1ltW; rewrite T1le_add2l.
move => z nz zp; case: (T1ltP z a) => az.
  by exists zero; move: lx;rewrite T1addn0 az T1lt0n; case x.
move: (sub_pr1 nz az) => sa.
move:zp; rewrite {1} sa T1lt_add2l => sb.
exists (T1succ (z - a)).
by rewrite (nf_succ (nf_sub nz na)) (limit_pr lx sb) {1} sa T1lt_add2l succ_lt.
Qed.


Lemma normal_compose f g: 
   normal f -> normal g -> normal (f \o g).
Proof.
move => [pa pb pc][pa' pb' pc']; split.
- by move => x nx; apply: pa; apply: pa'.
- by move => x y nx ny h; apply: pb; [ apply: pa' | apply: pa' | apply: pb'].
- move => x nx lx. 
  move: (pa' _ nx) => ny.
  have lg: T1limit (g x) by  apply:normal_limit.
  move:(pc _ ny lg) => [qa qb qc]; split => //.
    move => y nu yx /=; apply:T1ltW;apply: pb; auto.
  move: (pc' _ nx lx) => [qa' qb' qc'].
  move => z' nz' h /=; move: (qc _ nz' h) => [y /and3P[ya yb yc]].
  move: (qc' _ ya yb) => [z /and3P[za zb zc]]; exists z.
  by rewrite za zb /=;  apply: (T1lt_trans yc); apply: pb => //; apply: pa'.
Qed.


(** ** multiplication *)

(** There is a unique way to define multiplication (for NF arguments)
compatible with our interpretation of [cons]. In the case where [a] and [a'] 
are zero, we could use zero or [b] instead of [b']. With the current 
implementation, multiplication is associative, and there is a distributivity 
law *)


Fixpoint T1mul (c1 c2 : T1) {struct c2}:T1 :=
  if c2 is cons a' n' b' then
    if c1 is cons a n b then
       if((a==zero) && (a' == zero)) then cons zero (n*n' + n + n')%N b'
       else if(a'==zero) then  cons a  (n*n' + n + n')%N b
       else cons (a + a') n' ((cons a n b) * b')
     else zero   
  else zero
where  "c1 * c2" := (T1mul c1 c2) : cantor_scope.


Lemma mul_na n b x:  (cons zero n b) * x =  (cons zero n zero) * x.
Proof.
by elim: x => // a' _ n' b' Hb /=; rewrite Hb //;case pa: (a'==zero).
Qed.

Lemma T1muln0 x:  x * zero = zero.
Proof.  done.  Qed.

Lemma T1mul0n x:  zero * x  = zero.
Proof. by case:x. Qed.

Lemma mul_int n m : \F n * \F m = \F (n *m)%N.
Proof.
case: n; first by rewrite T1mul0n.
move => n;case: m; first by rewrite T1muln0 muln0.
by move => m /=; rewrite - mulnE mulnSr addnC.
Qed.

Lemma mul_phi0 a b: phi0 (a + b) = phi0 a * phi0 b.
Proof.
simpl;case hb:(a== zero); case ha: (b==zero) => //=;rewrite (eqP ha) T1addn0 //.
rewrite (eqP hb) //.
Qed.

Lemma T1mul_eq0 x y: (x * y == zero) = (x== zero) || (y == zero). 
Proof.
case: y x => [ [] |a n b] // [] // a' n' b' /=.
by case : (_ && _) => //; case: (a==zero).
Qed.


Lemma T1mul_eq1 a b: T1nf a -> (a* b == one) = ((a == one) && (b == one)). 
Proof.
case: a => //; [ by rewrite T1mul0n | move => a' n' b'].
case: b => //; [ by rewrite T1muln0 andbF | move => a n b].
simpl; case pa: (a'== zero); last first.
   case pb: (a==zero);rewrite !T1eqE pa // T1add_eq0 pa //.
case pb: (a== zero); last by rewrite andbF !T1eqE (T1add_eq0) pb ! andbF.
rewrite (eqP pa) T1lt1; move /and3P => [_ _ /eqP ->].
by rewrite /= !T1eqE pb /=; case n' => // m; case n => //=; rewrite muln0 addn0.
Qed.


Lemma mul_distr: right_distributive T1mul T1add.
Proof.
move => x y z; elim: y x z.
  by move => x z; rewrite T1muln0 !T1add0n.
move => a _ n b Hb; case; first  by move => z; rewrite ! T1mul0n.
move => a' n' b'; case; first by rewrite T1muln0 ! T1addn0. 
move => a'' n'' b'' /=.
case ha: (a'==zero); [rewrite (eqP ha) !andTb | rewrite !andFb ].
  case hb: (a==zero); first rewrite (eqP hb).
    case hc: (a''==zero); last by move: hc; case a''.
    by rewrite (eqP hc) /= - !addnS mulnDr mulnS - !addnA (addnCA n) (addnCA n).
  case hc: (a'' == zero).
    rewrite  (eqP hc) T1add0n  add_simpl1 ? hb // T1ltn0.
    by rewrite T1lt0n hb /= hb Hb /=.
  simpl;case pa: (a < a''); first  by rewrite /= hc.
  by case pb: (a'' < a);  rewrite /= hb // Hb /= hc.
case: (altP (a=P zero)) => hb.
  rewrite hb; case hc: (a''==zero).  
    rewrite (eqP hc) /= ha T1ltnn /= mulnS mulnDr addnS ! addnA (addnC n').
    by set X := (n' * n + n') %N;rewrite (addnAC (X + _)%N) (addnAC X).
  by rewrite T1ltn0  T1lt0n hc /negb /= ha hc add_le4 // hc.
case hc: (a'' == zero).
  have h: a' < a' + a by apply: add_le4.
  rewrite (eqP hc) T1ltn0  T1lt0n hb /= ha /= h  (T1lt_anti h) Hb //.
  by rewrite (negbTE hb) /= ha. 
rewrite /= ! T1lt_add2l. 
by case (T1ltgtP a a''); rewrite /=? ha ? hc ?(negbTE hb)//= Hb /= ha hc.
Qed.


Lemma mulA: associative T1mul.
Proof.
move => x y z; elim: z y x; first by move => a b; rewrite !T1muln0.
move => a _ n b Hb; case; first by move => x; rewrite T1muln0 T1mul0n.
move => a' n' b';case; [by rewrite !T1mul0n | move => a'' n'' b'' /=].
have aux:  (n'' * (n' * n + n' + n) + n'' + (n' * n + n' + n))%N =
           ((n'' * n' + n'' + n') * n + (n'' * n' + n'' + n') + n)%N.
       rewrite ! mulnDl ! mulnDr mulnA ! addnA; congr (_ + _ + _)%N.
       rewrite - ! addnA; congr addn;rewrite addnCA; congr addn.
       by rewrite addnA addnC. 
case pa: (a'==zero); first rewrite  (eqP pa).
  case pb: (a''== zero); rewrite ?(eqP pb) !andTb /= ? pb ? andFb.
     case pc: (a==zero) => /=;[ by rewrite aux | by rewrite pc Hb /=].
  case pc: (a==zero) => /=; rewrite pb andFb ? aux // pc Hb /= pb //.
case pb: (a==zero); rewrite /= ? pa ! andbF T1add_eq0 pa !andbF !andFb //.
by rewrite T1addA  Hb /= pa andbF.
Qed.


(** Note that in some case the product of [x] and one is not [x] *)

Lemma T1muln1 x: T1nf x -> x * one = x.
Proof.
case: x => // a n b /= /and3P[_ _]; rewrite muln0 add0n addn0.
by case (altP (a =P zero)) => // ->; rewrite T1lt1 eqxx => /eqP ->.
Qed.

Lemma T1mul1n x: one * x  = x.
Proof.  
by elim: x => // a _ n b /= ->; case  (altP (a =P zero)) => // ->.
Qed.

Lemma T1mul1nCE (x := T1bad): x * one  <> x.
Proof.  done. Qed.


Lemma T1muln1_CE x:
  (x == x * one) =
    (if x is cons a n b then ((a != zero) || (b== zero)) else true).
Proof.
by case: x => // a n b /=; rewrite muln0 addn0 fun_if !T1eqE !eqxx; case a.
Qed.

Lemma mul_succ x y: T1nf x -> x * (T1succ y) = x * y + x.
Proof. by move => h; rewrite succ_is_add_one mul_distr T1muln1. Qed.

Lemma T1lt_mul2l x y z: x != zero -> T1nf z -> ((x *y < x *z) = (y < z)).
Proof.
case x => // a n b _; elim: y z.
  case;rewrite T1muln0 => // u v w //=; case a => //; case u  => //.
move => a' Ha n' b' Hb; case; first by rewrite T1muln0 ! T1ltn0.
move => a'' n'' b'' nc.
move/and3P:(nc) => [_ nb _] /=.
case  pa: (a==zero).
  case pb: (a'==zero).
    rewrite !andTb (eqP pb) (eqP pa); case a'' => //=. 
    by rewrite  ltn_simpl2  eqn_simpl2.
  rewrite !andTb (eqP pa) T1add0n.
  case pc: (a''==zero); first by rewrite /= pb (eqP pc) T1ltn0 pb.
  simpl;case pd:(a' < a'') => //; case pe:( a' == a'') => //.
  case pf:( n'< n'')%N => //; case pg:( n' ==  n'')%N => //. 
  by move: (Hb _ nb); rewrite (eqP pa).
simpl.
case pb: (a'== zero).
   case pc: (a'' == zero).
     move: nc;rewrite (eqP pc) pb T1ltn0 T1nf_finite1=> /eqP ->.
     by rewrite /= !T1ltnn T1ltn0  eqxx ltn_simpl2 eqn_simpl2 if_same if_simpl.
   have: a < a + a'' by move: pc;rewrite -{1} (T1addn0 a)  T1lt_add2l; case a''.
   by rewrite (eqP pb) /= => ->; move: pc; case a''.
case pc: (a'' == zero).
   by rewrite (eqP pc) /= -{2 4} (T1addn0 a) T1lt_add2l T1eq_add2l !T1ltn0 pb.
rewrite /= T1lt_add2l T1eq_add2l.
case: (a' < a'') => //; case: (a' == a'') => //; case:  (n' < n'')%N => //.
by case: (n' == n'')%N => //; apply: Hb.
Qed.

Lemma mulnf0 a n b: a != zero -> b < phi0 a -> (cons zero n zero) * b < phi0 a.
Proof.
case: b => // a' n' b'; rewrite phi0_lt1 /=.
by case pa: (a'==zero); [case a | rewrite phi0_lt1].
Qed.

Lemma nf_mul a b: T1nf a -> T1nf b -> T1nf (a * b). 
Proof.
elim: b a => // => a Ha n b Hb; case => // a' n' b' sa.
case pb: (a==zero).
  move: sa; rewrite /=  (eqP pb) fun_if /= andbT;case eqP => // _ _ /andP [_].
rewrite /= pb andbF /=; move =>/and3P [na nb].
rewrite (nf_add (T1nf_consa sa) na) Hb //=.
case b; [ by rewrite T1muln0 /phi0  |move => u v w ]. 
rewrite /= ! (fun_if (fun z =>  z < phi0 (a' + a))) ! phi0_lt1.
rewrite - {3} (T1addn0 a') !T1lt_add2l !T1lt0n T1ltn0 T1add_eq0 !if_same pb.
by rewrite if_simpl => ->; rewrite andbF !if_same.
Qed.

Lemma T1lt_mul2r x y z:  (y * x < z * x) ->  (y < z). 
Proof.
elim: x y z => // a Ha n b Hb.
case => //; [ case => // | move => a' n' b'; case].
   by rewrite ! (fun_if (fun z =>  z < zero)) ! T1ltn0 !if_same.
move =>  a'' n'' b'' /=.
case pa: (a'==zero).
  case pb: (a==zero). 
    rewrite (eqP pa) !andbT (eq_sym zero a'') T1lt0n;case a'' => //=.
    by rewrite T1ltnn if_same if_simpl - ! mulnSr ltn_add2r ltn_mul2r /= => ->.
  by case a''; rewrite (eqP pa) // !andbF /= !T1ltnn ltnn ! eqxx; move /Hb.
case pb: (a==zero).
  case pc: (a''==zero); rewrite ! andbT /= ?pa? T1ltn0 //.
  case (T1ltgtP a' a'') => //.
  by rewrite - ! mulnSr ltn_add2r ltn_mul2r eqn_add2r eqn_mul2r /=.
rewrite ! andbF /= ltnn eqxx.
case pc: (a' + a < a'' + a); first by rewrite (T1lt_add2r pc).
by case pd: (a' + a == a'' + a) => // /Hb.
Qed.

Lemma T1le_mul2l x y z :  x != zero -> T1nf y ->
    (x *y <= x *z) = (y <= z).
Proof. by move => sa sn; rewrite !T1leNgt T1lt_mul2l. Qed.

Lemma T1le_mul2r x y z:  (y <= z) -> (y * x <= z * x). 
Proof. by rewrite !T1leNgt; apply: contra; apply: T1lt_mul2r.  Qed.

Lemma T1eq_mul2l p m n : p != zero -> T1nf m -> T1nf n -> 
   (p * m == p * n) = (m == n).
Proof. move => sa sb sc; rewrite ! T1eq_le ! T1le_mul2l => //. Qed.


Lemma T1le_pmulr x a: T1nf a -> x != zero -> a <= a * x.
Proof.
move => na xnz.
case az: (a==zero);first by rewrite (eqP az) T1mul0n.
by rewrite - {1} (T1muln1 na) T1le_mul2l ? az // T1ge1. 
Qed.

Lemma  T1le_pmulrCE (x:= \F1 ) (a:=T1bad) : (a <= a * x) = false.
Proof. done. Qed.

Lemma T1le_pmulrl x a: x != zero -> a <= x * a.
Proof.
move =>  xnz.
by rewrite - {1} (T1mul1n a); apply:T1le_mul2r; rewrite  T1ge1. 
Qed.

Lemma T1le_mulCE (m1:= one) (m2:= T1bad) (n1 := \F1) (n2 := one) : 
   (m1 <= n1) && (m2 <= n2) && ( m1 * m2 <= n1 * n2) == false.
Proof. done. Qed.

Lemma T1le_mul m1 m2 n1 n2 : T1nf m2 -> m1 <= n1 -> m2 <= n2 -> 
   m1 * m2 <= n1 * n2.
Proof.
move => nm2 s1 s2;apply (@T1le_trans (m1 * n2)).
   case az: (m1==zero);first by rewrite (eqP az) ! T1mul0n.
   by rewrite T1le_mul2l // az.
by apply:T1le_mul2r.
Qed.

(** *** Preparation of the exponention
The prouct of an integer and omega is omega. This holds in fact for any limit 
ordinals. We give here a formula for the product of omega and [x], and show 
that this is a limit ordinal. The converse holds. *)


Lemma mul_fin_omega n: (\F n.+1) * T1omega = T1omega.
Proof. done. Qed.


Lemma mul_int_limit n y: T1limit y -> \F n.+1 * y = y.
Proof.
elim y => // a _ m b Hb /=.
case pa: (a==zero) => //;case pb: (b==zero); last by move/Hb => ->.
by rewrite (eqP pb) T1muln0.
Qed.

Lemma T1mul_omega a n b: 
   T1omega * (cons a n b) = 
   if (a== zero) then cons one n zero else cons (one + a) n (T1omega * b).
Proof. by rewrite /T1omega/phi0 /=; case pa: (a==zero). Qed.

Lemma mul_omega_limit x: x != zero -> T1limit (T1omega * x).
Proof.
elim: x => // a _ n b Hb _.
rewrite T1mul_omega; case pa: (a==zero) => //.
rewrite /T1limit T1add_eq0 pa andbF -/T1limit.
case pb: (b== zero). by rewrite (eqP pb) T1muln0.
by rewrite  (Hb (negbT pb)) orbT.
Qed.



Fixpoint T1div_by_omega x :=
  if x is cons a n b then cons (a - one) n (T1div_by_omega b) else zero.

Lemma div_by_omega_pr x: T1nf x -> ((x==zero) || T1limit x) 
  -> T1omega * (T1div_by_omega x) = x.
Proof.
elim: x => // a _ n b Hb. 
rewrite orFb /T1limit -/T1limit; case pa: (a==zero) => //. 
move: (negbT pa); rewrite - T1ge1; case /orP.
   move /eqP  => <-.
   rewrite /T1div_by_omega -/T1div_by_omega T1subnn T1mul_omega eqxx.
   case b => // a' n' b' /=; move /andP => [_].
   by rewrite T1lt1 T1ltn0 ! if_same if_simpl => ->.
move => lt1  /and3P [na /Hb h _] /h h'.
rewrite /T1div_by_omega -/T1div_by_omega T1mul_omega h'.
by rewrite - (sub1a (negbT pa) na) (negbTE (sub_nz na lt1)).
Qed.

(** We show here every ordinal [x] is the product of omega and [y], 
to which an integer is added. We study the behaviour 
of this decomposition and multiplication *)

Lemma nf_div_by_omega x: T1limit x -> T1nf x -> T1nf (T1div_by_omega x).
Proof.
elim: x => // a _ n b Hb /= lx /and3P [sa sb sc]; apply /and3P; split => //.
+ by apply: nf_sub.
+ move: lx; case eqP => //_;case /orP; first by move /eqP -> .
  by move => lb ; apply: Hb.
move: lx; case pa: (a==zero) => // h.
have oz: T1omega != zero by done.
have nz: T1nf (phi0 (a - cons zero 0 zero)) by rewrite nf_phi0 nf_sub //.
rewrite - (T1lt_mul2l (T1div_by_omega b) oz nz) div_by_omega_pr //.
by rewrite -[T1omega ]/(phi0 (one)) - mul_phi0 - sub1a // pa.
Qed.

Lemma nf_revCE u v: T1bad <> T1omega * u  + \F v.
Proof.
case: (altP (u=Pzero)); first by move => ->; case v.
move/mul_omega_limit;set w:=  (T1omega * u).
case: v; first by rewrite T1addn0 => sa sb; move: sa; rewrite - sb.
by move => v; case w => // a n b; case a.
Qed.


Lemma add_simpl3 x y: y != zero -> 
  x + x * (T1omega * y) = x * (T1omega * y). 
Proof.
case: x => // a n b;case y => // a' n' b' _; rewrite T1mul_omega.
have e1: (one == zero) = false by done.
have e2: (one + a' == zero) = false by rewrite T1add_eq0 e1.
have e3: a < a + one by rewrite - succ_is_add_one succ_lt.
have e4: a < a + (one + a') by apply: add_le4; rewrite e2.
by case: eqP; rewrite /T1mul ? e1 ? e2 andbF -/T1mul {1}/T1add ? e3 ? e4.
Qed.

Lemma plus_int_Ox n x: x != zero -> \F n + T1omega * x =  T1omega * x.
Proof.
case: n => // n xnz.
by move:(mul_omega_limit xnz); case (T1omega * x) => // a m b /=; case a.
Qed.


Lemma nf_rev x (u := (T1div_by_omega (T1split x).1)) (v:= (T1split x).2):
 T1nf x ->  T1nf u /\  x = T1omega * u + \F v.
Proof.
move => nx.
move: (split_add x) (nf_split nx).
rewrite /u /v.
case (T1split x) => y n h ny. move: (h nx) => /andP [/eqP ->]. 
case /orP; first by move => /eqP -> //.
move => hh;  move:(nf_div_by_omega hh ny) => sa /=.
by rewrite (div_by_omega_pr ny) //=; rewrite hh orbT.
Qed.


Lemma nf_rev_unique u v (x:= T1omega *u + \F v): T1nf u ->
    u = T1div_by_omega (T1split x).1 /\ v = (T1split x).2.
Proof.
suff H: forall u v u' v', T1nf u -> T1nf u' ->
   T1omega * u + \F v = T1omega * u' + \F v' -> u = u' /\ v = v'.
  move => nu.
  have nx: T1nf x by rewrite nf_add // ? nf_finite // nf_mul.
  move: (nf_rev nx) => []; by apply: H.   
clear x u v.
move => u v u' v' nu nu' h.
have aux1: forall a b, T1omega * a + \F b < T1omega * (T1succ a).
   by move => a b; rewrite mul_succ // T1lt_add2l; case b.
have aux2:  forall a b, T1omega * a <= T1omega * a + \F b.
   move => a b; apply: add_le1.
move: (aux1 u v) (aux2 u' v'); rewrite h => sa sb.
move: (T1le_lt_trans sb sa); rewrite T1lt_mul2l // ?nf_succ // lt_succ_le_3 //.
move: (aux1 u' v') (aux2 u v); rewrite h => ta tb.
move: (T1le_lt_trans tb ta); rewrite T1lt_mul2l // ?nf_succ // lt_succ_le_3 //.
move => sc sd.
have uu': u = u' by move: sc sd; rewrite /T1le (eq_sym u'); case (T1ltgtP u u').
by move: h; rewrite uu' => /eqP; rewrite T1eq_add2l => /T1eqP /T1F_inj ->.
Qed.

Lemma nf_rev_sum x y
  (u := T1div_by_omega (T1split x).1) (n:= (T1split x).2)
  (v := T1div_by_omega (T1split y).1) (m:= (T1split y).2)
  (w := T1div_by_omega (T1split (x+y)).1) (p:= (T1split (x+y)).2):
  T1nf x -> T1nf y ->
  if (v==zero) then (w = u /\ p = (n + m)%N) else (w = u+v /\ p = m).
Proof.
move => nu nv.
move: (nf_rev nu)(nf_rev nv); rewrite -/u -/v -/n -/m; move => [sa sb][sc sd].
case pa: (v==zero).
  have eq3: x + y = T1omega *u + \F (n + m).
    by rewrite sb sd (eqP pa) T1muln0 T1add0n - T1addA add_int.
  by move: (nf_rev_unique (n+m)%N sa); rewrite - eq3; move => [-> ->].
have eq3: x +y =  T1omega * (u + v) + \F m.
  by rewrite sb sd -T1addA (T1addA (\F n)) plus_int_Ox ?pa // T1addA mul_distr.
by move: (nf_rev_unique m (nf_add sa sc)); rewrite - eq3; move => [-> ->].
Qed.

Lemma mul_sum_omega a n: a != zero ->
   (T1omega * a + \F n) * T1omega  = (T1omega * a) * T1omega.  
Proof.
case: n; [ by rewrite T1addn0 | move => n].
elim: a => // a _ m b Hb _.
rewrite T1mul_omega; case pa: (a== zero) => //.
rewrite /T1nat {1}/T1add -/T1add T1ltn0 T1lt0n T1add_eq0 andFb /negb.
rewrite {2 4} /T1omega /phi0 /T1mul -/T1mul andbF //.
Qed.

Lemma nf_rev_prod x y
  (u := T1div_by_omega (T1split x).1) (n:= (T1split x).2)
  (v := T1div_by_omega (T1split y).1) (m:= (T1split y).2)
  (w := T1div_by_omega (T1split (x*y)).1) (p:= (T1split (x*y)).2):
  T1nf x -> T1nf y ->
  if (u== zero) 
     then if  (n == 0) then (w = zero /\ p = 0)
     else  (w = v /\ p = (n*m)%N)
  else if (m==0) then (w = u * T1omega *v  /\ p = 0)
  else  (w = u * T1omega *v + u * \F m /\ p = n).
Proof.
move => nu nv. 
set H := nf_rev_unique.
move: (nf_rev nu)(nf_rev nv); rewrite -/u -/v -/n -/m; move => [sa sb][sc sd].
case pa: (u== zero).
  have : x * y = (\F n) * T1omega * v + \F (n * m)%N.
    by rewrite sb sd (eqP pa) T1muln0 T1add0n mul_distr mul_int mulA.
  case n; first by rewrite /w /p /= T1mul0n T1add0n => ->.
  move => n'; rewrite mul_fin_omega /= => h.
  by move: h (H _  (n'.+1 * m)%N sc) => <-  [-> ->].
move: (erefl (x* y)); rewrite {2} sd mul_distr mulA.
rewrite {2} sb mul_sum_omega ? pa // - !mulA => h.
have se: T1nf (u * (T1omega * v)) by rewrite !nf_mul //.
have sf: T1nf (u * (T1omega * v) + u * \F m). 
   by rewrite nf_add // nf_mul // nf_finite.
have aux: T1nf (T1omega * u) by rewrite nf_mul.
case pb: (m==0).
  by move: h (H _ 0 se); rewrite (eqP pb) T1muln0; move => <- [-> ->].
have e1: \F n + x = x by rewrite sb T1addA plus_int_Ox ? pa //.
have e2: x * \F m = T1omega * u * \F m + \F n.
  move: pb;elim m => // k Hr _; case ba: (k== 0).
    by rewrite (eqP ba) T1muln1 // T1muln1. 
  rewrite - (addn1) - add_int mul_distr Hr // T1muln1 // - T1addA e1 sb.
  by rewrite T1addA mul_distr T1muln1.
by move: h (H _ n sf); rewrite e2 T1addA - mulA - mul_distr  => <- [-> ->].
Qed.

(** *** Normality of multiplication
If [a] is a non-zero ordinal, the multiplication by [a] is normal.
This means, if [b] is limit, the supremum of all [a *c ] for [c<b ] is [a*b].
We show this for omega, and for some special cases. 
This is equivalent to existence of ordinal division.  
*)

Lemma mul_omega_pr1 a: a != zero -> T1nf a ->
  sup (T1mul a) T1omega (a * T1omega).
Proof.
move => sa sb.
have sc: T1nf T1omega by [].
split; first  by apply: nf_mul.
    by move  => y ny /T1ltW; rewrite (T1le_mul2l _ sa ny). 
move => z nz zp.
move: sb sa zp; case: a => // a1 n1 b1 sb _; rewrite /= andbF.
move: nz; case z; first by exists one => //=; case: (_ && _).
move => a2 n2 b2 /= /and3P [ha hb hc]. 
rewrite T1ltn0 !if_same if_simpl - succ_is_add_one lt_succ_le_3 //.
case /orP => a12; last first.
  exists one; simpl; move: a12; case az:(a1==zero); last  by move => /= ->.
  by rewrite (eqP az) T1ltn0.
rewrite (eqP a12).
exists (\F (n2.+2)); case az: (a1==zero).
  by rewrite /= az /= T1ltn0 az addnS ltnS leq_addl.
by rewrite /= az /= T1ltnn eqxx addnS ltnS leq_addl.
Qed.


Lemma mul_omega2_pr1 a (u:= cons one 1 zero): a != zero -> T1nf a ->
  sup (T1mul a) u (a * u).
Proof.
move => sa sb.
have sc: T1nf u by [].
split.
    by apply: nf_mul.
    by move  => y ny /T1ltW; rewrite (T1le_mul2l _ sa ny). 
move => z nz zp.
have eq1: a * u = a* T1omega + a * T1omega by rewrite - mul_distr //.
case: (T1ltP z (a*  T1omega)) => zo; first by exists T1omega => //.
move: (sub_pr1 nz zo) => sd.
move: (mul_omega_pr1 sa sb) => [se _ sf].
move: zp; rewrite sd eq1; rewrite T1lt_add2l => sg.
move: (sf _ (nf_sub nz se) sg) => [y1 /and3P [ya yb yc]].
exists (T1omega + y1); 
by rewrite nf_add // -[u] /(T1omega +T1omega) mul_distr  !T1lt_add2l yb yc.
Qed.


Lemma mul_omega_pr3 a b c: a != zero -> c != zero ->
   T1nf a -> T1nf b -> T1nf c ->
  sup (T1mul a) c (a * c) ->
  sup (T1mul a) (b+c) (a * (b + c)).
Proof.
move => az cz na nb nc [pa _ pc]; split => //.
    by apply: nf_mul => //; apply: nf_add.
  by move => y ny ybc; rewrite T1le_mul2l // T1ltW.
move => z nz zle.
case: (T1ltP z (a* b)) => zo. 
   by  exists b; rewrite nb zo add_le4.
move: (sub_pr1 nz zo) => sd.
move: zle; rewrite  sd mul_distr T1lt_add2l => se.
move: (pc _ (nf_sub nz (nf_mul na nb)) se) => [y1 /and3P [ya yb yc]].
by exists (b + y1); rewrite nf_add // mul_distr  !T1lt_add2l yb yc.
Qed.

 

(*
Lemma mul_omega2_pr3 a (u:= cons (\F 2) 0 zero): a != zero -> T1nf a ->
  sup (T1mul a) u (a * u).
Proof.
move => sa sb.
have sc: T1nf u by [].
split.
    by apply: nf_mul.
    by move  => y ny /T1ltW; rewrite (T1le_mul2l _ sa ny). 
move => z nz zp.
move: sb sa zp; case: a => // a1 n1 b1 sb _; rewrite /= andbF.
move: nz; case z; first by exists one => //=; case: (_ && _).
move => a2 n2 b2 /= /and3P [ha hb hc]. 
rewrite T1ltn0 !if_same if_simpl. 
case (T1ltP a2 a1) => ta tb.
  by exists T1omega; rewrite /= andbF (T1lt_trans ta) // add_le4 //.
move: (sub_pr1 ha ta) => sd.
move: tb; rewrite  {1} sd T1lt_add2l => se.

(*
move: (
case /orP => a12; last first.
  exists one; simpl; move: a12; case az:(a1==zero); last  by move => /= ->.
  by rewrite (eqP az) T1ltn0.
rewrite (eqP a12).
exists (\F (n2.+2)); case az: (a1==zero).
  by rewrite /= az /= T1ltn0 az addnS ltnS leq_addl.
by rewrite /= az /= T1ltnn eqxx addnS ltnS leq_addl.
Qed.

*)

Abort.
*)


(** ** Exponentiation *)

(** In order to compute [ a ^b ], we first write [b] as the sum of a limit 
ordinal and an integer [n]. Computing  [ a ^n ] is trivial. The limit ordinal
is omega times [c]; if [a] is at least one, then [a ^omega  = omega ^d ]
for some [d], and the result is [a ^ (omega * c)  = omega ^(d*c)=phi0(d*c) ].
This leads to the following definitions.
*)

Fixpoint exp_F a n :=
  if n is p.+1 then a * (exp_F a p) else one.

Definition exp_O a b :=
  if (a==zero) then if (b== zero) then one else a
  else if (a== one) then one
  else if (T1finite a) then (phi0 b)
  else phi0 ((T1log a) * T1omega * b).

Definition T1exp a b:=
  (exp_O a (T1div_by_omega (T1split b).1)) * (exp_F a ( (T1split b).2)).


Notation "a ^ b" := (T1exp a b) : cantor_scope.

(** Properties of [exp_O] *)


Lemma expO_mul1 a b: (exp_O a b) * (one) = exp_O a b.
Proof.
rewrite /exp_O; case: eqP; [by move => ->; case: eqP | case: eqP => //].
case:(T1finite a) => //=; rewrite andbT; case: eqP => // -> //.
Qed.

Lemma nf_expO a b: T1nf a -> T1nf b -> T1nf (exp_O a b).
Proof. 
move => na nb; rewrite /exp_O; case: eqP => //; case: eqP => //.
by rewrite fun_if !nf_phi0 nf_mul ? nb //  ?nf_mul // ? nf_log // if_same.
Qed.

Lemma expO_n0 x: exp_O x zero = one.
Proof. by rewrite /exp_O eqxx T1muln0 /= !if_same. Qed.

Lemma expO_1n n: exp_O (one) n  = one.
Proof.  done. Qed.


Lemma expO_eq0 a b: (exp_O a b == zero) = ((a== zero) && (b != zero)).
Proof.
rewrite /exp_O; case pa: (a==zero).
  by rewrite (eqP pa); case pb: (b==zero).
by case: (a== one) => //; case :(T1finite a).
Qed.

Lemma expO_eq1 a b: (exp_O a b == one) = ((a== one) || (b == zero)).
Proof.
rewrite /exp_O.
case pb: (b==zero); first by rewrite (eqP pb) T1muln0 !if_same orbT.
rewrite orbF; case pa: (a==zero) => //;case pc: (a == one) => //.
rewrite (fun_if (fun z => z == one)) /phi0 /T1nat !T1eqE !andbT !T1mul_eq0 pb.
by case a => // a' n' b' /=; case (a'== zero).
Qed.

Lemma expO_add z u v:  exp_O z u * exp_O z v = exp_O z (u + v).
Proof.
rewrite /exp_O; case: eqP.
  move ->; case: eqP; first by move ->;rewrite T1mul1n //.
  by move /eqP => uz;rewrite T1add_eq0 (negbTE uz) T1mul0n.
by case: eqP => //_ _;case (T1finite z); rewrite - mul_phi0 // mul_distr.
Qed.

(** Properties of [exp_F] *)
Lemma nf_expF a n: T1nf a -> T1nf (exp_F a n).
Proof. by move => na;elim: n => // n /= h; apply: nf_mul. Qed.

Lemma expF_add a n m: (exp_F a n) * (exp_F a m) = exp_F a (n + m).
Proof.
by elim: n; [ rewrite T1mul1n | move => n hr /=; rewrite - mulA hr].
Qed.

Lemma expF_mul a n m: exp_F a (n * m) =  exp_F (exp_F a n) m.
Proof.
by elim: m; [ rewrite muln0 | move => m /= <-; rewrite expF_add mulnS ].
Qed.

Lemma expF_1n n: exp_F (one) n  = one.
Proof. elim: n => // n /= -> //. Qed.

Lemma expF_eq0 a n: (exp_F a n == zero) = ((a== zero) && (n != 0)).
Proof.
elim: n => //; first by rewrite andbF.
by move => m /=; rewrite T1mul_eq0 => ->; rewrite andbC andKb andbT.
Qed.

Lemma expF_eq1 a n: T1nf a -> (exp_F a n == one) = ((a== one) || (n == 0)).
Proof.
move => na; elim: n => //; first by rewrite orbT. 
by move => n h; rewrite /exp_F -/exp_F T1mul_eq1 // h ?orbF; case: eqP.
Qed.

(** Properties of [exp] *)

Lemma nf_exp a b: T1nf a -> T1nf b -> T1nf (a ^b).
Proof.
move => na nb.
move: (nf_split nb) (proj1 (nf_rev nb)) => sa sb.
rewrite /T1exp nf_mul // ?nf_expF // nf_expO //.
Qed.

Lemma exp00: zero ^zero = one.
Proof. done. Qed.

Lemma expx0 x: x ^zero = one.
Proof. by rewrite /T1exp expO_n0.  Qed.

Lemma expx_pnat x n b: x ^ (cons zero n b)  = exp_F x n.+1.
Proof. by rewrite /T1exp /T1split eqxx expO_n0 T1mul1n. Qed.

Lemma expx_nat x n:  x ^ \F n = exp_F x n.
Proof. by case: n; [ rewrite expx0 | move => n; apply: expx_pnat]. Qed.

Lemma expx1 x: T1nf x -> x ^ one = x. 
Proof. by move => h; rewrite /one expx_pnat /exp_F T1muln1. Qed.

Lemma expx1CE: T1bad ^ one = one. 
Proof.  done. Qed.

Lemma exp2omega n: (\F n.+2)^ T1omega = T1omega.
Proof. done. Qed.

Lemma exp1x x: one ^ x = one.
Proof. by rewrite /T1exp expO_1n expF_1n. Qed.

Lemma exp_eq0 x y:  x^y ==  zero = ((x==zero) && (y != zero)).
Proof.
rewrite /T1exp T1mul_eq0 expO_eq0 expF_eq0.
rewrite - andb_orr; case pa: (x==zero) => //; rewrite !andTb.
by case y => // a n b /=; case pb: (a== zero) => //;case: (T1split b) => u v.
Qed.

Lemma exp0nz x: x != zero -> zero ^ x =  zero.
Proof.
by move => h; move:(exp_eq0 zero x); rewrite h /= => /eqP.
Qed.

Lemma exp_eq1 x y: T1nf x -> T1nf y ->
  (x^y == one) = ((x== one) || (y == zero)).
Proof.
move => nx ny; rewrite /T1exp;move: (nf_rev ny) => [sa sb].
rewrite [in RHS] sb T1mul_eq1 ? nf_expO // expF_eq1 // expO_eq1 T1add_eq0.
by rewrite T1mul_eq0 orFb; case pa: (x== one) => //=; case ((T1split y).2).
Qed.

Lemma exp_int a b: (\F a) ^ (\F b) = \F (a ^b%N).
Proof. by rewrite expx_nat; elim:b => // n h /=; rewrite h expnS mul_int. Qed.


Lemma exp_consCE1 (x := \F 2) (a := zero) (n := 0)(b := T1omega): 
   x ^(cons a n b) != x ^(cons a n zero) * x ^b.
Proof. done. Qed.

Lemma pow_omega x: T1nf x -> T1omega ^x = phi0 x.
Proof.
move => nx; rewrite {2}  (proj2 (nf_rev nx))  /T1exp mul_phi0;congr T1mul.
by elim (T1split x).2 => // n /= -> ;rewrite /T1omega - mul_phi0; case n.
Qed.

(** *** Existence and uniqueness of the Cantor Normal Form *)

Lemma cantor_exists a n b: T1nf (cons a n b) ->
    cons a n b = (T1omega^a) * (\F n.+1) + b.
Proof.
have eq : cons a n zero = phi0 a * \F n.+1 by case a => //.
move =>/and3P [na _ sc]; rewrite - add_to_cons // eq; congr (_ * _ + _). 
move: (proj2 (nf_rev na));set u := T1div_by_omega _;set v := (T1split a).2 => h.
rewrite /T1exp -/u -/v h mul_phi0; congr T1mul.
by elim v => // w /= <-; rewrite /T1omega - mul_phi0; case w.
Qed.

Lemma cantor_unique a n b a' n' b': 
  T1nf (cons a n b) -> T1nf (cons a' n' b') ->
  (T1omega^a) * (\F n.+1) + b = (T1omega^a') * (\F n'.+1) + b' ->
  (a=a' /\ n = n' /\ b = b').
Proof. by move => /cantor_exists <- /cantor_exists <-; case. Qed.


Lemma cantor_CE1 : T1omega ^ T1bad != phi0 T1bad.
Proof. done. Qed. 

Lemma cantorCE2: cons zero 0 T1omega != (T1omega^ zero) * (one) + T1omega.
Proof. done. Qed.

Lemma cantorCE3: cons T1bad 0 zero  != (T1omega^ T1bad) * (one) + zero.
Proof. done. Qed.


Lemma T1log_prod a b: a != zero -> b != zero ->
    T1log(a * b) = T1log a + T1log b.
Proof.
case: a b => // a1 n1 b1;case => // a2 n2 b2 _ _.
rewrite  /=; case p1: (a1==zero); case p2: (a2==zero) => //=.
  by rewrite (eqP p1) (eqP p2).
by rewrite (eqP p2) T1addn0.
Qed.

Lemma T1log_exp0 x n: T1nf x -> T1log (exp_F x n) = (T1log x) * (\F n).
Proof.
elim: n => // n h; rewrite /exp_F -/exp_F.
case xz: (x==zero); first by rewrite (eqP xz) T1mul0n //.
move => nx;rewrite T1log_prod ? expF_eq0 ? xz // h // -add1n -add_int mul_distr.
by rewrite T1muln1 // nf_log.
Qed.


Lemma T1log_exp1 z x: T1nf z -> T1nf x -> ~~ T1finite z ->
   T1log (z ^ x) = (T1log z) * x.
Proof.
move => nz nx.
case zz: (z== zero); first by rewrite (eqP zz).
move: (nf_rev nx); rewrite /T1exp.
set u := T1div_by_omega (T1split x).1; set n := (T1split x).2.
move => [nu ->]; rewrite T1log_prod ?expO_eq0 ? expF_eq0 ? zz //.
rewrite T1log_exp0 // mul_distr mulA => h; congr T1add.
rewrite /exp_O zz (negbTE h) fun_if /phi0 ifF //. 
move: h; case z => // a m b /=; case a => //.
Qed.

Lemma T1log_exp2 z u v: (z == zero) = false -> (z == one) = false -> 
   T1finite z -> T1nf u ->  T1log (z ^ (T1omega * u + \F v)) = u.
Proof.
move => z0 z1 fz nu; rewrite /T1exp.
have aux: T1log (exp_F z v) = zero.
  elim v => // n h; rewrite T1log_prod -/exp_F ? z0 ?expF_eq0 ?z0 // h.
  move: fz; case z => // a m b =>/= /eqP => -> //.
move: (nf_rev_unique v nu) => [<- <-].
by rewrite T1log_prod ?/exp_O ?expO_eq0 ?expF_eq0 ?z0 ?z1 // aux T1addn0 fz.
Qed.

Lemma exp_FO z n v: v != zero -> exp_F z n * exp_O z v = exp_O z v.
Proof.
move /negbTE => vz.
elim: n => //; first by rewrite T1mul1n.
move => n; rewrite /exp_F -/exp_F - mulA; move => ->.
rewrite /exp_O vz; case: eqP;[ by move => -> | case: eqP; first by move ->].
case fz: (T1finite z).
  move: fz; case z => // a' n'' b' /=;rewrite vz andbF => /eqP -> //.
move: fz;rewrite - mulA; case z => // a' n'' b'; rewrite /T1log.
rewrite /T1finite /phi0 {1} /T1mul T1mul_eq0 T1mul_eq0 vz => -> /=.
by rewrite add_simpl3 // vz.
Qed.

Lemma exp_FO1 z v n m: T1nf z -> T1nf v -> v != zero -> n != 0 ->
  exp_O z (v * \F n) * exp_F z m = exp_F (exp_O z v * exp_F z m) n.
Proof.
move => nz nv vz; case: n => // n _. 
elim: n => //; first by rewrite {2} /exp_F - mulA !T1muln1 // nf_expF //.
move => n; rewrite /exp_F -/exp_F => <-.
rewrite - mulA (mulA (exp_F z m )) exp_FO ? T1mul_eq0 //? (negbTE vz) //.
by rewrite mulA expO_add -(add1n) - add_int mul_distr T1muln1.
Qed.


Lemma exp_FO2 z m u: T1nf z -> m != 0 ->  exp_O (exp_F z m) u = exp_O z u.
Proof.
move => nz; case: m => // n _.
rewrite /exp_O expF_eq0 andbT expF_eq1 /exp_F -/exp_F //.
case pu: (u==zero); first by rewrite (eqP pu) !T1muln0 !if_same.
case pa: (z== zero); first by rewrite (eqP pa) T1mul0n.
case pb: (z== one); first by rewrite (eqP pb) expF_1n /=.
have h: forall t, T1finite t = (T1log t == zero) by case. 
rewrite h h (T1log_exp0 (n.+1) nz) T1mul_eq0 ! orbF //.
case pc: (T1log z == zero) => //. 
by rewrite - 3!mulA (mulA (\F _)); rewrite mul_fin_omega.
Qed.

Lemma exp_FO3 z x u (w := T1div_by_omega (T1split x).1):
   T1nf z -> T1nf w -> (w == zero) = false -> (z == zero) = false ->
  exp_O (z ^ x) u = phi0( T1log (z ^x) * T1omega * u).
Proof.
move => nz nw xnz zz.
case zo: (z== one); first by rewrite (eqP zo) exp1x T1mul0n.
case uz: (u==zero); first by rewrite (eqP uz) T1muln0 expO_n0.
rewrite /T1exp /exp_O -/w; set m:= (T1split x).2.
set a := (if T1finite z then phi0 w else _).
have na: T1nf a by rewrite fun_if !nf_phi0 !nf_mul // ? nf_log // nw if_same.
have ifa: ~~ T1finite a.
  rewrite /a; case fz:(T1finite z) => //; first by rewrite /= xnz.
  move: fz; case z => // a' n' b' /=; case a' => // a'' n'' b'' _.
  by rewrite andbF T1mul_eq0 xnz.
have ifp: T1finite (a * exp_F z m) = false.
  have : exp_F z m != zero by rewrite expF_eq0 zz.
  move: ifa; case a => // a' n' b' /=; case (exp_F z m)=> // a'' n'' b'' /=.
  by move=> /negbTE h _;case sa:(a'' == zero); rewrite h andFb /= ?T1add_eq0 h.
case az: (a== zero); first by move: ifa; rewrite (eqP az).
case ao: (a== one); first by move: ifa; rewrite (eqP ao).
by rewrite zz zo uz T1mul_eq0 expF_eq0 zz andFb T1mul_eq1//az ao orbF andFb ifp.
Qed.

(** *** Basic Properties *)


Lemma exp_sum x y z: T1nf x -> T1nf y -> z ^(x+y)  = z ^x * z ^y.
Proof.
move => nx ny; rewrite /T1exp.
move: (nf_rev_sum nx ny); case: eqP; move => h [-> ->].
  by rewrite h expO_n0 T1mul1n - mulA expF_add.
by rewrite -mulA (mulA (exp_F z _)) exp_FO ? mulA ? expO_add //; apply/eqP.
Qed.

Lemma exp_prod x y z: T1nf z -> T1nf x -> T1nf y -> z ^(x *y)  = (z ^x) ^y.
Proof.
move => nz nx ny.
move:(nf_rev_prod nx ny). rewrite {1 2} /T1exp.
set u := T1div_by_omega (T1split y).1; set n :=  (T1split y).2.
set v := T1div_by_omega (T1split x).1; set m :=  (T1split x).2.
set w := T1div_by_omega (T1split (x*y)).1; set p :=  (T1split (x* y)).2. 
move:(nf_rev nx); rewrite -/v -/m; move => [nv xv].
case z1: (z== one); first by rewrite (eqP z1) exp1x !expO_1n !expF_1n.
case vz: (v== zero).
  have ->: x = \F m by move: xv; rewrite  (eqP vz) T1muln0.
  case mz: (m==0).
    by move => [-> ->]; rewrite (eqP mz) expx0 expO_n0 expO_1n expF_1n.
  by move => [-> ->]; rewrite expx_nat expF_mul exp_FO2 // mz.
move => H.
have ->: w = v * T1omega * u + v * \F n.
  by move:H;case h: (n== 0); move => [-> _] //;rewrite (eqP h) T1muln0 T1addn0.
have ->: exp_F (z ^ x) n = (exp_O z (v * \F n) * exp_F z p).
  move: H; case h: (n== 0); move => [_ ->].
      by rewrite (eqP h) T1muln0 expO_n0.
   rewrite /T1exp -/v -/m exp_FO1 ? vz ? h//. 
case uz: (u== zero); first  by rewrite (eqP uz) !T1muln0 expO_n0 T1mul1n.
have xnz: x != zero by rewrite xv T1add_eq0 T1mul_eq0 vz orFb andFb.
case z0: (z==zero).
   rewrite (eqP z0) (exp0nz xnz) /exp_O eqxx uz T1mul0n T1add_eq0 !T1mul_eq0.
   by rewrite uz vz T1mul0n.
rewrite mulA; congr T1mul; rewrite (exp_FO3 u nz nv vz z0).
case fz: (T1finite z). 
  by rewrite /exp_O z0 z1 fz xv T1log_exp2 //mul_phi0.
have ez: forall w, exp_O z w = phi0 (T1log z * T1omega * w).
  by move => t ;rewrite /exp_O; move: fz;case z => // a k b; case a.   
rewrite ez ez - mul_phi0 T1log_exp1 ? fz// - !mulA.
by rewrite -!mul_distr (mulA x) xv mul_sum_omega ? vz // -!mulA -!mul_distr.
Qed.

Lemma pow_mon1 x y z: T1nf x -> T1nf y -> T1nf z -> x != zero ->
   y <= z -> x ^y <= x ^z.
Proof.
move => nx ny nz xnz yz.
rewrite (sub_pr1 nz yz) exp_sum // ? nf_sub // T1le_pmulr // ? nf_exp //.
by rewrite exp_eq0 (negbTE xnz).
Qed.

Lemma pow_mon2 x y z: T1nf x -> T1nf y -> T1nf z -> x != zero ->  x != one ->
   y < z -> x ^y < x ^z.
Proof.
move => nx ny nz xnz xn1 yz.
have na := (nf_exp nx (nf_sub nz ny)).
have nb: x ^ y != zero by rewrite exp_eq0  (negbTE xnz).
have nc: x ^ (z - y) != zero by rewrite exp_eq0  (negbTE xnz).
rewrite (sub_pr1 nz (T1ltW yz)) exp_sum // ? nf_sub //. 
rewrite - {1}(T1muln1 (nf_exp nx ny)) T1lt_mul2l// T1lt_neAle eq_sym.
by rewrite exp_eq1  ? nf_sub // (negbTE xn1) (sub_nz nz yz) T1ge1 nc.
Qed.

(* deplaccer *)
Lemma T1le_pmull x a: x != zero -> a <= x * a.
Proof. rewrite - {1} (T1mul1n a) - T1ge1; apply: T1le_mul2r. Qed.

Lemma pow_mon3 x y z: T1nf x ->  x <= y -> x ^z <= y ^z.
Proof.
move => nx xy.
have sa: forall n, T1nf (exp_F x n) by move =>  n;rewrite nf_expF.
rewrite /T1exp; apply: T1le_mul => //; last first.
  elim (T1split z).2; first by rewrite T1lenn.
  by move => n; rewrite /exp_F -/exp_F => h; apply:T1le_mul.
set w := (T1div_by_omega (T1split z).1).
rewrite /exp_O.
case xz: (x== zero).
   case wz: (w== zero); first by rewrite (eqP wz) !T1muln0 !if_same T1lenn.
   by rewrite (eqP xz) T1le0n.
case yz: (y== zero); first by move:xy; rewrite (eqP yz) T1len0 xz.
case xo: (x== one).
   rewrite T1ge1; case (y== one) => //; case (T1finite y) => //.
case yo: (y== one).
  by move: xy; rewrite (eqP yo); rewrite  T1le_eqVlt xo T1lt1 xz.
case fx: (T1finite x).
  case y => // a n b /=; case a => // a' n' b' /=. 
  by rewrite andbF phi0_le T1le_pmull.
case fy: (T1finite y).
  move: xy fx fy; case x => // a n b; case a => // a' n' b' /=.
  by case y => // a'' n'' b'' //; case a''.
rewrite phi0_le; apply: T1le_mul2r; apply: T1le_mul2r.
move: xy; case x => //; first by rewrite !T1le0n.
by move => a n b; case y => // a' n' b' /=; exact: T1le_cons_le.
Qed.


End CantorOrdinal.

Export CantorOrdinal.

(** * The type T2 *)

Module Gamma0.

(** ** Definition and Equality *)

(** This is like T1 with one more argument *)

Inductive T2 : Set :=
  zero : T2
| cons : T2 -> T2  -> nat -> T2 -> T2.

Declare Scope g0_scope.
Delimit Scope g0_scope with g0.
Open Scope g0_scope.


Fixpoint T2eq x y {struct x} :=
  match x, y with 
  | zero, zero  => true
  | cons a b n c, cons a' b' n' c' => 
      [&& T2eq a a', T2eq b b',  n== n' & T2eq c c' ] 
  | _, _ => false
end.

Lemma T2eqP : Equality.axiom T2eq.
Proof.
move=> x y; apply: (iffP idP) => [|<-].
  elim: x y; first by case  => [ // | a b n d//].
  by move => a H1 b H2 n d H4;case => // a' b' n' d'
    /= /andP [/H1 ->]  /andP [/H2 ->]   /andP [/eqP -> /H4 ->].
by elim: x => // a Ha b Hb n d Hd; rewrite /= Ha Hb Hd eqxx.
Qed.


Canonical T2_eqMixin := EqMixin T2eqP.
Canonical T2_eqType := Eval hnf in EqType T2 T2_eqMixin.

Arguments T2eqP {x y}.
Prenex Implicits T2eqP.

Lemma T2eqE a b n d a' b' n' d':
  (cons a b n d == cons a' b' n' d') = 
      [&& a == a', b == b', n== n' & d == d' ].
Proof. by []. Qed.

(**  We write [psi a b] instead of [cons a b 0 0]; we introduce omega and 
epsilon0. We consider also the size, this is really the depth of the object *)

Notation "[ x , y ]" := (cons x y 0 zero) (at level 0) :g0_scope.


Definition T2nat p := if p is n.+1 then cons zero zero n zero else zero.


Notation "\F n" := (T2nat n)(at level 29) : g0_scope.

Definition psi a b  := [a, b].

Definition one := [zero, zero].

Definition omega  := [zero, one].

Definition epsilon0  := [one,zero].

Fixpoint T1T2 (c: T1) : T2 :=
  if c is CantorOrdinal.cons a n b then cons zero (T1T2 a) n (T1T2 b)
  else zero.



Fixpoint size x :=
  if x is cons a b n c then 
     (maxn (size a) (maxn (size b) (size c))).+1
  else 0.

Lemma size_prop1 a b n c (l:= size (cons a b n c)):
   [/\ size a < l, size b < l, size c < l & size [a, b] <= l]%N.
Proof. 
rewrite /= !ltnS leq_maxl maxnCA leq_maxl maxnC - maxnA maxnC - maxnA leq_maxl. 
by rewrite -/size maxn0 maxnC leq_maxr.
Qed.

Lemma size_prop a b n c a' b' n' c' 
   (l := (size (cons a b n c) + size (cons a' b' n' c'))%N) :
   (size c + size c' < l)%N /\ (size [a, b] + size b' < l)%N /\
   (size a' + size a < l)%N /\ (size b + size b' < l)%N /\
   (size b + size [a', b'] < l)%N /\ (size a + size a' < l)%N.
Proof.
move: (size_prop1 a b n c) => [pa pb pc pd].
move: (size_prop1 a' b' n' c') => [pa' pb' pc' pd'].
rewrite (ltn_add_ll pc pc') (ltn_add_ll pb pb') (ltn_add_el pd pb'). 
by rewrite (ltn_add_le pb pd') (addnC (size a')) (ltn_add_ll pa pa').
Qed.

(** ** Order *)
(** Comparing ordinals is complicated. We are looking for the fixpoint of 
some complicated expression [F(a,b)], in which the psi-parts of [a] and [b] 
appear as arguments of [F]. Thus, a definition by induction is impossible. 
However if [l] is the some of the size if the arguments of [F], then all calls 
of [F] have a smaller value. Thus, we use a definition by induction on [l].
All proofs will be by induction on [l] as well.
*)


Definition lt_rec f x y :=
 if x is cons a b n c then
   if y is cons a' b' n' c' then
     if (  ((f a a')  && (f b ([a', b'])))
         || ((a == a') && (f b b'))
         || ((f a' a)  && (f ([a, b]) b'))
         || (((f a' a)  && ([a, b] == b'))))
     then true
     else if ((a== a') && (b==b')) then
       if (n < n')%N then true 
       else if (n == n') then  (f c c') else false
       else false 
   else false 
 else if y is cons a' b' n' c' then true else false.

Fixpoint T2lta k:=
 if k is k.+1 then lt_rec (T2lta k) else fun x y => false.


Definition T2lt a b :=  T2lta ((size a) + size b).+1 a b.
Definition T2le (x y :T2) := (x == y) || (T2lt x y).
Notation "x < y" := (T2lt x y) : g0_scope.
Notation "x <= y" := (T2le x y) : g0_scope.
Notation "x >= y" := (y <= x) (only parsing) : g0_scope.
Notation "x > y"  := (y < x) (only parsing)  : g0_scope.

(** Main result: Our comparison is a fix-point *)

Lemma T2ltE x y : x < y  = lt_rec T2lt x y.
Proof.
have aux: forall n x y, 
     ((size x + size y) < n)%N -> T2lta n x y = (x < y).
   clear x y;move => n; elim: n {1 3 4} n (leqnn n); first by case.
  move => k0 Hrec; case => // k1; rewrite ltnS => k1k0.
  case => // a b n c; case => // a' b' n' c'.
  rewrite /T2lt; set l := addn _ _; rewrite ltnS => e3.
  move: (leq_trans e3 k1k0) => e4.
  move: (size_prop a b n c a' b' n' c').
  rewrite -/l;move => [pa [pb [pc [pd [pe pf]]]]].
  rewrite /T2lta /lt_rec -/lt_rec  -/T2lta. 
  by rewrite ! Hrec //; apply:(leq_trans _ e3).
case x => // a b n c; case:y => // a' b' n' c'.
move: (size_prop a b n c a' b' n' c') => [pa [pb [pc [pd [pe pf]]]]].
by rewrite  /lt_rec {1} /T2lt /T2lta -/T2lta {1} /lt_rec -/lt_rec !aux.
Qed.


(** This is how we compare two psi-terms *)
Definition lt_psi  a b a' b':=
      ((a < a')  && (b < [a', b']))
   || ((a == a') && (b < b'))
   || ((a' < a)  && ([a, b] < b'))
   || ((a' < a)  && ([a, b] == b')).

Lemma T2lt_psi a b a' b': [a,b] < [a', b'] = lt_psi a b a' b'.
Proof. by rewrite {1} T2ltE /lt_rec ltnn if_same if_simpl.  Qed.

Lemma T2lt_consE a b n c a' b' n' c' : 
   cons a b n c < cons a' b' n' c' =
     if (lt_psi a b a' b') then true
     else if ((a== a') && (b==b')) then
       if (n < n')%N then true 
       else if (n == n') then  (c < c') else false
       else false. 
Proof. by rewrite {1} T2ltE. Qed.

(** Less-or-equal *)

Lemma T2le_consE a b n c a' b' n' c' : 
   cons a b n c <= cons a' b' n' c' =
     if (lt_psi a b a' b') then true
     else if ((a== a') && (b==b')) then
       if (n < n')%N then true 
       else if (n == n') then  (c <= c') else false
       else false. 
Proof. 
rewrite /T2le T2lt_consE.
case pa: (lt_psi a b a' b'); first by rewrite orbT.
rewrite T2eqE; case pb: (a==a') => //; case pc: (b==b') => //=.
case (ltngtP n n') => //.
Qed.

Lemma T2ltn0 x: (x < zero) = false.         Proof. by case: x. Qed.
Lemma T2lt0n x: (zero < x) = (x != zero).   Proof. by case: x. Qed.
Lemma T2le0n x: zero <= x.                  Proof. by case: x. Qed.
Lemma T2len0 x: (x <= zero) = (x == zero).  Proof. by case: x. Qed.
Lemma omega_lt_epsilon0: omega < epsilon0.  Proof. by []. Qed.

Lemma T2ltnn x: (x < x) = false.
Proof. 
elim: x => // a Ha b Hb n c Hc.
by rewrite T2lt_consE /lt_psi Ha Hb Hc ltnn !if_same !andbF.
Qed.

Lemma T2lt_ne a b : a < b -> (a == b) = false.
Proof. by case h: (a== b) => //; rewrite (eqP h) T2ltnn. Qed.

Lemma T2lt_ne' a b : a < b -> (b == a) = false.
Proof. rewrite eq_sym; apply /T2lt_ne. Qed.

Lemma T2ltW a b : (a < b) -> (a <= b). 
Proof. by rewrite /T2le => ->; rewrite orbT. Qed.

Lemma T2le_eqVlt a b : (a <= b) = (a == b) || (a < b).
Proof. by []. Qed.

Lemma T2lt_neAle a b : (a < b) = (a != b) && (a <= b).
Proof.  
by rewrite T2le_eqVlt; case h: (a < b);[ rewrite (T2lt_ne h) | case(a==b) ].
Qed.

Lemma T2lenn x: x <= x.   
Proof. by rewrite /T2le eqxx. Qed.

#[local] Hint Resolve T2lenn : core.


Lemma T2ge1 x:  (one <= x) = (x != zero).
Proof. case: x  => // [] // [] // [] // []  // [] //. Qed.

Lemma T2lt1 x: (x < one) = (x==zero).
Proof.  by case: x  => // [] // [] // [] // []  // [] . Qed.

Lemma T2nat_inc n p : (n < p)%N = (\F n < \F p).
Proof.
case: p => //; first by rewrite T2ltn0 ltn0.
by case: n => // n p //=; rewrite ltnS T2lt_consE if_same if_simpl. 
Qed.

Lemma psi_lt1 a b c  n a' b':
   cons a b n c < [a', b'] = ([a, b] < [a', b']).
Proof. by rewrite  T2lt_consE T2lt_psi T2ltn0 ! if_same if_simpl. Qed.


Lemma psi_lt2 a b n c n' c':  cons a b n' c' < cons a b n c = 
   (if (n' < n)%N then true else if n' == n then c' < c else false).
Proof. by rewrite T2lt_consE -T2lt_psi T2ltnn !eqxx. Qed.

Lemma T1T2_inj n p : (n == p) = (T1T2 n == T1T2 p).
Proof.
elim: n p => //; first by case.
move => a Ha n b  Hb [] // a' n' b' /=.
by rewrite T1eqE T2eqE - Ha - Hb eqxx.
Qed.


Lemma T1T2_inc n p : (n < p)%ca = (T1T2 n < T1T2 p)%g0.
Proof.
elim: n p => // [ [] // | a Ha n b Hb [] // a' n' b' /=].
rewrite T2lt_consE /lt_psi eqxx T2ltnn /= Ha Hb - T1T2_inj. 
by case pa:  (T1T2 a < T1T2 a').
Qed.

(** First two non-trivial results *)

Lemma T2lt_anti b a: a < b -> (b < a) = false.
Proof.
set n := (size a + size b).+1.
move: (leqnn n); rewrite {1}/n; move: n => n.
elim: n a b; first by move  => a b //;rewrite ltn0.
move => m Hrec a b; rewrite ltnS.
case: a b => [ [] // | a b n c [] // a' b' n' c'].
set l:= (size (cons a b n c) + size (cons a' b' n' c'))%N => lm.
have Hr : forall a b, (size a + size b < l)%N -> a < b -> (b < a) = false.
  by move => u v ll; apply: Hrec; apply: (leq_trans ll lm).
move: (size_prop a b n c a' b' n' c'); rewrite -/l.
move => [pa [pb [pc [pd [pe pf]]]]].
rewrite  !T2lt_consE /lt_psi.
case qa: (a < a').
  rewrite (Hr a a' pf qa) (T2lt_ne qa) (T2lt_ne' qa) !andFb /= !orbF !if_simpl. 
  by move => qc;rewrite (T2lt_ne' qc) (Hr _ _ pe qc).
case qa': (a' < a).
   rewrite (T2lt_ne qa') (T2lt_ne' qa') /= !orbF !if_simpl; case /orP.
      exact/(Hr _ _ pb).
   by move /eqP ->; rewrite T2ltnn.
rewrite /= !orbF (eq_sym a' a) (eq_sym b' b) (eq_sym n' n).
case: eqP => //= _.
case qb: (b < b'); first by rewrite (Hr b b' pd qb) (T2lt_ne qb).
case qb': (b' < b); first by rewrite (T2lt_ne' qb').
by case: eqP => //= _;case: (ltngtP n n') => // _; apply: Hr.
Qed.

Lemma T2lt_trichotomy a b: [|| (a< b), (a==b) | (b < a)].
Proof.
set n := (size a + size b).+1.
move: (leqnn n); rewrite {1}/n; move: n.
move => n; elim: n a b; first by move  => a b //;rewrite ltn0.
move => m Hrec a b; rewrite ltnS.
case: a b => [ [] // | a b n c [] // a' b' n' c'].
set l:= (size (cons a b n c) + size (cons a' b' n' c'))%N => lm.
have Hr : forall a b , (size a + size b < l)%N ->
    [|| (a< b), (a==b) | (b < a)]
  by move => u v ll; apply: Hrec; apply: (leq_trans ll lm).
move: (size_prop a b n c a' b' n' c'); rewrite -/l.
move => [pa [pb [pc [pd [pe pf]]]]].
rewrite !T2lt_consE /lt_psi.
case /or3P:(Hr _ _ pf) => caa'; last 1 first.
+ rewrite caa' (T2lt_anti caa') (T2lt_ne caa') (T2lt_ne' caa') !orbF !if_simpl.
  by case /or3P: (Hr _ _ pb) => -> //; rewrite !orbT //.
+ rewrite caa' (T2lt_anti caa') (T2lt_ne caa')(T2lt_ne' caa') !orbF !if_simpl.
  by rewrite /= (eq_sym _ b); case /or3P: (Hr _ _ pe) => -> //; rewrite !orbT.
+ rewrite caa' (eqP caa') T2ltnn eqxx /= !orbF.
  case /or3P:(Hr _ _ pd) => cbb'; last 1 first.
  * by rewrite cbb' (T2lt_anti cbb') (T2lt_ne' cbb') ! orbT.
  * by rewrite cbb'.
  * rewrite (eqP cbb') T2ltnn eqxx; case: (ltngtP n n') => //; rewrite ?orbT //.
    move => ->; case /or3P:(Hr _ _ pa) => cc; rewrite   ? cc ?orbT //.
    by rewrite (eqP cc) eqxx orbT.
Qed.

(** what follows is the same as for T1 *)

Lemma T2leNgt a b:  (a <= b) = ~~ (b < a).
Proof.
case /or3P: (T2lt_trichotomy a b).
- by move => h; rewrite (T2lt_anti h) (T2ltW h).
- by move /eqP ->; rewrite T2ltnn T2lenn.
- by move => h; rewrite h /T2le (T2lt_anti h) (T2lt_ne' h).
Qed.

Lemma T2ltNge a b:  (a < b) = ~~ (b <= a).
Proof. by rewrite T2leNgt negbK. Qed.

Lemma T2eq_le m n : (m == n) = ((m <= n) && (n <= m)).
Proof.
rewrite /T2le (eq_sym n m);case eqmn: (m == n) => //=.
by case lt1: (m < n) => //; rewrite (T2lt_anti lt1).
Qed.

Lemma T2le_total m n : (m <= n) || (n <= m).
Proof. 
by rewrite /T2le;case /or3P: (T2lt_trichotomy m n) => -> //; rewrite !orbT.
Qed.


CoInductive T2ltn_xor_geq m n : bool -> bool -> Set :=
  | T2LtnNotGeq of m < n  : T2ltn_xor_geq m n false true
  | T2GeqNotLtn of n <= m : T2ltn_xor_geq m n true false.

CoInductive T2leq_xor_gtn m n : bool -> bool -> Set :=
  | T2GeqNotGtn of m <= n : T2leq_xor_gtn m n true false
  | T2GtnNotLeq of n < m  : T2leq_xor_gtn m n false true.


CoInductive compare_T2 m n : bool -> bool -> bool -> Set :=
  | CompareT2Lt of m < n : compare_T2 m n true false false
  | CompareT2Gt of m > n : compare_T2 m n false true false
  | CompareT2Eq of m = n : compare_T2 m n false false true.


Lemma T2leP x y : T2leq_xor_gtn x y (x <= y) (y < x).
Proof.
by rewrite T2ltNge; case le_xy: (x <= y); constructor;rewrite // T2ltNge le_xy.
Qed.

Lemma T2ltP m n : T2ltn_xor_geq m n (n <= m) (m < n).
Proof. by case T2leP; constructor. Qed.

Lemma T2ltgtP m n : compare_T2 m n (m < n) (n < m) (m == n).
Proof.
rewrite T2lt_neAle T2eq_le;case: T2ltP; first by constructor.
by rewrite T2le_eqVlt orbC; case: T2leP; constructor; first exact /eqP.
Qed.

Lemma T2lt_psi_aux a b a' b': a < a' -> b < [a', b'] -> [a,b] < [a',b'].
Proof. by move => sa sb; rewrite T2ltE /lt_rec sa sb. Qed.

Lemma T2gt1 x: (one < x) = ((x != zero) && (x != one)).
Proof.
case: (T2ltgtP x one); rewrite ? andbT ? andbF //; last by case: x.
by rewrite T2lt1 => ->.
Qed.

(** Second non-trivial result *)

Theorem T2lt_trans b a c: a < b -> b < c -> a < c.
Proof.
set n := (size a + size b + size c).+1.
move: (leqnn n); rewrite {1}/n; move: n.
move => n; elim: n a b c; first by move  => a b c//;rewrite ltn0.
move => m Hrec []; first by case; [rewrite T2ltn0 | move => a' b' n' c'; case].
move => a b n c []; [ by rewrite T2ltn0 | move => a' b' n' c' ].
case; [ by rewrite T2ltn0 | move => a'' b'' n'' c'']; rewrite ltnS => la.
have Hr1: forall u v w, (size u < size (cons a b n c))%N -> 
  (size v <= size (cons a' b' n' c'))%N -> 
  (size w <= size (cons a'' b'' n'' c''))%N -> u < v -> v < w -> u < w.
  move => u v w sa sb sc; apply: Hrec; apply: leq_trans la.
  by rewrite ltn_add_le // ltn_add_le.
move: (size_prop1 a b n c) => [pa pb pc pd].
move: (size_prop1 a' b' n' c') => [pa' pb' pc' pd'].
move: (size_prop1 a'' b'' n'' c'') => [pa'' pb'' pc'' pd''].
rewrite  !T2lt_consE /lt_psi.
case (T2ltgtP a a') => qa.
+ rewrite /= !orbF if_simpl => lx.
  case (T2ltgtP a' a'') => qb.
  - rewrite andTb !orbF if_simpl => qc.
    rewrite (Hr1 _ _ _ pb pd' pd'' lx (T2lt_psi_aux qb qc)).
    by rewrite (Hr1 a a' a'' pa (ltnW pa') (ltnW pa'') qa qb).
  - case (T2ltgtP a a'') => qc.
     * rewrite /=  !orbF !if_simpl => qd; apply:(Hr1 _ _ _ pb pd' pd'' lx).
       by rewrite T2lt_psi /lt_psi qb (T2lt_anti qb) (T2lt_ne' qb) /=.
     * rewrite /= !if_simpl => qd.
       move: (T2lt_psi_aux qa lx) => ha.
       apply: ifT; case /orP: qd => h; last by rewrite - (eqP h).   
       apply: (Hrec [a, b] [a', b'] b'') => //;apply: leq_trans la.
       by rewrite ltn_add_el // leq_add.
     * rewrite /= !orbF if_simpl; case /orP; last by move/eqP <-; rewrite lx.
       by move => qd; rewrite  (Hr1 _ _ _ pb pd' (ltnW pb'') lx qd).
  - rewrite - qb qa (T2lt_ne qa) (T2lt_anti qa) /= !orbF !if_simpl.
    case (T2ltgtP b' b'') => h //=; [move => _; rewrite qb | by rewrite - h].
    apply: (Hr1 _ _ _ pb pd' pd'' lx). 
    by rewrite T2lt_psi /lt_psi qb h eqxx orbT.
+ case (T2ltgtP a' a'') => qb.
  - rewrite /= !orbF !if_simpl => sa sb; rewrite ifT//.
    rewrite -/(lt_psi a b a'' b'') -(T2lt_psi a b a'' b''). 
    case/orP:sa => h; last by rewrite  (eqP h).
    apply: (Hrec [a,b] b' [a'',b'']) => //; apply: leq_trans la.
    by rewrite ltn_add_le // ltn_add_el.
  - have qc: (a'' < a). 
      apply: (Hrec a'' a' a) => //; apply: leq_trans la.
      rewrite addnAC -addnA addnC ltn_add_ll// ltn_add_ll//.
    rewrite /= qc (T2lt_anti qc) (T2lt_ne' qc) /= !if_simpl => r1 r2.
    have sa:([a,b] < [a',b']) by rewrite T2lt_psi /lt_psi qa /= -!orbA r1 !orbT.
    apply: ifT;case /orP: r2 => h; last by rewrite - (eqP h).
    apply: (Hrec [a, b] [a', b'] b'') => //;apply: leq_trans la.
    by rewrite ltn_add_el // leq_add.
  - rewrite - qb qa (T2lt_anti qa)  (T2lt_ne' qa) /= ? if_simpl.
    case (T2ltgtP b' b'') => qc // sa sb; last by rewrite - qc.
    apply: ifT; case /orP: sa => h; last  by rewrite (eqP h).
    apply: (Hrec [a,b] b' b'') => //; apply: leq_trans la.
    by rewrite ltn_add_ll // ltn_add_el.
+ rewrite -qa /= !orbF; case (T2ltgtP b b') => qb //; last first.
  - rewrite - qb; case (T2ltgtP a a'') => qc //=;case (T2ltgtP b b'') => //= _.
    case: (ltngtP n n')=> //;case:(ltngtP n' n'') => //.
    * by move => sa sb; rewrite (ltn_trans  sb sa).
    * by move => -> ->.
    * by move => h ->; rewrite h.
    * move => -> -> sa sb; rewrite (Hr1 _ _ _ pc (ltnW pc') (ltnW pc'') sa sb).
      by rewrite ltnn eqxx.
  - move => _; case (T2ltgtP a a'') => qc /=; rewrite ?orbF ? if_simpl.
    * exact: (Hr1 _ _ _ pb (ltnW pb') pd'' qb).
    * have h: [a, b] < [a, b'] by rewrite T2lt_psi /lt_psi eqxx qb !orbT.
      move => h1;apply: ifT; case /orP: h1 => h2; last by rewrite - (eqP h2).
      apply: (Hrec [a, b] [a, b'] b'') => //;apply: leq_trans la.
      rewrite ltn_add_el // {2} qa leq_add //.
    * case (T2ltgtP b  b'') => // h.
       have hh:(size b'' + size b + size b' < m)%N.
         by apply: leq_trans la; rewrite -addnA addnC ltn_add_ll// ltn_add_ll//.
       move: (Hrec b'' b b' hh h qb) => s.
       by rewrite (T2lt_anti s) (T2lt_ne' s).
     by rewrite -h (T2lt_anti qb) (T2lt_ne' qb).
Qed.

Lemma T2lt_le_trans b a c: a < b -> b <= c -> a < c.
Proof.
by move => lab; case /orP;[ move /eqP => <- | apply:T2lt_trans].
Qed.

Lemma T2le_lt_trans b a c: a <= b -> b < c -> a < c.
Proof. by case /orP;[  move /eqP => <- |apply:T2lt_trans]. Qed.

Lemma T2le_trans b a c: a <= b -> b <= c -> a <= c.
Proof.
case /orP; first by move /eqP => ->. 
by move => l1 l2; rewrite /T2le (T2lt_le_trans l1 l2) orbT.
Qed.

Lemma T2le_psi1 a b n c: [a, b] <= cons a b n c.
Proof. by rewrite T2le_consE /lt_psi ! T2ltnn !eqxx // T2le0n /=; case: n. Qed.

Lemma T2lt_psi_b a b: b < [a,b].
Proof.
elim: b a => // a _ b Hb n c _ x.
have ha:= (T2le_psi1 a b n c).
have hb:= (T2lt_le_trans (Hb a) ha).
rewrite T2lt_consE /lt_psi; case: (T2ltgtP a x).
+ rewrite /= !orbF if_simpl => ax.
  by apply: (T2lt_trans (Hb x)); rewrite T2lt_consE /lt_psi hb eqxx !orbT.
+ by move => _ /=; rewrite orbC -/(T2le _ _) ha.
+ by move => _ /=; rewrite hb.
Qed.


Lemma T2lt_psi_a a b: a < [a,b].
Proof.
elim: a b => //a Ha b Hb n c _ x.
have ha:= (T2lt_le_trans (Ha b) (T2le_psi1 a b n c)).
have hb:= (T2lt_le_trans (T2lt_psi_b a b)(T2le_psi1 a b n c)).
have hc :[b,x] < [cons a b n c, x] by rewrite T2lt_consE /lt_psi hb T2lt_psi_b.
by rewrite T2lt_consE /lt_psi ha (T2lt_trans (Hb x) hc).
Qed.

(** ** Normal form *)
(** Same as in T1.
TODO:: show that compraison is well-founded for NF
 *)


Fixpoint T2nf x :=
  if x is cons a b n c then [&& T2nf a, T2nf b, T2nf c & c < [a,b] ]
  else true.

Lemma T2nf_cons_cons a b n a' b' n' c':
  T2nf(cons a b n (cons a' b' n' c')) = 
   [&& [a', b'] < [a, b], T2nf a, T2nf b & T2nf(cons a' b' n' c') ].
Proof. 
simpl;case: (T2nf a);rewrite /= ?andbF //.
case: (T2nf b);rewrite /= ? andbF //.
rewrite T2lt_consE - T2lt_psi.
by case: ([a', b'] < [a, b]); rewrite /= ?andbT //  T2ltn0 !if_same andbF.
Qed.

Lemma nf_psi a b n: T2nf (cons a b n zero) = T2nf a && T2nf b.
Proof. by rewrite  /= T2lt0n andbT. Qed.

Lemma T2nf_consE a b n c:
    T2nf (cons a b n c) = [&& T2nf a, T2nf b, T2nf c & c < [a,b] ].
Proof. by []. Qed.

Lemma nf_omega : T2nf omega.             Proof. by []. Qed.
Lemma nf_one : T2nf one.                 Proof. by []. Qed.
Lemma nf_finite n: T2nf (\F n).          Proof. by case:n. Qed.


(** ** Successor and predecessor *)
(** Same as for T1 *)

Lemma lt_tail a b n c: T2nf (cons a b n c) ->  c < cons a b n c.
Proof. 
move /and4P => [_ _ _ h]; apply: (T2lt_le_trans h (T2le_psi1 a b n c)).
Qed.

Lemma T1T2range1 x: T1T2 x < epsilon0.
Proof. by elim: x => // a Ha n b _ /=; rewrite T2lt_consE /lt_psi /= Ha. Qed.

Lemma T1T2range2 x: T2nf x -> x < epsilon0 -> {y: T1 | x = T1T2 y}.  
Proof. 
elim: x => //; first by exists CantorOrdinal.zero.
move => a _ b Hb n c Hc /= /and4P [na nb nc nd].
rewrite T2lt_consE /lt_psi !T2ltn0 /= !if_same T2lt1 /= !andbF !orbF if_simpl.
move => h; move: h nd => /andP[/eqP -> /(Hb nb)] [y1 ->] hh.
have aux:[zero, T1T2 y1] < epsilon0 by rewrite T2lt_psi /lt_psi /= T1T2range1.
have [y2 -> ] := (Hc nc (T2lt_trans hh aux)).
by exists (CantorOrdinal.cons y1 n y2). 
Qed.

Definition T2finite x:=
  if x is cons a b n c then ([a,b]==one) else true.

Fixpoint T2limit x := 
  if x is cons a b n c then 
    if ([a,b]==one) then false else (c== zero) || T2limit c
  else false.

Fixpoint T2split x:=
 if x is cons a b n c then
      if  ([a,b]==one)  then (zero, n.+1) else
     let: (x, y) := T2split c in (cons a b n x,y)
   else (zero,0).

Lemma T2nf_finite a b n c: [a,b]==one -> T2nf (cons a b n c) -> c = zero.
Proof.
by move => /eqP [-> ->] /and4P [_ _ _]; rewrite T2lt1 => /eqP.
Qed.

Lemma split_finite x: ((T2split x).1 == zero) = T2finite x.
Proof.
case x => // a b n c //=.  
by case pa: ([a, b] == one) => //;case: T2split x.
Qed.

Lemma T2finite2 x: T2finite x -> T2nf x -> x = \F ((T2split x).2).
Proof. 
case: x => // a b n c; rewrite /T2finite => sa sb.
rewrite (T2nf_finite sa sb) /T2split -/T2split sa.
by move: sa => /eqP [] -> ->. 
Qed.


Lemma omega_least_inf1 x: T2finite x -> x < omega.
Proof.
case: x => // a b n c /= /eqP [] -> ->.
by rewrite /omega T2lt_consE /lt_psi.
Qed.

Lemma omega_least_inf2 x: ~~ T2finite x -> omega <= x.
Proof.
case: x => // a b n c.
rewrite /omega T2le_consE /= /lt_psi !T2lt0n !T2ltn0 /= !T2gt1 => eq1.
rewrite eq1; move:eq1; rewrite T2eqE !orbF /= !andbT (eq_sym a zero).
case pa: (zero==a) => //= -> /=; rewrite (eq_sym b); case: (one==b) => //.
by rewrite T2le0n; case: n.
Qed.

Lemma split_limit x: ((T2split x).2 == 0) = ((x==zero) || T2limit x). 
Proof.  
elim: x => // a _ b _ n c Hc /=.
case: ([a, b] == one) => //; rewrite - Hc; by case: (T2split c).
Qed.

Fixpoint T2is_succ x := 
  if x is cons a b n c then ([a,b]==one) || T2is_succ c else false.

Fixpoint T2succ x :=
  if x is cons a b n c
     then if ([a,b]==one) then \F n.+2  else cons a b n (T2succ c)
  else one.

Fixpoint T2pred x :=
  if x is cons a b n c then
     if ([a,b]==one) then \F n else (cons a b n (T2pred c)) 
  else zero.

Lemma split_is_succ x: ((T2split x).2 != 0) = (T2is_succ x).
Proof.  
elim: x => // a _ b _ n c Hc /=.
case: ([a, b] == one); rewrite - Hc; by case: (T2split c).
Qed.

Lemma split_succ x: let:(y,n):= T2split x in T2split (T2succ x) = (y,n.+1).
Proof.  
elim: x => // a _ b _ n c /=.
by case pa: ([a, b] == one) => //=; rewrite pa /=;case: (T2split c) => u v ->.
Qed.

Lemma split_pred x: let:(y,n):= T2split x in T2split (T2pred x) = (y,n.-1).
Proof.  
elim: x => // a _ b _ n c /=.
case pa: ([a, b] == one)  => //=; first by case: n.
by rewrite pa /=; case:(T2split c) => // u v ->.
Qed.


Lemma split_le x :  (T2split x).1 <= x.
Proof.
elim: x => // a _ b _ n c Hc /=.
case pa:([a, b] == one)  => //; move: Hc; case (T2split c) => y m /=.
by rewrite T2le_consE !eqxx ltnn => -> /=; rewrite if_same.
Qed.

Lemma nf_split x : T2nf x -> T2nf (T2split x).1.
Proof.
elim: x => // a _ b _  n c Hc /=.
case pa: ([a, b] == one) => // /and4P [sa sb  /Hc sd se].
move: (T2le_lt_trans (split_le c) se).
by move: sd; case (T2split c) => y m /= -> ->; rewrite sa sb. 
Qed.

Lemma T2finite_succ x: T2finite x -> T2finite (T2succ x).
Proof. by elim: x => // a _ b _ n c Hc /= ->. Qed.

Lemma T1succ_nat n: T2succ (\F n) = \F (n.+1).
Proof. by case: n. Qed.

Lemma limit_pr1 x: (x == zero) (+) (T2limit x (+) T2is_succ x).
Proof.
elim: x => //a _ b _ n c Hc /=; case az: ([a, b] == one)  => //=.
by case cz: (c == zero); [ rewrite (eqP cz) | move: Hc; rewrite cz].
Qed.

Lemma limit_pr x y: T2limit x -> y < x -> T2succ y < x.
Proof.
elim: x y; [ by [] |move => a _ b _ n c Hc y /=].
case: y. 
  rewrite T2gt1 andTb !T2eqE !andbT !andbA.  
  by case sa: ((a == zero) && (b == zero)). 
move => a' b' n' c';rewrite /T2succ -/T2succ => hh.
case pa: ([a', b'] == one).
  rewrite T2lt_consE  /= T2lt_consE -!T2lt_psi (eqP pa).
  have ->: ((zero == a) && (zero == b)) = (one == [a,b]). 
    by rewrite T2eqE !eqxx !andbT.
  move: hh; rewrite (eq_sym _ one); case: (T2ltgtP one [a,b]) => //.
  by rewrite T2lt1.
rewrite T2lt_consE T2lt_consE.
case ha:(lt_psi a' b' a b) => //; case hb: ((a' == a) && (b' == b)) => //.
case: (ltngtP n' n) => // _ hc;apply: Hc => //.
move: hh hc; move/andP:hb => [/eqP <- /eqP <-]; rewrite pa. 
by case /orP => //; move /eqP ->; rewrite T2ltn0.
Qed.

Lemma T2le_psi_b a b : T2succ b <= [a,b].
Proof.
move: (T2lt_psi_b a b). 
case b => //; first by rewrite T2ge1.
move => a1 b1 n1 c1 /= h; apply: T2ltW; move: h.
case eq1: ([a1, b1] == one).
  rewrite !T2lt_consE T2ltn0 ltn0 /= andbF !if_same if_simpl.
  by move /eqP: eq1 => [ -> ->] ->.
by rewrite !T2lt_consE T2ltn0 ltn0 !if_same if_simpl => ->.
Qed.

Lemma pred_le a: T2pred a <= a.
Proof.
elim: a => // a _ b _ n c Hc /=; case pa: ([a, b] == one).
  by case: n => //= n; rewrite T2le_consE ltnSn; move: (eqP pa) => [-> ->].
by rewrite T2le_consE !eqxx Hc !if_same.
Qed.
  
Lemma pred_lt a: T2is_succ a -> T2pred a < a.
Proof.
elim: a => // a _ b _ n c Hc /=; case pa: ([a, b] == one).
  by case: n => //= n; rewrite T2lt_consE ltnSn; move: (eqP pa) => [-> ->].
by move => /=  h; rewrite T2lt_consE Hc // !eqxx !if_same.
Qed.

Lemma succ_lt a: a < T2succ a.
Proof. 
elim: a => // a _ b _ n c Hc /=; case pa: ([a, b] == one).
  by move: (eqP pa) => [-> ->]; rewrite T2lt_consE ltnSn.
by rewrite T2lt_consE !eqxx Hc !if_same.
Qed.

Lemma nf_succ a: T2nf a -> T2nf (T2succ a).
Proof.
elim:a => // a _ b _ n c Hc /= /and4P [pa pb /Hc pc pe].
case pf: ([a, b] == one) => //=; rewrite pa pb pc  /=.
by apply:limit_pr => //=; rewrite pf.
Qed.

Lemma nf_pred a: T2nf a -> T2nf (T2pred a).
Proof.
elim:a => // a _ b _  n c Hc /= /and4P [pa pb /Hc pc pe].
case pf: ([a, b] == one); first by apply: nf_finite.
by rewrite /= pa pb pc (T2le_lt_trans (pred_le c) pe). 
Qed.


Lemma succ_pred x: T2nf x -> T2is_succ x -> x = T2succ (T2pred x).
Proof.
elim:x => // a _ b _ n c Hc nf /=.
case az: ([a, b] == one) => /=. 
  rewrite (T2nf_finite az nf); move: (eqP az) => [-> ->]; case n => //.
by rewrite az => h; rewrite - Hc //; case/and4P: nf.
Qed.

Lemma succ_p1 x: T2is_succ (T2succ x).
Proof. 
by elim: x => // a _ b _ n c Hc /=; case:([a, b] == one) => //=;rewrite Hc orbT.
Qed.

Lemma pred_succ x: T2nf x -> T2pred (T2succ x) = x.
Proof.
elim:x => // a _ b _ n c Hc nf /=; case az: ([a, b] == one).
  by rewrite (T2nf_finite az nf); move: (eqP az) => [-> ->]. 
by rewrite /= az Hc //; case/and4P: nf.
Qed.

Lemma succ_inj x y: T2nf x -> T2nf y -> (T2succ x == T2succ y) = (x==y).
Proof.
move => nx ny;case h: (T2succ x == T2succ y).
  by rewrite - (pred_succ nx) (eqP h) (pred_succ ny) eqxx.
by case hh: (x==y) => //; rewrite -h (eqP hh) eqxx.
Qed.

Lemma lt_succ_succ x y: T2succ x < T2succ y -> x < y. 
Proof.
elim: x y; first by case; [ rewrite T2ltnn | move => a b n c  _ ].
move => a _ b _ n c Hc /=; case.
  rewrite {2}/T2succ T2lt1; case: ([a, b] == one) => //.
move => a' b' n' c'; case sa: ([a, b] == one) => /=.
  case /eqP:sa => -> -> /=;case sb: ([a', b'] == one) => //.
    rewrite {1} /T2lt /= if_same if_simpl ltnS. 
    by case /eqP:sb => -> ->; rewrite /T2lt /= => ->.
  move => _; rewrite T2lt_consE /lt_psi !T2ltn0 !T2lt0n /=. 
  move: sb; rewrite T2eqE !eqxx !(eq_sym zero) !andbT.
  by case az: (a' == zero) => //= ->.
case pa: ([a', b'] == one); rewrite !T2lt_consE.
  by rewrite -T2lt_psi T2lt1 /=; move: sa; rewrite T2eqE !andbT => ->.
case: (lt_psi a b a' b') => //; case:((a == a') && (b == b')) => //.
case: (ltngtP n n') => // _;apply: Hc.
Qed.

Lemma le_succ_succ x y: x <= y -> T2succ x <= T2succ y.
Proof. rewrite !T2leNgt; apply: contra; exact:lt_succ_succ.  Qed.

Lemma lt_succ_succE x y:  
  T2nf x -> T2nf y ->  (T2succ x < T2succ y) = (x < y).
Proof.
move => nx ny.
case (T2ltgtP (T2succ x) (T2succ y)).  
+ by move/lt_succ_succ => ->.
+ by move /lt_succ_succ => /T2lt_anti.
+ by move /eqP; rewrite   (succ_inj nx ny) => /eqP ->; rewrite T2ltnn.
Qed.

Lemma le_succ_succE x y: 
  T2nf x -> T2nf y -> (T2succ x <= T2succ y) = (x <= y).
Proof.
by move => na nb; rewrite /T2le (succ_inj na nb) (lt_succ_succE na nb).
Qed.

Lemma lt_succ_le_1 a b : T2succ a <= b ->  a < b.
Proof. apply: T2lt_le_trans (succ_lt a). Qed.

Lemma lt_succ_le_2 a b:  T2nf a -> a < T2succ b ->  a <= b.
Proof.
elim: a b; first by move => b;rewrite T2le0n.
move => a' _ b' _ n' c' Hc; case; first by rewrite T2lt1 => _ /eqP ->.
move => a b n c nx /=; case sa: ([a, b] == one).
  case /eqP: sa => -> ->; rewrite T2lt_consE T2le_consE -T2lt_psi T2lt1 /=.
  case sa: ((a' == zero) && (b' == zero)) => //.   
  have sa': ([a',b']==one) by rewrite T2eqE !andbT sa.
  rewrite (T2nf_finite sa' nx) ltnS leq_eqVlt if_same T2le0n.
  by case (ltngtP n' n).
rewrite T2lt_consE T2le_consE; case: (lt_psi _ _ _ _) => //.
case: (_ && _) => //; case: (ltngtP n' n) => // _. 
by apply: Hc; move:nx => /and4P[].  
Qed.

Lemma lt_succ_le_3 a b:  T2nf a -> (a < T2succ b) = (a <= b).
Proof.
move => na; case h:(a < T2succ b). 
  by rewrite (lt_succ_le_2 na  h).
rewrite - h; case (T2ltP b a) => // ab; exact: (T2le_lt_trans ab (succ_lt b)).
Qed.

Lemma lt_succ_le_4 a b: T2nf b ->  (a < b) = (T2succ a <= b).
Proof.
move => nb.
case: (T2ltP a b).
  rewrite T2leNgt T2ltNge;case h: (b < T2succ a) => //. 
  by rewrite(lt_succ_le_2 nb h).
by move /le_succ_succ => /(T2lt_le_trans (succ_lt b)); rewrite T2leNgt => ->.
Qed.

Lemma succ_nz x:  T2succ x != zero.
Proof. by move: (T2le_lt_trans (T2le0n x) (succ_lt x)); rewrite T2lt0n. Qed.

Lemma succ_psi a b: [a, b] != one -> T2succ [a,b] =  cons a b 0 one.
Proof. by rewrite /= T2eqE !eqxx !andbT; case (_ && _). Qed.

Lemma succ_psi_lt x a b : [a, b] != one ->  x < [a,b] -> T2succ x < [a,b].
Proof.
move => yn1; case: x => //; first by rewrite /= T2gt1 yn1.
move => a' b' n d /=.
case: ([a', b'] == one);rewrite !T2lt_consE ltn0 T2ltn0 !if_same if_simpl.
  move: yn1; rewrite - !T2lt_psi -/one eq_sym; case: (T2ltgtP one [a,b]) => //.
  by rewrite T2lt1.
by move => ->.
Qed.

Lemma succ_psi_lt2 a b x: [a, b] != one -> ([a, b] <= T2succ x) = ([a, b] <= x).
Proof.
move => ha;symmetry.
case (T2leP [a, b] (T2succ x)).
  by rewrite !T2leNgt; apply: contra; apply:succ_psi_lt.
by move => hb; move: (T2lt_trans (succ_lt x) hb);rewrite T2ltNge; move /negbTE.
Qed.

(** ** Addition *)
(** same as for T1 *)

Fixpoint T2add x y :=
  if x is cons a b n c then 
    if y is cons a' b' n' c' then
       if [a,b] < [a',b']  then y
       else if [a',b'] < [a,b] then cons a b n (c + y)
       else  cons a b (n+n').+1 c'
    else x 
  else y
 where "x + y" := (T2add x y) : g0_scope.

Fixpoint T2sub x y :=
  if x is cons a b n c then
     if y is cons a' b' n' c' then
           if (x < y) then zero 
           else if ([a',b'] < [a,b]) then x 
           else if (n<n')%N then zero
           else if ([a,b]==one) then 
             if (n==n')%N then zero else cons zero zero ((n-n').-1) zero
           else if(n==n') then c - c' else cons a b (n - n').-1 c 
     else x
  else zero
where "a - b" := (T2sub a b) : g0_scope.

Lemma T2subn0 x: x - zero = x.
Proof. by case x. Qed.

Lemma T2sub0n x: zero - x = zero.
Proof.  done.  Qed.

Lemma minus_lt a b: a < b -> a - b = zero.
Proof. by case: a b => // a b n c // [] // a' b' n' v' /= ->. Qed.

Lemma T2subnn x: x - x = zero.
Proof.
by elim: x => // a _ b _  n c Hc /=; rewrite !T2ltnn ltnn eqxx Hc if_same.
Qed.

Lemma minus_le a b: a <= b -> a - b = zero.
Proof.
rewrite T2le_eqVlt;case /orP; [move /eqP ->; apply: T2subnn| apply: minus_lt].
Qed.

Lemma nf_sub a b: T2nf a -> T2nf b -> T2nf (a - b).
Proof.
elim: a b => // a Ha b Hb n c Hc [] // a' b' n' c' na nb /=.
case: (_ < _) => //; case: (_ < _) => //; case: (ltngtP n n') => //.
 by case:eqP.
move: na nb => /and4P[_ _  nc _] /and4P [_ _  nc' _].
by case:eqP => // _ _ ; apply: Hc.
Qed.


Lemma sub_int n m : \F n - \F m = \F (n -m)%N.
Proof.
case: n m => // n [] // m /=; rewrite /T2lt /= if_same subSS //.
case: (ltngtP n m) => pa;first by move: (ltnW pa)=> /eqP ->.
 by rewrite -(subnSK pa). 
by rewrite pa subnn.
Qed.

Lemma succ_is_add_one a: T2succ a = a + one.
Proof.
elim:a => // a _ b _ n c Hc /=; rewrite addn0 Hc.
case:(T2ltgtP [a, b] one) => //; first by rewrite T2lt1 //.
by case => -> ->.
Qed.

Lemma add1Nfin a:  ~~ T2finite a  -> one + a = a.
Proof. by case:a => // a b n c /=; rewrite T2gt1 T2eqE andbT => -> //. Qed.

Lemma sub1Nfin a:  ~~ T2finite a  -> a - one  = a.
Proof. by case:a => // a b n c /=; rewrite T2lt1 T2gt1 T2eqE andbT => ->. Qed.

Lemma sub1a x: x != zero -> T2nf x -> x = one + (x - one). 
Proof.
case fb:(T2finite x); last by rewrite sub1Nfin ?fb // add1Nfin // fb //.
move: fb;case x => // a' b' n' c' /=.
rewrite T2lt1 T2gt1  T2eqE andbT/= => /andP [/eqP -> /eqP ->] _.
by rewrite T2lt1 /= => /andP [_ /eqP ->];case n'. 
Qed.

Lemma sub1b x: T2nf x -> x = (one + x) - one. 
Proof.
case h: (T2finite x); last by rewrite add1Nfin ? h // sub1Nfin // h.
by move => nx; rewrite (T2finite2 h nx); case: (T2split x).2.
Qed.

Lemma T2add0n: left_id zero T2add.     Proof. by []. Qed. 
Lemma T2addn0: right_id zero T2add.    Proof. by case. Qed.


Lemma add_int n m : \F n + \F m = \F (n +m)%N.
Proof.
by case: n m => // n [ | m]; rewrite /= - ? addnS  // - addnE addn0.
Qed.

Lemma add_fin_omega n: \F n + omega = omega.
Proof. by case: n. Qed.


Lemma split_add x: let: (y,n) :=T2split x in T2nf x ->
   (x == y + \F n) && ((y==zero) || T2limit y ).
Proof.
elim: x => //a _ b _ n c Hc  /=; case h: ([a, b] == one).
  move=> h1; rewrite (T2nf_finite h h1 (n:=0)); case: (eqP h) => -> ->.
  by rewrite T2add0n !eqxx /=.
move: Hc; case (T2split c) => y s h1 /and4P [_ _ /h1/andP [/eqP -> sb] _].
rewrite /= h sb andbT; case s => //=; first by rewrite T2addn0.
by move => m; rewrite T2lt1 T2gt1 /= h.
Qed.

Lemma add_to_cons a b n c: 
  c < [a,b] -> cons a b n zero + c = cons a b n c.
Proof.
case: c => // u v m z /=; rewrite T2lt_consE - T2lt_psi T2ltn0 !if_same. 
by rewrite if_simpl => h; rewrite h (T2lt_anti h).
Qed.

Lemma nf_add a b: T2nf a -> T2nf b -> T2nf (a + b).
Proof.
have psi1: forall a' b' n' c' a b, 
   cons a' b' n' c' < [a,b] = ([a', b'] < [a,b]).
  move => a' b' n' c' a'' b''. 
  by rewrite T2lt_consE T2ltn0 ltn0 !if_same if_simpl T2lt_psi. 
elim: a b => // a Ha b Hb n c Hc [] // a' b' n' c' ha hb /=.
case (T2ltgtP [a, b] [a', b']) => // h; last by move: hb; case:h => -> ->. 
move: ha; rewrite /T2nf -/T2nf => /and4P [sa sb sc sd].
rewrite sa sb Hc //=; move: sd; case c => //=; first by rewrite psi1.
move => a1 b1 n1 c1; rewrite psi1.
by case: (T2ltgtP [a1, b1]  [a', b']) => //;rewrite psi1.
Qed.


Lemma T2add_eq0 m n:  (m + n == zero) = (m == zero) && (n == zero).
Proof. 
case: m; [by rewrite T2add0n | move => a' b' n' c'; rewrite andFb].
by case: n => // a b n c /=; case: (T2ltgtP [a', b']  [a, b]).
Qed.

Lemma add_le1 a b: a <= a + b.
Proof.
elim:a b; first by rewrite /T2le /=; case;[ rewrite eqxx | ].
move => a' _ b' _  n' c' hc [] // a b n c /=.
case: (T2ltgtP [a', b'] [a, b]) => h; rewrite T2le_consE -T2lt_psi ?T2ltnn.
+ by rewrite h.
+ by rewrite !eqxx ltnn /=; apply: hc.
+ by rewrite !eqxx ltnS leq_addr. 
Qed.

Lemma add_le2 a b: b <= a + b.
Proof.
case: a => // a' b' n' c'; case: b ; [done | move => a b n c /=].
case: (T2ltgtP [a', b'] [a, b]) => h; rewrite T2le_consE -T2lt_psi ?h => //.
+ by rewrite !eqxx /= ltnn T2lenn if_same.
+ by case: h => -> ->; rewrite T2ltnn ltnS leq_addl !eqxx. 
Qed.

Lemma sub_le1 a b : T2nf a -> (a - b) <= a. 
Proof.
elim: a b => [b // | a' _ b' _  n' c' H].
case; [by rewrite T2subn0 T2lenn | move => a b n c/and4P [_ _ /H la lb] /=].
have hh: (n < n')%N -> ((n' - n).-1 < n')%N.
  by case: n' => // n' h; rewrite subSn // ltnS leq_subr.
rewrite T2lt_consE -T2lt_psi; case: (T2ltgtP [a', b'] [a, b]) => // eq1.
  case sa: ((a' == a) && (b' == b)) => //.
  by move: eq1; move/andP:sa => [/eqP -> /eqP ->]; rewrite T2ltnn.
case: eq1 => <- <- ; rewrite !eqxx /=.
case : (ltngtP n' n) => // eq2.
  case x1: ([a', b'] == one);rewrite T2le_consE (hh eq2) ?eqxx.
     by move: x1; rewrite T2eqE => /and4P [/eqP -> /eqP ->] /=.
   by rewrite /= if_same.
case : (c' < c) => //; case: ([a', b'] ==one) => //.
apply: (T2le_trans (la c)); apply:T2ltW; apply: (T2lt_le_trans lb).
apply: T2le_psi1.
Qed.

Lemma sub_pr a b: T2nf b -> (a + b) - a = b.
Proof.
elim: a b; first by move => b _; rewrite T2subn0.
move => a' _ b'  _ n' c' Hc; case; first by rewrite T2addn0 T2subnn.
move => a b n c nn /=.
case (T2ltgtP [a', b'] [a, b]) => pa;  rewrite /= T2lt_consE -T2lt_psi.
+ rewrite pa /=  (T2lt_anti pa); case h: (_ && _) => //.
  by move: pa; move/andP: h => [/eqP -> /eqP ->]; rewrite T2ltnn.
+ rewrite !T2ltnn !eqxx /= ltnn  (T2ltNge _ c') add_le1 /=.
  by rewrite Hc // ifF //; case: eqP => h //; move: pa; rewrite h T2lt1.
+ rewrite !T2ltnn !eqxx addnC ltn_simpl1 eqn_simpl1 - addSn addnK /=.
  move: pa nn; case => -> -> ; case: eqP => //; case => -> -> h.
  by rewrite (T2nf_finite _ h).
Qed.

Lemma add_inj a b c : T2nf b -> T2nf c -> a + b = a + c -> b = c.
Proof.
move => sb sc h.
by rewrite - (sub_pr a sb) - (sub_pr a sc) h.
Qed.

Lemma sub_pr1 a b: T2nf b -> a <= b -> b = a + (b - a).
Proof.
move => nb; rewrite /T2le.
case: (altP (a =P b)) => [-> | _ /=]; first by rewrite T2ltnn T2subnn T2addn0.
move: nb; elim: a b; first by move => b nb; rewrite T2subn0 //.
move => a' _ b' _  n' c' Hc; case; [by rewrite T2ltn0 | move => a b n c].
have aux: (n' < n)%N ->n = (n' + (n - n').-1).+1.
  by move => le1; rewrite - {1} (subnKC le1)  subnS addSn.
move => sa sb;rewrite /= (T2lt_anti sb).
move: sb; rewrite T2lt_consE - T2lt_psi.
have ->:(a' == a) && (b' == b) = ( [a', b'] == [a, b]) by rewrite T2eqE !andbT.
case: (T2ltgtP [a', b'] [a, b]) => sb; rewrite ? sb //.
move: sa; case: sb => <- <-  => sa.
have sb: [a', b'] = one -> c = zero.
  by move => h;move: sa;case:h =>  -> -> /= /andP[_];rewrite T2lt1 => /eqP ->.
case: (ltngtP n' n) => sc; rewrite ? sc ?eqxx //.
  move: sc (aux sc); case h: (n==n'); [ by rewrite (eqP h) ltnn | move => _ hh].
  by case: eqP => h1 ; [ rewrite h1 T2ltnn - hh sb | rewrite !T2ltnn - hh ].
move => dd'; case: eqP; first by  move => h; move: dd';rewrite (sb h) T2ltn0.
move: sa => /and4P [_ _  nd ne] _; move: (Hc c nd dd') => h.
have: c - c' < [a', b'] by move: (T2le_lt_trans (sub_le1 c' nd) ne).
rewrite - h; move: dd'; rewrite {1} h;case: (c - c').
   by rewrite T2addn0 T2ltnn.
move => a1 b1 c1 n1 d1. 
rewrite T2lt_consE T2ltn0 ltn0 !if_same  if_simpl -T2lt_psi=> ha.
by rewrite ha (T2lt_anti ha).
Qed.


Lemma omega_minus_one : omega - one = omega. 
Proof. by []. Qed.

Lemma sub_nz a b: T2nf b -> a < b -> (b - a) != zero.
Proof.
move => nb lab; move: (sub_pr1 nb (T2ltW lab)).
case h: (b - a == zero) => //; rewrite (eqP h) T2addn0 => eq.
by move: lab; rewrite eq T2ltnn.
Qed.

Lemma T2addA c1 c2 c3: c1 + (c2 + c3) = (c1 + c2) + c3.
Proof.
elim: c1 c2 c3 => // a1 _ b1 _ n1 c1 H; case.
   by move => c3;rewrite !T2add0n T2addn0.
move => a2 b2 n2 c2; case;[ by rewrite !T2addn0 | move => a3 b3 n3 c3 /=].
case: (T2ltgtP [a2, b2] [a3, b3]).
+ case: (T2ltgtP  [a1, b1] [a2, b2]) => pa pb /=.
   - by rewrite (T2lt_trans pa pb) /= pb.
   - by case (T2ltgtP a1 a3) => //; rewrite - H /= pb.
   - by rewrite  pa pb.
+ case: (T2ltgtP [a1, b1] [a2, b2]) => pa pb /=;
     move: (T2lt_anti pb) => pc.
   - by rewrite pb pc.
   - by move:(T2lt_trans pb pa) => h; rewrite h (T2lt_anti h) - H /= pb pc.
   - by rewrite pa pb pc.
+ move => e1; case: (T2ltgtP  [a1, b1] [a2, b2]) => pb /=; rewrite -e1.
   - by rewrite !T2ltnn. 
   - by rewrite pb (T2lt_anti pb) - H /= -e1 !T2ltnn.
   - by rewrite pb !T2ltnn addSn addnS addnA.
Qed.

Lemma T2le_add2l  p m n : (p + m <= p + n) = (m <= n).
Proof.
elim:p m n => // a _ b _ n c Hc.
case; first by move => n1; rewrite T2addn0 T2le0n add_le1.
move => a' b' n' c'; case.
  rewrite T2addn0  /=;case: (T2ltgtP [a, b] [a', b']) => h.
  +  rewrite T2le_consE -T2lt_psi  (T2lt_anti h) T2len0 ifF //. 
     case ha: ((a' == a) && (b' == b)) => //.
     by move:h; case /andP: ha => /eqP -> /eqP ->; rewrite T2ltnn.
  + rewrite T2le_consE /lt_psi !T2ltnn !eqxx  ltnn /=.  
    by rewrite -{2} (T2addn0 c) Hc.
 + rewrite !T2le_consE /lt_psi !T2ltnn !eqxx /= addnC ltn_simpl1 eqn_simpl1. 
   by rewrite T2len0. 
move => a'' b'' n'' c'' /=.
have ha: (a' == a) && (b' == b) = ([a',b'] == [a,b]) by rewrite T2eqE !andbT.
have hb:(a' == a'') && (b' == b'') = ([a',b'] == [a'',b''])
   by rewrite T2eqE !andbT.
case: (T2ltgtP [a, b] [a', b']);case:(T2ltgtP [a, b] [a'', b''])
  =>// pa pb; rewrite T2le_consE [in RHS] T2le_consE - !T2lt_psi.
- move: (T2lt_trans pa pb) => pc.
  by rewrite ha hb (T2lt_anti pb) (T2lt_ne' pb) (T2lt_ne' pc) (T2lt_anti pc).
- by rewrite ha hb -pa (T2lt_ne' pb) (T2lt_anti pb).
- by rewrite (T2lt_trans pb pa) pa.
- by rewrite !eqxx T2ltnn ltnn Hc T2le_consE -T2lt_psi /= hb.
- by rewrite T2ltnn -pa pb !eqxx ltnS leq_addr.
- by rewrite -pb pa.
- rewrite T2ltnn -pb addnC ltn_simpl1 eqn_simpl1 !eqxx hb - pb.
  by rewrite (T2lt_anti pa) (T2lt_ne' pa).
- by rewrite hb  - pa pb !eqxx T2ltnn /= ltnS ltn_add2l - !addSn eqn_add2l. 
Qed.

Lemma T2lt_add2l  p m n : (p + m < p + n) = (m < n).
Proof. by rewrite !T2ltNge T2le_add2l. Qed.


Lemma T2lt_add2r  p m n : (m + p  < n + p ) ->  (m < n).
Proof.
elim: m p n. 
  by move => p n; rewrite T2add0n; case: n => //;rewrite T2add0n T2ltnn.
move => a _ b _ n c Hc; case; first by move => u; rewrite ! T2addn0.
move => a' b'  n' c'; case.
  simpl;case (T2ltgtP [a, b]  [a', b']) => pa /=.
  + by rewrite !T2ltnn.
  + have h:(a == a') &&(b== b') = ([a,b] == [a',b']) by rewrite T2eqE !andbT.
    by rewrite  T2lt_consE -T2lt_psi h (T2lt_anti pa) (T2lt_ne' pa).
  + case: pa => -> ->.
    by rewrite T2lt_consE -T2lt_psi T2ltnn !eqxx ltn_simpl1 eqn_simpl1.
move => a'' b'' n'' c'' /= h1; rewrite T2lt_consE; move: h1.
have ha:(a == a'') &&(b== b'') = ([a,b] == [a'',b'']) by rewrite T2eqE !andbT.
have hb:(a == a') &&(b== b') = ([a,b] == [a',b']) by rewrite T2eqE !andbT.
case (T2ltgtP [a,b] [a',b']);case (T2ltgtP [a',b'] [a'',b''])
  => pb pa /=; rewrite T2lt_consE - !T2lt_psi // ? ha ? hb.
- by rewrite (T2lt_trans pa pb).
- by rewrite ! T2ltnn ltnn !eqxx //. 
- by rewrite -pb pa.
- case: (T2ltgtP [a,b] [a'',b'']) => //.
  by case: (ltngtP n n'') => // _ _ ; apply: Hc.
- by rewrite (T2lt_anti pa) (T2lt_ne' pa).
- by rewrite - pb  (T2lt_anti pa) (T2lt_ne' pa).
- by rewrite pa pb.
- by rewrite pa T2ltnn eqxx ltn_simpl1 eqn_simpl1.
- by rewrite pa pb !T2ltnn eqxx ltnS ltn_add2r if_same if_simpl => ->.
Qed.

Lemma T2le_add2r  p m n : (m <=n) -> (m + p  <= n + p).
Proof. rewrite !T2leNgt; apply: contra; apply: T2lt_add2r.  Qed.

Lemma T2eq_add2l  p m n : (p + m == p + n) = (m == n).
Proof. by rewrite !T2eq_le !T2le_add2l. Qed.

Lemma add_le3 a b: a = a + b -> b = zero.
Proof. move /eqP;rewrite -{1} (T2addn0 a) T2eq_add2l => /eqP -> //. Qed.

Lemma add_le4 a b: b != zero -> a < a + b.
Proof.
move: (add_le1 a b); rewrite T2le_eqVlt.
by case: (a<a+b); rewrite ? orbT // orbF => /eqP /add_le3 ->.
Qed.

Lemma sub_pr1r a b: T2nf a -> a - b = zero -> a <= b.
Proof.
move => nn h; case /orP: (T2le_total a b) => // h1.
by move: (sub_pr1 nn h1); rewrite h T2addn0 => ->. 
Qed.

Definition T2ap x := 
  if x is cons a b n c then ((n==0) && (c==zero)) else false.


Lemma ap_pr0 a b (x := [a,b]) u v:
  u < x -> v < x -> u + v < x.
Proof.
case: u v; [by move => u |move => a1 b1 n1 c1].
case; [by move => H  _ | move => a' b' n' c' l1 l2 /=].
have aux: forall n' d', cons a1 b1 n' d' < x.
  by move => n'' d'';move: l1;rewrite psi_lt1 psi_lt1.
by case: (T2ltgtP [a1, b1]  [a', b']).
Qed.

Lemma ap_limit x: T2ap x -> (x == one) || (T2limit x).
Proof.
case: x => // a b n f /= /andP[/eqP -> /eqP ->]. 
by rewrite eqxx orTb T2eqE !andbT; case: (_ && _).
Qed.

Lemma ap_pr1 c: 
   (forall a b,  a < c -> b < c -> a + b < c)  ->
   (c== zero) || T2ap c.
Proof.
case: c => // a b n c /=.
case: n c => [d H | n c H]; last first.
  have l2: (cons a b n c) < (cons a b n.+1 c) by rewrite psi_lt2 ltnS leqnn.
  move: (H _ _ l2 l2). rewrite /= psi_lt2 /= psi_lt2 /= T2ltnn if_same ltnS.
  by rewrite -{3}(add0n n) ltn_add2r.
case dz: (d == zero) => //.
have pa: [a,b] < cons a b 0 d by rewrite psi_lt2 /= T2lt0n dz.
by move: (H _ _ pa pa); rewrite /= psi_lt2 /= psi_lt2.
Qed.

Lemma ap_pr2 c: 
   T2nf c -> c <> zero ->
   (forall a b, T2nf a -> T2nf b ->  a < c -> b < c -> a + b < c)  ->
   T2ap c.
Proof.
case: c => // a b n c nc _ Hr.
have {Hr} H: forall u, T2nf u -> u < cons a b n c  -> u + u < cons a b n c.
  by move => u ua ub; apply: Hr.
case: n c H nc => [c H | n c H].
  rewrite /T2nf -/T2nf => /and4P[na nb nc nd].
  have np: T2nf [a,b] by rewrite nf_psi na nb.
  move: (H _ np). 
  rewrite T2lt_consE ! eqxx /=  T2ltnn T2lt_consE !eqxx /= if_simpl.
  by rewrite -T2lt_psi T2ltnn T2lt0n; case: eqP => // _; apply.
have l2: (cons a b n c) < (cons a b n.+1 c) by rewrite psi_lt2 ltnS leqnn.
move=> pa; have pb: T2nf (cons a b n c) by move: pa; rewrite /T2nf -/T2nf.
move: (H _ pb l2); rewrite /= T2ltnn psi_lt2 T2ltnn ltnS if_same.
by rewrite  -{3}(add0n n) ltn_add2r /=.
Qed.


Lemma ap_pr3 a b y (x := [a,b]): y < x -> y + x = x.
Proof.
by case: y => // a' b' n' c' /=; rewrite /x psi_lt1 => ->.
Qed.

Lemma ap_pr4 x: (forall b, b < x -> b + x = x) -> (x == zero) || T2ap x.
Proof.
case: x => // a b /=; case => [d H|].
  move: (H [ a, b]).
  rewrite /= T2ltnn psi_lt2 /=  T2lt0n; case:eqP => //=.
  by move => _ /(_ erefl). 
move => n d H /=.
move: (H (cons a b n zero)).
rewrite /= T2lt_consE  -T2lt_psi T2ltnn !eqxx ltnS leqnn.
by move => /(_ erefl); case => /eqP; rewrite  - {3} (addn0 n) eqn_add2l.
Qed.

(** ** The function phi *)
(** We consider he some funciton phi *)


Definition T2_pr1 x:= if x is cons a b n c then a else zero.
Definition T2_pr2 x:= if x is cons a b n c then b else zero.
Definition T2finite1 x:=
  if x is cons a b n c then [&& a == zero, b== zero & c == zero] else false.

Definition phi a b :=
   if b is cons u v n k then
     if ((n==0) && (k==zero)) then
        if (a < u) then b else [a,b]
     else if ((n==0) && (T2finite1 k) && (a <u))
       then [a, cons u v 0 (T2pred k) ]
     else [a,b]
   else [a,b].


Lemma phi_ap x y : (phi x y) = [T2_pr1 (phi x y), T2_pr2 (phi x y)].
Proof.
case: y => // a b n c /=.
case h: (_ && _) => //; last by case: (_ && _).
by case (x < a) => /=; move/andP: h => [/eqP -> /eqP ->].
Qed.

Lemma phi_le1 a b: a <= T2_pr1 (phi a b).
Proof.
case:b; first by rewrite /= T2lenn.
move => a'' b'' n'' c'' /=;  rewrite !fun_if /= eqxx if_same.
by case: (a < a''); rewrite !if_same.
Qed.

Lemma phi_le2 a b: T2_pr2 (phi a b) <= b.
Proof.
case:b; first by rewrite /= T2lenn.
move =>  a'' b'' n'' c'' /=.  
case sa: (_ && _).
   case aa: (a < a'') => //=.
   apply: T2le_trans (T2le_psi1 a'' b'' n'' c''). 
   apply /T2ltW; apply:T2lt_psi_b.
case sb: (_ && _) => //=; rewrite T2le_consE pred_le !eqxx /=.
by case n'' => //=; rewrite if_same //.
Qed.

Lemma phi_le3 a b:  a < T2_pr1 (phi a b) -> (phi a b) = b.
Proof.
case:b; first by rewrite /= T2ltnn.
move =>  a'' b'' n'' c'' /=.  
case sa: (_ && _); first by case aa: (a < a'') => //=; rewrite T2ltnn.
by case sb: (_ && _) => //=; rewrite T2ltnn.
Qed.

Lemma phi_fix1 a u v: a < u -> phi a [u,v] = [u, v].
Proof. by move => /= ->. Qed.

Lemma phi_fix2 a b (u:= T2_pr1 b) (v:= T2_pr2 b):
  phi a b = b -> b = [u,v] /\ a < u.
Proof.
move => h.  split; first by rewrite -h phi_ap h.
move: (h). rewrite - h (phi_ap a b) h -/u -/v /=.
by case: (a <u) => // h1; move: (T2lt_psi_b a [u, v]); rewrite h1 T2ltnn.
Qed.

Lemma phi_succ a u v n:  a < u ->
  phi a (cons u v 0 (\F n.+1)) = [a, cons u v 0 (\F n)].
Proof. by move => /= ->. Qed.

(** [phi a b] is either [b], [psi a b] or [psi a (b-1)]. *)


Lemma phi_cases a b: 
    {phi a b = b} + {phi a b = [a, b]} +  
    { phi a b = [a, T2pred b]  /\  b = T2succ (T2pred b) }.
Proof.
case b; first by left; right.
move => a' b' n' c' /=.
case sa: (_ && _).
  case sb: (a < a'); [ by left; left | by left; right].
case sb: (_ && _); [right |  by left; right].
move /andP: sb  sa=> [/andP  [/eqP -> h1]].
case sb:([a', b'] == one); first by case:(eqP sb) => ->; rewrite T2ltn0.
simpl; rewrite sb => _; move: h1; case c' => //.
move => a1 b1 n1 c1 /= /and3P [/eqP -> /eqP -> /eqP ->].
by split => //=;case n1 => //.
Qed.

Lemma nf_phi x y : T2nf x -> T2nf y -> T2nf (phi x y).
Proof.
move => nx ny.
case (phi_cases x y); first by case => -> //=; rewrite nx ny.
by move => [-> h]; rewrite /= nx T2lt0n /= nf_pred.
Qed.

Lemma phi_principalR a b: { c:T2 | [a, b] =  phi zero c}.
Proof.
case az:(a==zero); last by exists [a,b]; rewrite /= T2lt0n az.
rewrite (eqP az); case: b; first by exists zero.
move => a' b' n' c'.
case az1: (a'==zero).
  exists (cons a' b' n' c'). 
  by rewrite /= (eqP az1) T2ltnn !andbF; case: (_ && _).
case h: ((n' == 0) && (c' == zero)).
  move/andP:h => [/eqP -> /eqP ->].
  by exists (cons a' b' 0 one);  rewrite /phi !eqxx  T2lt0n az1 /=.
case h':( (n' == 0) && T2finite1 c'); last first.
  by exists (cons a' b' n' c');rewrite /= T2lt0n az1 h h' /=.
move/andP:h' => [/eqP ->]; case c' => //.
move => a1 b2 n2 c1 /= /and3P[/eqP -> /eqP -> /eqP ->].
by exists (cons a' b' 0 (\F(n2.+2))); rewrite /= T2lt0n az1 /=.
Qed.

Theorem phi_spec1 a b c: c < a -> phi c (phi a b) = phi a b.
Proof.
move => ca; move: (phi_ap a b) (phi_le1 a b); case: (phi a b) => //.
by move => a' b' n' c' /= [ -> ->] /= aa; rewrite (T2lt_le_trans ca aa).
Qed.


Lemma phi_spec2 a x: 
    T2nf a -> T2nf x ->  (forall c,  T2nf c -> c < a -> phi c x = x) -> 
    a <= T2_pr1 x.
Proof.
move => na nx ha.
move: (limit_pr1 a). 
case az: (a==zero); first by rewrite (eqP az) T2le0n.
have hb: phi zero x = x by apply: ha => //; rewrite T2lt0n az.
have eq1: x = [T2_pr1 x, T2_pr2 x] by move: (phi_ap zero x); rewrite hb.
case la: (T2limit a) => h.
  case (T2ltP (T2_pr1 x) a) => // sa.
  move: (limit_pr la sa) => /ha hc.
  have aux: T2nf (T2succ (T2_pr1 x)). 
    by apply: nf_succ; move: nx; case x => // a' b' n' c' /= /and4P [].
  by move: (phi_le1  (T2succ (T2_pr1 x)) x); rewrite hc // T2leNgt succ_lt.
move: (succ_pred na h) => nsa.
move: (succ_lt (T2pred a)); rewrite - nsa => /ha => eq.
have aux: T2nf (T2pred a). 
  by apply: nf_pred; move: na; case x => // a' b' n' c' /= /and4P [].
move: (eq aux); rewrite eq1 /=; case hc: (T2pred a < T2_pr1 x).
  by rewrite nsa - lt_succ_le_4 //; move: nx; rewrite {1} eq1 /= =>/andP [].
case => _ hd.
by move: (T2lt_ne (T2lt_psi_b (T2_pr1 x) (T2_pr2 x))); rewrite hd  eqxx.
Qed.


Lemma phi_spec3 a x: 
  T2nf a -> T2nf x -> (forall c,  T2nf c -> c < a -> phi c x = x) ->
  a != zero -> {b : T2 | x = phi a b}.
Proof.
move => sa sb sc anz. 
move: (phi_spec2 sa sb sc) => h.
have hb: phi zero x = x by apply:  sc => //; rewrite T2lt0n .
have eq1: x = [T2_pr1 x, T2_pr2 x]  by move: (phi_ap zero x); rewrite hb.
move: h; rewrite T2le_eqVlt; case hc: (a == T2_pr1 x) => /= hd; last first.
  by exists x; rewrite eq1 /phi !eqxx /= hd.
set u:= T2_pr2 x; move: sb.
have ->: x = [a, u] by rewrite eq1 (eqP hc).
simpl; move/and3P => [ _ nu _]; move: nu.
case: u; first by exists zero.
move => a1 b1 n1 c1 /= /and4P [_ _ nc _].
case he: ((n1 == 0) && (c1 == zero)).
   move/andP: he => [/eqP -> /eqP ->]; case aa: (a < a1); last first.
     by exists [a1,b1]; rewrite /= aa.
   by exists (cons a1 b1 0 one) ;rewrite /= aa.
case hf: ((n1 == 0) && T2finite1 c1 && (a < a1)); last first.
  by exists (cons a1 b1 n1 c1); rewrite /= he hf.
move: he;move/andP:hf => [/andP [/eqP sa' sb'] az1] _.
rewrite sa'; move: sb'; case c1 => //.
move => a2 b2 n2 c2 /= /and3P[/eqP -> /eqP -> /eqP ->].
by exists (cons a1 b1 0 (\F(n2.+2))); rewrite /= az1. 
Qed.

Lemma phi_spec4a u v: u != zero -> phi zero [u,v] = [u, v].
Proof. by move => h; rewrite /= T2lt0n h. Qed.


Lemma phi_spec4b x: phi zero x = x -> 
  x = [T2_pr1 x, T2_pr2 x]  /\ T2_pr1 x != zero.
Proof. by move /phi_fix2; rewrite T2lt0n. Qed.

Lemma phi_spec4c x: T2nf x -> phi zero x = x -> 
  { b: T2 | x = phi one b }.
Proof.
move => nx h.
move: (phi_fix2 h). set u := T2_pr1 x; set v := T2_pr2 x.
move => [-> uz]. 
case: (T2ltgtP one u) => h1; first by exists [u,v]; rewrite /= h1.
  by move: h1 uz; rewrite T2lt0n T2lt1 => ->.
rewrite - h1.
case v => //; first by exists zero.
move => a1 b1 n1 c1.
case oa: (one < a1); last first.
  by exists (cons a1 b1 n1 c1); rewrite /= oa fun_if fun_if andbF if_same.
case ha: (n1 == 0); last first.
  by exists (cons a1 b1 n1 c1); rewrite /= ha /=.
case hc: (c1 == zero). 
   by exists (cons a1 b1 0 one); rewrite /= oa (eqP ha) (eqP hc).
case hb: (T2finite1 c1); last first.
  by exists (cons a1 b1 n1 c1); rewrite /= ha hb hc oa /=.
move: hb hc; case: c1 => // a2 b2 n2 c2 /= /and3P [/eqP -> /eqP -> /eqP ->] _.
by exists (cons a1 b1 n1 (\F n2.+2)); rewrite /= ha oa (eqP ha).
Qed.

Lemma no_critical a: a < phi a zero.
Proof.  by apply: T2lt_psi_a. Qed.

Lemma phi_ab_le1 a b: b  <= phi a b.
Proof.
case:(phi_cases a b).
  case; move => -> //; apply: T2ltW; apply: T2lt_psi_b.
move => [sa sb];rewrite sa {1} sb. apply: T2le_psi_b.
Qed.

Lemma phi_ab_le2  a b:a < phi a b.
Proof.
case:(phi_cases a b).
  case => h; last by rewrite h; apply: T2lt_psi_a.
  move:(phi_fix2 h) => [sa sb].
  by apply: (T2lt_trans sb); rewrite h {2} sa; apply: T2lt_psi_a.
move => [-> _]; apply: T2lt_psi_a.
Qed.


Lemma phi_inv1 a b: phi a (T2succ b) = [a,b] -> 
   { n: nat | (b =  cons (T2_pr1 b) (T2_pr2 b) 0 (\F n) /\ a < T2_pr1 b) }.
Proof.
case b => //; first by rewrite /= T2ltn0.
move => a1 b1 n1 c1 /=.
case ha: ([a1, b1] == one).
   by simpl; case => _ _ s; move: (n_Sn n1); rewrite s.
simpl; rewrite  (negbTE (succ_nz c1)) andbF.
case hb: ((n1 == 0) && T2finite1 (T2succ c1) && (a < a1)).
  case/andP: hb => [/andP [nz hc] hd]; move: hc.
  case c1 => //; first by rewrite (eqP nz);  exists 0.
  move => a2 b2 n2 c2 /=; case he:([a2, b2] == one) => /= hf.
    by case => <- <- <- <-; exists (n2.+1).
  by move: hf;  rewrite  (negbTE (succ_nz c2)) !andbF.
by case => h; move: (T2lt_ne (succ_lt c1)); rewrite h eqxx.
Qed.

(** Monotonicity is non-trivial *)

Lemma phi_mono_a a b b': T2nf b -> b < b' -> phi a b < phi a b'.
Proof.
move => nb  bb'.
have aux: forall u v, u < v -> [a, u] < [a, v]. 
   by move => u v h; rewrite T2lt_psi /lt_psi eqxx h orbT.
case:(phi_cases a b); last first.
  move =>[sa sb]; rewrite sa;case:(phi_cases a b'); last first.
    move => [ua ub]; rewrite ua;  apply: aux.
    rewrite {1} sb in sa; rewrite {1} ub in ua.
    move: bb'; rewrite {1} sb {1} ub.
    move: (phi_inv1 sa) => [n [xa xb]]; rewrite xa.
    move: (phi_inv1 ua) => [m [ya yb]]; rewrite ya.
    set u1 := (T2_pr1 (T2pred b)); set u2 := (T2_pr2 (T2pred b)).
    set v1 := (T2_pr1 (T2pred b')); set v2 := (T2_pr2 (T2pred b')).
    simpl; rewrite T2lt_consE -T2lt_psi ltnn eqxx.
    case ta: ([u1,u2]==one).
        case tb: ([v1,v2]==one); first by rewrite T2ltnn.
        rewrite (eqP ta) T2gt1 tb //.
    case tb: ([v1, v2] == one).
      move: ta;  rewrite T2lt_consE -T2lt_psi T2lt1 T2eqE !eqxx !andbT/=.
      by move => ->.
    rewrite T2lt_consE -T2lt_psi ltnn eqxx; case: ([u1, u2] < [v1, v2]) => //.
    case: ((u1 == v1) && (u2 == v2)) => //.
    case m => //;[ by  case n | by move => m'; case n].
  case => h; last first.
    rewrite  h; apply: (T2lt_trans _ (aux _ _ bb')).
    by apply: aux; rewrite {2} sb; apply: succ_lt.
  move: (phi_fix2 h) => [sc sd].
  by rewrite h sc T2lt_psi /lt_psi sd - sc (T2le_lt_trans (pred_le b) bb').
case; first by move => ->; exact:(T2lt_le_trans bb' (phi_ab_le1 a b')).
move => sa; rewrite sa; case:(phi_cases a b').
  case; last by move => ->; apply: aux.
  move => h; move: (phi_fix2 h) => [sc sd]; rewrite h sc.
  by rewrite T2lt_psi /lt_psi sd - sc bb'.
move=> [sb sc]; rewrite sb; apply: aux.
move: bb'; rewrite {1} sc lt_succ_le_3 //; case /orP => // /eqP h.
move: sa; rewrite h.
rewrite {1} sc in sb.
move:  (phi_inv1 sb) => [n [xa xb]]; rewrite xa /= xb /=.
set u := (T2_pr1 (T2pred b')); set v := T2_pr2 (T2pred b').
simpl; case n => /=. 
  by move => h1; move: (T2lt_psi_b a [u,v]); rewrite - h1 T2ltnn.
by move => n1 []; case n1 => // n2 [] h2; move: (n_Sn n2); rewrite - h2.
Qed.

Lemma phi_mono_b a b b': T2nf b -> b <= b' -> phi a b <= phi a b'.
Proof.
move => sb.
by case /orP; [move => /eqP -> |move => sd;apply:T2ltW;apply:phi_mono_a].
Qed.

Lemma phi_mono_c a b b': T2nf b -> T2nf b' -> (phi a b < phi a b') = (b < b').
Proof.
move => sa sb; case: (T2ltP b b') => // h; first exact:(phi_mono_a a sa  h).
by rewrite T2ltNge phi_mono_b. 
Qed.


Lemma phi_inj a b b': T2nf b -> T2nf b' -> phi a b = phi a b' -> b = b'.
Proof.
move => pa pb pc; case: (T2ltgtP b b') => // h.
  by move: (phi_mono_a a pa h); rewrite pc T2ltnn.
by move: (phi_mono_a a pb h); rewrite pc T2ltnn.
Qed.


Lemma phi_inj1 a b b': T2nf b -> T2nf b' -> (phi a b == phi a b') = (b == b').
Proof.
move => nb nb'; case bb:(b== b'); first by rewrite (eqP bb) eqxx.
by apply /negP => /eqP /(phi_inj nb nb') => /eqP; rewrite bb.
Qed.

(** Two lemmas for equal or less-than *)

Lemma phi_eqE a b a' b': T2nf a -> T2nf a' ->  T2nf b -> T2nf b' ->
   (phi a b == phi a' b') =
    (if a < a' then  b == phi a' b'
     else if a' < a then phi a b == b' else  b== b').
Proof.
move => na na' nb nb'.
case: (T2ltgtP a a') => h.
+ move: (T2lt_le_trans h  (phi_le1 a' b')) => sa.
  have sb: phi a (phi a' b') = phi a' b' by rewrite (phi_ap a' b') /= sa.
  by rewrite - {1} sb; apply: phi_inj1 => //; apply: nf_phi.
+ move: (T2lt_le_trans h (phi_le1 a b)) => sa.
  have sb: phi a' (phi a b) = phi a b by rewrite (phi_ap a b) /= sa.
  by rewrite - {1} sb; apply: phi_inj1 => //; apply: nf_phi.
+ by rewrite h;apply: phi_inj1.
Qed.

Lemma phi_ltE a b a' b': T2nf a -> T2nf a' ->  T2nf b -> T2nf b' ->
   (phi a b < phi a' b') =
    (if a < a' then  b < phi a' b'
     else if a' < a then phi a b < b' else  b < b').
Proof.
move => na na' nb nb'.
case: (T2ltgtP a a') => h.
+ move: (T2lt_le_trans h  (phi_le1 a' b')) => sa.
  have sb: phi a (phi a' b') = phi a' b' by rewrite (phi_ap a' b') /= sa.
  by rewrite - {1} sb phi_mono_c //; apply: nf_phi.
+ move: (T2lt_le_trans h (phi_le1 a b)) => sa.
  have sb: phi a' (phi a b) = phi a b by rewrite (phi_ap a b) /= sa.
  by rewrite - {1} sb phi_mono_c //; apply: nf_phi.
+ by rewrite h phi_mono_c.
Qed.

(** Every [x] is uniquely a phi with some conditions *)

Lemma phi_inv0  a b a' b': 
  phi a b = phi a' b' -> b < phi a b -> b' < phi a' b' -> a = a'.
Proof.
move => sa sb sc.
have ->: a = T2_pr1 (phi a b).
  case: (phi_cases a b); last by move => [] ->.
  case => h; [by move: sb; rewrite h T2ltnn | by rewrite h].
have ->: a' = T2_pr1 (phi a' b').
  case: (phi_cases a' b'); last by move => [] ->.
  case => h; [by move: sc; rewrite h T2ltnn | by rewrite h].
by rewrite sa.
Qed.

Lemma phi_inv2 a b a' b': 
  phi a b = phi a' b' -> b < phi a b -> b' < phi a' b' -> b = b'.
Proof.
move => sa sb sc.
move: (phi_inv0 sa sb sc) => aa.
have sd: phi a b = [a, b] \/ phi a b = [a, T2pred b] /\ b = T2succ (T2pred b).
  case: (phi_cases a b); last by right.
  case => h; [by move: sb; rewrite h T2ltnn | by left].
have se: phi a b = [a, b'] \/ 
   phi a b = [a, T2pred b'] /\ b' = T2succ (T2pred b').
   rewrite sa aa; case: (phi_cases a' b'); last by right.
  case => h; [by move: sc; rewrite h T2ltnn | by left].
case sd; case se.
+ by move => ->; case => ->.
+ move => [ta tb] tc.
  move: (ta); rewrite tc; case => td; rewrite - td in tb.
  move: sa; rewrite tb - aa tc => h.
  symmetry in h; move: (phi_inv1 h) => [n [pa pb]].
  move: tc; rewrite pa /= pb; case n => //=.
  move => hh.
    by move: (T2lt_psi_b a  [T2_pr1 b, T2_pr2 b]); rewrite - hh T2ltnn.
  move => n' /=; case; case n' => //n'' /=; case => hb.
  by move: (n_Sn n''); rewrite - hb.
+ move =>tc  [ta tb].
  move: (ta); rewrite tc; case => td; rewrite - td in tb.
  have h:phi a (T2succ b') = [a, b'] by rewrite - tb.
  move: (phi_inv1 h) => [n [pa pb]].
  move: tc; rewrite sa - aa pa /= pb; case n => //=.
  move => hh.
    by move: (T2lt_psi_b a  [T2_pr1 b', T2_pr2 b']); rewrite - hh T2ltnn.
  move => n' /=; case; case n' => //n'' /=; case => hb.
  by move: (n_Sn n''); rewrite - hb.
+ by move => [-> u1] [v1 ->]; rewrite u1; move: v1; case => ->.
Qed.

Lemma phi_inv3 x: 
 T2ap x -> { a: T2 &  { b: T2 | 
    [/\ x = phi a b, b < x,  (size a <  size x)%N & (size b < size x)%N ] }}.
Proof.
case x => // a b n c /= /andP [/eqP -> /eqP ->]; clear n c.
simpl; rewrite maxn0.
case b; first by exists a, zero; rewrite maxn0 //.
move => a1 b1 n1 c1 /=; set u := maxn _ _.
move: (size_prop1 a1 b1 n1 c1);  set l := size (cons a1 b1 n1 c1).
move => [s1 s2 s3 s4].
have uv: u = maxn (size a) l by [].
have sa1: (size a < u.+1)%N by rewrite uv ltnS; apply: leq_maxl.
case pa: (a < a1); last first.
  exists a,(cons a1 b1 n1 c1); rewrite /= pa !andbF if_same.
  split => //; first by apply: T2lt_psi_b. 
  rewrite ltnS /u; set ww := maxn _ _; apply: leq_maxr.
have aux:((maxn (size a1)(maxn (size b1)(maxn 0 (maxn 0 0)).+1)).+1 < u.+1)%N.
  rewrite !max0n ltnS /u maxnA maxnA; set w := (maxn (size a1) (size b1)).
  apply: (@leq_trans (maxn w (size c1)).+1); last by apply: leq_maxr.
  rewrite ltnS {1} /maxn ltnS leqn0; case wz: (w==0); last by apply:leq_maxl.  
  move: pa wz; rewrite /w /maxn; case wz1: (size a1 < size b1)%N.
    by move => sa sb; move: wz1; rewrite (eqP sb) ltn0.
  by case a1 => //; rewrite T2ltn0.
case pb:((n1 == 0) && (c1 == zero)); last first.
  case pc: ((n1 == 0) && T2finite1 c1); last first.
    exists a,(cons a1 b1 n1 c1); rewrite /= pa pb pc /=. 
    split => //; first by apply: T2lt_psi_b. 
    rewrite ltnS /u; set ww := maxn _ _; apply: leq_maxr.
  move: pb; case /andP: pc => [/eqP n0 ]; rewrite n0 eqxx.
  case c1 => // a2 b2 n2 c2 /and3P [/eqP -> /eqP -> /eqP] -> _.
  exists a, (cons a1 b1 0 (cons zero zero n2.+1 zero)).
  rewrite /= pa; split => //.
  rewrite T2lt_consE /lt_psi pa (T2lt_anti pa) (T2lt_ne' pa) /=.
  rewrite T2lt_consE ltnn  T2lt0n !eqxx /= if_same //.
move/andP: pb => [/eqP -> /eqP ->].
exists a, (cons a1 b1 0 one); rewrite /= pa; split => //.
by rewrite psi_lt1; apply: T2lt_psi_b.
Qed.


(** Expression psi in terms of phi *)
Definition psi_phi_aux a b :=
  let (b', n) := T2split b in if phi a b' == b' then (T2succ b) else b.

Definition psi_phi a b := phi a (psi_phi_aux a b).

Lemma psi_phi1 a b (c:= psi_phi_aux a b): c < phi a c.
Proof.
move: (phi_ab_le1 a c); case /orP => // /eqP h.
symmetry in h;move: (phi_fix2 h).
case aux: (b == [T2_pr1 b, T2_pr2 b]).
  case h1: ([T2_pr1 b, T2_pr2 b] == one).
    rewrite /c /psi_phi_aux (eqP aux) /= h1 /=.
    by move => /= [pa]; move: (eqP h1) => [->]; rewrite T2ltn0.
  move: (erefl c); rewrite {2} /c /psi_phi_aux (eqP aux) /= h1 - (eqP aux).
  case h2: (phi a b == b); first by move => ->; case.
  by move => e1 _; move: h2; rewrite - e1 h eqxx.
rewrite /c /psi_phi_aux; case: (T2split b) => u _.
case h1: (phi a u == u); last by move => [h2 _]; move: aux; rewrite - h2 eqxx.
case; case b => //; first by rewrite T2ltn0.
move => a1 b1 n1 c1 /=.
case h2: ([a1, b1] == one) => /=; first by rewrite T2ltn0.
by case => _ h3; move: (succ_nz c1); rewrite h3.
Qed.

End Gamma0.

(** * Ackermann *)

(* Like T1 and T2 above, with one more argument *)

Module Ackermann.
Declare Scope ak_scope.
Delimit Scope ak_scope with ak.
Open Scope ak_scope.


Inductive T3 : Set :=
  zero : T3
| cons : T3 -> T3 -> T3 -> nat -> T3 -> T3.

Fixpoint T3eq x y {struct x} :=
  match x, y with 
  | zero, zero  => true
  | cons a b c n d, cons a' b' c' n' d' => 
      [&& T3eq a a', T3eq b b', T3eq c c', n== n' & T3eq d d' ] 
  | _, _ => false
end.

Lemma T3eqP : Equality.axiom T3eq.
Proof.
move=> x y; apply: (iffP idP) => [|<-].
  elim: x y; first by case => [ // | a b c n d//].
  by move => a H1 b H2 c H3 n d H4;case => // a' b' c' n' d'
    /= /andP [/H1 ->]  /andP [/H2 ->]  /andP [/H3 ->]  /andP [/eqP -> /H4 ->].
by elim: x => // a Ha b Hb c Hc n d Hd; rewrite /= Ha Hb Hc Hd eqxx.
Qed.


Canonical T3_eqMixin := EqMixin T3eqP.
Canonical T3_eqType := Eval hnf in EqType T3 T3_eqMixin.

Arguments T3eqP {x y}.
Prenex Implicits T3eqP.

Lemma T3eqE a b c n d a' b' c' n' d':
  (cons a b c n d == cons a' b' c' n' d') = 
      [&& a == a', b == b', c == c', n== n' & d == d' ].
Proof. by []. Qed.

Notation "[ x , y , z ]" := (cons x y z 0 zero) (at level 0) :ak_scope.
Definition T3nat p := if p is n.+1 then cons zero zero zero n zero else zero.
Notation "\F n" := (T3nat n)(at level 29) : ak_scope.

Fixpoint size x :=
  if x is cons a b c n d then 
     (maxn (size a) (maxn (size b) (maxn (size c) (size d)))).+1
  else 0.


Lemma size_a a b c n d: (size a < size (cons a b c n d))%N.
Proof. by rewrite /= ltnS leq_maxl. Qed.

Lemma size_b a b c n d: (size b < size (cons a b c n d))%N.
Proof. by rewrite /= ltnS maxnCA leq_maxl. Qed.

Lemma size_c a b c n d: (size c < size (cons a b c n d))%N. 
Proof. by rewrite /= ltnS maxnC - maxnA maxnC - !maxnA leq_maxl. Qed.

Lemma size_d a b c n d: (size d < size (cons a b c n d))%N. 
Proof. 
by rewrite /= ltnS maxnC - maxnA maxnC (maxnC (size c)) - !maxnA leq_maxl.
Qed.

Lemma size_psi a b c n d: (size [a, b, c] <= size (cons a b c n d))%N.
Proof. by rewrite ltnS maxn0 !maxnA leq_maxl. Qed.

Lemma size_prop1 a b c n d (l:= size (cons a b c n d)):
   [&& size a < l, size b < l, size c < l,  size d < l 
   & size [a, b, c] <= l]%N.
Proof. by rewrite size_a size_b size_c size_d size_psi. Qed.


Lemma size_prop a b c n d a' b' c' n' d'
   (l := ((size (cons a b c n d) + size (cons a' b' c' n' d')))%N) :
  [&& (size a' + size a < l), (size b + size b' < l),
   (size c + size c' < l), (size d + size d' < l),
   (size a + size a' < l), (size b' + size b < l),
   (size [a, b, c] + size b' < l),(size b + size [a', b', c'] < l),
   (size [a, b, c] + size c' < l) &(size c + size [a', b', c'] < l)]%N.
Proof.
have /and5P [pa pb pc pd pe] := (size_prop1 a b c n d). 
have /and5P [pa' pb' pc' pd' pe'] :=  (size_prop1 a' b' c' n' d').
rewrite (addnC (size a')) (addnC (size b')).
rewrite (ltn_add_ll pa pa') (ltn_add_ll pc pc') (ltn_add_ll pb pb').
rewrite (ltn_add_ll pd pd') (ltn_add_el pe pb') (ltn_add_el pe pc').
by rewrite (ltn_add_le pb pe') (ltn_add_le pc pe').
Qed.


(** ** Comparison *)

Definition lt_psi_rec f a b c a' b' c' (x := [a,b,c])(x':= [a', b', c']):=
  [|| [&& a==a', b==b' & f c c'],
      [&& a==a', f b b' & f c x'],
      [&& a==a', f b' b & f x c'],
      [&& a==a', f b' b & x == c'],
      [&& f a a', f b x' & f c x'],
      ((f a' a) && f x b'),
      ((f a' a) && (x == b')),
      ((f a' a) && f x c') |
      ((f a' a) && (x == c'))].

Definition lt_rec f x y :=
 if x is cons a b c n d then
   if y is cons a' b' c' n' d' then
     if (lt_psi_rec f a b c a' b' c') 
     then true
     else if ((a== a') && (b==b') && (c==c')) then
       if (n < n')%N then true 
       else if (n == n') then  (f d d') else false
       else false 
   else false 
 else if y is cons a' b' c' n' d' then true else false.

Fixpoint T3lta k {struct k}:=
 if k is k.+1 then lt_rec (T3lta k) else fun x y => false.


Definition T3lt a b :=  T3lta ((size a) + size b).+1 a b.
Definition T3le (x y :T3) := (x == y) || (T3lt x y).
Notation "x < y" := (T3lt x y) : ak_scope.
Notation "x <= y" := (T3le x y) : ak_scope.
Notation "x >= y" := (y <= x) (only parsing) : ak_scope.
Notation "x > y"  := (y < x) (only parsing)  : ak_scope.


Lemma T3ltE x y : x < y  = lt_rec T3lt x y.
Proof.
have aux: forall n x y, 
     ((size x + size y) < n)%N -> T3lta n x y = (x < y).
   clear x y;move => n; elim: n {1 3 4} n (leqnn n); first by case.
  move => k0 Hrec [] // k1; rewrite ltnS => k1k0.
  case => // a b c n d [] // a' b' c' n' d'.
  rewrite /T3lt; set l := (_ + _)%N; rewrite ltnS => e3.
  have e4 := (leq_trans e3 k1k0).
  move: (size_prop a b c n d a' b' c' n' d'); rewrite -/l.
  move/and5P=> [pa pb pc pd] /and5P [pe pf pg ph] /andP [pi pj].
  rewrite /T3lta /lt_rec -/lt_rec -/T3lta /lt_psi_rec.
  by rewrite ! Hrec //; apply:(leq_trans _ e3).
case x => // a b c n d; case:y => // a' b' c' n' d'.
move: (size_prop a b c n d a' b' c' n' d').
move/and5P=> [pa pb pc pd] /and5P [pe pf pg ph] /andP [pi pj].
rewrite  /lt_rec {1} /T3lt /T3lta -/T3lta {1} /lt_rec -/lt_rec.
by rewrite /lt_psi_rec !aux.
Qed.

Definition lt_psi (a b c a' b' c': T3):=
 [|| [&& a==a', b==b' & c < c'],
      [&& a==a', b < b' & c < [a',b',c']],
      [&& a==a', b' < b & [a,b,c] < c'],
      [&& a==a', b' < b & [a,b,c] == c'],
      [&& a < a', b < [a',b',c'] & c < [a',b',c']],
      ((a' < a) && ([a,b,c] < b')),
      ((a' < a) && ([a,b,c] == b')),
      ((a' < a) && ([a,b,c] < c')) |
      ((a' < a) && ([a,b,c] == c'))].

Lemma T3lt_psi a b c  a' b' c': [a,b,c] < [a', b',c'] = lt_psi a b c a' b' c'.
Proof. by rewrite {1} T3ltE /lt_rec ltnn if_same if_simpl.  Qed.


Lemma T3lt_consE a b c n d  a' b' c' n' d' : 
   cons a b c n d < cons a' b' c' n' d' =
     if ([a, b, c] < [a', b', c']) then true
     else if ([a, b, c] == [a', b', c']) then
       if (n < n')%N then true 
       else if (n == n') then  (d < d') else false
       else false. 
Proof.
by rewrite {1} T3ltE T3lt_psi T3eqE eqxx !andbT andbA.
Qed.


Lemma T3ltn0 x: (x < zero) = false.         Proof. by case x. Qed.
Lemma T3lt0n x: (zero < x) = (x != zero).   Proof. by case: x. Qed.

Lemma T3ltnn x: (x < x) = false.
Proof. 
elim:x => // a Ha b Hb c Hc n d Hd. 
by rewrite T3lt_consE T3lt_psi/lt_psi Ha Hb Hc Hd ltnn !andbF /= !if_same.
Qed.

Lemma T3lt_ne a b : a < b -> (a == b) = false.
Proof. by case h: (a== b) => //; rewrite (eqP h) T3ltnn. Qed.

Lemma T3lt_ne' a b : a < b -> (b == a) = false.
Proof. rewrite eq_sym; apply /T3lt_ne. Qed.

Lemma T3ltW a b : (a < b) -> (a <= b). 
Proof. by rewrite /T3le => ->; rewrite orbT. Qed.

Lemma T3le_eqVlt a b : (a <= b) = (a == b) || (a < b).
Proof. by []. Qed.

Lemma T3lt_neAle a b : (a < b) = (a != b) && (a <= b).
Proof.  
by rewrite T3le_eqVlt; case h: (a < b);[ rewrite (T3lt_ne h) | case(a==b) ].
Qed.

Definition one := [zero,zero,zero].
Definition omega := [zero,zero, one].
Definition epsilon0 :=  [zero, one, zero].
Definition T3bad := cons zero zero zero 0 one.

Lemma T3le0n x: zero <= x.                  Proof. by case: x. Qed.
Lemma T3len0 x: (x <= zero) = (x == zero).  Proof. by case: x. Qed.

Lemma T3ge1 x:  (one <= x) = (x != zero).
Proof. 
by case: x  => //; case => //; case => //; case => //; case => //; case. 
Qed.

Lemma T3lt1 x: (x < one) = (x==zero).
Proof. 
by case x => //;case => //; case => //; case => //; case => //;case. 
Qed.

Lemma T3lcp0_pr x y: x < y -> (y==zero) = false.
Proof.
by move => xy; apply /negP => yz; move: xy; rewrite (eqP yz) T3ltn0.
Qed.

Lemma finite_ltP n p : (n < p)%N = (\F n < \F p).
Proof.
case: p => //; first by rewrite T3ltn0 ltn0.
by case: n => // n p //=; rewrite T3lt_consE ltnS if_same if_simpl. 
Qed.


Lemma T3lt_anti b a: a < b -> (b < a) = false.
Proof.
set n := (size a + size b).+1.
move: (leqnn n); rewrite {1}/n; move: n.
move => n; elim: n a b; first by move  => a b //;rewrite ltn0.
move => m Hrec a b; rewrite ltnS.
case: a b; [ by case | move => a b c n d;case => // => a' b' c' n' d'].
set l:= (size (cons a b c n d) + size (cons a' b' c' n' d'))%N => lm.
have Hr : forall a b , (size a + size b < l)%N -> a < b -> (b < a) = false.
  by move => u v ll; apply: Hrec; apply: (leq_trans ll lm).
move: (size_prop a b c n d a' b' c' n' d'); rewrite -/l.
move/and5P=> [pa pb pc pd] /and5P [pe pf pg ph] /andP [pi pj].
rewrite T3lt_consE T3lt_psi T3lt_consE T3lt_psi !T3eqE /lt_psi.
case qa: (a < a').
  rewrite (Hr a a' pe qa) (T3lt_ne qa) (T3lt_ne' qa) !andFb /= !orbF if_simpl.
  move => /andP [qc qd]; rewrite (T3lt_ne' qc)  (T3lt_ne' qd). 
  by rewrite (Hr _ _ ph qc) (Hr _ _ pj qd).
case qa': (a' < a).
   rewrite (T3lt_ne qa') (T3lt_ne' qa') /= !orbF !if_simpl; case /or4P.
   + by move /(Hr _ _ pg)  ->.
   + by move /eqP ->; rewrite T3ltnn.
   + by move /(Hr _ _ pi) ->; rewrite andbF.
   + by move /eqP ->; rewrite T3ltnn andbF.
rewrite /= (eq_sym a' a) (eq_sym b' b) (eq_sym c' c) (eq_sym n' n).
case aa: (a== a') => //=.
case qb: (b < b').
  rewrite (T3lt_ne qb) (Hr _ _ pb qb) /= !orbF !if_simpl => h.
  by rewrite (Hr _ _ pj h) (T3lt_ne' h).
case qb': (b' < b).
  rewrite (T3lt_ne' qb') /=  orbF !if_simpl. 
  by case /orP => h; [rewrite (Hr _ _ pi h) | rewrite (eqP h) T3ltnn ]. 
case bb: (b== b') => //=.
case qc: (c < c'); first by rewrite (Hr c c' pc qc) (T3lt_ne qc).
case qc': (c' < c); first by rewrite (T3lt_ne' qc').
by case cc: (c== c') => //=;case: (ltngtP n n') => // _; apply: Hr.
Qed.

Lemma T3lt_trichotomy a b: [|| (a< b), (a==b) | (b < a)].
Proof.
set n := (size a + size b).+1.
move: (leqnn n); rewrite {1}/n; move: n.
move => n; elim: n a b; first by move  => a b //;rewrite ltn0.
move => m Hrec a b; rewrite ltnS.
case: a b; [ by case | move => a b c n d;case => // => a' b' c' n' d'].
set l:= (size (cons a b c n d) + size (cons a' b' c' n' d'))%N => lm.
have Hr : forall a b , (size a + size b < l)%N ->
    [|| (a< b), (a==b) | (b < a)]
  by move => u v ll; apply: Hrec; apply: (leq_trans ll lm).
move: (size_prop a b c n d a' b' c' n' d'); rewrite -/l.
move/and5P=> [pa pb pc pd] /and5P [pe pf pg ph] /andP [pi pj].
rewrite T3lt_consE T3lt_psi T3lt_consE T3lt_psi !T3eqE /lt_psi.
case /or3P:(Hr _ _ pa) => caa'; last 1 first.
+ rewrite caa' (T3lt_anti caa') (T3lt_ne caa') (T3lt_ne' caa') !orbF !if_simpl.
  rewrite /= (eq_sym _ c) (eq_sym _ b). 
  case /or3P: (Hr _ _ pj) => ->; rewrite ?orbT //=.
  by case /or3P: (Hr _ _ ph) => -> //=; rewrite ?orbT.
+ rewrite caa' (T3lt_anti caa') (T3lt_ne caa')(T3lt_ne' caa') !orbF !if_simpl.
  case /or3P: (Hr _ _ pg) => ->; rewrite ?orbT //=.
  case /or3P: (Hr _ _ pi) => ->; rewrite ?orbT //=.
+ rewrite caa' (eqP caa') T3ltnn eqxx /= !orbF.
  case /or3P:(Hr _ _ pb) => cbb'; last 1 first.
  *  rewrite cbb' (T3lt_anti cbb') (T3lt_ne' cbb'). simpl.
     by case /or3P: (Hr _ _ pi) => h; rewrite h /= ? orbT.
  * rewrite cbb' (T3lt_anti cbb') (T3lt_ne cbb') (T3lt_ne' cbb') (eq_sym _ c).
    by rewrite -(eqP caa'); case /or3P:(Hr _ _ pj) => h; rewrite h ?orbT.
  * rewrite (eqP cbb') T3ltnn !eqxx /=.
    case /or3P: (Hr _ _ pc) => h; rewrite h // ?orbT //(eqP h) T3ltnn eqxx /=.
    case (ltngtP n n') => // _; rewrite Hr //.
Qed.

Lemma T3lenn x: x <= x.   
Proof. by rewrite /T3le eqxx. Qed.

#[local] Hint Resolve T3lenn : core.

Lemma T3leNgt a b:  (a <= b) = ~~ (b < a).
Proof.
case /or3P: (T3lt_trichotomy a b).
- by move => h; rewrite (T3lt_anti h) (T3ltW h).
- by move /eqP ->; rewrite T3ltnn T3lenn.
- by move => h; rewrite h /T3le (T3lt_anti h) (T3lt_ne' h).
Qed.

Lemma T3ltNge a b:  (a < b) = ~~ (b <= a).
Proof. by rewrite T3leNgt negbK. Qed.

Lemma T3eq_le m n : (m == n) = ((m <= n) && (n <= m)).
Proof.
rewrite /T3le (eq_sym n m);case eqmn: (m == n) => //=.
by case lt1: (m < n) => //; rewrite (T3lt_anti lt1).
Qed.


CoInductive T3ltn_xor_geq m n : bool -> bool -> Set :=
  | T3LtnNotGeq of m < n  : T3ltn_xor_geq m n false true
  | T3GeqNotLtn of n <= m : T3ltn_xor_geq m n true false.

CoInductive T3leq_xor_gtn m n : bool -> bool -> Set :=
  | T3GeqNotGtn of m <= n : T3leq_xor_gtn m n true false
  | T3GtnNotLeq of n < m  : T3leq_xor_gtn m n false true.


CoInductive compare_T3 m n : bool -> bool -> bool -> Set :=
  | CompareT3Lt of m < n : compare_T3 m n true false false
  | CompareT3Gt of m > n : compare_T3 m n false true false
  | CompareT3Eq of m = n : compare_T3 m n false false true.


Lemma T3leP x y : T3leq_xor_gtn x y (x <= y) (y < x).
Proof.
by rewrite T3ltNge; case le_xy: (x <= y); constructor;rewrite // T3ltNge le_xy.
Qed.

Lemma T3ltP m n : T3ltn_xor_geq m n (n <= m) (m < n).
Proof. by case T3leP; constructor. Qed.

Lemma T3ltgtP m n : compare_T3 m n (m < n) (n < m) (m == n).
Proof.
rewrite T3lt_neAle T3eq_le;case: T3ltP; first by constructor.
by rewrite T3le_eqVlt orbC; case: T3leP; constructor; first exact /eqP.
Qed.


Lemma T3le_consE a b c n d  a' b' c' n' d' : 
   cons a b c n d <= cons a' b' c' n' d' =
     if ([a, b, c] < [a', b', c']) then true
     else if ([a, b, c] == [a', b', c']) then
       if (n < n')%N then true 
       else if (n == n') then  (d <= d') else false
       else false. 
Proof.
rewrite /T3le T3lt_consE; case: (T3ltgtP [a, b, c]  [a', b', c']) => //.
+ by rewrite orbT.
+ move => h; rewrite orbF; apply /negP => /eqP h'. 
  by move: h; case : h' => -> -> ->; rewrite T3ltnn.
+ case =>  -> -> ->; case (ltngtP n n'); rewrite ?orbF ? orbT //.
    move => nn; apply /negP => /eqP h'.
    by move: nn; case : h' => ->; rewrite ltnn.
  by move => ->; rewrite T3eqE !eqxx /=.
Qed.

Lemma T3lt_psi' a b c a' b' c': [a, b, c] < [a', b', c' ] =
  [|| [&& a==a', b==b' & c < c'],
      [&& a==a', b < b' & c < [a', b', c'] ],
      [&& a==a', b' <b & [a,b,c] <= c'],
      [&& a < a', b < [a', b', c'] & c < [a', b', c']],
      ((a' < a) && ([a,b,c] <= b')) |
      ((a' < a) && ([a,b,c] <= c'))].
Proof.
rewrite T3lt_psi /lt_psi; case: (T3ltgtP a a') => //=.
  by rewrite orbA (orbC (_ < b')) -/(T3le _ _)  (orbC (_ < c')) -/(T3le _ _).
case: (T3ltgtP b b') => //=.
by rewrite !orbF orbC.
Qed.


Theorem T3lt_trans b a c: a < b -> b < c -> a < c.
Proof.
set n := (size a + size b + size c).+1.
move: (leqnn n); rewrite {1}/n; move: n.
move => n; elim: n a b c; first by move  => a b c//;rewrite ltn0.
move => m Hrec []; first by case; [rewrite T3ltn0 | move => a b c n d; case].
move => a b c n d []; [ by rewrite T3ltn0 | move => a' b' c' n' d'].
case; [ by rewrite T3ltn0 | move => a'' b'' c'' n'' d'']; rewrite ltnS => la.
have Hr1: forall v u w, (size u < size (cons a b c n d))%N -> 
  (size v <= size (cons a' b' c' n' d'))%N -> 
  (size w <= size (cons a'' b'' c'' n'' d''))%N -> u < v -> v < w -> u < w.
  move => u v w sa sb sc; apply: Hrec; apply: leq_trans la.
  by rewrite ltn_add_le // ltn_add_le.
have Hr2: forall v u w, (size u <= size (cons a b c n d))%N -> 
  (size v < size (cons a' b' c' n' d'))%N -> 
  (size w <= size (cons a'' b'' c'' n'' d''))%N -> u < v -> v < w -> u < w.
  move => u v w sa sb sc; apply: Hrec; apply: leq_trans la.
  by rewrite ltn_add_le// ltn_add_el.
have Hr3: forall v u w, (size u <= size (cons a b c n d))%N -> 
  (size v <= size (cons a' b' c' n' d'))%N -> 
  (size w < size (cons a'' b'' c'' n'' d''))%N -> u < v -> v < w -> u < w.
  move => u v w sa sb sc; apply: Hrec; apply: leq_trans la.
  by rewrite ltn_add_el // leq_add.
move: (size_prop1 a b c n d) => /and5P [pa pb pc pd pe].
move: (size_prop1 a' b' c' n' d') => /and5P [pa' pb' pc' pd' pe'].
move: (size_prop1 a'' b'' c'' n'' d'') => /and5P [pa'' pb'' pc'' pd'' pe''].
rewrite T3lt_consE (T3lt_consE a')  (T3lt_consE a _ _ _ _ a'').
case (T3ltgtP [a, b, c] [a', b', c']) => //; last first.
  move => <-; case (T3ltgtP [a, b, c] [a'', b'', c'']) => //.
  move => _; case (ltngtP n n') => //.  
    move => nn'; case (ltngtP n' n'') =>//. 
      by move => nn''; rewrite (ltn_trans nn' nn'').
    by move => <-; rewrite nn'.
  by move => <- dd'; case (ltngtP n n'') => // _ dd''; rewrite (Hr1 d') // ltnW.
move => lta _; case (T3ltgtP [a', b', c'] [a'', b'', c'']) => //; last first.
  by move => <-; rewrite lta.
move => ltb _; apply: ifT.
move: (lta) (ltb); rewrite !T3lt_psi /lt_psi.
case (T3ltgtP a a') => qa.
+ rewrite /= !orbF => /andP [lx ly].
  have ha: [a,b,c] < [a',b',c'] by rewrite T3lt_psi /lt_psi qa lx ly !orbT.
  case: (T3ltgtP a' a'') => qb.
  - rewrite /= !orbF => /andP [lz lt].
    rewrite (Hr1 a' a a'' pa (ltnW pa') (ltnW pa'') qa qb).
    rewrite (Hr1 [a', b', c'] b [a'', b'', c''] pb pe' pe'' lx ltb).
    by rewrite (Hr1 [a', b', c'] c [a'', b'', c'']) // !orbT.
  - move => /= h; case: (T3ltgtP a'' a) => qc.
    * rewrite (T3lt_ne' qc) /=; case/or4P:h => h.
      + by rewrite (Hr3  [a', b', c']). 
      + by rewrite - (eqP h) ha.
      + by rewrite (Hr3 [a', b', c'] [a,b,c] c'') ?orbT. 
      + by rewrite - (eqP h) ha !orbT.
    * rewrite (T3lt_ne qc) /= orbF.
      by rewrite (Hr1 _ _ _ pb pe' pe'' lx ltb)  (Hr1 _ _ _ pc pe' pe'' ly ltb).
    * rewrite qc eqxx /= -qc (Hr1 _ _ _ pc pe' pe'' ly ltb).
      move: h; case: (T3ltgtP [a', b', c'] b'') => h; last 1 first.
          by rewrite - h lx !orbT.
        by rewrite (Hr1 _ _ _ pb pe' (ltnW pb'') lx h) orbT.
     rewrite /= qc => h1.
     have [-> ->] : [a, b, c] < c'' /\ c < c''.
        case /orP:h1 => h1; last by rewrite - (eqP h1).
          rewrite (Hr1 _ _ _ pc pe' (ltnW pc'') ly h1).
        by rewrite (Hr3 [a', b', c']). 
     by rewrite !andbT; case: (T3ltgtP b b'').
  -  have/andP [sa sb]: (b < [a'', b'', c'']) && (c < [a'', b'', c'']).
       by rewrite (Hr1 [a', b', c']) // (Hr1 [a', b', c']) //.
     by rewrite sa sb -qb qa  /= !orbT.
+ move => /= lt1; case: (T3ltgtP a'' a') => qb.
  - have qc: (a'' < a).
      rewrite (Hrec a'' a' a) //; apply:leq_trans la. 
      by rewrite addnC (addnC (size a'')) addnA !ltn_add_ll.
    rewrite qc (T3lt_anti qc) (T3lt_ne' qb)  (T3lt_ne' qc) /=.
    case /or4P => h. 
    * by rewrite (Hr3 [a', b', c']).
    * by rewrite - (eqP h) lta.
    * by rewrite (Hr3 [a', b', c'] [a,b,c] c'') // !orbT.
    * by rewrite - (eqP h) lta !orbT.
  - rewrite (T3lt_ne qb) /= orbF  => /andP [sa sb].
    rewrite  -/(lt_psi a b c a'' b'' c'') -(T3lt_psi); case /or4P:lt1 => h.
    * by apply: (Hr2  b').
    * by rewrite (eqP h).
    * by apply: (Hr2 c').
    * by rewrite (eqP h). 
  - rewrite qb eqxx qa  (T3lt_ne' qa) (T3lt_anti qa)/= -{1} qb.
    case: (T3ltgtP b' b'') => qc. 
    * rewrite /= orbF => qd; case /or4P: lt1 => lt1.
      + by rewrite (Hr2 b') // ltnW.
      + by rewrite (eqP lt1) qc.
      + move: (Hr2 c' [a, b, c] [a'',b'',c''] pe pc' pe'' lt1 qd).
        by rewrite T3lt_psi /lt_psi qb qa  (T3lt_ne' qa) (T3lt_anti qa).
      + move: qd; rewrite -(eqP lt1) T3lt_psi /lt_psi.
        by rewrite qb qa (T3lt_ne' qa) (T3lt_anti qa).
    * rewrite /= orbF;case /orP =>h; last by rewrite - (eqP h) lta ! orbT.
      by rewrite (Hr3 [a', b', c'] _ c'') // !orbT.
    * rewrite /= orbF - qc => qd; case /or4P: lt1 => h'; rewrite ?h' ?orbT //.
        by rewrite (Hr2 c' _ c'') ? orbT // ltnW.
      by rewrite (eqP h') qd ? orbT.
+ rewrite - qa [in [a, b', c']] qa /=; case: (T3ltgtP a a'') => qb.
  - case: (T3ltgtP b b') => qc.
    * rewrite /= !orbF  => sa /andP [sb sc].
      by rewrite (Hr1 b') // ?(ltnW pb') // (Hr1  [a', b', c']).
    * rewrite /= !orbF => sa /andP [sb sc].
      have: ([a, b, c] < [a'', b'', c'']).
        by case /orP: sa => h; [rewrite (Hr2  c') | rewrite (eqP h)].
      rewrite T3lt_psi /lt_psi qb (T3lt_ne qb) (T3lt_anti qb) orbF //.
    * by rewrite /= !orbF => qd /andP [sa sb]; rewrite qc sa (Hr1 c') // ltnW.
  - move => sa /=; case /or4P => sc.
    * by rewrite (Hr3 [a',b',c']).
    * by rewrite - (eqP sc) lta.
    * by rewrite (Hr3 [a',b',c'] _ c'') // !orbT.
    * by rewrite - (eqP sc) lta !orbT.
  - case: (T3ltgtP b b') => qc /=; rewrite !orbF => qd.
    * case: (T3ltgtP b' b'') => qe; rewrite /= ? orbF => qf.
      + rewrite (Hr1 b' b b'') // ?(ltnW pb') ?(ltnW pb'') //.
        by rewrite (Hr1 [a', b', c'] _ [a'', b'', c'']) ? orbT.
      +  case: (T3ltgtP b b'') => sa /=.
        - by rewrite (Hr1  [a', b', c']).
        - apply: ifT; case/orP: qf => qf; last by rewrite -(eqP qf).
          by apply: (Hr3 [a', b', c']).
        - case /orP: qf => qf; last by rewrite -(eqP qf) qd.
          by rewrite (Hr1 [a', b', c']) ? (ltnW pc'').
      + by rewrite  (Hr1 [a', b', c'] c [a'', b'', c'']) // - qe qc !orbT.
    * case: (T3ltgtP b' b'') => qe; rewrite /= ? orbF => qf.
      - have: [a,b,c] < [a'',b'',c''].
          by case /orP: qd =>h; rewrite ? (eqP h) // (Hr2 c').
        by rewrite T3lt_psi /lt_psi qb eqxx T3ltnn /= orbF. 
      - have ->: (b'' < b).
           rewrite (Hrec b'' b' b) //; apply:leq_trans la. 
           by rewrite addnC (addnC (size b'')) addnA !ltn_add_ll.
         case /orP: qf => qf; last by rewrite - (eqP qf) lta !orbT.
         by rewrite (Hr3 [a', b', c'] [a, b, c]) // !orbT.
      -  rewrite -qe qc /= (_: ([a, b, c] < c'')) ?orbT //. 
         by case /orP: qd => qd; rewrite ? (eqP qd) // (Hr2 c') // ltnW.
    * case: (T3ltgtP b' b'') => qe /=; rewrite ? orbF => qf.
      - by rewrite qc qe (Hr1 c' _ [a'', b'', c'']) ? orbT // ltnW.
      - rewrite [in (b''< b)] qc qe /=.
        case /orP: qf => qf; last by rewrite - (eqP qf) lta !orbT.
        by rewrite  (Hr3 [a', b', c'] [a, b, c]) // !orbT.
     - by rewrite qc qe eqxx (Hr1 c') // ltnW.
Qed.

Lemma T3lt_le_trans b a c: a < b -> b <= c -> a < c.
Proof.
by move => lab; case /orP;[  move /eqP => <- |apply:T3lt_trans].
Qed.

Lemma T3le_lt_trans b a c: a <= b -> b < c -> a < c.
Proof. by case /orP;[  move /eqP => <- |apply:T3lt_trans]. Qed.

Lemma T3le_trans b a c: a <= b -> b <= c -> a <= c.
Proof.
case /orP; first by move /eqP => ->. 
by move => l1 l2; rewrite /T3le (T3lt_le_trans l1 l2) orbT.
Qed.

Lemma T3le_anti : antisymmetric T3le.
Proof.  
move=> m n /andP [/orP []]; first by move /eqP ->.
by move => mn /(T3lt_le_trans mn); rewrite T3ltnn.
Qed.

Lemma T3le_total m n : (m <= n) || (n <= m).
Proof. 
by rewrite /T3le;case /or3P: (T3lt_trichotomy m n) => -> //; rewrite !orbT.
Qed.

Lemma T3le_psi a b c n d: [a,b,c] <= cons a b c n d.
Proof.
rewrite /T3le T3lt_consE T3ltnn T3eqE !eqxx T3lt0n (eq_sym 0) (eq_sym d) /=. 
by case: (ltngtP n 0) => //=; case: eqP.
Qed.

Lemma T3lt_psi_bc  a b c: ((b < [a,b,c]) && (c < [a, b, c])).
Proof.
move: a b c.
suff: forall x a b c, ((x <= b) || (x <= c)) -> x < [a,b,c].
  by move => H a b c; apply/andP; split; apply:H; rewrite T3lenn // orbT.
move => x; set n := (size x).+1.
move: (leqnn n); rewrite {1}/n;move: n.
move => n; elim: n x; first by move => x //;rewrite ltn0.
move => m Hrec [] // a' b' c' n' d'; rewrite ltnS => ln.
move => a b c.
move: (size_prop1 a' b' c' n' d'); set x := (cons a' b' c' n' d').
move /and5P=> [pa pb pc pd pe].
move: (leq_trans pb ln) (leq_trans pc ln) => la lb.
have sa: (b' < [a',b',c']) by apply: (Hrec b' la); rewrite T3lenn.
have sb: (c' < [a',b',c']) by apply: (Hrec c' lb); rewrite T3lenn orbT.
case /orP => ha.
  rewrite T3lt_consE; apply: ifT; rewrite /lt_psi.
  have aux := (T3le_trans (T3le_psi a' b' c' n' d') ha).
  move: (T3lt_le_trans sa aux) (T3lt_le_trans sb aux) => sa' sb'.
  have sc: (b' < [a,b,c]) by apply:(Hrec b' la); rewrite (T3ltW sa').
  have sd: (c' < [a,b,c]) by apply:(Hrec c' lb);rewrite (T3ltW sb').
  move: aux; rewrite /T3le orbC => aux.
  rewrite T3lt_psi /lt_psi sa' sc sd /=.
  by case: (T3ltgtP a' a) => //; rewrite ?orbT //= orbA aux.
rewrite T3lt_consE; apply: ifT; rewrite /lt_psi.
have aux:= (T3le_trans (T3le_psi a' b' c' n' d') ha).
move: (T3lt_le_trans sa aux) (T3lt_le_trans sb aux) => sa' sb'.
have sc: (b' < [a,b,c]) by apply:(Hrec b' la); rewrite (T3ltW sa') orbT.
have sd: (c' < [a,b,c]) by apply:(Hrec c' lb); rewrite (T3ltW sb') orbT.
move: aux; rewrite /T3le orbC => aux.
rewrite T3lt_psi /lt_psi  sb' sc sd /=.
case: (T3ltgtP a' a) => //=; first by rewrite aux !orbT.
by case: (T3ltgtP b' b) => //=; rewrite orbF aux.
Qed.

Lemma psi_lt1 a b c d n a' b' c':
   cons a b c n d < [a', b', c'] = ([a, b,c] < [a', b', c']).
Proof. by rewrite  T3lt_consE T3lt_psi T3ltn0 ! if_same if_simpl. Qed.

Lemma psi_lt2 a b c n d n' d':  cons a b c n' d' < cons a b c n d = 
   (if (n' < n)%N then true else if n' == n then d' < d else false).
Proof. by rewrite T3lt_consE T3ltnn eqxx. Qed.

Lemma T3lt_psi_b a b c: b < [a,b,c].
Proof. by move /andP: (T3lt_psi_bc a b c) => []. Qed.

Lemma T3lt_psi_c a b c: c < [a,b,c].
Proof. by move /andP: (T3lt_psi_bc a b c) => []. Qed.

Lemma T3lt_psi_a a b c: a < [a,b,c].
move: a b c.
suff: forall x a b c, (x <= a -> x < [a,b,c]).
  by move => H a b c; apply:H; rewrite T3lenn.
move => x; set n := (size x).+1.
move: (leqnn n); rewrite {1}/n;move: n.
move => n; elim: n x; first by move => x //;rewrite ltn0.
move => m Hrec; case => // a' b' c' n' d'; rewrite ltnS => ln.
move => a b c.
move: (size_prop1 a' b' c' n' d'); set x := (cons a' b' c' n' d').
move /and5P=> [pa pb pc pd pe] ha.
move: (leq_trans pb ln) (leq_trans pc ln) => la lb.
move: (T3le_trans (T3le_psi a' b' c' n' d') ha) => aux.
have sc: (a' < [a',b',c']) by apply:(Hrec a' (leq_trans pa ln));rewrite T3lenn.
rewrite psi_lt1 T3lt_psi /lt_psi.
move: (T3lt_le_trans sc aux) => sc'.
rewrite sc' (T3lt_anti sc') (T3lt_ne sc') /=.
have sa: (b' < [a',b',c']) by apply: T3lt_psi_b.
have sb: (c' < [a',b',c']) by apply: T3lt_psi_c.
rewrite (Hrec b' la) ? (T3ltW (T3lt_le_trans sa aux))//.
rewrite (Hrec c' lb) ? (T3ltW (T3lt_le_trans sb aux))//. 
Qed.


(** ** Normal form *)

Fixpoint T3nf x :=
  if x is cons a b c _ d 
  then [&& T3nf a, T3nf b, T3nf c, T3nf d & d < [a,b,c] ]
  else true.

Lemma nf_0: T3nf zero.
Proof. by []. Qed.

Lemma nf_psi a b c: T3nf [a, b, c] = [&& T3nf a, T3nf b & T3nf c].
Proof. by rewrite  /= T3lt0n andbT. Qed.

Lemma nf_int n: T3nf (\F n).
Proof. by case n. Qed.

Lemma nf_cons_cons a b c n a' b' c' n' d':
  T3nf (cons a b c n (cons a' b' c' n' d')) = 
   [&& [a', b',c'] < [a, b,c], T3nf [a,b, c] &
    T3nf (cons a' b' c' n' d') ].
Proof. 
simpl.
case: (T3nf a);rewrite /= ?andbF //.
case: (T3nf b);rewrite /= ? andbF //.
case: (T3nf c);rewrite /= ? andbF //.
by rewrite psi_lt1 andbC.
Qed.

Lemma nf_consE a b c n d:
    T3nf (cons a b c n d) = [&& T3nf [a,b,c], T3nf d & d < [a,b,c] ].
Proof. by rewrite /T3nf -/T3nf T3lt0n /= andbT !andbA. Qed.

Lemma nf_Wf : well_founded_P T3nf T3lt.
Proof. 
have az: Acc (restrict T3nf T3lt) zero by split => y [_]; rewrite T3ltn0.
rewrite /well_founded_P. 
set r:= (restrict (fun x : T3 => T3nf x) (fun a b : T3 => a < b)).
have TV: forall a b c n d,
  T3nf (cons a b c n d) -> Acc r [a,b,c] -> Acc r (cons a b c n d).
  move => a b c n d nx ay.
  move: (nx); rewrite nf_consE => /and3P [ny nd dy].
  have aux: forall a' b' c' n' d', [a', b', c'] < [a, b, c] ->
      T3nf (cons a' b' c' n' d') -> Acc r (cons a' b' c' n' d').
     move =>  a' b' c' n' d' h nx'; set x := (cons a' b' c' n' d').
     have h': (x < [a, b, c]) by rewrite psi_lt1.
     have h'': r x [a, b, c] by split.
     exact: (acc_rec h'' ay). 
  suff h: forall n, Acc r (cons a b c n zero).
    move: (h n.+1) => h1.
    have h2: (cons a b c n d) < (cons a b c n.+1 zero).
       by rewrite T3lt_consE !eqxx ltnS leqnn /= if_same.
    have h3: r (cons a b c n d) (cons a b c n.+1 zero) by [].
    exact: (acc_rec h3 h1).
  clear nx dy nd d n. 
  elim => [// | n Hr]; split; case; first by move => _; apply:az.
  move => a' b' c' n' d' []; rewrite T3lt_consE. 
  case(T3ltgtP [a', b', c'] [a, b, c]); first by move => h h' _ h''; apply: aux.
    done.
  case; move => -> -> ->; rewrite T3ltn0 if_same if_simpl ltnS leq_eqVlt.
  move => ta;case /orP => nn'; last first.
    have h': r (cons a b c n' d') (cons a b c n zero).  
      by split => //;rewrite T3lt_consE !eqxx nn' /= if_same.
    move => _; exact: (acc_rec h' Hr).
  move: ta;rewrite (eqP nn') nf_consE => /and3P [_ nd dy]. 
  have rd: r d' [a, b, c] by split.
  elim: (acc_rec rd ay) => y Ha Hb.
  split; case; first by move => _;apply: az.
  move => a'' b'' c'' n'' d'' []; rewrite T3lt_consE. 
  case: (T3ltgtP  [a'', b'', c''] [a, b, c]).  
     by move => sa sb sc _;apply: aux.
    done.
  case => -> -> -> sa sb sc; move: sb;case: (ltngtP n'' n) => cnn dy'.
      have h'': r (cons a b c n'' d'') (cons a b c n zero).
        by split => //; rewrite  T3lt_consE !eqxx T3ltnn cnn.
      exact: (acc_rec h'' Hr).
    by case dy'. 
   move: sa sc;move/and5P => [_ _ _ ny' _] /and5P [_ _ _ nd'' _].
   by rewrite cnn; apply: Hb. 
have TIX: forall a b c, T3nf [a,b,c]  -> Acc r b -> Acc r c ->
   (forall a' b' c', r a' a -> Acc r b' -> Acc r c' -> 
       T3nf b' -> T3nf c' -> Acc r [a', b', c'])-> 
   (forall b' c', r b' b -> Acc r c'-> T3nf c' -> Acc r [a, b', c'])-> 
   (forall c', r c' c -> Acc r [a, b, c'])-> Acc r [a,b,c].
  move => a b c nanc ab ac Ha Hb Hc; split.
  move => y; set n := (size y).+1.
  move: (leqnn n); rewrite {1}/n; move: n => n.
  elim: n y => [ // | n Hr]; case; first by move => _ _; apply: az.
  move => a' b' c' n' d' ll [nu lta nv].
  apply: TV; first by exact.
  move: (nv); rewrite nf_psi => /and3P[na nb nc].
  move: nu; rewrite nf_consE => /and3P [nu _ _].
  move: (nu); rewrite nf_psi => /and3P[na' nb' nc'].
  move: (size_prop1 a' b' c' n' d') => /and5P [_ lb lc _ _].
  move:ll; rewrite  ltnS => ll. 
  move: (leq_trans lb ll)(leq_trans lc ll) => lb' lc'{lb lc}.
  move: lta; rewrite psi_lt1 T3lt_psi /lt_psi.
  case /orP; first by move /and3P => [ /eqP -> /eqP -> cc]; apply Hc.
  case /orP. 
      by move /and3P => [/eqP -> lb lc];apply: Hb; [ |apply: Hr |].
  case /orP; first by move /and3P => [_ _ lc]; apply: (acc_rec _ ac).
  case /orP; first by move /and3P => [_ _ /eqP ->].
  case /orP. 
   by  move /and3P => [la lb lc] ;apply: Ha; try apply: Hr.
  case /orP; first by move => /andP [_ h]; exact: (acc_rec (And3 nu h nb) ab).
  case /orP; first by move => /andP [_ /eqP ->].
  case /orP; first by move => /andP [_ h]; exact: (acc_rec (And3 nu h nc) ac).
  by move => /andP [_ /eqP ->].
have TX: forall a b c, T3nf [a,b,c]  -> Acc r b -> Acc r c ->
   (forall a' b' c', r a' a -> Acc r b' -> Acc r c' -> 
       T3nf b' -> T3nf c' ->  Acc r [a', b', c']) -> 
   (forall b' c', r b' b -> Acc r c' ->  T3nf c' -> Acc r [a, b', c']) -> 
   Acc r [a,b,c].
  move => a b c nabc ab ac h1 h2.
  apply: (TIX _ _ _ nabc ab ac h1 h2); elim: ac  => x Ha Hb c' cx.
  have np: T3nf [a, b, c'].
    have [nc' _ _] := cx.
    by move: nabc ; rewrite !nf_psi nc' => /and3P[-> -> _].
  by apply: (TIX a b c' np ab (Ha _ cx) h1 h2)=> w rwc;apply: (Hb c' cx).
have TXI: forall a b c, T3nf [a,b,c]  -> Acc r b -> Acc r c ->
   (forall a' b' c', r a' a -> Acc r b' -> Acc r c' ->
       T3nf b' -> T3nf c'-> Acc r [a', b', c']) -> 
   Acc r [a,b,c].
  move => a b c nabc ab ac h1.
  apply: (TX _ _ _ nabc ab ac h1); elim: ab => x Ha Hb b' c' bx ac' nc'.
  have np: T3nf [a, b', c'].
    move: (bx) => [nb' _ _].
    by move: nabc ; rewrite !nf_psi nb' nc' => /and3P[-> _ _].
  apply: (TX a b' c' np (Ha _ bx) ac' h1) => u v uv av nv.
  exact: (Hb b' bx u v uv av nv).  
have TXII:  forall a b c, T3nf [a, b, c] -> Acc r a -> Acc r b -> Acc r c ->
  Acc r [a, b, c].
  move => a b c np aa ab ac; apply: (TXI _ _ _ np ab ac).
  elim: aa => x Ha Hb a' b' c' lax ab' ac' nb' nc'.
  have np': T3nf [a', b', c'].
    by move: (lax) => [na' _ _];rewrite !nf_psi na' nb' nc'. 
  apply: (TXI a' b' c' np' ab' ac') => a'' b'' c'' r1 ab'' ac'' nb'' nc''.
  exact: (Hb a' lax a'' b'' c'' r1 ab'' ac'' nb'' nc'').
move => a; set n := (size a).+1.
move: (leqnn n); rewrite {1}/n; move: n => n.
elim: n a => [ // | n Hr]; case; first by move => _ _; apply: az.
move => a' b' c' n' d' ll nx.
move: (nx); rewrite nf_consE =>/and3P [np _ _].
move:(np); rewrite nf_psi => /and3P[na nb nc].
move /and5P: (size_prop1 a' b' c' n' d') =>  [la lb lc _ _].
move: (leq_trans la ll)(leq_trans lb ll)(leq_trans lc ll) => la' lb' lc'.
by apply:TV; [ exact | apply: TXII]; first (by exact); apply: Hr. 
Qed.

Theorem lt_not_wf : ~ (well_founded T3lt).
Proof. 
set f := (fix f i := if i is n.+1 then cons zero zero zero 0 (f n) else omega).
case/not_decreasing; exists f; elim => //.
by move => n fn; rewrite /f -/f T3lt_consE /= fn.
Qed.

(** ** Successor Predecessor *)

Fixpoint T1_T3 (c:CantorOrdinal.T1) : T3 :=
  if c is CantorOrdinal.cons a n b then cons zero zero (T1_T3 a) n (T1_T3 b)
  else zero.

Lemma lt_epsilon0 a b c n d :
  cons a b c n d < epsilon0 = [&& a==zero, b == zero & c < epsilon0 ].
Proof.
rewrite psi_lt1 T3lt_psi /lt_psi !T3ltn0 !T3lt0n !T3lt1 /= !andbF !orbF.
by case pa: (a== zero) => /=; rewrite ? orbF // T3eqE pa /=.
Qed.

Lemma T1T3_lt_epsilon0 x: T1_T3 x < epsilon0.
Proof. by elim x => // a Ha n b Hb /=;rewrite lt_epsilon0 Ha eqxx. Qed.

Delimit Scope cantor_scope with ca.
Notation "x < y" := (CantorOrdinal.T1lt x y) : cantor_scope.

Lemma T1T3_inc x y: (x <y)%ca-> (T1_T3 x) < (T1_T3 y).
Proof.
elim: x y; [by case |  move => a Ha n b Hb; case => // a' n' b'].
rewrite /= T3lt_consE T3lt_psi /lt_psi T3ltnn /=.
case: (CantorOrdinal.T1ltgtP a a') => aa' //; first by rewrite Ha //.
rewrite aa' T3ltnn eqxx /=.
case: (CantorOrdinal.T1ltgtP b b') => bb'; first by rewrite Hb.
   by rewrite if_same if_simpl => ->.
   by rewrite if_same if_simpl => ->.
Qed.


Lemma TT1T3_inj: injective T1_T3.
Proof.
move => a b h.
by case:(CantorOrdinal.T1ltgtP a b) => lab //;
   move: (T1T3_inc lab); rewrite h T3ltnn.
Qed.

Lemma T1T3_surj x: T3nf x -> x < epsilon0 -> exists y, x = T1_T3 y.
Proof.
set n := (size x).+1.
move: (leqnn n); rewrite {1}/n; move: n => n.
elim: n x => [ // | n Hr x].
case x; first by exists CantorOrdinal.zero => //.
move => a' b' c' n' d'; rewrite ltnS => lu nc.
move  /and5P: (size_prop1 a' b' c' n' d') => [la lb lc ld _].
rewrite lt_epsilon0;  move => /and3P [sa sb sc].
move: nc; rewrite nf_consE nf_psi => /and3P [/and3P [_ _ nc] nd ne].
rewrite (eqP sa) (eqP sb).
have [y yp]:= (Hr c' (leq_trans lc lu) nc sc).
have ww: [a', b', c'] < [zero, one, zero] by rewrite lt_epsilon0 /= sa sb sc.
have [y' yp'] := (Hr d' (leq_trans ld lu) nd (T3lt_trans ne ww)).
by exists (CantorOrdinal.cons y n' y') => /=; rewrite -yp - yp'.
Qed.

Definition all_zero a b c :=[&& a==zero, b==zero & c== zero].

Fixpoint T3limit x := 
  if x is cons a b c n d then 
    if (all_zero a b c) then false else (d== zero) || T3limit d
  else false.

Definition T3finite x := 
   if x is cons a b c n d then all_zero a b c else true.

Fixpoint T3split x:=
 if x is cons a b c n d then
      if  all_zero a b c then (zero, n.+1) else
     let: (x, y) := T3split d in (cons a b c n x,y)
   else (zero,0).

Lemma all_zeroE a b c: all_zero a b c = ([a,b,c] == one).
Proof. by rewrite T3eqE !eqxx !andbT. Qed.

Lemma T3nf_finite a b c n d:  all_zero a b c -> T3nf (cons a b c n d) ->
    d = zero.
Proof.
move => /and3P [/eqP -> /eqP ->] /eqP -> /and5P [_ _ _ _].
by rewrite T3lt1 => /eqP.
Qed.

Lemma split_finite x: ((T3split x).1 == zero) = T3finite x.
Proof.
case x => // a b c n d //=.
by case pa: (all_zero a b c) => //;case: T3split x.
Qed.

Lemma T3finite1 n: T3finite (\F n).  
Proof. by case:n. Qed.

Lemma T3finite2 x: T3finite x -> T3nf x -> x = \F ((T3split x).2).
Proof. 
case: x => // a b c n d; rewrite /T3finite => sa sb.
rewrite (T3nf_finite sa sb) /T3split -/T3split sa.
by move: sa => /and3P [/eqP -> /eqP -> /eqP ->].
Qed.

Lemma T3gt1 x: (one < x) = ((x != zero) && (x != one)).
Proof.
case: (T3ltgtP x one); rewrite ? andbT ? andbF //; last by case x.
by rewrite T3lt1 => ->.
Qed.

Lemma omega_least_inf1 x: T3finite x -> x < omega.
Proof.
case: x => // a b c n d /=.
move => /and3P [/eqP -> /eqP -> /eqP ->].
by rewrite /omega T3lt_consE /lt_psi.
Qed.

Lemma omega_least_inf2 x: ~~ T3finite x -> omega <= x.
Proof.
case: x => // a b c n d.
rewrite /T3finite /all_zero  /T3le/omega T3lt_consE T3lt_psi /lt_psi.
rewrite !T3lt0n !T3ltn0 /= (eq_sym a zero) (eq_sym b zero) !T3gt1 !andbF /=.
rewrite (eq_sym [a,b,c] one) (eq_sym c one) (eq_sym d zero) !T3eqE.
case: (zero == a) => //; case : (zero == b) => //= -> /=.
by case h2: (one == c) => //; case: (ltngtP 0 n) => //=; case: eqP.
Qed.


Lemma lt_omega1 c n d a' b' c' n' d' :
   cons zero zero c n d < cons a' b' c' n' d' = 
     if ((a'== zero) && (b'==zero)) then
       ((c < c') || ((c==c') && ((n < n')%N || ((n==n') && (d < d')))))
    else  (c < [a', b', c']).
Proof.
rewrite T3lt_consE T3lt_psi /lt_psi !T3ltn0 !T3lt0n T3eqE eqxx !andbT /=.
rewrite (eq_sym zero a') (eq_sym zero b').
case pa: (a'==zero); last by rewrite orbF if_simpl.
case pb: (b'==zero);  [by case: (c<c')  | by rewrite /= orbF if_simpl].
Qed.

Lemma lt_omega2 c a' b' c' :
   ([zero, zero, c] < [a', b', c']) =
     if ((a'== zero) && (b'==zero)) then c < c' else  (c < [a', b', c']).
Proof. by rewrite lt_omega1 ltnn T3ltnn !andbF orbF. Qed.


Lemma split_limit x: ((T3split x).2 == 0) = ((x==zero) || T3limit x). 
Proof.  
elim: x => // a _ b _ c _ n d Hb /=.
case pa: (all_zero a b c) => //; rewrite - Hb; by case: (T3split d).
Qed.


Fixpoint T3is_succ x := 
  if x is cons a b c n d then (all_zero a b c) || T3is_succ d  else false.

Fixpoint T3succ x :=
  if x is cons a b c n d
     then if all_zero a b c then \F n.+2  else cons a b c n (T3succ d)
  else one.


Fixpoint T3pred x :=
  if x is cons a b c n d then
     if  all_zero a b c  then \F n else (cons a b c n (T3pred d)) 
  else zero.

Lemma split_is_succ x: ((T3split x).2 != 0) = (T3is_succ x).
Proof.  
elim: x => // a _ b _ c _ n d Hd /=.
case pa: (all_zero a b c) => //; rewrite - Hd; by case: (T3split d).
Qed.

Lemma split_succ x: let:(y,n):= T3split x in T3split (T3succ x) = (y,n.+1).
Proof.  
elim: x => // a _ b _ c _ n d /=.
by case pa: (all_zero a b c) => //=; rewrite pa /=;case: (T3split d) => u v ->.
Qed.


Lemma split_pred x: let:(y,n):= T3split x in T3split (T3pred x) = (y,n.-1).
Proof.  
elim: x => // a _ b _ c _ n d /=.
case pa: (all_zero a b c) => //=; first by case: n.
by rewrite pa /=; case:(T3split d) => // u v ->.
Qed.


Lemma split_le x :  (T3split x).1 <= x.
Proof.
elim: x => // a _ b _ c _ n d Hd /=.
case pa: (all_zero a b c) => //; move: Hd; case (T3split d) => y m /=.
rewrite /T3le T3lt_consE !eqxx ltnn T3eqE.
by case /orP => ->; rewrite ? eqxx // if_same orbT.
Qed.

Lemma nf_split x : T3nf x -> T3nf (T3split x).1.
Proof.
elim: x => // a _ b _ c _  n d Hd /=.
case pa: (all_zero a b c) => // /and5P [sa sb sc /Hd sd se] /=.
move: (T3le_lt_trans (split_le d) se).
by move: sd; case (T3split d) => y m /= -> ->; rewrite sa sb sc.
Qed.

Lemma T3finite_succ x: T3finite x -> T3finite (T3succ x).
Proof. by elim: x => // a _ b _ c _ n d Hb /= ->. Qed.

Lemma T1succ_nat n: T3succ (\F n) = \F (n.+1).
Proof. by case: n. Qed.

Lemma nf_omega : T3nf omega.               Proof. by []. Qed. 
Lemma nf_finite n: T3nf (\F n).            Proof. by case: n. Qed.

Lemma limit_pr1 x: (x == zero) (+) (T3limit x (+) T3is_succ x).
Proof.
elim: x => //a _ b _ c _ n d Hd /=; case az: (all_zero a b c) => //.
by case dz: (d == zero); [ rewrite (eqP dz) | move: Hd; rewrite dz].
Qed.

Lemma limit_pr x y: T3limit x -> y < x -> T3succ y < x.
Proof.
elim: x y; [ by [] |move => a _ b _ c _ n d Hd y /=].
case: y. 
  rewrite /T3succ T3gt1 andTb T3eqE => H1 _.
  apply /negP => /and5P [sa sb sc _ _]; move: H1; rewrite /all_zero sa sb sc//.
move => a' b' c' n' d';rewrite /T3succ -/T3succ !all_zeroE => hh.
case pa:([a', b', c'] == one); rewrite T3lt_consE => h; rewrite T3lt_consE.
  move: h hh; rewrite (eqP pa).  
  by case: (T3ltgtP one  [a, b, c]) => // ->; rewrite eqxx.
move: h;case:(T3ltgtP [a',b',c']  [a, b, c]) => // _.
move: hh; case: eqP => // _ hh;case: (ltngtP n' n) => //; case /orP: hh => hh.
   by rewrite (eqP hh) T3ltn0.
by move => _; apply: Hd.
Qed.

Lemma pred_le a: T3pred a <= a. (* plus simple.  *)
Proof.
elim: a => // a _ b _ c _ n d Hd /=;rewrite all_zeroE; case: eqP. 
  case => -> -> ->; case: n => // n; apply:T3ltW; rewrite T3lt_consE.
  by rewrite T3ltnn eqxx ltnS leqnn.
move => _; rewrite /T3le T3lt_consE T3ltnn ! eqxx ltnn T3eqE.
by case /orP: Hd => ->; rewrite ?orbT // !eqxx.
Qed.
  
Lemma pred_lt a: T3is_succ a -> T3pred a < a.
Proof.
elim: a => // a _ b _ c _ n d Hd /=; rewrite all_zeroE; case: eqP. 
  by move => h; case: n => // n _; rewrite T3lt_consE h T3ltnn eqxx ltnS leqnn.
by move => /= _ h; rewrite T3lt_consE Hd // !eqxx !if_same.
Qed.

Lemma succ_lt a: a < T3succ a.
Proof. 
elim: a => // a _ b _ c _ n d Hd /=; rewrite all_zeroE; case: eqP.
   by rewrite T3lt_consE ltnS leqnn; move => ->; rewrite T3ltnn eqxx.
by rewrite T3lt_consE !eqxx Hd !if_same.
Qed.

Lemma nf_succ a: T3nf a -> T3nf (T3succ a).
Proof.
elim:a => // a _ b _ c _ n d Hd /= /and5P [pa pb pc /Hd pd pe].
case az: (all_zero a b c) => //=; rewrite pa pb pc pd /=.
by apply:limit_pr => //=; rewrite az.
Qed.

Lemma nf_pred a: T3nf a -> T3nf (T3pred a).
Proof.
elim:a => // a _ b _ c _ n d Hd /= /and5P [pa pb pc /Hd pd pe].
case az: (all_zero a b c); first by apply: nf_finite.
by rewrite /= pa pb pc pd /= (T3le_lt_trans (pred_le d) pe). 
Qed.


Lemma succ_pred x: T3nf x -> T3is_succ x -> x = T3succ (T3pred x).
Proof.
elim:x => // a _ b _ c _ n d Hd /= /and5P [pa pb pc pd pe].
case az: (all_zero a b c) => /=; last by rewrite az => h; rewrite - Hd.
move: pe;move/and3P: az=> [/eqP -> /eqP -> /eqP ->].
by rewrite T3lt1 => /eqP ->; case:n.
Qed.

Lemma succ_p1 x: T3is_succ (T3succ x).
Proof. 
elim: x => // a _ b _ c _ n d Hd /=.
by case: (all_zero a b c) => //=;rewrite Hd orbT.
Qed.

Lemma pred_succ x: T3nf x -> T3pred (T3succ x) = x. 
Proof.
elim:x => // a _ b _ c _ n d Hd /= /and5P [pa pb pc pd pe].
case az: (all_zero a b c) => /=; last by  rewrite az Hd.
move: pe;move/and3P: az=> [/eqP -> /eqP -> /eqP ->].
by rewrite T3lt1 => /eqP ->.  
Qed.

Lemma succ_inj x y: T3nf x -> T3nf y -> (T3succ x == T3succ y) = (x==y).
Proof.
move => nx ny;case h: (T3succ x == T3succ y).
  by rewrite - (pred_succ nx) (eqP h) (pred_succ ny) eqxx.
by case hh: (x==y) => //; rewrite -h (eqP hh) eqxx.
Qed.

Lemma lt_succ_succ x y: T3succ x < T3succ y -> x < y. 
Proof.
elim: x y; first by case; [ rewrite T3ltnn | move => a b c n d  _ ].
move => a _ b _ c _ n d Hd /=; case.
  by rewrite {2}/T3succ T3lt1; case (all_zero a b c) => //.
move => a' b' c' n' d'; rewrite all_zeroE;case sa: ([a, b, c] == one).
  rewrite /= all_zeroE; case sb: ([a', b', c'] == one).
    rewrite {1} /T3lt /= if_same if_simpl ltnS T3lt_consE (eqP sb) sa => ->.
    by rewrite if_same.
  by move => _; rewrite T3lt_consE (eqP sa) T3gt1 sb.
rewrite /= all_zeroE;case: eqP => /=.
  by move => sb; rewrite T3lt_consE T3lt1 /= sa.
move => _; rewrite T3lt_consE => h; rewrite T3lt_consE; move: h.
case: (T3ltgtP [a, b, c] [a', b', c']) => // _.
case (ltngtP n n') => // _; apply: Hd.
Qed.

Lemma le_succ_succ x y: x <= y -> T3succ x <= T3succ y.
Proof. rewrite !T3leNgt; apply: contra; exact:lt_succ_succ.  Qed.

Lemma lt_succ_succE x y:  
  T3nf x -> T3nf y ->  (T3succ x < T3succ y) = (x < y).
Proof.
move => nx ny.
case (T3ltgtP (T3succ x) (T3succ y)).  
+ by move/lt_succ_succ => ->.
+ by move /lt_succ_succ => /T3lt_anti.
+ by move /eqP; rewrite   (succ_inj nx ny) => /eqP ->; rewrite T3ltnn.
Qed.

Lemma le_succ_succE x y: 
  T3nf x -> T3nf y -> (T3succ x <= T3succ y) = (x <= y).
Proof.
by move => na nb; rewrite /T3le (succ_inj na nb) (lt_succ_succE na nb).
Qed.

Lemma lt_succ_le_1 a b : T3succ a <= b ->  a < b.
Proof. apply: T3lt_le_trans (succ_lt a). Qed.

Lemma lt_succ_le_2 a b:  T3nf a -> a < T3succ b ->  a <= b. (* !!!mieux *)
Proof.
elim: a b; first by move => b;rewrite T3le0n.
move => a' _ b' _ c' _ n' d' Hd; case; first by rewrite T3lt1 => _ /eqP ->.
move => a b c n d  nx /=; rewrite all_zeroE; case: eqP => sa.
  rewrite T3lt_consE => h; rewrite /T3le T3lt_consE sa; move: h.
  case: (T3ltgtP [a', b', c'] one) => //; first by  rewrite orbT.
  move => h; move: nx;case: h => -> -> ->; rewrite /T3nf => /and5P [ _ _ _ _].
  rewrite T3lt1 T3ltn0 if_same if_simpl ltnS leq_eqVlt.
  move =>/eqP ->; case/orP => h'; rewrite h' ?orbT // (eqP h') ltnn T3eqE.
  by move: sa; case => -> -> ->; rewrite /= eqxx /= T3lt0n eq_sym; case: eqP.
rewrite T3lt_consE => h; rewrite /T3le T3lt_consE; move: h.
case: (T3ltgtP [a', b', c'] [a,b,c]) => //;first by rewrite orbT.
case => -> -> ->; case: (ltngtP n' n); rewrite ? orbT// => ->.
move:nx => /and5P[_ _ _ nd _]  /(Hd _ nd) /orP [/eqP -> | ->] //.
  by rewrite eqxx.
by rewrite orbT.
Qed.

Lemma lt_succ_le_3 a b:  T3nf a -> (a < T3succ b) = (a <= b).
Proof.
move => na; case h:(a < T3succ b). 
  by rewrite (lt_succ_le_2 na  h).
rewrite - h; case (T3ltP b a) => // ab; exact: (T3le_lt_trans ab (succ_lt b)).
Qed.

Lemma lt_succ_le_4 a b: T3nf b ->  (a < b) = (T3succ a <= b).
Proof.
move => nb.
case: (T3ltP a b).
  rewrite T3leNgt T3ltNge;case h: (b < T3succ a) => //. 
  by rewrite(lt_succ_le_2 nb h).
by move /le_succ_succ => /(T3lt_le_trans  (succ_lt b)); rewrite T3leNgt => ->.
Qed.

Lemma succ_nz x:  T3succ x != zero.
Proof. by move: (T3le_lt_trans (T3le0n x) (succ_lt x)); rewrite T3lt0n. Qed.

Lemma succ_psi a b c: [a, b, c] != one -> T3succ [a,b,c] =  cons a b c 0 one.
Proof.
by simpl; rewrite - all_zeroE; move /negbTE => ->.
Qed.


Lemma succ_psi_lt x a b c: [a, b, c] != one -> 
   x < [a,b,c] -> T3succ x < [a,b,c].
Proof.
move => yn1; case: x => //; first by rewrite /= T3gt1 yn1.
move => a' b' c' n d /=; rewrite psi_lt1 all_zeroE; case: eqP.
  by move => -> h; rewrite T3lt_consE h.
by move => sa sb; rewrite T3lt_consE sb.
Qed.


Lemma succ_psi_lt2 a b c x: [a, b, c] != one -> 
  ([a, b, c] <= T3succ x) = ([a, b, c] <= x).
Proof.
move => ha;symmetry.
case (T3leP [a, b, c] (T3succ x)).
  by rewrite !T3leNgt; apply: contra; apply:succ_psi_lt.
by move => hb; move: (T3lt_trans (succ_lt x) hb);rewrite T3ltNge; move /negbTE.
Qed.

(** ** Addition *)

Fixpoint T3add x y :=
  if x is cons a b c n d then 
    if y is cons a' b' c' n' d' then
       if [a,b,c] < [a',b',c']  then y
       else if [a',b',c'] < [a,b,c] then cons a b c n (d + y)
       else  cons a b c (n+n').+1 d'
    else x 
  else y
 where "x + y" := (T3add x y) : ak_scope.

Fixpoint T3sub x y :=
  if x is cons a b c n d then
     if y is cons a' b' c' n' d' then
           if (x < y) then zero 
           else if ([a',b',c'] < [a,b,c]) then x 
           else if (n<n')%N then zero
           else if ([a,b,c] == one) then 
             if (n==n')%N then zero else cons zero zero zero ((n-n').-1) zero
           else if(n==n') then d - d' else cons a b c (n - n').-1 d 
     else x
  else zero
where "a - b" := (T3sub a b) : ak_scope.

Lemma T3subn0 x: x - zero = x.
Proof. by case x. Qed.

Lemma T3sub0n x: zero - x = zero.
Proof.  done.  Qed.

Lemma minus_lt a b: a < b -> a - b = zero.
Proof. by case: a b => // a b c n d // [] // a' b' c' n' d' /= ->. Qed.

Lemma T3subnn x: x - x = zero.
Proof.
by elim: x => // a _ b _ c _ n d Hr /=; rewrite !T3ltnn ltnn eqxx Hr if_same.
Qed.

Lemma minus_le a b: a <= b -> a - b = zero.
Proof.
rewrite T3le_eqVlt;case /orP; [move /eqP ->; apply: T3subnn| apply: minus_lt].
Qed.

Lemma nf_sub a b: T3nf a -> T3nf b -> T3nf (a - b).
Proof.
elim: a b => // a Ha b Hb c Hc n d Hd [] // a' b' c' n' d' na nb /=.
case: (_ < _) => //; case: (_ < _) => //; case: (ltngtP n n') => //.
 by case: eqP.
move: na nb => /and5P[_ _ _ nd _] /and5P [_ _ _  nd' _].
by case: eqP => // _ _; apply: Hd.
Qed.


Lemma sub_int n m : \F n - \F m = \F (n -m)%N.
Proof.
case: n m => // n [] // m /=; rewrite /T3lt /= if_same subSS //.
case: (ltngtP n m) => pa;first by move: (ltnW pa)=> /eqP ->.
 by rewrite -(subnSK pa). 
by rewrite pa subnn.
Qed.

Lemma succ_is_add_one a: T3succ a = a + one.
Proof.
elim:a => // a _ b _ c _ n d Hd /=; rewrite addn0 Hd all_zeroE. 
case:(T3ltgtP [a, b, c] one) => //; first by rewrite T3lt1 //.
by case => -> -> ->.
Qed.

Lemma add1Nfin a:  ~~ T3finite a  -> one + a = a.
Proof. (* !!! bof *)
by case:a => // a b c n d /=; rewrite all_zeroE T3gt1 /= => ->.
Qed.

Lemma sub1Nfin a:  ~~ T3finite a  -> a - one  = a.
Proof. by case:a => // a b c n d /=; rewrite all_zeroE T3lt1 T3gt1 => ->. Qed.


Lemma sub1a x: x != zero -> T3nf x -> x = one + (x - one). 
Proof.
case fb:(T3finite x); last by rewrite sub1Nfin ?fb // add1Nfin // fb //.
move: fb;case x => // a' b' c' n' d' /=.
rewrite all_zeroE T3lt1 T3gt1 /= => h _; rewrite h  (eqP h) T3lt1 /=.  
by move: (eqP h); case =>  -> -> ->; move /and5P=> [_ _ _ _ /eqP -> ];case n'.
Qed.

Lemma sub1b x: T3nf x -> x = (one + x) - one. 
Proof.
case hh: (T3finite x); last by rewrite add1Nfin ? hh // sub1Nfin // hh.
move: hh;case:x => // a b c n d /=.
rewrite all_zeroE T3lt1 T3gt1 => h; rewrite h (eqP h) T3lt1 andbF /=.
by move: (eqP h); case =>  -> -> ->; move /and5P=> [_ _ _ _ /eqP -> ]. 
Qed.


Lemma sub_1aCE (a:= T3bad) : one + (a - one) != a.
Proof.  done.  Qed.

Lemma sub_1bCE (a:= T3bad) : (one + a - one) != a.
Proof. done.  Qed.

Lemma T3add0n : left_id zero T3add.    Proof. by []. Qed. 
Lemma T3addn0: right_id zero T3add.    Proof. by case. Qed.


Lemma add_int n m : \F n + \F m = \F (n +m)%N.
Proof.
case: n m => // n; case; first by rewrite addn0 T3addn0.
by move => m /=; rewrite - addnS.
Qed.

Lemma add_fin_omega n: \F n + omega = omega.
Proof. by case: n. Qed.

Lemma fooCE (x:= T3bad):
   ~~T3limit x  /\(forall u v, T3limit u -> x <> u + \F v.+1).
Proof. 
split => // u v; case: u => // a b c n d /=.
rewrite all_zeroE T3lt1 T3gt1.
by case x1: ([a, b, c] == one) => // h /= xa; move: x1; case: xa=> <- <- <-. 
Qed.

Lemma split_add x: let: (y,n) :=T3split x in T3nf x ->
   (x == y + \F n) && ((y==zero) || T3limit y ).
Proof.
elim: x => //a _ b _ c _ n d Hd /=;case h: (all_zero a b c).
  move /and3P: h => [/eqP -> /eqP -> /eqP ->].
  by rewrite T3lt1 /= !andbT => /andP [_ /eqP ->].
move: Hd; case (T3split d) => y s h1 /and5P [_ _ _ /h1/andP [/eqP -> sb] _].
rewrite /= h sb andbT; case s => //=; first by rewrite T3addn0.
by move => m; rewrite T3lt1 T3gt1 /= - all_zeroE h.
Qed.

Lemma add_to_cons a b c n d: 
  d < [ a,b,c] -> cons a b c n zero + d = cons a b c n d.
Proof.
by case d => // u v w m z /=; rewrite psi_lt1 => h; rewrite h // (T3lt_anti h).
Qed.


Lemma addC_CE (a := one) (b := omega):
  [&& T3nf a, T3nf b & a + b != b + a].
Proof. done.  Qed.

Lemma nf_add a b: T3nf a -> T3nf b -> T3nf (a + b).
Proof.
elim: a b => // a Ha b Hb c Hc n d Hd [] // a' b' c'  n' d' ha hb /=.
case (T3ltgtP [a, b, c] [a', b', c']) => // h.
  move: ha; rewrite /T3nf -/T3nf => /and5P [sa sb sc sd se].
  rewrite sa sb sc Hd //=; move: se; case d => //=; first by rewrite psi_lt1.
  move => a1 b1 c1 n1 d1; rewrite psi_lt1 => ha.
  case: (T3ltgtP [a1, b1, c1]  [a', b', c']); rewrite psi_lt1 //.
by move: hb; case:h => -> -> ->. 
Qed.


Lemma T3add_eq0 m n:  (m + n == zero) = (m == zero) && (n == zero).
Proof. 
case: m; [by rewrite T3add0n | move => a' b' c' n' d'; rewrite andFb].
by case: n => // a b c n d /=; case: (T3ltgtP [a', b', c']  [a, b, c]).
Qed.

Lemma add_le1 a b: a <= a + b.
Proof.
elim:a b; first by rewrite /T3le /=; case;[ rewrite eqxx | ].
move => a' _ b' _ c' _ n' d' hd [] // a b c n d/=.
case: (T3ltgtP [a', b', c'] [a, b, c]) => h; rewrite /T3le T3lt_consE.
+ by rewrite h orbT.
+ by rewrite T3ltnn ltnn T3eqE !eqxx /=; apply: hd.
+ by rewrite T3ltnn  ltnS leq_addr eqxx orbT.
Qed.

Lemma add_le2 a b: b <= a + b.
Proof.
case: a => // a' b' c' n' d'; case: b ; [done | move => a b c n d /=].
case: (T3ltgtP [a', b', c'] [a, b, c]) => h; rewrite /T3le T3lt_consE ?h.
+ by rewrite eqxx.
+ by rewrite orbT.
+ by rewrite T3ltnn eqxx ltnS leq_addl orbT.
Qed.

Lemma sub_le1 a b : T3nf a -> (a - b) <= a. 
Proof.
elim: a b => [b // | a' _ b' _ c' _ n' d' H].
case; [by rewrite T3subn0 T3lenn | move => a b c n d/and5P [_ _ _ /H la lb] /=].
have hh: (n < n')%N -> ((n' - n).-1 < n')%N.
  by case: n' => // n' h; rewrite subSn // ltnS leq_subr.
rewrite T3lt_consE;case: (T3ltgtP [a', b', c'] [a, b, c]) => // eq1.
case : (ltngtP n' n) => // eq2.
  case x1: ([a', b', c'] == one) => //. 
    by rewrite /T3le T3lt_consE (eqP x1) T3ltnn eqxx hh // orbT.
  by rewrite /T3le T3lt_consE T3ltnn eqxx hh // orbT.
case : (d' < d) => //; case: ([a', b', c'] ==one) => //.
apply: (T3le_trans (la d)); apply:T3ltW; apply: (T3lt_le_trans lb).
apply: T3le_psi.
Qed.

Lemma sub_pr a b: T3nf b -> (a + b) - a = b.
Proof.
elim: a b; first by move => b _; rewrite T3subn0.
move => a' _ b' _ c' _ n' d' Hd; case; first by rewrite T3addn0 T3subnn.
move => a b c n d nn /=.
case (T3ltgtP [a', b', c'] [a, b, c]) => pa;  rewrite /= T3lt_consE.
    by rewrite pa /=  (T3lt_anti pa) (T3lt_ne' pa).
  rewrite !T3ltnn ltnn !eqxx (T3ltNge _ d') add_le1 /=.
  by rewrite Hd // ifF //; case: eqP => h //; move: pa; rewrite h T3lt1.
rewrite !T3ltnn !eqxx addnC ltn_simpl1 eqn_simpl1 - addSn addnK /=.
move: pa nn; case => -> -> ->; case: eqP => //; case => -> -> ->.
by rewrite /T3nf T3lt1 /= => /andP[_ /eqP ->].
Qed.

Lemma add_inj a b c : T3nf b -> T3nf c -> a + b = a + c -> b = c.
Proof.
move => sb sc h.
by rewrite - (sub_pr a sb) - (sub_pr a sc) h.
Qed.

Lemma sub_pr1 a b: T3nf b -> a <= b -> b = a + (b - a).
Proof.
move => nb; rewrite /T3le.
case: (altP (a =P b)) => [-> | _ /=]; first by rewrite T3ltnn T3subnn T3addn0.
move: nb; elim: a b; first by move => b nb; rewrite T3subn0 //.
move => a' _ b' _ c' _ n' d' Hd; case; [by rewrite T3ltn0 | move => a b c n d].
have aux: (n' < n)%N ->n = (n' + (n - n').-1).+1.
  by move => le1; rewrite - {1} (subnKC le1)  subnS addSn.
move => sa sb;rewrite /= (T3lt_anti sb).
move: sb; rewrite T3lt_consE. 
case: (T3ltgtP [a', b', c'] [a, b, c]) => sb; rewrite ? sb //.
move: sa; case: sb => <- <- <- => sa.
have sb: [a', b', c'] = one -> d = zero.
  by move => h;move: sa;case:h => -> -> -> /= /andP[_];rewrite T3lt1 => /eqP ->.
case: (ltngtP n' n) => sc; rewrite ? sc ?eqxx //.
  move: sc (aux sc); case h: (n==n'); [ by rewrite (eqP h) ltnn | move => _ hh].
  by case: eqP => h1 ; [ rewrite h1 T3ltnn - hh sb | rewrite !T3ltnn - hh ].
move => dd'; case: eqP; first by  move => h; move: dd';rewrite (sb h) T3ltn0.
move: sa => /and5P [_ _ _ nd ne] _; move: (Hd d nd dd') => h.
have: d - d' < [a', b', c'] by move: (T3le_lt_trans (sub_le1 d' nd) ne).
rewrite - h; move: dd'; rewrite {1} h;case: (d - d').
   by rewrite T3addn0 T3ltnn.
move => a1 b1 c1 n1 d1 _; rewrite psi_lt1 => ha.
by rewrite ha (T3lt_anti ha).
Qed.


Lemma omega_minus_one : omega - one = omega. 
Proof. by []. Qed.

Lemma sub_nz a b: T3nf b -> a < b -> (b - a) != zero.
Proof.
move => nb lab; move: (sub_pr1 nb (T3ltW lab)).
case h: (b - a == zero) => //; rewrite (eqP h) T3addn0 => eq.
by move: lab; rewrite eq T3ltnn.
Qed.

Lemma T3addA c1 c2 c3: c1 + (c2 + c3) = (c1 + c2) + c3.
Proof.
elim: c1 c2 c3 => // a1 _ b1 _ c1 _ n1 d1 H; case.
   by move => c3;rewrite !T3add0n T3addn0.
move => a2 b2 c2 n2 s2; case;[ by rewrite !T3addn0 | move => a3 b3 c3 n3 d3 /=].
case: (T3ltgtP [a2, b2, c2] [a3, b3, c3]).
+ case: (T3ltgtP  [a1, b1, c1] [a2, b2, c2]) => pa pb /=.
   - by rewrite (T3lt_trans pa pb) /= pb.
   - by case (T3ltgtP a1 a3) => //; rewrite - H /= pb.
   - by rewrite  pa pb.
+ case: (T3ltgtP [a1, b1, c1] [a2, b2, c2]) => pa pb /=;
     move: (T3lt_anti pb) => pc.
   - by rewrite pb pc.
   - by move:(T3lt_trans pb pa) => h; rewrite h (T3lt_anti h) - H /= pb pc.
   - by rewrite pa pb pc.
+ move => e1; case: (T3ltgtP  [a1, b1, c1] [a2, b2, c2]) => pb /=; rewrite -e1.
   - by rewrite !T3ltnn. 
   - by rewrite pb (T3lt_anti pb) - H /= -e1 !T3ltnn.
   - by rewrite pb !T3ltnn addSn addnS addnA.
Qed.

Lemma T3le_add2l  p m n : (p + m <= p + n) = (m <= n).
Proof.
elim:p m n => // a _ b _ c _ n d Hd.
case; first by move => n1; rewrite T3addn0 T3le0n add_le1.
move => a' b' c' n' d'; case.
  rewrite T3addn0  /=; case: (T3ltgtP [a, b, c] [a', b', c']) => h.
      by rewrite T3le_consE (T3lt_ne' h) (T3lt_anti h) T3len0.
    by rewrite T3le_consE T3ltnn ltnn !eqxx - (Hd _ zero)  T3addn0.
  by rewrite T3le_consE T3ltnn eqxx  addnC ltn_simpl1 eqn_simpl1 T3len0. 
move => a'' b'' c'' n'' d'' /=.
case: (T3ltgtP [a, b, c] [a', b', c']);case:(T3ltgtP [a, b, c] [a'', b'', c''])
  =>// pa pb; rewrite T3le_consE [in RHS] T3le_consE.
- move: (T3lt_trans pa pb) => pc.
  by rewrite (T3lt_anti pb) (T3lt_ne' pb) (T3lt_ne' pc) (T3lt_anti pc).
- by rewrite -pa (T3lt_ne' pb) (T3lt_anti pb).
- by rewrite (T3lt_trans pb pa) pa.
- by rewrite !eqxx T3ltnn ltnn Hd T3le_consE.
- by rewrite T3ltnn -pa pb eqxx ltnS leq_addr.
- by rewrite -pb pa.
- rewrite T3ltnn -pb addnC ltn_simpl1 eqn_simpl1 eqxx.
  by rewrite (T3lt_anti pa) (T3lt_ne' pa).
- by rewrite - pa pb eqxx T3ltnn /= ltnS ltn_add2l - !addSn eqn_add2l. 
Qed.

Lemma T3lt_add2l  p m n : (p + m < p + n) = (m < n).
Proof. by rewrite !T3ltNge T3le_add2l. Qed.


Lemma T3lt_add2r  p m n : (m + p  < n + p ) ->  (m < n).
Proof.
elim: m p n. 
  by move => p n; rewrite T3add0n; case: n => //;rewrite T3add0n T3ltnn.
move => a _ b _ c _ n d Hd; case; first by move => u; rewrite ! T3addn0.
move => a' b' c' n' d'; case.
  simpl;case (T3ltgtP [a, b, c]  [a', b', c']) => pa /=.
  + by rewrite !T3ltnn.
  + by rewrite  T3lt_consE (T3lt_anti pa) (T3lt_ne' pa).
  + by rewrite T3lt_consE pa T3ltnn eqxx ltn_simpl1 eqn_simpl1.
move => a'' b'' c'' n'' d'' /= h1; rewrite T3lt_consE; move: h1.
case (T3ltgtP [a,b,c] [a',b',c']);case (T3ltgtP [a',b',c'] [a'',b'',c''])
  => pb pa /=; rewrite T3lt_consE.
- by rewrite (T3lt_trans pa pb).
- by rewrite ! T3ltnn ltnn eqxx if_same.
- by rewrite -pb pa.
- case: (T3ltgtP [a,b,c] [a'',b'',c'']) => //.
  by case: (ltngtP n n'') => // _ _; apply: Hd.
- by rewrite (T3lt_anti pa) (T3lt_ne' pa).
- by rewrite - pb  (T3lt_anti pa) (T3lt_ne' pa).
- by rewrite pa pb.
- by rewrite pa T3ltnn eqxx ltn_simpl1 eqn_simpl1.
- by rewrite pa pb !T3ltnn eqxx ltnS ltn_add2r if_same if_simpl => ->.
Qed.

Lemma T3le_add2r  p m n : (m <=n) -> (m + p  <= n + p).
Proof. rewrite !T3leNgt; apply: contra; apply: T3lt_add2r.  Qed.

Lemma T3eq_add2l  p m n : (p + m == p + n) = (m == n).
Proof. by rewrite ! T3eq_le ! T3le_add2l. Qed.

Lemma add_le3 a b: a = a + b -> b = zero.
Proof. move /eqP;rewrite -{1} (T3addn0 a) T3eq_add2l => /eqP -> //. Qed.

Lemma add_le4 a b: b != zero -> a < a + b.
Proof.
move: (add_le1 a b); rewrite T3le_eqVlt.
by case: (a<a+b); rewrite ? orbT // orbF => /eqP /add_le3 ->.
Qed.

Lemma sub_pr1r a b: T3nf a -> a - b = zero -> a <= b.
Proof.
move => nn h; case /orP: (T3le_total a b) => // h1.
by move: (sub_pr1 nn h1); rewrite h T3addn0 => ->. 
Qed.

Lemma sub_pr1rCE (a := T3bad) (b := one) :  (a - b == zero) && (b < a).
Proof. done. Qed.

Lemma T3addS a b : (a + T3succ b) = T3succ (a+ b).
Proof. by rewrite ! succ_is_add_one T3addA. Qed.

(** ** limit *)
Notation Tf := (nat -> T3).


Definition limit_of (f: Tf) x :=
  [/\ (forall n m, (n < m)%N -> f n < f m),
      (forall n, f n < x) & 
      (forall y, T3nf y -> y < x -> (exists n, y <= f n))].


Lemma fincP (f: Tf) :
  (forall n, f n < f n.+1) -> 
  (forall n m, (n < m)%N -> f n < f m).
Proof.
move => h n; elim => //.
move => m Hm;rewrite ltnS leq_eqVlt; case /orP;first by move => /eqP ->.
move /Hm => sa; exact: (T3lt_trans sa (h m)).
Qed.


Definition limit12_hyp a b c:=
   if c is cons a1 b1 c1 n1 d1 then 
       (n1 == 0) && (d1 == zero) &&
       ( ((a == a1) && (b < b1)) || ((a < a1) && (b < c)))
   else false.

Definition phi0:= fun _ :nat => zero.
Definition phi1 a (f:Tf) := fun n => a + f n.
Definition phi5 (f:Tf) := fun n => [f n, zero,zero].
Definition phi12a a b (f:Tf) := fun n => [a,b,f n].


Lemma limit1 a b f:
   T3nf a -> (limit_of f b) ->  (limit_of (phi1 a f) (a + b)).
Proof.  
move => na [sa sb sc].
split.
+ by move => n m / sa => h; rewrite T3lt_add2l.
+ by move => n; rewrite T3lt_add2l (sb n).
+ move => y ny hy.
  case: (T3ltP a y) => cp; last first.
        by exists 0; apply: (T3le_trans cp); rewrite add_le1.
  move: (sub_pr1 ny (T3ltW cp)) => yv.
  have ha: y - a < b by move: hy; rewrite {1} yv T3lt_add2l.
  have [n nv] := (sc _ (nf_sub ny na) ha).
  by exists n; rewrite yv  T3le_add2l nv.
Qed.


Lemma limit5 f x: (limit_of f x) ->  (limit_of (phi5 f) [x,zero,zero]).
Proof.
move => [sa sb sc].
have gi:forall n m : nat, (n < m)%N ->  (phi5 f) n <  (phi5 f) m.
  by move => n m /sa ha; rewrite T3lt_psi /lt_psi eqxx T3ltnn ha /= !orbT.
split => //.
  by move => n; rewrite T3lt_psi /lt_psi eqxx T3ltnn (sb n)  /= !orbT.
move => y.
move:{2} (size y).+1 (leqnn (size y).+1) =>  n; elim: n y=> //.
move => m Hrec y; rewrite ltnS.
case: y => //; first by move => _  _ _; exists 0; rewrite T3le0n.
move => a b c n d lm ny; rewrite psi_lt1.
have /and5P [_ lb lc _ _] :=  (size_prop1 a b c n d).
rewrite T3lt_psi /lt_psi !T3ltn0 !andbF !orbF /=.
move/and3P => [ ax bx cx].
move: ny; rewrite /T3nf -/T3nf => /and5P [na nb nc _ _].
have [n1 bp1] := (Hrec _ (leq_trans lb lm) nb bx).
have [n2 cp1] := (Hrec _ (leq_trans lc lm) nc cx).
have [n3 ap1] := (sc a na ax).
set k := (n1 + n2 + n3).+1.
have ha: (a < f k) by apply /(T3le_lt_trans ap1) /sa;rewrite ltnS leq_addl.
have hb: (b <  (phi5 f) k).
   by apply /(T3le_lt_trans bp1) /gi;rewrite /k ltnS  -addnA leq_addr.
have hc: (c <  (phi5 f) k). 
  by apply /(T3le_lt_trans cp1) /gi;rewrite /k ltnS addnAC leq_addl.
exists k.
by rewrite T3le_consE T3lt_psi /lt_psi !T3ltn0 !andbF !orbF /= ha hb hc.
Qed.


Lemma limit12a f a b c:   ~~ (limit12_hyp a b c) ->
   (limit_of f c) ->  (limit_of (phi12a a b f)[a, b, c]).
Proof.
move => H [sa sb sc].
have gi:forall n m : nat, (n < m)%N -> (phi12a a b f) n < (phi12a a b f) m.
  by move => n m /sa ha; rewrite T3lt_psi /lt_psi !eqxx ha. 
split => //.
  by move => n; rewrite T3lt_psi /lt_psi !eqxx  (sb n).  
move => y.
move:{2} (size y).+1 (leqnn (size y).+1) =>  n; elim: n y=> //.
move => m Hrec y; rewrite ltnS.
rename a into a1;rename b into b1; rename c into c1.
case: y => //; first by move => _  _ _; exists 0; rewrite T3le0n.
case: c1 H sb sc Hrec.
  by move => _ H; move: (H 0); rewrite T3ltn0.
move => a2 b2 c2 n2 d2 /=.
rewrite !negb_and negb_or !negb_and - !T3leNgt; set c1 := cons _ _ _ _ _.
move => H sb sc Hrec a b c n d lm ny; rewrite psi_lt1.
have /and5P [_ lb lc _ _]:= (size_prop1 a b c n d).
have/and5P [na nb nc nd ne] := ny.
have nabc: T3nf [a,b,c] by rewrite nf_psi na nb nc.
rewrite T3lt_psi /lt_psi.
case /orP.
  move => /and3P[ha hb hc].
  have [k kp] := (sc c nc hc).
  have ck1 := (T3le_lt_trans kp (sa _ _ (ltnSn k))).
  by exists k.+1; rewrite T3le_consE T3lt_psi /lt_psi ha hb ck1.
case /orP.
  move => /and3P [ha hb hc].
  have [k kp] := (Hrec _ (leq_trans lc lm) nc hc).
  have ck1 := (T3le_lt_trans kp (gi _ _ (ltnSn k))).
  by exists k.+1; rewrite T3le_consE T3lt_psi /lt_psi ha hb ck1 !orbT.
case /orP.
  move => /and3P [ha hb hc].
  have [k kp] := (sc _ nabc hc).
  have ck1 := (T3le_lt_trans kp (sa _ _ (ltnSn k))).
  by exists k.+1; rewrite T3le_consE T3lt_psi /lt_psi ha hb ck1 !orbT.
case /orP.
  move => /and3P [ha hb/eqP hc].
  by move: H; case: hc => <- <- cc <- <- /=; rewrite T3leNgt eq_sym ha hb.
case /orP.
  move => /and3P [ha hb hc].
  have [k1 k1p] := (Hrec _ (leq_trans lb lm) nb hb).
  have [k2 k2p] := (Hrec _ (leq_trans lc lm) nc hc).
  set k := (k1+k2).+1.
  have hd: b < (phi12a a1 b1 f) k.
    by apply /(T3le_lt_trans k1p) /gi; rewrite ltnS leq_addr.
  have he: c < (phi12a a1 b1 f) k. 
    by apply /(T3le_lt_trans k2p) /gi; rewrite ltnS leq_addl.
  by exists k; rewrite T3le_consE T3lt_psi /lt_psi ha hd he !orbT.
case /orP.
  move => /andP [ha hb]; exists 1.
  by rewrite T3le_consE T3lt_psi /lt_psi ha (T3lt_ne' ha) (T3lt_anti ha) hb.
case /orP.
  move => /andP [ha hb]; exists 1.
  by rewrite T3le_consE T3lt_psi /lt_psi ha hb !orbT.
case /orP.
  move => /andP [ha hc].
  have [k kp] := (sc _ nabc hc).
  have ck1 := (T3le_lt_trans kp (sa _ _ (ltnSn k))).
  by exists k.+1; rewrite T3le_consE T3lt_psi /lt_psi ha ck1 !orbT.
move => /andP [ha /eqP hc]; exists 1. 
rewrite T3le_consE T3lt_psi /lt_psi ha (T3lt_ne' ha) (T3lt_anti ha) hc.
move: H; case: (hc) => <- <- cc <- <- /=. 
by rewrite (T3leNgt a) ha (T3lt_ne ha) /=;case /orP => -> //; rewrite orbT.
Qed.


Fixpoint phi3 x n := if n is n.+1 then phi3 x n + x else x. 

Lemma phi3v a b c k: phi3 [a,b,c] k = cons a b c k zero.  
Proof. by elim k => // n H /=; rewrite H /= T3ltnn addn0. Qed.


Lemma limit3 x: limit_of (phi3 [zero,zero,x]) [zero, zero, T3succ x].
Proof.
split.
    by move => n m; rewrite !phi3v T3lt_consE T3ltnn eqxx => ->.
  by move => n; rewrite phi3v T3lt_consE lt_omega1 eqxx /= succ_lt.
case => //; first by move => _ h; exists 0.
move => a b c n d  /and5P[_ _ nc _ _]; rewrite -/T3nf in nc.
rewrite psi_lt1 T3lt_psi' !T3ltn0 !T3lt0n !andbF /= => h.
exists (n.+1); rewrite phi3v T3le_consE ltnS leqnn if_simpl -/(orb _ _).
move: h; rewrite  lt_succ_le_3 //;case/orP.
  move => /and3P [sa sb sc]; rewrite (eqP sa) (eqP sb).
  by move: sc; rewrite T3lt_psi /lt_psi eqxx T3ltnn /T3le /=;case:(T3ltgtP x c).
case xz: (x==zero).
  rewrite (eqP xz) /= /T3le -/one; case (T3ltgtP [a, b, c]  one) => //.
  by rewrite !andbF.
case ha: ([a,b,c] == one) => hh.
  by rewrite (eqP ha) T3lt_consE T3lt_psi /lt_psi eqxx T3lt0n xz.
rewrite orbC; apply: (T3le_trans _ (T3ltW (T3lt_psi_c zero zero x))).
by move: hh; rewrite (succ_psi_lt2 _ (negbT ha)) andbA; case /orP => /andP [].
Qed.


Lemma limit2: limit_of (phi3 one) omega.
Proof. by apply: limit3. Qed.


Lemma limit12b1 x:  (limit12_hyp zero zero x) -> 
  limit_of (phi3 x) [zero, zero, x].
Proof.
case x => // [a1 b1 c1 n1 d1] /=.
rewrite !T3lt0n /= andbT => /andP[/andP [/eqP -> /eqP ->]]. 
have ->: (zero == a1) && (b1 != zero) || (a1 != zero) =
      (a1 != zero) || (b1 != zero). 
   by rewrite eq_sym; case:eqP => //=; rewrite orbF.
move => sa; clear n1 d1.
split.
   by apply: fincP => n; rewrite !phi3v T3lt_consE !T3ltnn eqxx ltnS leqnn.
  by move => n; rewrite phi3v T3lt_consE T3lt_psi_c.
case => //; first by move => _ h; exists 0.
move => a b c n d  /and5P[_ _ nc _ _]; rewrite -/T3nf in nc.
rewrite psi_lt1 T3lt_psi' !T3ltn0 !T3lt0n !andbF /= => h.
exists (n.+1); rewrite phi3v T3le_consE ltnS leqnn if_simpl -/(orb _ _) orbC.
case/orP:h; last by rewrite andbA;case /orP => /andP [_]. 
move => /and3P[/eqP -> /eqP -> cc]; rewrite /T3le  T3lt_psi' cc !T3lt0n.
move: sa; case a1z: (a1==zero); rewrite ?orbT //= (eq_sym  _ a1) a1z.
by move => ->; rewrite !orbT.
Qed.

Fixpoint phi4 x n := 
   if n is n.+1 then [x, phi4 x n, phi4 x n] else [x,zero,zero].

Lemma limit4 x: limit_of (phi4 x) [T3succ x, zero, zero].
Proof.
have ff:forall n m : nat, (n < m)%N -> phi4 x n < phi4 x m.
     by apply: fincP => n /=; apply: T3lt_psi_b.  
split => //.
  elim =>//. 
    by rewrite /= T3lt_psi /lt_psi !T3lt0n /= succ_lt !orbT.
    by move => n /= H; rewrite /= T3lt_psi /lt_psi H succ_lt !orbT.
move => y.
move:{2} (size y).+1 (leqnn (size y).+1) =>  n; elim: n y=> //.
move => m Hrec y; rewrite ltnS.
case: y => //; first by move => _  _ _; exists 0; rewrite T3le0n.
move => a b c n d lm.
rewrite psi_lt1 /T3nf -/T3nf => /and5P [na nb nc _ _].
rewrite T3lt_psi /lt_psi !T3ltn0 /= !andbF !orbF /=.
rewrite (lt_succ_le_3 _ na) => /and3P [asx bx cx].
have /and5P [la lb lc ld _] := (size_prop1 a b c n d).
have [n1 bp1] := (Hrec _ (leq_trans lb lm) nb bx).
have [n2 cp1] := (Hrec _ (leq_trans lc lm) nc cx).
set k := (n1 + n2).+1.
have ha: (b < phi4 x k) 
  by apply:(T3le_lt_trans bp1); apply: ff; rewrite ltnS leq_addr.
have hb: (b < phi4 x k.+1) by apply: (T3lt_trans ha); apply:ff.
have hc: (c < phi4 x k.+1). 
  by apply:(T3le_lt_trans cp1); apply: ff; rewrite ltnS /k -addSn leq_addl.
exists k.+1.
rewrite /= T3le_consE ltn0 T3len0 T3lt_psi /lt_psi ha hb hc.
by case/orP: asx => ->; rewrite !orbT.
Qed.

Fixpoint phi8 x y n := 
   if n is n.+1 then [x, phi8 x y n, phi8 x y n] else [T3succ x,zero,y].

Lemma limit8 x y: limit_of (phi8 x y) [T3succ x, zero, T3succ y].
Proof.
set f := phi8 x y.
have ff:forall n m : nat, (n < m)%N -> f n < f m.
     by apply: fincP => n /=; apply: T3lt_psi_b.  
split => //.
  elim =>//. 
    by rewrite /= T3lt_psi /lt_psi !T3lt0n /= succ_lt !eqxx.
    by move => n /= H; rewrite /= T3lt_psi /lt_psi H succ_lt !orbT.
move => z.
move:{2} (size z).+1 (leqnn (size z).+1) =>  n; elim: n z=> //.
move => m Hrec z; rewrite ltnS.
case: z => //; first by move => _  _ _; exists 0; rewrite T3le0n.
move => a b c n d lm ny; rewrite psi_lt1.
move: ny; rewrite /T3nf -/T3nf => /and5P [na nb nc _ _].
move /and5P: (size_prop1 a b c n d) => [la lb lc ld _].
rewrite T3lt_psi /lt_psi !T3ltn0  !T3lt0n!andbF /=.
case: (T3ltgtP a (T3succ x)).
+ rewrite /= orbF (lt_succ_le_3 _ na) => ax /andP [bx cx].
  have [n1 bp1] := (Hrec _ (leq_trans lb lm) nb bx).
  have [n2 cp1] := (Hrec _ (leq_trans lc lm) nc cx).
  set k := (n1 + n2).+1.
  have ha: (b < f k) 
    by apply:(T3le_lt_trans bp1); apply: ff; rewrite ltnS leq_addr.
  have hb: (b < f k.+1) by apply: (T3lt_trans ha); apply:ff.
  have hc: (c < f k.+1). 
    by apply:(T3le_lt_trans cp1); apply: ff; rewrite ltnS /k -addSn leq_addl.
  exists k.+1.
  rewrite /= T3le_consE ltn0 T3len0 T3lt_psi /lt_psi ha hb hc.
  by case/orP: ax => ->; rewrite !orbT.
+ rewrite /= orbC  -/(T3le _ _) => sa; rewrite succ_psi_lt2.
    by move => sb;exists 0; rewrite /= T3le_consE T3lt_psi' sa sb !orbT.
  apply /eqP => h; by move: sa; case: h => ->; rewrite T3ltn0.
+ case bz: (b==zero).
* rewrite /= orbF (lt_succ_le_3 _ nc) => ax; case /orP.
      move => cy; move: (succ_lt x) => h.
      exists 1;  rewrite /= T3le_consE T3lt_psi /lt_psi ax h (T3lt_anti h).
      by rewrite (T3lt_ne' h) /= (eqP bz) (eqP cy) eqxx !orbT.
    by exists 0; rewrite /= T3le_consE T3lt_psi /lt_psi ax bz T3ltnn eqxx b0.
* rewrite /= orbF orbC -/(T3le _ _) => sa sb.
  exists 0.
  rewrite /= T3le_consE T3lt_psi /lt_psi T3ltn0  T3lt0n sa bz eqxx T3ltnn.
  by rewrite /= -sa orbF orbC -/(T3le _ _) -succ_psi_lt2 ? sb // T3eqE bz andbF.
Qed.

Fixpoint phi12b2 x y n := 
   if n is n.+1 then [x, phi12b2 x y n, phi12b2 x y n] else y.

Lemma limit12b2 x y: (limit12_hyp (T3succ x) zero y) ->
    limit_of (phi12b2 x y) [T3succ x, zero, y].
Proof.
move => l12h.
set f := phi12b2 x y.
have ff:forall n m : nat, (n < m)%N -> f n < f m.
     by apply: fincP => n /=;apply: T3lt_psi_b.  
split => //.
  elim =>//; first by apply: T3lt_psi_c. 
    by move => n /= H; rewrite /= T3lt_psi /lt_psi H succ_lt !orbT.
move => z.
move:{2} (size z).+1 (leqnn (size z).+1) =>  n; elim: n z=> //.
move => m Hrec z; rewrite ltnS.
case: z => //; first by move => _  _ _; exists 0; rewrite T3le0n.
move => a b c n d lm ny; rewrite psi_lt1.
move: ny; rewrite /T3nf -/T3nf => /and5P [na nb nc _ _].
move /and5P: (size_prop1 a b c n d) => [la lb lc ld _].
rewrite T3lt_psi /lt_psi !T3ltn0  !T3lt0n!andbF /=.
case: (T3ltgtP a (T3succ x)).
* rewrite /= orbF (lt_succ_le_3 _ na) => ax /andP [bx cx].
  have [n1 bp1] := (Hrec _ (leq_trans lb lm) nb bx).
  have [n2 cp1] := (Hrec _ (leq_trans lc lm) nc cx).
  set k := (n1 + n2).+1.
  have ha: (b < f k) 
    by apply:(T3le_lt_trans bp1); apply: ff; rewrite ltnS leq_addr.
  have hb: (b < f k.+1) by apply: (T3lt_trans ha); apply:ff.
  have hc: (c < f k.+1). 
    by apply:(T3le_lt_trans cp1); apply: ff; rewrite ltnS /k -addSn leq_addl.
  exists k.+1.
  rewrite /= T3le_consE ltn0 T3len0 T3lt_psi /lt_psi ha hb hc.
  by case/orP: ax => ->; rewrite !orbT.
* rewrite /= orbC  -/(T3le _ _) => sa sb.
  move: (T3lt_trans (succ_lt x)  sa) => sc.
  exists 1.
  rewrite /= T3le_consE T3lt_psi /lt_psi sc (T3lt_anti sc) (T3lt_ne' sc) /=.
  by case /orP: sb => ->; rewrite !orbT.
* case bz: (b==zero); last first.
    rewrite /= orbF => sa sb;  move:(succ_lt x) => sc; exists 1.
    rewrite /= T3le_consE T3lt_psi /lt_psi sa sc (T3lt_anti sc) (T3lt_ne' sc).
    by rewrite - sa /=; case /orP: sb => ->; rewrite !orbT. 
  rewrite /= orbF => sa sb.
move:(succ_lt x) => sc; case: (T3leP [a, b, c]  y) => sd.
  exists 1; case /orP: sd => xx;
     by rewrite /= T3le_consE T3lt_psi /lt_psi xx sa sc !orbT.
move: sb sd l12h; case y => //.
move => a1 b1 c1 n1 d1 /= ha hb /andP [/andP [/eqP nz /eqP dz]].
move: ha hb; rewrite nz dz => ha.
rewrite  T3lt_psi /lt_psi (eqP bz) (T3lt_anti ha) (T3lt_ne' ha) - sa.
rewrite T3ltn0  !andbF !orbF !T3lt0n /= (eq_sym a).
by case: (T3ltgtP a1 a) => //; case: (b1 == zero).
Qed.

Fixpoint phi6 x y n := 
   if n is n.+1 then [x, y, phi6 x y n] else [x,y,zero].


Fixpoint phi10 x y z n := 
   if n is n.+1 then [x, y, phi10 x y z n] else [x,T3succ y,z].
 
Fixpoint phi12b4 x y z n := 
   if n is n.+1 then [x, y, phi12b4 x y z n] else z.

Lemma limit6 x y: 
    limit_of (phi6 x y) [x,T3succ y, zero].
Proof.
set f := phi6 x y.
have ff:forall n m : nat, (n < m)%N -> f n < f m.
     by apply: fincP => n /=;apply: T3lt_psi_c.  
split => //.
  elim; first by rewrite T3lt_psi /lt_psi eqxx !T3lt0n succ_lt /= orbT.
  by move => n /= H; rewrite /= T3lt_psi /lt_psi H succ_lt eqxx !orbT.
move => z.
move:{2} (size z).+1 (leqnn (size z).+1) =>  n; elim: n z=> //.
move => m Hrec z; rewrite ltnS.
case: z => //; first by move => _  _ _; exists 0; rewrite T3le0n.
move => a b c n d lm ny; rewrite psi_lt1.
move: ny; rewrite /T3nf -/T3nf => /and5P [na nb nc _ _].
move /and5P: (size_prop1 a b c n d) => [la lb lc ld _].
rewrite T3lt_psi /lt_psi !T3ltn0 !andbF !orbF /=.
rewrite (lt_succ_le_3 _ nb).
case /orP.
  move /and3P =>[ax lby cz].
  have [k kp] := (Hrec _ (leq_trans lc lm) nc cz).
  have ck1 := (T3le_lt_trans kp (ff _ _ (ltnSn k))).
  have ck2 := (T3lt_trans ck1 (ff _ _ (ltnSn k.+1))).
  exists k.+2; rewrite T3le_consE T3lt_psi /lt_psi ax ck1 ck2.
  by case /orP:lby => -> //; rewrite orbT.
case /orP.
  move /and3P =>[ax bz cz].
  have [k1 kp1] := (Hrec _ (leq_trans lc lm) nc cz).
  have [k2 kp2] := (Hrec _ (leq_trans lb lm) nb bz).
  set k := (k1 + k2).+1.
  have ha: (b < f k) by apply /(T3le_lt_trans kp2) /ff; rewrite ltnS leq_addl.
  have hb: (c < f k) by apply /(T3le_lt_trans kp1) /ff; rewrite ltnS leq_addr.
  by exists k; rewrite T3le_consE T3lt_psi /lt_psi ax ha hb !orbT.
rewrite - andb_orr orbC => /andP[xa xb].
case abc1: ([a,b,c]== one).
    exists 1; rewrite T3le_consE T3lt_psi /lt_psi xa.
    rewrite (eqP abc1) (eq_sym one y); case: (T3ltgtP y one); rewrite ?orbT //.
    rewrite (T3lt_ne' xa) (T3lt_anti xa) /=  T3lt1 => /eqP ->.
    rewrite T3lt_psi /lt_psi !T3lt0n T3eqE /= (eq_sym x).
    by case: (zero ==x) => //; rewrite eqxx !orbT.
move: xb; rewrite -/(T3le _ _)  succ_psi_lt2 ? abc1 // => xc.
exists 1. 
by rewrite T3le_consE T3lt_psi /lt_psi xa; case /orP: xc => ->; rewrite !orbT.
Qed.

Lemma limit10 x y z: 
    limit_of (phi10 x y z) [x,T3succ y, T3succ z].
Proof.
set f := phi10 x y z.
have ff:forall n m : nat, (n < m)%N -> f n < f m.
     by apply: fincP => n /=;apply: T3lt_psi_c.  
split => //.
  elim; first by rewrite T3lt_psi /lt_psi !eqxx succ_lt. 
  by move => n /= H; rewrite /= T3lt_psi /lt_psi H succ_lt eqxx !orbT.
move => t.
move:{2} (size t).+1 (leqnn (size t).+1) =>  n; elim: n t=> //.
move => m Hrec t; rewrite ltnS.
case: t => //; first by move => _  _ _; exists 0; rewrite T3le0n.
move => a b c n d lm ny; rewrite psi_lt1.
move: ny; rewrite /T3nf -/T3nf => /and5P [na nb nc _ _].
move /and5P: (size_prop1 a b c n d) => [la lb lc ld _].
rewrite T3lt_psi' /lt_psi. 
rewrite (lt_succ_le_3 _ nb) (lt_succ_le_3 _ nc).
have ha:= (T3lt_psi_c x (T3succ y) z).
case abc1: ([a,b,c] == one).  
  case: (eqP abc1) => -> -> ->; exists 0. 
  by rewrite T3le_consE T3gt1 /= /one T3eqE /= (negbTE(succ_nz y)) andbF.
rewrite succ_psi_lt2 ? abc1 //  succ_psi_lt2 ? abc1 //.
case /orP.
   move => /and3P [ax lby cz].
   exists 1.
  rewrite T3le_consE T3lt_psi /lt_psi ax (eqP ax) (eqP lby) succ_lt.
  case /orP: cz; first by move /eqP => ->; rewrite eqxx !orbT.
  by rewrite T3lt_psi /lt_psi !eqxx => ->; rewrite !orbT.
case /orP. 
  move => /and3P [ax lby cz].
  have [k kp] := (Hrec _ (leq_trans lc lm) nc cz).
  have ck1 := (T3le_lt_trans kp (ff _ _ (ltnSn k))).
  have ck2 := (T3lt_trans ck1 (ff _ _ (ltnSn k.+1))).
  exists k.+2; rewrite T3le_consE T3lt_psi /lt_psi ax ck1 ck2.
  by case /orP: lby => -> //;rewrite !orbT.
case /orP. 
  move => /and3P [ax lby cz].
  exists 1.
  rewrite T3le_consE T3lt_psi /lt_psi ax.
  by rewrite (T3le_lt_trans cz ha) (T3lt_trans (succ_lt y) lby) !orbT.
case /orP. 
  move => /and3P [ax bz cz].
  have [k1 kp1] := (Hrec _ (leq_trans lc lm) nc cz).
  have [k2 kp2] := (Hrec _ (leq_trans lb lm) nb bz).
  set k := (k1 + k2).+1.
  have hc: (b < f k) by apply /(T3le_lt_trans kp2) /ff; rewrite ltnS leq_addl.
  have hb: (c < f k) by apply /(T3le_lt_trans kp1) /ff; rewrite ltnS leq_addr.
  by exists k; rewrite T3le_consE T3lt_psi /lt_psi ax hc hb !orbT.
rewrite - andb_orr orbC => /andP[xa xb].
exists 1.
rewrite T3le_consE T3lt_psi /lt_psi xa (T3lt_anti xa)  (T3lt_ne' xa)/=.
case /orP: xb.
  by move => sa; rewrite (T3le_lt_trans sa ha) !orbT.
by case /orP => -> //; rewrite !orbT.
Qed.


Lemma limit12b4 x y z: (limit12_hyp x (T3succ y) z) ->
    limit_of (phi12b4 x y z) [x,T3succ y,z].
Proof.
move => H0.
set f := phi12b4 x y z.
have ff:forall n m : nat, (n < m)%N -> f n < f m.
     by apply: fincP => n /=;apply: T3lt_psi_c.  
split => //.
  elim; first by apply: T3lt_psi_c.
  by move => n /= H; rewrite /= T3lt_psi /lt_psi H succ_lt eqxx !orbT.
move => t.
move:{2} (size t).+1 (leqnn (size t).+1) =>  n; elim: n t=> //.
move => m Hrec t; rewrite ltnS.
case: t => //; first by move => _  _ _; exists 0; rewrite T3le0n.
move => a b c n d lm ny; rewrite psi_lt1.
move: ny; rewrite /T3nf -/T3nf => /and5P [na nb nc _ _].
move /and5P: (size_prop1 a b c n d) => [la lb lc ld _].
rewrite T3lt_psi' /lt_psi.
case /orP.
  move => /and3P[ax yb cz].
  exists 1; rewrite T3le_consE T3lt_psi /lt_psi ax {3} (eqP yb) succ_lt.
  suff: ([a, b, c] < z) by move => ->; rewrite !orbT.
  move: H0 cz;  case z => // a1 b1 c1 n1 d1 /=.
  move => /andP [/andP [/eqP -> /eqP ->]]; rewrite - (eqP yb) - (eqP ax).
  by case /orP => /andP[pa pb] pc; rewrite T3lt_psi /lt_psi pa pb pc !orbT.
case /orP.
  move => /and3P [ax yb cz].
  rewrite (lt_succ_le_3 _ nb)  in yb.
  have [k kp] := (Hrec _ (leq_trans lc lm) nc cz).
  have ck1 := (T3le_lt_trans kp (ff _ _ (ltnSn k))).
  have ck2 := (T3lt_trans ck1 (ff _ _ (ltnSn k.+1))).
  exists k.+2; rewrite T3le_consE T3lt_psi /lt_psi ax ck1 ck2.
  by case /orP: yb => -> //;rewrite !orbT.
case /orP.
  move => /and3P [ax bz cz].
  exists 1; rewrite T3le_consE T3lt_psi /lt_psi ax (T3lt_trans (succ_lt y) bz).
  by case /orP: cz => ->; rewrite !orbT.
case /orP.
  move => /and3P [ax bz cz].
  have [k1 kp1] := (Hrec _ (leq_trans lc lm) nc cz).
  have [k2 kp2] := (Hrec _ (leq_trans lb lm) nb bz).
  set k := (k1 + k2).+1.
  have ha: (b < f k) by apply /(T3le_lt_trans kp2) /ff; rewrite ltnS leq_addl.
  have hb: (c < f k) by apply /(T3le_lt_trans kp1) /ff; rewrite ltnS leq_addr.
  by exists k; rewrite T3le_consE T3lt_psi /lt_psi ax ha hb !orbT.
rewrite - andb_orr orbC => /andP[xa xb].
exists 1.
rewrite T3le_consE T3lt_psi /lt_psi xa (T3lt_anti xa)  (T3lt_ne' xa)/=.
case /orP: xb.
   by case/orP => ->; rewrite !orbT.
rewrite succ_psi_lt2; first by case/orP => ->  //;rewrite !orbT.
by apply/negP;move /eqP => h; move: xa; case: h => ->; rewrite T3ltn0.
Qed.

Fixpoint phi7 x y f n := 
  if n is n.+1 then [x, f n, phi7 x y f n] else y.


Fixpoint phi9 x y f n := 
  if n is n.+1 then [f n, phi9 x y f n,  phi9 x y f n] else [x, zero,y].

Fixpoint phi11 x y z f n := 
  if n is n.+1 then [x,f n, phi11 x y z f n ] else [x, y,z].


Fixpoint phi12b3 y f n := 
  if n is n.+1 then [f n, phi12b3 y f n , phi12b3 y f n] else y.
 

Fixpoint phi12b5 x z f n := 
  if n is n.+1 then [x,f n, phi12b5 x z f n ] else z.


Lemma limit7 x y f: (limit_of f y)  ->
  (limit_of ( phi7 x y f) [x,y,zero]).
Proof.
move => [sa sb sc].
set g := (phi7 x y f). 
have ff:forall n m : nat, (n < m)%N -> g n < g m.
   by apply: fincP => n /=; apply: T3lt_psi_c.  
split => //.
  elim; first by apply: T3lt_psi_b.
  by move => n /= H; rewrite /= T3lt_psi /lt_psi H eqxx sb /= !orbT.
move => t.
move:{2} (size t).+1 (leqnn (size t).+1) =>  n; elim: n t=> //.
move => m Hrec t; rewrite ltnS.
case: t => //; first by move => _  _ _; exists 0; rewrite T3le0n.
move => a b c n d lm nt; rewrite psi_lt1.
move: nt; rewrite /T3nf -/T3nf => /and5P [na nb nc _ _].
move /and5P: (size_prop1 a b c n d) => [la lb lc ld _].
rewrite T3lt_psi' /lt_psi T3ltn0 T3len0 !andbF /=.
case /orP.
  move /and3P => [ax lby cz].
  have [k2 kp2] := (sc _ nb lby).
  have [k1 kp1] := (Hrec _ (leq_trans lc lm) nc cz).
  set k := (k1 + k2).+1.
  have pa:(b < f k) by apply/(T3le_lt_trans kp2) /sa; rewrite ltnS leq_addl.
  have pb: (c < g k.+1)
      by apply/(T3le_lt_trans kp1) /ff; rewrite /k ltnS -addnS leq_addr.
  by exists (k.+1); rewrite T3le_consE T3lt_psi/lt_psi ax pa pb !orbT.
case /orP.
  move /and3P => [ax bz cz].
  have [k1 kp1] := (Hrec _ (leq_trans lc lm) nc cz).
  have [k2 kp2] := (Hrec _ (leq_trans lb lm) nb bz).
  set k := (k1 + k2).+1.
  have pa:(b < g k) by apply/(T3le_lt_trans kp2) /ff; rewrite ltnS leq_addl.
  have pb:(c < g k) by apply/(T3le_lt_trans kp1) /ff; rewrite ltnS leq_addr.
  by exists k; rewrite T3le_consE T3lt_psi/lt_psi ax pa pb !orbT.
rewrite orbF => /andP [ha hb].
exists 1.
by rewrite T3le_consE T3lt_psi/lt_psi ha; case/orP: hb => ->; rewrite !orbT.
Qed.


Lemma limit9 x y f: (limit_of f x)  ->
  (limit_of (phi9 x y f) [x,zero, T3succ y]).
Proof.
move =>  [sa sb sc].
set g := (phi9 x y f). 
have ff:forall n m : nat, (n < m)%N -> g n < g m.
   by apply: fincP => n /=; apply: T3lt_psi_c.  
split => //.
  elim; first by rewrite T3lt_psi/lt_psi eqxx succ_lt.
  by move => n /= H; rewrite /= T3lt_psi /lt_psi H /= -/phi9 sb !orbT.
move => t.
move:{2} (size t).+1 (leqnn (size t).+1) =>  n; elim: n t=> //.
move => m Hrec t; rewrite ltnS.
case: t => //; first by move => _  _ _; exists 0; rewrite T3le0n.
move => a b c n d lm nt; rewrite psi_lt1.
move: nt; rewrite /T3nf -/T3nf => /and5P [na nb nc _ _].
move /and5P: (size_prop1 a b c n d) => [la lb lc ld _].
rewrite T3lt_psi' /lt_psi T3ltn0 T3len0 !andbF /=.
case /orP.
  move /and3P => [ax lby cy].
  rewrite (lt_succ_le_3 _ nc)  in cy.
  exists 1; rewrite T3le_consE T3lt_psi/lt_psi (eqP ax) (sb 0) (eqP lby).
  case /orP: cy; first by move /eqP ->; rewrite eqxx !orbT.
  by rewrite T3lt_psi /lt_psi => ->; rewrite !eqxx /= !orbT.
case /orP.
  move /and3P => [ax lby cy]; rewrite T3lt0n in lby.
  have ha: ([a, b, c] < [a, zero, y]).
    apply:(T3le_lt_trans _ (T3lt_psi_c a zero y)).
    by rewrite - succ_psi_lt2 ?cy // T3eqE (negbTE lby) !andbF.
  exists 1. 
  by rewrite T3le_consE T3lt_psi/lt_psi  -(eqP ax) ha (eqP ax) (sb 0) !orbT.
case /orP.
  move /and3P => [ax bz cz].
  have [k1 kp1] := (Hrec _ (leq_trans lc lm) nc cz).
  have [k2 kp2] := (Hrec _ (leq_trans lb lm) nb bz).
  have [k3 kp3] := (sc _ na ax). 
  set k := (k1 + k2+k3).+1.
  have pa:(b < g k.+1).
   by apply/(T3le_lt_trans kp2) /ff; rewrite /k ltnS - addnS addnAC leq_addl.
  have pb:(c < g k.+1). 
    by apply/(T3le_lt_trans kp1) /ff; rewrite /k ltnS  - addnS - addnA leq_addr.
  have pc:(a < f k). 
    by apply/(T3le_lt_trans kp3) /sa; rewrite ltnS leq_addl.
  by exists k.+1; rewrite T3le_consE T3lt_psi/lt_psi pa pb pc !orbT.
move /andP => [ha hb].
have hc: ([a, b, c] < [x, zero, y]).
  apply:(T3le_lt_trans _ (T3lt_psi_c x zero y)).
  rewrite - succ_psi_lt2 ?cy //; apply /negP => h. 
  by move: ha; case: (eqP h) => ->; rewrite T3ltn0.
exists 1.
by rewrite T3le_consE T3lt_psi/lt_psi (T3lt_trans (sb 0) ha) hc !orbT.
Qed.

Lemma limit11 x y z f: (limit_of f y)  ->
  (limit_of (phi11 x y z f) [x, y, T3succ z]).
Proof.
move =>  [sa sb sc].
set g := (phi11 x y z f). 
have ff:forall n m : nat, (n < m)%N -> g n < g m.
   by apply: fincP => n /=; apply: T3lt_psi_c.  
split => //.
  elim; first by rewrite T3lt_psi/lt_psi !eqxx succ_lt.
  by move => n /= H; rewrite /= T3lt_psi /lt_psi H /= -/phi11 sb eqxx !orbT.
move => t.
move:{2} (size t).+1 (leqnn (size t).+1) =>  n; elim: n t=> //.
move => m Hrec t; rewrite ltnS.
case: t => //; first by move => _  _ _; exists 0; rewrite T3le0n.
move => a b c n d lm nt; rewrite psi_lt1.
move: nt; rewrite /T3nf -/T3nf => /and5P [na nb nc _ _].
move /and5P: (size_prop1 a b c n d) => [la lb lc ld _].
rewrite T3lt_psi' /lt_psi.
case /orP.
  move /and3P => [ax lby cy].
  rewrite (lt_succ_le_3 _ nc)  in cy.
  exists 1; rewrite T3le_consE T3lt_psi/lt_psi (eqP ax) (eqP lby) (sb 0). 
  case /orP: cy; first by move /eqP ->; rewrite !eqxx !orbT.
  by rewrite T3lt_psi /lt_psi => ->; rewrite !eqxx /= !orbT.
case /orP.
  move /and3P => [ax bz cz].
  have [k1 kp1] := (Hrec _ (leq_trans lc lm) nc cz).
  have [k2 kp2] := (sc _ nb bz). 
  set k := (k1 + k2).+1.
  have pa:(b < f k) by apply/(T3le_lt_trans kp2) /sa; rewrite ltnS leq_addl.
  have pb:(c < g k.+1).
    by apply/(T3le_lt_trans kp1) /ff; rewrite /k ltnS -addnS leq_addr.
  by exists k.+1; rewrite T3le_consE T3lt_psi/lt_psi ax pa pb !orbT.
case /orP.
  move /and3P => [ax bz]; rewrite succ_psi_lt2 ?T3eqE ?(T3lcp0_pr bz) ?andbF //.
  by case/orP => h;exists 0; rewrite T3le_consE T3lt_psi/lt_psi ax bz h !orbT.
case /orP.
  move /and3P => [ax bz cz].
  have [k1 kp1] := (Hrec _ (leq_trans lc lm) nc cz).
  have [k2 kp2] := (Hrec _ (leq_trans lb lm) nb bz).
  set k := (k1 + k2).+1.
  have pa:(b < g k) by apply/(T3le_lt_trans kp2) /ff; rewrite ltnS leq_addl.
  have pb:(c < g k) by apply/(T3le_lt_trans kp1) /ff; rewrite ltnS leq_addr.
  by exists k; rewrite T3le_consE T3lt_psi/lt_psi ax pa pb !orbT.
case /orP; move => /andP [xa yb].
  exists 0. 
  by rewrite T3le_consE T3lt_psi/lt_psi xa; case/orP: yb => ->;rewrite !orbT.
exists 0; rewrite T3le_consE T3lt_psi/lt_psi xa.
move: yb; rewrite succ_psi_lt2 ?T3eqE ?(T3lcp0_pr xa) ?andbF //.
by case /orP => ->; rewrite !orbT.
Qed.



Lemma limit12b3 x y f: (limit_of f x)  -> (limit12_hyp x zero y) ->
  (limit_of (phi12b3 y f) [x, zero, y]).
Proof.
move =>  [sa sb sc] H0.
set g := (phi12b3 y f). 
have ff:forall n m : nat, (n < m)%N -> g n < g m.
   by apply: fincP => n /=; apply: T3lt_psi_c.  
split => //. 
  elim; first by apply:T3lt_psi_c.
  by move => n /= H; rewrite /= T3lt_psi /lt_psi H /= -/phi11 sb !orbT.
move => t.
move:{2} (size t).+1 (leqnn (size t).+1) =>  n; elim: n t=> //.
move => m Hrec t; rewrite ltnS.
case: t => //; first by move => _  _ _; exists 0; rewrite T3le0n.
move => a b c n d lm nt; rewrite psi_lt1.
move: nt; rewrite /T3nf -/T3nf => /and5P [na nb nc _ _].
move /and5P: (size_prop1 a b c n d) => [la lb lc ld _].
rewrite T3lt_psi' /lt_psi T3ltn0 !andbF !orFb.
case /orP.
  move /and3P => [ax lby cy].
  exists 1; rewrite T3le_consE T3lt_psi/lt_psi (eqP ax)  (eqP lby)(sb 0).
  suff: ([x, zero, c] < y) by move => ->; rewrite !orbT.
  move: H0 cy;  case y => // a1 b1 c1 n1 d1 /=.
  move => /andP [/andP [/eqP -> /eqP ->]] h; rewrite T3lt_psi' => ->.
  by case /orP:h => /andP[pa pb]; rewrite pa ? pb  !orbT.
case /orP.
  move /and3P => [ax lby cy]. 
  exists 1; rewrite T3le_consE T3lt_psi/lt_psi (eqP ax) (sb 0) - (eqP ax).
  by case /orP: cy => ->; rewrite !orbT.
case /orP.
  move /and3P => [ax lby cy].
  have [k1 kp1] := (Hrec _ (leq_trans lc lm) nc cy).
  have [k2 kp2] := (Hrec _ (leq_trans lb lm) nb lby).
  have [k3 kp3] := (sc _ na ax). 
  set k := (k1 + k2+k3).+1.
  have pa:(b < g k.+1).
   by apply/(T3le_lt_trans kp2) /ff; rewrite /k ltnS - addnS addnAC leq_addl.
  have pb:(c < g k.+1). 
    by apply/(T3le_lt_trans kp1) /ff; rewrite /k ltnS  - addnS - addnA leq_addr.
  have pc:(a < f k). 
    by apply/(T3le_lt_trans kp3) /sa; rewrite ltnS leq_addl.
  by exists k.+1; rewrite T3le_consE T3lt_psi/lt_psi pa pb pc !orbT.
move /andP => [ax bx]. 
exists 1; rewrite T3le_consE T3lt_psi/lt_psi (T3lt_trans (sb 0) ax).
by case /orP: bx => ->; rewrite !orbT.
Qed.


Lemma limit12b5 x y z f: (limit_of f y)  -> (limit12_hyp x y z) ->
  (limit_of (phi12b5 x z f) [x,y,z]).
Proof.
move =>  [sa sb sc] H0.
set g := (phi12b5 x z f). 
have ff:forall n m : nat, (n < m)%N -> g n < g m.
   by apply: fincP => n /=; apply: T3lt_psi_c.  
split => //. 
  elim; first by apply:T3lt_psi_c.
  by move => n /= H; rewrite /= T3lt_psi /lt_psi H eqxx /= -/phi11 sb !orbT.
move => t.
move:{2} (size t).+1 (leqnn (size t).+1) =>  n; elim: n t=> //.
move => m Hrec t; rewrite ltnS.
case: t => //; first by move => _  _ _; exists 0; rewrite T3le0n.
move => a b c n d lm nt; rewrite psi_lt1.
move: nt; rewrite /T3nf -/T3nf => /and5P [na nb nc _ _].
move /and5P: (size_prop1 a b c n d) => [la lb lc ld _].
rewrite T3lt_psi' /lt_psi.
case /orP.
  move /and3P => [ax lby cy].
  exists 1; rewrite T3le_consE T3lt_psi/lt_psi ax (eqP lby)(sb 0) cy.
  suff: ([a, y, c] < z) by move => ->; rewrite !orbT.
  move: H0 cy;  case z => // a1 b1 c1 n1 d1 /=.
  move => /andP [/andP [/eqP -> /eqP ->]] h; rewrite T3lt_psi' => ->.
  by case /orP:h => /andP[pa pb]; rewrite (eqP ax) pa ? pb  !orbT.
case /orP.
  move /and3P => [ax lby cy]. 
  have [k1 kp1] := (Hrec _ (leq_trans lc lm) nc cy).
  have [k2 kp2] := (sc _ nb lby). 
  set k := (k1 + k2).+1.
  have pa:(b < f k) by apply/(T3le_lt_trans kp2) /sa; rewrite ltnS leq_addl.
  have pb:(c < g k.+1).
    by apply/(T3le_lt_trans kp1) /ff; rewrite /k ltnS -addnS leq_addr.
  by exists k.+1; rewrite T3le_consE T3lt_psi/lt_psi ax pa pb !orbT.
case /orP.
  move /and3P => [ax lby cy]. 
  exists 1; rewrite T3le_consE T3lt_psi/lt_psi ax (T3lt_trans (sb 0) lby).
  by case/orP: cy => ->; rewrite !orbT.
case/orP.
  move /and3P => [ax lby cy].
  have [k1 kp1] := (Hrec _ (leq_trans lc lm) nc cy).
  have [k2 kp2] := (Hrec _ (leq_trans lb lm) nb lby).
  set k := (k1 + k2).+1.
  have pa:(b < g k) by apply/(T3le_lt_trans kp2) /ff; rewrite ltnS leq_addl.
  have pb:(c < g k) by apply/(T3le_lt_trans kp1) /ff; rewrite ltnS leq_addr.
  by exists k; rewrite T3le_consE T3lt_psi/lt_psi ax pa pb !orbT.
case/orP;move /andP => [ax bx].
  case (T3ltP z y) => yz; last first.
    exists 1; rewrite T3le_consE T3lt_psi/lt_psi ax. 
    by case/orP: (T3le_trans bx yz) => ->; rewrite !orbT.
  move: H0 yz; case z => // a1 b1 c1 n1 d1 /=.
    move => /andP [/andP [/eqP -> /eqP ->]] pv pw; move: pv.
    rewrite (T3lt_anti (T3lt_trans (T3lt_psi_b a1 b1 c1) pw)).
    by rewrite (T3lt_anti pw) !andbF. 
exists 1.  
by rewrite T3le_consE T3lt_psi/lt_psi ax; case/orP: bx => ->; rewrite !orbT.
Qed.

Definition phi_rec_psi f a b c :=
  if (c==zero) then 
    if(b==zero) then
       if(a==zero) then phi0
       else if(T3is_succ a) then phi4 (T3pred a) 
       else phi5 (f a)
    else if(T3is_succ b) then phi6 a (T3pred b)
    else phi7 a b (f b)
  else if(T3is_succ c) then 
    if(b==zero) then
      if(a==zero) then phi3 [zero,zero, T3pred c]
      else if (T3is_succ a) then phi8 (T3pred a) (T3pred c)
      else phi9 a (T3pred c) (f a)
    else if(T3is_succ b) then phi10 a (T3pred b) (T3pred c)
    else phi11 a b (T3pred c) (f b) 
  else if (limit12_hyp a b c) then
    if(b==zero) then
      if(a==zero) then phi3 c
      else if(T3is_succ a) then phi12b2 (T3pred a) c
      else phi12b3 c (f a)
    else if (T3is_succ b) then phi12b4 a (T3pred b) c
    else phi12b5 a c (f b)
  else phi12a a b (f c).

Definition phi_rec f (x: T3) :=
  if x is cons a b c n d then 
  if (d==zero) then 
    if n is n.+1 then phi1 (cons a b c n zero) (phi_rec_psi f a b c)
     else phi_rec_psi f a b c
  else phi1 (cons a b c n zero) (f d) 
  else phi0.


Fixpoint phia k := if k is k.+1 then phi_rec (phia k) else (fun x =>phi0).
Definition phi x := phia (size x).+1 x.

Lemma phiE x : phi x = phi_rec phi x.
Proof.
have aux: forall n x, 
     (size x < n)%N -> phia n x = (phi x).
   clear x; move => n; elim: n {1 3 4} n (leqnn n); first by case.
  move => k0 Hrec [] // k1; rewrite ltnS => k1k0.
  case => // a b c n d; rewrite ltnS => e3.
  move /and5P:(size_prop1 a b c n d) => [pa pb pc pd pe].
  have la:= (leq_trans pa e3).
  have lb:= (leq_trans pb e3).
  have lc:= (leq_trans pc e3).
  have ld:= (leq_trans pd e3).
  have le: (size (cons a b c 0 d) <= k0)%N.
    by move:(leq_trans e3 k1k0).
  rewrite /phi /phia -/phia /phi_rec -/phi -/(phi_rec _ d).
  case dz: (d==zero). 
    case n; first by rewrite /phi_rec_psi !Hrec //.
    by move => m; congr (phi1 _ _);rewrite /phi_rec_psi !Hrec.
   by congr phi1; rewrite !Hrec.
case x => // a b c n d.
move: (size_prop1 a b c n d).
move/and5P=> [pa pb pc pd pe]. 
rewrite /phi /phia -/phia /phi_rec -/phi -/(phi_rec _ d).
case dz: (d==zero). 
  case n; first by rewrite /phi_rec_psi !aux.
  by move => m; congr (phi1 _ _);rewrite /phi_rec_psi !aux.
by congr phi1; rewrite aux.
Qed.

Lemma phiE_1 a b c n: 
  phi (cons a b c n.+1 zero) = phi1 (cons a b c n zero) (phi [a, b, c]).
Proof. by rewrite phiE /=; congr phi1; rewrite phiE /phi_rec eqxx. Qed.

Lemma phiE_2 a b c n d: d != zero ->
  phi (cons a b c n d) = phi1 (cons a b c n zero) (phi d).
Proof. by move => dz; rewrite phiE /phi_rec (negbTE dz). Qed.

Lemma phiE_3 a b c:  phi ([a,b,c]) = phi_rec_psi phi a b c.
Proof. by rewrite phiE /phi_rec. Qed.

Lemma phiL x: T3nf x -> T3limit x -> limit_of (phi x) x.
Proof.
set n := (size x).+1.
move: (leqnn n); rewrite {1}/n; move: n => n.
elim: n x => [ // | k Hr]; case => //.
move => a b c n d; rewrite ltnS => sa nx.
move: (size_prop1 a b c n d) => /and5P[la lb lc ld le].
move: (nx); rewrite nf_consE => /and3P [nabc nd ne] lx.
case dz: (d==zero); last first.
  move: lx => /=; rewrite dz /=; case:(all_zero a b c) => // ly. 
  have py: limit_of (phi d) d by  apply: Hr => //; apply: (leq_trans ld sa).
  have pd: T3nf(cons a b c n zero) by rewrite nf_consE nabc.
  rewrite  phiE_2 ? dz // - (add_to_cons n ne); exact: (limit1 pd py).
suff: limit_of (phi [a, b, c]) [a, b, c].
  rewrite (eqP dz); case n => // m ha.
  have ny: T3nf (cons a b c m zero) by rewrite nf_consE nabc.
  by move: (limit1 ny ha); rewrite phiE_1 /T3add T3ltnn addn0.
have la':= (leq_trans la sa).  
have lb':= (leq_trans lb sa).
have lc':= (leq_trans lc sa).
move: lx; rewrite /T3limit dz /= => lx.
clear d la lb lc ld le sa nx nd dz ne.
rewrite phiE_3 /phi_rec_psi.
move: nabc; rewrite /T3nf -/T3nf =>/and5P[na nb nc _ _].
move: (limit_pr1 c).
case cz: (c==zero).
  move: (limit_pr1 b).
  case bz: (b==zero).
    rewrite (eqP bz) (eqP cz). 
    move: lx (limit_pr1 a); rewrite /all_zero bz cz.
    case az: (a==zero) => //=. 
    case la: (T3is_succ a).
      move => _ _ _ _; rewrite {2} (succ_pred na la); apply: limit4.
    by rewrite addbF => _ lla _ _; apply: limit5; apply: Hr.
  case lb: (T3is_succ b). 
    rewrite {3} (succ_pred nb lb)  (eqP cz) => _ _; apply: limit6.
  by rewrite addbF => /= llb _; rewrite (eqP cz); apply: limit7;apply: Hr.
case lc: (T3is_succ c).
  move: (limit_pr1 b).
  case bz: (b==zero).
    move: (limit_pr1 a).
    case az: (a==zero).
      rewrite (eqP az) (eqP bz)  {3} (succ_pred nc lc) => _ _ _; apply: limit3.
    case la: (T3is_succ a).
      move => _ _ _; rewrite {2}(succ_pred na la) {2}(succ_pred nc lc)(eqP bz).
      apply: limit8.
    rewrite /= addbF (eqP bz) {3}(succ_pred nc lc)=>  lla _ _. 
    by apply: limit9; apply: Hr.
  case lb: (T3is_succ b). 
    move => _ _.  rewrite {2}(succ_pred nb lb) {2}(succ_pred nc lc). 
    apply: limit10.
  rewrite /= addbF {3}(succ_pred nc lc) => lbb _; apply: limit11.
  by apply: Hr.
rewrite /= addbF => lcc; move: (Hr _ lc' nc lcc) => hc.
case h12: (limit12_hyp a b c); last by apply: limit12a => //; rewrite h12.
move: (limit_pr1 b).
case bz: (b==zero).
  move: (limit_pr1 a); move: h12.
  case az: (a==zero).
    by rewrite (eqP az) (eqP bz) => h12 _ _; apply:limit12b1.
  case la: (T3is_succ a).
    rewrite {1 4}(succ_pred na la) (eqP bz) => h12 _ _.
    by apply: limit12b2.
  rewrite /= addbF (eqP bz)=> h12 lla _. 
  by apply: limit12b3 => //; apply: Hr.
case lb: (T3is_succ b).
  by move: h12;rewrite {1 4}(succ_pred nb lb) => h12 _; apply: limit12b4.
by rewrite /= addbF => llb; apply: limit12b5 => //; apply: Hr.
Qed.


Lemma conc1 (x:= [zero,zero, epsilon0]): limit_of (phi3 epsilon0) x.
Proof.
have ->: (phi3 epsilon0) = phi x.
  by rewrite /x phiE_3 /= /phi_rec_psi -/phi_rec_psi eqxx /=.
by apply: phiL.
Qed.


(** ** additive principal *)

Definition T3ap x := 
  if x is cons a b c n d then ((n==0) && (d==zero)) else false.

Lemma ap_pr0 a b c (x := [a,b,c]) u v:
  u < x -> v < x -> u + v < x.
Proof.
case: u v; [by move => u |move => a1 b1 c1 n1 d1].
case; [by move => H  _ | move => a' b' c' n' d' l1 l2 /=].
have aux: forall n' d', cons a1 b1 c1 n' d' < x.
  by move => n'' d'';move: l1;rewrite psi_lt1 psi_lt1.
by case: (T3ltgtP [a1, b1, c1]  [a', b', c']).
Qed.

Lemma ap_limit x: T3ap x -> (x == one) || (T3limit x).
Proof.
case: x => // a b c n d /= /andP[/eqP -> /eqP ->]; rewrite all_zeroE /=.
by case: eqP.
Qed.

Lemma ap_pr1 c: 
   (forall a b,  a < c -> b < c -> a + b < c)  ->
   (c== zero) || T3ap c.
Proof.
case: c => // a b c n d /=.
case: n d => [d H | n d H]; last first.
  have l2: (cons a b c n d) < (cons a b c n.+1 d) by rewrite psi_lt2 ltnS leqnn.
  move: (H _ _ l2 l2). rewrite /= psi_lt2 /= psi_lt2 /= T3ltnn if_same ltnS.
  by rewrite -{3}(add0n n) ltn_add2r.
case dz: (d == zero) => //.
have pa: [a,b,c] < cons a b c 0 d by rewrite psi_lt2 /= T3lt0n dz.
by move: (H _ _ pa pa); rewrite /= psi_lt2 /= psi_lt2.
Qed.

Lemma ap_pr2 c: 
   T3nf c -> c <> zero ->
   (forall a b, T3nf a -> T3nf b ->  a < c -> b < c -> a + b < c)  ->
   T3ap c.
Proof.
case: c => // a b c n d nd _ Hr.
have {Hr} H: forall u, T3nf u -> u < cons a b c n d  -> u + u < cons a b c n d.
  by move => u ua ub; apply: Hr.
case: n d H nd => [d H | n d H].
  rewrite /T3nf -/T3nf => /and5P[na nb nc nd ne].
  have np: T3nf [a,b,c] by rewrite nf_psi na nb nc.
  move: (H _ np). 
  rewrite T3lt_consE T3ltnn eqxx /= T3ltnn T3lt_consE T3ltnn eqxx /= T3lt0n.
  by case: eqP => // _; apply.
have l2: (cons a b c n d) < (cons a b c n.+1 d) by rewrite psi_lt2 ltnS leqnn.
move=> pa; have pb: T3nf (cons a b c n d) by move: pa; rewrite /T3nf -/T3nf.
move: (H _ pb l2); rewrite /= T3ltnn psi_lt2 T3ltnn ltnS if_same.
by rewrite  -{3}(add0n n) ltn_add2r /=.
Qed.


Lemma ap_pr3 a b c y (x := [a,b,c]): y < x -> y + x = x.
Proof.
by case: y => // a' b' c' n' d' /=; rewrite /x psi_lt1 => ->.
Qed.

Lemma ap_pr4 x: (forall b, b < x -> b + x = x) -> (x == zero) || T3ap x.
Proof.
case: x => // a b c /=; case => [d H|].
  move: (H [ a, b, c]).
  rewrite /= T3ltnn psi_lt2 /=  T3lt0n; case:eqP => //=.
  by move => _ /(_ erefl). 
move => n d H /=.
move: (H (cons a b c n zero)).
rewrite /= T3lt_consE T3ltnn eqxx ltnS leqnn.
by move => /(_ erefl); case => /eqP; rewrite  - {3} (addn0 n) eqn_add2l.
Qed.

Lemma ap_pr2CE (c := cons zero zero T3bad 1 zero):
   (forall a b, T3nf a -> T3nf b ->  a < c -> b < c -> a + b < c).
Proof.
move => a b na nb.
have aux: forall a' b' c' n' d',
    cons a' b' c' n' d' < c =
     if (a'==zero) && (b'==zero) then 
         if (c' < T3bad) then true else if (c'==T3bad) then n'==0  else false
     else  ([a', b', c'] < T3bad).
  move => a' b' c' n' d'. 
  rewrite /c T3lt_consE T3ltn0 !if_same if_simpl ltnS leqn0 T3eqE !eqxx.
  rewrite T3lt_psi /lt_psi !T3ltn0 !T3lt0n !andbF /=.
  case pa: (a'==zero) => /=; last by rewrite T3eqE pa /= orbF if_simpl.
  case pb: (b'==zero); last by rewrite  T3eqE pb andbF /= orbF if_simpl.
  by case : (T3ltgtP c' T3bad).
move: na nb;case: a; first by rewrite T3add0n.
move => a' b' c' n' d' HA; case: b; first by rewrite T3addn0.
move => a'' b'' c'' n'' d'' _.
rewrite aux.
case pa: ((a' == zero) && (b' == zero)); last first.
  move => H; rewrite aux.
  case pa': ((a'' == zero) && (b'' == zero)) => H' /=;
    by case: (T3ltgtP [a', b', c'] [a'', b'', c'']) => sa; rewrite aux ?pa ?pa'.
move => pb; rewrite aux.
case pa': ((a'' == zero) && (b'' == zero)) => H' /=; last first.
  case: (T3ltgtP [a', b', c'] [a'', b'', c'']) => pb'; rewrite aux ?pa ?pa' //.
  move: pb; case: (T3ltgtP c' T3bad) => // ww.
  by move: pa pa'; case: pb' => -> -> _ ->.
move/andP: pa => [/eqP -> /eqP ->].
move/andP: pa' => [/eqP -> /eqP ->].
rewrite !T3lt_psi /lt_psi eqxx T3ltnn /= !orbF.
case: (T3ltgtP c' c'') => h; rewrite aux => //=.
move:pb;case: (T3ltgtP c' T3bad) => // ww.
by move: HA; rewrite /T3nf ww /T3bad /T3nf -/T3nf T3ltnn !andbF.
Qed.


Definition psi_succ x :=
  if x is cons a b c _ _ then 
   if ((a==zero) && (b==zero)) then [zero,zero, T3succ c] else [zero,zero, x]
  else zero.

Lemma psi_succ_pr1 a b c: [a,b,c] < psi_succ ([a,b,c]).
Proof.
simpl; case ha: ((a== zero)  && (b==zero)); last by apply: T3lt_psi_c.
move/andP:ha => [/eqP -> /eqP ->]. 
by rewrite lt_omega2 eqxx succ_lt.
Qed.


Lemma succ_psi1 a b c (x:= [a, b, c]): ((a != zero) || (b != zero)) ->
    (forall a' b' c',  x < [a',b',c'] -> (psi_succ x) <=  [a',b',c']).
Proof. 
move => sab.
rewrite {2}/x /psi_succ -(negbK ((a == zero) && (b == zero))) negb_and sab /=.
move => a' b' c' ee; move: (ee).
rewrite /T3le !T3lt_psi /lt_psi !T3ltn0 !T3lt0n andbF /= ee.
move: sab.
case az: (a'==zero) => //; rewrite ?orbT // (eq_sym zero a') az /=.
rewrite (eqP az) T3ltn0 T3lt0n T3eqE (eq_sym zero b').
case az': (a==zero) => //=; case bz': (b'==zero) => //=; rewrite (eqP bz') //.
   rewrite T3ltn0 T3lt0n eqxx !orbF; case bz: (b==zero) => //=.
   by rewrite  orbC andbT. 
by rewrite /= orbC eqxx andbT orbF.
Qed.


Lemma succ_psi2 u (x := [zero,zero,u]) :
   (forall a' b' c', T3nf c' -> x < [a',b',c'] -> (psi_succ x) <=  [a',b',c']).
Proof.
move => a' b' c' nc'.
rewrite /T3le lt_omega2 /x /psi_succ eqxx /=; rewrite lt_omega2.
case pa: ((a' == zero) && (b' == zero)).
   rewrite lt_succ_le_4 //; case/orP; last by move => ->; rewrite orbT.
   by move => /eqP ->; move/andP: pa => [/eqP -> /eqP ->]; rewrite eqxx.
by move => h;rewrite succ_psi_lt // ? orbT //; rewrite T3eqE andbA pa.
Qed.


Lemma succ_prCE  (u:= one) (v := T3bad):  (u < v) && (v < T3succ u).
Proof. done. Qed.

Lemma succ_psiCE (z := [zero,zero, T3bad]):
   (omega < z) && (z < (psi_succ omega)) && ~~(T3nf z).
Proof. done. Qed.


Definition sup_of (f: T3-> T3) x z :=
  [/\ T3nf z,
      (forall y, T3nf y -> y < x -> f y <= z) &
      (forall z', T3nf z' -> z' < z -> exists y, 
          [&& T3nf y, y < x & z' < f y])].


Definition normal f:=
  [/\ forall x, T3nf x -> T3nf (f x),
      (forall x y, T3nf x -> T3nf y -> x < y -> f x < f y)&
      (forall x, T3nf x -> T3limit x -> sup_of f x (f x)) ].


Lemma sup_unique f x z z': sup_of f x z -> sup_of f x z' -> z = z'.
Proof. 
move => [pa pb pc] [pa' pb' pc']; case (T3ltgtP z z') => // sa.
  move: (pc' z pa sa) => [y /and3P [ya yb yc]].
  by move: (pb _ ya yb); rewrite (T3leNgt) yc.
move: (pc _ pa' sa) => [y /and3P [ya yb yc]].
by move: (pb' _ ya yb); rewrite (T3leNgt) yc.
Qed.

Lemma sup_Oalpha_zero: sup_of id zero zero.
Proof.
by split; [ | move => y _; rewrite T3ltn0 | move => z; rewrite T3ltn0 ].
Qed.


Lemma sup_Oalpha_limit x: T3nf x -> T3limit x -> sup_of id x x.
Proof.
move => nx lx ;split; [done | by move => y _ /T3ltW | ].
move => z nz H.
by exists (T3succ z); rewrite (limit_pr lx H) succ_lt nf_succ.
Qed.

Lemma sup_Oalpha_succ x: T3nf x -> sup_of id (T3succ x) x.
Proof.
move => nx;split. 
- done.
- by move => y nf; rewrite lt_succ_le_3.
- by move => z nz zx; exists x; rewrite succ_lt nx zx.
Qed.

Lemma normal_id: normal id.
Proof. split => //; apply: sup_Oalpha_limit. Qed.

Lemma normal_limit f x: normal f -> T3nf x -> T3limit x -> T3limit (f x).
Proof.
move => [pa pb pc] nx lx.
move: (pc _ nx lx) => [sa sb sc].
move: (limit_pr1 (f x)); case fz: (f x == zero).
  have zx:  zero < x by move: lx; case x. 
  have nz: T3nf zero by [].
  by move: (pb zero x nz nx zx);  rewrite (eqP fz) T3ltn0.
case: (T3limit (f x)) => //= sf.
have sd:T3pred (f x) < f x by rewrite {2} (succ_pred  (pa _ nx) sf) succ_lt.
move: (sc  _ (nf_pred sa) sd) => [y /and3P[ny yx yc]].
move: yc; rewrite (lt_succ_le_4 _ (pa  _ ny)).
by rewrite -(succ_pred  (pa _ nx) sf) T3leNgt (pb _ _ ny nx yx).
Qed.

Lemma normal_compose f g: 
   normal f -> normal g -> normal (f \o g).
Proof.
move => [pa pb pc][pa' pb' pc']; split.
- by move => x nx; apply: pa; apply: pa'.
- by move => x y nx ny h; apply: pb; [ apply: pa' | apply: pa' | apply: pb'].
- move => x nx lx. 
  move: (pa' _ nx) => ny.
  have lg: T3limit (g x) by  apply:normal_limit.
  move:(pc _ ny lg) => [qa qb qc]; split => //.
    move => y nu yx /=; apply:T3ltW;apply: pb; auto.
  move: (pc' _ nx lx) => [qa' qb' qc'].
  move => z' nz' h /=; move: (qc _ nz' h) => [y /and3P[ya yb yc]].
  move: (qc' _ ya yb) => [z /and3P[za zb zc]]; exists z.
  by rewrite za zb /=;  apply: (T3lt_trans yc); apply: pb => //; apply: pa'.
Qed.

Lemma add_normal a:  T3nf a -> normal (T3add a).
Proof.
move => na;split.
    by move => x nx; apply: nf_add.
  by move => x y nx ny; rewrite T3lt_add2l. 
move => x nx lx; split.
    by apply: nf_add.
  by move  => y _ /T3ltW; rewrite T3le_add2l.
move => z nz zp; case (T3ltP z a) => az.
  by exists zero; move: lx;rewrite T3addn0 az T3lt0n; case x.
move: (sub_pr1 nz az) => sa.
move:zp; rewrite {1} sa T3lt_add2l => sb.
exists (T3succ (z - a)).
by rewrite (nf_succ (nf_sub nz na)) (limit_pr lx sb) {1} sa T3lt_add2l succ_lt.
Qed.



End Ackermann.


(* to move elsewhere *)

(*
Section foo.


Variable P: pred T3.
Hypothesis exP : exists n, P n.

Inductive acc_T3 i : Prop := AccT0 of P i | 
 AccT3: forall j, i < j -> acc_T3 j -> acc_T3 i.

Lemma foo: acc_T3 zero.
Proof.  
Abort.
*)




