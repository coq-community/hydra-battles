(**  

  A type for ordinals terms in Cantor Normal Form

After Manolios and Vroon's work on ACL2 


Pierre Casteran 
LaBRI, University of Bordeaux 

Evelyne Contejean
LRI 

 
*)

From Coq Require Import Arith Max Bool Lia  Compare_dec  Relations Ensembles
     Wellfounded Bool RelationClasses Operators_Properties ArithRing
     Logic.Eqdep_dec.

From Coq Require PArith.
From hydras  Require Import  More_Arith  Restriction   DecPreOrder.
From hydras Require Import OrdNotations.
Set Implicit Arguments.

Declare Scope t1_scope.
Delimit Scope t1_scope with t1.
Open Scope t1_scope.

Coercion is_true: bool >-> Sortclass.


(** *  Definitions 

 *)

(**  **  A type of terms (not necessarily in normal form)

[ocons a n b]  is intended to represent
  the ordinal  [omega^a * (S n)  + b]

Note that [T1] contains terms which are not in Cantor normal  form.
This issue is solved later which the help of the predicate [nf]

*)
  
Inductive T1 : Set  :=
| zero 
| ocons (alpha : T1) (n : nat) (beta : T1) .
 




(** Basic functions and predicates on [T1] 
*)

Notation one := (ocons zero 0 zero).
Notation omega := (ocons (ocons zero 0 zero) 0 zero).


(** The [(S n)]-th ordinal 
 *)

Notation FS n := (ocons zero n zero).

(** the [n]-th ordinal 
 *)

Definition fin (n:nat) := match n with 0 => zero | S p => FS p end.
Coercion fin  : nat >-> T1.


(* begin hide *)
Lemma FS_rw (n:nat) : FS n = S n.
Proof. reflexivity. Qed.
(* end hide *)



(** Successor and limits (syntactic definitions) *)

Fixpoint succb alpha :=
  match alpha with
      zero => false
    | ocons zero _ _ => true
    | ocons alpha n beta => succb beta
  end.

Fixpoint limitb alpha :=
  match alpha with
      zero => false
    | ocons zero _ _ => false
    | ocons alpha n zero => true
    | ocons alpha n beta => limitb beta
  end.

(** Exponential of base [omega] *)

Notation "'phi0' alpha" := (ocons alpha 0 zero) (at level 10) : t1_scope.


(** multiples of [phi0 alpha]  *)

Definition omega_term (alpha:T1)(k:nat) :=
  ocons alpha k zero.


(**  omega towers 
*)

Fixpoint tower (height:nat) : T1 := 
 match height with 
| 0 =>  FS 0 
| S h => phi0 (tower h)
 end.


(** Additive principal ordinals 
 *)

Inductive ap : T1 -> Prop :=
  ap_intro : forall a, ap (phi0 a).



(**  **  A linear  strict order on [T1] 
 *)

Fixpoint compare (alpha beta:T1):comparison :=
  match alpha, beta with
    zero, zero => Eq
  | zero, ocons a' n' b' => Lt
  | _   , zero => Gt
  | (ocons a n b),(ocons a' n' b') =>
      (match compare a a' with 
       | Lt => Lt
       | Gt => Gt
       | Eq => (match Nat.compare n n' with
                | Eq => compare b b'
                | comp => comp
                end)
       end)
  end.


Definition lt_b alpha beta : bool :=
  match compare alpha beta with
      Lt => true
    | _ => false
  end.


Definition le_b alpha beta := negb (lt_b beta alpha).

Definition eq_b alpha beta := match compare alpha beta with
                                Eq => true
                              | _ => false
                              end.

Definition lt alpha beta : Prop := lt_b alpha beta.

Example Ex0:
  lt (ocons (phi0 (phi0 omega)) 2
            (ocons (phi0 10) 33
                   (ocons (phi0 9) 63 zero)))
     (ocons  (phi0 (phi0 omega)) 2 (phi0 (phi0 11))).
Proof. reflexivity. Qed.

Definition le (alpha beta :T1) :=
  match compare alpha beta with
    Gt => False
  | _ => True
  end. 

Global Hint Unfold le : T1. 




(**   ** The predicate "to be in normal form" 

Cantor normal form needs the exponents of omega to be
   in strict decreasing order *)


Fixpoint nf_b (alpha : T1) : bool :=
  match alpha with
    | zero => true
    | ocons a n zero => nf_b a
    | ocons a n ((ocons a' n' b') as b) =>
      (nf_b a && nf_b b && lt_b a' a)%bool
  end. 

Definition nf alpha :Prop := nf_b alpha .

(** epsilon0 as a set *)

Definition epsilon_0 : Ensemble T1 := nf.


(** ** Arithmetic functions 
*)

(** *** Successor *)

Fixpoint succ (alpha:T1) : T1 :=
  match alpha with zero => fin 1
             | ocons zero n _ => ocons zero (S n) zero
             | ocons beta n gamma => ocons beta n (succ gamma)
 end.

(** *** Predecessor (partial function *)

Fixpoint pred (c:T1) : option T1 :=
  match c with zero => None
             | ocons zero 0 _ => Some zero
             | ocons zero (S n) _ => Some (ocons zero n zero)
             | ocons a n b => 
                  match (pred b) with None => None
                                    | Some c => Some (ocons a n c)
                  end
  end.

(** *** Addition *)

Fixpoint plus (alpha beta : T1) :T1 :=
  match alpha,beta with
  |  zero, y  => y
 |  x, zero  => x
 |  ocons a n b, ocons a' n' b' =>
    (match compare a a' with
     | Lt => ocons a' n' b'
     | Gt => (ocons a n (plus b (ocons a' n' b')))
     | Eq  => (ocons a (S (n+n')) b')
     end)
  end
where "alpha + beta" := (plus alpha beta) : t1_scope.




(** *** multiplication *)

Fixpoint mult (alpha beta : T1) :T1 :=
  match alpha,beta with
 |  zero, _  => zero
 |  _, zero => zero
 |  ocons zero n _, ocons zero n' _ => 
                 ocons zero (Peano.pred((S n) * (S n'))) zero
 |  ocons a n b, ocons zero n' _ =>  
                 ocons a (Peano.pred ((S n) * (S n'))) b
 |  ocons a n b, ocons a' n' b' =>
     ocons (a + a') n' ((ocons a n b) * b')
 end
where  "alpha * beta" := (mult alpha beta) : t1_scope.



(**  *** Substraction  (used as a helper for exponentiation) *)

Fixpoint minus (alpha beta : T1) :T1 :=
  match alpha,beta with
 |  zero, y  => zero
 |  ocons zero n _, ocons zero n' _ =>
                  if (le_lt_dec n n') 
                  then zero
                  else  ocons zero (Peano.pred (n-n')) zero
 |  ocons zero n _, zero =>  ocons zero n zero
 |  ocons zero n _, y =>  zero
 |  ocons a n b, zero =>  ocons a n b
 |  ocons a n b, ocons a' n' b' =>
      (match compare a a' with 
            | Lt => zero
            | Gt => ocons a n b
            | Eq => (match Nat.compare n n' with
                   | Lt => zero
                   | Gt => (ocons a (Peano.pred (n - n')) b')
                   | Eq => b - b'
                   end)
       end)
 end
 where  "alpha - beta" := (minus alpha beta):t1_scope.

(**  ***  exponentiation functions  
*)


Fixpoint exp_F (alpha : T1)(n : nat) :T1 :=
 match n with 
 | 0 =>  FS 0
 | S p => alpha * (exp_F alpha p)
 end.



Fixpoint exp  (alpha beta : T1) :T1 :=
  match alpha ,beta with
 |  _, zero => ocons zero 0 zero
 | ocons zero 0 _ , _ => ocons zero 0 zero
 | zero, _         => zero
 | x , ocons zero n' _ =>  exp_F x (S n')
 | ocons zero n _, ocons  (ocons zero 0 zero) n'  b' =>
        ((ocons (ocons zero n' zero) 0 zero) * 
                ((ocons zero n zero) ^  b'))
 | ocons zero n _, ocons  a' n' b' =>
            (omega_term 
                    (omega_term (a' - 1) n')
                    0) *
                 ((ocons zero n zero) ^ b')
 | ocons a  n b, ocons  a' n' b' =>
    ((omega_term   (a * (ocons a' n' zero)) 
                            0) * 
            ((ocons a n b) ^ b'))
end 
where "alpha ^ beta " := (exp alpha beta) : t1_scope.

(** * Lemmas *)

Lemma compare_refl : forall alpha, compare alpha alpha =  Eq.
Proof.
 induction alpha; cbn; auto.
 rewrite IHalpha1, IHalpha2.
 now rewrite Nat.compare_refl.
Qed.

Lemma compare_of_phi0 alpha beta:
  compare (phi0 alpha) (phi0 beta) = compare alpha beta.
   cbn;  now destruct (compare alpha beta).
Qed.



Lemma zero_lt : forall alpha n beta, lt  zero (ocons alpha  n beta).
Proof.  reflexivity. Qed. 

Lemma head_lt :
  forall alpha alpha' n n' beta beta',
       lt alpha  alpha' -> 
       lt (ocons alpha n beta)  (ocons alpha' n' beta').
Proof.
  unfold lt, lt_b ;  intros.   
  cbn;  destruct (compare alpha alpha') ; auto;   discriminate. 
Qed.

Lemma coeff_lt : forall alpha n n' beta beta',
                (n < n')%nat -> 
                lt (ocons alpha n beta)  (ocons alpha n' beta').
Proof.
  unfold lt, lt_b ;  intros;  cbn;   rewrite compare_refl.
  now apply Nat.compare_lt_iff in H as ->.
Qed. 

Lemma tail_lt : forall alpha n beta beta',
               lt beta  beta' -> 
               lt (ocons alpha n beta)  (ocons alpha n beta').
Proof.
 intros; unfold lt, lt_b; cbn; rewrite compare_refl.
 now rewrite Nat.compare_refl.
Qed. 

Global Hint Resolve zero_lt head_lt coeff_lt tail_lt  : T1.

Open Scope t1_scope.



Lemma zero_nf : nf zero. 
Proof. reflexivity. Qed.


Lemma single_nf :  forall a n, nf a ->  nf (ocons a n zero).
Proof.   unfold nf; now cbn. Qed. 

Lemma ocons_nf : forall a n a' n' b, lt a'  a -> 
                           nf a -> 
                           nf(ocons a' n' b)-> 
                           nf(ocons a n (ocons a' n' b)).
Proof. 
unfold nf; cbn; intros a n a' n' b H H0 H1;  rewrite H0.
destruct b. 
- red in H; rewrite H1, H; reflexivity.
- simpl; simpl in H1;
  destruct (nf_b a'), (lt_b b1 a'), (nf_b b1), (nf_b b2), b2; simpl in *; auto.
  all : destruct (lt_b b2_1 b1); simpl in *;auto.
Qed. 

Global Hint Resolve zero_nf single_nf ocons_nf: T1.


Lemma nf_inv1 : forall a n b, nf (ocons a n b) -> nf a.
Proof.
  unfold nf;destruct b; cbn.
  - auto.
  - destruct (nf_b a); auto.
Qed.

Lemma nf_inv2 : forall a n b, nf (ocons a n b) -> nf b.
Proof.
  unfold nf; cbn; destruct a, b;  auto with T1.
  destruct (nf_b (ocons b1 n0 b2)); auto. 
  destruct (nf_b (ocons b1 n1 b2)); auto.
  destruct (nf_b (ocons a1 n a2)); auto.
Qed.


Lemma nf_inv3 : forall a n  a' n' b', nf (ocons a n (ocons a' n' b')) ->
                                    lt a' a.
Proof.
  unfold nf; cbn;
  destruct a, a', b';  try discriminate; auto with T1.
  -   intro H; red in H;repeat rewrite andb_true_iff in H.
       simpl in H.
      decompose [and] H.  discriminate.  
  -   intro H;  red in H;  repeat rewrite andb_true_iff in H;
        decompose [and] H;discriminate.  
  -   intro H;   red in H; repeat rewrite andb_true_iff in H;
        decompose [and] H;discriminate.  
  -   unfold lt;auto.
      intro H;  red in H;  repeat rewrite andb_true_iff in H.
      decompose [and] H; auto. 
  - intros H; red in H; repeat rewrite andb_true_iff in H;  decompose [and] H; auto. 
Qed.

Ltac nf_decomp H :=
  let nf0 := fresh "nf"
  in let nf1 := fresh "nf"
     in let Hlp := fresh "lt"
     in 
     match type of H with
     | nf (ocons ?t ?n zero) => assert (nf0:= nf_inv1 H)
     | nf (ocons ?t1 ?n (ocons ?t2 ?p ?t3))
       => assert (nf0 := nf_inv1 H); assert(nf1 := nf_inv2 H);
          assert (lt := nf_inv3 H)
     | nf (ocons ?t1 ?n ?t2) => assert (nf0 := nf_inv1 H); assert(nf1 := nf_inv2 H)
     end.
   
(**  lt alpha (phi0 beta)  *)
(** Should be deprecated *)


Inductive nf_helper : T1 -> T1 -> Prop :=
| nf_helper_z : forall alpha, nf_helper zero alpha
| nf_helper_c : forall alpha alpha' n' beta',
                lt alpha' alpha -> 
                nf_helper (ocons alpha' n' beta') alpha.




Global Hint Constructors nf_helper : T1.





(* A tactic for decomposing a non zero ordinal *)
(* use : H : lt zero ?c ; a n b : names to give to the constituents of 
   c *)

Definition get_decomposition : forall c:T1, lt zero c ->
                           {a:T1 & {n:nat & {b:T1 | c = ocons a n b}}}.
Proof.
 intro c; case c.
 - intro H; elimtype False; inversion H. 
 -  intros c0 n c1; exists c0;exists n;exists c1;auto.
Defined.

Ltac decomp_exhib H a n b e:= 
 let Ha := fresh in
 let Hn := fresh in
 let Hb := fresh in
  match type of H
  with lt zero ?c =>
    case (get_decomposition  H);
     intros a Ha;
     case Ha;intros n Hn; case Hn; intros b e;
     clear Ha Hn 
  end.


Lemma nf_FS : forall n:nat, nf (FS n). 
Proof. auto with T1. Qed.

Lemma nf_fin : forall n:nat, nf (fin n). 
Proof. destruct n; auto with T1.  Qed.

(** ** Successors, limits and zero *)

Lemma succ_not_zero : forall alpha, succ alpha <> zero.
Proof.
  destruct  alpha.
  -  discriminate.
  - cbn; destruct alpha1; discriminate.
Qed.


Lemma succ_succb : forall alpha, succb (succ alpha).
Proof.
  induction  alpha.
   -reflexivity. 
   - simpl.
     destruct alpha1.
     + reflexivity.
     + simpl. trivial.
Qed.

(**  **  Properties of [compare] *)


Lemma compare_rev : forall alpha beta, compare beta alpha =
                                       CompOpp (compare alpha beta).
Proof.
  induction alpha, beta.
  1-3: easy.
  simpl.
  rewrite IHalpha1, Nat.compare_antisym.
  destruct (compare alpha1 beta1).
  2-3: easy.
  now destruct (n ?= n0) eqn:?; simpl.
Qed.

(* TODO : use new tactics on [compare] by Jeremy/Zimmi *)

Lemma compare_reflect : forall alpha beta,
    match compare alpha beta with
    | Lt => lt alpha beta
    | Eq => alpha = beta
    | Gt => lt beta alpha
    end.
Proof.
  unfold lt, lt_b; induction alpha, beta.
  1-3: easy.
  simpl.
  specialize (IHalpha1 beta1).
  specialize (IHalpha2 beta2).
  rewrite compare_rev with alpha1 beta1, compare_rev with alpha2 beta2, Nat.compare_antisym in *.
  destruct (compare alpha1 beta1), (compare alpha2 beta2), (n0 ?= n) eqn:Heq; simpl in *; subst.
  2-27: easy.
  now apply Nat.compare_eq_iff in Heq as ->.
Qed.

Lemma compare_correct  (alpha beta : T1) :
  CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
              (compare alpha beta).
Proof.
  generalize (compare_reflect alpha beta).
  destruct (compare alpha beta); now constructor.
Qed.

(** ** Properties of [compare]: first part *)

Lemma eq_b_iff (alpha beta : T1) :
  eq_b alpha beta = true <-> alpha = beta.
Proof.
  split.
  - unfold eq_b.
    specialize (compare_reflect alpha beta).
    case (compare alpha beta);auto; try discriminate.
  - intro;subst;unfold eq_b; now rewrite compare_refl.
Qed.

Lemma compare_Eq_impl : forall a b, compare a b = Eq -> a = b.
Proof.
  intros * H.
  pose proof (compare_reflect a b).
  now rewrite H in *; simpl.
Qed.

Lemma compare_eq_iff a b :  compare a b = Eq <-> a = b.
Proof.
  split; intro H; [ now apply compare_Eq_impl|subst; apply compare_refl].
Qed.

Lemma compare_Lt_impl a b :  compare a b = Lt -> lt a b.
Proof.
  intros * H.
  pose proof (compare_reflect a b).
  now rewrite H in *; simpl.
Qed.

(** ** On [lt] and [le] *)

Theorem not_lt_zero alpha : ~ lt alpha  zero.
Proof.  destruct alpha; compute; discriminate. Qed.

Global Hint Resolve not_lt_zero : T1.


 Inductive lt_cases (a  b : T1) (n :nat) (a' b':T1) (n':nat) : Type :=
    lt_left (H : lt a a')
  | lt_middle (H : a = a')(H1 : (n < n')%nat)
  | lt_right (H : a = a')(H1 : n = n')(H2 : lt b b').


 Lemma lt_inv_strong : forall a n b a' n' b', 
     lt (ocons a n b) (ocons a' n' b') ->
     lt_cases a b n a' b' n'. 
 Proof. unfold lt, lt_b.
        intros; simpl in H.
        destruct (compare a a') eqn:Ha.
        - apply compare_eq_iff in Ha as ->.
          destruct (n ?= n') eqn:?.
          + destruct (compare b b') eqn:?.
            1,3: easy.
            constructor 3.
            * easy.
            * now apply Nat.compare_eq_iff.
            * now apply compare_Lt_impl.
          + constructor 2.
            * easy.
            * now apply Nat.compare_lt_iff.
          + constructor 2.
            * easy.
            * now apply Nat.compare_lt_iff.
        - constructor 1.
          now apply compare_Lt_impl.
        - easy.
 Defined.

  Theorem lt_inv : forall a n b a' n' b', 
                      lt (ocons a n b) (ocons a' n' b') ->
                      lt a  a' \/
                      a = a' /\ (n < n')%nat \/
                      a = a' /\ n = n' /\ lt b  b'.
  Proof.
   intros; destruct (lt_inv_strong H).
   - now left. 
   - right; left;auto. 
   -  right; right; auto. 
 Qed.


Theorem lt_irrefl alpha: ~ lt alpha alpha.
Proof. 
 induction alpha.
 -  red;inversion_clear 1.
 -  intro H; case (lt_inv_strong  H); intuition. abstract lia.
Qed.



Global Hint Resolve lt_irrefl : T1.


Lemma lt_inv_nb : forall a n n' b b',
                       lt (ocons a n b) (ocons a n' b') ->
                       {(n<n')%nat} + { n=n' /\ lt b  b'}.
Proof.
 intros.
 destruct (lt_inv_strong H).
  destruct (lt_irrefl H0).
  destruct H0.
 intuition.
 intuition.
Qed.


Lemma lt_inv_b : forall a n b b',
       lt (ocons a n b) (ocons a n b') -> lt b  b'.
Proof.
 intros a n b b' H; destruct (lt_inv_strong H).
  destruct (lt_irrefl H0).
  destruct H.
 destruct H0.
  destruct (Nat.lt_irrefl n);tauto.
 tauto. 
Qed.

Theorem lt_trans (alpha beta gamma : T1) :
  lt alpha beta -> lt beta gamma -> lt alpha gamma.
  Proof.
  intro H; revert gamma; revert  H;  revert  alpha beta.
  induction  alpha.
  - destruct beta.
   + discriminate. 
   + destruct gamma.
    * discriminate. 
    * auto with T1.
  - destruct beta.
   + discriminate. 
   + destruct gamma.
    * discriminate. 
    * destruct (lt_inv_strong H).
      -- intro H2; destruct (lt_inv_strong H2).
         eauto with T1.
         subst; auto with T1.
         subst; auto with T1.
      -- subst; clear H; destruct H1.
         ++ intro H2; destruct (lt_inv_strong H2).
            ** auto with T1.
            ** subst; eauto with arith T1.
            ** subst; auto with arith T1. 
         ++ intro H2; destruct (lt_inv_strong H2).
            ** auto with T1. 
            ** subst; eauto with arith T1. 
            ** subst; eauto with arith T1.  
      -- subst; clear H; intro H3; destruct (lt_inv_strong H3).
         ++  auto with T1.
         ++  subst; auto with T1.
         ++  subst; eauto with T1.
Qed.

Theorem lt_not_gt alpha beta : lt alpha beta  -> ~ lt beta alpha.
Proof.
 intros  H H0;
  generalize (lt_trans  H H0);  intro H2; case (lt_irrefl H2).
Qed.

Lemma finite_lt : forall n p : nat, (n < p)%nat ->
                                    lt (FS n)   (FS p).
Proof.
 intros; auto with T1.   
Qed.

Lemma finite_ltR :
  forall n p : nat, lt (FS n) (FS p) -> (n < p)%nat.
Proof.
  intros; simpl in H. unfold lt, lt_b in H.
  destruct (compare _ _) eqn:?.
  1,3: easy.
  simpl in *.
  destruct (n ?= p) eqn:?.
  1,3: easy.
  now apply Nat.compare_lt_iff.
Qed.

Lemma le_refl (alpha : T1) : le alpha alpha.
Proof. 
 unfold le; now rewrite compare_refl.
Qed.

Lemma lt_le_incl : forall alpha beta, lt alpha beta -> le alpha beta.
Proof.
 unfold le, lt, lt_b; intros.
  destruct (compare alpha beta); auto; try discriminate.
Qed. 

Lemma le_eq_lt_dec alpha beta:  le alpha beta ->
                                {alpha = beta} + {lt alpha beta}.
Proof.
  unfold le, lt, lt_b; intro H; case_eq (compare alpha beta).
  - left; generalize (compare_reflect alpha beta); now rewrite H0.
  - right; auto. 
  -  intro H0; rewrite H0 in H; contradiction. 
Defined.

Lemma lt_succ (alpha : T1) : lt alpha (succ alpha).
Proof.
  induction alpha; cbn; auto with T1.
  - destruct alpha1; cbn ; auto with T1.   
Qed.

Definition max (alpha beta : T1) : T1 := match compare alpha beta
                             with Lt => beta | _ => alpha end.


Lemma le_lt_or_eq (alpha beta: T1): le alpha beta ->
                                    alpha = beta \/ lt alpha beta.
Proof.
 intros  H; destruct (le_eq_lt_dec _ _ H);auto. 
Qed.



Lemma lt_a_phi0_a : forall a, lt a  (phi0 a).
Proof.
 induction a;simpl.
 - (* unfold phi0; *) auto with T1. 
 -  (* unfold phi0 in *. *)
    assert (H : le (ocons a1 0 zero) (ocons a1 n a2)).
    {  case n.
      -  case a2.
        +  apply le_refl. 
        +  intros; apply lt_le_incl. auto with T1 arith. 
      -  intros; apply lt_le_incl; auto with T1 arith. 
     }
  apply head_lt; destruct (le_lt_or_eq _ _ H).
  + injection H0; intros;  now subst. 
  + eapply lt_trans; eauto.  
Qed.


Lemma phi0_lt : forall a b, lt a  b -> lt (phi0 a) (phi0 b).
Proof.
 intros c c' H; auto with T1.  
Qed.


Lemma phi0_ltR : forall a b, lt (phi0 a) (phi0 b) -> lt  a  b.
Proof.
 intros c c' H; case (lt_inv H).
  -  trivial.
  -  intros [(_,i)|(_,(_,i))]; inversion i.
Qed.


Lemma nf_of_finite : forall  n b, nf (ocons zero n b) -> 
                                  b = zero.
Proof.
  intros n b H; destruct b.
  - reflexivity.
  - apply nf_inv3 in H; case (not_lt_zero H);auto. 
Qed.

Theorem zero_le : forall a, le zero a.
Proof.
 unfold le; destruct  a; reflexivity. 
Qed.

Theorem le_trans : forall a b c, le a  b -> le b  c -> le a  c.
Proof.
 intros a b c H H0; destruct (le_lt_or_eq _ _ H).
 - now subst.  
 - destruct (le_lt_or_eq _ _ H0).
  + now subst. 
  + apply lt_le_incl; eapply lt_trans; eauto.
Qed.

Theorem le_lt_trans : forall a b c, le a  b -> lt b  c -> lt a  c.
Proof.
   intros a b c H H0; destruct (le_lt_or_eq _ _ H).
 -  subst b;auto.
 -  intros;eapply lt_trans;eauto.
Qed.

Theorem lt_le_trans : forall a b c, lt a  b -> le b  c -> lt a  c.
Proof.
  intros a b c H H0; destruct (le_lt_or_eq _ _ H0).
 -  subst b;auto.
 -  eapply lt_trans;eauto.
Qed.

Theorem le_inv : forall a n b a' n' b', 
                      le (ocons a n b)  (ocons a' n' b') ->
                      lt a  a' \/
                      a = a' /\ (n < n')%nat \/
                      a = a' /\ n = n' /\ le b  b'.
Proof.
 intros a n b a' n' b' H; destruct (le_lt_or_eq _ _  H) as [H0 | H0].
 -  injection H0; intros; subst; right; right;repeat split;auto. 
    apply le_refl. 
 -  destruct  (lt_inv H0) as [H1 | [H1 | H1]].
    + now left. 
    + right; auto. 
    + right;  decompose [and] H1; right; repeat split; auto.
      apply lt_le_incl; auto. 
Qed.

Arguments le_inv [a n b a' n' b'] _.

Lemma nf_helper_inv :
  forall a n b a', lt (ocons a n b) (phi0 a') -> lt a a'.
Proof. 
  intros a n b a' H; destruct (lt_inv H); auto. 
  destruct H0 as [H0 | H0]; decompose [and] H0.
  - abstract lia. 
  - exfalso; eapply not_lt_zero; eassumption.  
Qed.

Lemma lt_not_le: forall a b,  lt a b -> ~ le b  a.
Proof.
 intros a b H H0; destruct (le_lt_or_eq _ _ H0).
 - subst; destruct (lt_irrefl H).
 - absurd (lt a a); eauto with T1.
    eapply lt_trans;eauto.
Qed.

Global Hint Resolve lt_le_incl le_refl : T1.


Lemma lt_inv_le : forall a n b a' n' b', 
                     lt (ocons a n b)  (ocons a' n' b') -> 
                     le a  a'.
Proof.
 intros a n b a' n' b' H; case (lt_inv H).
 -  auto with T1.
 -  intros [(e,i)|(e,(e',i))].
    + subst a; auto with T1.
    +  subst a; auto with T1.
Qed.


Theorem le_zero_inv : forall a, le a  zero -> a = zero.
Proof.
  intros a H; destruct (le_lt_or_eq _ _ H); auto.
  destruct (not_lt_zero H0).
Qed.

Theorem le_tail : forall a n b b',
    le b  b' -> 
    le (ocons a n b) (ocons a n b').
Proof.
 intros; destruct (le_lt_or_eq _ _ H).
 -  subst b; auto with T1.
 -  auto with T1.
Qed.

Global Hint Resolve zero_le le_tail : T1.

Theorem le_phi0 : forall a n  b , 
                    le (phi0 a) (ocons a n b).
Proof.
 induction  n.
 -   intro; apply le_tail; auto with T1.
 -   intros b; apply lt_le_incl;  apply le_lt_trans with (ocons a n b).
     + auto.
     + auto with T1 arith.   
Qed.

Lemma head_lt_ocons : forall a n b, lt a  (ocons a n b).
Proof.
 induction a; auto with T1. 
Qed.


Definition T1_eq_dec  (alpha beta : T1):
{alpha = beta} + {alpha <> beta}.
Proof.
  decide equality; apply eq_nat_dec.
Defined.  

Definition lt_eq_lt_dec : forall alpha beta : T1,
    {lt alpha  beta} + {alpha = beta} + {lt beta  alpha}.
Proof.
 induction alpha; destruct beta; auto with T1.
 case (IHalpha1 beta1);intros s.
 -  case s;intros; auto with T1.
     subst beta1. case (Compare_dec.lt_eq_lt_dec n n0).
  +  destruct 1.
     * auto with T1.
     * subst n;  case (IHalpha2 beta2); auto with T1.
       destruct 1;[idtac| subst beta2];auto with T1.
  +  right;auto with T1.
 -  auto with T1.
Defined.

Definition lt_le_dec (alpha beta : T1) :
  {lt alpha beta} + {le beta  alpha}.
Proof.
  case (lt_eq_lt_dec alpha beta).
  - destruct 1.
    + left;auto.
    + subst;   right; auto with T1.
  - right; auto with T1.
Defined.

Lemma le_lt_eq (alpha beta : T1) :
  le alpha  beta -> {lt alpha  beta} + {alpha = beta}.
Proof.
  intros H; destruct (lt_le_dec alpha beta);auto.
  right;
    destruct (le_lt_or_eq _ _ H),(le_lt_or_eq _ _ l); auto. 
   destruct (@lt_irrefl alpha); now apply lt_trans with beta. 
Qed. 


Instance epsilon0_pre_order : TotalDecPreOrder le.
Proof.
  split.
  - split.
    + intro x; apply le_refl.
    +  red;apply le_trans.
  -  split.
     + intros a b; destruct (lt_le_dec a b).
       *  left; auto with T1.
       *  destruct (lt_le_dec a b).
          -- left;auto with T1.
          -- now right.
     + intros a b; destruct (lt_eq_lt_dec a b) as [[H1 | H2] | H3].
       * left;auto with T1.
       * subst a ; left; auto with T1.
       * right;intro H4; now destruct (lt_not_le H3).
Defined.


Ltac auto_nf :=
  match goal with
    |- nf ?alpha =>
    ( repeat (apply ocons_nf || apply single_nf || apply zero_nf))
    || (eapply nf_inv1 || eapply nf_inv2); eauto
  end.

Lemma nf_tail_lt_nf b b':
  lt b' b -> nf b' ->
  forall a n,   nf (ocons a n b) -> nf (ocons a n b').
Proof.
 intros H H0 a n H1; destruct b. 
 -  destruct (not_lt_zero  H).
 -  destruct b'. 
  + do 2 auto_nf. 
  +  destruct (lt_inv H).
     *  apply ocons_nf; trivial.
        -- apply lt_trans with b1;  auto.
           eapply nf_inv3; eauto.
        -- eapply nf_inv1; eauto. 
     *  destruct H2 as [H2 | H2].
        -- decompose [and] H2;subst. 
           apply ocons_nf; auto.
           eapply nf_inv3; eauto.
           eapply nf_inv1; eauto.
        -- decompose [and] H2;subst. 
           clear H2; apply ocons_nf; auto.
           ++ eapply nf_inv3; eauto.
           ++ eapply nf_inv1; eauto.
Qed.


Lemma tail_lt_ocons : forall b n a, 
     nf (ocons a n b)-> 
     lt b (ocons a n b).
Proof.
 induction b.
 -  eauto with T1. 
 - intros n0 a H; apply head_lt; eapply nf_inv3; eauto.  
Qed.

Lemma nf_helper_inv1 : forall a n b a', nf_helper (ocons a n b) a' -> lt a  a'.
Proof. now inversion 1. Qed.

Lemma nf_intro : forall a n b, nf a -> 
                               nf b ->
                               nf_helper b a -> 
                               nf (ocons a n b).
Proof.  destruct 3;  eauto with T1. Qed. 

Lemma nf_intro' : forall a n b, nf a -> 
                               nf b ->
                               lt b  (ocons a 0 zero) -> 
                               nf (ocons a n b).
Proof.
  destruct b.
  - eauto with T1.
  - intros H H0 H1; apply ocons_nf; auto.
    now apply nf_helper_inv in H1.
Qed.


Lemma nf_helper_intro : forall a n b, nf (ocons a n b) -> 
                                    nf_helper b a.
Proof.
  intros a n b H; unfold nf in H; cbn in H.
  destruct b.
  -  constructor. 
  -  constructor; auto.
     red in H; decompose [and] H; repeat rewrite andb_true_iff in H;
       tauto. 
Qed.

Lemma nf_coeff_irrelevance : forall a b n p, nf (ocons a n b) ->
                                             nf (ocons a p b).
Proof.
 intros; apply nf_intro.
 -  eapply nf_inv1;eauto.
 -  eapply nf_inv2;eauto.
 -  eapply nf_helper_intro;eauto.
Qed.

Lemma nf_helper_phi0 : forall a b, nf_helper b a ->
                                 lt b ( phi0 a).
Proof.
  induction 1; auto with T1. 
Qed.

Lemma nf_helper_phi0R : forall a b, lt b  (phi0 a) -> nf_helper b a.
Proof.
  induction b.
  - constructor.
  - intro H; apply nf_helper_inv in H; constructor;auto. 
Qed.

Lemma nf_helper_iff :
  forall a b, nf a -> nf b ->
              (nf_helper b a <-> forall n, nf(ocons a n b)).
Proof.
  split.
  - intros; now apply nf_intro.
  - intro; now apply nf_helper_intro with 0.
Qed.

Lemma nf_tower : forall n, nf (tower n).
Proof.  induction n; simpl; (* unfold phi0;*)  auto with T1.
Qed.

(** A strong induction scheme for nf *)

Definition nf_rect : forall P : T1 -> Type,
    P zero ->
    (forall n: nat,  P (ocons zero n zero)) ->
    (forall a n b n' b', nf (ocons a n b) -> 
                         P (ocons a n b)-> 
                         nf_helper b' (ocons a n b) -> 
                         nf b' -> 
                         P b' ->
                         P (ocons (ocons a n b) n' b')) ->
    forall a: T1, nf a -> P a.
Proof.
  intros P H0 Hfinite Hcons; induction a.
  -  trivial.
  -  generalize IHa1;case a1.
     +  intros IHc0 H; rewrite (nf_of_finite H);  apply Hfinite.
     +  intros c n0 c0 IHc0 H2; apply Hcons.
        *  eapply nf_inv1;eauto.
        *  apply IHc0; eapply nf_inv1; eauto.
        *  eapply nf_helper_intro;  eauto.
        *  eapply nf_inv2;eauto.
        * apply IHa2; eapply nf_inv2;eauto.
Defined.

(** ** Properties of [compare]: second part *)

Lemma compare_Lt_eq : forall a b, lt a  b -> compare a b = Lt.
Proof.
  intros c1 c2; generalize (compare_reflect c1 c2).  
  case (compare c1 c2);auto.
  - intros e H;subst c2;case (lt_irrefl H).
  - intros H1 H2;case (lt_not_gt H2);auto.
Qed.

Lemma compare_Gt_eq : forall a b:T1 , lt b  a  -> compare a b = Gt.
Proof.
  intros a b; generalize (compare_reflect a b);  
    case (compare a b);auto.
  - intros e H;subst b;case (lt_irrefl H).
  -  intros H1 H2;case (lt_not_gt H2);auto.
Qed.

Theorem compare_reflectR ( alpha  beta : T1) :
  (match lt_eq_lt_dec alpha beta with
     inleft  (left _) => Lt
   | inleft  (right _) => Eq
   | inright _ => Gt
   end)
  = compare alpha  beta.
Proof.
  case (lt_eq_lt_dec alpha beta).
  -  destruct s.
     +  rewrite compare_Lt_eq;auto.
     +  subst alpha;rewrite compare_refl;auto.
  -  intro; rewrite compare_Gt_eq;auto.
Qed.

Lemma lt_iff : forall alpha beta,
    compare alpha beta = Lt <-> lt alpha  beta.
Proof.
  split.
  - apply compare_Lt_impl.
  - apply compare_Lt_eq.
Qed.

Lemma gt_iff : forall alpha beta,
    compare alpha beta = Gt <-> lt beta  alpha.
Proof.
  intros.
  rewrite compare_rev, <- lt_iff.
  now destruct (compare _ _).
Qed.

(** ** Properties of [max] *)

Lemma max_le_1 (alpha beta : T1) : le alpha  (max alpha beta).
Proof.
  unfold max; case (lt_eq_lt_dec alpha beta).
  -  destruct 1.
     +  rewrite compare_Lt_eq;auto with T1.
     +  subst beta;rewrite compare_refl;  auto with T1. 
  - intro;rewrite compare_Gt_eq;  auto with T1. 
Qed.

Lemma max_comm alpha beta :  max alpha beta = max beta alpha.
Proof.
  unfold max; case (lt_eq_lt_dec alpha beta).
  -  destruct 1.
     +  rewrite compare_Lt_eq;auto.
        rewrite compare_Gt_eq;auto.
     +  subst beta;auto.
  -  intro; rewrite compare_Gt_eq ;auto; rewrite compare_Lt_eq;auto.
Qed.

Lemma max_dec alpha beta :
  {max alpha beta = alpha} + {max alpha beta = beta}.
Proof.
  unfold max;  case (lt_eq_lt_dec alpha beta);auto.
  -  destruct 1.
     +  repeat rewrite compare_Lt_eq;auto.
     +  subst beta;repeat rewrite compare_refl;auto.
  - intro; repeat rewrite compare_Gt_eq;auto.
Qed.

Lemma max_nf (alpha beta : T1) :
  nf alpha -> nf beta -> nf (max alpha beta).
Proof.
  case (max_dec alpha beta); intro H;rewrite H;auto.
Qed.


Lemma max_assoc : forall alpha beta gamma,
    max (max alpha beta) gamma =
    max alpha (max beta gamma).
Proof.
  intros a b c; unfold max;  case (lt_eq_lt_dec a b).
  -  destruct 1.
     +  repeat (rewrite (compare_Lt_eq l)).
        case (lt_eq_lt_dec b c).
        * destruct 1.
          { repeat (rewrite (compare_Lt_eq l0)).
            assert (H : lt a  c) by ( eapply lt_trans;eauto).
            rewrite (compare_Lt_eq H);auto.
          }  
          subst c; repeat rewrite compare_refl.
          rewrite compare_Lt_eq;auto.
        *  intro H; repeat (rewrite (compare_Gt_eq H)).
           rewrite compare_Lt_eq;auto.
     +  subst b; repeat (rewrite (compare_refl));auto.
        case (lt_eq_lt_dec a c).
        *  destruct 1.
           {  repeat (rewrite (compare_Lt_eq l));auto. }
           subst c;repeat rewrite compare_refl;auto.
        *  intro H;repeat (rewrite (compare_Gt_eq H));auto.
           repeat rewrite compare_refl;auto.
  -  intro H; repeat rewrite (compare_Gt_eq H);auto.
     case (lt_eq_lt_dec a c).
     +  destruct 1.
        * rewrite (compare_Lt_eq l);auto.
          assert (H0: lt b  c) by (eapply lt_trans;eauto).
          repeat rewrite (compare_Lt_eq H);auto.
          rewrite (compare_Lt_eq H0);auto.
          rewrite (compare_Lt_eq  l);auto.
        *  subst c; repeat rewrite (compare_Lt_eq c);auto.
           rewrite compare_refl;auto.
           repeat rewrite (compare_Lt_eq H);auto.
           now rewrite (compare_refl).
     +    intro H0;   rewrite (compare_Gt_eq H0).
          case (lt_eq_lt_dec b c).
          * destruct 1.
            repeat rewrite (compare_Lt_eq l);auto.
            repeat rewrite (compare_Gt_eq H0);auto.
            subst c;repeat rewrite (compare_refl);auto.
            repeat rewrite (compare_Gt_eq H);auto.
          *  intro H1;repeat rewrite (compare_Gt_eq H1);auto.
             repeat rewrite (compare_Gt_eq H);auto.
Qed.

(** **  Restriction of lt and le to terms in normal form *)
Reserved Notation "x 't1<' y" (at level 70, no associativity).
Reserved Notation "x 't1<=' y" (at level 70, no associativity).
Reserved Notation "x 't1>=' y" (at level 70, no associativity).
Reserved Notation "x 't1>' y" (at level 70, no associativity).


Reserved Notation "x 't1<=' y 't1<=' z" (at level 70, y at next level).
Reserved Notation "x 't1<=' y 't1<' z" (at level 70, y at next level).
Reserved Notation "x 't1<' y 't1<' z" (at level 70, y at next level).
Reserved Notation "x 't1<' y 't1<=' z" (at level 70, y at next level).

Definition LT := restrict nf lt.
Infix "t1<" := LT : t1_scope.
Definition LE := restrict nf le.
Infix "t1<=" := LE : t1_scope.

Notation "alpha t1< beta t1< gamma" :=
  (LT alpha beta /\ LT beta gamma) : t1_scope.

Definition Elements alpha : Ensemble T1 :=
  fun beta => beta t1< alpha.

Coercion Elements : T1 >-> Ensemble.

Lemma LT_nf_l : forall alpha beta , alpha t1< beta -> nf alpha.
Proof. now  destruct 1. Qed.

Lemma LT_nf_r : forall alpha beta , alpha t1< beta -> nf beta.
Proof. now  destruct 1.  Qed.

Lemma LT_lt alpha beta : alpha t1< beta -> lt alpha beta.
Proof. now destruct 1. Qed.

Lemma LE_nf_l : forall alpha beta , alpha t1<= beta -> nf alpha.
Proof. now  destruct 1. Qed.

Lemma LE_nf_r : forall alpha beta , alpha t1<= beta -> nf beta.
Proof. now  destruct 1. Qed.

Lemma LE_le alpha beta : alpha t1<= beta -> le alpha beta.
Proof. now destruct 1. Qed.

Global Hint Resolve LT_nf_r LT_nf_l LT_lt LE_nf_r LE_nf_l LE_le : T1.

Lemma not_zero_lt : forall alpha, nf alpha -> alpha <> zero -> zero t1< alpha.
Proof.
  split.
  - constructor. 
   - split;auto. 
     destruct alpha.
     + destruct H0;auto.
     + constructor. 
Qed.

Lemma LE_zero : forall alpha, nf alpha -> zero t1<= alpha.
Proof. split; auto with  T1. Qed. 


Lemma LE_refl : forall alpha, nf alpha -> alpha t1<= alpha. 
Proof. split; auto with  T1. Qed. 


Lemma LT_trans : forall a b c:T1, a t1< b -> b t1< c -> a t1< c.
Proof.
  unfold LT, restrict; intros a b c H H0; decompose [and] H  ;
    decompose [and] H0; repeat split; auto.
  now apply lt_trans with b.
Qed.


Theorem LE_trans (alpha beta gamma: T1):
          alpha t1<=  beta -> beta t1<=  gamma ->  alpha t1<= gamma.
Proof.
  unfold LE, restrict; intros  H H0; decompose [and] H  ;
    decompose [and] H0; repeat split; auto.
  now apply le_trans with beta.     
Qed. 

Lemma LE_antisym (alpha beta : T1):  alpha t1<= beta ->
                                     beta t1<= alpha ->
                                     alpha = beta.
Proof.
  unfold LE; intros [H [H0 H1]] [H2 [H3 H4]].
  unfold le in *; generalize (compare_reflectR alpha beta).
  destruct  (lt_eq_lt_dec alpha beta).
  -  destruct s; trivial.
     + rewrite compare_rev in H3;  intro e; rewrite <- e in *; contradiction.
  - rewrite compare_rev in H3;  intro e; rewrite <- e in *; contradiction.  
Qed. 


Lemma LT1 : forall alpha n beta, nf (ocons alpha n beta) ->
                                 zero t1< ocons alpha n beta.
Proof. repeat split;auto; constructor. Qed.

Lemma LT2 : forall alpha alpha' n n' beta beta',
    nf (ocons alpha n beta) ->
    nf (ocons alpha' n' beta') ->
    alpha t1< alpha' ->
    ocons alpha n beta t1< ocons alpha' n' beta'.
Proof. repeat split; auto; apply head_lt; auto. destruct H1; tauto. Qed.


Lemma LT3 : forall alpha  n n' beta beta',
    nf (ocons alpha n beta) ->
    nf (ocons alpha n' beta') ->
    n < n'  ->
    ocons alpha n beta t1< ocons alpha n' beta'.
Proof. repeat split; auto. apply coeff_lt. auto.   Qed.

Lemma LT4 : forall alpha  n  beta beta',
    nf (ocons alpha n beta) ->
    nf (ocons alpha n beta') ->
    beta t1< beta'  ->
    ocons alpha n beta t1< ocons alpha n beta'.
Proof.   repeat split; auto; apply tail_lt.  destruct H1; tauto. Qed.

Global Hint Resolve LT1 LT2 LT3 LT4: T1.


Lemma LT_irrefl (alpha : T1) : ~ alpha t1< alpha.
Proof. 
  destruct 1 as [H [H0 H1]]; destruct (lt_irrefl H0).
Qed.

Lemma LE_LT_trans : forall alpha beta gamma, alpha t1<= beta -> beta t1< gamma ->
                                             alpha t1< gamma.
Proof.
  intros alpha beta gamma [H1 [H2 H3]] [H4 [H5 H6]]; repeat split; auto. 
  apply le_lt_trans with beta;auto.
Qed.

Lemma LT_LE_trans (alpha beta gamma : T1) : alpha t1< beta ->
                                            beta t1<= gamma  ->
                                            alpha  t1< gamma.
Proof.
  intros [H [H0 H1]] [H' [H'0 H'1]]; repeat split; auto with T1.
  apply lt_le_trans with beta;auto.
Qed.


Lemma not_LT_zero : forall alpha, ~ alpha t1< zero.
Proof. intros alpha [H [H0 H1]]; inversion H0.
       destruct (not_lt_zero H0).
Qed. 

Instance LT_St : StrictOrder LT.
Proof.
  split.
  - intros alpha H; apply (LT_irrefl H).
  - intros x y z H H0; eapply LT_trans; eauto.
Qed.


Lemma nf_ocons_LT : forall (a : T1) (n : nat) (a' : T1) (n' : nat) (b : T1),
    a' t1< a ->
    nf a -> nf (ocons a' n' b) -> nf (ocons a n (ocons a' n' b)).
Proof.
  intros; apply ocons_nf; auto; destruct H;tauto.
Qed.

Global Hint Resolve nf_ocons_LT: T1.

Global Hint Resolve nf_inv1 nf_inv2 nf_inv3 : T1.

Lemma head_LT_cons : forall alpha n beta, nf (ocons alpha n beta) ->
                                          alpha t1< ocons alpha n beta.
Proof.
  split; eauto with T1.
  split.
  -  apply head_lt_ocons.
  -  auto.
Qed. 

Lemma tail_LT_cons : forall alpha n beta, nf (ocons alpha n beta) ->
                                          beta t1< ocons alpha n beta.
Proof. 
  split;  eauto with T1.
  split; auto. 
  apply tail_lt_ocons; auto.
Qed.



Lemma  LT_inv : forall a n b a' n' b', 
    ocons a n b t1<  ocons a' n' b' ->
    a t1< a' \/
    a = a' /\ (n < n'  \/ n = n' /\   b t1< b').
Proof.
  intros a n b a' n' b' H; case H.
  -   clear H;intros H (H0,H1);  case (lt_inv H0).
      +   left; split.
          *  eapply nf_inv1;eauto.
          *  split;auto;eapply nf_inv1;eauto.
      + intros [(e,i)|(e,(e',i))]. 
        *   auto. 
        *   right;split;auto.
            right;split;auto.
            split.
            eapply nf_inv2;eauto. 
            split;[auto|eapply nf_inv2;eauto].
Qed.

Inductive LT_cases (a  b : T1) (n :nat) (a' b':T1) (n':nat) : Type :=
  LT_left (H : a t1< a')
| LT_middle (H : a = a')(H1 : n < n')
| LT_right (H : a = a')(H1 : n = n')(H2 : b t1< b').


Lemma  LT_inv_strong : forall a  b n a'  b' n', 
    ocons a n b t1<  ocons a' n' b' -> LT_cases a b n a'  b' n'. 
Proof.
  intros a  b n a' b' n' H. case H.
  -   clear H;intros H (H0,H1);  case (lt_inv_strong H0).
      +   constructor 1. split.
          *  eapply nf_inv1;eauto.
          *  split;auto;eapply nf_inv1;eauto.
      + intros; subst.  constructor 2; auto. 
      + constructor 3 ; auto. split; eauto with T1. 
Defined.

Lemma remove_first_sumand : 
  forall a n b  b', 
    ocons a n b t1<  ocons a n b' -> b t1< b'.
Proof.
  intros a n b b' H; apply LT_inv in H.
  destruct H.
  - destruct H as [_ [H _] ].
    destruct (lt_irrefl H).    
  - destruct H as [_ [H | [ _ H]]]; auto.
    destruct (Nat.lt_irrefl _ H).   
Qed.


Lemma LT_ocons_0 : forall a n b a' b', ocons a n b t1<  ocons a' 0 b' ->
                                       a t1< a' \/ n = 0 /\ a = a' /\  b t1< b'.
Proof.
  intros a n b x c H; case (LT_inv H).
  - now left.
  -  intros [e H0];subst x; case H0;intro H1. 
     +   abstract lia. 
     +   case H1;right;auto.
Qed.



Lemma  LE_phi0 : forall a n b,  nf (ocons a n b) ->
                                phi0 a t1<= ocons a n b.
Proof.
  intros a n b; repeat split; eauto with T1.
  apply le_phi0.
Qed.



(** ** Well foundedness of [LT] *)



Module Direct_proof.
  Section well_foundedness_proof.
    
    Local Hint Unfold restrict LT: T1.

    Lemma Acc_zero : Acc LT  zero.
    Proof.
      split; intros y (H1, (H2,H3)).  destruct (not_lt_zero H2).
    Qed.


    (* begin hide *)
    
    Section First_attempt.
      Lemma wf_LT : forall alpha: T1,  nf alpha -> Acc LT alpha. 
      Proof.
        induction alpha as [| beta IHbeta n gamma IHgamma].
        - split.
          inversion 1.
          destruct H2 as [H3 _]. destruct (not_lt_zero H3). 
        -  split; intros delta Hdelta. 
      Abort.    

    End First_attempt.

    (* end hide *)

    (** *** Strong accessibility (inspired by Tait's proof) *)
    
    Let Acc_strong (alpha:T1) :=
      forall n beta, 
        nf (ocons alpha n beta) -> Acc LT (ocons alpha  n beta).


    Remark acc_impl {A} {R: A -> A -> Prop} (a b:A) :
      R a b -> Acc R b -> Acc R a.
    Proof.
      intros H H0; revert a H; now destruct H0.
    Qed.
 
    Lemma Acc_strong_stronger : forall alpha, 
        nf alpha -> Acc_strong  alpha -> Acc LT  alpha.
    Proof.
      intros alpha H H0.  apply acc_impl with (phi0 alpha).
      - repeat split; trivial.
        + now apply lt_a_phi0_a.
      -  apply H0;  now apply single_nf.
    Qed.

 
    Lemma Acc_implies_Acc_strong : forall alpha, 
        Acc LT  alpha -> Acc_strong alpha.
    Proof.
    
      (*  main induction (on a's accessibility)   *)

      
      unfold Acc_strong; intros alpha Aalpha; pattern alpha.
      eapply Acc_ind with (R:= LT);[| assumption].
      clear alpha Aalpha; intros alpha Aalpha IHalpha. 

      (*  for any n and b, such that (ocons a n b) is well formed,
        b is accessible 
     *)  

      assert(beta_Acc: 
               forall beta, nf_helper beta alpha -> nf alpha -> nf beta 
                            -> Acc LT beta).
      
      (*  Proof of beta_Acc:
          Since beta is  less than omega ^ alpha, 
          beta  is of the form omega^alpha'*(p+1)+beta' where
          LT alpha' alpha, so the inductive hypothesis IHalpha can be used 
       *)
      {  intros b H H' H'';  assert (H0 : LT b (phi0 alpha)).
         { repeat split;auto; apply nf_helper_phi0; auto. }
         generalize H0; pattern b; case b.
         - intro;apply Acc_zero.
         -  intros t n t0 H1; case H1;  destruct 2;
              case (lt_inv H3).
            + intro H5;generalize H2;case n.
              { inversion 1.
                - intros; apply IHalpha.
                  + split.
                    * apply nf_inv1 in H2. auto. 
                    * split;auto.
                  + auto. 
              }
              intros;apply IHalpha.
              split;auto.
              eapply nf_inv1;eauto.
              auto.
            + destruct 1.
              case H5;intros H6 H7; abstract lia.  
              case H5;intros _ (_,H6);destruct (not_lt_zero H6).
      }
      
      (* end of proof of beta_Acc *)
      (* we can now use a nested induction on n (Peano induction)
          then on b (well_founded induction using b_Acc) *)
      induction n.
      -    (* n=0 : let's use b's accessibility for doing an induction on b *)
        intros b Hb; assert (H : Acc LT  b).
        {  apply beta_Acc.
           -  eapply nf_helper_intro; eauto.
           -  eapply nf_inv1;eauto.
           -  eapply nf_inv2;eauto.
        }
        
        (* let's prove that every predecessor of (ocons a 0 b) 
            is accessible *)
        { 
          pattern b;eapply Acc_ind;[|eexact H].
          intros; split; intro y; case y.
          - intro; apply Acc_zero.
          -   intros c n c0 H3; case (LT_ocons_0 H3).
              intro; unfold LT; case H3;auto.
              intros (e,(e',r)); subst n c; auto.
        }
        
      -  (*  induction step for (S n) *)
        { intros b H; generalize H; pattern b; eapply Acc_ind with (R:= LT).
          - split; intro y;pattern y; case y.
            intro;apply Acc_zero.
            intros c n0 c0 H3.
            case (LT_inv H3).
            + (* c < alpha *)
              intro; apply IHalpha;auto.
              case H3; auto. 
            + (* c = alpha and n0 < S n *)
              intros (e,[i|(e',r')]).
              assert (disj:n0 = n \/ (n0 < n)%nat).
              { inversion i;auto with arith. }
              case disj;intro H4.
              * subst n c; apply IHn.
                case H3;auto.
              * apply Acc_inv with (ocons alpha  n zero).
                apply IHn.
                apply single_nf;auto. 
                subst c; eapply nf_inv1;eauto.
                subst c; split. 
                case H3;auto. 
                split. 
                auto with T1.
                apply single_nf;auto.

                case H3;intros;eapply nf_inv1;eauto.
              (* c = a, n0 = S n and c0 < x *)
              *  subst n0 c;apply H1; auto.
                 case H3;auto.
          - apply beta_Acc. 
            + eapply nf_helper_intro;eauto.
            + eapply nf_inv1;eauto.
            + eapply nf_inv2;eauto.
        }
    Qed.

    (** ***  A (last) structural induction *)

    Theorem nf_Acc : forall alpha, nf alpha -> Acc LT  alpha.
    Proof.
      induction alpha.
      -  intro; apply Acc_zero.
      -  intros; eapply Acc_implies_Acc_strong;auto.
         apply IHalpha1;eauto.
         apply nf_inv1 in H; auto. 
    Qed. 


  End well_foundedness_proof.
End Direct_proof.

Definition nf_Acc := Direct_proof.nf_Acc.


Corollary nf_Wf : well_founded_restriction _ nf lt.
Proof.  red; intros; now apply nf_Acc. Qed.


Corollary T1_wf : well_founded LT.
Proof.
  intros alpha; case_eq(nf_b alpha).
  -  intro H; now generalize (nf_Wf H).
  -  intros H; split. 
     destruct 1 as [H1 [H2 H3]].
     red in H3; rewrite H in H3; discriminate.    
Qed. 

Definition transfinite_recursor_lt :
  forall (P:T1 -> Type),
    (forall x:T1, 
        (forall y:T1, nf x -> nf y ->  lt y  x -> P y) -> P x) ->
    forall alpha: T1, P alpha.
Proof.
  intros; apply well_founded_induction_type with LT.
  -  exact T1_wf;auto.
  - intros; apply X.
    intros; apply X0; repeat split;auto. 
Defined.

Definition transfinite_recursor := well_founded_induction_type T1_wf.

Import  Direct_proof.

Ltac transfinite_induction_lt alpha :=
  pattern alpha; apply transfinite_recursor_lt.

Ltac transfinite_induction alpha :=
  pattern alpha; apply transfinite_recursor.

(** **  Properties of successor *)

(* begin hide *)
Lemma succ_nf_helper : forall c a n b, nf_helper c (ocons a n b) -> 
                                       nf_helper (succ c) (ocons a n b).
Proof.
  induction c.
  -  simpl; repeat constructor.
  - simpl; case c1.
    +  repeat constructor.
    + intros t n0 t0 a n1 b H; inversion_clear H; constructor; auto.
Qed.
(* end hide *)

Lemma succ_nf : forall alpha : T1 , nf alpha -> nf (succ alpha).
Proof.
  induction alpha.
  -  simpl;repeat constructor; auto  with arith.
  -  simpl; generalize IHalpha1 ; case alpha1.
     +  simpl;repeat constructor; auto.
     + intros c n0 c0 H H0;  apply nf_intro.
       * eapply nf_inv1; eauto.
       *  apply IHalpha2; eapply nf_inv2 ; eauto.
       * apply succ_nf_helper; eapply nf_helper_intro; eauto.
Qed.

(** **  properties of addition *)

Lemma plus_zero alpha:  zero + alpha  = alpha.
Proof.  simpl;  case alpha; auto. Qed.

Lemma plus_zero_r alpha: alpha + zero = alpha.
Proof.
   case alpha;now simpl.
Qed.

Lemma succ_is_plus_one (alpha : T1) :  succ alpha = alpha + 1.
Proof.
  induction alpha as [ |a IHa n b IHb]; [trivial |].
  - destruct  a; cbn.
    +  now rewrite <- plus_n_O.
    +  rewrite IHb; f_equal. 
Qed.

Lemma succ_of_plus_finite :
  forall alpha (H: nf alpha) (i:nat) , succ (alpha + i) = alpha + S i.
Proof.
  induction  alpha; cbn.
  -  destruct i; reflexivity. 
  -  destruct i.
     +  simpl.
        destruct alpha1.
        * simpl; replace (n + 0)%nat with n.
          { auto. }
          { abstract lia. }
        * simpl; rewrite succ_is_plus_one; auto.
     + simpl; destruct alpha1.
       * simpl; replace (S (n + i)) with (n + S i)%nat; auto.
       *  simpl; assert (nf alpha2) by eauto with T1.
          generalize  (IHalpha2 H0 (S i)).
          replace (fin (S i)) with (FS i); auto.
          replace (fin (S (S  i))) with (FS (S i)).
          {intro H1; now rewrite H1. }
          reflexivity.
Qed.

(** **  [plus] and [LT] *)


Lemma plus_ocons_ocons_rw1 : forall a n b a' n' b', 
    lt a  a' ->
    ocons a n b + ocons a' n' b' = ocons a' n' b'.
Proof.
  simpl; destruct a.
  -  destruct a'. 
     +  inversion 1.
     +  intros; rewrite compare_Lt_eq; auto with T1.
  -  destruct a'; inversion 1.
     + now rewrite compare_Lt_eq.
Qed.


Lemma plus_ocons_ocons_rw2 : forall a n b n' b', 
    nf (ocons a n b) ->
    nf (ocons a n' b') ->
    ocons a n b + ocons a n' b' = 
    ocons a (S (n + n')) b'.  
Proof.
  cbn; destruct a.
  - intros n b n' b' H H0; now rewrite (nf_of_finite H0).
  - now  rewrite compare_refl.
Qed.

Lemma plus_ocons_ocons_rw3 : forall a n b a' n' b', 
    lt a' a ->
    nf (ocons a n b) ->
    nf (ocons a' n' b') ->
    ocons a n b + ocons a' n' b'= 
    ocons a n (b + (ocons a' n' b')).
Proof.
  simpl;intros a n b a' n' b' H H0 H1; rewrite compare_Gt_eq.
  - destruct a; intros; auto.
  -  assumption.
Qed.

(** ** On additive principal ordinals *)

Lemma ap_plus : forall a,
    ap a ->
    forall b c,
      nf b -> nf c -> lt b  a -> lt c  a -> lt (b + c)  a.
Proof.
  destruct 1. 
  intro b; elim b. 
  - intro c; elim c;intros.
    +  simpl; auto with T1. 
    +  simpl;auto.
  -  intros c H0 n t H c0 H1 H2 H3 H4;  generalize c0 H2 H4.
     destruct c1.
     + rewrite (plus_zero_r);auto.
     + intros H5 H6;  case (lt_eq_lt_dec c c1_1).
       *  destruct 1.
          { rewrite (plus_ocons_ocons_rw1 n t n0 c1_2 l); auto. }
          subst c1_1; rewrite (plus_ocons_ocons_rw2 H1 H5).
          apply nf_helper_inv  in H6.
          auto with T1.
       *  intro H7; rewrite plus_ocons_ocons_rw3;auto.
          apply nf_helper_inv  in H3; auto with T1. 
Qed.

Lemma ap_plusR : forall c, nf c -> c <> zero ->
                           (forall a b, nf a -> nf b ->  lt a  c ->
                                        lt b  c -> lt (a + b) c)  ->
                           ap c.
Proof.
  destruct c as [|c1 n c2].
  -  now destruct 2. 
  - case c2.
    + case n.
      *  constructor.
      *  intros n0 H H0 H1;
           generalize (H1 (ocons c1 0 zero) (ocons c1 n0 zero)).
         clear H1;intros H1.
         assert (H2 : nf (ocons c1 0 zero)) by 
             (eapply nf_coeff_irrelevance;eauto).
         assert (H3 : nf (ocons c1 n0 zero)) by 
             (eapply nf_coeff_irrelevance;eauto).
         assert  (H4 : lt (ocons c1 0 zero) (ocons c1 (S n0) zero)).
         {auto with T1 arith. } 
         assert (H5 : lt (ocons c1 n0 zero)  (ocons c1 (S n0) zero )) by
             (auto with T1 arith  ).
         generalize (H1 H2 H3 H4 H5); intro H6.
         rewrite plus_ocons_ocons_rw2 in H6; simpl in H6.
         case (lt_irrefl H6);auto.
         auto.
         auto.
    + intros t n0 t0 H H0 H1; assert (H2 : nf (ocons c1 n zero)).
      { apply  single_nf; eapply nf_inv1;eauto. } 
      assert (H3: nf (ocons t n0 t0)).
      {  eapply nf_inv2;eauto. }
      assert (H4 : lt (ocons c1 n zero) (ocons c1 n (ocons t n0 t0))).
      { apply tail_lt; auto with T1. }
      assert (H5 : lt (ocons t n0 t0) (ocons c1 n (ocons t n0 t0))).
      {  apply nf_inv3 in H.  auto with T1. }
      generalize (H1 _ _ H2 H3 H4 H5).
      clear H1 H4 H5;intro H1; rewrite plus_ocons_ocons_rw3 in H1; auto.
      *   simpl in H1; case (lt_irrefl H1); auto.
      *   apply nf_inv3 in H; auto. 
Qed. 

(** Technical lemma for proving [plus_nf] *)

Lemma plus_nf0 : forall a, nf a -> forall b c, lt b  (phi0 a) ->
                                               lt c  (phi0 a) ->
                                               nf b -> nf c ->
                                               nf (b + c).
Proof.
  intros a; pattern a; transfinite_induction_lt a.
  intros x Cx Hx.
  destruct b; destruct c.
  -  simpl;constructor.
  -  simpl;auto with T1.
  - intros;rewrite plus_zero_r; auto with T1.
  -  intros; case (lt_eq_lt_dec b1 c1).
     +  destruct 1.
        *  rewrite plus_ocons_ocons_rw1; auto with T1. 
        *  subst c1; rewrite plus_ocons_ocons_rw2; auto with T1.
     +  intro; rewrite plus_ocons_ocons_rw3;auto with T1.
        apply nf_intro.
        * eapply nf_inv1;eauto with T1.
        * nf_decomp H1; nf_decomp H2.
          eapply Cx with b1; trivial.
          apply nf_helper_inv in H;auto with T1.
          apply nf_helper_phi0. 
          eapply nf_helper_intro with n; trivial. 
          apply nf_helper_phi0. 
          eapply nf_helper_intro with n0; trivial. 
          apply ocons_nf; auto.
        *  nf_decomp H1; nf_decomp H2.
           apply nf_helper_phi0R; apply ap_plus; trivial.
           constructor.
           apply nf_helper_phi0.
           eapply nf_helper_intro; trivial. 
           auto with T1.
           Unshelve. 
           exact 0.
Defined.


Lemma plus_nf : forall a,  nf a -> forall b, nf b -> nf (a + b).
Proof.
  intros a Ha b Hb; case (lt_eq_lt_dec a b).
  - destruct 1.
    + (** a < b *)  apply plus_nf0 with b; auto.
      apply lt_trans with b; auto.
      apply lt_a_phi0_a.
      apply lt_a_phi0_a.
    + (** a = b *)  subst b;
        apply plus_nf0 with a; try assumption; 
          apply lt_a_phi0_a.
  - (** b < a *)
    intro; apply plus_nf0 with a; auto.
   + apply lt_a_phi0_a.
   + apply lt_trans with a;auto; apply lt_a_phi0_a.
Qed.


Lemma omega_term_plus_rw:
  forall a n b, 
    nf (ocons a n b) ->
    omega_term a n + b = ocons  a n b.
Proof.
  simpl; destruct a.
  -  intros n b H; rewrite (nf_of_finite H); auto.
  -  destruct b.
     + reflexivity.
     +  intro H.
        apply nf_inv3 in H. 
        red in H.
        unfold lt_b in H. 
        rewrite compare_rev . 
        destruct  (compare b1 (ocons a1 n a2)); try discriminate. 
        reflexivity. 
Qed.

Lemma plus_is_zero alpha beta :
  nf alpha -> nf beta ->
  alpha + beta  = zero -> alpha = zero /\  beta = zero.
Proof.
  destruct alpha, beta.
  - now split.  
  - cbn;  discriminate 3.
  -  intro;rewrite plus_zero_r.
     +  discriminate 2.
  -  simpl; case alpha1;case beta1.
     +  discriminate 3.
     + intros c n1 c0 H H0; rewrite compare_Lt_eq.
       *  discriminate 1.
       *  constructor.
     +  intros c n1 c0 H H0; rewrite compare_Gt_eq.
        *  discriminate 1.
        *  constructor.
     + intros c n1 c0 c3 n2 c4 H H0;
         case (compare  (ocons c3 n2 c4) (ocons c n1 c0));discriminate 1.
Qed.


Lemma plus_not_monotonous_l : exists alpha beta gamma : T1,
    alpha t1< beta /\ alpha + gamma = beta + gamma.
Proof.
  exists 3, 5, omega;  now  compute.
Qed.


Lemma mult_not_monotonous :  exists alpha beta gamma : T1,
      alpha t1< beta /\ alpha * gamma = beta * gamma.
Proof.
  exists 3, 5, omega; now compute.
Qed.


(** ** monotonicity of [succ]  *)

Lemma succ_strict_mono : forall a b, 
    lt a  b -> nf a -> nf b -> 
    lt (succ a) (succ b).
Proof.
  induction a; destruct b. 
  - intros; destruct (not_lt_zero H).
  -  cbn. destruct b1.
     intros.   apply coeff_lt; auto with arith. 
     intros _ _ H.
     apply head_lt; auto with T1. 
  -  intro H; destruct (not_lt_zero H).
  - cbn;  destruct a1.
    + destruct b1.
     *  intros H H0 H1;  destruct (lt_inv H).
        destruct (not_lt_zero H2).  
        destruct H2.
        -- destruct H2; auto with arith T1.
        -- decompose [and] H2.
           assert (b2 = zero).      
           { eapply nf_of_finite; eauto. }
           subst b2. 
           destruct (not_lt_zero H6).  
     * intros; apply head_lt; auto with T1.
    + intros H H0 H1; nf_decomp H0; nf_decomp H1.
      destruct b1.
      * destruct (lt_inv H).
        destruct (not_lt_zero H2).  
        destruct H2 as [H2 | H2]; destruct H2; discriminate. 
      * destruct (lt_inv H).
        -- auto with T1.
        -- destruct H2 as [[H2 H3] | H2].
           ++ rewrite H2; auto with T1.
           ++  decompose [and] H2; rewrite H5, H3.
               apply tail_lt. 
               apply IHa2 ; auto. 
Qed. 

Lemma succ_strict_mono_LT : forall alpha beta, 
    alpha t1< beta -> succ alpha t1< succ beta.
Proof.  
  intros alpha beta H; destruct H as [H [H0 H1]]; repeat split;auto.
  - now apply succ_nf.
  - now apply succ_strict_mono.   
  - now apply succ_nf.
Qed.

Lemma succ_mono : forall a b, nf a -> nf b ->
                              le a  b -> le (succ a)  (succ b).
Proof.
  intros a b H H0 H1; destruct (le_lt_or_eq _ _ H1).
  -  subst a; auto with T1.
  - apply lt_le_incl;  now  apply succ_strict_mono.
Qed.


Lemma lt_succ_le_R : forall a,  nf a -> forall b, nf b ->
                                                  le (succ a) b ->  lt a  b .
Proof.
  intros c Hc; elim Hc using nf_rect.
  - intros b H H0.  destruct b. destruct H0.   auto with T1. 
  - intros n b H H0.  destruct (le_lt_or_eq _ _ H0).
    subst. 
    cbn. 
    auto with T1 arith. 
    apply lt_trans with (succ (FS n)); auto with T1.
    cbn; auto with T1 arith. 
  - intros a  n b n' b' H H0 H1 H2 H3 b0 H4 H5.
    destruct (le_lt_or_eq _ _ H5).
    subst b0.
    apply lt_succ;auto.
    apply lt_trans with (succ (ocons (ocons a n b) n' b')).
    apply lt_succ;auto.
    auto. 
Qed.

Lemma LT_succ_LE_R : forall alpha  beta,
    nf alpha ->
    succ alpha  t1<= beta -> alpha  t1< beta. 
Proof. 
  intros. 
  destruct H0 as [H1 [H2 H3]].
  repeat split; auto. 
  apply  lt_succ_le_R; auto. 
Qed.

Lemma lt_succ_le_2 : forall a,  nf a -> forall b, nf b ->
                                                  lt a  (succ b)  ->  le a  b.
Proof.
  intros c Hc; elim Hc using nf_rect.
  - intros;apply zero_le.
  -  intros n b H; case b; cbn.
     + intros H0; generalize (lt_inv_nb  H0).
       intros [H2 | [_ H2]]; inversion H2.
     +    destruct alpha.
          * intros.  destruct (lt_inv_nb H0).
            assert (H8:n = n0 \/ (n < n0)%nat) by lia.
            destruct H8.
            destruct beta.    
            subst n0. 
            auto with T1.
            subst n0; auto with T1.
            auto with T1.
            destruct a.
            
            destruct (not_lt_zero H2).  
          * 
            intros.
            apply lt_le_incl.
            auto with T1.
  -  destruct b0.
     intros. 
     cbn in H5. 
     destruct (lt_inv  H5).
     destruct (not_lt_zero H6).
     destruct H6. 
     destruct H6; discriminate. 
     destruct H6; discriminate. 
     intros. 
     cbn in H5. 
     destruct b0_1.
     destruct (lt_inv  H5).
     destruct (not_lt_zero H6).
     destruct H6; discriminate. 
     destruct (lt_inv  H5).
     apply lt_le_incl;auto  with T1.

     destruct H6.
     destruct H6.
     injection H6;intros. 
     subst. 
     auto with T1. 
     decompose [and] H6.
     injection H7; intros; subst.  
     apply le_tail.
     apply H3; trivial.
     now apply nf_inv2 in H4. 
Qed.  



Lemma lt_succ_le : forall a,  nf a -> forall b, nf b ->
                                                lt a  b -> le (succ a)  b.
Proof.
  induction a.
  -  intros H0 c'; case c'.
     +  intros H1 H2; destruct (not_lt_zero H2). 
     +  destruct alpha.
        *  destruct n; intros t H H1.
           generalize (nf_of_finite H).
           intro; subst.
           now compute. 
           now compute.
        *  intros; simpl. now  compute. 
  -  destruct b.
     intros H0 H1; destruct (not_lt_zero H1).
     intros H0 H1; destruct (lt_inv H1).
     destruct a1;
       simpl.
     apply lt_le_incl.    
     auto with T1.
     apply lt_le_incl.    
     auto with T1.
     destruct H2.
     destruct H2; subst b1.
     simpl succ. 
     destruct a1.
     generalize (nf_of_finite H0).
     intro; subst. 
     generalize (lt_le_S _ _ H3).

     intro H2; destruct (Lt.le_lt_or_eq _ _ H2).
     auto with T1.
     subst; auto with T1.
     auto with T1.
     decompose [and] H2; subst. 
     clear H2.
     simpl succ. 
     destruct b1. 
     generalize (nf_of_finite H).
     intro; subst. 
     destruct (lt_inv H1). 
     destruct (not_lt_zero H2).
     destruct H2.
     destruct H2.
     destruct (Nat.lt_irrefl _ H3).
     decompose [and] H2; subst. 
     generalize (nf_of_finite H0).
     intro; subst. 
     destruct (not_lt_zero H7).
     apply le_tail. 
     eauto with T1.
Qed.

Lemma LT_succ_LE : forall alpha beta ,
    alpha t1< beta -> succ alpha t1<= beta.
Proof.   
  intros. 
  destruct H as [H1 [H2 H3]]; repeat split; auto. 
  apply succ_nf;auto. 
  apply  lt_succ_le; auto. 
Qed.

Lemma LT_succ_LE_2: forall alpha beta : T1,  nf beta -> alpha t1< succ beta
                                             -> alpha  t1<= beta.
  intros.
  split; eauto with T1.
  split; eauto with T1.
  apply lt_succ_le_2; eauto with T1.
Qed. 



Lemma succ_strict_monoR :
  forall alpha beta, nf alpha -> nf beta -> lt (succ alpha) (succ beta) ->
                     lt alpha beta.
Proof.
  intros alpha beta Halpha Hbeta H.
  apply lt_le_trans with (succ alpha).
  - now apply lt_succ.
  - apply lt_succ_le_2; auto.
    now apply succ_nf.
Qed.


Lemma succ_monomorphism : forall alpha (H:nf alpha) beta (H' : nf beta),
    lt alpha beta <-> lt (succ alpha) (succ beta).
Proof.
  split.
  - intro; now apply succ_strict_mono.
  -  intro; now apply succ_strict_monoR.
Qed.


Lemma succ_injective : forall alpha (H:nf alpha) beta (H' : nf beta),
    succ alpha = succ beta -> alpha = beta.
Proof.
  intros.
  destruct (lt_eq_lt_dec alpha beta); auto.
  destruct s; auto. 
  all:  rewrite succ_monomorphism  in l; auto;  rewrite H0 in l;
    now destruct (lt_irrefl l).
Qed.

Lemma succ_compatS : forall n:nat, succ (FS n) = FS (S n).
Proof.  reflexivity.  Qed.

Lemma succ_compat (n:nat) : succ (fin n) = FS n.
Proof.
  destruct n; reflexivity.
Qed.


(** ** monotonicity of [phi0] *)


Lemma phi0_mono_strict : forall a b, lt a  b -> lt (phi0 a) (phi0 b).
Proof.  auto with T1.  Qed.


Lemma phi0_mono_strict_LT : forall alpha beta, alpha t1< beta ->
                                               phi0 alpha t1< phi0 beta.
Proof. intros.  apply LT2; eauto with T1.
Qed.


Lemma phi0_mono : forall a b, le a  b  -> le (phi0 a) ( phi0 b).
Proof.
  intros a b H; destruct (le_lt_or_eq _ _ H).
  -  subst b; auto with T1. 
  -  apply lt_le_incl;  auto with T1.
Qed.


Lemma plus_left_absorb : 
  forall a n b c, lt c  (phi0 a) ->
                  c + ocons a n b = ocons a n b.
Proof.
  cbn;  destruct c.
  -   reflexivity.
  -   cbn. intro H; destruct (lt_inv H). 
      red in H0; unfold lt_b in H0 .
      destruct (compare c1 a); auto; try discriminate.
      destruct H0 as [[H0 H1] |[H0 [H1 H2]]].
      destruct (Nat.nlt_0_r _ H1).
      destruct (not_lt_zero H2).
Qed.

Lemma plus_compat: forall n p,  FS n +  FS p = FS (S n + p).
Proof.   reflexivity. Qed.


(** ** Multiplication *)

Lemma mult_fin_omega : forall n: nat, 
    FS n * omega = omega.
Proof.  now cbn. Qed.

Lemma phi0_plus_mult : forall a b, nf a -> nf b -> 
                                   phi0 (a + b) = phi0 a * phi0 b.
Proof.
  cbn; intro a; case a.
  -  intro b; case b;reflexivity. 
  -  intros until b;case b;simpl.
     +  case alpha;cbn;auto.
     +  reflexivity. 
Qed.

Lemma mult_compat : forall n p,  FS n * FS p =
                                 FS (n * p + n + p)%nat.
Proof.
  cbn; intros; f_equal;   ring. 
Qed.


Lemma mult_a_0 : forall a, a * zero = zero.
Proof.
  induction a as [|a1 IHa1 n a2 IHa2];[reflexivity| now destruct a1].  
Qed.

Lemma mult_1_a : forall a, nf a ->  1 * a = a.
Proof.
  induction a. 
  - reflexivity.
  - cbn; simpl in IHa2.
    intro H; case_eq a1.
    + intro; subst a1;  rewrite (nf_of_finite H);
        now rewrite <- (plus_n_O n).
    + intros t n0 t0 H0; subst a1; rewrite IHa2.
      * reflexivity.
      *  eapply nf_inv2;eauto.
Qed.

Lemma mult_a_1 : forall a, nf a -> a * 1  = a.
Proof.
  induction a.
  - reflexivity.
  - cbn;  simpl in IHa2.
    intro H;  case_eq a1.
    intro; subst a1; rewrite mult_1_r.
    now rewrite (nf_of_finite H).
    intros; subst a1; now  rewrite mult_1_r.
Qed.

Lemma nf_mult_fin alpha n: nf alpha -> nf (alpha * fin n).
Proof.
  revert n; induction n.
  -  now  rewrite mult_a_0.
  -  cbn; destruct alpha as [|alpha0 np alpha1].
     +  auto.
     + destruct alpha0.
       * intro; apply nf_FS.
       * intro; eapply nf_coeff_irrelevance; eauto.
Qed.

(**  **  About minus *)

Lemma minus_lt : forall a b, lt a  b -> a - b = zero.
Proof.
  induction a, b.
  1-3: easy.
  - intro H;
    destruct (lt_inv H) as [Hlt | [(Heq, Hlt) | (Heq0, (Heq1, Hlt))]]; 
    subst; simpl.
    + destruct a1.
      * now destruct b1.
      * unfold lt, lt_b in Hlt.
        now destruct (compare _ _).
    +  destruct b1.
      2: simpl.
      * destruct le_lt_dec; [easy | lia].
      * rewrite !compare_refl, Nat.compare_refl.
        now apply Nat.compare_lt_iff in Hlt as ->.
    + destruct b1.
      -- destruct le_lt_dec; [easy | lia].
      -- rewrite compare_refl, Nat.compare_refl.
         now apply IHa2.
Qed.


Lemma minus_a_a : forall a, a - a = zero.
Proof.
  induction a; simpl.
  - easy.
  - destruct a1.
    * destruct le_lt_dec; [easy | lia].
    * now rewrite compare_refl, Nat.compare_refl.
Qed.

Lemma minus_le : forall a b, le a b -> a - b = zero.
Proof.
  intros a b H; destruct (le_lt_or_eq _ _ H). 
  -  subst b; apply minus_a_a.
  -  apply minus_lt;auto.
Qed.



(** ** Exponential *)





Lemma exp_fin_omega : forall n, FS (S n) ^ omega = omega.
Proof.  reflexivity. Qed.



(** ** Relations between [ocons], [phi0] and [+]


 The next three lemmas express the consistency between
     the intuitive meaning given to the constructor cons and
     its derivates : phi0, omega-term, and the arithmetic 
     operations on ordinals which belong to epsilon0 *)


Lemma phi0_eq_bad : forall alpha, omega ^ alpha = phi0 alpha.
Proof.
  intro alpha.
  Fail reflexivity.  
(*
The command has indeed failed with message:
In environment
alpha : T1
Unable to unify "phi0 alpha" with "omega ^ alpha".
 *)
Abort.


Lemma phi0_eq : forall alpha, nf alpha -> omega ^ alpha =  phi0 alpha.
Proof.
  simple induction alpha; cbn.
  - reflexivity.
  -  destruct alpha0; cbn.
     +  intros H n t H0 H1;  generalize (nf_of_finite H1);
          intro; subst;
            case n; cbn.  
        * reflexivity.
        * induction n0; cbn.
          reflexivity.
          rewrite IHn0;  reflexivity.
     +  intros  H n0 t H0 H1; unfold omega_term;
          rewrite H0; cbn.
        rewrite <- (omega_term_plus_rw H1);
          rewrite  phi0_plus_mult.
        * unfold omega_term;auto.
        * unfold omega_term. apply single_nf.  eauto with T1. 
        *  eapply nf_inv2;eauto.
           
        * eapply nf_inv2;eauto.
Qed.


Lemma omega_term_def : forall a n, nf a -> omega_term a n =
                                           omega ^ a *  FS n.
Proof. 
  intros a n H; rewrite phi0_eq; auto.
  simpl; case a; simpl; unfold omega_term; auto.
  - rewrite <- (plus_n_O n); auto.
  - rewrite <- (plus_n_O n);  auto.
Qed.


Lemma ocons_def : forall a n b, nf(ocons a n b) ->
                                ocons a n b =  omega ^ a * FS n + b.
Proof.
  intros; rewrite <- omega_term_plus_rw; auto.
  - rewrite omega_term_def; auto.
    eapply nf_inv1;eauto.
Qed.

Theorem unique_decomposition : forall a n b a' n' b',
    nf (ocons a n b) -> nf (ocons a' n' b') ->
    omega ^ a *  FS n + b =
    omega ^ a' * FS n' + b' ->
    a = a' /\ n = n' /\ b = b'.
Proof.
  intros a n b a' n' b' N N'; rewrite <- (ocons_def N);
    rewrite <- (ocons_def N'); now injection 1.
Qed.

Theorem Cantor_normal_form :
  forall o, lt zero  o -> nf o ->
            {a:T1 & {n: nat & {b : T1 |
                                o = omega ^ a * FS n + b  /\
                                nf (ocons a n b) }}}.
Proof.
  intro ; case o.
  - intro H; case (lt_irrefl H). 
  - intros a n b H H0; exists a;exists n;exists b; split. 
    + now apply ocons_def.
    + assumption.
Defined.





Lemma LT_one : forall alpha, alpha t1< one -> alpha = zero.
Proof.
  intros alpha [H1 [H2 _]].
  destruct alpha; auto. 
  destruct (lt_inv H2).
  - destruct (not_lt_zero H). 
  -   decompose [and or] H.
      destruct (Nat.nlt_0_r _ H4).
      destruct (not_lt_zero H5). 
Qed.


Lemma lt_omega_inv : forall alpha,  alpha t1< omega ->
                                    alpha = zero \/ exists n, alpha = FS n.
Proof.                                    
  intros alpha [H1 [H2 _]]; destruct alpha; auto. 
  destruct (lt_inv H2). 
  -  assert(alpha1 = zero).
     {   apply LT_one.
         split.
         subst. 
         eauto with T1.
         split.
         auto.
         now compute. 
     }
     subst alpha1;  right; exists n.
     generalize (nf_of_finite H1).
     intro; now subst. 
  -     destruct H as [[H3 H4] |[H3 [H4 H5]]].
        destruct (Nat.nlt_0_r _ H4).
        destruct (not_lt_zero H5). 
Qed.

Ltac T1_inversion H :=
  match type of H with lt _ zero => destruct (not_lt_zero H)
                  | Nat.lt _ 0 => destruct (Nat.nlt_0_r _ H)
                  | Nat.lt ?x ?x => destruct (Lt.lt_irrefl _ H)
                  | lt ?x ?x => destruct (lt_irrefl  H)
                  | lt (ocons _ _ _) (ocons _ _ _) =>
                    destruct (lt_inv H)
                  | nf (ocons zero ?n ?y) => let e := fresh "e" in
                                             generalize (nf_of_finite H);
                                             intros  e
  end.

Lemma LT_of_finite :
  forall alpha n, alpha t1< FS n -> alpha = zero \/
                                  exists p, p < n  /\ alpha = FS p.
Proof.
  intros alpha n [H1 [H2 H3]].
  destruct alpha.
  - now left.
  - T1_inversion H2.
    T1_inversion H.
    destruct H as [[H4 H5] |[H4 [H5 H6]]].
    subst. 
    generalize (nf_of_finite H1).
    intro;subst. 
    right; exists n0.
    split; auto with T1 arith.  
    T1_inversion H6.
Qed.



Lemma nf_omega : nf omega.
Proof.  auto with T1. Qed.

(* About omega ^ omega *)

Theorem nf_phi0 alpha : nf alpha -> nf (phi0 alpha).
Proof. compute; auto with T1. Qed.



Global Hint Resolve nf_phi0 : T1.

Definition omega_omega := phi0 omega.

Lemma nf_omega_omega : nf omega_omega.
Proof.  repeat constructor. Qed.   


Lemma mult_0_a : forall a, zero * a  = zero.
Proof.  induction a;simpl;auto. Qed.


Lemma mult_Sn_add (alpha : T1) n : nf alpha -> 
                                   alpha * (FS (S n))  = alpha * FS  n + alpha.
Proof.
  intro; simpl;  destruct alpha.
  -   now  simpl.
  - destruct alpha1.
    +  assert (H0 :alpha2 = zero).
       { eapply nf_of_finite; eauto. }
       subst;  rewrite plus_compat; f_equal;  ring.
    +  simpl; rewrite !compare_refl, Nat.compare_refl.
       f_equal.
       lia.
Qed.




Lemma cases_for_mult (alpha : T1) :
  nf alpha -> 
  alpha = zero \/
  (exists n : nat, alpha = FS n) \/
  (exists a n, a<> zero /\ alpha = ocons a n zero) \/
  (exists a n b,  a <> zero /\ b <> zero /\ alpha = ocons a n b).
Proof.
  destruct alpha.
  - now left.
  - right.
    destruct alpha1.
    left; exists n.

    apply nf_of_finite in H. now subst.
    right.
    destruct alpha2.
    left .     exists (ocons alpha1_1 n0 alpha1_2),n.
    split;[discriminate|trivial].
    right ;    exists (ocons alpha1_1 n0 alpha1_2), n, (ocons alpha2_1 n1 alpha2_2).
    split;[discriminate|trivial].
    split;[discriminate|trivial].

Qed.


Lemma L03 alpha n beta p :
  alpha <> zero ->
  (ocons alpha n beta * FS p) = ocons alpha (p + n * S p) beta.
  simpl.
  destruct alpha.
  now destruct 1.
  trivial.
Qed.

Lemma L05 a n b c p d :
  a <> zero -> c <> zero ->
  (ocons a n b * ocons c p d) =
  ocons (a + c) p (ocons a n b * d).
  simpl.
  destruct a, c; intros.
  now destruct H.
  now destruct H.
  now destruct H0.
  auto.
Qed.

Lemma nf_LT_iff :
  forall alpha n beta, nf (ocons alpha n beta) <->
                       nf alpha /\ nf beta
                       /\ beta t1< phi0 alpha.
Proof.
  split.
  intros H.
  repeat split; eauto with T1.
  apply    nf_helper_phi0.
  eapply nf_helper_intro; eauto.
  intro H; decompose [and] H.
  apply nf_intro; eauto.
  apply nf_helper_phi0R. destruct H3; tauto.
Qed.

Lemma plus_smono_r (alpha:T1) :
  forall beta gamma,  lt beta gamma -> lt (plus alpha beta) (plus alpha gamma).
  induction alpha.
  - simpl;auto.
  - intros; simpl.
    destruct beta, gamma.
    +  destruct (lt_irrefl H).
    + clear H. 
      case_eq (compare alpha1 gamma1); intro H0.
      apply coeff_lt; abstract lia.
      * apply head_lt; now rewrite <- lt_iff.
      * apply tail_lt.
        rewrite <- (plus_zero_r alpha2) at 1;  apply IHalpha2.
        apply zero_lt.
    + destruct (not_lt_zero H).
    + T1_inversion H.
      
      case_eq (compare alpha1 beta1); intro H1.
      apply compare_Eq_impl in H1; subst.
      rewrite  <- lt_iff in H0; rewrite H0.
      apply head_lt; now rewrite <- lt_iff.
      rewrite lt_iff in H1.
      assert (H2:= lt_trans  H1  H0).
      rewrite <- lt_iff in H2. rewrite H2.
      apply head_lt. auto.

      case_eq (compare alpha1 gamma1); intro H2.
      apply compare_Eq_impl in H2.
      subst.
      apply coeff_lt.
      abstract lia.
      apply head_lt.
      rewrite <- lt_iff; auto.
      apply tail_lt.
      apply IHalpha2.
      apply head_lt; auto.
      destruct H0.
      destruct H0.
      subst.
      case_eq (compare alpha1 gamma1).
      intro.
      apply coeff_lt; abstract lia.
      intro; apply coeff_lt; auto.
      intro; apply tail_lt; apply IHalpha2.
      apply coeff_lt; auto.
      decompose [and] H0; subst.
      case_eq (compare alpha1 gamma1).

      intro; apply tail_lt; auto.
      intros; apply tail_lt. auto.
      intro. apply tail_lt. apply IHalpha2.
      apply tail_lt;auto.      
Qed.


Lemma plus_smono_LT_r (alpha:T1) :
  forall beta gamma,  nf alpha -> beta t1< gamma -> alpha + beta t1< alpha + gamma.
Proof.
  destruct 2 as [H1 [H2 H3]]; split.
  apply plus_nf; auto.
  split.
  now apply plus_smono_r.
  apply plus_nf; auto.  
Qed.




Lemma LT_add (alpha beta : T1): nf alpha -> nf beta -> beta <> zero ->
                                alpha t1< alpha + beta.
Proof.
  intros H H0 H1.
  rewrite <- plus_zero_r at 1.
  apply plus_smono_LT_r; auto.
  apply not_zero_lt; auto.
Qed.



Section Proof_of_nf_mult.

  Variable alpha : T1.
  Hypothesis Halpha : nf alpha.

  Let P (beta : T1) :=
    nf beta -> nf (alpha * beta) /\
               (alpha <> zero ->
                forall gamma, gamma t1< beta ->
                              alpha * gamma t1< alpha * beta).
  Section Induction.
    
    Variable beta : T1.
    Hypothesis Hbeta : nf beta.
    Hypothesis IHbeta : forall delta, delta t1< beta -> P delta.


    Lemma L1 : alpha = zero -> P beta.
    Proof.
      intro; subst; unfold P; intros;rewrite mult_0_a; split.
      - auto with T1.
      - now destruct 1.
    Qed.

    Lemma L2 : beta = zero -> P beta.
    Proof.
      intro; subst; unfold P; rewrite mult_a_0.
      split; auto.
      intros H0 gamma H1;  destruct (not_LT_zero H1).
    Qed.

    
    Lemma L3 n p : alpha = FS n -> beta = FS p -> P beta.
    Proof.
      intros; subst; red; intros; split.
      - apply (nf_mult_fin  (S p) H).
      - intros _ gamma H1; destruct (LT_of_finite H1 ).
        + subst; rewrite mult_a_0; eauto with T1.
        +  destruct H0 as [p0 [H2 H3]]; subst; simpl.
           apply LT3; eauto with T1.
           apply Plus.plus_lt_le_compat; auto.
           apply PeanoNat.Nat.mul_le_mono_l; abstract lia.
    Qed. 


    Lemma L4 : forall a n b p, a <> zero ->
                               alpha = ocons a n b -> beta = FS p ->
                               P beta.
    Proof.
      unfold P; intros; subst;  split. 
      -  simpl; destruct a.
         +  now destruct H.
         + apply nf_coeff_irrelevance with n; auto.
      -  intros _ gamma H4; destruct (LT_of_finite H4).
         +   subst; rewrite mult_a_0; simpl;  destruct a.
             *  apply LT1,  nf_FS.
             *  auto with T1.
         + destruct H0 as [p0 [H5 H6]]; subst; simpl.
           assert (p0 + n * S p0 < p + n * S p)%nat.
           { 
             apply Plus.plus_lt_le_compat; auto.
             apply PeanoNat.Nat.mul_le_mono_l;  abstract lia.
           }
           destruct a.
           * apply LT3;auto.
           * apply LT3; eauto with T1.
    Qed.

    Lemma L5 a n b c p : a <> zero -> c <> zero ->
                         (ocons a n b) * (ocons c p zero) =
                         ocons (a + c)  p zero.
    Proof.
      cbn; destruct a,c; trivial.
      -  now destruct 1.
      -  now destruct 2.
    Qed.

    Lemma L6 n c p d :  c <> zero -> FS n * ocons c p d =  ocons c p (FS n * d).
    Proof.
      cbn; destruct c; [now destruct 1 | trivial].
    Qed.

    Lemma L7 n c p :  c <> zero -> FS n * ocons c p zero = ocons c p zero.
    Proof.
      intro H; rewrite (L6 n _  _ H).
      now rewrite mult_a_0.
    Qed.


    Lemma L8 n  c p : alpha = FS n -> beta = ocons c p zero -> c <> zero ->
                      P beta.
    Proof.
      intros;  subst; intros.
      assert (nf (FS n * ocons c p zero)).
      {  rewrite L7;  auto;   split; auto.
      }
      split; auto.
      intros _ gamma H3; assert (nf gamma) by eauto with T1.
      destruct (cases_for_mult  H2).
      - subst;rewrite mult_a_0; auto.
        rewrite L7; auto.
      -  destruct H4.
         + destruct H4; subst;  rewrite mult_compat.
           rewrite L7; auto.
           *  apply LT2; eauto with T1.
              --  apply not_zero_lt; eauto with T1.
         +  destruct H4.
            * destruct H4 as [a [q [H6 H7]]]; subst; rewrite L7; auto.
              -- rewrite L7; auto.
            *  destruct H4 as [a [q [b [H6 [H7 H8]]]]]; subst.
               rewrite L6; auto.
               rewrite L6; auto.
               -- rewrite mult_a_0.
                  destruct (LT_inv H3).
                  ++ apply LT2; auto.
                     rewrite <- L6; auto.
                     ** destruct (@IHbeta (ocons a q b)); auto with T1.
                  ++    destruct H4.
                        subst; destruct H5.
                        ** apply LT3; auto with T1.
                           rewrite <- L6 ; auto.
                           destruct (@IHbeta (ocons c q b)); auto.
                        ** destruct H4.
                           destruct (not_LT_zero H5); auto.
    Qed.


    Lemma L9 : forall n c, nf c -> c <> zero -> FS n * c <> zero.
    Proof.
      intros n c H H0; destruct (cases_for_mult  H) as [| H1].
      - contradiction.
      -  destruct H1 as [H1 | [ H1 | H1]].
         +   destruct H1; subst;   discriminate.
         +   destruct H1 as [a [p [H2 H3]]]; subst; cbn.
             destruct a;discriminate.
         + destruct H1 as [a [p [b [H2 [H3 H4]]]]]; subst; cbn.
           destruct a; [ now destruct H2| discriminate].
    Qed.

    Lemma L10 : forall a n b c, nf c -> nf (ocons a n b) ->
                                a <>zero -> c <> zero ->
                                ocons a n b * c <> zero.
    Proof.
      intros a n b c H H0 H1 H2; destruct (cases_for_mult    H).
      -  subst; now destruct H2.
      - destruct H3 as [H3 | [H3 | H3]].
        + destruct H3; subst; rewrite L03; auto; discriminate.
        +  destruct H3 as [d [p [H4 H5]]]; subst; rewrite L05; auto; discriminate.
        + destruct H3 as [d [p [e [H4 [H5 H6]]]]];
            subst; rewrite L05; auto; discriminate.
    Qed.


    Lemma L11 n  c p d :
      alpha = FS n -> beta = ocons c p d  -> c <> zero ->
      d <> zero ->  P beta.
    Proof. 
      intros H H0 H1 H2; subst alpha beta.
      assert (nf (FS n * ocons c p d)).
      { rewrite L6.
        - assert (FS n * d t1< FS n * phi0 c).
          {  destruct (@IHbeta (ocons c 0 zero)); eauto with T1.
             - destruct p.
               + apply LT4;auto with T1.
                 apply nf_phi0; eauto with T1.
                 apply not_zero_lt; eauto with T1.
               + apply LT_trans with (ocons c 0 d).
                 * apply LT4;eauto with T1.
                   apply not_zero_lt; eauto with T1.
                 * apply LT3; eauto with T1 arith.
             -  assert (H3 : FS n <> zero)  by discriminate.
                apply (H0 H3 d).
                rewrite nf_LT_iff in Hbeta; tauto.
          }
          rewrite L7 in H.
          + rewrite nf_LT_iff; split;  eauto with T1.
          +  destruct (@IHbeta (phi0 c)).
             destruct p.
             * apply LT4;auto with T1.
               apply nf_phi0; eauto with T1.
               apply not_zero_lt; eauto with T1.
             *  apply LT_trans with (ocons c 0 d).
                -- apply LT4;eauto with T1.
                   apply not_zero_lt; eauto with T1.
                -- apply LT3; eauto with T1 arith.
             * auto with arith.
               eauto with T1.    
             * eauto with T1.
        - auto.
      } 
      split; auto.
      intros _ gamma H4; assert (nf gamma) by eauto with T1.
      destruct (cases_for_mult  H3).
      -  subst; rewrite mult_a_0; auto.
         rewrite L6; auto.
         apply LT1; rewrite <- L6; auto.
      -   destruct H5.
          + destruct H5; subst.
            rewrite mult_compat, L6; auto.
            apply LT2; auto.
            rewrite <- L6; eauto with T1.
            apply not_zero_lt; eauto with T1.
          +   destruct H5.
              * destruct H5 as [a [q [H6 H7]]]; subst; rewrite L6; auto.
                rewrite L6, mult_a_0; auto.
                destruct (LT_inv H4); auto.
                --  apply LT2; auto with T1.
                    rewrite <- L6; eauto with T1.
                --  destruct H5; subst.
                    ++ destruct H7.
                       ** apply LT3; auto with T1.
                          rewrite <- L6; auto.
                       ** destruct H5; subst.
                          apply LT4; eauto with T1.
                          rewrite <- L6; auto.
                          apply not_zero_lt.
                          destruct (@IHbeta  d).
                          apply tail_LT_cons; auto.
                          eauto with T1.
                          auto.
                          apply L9; eauto with T1.
              * destruct H5 as [a [q [b [H6 [H7 H8]]]]]; subst.
                repeat rewrite L6; auto.
                destruct (LT_inv H4).
                --  apply LT2; auto.
                    rewrite <- L6; auto.
                    destruct (@IHbeta (ocons a q b)); auto.
                    rewrite <- L6; auto.
                --  destruct H5.
                    subst; destruct H8.
                    apply LT3; auto with T1.
                    rewrite <- L6; auto.
                    destruct (@IHbeta (ocons c q b)); auto.
                    rewrite <- L6; auto.
                    ++ destruct H5; subst.
                       apply LT4.
                       rewrite <- L6; auto.
                       destruct (@IHbeta (ocons c p b)); auto.
                       rewrite <- L6; auto.
                       destruct (@IHbeta  d); auto.
                       apply tail_LT_cons; eauto with T1.
                       eauto with T1.
                       apply H9; auto.
                       discriminate.
    Qed.

    Lemma L12 : forall a n b c p d , a <> zero -> c <> zero ->
                                     alpha = ocons a n b ->
                                     beta = ocons c p d ->
                                     P beta.
    Proof.
      unfold P;  intros; subst.
      assert (nf (ocons a n b * ocons c p d)).
      {  rewrite L05; auto.
         destruct (T1_eq_dec d zero).
         + subst;  rewrite mult_a_0; apply single_nf.
           apply plus_nf; eauto with T1.
         +  apply nf_intro.
            apply plus_nf; eauto with T1.
            generalize (@IHbeta d); intro H1; destruct H1; auto with T1.
            apply tail_LT_cons; eauto with T1.
            eauto with T1.
            apply nf_helper_phi0R.
            apply lt_le_trans with (ocons a n b * phi0 c).
            {
              generalize (@IHbeta    (phi0 c)); intro H1; unfold P in H1.
              destruct H1; auto.
              - destruct p.
                + apply LT4; eauto with T1.
                  apply not_zero_lt; eauto with T1.
                + apply LT3; eauto with T1; auto with arith.
              -  eauto with T1.
              -  assert (ocons a n b <> zero)  by discriminate.
                 specialize (H2 H4 d). 
                 rewrite nf_LT_iff in H3.
                 destruct H2. 
                 tauto.
                 destruct H5; auto.
            }
            rewrite L5; auto.
            * apply le_refl.
      }
      split; auto.
      intros _ gamma Hgamma; assert (nf gamma) by eauto with T1.
      rewrite L05; auto.
      destruct (cases_for_mult  H2).
      -  subst; rewrite mult_a_0; apply LT1.
         rewrite <- L05; auto.
      -  destruct H4.
         + destruct H4 as [q Hq]; rewrite Hq. 
           rewrite L03; auto.
           apply LT2;   auto.
           generalize  (@IHbeta (FS q)); intros H5.
           destruct H5; auto.
           subst; auto. 
           apply nf_FS; auto.
           rewrite <- L05; auto.
           apply LT_add; eauto with T1.
         + destruct H4. 
           destruct H4 as [x [x0 [H4 H5]]].
           rewrite H5, L05, mult_a_0.
           rewrite H5 in Hgamma.
           destruct (LT_inv Hgamma).
           *  apply LT2.
              apply single_nf; eauto with T1.
              apply plus_nf; eauto with T1.
              rewrite <- L05; auto.
              apply plus_smono_LT_r; eauto with T1.
           * destruct H6.
             subst x.
             destruct H7. 
             apply LT3.
             apply single_nf; eauto with T1.
             apply plus_nf; eauto with T1.
             rewrite <- L05; auto.
             auto.
             destruct H6; subst x0.
             apply LT4.
             apply single_nf; auto with T1.
             apply plus_nf; eauto with T1.
             rewrite <- L05; auto.
             assert (nf (ocons a n b * d)).
             { destruct (@IHbeta d); eauto with T1.
               apply tail_LT_cons; eauto with T1.
             }
             apply not_zero_lt; auto.
             apply L10; eauto with T1.
             intro; subst; destruct (LT_irrefl H7).
           *        auto.
           * auto.
           * destruct H4 as [e [q [f [H6 [H7 H8]]]]].
             rewrite H8, L05; auto.
             rewrite H8 in Hgamma.
             destruct (LT_inv Hgamma).
             --  apply LT2.
                 rewrite <- L05; auto.
                 destruct (@IHbeta ( ocons e q f)); auto.
                 subst;auto.
                 rewrite <- L05;auto. 
                 apply plus_smono_LT_r; eauto with T1.
             --   destruct H4; subst.
                  destruct H5.
                  ++  apply LT3; auto.
                      rewrite <- L05; auto.
                      destruct (@IHbeta (ocons c q f)); auto.
                      rewrite <- L05; auto.
                  ++ 
                    destruct H4; subst.
                    apply LT4; auto.
                    rewrite <- L05; auto.
                    destruct (@IHbeta (ocons c p f)); auto.
                    rewrite <- L05; auto.
                    destruct (@IHbeta  d); eauto with T1.
                    apply tail_LT_cons; auto.
                    assert (ocons a n b <> zero) by discriminate.
                    specialize (H8 H9 f H5);  auto.
    Qed.


    Lemma L13 : P beta.
      destruct (cases_for_mult  Halpha).
      - apply L1;auto.
      - destruct (cases_for_mult  Hbeta).
        + apply L2; auto.
        + destruct H as [[n Hn] | ].
          destruct H0 as [[p Hp] | ].
          eapply L3; eauto.
          destruct H as [[a [p  [H1 H2]]] | ].
          apply L8 with n a p; auto.
          destruct H as [a [p [b [H1 [H2 H3]]]]].
          apply L11 with n a p b; auto.
          destruct H.
          destruct H as [a [n [H1 H2]]].
          destruct H0.

          destruct H.  apply L4 with a n zero x; auto.
          destruct H.
          destruct H as [b [p [H3 H4]]].
          apply L12 with a n zero b p zero; auto.
          destruct H as [b [p [c [H3 [H4 H5]]]]].
          apply L12 with a n zero b p c;auto.
          destruct H as [a [n [b [H1 [H2 H3]]]]].
          destruct H0.
          destruct H.
          apply L4 with a n b x; auto.
          destruct H.
          destruct H as [c [p [H4 H5]]].
          apply L12 with a n b c p zero; auto.
          destruct H as  [c [p [d [H4 [H5 H6]]]]].
          apply L12 with a n b c p d;auto.
    Qed.

  End Induction.



  Lemma L14  beta : nf beta -> P beta.
  Proof.
    pattern beta; apply well_founded_induction with LT.
    apply T1_wf.
    intros; apply L13.
    auto. 
    intros.
    apply H; eauto with T1.
  Qed.


End Proof_of_nf_mult.



Theorem nf_mult alpha beta : nf alpha -> nf beta ->
                             nf (alpha * beta).
Proof.
  intros.
  destruct  (L14   H  H0); auto. 
Qed.


Theorem mult_mono alpha beta gamma : nf alpha -> alpha <> zero ->
                                     beta t1< gamma -> alpha * beta t1< alpha * gamma.
Proof.
  intros.
  destruct  (@L14  alpha H gamma ); eauto with T1.
Qed.


Lemma nf_exp_F alpha n : nf alpha -> nf (exp_F alpha n).
Proof.
  induction n; cbn.
  - eauto with T1.
  - intro; apply nf_mult; auto.
Qed.


Lemma exp_F_eq alpha n : nf alpha -> (exp_F alpha n = alpha ^ n)%t1.
Proof.
  induction n; cbn.
  - destruct alpha.
    + trivial.
    + destruct alpha1.
    * destruct n; auto.
    * trivial.
  -   destruct alpha.
     intro; now rewrite mult_0_a.
     destruct alpha1.
     + destruct n0;auto.
      intros; assert (alpha2 = zero).
      { eapply nf_of_finite; eauto. }
      subst; rewrite mult_1_a.
       *  destruct n;cbn;auto.
       * apply nf_exp_F.
         auto with T1.
     +  reflexivity.
Qed.




Lemma limitb_cases : forall alpha n beta,
    nf (ocons alpha n beta) ->
    limitb (ocons alpha n beta)  ->
    { alpha <> zero /\ beta = zero} +
    {alpha <> zero /\ limitb beta }.
Proof.
  intros alpha n beta H;  simpl;  destruct alpha.
  - discriminate.
  - destruct beta.
    +  left; split;auto.
       discriminate.
    + right; split; auto.
      * discriminate.  
Defined.

Lemma pred_of_succ : forall  beta,  nf beta -> pred (succ beta) = Some beta.
Proof.
  induction beta.
  - reflexivity.
  - simpl; destruct beta1.
    + intros; replace beta2 with zero.   
      reflexivity. 
      { T1_inversion H. auto.      }
    +  intros; simpl;  destruct n.
       *   destruct beta2.
           { reflexivity. }
           { simpl;  destruct (beta2_1).
             - f_equal.
               cbn. 
               apply nf_inv2 in H. 
               T1_inversion H.
               subst;auto. 
             -
               simpl; simpl in *; destruct (pred (succ beta2_2)).
               f_equal.
               injection   IHbeta2.
               intro;subst;auto.
               eapply nf_inv2;eauto. 
               discriminate IHbeta2.
               eapply nf_inv2;eauto. 
           }           
       * rewrite IHbeta2;   auto.
         apply nf_inv2 in H; eauto. 
Qed.




Lemma pred_of_limit : forall alpha, nf alpha ->
                                    limitb alpha ->
                                    pred alpha = None.
Proof.
  intros; induction alpha.
  - reflexivity. 
  -    simpl; destruct alpha1.
       +   destruct n;  simpl in H0; discriminate.
       +   destruct (limitb_cases  H H0).
           *  destruct a.    
              subst.
              reflexivity.
           * destruct a; rewrite IHalpha2;auto.
             eauto with T1.
Qed.


Definition zero_limit_succ_dec :
  forall alpha, nf alpha ->
                ({alpha = zero} + {limitb alpha }) + 
                {beta : T1 |  nf beta /\ alpha = succ beta} .
Proof with eauto with T1.
  induction alpha as [| gamma Hgamma n beta Hbeta].
  - intros _; left; now left.                                           
  - intro H;  destruct gamma.
    + assert (beta = zero). eapply nf_of_finite; eauto. 
      
      subst beta; right.
      destruct n.
      { exists zero. split; auto with T1. }
      { exists (FS n).    split.
        apply nf_FS.
        reflexivity. 
      }
    +  destruct Hbeta ...
       *   destruct s.
           subst beta.
           left;right.
           reflexivity.
           left;right.
           simpl; destruct beta.
           reflexivity.
           auto.
       *  destruct s as [beta0 [H1 H2]]; subst beta.
          right;  exists (ocons (ocons gamma1 n0 gamma2) n beta0).
          split.
          { apply nf_intro; auto.
            inversion H; auto.
            apply nf_inv1 in H. auto. 
            apply nf_helper_phi0R; apply lt_trans with (succ beta0);auto.
            apply lt_succ.
            apply nf_helper_phi0;  eapply nf_helper_intro; eauto.
          }
          reflexivity.
Defined. 



Lemma pred_of_limitR : forall alpha, nf alpha -> alpha <> zero ->
                                     pred alpha = None -> limitb alpha.
Proof.
  intros alpha Halpha; destruct (zero_limit_succ_dec Halpha).
  - destruct s; auto.
  - destruct s  as [x [H H0]]; subst.
    rewrite pred_of_succ; auto.
    + discriminate.
Qed.



Lemma pred_LT : forall alpha beta, nf alpha -> pred alpha = Some beta ->
                                   beta t1< alpha .
Proof.
  intros; destruct (zero_limit_succ_dec H).
  - destruct s.
    +  subst; discriminate.
    +   rewrite pred_of_limit in H0; trivial.
        * discriminate.
  -   destruct s.
      destruct a.
      subst;     rewrite pred_of_succ in H0; trivial.
      +  injection H0; intros;  subst x; split; auto.
         split; auto.
         now apply lt_succ.
Qed.






Lemma pred_nf : forall alpha beta, nf alpha -> pred alpha = Some beta ->
                                   nf  beta.
Proof.
  intros alpha beta H H0; now destruct (pred_LT H H0).
Qed.



Lemma limitb_succ : forall alpha, nf alpha ->  ~ limitb (succ alpha) .
  induction alpha.
  - discriminate.
  - intros;  simpl;  destruct alpha1.
    + discriminate. 
    + simpl; case_eq (succ alpha2).
      *  intros; now destruct (succ_not_zero alpha2).
      *  intros; rewrite <- H0; apply IHalpha2; eauto with T1.
Qed. 

Lemma LT_succ : forall alpha, nf alpha -> alpha t1< succ alpha.
Proof. 
  repeat split; auto.
  -  apply lt_succ.
  -  now apply succ_nf.
Qed.

Lemma limitb_not_zero : forall alpha, nf alpha -> limitb alpha  ->
                                        alpha <> zero.
Proof.
  unfold not; intros; subst;discriminate.
Qed.


Global Hint Resolve limitb_not_zero : T1.


Lemma limitb_succ_tail :
  forall alpha n beta, nf beta ->  ~ limitb (ocons alpha n (succ beta)).
Proof.  
  simpl;intros; destruct alpha.
  - discriminate.
  -  case_eq (succ beta).
     + intro; now destruct (succ_not_zero beta).
     +  intros gamma p delta H0;  rewrite <- H0; now  apply limitb_succ.
Qed.


Lemma succ_not_limit : forall alpha:T1, succb alpha -> limitb alpha = false.
Proof.
  induction  alpha. 
  intro; discriminate.
  simpl.
  destruct alpha1.
  auto.
  intro.
  rewrite IHalpha2;auto.
  destruct alpha2;auto.
Qed.


Lemma succb_def alpha (Halpha : nf alpha) :
  succb alpha -> {beta | nf beta /\ alpha = succ  beta}.
Proof.
  intro H; destruct   (zero_limit_succ_dec Halpha) as [[H0 | H0] | H0].
  - subst alpha; discriminate.
  - rewrite succ_not_limit in H0; trivial.
    discriminate.
  -   exact H0.
Defined.


Lemma succb_iff alpha (Halpha : nf alpha) :
  succb alpha <-> exists beta : T1, nf beta /\ alpha = succ  beta.
Proof.
  split.
  intro H; destruct (succb_def Halpha).  
  - trivial.   
  - now exists x.
               - destruct 1 as [beta [Hbeta  H'beta]].
                 subst.     
                 now apply succ_succb.
Qed.

Lemma LE_r : forall alpha beta, alpha t1< beta -> alpha t1<= beta.
Proof.
  intros alpha beta [H1 [H2 H3]]; repeat split; eauto with T1.
Qed.

Lemma LE_LT_eq_dec : forall alpha beta, alpha t1<= beta ->
                                        {alpha t1< beta} + {alpha = beta}.
Proof. 
  unfold LE, restrict; intros alpha beta H; decompose [and] H.
  destruct (le_eq_lt_dec _ _ H2).
  now right.  
  left; repeat split; auto. 
Defined.



Lemma LT_eq_LT_dec : forall alpha beta,
    nf alpha -> nf beta ->
    {alpha t1< beta} + {alpha = beta} + {beta t1< alpha}.
Proof.
  intros; destruct  (lt_eq_lt_dec alpha beta) as [[H1 | H1] | H1].
  - left; left; split; eauto with T1.
  - left; now right.
  - right; split; auto with T1. 
Defined.


Lemma lt_ocons_phi0_inv alpha n beta gamma :
  ocons alpha n beta t1< phi0  gamma <-> beta t1< phi0 alpha /\ alpha t1< gamma.
Proof.                                        
  split.
  -  destruct 1 as [H [H0 H1]]; repeat split; eauto with T1.
     apply nf_helper_inv in H0; auto.
     rewrite nf_LT_iff in H.
     destruct H; eauto with T1.
     destruct H2; eauto with T1.
     now apply nf_helper_inv in H0.
  - destruct 1.
    apply LT2; auto.
    rewrite nf_LT_iff; eauto with T1.
    eauto with T1.
Qed.


Lemma nf_LT_right : forall alpha n beta beta',
    nf (ocons alpha n beta) ->
    beta' t1< beta ->
    nf (ocons alpha n beta').
Proof.
  intros alpha n beta beta'; repeat rewrite nf_LT_iff.
  intros [H1 [H2 H3]] H4;  split; auto.
  split.   eauto with T1.
  apply LT_trans with beta; auto.
Qed.


Lemma eq_succ_LT : forall alpha beta, nf beta -> alpha = succ beta ->
                                      beta t1< alpha.
Proof. 
  intros; subst;  apply LT_succ; auto.
Qed. 

Lemma eq_succ_lt : forall alpha beta, nf beta -> alpha = succ beta ->
                                      lt  beta  alpha.
Proof. 
  intros alpha beta H H0; destruct (eq_succ_LT H H0); tauto.
Qed. 


Definition strict_lub (s : nat -> T1) (lambda : T1) :=
  (forall i, s i t1< lambda) /\
  (forall alpha, (forall i, s i t1<= alpha) -> lambda t1<= alpha).


Definition strict_lub_lub : forall s l alpha,  strict_lub s l ->
                                               (forall i, s i t1<=  alpha) ->
                                               l t1<= alpha.
Proof. destruct 1; auto. Qed.


Definition strict_lub_maj : forall s l ,  strict_lub s l ->
                                          forall i, s i t1< l.
Proof. destruct 1; trivial.  Qed.



Lemma strict_lub_unique : forall s l l', strict_lub s l ->
                                         strict_lub s l' ->
                                         l = l'.
Proof.
  intros s l l' H H'; destruct H, H';  apply LE_antisym;eauto.
  apply H0.
  auto with T1.
  intro; apply LE_r; auto.
  apply H2.  intro; apply LE_r; auto.
Qed.




Lemma strict_lub_limitb : forall (alpha :T1)(s : nat -> T1),
    nf alpha -> strict_lub s alpha -> limitb alpha.
Proof.
  destruct 2.
  destruct (zero_limit_succ_dec H).
  destruct s0.
  - 
    subst.
    destruct (not_LT_zero (H0 0)).
  - assumption.
  -     destruct s0 as [beta [H2 H3]].
        subst.
        specialize (H1 beta ).
        assert (forall i, s i t1<= beta).
        {
          intro i.  
          apply LT_succ_LE_2;auto.
        }
        generalize (H1 H3).
        intro H4.
        absurd (beta t1< beta).
        apply LT_irrefl.
        apply LT_LE_trans with (succ beta);auto.
        now    apply LT_succ.     
Qed.



Lemma lt_one (alpha:T1) : lt alpha one -> alpha = zero.
  destruct alpha.
  - auto.
  -  intro H;  destruct (lt_inv H) as [H0 | H0].
     +     destruct (not_lt_zero H0).
     +   destruct H0 as [[_ H1] | [_  [_ H1]]].
         *   abstract lia.
         *   destruct (not_lt_zero H1).
Qed.



Lemma  omega_limit : strict_lub fin omega.
Proof.    
  split.
  - intro i;  destruct i; compute; auto.
  -   intros  alpha H .
      assert (Hnf : nf alpha) by eapply (LE_nf_r (H 0)).
      + destruct (LT_eq_LT_dec nf_omega Hnf ) as [[H0 | H0] | H0].
        *  now apply LE_r.
        *  subst; now apply LE_refl.
        * destruct  (lt_omega_inv H0).
          { subst ; auto with T1.
            specialize (H 1);  compute in H; tauto.
          }
          { destruct H1 as [n H3].
            subst ; generalize (H (S (S n))).
            intro H2.
            destruct (le_inv  (LE_le H2)) as [H1 | H1].
            -   destruct (not_lt_zero H1).
            -   destruct H1 as [[_ H3] | [_ [H3 _]]].
                + destruct (Nat.nlt_succ_diag_l _ H3). 
                + destruct (Nat.neq_succ_diag_l _ H3).
          }
Qed.



Lemma LT_succ_LT_eq_dec :
  forall alpha beta, nf alpha -> nf beta ->
                     alpha t1< succ beta -> {alpha t1< beta} + {alpha = beta}.
Proof. 
  intros.
  destruct H1 as [H2 [H3 H4]].
  generalize (lt_succ_le_2 H H0 H3).
  intro;  destruct (le_eq_lt_dec _ _ H1).
  now right.
  left; repeat split; auto. 
Defined.


Lemma lt_succ_le_2':
  forall a : T1, nf a -> forall b : T1, nf b -> a t1<  succ b  ->
                                        a t1< b \/ a = b.
Proof.
  intros.
  destruct H1 as [H2 [H3 H4]].
  generalize (lt_succ_le_2  H2 H0 H3);auto.
  intro H5;  destruct (le_lt_or_eq _ _ H5); auto. 
  left; split; auto.   
Qed.   





Lemma succ_lt_limit alpha (Halpha : nf alpha)(H : limitb alpha ):
  forall beta, beta t1< alpha -> succ beta t1< alpha.
Proof. 
  intros beta H0;  assert (H1 :succ beta t1<= alpha) by 
      (apply  LT_succ_LE; auto).
  destruct (LE_LT_eq_dec H1); auto.
  subst alpha; destruct  (@limitb_succ beta ); eauto with T1. 
Qed. 


Lemma succ_ocons alpha n beta : beta <> zero -> nf (ocons alpha n beta) -> 
                                succ (ocons alpha n beta) =
                                ocons alpha n (succ beta).
Proof.
  destruct alpha; cbn.
  - intros H H0; destruct H; apply nf_of_finite with n; auto. 
  - reflexivity.
Qed.


(* Demo *)

Example alpha_0 : T1 :=
  ocons (ocons (ocons zero 0 zero)
               0
               zero)
        0
        (ocons (ocons zero 2 zero)
               4
               (ocons zero 1 zero)).

Compute alpha_0.

(*
   = ocons omega 0 (ocons (FS 2) 4 (FS 1))
     : T1
 *)

Compute nf_b alpha_0.



Example alpha_0_eq : alpha_0 = phi0 omega  +
                               phi0 (fin 3)  * fin 5 +
                               fin 2.
Proof. reflexivity. Qed.




Lemma succ_rw1 : forall alpha n beta, alpha <> zero ->
                                      succ (ocons alpha n beta)=
                                      ocons alpha n (succ beta).
Proof.
  induction alpha.
  - destruct 1;auto.
  - cbn; auto. 
Qed.


Lemma succ_cons alpha i beta : alpha <> zero -> nf (ocons alpha i beta) ->
                               succ (ocons alpha i beta) =
                               ocons alpha i (succ beta).
  simpl.
  destruct alpha.
  - now destruct 1.
  - reflexivity.
Qed.

Example Ex1 :  fin 42 + omega = omega.
Proof. reflexivity. Qed.

Example Ex2 : limitb (omega ^ (omega + fin 5)).
Proof. reflexivity. Qed.



(**  **  An abstract syntax for ordinals in Cantor normal form *)
Declare Scope ppT1_scope.
Delimit Scope ppT1_scope with pT1.

Inductive ppT1 :=
| P_fin (_ : nat)
| P_add (_ _ : ppT1)
| P_mult (_ : ppT1) (_ : nat)
| P_exp (_ _ : ppT1)
| P_omega
.

Coercion P_fin : nat >-> ppT1. 

Notation "alpha + beta" := (P_add alpha beta) : ppT1_scope.

Notation "alpha * n" := (P_mult alpha n) : ppT1_scope.

Notation "alpha ^ beta" := (P_exp alpha beta) : ppT1_scope.

Notation _omega := P_omega.

Check (_omega ^ _omega * 2 + P_fin 1)%pT1.

Fixpoint pp0 (alpha : T1) : ppT1 :=
  match alpha with
  | zero => P_fin 0
  | ocons zero n zero => P_fin (S n)
  | ocons one 0 zero => _omega
  | ocons one 0 beta => (_omega + pp0 beta)%pT1
  | ocons one n zero => (_omega * (S n))%pT1
  | ocons one n beta => (_omega * (S n) + pp0 beta)%pT1
  | ocons alpha 0 zero => (_omega ^ pp0 alpha)%pT1
  | ocons alpha 0 beta => (_omega ^ pp0 alpha + pp0 beta)%pT1
  | ocons alpha n zero => (_omega ^ pp0 alpha * (S n))%pT1
  | ocons alpha n beta => (_omega ^ pp0 alpha * (S n) + pp0 beta)%pT1
  end.

Fixpoint eval_pp (e : ppT1) : T1 :=
  match e with
    P_fin 0 => zero
  | P_fin n => n       
  | P_add e f => ( (eval_pp e) +  (eval_pp f))%t1
  | P_mult e n => ( (eval_pp e) * (S n))%t1
  | P_exp e f => ((eval_pp e) ^ (eval_pp f))%t1
  | _omega   => T1.omega
  end.

Compute eval_pp (P_fin 4).


(* Coercion pp0 : T1 >-> ppT1. *)

Compute (pp0 (T1.omega ^ T1.omega * 2 + 1))%t1.


Fixpoint reassoc (exp : ppT1) (fuel :nat) : ppT1 :=
  match exp, fuel  with
  | exp, 0 => exp
  | P_add e (P_add f g), S n =>
    reassoc (P_add (P_add (reassoc  e n) (reassoc f n))
                   (reassoc g n)) n
  | P_add e f , S n =>  P_add (reassoc e n) (reassoc f n)
  | P_mult e i , S n=> P_mult (reassoc e n) i
  | P_exp e f , S n => P_exp (reassoc e n) (reassoc f n)
  | e, _=> e
  end.



Fixpoint p_size (exp : ppT1) : nat :=
  match exp with
    P_add e f |  P_exp e f => (S ((p_size e) + (p_size f)))%nat
  | P_mult e _ => S (p_size e)
  | _ => 1%nat
  end.

Definition pp (e: T1) : ppT1  := let t := pp0 e in reassoc t (p_size t).

Compute (pp (T1.omega ^ T1.omega * 2 + T1.omega ^ 5 + T1.omega +  1))%t1 .

Compute (pp (T1.omega ^(T1.omega ^ T1.omega * 2 + T1.omega ^ 5 +T1.omega +  1)))%t1 .

Compute pp T1.omega.

Eval simpl in  fun n:nat =>
                 (pp (T1.omega ^(T1.omega ^ T1.omega * n + T1.omega ^ n +T1.omega +  1)))%t1 .


Ltac is_closed alpha :=
  match alpha with
    zero => idtac
  | 0 => idtac
  | S ?n => is_closed n          
  |ocons ?a ?n ?b => is_closed a ; is_closed n ; is_closed b
  | ?other => fail
  end.

Ltac pp0tac alpha   :=
  match alpha with
  | zero => exact 0
  | ocons zero ?n zero => exact (S n)
  | ocons one 0 zero => exact omega%pT1
  | ocons one 0 ?beta => exact (omega + ltac :(pp0tac beta))%pT1
  | ocons one ?n zero => exact (omega * (S n))%pT1
  | ocons one ?n ?beta => exact (omega * (S n) + ltac: (pp0tac beta))%pT1
  | ocons ?alpha 0 zero => exact (omega ^ ltac: (pp0tac alpha))%pT1
  | ocons ?alpha 0 ?beta => exact (omega ^ ltac :(pp0tac alpha) + ltac: (pp0tac beta))%pT1
  | ocons ?alpha ?n zero => exact (omega ^ ltac: (pp0tac alpha) * (S n))%pT1
  | ocons ?alpha ?n ?beta => exact (omega ^ ltac: (pp0tac alpha) * (S n) + ltac : (pp0tac beta)%pT1)
                                   
  end.

Ltac pptac term :=
  let t := eval cbn in term
    in tryif is_closed t then exact (pp t) (* (ltac: (pp0tac t)) *)
      else exact term.   

Section essai.
  Variable n : nat.

  
  Compute  ltac: (pp0tac (ocons (ocons zero 0 zero) 3 zero)).
  Compute ltac: (pptac (ocons omega (S (S n)) (ocons omega (S n) 4))%t1).
  Compute ltac: (pptac (1 + omega * (S 6))).

End essai.


Check (phi0 (phi0 (FS 6))).

Compute pp ((phi0 10 * 3) * (phi0 7 * 8)).

Compute pp (3 * (omega + 5)).

Compute pp (3 * (omega * 7 + 15)).




