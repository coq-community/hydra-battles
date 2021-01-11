(**  Iteration of a function (similar to [Nat.iter]) *)

(** Pierre Castéran, Univ. Bordeaux and LaBRI *)


Open Scope nat_scope.
From Coq Require Import RelationClasses Relations Arith Max Lia.
From hydras Require Import Exp2.

Fixpoint iterate {A:Type}(f : A -> A) (n: nat)(x:A) :=
  match n with
  | 0 => x
  | S p => f (iterate  f p x)
  end.

(* tail recursive iterate *)

Fixpoint iterate_t {A:Type}(f : A -> A) (n: nat)(x:A) :=
  match n with
  | 0 => x
  | S p =>  (iterate_t  f p (f x))
  end.



(** ** Abstract properties of arithmetic functions *)

Definition nat_fun := nat -> nat.

Definition strict_mono f := forall n p,  n < p -> f n < f p.

Definition strict_mono1 f := forall n p,  0 < n < p -> f n < f p.

Definition dominates_from n g f  := forall p, n <= p -> f p < g p.

Definition dominates_strong g f  := {i : nat | dominates_from i g f}.

Definition dominates g f := exists i : nat, dominates_from i g f .

Definition fun_le f g  := forall n:nat,  f n <=  g n.

Definition good_fun f :=  strict_mono f /\ fun_le S f.

Infix ">>" := dominates (at level 60).

Infix ">>s" := dominates_strong (at level 60).

Infix "<<=" := fun_le (at level 60).




Lemma S_pred_rw (f : nat -> nat) : S <<= f ->
                                   forall x, S (Nat.pred (f x)) = f x.
Proof.
  intros H x; case_eq (f x).
  - intro H0. specialize (H x); rewrite H0 in H.
    inversion H.
  - reflexivity.
Qed.

Lemma iterate_t_rw {A}(f:A->A) : forall n x,
    iterate_t f n x = iterate f n x.
Proof.
 induction n; simpl; auto.
  intro; rewrite IHn.
  clear IHn; induction n; auto.
  cbn; now f_equal.
Qed.



Lemma fun_le_trans f g h : f <<= g ->  g <<= h -> f <<= h.
Proof. 
  intros; red; intro n; transitivity (g n); auto.
Qed.

Lemma mono_le f (Hf : strict_mono f) :  forall n, n <= f n.
Proof.
  induction n.
  - auto with arith. 
  -  apply Lt.le_lt_trans with (f n);  auto with arith.  
Qed.


Lemma mono_injective f (Hf : strict_mono f) :
  forall n p , f n = f p -> n = p.
Proof.
  intros n p H.
  destruct (PeanoNat.Nat.lt_total n p).
  - specialize (Hf _ _ H0);   rewrite H in Hf;  destruct (Lt.lt_irrefl _ Hf).
  -  destruct H0; trivial. 
     +  specialize (Hf _ _ H0); rewrite H in Hf; destruct (Lt.lt_irrefl _ Hf).
Qed.

Lemma mono_weak f (H: strict_mono f) :
  forall n p, n <= p -> f n <= f p.
Proof.
  induction 1.
  - left.
  - apply PeanoNat.Nat.lt_le_incl; apply H; auto with arith. 
Qed.


Lemma dominates_from_max :
  forall f g h i j, dominates_from  i g f  ->
                    dominates_from j  h g  ->
                    dominates_from  (Nat.max i j) h f .
Proof.
  intros f g h i j H H0 k Hk;  transitivity (g k).
  + apply H;  eauto with arith.
  + apply H0; eauto with arith.
Qed.

Lemma dominates_trans : forall f g h,  dominates g f ->
                                       dominates h g ->
                                       dominates h f.
Proof.
  intros f g h [i Hi] [j Hj]; exists (Nat.max i j);
    eapply dominates_from_max with g; eauto.
Qed.

Lemma dominates_trans_strong : forall f g h,
    dominates_strong g f ->
    dominates_strong h g ->
    dominates_strong h f.
Proof.
  intros f g h [i Hi] [j Hj];exists (Nat.max i j);
    eapply dominates_from_max with g; eauto.
Qed.


Lemma exp2_ge_S : S  <<= exp2.
Proof. 
  red; induction n. 
  - cbn; auto with arith. 
  - cbn;  abstract lia.
Qed.

Lemma exp2_mono : strict_mono exp2.
Proof.
  red; induction 1; cbn.
  - generalize (exp2_positive n); generalize (exp2 n);intros; abstract lia.
  - generalize IHle, (exp2_positive m); generalize (exp2 n), (exp2 m);
         intros;abstract lia.
Qed. 

(** ** Abstract properties of iterate *)

(** *** fixpoint rewriting *)

Lemma iterate_S_eqn {A:Type}(f : A -> A) (n: nat)(x:A):
  iterate f (S n) x = f (iterate f n x).
Proof. reflexivity.  Qed.


(** *** Equation associated with tail recursion *)

Lemma iterate_S_eqn2 {A:Type}(f : A -> A) (n: nat)(x:A):
  iterate f (S n) x =  (iterate f n (f x)).
Proof.
  induction n. 
  - reflexivity.
  - rewrite (iterate_S_eqn f (S n)), IHn;  reflexivity. 
Qed.


Lemma iterate_rw {A} {f : A -> A} n  :
  forall x, iterate f  (S n)  x = iterate f n (f x).
Proof.
  simpl; induction n.
  - reflexivity. 
  -  intros; simpl; now f_equal. 
Qed.

(* rename ! *)

Lemma iterate_compat {A} (f : A -> A) n :
  forall x, iterate f n x = Nat.iter n f x.
Proof. 
  induction n.
  - reflexivity.  
  - simpl; intros; now rewrite IHn.
Qed.

Lemma iterate_ext {A:Type}(f g: A -> A) (H: forall x, f x = g x):
  forall n x, iterate f n x = iterate g n x.
  induction n; simpl; auto.
  intro; rewrite IHn. now rewrite H.
Qed.

Lemma iterate_ext2 {A:Type} (f g : (A ->A)->A -> A)
      (h i : A->A) : (forall x, h x = i x) ->
                     (forall h' i',  (forall x, h' x = i' x) ->
                                     forall x, f h' x = g i' x) ->
                     forall n x, iterate f n h x = iterate g n i x.
Proof.
  induction n.
  - intros; simpl; auto.
  - intros; simpl; apply H0. auto.
Qed.

  
Lemma iterate_le f (Hf : strict_mono f) :
  forall i j, i <= j -> forall z, iterate f i z <= iterate f j z.
Proof.
  induction 1.
  - trivial.   
  - intros; rewrite iterate_S_eqn.
    transitivity (iterate f m z); auto. 
    apply mono_le; auto. 
Qed.



Lemma iterate_lt  f (Hf : good_fun f):
  forall i j, i < j -> forall z, iterate f i z < iterate f j z.
Proof.
  destruct Hf as [H H0]; induction 1.
  - intros; rewrite iterate_S_eqn; auto.
  - intros; rewrite iterate_S_eqn.
    transitivity (iterate f m z); auto. 
Qed.

Lemma iterate_mono_weak (f: nat -> nat):
  (forall x,  x <= f x) ->
  forall n x,  iterate f n x <= iterate f (S n)  x.
Proof.
  induction n.
  - cbn; auto with arith.
  - cbn; intros; apply H.
Qed.

Lemma iterate_mono_weak_2 (f: nat -> nat):
  (forall x,  (x <= f x)%nat) ->
  forall n p x,  (n <= p -> iterate f n x <= iterate f p x)%nat.
Proof.
  induction 2.
  -  reflexivity.
  - transitivity (iterate f m x); auto.
    apply iterate_mono_weak; auto.
Qed.

Lemma iterate_mono2 (f: nat -> nat):
  (forall x y,  x <= y -> f x <= f y)%nat ->
  forall n x y,  (x <= y -> iterate f n x <= iterate f n y)%nat.
Proof.
induction n.
 - simpl; trivial.
 - simpl; intros; now apply H, IHn.
Qed.


Lemma iterate_mono f (Hf : strict_mono f) (Hf' :  S  <<= f):
  forall n, strict_mono (iterate f n).
Proof.
  induction n.
  -  red; intro i; cbn;auto.
  - cbn; intros i j H;  apply Hf;auto.
Qed.

Lemma iterate_ge : forall f , S  <<= f -> 
                              forall  j n, j <= iterate f n j.
Proof.
  induction n.
  - cbn; auto with arith.
   -  apply PeanoNat.Nat.lt_le_incl;rewrite iterate_S_eqn;
        apply PeanoNat.Nat.le_lt_trans with (iterate f n j); auto.
Qed.


Lemma iterate_Sge f j : S <<= f -> S <<= iterate f (S j).
Proof.
  intros h x; rewrite iterate_rw.
   transitivity (f x).                      
    -  apply h.
    - now apply iterate_ge.
Qed.

Lemma iterate_ge' : forall f,  id <<= f ->
                               forall n j, 0 < n -> j <= iterate f n j.
Proof.
  induction n.
  - inversion 1.
  - intros; destruct n.
    + simpl; apply H.
    +  transitivity (iterate f (S n) j).
       * apply IHn; auto with arith.
       * simpl; apply H.
Qed.

Lemma iterate_ge'' f : id <<= f -> strict_mono f -> forall i k,
      k <= Nat.pred (iterate (fun z => S (f z)) (S i) k).
Proof.
  induction i.
  -  intros; cbn ; apply H.
  - intros;  rewrite iterate_rw;
    apply le_trans with
        (Nat.pred (iterate (fun z : nat => S (f z)) (S i) k)).
    + auto.
    + cbn;  assert (H1: strict_mono (fun z => S (f z))).
   { intros x y Hlt; apply H0 in Hlt;  auto with arith. }
   generalize  (iterate_mono _ H1).
   assert (H2: S <<= (fun z : nat => S (f z))).
   { intro x; auto with arith.
     specialize (H x); auto with arith.
   }   intros H3;  specialize (H3 H2 i).
   apply Nat.lt_le_incl.
   assert (H4: k < S (f k)).
   { apply le_lt_trans with (f k).
     - apply H.                       
     - auto with arith.
   }
   specialize (H3 _ _ H4); auto.
Qed.

Lemma strict_mono_iterate_S f :
  strict_mono f -> id <<= f ->
  forall i,  strict_mono
               (fun k =>  Nat.pred (iterate (fun z => S (f z)) (S i) k)).
Proof.
  intros Hmono Hle; induction i.
  - cbn; apply Hmono.
  -  intros k l Hlt.
    assert (H: k <= Nat.pred (iterate (fun z : nat => S (f z)) (S (S i)) k))
    by (apply iterate_ge''; auto).
    assert (H0: k < iterate (fun z : nat => S (f z)) (S (S i)) k).
    { 
      replace k with (iterate (fun z => S (f z)) 0 k) at 1.
      -  apply iterate_lt.
        + split.
          *  intros x y Hxy; specialize (Hmono _ _ Hxy); auto with arith.
          *  intros x; auto with arith; specialize (Hle x); auto with arith.
        + auto with arith.
      - reflexivity. 
    }
    rewrite <-  Nat.pred_lt_mono.
    + apply iterate_mono.
      * intros x y Hxy; specialize (Hmono _ _ Hxy); auto with arith.
      * intros x; specialize (Hle x); auto with arith.
      * auto. 
    +  intro H1; rewrite H1 in H0; inversion H0.
Qed.


Lemma iterate_mono_1 (f g: nat_fun) (k:nat) (Hf: strict_mono f)
      (Hf' : S <<= f)
      (H : forall n, k <= n -> f n <= g n) :
  forall i n, k <= n -> iterate f i n <= iterate g i n.
Proof. 
  induction i. 
  - simpl; auto with arith. 
  - intros; repeat rewrite iterate_S_eqn. 
    transitivity (f (iterate g i n)); auto. 
    + apply mono_weak; auto. 
    + apply H; transitivity (iterate f i n); [ | auto].
      * induction H0.
        -- clear IHi;  induction i. 
       ++ simpl; auto with arith. 
       ++  rewrite iterate_S_eqn. 
           transitivity (iterate f i k).
           **  auto. 
           **  apply Nat.lt_le_incl; auto. 
        --  transitivity (S m).
            ++ auto with arith. 
            ++ apply iterate_ge; auto. 
Qed.

Lemma iterate_dom_prop :
  forall f g i (Hgt : S <<= f)
         (Hm : strict_mono f) (Hm': strict_mono g),
    dominates_from i g f ->
    forall k, 0 < k -> dominates_from i (iterate g k) (iterate f k).
Proof.
  induction k.
  -   intro H0; inversion H0.
  -   destruct k.
      +   simpl;  intros _ l Hl;  apply H; auto.
      +   intros _ l Hl; repeat rewrite iterate_S_eqn.
          transitivity (g (f (iterate f k l))).
          *   apply H; transitivity (f l).
              {   transitivity l;  auto. 
                  apply PeanoNat.Nat.lt_le_incl.
                  eapply Hgt; auto.
              }
              apply mono_weak;  auto.
              eapply iterate_ge;  auto. 
          *  apply Hm';  assert (0 < S k)%nat by auto with arith.
             apply IHk in H0; specialize (H0 l).
             repeat rewrite iterate_S_eqn in H0; auto.   
Qed.

Lemma dominates_from_le  i j g f : i <= j ->
                                   dominates_from i g f -> 
                                   dominates_from j g f .
Proof. 
  induction 1; auto.
  intros H0 x H1; apply IHle; auto.
  auto with arith.
Qed.



Lemma smono_Sle f : f 0 <> 0 -> strict_mono f -> S <<= f.
Proof.
  intros H H0 x; induction x.
  - destruct (f 0).
    + now destruct H.
    + auto with arith.
  - apply le_lt_trans with (f x).
    + auto.
    + apply H0; auto with arith.
Qed.

(* Iterating a functional *)

Lemma iterate_2_mono (f : (nat->nat)->(nat->nat)):
   (forall g, strict_mono g -> S <<= g -> strict_mono (f g))->
   (forall g, strict_mono g -> S <<= g -> S <<=  (f g))->
   forall k g x  y,  strict_mono g -> S <<= g ->
                     (x < y)%nat ->
                     (iterate f k g x < iterate f k g y)%nat.
  Proof.
   induction k.
   - simpl; intros; apply (H1 _ _ H3); auto.
   -  intros; rewrite iterate_S_eqn2.
      apply (IHk (f g) x y ); auto.
Qed.

Lemma iterate_2_mono_weak (f : (nat->nat)->(nat->nat)):
   (forall g, strict_mono g -> S <<= g -> strict_mono (f g))->
   (forall g, strict_mono g -> S <<= g -> S <<=  (f g))->
   forall k g x  y,  strict_mono g -> S <<= g ->
                     (x <= y)%nat ->
                     (iterate f k g x <= iterate f k g y)%nat.
Proof.
  intros; destruct (le_lt_or_eq x y H3).
  -  apply Nat.lt_le_incl.
     apply iterate_2_mono; auto.
  - now subst.
Qed.


Lemma iterate2_mono3 (phi  : (nat->nat)->(nat->nat)) :
  (forall g, strict_mono g -> S <<= g ->
             strict_mono (phi g) /\ S <<= phi g)->
  (forall (f g : nat -> nat), strict_mono f -> S <<= f  ->
                              strict_mono g -> S <<= g ->
                              ((forall x, f x <= g x) ->
                               forall x, phi f x <= phi g x)) ->
  forall g h,  strict_mono g -> S <<= g -> strict_mono h -> S <<= h ->
             (forall x,  g x <= h x) ->
  forall k x y,  x <= y -> 
                 iterate phi k  g x <= iterate phi k h y.
Proof.
  intros; revert k x y H6.
  assert (H6: forall k, strict_mono (iterate phi k h) /\
                        S <<= iterate phi k h).
  {
    intro k; induction k.
    - simpl; split; auto.
    - destruct IHk; split.
      + simpl; destruct (H (iterate phi k h)); auto. 
      + simpl; destruct (H (iterate phi k h)); auto.
  }  
  assert (H7: forall k, strict_mono (iterate phi k g) /\
                        S <<= iterate phi k g). {
    { intro k; induction k.
      - simpl; split; auto.
      - destruct IHk; split.
        + simpl; destruct (H (iterate phi k g));  auto.
        +  simpl;  destruct (H (iterate phi k g)); auto.
    }
  }
  induction k.
  - simpl; intros; transitivity (g y).
    +  apply mono_weak; auto.
    +  auto.
  -   intros; repeat rewrite iterate_S_eqn;
        transitivity (phi (iterate phi k h) x).
      +  apply H0.
         * destruct (H7 k); auto.
         * destruct (H7 k); auto.
         * destruct (H6 k); auto.
         * destruct (H6 k); auto.
         * intro; apply IHk; auto with arith.
      + clear IHk; destruct (H6 k).
        destruct  (H (iterate phi k h) H9 H10);  apply mono_weak; auto.
Qed.


Lemma iterate_2_mono2 (phi psi : (nat->nat)->(nat->nat)):
  (forall g, strict_mono g -> S <<= g -> strict_mono (phi g))->
  (forall g, strict_mono g -> S <<= g -> S <<=  (phi g))->
  (forall g, strict_mono g -> S <<= g -> strict_mono (psi g))->
  (forall g, strict_mono g -> S <<= g -> S <<=  (psi g))->
  (forall g x ,  good_fun g  -> phi g x <= psi g x) ->
  (forall f g, strict_mono f -> strict_mono g -> S <<= f -> S <<= g ->
               (forall x, f x <= g x) -> (forall x, psi f x <= psi g x)) ->
  forall k g x  y,  strict_mono g -> S <<= g ->
                    (x <= y)%nat ->
                    (iterate phi k g x <= iterate psi k g y)%nat.
Proof.
  induction k.
  -  simpl;  intros;  destruct (le_lt_or_eq _ _ H7).
     + apply Nat.lt_le_incl.
       apply H5; auto.
     + subst; auto.
  -  intros;  repeat rewrite iterate_S_eqn2.
    transitivity (iterate psi k (psi g) x).
    +   specialize (IHk (phi g) x x (H g H5 H6) (H0 g H5 H6)).
        transitivity (iterate psi k (phi g) x).
        * apply IHk; auto.
        * apply iterate2_mono3; auto.
          --  intros; apply H3; auto.
              now split.
    + apply iterate2_mono3; auto.
Qed.


(**  ** Ackermann stuff  *)

Fixpoint Ack (m:nat) : nat -> nat :=
  match m with 0 => S
          |   S n => fun k =>  iterate (Ack n) (S k) 1
  end.

(** *** Equations (from wikipedia) *)

Lemma Ack_0 : Ack 0 = S.
Proof refl_equal.

Lemma Ack_S_0 m : Ack (S m) 0 = Ack m 1.
Proof.  now simpl. Qed.

Lemma Ack_S_S : forall m p,
    Ack (S m) (S p) = Ack m (Ack (S m) p).
Proof.  now simpl. Qed.


Definition phi_Ack (f : nat -> nat) (k : nat) :=
       iterate f (S k) 1.

Definition phi_Ack' (f : nat -> nat) (k : nat) :=
       iterate f  k (f 1).

Lemma phi_Ack'_ext f g: (forall x, f x = g x) ->
                        forall p,  phi_Ack' f p = phi_Ack' g p.
Proof.
  induction p.      
  -  cbn; auto.
  -  cbn;  unfold phi_Ack' in IHp;  rewrite IHp;  apply H.
Qed.

Lemma phi_phi'_Ack : forall f k,
    phi_Ack f k = phi_Ack' f k.
Proof.
  unfold phi_Ack, phi_Ack'; intros.
  now rewrite iterate_S_eqn2.
Qed.

Lemma Ack_paraphrase : forall m ,  Ack m  =
                                    match m with
                                    | 0 => S 
                                    | S p =>  phi_Ack  (Ack p) 
                                    end.
Proof.
  destruct m; reflexivity.
Qed.

Lemma Ack_paraphrase' : forall m k,  Ack m  k=
                                    match m with
                                    | 0 => S k
                                    | S p =>  phi_Ack'  (Ack p) k
                                    end.
Proof.
  destruct m.
  -   reflexivity.
  - intro k; rewrite <- phi_phi'_Ack; reflexivity.
Qed.

Lemma Ack_as_iter' : forall m p, Ack m p = iterate phi_Ack' m S p.
Proof.
  induction  m.
  - reflexivity.
  -intro p; rewrite Ack_paraphrase', iterate_S_eqn.
   apply phi_Ack'_ext; auto.
Qed.


Lemma Ack_as_iter : forall m , Ack m  = iterate phi_Ack m S.
Proof.
  induction  m.
  - reflexivity.
  - rewrite Ack_paraphrase, iterate_S_eqn;  now rewrite IHm.
Qed.

Lemma exp2_as_iterate n : exp2 n = iterate (fun i => 2 * i)%nat n 1.
Proof.
  induction  n.
  - reflexivity.
  - rewrite iterate_S_eqn; simpl exp2; rewrite <- IHn; abstract lia.
Qed.


Definition hyper_exp2 k := iterate exp2 k 1.


