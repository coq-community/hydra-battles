(** Pierre Castéran, inspired   from Sladek's paper "The Termite and the Tower"
 *)
(** Old stuff 
*)

Require Import ArithRing Lia   Max.

Definition id_nat (n:nat) := n.

Fixpoint iterate {A:Type}(f : A -> A) (n: nat)(x:A) :=
  match n with
      0 => x
    | S p => f (iterate  f p x)
  end.


Lemma iterate_S_eqn {A:Type}(f : A -> A) (n: nat)(x:A):
  iterate f (S n) x = f (iterate f n x).
Proof. reflexivity.  Qed.

Definition mono (f: nat -> nat) :=
  forall n p,  n < p -> f n < f p.

Lemma mono_le f (Hf : mono f) :
  forall n, n <= f n.
  induction n.
  auto with arith.   
  apply Lt.le_lt_trans with (f n).
  auto. 
  apply Hf.
  auto with arith. 
Qed. 


Lemma iterate_le f (Hf : mono f) :
  forall x y, x <= y -> forall z, iterate f x z <= iterate f y z.
  induction 1.
  auto.
  intros.
  rewrite iterate_S_eqn.
  transitivity (iterate f m z); auto. 
  apply mono_le.
  auto. 
Qed.

Lemma mono_weak f (H: mono f) :
  forall n p, n <= p -> f n <= f p.
Proof.
  induction 1.
  left.
  auto.
   transitivity (f m); auto.
   Search lt le.
  apply PeanoNat.Nat.lt_le_incl; apply H;auto.
Qed.

Definition dominates_from i g f  := forall j, i <= j -> f j < g j.

Definition dominates_strong g f  := {i : nat | dominates_from i g f}.

Definition dominates g f := exists i : nat, dominates_from i g f .


Infix ">>" := dominates (at level 60).

Infix ">>s" := dominates_strong (at level 60).



Lemma dominates_from_max :
  forall f g h i j, dominates_from  i g f  -> dominates_from j  h g  ->
                    dominates_from  (max i j) h f .
Proof.
  intros f g h i j H H0 k Hk;  transitivity (g k).
  +  apply H; eauto with arith.
  + apply H0; eauto with arith.
Qed.


Lemma dominates_trans : forall f g h,  dominates g f ->
                                       dominates h g ->
                                       dominates h f.
Proof.
  intros f g h [i Hi] [j Hj]; exists (max i j);
  eapply dominates_from_max with g; eauto.
Qed.

Lemma dominates_trans_strong : forall f g h,
                                 dominates_strong g f ->
                                 dominates_strong h g ->
                                 dominates_strong h f.
Proof.
  intros f g h [i Hi] [j Hj];exists (max i j);
  eapply dominates_from_max with g; eauto.
Qed.



Definition Fsuc F := fun n => iterate F (S n) n.


Fixpoint  iterates F i := match i with
                              0 => F
                            | S i =>  Fsuc (iterates F i)
                          end.


Definition F_ i := iterates S i.

Definition F_omega i := F_ i i.


(*
Fixpoint  F_ i n :=
  match i with
    | 0 => S  n
    | S j => iterate  (F_  j) (S n)  n
  end.
 *)

Lemma F_S_rw : forall i n, F_ (S i) n = iterate (F_ i) (S n) n.
Proof.   reflexivity. Qed.

Lemma F0_Id : dominates_from  0 (F_ 0) id_nat.
Proof.
  intros i Hi; simpl; auto with arith. 
Qed.



Lemma iterate_mono f (Hf: mono f) : forall n,
                                      mono (iterate f n).
Proof.
  induction n.
  -  red; intro i; cbn;auto.
  - cbn; intros i j H;  apply Hf;auto.
Qed.

Lemma F1_F0_2 : dominates_from 2 (F_ 1) (F_ 0).
Proof.
  intros i Hi; rewrite F_S_rw; cbn.  
  pattern i at 2; generalize Hi; induction 1.
  - cbn; auto with arith. 
  -  Locate succ_lt_mono. rewrite <- PeanoNat.Nat.succ_lt_mono.
     cbn.
     
     transitivity    (S (iterate (fun n : nat => S n) m m )); auto.
     rewrite <- PeanoNat.Nat.succ_lt_mono.
     apply iterate_mono.  
     + intros x y Hxy;auto with arith.
     + auto with arith. 
Qed.

Corollary  F1_F0 : dominates_strong (F_ 1) (F_ 0).
Proof. exists 2; apply F1_F0_2. Defined.

Definition f_gt_from i f :=dominates_from i f id_nat.
Definition f_gt f := f >> id_nat.


Lemma mono_f_gt_0 f : mono f -> 0 < f 0 ->
                      f_gt_from 0 f.
  intros H H0 i _.
  induction i.
  assumption. 
  apply Lt.le_lt_trans with (f i).
   unfold id_nat; auto with arith.
   apply H. auto with arith.
Qed.


Lemma f_gt_from_le  i j f : i <= j -> f_gt_from i f -> 
                            f_gt_from j f.
  induction 1.
  auto. 
  intros H0 x.
  intro. apply IHle.
  auto.
  auto with arith. 
Qed.

Lemma mono_f_gt f i : mono f -> 0 < f 0 -> f_gt_from i f.
Proof.                    
  intros; apply f_gt_from_le with 0.
  - auto with arith. 
  - now apply mono_f_gt_0.
Qed.


Lemma iterate_ge : forall f i, f_gt_from i f -> 
                               forall  j, i <= j ->
                                          forall n,
                                            j <= iterate f n j.
Proof.
  induction n.
  cbn.
  auto with arith.
  apply PeanoNat.Nat.lt_le_incl.
  rewrite iterate_S_eqn.
  apply Lt.le_lt_trans with (iterate f n j).
  auto.
  apply H.
  apply Le.le_trans with j.
  auto.
  auto.
Qed.  

Lemma dominates_iterate :
  forall  i f,
    f_gt_from i f ->
    mono f ->
    forall n,
      {j:nat | i<= j /\ f_gt_from j (iterate f (S n))}.

  induction n.
  exists i.
  split;auto.
  destruct IHn as [j [H1 H2]].
  exists j.
  split;auto.
  red in H2; red.
  intros k Hk.
  unfold id_nat.
  rewrite iterate_S_eqn.
  apply Lt.le_lt_trans with (f (iterate f n k)).
  apply Le.le_trans with  (iterate f n k).
  apply iterate_ge with i.
  auto.
  eauto with arith.
  apply PeanoNat.Nat.lt_le_incl.
  apply H.
  apply Le.le_trans with k. eauto with arith.
  apply iterate_ge with i.
  auto. 
  eauto with arith. 
  apply H0.
  rewrite iterate_S_eqn.
  apply H.
  
  apply Le.le_trans with  k.
  eauto with arith. 
  apply iterate_ge with i.
  auto. 
  eauto with arith. 
Defined.


Corollary iterate_gt_diag' :
  forall  i f,
    f_gt_from i f ->
    mono f ->
    forall n, 0 < n -> 
              {j:nat | i<= j /\ f_gt_from j (iterate f n)}.
Proof.
  intros.
  destruct n.
  elimtype False.
  inversion H1.
  apply dominates_iterate; auto.
Defined.

Corollary iterate_ge_diag' :
  forall  i f,
    f_gt_from i f ->
    mono f ->
    forall n, 
      {j:nat | i<= j /\ forall k, j<= k -> k <= iterate f n k}.
Proof.
  intros.
  destruct n.
  exists i.
  split;auto. 
  exists i.
  split. 
  auto.
  intros.
  red in H.
  red in H.
  generalize  (H k H1); intros.
  
  unfold id_nat in H2, H.
  rewrite iterate_S_eqn.   
  apply PeanoNat.Nat.lt_le_incl.
  apply Lt.lt_le_trans with (f k).
  auto.
  apply mono_weak.
  auto.

  eapply   iterate_ge with i.
  red. 
  red. unfold id_nat.
  apply H.
  auto. 
Qed.

Lemma iterate_dom_prop :
  forall f g i (Hgt : f_gt_from i f)
         (Hm : mono f) (Hm': mono g),
    dominates_from i g f ->
    forall k, 0 < k ->
              dominates_from i (iterate g k) (iterate f k).
  induction k.
  intro H0; inversion H0.
  destruct k.
  simpl.
  intros _ l Hl.
  apply H; auto.
  intros _ l Hl; repeat rewrite iterate_S_eqn.
  transitivity (g (f (iterate f k l))).
  apply H.
  transitivity (f l).
  transitivity l.
  auto. 
  apply PeanoNat.Nat.lt_le_incl.
  eapply Hgt; auto.
  apply mono_weak.
  auto.
  
  eapply iterate_ge with i.
  auto. 
  auto. 
  apply Hm'.
  assert (0 < S k) by auto with arith.
  specialize (IHk H0 l Hl).
  repeat rewrite iterate_S_eqn in IHk.   auto.
Qed. 


Lemma F_gt_0 :  f_gt (F_ 0).
Proof.
  exists 0;  intro x; cbn; auto with arith.
Qed. 


Lemma mono_F0 : mono (F_ 0).
Proof.
  red;intros; cbn; auto with arith.
Qed.



Lemma LF0 : forall n,  F_ 0 n = S n.
Proof. reflexivity. Qed.


Lemma LF0' : forall i j, iterate (F_ 0) i j = (i + j).
Proof. 
  induction i.
  -   reflexivity.
  -  intro; cbn;  f_equal; auto. 
Qed.


Lemma LF1 : forall n,  F_ 1 n = S (2 * n).
Proof.
  intro;  cbn;   rewrite LF0'; ring.
Qed. 


Fixpoint exp2 (n:nat) : nat :=
  match n with
      0 => 1
    | S i => 2 * exp2 i
  end.


Lemma exp2_positive : forall i, 0 < exp2 i.
Proof.
  induction i.
  - cbn; auto with arith.
  - cbn; lia.
Qed.


Lemma LF1' : forall i j, exp2 i * j < iterate (F_ 1) (S i) j .
Proof.
  induction i.
  - cbn.  intros; cbn. ring_simplify.  rewrite LF0'.
    lia.
  - intros.
    simpl exp2.  ring_simplify.
    simpl (2+i).
    rewrite iterate_S_eqn.
    rewrite LF1.
    specialize (IHi j).
    rewrite Mult.mult_assoc_reverse.
    generalize IHi; generalize  (exp2 i * j);
    generalize  (iterate (F_ 1) (S i) j).  
    clear IHi. intros. lia.
Qed.

Lemma LF2 :  F_ 2  >>s  (fun i => exp2 i * i).
Proof.
  exists 0; red; intros; apply LF1'.
Qed.



Lemma minoration : F_ 2 >>s exp2.
  eapply  dominates_trans_strong.
  2: eapply LF2.
  exists 2.
  intros i.
  induction 1.
  compute.
  auto with arith.
  simpl. 
  rewrite <- mult_n_Sm.
  ring_simplify.
  rewrite Mult.mult_assoc_reverse.
  generalize IHle; generalize  (exp2 m * m); generalize (exp2 m).

  clear IHle.
  intros.  lia. 
Qed. 


Section step. 
  Variable i : nat.
  Hypothesis Hi : F_ i >>s id_nat.
  Hypothesis Hi' : mono (F_ i).


  Let n := proj1_sig Hi.

  Remark R: forall j, n <= j -> j < F_ i j.
  Proof.
    pattern n.
    apply proj2_sig.
  Qed.

  Lemma dom_dom:  F_ (S i) >>s F_ i.
    exists (S n).
    intros p Hp.
    
    rewrite F_S_rw.
    pattern p at 2; generalize Hp; induction 1.
    rewrite iterate_S_eqn.
    
    cbn.
    apply Hi'.
    apply Lt.lt_le_trans with (F_ i (S n)).
    apply R.
    auto with arith.

    apply mono_weak;auto.
    assert (f_gt (F_ i)).
    exists n.
    red.
    apply R.
    apply iterate_ge with n.
    pattern n; apply proj2_sig.
    auto with arith. 
    rewrite (iterate_S_eqn).
    apply Hi'.
    rewrite (iterate_S_eqn).
    apply Lt.le_lt_trans with (iterate (F_ i) m (S m)).
    apply iterate_ge with n.
    pattern n; apply proj2_sig.
    auto with arith.
    assert (forall l, n <= l -> l < F_ i l).  
    pattern n; apply proj2_sig.
    apply H.
    apply Le.le_trans with (S m).
    auto with arith.
    apply iterate_ge with n.
    pattern n; apply proj2_sig.
    auto with arith.
  Qed.


  Lemma mono_mono : mono (F_ (S i)). 
    intros x y Hxy.
    repeat rewrite F_S_rw.
    generalize (iterate_mono _ Hi' (S x)).
    intro. 
    red in H.
    specialize (H x y Hxy).
    apply Lt.lt_le_trans with (iterate (F_ i) (S x) y).
    auto. 
    clear H.
    apply iterate_le.
    auto. 
    auto with arith.
  Qed.

End step. 


Lemma big_induction : forall i,
                        (mono (F_ i) *  (F_ (S i) >>s F_ i) *
                         (F_ i >>s id_nat))%type.
  induction i. 
  repeat split.
  apply mono_F0.
  exists 1.
  intros x Hx; rewrite LF1, LF0.
  lia.
  exists 0.
  intros x Hx.
  simpl.
  unfold id_nat;auto with arith.
  destruct IHi as [[X Y] Z];repeat split.
  apply mono_mono;auto. 
  apply dom_dom;auto. 
  eapply dominates_trans_strong; eauto.
  apply mono_mono;auto. 
  eapply dominates_trans_strong; eauto.
Defined.

Theorem Le_thm : forall i:nat, F_ (S i) >>s F_ i.
Proof.
  intro i; destruct (big_induction i) as [[_ p] _]; auto.
Defined.


Fixpoint roofed_tower (n top: nat) :=
  match n with
      0 => top
    | S p => exp2 (roofed_tower p top )
  end.


Lemma L2 : forall n t, iterate exp2 n t = roofed_tower n t.
  induction n;simpl; auto.
Qed.



Lemma exp2_mono : mono exp2.
  red.
  induction 1.
  simpl. 
  generalize (exp2_positive n). generalize (exp2 n).
  intros; lia.
  cbn.
  generalize IHle, (exp2_positive m). generalize (exp2 n), (exp2 m).
  intros; lia.
Qed. 


Lemma L3 : forall x,
              dominates_from x (F_ 2) exp2 ->
              forall k,
                0 < k ->
                dominates_from x 
                               (iterate (F_ 2)  k)
                               (iterate exp2 k).
  intros x Hx.
  intros; 
    apply iterate_dom_prop; auto.
  red;intros.
  intros i Hi.
  unfold id_nat.
  clear Hi.
  induction i.
  cbn;auto with arith.
  cbn.
  generalize IHi; generalize (exp2 i).
  intros; lia. apply exp2_mono.
  destruct (big_induction 2).
  destruct p;auto.
Qed.



Lemma dominates_from_le  i j g f : i <= j ->
                                   dominates_from i g f -> 
                                   dominates_from j g f .
  induction 1; auto.
  intros H0 x.
  intro. apply IHle.
  auto.
  auto with arith.
Qed. 

Lemma exp2_gt_id : forall n, n < exp2 n.
  induction n.
  cbn; auto with arith.
  cbn.
  generalize IHn; generalize (exp2 n).
  intros; lia.
Qed.

(* Simplifier cette preuve ! *)
Lemma LF3 : F_ 3 >>s (fun  n => iterate exp2 n n).
  
  red.
  destruct minoration as [x Hx].
  assert  (F_ 2 >>s id_nat).
  destruct (big_induction 2);   auto.
  case H; intros;  exists (max x0 (max x 1)).
  red; intros.
  assert (dominates_from j (F_ 2) exp2).
  { 
    intros k Hk; apply Hx.
    transitivity j;  eauto with arith.
  }
  generalize (L3 j H1).
  intros.
  specialize (H2 j).
  assert (0 < j) by   eauto with arith.
  specialize (H2 H3).
  rewrite F_S_rw.
  apply Lt.le_lt_trans with ( iterate (F_ 2)  j j).
  generalize  (iterate_dom_prop  exp2 (F_ 2) j);  intro.
  assert (f_gt_from j (F_ 2)).
  {   apply  f_gt_from_le with x0;  eauto with arith.
  }
  assert (mono (F_ 2)).
  {  destruct (big_induction 2);   now destruct p. }
  assert (dominates_from j  (F_ 2) exp2).
  {  assert (f_gt_from j exp2) .
    {  apply f_gt_from_le with 0.
       auto with arith. 
       intros z _.
       apply exp2_gt_id.
    }
    specialize (H4 H7 exp2_mono H6 H1 j);  auto.
  }
  apply PeanoNat.Nat.lt_le_incl;  eapply H4; auto.
  apply f_gt_from_le with 0;   auto with arith. 
  intros z _;  apply exp2_gt_id.
  apply exp2_mono;  auto.
  rewrite iterate_S_eqn.
  apply d.
  transitivity j.
  eauto with arith. 
  apply iterate_ge with j; auto.
  apply f_gt_from_le with x0; auto. 
  eauto with arith. 
Qed.

