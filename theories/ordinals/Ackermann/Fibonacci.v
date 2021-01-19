Require Import primRec cPair extEqualNat.

Compute cPair 2 3.

Definition fib_step_cPair p := cPair (cPairPi1 p + cPairPi2 p)
                                     (cPairPi1 p).




Definition fib_cPair n :=  cPairPi2 (nat_rec (fun _ => nat)
                                             (cPair 1 1)
                                             (fun _ p => fib_step_cPair p)
                                             n).

Definition fib_step (p: nat * nat) := (fst p + snd p, fst p).

Definition fib_iter n :=snd  (nat_rec (fun _ => (nat*nat)%type)
                                      (1,1)
                                      (fun _ p => fib_step p)
                                      n).

Compute fib_iter 10.

Definition inv (p: nat*nat) (c: nat) :=  c = cPair (fst p) (snd p).

Lemma inv_Pi : forall p c, inv p c ->  snd p = cPairPi2 c.
Proof. 
  intros.
  unfold inv in H.
  subst.
  now rewrite cPairProjections2.
Qed.

Lemma L0: inv (1,1) (cPair 1 1).
Proof. reflexivity. Qed.

Lemma LS : forall p c,  inv p c -> inv (fib_step p) (fib_step_cPair c).
Proof.
  destruct p; intros.
  unfold inv in *. simpl fst  in *. simpl snd in *.
  unfold fib_step_cPair.
  subst.
  SearchRewrite (cPairPi1 (cPair _ _)).
  now rewrite cPairProjections1, cPairProjections2.
Qed.

Lemma L1 : forall  p c,
    inv p c -> forall n,
      inv (nat_rec (fun _ => (nat*nat)%type)
                   p
                   (fun _ p => fib_step p)
                   n)
          (nat_rec (fun _ => nat)
                   c
                   (fun _ p => fib_step_cPair p)
                   n).
  induction n.      
  - cbn; assumption.
  - cbn. apply LS. assumption. 
Qed.



Check fun (n: nat) =>  inv_Pi _ _ (L1 _ _ L0 n).

Lemma OK : extEqual 1 fib_iter fib_cPair.
Proof.
  intro n;  apply  (inv_Pi _ _ (L1 _ _ L0 n)).
Qed.

Lemma fib_cPairIsPR: isPR 1 fib_cPair.
  unfold fib_cPair.
  apply compose1_1IsPR.
  apply indIsPR.
  unfold fib_step_cPair.
  apply filter01IsPR.
  apply compose1_2IsPR.
  apply compose1_1IsPR.
  apply idIsPR.
  apply compose1_2IsPR.
  apply cPairPi1IsPR.
  apply cPairPi2IsPR.
  apply plusIsPR.
  apply cPairPi1IsPR.
  apply cPairIsPR.
  apply cPairPi2IsPR.
Qed.


Lemma fib_iterIsPR : isPR 1 fib_iter.
  generalize fib_cPairIsPR.
  destruct 1 as [x Hx].
  exists x.
  apply extEqualTrans with fib_cPair.
  auto.
  apply extEqualSym.
  apply OK.
Qed.


Fixpoint fib (n:nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | S ((S p) as q) => fib q + fib p
  end.

Lemma fib_OK0 : forall n,
    (nat_rec (fun _ => (nat*nat)%type)
             (1,1)
             (fun _ p => fib_step p)
             n) = (fib (S n), fib n).
  induction n; simpl.
  auto.
  destruct n.
  cbn.  reflexivity.
  rewrite IHn.
  unfold fib_step.
  simpl fst; simpl snd.
  auto.
Qed.

Lemma fib_iter_Ok : extEqual 1 fib fib_iter.
Proof.
  
  intro n. 
  change (fib n) with (snd (fib (S n), fib n)).
  rewrite <- fib_OK0.
  reflexivity. 
Qed.


Lemma fibIsPR : isPR 1 fib.
  destruct fib_iterIsPR as [x Hx].
  exists x; apply extEqualTrans with fib_iter.
  auto.
  apply extEqualSym, fib_iter_Ok.
Qed.


