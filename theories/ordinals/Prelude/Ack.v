From hydras Require Export Iterates .
From Coq Require Import Lia.

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




