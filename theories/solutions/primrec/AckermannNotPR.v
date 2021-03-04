From hydras Require Import Iterates primRec extEqualNat. 
Import Iterates.

Lemma iterate_compat {f : nat -> nat}(n:nat)(x:nat):
  Iterates.iterate f n x = primRec.iterate f n x.
Proof.
  induction n; cbn.
  - reflexivity.
  - now rewrite IHn.
Qed.

Fixpoint Ack (m:nat) : nat -> nat :=
  match m with 0 => S
          |   S n => fun k =>  iterate (Ack n) (S k) 1
  end.


Lemma ack_0_p p : Ack 0 p = S p.
Proof.
  reflexivity.
Qed.

Lemma ack_Sn_0  (n:nat) : Ack (S n) 0 = Ack n 1.
Proof.
  reflexivity.
Qed.

Lemma ack_Sn_Sp (n p:nat): Ack (S n) (S p) =
                           Ack n (Ack (S n) p).
Proof.
  reflexivity.
Qed.


Lemma AckSn_as_iterate (n:nat) : extEqual 1 (Ack (S n))
                                          (fun k => iterate (Ack n) (S k) 1).
  intros k;reflexivity.
Qed. 


Lemma AckSn_as_PRiterate (n:nat):
  extEqual 1 (Ack (S n)) (fun k => primRec.iterate (Ack n) (S k) 1).
  

  Search iterate.
  intros k. rewrite AckSn_as_iterate.
  generalize (Ack n); intro f.
  generalize 1; generalize (S k).
  induction n0.
  cbn.
  auto.
  cbn.
  intro n1; rewrite IHn0.
  auto.
Qed.

Lemma iterate_nat_rec (g: nat->nat) (n:nat) x :
  iterate g n x = nat_rec (fun _ => nat) x (fun x y => g y) n.
  induction n; cbn; auto.
Qed.


Section Proof_of_Ackn_PR.

  Section S_step.
    Variable n:nat.

    Hypothesis IHn: isPR 1 (Ack n).

    Remark R1 : extEqual 1 (Ack (S n))
                         (fun a : nat =>
                            nat_rec (fun _ : nat => nat) 1
                                    (fun _ y : nat => Ack n y)
                                    (S a)).
    
    Proof.
      intro a; cbn; now rewrite iterate_nat_rec.
    Qed.

    Remark R2 : isPR 1
                     (fun a : nat =>
                        nat_rec (fun _ : nat => nat) 1
                                (fun _ y : nat => Ack n y)
                                (S a)).
    Proof.
      apply compose1_1IsPR.
      - apply succIsPR.
      - eapply indIsPR.
        now apply filter01IsPR.  
    Qed.


    Remark R3 : isPR 1 (Ack (S n)).
    Proof.
      destruct R2 as [x Hx]; exists x.
      eapply extEqualTrans with (1:= Hx).
      intro; symmetry; apply R1.
    Qed.

  End S_step.

  Theorem Ackn_IsPR (n: nat) : isPR 1 (Ack n).
  Proof.
    induction n.
    - cbn; apply succIsPR.
    -  apply R3; auto.  
  Qed.

End Proof_of_Ackn_PR.
  
  
  (** _There are many other definitions in the litterature. So feel free to 
    use the one you prefer, but it must respect the "equations" above *)


  Theorem AckIsntPR : isPR 2 Ack -> False.
  Admitted.



  (*
 _This is not a trivial exercise. You may have to prove several additional 
lemmas. 
   *)





