(** Prove that Stdlib's function Min is primitive recursive *)
(** this is a variant of the exercise MinPR *)


From hydras Require Import  primRec extEqualNat.
From Coq Require Import ArithRing Lia Compare_dec.

(** Define an n-ary if-then-else *)

Fixpoint naryIf (n:nat) :
  naryRel n -> naryFunc n -> naryFunc n -> naryFunc n
  :=
    match n return (naryRel n -> naryFunc n -> naryFunc n -> naryFunc n) with
      0 => (fun b x y =>  if b then x else y)
    | S m => fun (p': naryRel (S m)) (g h: naryFunc (S m)) =>
               fun x => naryIf m (p' x) (g x) (h x)
    end.

#[export] Instance If2IsPR (p: naryRel 2)(f g : naryFunc 2):
  isPRrel 2 p -> isPR 2 f -> isPR 2 g ->
  isPR 2 (naryIf 2 p f g).
Proof.
  unfold naryIf; cbn.
  intros [x Hx] [y Hy] [z Hz].
  assert (H: isPR 2  (fun a b => charFunction 2 p a b * f a b +
                                 (1- charFunction 2 p a b) * g a b)).
  {
    apply   compose2_2IsPR.
    - apply compose2_2IsPR.
      + exists x; auto.
      + exists y; auto.
      + apply multIsPR.
    - apply   compose2_2IsPR.
      +  apply compose2_2IsPR.
         *   apply filter01IsPR.
             apply const1_NIsPR.
         *  exists x; auto.
         *  apply minusIsPR.
      +  exists z; auto.
      +  apply multIsPR.
    -   apply plusIsPR.
  }
  destruct H as [t Ht]; exists t;  eapply extEqualTrans.
  -   apply Ht.
  -  intros a b; case_eq (p a b).
     + intro H0; unfold charFunction.
       rewrite H0.
       replace (1 - 1) with 0; ring_simplify; reflexivity.
     +  intro H1; unfold charFunction; rewrite H1; cbn; lia. 
Qed. 

Section Proof_of_MinIsPR.

  Let minPR : naryFunc 2 :=
    naryIf 2 leBool
           (fun x _ => x)
           (fun _ y => y).

  Lemma minPR_correct : extEqual 2 minPR PeanoNat.Nat.min.
  Proof.
    intros a b; unfold minPR, naryIf, leBool.
    destruct  (le_lt_dec a b).
    -    rewrite PeanoNat.Nat.min_l; auto; reflexivity. 
    - rewrite PeanoNat.Nat.min_r; auto with arith; reflexivity. 
  Qed.

  #[local] Instance minPR_PR : isPR 2 minPR.
  Proof.
    unfold minPR;apply If2IsPR.
   -  apply leIsPR.
   -  apply pi1_2IsPR.
   -  apply pi2_2IsPR. 
  Qed.

  #[export] Instance minIsPR : isPR 2 min.
  Proof.
    destruct minPR_PR as [f Hf].
    exists f; eapply extEqualTrans with (1:= Hf). 
    apply minPR_correct.
  Qed.


End Proof_of_MinIsPR.


