(* @todo  add as an exercise *)

(** Returns smallest value of x less or equal than b such that (P b x). 
    Otherwise returns b  *)


From hydras Require Import  primRec extEqualNat.
From Coq Require Import Min ArithRing Lia Compare_dec Arith Lia.


(* begin snippet boundedSearch3 *)

Lemma boundedSearch3 :
  forall (P : naryRel 2) (b  : nat), boundedSearch P b <= b. (* .no-out *)

(* end snippet boundedSearch3 *)

Proof.
  unfold boundedSearch; intros P b; generalize b at 2 3.
  induction b0.
  - cbn; auto.
  - cbn; destruct (Nat.eq_dec (boundedSearchHelp (P  b) b0) b0); auto.
    case_eq (P b b0); auto.
Qed.

(* begin snippet boundedSearch4 *)

Lemma boundedSearch4 :
  forall (P : naryRel 2) (b  : nat),
    P b b = true ->
    P b (boundedSearch P b) = true. (* .no-out *)

(* end snippet boundedSearch4 *)

Proof.
  intros;  destruct (boundedSearch2 P b); auto. 
  now rewrite H0.
Qed.


Definition isqrt_spec n r := r * r <= n < S r * S r.

Section sqrtIsPR.

  Let P (n r: nat) :=  Nat.ltb n (S r * S r).
  Definition isqrt := boundedSearch P. 

  Section Proof_isqrt.
    Variable n: nat.

    Remark R00 : P n (isqrt n) = true.
    Proof.
      apply boundedSearch4.
      unfold P; cbn;  apply leb_correct; lia.
    Qed.

    Lemma R01 : n < S (isqrt n) * S (isqrt n).
    Proof.
      generalize R00; intro H; apply leb_complete in H; auto.
    Qed.

    Lemma R02 : isqrt n * isqrt n <= n.
    Proof.
     destruct (le_lt_dec (isqrt n * isqrt n) n); auto.
     case_eq (isqrt n).
     -  cbn; auto with arith.
     -  intros n0 H;  assert (H0: n0 < isqrt n).       
          { rewrite H; auto with arith. }
          generalize (boundedSearch1 P n n0 H0) ; intro H1.
          unfold P in H1; rewrite Nat.ltb_ge in H1; auto.
    Qed.

  End Proof_isqrt.

   Lemma sqrt_correct (n: nat) : isqrt_spec n (isqrt n).
   Proof.
     split.
     - apply R02.
     - apply R01.
   Qed.

 Lemma issqrtIsPR : isPR 1 isqrt.
 Proof.
   unfold isqrt; apply boundSearchIsPR; unfold P; red.
   assert (H: isPR 2 (fun a b => 
                     (charFunction 2 ltBool a (S b * S b)))).
   {
     apply compose2_2IsPR.
     - apply filter10IsPR; apply idIsPR.
     - apply filter01IsPR;  apply compose1_2IsPR.
       + apply succIsPR.
       + apply succIsPR.
       + apply multIsPR.
   - apply ltIsPR.
   }
   destruct H as [x Hx]; exists x.  
   eapply extEqualTrans.
   - apply Hx.
   - intros a b; simpl .
     case_eq (ltBool a (S (b + b * S b))).
    +  case_eq (a <? S (b + b * S b) );  auto.
       intros.
       rewrite Nat.ltb_ge in H.
       apply ltBoolTrue in H0; lia.
    +  intro H; apply ltBoolFalse in H.
       case_eq (a <? S (b + b * S b)); auto.
       intro H0;  rewrite Nat.ltb_lt in H0.
       now destruct H.
Qed. 


End sqrtIsPR.

(** slow! *)

Compute isqrt 22.

(** Extra work :
   Define a faster implementation of [sqrt_spec], and prove your function is 
   extensionnaly equal to [isqrt] (hence PR!)
 *)
