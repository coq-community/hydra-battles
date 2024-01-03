(** 

  Dichotomic strategy, according to Bergeron, Brlek et al. 

  Let $n>3$ be a positive number. We associate to $n$ the integer 
   $n/ (2^{\lfloor(\log_2{n}+1)/2\rfloor})$.
  For instance, if $n=87$, the result is 10.

*)
 

From Coq Require Import Arith NArith.
From additions Require Export Strategies Pow Compatibility 
  More_on_positive.

Open Scope positive_scope.


(** Computes $2^{\lfloor(\log_2{n})/2\rfloor} 
*)

(* begin snippet dichotomy *)
Function dicho_aux (p:positive) {struct p} : positive :=
 match p with
   | 1%positive   =>  xH
   | 2%positive | 3%positive  => 2 
   | xO (xO q) | xO (xI q) | xI (xO q) | xI (xI q) =>
                                         xO (dicho_aux q)
 end.

Definition dicho  (p:positive) : positive :=
  N2pos (N.div (Npos p) (Npos (dicho_aux p))). 

Compute dicho  87.

Compute dicho  130.

Compute dicho 128.
(* end snippet dichotomy *)

(* 
= 10
     : positive
 *)

(** rewriting lemmas *)

Lemma dicho_aux_xOxO :  forall p: positive,
                          dicho_aux (xO (xO p)) = xO (dicho_aux p).
Proof. reflexivity. Qed.


Lemma dicho_aux_xOxI :  forall p: positive,
                          dicho_aux (xO (xI p)) = xO (dicho_aux p).
Proof. reflexivity. Qed.

Lemma dicho_aux_xIxO :  forall p: positive,
                          dicho_aux (xI (xO p)) = xO (dicho_aux p).
Proof. reflexivity. Qed.

Lemma dicho_aux_xIxI :  forall p: positive,
                          dicho_aux (xI (xI p)) = xO (dicho_aux p).
Proof. reflexivity. Qed.


Lemma dicho_aux_le_xOXO :
  forall p:positive ,  xO (dicho_aux p) <= p ->
                       xO (dicho_aux (p~0~0)) <= p~0~0.
Proof.
  intros; rewrite dicho_aux_xOxO.
  red;rewrite Pos.compare_xO_xO.
  fold (xO(dicho_aux p) <= p~0).
  transitivity p; auto.
  clear H;red;  change (p~0) with (2 * p);
  change  p with (1 * p) at 1;
  rewrite Pos.mul_compare_mono_r;   discriminate. 
Qed.



Lemma dicho_aux_le_xOXI :
  forall p:positive , xO (dicho_aux p) <= p ->
                      xO (dicho_aux (p~0~1)) <= p~0~1.
Proof.
  intros; rewrite dicho_aux_xIxO.
  transitivity (xO (xO p)).
  -   red;rewrite Pos.compare_xO_xO.
      fold (xO(dicho_aux p) <= p~0).
      transitivity p;  auto.
      change (p~0) with (2 * p) at 1;
        change p with (1 * p) at 1;
        red;rewrite Pos.mul_compare_mono_r;
        discriminate.
  -    clear H; induction p; simpl;[auto | auto | discriminate ].
Qed.

Lemma dicho_aux_le_xIXO :
  forall p:positive , xO (dicho_aux p) <= p ->
                      xO (dicho_aux (p~1~0)) <= p~1~0.
Proof.
 intros; rewrite dicho_aux_xOxI.
  transitivity (xO (xO p)).
  -  red;rewrite Pos.compare_xO_xO.
     fold (xO(dicho_aux p) <= p~0)%positive.
     transitivity p;  auto.
     change  (xO p) with (2 * p) .
     change  p with (1 * p) at 1. 
     red;rewrite Pos.mul_compare_mono_r; discriminate. 
  - red; cbn ; clear H; induction p; simpl;auto; try discriminate.
Qed.


Lemma dicho_aux_le_xIXI :
  forall p:positive , xO (dicho_aux p) <= p ->
                      xO (dicho_aux (p~1~1)) <= p~1~1.
Proof.
 intros; rewrite dicho_aux_xIxI.
  transitivity (xO (xO p)).
  red;rewrite Pos.compare_xO_xO.
 fold (xO (dicho_aux p) <= p~0).
  transitivity p; auto.
  change (p~0) with (2 * p) at 1.
  replace p with (1 * p) at 1.
  red;rewrite Pos.mul_compare_mono_r.
  - discriminate. 
  - now simpl.
  - red; cbn;
    clear H; induction p; simpl;auto.
    discriminate.
Qed.

#[global] Hint Resolve dicho_aux_le_xOXO dicho_aux_le_xOXI 
             dicho_aux_le_xIXO dicho_aux_le_xIXI : chains.

Lemma dicho_aux_lt : forall p, 3 < p ->
                               xO (dicho_aux p) <=  p.
Proof.
  intro p; pattern p; apply positive_4step_ind; try discriminate.
  - destruct p0.
    + destruct p0.
      * intros; repeat split; auto with chains.
      * intros;   repeat split; auto with chains.
      *  compute; repeat split;auto; try discriminate.
    + destruct p0.
      * intros;  repeat split; auto with chains.
      * intros;   repeat split; auto with chains.
      * compute; repeat split;auto; try discriminate.
    + compute; intuition auto;  discriminate. 
Qed.

Lemma dicho_aux_gt : forall p, 3 < p -> 1 < dicho_aux p.
Proof.
  intro p; pattern p; apply positive_4step_ind; try discriminate;
  destruct p0;   repeat split.
Qed. 


Lemma dicho_lt : forall p:positive, 3 < p -> dicho  p < p.
Proof. 
 intros p H; unfold dicho; generalize (dicho_aux_gt p H); intro H0.
 generalize (N.div_lt (N.pos p) (N.pos (dicho_aux p))); intro H1.
 unfold N2pos; case_eq (N.pos p / N.pos (dicho_aux p))%N.
 - intro; transitivity 3%positive ;[reflexivity | auto].
 - intros p0 H2; assert (N.pos p0 < N.pos p)%N.
   + rewrite <- H2; now apply H1.
   + assumption. 
Qed.

Lemma dicho_gt : forall p:positive, 3 < p -> 1 < dicho  p.
Proof. 
intros p H; unfold dicho; generalize (dicho_aux_lt p H).
intro H0; assert (2 <= N.pos p / (N.pos (dicho_aux p)) )%N.
- replace 2%N with (2%N * Npos (dicho_aux p) / Npos (dicho_aux p))%N.
  + apply N.Div0.div_le_mono; try discriminate. 
    * replace 2%N with (Npos 2%positive); cbn;auto.
  + rewrite N.div_mul; [auto | discriminate].
- case_eq (N.pos p / N.pos (dicho_aux p))%N.
  + intro H2; rewrite H2 in H1; destruct H1.
    reflexivity. 
+   intros p0 H2; rewrite H2 in H1.
    assert (1 < N.pos p0)%N.
    * apply N.lt_le_trans with 2%N;auto.
      reflexivity. 
    * assumption.
Qed.


(* begin snippet DichoStrat:: no-out *)
#[ global ] Instance Dicho_strat : Strategy dicho.
(* end snippet DichoStrat *)
Proof.
  split.
  - apply dicho_lt.
  - apply dicho_gt.
Qed.

