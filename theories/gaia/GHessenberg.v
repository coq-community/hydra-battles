From mathcomp Require Import all_ssreflect zify.
From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder ON_Generic.
From hydras Require Import T1 E0 Hessenberg.

From gaia Require Export ssete9.

Require Import T1Bridge. 
Set Implicit Arguments.
Unset Strict Implicit.


Open Scope cantor_scope.

(* begin snippet oplusDef *)
#[local] Notation hoplus := Epsilon0.Hessenberg.oplus.

Definition oplus alpha beta := h2g (hoplus (g2h alpha) (g2h beta)).

Infix "o+" := oplus: cantor_scope. 

Fixpoint o_finite_mult n alpha :=
  if n is p.+1 then alpha o+ (o_finite_mult p alpha)
  else zero. 
 

Compute T1pp (T1omega o+ T1omega).

Compute T1pp (o_finite_mult 5 (T1omega + \F 1)).
(* end snippet oplusDef *)


(** Equations for oplus *)

(* begin snippet oplusEquations:: no-out *)
Lemma oplus0b:  left_id zero oplus.
Proof. rewrite /oplus; case => // /=. 
       move => ? ? ? ;rewrite !h2g_g2hK => //.
Qed.
(* end snippet oplusEquations *)

(* begin snippet oplusEquationsb:: no-out *)
Lemma oplusa0: right_id zero oplus.
(* end snippet oplusEquationsb *)
Proof. rewrite /oplus; case => // /=. 
       move => ? ? ? ;rewrite !h2g_g2hK => //.
Qed.

(* begin snippet oplusEquationsc:: no-out *)
Lemma oplus_eqn a b :
 a o+ b =
   match a, b with
     zero, _ => b
   | _, zero => a
   | cons a1 n1 b1, cons a2 n2 b2 =>
       match compare  a1 a2 with
         Gt => cons a1 n1 (b1 o+ b)
       | Eq => cons a1 (S (n1 + n2)) (b1 o+ b2)
       | Lt => cons a2 n2 (a o+ b2)
       end
   end.
(* end snippet oplusEquationsc *)
Proof.
  rewrite /oplus oplus_eqn; case: a.
  cbn ; by rewrite h2g_g2hK.
  case: b.  move => ? ? ? ;by rewrite !h2g_g2hK. 
  move => t n t0 t1 n0 t2; rewrite !g2h_cons compare_g2h. 
  case (compare t1 t); by rewrite h2g_cons !h2g_g2hK.
Qed.


(* begin snippet oplusLemmasa:: no-out  *)
Lemma  oplus_nf (alpha  beta : T1) :
  T1nf alpha ->  T1nf beta -> T1nf (alpha o+ beta).
Proof.
  rewrite /oplus -?nf_ref => Halpha Hbeta; apply oplus_nf ; by rewrite hnf_g2h.
Qed.

Lemma oplusC (alpha beta: T1):
  T1nf alpha -> T1nf beta -> alpha o+ beta =  beta o+ alpha.
Proof.
  move => Halpha Hbeta; rewrite /oplus oplus_comm ?hnf_g2h //.
Qed.

 Lemma oplusA  (alpha beta gamma:T1) :
    T1nf alpha -> T1nf beta -> T1nf gamma ->
    alpha o+ (beta o+ gamma) = alpha o+ beta o+ gamma.
 Proof.
   move => Halpha Hbeta Hgamma;
           rewrite /oplus !g2h_h2gK oplus_assoc ?hnf_g2h => //.
 Qed.


 Lemma oplus_lt1 : forall a b, T1nf a -> T1nf b ->  zero <  a ->
                               b < b o+  a.
   (* end snippet oplusLemmasa *)
  Proof.
   move => a b Ha Hb Hlt; rewrite /oplus.
   replace b with (h2g (g2h b)) at 1 ; last first.
   by (rewrite h2g_g2hK). 
   rewrite -hlt_iff; apply oplus_lt1 => //; rewrite ?hnf_g2h //.
   rewrite hlt_iff ?h2g_g2hK => //.
 Qed.

  (* begin snippet oplusLemmasb:: no-out  *)
  
 Lemma oplus_lt2 : forall a b, T1nf a -> T1nf b ->  zero < b ->
                               a < b o+ a.
  (* end snippet oplusLemmasb  *)
Proof.
  intros a b Ha Hb  HD;  rewrite (oplusC Hb Ha); auto;
    apply oplus_lt1;auto.
Qed.

(* begin snippet oplusLemmasc:: no-out  *)
Lemma oplus_strict_mono_l (a b c:T1):
  T1nf a -> T1nf b -> T1nf c ->  a < b -> a o+ c < b  o+ c.
(* end snippet oplusLemmasc  *)
Proof.
  rewrite /oplus => Ha Hb Hc.
  rewrite <- hlt_iff => Hab.
  apply oplus_strict_mono_l => //; rewrite  ?hnf_g2h => //.
  by rewrite hlt_iff ?h2g_g2hK. 
Qed.

(* begin snippet oplusLemmasd:: no-out  *)
Lemma oplus_strict_mono_r (a b c:T1):
  T1nf a -> T1nf b -> T1nf c ->  b < c -> a o+ b < a  o+ c.
(* end snippet oplusLemmasd  *)
Proof.
  rewrite /oplus => Ha Hb Hc; rewrite <- hlt_iff => Hbc.
  apply oplus_strict_mono_r => //; rewrite  ?hnf_g2h => //.
  by rewrite hlt_iff ?h2g_g2hK.
Qed.

(* begin snippet oplusLemmase:: no-out  *)
Lemma oplus_lt_phi0 a b c:  T1nf a -> T1nf b -> T1nf c ->
                            a < c ->  b < c ->  phi0 a o+ phi0 b < phi0 c.
(* end snippet oplusLemmase  *)
Proof.
  move => Ha Hb Hc Hab Hbc; rewrite /oplus.
  replace (phi0 c) with (h2g (T1.phi0 (g2h c))); last first.
  by rewrite -g2h_phi0 ?h2g_g2hK. 
  rewrite -hlt_iff !g2h_phi0. 
  apply oplus_lt_phi0; rewrite ?hnf_g2h ?hlt_iff ?h2g_g2hK  => //. 
Qed.
