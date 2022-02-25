From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder ON_Generic.
From hydras Require Import T1 E0 Hessenberg.
From mathcomp Require Import all_ssreflect zify.
From gaia Require Export ssete9.
Set Bullet Behavior "Strict Subproofs".

Require Import T1Bridge. 
Set Implicit Arguments.
Unset Strict Implicit.

#[local] Notation hoplus := Epsilon0.Hessenberg.oplus.

Definition oplus alpha beta := h2g (hoplus (g2h alpha) (g2h beta)).


Infix "o+" := oplus: cantor_scope. 
Open Scope cantor_scope.

Fixpoint o_finite_mult n alpha :=
match n with
    0 => zero
  | S p =>  alpha o+ (o_finite_mult p alpha)
end.

Compute ppT1 (T1omega o+ T1omega).

Compute ppT1 (o_finite_mult 5 (T1omega + \F 1)).

(** Equations for oplus *)

Lemma oplus_neutral_l beta : zero o+ beta = beta.
Proof. rewrite /oplus ; case: beta => // /=.
       move => ? ? ? ;rewrite !h2g_g2hK => //.
Qed.

Lemma oplus_neutral_r alpha : alpha o+ zero = alpha.
Proof. rewrite /oplus ; case: alpha => // /=.
       move => ? ? ? ;rewrite !h2g_g2hK => //.
Qed.

Lemma oplus_eqn :
  forall a b, 
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
Proof.
  move => a b; rewrite /oplus oplus_eqn.
  case: a.
  cbn ; by rewrite h2g_g2hK.
  case: b.  move => ? ? ? ;by rewrite !h2g_g2hK. 
  move => t n t0 t1 n0 t2; rewrite !g2h_cons compare_g2h. 
  case (compare t1 t); rewrite h2g_cons !h2g_g2hK; reflexivity. 
Qed.


Lemma  oplus_nf (alpha  beta : T1) :
  T1nf alpha ->  T1nf beta -> T1nf (alpha o+ beta).
Proof.
  rewrite /oplus -?nf_ref => Halpha Hbeta.
  apply oplus_nf ; by rewrite hnf_g2h.
Qed.

 Lemma oplus_comm (alpha beta: T1):
   T1nf alpha -> T1nf beta -> alpha o+ beta =  beta o+ alpha.
 Proof.
   move => Halpha Hbeta; rewrite /oplus oplus_comm ?hnf_g2h //.
 Qed.


 Lemma oplusA  (alpha beta gamma:T1) :
    T1nf alpha -> T1nf beta -> T1nf gamma ->
    alpha o+ (beta o+ gamma) =
      alpha o+ beta o+ gamma.
 Proof.
   move => Halpha Hbeta Hgamma;
           rewrite /oplus !g2h_h2gK oplus_assoc ?hnf_g2h => //.
 Qed.


 Lemma oplus_lt1 : forall a b, T1nf a -> T1nf b ->  zero <  a ->
                               b < b o+  a.
 Proof.
   move => a b Ha Hb Hlt; rewrite /oplus.
   (* Todo : understand contexts use in SSr rewrite *)
   replace b with (h2g (g2h b)) at 1 ; last first.
   by (rewrite h2g_g2hK). 
   rewrite -hlt_iff; apply oplus_lt1 => //; rewrite ?hnf_g2h //.
   rewrite hlt_iff ?h2g_g2hK => //.
 Qed.

 Lemma oplus_lt2 : forall a b, T1nf a -> T1nf b ->  zero < b ->
                               a < b o+ a.
Proof.
  intros a b Ha Hb  HD;  rewrite (oplus_comm Hb Ha); auto;
    apply oplus_lt1;auto.
Qed.

Lemma oplus_strict_mono_l (a b c:T1):
  T1nf a -> T1nf b -> T1nf c ->
  a < b -> a o+ c < b  o+ c.
  
Proof.
  rewrite /oplus => Ha Hb Hc.
  rewrite <- hlt_iff => Hab.
  apply oplus_strict_mono_l => //; rewrite  ?hnf_g2h => //.
  by rewrite hlt_iff ?h2g_g2hK. 
Qed.


Lemma oplus_strict_mono_r (a b c:T1):
  T1nf a -> T1nf b -> T1nf c ->
  b < c -> a o+ b < a  o+ c.
Proof.
   rewrite /oplus => Ha Hb Hc.
  rewrite <- hlt_iff => Hbc.
  apply oplus_strict_mono_r => //; rewrite  ?hnf_g2h => //.
  by rewrite hlt_iff ?h2g_g2hK.
Qed.


Lemma oplus_lt_phi0 a b c:  T1nf a -> T1nf b -> T1nf c ->
                                      a < c ->  b < c ->
                                     phi0 a o+ phi0 b < phi0 c.
Proof.
  move => Ha Hb Hc Hab Hbc; rewrite /oplus.
    replace (phi0 c) with (h2g (hphi0 (g2h c))). 
  rewrite -hlt_iff. 
rewrite !g2h_phi0. 
apply oplus_lt_phi0; rewrite ?hnf_g2h ?hlt_iff   ?h2g_g2hK  => //. 
by rewrite -g2h_phi0 ?h2g_g2hK. 
Qed.
