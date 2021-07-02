Require Import Iterates F_alpha E0.
Require Import ArithRing Lia   Max.
Import Exp2 Canon.
Require Import Mult.
Open Scope nat_scope.


Section S1.
  Hypothesis H : forall (alpha beta:E0), alpha o<= beta ->
                                         forall i,  2 <= i ->
                                                    F_ alpha i <= F_ beta i.

 
  Remark R1 : 3 o<= omega.
  rewrite Le_iff; repeat split; left; reflexivity.
  Qed.

  Remark R2 : 2 <= 2.
  Proof (le_n 2).

 Let instance_H := H (Fin 3) omega R1 _ R2.
 
  Remark R3 : F_ omega 2 = F_ 2 2.
  Proof.
    rewrite F_lim_eqn.
    - unfold Canon, CanonS; cbn; f_equal.
         apply E0_eq_intro; reflexivity.
    -  reflexivity.
  Qed.


 
  Remark R4 : F_ 3 2 = F_ 2 (F_ 2 (F_ 2 2)).
  Proof.
    ochange (Fin 3) (Succ 2).
    rewrite F_succ_eqn.
    do 3 rewrite iterate_S_eqn.
    reflexivity. 
  Qed.


  Remark R6 : forall i, i < F_ 2 i.
  apply F_alpha_ge_S.
 Qed.

  Lemma Fake_thm : False.
    assert( F_ omega 2 < F_ 3 2). {
      rewrite R3, R4.
      generalize (R6 (F_ 2 2)); intro.
      generalize (R6 (F_ 2 (F_ 2 2))); intro.
      lia.
    }
    lia.
  Qed.

End S1.


