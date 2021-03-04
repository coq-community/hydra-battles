From hydras Require Import Schutte AP CNF.
From Coq Require Import List.
Open Scope schutte_scope.

Section Cter_example.

  Hypothesis  cnf_lt_epsilon0_iff :
    forall l alpha,
      is_cnf_of alpha l ->
      (alpha < epsilon0 <->  Forall (fun beta =>  beta < alpha) l).


  Let alpha := phi0 (succ epsilon0).
  Let l := succ epsilon0 :: nil.

  Remark R1 : epsilon0 < alpha.
  Proof.
    rewrite <- epsilon0_fxp; unfold alpha.
    apply phi0_mono.
    apply lt_succ.
  Qed.

  Remark R2 : is_cnf_of alpha l.
    red.
    split.
    constructor.
    cbn.
    now rewrite alpha_plus_zero.
  Qed.


  Remark R3 :  Forall (fun beta =>  beta < alpha) l.
  Proof.
    unfold l; constructor. 
     apply lt_succ_lt.
    unfold alpha.
     apply is_limit_phi0.
    auto with schutte.
    apply R1.
    constructor.
  Qed.

  Lemma counter_ex : False.
    destruct (cnf_lt_epsilon0_iff l alpha R2) as [H H0].
    specialize (H0 R3).
    eapply lt_irrefl.
    eapply lt_trans with alpha.
    apply R1.
    auto.
  Qed.

End Cter_example.

