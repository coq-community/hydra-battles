(** Build a counter-example to the hypothesis [cnf_lt_epsilon0_iff] below
 *)


From hydras Require Import Schutte AP CNF.
From Coq Require Import List.

Open Scope schutte_scope.

Section Cter_example.

  Hypothesis  cnf_lt_epsilon0_iff :
    forall l alpha,
      is_cnf_of alpha l ->
      (alpha < epsilon0 <->  Forall (fun beta =>  beta < alpha) l).

  Lemma counter_ex : False.
  Admitted.

End Cter_example.

