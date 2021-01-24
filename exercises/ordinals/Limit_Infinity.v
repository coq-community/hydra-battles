(** Prove that, for any ordinal [0 < alpha < epsilon0], [alpha] is a limit 
  if and only if forall ordinal [beta < alpha], there exists an infinite 
  number of ordinals betawee [beta] and [alpha]
 *)

From hydras Require Import Epsilon0 T1.
Open Scope t1_scope.
From Coq Require Import Ensembles Image Compare_dec.


Definition Infinite {A: Type} (E: Ensemble A) :=
  exists s: nat -> A, injective nat A s /\ forall i, In  E (s i).

Section On_alpha.

  Variable alpha: T1.
  Hypothesis Halpha : nf alpha.
  Hypothesis HnonZero : alpha <> zero.
  
  Theorem Limit_Infinity :
    limitb alpha <->
    (forall beta,
        beta t1< alpha ->
        Infinite (fun gamma =>  beta t1< gamma t1< alpha)).
  Admitted.
  
End On_alpha.

