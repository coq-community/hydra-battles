Definition t : Type := (nat + nat)%type.
Declare Scope oo_scope.

Notation "'omega'" := (inr  0: t) : oo_scope.
Parameter P : t -> Prop.
Open Scope oo_scope.



Lemma P_iff (alpha:t) : P alpha <-> alpha = omega.
Proof.
  unfold t.
  
split.
Abort.


Lemma iff_intro (P Q: Prop) :
  (P -> Q) -> (Q -> P) -> (P <-> Q).
Proof. tauto. Qed.

Lemma P_iff' (alpha:t) : P alpha <-> alpha = omega.
Proof.
 apply iff_intro.
Abort.

Lemma P_imp (alpha:t) : P alpha -> alpha = omega.
Proof.
 intro. 
Abort.
