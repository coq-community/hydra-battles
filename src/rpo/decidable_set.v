(**  by Evelyne Contejean *)

Module Type S.

Parameter A : Set.
Axiom eq_A_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.

End S.
