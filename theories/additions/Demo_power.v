From additions Require Import Monoid_def Monoid_instances Pow.
(* begin snippet DemoPower *)
Open Scope M_scope.

Compute 22%Z ^ 20.

Import Int31.

Coercion phi_inv : Z >-> int31.

Compute 22%int31 ^ 20.

(* end snippet DemoPower *)



