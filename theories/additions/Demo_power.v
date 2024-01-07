From additions Require Import Monoid_def Monoid_instances Pow.
(* begin snippet DemoPower *)
Open Scope M_scope.

Compute 22%Z ^ 20.

Import Uint63.
Search (Z -> int).
Coercion of_Z : Z >-> int.

Compute 22%int63 ^ 50.

(* end snippet DemoPower *)



