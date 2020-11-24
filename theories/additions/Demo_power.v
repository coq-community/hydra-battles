Require Import Monoid_def 
               Monoid_instances
               Pow.
Open Scope M_scope.

Compute 22%Z ^ 20.
(* 705429498686404044207947776%Z *)

Import Int31.

Coercion phi_inv : Z >-> int31.

Compute (22%int31 ^ 20).
(**   = 2131755008%int31
     : int31
*)


