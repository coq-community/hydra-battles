(* After Guillaume Melquiond
   Coq-club, Dec 21, 2020  *)




Inductive fuel :=
 | FO : fuel
 | FS : (unit -> fuel) -> fuel.

(* the dummy "unit" argument is only there in case you intend to
evaluate your code using a cbv strategy, e.g., vm_compute. *)

Fixpoint foo (n:nat) x :=
 match n with
 | S n => FS (fun _ => foo n (foo n x))
 | O => x
 end.

