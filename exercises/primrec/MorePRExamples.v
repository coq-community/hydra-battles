Require Import primRec Arith ArithRing List.
Import extEqualNat.


(** ** Solution to an exercise  *)

Definition double n := n * 2.

Lemma doubleIsPR : isPR 1 double.
Admitted.

Fixpoint exp n p :=
  match p with
    0 => 1
  | S m =>  exp n m * n
  end.

(** You may use the following function as a helper.
    It is easier to apply [primRec]'s lemmas 
 *)

Definition exp_alt := fun a b => nat_rec (fun _ => nat)
                                     1
                                     (fun _ y =>  y * a)
                                     b.

Lemma expIsPR : isPR 2 exp.
Admitted.

Fixpoint tower2 n :=
  match n with
    0 => 1
  | S p => exp 2 (tower2 p)
  end.

Lemma tower2IsPR : isPR 1 tower2.
Admitted.

    
Fixpoint fact n :=
  match n with 0 => 1
          |   S p  => n * fact p
  end.

Lemma factIsPR : isPR 1 fact.
Admitted.


