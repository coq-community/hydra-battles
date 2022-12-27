
(* Robert Krebbers's trick  *)

Require Import FunInd Recdef Wf_nat Lia.

Function zero (n:nat)  {wf lt n} : nat :=
  match n with
    0 => 0
  | p => zero (Nat.div2 p)
  end.
Proof.
  intros; apply PeanoNat.Nat.lt_div2; auto with arith.
  apply lt_wf.
Defined.

Compute zero 677.

About lt_wf. 

(** Let's see whqat happens if lt_wf was opaque *)

Module OpaqueWf.

 Lemma lt_wf : well_founded lt.
  Proof.
   intro n; induction n.
   - split; intro p; inversion 1.
   - split; intros y Hy; assert (H: y < n \/ y = n) by lia.      
    destruct H.
    + now apply IHn.    
    + now subst.
Qed.

  Function zero (n:nat)  {wf lt n} : nat :=
    match n with
      0 => 0
    | _ => zero (Nat.div2 n)
    end.
  Proof.
    intros;  apply PeanoNat.Nat.lt_div2; auto with arith.
    apply lt_wf.
 Defined.

 Compute zero 3.

 (** From Init.Wf *)

 
  (* *Lazily* add 2^n - 1 Acc_intro on top of wf. 
     Needed for fast reductions using Function and Program Fixpoint 
     and probably using Fix and Fix_F_2 
   *)    
 (* Fixpoint Acc_intro_generator n (wf : well_founded R)  := 
    match n with 
        | O => wf
        | S n =>
          fun x =>
            Acc_intro x
                      (fun y _ =>
                         Acc_intro_generator n
                                             (Acc_intro_generator n wf) y)
    end.
*)
 
About Acc_intro_generator.

Compute Acc_intro_generator 2 lt_wf .
Compute Acc_intro_generator 2 lt_wf  42.

Function zero' (n:nat)  {wf lt n} : nat :=
  match n with
    0 => 0
  | _ => zero' (Nat.div2 n)
  end.
Proof.
  intros; apply PeanoNat.Nat.lt_div2;  auto with arith.
  apply (Acc_intro_generator  32), lt_wf.
Defined.

 Compute zero' 677.

End OpaqueWf.


(* TODO: Check if required *)


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
