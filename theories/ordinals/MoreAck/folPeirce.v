(** Experimental *)

(* begin snippet prelude:: no-out *)
From Coq Require Import Arith Lists.List.

Require Import fol folProp folProof  Languages folLogic.
Require Import primRec.

Require Import FOL_notations.
Import FolNotations. 

#[local] Arguments Ensembles.In {_} .
#[local] Arguments Ensembles.Add {_} .
Import Ensembles. 

Lemma In_add1 {T:Type}(a:T)(S: Ensemble T):
  In (Add  S a) a.
Proof.  right; auto with sets. Qed.

Lemma In_add2 {T:Type}(a b:T)(S : Ensemble T):
  In S a -> In (Add  S b) a.
Proof.  left; auto with sets. Qed.

#[local] Hint Unfold mem: sets. 

#[local] Hint Resolve In_add1 In_add2: sets. 


(* end snippet prelude *)

(* begin snippet PeirceProof:: no-out *)
Section PeirceProof.

Variable L : Language. 
Variables P Q: Formula L. 
Variable G : System L. 

Definition Peirce := (((P -> Q) ->P) -> P)%fol.

Lemma peirce : SysPrf L G Peirce. 
Proof with auto with sets.
(* end snippet PeirceProof *)

(* begin snippet step1 *)
  unfold Peirce; apply impI. 
(* end snippet step1 *)

(* begin snippet step2 *)
  eapply orE with (notH P) P%fol; 
       [apply noMiddle | | apply impRefl].
(* end snippet step2 *)
(* begin snippet step3 *)
   apply impI; eapply impE with (P -> Q)%fol. 
(* end snippet step3 *)
(* begin snippet step4:: no-out *)
    - apply Axm ...
    - apply impI; apply contradiction with P; apply Axm ...
Qed.
(* end snippet step4 *)

End PeirceProof.

About peirce.


