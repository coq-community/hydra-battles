(** Pierre Casteran, Univ. Birdeaux and LaBRI  *)

From hydras.Hydra Require Import Hydra_Definitions Hydra_Lemmas.

(** The hydra from page 286 of [KP] *)

Section KP.
(** initial state *)

Definition h0 : Hydra :=
  hyd2 (hyd2 (hyd_mult head 3)
             (hyd1 (hyd1 head)))
       (hyd2 head
             (hyd2 head head)).

Fact F1 : hsize h0 = 14.
Proof. reflexivity. Qed.

Fact F2 : height h0 = 4.
Proof. reflexivity. Qed.

(**  after stage 1 *)

Definition h1 :=
  hyd2 (hyd3 (hyd_mult head 2)
             (hyd_mult head 2)
             (hyd1 (hyd1 head)))
       (hyd2 head
             (hyd2 head head)).



Compute hsize h1.

(** After stage 2 *)

Notation hyd4 h1 h2 h3 h4 :=
  (node (hcons h1 (hcons h2 (hcons h3 (hcons h4 hnil))))).


Let  h' := hyd1 (hyd_mult head 2).

Definition h2 := 
                  hyd4 (hyd3 (hyd_mult head 2)
                             (hyd_mult head 2)
                             (hyd1 (hyd1 head)))
                       h'  h' h'.


(** After stage 3 *)

Definition h3 := hyd4
                   (node (hcons_mult (hyd1 head) 4
                                     (hcons (hyd2 head head)
                                            (hcons (hyd1 (hyd1 head))
                                                   hnil))))
                   h' h' h'.



Fact h0_h1 : round_n 1 h0 h1.
Proof.
  right. 
  r2_up 0. r2_here 0 0.

Qed.

Fact h1_h2 : round_n 2 h1 h2.
Proof.
  right; unfold h1, h2. r2_here 1 0.   
Qed.


Fact h2_h3 : round_n 3 h2 h3.
Proof.
  right.
  r2_up 0.
  r2_here 0 0.
Qed.

Lemma battle_example : battle standard 1 h0 4 h3.
Proof.
  eright.
  eapply h0_h1.
  eright.
  eapply h1_h2.
  eleft. 
  eapply h2_h3.
Qed.


Compute hsize h3.
(** = 28 *)


End KP.

