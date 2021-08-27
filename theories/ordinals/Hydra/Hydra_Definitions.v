(** Pierre Casteran, LaBRI, University of Bordeaux *)


(** * Data types 

 An hydra is a finitely branched tree. We use the auxiliary type [Hydrae]  for
 representing finite sequences  of hydras.
 *)

From Coq Require Export Relations Max.
From hydras Require Import T1 Epsilon0.

(* begin snippet HydraDef *)

Inductive Hydra : Set :=
|  node :  Hydrae -> Hydra
with Hydrae : Set :=
| hnil : Hydrae
| hcons : Hydra -> Hydrae -> Hydrae.

(* end snippet HydraDef *)

(** Alternative representation (discarded) *)

(* begin snippet HydraAlt *)

Module Alt.

  Inductive Hydra : Set :=
    hnode (daughters : list Hydra).

End Alt.

(* end snippet HydraAlt *)

(**   Mutual induction scheme for types Hydra and Hydrae 
 *)


(* begin snippet HydraRect2 *)
Scheme Hydra_rect2 := Induction for Hydra Sort Type
with   Hydrae_rect2 := Induction for Hydrae Sort Type.
(* end snippet HydraRect2 *)

(* begin snippet hForall *)
(** All elements of s satisfy P *)
Fixpoint h_forall (P: Hydra -> Prop) (s: Hydrae) :=
  match s with
    hnil => True
  | hcons h s' => P h /\ h_forall P s'
  end.
(* end snippet hForall *)

Lemma h_eq_dec : forall h h':Hydra, {h = h'}+{h <> h'}
with hs_eq_dec : forall l l':Hydrae, {l = l'}+{l <> l'}.
Proof.
 all: decide equality.  
Defined. 



(**   Number of nodes (a.k.a. size)
 *)

(* begin snippet hsize *)
Fixpoint hsize (h:Hydra) : nat :=
  match h with node l => S (lhsize l) end
with lhsize l : nat :=
       match l with
         | hnil => 0
         | hcons h hs => hsize h + lhsize hs
  end.
(* end snippet hsize *)

(** ***  height (length of longest branch) 
 *)

(* begin snippet height *)
Fixpoint height  (h:Hydra) : nat :=
  match h with node l => lheight l  end
with
lheight l : nat :=
  match l with hnil => 0
          | hcons h hs => Max.max (S (height h)) (lheight hs)
  end.
(* end snippet height *)

(** ** Abbreviations 
 *)

(** *** Heads : A head is just a node without daughters
*)

(* begin snippet headsEtc *)

Notation head := (node hnil).

(** *** Hydra with 1, 2 or 3 daughters 
 *)

Notation hyd1 h := (node (hcons h hnil)).
Notation hyd2 h h' := (node (hcons h (hcons h' hnil))).
Notation hyd3 h h' h'' := (node (hcons h (hcons h' (hcons h'' hnil)))).

(* end snippet headsEtc *)

(** *** Adds n copies of the same hydra h at the right of  s 
*)

(* begin snippet hconsMult *)
Fixpoint hcons_mult (h:Hydra)(n:nat)(s:Hydrae):Hydrae :=
  match n with 
  | O => s
  | S p => hcons h (hcons_mult h p s)
  end.


(** *** Hydra with n equal daughters *)

Definition hyd_mult h n :=
  node (hcons_mult h n hnil).
(* end snippet hconsMult *)

(** ** Managing sequences of hydras
 *)

(** *** Appending
 *)


Fixpoint hy_app (s1 s2: Hydrae) : Hydrae :=
  match s1 with
    hnil => s2
  | hcons h1 s1' => hcons h1 (hy_app s1' s2)
  end.

(** ***  Adds a  head to  the right of [s]
 *)

Fixpoint add_head_r (s: Hydrae) :=
  match s with
    hnil => hcons  head hnil
  | hcons h s' => hcons h (add_head_r s')
  end.

(** ***  Adds i   heads to the right of [s]
 *)

Fixpoint add_head_r_plus (s:Hydrae) (i:nat)  :=
  match i with
    0 => s
  | S j => add_head_r (add_head_r_plus s j)
  end.

(** *** adds [i] heads to  the root of [h] (to the right of its daughters)
 *)

Definition add_r h i :=
  match h with node s => node (add_head_r_plus s i) end.





(** *  Hydra Battles

    ** Relation associated with a single round.

  We represent the rules of Hydra Battles through a binary relation:
  [round_n n] on the [Hydra] type. 
The proposition  [round_n n  h h'] holds if [h'] is obtained from [h] by a single round of a battle, and [n] is the _expected_ replication  factor (irrelevant if the chopped head is at distance 1 from the foot).

The proposition [round_n n h h'] holds 

- if [h'] is obtained from [h] by chopping off one head of height 1. This situation is described by the proposition [R1 h h'].

- Or [h'] is obtained from [h] through a beheading at distance $\geq 2$ from the foot, with creation of [n] copies of some dub-hydra.


Before giving the definition in Coq of [round_n], we need to define several  auxiliary relations.


 ***  S0

 The proposition [S0 s s'] holds if the sequence [s'] is obtained by removing one head from [s]
*)

(* begin snippet S0Def *)
Inductive S0 :  relation Hydrae :=
| S0_first : forall s, S0  (hcons head s) s
| S0_rest : forall  h s s',
    S0  s s' ->  S0  (hcons h s) (hcons h s').
(* end snippet S0Def *)

(** *** R1

    The proposition [R1 h h'] holds if [h'] is obtained by removing one head from [h] at distance 1 from  the foot 

*)

(* begin snippet R1Def *)
Inductive R1  :  relation Hydra :=
| R1_intro : forall s s', S0 s s' -> R1 (node s) (node s').
(* end snippet R1Def *)

 (** *** S1 

  [S1 n s s'] holds if [s'] is obtained from [s] by replacing some  member [h] of [s] by $n+1$ copies of [h],  where [R1 h h'] holds.
  Thus, [n] is the number of new replicas of [h']. 

 *)

(* begin snippet S1Def *)

Inductive S1 (n:nat)  : relation  Hydrae  :=
| S1_first : forall s h h' ,
              R1 h h' -> 
              S1 n (hcons h s) (hcons_mult h' (S n) s)
| S1_next : forall h s s',
                 S1 n s s' ->
                 S1 n (hcons h s) (hcons h s').

(* end snippet S1Def *)


(**  *** R2

The proposition [R2 n h h'] holds if some sub-hydra [h0] of [h] has been replaced by [h'0],
  where [R1 n h0 h'0]. The [S2] relation is just a helper for [R2].

  

*)

(* begin snippet R2Def *)
Inductive R2 (n:nat)  :  relation Hydra  :=
| R2_intro : forall s s', S1 n s s' -> R2 n (node s) (node s')
| R2_intro_2 : forall s s', S2 n s s' -> R2 n (node s) (node s')

with S2 (n:nat) :  relation Hydrae :=
     |  S2_first : forall h h' s ,
         R2 n   h h'->  S2  n (hcons h s) (hcons h'  s)
     |  S2_next  : forall h   r r',
         S2 n r r' ->  S2 n (hcons h r) (hcons h r').
(* end snippet R2Def *)

(**  *** [round_n]

   Let [n] be an _expected_ replication number. The relation [round_n n h h']
   holds:
   - if  [h'] is obtained from [h] by removing one head of height 1 (and the factor [n] is irrelevant)
   - or  [h'] is obtained from [h] by removing one head of height greater or equal than 2, and this beheading was made with a relocation factor [n].
*)

(* begin snippet roundNDef *)
Definition round_n n h h' := R1 h h' \/ R2 n h h'.
(* end snippet roundNDef *)


(** Transition system associated with battles *)


(** *** Binary relation associated with a battle round *)

(* begin snippet roundDef *)
Definition round h h' := exists n,  round_n n h h'.

Infix "-1->" := round (at level 60).
(* end snippet roundDef *)



(** *** transitive closures of round 
*)

(* begin snippet roundPlus *)
Definition round_plus := clos_trans_1n Hydra round.

Definition round_star h h' := h = h' \/ round_plus h h'.

Infix "-+->" := round_plus (at level 60).
Infix "-*->" := round_star (at level 60).
(* end snippet roundPlus *)

(** **  Experimental tactics for interactive battles  *)

(**  *** removes the i-th daughter (should be a head) *)

Ltac chop_off i :=
  match goal with |- S0 ?h ?h' =>
                  match i with
                    | O => eapply S0_first
                    | S ?j => eapply S0_rest; chop_off j
                  end
                  |  |- round ?h ?h' =>
                     exists 0; left; split; chop_off i
                  |  |- round_n ?n ?h ?h' =>
                     left ; split; chop_off i
  end.


(**  Calls the [R2] relation *)

Ltac h_search_n n  :=  match goal with
                       |- round ?h ?h' =>  exists n; eright
                    end.

Ltac h_search   :=  match goal with
                    | |- round_n ?p ?h ?h' => eright
                    end.


Ltac s2_nth n :=
  match n with
    | 0 => eleft
    | S ?p => eright ; s2_nth p
    end.

(** Moves to the [i]-th daugther *)

Ltac r2_up i := match goal with
                    |- R2 ?n ?h ?h' => eright; s2_nth i 
end.

Ltac S1_nth i :=
  match goal with
      |- S1 ?n ?h ?h' =>
      match i with
        | 0 => eleft
        | S ?j => eright ; S1_nth j
      end
  end.


(** Notifies we are at distance 2 from the expected head 
    goto to [i]-th dauchter, then chop off the [j]-th head *)

Ltac r2_d2 i j :=
 match goal with
      |- R2 ?n ?h ?h' =>  eleft; S1_nth i; split; chop_off j
 end.

(** End of the battle *)

Ltac stop :=
  match goal with
      |- round_star ?h ?h' => left; reflexivity
  end.

(** Still fighting *)

Lemma round_star_intro h h'' : forall h',
    h -1-> h' -> h' -*-> h'' -> h -*-> h''.
Proof. 
  destruct 2.
  - subst; right; now left .
  - right; now right with h'.
Qed.

Ltac forward :=
  match goal with
      |- round_star ?h ?h' => eapply round_star_intro
  end.



(**  ** Traces *)

Inductive trace_to  dest : list  nat -> Hydra -> Prop :=
  trace_to1 : forall n h, round_n  n h dest -> trace_to dest (cons n nil) h
| trace_toS : forall n t h h',  round_n n  h h' -> trace_to dest t h' ->
                                 trace_to dest (n:: t) h.

Definition trace t h h' := trace_to h' t h.

(** 
  Let $h$ be an hydra and $n$ and expected replication factor. The next step of 
  the current battle may be specified by the following type *)



Definition round_spec h n :=
  {h' : Hydra |  round_n n h h'} + {h = head}.

(** ** Classes of battles 

In an hydra battle, the interaction between the two players  may depend on the time (number of rounds) elapsed since the beginning of the fight.

Let us formalize this dependence through a relation linking the number of the current round, and the hydra before and after the considered round.


*)

(* begin snippet BattleDef *)

Definition round_t := nat -> Hydra -> Hydra -> Prop.

Class Battle :=  {battle_rel : round_t;
                  battle_ok : forall i h h',
                      battle_rel  i h h' -> round h h'}.

Arguments battle_rel : clear implicits.

(* end snippet BattleDef *)

(** In the current state of this development, we will consider two instances of class [Battle]:

 - In [free], we hydra may chose any replication factor at any time.

 - In [standard] the replication factor at round number [i] is just [i]
 *)


(* begin snippet freeDef *)
  
Program Instance free : Battle := Build_Battle (fun _  h h' => round h h') _.

(* end snippet freeDef *)

(* begin snippet standardDef *)

Program Instance standard : Battle := (Build_Battle round_n _).
Next Obligation.
  now exists i.  
Defined.

(* end snippet standardDef *)

(**  The following relation allows us to consider sequences of rounds in a given  class  of battles 

 The proposition [battle b i h j h'] holds if there is a battle of class [B] that
  starts with hydra [h] at round [i] and ends with hydra [h'] at round [j]
 *)

(* begin snippet battleRelDef *)

Inductive battle (B:Battle) : nat -> Hydra -> nat -> Hydra -> Prop :=
  battle_1 : forall i h  h', battle_rel   B i  h h' -> 
                            battle B i h (S i) h'
| battle_n : forall i h  j h' h'', battle_rel  B i h h''  ->
                                   battle B (S i) h'' j h'  ->
                                   battle B i h j h'.

(* end snippet battleRelDef *)

 (** number of steps leading to the hydra's death *)

Definition battle_length B k h l :=
    battle B k h  (Nat.pred (k + l)%nat) head.


(** *** Uniform termination *)

(* begin snippet TerminationDef *)

Definition Termination :=  well_founded (transp _ round).

(* end snippet TerminationDef *)

Definition B_termination (B: Battle) :=
  well_founded (fun h' h =>  exists i:nat, battle_rel B i h h' ).


(** *** Variants for proving termination 
 *)

(* begin snippet HvariantDef *)

Class Hvariant {A:Type}{Lt:relation A}
      (Wf: well_founded Lt)(B : Battle)
      (m: Hydra -> A): Prop :=
  {variant_decr: forall i h h',
      h <> head ->
      battle_rel  B i  h h' -> Lt (m h') (m h)}.

(* end snippet HvariantDef *)

(** Variant bounded by some ordinal alpha < epsilon0 *)
(** **  Strictly Bounded variants *)

(* begin snippet BoundedVariant *)

Class BoundedVariant {A:Type}{Lt:relation A}
      {Wf: well_founded Lt}{B : Battle}
      {m: Hydra -> A} (Var: Hvariant  Wf  B m)(mu:A):=
  {
  m_bounded: forall h, Lt (m h ) mu
  }.

(* end snippet BoundedVariant *)



(** *** Liveness 

 For every reachable configuration [(i,h)], either [h] is a head, or 
 there exists a beheading leading to some configuration [(S i, h')].
 *)

(* begin snippet AliveDef *)

Definition Alive (B : Battle) :=
  forall i h,
     h <> head ->
    {h' : Hydra |  battle_rel  B i h h'}.

(* end snippet AliveDef *)
