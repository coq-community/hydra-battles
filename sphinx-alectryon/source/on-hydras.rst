

Hydras
=======


   :alectryon/serapi/args: -R ../../theories/ordinals hydras

.. coq::
   
   Require Import Hydra_Definitions.

   Print Hydra. (* .out .unfold *)

Abbreviations
-------------

We provide several notations for hydra patterns which occur often in our
developments.

.. coq::

   (** heads *)
   Notation head := (node hnil).
    
   (** nodes  with 1, 2 or 3 daughters *)
   Notation hyd1 h := (node (hcons h hnil)).
   Notation hyd2 h h' := (node (hcons h (hcons h' hnil))).
   Notation hyd3 h h' h'' := 
                      (node (hcons h (hcons h' (hcons h'' hnil)))).


Example
^^^^^^^

.. coq::
   
   Example Hy := hyd3 head
                      (hyd2
                         (hyd1 
                            (hyd2 head head))
                         head) 
                      head.

Recursive Definitions on type ``Hydra``
---------------------------------------

.. coq::

   Fixpoint hsize (h:Hydra) : nat :=
     match h with node l => S (lhsize l)
     end
   with lhsize l : nat :=
     match l with hnil => 0
               | hcons h hs => hsize h + lhsize hs 
     end.

   Compute hsize Hy. (* .unfold *)


Likewise, the *height* (maximum distance between the foot and a head) is
defined by mutual recursion:

.. coq::

    Fixpoint height  (h:Hydra) : nat :=
     match h with node l => lheight l
     end
    with lheight l : nat :=
     match l with 
     | hnil => 0
     | hcons h hs => Max.max (S (height h)) (lheight hs)
     end.

    Compute height Hy. (* .unfold *)

Induction principles for hydras
-------------------------------

    In this section, we show how induction principles are used to prove
    properties on the type ``Hydra``. Let us consider for instance the
    following statement:

     “The height of any hydra is strictly less than its size.”
     


A failed attempt
^^^^^^^^^^^^^^^^^^


 One may try to use the default tactic of proof by induction, which
   corresponds to an application of the automatically generated induction
   principle for type ``Hydra``:

.. coq::

   About Hydra_ind. (* .unfold *)

..
   
    Let us try to prove our lemma.

.. coq::

   Lemma height_lt_size (h:Hydra) :
     height h <= hsize h.
   Proof.
     induction h as [s].

..

    We might be tempted to do an induction on the sequence ``s``:

.. coq:: 

    induction s as [| h s']; [auto with arith|]. (* .unfold *)
   Abort.
..

    Note that the displayed subgoal does not contain any assumption on
    ``h``, thus there is no way to infer any property about the height and
    size of the hydra ``hcons h t``.
    
    
A principle of mutual induction
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In order to get an appropriate induction scheme for the types ``Hydra``
and ``Hydrae``, we can use Coq’s command ``Scheme``.


.. coq::

   Scheme Hydra_rect2 := Induction for Hydra Sort Type
   with Hydrae_rect2 := Induction for Hydrae Sort Type.
   
   About Hydra_rect2. (* .unfold *)

..

A similar principle is generated for sequences of hydras.
   
.. coq::
   
   About Hydrae_rect2. (* .fold *)

..      


A correct proof
^^^^^^^^^^^^^^^^

  Let us now use ``Hydra_rect2`` for proving that the height of any hydra
  is strictly less than its size. Using this scheme requires an auxiliary
  predicate, called ``P0`` in ``Hydra_rect2``’s statement.

  **To do** : The proof of ``height_lt_size`` (in three parts) is not correctly
  indented.

  
  From Module `Hydra.Hydra_Examples <../../../../theories/html/hydras.Hydra.Hydra_Examples.html>`__

 .. coq::
   
       Require Import Max More_Arith Lia. 
   
       (** All elements of s satisfy P *)

       Fixpoint h_forall (P: Hydra -> Prop) (s: Hydrae) :=
       match s with
       |  hnil => True
       | hcons h s' => P h /\ h_forall P s'
       end.

       Lemma height_lt_size (h:Hydra) :  height h < hsize h.
       Proof.
        induction h using Hydra_rect2  with 
        (P0 :=  h_forall (fun h =>  height h < hsize h)). (* .unfold *)

..

.. coq::  none
   
         -  destruct h as [ | h s'].
          + cbn; auto with arith.
          +  simpl.  destruct IHh; assert (lheight s' <= lhsize s').
             { clear H; induction s'. 
               -  cbn; auto with arith. 
               -  simpl; destruct (lheight s').
                + cbn in H0; destruct H0; apply IHs' in H0 .
                  red in H;  transitivity (hsize h0); auto.
                  auto with arith. 
                + cbn in H0; destruct H0. 
                   apply IHs' in H0.
                   clear IHs'; rewrite succ_max_distr; 
                   transitivity (S (height h0) + (S n)).
                   apply max_le_plus; auto.
                   cbn; lia.
            }
            clear H0; cbn; destruct (lheight s').
            *   lia. 
            *   specialize (max_le_plus (height h) n); lia.
      -  easy.   
      -  split;auto.
	 
..    
  
       Three sub-proofs ...
  
.. coq:: 

     Qed. 

..
   
Exercise
^^^^^^^^^

   It happens very often that, in the proof of  a proposition of the form 
   `` forall  h:Hydra, P h``, the predicate ``P0``
   is  just ``h_forall P``.
   Design a tactic for induction on hydras that frees the user from binding
   explicitly ``P0``   and solves trivial subgoals. Apply it for writing
   a shorter proof of ``height_lt_size``.

   
Relational description of hydra battles
---------------------------------------

In this section, we represent the rules of hydra battles as a binary
relation associated with a *round*, i.e., an interaction composed of the
two following actions:

#. Hercules chops off one head of the hydra

#. Then, the hydra replicates the wounded part (if the head is at
   distance :math:`\geq 2` from the foot).

The relation associated with each round of the battle is parameterized
by the *expected* replication factor (irrelevant if the chopped head is
at distance 1 from the foot, but present for consistency’s sake).

In our description, we will apply the following naming convention: if
:math:`h` represents the configuration of the hydra before a round, then
the configuration of :math:`h` after this round will be called
:math:`h'`. Thus, we are going to define a proposition ``round_n n h h'`` whose intended meaning will be “the hydra
:math:`h` is transformed into :math:`h'` in a single round of a battle,
with the expected replication factor :math:`n`”.

Since the replication of parts of the hydra depends on the distance of
the chopped head from the foot, we decompose our description into two
main cases, under the form of a bunch of [mutually] inductive predicates
over the types ``Hydra`` and ``Hydrae``.

The mutually exclusive cases we consider are the following:

-  **R1**: The chopped off head was at distance 1 from the foot.

-  **R2**: The chopped off head was at a distance greater than or equal
   to :math:`2` from the foot.
