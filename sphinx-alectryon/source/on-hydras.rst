========================
Hydras and Hydra Games
========================

-------------
Introduction
-------------

In this part, we present a development for the `\coq{}` proof
assistant, after the work of Kirby and Paris. This formalization
contains the following main parts:

-  Representation in :raw-latex:`\coq{}` of hydras and hydra battles

-  A proof that every battle is finite and won by Hercules. This proof
   is based on a *variant* which maps any hydra to an ordinal strictly
   less than :math:`\epsilon_0` and is strictly decreasing along any
   battle.

-  Using a combinatorial toolkit designed by J. Ketonen and
   R. Solovay :raw-latex:`\cite{KS81}`, we prove that, for any ordinal
   :math:`\mu<\epsilon_0`, there exists no such variant mapping any
   hydra to an ordinal stricly less than :math:`\mu`. Thus, the
   complexity of :math:`\epsilon_0` is really needed in the previous
   proof.

-  We prove a relation between the length of a “classic” class of
   battles  [1]_ and the Wainer-Hardy hierarchy of “rapidly growing
   functions” :math:`H_\alpha` :raw-latex:`\cite{Wainer1970}`. The
   considered class of battles, which we call *standard* is the most
   considered one in the scientific litterature(including
   popularization).

Simply put, this document tries to combine the scientific interest of
two articles :raw-latex:`\cite{KP82, KS81}` and a
book :raw-latex:`\cite{schutte}` with the playful activity of truly
proving theorems. We hope that such a work, besides exploring a nice
piece of discrete maths, will show how :raw-latex:`\coq{}` and its
standard library are well fitted to help us to understand some
non-trivial mathematical developments, and also to experiment the
constructive parts of the proof through functional programming.

We also hope to provide a little clarification on infinity (both
potential and actual) through the notions of function, computation,
limit, type and proof.

Difference from Kirby and Paris’s Work
----------------------------------------

In :raw-latex:`\cite{KP82}`, Kirby and Paris show that there is no proof
of termination of all hydra battles in Peano Arithmetic (PA). Since we
are used to writing proofs in higher order logic, the restriction to PA
was quite unnatural for us. So we chosed to prove another statement
without any reference to PA, by considering a class of proofs indexed by
ordinal numbers up to :math:`\epsilon_0`.

State of the development
------------------------

The :raw-latex:`\coq{}` scripts herein are in constant development since
our contribution :raw-latex:`\cite{CantorContrib}` on notations for the
ordinals :math:`\epsilon_0` and :math:`\Gamma_0`. We added new material
: axiomatic definition of countable ordinals after
Schütte :raw-latex:`\cite{schutte}`, combinatorial aspects of
:math:`\epsilon_0`, after Ketonen and Solovay :raw-latex:`\cite{KS81}`
and Kirby and Paris :raw-latex:`\cite{KP82}`, recent :raw-latex:`\coq{}`
technology: type classes, equations, etc.

We are now working in order to make clumsy proofs more readable,
simplify definitions, and “factorize” proofs as much as possible. Many
possible improvements are suggested as “todo”s or “projects” in this
text.

Future work (projects)
----------------------

:raw-latex:`\index{hydras}{Projects}`

This document and the proof scripts are far from being complete.

First, there must be a lot of typos to correct, references and index
items to add. Many proofs are too complex and should be simplified, etc.

The following extensions are planned, but help is needed:

-  Semi automatic tactics for proving inequalities
   :math:`\alpha < \beta`, even when :math:`\alpha` and :math:`\beta`
   are not closed terms.

-  Extension to :math:`\Gamma_0` (in Veblen normal form)

-  More lemmas about hierarchies of rapidly growing functions, and their
   relationship with primitive recursive functions and provability in
   Peano arithmetic (following :raw-latex:`\cite{KS81, KP82}`).

-  From :raw-latex:`\coq`’s point of view, this development could be
   used as an illustration of the evolution of the software, every time
   new libraries and sets of tactics could help to simplify the proofs.

Main references
----------------

In our development, we adapt the definitions and prove many theorems
which we found in the following articles.

-  “Accessible independence results for Peano arithmetic” by Laurie
   Kirby and Jeff Paris :raw-latex:`\cite{KP82}`

-  ”Rapidly growing Ramsey Functions” by Jussi Ketonen and Robert
   Solovay :raw-latex:`\cite{KS81}`

-  “The Termite and the Tower”, by Will
   Sladek :raw-latex:`\cite{Sladek07thetermite}`

-  Chapter V of “Proof Theory” by Kurt
   Schütte :raw-latex:`\cite{schutte}`

.. _sec:orgheadline91:

------------------------------------------------
Hydras and their representation in *Coq*
------------------------------------------------

This chapter is dedicated to the representation of hydras and rules of
the hydra game in :raw-latex:`\coq`’s specification
language: :raw-latex:`\gallina`.

Technically, a *hydra* is just a finite ordered tree, each node of which
has any number of sons. Contrary to the computer science tradition, we
display the hydras with the heads up and the foot (i.e., the root of the
tree) down. Fig. :raw-latex:`\ref{fig:Hy}` represents such a hydra,
which will be referred to as ``Hy`` in our examples (please look at the
module `Hydra.Hydra_Examples <../../../../theories/html/hydras.Hydra.Hydra_Examples.html>`__).
*For a less formal description of hydras, please
see*\ https://www.smbc-comics.com/comic/hydra\ *.*




   :alectryon/serapi/args: -R ../../theories/ordinals hydras

In order to describe trees where each node can have an arbitrary (but
finite) number of sons, it is usual to define a type where each node
carries a *forest*, *i.e* a list of trees (see for instance Chapter 14,
pages 400-406 of :raw-latex:`\cite{BC04}`).

For this purpose, we define two mutual *ad-hoc* inductive types, where
``Hydra`` is the main type, and ``Hydrae`` is a helper for describing
finite sequences of hydras. :raw-latex:`\label{types:Hydra}`
:raw-latex:`\label{types:Hydrae}`
			   
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
+++++++

.. coq::
   
   Example Hy := hyd3 head
                      (hyd2
                         (hyd1 
                            (hyd2 head head))
                         head) 
                      head.

Recursive Definitions on type ``Hydra``
---------------------------------------


In order to define a recursive function over the type ``Hydra``, one has
to consider the three constructors ``node``, ``hnil`` and ``hcons`` of
the mutually inductive types ``Hydra`` and ``Hydrae``. Let us define for
instance the function which computes the number of nodes of any hydra:

From Module \ `Hydra.Hydra_Definitions <../../../../theories/html/hydras.Hydra.Hydra_Definitions.html>`__
   
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


Exercise
+++++++++

   Define a function ``max_degree: Hydra ->  nat`` which  returns the
   highest degree of a node in any hydra.
   For instance, the evaluation of the term ``max_degree Hy``
   should return ``3``.
 

Induction principles for hydras
-------------------------------

    In this section, we show how induction principles are used to prove
    properties on the type ``Hydra``. Let us consider for instance the
    following statement:

     “The height of any hydra is strictly less than its size.”
     


A failed attempt
++++++++++++++++


 One may try to use the default tactic of proof by induction, which
   corresponds to an application of the automatically generated induction
   principle for type ``Hydra``:

.. coq::

   About Hydra_ind. (* .no-in .unfold *)

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
++++++++++++++++++++++++++++++++

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
++++++++++++++++

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
.. coq::
   
	 (** ... *)
        Qed. 

   
Exercise
+++++++++

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


   
Chopping off a head at distance 1 from the foot (relation R1)
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

If Hercules chops off a head near the floor, there is no replication at
all. We use an auxiliary predicate ``S0``, associated with the removing
of one head from a sequence of hydras.



From Module `Hydra.Hydra_Definitions <../../../../theories/html/hydras.Hydra.Hydra_Definitions.html>`__

.. coq::
   
   Inductive S0 :  relation Hydrae :=
   | S0_first : forall s, S0  (hcons head s) s
   | S0_rest : forall  h s s',  S0  s s' ->
                                S0  (hcons h s) (hcons h s').

   Inductive R1  :  Hydra -> Hydra -> Prop :=
   | R1_intro : forall s s', S0 s s' -> R1 (node s) (node s').


Example
++++++++

 Let us represent in *Coq* the transformation of the hydra
 of Fig. `\vref{fig:Hy}` into the configuration represented in
 Fig.`\ref{fig:Hy-prime}`.



From 
Module `Hydra.Hydra_Examples <../../../../theories/html/hydras.Hydra.Hydra_Examples.html>`__

.. coq::
  
   Example Hy' := hyd2 head
                      (hyd2
                         (hyd1 
                            (hyd2 head head))
                         head).

   Lemma Hy_1 : R1 Hy Hy'.
   Proof. 
     split; right; right; left.
   Qed.
..



.. coq::

   Example Hy'' := 
        hyd2 head
             (hyd2 (hyd_mult (hyd1 head) 5)
                   head).
