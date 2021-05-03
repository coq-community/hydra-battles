   :alectryon/serapi/args: -R ../../theories/ordinals hydras
			   
##########################
Hydras and Hydra Battles
##########################


*********************
Introduction
*********************


In this part, we present a development for the :raw-latex:`\coq{}` proof
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
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In :raw-latex:`\cite{KP82}`, Kirby and Paris show that there is no proof
of termination of all hydra battles in Peano Arithmetic (PA). Since we
are used to writing proofs in higher order logic, the restriction to PA
was quite unnatural for us. So we chosed to prove another statement
without any reference to PA, by considering a class of proofs indexed by
ordinal numbers up to :math:`\epsilon_0`.

State of the development
~~~~~~~~~~~~~~~~~~~~~~~~

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
~~~~~~~~~~~~~~~

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

****************************
Hydras in *Coq*
****************************


This chapter is dedicated to the representation of hydras and rules of
the hydra game in :raw-latex:`\coq`’s specification
language: :raw-latex:`\gallina`.

Technically, a *hydra* is just a finite ordered tree, each node of which
has any number of sons. Contrary to the computer science tradition, we
display the hydras with the heads up and the foot (i.e., the root of the
tree) down. Fig. :raw-latex:`\ref{fig:Hy}` represents such a hydra,
which will be referred to as ``Hy`` in our examples (please look at the
module `Hydra.Hydra_Examples <../theories/html/hydras.Hydra.Hydra_Examples.html>`__).
*For a less formal description of hydras, please
see*\ https://www.smbc-comics.com/comic/hydra\ *.*

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.6]

   \node (foot) at (2,0) {$\bullet$};
   \node (N1) at (2,2) {$\bullet$};
   \node (N2) at (2,4) {$\bullet$};
   \node (N3) at (2,6) {$\bullet$};
   \node (H0) at (0,2) {$\Smiley[2][vertfluo]$};
   \node (H1) at (0,8) {$\Smiley[2][vertfluo]$};
   \node (H2) at (4,8) {$\Smiley[2][vertfluo]$};
   \node (H4) at (4,2) {$\Smiley[2][vertfluo]$};
   \node (H5) at (4,4) {$\Smiley[2][vertfluo]$};
   \draw (foot) -- (N1)[very thick] ;
   \draw (N1) -- (N2);
   \draw (N2) -- (N3);
   \draw (N3) to [bend left= 10]  (H1) ;
   \draw (N3) to [bend right= 16] (H2);
   \draw (foot) to [bend left= 10]  (H0) ;
   \draw (foot) to [bend right = 10] (H4) ;
   \draw (N1) to [bend right= 16] (H5);
   \end{tikzpicture}

We use a specific vocabulary for talking about hydras.
Table :raw-latex:`\ref{tab:hyd2tree}` shows the correspondance between
our terminology and the usual vocabulary for trees in computer science.

.. raw:: latex

   \centering

========= ===================
Hydras    Finite rooted trees
========= ===================
foot      root
head      leaf
node      node
segment   (directed) edge
sub-hydra subtree
daughter  immediate subtree
========= ===================

The hydra ``Hy`` has a *foot* (below), five *heads*, and eight
*segments*. We leave it to the reader to define various parameters such
as the height, the size, the highest arity (number of sons of a node) of
a hydra. In our example, these parameters have the respective values :
:math:`4`, :math:`9` and :math:`3`.

.. _sec:orgheadline44:

The rules of the game
~~~~~~~~~~~~~~~~~~~~~

:raw-latex:`\label{sect:replication-def}`

A *hydra battle* is a fight between Hercules and the Hydra. More
formally, a battle is a sequence of *rounds*. At each round:

-  If the hydra is composed of just one head, the battle is finished and
   Hercules is the winner.

-  Otherwise, Hercules chops off *one* head of the hydra,

   -  If the head is at distance 1 from the foot, the head is just lost
      by the hydra, with no more reaction.

   -  Otherwise, let us denote by :math:`r` the node that was at
      distance :math:`2` from the removed head in the direction of the
      foot, and consider the sub-hydra :math:`h'` of :math:`h`, whose
      root is :math:`r`  [2]_. Let :math:`n` be some natural number.
      Then :math:`h'` is replaced by :math:`n+1` of copies of :math:`h'`
      which share the same root :math:`r`. The *replication factor*
      :math:`n` may be different (and generally is) at each round of the
      fight. It may be chosen by the hydra, according to its strategy,
      or imposed by some particular rule. In many presentations of hydra
      battles, this number is increased by :math:`1` at each round. In
      the following presentation, we will also consider battles where
      the hydra is free to choose its  replication factor at each round
      of the battle [3]_.

Note that the description given in :raw-latex:`\cite{KP82}` of the
replication process in hydra battles is also semi-formal.

:raw-latex:`\label{original-rules}`

   “From the node that used to be attached to the head which was just
   chopped off, traverse one segment towards the root until the next
   node is reached. From this node sprout :math:`n` replicas of that
   part of the hydra (after decapitation) which is “above” the segment
   just traversed, i.e., those nodes and segments from which, in order
   to reach the root, this segment would have to be traversed. If the
   head just chopped off had the root of its nodes, no new head is
   grown.”

Moreover, we note that this description is in *imperative* terms. In
order to build a formal study of the properties of hydra battles, we
prefer to use a mathematical vocabulary, i.e., graphs, relations,
functions, etc. Thus, the replication process will be represented as a
binary relation on a data type ``Hydra``, linking the state of the hydra
*before* and *after* the transformation. A battle will thus be
represented as a sequence of terms of type ``Hydra``, respecting the
rules of the game.

Example
~~~~~~~

Let us start a battle between Hercules and the hydra ``Hy`` of
Fig. :raw-latex:`\ref{fig:Hy}`.

At the first round, Hercules choses to chop off the rightmost head of
``Hy``. Since this head is near the floor, the hydra simply loses this
head. Let us call ``Hy’`` the resulting state of the hydra, represented
in Fig. :raw-latex:`\vref{fig:Hy-prime}`.

Next, assume Hercules choses to chop off one of the two highest heads of
``Hy’``, for instance the rightmost one.
Fig. :raw-latex:`\vref{fig:Hy2}` represents the broken segment in dashed
lines, and the part that will be replicated in red. Assume also that the
hydra decides to add 4 copies of the red part [4]_. We obtain a new
state ``Hy”`` depicted in Fig. :raw-latex:`\ref{fig:Hy3}`.

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.6]

   \node (foot) at (2,0) {$\bullet$};
   \node (N1) at (2,2) {$\bullet$};
   \node (N2) at (2,4) {$\bullet$};
   \node (N3) at (2,6) {$\bullet$};
   \node (H0) at (0,2) {$\Smiley[2][vertfluo]$};
   \node (H1) at (0,8) {$\Smiley[2][vertfluo]$};
   \node (H2) at (4,8) {$\Smiley[2][vertfluo]$};
   \node (H5) at (4,4) {$\Smiley[2][vertfluo]$};
   %\node (H4) at (6,0) {$\Xey[2][lightgray]$};
   \draw (foot) -- (N1)[very thick] ;
   \draw (N1) -- (N2);
   \draw (N2) -- (N3) ;
   \draw (N3) to [bend left= 10]  (H1) ;
   \draw (N3) to [bend right= 16] (H2);
   \draw (foot) to [bend left= 10]  (H0) ;
   \draw (N1) to [bend right= 16] (H5);
   \end{tikzpicture}

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.5]

   \node (foot) at (2,0) {$\bullet$};
   \node (N1) at (2,2) {$\bullet$};
   \node (N2) at (2,4)  {{\color{lightred}$\bullet$}};
   \node (N3) at (2,6) {{\color{lightred}$\bullet$}};
   \node (H0) at (0,2) {$\Smiley[2][vertfluo]$};
   \node (H1) at (0,8) {$\Sey[2][lightred]$};
   %\node (H2) at (5,0) {$\Xey[2][lightgray]$};
   \node (H5) at (4,4) {$\Smiley[2][vertfluo]$};
   \node (ex) at (5,8) {};
   \draw (foot) -- (N1)[very thick] ;
   \draw (N1) -- (N2);
   \draw  (N2) -- (N3)[draw=lightred];
   \draw (N3) to   [bend left= 10](H1) [draw=lightred];
   \draw [dashed] (N3) to [bend left= 10](ex);
   \draw (foot) to [bend left= 10]  (H0) ;
   \draw (N1) to [bend right= 16] (H5);
   \end{tikzpicture}

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.6]

   \node (foot) at (2,0) {$\bullet$};
   \node (N1) at (2,2) {$\bullet$};
   \node (N2) at (2,4) {$\bullet$};
   \node (N3) at (2,6) {{\color{lightred}$\bullet$}};
   \node (H1) at (0,8) {$\Smiley[2][vertfluo]$};
   \node (H11) at (2,8) {$\Smiley[2][vertfluo]$};
   \node (H12) at (4,8) {$\Smiley[2][vertfluo]$};
   \node (H13) at (6,8) {$\Smiley[2][vertfluo]$};
   \node (H14) at (8,8) {$\Smiley[2][vertfluo]$};

   \node (N3) at (1,6) {$\bullet$};
   \node (N31) at (2,6) {$\bullet$};
   \node (N32) at (3,6) {$\bullet$};
   \node (N33) at (4,6) {$\bullet$};
   \node (N34) at (5,6) {$\bullet$};

   \node (H0) at (0,2) {$\Smiley[2][vertfluo]$};
   \node (H5) at (4,4) {$\Smiley[2][vertfluo]$};
   \draw (foot) -- (N1)[very thick] ;
   \draw (N1) -- (N2);
   \draw (N2) -- (N3);
   \draw (N2) -- (N31);
   \draw (N2) -- (N32);
   \draw (N2) -- (N33);
   \draw (N2) -- (N34);
   \draw (N3) to   [bend left= 10](H1) ;
   \draw (N31) to   [bend left= 10](H11) ;
   \draw (N32) to   [bend left= 10](H12) ;
   \draw (N33) to   [bend left= 10](H13) ;
   \draw (N34) to   [bend left= 10](H14) ;
   \draw (foot) to [bend left= 10]  (H0) ;
   \draw (N1) to [bend left= 10]  (H5) ;
   \end{tikzpicture}

Figs. :raw-latex:`\ref{fig:Hy4}` and :raw-latex:`\vref{fig:Hy5}`
represent a possible third round of the battle, with a replication
factor equal to :math:`2`. Let us call ``Hy”’`` the state of the hydra
after that third round.

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.6]

   \node (foot) at (2,0)  {{\color{lightred}$\bullet$}};
   \node (N1) at (2,2) {{\color{lightred}$\bullet$}};
   \node (N2) at (2,4) {{\color{lightred}$\bullet$}};
   \node (N3) at (2,6) {{\color{lightred}$\bullet$}};
   \node (exN4) at (4,4) {};
   \node (H1) at (0,8) {$\Sey[2][lightred]$};
   \node (H11) at (2,8) {$\Sey[2][lightred]$};
   \node (H12) at (4,8) {$\Sey[2][lightred]$};
   \node (H13) at (6,8) {$\Sey[2][lightred]$};
   \node (H14) at (8,8) {$\Sey[2][lightred]$};

   \node (N3) at (1,6) {{\color{lightred}$\bullet$}};
   \node (N31) at (2,6) {{\color{lightred}$\bullet$}};
   \node (N32) at (3,6) {{\color{lightred}$\bullet$}};
   \node (N33) at (4,6) {{\color{lightred}$\bullet$}};
   \node (N34) at (5,6) {{\color{lightred}$\bullet$}};

   \node (H0) at (0,2) {$\Smiley[2][vertfluo]$};
   %\node (H5) at (4,0) {$\Xey[2][lightgray]$};
   \draw (foot) -- (N1)[very thick,draw=lightred] ;
   \draw (N1) -- (N2)[draw=lightred];
   \draw (N2) -- (N3)[draw=lightred];
   \draw (N2) -- (N31)[draw=lightred];
   \draw (N2) -- (N32)[draw=lightred];
   \draw (N2) -- (N33)[draw=lightred];
   \draw (N2) -- (N34)[draw=lightred];
   \draw (N3) to   [bend left= 10](H1) [draw=lightred];
   \draw (N31) to   [bend left= 10](H11) [draw=lightred];
   \draw (N32) to   [bend left= 10](H12) [draw=lightred];
   \draw (N33) to   [bend left= 10](H13) [draw=lightred];
   \draw (N34) to   [bend left= 10](H14) [draw=lightred];
   \draw (foot) to [bend left= 10]  (H0) ;
   \draw [dashed] (N1) to  [bend left= 10](exN4);
   \end{tikzpicture}

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.4]

   \node (foot) at (10,0) {$\bullet$};


   \node (N1) at (2,2) {$\bullet$};
   \node (N2) at (2,4) {$\bullet$};
   \node (N3) at (2,6) {{\color{lightred}$\bullet$}};
   \node (H1) at (0,8) {$\Smiley[1][vertfluo]$};
   \node (H11) at (2,8) {$\Smiley[1][vertfluo]$};
   \node (H12) at (4,8) {$\Smiley[1][vertfluo]$};
   \node (H13) at (6,8) {$\Smiley[1][vertfluo]$};
   \node (H14) at (8,8) {$\Smiley[1][vertfluo]$};

   \node (N3) at (1,6) {$\bullet$};
   \node (N31) at (2,6) {$\bullet$};
   \node (N32) at (3,6) {$\bullet$};
   \node (N33) at (4,6) {$\bullet$};
   \node (N34) at (5,6) {$\bullet$};

   \node (H0) at (-3,3) {$\Smiley[1][vertfluo]$};

   \draw (foot) to [bend left=10] (N1)[very thick] ;
   \draw (N1) -- (N2);
   \draw (N2) -- (N3);
   \draw (N2) -- (N31);
   \draw (N2) -- (N32);
   \draw (N2) -- (N33);
   \draw (N2) -- (N34);
   \draw (N3) to   [bend left= 10](H1) ;
   \draw (N31) to   [bend left= 10](H11) ;
   \draw (N32) to   [bend left= 10](H12) ;
   \draw (N33) to   [bend left= 10](H13) ;
   \draw (N34) to   [bend left= 10](H14) ;
   \draw (foot) to [bend left = 15]  (H0) ;


   % second copy 
   \node (N01) at (12,2) {$\bullet$};
   \node (N02) at (12,4) {$\bullet$};
   \node (N03) at (12,6) {{\color{lightred}$\bullet$}};
   \node (H001) at (10,8) {$\Smiley[1][vertfluo]$};
   \node (H0011) at (12,8) {$\Smiley[1][vertfluo]$};
   \node (H0012) at (14,8) {$\Smiley[1][vertfluo]$};
   \node (H0013) at (16,8) {$\Smiley[1][vertfluo]$};
   \node (H0014) at (18,8) {$\Smiley[1][vertfluo]$};

   \node (N03) at (11,6) {$\bullet$};
   \node (N031) at (12,6) {$\bullet$};
   \node (N032) at (13,6) {$\bullet$};
   \node (N033) at (14,6) {$\bullet$};
   \node (N034) at (15,6) {$\bullet$};

   \draw (foot) -- (N01)[very thick] ;
   \draw (N01) -- (N02);
   \draw (N02) -- (N03);
   \draw (N02) -- (N031);
   \draw (N02) -- (N032);
   \draw (N02) -- (N033);
   \draw (N02) -- (N034);
   \draw (N03) to   [bend left= 10](H001) ;
   \draw (N031) to   [bend left= 10](H0011) ;
   \draw (N032) to   [bend left= 10](H0012) ;
   \draw (N033) to   [bend left= 10](H0013) ;
   \draw (N034) to   [bend left= 10](H0014) ;

   % third copy 
   \node (N001) at (22,2) {$\bullet$};
   \node (N002) at (22,4) {$\bullet$};
   \node (N003) at (22,6) {{\color{lightred}$\bullet$}};
   \node (H001) at (20,8) {$\Smiley[1][vertfluo]$};
   \node (H0011) at (22,8) {$\Smiley[1][vertfluo]$};
   \node (H0012) at (24,8) {$\Smiley[1][vertfluo]$};
   \node (H0013) at (26,8) {$\Smiley[1][vertfluo]$};
   \node (H0014) at (28,8) {$\Smiley[1][vertfluo]$};

   \node (N003) at (21,6) {$\bullet$};
   \node (N0031) at (22,6) {$\bullet$};
   \node (N0032) at (23,6) {$\bullet$};
   \node (N0033) at (24,6) {$\bullet$};
   \node (N0034) at (25,6) {$\bullet$};

   \draw (foot) -- (N001)[very thick] ;
   \draw (N001) -- (N002);
   \draw (N002) -- (N003);
   \draw (N002) -- (N0031);
   \draw (N002) -- (N0032);
   \draw (N002) -- (N0033);
   \draw (N002) -- (N0034);
   \draw (N003) to   [bend left= 10](H001) ;
   \draw (N0031) to   [bend left= 10](H0011) ;
   \draw (N0032) to   [bend left= 10](H0012) ;
   \draw (N0033) to   [bend left= 10](H0013) ;
   \draw (N0034) to   [bend left= 10](H0014) ;
   \end{tikzpicture}

.. raw:: latex

   \FloatBarrier

We leave it to the reader to guess the following rounds of the battle …

.. _sec:orgheadline48:

Hydras and their representation in *Coq*
----------------------------------------

:raw-latex:`\index{hydras}{Library Hydra!Types!Hydra}`
:raw-latex:`\index{hydras}{Library Hydra!Types!Hydrae}`

In order to describe trees where each node can have an arbitrary (but
finite) number of sons, it is usual to define a type where each node
carries a *forest*, *i.e* a list of trees (see for instance Chapter 14,
pages 400-406 of :raw-latex:`\cite{BC04}`).

For this purpose, we define two mutual *ad-hoc* inductive types, where
``Hydra`` is the main type, and ``Hydrae`` is a helper for describing
finite sequences of hydra. :raw-latex:`\label{types:Hydra}`
:raw-latex:`\label{types:Hydrae}`

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent` *From
Module *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html#Hydra>`__

.. coq::
   
   Require Import Hydra_Definitions.
 
   Print Hydra. (* .out .unfold *)


   
Exercise
^^^^^^^^^^
	    
         Look for an existing library on trees with nodes of
         arbitrary arity, in order to replace  this ad-hoc type
         with something more generic.



Project
^^^^^^^
  
    Another very similar representation could use the \texttt{list}    type family instead of the specific  type \texttt{Hydrae}:

 .. coq::
    
    Module Alt. (* .none *)

     Inductive Hydra: Set :=
           hnode (daughters : list Hydra).

     End Alt. (* .none *)
 ..
 
    Using this representation, re-define all the constructions
    of this chapter.  You will probably have to use patterns
     describe    for instance in~\cite{BC04} or the archives of
     the Coq-club~\cite{Coq}.


Project
^^^^^^^
   The type \texttt{Hydra} above describes hydras as \emph{plane trees}, i.e., as drawn on a sheet of paper or computer screen.    Thus, hydras are \emph{oriented},
   and it is appropriate to consider a \emph{leftmost} or \emph{rightmost} head of
   the beast. It could be interesting to consider another representation, in which
   every non-leaf node has a \emph{multi-set} -- not an ordered list -- of daughters.


Abbreviations
^^^^^^^^^^^^^

We provide several notations for hydra patterns which occur often in our
developments.

*From
Module *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html#head>`__

.. coq::
   
   (** heads *)
   Notation head := (node hnil).
    
   (** nodes  with 1, 2 or 3 daughters *)
   Notation hyd1 h := (node (hcons h hnil)).
   Notation hyd2 h h' := (node (hcons h (hcons h' hnil))).
   Notation hyd3 h h' h'' := 
                      (node (hcons h (hcons h' (hcons h'' hnil)))).

For instance, the hydra ``Hy`` of Figure :raw-latex:`\vref{fig:Hy}` is
defined in *Gallina* as follows:

.. raw:: latex

   \vspace{4mm}

:raw-latex:`\noindent` *From
Module *\ `Hydra.Hydra_Examples <../theories/html/hydras.Hydra.Hydra_Examples.html#Hy>`__

.. coq::
   
    Example Hy :=
       hyd3 head
               (hyd2
                  (hyd1 
                      (hyd2 head head))
                      head) 
                  head.


Hydras quite frequently contain multiple adjacent copies of the same
subtree. The following functions will help us to describe and reason
about replications in hydra battles.


*From
Module *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html#hcons_mult>`__

.. coq::
   
   Fixpoint hcons_mult (h:Hydra)(n:nat)(s:Hydrae):Hydrae :=
     match n with 
     | O => s
     | S p => hcons h (hcons_mult h p s)
     end.

   (** A node with n clones of the same daughter *)

    Definition hyd_mult h n :=
     node (hcons_mult h n hnil).


For instance, the hydra :math:`Hy''` of Fig :raw-latex:`\vref{fig:Hy3}`
can be defined in :raw-latex:`\coq{}` as follows:

.. coq::
   
   Example Hy'' := 
        hyd2 head
             (hyd2 (hyd_mult (hyd1 head) 5)
                   head).



Recursive functions on type ``Hydra``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:raw-latex:`\label{sec:hsize-def}`

In order to define a recursive function over the type ``Hydra``, one has
to consider the three constructors ``node``, ``hnil`` and ``hcons`` of
the mutually inductive types ``Hydra`` and ``Hydrae``. Let us define for
instance the function which computes the number of nodes of any hydra:


*From
Module *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html>`__

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
 
   Compute height Hy.
 
Exercise
^^^^^^^

   Define a function ``max_degree: Hydra -> nat`` which  returns the highest degree of a node in any hydra. For instance, the evaluation of the term ``max_degree Hy`` should return ``3``.


Induction principles for hydras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In this section, we show how induction principles are used to prove
properties on the type ``Hydra``. Let us consider for instance the
following statement:

   “The height of any hydra is strictly less than its size.”

A failed attempt
^^^^^^^^^^^^^^^^

One may try to use the default tactic of proof by induction, which
corresponds to an application of the automatically generated induction
principle for type ``Hydra``:

.. coq::

   About Hydra_ind. (* .no-in .unfold *)


Ler us start a simple proof by induction.

 *From
Module *\ `Hydra.Hydra_Examples <../theories/html/hydras.Hydra.Hydra_Examples.html>`__

.. coq::
   
   Require Import Arith. (* . none *)
   
   Lemma height_lt_size (h:Hydra) :
     height h <= hsize h.
   Proof.
     induction h as [s]. (* .unfold *)


Let us try now to do an induction on the sequence ``s``:

.. coq::

   induction s; [cbn; auto with arith | ]. (* .unfold *)

   


Note that the displayed subgoal does not contain any assumption on
``h``, thus there is no way to infer any property about the height and
size of the hydra ``(hcons h t)``.

.. coq::

   Abort.


A Principle of mutual induction
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In order to get an appropriate induction scheme for the types ``Hydra``
and ``Hydrae``, we can use :raw-latex:`\coq{}`’s command ``Scheme``.

.. coq::
   
   Scheme Hydra_rect2 := Induction for Hydra Sort Type
   with Hydrae_rect2 := Induction for Hydrae Sort Type.

   Check Hydra_rect2. (* .unfold .no-in  *)

   Check Hydrae_rect2. (*  .unfold .no-in *)

A Correct proof
^^^^^^^^^^^^^^^

Let us now use ``Hydra_rect2`` for proving that the height of any hydra
is strictly less than its size. Using this scheme requires an auxiliary
predicate, called ``P0`` in ``Hydra_rect2``\ ’s statement.


 *From
Module *\ `Hydra.Hydra_Examples <../theories/html/hydras.Hydra.Hydra_Examples.html>`__

.. coq::
   
   (** All elements of s satisfy P *)

   Fixpoint h_forall (P: Hydra -> Prop) (s: Hydrae) :=
     match s with
         hnil => True
       | hcons h s' => P h /\ h_forall P s'
     end.
 
   Lemma  height_lt_size (h:Hydra) :  height h < hsize h.
   Proof.
     induction h using Hydra_rect2  with 
        (P0 :=  h_forall (fun h =>  height h < hsize h)).
     -  destruct h as [ | h s'].
	(** ... *)
..

.. coq:: none
	 
       + cbn; auto with arith.
       +  cbn;  destruct IHh; assert (lheight s' <= lhsize s').
          { clear H; induction s'. 
             -     cbn; auto with arith. 
             -     simpl.  destruct (lheight s').
                 + cbn in H0; destruct H0; apply IHs' in H0 .
                     red in H;  transitivity (hsize h0); auto.
                     auto with arith. 
                 + cbn in H0; destruct H0. 
                    apply IHs' in H0.    clear IHs'.            
                    rewrite succ_max_distr; 
                      transitivity (S (height h0) + (S n)).
                      apply max_le_plus; auto.
                      cbn; lia.
          }
          clear H0; cbn; destruct (lheight s').
          *   lia. 
          *   specialize (max_le_plus (height h) n); lia.
..

.. coq::
   
     -  easy.   
     -  split;auto. 
   Qed.

Exercise
^^^^^^^

It happens very often that, in the proof of  a proposition of
the form  ``forall h:Hydra, P h`` using ``Hydra_rect2``,
the predicate ``P0`` is instancied to ``h_forall P`` .
Design a tactic for induction on hydras that frees the user
from giving explicitly  ``P0``,  and solves trivial subgoals.
Apply it for writing  a shorter proof of ``height_lt_size`` .




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
:math:`h'`. Thus, we are going to define a proposition
(``round_n n\;h\;h'``) whose intended meaning will be “the hydra
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
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If Hercules chops off a head near the floor, there is no replication at
all. We use an auxiliary predicate ``S0``, associated with the removing
of one head from a sequence of hydras.

.. raw:: latex

   \vspace{4pt}

*From
Module\ *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Inductive S0 :  relation Hydrae :=
   | S0_first : forall s, S0  (hcons head s) s
   | S0_rest : forall  h s s',  S0  s s' ->
                                S0  (hcons h s) (hcons h s').

   Inductive R1  :  Hydra -> Hydra -> Prop :=
   | R1_intro : forall s s', S0 s s' -> R1 (node s) (node s').
   \end{Coqsrc}

.. _sec:orgheadline45:

Example
^^^^^^^

Let us represent in :raw-latex:`\coq{}` the transformation of the hydra
of Fig. :raw-latex:`\vref{fig:Hy}` into the configuration represented in
Fig. :raw-latex:`\ref{fig:Hy-prime}`.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Hydra_Examples <../theories/html/hydras.Hydra.Hydra_Examples.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Example Hy_1 : R1 Hy Hy'.
   Proof. 
     split; right; right; left.
   Qed.
   \end{Coqsrc}

Chopping off a head at distance :math:`\geq 2` from the foot (relation R2) 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Let us now consider beheadings where the chopped-off head is at distance
greater than or equal to :math:`2` from the foot. All the following
relations are parameterized by the replication factor :math:`n`.

Let :math:`s` be a sequence of hydras. The proposition (``S1 n s s’``)
holds if :math:`s'` is obtained by replacing some element :math:`h` of
:math:`s` by :math:`n+1` copies of :math:`h'`, where the proposition
(``R1 h h’``) holds, in other words, :math:`h'` is just :math:`h`,
without the chopped-off head. ``S1`` is an inductive relation with two
constructors that allow us to choose the position in :math:`s'` of the
wounded sub-hydra :math:`h`.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent` *From
Module *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html#S1>`__

.. raw:: latex

   \begin{Coqsrc}
   Inductive S1 (n:nat)  : Hydrae -> Hydrae -> Prop :=
   | S1_first : forall s h h' ,   R1 h h' -> 
                     S1 n (hcons h s) (hcons_mult h' (S n) s)
   | S1_next : forall h s s',  S1 n s s' ->
                      S1 n (hcons h s) (hcons h s').
   \end{Coqsrc}

The rest of the definition is composed of two mutually inductive
relations on hydras and sequences of hydras. The first constructor of
``R2`` describes the case where the chopped head is exactly at height
:math:`2`. The others constructors allow us to consider beheadings at
height strictly greater than :math:`2`.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html#R2>`__

.. raw:: latex

   \begin{Coqsrc}
   Inductive R2 (n:nat)  :  Hydra -> Hydra -> Prop :=
   | R2_intro : forall s s', S1 n s s' -> R2 n (node s) (node s')
   | R2_intro_2 : forall s s', S2 n s s' -> R2 n (node s) (node s')

   with S2 (n:nat) :  Hydrae -> Hydrae -> Prop :=
   |  S2_first : forall h h' s ,
                  R2 n  h h'  -> 
                  S2  n (hcons h s) (hcons h'  s)
   |  S2_next  : forall h   r r',
                  S2 n   r r' ->
                  S2 n (hcons h r) (hcons h r').                  
   \end{Coqsrc}

.. _example-1:

Example
^^^^^^^

Let us prove the transformation of ``Hy’`` into ``Hy”`` (see
Fig. :raw-latex:`\vref{fig:Hy3}`). We use an experimental set of tactics
for specifying the place where the interaction between Hercules and the
hydra holds.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Hydra_Examples <../theories/html/hydras.Hydra.Hydra_Examples.html>`__.

.. raw:: latex

   \begin{Coqsrc}
   Example R2_example:  R2 4 Hy' Hy''.
   Proof.
       (** move to 2nd sub-hydra (0-based indices) *) R2_up 1. 
       (** move to first sub-hydra *)  R2_up 0.
       (** we're at distance 2 from the to-be-chopped-off head 
           let's go to the first daughter, 
           then chop-off the leftmost head *)  r2_d2  0 0. 
   Qed.
   \end{Coqsrc}

The reader is encouraged to look at all the successive subgoals of this
example. *Please consider also
exercise :raw-latex:`\vref{exo:interactive-battle}`.*

Binary relation associated with a round
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We combine the two cases above into a single relation. First, we define
the relation ``(round_n n h h’)`` where ``n`` is the expected number of
replications (irrelevant in the case of an ``R1``-transformation).

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html#round_n>`__

:raw-latex:`\index{hydras}{Library Hydra!Predicates!round\_n}`

.. raw:: latex

   \begin{Coqsrc}
   Definition round_n n h h' := R1 h h' \/ R2 n h h'.  
   \end{Coqsrc}

By abstraction over ``n``, we define a *round* (small step) of a battle:

:raw-latex:`\index{hydras}{Library Hydra!Predicates!round}`
:raw-latex:`\label{sect:infix-round}`

.. raw:: latex

   \begin{Coqsrc}
   Definition round h h' := exists n,  round_n n h h'.

   Infix "-1->" := round (at level 60).
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Give a direct translation of Kirby and Paris's description of hydra battles (quoted on page~\pageref{original-rules}) and prove that our relational description is consistent with theirs.
   \end{project}

Rounds and battles
~~~~~~~~~~~~~~~~~~

Using library
`Relations.Relation_Operators <https://coq.inria.fr/distrib/current/stdlib/Coq.Relations.Relation_Operators.html>`__,
we define ``round_plus``, the transitive closure of ``round``, and
``round_star``, the reflexive and transitive closure of ``round``.

:raw-latex:`\label{sect:infix-rounds}`

.. raw:: latex

   \begin{Coqsrc}
   Definition round_plus := clos_trans_1n Hydra round.
   Infix "-+->" := rounds (at level 60).

   Definition round_star h h' := h = h' \/ round_plus h h'.
   Infix "-*->" := round_star (at level 60).
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove the following lemma:

   \begin{Coqsrc}
   Lemma rounds_height : forall h h', 
      h -+-> h' -> height h' <= height h.  
   \end{Coqsrc}
     
   \end{exercise}

.. raw:: latex

   \begin{remark}
   \label{remark:transitive-closure}
   \coq's library \href{https://coq.inria.fr/distrib/current/stdlib/Coq.Relations.Relation_Operators.html}{Coq.Relations.Relation\_Operators} 
   contains three logically equivalent definitions of the transitive closure of a binary relation. This equivalence is proved in 
   \href{https://coq.inria.fr/distrib/current/stdlib/Coq.Relations.Operators_Properties.html}{Coq.Relations.Operators\_Properties} . 

   Why three definitions for a single mathematical concept?
   Each definition generates an associated induction principle. 
    According to the form of statement one would like to prove, there is a ``best choice'':

   \begin{itemize}
   \item For proving $\forall y, x\,R^+\,y \;\arrow\; P\,y$, prefer 
   \texttt{clos\_trans\_n1}
   \item For proving $\forall x,\,x\,R^+\,y \;\arrow\; P\,x$, prefer \texttt{clos\_trans\_1n}
   \item For proving $\forall x\,y, \,x\,R^+\,y \;\arrow\;P\,x\,y$,  
   prefer \texttt{clos\_trans},
   \end{itemize}
   But there is no ``wrong choice'' at all: the equivalence lemmas in \linebreak 
   \href{https://coq.inria.fr/distrib/current/stdlib/Coq.Relations.Operators_Properties.html}{Coq.Relations.Operators\_Properties} 
    allow the user
   to convert any one of the three closures into another one before applying the corresponding elimination tactic.
   The same remark also holds for reflexive and transitive closures. 
   \end{remark}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Define a restriction of \coqsimple{round},  where Hercules always chops off
   the leftmost among the lowest heads.

   Prove that, if $h$ is not a simple head, then there exists a unique $h'$ such that \texttt{h}  is transformed into \texttt{ h'} in one round, according to this restriction.


   \end{exercise}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}[Interactive battles]\label{exo:interactive-battle}
   Given a hydra \texttt{h}, the specification of a hydra battle for \texttt{h} is the type 
   \Verb@{h':Hydra | h -*-> h'}@. In order to avoid long sequences of \texttt{split}, \texttt{left}, and 
   \texttt{right}, design a set of dedicated tactics for the interactive building of a battle.
   Your tactics will have the following functionalities:
   \begin{itemize}
   \item  Chose to stop a battle, or continue
   \item Chose an expected number of replications
   \item Navigate in a hydra, looking for a head to chop off.
   \end{itemize}

   Use your tactics for simulating a small part of a hydra battle, for instance the rounds which lead from
   \texttt{Hy} to \texttt{Hy'''}  (Fig.~\vref{fig:Hy5}).

   \textbf{Hints:} 
   \begin{itemize}

   \item Please keep in mind that the last  configuration of your interactively built battle is known only at the end of the battle. Thus, you will have to create and solve subgoals with existential variables. For that purpose, the tactic \texttt{eexists}, applied to the 
   goal \Verb@{h':Hydra | h -*-> h'}@ generates the subgoal \Verb|h -*-> ?h'|.
   \item You may use Gérard Huet's \emph{zipper} data structure~\cite{zipper} for writing tactics associated with Hercule's  interactive search for a head to chop off.
   \end{itemize}






   \end{exercise}

.. _sect:battle-classes:

Classes of battles
~~~~~~~~~~~~~~~~~~

In some presentations of hydra battles,
e.g. :raw-latex:`\cite{KP82, bauer2008}`, the transformation associated
with the :math:`i`-th round may depend on :math:`i`. For instance, in
these articles, the replication factor at the :math:`i`-th round is
equal to :math:`i`. In other examples, one can allow the hydra to apply
any replication factor at any time. In order to be the most general as
possible, we define the type of predicates which relate the state of the
hydra before and after the :math:`i`-th round of a battle.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html>`__
:raw-latex:`\label{types:Battle}`
:raw-latex:`\index{hydras}{Library Hydra!Type classes!Battle}`

.. raw:: latex

   \begin{Coqsrc}
   Definition dep_round_t := nat -> Hydra -> Hydra -> Prop.

   Class Battle :=  
       { battle_rel : dep_round_t;
         battle_inclusion : forall i h h', battle_rel i h h' -> round h h'}.
   \end{Coqsrc}

The most general class of battles is ``free``, which allows the hydra to
chose any replication factor at every step:

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html#free>`__

.. raw:: latex

   \begin{Coqsrc}
   Program Instance free : Battle := Build_Battle (fun _  h h' => round h h') _.
   \end{Coqsrc}

We chosed to call *standard* the kind of battles which appear most often
in the litterature and correspond to an arithmetic progression of the
replication factor : :math:`0,1,2,3, \dots`

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html#standard>`__

.. raw:: latex

   \begin{Coqsrc}
   Program Instance standard : Battle := (Build_Battle round_n _).
   Next Obligation.
     now exists i.  
   Defined.
   \end{Coqsrc}

Big steps
~~~~~~~~~

Let :math:`B` be any instance of class ``Battle``. It is easy to define
inductively the relation between the :math:`i`-th and the :math:`j`-th
steps of a battle of type :math:`B`.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html#fight>`__

.. raw:: latex

   \begin{Coqsrc}
   Inductive battle (B:Battle) : nat -> Hydra -> nat -> Hydra -> Prop :=
   | battle_1 : forall i h  h', 
         battle_rel   B i  h h' -> battle B i h (S i) h'
   | battle_n : forall i h  j h' h'',  
         battle_rel  B i h h''  ->
         battle B (S i) h'' j h'  ->
         battle B i h j h'.
   \end{Coqsrc}

The following property allows us to build battles out of smaller ones.

.. raw:: latex

   \begin{Coqsrc}
   Lemma battle_trans {b:Battle} :
     forall i h j h', battle b i h j h' ->
           forall k h0,  battle b k h0 i h -> battle b k h0 j h'.
   \end{Coqsrc}

.. _sect:big-battle:

A long battle
-------------

In this section we consider a simple example of battle, starting with a
small hydra, shown on figure :raw-latex:`\vref{fig:hinit}`, with a
simple strategy for both players:

-  At each round, Hercules chops off the rightmost head of the hydra.

-  The battle is called *standard*\  [5]_: at the round number
   :math:`i`, the expected replication is :math:`i`.

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[thick, scale=0.30]
    \node (foot) at (6,0) {$\bullet$};
   \node (n1) at  (3,3) {$\bullet$};
   \node (h1) at  (1,6) {$\Smiley[1][green]$};
   \node (h2) at  (3,6) {$\Smiley[1][green]$};
   \node (h3) at  (6,6) {$\Smiley[1][green]$};
   \node (h4) at  (6,6) {$\Smiley[1][green]$};
   \node (h5) at  (6,3) {$\Smiley[1][green]$};
   \node (h6) at  (9,3) {$\Smiley[1][green]$};
   \draw (foot) -- (n1);
   \draw (n1) to   [bend left=20] (h1);
   \draw (n1) to   (h2);
   \draw (n1) to   [bend right=20] (h3);
   \draw (foot) -- (h5);
   \draw (foot) to  [bend right=20] (h6);
   \end{tikzpicture}

.. raw:: latex

   \begin{Coqsrc}
   Definition hinit := hyd3 (hyd_mult head 3)  head head.  
   \end{Coqsrc}

The lemma we would like to prove is “The considered battle lasts exactly
:math:`N` rounds”, with :math:`N` being a natural number we gave to
guess.

But the battle is so long that no *test* can give us any estimation of
its length, and we do need the expressive power of logic to compute this
length. However, in order to guess this length, we made some
experiments, computing with :raw-latex:`\gallina{}`,
:raw-latex:`\coq{}`’s functional programming language. Thus, we can
consider this development as a collaboration of proof with computation.
In the following lines, we show how we found experimentally the value of
the number :math:`N`. The complete proof is in file
`../theories/html/hydras.Hydra.BigBattle.html <../theories/html/hydras.Hydra.BigBattle.html>`__.

The beginning of hostilities
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

During the two first rounds, our hydra loses its two rightmost heads.
Figure :raw-latex:`\vref{fig:hinit-plus2}` shows the state of the hydra
just before the third round.

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[thick, scale=0.30]
    \node (foot) at (3,0) {$\bullet$};
   \node (n1) at  (3,3) {$\bullet$};
   \node (h1) at  (1,6) {$\Smiley[1][green]$};
   \node (h2) at  (3,6) {$\Smiley[1][green]$};
   \node (h3) at  (6,6) {$\Smiley[1][green]$};
   \node (h4) at  (6,6) {$\Smiley[1][green]$};
   \draw (foot) -- (n1);
   \draw (n1) to   [bend left=20] (h1);
   \draw (n1) to   (h2);
   \draw (n1) to   [bend right=20] (h3);
   \end{tikzpicture}

The following lemma is a formal description of these first rounds, in
terms of the ``battle`` predicate.

.. raw:: latex

   \begin{Coqsrc}
   Lemma L_0_2 : battle standard 0 hinit 2 (hyd1 h3).   
   \end{Coqsrc}

Looking for regularities
~~~~~~~~~~~~~~~~~~~~~~~~

A first study with pencil and paper suggested us that, after three
rounds, the hydra always looks like in
figure :raw-latex:`\vref{fig:hinit-plusn}` (with a variable number of
subtrees of height 1 or 0). Thus, we introduce a few handy notations.

.. raw:: latex

   \begin{Coqsrc}
   Notation h3 := (hyd_mult head 3).
   Notation h2 := (hyd_mult head 2).
   Notation h1 := (hyd1 head).

   Definition hyd a b c := 
     node (hcons_mult h2  a
                (hcons_mult h1  b
                            (hcons_mult head c hnil))).
   \end{Coqsrc}

For instance Fig :raw-latex:`\vref{fig:hinit-plusn}` shows the hydra
(``hyd 3 4 2``). The hydra (``hyd 0 0 0``) is the “final” hydra of any
terminating battle, i.e., a tree whith exactly one node and no edge.

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[thick, scale=0.30]
    \node (foot) at (15,0) {$\bullet$};
   \node (a) at  (3,4) {$\bullet$};
   \node (b) at  (6,4) {$\bullet$};
   \node (c) at  (9,4) {$\bullet$};
   \node (d) at  (13,4) {$\bullet$};
   \node (e) at  (16,4) {$\bullet$};
   \node (f) at  (19,4) {$\bullet$};
   \node (g) at  (22,4) {$\bullet$};
   \node (h) at  (25,4) {$\Smiley[1][green]$};
   \node (i) at  (28,4) {$\Smiley[1][green]$};
   \node (aa) at  (2.5,8) {$\Smiley[1][green]$};
   \node (ab) at  (3.5,8) {$\Smiley[1][green]$};
   \node (ba) at  (5.5,8) {$\Smiley[1][green]$};
   \node (bb) at  (6.5,8) {$\Smiley[1][green]$};
   \node (ca) at  (8.5,8) {$\Smiley[1][green]$};
   \node (cb) at  (9.5,8) {$\Smiley[1][green]$};
   \node (da) at  (13,8) {$\Smiley[1][green]$};
   \node (ea) at  (16,8) {$\Smiley[1][green]$};
   \node (fa) at  (19,8) {$\Smiley[1][green]$};
   \node (ga) at  (22,8) {$\Smiley[1][green]$};
   \draw (foot) -- (a);
   \draw (foot) -- (b);
   \draw (foot) -- (c);
   \draw (foot) -- (d);
   \draw (foot) -- (e);
   \draw (foot) -- (f);
   \draw (foot) -- (g);
   \draw (foot) -- (h);
   \draw (foot) -- (i);
   \draw (a) -- (aa);
   \draw (a) -- (ab);
   \draw (b) -- (ba);
   \draw (b) -- (bb);
   \draw (c) -- (ca);
   \draw (c) -- (cb);
   \draw (d) -- (da);
   \draw (e) -- (ea);
   \draw (f) -- (fa);
   \draw (g) -- (ga);
   % \node (a) at  (3,4) {$\bullet$};
   % \node (h1) at  (1,6) 
   % \node (h2) at  (3,6) {$\Smiley[1][green]$};
   % \node (h3) at  (6,6) {$\Smiley[1][green]$};
   % \node (h4) at  (6,6) {$\Smiley[1][green]$};
   % \draw (foot) -- (n1);
   % \draw (n1) to   [bend left=20] (h1);
   % \draw (n1) to   (h2);
   % \draw (n1) to   [bend right=20] (h3);
   \end{tikzpicture}

With these notations, we get a formal description of the first three
rounds.

.. raw:: latex

   \begin{Coqsrc}
   Lemma L_2_3 : battle standard 2 (hyd1 h3)  3 (hyd 3 0 0).

   Lemma L_0_3 : battle standard 0 hinit 3 (hyd 3 0 0).
   \end{Coqsrc}

Testing …
~~~~~~~~~

In order to study *experimentally* the different configurations of the
battle, we will use a simple datatype for representing the states as
tuples composed of the round number, and the respective number of
daughters ``h2``, ``h1``, and heads of the current hydra.

.. raw:: latex

   \begin{Coqsrc}
    Record state : Type :=
       mks {round: nat ; n2 : nat ; n1 : nat ; nh : nat}.
   \end{Coqsrc}

The following function returns the next configurarion of the game. Note
that this function is defined only for making experiments and is not
“certified”. Formal proofs about our battle only start with the lemma
``step_battle``, page :raw-latex:`\pageref{lemma:step-battle}`.

.. raw:: latex

   \begin{Coqsrc}
   Definition next (s : state) :=
     match s with
     | mks round a b (S c) => mks (S round) a b c
     | mks round a (S b) 0 => mks (S round) a b (S round)
     | mks round (S a) 0 0 => mks (S round) a (S round) 0
     | _ => s
     end.
   \end{Coqsrc}

We can make bigger steps through iterations of ``next``. The functional
``iterate``, similar to Standard Library’s ``Nat.iter``, is defined and
studied
in `Prelude.Iterates <../theories/html/hydras.Prelude.Iterates.html#iterate>`__.
:raw-latex:`\index{hydras}{Library Prelude!iterate}`

:raw-latex:`\label{Functions:iterate}`

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint iterate {A:Type}(f : A -> A) (n: nat)(x:A) :=
     match n with
     | 0 => x
     | S p => f (iterate  f p x)
     end.
   \end{Coqsrc}

The following function computes the state of the battle at the
:math:`n`-th round.

.. raw:: latex

   \begin{Coqsrc}
   Definition test n := iterate next (n-3) (mks 3 3 0 0).

   Compute test 3.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
         = {| round := 3; n2 := 3; n1 := 0; nh := 0 |}
        : state 
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
    Compute test 4.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
     = {| round := 4; n2 := 2; n1 := 4; nh := 0 |}
        : state
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Compute test 5.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
     = {| round := 5; n2 := 2; n1 := 3; nh := 5 |}
        : state
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Compute test 2000.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
     = {| round := 2000; n2 := 1; n1 := 90; nh := 1102 |}
        : state
   \end{Coqanswer}

The battle we are studying seems to be awfully long. Let us concentrate
our tests on some particular events : the states where
:math:`\texttt{nh}=0`. From the value of ``test 5``, it is obvious that
at the 10-th round, the counter ``nh`` is equal to zero.

.. raw:: latex

   \begin{Coqsrc}
    Compute test 10.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
       = {| round := 10; n2 := 2; n1 := 3; nh := 0 |}
        : state
    \end{Coqanswer}

Thus, :math:`(1 + 11)` rounds later, the ``n1`` field is equal to
:math:`2`, and ``nh`` to :math:`0`.

.. raw:: latex

   \begin{Coqsrc}
   Compute test 22.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
    = {| round := 22; n2 := 2; n1 := 2; nh := 0 |}
        : state
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
    Compute test 46.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   ( = {| round := 46; n2 := 2; n1 := 1; nh := 0 |}
        : state
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Compute test 94.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
    = {| round := 94; n2 := 2; n1 := 0; nh := 0 |}
        : state
   \end{Coqanswer}

Next round, we decrement ``n2`` and set ``n1`` to :math:`95`.

.. raw:: latex

   \begin{Coqsrc}
    Compute test 95.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
     = {| round := 95; n2 := 1; n1 := 95; nh := 0 |}
        : state
   \end{Coqanswer}

We now have some intuition of the sequence. It looks like the next
“``nh``\ =0” event will happen at the :math:`192=2(95+1)`-th round, then
at the :math:`2(192+1)`-th round, etc.

.. raw:: latex

   \begin{Coqsrc}
   Definition doubleS (n : nat) := 2 * (S n).

   Compute test (doubleS 95).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
    = {| round := 192; n2 := 1; n1 := 94; nh := 0 |}
        : state
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Compute test (iterate doubleS 2 95).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
     = {| round := 386; n2 := 1; n1 := 93; nh := 0 |}
        : state
   \end{Coqanswer}

Proving …
~~~~~~~~~

We are now able to reason about the sequence of transitions defined by
our hydra battle. Instead of using the data-type ``state`` we study the
relationship between different configurations of the battle.

Let us define a binary relation associated with every round of the
battle. In the following definition ``i`` is associated with the round
number (or date, if we consider a discrete time), and ``a``, ``b``,
``c`` respectively associated with the number of ``h2``, ``h1`` and
heads connected to the hydra’s foot.

.. raw:: latex

   \begin{Coqsrc}
   Inductive one_step (i: nat) :
     nat -> nat -> nat -> nat -> nat -> nat -> Prop :=
   | step1: forall a b c, one_step i a b (S c) a b c
   | step2:  forall a b, one_step i a (S b) 0 a b (S i)
   | step3: forall a, one_step i (S a) 0 0 a (S i) 0.
   \end{Coqsrc}

The relation between ``one_step`` and the rules of hydra battle is
asserted by the following lemma.

:raw-latex:`\label{lemma:step-battle}`

.. raw:: latex

   \begin{Coqsrc}
   Lemma step_battle : forall i a b c a' b' c', 
      one_step i a b c a' b' c' ->
      battle standard i (hyd  a b c)  (S i) (hyd a' b' c').
   \end{Coqsrc}

Next, we define “big steps” as the transitive closure of ``one_step``,
and reachability (from the initial configuration of
figure :raw-latex:`\ref{fig:hinit}` at time :math:`0`).

.. raw:: latex

   \begin{Coqsrc}
    Inductive steps : nat -> nat -> nat -> nat ->
                     nat -> nat -> nat -> nat -> Prop :=
   | steps1 : forall i a b c a' b' c',
       one_step i a b c a' b' c' -> steps i a b c (S i) a' b' c'
   | steps_S : forall i a b c j a' b' c' k a'' b'' c'',
       steps i a b c j a' b' c' ->
       steps j a' b' c' k a'' b'' c'' ->
       steps i a b c k  a'' b'' c''.

   Definition reachable (i a b c : nat) : Prop :=
     steps 3 3 0 0 i a b c.
   \end{Coqsrc}

The following lemma establishes a relation between ``steps`` and the
predicate ``battle``.

.. raw:: latex

   \begin{Coqsrc}
    Lemma steps_battle : forall i a b c j a' b' c', 
      steps i a b c j a' b' c' ->
      battle standard i (hyd  a b c)   j  (hyd a' b' c').
   \end{Coqsrc}

Thus, any result about ``steps`` will be applicable to standard battles.
Using the predicate ``steps``, our study of the length of the considered
battle can be decomposed into three parts:

#. Characterization of regularities of some events

#. Study of the beginning of the battle

#. Computing the exact length of the battle.

First, we prove that, if at round :math:`i` the hydra is equal to
(``hyd a (S b) 0``), then it will be equal to (``hyd a b 0``) at the
:math:`2(i+1)`-th round.

.. raw:: latex

   \begin{Coqsrc}
   Lemma LS : forall c a b i,  steps i a b (S c) (i + S c) a b 0.
   Proof.
     induction c.
    -   intros;  replace (i + 1) with (S i).
        + repeat constructor.
        + ring.
    -  intros; eapply  steps_S.
      +   eleft;   apply rule1.
      +   replace (i + S (S c)) with (S i + S c) by ring;  apply IHc.
   Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma doubleS_law : forall  a b i, steps i a (S b) 0 (doubleS i) a b 0.
   Proof.
     intros;  eapply steps_S.
     +   eleft;   apply step2.
     +   unfold doubleS; replace (2 * S i) with (S i + S i) by ring; 
           apply LS.
   Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma reachable_S  : forall i a b, reachable i a (S b) 0 ->
                                      reachable (doubleS i) a b 0.
   Proof.
     intros; right with  (1 := H); apply doubleS_law.
   Qed.
   \end{Coqsrc}

From now on, the lemma ``reachable_S`` allows us to watch larger steps
of the battle.

.. raw:: latex

   \begin{Coqsrc}
    Lemma L4 : reachable 4 2 4 0.
   Proof.
     left; constructor.
   Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma L10 : reachable 10 2 3 0.
   Proof.
     change 10 with (doubleS 4).
     apply reachable_S, L4.
   Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma L22 : reachable 22 2 2 0.
   Proof.
     change 22 with (doubleS 10).
     apply reachable_S, L10.
   Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma L46 : reachable 46 2 1 0.
   Proof.
     change 46 with (doubleS 22); apply  reachable_S, L22.
   Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma L94 : reachable 94 2 0 0.
   Proof.
     change 94 with (doubleS 46); apply reachable_S, L46.
   Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma L95 : reachable 95 1 95 0.
   Proof.
     eapply steps_S.
     -  eexact L94.
     -  repeat constructor.
   Qed.
   \end{Coqsrc}

Giant steps
~~~~~~~~~~~

We are now able to make bigger steps in the simulation of the battle.
First, we iterate the lemma ``reachable_S``.

.. raw:: latex

   \begin{Coqsrc}
   Lemma Bigstep : forall b i a , reachable i a b 0 ->
                                  reachable (iterate doubleS b i) a 0 0.
    Proof.
     induction b.
     -  trivial.
     -  intros;  simpl;   apply reachable_S in H.
        rewrite <- iterate_comm; now apply IHb.
    Qed.
   \end{Coqsrc}

Applying lemmas ``BigStep`` and ``L95`` we make a first jump.

.. raw:: latex

   \begin{Coqsrc}
    Definition M := (iterate doubleS 95 95).

   Lemma L2_95 : reachable M 1 0 0.
   Proof.
     apply Bigstep,  L95.
   Qed.
   \end{Coqsrc}

Figure :raw-latex:`\ref{fig:HM}` represents the hydra at the
:math:`M`-th round. At the :math:`(M+1)`-th round, it will look like in
fig :raw-latex:`\ref{fig:HM-plus1}`.

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.5]
   \node (foot) at (2,0) {$\bullet$};
   \node (N1) at (2,2) {$\bullet$};
   \node (N2) at (3,4) {$\Smiley[2][green]$};
   \node (N3) at (1,4) {$\Smiley[2][green]$};
   \draw (foot) -- (N1);
   \draw (N1) to [bend right =15] (N2);
   \draw (N1) to  [bend left=15](N3);
   \end{tikzpicture}

The state of the hydra after :math:`M` rounds.

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.5]
   \node (foot) at (10,0) {$\bullet$};
   \node (N1) at (0,5) {$\bullet$};
   \node (N12) at (0,8) {$\Smiley[2][green]$};
   \node (N2) at (2,5) {$\bullet$};
   \node (N22) at (2,8) {$\Smiley[2][green]$};
   \node (N3) at (4,5) {$\bullet$};
   \node (N32) at (4,8) {$\Smiley[2][green]$};
   \node (N4) at (6,5) {$\bullet$};
   \node (N42) at (6,8) {$\Smiley[2][green]$};

   \node (Ndots) at (12,8) {\Huge $\dots$};
   \node (Ndots2) at (12,5) {\Huge $\dots$};

   \node (N8) at (18,5) {$\bullet$};
   \node (N82) at (18,8) {$\Smiley[2][green]$};
   \node (N9) at (20,5) {$\bullet$};
   \node (N92) at (20,8) {$\Smiley[2][green]$};


   \draw (foot) -- (N1);
   \draw (foot) -- (N2);
   \draw (foot) -- (N3);
   \draw (foot) -- (N4);
   \draw (foot) -- (N8);
   \draw (foot) -- (N9);
   \draw (N1) to  (N12);
   \draw (N2) to  (N22);
   \draw (N3) to  (N32);
   \draw (N4) to  (N42);
   \draw (N8) to  (N82);
   \draw (N9) to  (N92);
   \end{tikzpicture}

The state of the hydra after :math:`M+1` rounds (with :math:`M+1`
heads).

.. raw:: latex

   \begin{Coqsrc}
   Lemma L2_95_S : reachable (S M) 0 (S M) 0.
   Proof.
     eright.
     - apply L2_95.
     -  left; constructor 3.
   Qed.
   \end{Coqsrc}

Then, applying once more the lemma ``BigStep``, we get the exact time
when Hercules wins!

.. raw:: latex

   \begin{Coqsrc}
   Definition N :=   iterate doubleS (S M) (S M).

   Theorem   SuperbigStep : reachable N  0 0 0 .
   Proof.
     apply Bigstep, L2_95_S.
   Qed.
   \end{Coqsrc}

We are now able to prove formally that the considered battle is composed
of :math:`N` steps.

.. raw:: latex

   \begin{Coqsrc}
   Lemma Almost_done :
     battle standard 3 (hyd 3 0 0) N (hyd 0 0 0).
   Proof. 
     apply steps_battle, SuperbigStep.
   Qed.

   Theorem Done :
     battle standard 0 hinit N head.
   Proof.
     eapply battle_trans.
     -   apply Almost_done.
     -  apply L_0_3.
   Qed.
   \end{Coqsrc}

A minoration lemma
~~~~~~~~~~~~~~~~~~

Now, we would like to get an intuition of how big the number :math:`N`
is. For that purpose, we use a minoration of the function ``doubleS`` by
the function (``fun n => 2 * n``).

.. raw:: latex

   \begin{Coqsrc}
   Definition exp2 n := iterate (fun n => 2 * n) n 1.
   \end{Coqsrc}

Using some facts (proven in
`hydras.Hydra.BigBattle <../theories/html/hydras.Hydra.BigBattle.html>`__),we
get several minorations.

.. raw:: latex

   \begin{Coqsrc}
   Lemma minoration_0 : forall n,  2 * n <= doubleS n.

   Lemma minoration_1 : forall n x, exp2 n * x <= iterate doubleS n x.

   Lemma minoration_2 : exp2 95 * 95 <= M.

   Lemma minoration_3 : exp2 (S M) * S M <= N.

   Lemma minoration : exp2 (exp2 95 * 95) <= N.
   \end{Coqsrc}

The number :math:`N` is greater than or equal to
:math:`2^{2^{95}\times 95}.` If we wrote :math:`N` in base :math:`10`,
:math:`N` would require at least :math:`10^{30}` digits!

Generic properties
------------------

The example we just studied shows that the termination of any battle may
take a very long time. If we want to study hydra battles in general, we
have to consider any hydra and any strategy, both for Hercules and the
hydra itself. So, we first give some definitions, generally borrowed
from transition systems vocabulary (see :raw-latex:`\cite{tel_2000}` for
instance).

Liveliness
~~~~~~~~~~

Let :math:`B` be an instance of ``Battle``. We say that :math:`B` is
*alive* if for any configuration :math:`(i,h)`, where :math:`h` is not a
head, there exists a further step in class :math:`B`.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html#Alive>`__

.. raw:: latex

   \begin{Coqsrc}
   Definition Alive (B : Battle) :=
     forall i h, 
        h <> head -> {h' : Hydra |  B i h h'}.
   \end{Coqsrc}

The theorems ``Alive_free`` and ``Alive_standard`` of the module
`Hydra.Hydra_Theorems <../theories/html/hydras.Hydra.Hydra_Theorems.html>`__
show that the classes ``free`` and ``standard`` satisfy this property.

.. raw:: latex

   \begin{Coqsrc}
   Theorem Alive_free: Alive free.

   Theorem Alive_standard: Alive standard.  
   \end{Coqsrc}

Both theorems are proved with the help of the following strongly
specified function:

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Hydra_Lemmas <../theories/html/hydras.Hydra.Hydra_Lemmas.html#next_round_dec>`__

.. raw:: latex

   \begin{Coqsrc}
   Definition  next_round_dec n :
    forall h, (h = head) + {h' : Hydra & {R1 h h'} + {R2 n h  h'}}.
   \end{Coqsrc}

Termination
~~~~~~~~~~~

The termination of all battles is naturally expressed by the predicate
``well_founded`` defined in the module
`Coq.Init.Wf <https://coq.inria.fr/distrib/current/stdlib/Coq.Init.Wf.html>`__
of the Standard Library.

:raw-latex:`\index{hydras}{Library Hydra!Predicates!Termination}`

.. raw:: latex

   \begin{Coqsrc}
   Definition Termination :=  well_founded (transp _ round).
   \end{Coqsrc}

Let :math:`B` be an instance of class ``Battle``. A *variant* for
:math:`B` consists in a well-founded relation :math:`<` on some type
``A``, and a function (also called a *measure*) ``m:Hydra->A`` such that
for any successive steps :math:`(i,h)` and :math:`(1+i,h')` of a battle
in :math:`B`, the inequality :math:`m(h')<m(h)` holds.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Hydra_Definitions <../theories/html/hydras.Hydra.Hydra_Definitions.html#Hvariant>`__

:raw-latex:`\label{sect:hvariant-def}`

:raw-latex:`\index{hydras}{Library Hydra!Type classes!Hvariant}`

.. raw:: latex

   \begin{Coqsrc}
   Class Hvariant {A:Type}{Lt:relation A}(Wf: well_founded Lt)(B : Battle)
     (m: Hydra -> A):   Prop :=
     {variant_decr: forall i h h',
         h <> head ->
         battle_rel  B i  h h' -> Lt (m h') (m h)}.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
    Prove that, if there is an instance of (\texttt{Hvariant Lt wf\_Lt $B$ $m$}), then there exists no infinite battle in  $B$.
   \end{exercise}

A small proof of impossibility
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

:raw-latex:`\index{coq}{Proofs of impossibility}`

:raw-latex:`\label{omega-case}`

When one wants to prove a termination theorem with the help of a
variant, one has to consider first a well-founded set :math:`(A,<)`,
then a strictly decreasing measure on this set. The following two lemmas
show that if the order structure :math:`(A,<)` is too simple, it is
useless to look for a convenient measure, which simply no exists. Such
kind of result is useful, because it saves you time and effort.

The best known well-founded order is the natural order on the set
:math:`\mathbb{N}` of natural numbers (the type ``nat`` of Standard
library). It would be interesting to look for some measure
:math:`m:\texttt{nat}\arrow\texttt{nat}` and prove it is a variant.

Unfortunately, we can prove that *no* instance of class
(``WfVariant round Peano.lt m``) can be built, where :math:`m` is *any*
function of type ``Hydra \arrow nat``.

Let us present the main steps of that proof, the script of which is in
the module
 `Hydra/Omega_Small.v <../theories/html/hydras.Hydra.Omega_Small.html>`__
 [6]_.

Let us assume there exists some variant :math:`m` from ``Hydra`` into
``nat`` for proving the termination of all hydra battles.

.. raw:: latex

   \begin{Coqsrc}
   Section Impossibility_Proof.
    Variable m : Hydra -> nat.
    Hypothesis Hvar : Hvariant lt_wf free m.
   \end{Coqsrc}

We define an injection :math:`\iota` from the type ``nat`` into
``Hydra``. For any natural number :math:`i`, :math:`\iota(i)` is the
hydra composed of a foot and :math:`i+1` heads at height :math:`1`. For
instance, Fig. :raw-latex:`\ref{fig:flower}` represents the hydra
:math:`\iota(3)`.

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.5]
   \node (foot) at (4,0) {$\bullet$};
   \node (N1) at (2,2) {$\Smiley[2][green]$};
   \node (N2) at (4,2) {$\Smiley[2][green]$};
   \node (N3) at (6,2) {$\Smiley[2][green]$};
   \node (N4) at (8,2) {$\Smiley[2][green]$};
   \draw (foot) to [bend left =25] (N1);
   \draw (foot) to [bend left =15] (N2);
   \draw (foot) to [bend right =15] (N3);
   \draw (foot) to [bend right =25] (N4);
   \end{tikzpicture}

.. raw:: latex

   \begin{Coqsrc}
     Let iota (i: nat) := hyd_mult head (S i).    
     \end{Coqsrc}

Let us consider now some hydra ``big_h`` out of the range of the
injection :math:`\iota` (see
Fig. :raw-latex:`\vref{fig:h-omega-omega}`).

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.5]
   \node (foot) at (2,0) {$\bullet$};
   \node (N1) at (2,2) {$\bullet$};
   \node (N2) at (2,4) {$\Smiley[2][green]$};
   \draw (foot) -- (N1);
   \draw (N1) to  (N2);
   \end{tikzpicture}

The hydra ``big_h``.

.. raw:: latex

   \begin{Coqsrc}
     Let big_h := hyd1 (hyd1 head).
    \end{Coqsrc}

Using the functions :math:`m` and :math:`\iota`, we define a second
hydra ``small_h``, and show there is a one-round battle that transforms
``big_h`` into ``small_h``. Please note that, due to the hypothesis
``Hvar``, we are interested in the termination of *free* battles. There
is no problem to consider a round with (``m big_h``) as the replication
factor.

.. raw:: latex

   \begin{Coqsrc}
    Let small_h := iota (m big_h).
      
    Fact big_to_small : big_h -1-> small_h.
    Proof.
         exists (m big_h); right; repeat constructor.     
    Qed.
       \end{Coqsrc}

But, by hypothesis, :math:`m` is a variant. Hence, we infer the
following inequality.

.. raw:: latex

   \begin{Coqsrc}
   Lemma m_lt : m small_h < m big_h.
    \end{Coqsrc}

In order to get a contradiction, it suffices to prove the inequality
:math:`m(\texttt{big\_h}) \leq m(\texttt{small\_h})` i.e.,
:math:`m(\texttt{big\_h}\leq m(\iota (m(\texttt{big\_h})))`.

More generally, we prove the following lemma:

.. raw:: latex

   \begin{Coqsrc}
   Lemma m_ge : forall i:nat, i <= m (iota i).
   \end{Coqsrc}

Intuitively, it means that, from any hydra of the form (``iota i``), the
battle will take (at least) :math:`i` rounds. Thus the associated
measure cannot be less than :math:`i`. Technically, we prove this lemma
by Peano induction on :math:`i`.

-  The base case :math:`i=0` is trivial

-  Otherwise, let :math:`i` be any natural number and assume the
   inequality :math:`i \leq m(\iota(i))`.

   #. But the hydra :math:`\iota(S(i))` can be transformed in one round
      into :math:`\iota(i)` (by losing its righmost head, for instance)

   #. Since :math:`m` is a variant, we have
      :math:`m(\iota(i)) < m(\iota(S(i)))`, hence
      :math:`i< m(\iota(S(i)))`, which implies
      :math:`S(i)\leq  m(\iota(S(i)))`.

Then our proof is almost finished.

.. raw:: latex

   \begin{Coqsrc}
   Theorem Contradiction : False.
   Proof.
    apply (Nat.lt_irrefl (m big_h));
      apply  Lt.le_lt_trans with (m small_h).
     - apply m_ge.
     - apply m_lt.
   Qed. 

   End Impossibility_Proof.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove that there exists no variant $m$ from \texttt{Hydra} into \texttt{nat} for proving
       the  termination of all \emph{standard} battles.
   \end{exercise}

Conclusion
^^^^^^^^^^

In order to build a variant for proving the termination of all hydra
battles, we need to consider order structures more complex than the
usual order on type ``nat``. The notion of *ordinal number* provides a
catalogue of well-founded order types. For a reasonably large bunch of
ordinal numbers, *ordinal notations* are data-types which allow the
:raw-latex:`\coq{}` user to define functions, to compute and prove some
properties, for instance by reflection.

The next chapter is dedicated to a generic formalization of ordinal
notations, and chapter :raw-latex:`\ref{chap:T1}` to a proof of
termination of all hydra battles with the help of an ordinal notation
for the interval :math:`[0,\epsilon_0)`  [7]_.
:raw-latex:`\index{maths}{Notations!Interval}`

Introduction to ordinal numbers and ordinal notations
=====================================================

The proof of termination of all hydra battles presented
in :raw-latex:`\cite{KP82}` is based on *ordinal numbers*. From a
mathematical point of view, an ordinal is a representant of an
equivalence class for isomorphims of totally ordered well-founded sets.

For the computer scientist, ordinals are tools for proving the totality
of a given recursive function, or termination of a transition system.
*Ordinal arithmetic* provides a set of functions whose properties, like
*monotony*, allow to define *variants*, *i.e.* strictly decreasing
measures used in proofs of termination.

Let us have a look at Figure :raw-latex:`\ref{fig:ordinal-sequence}`. It
presents a few items of a sequence of ordinal numbers, which extends the
sequence of natural numbers.

.. raw:: latex

   \centering

.. raw:: latex

   \fbox{\Large
     \begin{minipage}{1.0\linewidth}
     \begin{align*}
        &\textcolor{blue}{0},\,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,\ldots\\
   &\textcolor{red}{\omega},\,\omega+1,\omega+2,\omega+3,\ldots\\
   &\textcolor{red}{\omega\times 2},\,\omega\times 2+1,\ldots, \textcolor{red}{\omega\times 3},\,\omega\times 3+1,\ldots, \textcolor{red}{\omega\times 4},\ldots\\
   &\textcolor{red}{\omega^2},\ldots, \textcolor{red}{\omega^2\times 42},\ldots,\textcolor{red}{\omega^3},\ldots, \textcolor{red}{\omega^4},\omega^4+1,\ldots\\
   &\textcolor{red}{\omega^\omega},\ldots, \textcolor{red}{\omega^\omega+\omega^7\times 8},\ldots,\textcolor{red}{\omega^\omega\times 2},\omega^\omega\times 2+1, \ldots\\
   &\textcolor{red}{\omega^{\omega^\omega}},\ldots, \textcolor{red}{\omega^{\omega^\omega}+\omega^\omega\times 42+ \omega^{55}+\omega}, \ldots, \textcolor{red}{\omega^{\omega^{\omega+1}}}, \omega^{\omega^{\omega+1}}+1,\dots\\
   & \textcolor{red}{\epsilon_0 (= \omega^{\epsilon_0)}}, \epsilon_0+1, \epsilon_0+2, \epsilon_0+3, \ldots\\
   & \textcolor{red}{\epsilon_1}, \ldots, \textcolor{red}{\epsilon_2}, \ldots, \textcolor{red}{\epsilon_\omega},\ldots \\
   & \textcolor{red}{\Gamma_0}, \Gamma_0+1, \Gamma_0+2, \Gamma_0+3,\ldots, \textcolor{red}{\Gamma_0+\omega}, \ldots\\
   &\ldots
     \end{align*}   
     \end{minipage}}

Let us comment some features of this figure:

-  The ordinals are listed in a strictly increasing order.

-  Dots : “:math:`\ldots`” stand for infinite sequences of ordinals, not
   shown for lack of space. For instance, the ordinal :math:`42` is not
   shown in the first line, but it exists, somewhere between :math:`17`
   and :math:`\omega`.

-  Each ordinal printed in black is the immediate successor of another
   ordinal. We call it a *successor* ordinal. For instance, :math:`12`
   is the successor of :math:`11`, and :math:`\omega^4+1` the successor
   of :math:`\omega^4`.

-  Ordinals (displayed in red) that follow immediately dots are called
   *limit ordinals*. With respect to the order induced by this sequence,
   any limit ordinal :math:`\alpha` is the least upper bound of the set
   :math:`\mathbb{O}_\alpha` of all ordinals strictly less than
   :math:`\alpha`.

-  For instance :math:`\omega` is the least upper bound of the set of
   all finite ordinals (in the first line). It is also the first limit
   ordinal, and the first infinite ordinal, in the sense that the set
   :math:`\mathbb{O}_\omega` is infinite.

-  The ordinal :math:`\epsilon_0` is the first number which is equal to
   its own exponential of base :math:`\omega`. It plays an important
   role in proof theory, and is particularly studied in
   chapters :raw-latex:`\ref{chap:T1}` to
   :raw-latex:`\ref{chap:alpha-large}`.

-  Any ordinal is either the ordinal :math:`0`, a successor ordinal, or
   a limit ordinal.

The mathematical point of view
------------------------------

Well-ordered sets
~~~~~~~~~~~~~~~~~

Let us start with some definitions. A *well-ordered set* is a set
provided with a binary relation :math:`<` which has the following
properties.

irreflexivity
   : :math:`\forall x\in A, x\not< x`

transitivity
   : :math:`\forall x\,y\,z\in A, x<y \Rightarrow y<z \Rightarrow x<z`

trichotomy
   : :math:`\forall x\,y\in A, x<y \vee x = y \vee y < x`

well foundedness
   : :math:`<` is well-founded (every element of :math:`A` is
   accessible) [8]_.

The best known examples of well-ordered sets are the set
:math:`\mathbb{N}` of natural numbers (with the usual order :math:`<`),
as well as any finite segment :math:`[0,i)=\{j\in\mathbb{N}\,|\,j<i\}`.
The disjoint union of two copies of :math:`\mathbb{N}`, *i.e.* the set
:math:`\{0,1\}\times\mathbb{N}` is also well-ordered, with respect to
the order below:

.. math::

   \begin{aligned}
   (i,j) < (i,k) & \;\textit{\textbf{if} }\; j < k\\
   (0,k) < (1,l) & \;\textit{\textbf{for\,any}}\;k \;\textit{\textbf{and}} \; l\end{aligned}

Ordinal numbers
~~~~~~~~~~~~~~~

:raw-latex:`\index{maths}{Ordinal numbers}`

Let :math:`(A,<_A)` and :math:`(B,<_B)` two well-ordered sets. :math:`A`
and :math:`B` are said to have *the same order type* if there exists a
strictly monotonous bijection :math:`b` from :math:`A` to :math:`B`,
*i.e.* which verifies the proposition
:math:`\forall x\,y\in A,\, x <_A y \Rightarrow b(x) <_B  b(y)`.

Having the same order type is an equivalence relation between
well-ordered sets. Ordinal numbers (in short: *ordinals*) are
descriptions (*names*) of the equivalence classes. For instance, the
order type of :math:`(\mathbb{N},<)` is associated with the ordinal
called :math:`\omega`, and the order we considered on the disjoint union
of :math:`\mathbb{N}` and itself is named :math:`\omega+\omega`.

In a set-theoretic framework, one can consider any ordinal
:math:`\alpha` as a well-ordered set, whose elements are just the
ordinals strictly less than :math:`\alpha`, *i.e.* the *segment*
:math:`\mathbb{O}_\alpha=[0, \alpha)`. So, one can speak about *finite*,
*infinite*, *countable*, etc., ordinals. Nevertheless, since we work
within type theory, we do not identify ordinals as sets of ordinals, but
consider the correspondance between ordinals and sets of ordinals as the
function that maps :math:`\alpha` to :math:`\mathbb{O}_\alpha`. For
instance :math:`\mathbb{O}_\omega=\mathbb{N}`, and
:math:`\mathbb{O}_7=\{0,1,2,3,4,5,6\}`.

We cannot cite all the litterature published on ordinals since Cantor’s
book :raw-latex:`\cite{cantorbook}`, and leave it to the reader to
explore the bibliography.

Ordinal numbers in Coq
----------------------

Two kinds of representation of ordinals are defined in our development.

-  A “mathematical” representation of the set of countable ordinal
   numbers, afer Kurt Schütte :raw-latex:`\cite{schutte}`. This
   representation uses several (hopefully harmless) axioms. We use it as
   a reference for proving the correctness of ordinal notations.

-  A family of *ordinal notations*, *i.e.* data types used to represent
   segments :math:`[0,\mu)`, where :math:`\mu` is some countable
   ordinal. Each ordinal notation is defined inside the Calculus of
   Inductive Constructions (without axioms). Many functions are defined,
   allowing proofs by computation. Note that proofs of correctness of a
   given ordinal notation with respect to Schütte’s model obviously use
   axioms. Please execute the ``Print Assumptions`` command in case of
   doubt.

It is interesting to compare proofs of a given property (for instance
the associativity of addition) both in the computational framework of
some ordinal notation, and in the axiomatic model of Schütte.

Ordinal Notations
-----------------

Fortunately, the ordinals we need for studying hydra battles are much
simpler than Schütte’s, and can be represented as quite simple data
types in :raw-latex:`\gallina`. So, we will use *ordinal notations*
(also called *[ordinal] notation systems*).

Let :math:`\alpha` be some (countable) ordinal; in :raw-latex:`\coq{}`
terms, we call *ordinal notation for :math:`\alpha`* a structure
composed of:

-  A data type :math:`A` for representing all ordinals strictly below
   :math:`\alpha`,

-  A well founded order :math:`<` on :math:`A`,

-  A correct function for comparing two ordinals. Note that the
   reflexive closure of :math:`<` is thus a *total order*.

Such a structure can be proved correct relatively to a bigger ordinal
notation or to Schütte’s model.

A class for ordinal notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following class definition, parameterized with a type :math:`A`, a
binary relation ``lt`` on :math:`A`, specifies that ``lt`` is a
well-founded strict order. The reflexive closure of ``lt``, (called
``le``, for “less or equal than”) is a total decidable order,
implemented through a comparison function ``compare``. The correctness
of this function is expressed through Stdlib’s type
``Datatypes.CompareSpec``.

First, we import the definition of strict orders from the library
 `Classes.RelationClasses <https://coq.inria.fr/distrib/current/stdlib/Coq.Classes.RelationClasses.html>`__,
and the inductive specification of a comparison from
`Init.Datatypes <https://coq.inria.fr/distrib/current/stdlib/Coq.Init.Datatypes.html>`__.

.. raw:: latex

   \begin{Coqsrc}
   Variable A: Type.

     Class StrictOrder (R : relation A) : Prop := {
       StrictOrder_Irreflexive :> Irreflexive R ;
       StrictOrder_Transitive :> Transitive R }.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Inductive CompareSpec (Peq Plt Pgt : Prop) : comparison -> Prop :=
       CompEq : Peq -> CompareSpec Peq Plt Pgt Eq
     | CompLt : Plt -> CompareSpec Peq Plt Pgt Lt
     | CompGt : Pgt -> CompareSpec Peq Plt Pgt Gt
   \end{Coqsrc}

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`\ *From
Library *\ `OrdinalNotations.Definitions <../theories/html/hydras.OrdinalNotations.Definitions.html>`__

:raw-latex:`\label{types:ON}`
:raw-latex:`\index{hydras}{Library OrdinalNotations!Type classes!ON}`

.. raw:: latex

   \begin{Coqsrc}
   Class ON {A:Type}(lt: relation A)
         (compare : A -> A -> comparison)  :=
     {
     sto :> StrictOrder lt;
     wf : well_founded lt;
     compare_correct :
       forall alpha beta:A,
         CompareSpec (alpha=beta) (lt alpha beta) (lt beta alpha)
                     (compare alpha beta);
     }.
   \end{Coqsrc}

:raw-latex:`\label{sect:on-lt-notation}`
:raw-latex:`\label{sect:on-le-notation}`

.. raw:: latex

   \begin{Coqsrc}
   Definition on_t  {A:Type}{lt: relation A}
               {compare : A -> A -> comparison}
               {on : ON lt compare} := A.

   Definition ON_compare {A:Type}{lt: relation A}
               {compare : A -> A -> comparison}
               {on : ON lt compare} := compare.

   Definition ON_lt {A:Type}{lt: relation A}
              {compare : A -> A -> comparison}
              {on : ON lt compare} := lt.

   Infix "o<" := ON_lt : ON_scope.

   Definition ON_le  {A:Type}{lt: relation A}
              {compare : A -> A -> comparison}
              {on : ON lt compare} :=
     clos_refl _ ON_lt.

   Infix "o<=" := ON_le : ON_scope.
   \end{Coqsrc}

.. raw:: latex

   \begin{remark}
   The infix notations \texttt{o<} and \texttt{o<=} are defined in order to make apparent the distinction between the various notation scopes that may co-exist in a same statement. So the infix \texttt{<} and \texttt{<=} are reserved to the natural numbers. In the mathematical formulas, however, we still use $<$ and $\leq$ for comparing ordinals.
   \end{remark}

.. _sect:measure-ON:

Ordinal notations and termination measures
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following lemma (together with the type class mechnism) allows us to
define termination measures over any ordinal notation. It is just an
application of the libraries ``Coq.Wellfounded.Inverse_Image`` and
``Coq.Wellfounded.Inclusion``.

.. raw:: latex

   \begin{Coqsrc}
   Definition measure_lt {A:Type}{lt: relation A}
               {compare : A -> A -> comparison}
               {on : ON lt compare}
               {B : Type} (m : B -> A) : relation B :=
                fun x y => on_lt (m x) (m y).
               
   Lemma wf_measure  {A:Type}(lt: relation A)
               {compare : A -> A -> comparison}
               {on : ON lt compare}
               {B : Type}
               (m : B -> A):  well_founded (measure_lt m). 
   \end{Coqsrc}

A simple example of application is given in
Sect. :raw-latex:`\vref{sect:merge-example}`.

Example: the ordinal :math:`\omega`
-----------------------------------

The simplest example of ordinal notation is built over the type ``nat``
of :raw-latex:`\coq`’s standard library. We just have to apply already
proven lemmas about Peano numbers.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`\ *From
Library *\ `OrdinalNotations.ON_Omega <../theories/html/hydras.OrdinalNotations/ON_Omega.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Global Instance Omega : ON  Peano.lt Nat.compare.
   Proof.
    split.
    - apply Nat.lt_strorder.
    - apply Wf_nat.lt_wf.
    - apply Nat.compare_spec.
   Qed.

   Compute ON_compare 6 9.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
        = Lt
        : comparison
   \end{Coqanswer}

Sum of two ordinal notations
----------------------------

Let ``NA`` and ``NB`` be two ordinal notations, on the respective types
``A`` and ``B``.

We consider a new strict order on the disjoint sum of the associated
types, by putting all elements of ``A`` before the elements of ``B``
(thanks to Standard Library’s relation operator ``le_AsB``).

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent` *From
Library *\ `Relations.Relation_Operators <https://coq.inria.fr/distrib/current/stdlib/Coq.Relations.Relation_Operators.html>`__.

.. raw:: latex

   \begin{Coqanswer}
   Inductive
   le_AsB (A B : Type) (leA : A -> A -> Prop) (leB : B -> B -> Prop)
     : A + B -> A + B -> Prop :=
   | le_aa : forall x y : A, leA x y -> le_AsB A B leA leB (inl x) (inl y)
   | le_ab : forall (x : A) (y : B), le_AsB A B leA leB (inl x) (inr y)
   | le_bb : forall x y : B, leB x y -> le_AsB A B leA leB (inr x) (inr y)
   \end{Coqanswer}

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`\ *From
Library *\ `OrdinalNotations.ON_plus <../theories/html/hydras.OrdinalNotations/ON_plus.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Section Defs.

     Context `(ltA: relation A)
             (compareA : A -> A -> comparison)
             (NA: ON ltA compareA).
     Context `(ltB: relation B)
             (compareB : B -> B -> comparison)
             (NB: ON ltB compareB).


   Definition t := (A + B)%type.
   Arguments inl  {A B} _.
   Arguments inr  {A B} _.

   Definition lt : relation t := le_AsB _ _ ltA ltB.
   \end{Coqsrc}

Before building an instance of ``ON``, we have to define a comparison
function.

.. raw:: latex

   \begin{Coqsrc}
   Definition compare (alpha beta: t) : comparison :=
      match alpha, beta with
        inl _, inr _ => Lt
      | inl a, inl a' => compareA a a'
      | inr b, inr b' => compareB b b'
      | inr _, inl _ => Gt
     end.

   Lemma compare_correct alpha beta :
       CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
                               (compare alpha beta).
   \end{Coqsrc}

The Lemma ``Wellfounded.Disjoint_Union.wf_disjoint_sum`` of Standard
Library helps us to prove that our order ``lt`` is well-founded.

.. raw:: latex

   \begin{Coqsrc}
   Lemma lt_wf : well_founded lt.
   Proof. 
     destruct NA, NB; apply wf_disjoint_sum; [apply wf | apply wf0].
   Qed.
   \end{Coqsrc}

Then, we register an instance of ``ON``:

.. raw:: latex

   \begin{Coqsrc}
   Global Instance ON_plus : ON lt compare.
   Proof.
     split.
     - apply lt_strorder.
     -  apply lt_wf.
     - apply compare_correct.
   Qed.
   \end{Coqsrc}

The ordinal :math:`\omega+\omega`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The ordinal :math:`\omega+\omega` (also known as :math:`\omega\times 2`)
may be represented as the concatenation of two copies of :math:`\omega`
(Figure :raw-latex:`\ref{fig:omega-plus-omega}`).

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.5]
   \begin{scope}[color=blue]
   \node(A0) at (2,0)[label=below:$0$]{$\bullet$};
   \node(A1) at (3,0)[label=below:$1$]{$\bullet$};
   \node(A2) at (4,0)[label=below:$2$]{$\bullet$};
   \node (Adots) at (6,0) {$\ldots$};
   \node(An) at (8,0)[label=below:$n$]{$\bullet$};
   \node(A2) at (10,0)[label=below:$n+1$]{$\bullet$};
   \node (Adots1) at (12,0) {$\ldots$};
   \end{scope}
   \begin{scope}[color=red]
   \node(B0) at (14,0)[label=below:$0$,label=above:\textcolor{red}{$\omega$}]{$\bullet$};
   \node(B1) at (16,0)[label=below:$1$, label=above:$\omega+1$]{$\bullet$};
   \node(B2) at (18,0)[label=below:$2$,label=above:$\omega+2$]{$\bullet$};
   \node (Bdots) at (20,0) {$\ldots$};
   \node (Bn) at (22,0) [label=below:$p$, label=above:$\omega+p$]{$\bullet$};
   \node (Bdots2) at (24,0) {$\ldots$};
   \end{scope}
   \end{tikzpicture}

We can define this notation in :raw-latex:`\coq{}` as an instance of
``ON_plus``.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`\ *From
Module *\ `OrdinalNotations.ON_Omega_plus_omega <../theories/html/hydras.OrdinalNotations.ON_Omega_plus_omega.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Definition Omega_plus_Omega := ON_plus Omega Omega.

   Existing Instance Omega_plus_Omega.
   Definition t := @ON_plus.t nat nat.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Example ex1 : inl 7 o< inr 0.
   Proof. constructor. Qed.
   \end{Coqsrc}

We can now define abbreviations. For instance, the finite ordinals are
represented by terms built with the constructor ``inl``, and the first
infinite ordinal :math:`\omega` by the term ``(inr 0)``.

.. raw:: latex

   \begin{Coqsrc}
   Definition fin (i:nat) : t := inl i.
   Coercion fin : nat >-> t.

   Notation "'omega'" := (inr  0:t).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Example ex1' : fin 7 o< omega.
   Proof. constructor. Qed.

   Lemma lt_omega alpha : 
        alpha o< omega <-> exists n:nat,  alpha = fin n.
   (* ... *)
   \end{Coqsrc}

Limits and successors
---------------------

Let us look again at our implementation of :math:`\omega+\omega`. We can
classify its elements into three categories:

-  The least ordinal, ``(inl 0)``, also known as ``(fin 0)``.

-  The limit ordinal :math:`\omega`.

-  The successor ordinals, either of the form ``(inl (S i))`` or
   ``(inr (S i))``

Definitions
~~~~~~~~~~~

It would be interesting to specify at the most generic level, what is a
zero, a successor or a limit ordinal. Let :math:`<` be a strict order on
a type :math:`A`.

-  A *least* element is a minorant (in the large sense) of the full set
   on :math:`A`,

-  :math:`y` is a *successor* of :math:`x` if :math:`x<y` and there is
   no element between :math:`x` and :math:`y`. We will also say that
   :math:`x` is a *predecessor* of :math:`y`.

-  :math:`x` is a *limit* if :math:`x` is not a least element, and for
   any :math:`y` such that :math:`yo<x`, there exists some :math:`z`
   such that :math:`y<z<x`.

The following definitions are in Library
`Prelude.MoreOrders <../theories/html/hydras.Prelude.MoreOrders.html>`__.

.. raw:: latex

   \begin{Coqsrc}
   Section A_given.
     Variables (A : Type)  (lt: relation A).
     
   Local Infix "<" := lt.
   Local Infix "<=" := (clos_refl _ lt).

   Definition Least {sto : StrictOrder lt} (x : A):=
     forall y,  x <= y.

   Definition Successor {sto : StrictOrder lt} (y x : A):=
     x < y /\ (forall z,  x < z ->  z <  y -> False).

   Definition Limit {sto : StrictOrder lt}  (x:A)  :=
     (exists w:A,  w < x) /\
     (forall y:A, y < x -> exists z:A, y < z /\ z < x).
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove, that, in any ordinal notation system, every ordinal has at most one predecessor, and at most one successor. 

   \emph{You may start this exercise with the file
   \url{../exercises/ordinals/predSuccUnicity.v}.}

   \end{exercise}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove, that, in any ordinal notation system, if $\beta$ is a successor of $\alpha$,
   then for any $\gamma$, $\gamma<\beta$ implies 
   $\gamma\leq\alpha$.

   \emph{You may start this exercise with the file
   \url{../exercises/ordinals/lt_succ_le.v}.}
   \end{exercise}

Limits and successors in :math:`\omega+\omega`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Using the definitions above, we can prove the following lemma:

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`\ *From
Module *\ `OrdinalNotations.ON_Omega_plus_omega <../theories/html/hydras.OrdinalNotations.ON_Omega_plus_omega.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Lemma limit_iff (alpha : t) : Limit alpha <-> alpha = omega.
   \end{Coqsrc}

Regarding successors, let us introduce the following definition:

.. raw:: latex

   \begin{Coqsrc}
   Definition succ (alpha : t) :=
     match alpha with
       inl n => inl (S n)
     | inr n => inr (S n)
     end.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma Successor_correct alpha beta : Successor beta alpha <->
                                        beta = succ alpha.
   \end{Coqsrc}

We can also check whether an ordinal is a successor by a simple pattern
matching:

.. raw:: latex

   \begin{Coqsrc}
   Definition succb (alpha: t) : bool := match alpha with
                                    | inr (S  _) | inl (S _) => true
                                    | _ => false
                                    end.

   Lemma succb_correct (alpha : t) :
       succb alpha <->  exists beta: t, alpha = succ beta.
   \end{Coqsrc}

Finally, the nature of any ordinal is decidable(inside this notation
system) :

:raw-latex:`\noindent`\ *From
Module *\ `ON_Generic <../theories/html/hydras.OrdinalNotations.ON_Generic.html>`__

.. raw:: latex

   \begin{Coqsrc}
     Definition ZeroLimitSucc_dec {A:Type}{lt: relation A}
              {compare : A -> A -> comparison}
              {on : ON lt compare} :=
     forall alpha,
       {Least alpha} +
       {Limit alpha} +
       {beta: A | Successor alpha beta}.
   (* ... *)
   \end{Coqsrc}

:raw-latex:`\noindent`\ *From
Module *\ `OrdinalNotations.ON_Omega_plus_omega <../theories/html/hydras.OrdinalNotations.ON_Omega_plus_omega.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Definition Zero_limit_succ_dec : ZeroLimitSucc_dec.
   \end{Coqsrc}

Product of ordinal notations
----------------------------

Let ``NA`` and ``NB`` be two ordinal notations, on the respective
ordered types ``A`` and ``B``. The product of ``NA`` and ``NB`` is
considered as the concatenation of :math:`B` copies of :math:`A`,
ordered by the lexicographic order on :math:`B\times A`.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent` *From
Module *\ `OrdinalNotations.ON_mult <../theories/html/hydras.OrdinalNotations.ON_mult.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Section Defs.

     Context `(ltA: relation A)
             (compareA : A -> A -> comparison)
             (NA: ON ltA compareA).
     Context `(ltB: relation B)
             (compareB : B -> B -> comparison)
             (NB: ON ltB compareB).

   Definition t := (B * A)%type.
   Definition lt : relation t := lexico ltB ltA.
   Definition le := clos_refl _ lt.

   Definition compare (alpha beta: t) : comparison :=
     match compareB (fst alpha) (fst beta) with
     |  Eq => compareA (snd alpha) (snd beta)
     | c => c
     end.

   Lemma compare_reflect alpha beta :
     match (compare alpha beta)
     with
       Lt => lt alpha  beta
     | Eq => alpha = beta
     | Gt => lt beta  alpha
     end.

   Global Instance ON_mult : ON lt compare.

   End Defs.
   \end{Coqsrc}

The ordinal :math:`\omega^2`
----------------------------

The ordinal :math:`\omega^2` (also called :math:`\phi_0(2)`, see
Chap. :raw-latex:`\ref{chap:schutte}`), is an instance of the
multiplication presented in the last section.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`\ *From
Module *\ `OrdinalNotations.ON_Omega2 <../theories/html/hydras.OrdinalNotations.ON_Omega2.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Definition Omega2 := ON_mult Omega Omega.
   Existing Instance Omega2.
   Definition t := ON_mult.t nat nat.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Definition zero: t := (0,0).

   Definition fin (n:nat) : t := (0, n).

   Coercion fin : nat >-> t.

   Notation "'omega'" := (1,0) : ON_scope.

   Definition limitb (alpha : t) := 
    match alpha with
    |  (S _, 0) => true
    | _ => false
   end.
   \end{Coqsrc}

Arithmetic of :math:`\omega^2`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Successor
^^^^^^^^^

The successor of any ordinal is defined by a simple pattern-matching.
This function is proved to be correct w.r.t. the ``Successor``
predicate.

.. raw:: latex

   \begin{Coqsrc}
   Definition succ (alpha : t) := (fst alpha, S (snd alpha)).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma lt_succ_le alpha beta : alpha o< beta <-> succ alpha o<= beta.

   Lemma lt_succ alpha : alpha o< succ alpha.

   Lemma succ_ok alpha beta : Successor beta alpha <-> beta = succ alpha.
   \end{Coqsrc}

Addition
^^^^^^^^

We can define on ``Omega2`` an addition which extends the addition on
``nat``.

.. raw:: latex

   \begin{Coqsrc}
   Definition  plus (alpha beta : t) : t :=
     match alpha,beta with
     | (0, b), (0, b') => (0, b + b')
     | (0,0), y  => y
     | x, (0,0)  => x
     | (0, b), (S n', b') => (S n', b')
     | (S n, b), (S n', b') => (S n + S n', b')
     | (S n, b), (0, b') => (S n, b + b')
      end.

   Infix "+" := plus : o2_scope.
   \end{Coqsrc}

Please note that this operation is not commutative:

.. raw:: latex

   \begin{Coqsrc}
   Example non_commutativity_of_plus :  omega + 3 <> 3 + omega.
   Proof.
     cbn.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   1 subgoal (ID 237)
     
     ============================
   (1, 3) <> omega.
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
    discriminate.
   Qed.
   \end{Coqsrc}

Multiplication
^^^^^^^^^^^^^^

The restriction of ordinal multiplication to the segment
:math:`[0,\omega^2)` is not a total function. For instance
:math:`\omega\times\omega= \omega^2` is outside the set of represented
values. Nevertheless, we can define two operations mixing natural
numbers and ordinals.

.. raw:: latex

   \begin{Coqsrc}
   (** multiplication of an ordinal by a natural number *)

   Definition mult_fin_r  (alpha : t) (p : nat): t :=
     match alpha, p with
    |  (0,0), _  => zero
    |  _, 0 => zero
    |  (0, n), p => (0, n * p)
    |  ( n, b),  n' => ( n *  n', b)
    end.
   Infix "*" := mult_fin_r : o2_scope.

   (** multiplication of  a natural number by an ordinal *)

   Definition mult_fin_l (n:nat)(alpha : t) : t :=
     match n, alpha with
    |  0, _  => zero
    |  _, (0,0) => zero
    |   n , (0,n') => (0, (n*n')%nat)
    |  n, (n',p') => (n', (n * p')%nat)
    end.

   Example e1 : (omega * 7 + 15) * 3 = omega * 21 + 15.
   Proof. reflexivity. Qed.

   Example e2 :  mult_fin_l 3 (omega * 7 + 15) = omega * 7 + 45.
   Proof. reflexivity. Qed.
   \end{Coqsrc}

Multiplication with a finite ordinal and addition are related through
the following lemma:

.. raw:: latex

   \begin{Coqsrc}
   Lemma unique_decomposition alpha : 
       exists! i j: nat,  alpha = omega * i + j.
   \end{Coqsrc}

.. _sect:merge-example:

A proof of termination using :math:`\omega^2`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.

Using the lemma of Sect. :raw-latex:`\vref{sect:measure-ON}`, we can
define easily a total function which merges two lists (example
contributed by Pascal Manoury).

:raw-latex:`\index{coq}{Commands!Function}`

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`\ *From
Module *\ `OrdinalNotations.ON_Omega2 <../theories/html/hydras.OrdinalNotations.ON_Omega2.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Section Merge.

     Variable A: Type.

     Local Definition m (p : list A * list A) :=
       omega * length (fst p) + length (snd p).

     Function  merge  (ltb: A -> A -> bool)
             (xys: list A * list A)
             {wf (measure_lt m) xys} :
       list A :=
       match xys with
         (nil, ys) => ys
       | (xs, nil) => xs
       | (x :: xs, y :: ys) =>
         if ltb x y then x :: merge  ltb (xs, (y :: ys))
         else y :: merge  ltb ((x :: xs), ys)
       end.

     - intros; unfold m, measure_lt; cbn; destruct xs0; simpl; left; lia.
     - intros; unfold m, measure_lt; cbn; destruct ys0; simpl; right; lia.
     - apply wf_measure.
     Defined.

   End Merge.

   Goal forall l, merge nat Nat.leb (nil, l) = l.
     intro; now rewrite merge_equation.
   Qed.
   \end{Coqsrc}

.. _omega2-case:

Yet another proof of impossibility
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In Sect. :raw-latex:`\vref{omega-case}`, we proved that there exists no
variant from ``Hydra`` to ``(nat,<)`` (*i.e.* the ordinal
:math:`\omega`) for proving the termination of all hydra battles. We
prove now that the ordinal :math:`\omega^2` is also insufficient for
this purpose.

The proof we are going to comment has exactly the same structure as in
Section :raw-latex:`\ref{omega-case}`. Nevertheless, the proof of
technical lemmas is a little more complex, due to the structure of the
lexicographic order on :math:`\mathbb{N}\times\mathbb{N}`. Consider for
instance that there exists an infinite number of ordinals between
:math:`\omega` and :math:`\omega\times 2`.

The detailed proof script is in the file
`../theories/html/hydras.Hydra.Omega2_Small.html <../theories/html/hydras.Hydra.Omega2_Small.html>`__.

Preliminaries
^^^^^^^^^^^^^

Let us assume there is a variant from ``Hydra`` into :math:`\omega^2`
for proving the termination of all hydra battles.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Omega2_Small <../theories/html/hydras.Hydra.Omega2_Small.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Section Impossibility_Proof.
     
    Variable m : Hydra -> ON_Omega2.t.
     
    Context (Hvar : Hvariant (ON_Generic.wf (ON:=Omega2))  free m).
   \end{Coqsrc}

We follow the same pattern as in Sect. :raw-latex:`\ref{omega-case}`.
First, we define an injection :math:`\iota` from type ``t`` into
``Hydra``, by associating to each ordinal
:math:`\omega\times i+ j = (i,j)` the hydra with :math:`i` branches of
length :math:`2` and :math:`j` branches of length :math:`1`.

.. raw:: latex

   \vspace{4pt}

*From Module
 *\ `Hydra.Omega2_Small <../theories/html/hydras.Hydra.Omega2_Small.html#iota>`__

.. raw:: latex

   \begin{Coqsrc}
    Let iota (p: ON_Omega2.t) := 
        node (hcons_mult (hyd1 head) (fst p)
                       (hcons_mult head (snd p) hnil)).
   \end{Coqsrc}

For instance, Figure :raw-latex:`\vref{fig:essai2}` shows the hydra
associated to the ordinal :math:`(3,5)`, a.k.a.
:math:`\omega\times 3 + 5`.

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.4]
   \node (foot) at (6,0) {$\bullet$};
   \node (N1) at (1,3) {$\bullet$};
   \node (N2) at (3,3) {$\bullet$};
   \node (N3) at (5,3) {$\bullet$};
   \node (N4) at (8,3) {$\Smiley[2][green]$};
   \node (N5) at (11,3) {$\Smiley[2][green]$};
   \node (N6) at (14,3) {$\Smiley[2][green]$};
   \node (N7) at (17,3){$\Smiley[2][green]$};
   \node (N8) at (20,3){$\Smiley[2][green]$};
   \node  (N9) at (0,5) {$\Smiley[2][green]$};
   \node (N10) at (2,5) {$\Smiley[2][green]$};
   \node (N11) at (4,5) {$\Smiley[2][green]$};
   \draw (foot) to [bend left=10] (N1);
   \draw (foot) -- (N2);
   \draw (foot) -- (N3);
   \draw (foot) -- (N4);
   \draw (foot) -- (N5);
   \draw (foot) -- (N6);
   \draw (foot) to [bend right=10] (N7);
   \draw (foot) to [bend right=15] (N8);
   \draw (N1) to [bend left=10] (N9);
   \draw (N2) -- (N10);
   \draw (N3) -- (N11);
   \end{tikzpicture}

Like in Sect. :raw-latex:`\ref{omega-case}`, we build a hydra out of the
range of ``iota`` (represented in
Fig. :raw-latex:`\vref{fig:h-omega2-small}`).

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.5]
   \node (foot) at (2,0) {$\bullet$};
   \node (N1) at (2,2) {$\bullet$};
   \node (N2) at (3,4) {$\Smiley[2][green]$};
   \node (N3) at (1,4) {$\Smiley[2][green]$};
   \draw (foot) -- (N1);
   \draw (N1) to [bend right =15] (N2);
   \draw (N1) to  [bend left=15](N3);
   \end{tikzpicture}

The hydra ``big_h``.

.. raw:: latex

   \begin{Coqsrc}
      Let big_h := hyd1 (hyd2 head head).  
   \end{Coqsrc}

In a second step, we build a “smaller” hydra [9]_.

.. raw:: latex

   \begin{Coqsrc}
      Let small_h := iota (m big_h).
   \end{Coqsrc}

Like in Sect. :raw-latex:`\ref{omega-case}`, we prove the double
inequality ``m big_h o<= m small_h o< m big_h``, which is impossible.

Proof of the inequality ``m small_h o< m big_h``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In order to prove the inequality ``m_lt: m small_h o< m big_h``, it
suffices to build a battle transforming ``big_h`` into ``small_h``.

First we prove that ``small_h`` is reachable from ``big_h`` in one or
two steps. Let us decompose ``m big_h`` as :math:`(i,j)`. If
:math:`j=0`, then one round suffices to transform ``big_h`` into
:math:`\iota(i,j)`. If :math:`j>0`, then a first round transforms
``big_h`` into :math:`\iota(i+1,0)` and a second round into
:math:`\iota(i,j)`. So, we have the following result.

.. raw:: latex

   \begin{Coqsrc}
     Lemma big_to_small: big_h -+-> small_h.
   \end{Coqsrc}

Since :math:`m` is a variant, we infer the following inequality:

.. raw:: latex

   \begin{Coqsrc}
      Corollary m_lt : m small_h o< m big_h.
   \end{Coqsrc}

Proof of the inequality ``m big_h o<= m small_h`` 
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The proof of the inequality ``m big_h o<= m small_h`` is quite more
complex than in Sect :raw-latex:`\ref{omega-case}`. If we consider any
ordinal :math:`\alpha=(i,j)`, where :math:`i>0`, there exists an
infinite number of ordinals stricly less than :math:`\alpha`, and there
exists an infinite number of battles that start from
:math:`\iota(\alpha)`. Indeed, at any configuration :math:`\iota(k,0)`,
where :math:`k>0`, the hydra can freely choose any replication number.
Intuitively, the measure of such a hydra must be large enough for taking
into account all the possible battles issued from that hydra. Let us now
give more technical details.

-  The proof of the lemma ``m_ge : m big_h o<= m small_h`` uses
   well-founded induction on ``big_h``.

-  For any pair :math:`p`, we have to distinguish between three cases,
   according to the value of :math:`p`\ ’s components.

   -  :math:`p=(0,0)`

   -  :math:`p=(i,0)`, where :math:`i>0` : :math:`p` corresponds to a
      limit ordinal

   -  :math:`p=(i,j)`, where :math:`j>0` : :math:`p` is the successor of
      :math:`(i,j-1)`.

Let us define the notion of elementary “step” of decreasing sequences in
``t``

.. raw:: latex

   \begin{Coqsrc}
     Inductive step : t -> t -> Prop :=
     | succ_step : forall i j,  step (i, S j) (i, j)
     | limit_step : forall i j, step (S i, 0) (i, j).
   \end{Coqsrc}

The following lemma establishes a correspondance between the relation
``step`` and hydra battles.

.. raw:: latex

   \begin{Coqsrc}
     Lemma step_to_battle : forall p q, step p q -> iota p -+-> iota q.
   \end{Coqsrc}

:raw-latex:`\index{maths}{Transfinite induction}`

Thus, starting from any inequality :math:`q < p` on type ``t``, we can
build by *transfinite induction* (*i.e.* well-founded) over ``p`` a
battle that transforms the hydra :math:`\iota(p)` into :math:`\iota(q)`.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Omega2_Small <../theories/html/hydras.Hydra.Omega2_Small.html#m_ge>`__

.. raw:: latex

   \begin{Coqsrc}
     Lemma m_ge : forall p : t,   p o<= m (iota p).
     Proof.
       unfold small_h; pattern (m big_h) .   
        apply  well_founded_induction with (R := lt) (1:= lt_wf).
        intro p ; pattern p;
        apply  well_founded_induction with 
                  (R := lt2) (1:= wf_lexico lt_wf lt_wf);
        intros (i,j) IHij. 
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
     i, j : nat
     IHij : forall y : t, y o< (i, j) -> y o<= m (iota y)
     ============================
     (i, j) o<= m (iota (i, j)) 
   \end{Coqanswer}

Then we have three cases to consider, according to the value of
:math:`p`.

-  If :math:`p=(0,0)` then obviously, :math:`\iota(p)\geq p = (0,0)`

-  If :math:`p=(i+1,0)` for some :math:`i\in\mathbb{N}`, we remark that
   :math:`p` is strictly greater than any pair :math:`(i, j)`, where
   :math:`j` is any natural number.

   Applying the battle rules, for any :math:`j`, we have
   :math:`\iota(i+1,j)  {\round} \iota(i, j)`, thus
   :math:`m(\iota(p)) > m(\iota(i,j)` since :math:`m` is assumed to be a
   variant.

   Applying the induction hypothesis, we get the inequality
   :math:`m(\iota(i,j)) \geq (i,j)` for any :math:`j`.

   Thus, :math:`m(\iota(p)) > (i,j)` for any :math:`j`. Applying the
   lemma ``limit_is_lub``, we get the inequality
   :math:`m(\iota(i+1,0))\geq (i+1,0)`

-  If :math:`p=(i,j+1)` with :math:`j\in\mathbb{N}`, we have
   :math:`\iota(p)  {\round} \iota(i, j)`, hence
   :math:`m(\iota(p))> m(\iota(i,j)) \geq (i,j)`, thus
   :math:`m(\iota(p))\geq (i,j+1)=p`

.. raw:: latex

   \begin{Coqsrc}
     (* ... *)
   Qed.
   \end{Coqsrc}

End of the proof
^^^^^^^^^^^^^^^^

From ``m_ge``, we get ``m big_h o<= m small_h = m (iota (m big_h))``.
Since :math:`<` is a strict order (irreflexive and transitive), this
inequality is incompatible with the strict inequality
``m small_h o< m big_h`` (lemma ``m_lt``).

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent` In
:raw-latex:`\coq `(Module `Hydra.Omega2_Small <../theories/html/hydras.Hydra.Omega2_Small.html#Impossible>`__):

.. raw:: latex

   \begin{Coqsrc}
     Theorem Impossible: False.
     Proof.
       destruct (StrictOrder_Irreflexive (m big_h)).
       apply le2_lt2_trans with (m small_h).
       -  unfold small_h; apply m_ge.
       -  apply m_lt. 
   Qed. 
   End Impossibility_Proof.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove that there exists no variant $m$ from \texttt{Hydra} into $\omega^2$ for proving
       the  termination of all \emph{standard} battles.
   \end{exercise}

.. raw:: latex

   \begin{remark}
   In Chapter~\ref{ks-chapter}, we  prove a generalization of the impossibility lemmas of
   Sect.~\ref{omega-case} and this section, with the same proof structure, but with much more 
   complex technical details.
    \end{remark}

A notation for finite ordinals
------------------------------

Let :math:`n` be some natural number. The segment associated with
:math:`n` is the interval :math:`[0,n)\,=\,\{0,1,\dots,n-1\}`. One may
represent the ordinal :math:`n` by a sigma type.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`\ *From
Module *\ `OrdinalNotations.ON_Finite <../theories/html/hydras.OrdinalNotations.ON_Finite.html>`__

:raw-latex:`\label{def: Finite-ord-type}`

.. raw:: latex

   \begin{Coqsrc}
   Coercion is_true: bool >-> Sortclass.

   Definition t (n:nat) := {i:nat | Nat.ltb i n}.
   \end{Coqsrc}

The order on type (``t n``) is defined through the projection on
``nat``.

.. raw:: latex

   \begin{Coqsrc}
   Definition lt {n:nat} : relation (t n) :=
     fun alpha beta => Nat.ltb ( proj1_sig alpha) (proj1_sig beta).
   \end{Coqsrc}

For instance, let us build two elements of the segment :math:`[0, 7)`,
*i.e.* two inhabitants of type (``t 7``), and prove a simple inequality
(see Fig. :raw-latex:`\ref{fig:O7}`).

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.6]

   \node (N0) at (0,0) {$\bullet$};
   \node (i0) at (0,1) {$0$};
   \node (N1) at (2,0) {$\bullet$};
   \node (i1) at (2,1) {$1$};
   \node (N2) at (4,0) {$\bullet$};
   \node (i2) at (4,1) {$2$};
   \node (N3) at (6,0) {$\bullet$};
   \node (i3) at (6,1) {$3$};
   \node (N4) at (8,0) {$\bullet$};
   \node (i4) at (8,1) {$4$};
   \node (N5) at (10,0) {$\bullet$};
   \node (i5) at (10,1) {$5$};
   \node (N6) at (12,0) {$\bullet$};
   \node (i6) at (12,1) {$6$};
   \node(alpha1) at (4,-1) {$\alpha_1$};
   \node(alpha2) at (10,-1) {$\beta_1$};
   \end{tikzpicture}

:raw-latex:`\index{coq}{Commands!Program}`

.. raw:: latex

   \begin{Coqsrc}
   Program Example alpha1 : t 7 := 2.

   Program Example beta1 : t 7 := 5.

   Example i1 : lt  alpha1 beta1.
   Proof. now compute. Qed.
   \end{Coqsrc}

Note that the type (``t 0``) is empty, and that, for any natural number
:math:`n`, :math:`n` does not belong to (``t n``).

.. raw:: latex

   \begin{Coqsrc}
   Lemma t0_empty (alpha: t 0): False.
   Proof.
     destruct alpha.
     destruct x; cbn in i; discriminate.
   Qed.


   Program Definition bad : t 10 := 10.
   Next Obligation.
     compute.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   1 subgoal (ID 162)
     
     ============================
     false = true
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Abort.
   \end{Coqsrc}

Note also that attempting to compare a term of type (``t n``) with a
term of type (``t p``) leads to an error if :math:`n` and :math:`p` are
not convertible.

.. raw:: latex

   \begin{Coqsrc}

   Program Example gamma1 : t 8 := 7.

   Fail Goal lt alpha1 gamma1.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
    The command has indeed failed with message:
   The term "gamma1" has type "t 8" while it is expected to have type "t 7".
   \end{Coqanswer}

In order to build an instance of ``OrdinalNotation``, we define a
comparison function, by delegation to standard library’s
``Nat.compare``, and prove its correction.

.. raw:: latex

   \begin{Coqsrc}
   Definition compare {n:nat} (alpha beta : t n) :=
     Nat.compare (proj1_sig alpha) (proj1_sig beta).

   Lemma compare_correct {n} (alpha beta : t n) :
     CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
                 (compare alpha beta).
   \end{Coqsrc}

.. raw:: latex

   \begin{remark}
    The proof of \texttt{compare\_correct} uses a well-known pattern of \coq{}.
   Let us consider  the following subgoal.

   \begin{Coqanswer}
    1 subgoal (ID 110)
     
     n, x0 : nat
     i, i0 : x0 <? S n
     ============================
     exist (fun i1 : nat => i1 <=? n) x0 i =
     exist (fun i1 : nat => i1 <=? n) x0 i0
   \end{Coqanswer}

   Applying the tactic \texttt{f\_equal} generates a simpler subgoal.

   \begin{Coqanswer}
   1 subgoal (ID 112)
     
     n, x0 : nat
     i, i0 : x0 <? S n
     ============================
     i = i0
   \end{Coqanswer}

   We have now to prove that there exists at most one  proof of (\texttt{Nat.ltb x0 (S n)}). This is not obvious, but  a consequence of the following lemma of library 
   \href{https://coq.inria.fr/distrib/current/stdlib/Coq.Logic.Eqdep_dec.html}{Coq.Logic.Eqdep\_dec}.

   \index{Coq!Unicity of equality proofs}
   \label{sect:eq-proof-unicity}

   \begin{Coqanswer}
   eq_proofs_unicity_on :
   forall (A : Type) (x : A),
   (forall y : A, x = y \/ x <> y) -> 
   forall (y : A) (p1 p2 : x = y), p1 = p2
   \end{Coqanswer}

   Thus unicity of proofs of \texttt{Nat.ltb x0 (S n)}  comes from the decidability of
   equality on type \texttt{bool}.
   This is why we used the boolean function \texttt{Nat.ltb} instead of the inductive predicate \texttt{Nat.lt} in the definition of type \texttt{t $n$} (see page~\pageref{def: Finite-ord-type}).
   For more information about this pattern, please look at the numerous mailing lists and 
   FAQs on \coq{}).



   \end{remark}

Applying lemmas of the libraries ``Coq.Wellfounded.Inverse_Image``,
:raw-latex:`\linebreak` ``Coq.Wellfounded.Inclusion``, and
``Coq.Arith.Wf_nat``, we prove that our relation ``lt`` is well founded.

.. raw:: latex

   \begin{Coqsrc}
   Lemma lt_wf (n:nat) : well_founded (@lt n).
   \end{Coqsrc}

Now we can build our instance of ``OrdinalNotation``.

.. raw:: latex

   \begin{Coqsrc}
   Global Instance sto n : StrictOrder (@lt n).

   Global Instance FinOrd (n:nat) : OrdinalNotation (sto n) compare.
   Proof.
     split.
     - apply compare_correct.
     - apply lt_wf.
   Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{remark}
   It is important to keep in mind  that the integer $n$ is not an ``element'' of \texttt{FinOrd $n$}. In set-theoretic presentations of ordinals, the set associated with the ordinal $n$ is $\{0,1,\dots,n-1\}$. 
   In our formalization, the interpretation of an ordinal as a set is realized by the following definition
   (in ~\href{../theories/html/hydras.OrdinalNotations.ON_Generic.html}{ON\_Generic}).

   \begin{Coqsrc}
   Definition bigO `{nA : @OrdinalNotation A ltA stoA compareA}
              (a: A) : Ensemble A :=
     fun x: A => ltA x a.
   \end{Coqsrc}
   \end{remark}

.. raw:: latex

   \begin{remark}
    There is no interesting arihmetic on finite ordinals, since functions like successor, addition, etc.,  cannot be represented in \coq{} as \emph{total} functions.
   \end{remark}

.. raw:: latex

   \begin{remark}
   Finite ordinals are also formalized in MathComp~\cite{SSR}.  See also Adam Chlipala's \emph{CPDT}~\cite{chlipalacpdt2011} for a thorough study of the use of dependent types.  
   \end{remark}

Comparing two ordinal notations
-------------------------------

It is sometimes useful to compare two ordinal notations with respect to
expressive power (the segment of ordinals they represent).

The following class specifies a strict inclusion of segments. The
notation ``OA`` describes a segment :math:`[0,\alpha)`, and ``OB`` is a
larger segment (which contains a notation for :math:`\alpha`, whilst
:math:`\alpha` is not represented in ``OA``). We require also that the
comparison functions of the two notation systems are compatible.

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.6]
   \begin{scope}[color=blue]
   \node (A) at (0,0) {$A$};
   \node(A0) at (2,0)[label=below:$0$]{$\bullet$};
   \node(A1) at (3,0)[label=below:$1$]{$\bullet$};
   \node(A2) at (4,0)[label=below:$2$]{$\bullet$};
   \node (Adots) at (6,0) {$\ldots$};
   \end{scope}
   \begin{scope}[color=red]
   \node (B) at (0,2) {$B$};
   \node(B0) at (2,2)[label=above:$0$]{$\bullet$};
   \node(B1) at (3,2)[label=above:$1$]{$\bullet$};
   \node(B2) at (4,2)[label=above:$2$]{$\bullet$};
   \node (Bdots) at (6,2) {$\ldots$};
   \node (b) at (8,2) [label=above:$\alpha$]{$\bullet$};
   \node (bsucc) at (9,2) [label=above:$\alpha+1$]{$\bullet$};
   \node (Bdots2) at (10,2) {$\ldots$};
   \end{scope}
   \begin{scope}[color=red!50!blue]
   \draw [->,thin] (A0) -- node [auto] {$\iota$} (B0);
   \draw [->,thin] (A1) -- node [auto] {$\iota$} (B1);
   \draw [->,thin] (A2) -- node [auto] {$\iota$} (B2);
   \draw [->,thin] (Adots) -- node [auto] {$\iota$} (Bdots);
   \end{scope}
   \end{tikzpicture}

If ``OB`` is presumed to be correct, then we may consider that ``OA``
“inherits” its correctness from the bigger notation system ``OB``.

:raw-latex:`\label{types:SubON}`
:raw-latex:`\index{hydras}{Library OrdinalNotations!Type classes!SubON}`

.. raw:: latex

   \begin{Coqsrc}
   Class  SubON 
          `(OA : @ON A ltA  compareA)
          `(OB : @ON B ltB  compareB)
          (alpha :  B)
          (iota : A -> B):=
     {
     SubON_compare: forall x y : A,  compareB (iota x) (iota y) =
                                    compareA x y;
     SubON_incl : forall x, ltB (iota x) alpha;
     SubON_onto : forall y, ltB y alpha  -> exists x:A, iota x = y}.
   \end{Coqsrc}

For instance, we prove that ``Omega`` is a sub-notation of
``Omega_plus_Omega`` (with :math:`\omega` as the first “new” ordinal,
and ``fin`` as the injection).

.. raw:: latex

   \begin{Coqsrc}
   Instance Incl : SubON Omega Omega_plus_Omega omega fin.
   \end{Coqsrc}

We can also show that, if :math:`i<j`, then the segment :math:`[0,i)` is
a “sub-segment” of :math:`[0,j)`. Since the terms (:math:`t\;i`) and
(:math:`t\;j`) are not convertible, we consider a “cast” function
:math:`\iota` from (:math:`t\;i`) into (:math:`t\;j`), and prove that
this function is a monotonous bijection from (:math:`t\;i`) to the
segment :math:`[0,i)` of (:math:`t\;j`).

:raw-latex:`\index{coq}{Commands!Program}`

We are now able to build an instance of ``SubON``.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`\ *From
Module *\ `OrdinalNotations.ON_Finite <../theories/html/hydras.OrdinalNotations.ON_Finite.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Section Inclusion_ij.

     Variables i j : nat.
     Hypothesis Hij : (i < j)%nat.

     Remark Ltb_ij : Nat.ltb i j.

     Program Definition iota_ij  (alpha: t i) : t j :=  alpha.
    
      Let b : t j := exist _ i Ltb_ij.
      
      Global Instance F_incl_ij  : SubON  (FinOrd i) (FinOrd j) b iota_ij.
     (* ... *)

     End Inclusion_ij.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove that \texttt{Omega\_plus\_Omega} cannot be a sub-notation of \texttt{Omega}.
   \end{exercise}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Adapt the definition of \texttt{Hvariant} (Sect.~\ref{sect:hvariant-def}) in order to
   have an ordinal notation as argument. Prove that if $O_A$ is a sub-notation of $O_B$, then any variant defined on  $O_A$ can be automatically transformed into 
   a variant on $O_B$.
   \end{project}

Comparing an ordinal notation with Schütte’s model
--------------------------------------------------

Finally, it may be interesting to compare an ordinal notation with the
more theoretical model from Schütte (well, at least with our
formalization of that model). This would be a relative proof of
correctness of the considered ordinal notation.

The following class specifies that a notation ``OA`` describes a segment
:math:`[0,\alpha)`, where :math:`\alpha` is a countable ordinal *à la*
Schütte.

:raw-latex:`\label{types:ON-for}`
:raw-latex:`\index{hydras}{Library OrdinalNotations!Type classes!ON\_correct}`

.. raw:: latex

   \begin{Coqsrc}
   Class ON_correct `(alpha : Schutte_basics.Ord)
        `(OA : @ON A ltA  compareA)
         (iota : A -> Schutte_basics.Ord) :=
     { ON_correct_inj : forall a, Schutte_basics.lt (iota a) alpha;
       ON_correct_onto : forall beta, Schutte_basics.lt beta alpha ->
                                   exists b, iota b = beta;
       On_compare_spec : forall a b:A,
           match compareA a b with
             Datatypes.Lt => Schutte_basics.lt (iota a) (iota b)
           | Datatypes.Eq => iota a = iota b
           | Datatypes.Gt => Schutte_basics.lt (iota b) (iota a)
           end
   }.
   \end{Coqsrc}

For instance, the following theorem tells that ``Epsilon0``, our
notation system for the segment :math:`[0,\epsilon0)` is a correct
implementation of the theoretically defined ordinal :math:`\epsilon_0`
(see chapter :raw-latex:`\ref{chap:schutte}` for more details).

.. raw:: latex

   \begin{Coqsrc}
   Instance Epsilon0_correct :
     ON_correct epsilon0 Epsilon0  (fun alpha => inject (cnf alpha)).
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
     When you have read Chapter~\ref{chap:schutte}, prove that the sum of two ordinal notations \texttt{ON\_plus} implements the addition of ordinals.
   \end{project}

Isomorphism of ordinal notations
--------------------------------

In some cases we want to show that two notation systems describe the
same segment (for instance :math:`[0,3+\omega)` and
:math:`[0,\omega)`\ :raw-latex:`\;`). For this purpose, one may prove
that the two notation systems are order-isomorphic.

:raw-latex:`\index{hydras}{Library OrdinalNotations!Type classes!ON\_Iso}`

:raw-latex:`\label{types:ON-iso}`

.. raw:: latex

   \begin{Coqsrc}
   Class  ON_Iso 
          `(OA : @ON A ltA compareA)
          `(OB : @ON B ltB  compareB)
          (f : A -> B)
          (g : B -> A):=
     {
     iso_compare: forall x y : A, 
         compareB (f x) (f y) = compareA x y;
     iso_inv1 : forall a, g (f a)= a;
     iso_inv2 : forall b, f (g b) = b
   }.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   \label{exo:i-plus-omega}
   Let $i$ be some natural number. Prove that the notation systems 
   \texttt{Omega} and (\texttt{ON\_plus (OrdFin $i$) Omega}) are isomorphic.

   {\it \textbf{Note:} This property reflects the equality $i+\omega=\omega$, that we prove also in larger notation systems, as well as in Schütte's model.}
   This exercise is partially solved for $i=3$ (in ~\href{../theories/html/hydras.OrdinalNotations.Example_3PlusOmega.html}{OrdinalNotations.Example\_3PlusOmega}).

   \end{exercise}

:raw-latex:`\index{hydras}{Projects}` :raw-latex:`\label{exo:ON-mult}`

.. raw:: latex

   \begin{project}
   % Define in \coq{} the product of two ordinal notations $N_A$ and $N_B$.
   % If $A$ [resp. $B$] is the underlying type of $N_A$ [resp. $N_B$], the
   % product \texttt{ON\_mult $N_A$ $N_B$} is implemented over the cartesian product $B\times A$ (with the lexicographic ordering).

   This exercise is about the non-commutativity of the multiplication of ordinals, reflected in ordinal notations.

   For instance, the
   elements of the product (\texttt{ON\_mult Omega (FinOrd 3)}) are ordered as follows.
   \[(0,0),(0,1),(0,2),(0,3),(0,4),\dots,{\color{red}(1,0),} (1,1),(1,2),\dots, {\color{red}(2,0)},(2,1),(2,2),\dots\]

   Note that the elements of  (\texttt{ON\_mult (FinOrd 3) Omega}) are differently ordered (without limit ordinals):
   \[(0,0),(1,0),(2,0),(0,1),(1,1),(2,1),(0,2),(1,2),(2,2),(0,3),\dots\]


   Prove formally  that \texttt{ON\_mult (FinOrd $i$) Omega} is isomorphic to
   \texttt{Omega}  whilst
   \texttt{Omega}  is a sub-notation of \texttt{ON\_mult Omega (FinOrd $i$)},
   for any strictly positive $i$. 

   \textbf{Note:} Like Exercise~\ref{exo:i-plus-omega}, this project corresponds to the [in]equalities $i+\omega=\omega<\omega+i$, for any natural number $i$.
   \end{project}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Consider two isomorphic ordinal notations \texttt{OA} and \texttt{OB}.
   Prove that, if \texttt{OA} [resp. \texttt{OB}] is a correct implementation 
   of $\alpha$ [resp. $\beta$], then $\alpha=\beta$.
   \end{project}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   \label{project:succ-limit-dec}
   Add to the class \texttt{ON} the requirement that for any $\alpha$ it is decidable whether $\alpha$ is $0$, a successor or a limit ordinal.


   \textbf{Hint:}   Beware of the instances associated with sum and product of notations!
     You may consider additional fields 
   to make the sum and product of notations ``compositional''.

   \end{project}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   \label{project:on-setoid}
   Reconsider the  class \texttt{ON}, with an equivalence instead of Leibniz equality.
   \end{project}

Other ordinal notations
-----------------------

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   The directory \texttt{theories/OmegaOmega} contains an ad-hoc formalization of $\omega^\omega$, contributed by Pascal Manoury. Every ordinal $\alpha$ is represented by a list $l$ whose elements are the coefficients of $\omega$ in  the Cantor normal form of $\alpha$ (in reverse order). For instance, the ordinal 
   $\omega^{8}\times 5 + \omega^{6}\times 8 + \omega^2\times 10 + \omega + 7$ is represented by the list \texttt{[5;0;8;0;0.0;10,1,7]}. 


    Develop this representation and compare it with the other ordinal notations.



   \end{project}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Let $N_A$ be a notation system for ordinals strictly less than $\alpha$, 
   with the strict order $(A,<_A)$. Please build the notation system
   \texttt{ON\_Expl $N_A$}, on the type of multisets of elements of $A$
   (or, if preferred, the type of non-increasing finite sequences on $A$,
   provided with the lexicographic ordering on lists).

   For instance, let us take $N_A=\texttt{Omega}$, and take $\alpha=\langle 4,4,2,1,0\rangle$,
    $\beta=\langle 4,3,3,3,3,3,2\rangle$, and $\gamma=\langle 5\rangle$. Then $\beta<\alpha<\gamma$. 

   In contrast the list $\langle5,6,3,3\rangle$ is not non-increasing (\emph{i.e.} sorted w.r.t. $\geq$), so it is not to be considered.

   Note that if the notation $N_A$ implements the ordinal 
   $\alpha$,  the new notation $\omega^{N_A}$ must implement the ordinal $\phi_0(\alpha)$, a.k.a. $\omega^\alpha$ (see chapter~\ref{chap:schutte})

   \end{project}

.. raw:: latex

   \begin{remark}
    The set of ordinal terms in Cantor normal form (see Chap.~\ref{chap:T1}) and 
   in Veblen normal form (see 
   \href{../theories/html/hydras.Gamma0.Gamma0.html}{Gamma0.Gamma0}) are shown to be ordinal notation systems, but there is a lot of work to be done in order to unify ad-hoc  definitions and proofs which were written before the definition of the \texttt{ON} type class.
   \end{remark}

.. _cnf-math-def:

A proof of termination, using ordinals below :math:`\epsilon_0`
===============================================================

:raw-latex:`\label{chap:T1}`

In this chapter, we adapt to :raw-latex:`\coq{}` the
well-known :raw-latex:`\cite{KP82}` proof that Hercules eventually wins
every battle, whichever the strategy of each player. In other words, we
present a formal and self contained proof of termination of all [free]
hydra battles. First, we take from Manolios and
Vroon :raw-latex:`\cite{Manolios2005}` a representation of the ordinal
:math:`\epsilon_0` as terms in Cantor normal form. Then, we define a
variant for hydra battles as a measure that maps any hydra to some
ordinal strictly less than :math:`\epsilon_0`.

.. _sec:epsilon0-intro:

The ordinal :math:`\epsilon_0`
------------------------------

Cantor normal form
~~~~~~~~~~~~~~~~~~

:raw-latex:`\index{maths}{Cantor normal form}`

The ordinal :math:`\epsilon_0` is the least ordinal number that
satisfies the equation :math:`\alpha = \omega^\alpha`, where
:math:`\omega` is the least infinite ordinal. Thus, we can consider
:math:`\epsilon_0` as an *infinite* :math:`\omega`-tower. Nevertheless,
any ordinal strictly less that :math:`\epsilon_0` can be finitely
represented by a unique *Cantor normal form*, that is, an expression
which is either the ordinal :math:`0` or a sum
:math:`\omega^{\alpha_1} \times n_1 + \omega^{\alpha_2} \times n_2 + 
  \dots + \omega^{\alpha_p} \times n_p` where all the :math:`\alpha_i`
are ordinals in Cantor normal form,
:math:`\alpha_1 > \alpha_2 > \alpha_p`, and all the :math:`n_i` are
positive integers.

An example of Cantor normal form is displayed in Fig
:raw-latex:`\ref{fig:cnf-example}`: Note that any ordinal of the form
:math:`\omega^0 \times i + 0` is just written :math:`i`.

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[scale=2, every node/.style={transform shape}]
   \node[color=blue]{$\omega^{(\omega^\omega\,+\, \omega^2 \times 8 \,+\, \omega)}+ \omega^\omega + \omega^4+ 6$};
   \end{tikzpicture}

In the rest of this section, we define an inductive type for
representing in ``Coq`` all the ordinals strictly less than
:math:`\epsilon_0`, then extend some arithmetic operations to this type,
and finally prove that our representation fits well with the expected
mathematical properties: the order we define is a well order, and the
decomposition into Cantor normal form is consistent with the
implementation of the arithmetic operations of exponentiation of base
:math:`\omega` and addition.

.. _sec:orgheadline65:

Remark
''''''

Unless explicitly mentionned, the term “ordinal" will be used instead of
“ordinal strictly less than :math:`\epsilon_0`" (except in
Chapter :raw-latex:`\ref{chap:schutte}` where it stands for “countable
ordinal”).

.. _sec:orgheadline72:

A data type for ordinals in Cantor normal form
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

:raw-latex:`\label{sec:T1-inductive-def}`

Let us define an inductive type whose constructors are respectively
associated with the ways to build Cantor normal forms:

-  the ordinal :math:`0`

-  the construction
   :math:`(\alpha,\, n,\,\beta)  \mapsto \omega^\alpha \times (n + 1)+ \beta \quad (n\in\mathbb{N})`

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`\ *From
Module *\ `Epsilon0.T1 <../theories/html/hydras.Epsilon0.T1.html#T1>`__

:raw-latex:`\label{types:T1}`
:raw-latex:`\index{hydras}{Library Epsilon0!Types!T1}`

.. raw:: latex

   \begin{Coqsrc}
   Inductive T1 : Set  :=
   | zero : T1
   | ocons : T1 -> nat -> T1 -> T1.
   \end{Coqsrc}

Remark
''''''

The name ``T1`` we gave to this data-type is proper to this development
and refers to a hierarchy of ordinal notations. For instance, in Library
`Gamma0.T2 <../theories/html/hydras.Gamma0.T2.html>`__, the following
type is used to represent ordinals strictly less than :math:`\Gamma_0`,
in Veblen normal form (see also :raw-latex:`\cite{schutte}`).
:raw-latex:`\noindent`

.. raw:: latex

   \begin{Coqsrc}
   Inductive T2 : Set :=
     zero : T2
   | gcons : T2 -> T2 -> nat -> T2 -> T2.
   \end{Coqsrc}

.. _alpha0-def:

Example
^^^^^^^

For instance, the ordinal :math:`\omega^\omega+\omega^3\times 5+2` is
represented by the following term:

.. raw:: latex

   \begin{Coqsrc}
   Example alpha_0 : T1 :=
     ocons (ocons (ocons zero 0 zero)
                  0
                  zero)
           0
          (ocons (ocons zero 2 zero)
                 4
                 (ocons zero 1 zero)).
   \end{Coqsrc}

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.5, level 1/.style={sibling distance=6cm},
   level 2/.style={sibling distance=35mm},  
   level 3/.style={sibling distance=17mm}]
   \node  {ocons}
     child {  node {ocons}
               child { node {ocons} child {node {zero}} child {node{0}} child{node{zero}}}
            child {node {0}}
            child {node {zero}}}
       child {node {0}}
      child {node {ocons} 
    child { node {ocons} child {node {zero}} child {node{2}} child{node{zero}}}
     child {node {4}}
            child {node {ocons} child {node {zero}} child {node{1}} child{node{zero}}}};

   \end{tikzpicture}

.. _remark-1:

Remark
''''''

For simplicity’s sake, we chosed to forbid expressions of the form
:math:`\omega^\alpha\times 0 + \beta`. Thus, the contruction
(``ocons \alpha n \beta``) is intented to represent the ordinal
:math:`\omega^\alpha\times(n+1)+\beta` and not
:math:`\omega^\alpha\times n+\beta`. In a future version, we should
replace the type ``nat`` with ``positive`` in ``T1``\ ’s definition. But
this replacement would take a lot of time …

.. _abbreviations-1:

Abbreviations
~~~~~~~~~~~~~

Some abbreviations may help to write more concisely complex ordinal
terms.

.. _sec:orgheadline67:

Finite ordinals
^^^^^^^^^^^^^^^

For representing finite ordinals, *i.e.* natural numbers, we first
introduce a notation for terms of the form :math:`n+1`, then define a
coercion from type ``nat`` into ``T1``.
:raw-latex:`\label{sect:notation-FS}`

.. raw:: latex

   \begin{Coqsrc}
   Notation "'FS' n" :=
        (ocons zero n zero) (at level 10) : t1_scope.
   \end{Coqsrc}

:raw-latex:`\label{sect:notation-F}`

.. raw:: latex

   \begin{Coqsrc}
   Definition fin (n:nat) : T1 := 
       match n with 0 => zero | S p => FS p end. 

   Coercion fin  : nat >-> T1.

   Example ten : T1 := 10.   
   \end{Coqsrc}

.. _sec:orgheadline68:

The ordinal :math:`\omega`
^^^^^^^^^^^^^^^^^^^^^^^^^^

Since :math:`\omega`\ ’s Cantor normal form is i.e.
:math:`\omega^{\omega^0}\times 1+ 0`, we can define the following
abbreviation:

:raw-latex:`\label{sect:omega-notation2}`

.. raw:: latex

   \begin{Coqsrc}
   Notation omega := (ocons (ocons zero 0 zero) 0 zero): t1_scope.
   \end{Coqsrc}

Note that ``omega`` is not an identifier, thus any tactic like
``unfold omega`` would fail.

.. _sect:notation-phi0:

The ordinal :math:`\omega^\alpha`, a.k.a. :math:`\phi_0(\alpha)`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We provide also a notation for ordinals of the form
:math:`\omega^\alpha`.

:raw-latex:`\index{hydras}{Library Epsilon0!Notations!phi0@phi0 (exponential of base omega)}`

.. raw:: latex

   \begin{Coqsrc}
   Notation "'phi0' alpha" := (ocons alpha 0 zero) (at level 29) : t1_scope.
   \end{Coqsrc}

:raw-latex:`\index{maths}{Additive principal ordinals}`

.. raw:: latex

   \begin{remark}
   \label{sec:orgheadline69}
   The name \(\phi_0\)
      comes from ordinal numbers theory. In~\cite{schutte}, Schütte defines 
   $\phi_0$  as the ordering (\emph{i.e.} enumerating) function of the set  of \emph{additive principal ordinals} \emph{i.e.} strictly positive ordinals $\alpha$ that verify $\forall \beta<\alpha, \beta+\alpha=\alpha$. For Schütte,  $\omega^\alpha$ is just a notation for $\phi_0(\alpha)$.  See also Chapter~\ref{chap:schutte} of this document.
   \end{remark}

.. _sec:orgheadline71:

The hierarchy of :math:`\omega`-towers:
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The ordinal :math:`\epsilon_0`, although not represented by a finite
term in Cantor normal form, is approximated by the sequence of
:math:`\omega`-towers (see also
Sect :raw-latex:`\vref{sect:epsilon0-as-limit}` ).

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Epsilon0.T1 <../theories/html/hydras.Epsilon0.T1.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint omega_tower (height:nat) : T1 := 
    match height with 
    | 0 =>  1 
    | S h => phi0 (omega_tower h)
    end.
   \end{Coqsrc}

For instance, Figure :raw-latex:`\ref{fig:tower7}` represents the
ordinal returned by the evaluation of the term ``omega_tower 7``.

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[scale=2, every node/.style={transform shape}]
   \node[color=blue]{$\omega^{{{\omega}^{{{\omega}}^{{{\omega}}^{{\omega^{{\omega}^{\omega}}}}}}}}$};
   \end{tikzpicture}

.. _sect:ppT1:

Pretty-printing ordinals in Cantor normal form
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

:raw-latex:`\index{hydras}{Library Epsilon0!Types!ppT1}`

Let us consider again the ordinal :math:`\alpha_0` defined in
section :raw-latex:`\vref{alpha0-def}` If we ask :raw-latex:`\coq{}` to
print its normal form, we get a hardly readable term of type ``T1``.

.. raw:: latex

   \begin{Coqsrc}
   Compute alpha_0.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
     = ocons omega 0 (ocons (FS 2) 4 (FS 1))
        : T1
   \end{Coqanswer}

The following data type defines an abstract syntax for more readable
ordinals terms in Cantor normal form:

:raw-latex:`\label{types:ppT1}`
:raw-latex:`\index{hydras}{Library Epsilon0!Functions!pp@ pp (pretty printing terms in Cantor normal form)}`

.. raw:: latex

   \begin{Coqsrc}
   Inductive ppT1 : Set :=
       P_fin : nat -> ppT1
     | P_add : ppT1 -> ppT1 -> ppT1
     | P_mult : ppT1 -> nat -> ppT1
     | P_exp : ppT1 -> ppT1 -> ppT1
     | P_omega : ppT1
   \end{Coqsrc}

The function ``pp: T1 -> ppT1`` converts any closed term of type ``T1``
into a human-readable expression. For instance, let us convert the term
``alpha_0``.

.. raw:: latex

   \begin{Coqsrc}
   Compute pp alpha_0.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
        = (omega ^ omega + omega ^ 3 * 5 + 2)%pT1
        : ppT1
   \end{Coqanswer}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Design  (in \ocaml?) a set of tools for systematically pretty printing ordinal terms in Cantor normal form.
   \end{project}

.. _sec:orgheadline73:

Comparison between ordinal terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In order to compare two terms of type ``T1``, we define a recursive
function ``compare`` that maps two ordinals :math:`\alpha` and
:math:`\beta` to a value of type ``comparison``. This type is defined in
:raw-latex:`\coq`’s standard library ``Init.Datatypes`` and contains
three constructors: ``Lt`` (less than), ``Eq`` (equal), and ``Gt``
(greater than).

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Epsilon0.T1 <../theories/html/hydras.Epsilon0.T1.html#compare>`__

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint compare (alpha alpha':T1):comparison :=
     match alpha, alpha' with
       zero, zero => Eq
     | zero, ocons a' n' b' => Lt
     | _   , zero => Gt
     | (ocons a n b),(ocons a' n' b') =>
         (match compare a a' with 
             | Lt => Lt
             | Gt => Gt
             | Eq => (match lt_eq_lt_dec n n'
                      with
                          inleft  (left _) => Lt
                        | inright _ => Gt
                        |   _ => compare b b'
                      end)
          end)
     end.
   \end{Coqsrc}

It is now easy to define the boolean predicate ``lt_b \alpha \beta``:
“:math:`\alpha` is strictly less than :math:`\beta`”. By coercion to
sort ``Prop`` we define also the predicate ``lt``.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Epsilon0.T1 <../theories/html/hydras.Epsilon0.T1.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Definition lt_b alpha beta : bool :=
     match compare alpha beta with
         Lt => true
       | _ => false
     end.

   Definition lt alpha beta : Prop := lt_b alpha beta.
   \end{Coqsrc}

:raw-latex:`\label{Predicates:lt-T1}` Please note that this definition
of ``lt`` makes it easy to write proofs by computation, as shown by the
following examples.

.. raw:: latex

   \begin{Coqsrc}
   Example E1 : lt (ocons omega 56 zero) (tower 3).
   Proof. reflexivity. Qed.

   Example E2 : ~ lt (tower 3) (tower 3).
   Proof.  discriminate.  Qed.
   \end{Coqsrc}

The following lemmas establish relations between ``compare``, the
predicate ``lt`` and Leibniz equality ``eq``.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Epsilon0.T1 <../theories/html/hydras.Epsilon0.T1.html#compare_refl>`__

.. raw:: latex

   \begin{Coqsrc}
   Lemma compare_refl : forall alpha, compare alpha alpha =  Eq.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma compare_reflect : forall alpha beta,
       match compare alpha beta with
       |   Lt => lt alpha  beta
       |   Eq => alpha = beta
       |   Gt => lt beta  alpha
       end.
   \end{Coqsrc}

We prove also that the relation ``lt`` is a strict total order.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Epsilon0.T1 <../theories/html/hydras.Epsilon0.T1.html#lt_irrefl>`__

.. raw:: latex

   \begin{Coqsrc}
   Theorem lt_irrefl (alpha: T1):  ~ lt alpha alpha.

   Theorem lt_trans (alpha beta gamma : T1) :
     lt alpha  beta -> lt beta gamma -> lt alpha gamma.

   Definition lt_eq_lt_dec  :
      forall alpha beta : T1, 
             {lt alpha  beta} + {alpha = beta} + {lt beta alpha}.
   \end{Coqsrc}

Note that the order ``lt`` is not reflected in the structure (size
and/or height) of the terms of ``T1``.

.. raw:: latex

   \begin{Coqsrc}
   Example Ex0:
     lt (ocons (phi0 (phi0 omega)) 2
               (ocons (phi0 10) 33
                      (ocons (phi0 9) 63 zero)))
        (ocons  (phi0 (phi0 omega)) 2 (phi0 (phi0 11))).
   Proof.
     reflexivity. 
   Qed.
   \end{Coqsrc}

.. _sect:t1-nf:

A Predicate for Characterizing Normal Forms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:raw-latex:`\label{sec:orgheadline74}`
:raw-latex:`\label{sec:orgheadline75}` Our data-type ``T1`` allows us to
write expressions that are not properly in Cantor normal form as
specified in Section :raw-latex:`\ref{sec:epsilon0-intro}`. For
instance, consider the following term of type ``T1``.

.. raw:: latex

   \begin{Coqbad}
   Example bad_term  : T1 := ocons 1 1 (ocons omega 2 zero).
   \end{Coqbad}

This term would have been written
:math:`\omega^1\times 2 + \omega^\omega \times 3` in the usual
mathematical notation. We note that the exponents of :math:`\omega` are
not in the right (strictly decreasing) order. Nevertheless, with the
help of the order ``lt`` on ``T1``, we are now able to characterize the
set of all well-formed ordinal terms:

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent` *From
Module *\ `Epsilon0.T1 <../theories/html/hydras.Epsilon0.T1.html#nf_b>`__

:raw-latex:`\label{Predicates:nf-T1}`

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint nf_b (alpha : T1) : bool :=
     match alpha with
       | zero => true
       | ocons a n zero => nf_b a
       | ocons a n ((ocons a' n' b') as b) =>
         (nf_b a && nf_b b && lt_b a' a)%bool
     end. 

   Definition nf alpha: Prop := nf_b alpha.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
    Compute nf_b alpha_0.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
      = true 
        : bool
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
    Compute nf_b bad_term.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
      = false 
        : bool
   \end{Coqanswer}

Making normality implicit
~~~~~~~~~~~~~~~~~~~~~~~~~

We would like to get rid of terms of type ``T1`` which are not in Cantor
normal form. A simple way to do this is to consider statements of the
form ``forall alpha: T1, nf alpha -> P alpha``, where :math:`P` is a
predicate over type ``T1``, like in the following lemma  [10]_.

.. raw:: latex

   \begin{Coqsrc}
   Lemma plus_is_zero alpha beta :
     nf alpha -> nf beta ->
     alpha + beta  = zero -> alpha = zero /\  beta = zero.
   \end{Coqsrc}

But this style leads to clumsy statements, and generates too many
sub-goals in interactive proofs (although often solved with ``auto`` or
``eauto``).

One may encapsulate conditions of the form ``(nf \alpha)`` in the most
used predicates. For instance, we introduce the restriction of ``lt`` to
terms in normal form, and provide a handy notation for this restriction.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `hydras.Prelude.Restriction <../theories/html/hydras.Prelude.Restriction.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Definition restrict {A:Type}(E: Ensemble A)(R: relation A) :=
       fun a b => E a /\ R a b /\ E b.
    \end{Coqsrc}

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Epsilon0.T1 <../theories/html/hydras.Epsilon0.T1.html#LT>`__

.. raw:: latex

   \begin{Coqsrc}
   Definition LT := restrict nf lt.
   Infix "t1<" := LT : t1_scope.

   Definition LE := restrict nf le.
   Infix "t1<=" := LE : t1_scope.
   \end{Coqsrc}

:raw-latex:`\label{Predicates:LT-T1}`

For instance, in the following lemma, the condition that :math:`\alpha`
is in normal form is included in the condition :math:`\alpha< 1`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma LT_one : forall alpha, alpha t1< one -> alpha = zero.
   \end{Coqsrc}

A sigma-type for :math:`\epsilon_0`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

As we noticed in Sect. :raw-latex:`\ref{sect:t1-nf}`, the type ``T1`` is
not a correct ordinal notation, since it contains terms that are not in
Cantor normal form. In certain contexts (for instance in
Sections :raw-latex:`\ref{sect:L-equations}`,
:raw-latex:`\ref{sect:hardy}`, and :raw-latex:`\ref{sect:wainer}`), we
need to define total recursive functions on well-formed ordinal terms
less than :math:`\epsilon_0`, using the ``Equations``
plug-in :raw-latex:`\cite{sozeau:hal-01671777}`. In order to define a
type whose inhabitants represent just ordinals, we build a type
gathering a term of type ``T1`` and a proof that this term is in normal
form.

:raw-latex:`\label{sect:E0-def}` :raw-latex:`\label{types:E0}`
:raw-latex:`\index{hydras}{Library Epsilon0!Types!E0}`

*From
Module *\ `Epsilon0.E0 <../theories/html/hydras.Epsilon0.E0.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Class E0 : Type := t1_2o {cnf : T1; cnf_ok : nf cnf}.
   \end{Coqsrc}

Many constructs : types, predicates, functions, notations, etc., on type
``T1`` are adapted to ``E0``.

First, we declare a notation scope for ``E0``.

.. raw:: latex

   \begin{Coqsrc}
   Declare Scope E0_scope.
   Delimit Scope E0_scope with e0.
   Open Scope E0_scope.
   \end{Coqsrc}

Then we redefine the predicates of comparison.

:raw-latex:`\label{Predicates:Lt-E0}`

.. raw:: latex

   \begin{Coqsrc}
   Definition Lt (alpha beta : E0) := T1.LT (@cnf alpha) (@cnf beta).
   Definition Le (alpha beta : E0) := T1.LE (@cnf alpha) (@cnf beta).

   Infix "o<" := Lt : E0_scope.
   Infix "o<=" := Le : E0_scope.
   \end{Coqsrc}

Equality in ``E0`` is just Leibniz equality. Note that, since ``nf`` is
defined by a Boolean function, for any term :math:`\alpha:\texttt{T1}`,
there exists at most one proof of ``nf \alpha``, thus two ordinals of
type ``E0`` are equal if and only iff their projection to ``T1`` are
equal (see also Sect. :raw-latex:`\vref{sect:eq-proof-unicity}`).

:raw-latex:`\index{coq}{Unicity of equality proofs}`

.. raw:: latex

   \begin{Coqsrc}
   Require Import Logic.Eqdep_dec.

   Lemma nf_proof_unicity :
     forall (alpha:T1) (H H': nf alpha), H = H'.

   Lemma E0_eq_iff alpha beta : alpha = beta <-> cnf alpha = cnf beta.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   In earlier versions of this development, the predicate \texttt{nf} was defined  inductively, with various constructors describing all possible cases.
   \begin{enumerate}
   \item Please give such a definition, in a dedicated module.
   \item Prove the logical equivalence between your definition and ours.
   \item Define a variant of the type \texttt{E0} (with your definition of \texttt{nf}).
   \item Can you still prove a lemma like \texttt{E0\_eq\_iff} ? With the help of an axiom from some module of the standard library ?
   \end{enumerate}
   \end{exercise}

In order to upgrade constants and fonctions from type ``T1`` to ``E0``,
we have to prove that the term they build is in normal form. For
instance, let us represent the ordinals :math:`0` and :math:`\omega` as
instances of the class ``E0``.

:raw-latex:`\label{sect:omega-T1}`

.. raw:: latex

   \begin{Coqsrc}
   Instance Zero : E0.
   Proof.
     now exists T1.zero.
   Defined.

   Instance _Omega : E0.
   Proof.  now exists omega%t1. 
   Defined.

   Notation "'omega'"  := _Omega : E0_scope.
   \end{Coqsrc}

Syntactic definition of limit and successor ordinals
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Pattern matching and structural recursion allow us to define boolean
characterizations of successor and limit ordinals.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent` *From
Module *\ `Epsilon0.T1 <../theories/html/hydras.Epsilon0.T1.html#succb>`__

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint succb (alpha:T1) : bool :=
     match alpha with
       | zero => false
       | ocons zero _ _ => true
       | ocons alpha n beta => succb beta
     end.

   Fixpoint limitb (alpha : T1) : bool :=
     match alpha with
       | zero => false
       | ocons zero _ _ => false
       | ocons alpha n zero => true
       | ocons alpha n beta => limitb beta
     end.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
     Compute limitb omega.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
     = true
        : bool
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Compute succb 42.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
     = true
        : bool
   \end{Coqanswer}

The correctness of these definitions with respect to the mathematical
notions of limit and successor ordinals is established through several
lemmas. For instance, Lemma ``canonS_limit``,
page :raw-latex:`\pageref{lemma:canonS-limit}`, shows that if
:math:`\alpha` is (syntactically) a limit ordinal, then it is the least
upper bound of a strictly increasing sequence of ordinals.

The following function is very useful in constructions by cases (proofs
and function definitions).

.. raw:: latex

   \begin{Coqsrc}
   Definition zero_succ_limit (alpha: T1) :
       {succb alpha} + {limitb alpha} +  {alpha=zero}.
       (* ... *)
   Defined.
   \end{Coqsrc}

Arithmetic on :math:`\epsilon_0`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _successor-1:

Successor
^^^^^^^^^

:raw-latex:`\index{hydras}{Library Epsilon0!Functions!succ}`

The successor of any ordinal :math:`\alpha< \epsilon_0` is defined by
structural recursion on its Cantor normal form.

:raw-latex:`\label{Functions:succ-T1}`

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Epsilon0.T1 <../theories/html/hydras.Epsilon0.T1.html#succ>`__

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint succ (alpha:T1) : T1 :=
     match alpha with 
      | zero => 1
      | ocons zero n _ => ocons zero (S n) zero
      | ocons beta n gamma => ocons beta n (succ gamma)
    end.
   \end{Coqsrc}

The following lemma establishes the connection between the function
``succ`` and the Boolean predicate ``succb``.

.. raw:: latex

   \begin{Coqsrc}
    Lemma succb_iff alpha (Halpha : nf alpha) :
     succb alpha <-> exists beta : T1, nf beta /\ alpha = succ  beta.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove in \coq{} that for any ordinal $0< \alpha<\epsilon_0$, $\alpha$ is a limit if 
   and only if for all $\beta<\alpha$, the interval $[\beta,\alpha)$ is
   infinite.

   \emph{You may start this exercise with the file
   \url{../exercises/ordinals/Limit_Infinity.v}.}
    \end{exercise}

Addition and multiplication
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Ordinal addition and multiplication are also defined by structural
recursion over the type ``T1``. Please note that they use the
``compare`` function on some subterms of their arguments.

:raw-latex:`\label{sect:infix-plus-T1}`

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint plus (alpha beta : T1) : T1 :=
     match alpha,beta with
    |  zero, y  => y
    |  x, zero  => x
    |  ocons a n b, ocons a' n' b' =>
       (match compare a a' with
        | Lt => ocons a' n' b'
        | Gt => (ocons a n (plus b (ocons a' n' b')))
        | Eq  => (ocons a (S(n+n')) b')
        end)
     end
   where "alpha + beta" := (plus alpha beta) : t1_scope.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint mult (alpha beta : T1) :T1 :=
     match alpha,beta with
    |  zero, y  => zero
    |  x, zero => zero
    |  ocons zero n _, ocons zero n' _ => 
                    ocons zero (Peano.pred((S n) * (S n'))) zero
    |  ocons a n b, ocons zero n' b' =>  
                    ocons a (Peano.pred((S n) * (S n'))) b
    |  ocons a n b, ocons a' n' b' =>
        ocons (a + a') n' ((ocons a n b) * b')
    end
   where  "alpha * beta" := (mult alpha beta) : t1_scope.
   \end{Coqsrc}

Examples
^^^^^^^^

The following examples are instances of *proofs by computation*. Please
note that addition and multiplication on ``T1`` are not commutative.
Moreover, both operations fail to be strictly monotonous in their first
argument.

.. raw:: latex

   \begin{Coqsrc}
   Example e2 : 6 + omega = omega.
   Proof. reflexivity. Qed.

   Example e'2 : omega t1< omega + 6.
   Proof. now compute. Qed.

   Example e''2 : 6 * omega = omega.
   Proof. reflexivity. Qed.

   Example e'''2 : omega t1< omega * 6.
   Proof. now compute. Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma plus_not_monotonous_l : exists alpha beta gamma : T1,
       alpha t1< beta /\ alpha + gamma = beta + gamma.
   Proof.
     exists 3, 5, omega;  now  compute.
   Qed.

   Lemma mult_not_monotonous :  exists alpha beta gamma : T1,
         alpha t1< beta /\ alpha * gamma = beta * gamma.
   Proof.
     exists 3, 5, omega; now compute.
   Qed.
   \end{Coqsrc}

The function ``succ`` is related with addition through the following
lemma:

.. raw:: latex

   \begin{Coqsrc}
   Lemma succ_is_plus_one (alpha : T1) :  succ alpha = alpha + 1.
   Proof.
     induction alpha as [|a IHa n b IHb].
     (* ... *)
   \end{Coqsrc}

Arithmetic on Type ``E0``
^^^^^^^^^^^^^^^^^^^^^^^^^

We define an addition in type ``E0``, since the sum of two terms in
normal form is in normal form too.

.. raw:: latex

   \begin{Coqsrc}
   Lemma plus_nf : forall a,  nf a -> forall b, nf b -> nf (a + b).
   Proof.
    (* ... *)

   Instance plus (alpha beta : E0) : E0.
   Proof.
     refine (@mkord (T1.plus (@cnf alpha) (@cnf beta))_ );
       apply plus_nf; apply cnf_ok.
   Defined.

   Infix "+" := plus : E0_scope.

   Check omega + omega.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   omega + omega
        : E0
   \end{Coqanswer}

.. raw:: latex

   \begin{remark}
   In all this development, two representations of ordinals co-exist: ordinal terms (type \texttt{T1}, notation scope \texttt{t1\_scope}, for reasoning on the tree-structure of Cantor normal forms), and ordinal terms \emph{known to be in normal form} (type \texttt{E0}, notation scope \texttt{E0\_scope}). Looking at the contexts displayed by \coq{} prevents you from any risk of confusion.
   \end{remark}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove that for any ordinal $\alpha:\texttt{E0}$, 
   $\omega\leq \alpha$ if and only if, for any natural number $i$,
   $i+\alpha=\alpha$.

   \emph{You may start this exercise with the file
   \url{../exercises/ordinals/ge_omega_iff.v}.}
   \end{exercise}

Well-foundedness and transfinite induction
------------------------------------------

:raw-latex:`\index{maths}{Transfinite induction}`

.. _sec:orgheadline82:

About well-foundedness
~~~~~~~~~~~~~~~~~~~~~~

In order to use ``T1`` for proving termination results, we need to prove
that our order ``<`` is well-founded. Then we will get *transfinite
induction* for free.

The proof of well-foundedness of the strict order :math:`<` on Cantor
normal forms is already available in the Cantor contribution by Castéran
and Contejean :raw-latex:`\cite{CantorContrib}`. That proof relies on a
library on recursive path orderings written by E. Contejean. We present
here a direct proof of the same result, which does not require any
knowledge on r.p.o.s.

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove that the \emph{total} order \texttt{lt} on \texttt{T1} is not well-founded. 
   \textbf{Hint:}  You will have to build a counter-example with terms of type \texttt{T1}
   which are not in Cantor normal form.

   \emph{You may start this exercise with the file
   \url{../exercises/ordinals/T1_ltNotWf.v}.}
   \end{exercise}

.. _sec:orgheadline77:

A first attempt
^^^^^^^^^^^^^^^

:raw-latex:`\index{coq}{Well-founded induction}`

It is natural to try to prove by structural induction over ``T1`` that
every term in normal form is accessible through ``LT``.

Unfortunately, it won’t work. Let us consider some well-formed term
:math:`\alpha=\texttt{ocons $\beta\;n\;\gamma$}`, and assume that
:math:`\beta` and :math:`\gamma` are accessible through ``LT``. For
proving the accessibility of :math:`\alpha`, we have to consider any
well formed term :math:`\delta` such that :math:`\delta<\alpha`. But
nothing guarantees that :math:`\delta` is strictly less than
:math:`\beta` nor :math:`\gamma`, and we cannot use the induction
hypotheses on :math:`\beta` nor :math:`\gamma`.

.. raw:: latex

   \begin{Coqbad}
   Section First_attempt.

    Lemma wf_LT : forall alpha,  nf alpha -> Acc LT alpha. 
    Proof.
     induction alpha as [| beta IHbeta n gamma IHgamma].
     - split.
       inversion 1.
       destruct H2 as [H3 _];not_neg H3.
     -  split; intros delta Hdelta.
   \end{Coqbad}

.. raw:: latex

   \begin{Coqanswer}
   1 subgoal (ID 560)
     
     beta : T1
     n : nat
     gamma : T1
     IHbeta : nf beta -> Acc LT beta
     IHgamma : nf gamma -> Acc LT gamma
     H : nf (ocons beta n gamma)
     delta : T1
     Hdelta : delta t1< ocons beta n gamma
     ============================
     Acc LT delta
    \end{Coqanswer}

.. raw:: latex

   \begin{Coqbad}
     Abort.
   \end{Coqbad}

The problem comes from the hypothesis ``Hdelta``. It does not prevent
:math:`\delta` to be bigger that :math:`\beta` or :math:`\gamma`; for
instance :math:`\delta` may be of the form ``ocons \beta' p' \gamma'``,
where :math:`\beta' \leq  \beta` and :math:`p' < n`. Thus, the induction
hypotheses ``IHbeta`` and ``IHgamma`` are useless for finishing our
proof.

.. _sec:orgheadline78:

Using a stronger inductive predicate.
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Instead of trying to prove directly that any ordinal term :math:`\alpha`
in normal form is accessible through ``LT``, we propose to show first
that any well formed term of the form
:math:`\omega^\alpha\times(n+1)+\beta` is accessible (which is a
stronger result).

.. raw:: latex

   \begin{Coqsrc}
    Let Acc_strong (alpha:T1) :=
         forall n beta, 
           nf (ocons alpha n beta) -> Acc LT (ocons alpha  n beta).
   \end{Coqsrc}

The following lemma is an application of the strict inequality
:raw-latex:`\showmath{\alpha < \omega ^\alpha}`. If
:raw-latex:`\showmath{\alpha}` is strongly accessible, then, by
definition, :raw-latex:`\showmath{\omega^\alpha}` is accessible, thus
:raw-latex:`\showmath{\alpha}` is *a fortiori* accessible.

.. raw:: latex

   \begin{Coqsrc}
    Lemma Acc_strong_stronger : forall alpha, 
        nf alpha -> Acc_strong  alpha -> Acc LT  alpha.
    Proof.
     intros alpha H H0; apply acc_imp with (phi0 alpha).
     - repeat split; trivial.
       + now apply lt_a_phi0_a.
     -  apply H0;  now apply single_nf.
   Qed.
   \end{Coqsrc}

Thus, it remains to prove that every ordinal strictly less than
:raw-latex:`\showmath{\epsilon_0}` is strongly accessible.

:raw-latex:`\label{sec:orgheadline81}`
:raw-latex:`\label{proof-wf-epsilon0}`

.. _sec:orgheadline79:

A helper
''''''''

First, we prove that, for any ``LT``-accessible term
:raw-latex:`\showmath{\alpha}`, :raw-latex:`\showmath{\alpha}` is
strongly accessible too (*i.e.* any well formed term
(``ocons \alpha n \beta``) is accessible).

.. raw:: latex

   \begin{Coqsrc}
   Lemma Acc_implies_Acc_strong : 
      forall alpha, Acc LT  alpha -> Acc_strong alpha.
   \end{Coqsrc}

The proof is structured as an induction on
:raw-latex:`\showmath{\alpha}`’s accessibility. Let us consider any
accessible term :math:`\alpha`.

.. raw:: latex

   \begin{Coqanswer}
     subgoal 1 

     alpha : T1
     Aalpha : forall y : T1,  y t1< alpha -> Acc LT y
     IHalpha : forall y : T1,
          LT y alpha ->
          forall (n : nat) (beta : T1),
          nf (ocons y n beta) -> Acc LT (ocons y n beta)
     ============================
      forall (n : nat) (beta : T1),
      nf (ocons alpha n beta) -> Acc LT (ocons alpha n beta)
   \end{Coqanswer}

Let ``n:nat`` and ``beta:T1`` such that (``ocons alpha n beta``) is in
normal form. We prove first that ``beta`` is accessible, which allows us
to prove by well-founded induction on ``beta``, and natural induction on
``n``, that (``ocons alpha n beta``) is accessible. The proof, quite
long, can be consulted in
`Epsilon0.T1 <../theories/html/hydras.Epsilon0.T1.html>`__.

.. _sec:orgheadline80:

Accessibility of any well-formed ordinal term
'''''''''''''''''''''''''''''''''''''''''''''

Our goal is still to prove accessibility of any well formed ordinal
term. Thanks to our previous lemmas, we are almost done.

.. raw:: latex

   \begin{Coqsrc}
   (* A (last) structural induction *)

   Theorem nf_Acc : forall alpha, nf alpha -> Acc LT  alpha.
   Proof.
    induction alpha.
   -  intro; apply Acc_zero.
    -  intros; eapply Acc_implies_Acc_strong;auto.
       apply IHalpha1;eauto.
       apply nf_inv1 in H; auto. 
   Defined.

   Corollary T1_wf : well_founded LT.
   \end{Coqsrc}

:raw-latex:`\index{maths}{Transfinite induction}`

.. raw:: latex

   \begin{Coqsrc}

   Definition transfinite_recursor :
    forall (P:T1 -> Type),
      (forall x:T1, 
        (forall y:T1, nf x -> nf y ->  lt y  x -> P y) -> P x) ->
       forall alpha:T1, P alpha.
   Proof.
    intros; apply well_founded_induction_type with LT.
    -  exact T1_wf;auto.
    - intros. apply X. intros; apply X0. repeat split;auto. 
   Defined.
   \end{Coqsrc}

The following tactic starts a proof by transfinite induction on any
ordinal :raw-latex:`\mathcolor{$\alpha<\epsilon_0$}`.

.. raw:: latex

   \begin{Coqsrc}
   Ltac transfinite_induction alpha :=
     pattern alpha; apply transfinite_recursor;[ | try assumption].
   \end{Coqsrc}

.. raw:: latex

   \begin{remark}
   \label{remark:a3pat}
   The alternate proof of well-foundedness using \'Evelyne Contejean's work on recursive path ordering~\cite{DershowitzRPO, a3pat} is available in the library \href{../theories/html/hydras.Epsilon0.Epsilon0rpo.html}{Epsilon0rpo}.
    \end{remark}

An ordinal notation for :math:`\epsilon_0`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We build an instance of ``ON``, and prove its correction w.r.t.
Schutte’s model.

:raw-latex:`\label{instance-epsilon0}`

.. raw:: latex

   \begin{Coqsrc}
   Instance Epsilon0 : ON Lt compare.  
   (* ... *)
   \end{Coqsrc}

*From
Module *\ `Schutte.Schutte.Correctness_E0 <../theories/html/hydras.Schutte.Schutte.Correctness_E0.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Instance Epsilon0_correct :
     ON_correct epsilon0 Epsilon0 (fun alpha => inject (cnf alpha)).
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
    \emph{This exercise is a continuation of Project~\vref{exo:ON-mult}.}
   Use \texttt{ON\_mult} to define an ordinal notation \texttt{Omega2} for $\omega^2=\omega\times\omega$.

   Prove that \texttt{Omega2} is a sub-notation of \texttt{Epsilon0}.

   Define on \texttt{Omega2} an addition compatible with the addition on \texttt{Epsilon0}.

   \textbf{Hint}. You may use the following definition (in 
   \href{../theories/html/hydras.OrdinalNotations.Definitions.html}{OrdinalNotations.Definitions}).

   \begin{Coqsrc}
   Definition SubON_same_op  `{OA : @ON A ltA  compareA}
          `{OB : @ON B ltB  compareB}
          {iota : A -> B} 
          {alpha: B}
          {_ : SubON OA OB alpha iota}
          (f : A -> A -> A)
          (g : B -> B -> B)
     :=
     forall x y,  iota (f x y) = g (iota x) (iota y).
   \end{Coqsrc}

   \end{project}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   The class \texttt{ON} of ordinal notations has been defined long after this 
   chapter, and is not used yet in the development of the type \texttt{E0}. 
   A better integration of both notions should simplify the development on ordinals in Cantor normal form. This integration is planned for the future versions.

   \end{project}

A Variant for hydra battles
---------------------------

In order to prove the termination of any hydra battle, we try to define
a variant mapping hydras to ordinals strictly less than
:math:`\epsilon_0`. In order to make such a variant easy to define (for
instance by a structural recursion), we introduce a variant of addition,
which, contrary to :math:`+`, is commutative and strictly monotonous in
both of its arguments. This last property makes it possible to prove
that our function is truly a variant for hydra battles (in
Sect. :raw-latex:`\vref{sect:variant-decr}`).

.. _sec:orgheadline87:

Natural sum (a.k.a. Hessenberg’s sum)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

:raw-latex:`\label{hydra-variant}`

Natural sum (Hessenberg’s sum) is a commutative and monotonous version
of addition. It is used as an auxiliary operation for defining variants
for hydra battles, where Hercules is allowed to chop off any head of the
hydra.

In the litterature, the natural sum of ordinals :math:`\alpha` and
:math:`\beta` is often denoted by :math:`\alpha \# \beta` or
:math:`\alpha \oplus  \beta`. Thus we called ``oplus`` the associated
*Coq* function.

.. _sec:orgheadline84:

Definition of ``oplus``
^^^^^^^^^^^^^^^^^^^^^^^

The definition of ``oplus`` is recursive in both of its arguments and
uses the same pattern as for the ``merge`` function on lists of library
``Coq.Sorting.Mergesort``.

#. Define a nested recursive function, using the ``Fix`` construct

#. Build a principle of induction dedicated to ``oplus``

#. Establish equations associated to each case of the definition.

.. _sec:orgheadline83:

Nested recursive definition
'''''''''''''''''''''''''''

The following definition is composed of

-  A main function ``oplus``, structurally recursive in its first
   argument ``alpha``

-  An auxiliary function ``oplus_aux`` within the scope of ``alpha``,
   structurally recursive in its argument ``beta``; ``oplus_aux beta``
   is supposed to compute ``oplus alpha beta``.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Epsilon0.Hessenberg <../theories/html/hydras.Epsilon0.Hessenberg.html#oplus>`__

:raw-latex:`\label{sect:infix-oplus}`

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint oplus (alpha beta : T1) : T1 :=
     let fix oplus_aux beta {struct beta} :=
         match alpha, beta with
           | zero, _ => beta
           | _,  zero => alpha
           | ocons a1 n1 b1, ocons a2 n2 b2 =>
             match compare a1 a2 with
               |  Gt => ocons a1 n1 (oplus b1 beta)
               |  Lt => ocons a2 n2 (oplus_aux b2)
               |  Eq => ocons a1 (S (n1 + n2)%nat) (oplus b1 b2)
             end
         end
     in oplus_aux beta.

   Infix "o+" := oplus  (at level 50, left associativity).
   \end{Coqsrc}

The reader will note that each recursive call of the functions ``oplus``
and ``oplus_aux`` satisfies *Coq*\ ’s constraint on recursive
definitions. The function ``oplus`` is recursively called on a sub-term
of its first argument, and ``oplus_aux`` on a sub-term of its unique
argument. Thus, ``oplus``\ ’s definition is accepted by
:raw-latex:`\coq{}` as a structurally recursive function.

.. _sec:orgheadline86:

Rewriting lemmas
^^^^^^^^^^^^^^^^

*Coq*\ ’s constraints on recursive definitions result in the quite
complex form of ``oplus``\ ’s definition. Proofs of properties of this
function can be simpler if we derive a few rewriting lemmas that will
help to simplify expressions of the form (``oplus \alpha \beta``).

A first set of lemmas correspond to the various cases of ``oplus``\ ’s
definition. They can be proved almost immediately.

.. raw:: latex

   \begin{Coqsrc}
   Lemma oplus_alpha_0 (alpha : T1) : alpha o+ zero = alpha.
   Proof.
     destruct alpha; reflexivity.
   Qed.

   Lemma oplus_0_beta (beta : T1): zero o+ beta = beta.
   Proof.
     destruct beta; reflexivity.
   Qed.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Compare \texttt{oplus}'s definition (with inner fixpoint) with other possibilities
   (\texttt{coq-equations}, \texttt{Function}, etc.).
   \end{project}

More theorems on Hessenberg’s sum
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We need to prove some properties of :math:`\oplus`, particularly about
its relation with the order :math:`<` on ``T1``.

Boundedness
^^^^^^^^^^^

If :math:`\alpha` and :math:`\beta` are both strictly less than
:math:`\omega^\gamma`, then so is their natural sum
:math:`\alpha \oplus \beta`. This result can be proved by structural
induction on :math:`\gamma`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma oplus_bounded_phi0 alpha beta gamma :
     nf alpha -> nf beta -> nf gamma ->
     lt alpha (phi0 gamma) ->
     lt beta (phi0 gamma) ->
     lt (alpha o+ beta) (phi0 gamma).
   \end{Coqsrc}

This lemma helps us

Commutativity, associativity
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We prove the commutativity of :math:`\oplus` in two steps.

First, we prove by transfinite induction on :math:`\alpha` that the
restriction of :math:`\oplus` to the interval :math:`[0..\alpha)` is
commutative.

:raw-latex:`\index{maths}{Transfinite induction}`

.. raw:: latex

   \begin{Coqsrc}
   Lemma oplus_comm_0 : forall alpha, nf alpha ->
        forall a b,  nf a -> nf b ->
                     lt a alpha ->
                     lt b alpha ->
                     a o+ b = b o+ a.
    Proof with eauto with T1.
       intros alpha Halpha; transfinite_induction alpha.
   (* rest of proof omitted *)  
   \end{Coqsrc}

Then, we infer :math:`\oplus`\ ’s commutativity for any pair of
ordinals: Let :math:`\alpha` and :math:`\beta` be two ordinals strictly
less than :math:`\epsilon_0`. Both ordinals :math:`\alpha` and
:math:`\beta` are strictly less than
:math:`\textrm{max}(\alpha,\beta)+1`. Thus, we have just to apply the
lemma :raw-latex:`\coqsimple{oplus\_comm\_0}`.

.. raw:: latex

   \begin{Coqsrc}
     Lemma oplus_comm : forall alpha beta, 
         nf alpha -> nf beta ->
         alpha o+ beta =  beta o+ alpha.
     Proof with eauto with T1.
       intros alpha beta Halpha Hbeta;
       apply oplus_comm_0 with (succ (max alpha beta)) ...  
     (* ... *)
   \end{Coqsrc}

The associativity of Hessenberg’s sum is proved the same way.

.. raw:: latex

   \begin{Coqsrc}
    Lemma oplus_assoc_0 :
       forall alpha,
         nf alpha ->
         forall a b c,  nf a -> nf b -> nf c ->
                         lt a alpha ->
                         lt b alpha -> lt c alpha ->
                         a o+ (b o+ c) = (a o+ b) o+ c.
     Proof with eauto with T1.
       intros alpha Halpha.
       transfinite_induction alpha.
       (* ... *)
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
    Lemma oplus_assoc : forall alpha beta gamma,
                           nf alpha -> nf beta -> nf gamma ->
                                       alpha o+ (beta o+ gamma) =
                                       alpha o+ beta o+ gamma.
    Proof with eauto with T1.
       intros;
       apply oplus_assoc_0 with (succ (max alpha (max beta gamma))) ...
       (* ... *)   
   \end{Coqsrc}

Monotonicity
^^^^^^^^^^^^

At last, we prove that :math:`\oplus` is strictly monotonous in both of
its arguments.

.. raw:: latex

   \begin{Coqsrc}
   Lemma oplus_strict_mono_LT_l (alpha beta gamma : T1) :
     nf gamma   -> alpha  t1< beta ->
     alpha o+ gamma  t1< beta o+ gamma.

   Lemma oplus_strict_mono_LT_r (alpha beta gamma : T1) :
     nf alpha -> beta t1< gamma ->
     alpha o+ beta t1< alpha o+ gamma.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   The library \texttt{Hessenberg} looks too long (proof scripts and compilation).
   Please try to make it simpler and more efficient!
   Thanks!
   \end{project}

.. _sec:hydra-measure:

A termination measure for hydra battles 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Let us define a measure from type ``Hydra`` into ``T1``.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Hydra_Termination <../theories/html/hydras.Hydra.Hydra_Termination.html#m>`__

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint m (h:Hydra) : T1 :=
     match h with head => zero
                | node hs => ms hs
   end 
   with ms (s:Hydrae) :  T1 :=
     match s with  hnil => zero
                 | hcons h s' => phi0 (m h) o+  ms s'
    end.  
   \end{Coqsrc}

First, we prove that the measure :math:`m(h)` of any hydra :math:`h` is
a well-formed ordinal term of type ``T1``.

.. raw:: latex

   \begin{Coqsrc}
   Lemma m_nf : forall h, nf (m h).
   Proof.
    intro h; elim h using Hydra_rect2 
               with (P0 := fun s =>  nf (ms s)).
    (* ... *)

   Lemma ms_nf : forall s, nf (ms s).
   Proof with auto with T1.
   (* ... *)
   \end{Coqsrc}

For proving the termination of all hydra battles, we have to prove that
``m`` is a variant. First, a few technical lemmas follow the
decomposition of ``round`` into several relations. Then the lemma
``round_decr`` gathers all the cases.

:raw-latex:`\label{sect:variant-decr}`

.. raw:: latex

   \begin{Coqsrc}
   Lemma S0_decr :
     forall s s', S0  s s' -> ms s' t1< ms s.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma R1_decr : forall h h',
                     R1 h h' -> m h' t1< m h.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma S1_decr n:
     forall s s', S1 n s s' -> ms s' t1<  ms s.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma R2_decr n : forall h h', R2 n h h' -> m h'  t1< m h.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma round_decr : forall h h', h -1-> h' -> m h' t1< m h.
   Proof.
      destruct 1 as [n [H | H]].
      -  now apply R1_decr.
      -  now apply R2_decr with n.
   Qed.
   \end{Coqsrc}

Finally, we prove the termination of all (free) battles.

:raw-latex:`\label{thm:every-battle-terminates}`

.. raw:: latex

   \begin{Coqsrc}
   Global Instance HVariant : Hvariant lt_wf free var.
   Proof.
    split; intros; eapply round_decr; eauto.
   Qed.

   Theorem every_battle_terminates: Termination.
   Proof. 
     red; apply Inclusion.wf_incl with 
            (R2 := fun h h' =>  m h t1< m h').
      red; intros;  now apply round_decr.
      apply Inverse_Image.wf_inverse_image, T1_wf.
   Qed.
   \end{Coqsrc}

.. _conclusion-1:

Conclusion
----------

Let us recall three results we have proved so far.

-  There exists a strictly decreasing variant which maps ``Hydra`` into
   the segment :math:`[0,\epsilon_0)` for proving the termination of any
   hydra battle

-  There exists *no* such variant from ``Hydra`` into
   :math:`[0,\omega^2)`, *a fortiori* into :math:`[0,\omega)`.

So, a natural question is “Does there exist any strictly decreasing
variant mapping type ``Hydra`` into some interval :math:`[0,\alpha[`
(where :math:`\alpha <\epsilon_0`) for proving the termination of all
hydra battles”. The next chapter is dedicated to a formal proof that
there exists no such :math:`\alpha`, even if we consider a restriction
to the set of “standard” battles.

.. _chap:ketonen:

Accessibility inside :math:`\epsilon_0`: The Ketonen-Solovay Machinery:raw-latex:`\label{ks-chapter}`
=====================================================================================================

:raw-latex:`\index{maths}{Ordinal numbers!Ketonen-Solovay machinery}`

.. _introduction-1:

Introduction
------------

The reader may think that our proof of termination in the previous
chapter requires a lot of mathematical tools and may be too complex. So,
the question is “is there any simpler proof” ?

In their article :raw-latex:`\cite{KP82}`, Kirby and Paris show that
this result cannot be proved in Peano arithmetic. Their proof uses some
knowledge about model theory and non-standard models of Peano
arithmetic. In this chapter, we focus on a specific class of proofs of
termination of hydra battles: construction of some variant mapping the
type ``Hydra`` into a given initial segment of ordinals. Our proof
relies only on the Calculus of Inductive Constructions and is a natural
complement of the results proven in the previous chapters.

-  There is no variant mapping the type ``Hydra`` into the interval
   :math:`[0,\omega^2)` (section  :raw-latex:`\vref{omega2-case}`), and
   a fortiori :math:`[0,\omega)` (section
    :raw-latex:`\vref{omega-case}`).

-  There exists a variant which maps the type ``Hydra`` into the
   interval :math:`[0,\epsilon_0)` (theorem ``every_battle_terminates``,
   in section :raw-latex:`\vref{thm:every-battle-terminates}`).

Thus, a very natural question is the following one:

   “Is there any variant from ``Hydra`` into some interval
   :math:`[0,\mu)`, where :math:`\mu<\epsilon_0`, for proving the
   termination of all hydra battles ?”

We prove in :raw-latex:`\coq{}` the following result:

   There is no variant for proving the termination of all hydra battles
   from ``Hydra`` into the interval :math:`[0..\mu)`, where
   :math:`\mu< \epsilon_0`. The same impossibility holds even if we
   consider only standard battles (with the successive replication
   factors :math:`0,1,2,\dots,t,t+1,\dots`).

Our proofs are constructive and require no axioms: they are closed terms
of the CIC, and are mainly composed on function definitions and proofs
of properties of these functions. They share much theoretical material
with Kirby and Paris’, although they do not use any knowledge about
Peano arithmetic nor model theory. The combinatorial arguments we use
and implement come from an article by J. Ketonen and
R. Solovay :raw-latex:`\cite{KS81}`, already cited in the work by
L. Kirby et J. Paris. Section :math:`2` of this article: ”A hierarchy of
probably recursive functions”, contains a systematic study of *canonical
sequences*, which are closely related to rounds of hydra battles.
Nevertheless, they have the same global structure as the simple proofs
described in sections :raw-latex:`\vref{omega-case}` and
:raw-latex:`\vref{omega2-case}`. We invite the reader to compare the
three proofs step by step, lemma by lemma.

.. _ketonen-solovay-sect:

Canonical Sequences
-------------------

:raw-latex:`\index{maths}{Ordinal numbers!Canonical sequences}`

Canonical sequences are functions that associate an ordinal
:math:`\canonseq{\alpha}{i}` to every ordinal :math:`\alpha<\epsilon_0`
and positive integer :math:`i`. They satisfy several nice properties:

:raw-latex:`\index{maths}{Transfinite induction}`

-  If :math:`\alpha\not=0`, then :math:`\canonseq{\alpha}{i}<\alpha`.
   Thus canonical sequences can be used for proofs by transfinite
   induction or function definition by transfinite recursion

-  If :math:`\lambda` is a limit ordinal, then :math:`\lambda` is the
   least upper bound of the set
   :math:`\{\canonseq{\lambda}{i}\;|\,i\in\mathbb{N}_1\}`

-  If :math:`\beta<\alpha<\epsilon_0`, then there is a “path” from
   :math:`\alpha` to :math:`\beta`, *i.e.* a sequence
   :math:`\alpha_0=\alpha, \alpha_1, \dots, \alpha_n=\beta`, where for
   every :math:`k<n`, there exists some :math:`i_k` such that
   :math:`\alpha_{k+1}=\canonseq{\alpha_k}{i_k}`

-  Canonical sequences correspond tightly to rounds of hydra battles: if
   :math:`\alpha\not=0`, then :math:`\iota(\alpha)` is transformed into
   :math:`\iota(\canonseq{\alpha}{i+1})` in one round with the
   replication factor :math:`i` (Lemma
   `Hydra.O2H.canonS_iota_i <../theories/html/hydras.Hydra.O2H.html#canonS_iota_i>`__).

-  From the two previous properties, we infer that whenever
   :math:`\beta<\alpha<\epsilon_0`, there exists a (free) battle from
   :math:`\iota(\alpha)` to :math:`\iota(\beta)`.

.. raw:: latex

   \begin{remark}
     In~\cite{KS81}, canonical sequences are defined for any ordinal $\alpha <\epsilon_0$,
   by stating that if $\alpha$ is a successor ordinal $\beta+1$,  the sequence associated with 
   $\alpha$ is simply the constant sequence whose terms are equal to $\beta$.
   Likewise, the canonical sequence of $0$ maps any natural number to $0$.

   This convention allows us to make total the function that maps any ordinal $\alpha$ and natural number $i$ to the ordinal $\canonseq{\alpha}{i}$.

   \end{remark}

First, let us recall how canonical sequences are defined
in :raw-latex:`\cite{KS81}`. For efficiency’s sake, we decided not to
implement directly K.&S’s definitions, but to define in
:raw-latex:`\gallina{}` simply typed structurally recursive functions
which share the abstract properties which are used in the mathematical
proofs [11]_.

Mathematical definition of canonical sequences
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In :raw-latex:`\cite{KS81}` the definition of
:math:`\canonseq{\alpha}{i}` is based on the following remark:

   Any non-zero ordinal :math:`\alpha` can be decomposed in a unique way
   as the product :math:`\omega^\beta\times (\gamma+1)`.

Thus the :math:`\canonseq{\alpha}{i}` s are defined in terms of this
decomposition:

.. raw:: latex

   \begin{definition}[Canonical sequences: mathematical definition]\label{def:canonseq-math}
     
   \end{definition}

.. raw:: latex

   \begin{mathframe}
     \begin{itemize}
   \item Let $\lambda<\epsilon_0$ be a limit ordinal 

   \begin{itemize}
   \item If $\lambda=\omega^{\alpha+1}\times (\beta+1)$, then 
   $\canonseq{\lambda}{i}= \omega^{\alpha+1}\times\beta +  \omega^\alpha \times i$
   \item If $\lambda=\omega^{\gamma}\times (\beta+1)$, where $\gamma<\lambda$ is a limit ordinal, then 
   $\canonseq{\lambda}{i}=\omega^{\gamma}\times \beta + \omega^{\canonseq{\gamma}{i}}$
   \end{itemize}

   \item For successor ordinals, we have $\canonseq{\alpha+1}{i}= \alpha$ 

   \item Finally, $\canonseq{0}{i}= \alpha$.
   \end{itemize}
   \end{mathframe}

Canonical sequences in Coq
^^^^^^^^^^^^^^^^^^^^^^^^^^

:raw-latex:`\index{hydras}{Library Epsilon0!Functions!canon}`
:raw-latex:`\index{hydras}{Library Epsilon0!Functions!canonS}`

Our definition may look more complex than the mathematical one, but uses
plain structural recursion over the type :raw-latex:`\coqsimple{T1}`.
Thus, tactics like :raw-latex:`\coqsimple{cbn}`,
:raw-latex:`\coqsimple{simpl}`, :raw-latex:`\coqsimple{compute}`, etc.,
are applicable. For simplicity’s sake, we use an auxiliary function
``canonS`` of type ``T1 -> nat -> T1`` such that (``canonS \alpha i``)
is equal to :math:`\canonseq{\alpha}{i+1}`.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Epsilon0.Canon <../theories/html/hydras.Epsilon0.Canon.html#canonS>`__

:raw-latex:`\label{Functions:canonS}`
:raw-latex:`\label{Functions:canon}`

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint canonS alpha (i:nat) :=
     match alpha with
         zero => zero
       | ocons zero 0 zero => zero
       | ocons zero (S k) zero => FS k
       | ocons gamma 0 zero =>
         match pred gamma with
             Some gamma' => ocons gamma' i zero
           | None => ocons (canonS gamma i) 0 zero
         end
       | ocons gamma (S n) zero =>
          match pred gamma with
              Some gamma' => ocons gamma n (ocons gamma' i zero)
            | None => ocons gamma n (ocons (canonS gamma i) 0 zero)
          end
       | ocons alpha n beta => ocons alpha n (canonS beta i)
     end.
   \end{Coqsrc}

The following function computes :math:`\canonseq{\alpha}{i}`, except for
the case :math:`i=0`, where it simply returns
:math:`0`\ :raw-latex:`\;` [12]_.

.. raw:: latex

   \begin{Coqsrc}
    Definition canon alpha i := 
      match i with 0 => zero | S j => canonS alpha j end. 
   \end{Coqsrc}

For instance :raw-latex:`\coq`’s computing facilities allow us to verify
the equalities:raw-latex:`\linebreak `
:raw-latex:`\mathcolor{$\canonseq{\omega^\omega}{3} = \omega^3$}` and
:raw-latex:`\mathcolor{$\canonseq{\omega^\omega*3}{42} = \omega^\omega*2 + \omega^{42}$}`.

.. raw:: latex

   \begin{Coqsrc}
   Compute (canon (omega ^ omega) 3).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
     = phi0 (FS 2) : T1
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Example canon3 :  canon (omega ^ omega) 3 = omega ^ 3.
   Proof. reflexivity. Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Compute pp (canon (omega ^ omega * 3) 42).  
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
       = (omega ^ omega * 2 + omega ^ 42)%pT1
        : ppT1
   \end{Coqanswer}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Many lemmas presented in this chapter were stated and proved before the introduction of 
   the type class \texttt{ON} of ordinal notations, and in particular its  instance \texttt{Epsilon0}.
   Thus definitions and lemmas refer to the type \texttt{T1} of possibly not well-formed terms.
   This should be fixed in  a future version.
   \end{project}

Basic properties of canonical sequences
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We did not try to prove that our definition truly implements Ketonen and
Solovay’s :raw-latex:`\cite{KS81}`’s canonical sequences. The most
important is that we were able to prove the abstract properties of
canonical sequences that are really used in our proof. The complete
proofs are in the module
 `Epsilon0.Canon <../theories/html/hydras.Epsilon0.Canon.html>`__

Proving the equality :math:`\canonseq{\alpha+1}{i}=\alpha` is not as
simple as suggested by the equations of
definition :raw-latex:`\ref{def:canonseq-math}` . Nevertheless, we can
prove it by plain structural induction on :math:`\alpha`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma canonS_succ i alpha :
     nf alpha ->  canonS (succ alpha) i = alpha.
   Proof.
    induction alpha.
    (* ... *)
   \end{Coqsrc}

Canonical sequences and the order :math:`<`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:raw-latex:`\index{maths}{Transfinite induction}`

We prove by transfinite induction over :math:`\alpha` that
:math:`\canonseq{\alpha}{i+1}` is an ordinal strictly less than
:math:`\alpha` (assuming :math:`\alpha\not=0`). This property allows us
to use the function ``canonS`` and its derivates in function definitions
by transfinite recursion.

:raw-latex:`\label{lemma:canonS_LT}`

.. raw:: latex

   \begin{Coqsrc}
   Lemma canonS_LT i alpha :
     nf alpha -> alpha <> zero -> canonS alpha i t1<  alpha.
   \end{Coqsrc}

Limit ordinals are truly limits
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following theorem states that any limit ordinal
:math:`\lambda<\epsilon_0` is the limit of the sequence
:raw-latex:`\showmath{\canonseq{\lambda}{i}\;(1\le i)}`.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Epsilon0.Canon <../theories/html/hydras.Epsilon0.Canon.html#canonS_limit_strong>`__

.. raw:: latex

   \begin{Coqsrc}
   Lemma canonS_limit_strong (lambda : T1) : 
        nf lambda ->
        limitb lambda  ->
        forall beta, beta t1< lambda ->
                     {i:nat | beta t1< canonS lambda i}.

   Proof.
     transfinite_induction_LT lambda.
     (* ... *)
   Defined.
   \end{Coqsrc}

:raw-latex:`\label{lemma:canonS-limit}`

Note the use of :raw-latex:`\coq`’s ``sig`` type in the theorem’s
statement, which relates the boolean function ``limitb`` defined on the
``T1`` data-type with a constructive view of the limit of a sequence:
for any :math:`\beta<\lambda`, we can compute an item of the canonical
sequence of :math:`\lambda` which is greater than :math:`\beta`. We can
also state directly that :math:`\lambda` is a (strict) least upper bound
of the elements of its canonical sequence.

.. raw:: latex

   \begin{Coqsrc}
   Lemma canonS_limit_lub (lambda : T1) :
     nf lambda -> limitb lambda  ->
     strict_lub (canonS lambda) lambda.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}\label{exo:simply-typed-canonseq}
   Instead of using the \texttt{sig} type, define a simply typed function that, given two ordinals $\alpha$ and $\beta$, returns a natural number $i$ such that, if $\alpha$ is a limit ordinal and $\beta<\alpha$, then $\beta< \canonseq{\alpha}{i+1}$. Of course, you will have to prove the correctness of your function. 

   \textbf{Hint:} You may add to your function a third argument usually called \texttt{fuel} for allowing you to give a structurally 
   recursive function (\emph{cf} the post of Guillaume Melquiond on Coq-club (Dec 21, 2020)
   \url{https://sympa.inria.fr/sympa/arc/coq-club/2020-12/msg00069.html}).
   The type \texttt{fuel}, an alternative 
   to \texttt{nat} is available on \href{../theories/html/hydras.Prelude.Fuel.html}{Prelude.Fuel}).
   \index{coq}{Giving fuel to a long computation}

   \end{exercise}

Accessibility inside :math:`\epsilon_0` : Paths
-----------------------------------------------

:raw-latex:`\index{maths}{Ordinal numbers!Accessibility inside epsilon0}`
:raw-latex:`\label{sect:pathes-intro}`

Let us consider a kind of accessibility problem inside
:math:`\epsilon_0`: given two ordinals :math:`\alpha` and :math:`\beta`,
where :math:`\beta<\alpha<\epsilon_0`, find a *path* consisting of a
finite sequence :math:`\gamma_0=\alpha,\dots,\gamma_l=\beta`, where, for
every :math:`i<l`, :math:`\gamma_i \not= 0`  [13]_ and there exists some
strictly positive integer :math:`s_i` such that
:math:`\gamma_{i+1}=\canonseq{\gamma}{s_i}`.

Let :math:`s` be the sequence
:math:`\langle s_0,s_1,\dots, s_{l-1} \rangle`. We describe the
existence of such a path with the notation
:math:`\alpha\xrightarrow [s]{}\beta`.

We say also that the considered path from :math:`\alpha` to
:math:`\beta` *starts at [index] :math:`s_0` and ends at :math:`s_l`*.

For instance, we have :math:`\omega*2 \xrightarrow[2,2,2,4,5]{}3`,
through the path
:math:`\langle\omega\times 2, \omega+2,\omega+1,\omega,4,3\rangle`.

.. raw:: latex

   \begin{remark}
     

   Note that, given $\alpha$ and $\beta$, where $\beta < \alpha$, the sequence $s$ which leads from $\alpha$ to $\beta$ is not unique.

   Indeed, if $\alpha$ is a limit ordinal, the first element of $s$ can be any integer $i$ such that $\beta<\canonseq{\alpha}{i}$, and if $\alpha$ is a successor ordinal,
   then the sequence $s$ can start with any positive integer.


   For instance, we have also 
   $\omega*2 \xrightarrow[3,4,5,6]{}\omega$. 
   Likewise,
   $\omega*2 \xrightarrow[1,2,1,4]{} 0$ and
   $\omega*2 \xrightarrow[3,3,3,3,3,3,3,3]{} 0$.
   \end{remark}

.. _path-to-definition:

Formal definition
~~~~~~~~~~~~~~~~~

In :raw-latex:`\coq{}`, the notion of path can be simply defined as an
inductive predicate parameterized by the destination :math:`\beta`.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Epsilon0.Paths <../theories/html/hydras.Epsilon0.Paths.html>`__

:raw-latex:`\index{hydras}{Library Epsilon0!Predicates!path\_to}`
:raw-latex:`\label{sect:path-to-def}`

.. raw:: latex

   \begin{Coqsrc}
   (Definition transition_S i : relation T1 :=
     fun alpha beta =>  alpha <> zero /\ beta = canonS alpha i.

   Definition transition i : relation T1 :=
     match i with 0 => fun _ _ => False | S j => transition_S j end.

   Inductive path_to (beta: T1) : list nat -> T1 -> Prop :=
     path_to_1 : forall (i:nat) alpha , 
       i <> 0 ->
       transition i alpha beta ->
       path_to beta (i::nil) alpha
   | path_to_cons : forall i alpha s gamma,
       i <> 0 ->
       transition i alpha gamma ->
       path_to beta  s gamma ->
       path_to beta  (i::s) alpha.
   \end{Coqsrc}

.. raw:: latex

   \begin{remark}
   The definition above is parameterized with the \emph{destination} of the path and indexed by the origin, hence the name \texttt{path\_to}. The rationale behind this choice is a personal preference of the developer  for the kind of eliminators generated by \coq{} in this case. The symmetric option could have been also considered (see also Remark~\vref{remark:transitive-closure}).
   \end{remark}

.. raw:: latex

   \begin{remark}
   In the present version of our library, we use a variant \texttt{path\_toS} of
   \texttt{path\_to}, where the proposition
   (\texttt{path\_toS $\beta$ $s$ $\alpha$}) is equivalent to
   (\texttt{path\_to $\beta$ (shift $s$) $\alpha$}). This variant is scheduled to be deprecated.
   \end{remark}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Write a tactic for solving goals of the form (\texttt{path\_to $\beta$ $s$ $\alpha$})
   where $\alpha$, $\beta$ and $s$ are closed terms. 
   You should solve automatically the following goals:

   \begin{Coqsrc}
    path_to omega (2::2::2::nil) (omega * 2).

    path_to omega (3::4::5::6::nil) (omega * 2).

    path_to zero (interval 3 14) (omega * 2).

    path_to zero (repeat 3 8) (omega * 2).
   \end{Coqsrc}

   \end{exercise}

Existence of a path
~~~~~~~~~~~~~~~~~~~

:raw-latex:`\index{maths}{Transfinite induction}`

By transfinite induction on :math:`\alpha`, we prove that for any
:math:`\beta<\alpha`, one can build a path from :math:`\alpha` to
:math:`\beta` (in other terms, :math:`\beta` is accessible from
:math:`\alpha`).

.. raw:: latex

   \begin{Coqsrc}
   Lemma LT_path_to (alpha beta : T1) :
     beta t1< alpha -> {s : list nat | path_to beta s alpha}.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}[continuation of exercise~\vref{exo:simply-typed-canonseq}]Define a simply typed function for computing a path from $\alpha$ to $\beta$.
   \end{exercise}

:raw-latex:`\noindent ` From the lemma
``canonS_LT`` :raw-latex:`\vref{lemma:canonS_LT}`, we can convert any
path into an inequality on ordinals (by induction on paths).

.. raw:: latex

   \begin{Coqsrc}
   Lemma path_to_LT beta s alpha :
     path_to beta s alpha -> nf alpha -> beta t1< alpha.
   \end{Coqsrc}

.. _KS-o2h:

Paths and hydra battles
~~~~~~~~~~~~~~~~~~~~~~~

In order to apply our knowledge about ordinal numbers less than
:math:`\epsilon_0` to the study of hydra battles, we define an injection
from the interval :math:`[0,\epsilon_0)` into the type ``Hydra``.

.. raw:: latex

   \vspace{4pt}

*From Module *\ `Hydra.O2H <../theories/html/hydras.Hydra.O2H.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint iota (alpha : T1) : Hydra :=
     match alpha with
     | T1.zero => head
     | ocons gamma n beta => 
            node (hcons_mult (iota gamma) (S n) (iotas beta))
     end 
   with iotas (alpha : T1) :  Hydrae :=
          match alpha with
          | T1.zero => hnil
          | ocons alpha0 n beta  => 
              hcons_mult (iota alpha0) (S n) (iotas beta)
          end.
   \end{Coqsrc}

For instance Fig. :raw-latex:`\ref{fig:iota-example}` shows the image by
:math:`\iota` of the ordinal
:math:`\omega^{\omega+2}+\omega^\omega \times 2 + \omega + 1`

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.3]
   \node (foot) at (10,0) {$\bullet$};
   \node (N1) at (2,2) {$\bullet$};
   \node (N2) at (10,2) {$\bullet$};
   \node (N22) at (7,2) {$\bullet$};
   \node (N3) at (14,2) {$\bullet$};
   \node (N4) at (18,2) {$\Smiley[2][green]$};
   \node (N5) at (0,4) {$\bullet$};
   \node (N6) at (2,5) {$\Smiley[2][green]$};
   \node (N7) at (4,6) {$\Smiley[2][green]$};
   \node (N88) at (7,4) {$\bullet$};
   \node (N8) at (10,4) {$\bullet$};
   \node (N9) at (14,6) {$\Smiley[2][green]$};
   \node (N10) at (0,8) {$\Smiley[2][green]$};
   \node (N11) at (10,7) {$\Smiley[2][green]$};
   \node (N111) at (7,7) {$\Smiley[2][green]$};
   \draw (foot) to [bend left=10] (N1);
   \draw (foot) -- (N2);
   \draw (foot) -- (N22);
   \draw (foot) -- (N3);
   \draw (foot) -- (N4);
   \draw (N1) to  (N5);
   \draw (N1) to   [bend left=10] (N6);
   \draw (N1) to   [bend right=20] (N7);
   \draw (N2) to  (N8);
   \draw (N22) to  (N88);
   \draw (N8) to  (N11);
   \draw (N88) to  (N111);
   \draw (N3) to  (N9);
   \draw (N5) to  (N10);
   \end{tikzpicture}

The following lemma (proved in
 `Hydra.O2H.v <../theories/html/hydras.Hydra.O2H.html>`__) maps
canonical sequences to rounds of hydra battles.

:raw-latex:`\label{lemma:canonS-iota}`

.. raw:: latex

   \begin{Coqsrc}
   Lemma canonS_iota i alpha :
       nf alpha -> alpha <> 0 ->
       iota alpha -1-> iota (canonS alpha i).
   \end{Coqsrc}

The next step of our development extends this relationship to the order
:math:`<` on :math:`[0,\epsilon_0)` on one side, and hydra battles on
the other side.

.. raw:: latex

   \begin{Coqsrc}
   Lemma path_to_battle alpha s beta :
     path_to  beta  s alpha -> nf alpha ->
     iota alpha -+-> iota beta.
   \end{Coqsrc}

As a corollary, we are now able to transform any inequality
:math:`\beta<\alpha<\epsilon_0` into a (free) battle.

.. raw:: latex

   \begin{Coqsrc}
   Lemma LT_to_battle alpha beta :
       beta t1< alpha ->  iota alpha -+-> iota beta.
   \end{Coqsrc}

A proof of impossibility
------------------------

We now have the tools for proving that there exists no variant bounded
by some :math:`\mu<\epsilon_0` for proving the termination of all
battles. The proof we are going to show is a proof by contradiction. It
can be considered as a generalization of the proofs described in
sections :raw-latex:`\vref{omega-case}` and
:raw-latex:`\vref{omega2-case}`.

In the module
`Epsilon0_Needed_Generic <../theories/html/hydras.Hydra.Epsilon0_Needed_Generic.html>`__,
we assume there exists some variant :math:`m` bounded by some ordinal
:math:`\mu<\epsilon_0`. This part of the development is parameterized by
some class :math:`B` of battles, which will be instantiated later to
``free`` or ``standard``.

.. raw:: latex

   \begin{Coqsrc}
   Class BoundedVariant {A:Type}{Lt:relation A}
         {Wf: well_founded Lt}{B : Battle}
         {m: Hydra -> A} (Var: Hvariant  Wf  B m)(mu:A):=
     {
     m_bounded: forall h, Lt (m h ) mu
     }.
   \end{Coqsrc}

Let us assume there exists such a variant:

.. raw:: latex

   \begin{Coqsrc}
   Context (B: Battle)
             (mu: T1)
             (Hmu: nf mu)
             (m : Hydra -> T1)
             (Var : Hvariant  T1_wf B m)
             (Hy : BoundedVariant  Var mu).

     Hypothesis m_decrease : forall  i h h',
         round_n i h h'   -> m h' t1< m h.
   \end{Coqsrc}

:raw-latex:`\label{remark:m-decrease}`

.. raw:: latex

   \begin{remark}
     The hypothesis \texttt{m\_decrease} is not provable  in general, but is satisfied by
   the  \texttt{free} and \texttt{standard} kinds of battles. This trick allows to 
   ``factorize'' our proofs  of impossibility.
   \end{remark}

:raw-latex:`\index{maths}{Transfinite induction}`

First, we prove that :math:`m(\iota(\alpha))` is always greater than or
equal to :math:`\alpha`, by transfinite induction over :math:`\alpha`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma m_ge_0 alpha:  nf alpha -> alpha t1<= m (iota alpha).
   \end{Coqsrc}

-  If :math:`\alpha=0`, the inequality trivially holds

-  If :math:`\alpha` is the successor of some ordinal :math:`\beta`, the
   inequality :math:`\beta \leq m(\iota(\beta))` holds (by induction
   hypothesis). But the hydra :math:`\iota(\alpha)` is transformed in
   one round into :math:`\iota(\beta)`, thus
   :math:`m(\iota(\beta))<m(\iota(\alpha))`. Hence
   :math:`\beta<m(\iota(\alpha))`, which implies
   :math:`\alpha \leq m(\iota(\alpha))`

-  If :math:`\alpha` is a limit ordinal, then :math:`\alpha` is the
   least upper bound of the set of all the :math:`\canonseq{\alpha}{i}`.
   Thus, we have just to prove that
   :math:`\canonseq{\alpha}{i}< m(\iota(\alpha))` for any :math:`i`.

   -  Let :math:`i` be some natural number. By the induction hypothesis,
      we have
      :math:`\canonseq{\alpha}{i} \leq m(\iota(\canonseq{\alpha}{i}))`.
      But the hydra :math:`\iota(\alpha)` is transformed into
      :math:`\iota(\canonseq{\alpha}{i})` in one round, thus
      :math:`m(\iota(\canonseq{\alpha}{i})) < m(\iota(\alpha))`, by our
      hypothesis ``m_decrease``.

Please note that the impossibility proofs of
sections :raw-latex:`\vref{omega-case}` and
:raw-latex:`\vref{omega2-case}` contain a similar lemma, also called
``m_ge``. We are now able to build a counter-example.

.. raw:: latex

   \begin{Coqsrc}
     Definition big_h := iota mu.
     Definition beta_h := m big_h.
     Definition small_h := iota beta_h.
   \end{Coqsrc}

From Lemma ``m_ge_0`` we infer the following inequality :

.. raw:: latex

   \begin{Coqsrc}
       Corollary m_ge_generic : m big_h t1<= m small_h.
    \end{Coqsrc}

The (big) rest of the proof is dedicated to prove formally the converse
inequality ``m small_h t1< m big_h``.

.. _sec:free-battles-case:

The case of free battles
~~~~~~~~~~~~~~~~~~~~~~~~

Let us now consider that :math:`B` is instantiated to ``free`` (which
means that we are considering proofs of termination of *all* battles).
The following lemmas are proved in
Module `Hydra.Epsilon0_Needed_Free <../theories/html/hydras.Hydra.Epsilon0_Needed_Free.html>`__.
The case :math:`B=\texttt{standard}` is studied in
section :raw-latex:`\vref{std-case}`.

.. raw:: latex

   \begin{Coqsrc}
   Section Impossibility_Proof.

     Context (mu: T1)
             (Hmu: nf mu)
             (m : Hydra -> T1)
             (Var : Hvariant  T1_wf free m)
             (Hy : BoundedVariant Var mu).
     \end{Coqsrc}

#. The following lemma is an application of ``m_ge_generic``, since
   ``free`` satisfies trivially the hypothesis ``m_decrease`` (see
   page :raw-latex:`\pageref{remark:m-decrease}`).

   .. raw:: latex

      \begin{Coqsrc}
      Lemma m_ge : m big_h t1<= m small_h.
        Proof.
          apply m_ge_generic.
         (* ... *)
      \end{Coqsrc}

#. From the hypothesis ``m_bounded``, we have ``m big_h t1< mu``

#. By Lemma ``LT_to_battle``, we get a (free) battle from
   ``big_h = iota mu`` to ``small_h = iota (m big_h)``.

   .. raw:: latex

      \begin{Coqsrc}
        Lemma  big_to_small : big_h  -+-> small_h.
      \end{Coqsrc}

#. From the hypotheses on :math:`m`, we infer:

   .. raw:: latex

      \begin{Coqsrc}
      Lemma m_lt : m small_h t1< m big_h.
      \end{Coqsrc}

#. From lemmas ``m_ge`` and ``m_lt``, and the irreflexivity of
   :math:`<`, we get a contradiction.

   .. raw:: latex

      \begin{Coqsrc}
      Theorem Impossibility_free : False.

      End Impossibility_Proof.
      \end{Coqsrc}

We have now proved there exists no bounded variant for the class of free
battles.

.. raw:: latex

   \begin{Coqsrc}
   Check Impossibility_free.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   Impossibility_free
        : forall (mu : T1) (m : Hydra -> T1) (Var : Hvariant T1_wf free m),
          BoundedVariant Var mu -> False
   \end{Coqanswer}

.. _sec:standard-intro:

The case of standard battles
----------------------------

:raw-latex:`\label{std-case}` One may wonder if our theorem holds also
in the framework of standard battles. Unfortunately, its proof relies on
the lemma ``LT_to_round_plus`` of
Module `Hydra.O2H <../theories/html/hydras.Hydra.O2H.html>`__.

.. raw:: latex

   \begin{Coqsrc}
   Lemma LT_to_round_plus alpha beta :
       beta t1< alpha ->  iota alpha -+-> iota beta.
   \end{Coqsrc}

This lemma builds a battle out of any inequality :math:`\beta<\alpha`.
It is a straightforward application of ``LT_path_to`` of
Module `Epsilon0.Paths <../theories/html/hydras.Epsilon0.Paths.html>`__:

.. raw:: latex

   \begin{Coqsrc}
   Lemma LT_path_to (alpha beta : T1) :
     beta t1< alpha -> {s : list nat | path_to beta s alpha}.
   \end{Coqsrc}

The sequence :math:`s`, used to build the sequence of replication
factors of the battle depends on :math:`\beta`, so we cannot be sure
that the generated battle is a genuine standard battle.

The solution of this issue comes once again from Ketonen and Solovay’s
article :raw-latex:`\cite{KS81}`. Instead of considering plain paths,
i.e. sequences :math:`\alpha_0=\alpha,\alpha_1,\dots,\alpha_k=\beta`
where :math:`\alpha_{j+1}` is equal to :math:`\canonseq{\alpha_j}{i_j}`
where :math:`i_j` is *any* natural number, we consider various
constraints on these sequences. In particular, a path is called
*standard* if :math:`i_{j+1} = i_j + 1` for every :math:`j<k`. It
corresponds to a “segment” of some standard battles. Please note that
the vocabulary on paths is ours, but all the concepts come really
from :raw-latex:`\cite{KS81}`.

In :raw-latex:`\coq{}`, standard paths can be defined as follows.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Epsilon0.KS <../theories/html/hydras.Epsilon0.KS.html>`__

.. raw:: latex

   \begin{Coqsrc}
   (**  standard path from (i, alpha) to (j, beta) *)

   Inductive standard_pathR(j:nat)( beta:T1):  nat -> T1 -> Prop :=
     std_1 : forall i alpha, 
          beta = canon alpha i -> j = S i ->
          standard_pathR j beta i  alpha
   | std_S : forall i alpha, 
         standard_pathR j beta (S i) (canon alpha i)  ->
         standard_pathR j beta i alpha.

   Definition standard_path  i alpha j beta := 
      standard_pathR j beta i alpha.
   \end{Coqsrc}

In the mathematical text and figures, we shall use the notation
:math:`\alpha \xrightarrow[i,j]{}\beta` for the proposition
(``standard_path i \alpha j \beta``). In :raw-latex:`\cite{KS81}` the
notation is :math:`\alpha \xrightarrow[i]{*}\beta` for the proposition
:math:`\exists j, i<j \wedge \alpha \xrightarrow[i,j]{} \beta`.

Our goal is now to transform any inequality
:math:`\beta<\alpha<\epsilon_0` into a standard path
:math:`\alpha \xrightarrow[i,j]{} \beta` for some :math:`i` and
:math:`j`, then into a standard battle from :math:`\iota(\alpha+i)` to
:math:`\iota(\beta)`. Following :raw-latex:`\cite{KS81}`, we proceed in
two stages:

#. we simulate plain (free) paths from :math:`\alpha` to :math:`\beta`
   with paths made of steps :math:`(\gamma,\canonseq{\gamma}{n})`, *with
   the same :math:`n` all along the path*

#. we simulate any such path by a standard path.

Paths with a constant index
~~~~~~~~~~~~~~~~~~~~~~~~~~~

First of all, paths with a constant index enjoy nice properties. They
are defined as paths where all the :math:`i_j` are equal to the same
natural number :math:`i`, for some :math:`i>0`.

Like in :raw-latex:`\cite{KS81}`, we shall use the notation
:math:`\alpha \xrightarrow[i]{} \beta` for denoting such a path, also
called an :math:`i`-path.

.. raw:: latex

   \begin{Coqsrc}
   Definition const_pathS i :=
       clos_trans_1n T1 (fun alpha beta => beta = canonS alpha i).

   Definition const_path i alpha beta :=
     match i with
       0 => False
     | S j => const_pathS j alpha beta
   end.
   \end{Coqsrc}

A most interesting property of :math:`i`-paths is that we can “upgrade”
their index, as stated by K.&S.’s Corollary 12.

:raw-latex:`\index{maths}{Transfinite induction}`

.. raw:: latex

   \begin{Coqsrc}
   Corollary Cor12 (alpha : T1) :  nf alpha ->
            forall beta i n, beta  t1< alpha  ->
                   i < n ->
                    const_pathS i alpha beta ->
                    const_pathS n alpha beta.
   Proof.
     transfinite_induction_lt alpha.
     (* (long) proof skipped *)
   \end{Coqsrc}

We also use a version of ``Cor12`` with large inequalities.

.. raw:: latex

   \begin{Coqsrc}
   Corollary Cor12_1 (alpha : T1) :
     nf alpha ->
     forall beta i n, beta t1< alpha ->
                      i <= n ->
                      const_pathS i alpha beta ->
                      const_pathS n alpha beta.
   \end{Coqsrc}

Sketch of proof of ``Cor12``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

:raw-latex:`\index{maths}{Transfinite induction}`

We prove this lemma by transfinite induction on :math:`\alpha`. Let us
consider a path :math:`\alpha \xrightarrow [i]{} \beta` :math:`(i>0)`.
Its first step is the pair :math:`(\alpha,\canonseq{\alpha}{i})`, We
have :math:`\canonseq{\alpha}{i}<\alpha` and
:math:`\canonseq{\alpha}{i} \xrightarrow [i]{} \beta`. Let :math:`n` be
any natural number such that :math:`n>i`. By the induction hypothesis,
there exists a path
:math:`\canonseq{\alpha}{n} \xrightarrow[i]{} \beta`.

-  If :math:`\alpha` is a successor ordinal :math:`\gamma+1`, then
   :math:`\canonseq{\alpha}{n} =
   \canonseq{\alpha}{i}=\gamma`. Thus we have a path
   :math:`\alpha  \xrightarrow [n]{}  \gamma \xrightarrow [n]{} \beta`

-  If :math:`\alpha` is a limit ordinal, we apply the following theorem
   (numbered ``2.4`` in Ketonen and Solovay’s article).

   .. raw:: latex

      \begin{Coqsrc}
      Theorem Theorem_2_4 (lambda : T1) :
         nf lambda ->
         limitb lambda  ->
         forall i j, (i < j)%nat ->
                     const_pathS 0 (canonS lambda j)
                                   (canonS lambda i). 
        \end{Coqsrc}

   We build the following paths :

   #. :math:`\alpha \xrightarrow[n]{} \canonseq{\alpha}{n}`

   #. :math:`\canonseq{\alpha}{n} \xrightarrow[1]{} \canonseq{\alpha}{i}`
      (by ``Theorem_2_4``),

   #. :math:`\canonseq{\alpha}{n} \xrightarrow[n]{} \canonseq{\alpha}{i}`
      (applying the induction hypothesis to the preceding path);

   #. :math:`\canonseq{\alpha}{i} \xrightarrow[n]{} \beta` (applying the
      induction hypothesis)

   #. :math:`\alpha \xrightarrow[n]{} \beta` (by composition of 1, 3,
      and 4).

.. raw:: latex

   \begin{remark}
    \texttt{Cor12} ``casts'' $i$-paths into $n$-paths for any $n>i$.
   But the obtained $n$-path can be much longer than the original $i$-path.
   The following exercise will give an idea of this increase. 
   \end{remark}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
     Prove that  the length of the $i+1$-path from
     $\omega^\omega$ to $\omega^i$ is $1 + (i+1)^{(i+1)}$, for any $i$. Note that the $i$-path from
     $\omega^\omega$ to $\omega^i$ is only one step long.
    \end{exercise}

Why is ``Cor12`` so useful? Let us consider two ordinals
:math:`\beta<\alpha<\epsilon_0`. By induction on :math:`\alpha`, we
decompose any inequality :math:`\beta<\alpha` into
:math:`\beta < \canonseq{\alpha}{i}< \alpha`, where :math:`i` is some
integer. Applying collorary ``Cor12’`` we build a :math:`n`-path from
:math:`\beta` to :math:`\alpha`, where :math:`n` is the maximum of the
indices :math:`i` met in the induction.

Lemma 1, Section 2.6 of :raw-latex:`\cite{KS81}` is naturally expressed
in terms of :raw-latex:`\coq`’s :raw-latex:`\verb@sig@ `construct.

:raw-latex:`\label{lemma:L-2_6-1}` :raw-latex:`\index{coq}{Sigma types}`

.. raw:: latex

   \begin{Coqsrc}
   Lemma Lemma2_6_1 (alpha : T1) :  
     nf alpha -> forall beta,  beta t1< alpha  ->
     {n:nat | const_pathS n alpha beta}.
   Proof.
     transfinite_induction alpha.
     (* ... *)
   \end{Coqsrc}

Intuitively, lemma ``L2_6_1`` shows that if
:math:`\beta<\alpha<\epsilon_0`, then there exists a battle from
:math:`\iota(\alpha)` to :math:`\iota(\beta)` where the replication
factor is constant, although large enough.

Casting paths with a constant index into a standard path
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The article :raw-latex:`\cite{KS81}` contains the following lemma, the
proof of which is quite complex, which allows to simulate
:math:`i`-paths by :math:`[i+1,j]`-paths, where :math:`j` is large
enough.

.. raw:: latex

   \begin{Coqsrc}
   (* Lemma 1 page 300 of [KS] *)

   Lemma constant_to_standard_path 
     (alpha beta : T1) (i : nat):
     nf alpha -> const_pathS i alpha beta -> zero  t1< alpha ->
     {l:nat | standard_path (S i) alpha j beta}.
   \end{Coqsrc}

Sketch of proof of ``constant_to_standard_path``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Our proof follows the proof by Ketonen and Solovay, including its
organization as a sequence of lemma. Since it is a non-trivial proof, we
will comment its main steps below.

.. _preliminaries-1:

Preliminaries
^^^^^^^^^^^^^

Please note that, given an ordinal :math:`\alpha:\texttt{T1}`, and two
natural numbers :math:`i` and :math:`l`, there exists at most a standard
path :math:`\alpha \xrightarrow [i,i+l]{*} \beta`. The following
function computes :math:`\beta` from :math:`\alpha`, :math:`i` and
:math:`l`.

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint standard_gnaw (i:nat)(alpha : T1)(l:nat):  T1  :=
     match l with
     | 0 => alpha
     | S m => standard_gnaw (S i) (canon alpha i) m
     end.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
     Compute standard_gnaw 2 omega 15.
   (*   = zero
        : T1 *)
   Compute pp (standard_gnaw 2 (omega^omega)  10).
   (*
   = (omega + 7)%pT1
        : ppT1
   *)
   Compute pp (standard_gnaw 4 (omega^omega)  100).
   (*
    = (omega ^ 3 * 4 + omega ^ 2 * 5 + omega * 3 + 39)%pT1
        : ppT1 *)
   \end{Coqsrc}

:raw-latex:`\index{maths}{Transfinite induction}`

By transfinite induction over :math:`\alpha`, we prove that the ordinal
:math:`0` is reachable from any ordinal :math:`\alpha<\epsilon_0` by
some standard path.

.. raw:: latex

   \begin{Coqsrc}
   Lemma standard_path_to_zero :
     forall  alpha i, nf alpha ->
                      {j: nat | standard_path (S i) alpha j zero}.
   \end{Coqsrc}

Noq, let us consider two ordinals :math:`\beta<\alpha<\epsilon_0`. Let
:math:`p` be some :math:`(n+1)`-path from :math:`\alpha` to
:math:`\beta`.

.. raw:: latex

   \begin{Coqsrc}
    Section Constant_to_standard_Proof.

     Variables (alpha beta: T1) (n : nat).
     Hypotheses (Halpha: nf alpha) (Hpos : zero t1<  beta)
                (p : const_pathS n alpha  beta).
   \end{Coqsrc}

Applying ``standard_path_to_zero``, :math:`0` is reachable from
:math:`\alpha` by some standard path (see
figure :raw-latex:`\vref{fig:belle-preuve-1}`).

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.25]
   \node (alpha) at (0,0) {$\alpha$};
       \node (beta) at (32, 0){$\beta$};
     

     \draw[->, very thick,blue] (alpha)-- node [below]{$n+1$} node [above] {$+$} (beta);

     \node (alpha1) at (5,5) {};
     \node (alpha2) at (13,5) {};
       \node (alpha3) at (20,5) {};
     \node (alphalast) at (35,5) {};
     \node (zero) at (45,0) {$0$};
     \draw [->, dashed,very thick,blue] (alpha)-- node [below, rotate=40]{$n+1$}  (alpha1);
     \draw [->, dashed,very thick,blue] (alpha1)-- node [below]{$n+2$}  (alpha2);
      \draw [->, dashed,very thick,blue] (alpha2)-- node [below]{$n+3$}  (alpha3);
     
     \node (dots) at (24,5) {$\dots$};
     \draw [->, dashed, very thick,blue] (alphalast)-- node [below, rotate=-26]{$n+p+1$}  (zero);

   \end{tikzpicture}

.. _section-1:

Since comparison on ``T1`` is decidable, one can compute the last step
:math:`\gamma` of the standard path from :math:`(\alpha,n+1)` such that
:math:`\beta\leq \gamma`. Let :math:`l` be the length of the path from
:math:`\alpha` to :math:`\gamma`. This step of the proof is illustrated
in figure :raw-latex:`\vref{fig:belle-preuve-2}`.

.. raw:: latex

   \centering

.. raw:: latex

   \begin{tikzpicture}[very thick, scale=0.25]
   \node (alpha) at (0,0) {$\alpha$};
       \node (beta) at (32, 0){$\beta$};
     



     \node (alpha1) at (5,5) {};
     \node (alpha2) at (13,5) {};
     \node (dots) at (17,5) {$\ldots$};
       \node (alpha3) at (20,5) {};
       \node (gamma) at (24,0) {$\gamma$};
       \node (delta) at (38,0) {$\delta$};
       \draw [->, dashed,very thick,blue] (alpha)-- node [below,rotate=35]{$n+1$}  (alpha1);
     \draw [->, dashed,very thick,blue] (alpha1)-- node [below]{$n+2$}  (alpha2);
      \draw [->, dashed,very thick,blue] (alpha3)-- node [below,rotate = -48]{\tiny $n+l$}  (gamma);
      \draw  [->, dashed, blue] (gamma) to    [bend left=80] node [below]{$n+l+1$} (delta);
      \draw[->, very thick,blue] (alpha) to [bend right=34] node [below]{$n+1$} node [above] {$+$} (beta);
      \draw[thick] (alpha)--  (gamma);
      \draw[thick] (gamma)--  node [above] {$\geq$} (beta);
       \draw[thick] (beta)--  node [above] {$>$} (delta);
   \end{tikzpicture}

.. _section-2:

-  If :math:`\beta=\gamma`, its OK! We have got a standard path from
   :math:`\alpha` to :math:`\beta` with successive indices
   :math:`n+1, n+2, \dots, n+l+1`

-  Otherwise, :math:`\beta < \gamma`. Let us consider
   :math:`\delta=\canonseq{\gamma}{n+l+1}`. By applying several times
   lemma ``Cor12``, one converts every path of
   Fig :raw-latex:`\ref{fig:belle-preuve-2}` into a :math:`n+l+1`-path
   (see figure :raw-latex:`\ref{fig:belle-preuve-3}`).

   But :math:`\gamma` is on the :math:`n+l+1`-path from :math:`\alpha`
   to :math:`\beta`. As shown by
   figure :raw-latex:`\vref{fig:fin-belle-preuve}`, the ordinal
   :math:`\delta`, reachable from :math:`\gamma` in one single step,
   must be greater than or equal to :math:`\beta`, which contradicts our
   hypothesis :math:`\beta < \gamma`.

   .. raw:: latex

      \centering

   .. raw:: latex

      \begin{tikzpicture}[very thick, scale=0.25]
      \node (alpha) at (0,0) {$\alpha$};
          \node (beta) at (32, 0){$\beta$};
          \node (alpha1) at (5,5) {};
        \node (alpha2) at (13,5) {};
        \node (dots) at (17,5) {$\ldots$};
          \node (alpha3) at (20,5) {};
          \node (gamma) at (24,0) {$\gamma$};
          \node (delta) at (38,0) {$\delta$};
           \draw [->, dashed,very thick,blue] (alpha)-- node [below, rotate = 40] {\tiny $n+l+1$}  node [above, rotate = 40]{\tiny $+$}  (alpha1);
        \draw [->, dashed,very thick,blue] (alpha1)-- node [below]{\tiny $n+l+1$} node [above]{\tiny $+$} (alpha2);
         \draw [->, dashed,very thick,blue] (alpha3)-- node [below, rotate = -48]{\tiny $n+l+1$} node [above, rotate = -36]{\tiny $+$}  (gamma);
         \draw  [->, dashed, blue] (gamma) to    [bend left=80] node [below]{\tiny $n+l+1$} node [above]{\color{red} $1$} (delta);
         \draw[->, very thick,blue] (alpha) to [bend right=34] node [below]{\small $n+l+1$} node [above] {\tiny $+$} (beta);
          \draw[thick] (gamma)--   node [above]{\color{red} $>$}(beta);
         \draw[thick] (alpha)--  (gamma);
        
          \draw[thick] (beta)--  node [above] {$>$} (delta);

        
        
      \end{tikzpicture}

   .. raw:: latex

      \centering

   .. raw:: latex

      \begin{tikzpicture}[very thick, scale=0.25]
      \node (alpha) at (0,0) {$\alpha$};
          \node (beta) at (32, 0){$\beta$};
        
        \node (alpha1) at (5,5) {};
        \node (alpha2) at (13,5) {};
        \node (dots) at (15,5) {$\ldots$};
          \node (alpha3) at (18,5) {};
          \node (gamma) at (24,0) {$\gamma$};
          \node (delta) at (42,0) {$\delta$};
          \draw [->, dashed,very thick,blue] (alpha)-- node [below, rotate = 40] {\tiny $n+l+1$}  node [above, rotate = 40]{\tiny $+$}  (alpha1);
        \draw [->, dashed,very thick,blue] (alpha1)-- node [below]{\tiny $n+l+1$} node [above]{\tiny $+$} (alpha2);
         \draw [->, dashed,very thick,blue] (alpha3)-- node [below, rotate = -36]{\tiny $n+l+1$} node [above, rotate = -36]{\tiny $+$}  (gamma);
         \draw  [->, dashed, blue] (gamma) to    [bend left=80] node [below]{\small $n+l+1$} node [above]{\color{red} $1$} (delta);
         \draw[->, very thick,blue] (alpha) to [bend right=34] node [below]{\small $n+l+1$} node [above] {\tiny $+$} (beta);
         \draw[thick] (alpha)--  (gamma);
        
          \draw[thick] (gamma)--  node [below]{\tiny $n+l+1$} node [above]{\color{red} $+$}(beta);
          \draw[thick] (beta)--  node [above] {$>$} (delta);

      \end{tikzpicture}

The only possible case is thus :math:`\beta=\gamma`, so we have got a
standard path from :math:`\alpha` to :math:`\beta`.

.. raw:: latex

   \begin{Coqsrc}
    Lemma constant_to_standard_0 : 
       {l : nat | standard_fun (S n) alpha l = beta}.
    (* ... *)

   End Constant_to_standard_Proof.
   \end{Coqsrc}

Here is the full statement of the conversion from constant to standard
paths.

.. raw:: latex

   \begin{Coqsrc}
   Lemma constant_to_standard_path 
     (alpha beta : T1) (i : nat):
     nf alpha -> const_pathS i alpha beta -> zero  t1< alpha ->
     {j:nat | standard_path (S i) alpha j beta}.
   \end{Coqsrc}

Applying ``Lemma2_6_1`` and ``constant_to_standard_path``, we get the
following corollary.

.. raw:: latex

   \begin{Coqsrc}
   Corollary  LT_to_standard_path  (alpha beta : T1) :
     beta t1< alpha ->
     {n : nat & {j:nat | standard_path (S n) alpha j beta}}.
   \end{Coqsrc}

.. _sec:standard-battles-cases:

Back to hydras
~~~~~~~~~~~~~~

We are now able to complete our proof that there exists no bounded
variant for proving the termination of standard hydra battles. This
proof can be consulted in the module
`../theories/html/hydras.Hydra.Epsilon0_Needed_Std.html <../theories/html/hydras.Hydra.Epsilon0_Needed_Std.html>`__.
Please note that it has the same global structure as in
section:raw-latex:`\ref{sec:free-battles-case}` Applying the lemmas
``Lemma2_6_1`` of the module
```Epsilon0.Paths`` <../theories/html/hydras.Epsilon0.Paths.html#Lemma2_6_1>`__
and
```constant_to_standard_path`` <../theories/html/hydras.Epsilon0.Paths.html#constant_to_standard_path>`__,
we can convert any inequality :math:`\beta<\alpha<\epsilon_0` into a
standard path from :math:`\alpha` to :math:`\beta`, then into a fragment
of a standard battle from :math:`\iota(\alpha)` to :math:`\iota(\beta)`,
hence the inequality :math:`m(\iota(\beta))<m(\iota(\alpha))`.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Hydra.Epsilon0_Needed_Std <../theories/html/hydras.Hydra.Epsilon0_Needed_Std.html#LT_to_standard_battle>`__

.. raw:: latex

   \begin{Coqsrc}
   Lemma LT_to_standard_battle :
       forall alpha beta,
         beta t1< alpha ->
         exists n i,  battle standard  n (iota alpha) i (iota beta).
   \end{Coqsrc}

Next, please consider the following context:

.. raw:: latex

   \begin{Coqsrc}
   Section Impossibility_Proof.

   Context (mu: T1)
             (Hmu: nf mu)
             (m : Hydra -> T1)
             (Var : Hvariant  T1_wf standard m)
             (Hy : BoundedVariant Var mu).
    \end{Coqsrc}

In the same way as for free battles, we import a large inequality from
the module
`Epsilon0_Needed_Generic <../theories/html/hydras.Hydra.Epsilon0_Needed_Generic.html>`__.

.. raw:: latex

   \begin{Coqsrc}
    Lemma m_ge : m big_h t1<= m small_h.
   \end{Coqsrc}

.. _section-3:

If remains to prove the following strict inequality, in order to have a
contradiction.

.. raw:: latex

   \begin{Coqsrc}
     Lemma m_lt : m small_h  t1< m big_h.

     Theorem Impossibility_std: False.

   End Impossibility_Proof.
   \end{Coqsrc}

Sketch of proof:
''''''''''''''''

Let us recall that :math:`\texttt{big\_h} = \iota(\mu)` and
:math:`\texttt{small\_h} = \iota (m (\texttt{big\_h}))`.

Since :math:`m(\texttt{big\_h})< \mu`, there exists a standard path from
:math:`\mu` to :math:`m(\texttt{big\_h})`, hence a standard battle from
:math:`\iota(\mu)` to :math:`\iota(m(\texttt{big\_h}))`, i.e. from
``big_h`` to ``small_h``.

Since :math:`m` is assumed to be a variant for standard battles, we get
the inequality :math:`m(\texttt{small\_h}) < m(\texttt{big\_h})`.

Remarks
~~~~~~~

We are grateful to J. Ketonen and R. Solovay for the high quality of
their explanations and proof details. Our proof follows tightly the
sequence of lemmas in their article, with a focus on constructive
aspects. Roughly steaking, our implementation *builds*, out of a
hypothetic variant :math:`m`, bounded by some ordinal
:math:`\mu<\epsilon_0`, a hydra ``big_h`` which verifies the impossible
inequality :math:`m(\texttt{big\_h})< m(\texttt{big\_h})`.

On may ask whether the preceding results are too restrictive, since they
refer to a particular data type ``T1``. In fact, our representation of
ordinals strictly less than :math:`\epsilon_0` is faithful to their
mathematical definition, at least Kurt
Schütte’s :raw-latex:`\cite{schutte}`, as proved in
Chapter :raw-latex:`\vref{chap:schutte}`. (please see also `the module
``hydras.Schutte.Correctness_E0`` <../theories/html/hydras.Schutte.Correctness_E0.html>`__).

Thus, we can infer that our theorems can be applied to any well order.

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Study a possible modification of the definition of a variant  (for  standard battles).

   \begin{itemize}
   \item The variant is assumed to be strictly decreasing \emph{on configurations 
   reachable from some initial configuration where the replication factor is equal to $0$}
   \item The variant may depend on the number of the current round.
   \end{itemize}

   In other words, its type should be \texttt{nat -> Hydra -> T1}, and it must 
   verify the inequality $m\, (S\,i)\, h' < m\,i\, h$ whenever the configuration 
   $(i,h)$ is reachable from some initial configuration $(0,h_0)$
   and \texttt{h} is transformed into \texttt{h'} in the considered round.
   Can we still prove the theorems of section~\ref{std-case} with this new definition?

   \end{project}

.. _chap:alpha-large:

Large sets and rapidly growing functions
========================================

In this chapter, we try to feel how long a standard battle can be. To be
precise, for any ordinal :math:`\alpha<\epsilon_0` and any positive
integer :math:`k`, we give a minoration of the number of steps of a
standard battle which starts with the hydra :math:`\iota(\alpha)` and
the replication factor :math:`k`.

We express this number in terms of the Hardy hierarchy of fast-growing
functions :raw-latex:`\cite{BW85, Wainer1970, KS81, Promel2013}`. From
the :raw-latex:`\coq{}` user’s point of view, such functions are very
attractive: they are defined as functions in :raw-latex:`\gallina{}`,
and we can apply them *in theory*, but they are so complex that you will
never be able to look at the result of the computation. Thus, our
knowledge on these functions must rely on *proofs*, not tests. In our
development, we use often the rewriting rules generated by
:raw-latex:`\coq`’s ``Equations`` plug-in.

.. _definitions-1:

Definitions
-----------

.. raw:: latex

   \begin{definition}
   Let $0<\alpha<\epsilon_0$ be any ordinal, and $s$ a finite sequence $\langle s_1, s_2, \dots, s_N\rangle$ of strictly positive natural numbers. 

   We say that $s$ is \emph{$\alpha$-large} if the sequence $\langle \alpha_0=\alpha,\dots,\alpha_{i+1}=\canonseq{\alpha_i}{i+1},\dots \rangle$ leads to $0$. 

   We say that $s$ is \emph{minimally $\alpha$-large} (in short:
   \emph{$\alpha$-mlarge}) if $s$ is $\alpha$-large 
    and every strict prefix of $s$ leads to a non-zero ordinal (\emph{cf} Sect.~\vref{sect:path-to-def}).

   \index{maths}{Ordinal numbers!Large sets}
   \index{maths}{Ordinal numbers!Minimal large sets}

   \end{definition}

.. raw:: latex

   \begin{remark}
     Ketonen and Solovay~\cite{KS81} consider  large finite \emph{sets} of natural numbers,  but they are mainly used as sequences. Thus, we chosed to represent them explicitely as (sorted) lists. 
   \end{remark}

The following function “gnaws” an ordinal :math:`\alpha`, folowing a
sequence of indices (ignoring the :math:`0`\ s). :raw-latex:`\noindent`
*From
Module *\ `Epsilon0.Paths <../theories/html/hydras.Epsilon0.Paths.html#gnaw>`__

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint gnaw (alpha : T1) (s: list nat) :=
     match s with
       | nil => alpha
       | (0::s') => gnaw  alpha s'
       | (S i :: s')  =>  gnaw (canonS i alpha) s'
     end.

   Definition large alpha (s:list nat) := gnaw alpha s = zero.
   \end{Coqsrc}

Minimal large sequences can be directly defined in terms of the
predicate ``path_to`` (:raw-latex:`\vref{sect:path-to-def}`) which
already prohibits paths containing non-final ``zero``\ s.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent` *From
Module *\ `Epsilon0.Large_Sets <../theories/html/hydras.Epsilon0.Large_Sets.html#mlarge>`__

:raw-latex:`\index{hydras}{Library Epsilon0!Predicates!mlarge@mlarge (minimal large sequences)}`

.. raw:: latex

   \begin{Coqsrc}
   Definition mlarge alpha (s:list nat) := path_to zero s alpha.
   \end{Coqsrc}

Let us consider two integers :math:`k` and :math:`l`, such that
:math:`0<k<l`. In order to check whether the interval :math:`[k,l]` is
minimally large for :math:`\alpha`, it is enough to follow from
:math:`\alpha` the path associated with the interval :math:`[k,l(` and
verify that the last ordinal we obtain is equal to :math:`1`.

.. _example-2:

Example
~~~~~~~

For instance the interval :math:`[6,70]` leads :math:`\omega^2` to
:math:`\omega\times 2 + 56`. Thus this interval is not
:math:`\omega^2`-mlarge.

.. raw:: latex

   \begin{Coqsrc}
   Compute pp (gnaw (omega * omega) (interval 6 70)).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
    = (omega * 2 + 56)%pT1
        : ppT1
   \end{Coqanswer}

Let us try another computation.

.. raw:: latex

   \begin{Coqsrc}
   Compute (gnaw (omega * omega) (interval 6 700)).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
    = zero : T1
   \end{Coqanswer}

We may say that the interval :math:`[6,700]` is :math:`\omega^2`-large,
since it leads to :math:`0`, but nothing assures us that the condition
of minimality is satisfied.

The following lemma relates minimal largeness with the function
``gnaw``.

.. raw:: latex

   \begin{Coqsrc}
   Lemma mlarge_iff alpha x (s:list nat) :
     s <> nil -> ~ In 0 (x::s) ->
     mlarge alpha (x::s) <-> gnaw alpha (but_last x s) = one.
    \end{Coqsrc}

For instance, we can verify that the interval :math:`[6,510]` is
:math:`\omega^2`-mlarge.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent` *From
Module *\ `Epsilon0.Large_Sets_Examples <../theories/html/hydras.Epsilon0.Large_Sets_Examples.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Example Ex1 : mlarge (omega * omega) (interval 6 510).
   \end{Coqsrc}

Length of minimal large sequences
---------------------------------

Now, consider any natural number :math:`k>0`. We would like to compute a
number :math:`l` such that the interval :math:`[k,l]` is
:math:`\alpha`-mlarge. So, the standard battle starting with
:math:`\iota(\alpha)` and the replication factor :math:`k` will end
after :math:`(l-k+1)` steps.

First, we notice that this number :math:`l` exists, since the segment
:math:`[0,\epsilon_0)` is well-founded and
:math:`\canonseq{\alpha}{i}<\alpha` for any :math:`i` and
:math:`\alpha>0`. Moreover, it is unique:

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent` *From
Module *\ `Epsilon0.Large_Sets <../theories/html/hydras.Epsilon0.Large_Sets.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Lemma mlarge_unicity alpha k l l' : 
     mlarge alpha (interval (S k) l) ->
     mlarge alpha (interval (S k) l') ->
     l = l'.
   \end{Coqsrc}

Thus, it seems obvious that there must exist a function, parameterized
by :math:`\alpha` which associates to any strictly positive integer
:math:`k` the number :math:`l` such that the interval :math:`[k,l]` is
:math:`\alpha`-mlarge. It would be fine to write in
:raw-latex:`\gallina{}` a definition like this:

.. raw:: latex

   \begin{Coqbad}
   Function L (alpha: E0) (i:nat) :  nat := ...
   \end{Coqbad}

But we do not know how to fill the dots yet … In the next section, we
will use :raw-latex:`\coq{}` to reason about the *specification* of
``L``, prove properties of any function which satisfies this
specification. In Sect. :raw-latex:`\ref{sect:L-equations}`, we use the
``coq-equations`` plug-in to define a function ``L_``, and prove its
correctness w.r.t. its specification.

Formal specification
~~~~~~~~~~~~~~~~~~~~

Let :math:`0<\alpha<\epsilon_0` be an ordinal term. We consider any
function which associates maps any strictly positive integer :math:`k`
to the number :math:`l`, where the interval :math:`[k,l)` is
:math:`\alpha`-mlarge.

.. raw:: latex

   \begin{remark}
   The upper bound of the considered interval has been chosen to be  $l-1$ and not $l$, in order to simplify some statements and proofs in composition lemmas associated with the ordinals of the form $\alpha\times i$ and 
   $\omega^\alpha\times i + \beta$.
   In order to consider any ordinal below $\epsilon_0$, we consider a special case for $\alpha=0$.
   \end{remark}

Our specification of the function ``L`` is as follows:

.. raw:: latex

   \begin{Coqsrc}
   Inductive L_spec : T1 -> (nat -> nat) -> Prop :=
   | L_spec0 : forall f, (forall k, f k = k) ->  L_spec zero f
   | L_spec1 : forall alpha f,
       alpha <> zero ->
       (forall k, mlarge alpha (interval (S k) (Nat.pred (f (S k))))) ->
       L_spec alpha f.
   \end{Coqsrc}

Note that, for :math:`\alpha\not=0`, the value of :math:`f(0)` is not
specified. Nevertheless, the restriction of :math:`f` to the set of
strictly positive integers is unique (up to extensionnality).

.. raw:: latex

   \begin{Coqsrc}
   Lemma L_spec_unicity alpha f g :
     L_spec alpha f -> L_spec alpha g -> forall k, f (S k) = g (S k).
   \end{Coqsrc}

Abstract properties
~~~~~~~~~~~~~~~~~~~

Let us now prove properties of any function :math:`f` (if any) which
satisfies ``L_spec``. We are looking for properties which could be used
for writing *equations* and prove the correctness of the function
generated by the ``coq-equations`` plug-in. Moreover, they will give us
some examples of :math:`L_\alpha` for small values of :math:`\alpha`.

Our exploration of the :math:`L_\alpha`\ s follows the usual scheme :
transfinite induction, and proof-by-cases : zero, successors and limit
ordinals.

:raw-latex:`\index{maths}{Transfinite induction}`

.. _sect:L-spec-zero:

The ordinal zero
^^^^^^^^^^^^^^^^

The base case is directly a consequence of the specification.

.. raw:: latex

   \begin{Coqsrc}
   Lemma L_zero_inv f : L_spec zero f -> forall k, f (S k) = S k.
   \end{Coqsrc}

.. _sect:L-spec-succ:

Successor ordinals
^^^^^^^^^^^^^^^^^^

Let :math:`\beta` be some ordinal, and assume the arithmetic function
:math:`f` satisfies the specification :math:`(\texttt{L\_spec}\;\beta)`.
Let :math:`k` be any natural number. Any path from
:math:`\texttt{succ}\,\beta` to :math:`0` starting at :math:`k+1` can be
decomposed into a first step from :math:`\texttt{succ}\,\beta` to
:math:`\beta`, then a path from :math:`\beta` at :math:`k+2` to
:math:`0`. By hypothesis the interval :math:`[k+2, f(k+2)-1]` is
:math:`\beta`-mlarge. But the interval :math:`[k+1, f(k+2)-1]` is the
concatenation of the singleton :math:`\{k+1\}` and the interval
:math:`[k+2, f(k+2)-1]`. So, the function :math:`\lambda\,k.\,f(k+1)`
satisfies the specification :math:`\texttt{L\_spec}\,\beta`.

Note that our decomposition of intervals works only if the intervals we
consider are not empty. In order to ensure this property, we assume that
:math:`f\;k` is always greater than :math:`k`, which we note
``S <<= f``, or ``(fun_le S f)`` (defined
in `Prelude.Iterates <../theories/html/hydras.Prelude.Iterates.html#fun_le>`__).

.. raw:: latex

   \begin{Coqsrc}
   Definition fun_le f g  := forall n:nat,  f n <=  g n.
   Infix "<<=" := fun_le (at level 60).
   \end{Coqsrc}

It looks also natural to show that the functions we consider are
strictly monotonous. The section on successor ordinals has thus the
following structure.

.. raw:: latex

   \begin{Coqsrc}
   Section succ.
      Variables (beta : T1) (f : nat -> nat).

      Hypotheses (Hbeta : nf beta)
                 (f_mono : strict_mono f)
                 (f_Sle : S <<= f)
                 (f_ok : L_spec beta f).

      Definition L_succ := fun k => f (S k).

      Lemma L_succ_mono : strict_mono L_succ.

      Lemma L_succ_Sle : S <<= L_succ.
     
      Lemma L_succ_ok : L_spec (succ beta) L_succ.
        
   End succ.

   \end{Coqsrc}

.. _sect:L-spec-lim:

Limit ordinals
^^^^^^^^^^^^^^

Let :math:`\lambda<\epsilon_0` be any limit ordinal. In a similar way as
for successors, we decompose any path from :math:`\lambda` into a first
step to :math:`\canonseq{\lambda}{k}`, followed by a path to :math:`0`.
In the following section, we assume that there exists à correct function
for :math:`\canonseq{\lambda}{k}`, *for any strictly positive
:math:`k`*.

.. raw:: latex

   \begin{Coqsrc}
   Section lim.
     Variables (lambda : T1)
               (Hnf : nf lambda)
               (Hlim : limitb lambda)
               (f : nat -> nat -> nat)
               (H : forall k, L_spec (canonS lambda k) (f (S k))).
     
     Let L_lim k := f k (S k).

     Lemma L_lim_ok : L_spec lambda L_lim.
     
   End lim.
   \end{Coqsrc}

First results
~~~~~~~~~~~~~

Applying the previous lemmas on successors and limit ordinals, we obtain
a few correct implementations of ``(L_spec \alpha)`` for small values of
:math:`\alpha`.

Finite ordinals
^^^^^^^^^^^^^^^

By iterating the functional ``L_succ``, we get a realization of
``(L_spec (fin i))`` for any natural number :math:`i`.

.. raw:: latex

   \begin{Coqsrc}
   Definition L_fin i := fun k => (i + k)%nat.

   Lemma L_fin_ok i : L_spec (fin i) (L_fin i).
   \end{Coqsrc}

The first limit ordinal :math:`\omega`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The lemmas ``L_fin_ok`` and ``L_lim_ok`` allow us to get by
diagonalization a correct implementation for ``L_spec omega``.

.. raw:: latex

   \begin{Coqsrc}
   Definition L_omega k := S (2 * k)%nat.

   Lemma L_omega_ok : L_spec omega L_omega.
   \end{Coqsrc}

Towards :math:`\omega^2`
^^^^^^^^^^^^^^^^^^^^^^^^

We would like to get exact formulas for the ordinal :math:`\omega^2`,
a.k.a. :math:`\phi_0(2)`. This ordinal is the limit of the sequence
:math:`\omega\times i\;(i \in \mathbb{N}`. Thus, we have to study
ordinals of this form, then use our lemma on limits.

The following lemma establishes a path from :math:`\omega\times ( i+1)`
to :math:`\omega \times i`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma path_to_omega_mult (i k:nat) :
     path_to (omega * i) (interval (S k) (2 * (S k))) (omega * (S i)).
   \end{Coqsrc}

Let us consider a path from :math:`\omega\times(i+1)` to :math:`0`
starting at :math:`k+1`. A first “big step” will lead to
:math:`\omega\times i` at :math:`2(k+1)`. If :math:`i>0`, the next jump
leads to :math:`\omega\times(i-1)` at :math:`2(2(k+1))+1`, etc.

The following lemma expresses the length of the mlarge sequences
associated with the finite multiples of :math:`\omega`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma omega_mult_mlarge_0 i  : forall k,
       mlarge  (omega * (S i))
               (interval (S k)
                         (Nat.pred (iterate (fun p =>  S (2 * p)%nat)
                                            (S i)
                                            (S k)))).
   \end{Coqsrc}

Thus, we infer the following result:

*From
Module *\ `Epsilon0.Large_Sets <../theories/html/hydras.Epsilon0.Large_Sets.html#L_omega_mult>`__

.. raw:: latex

   \begin{Coqsrc}
   Definition L_omega_mult i (x:nat) :=  iterate L_omega i x.

   Lemma L_omega_mult_ok (i: nat) :  L_spec (omega * i) (L_omega_mult i).
   \end{Coqsrc}

For instance, let us consider the ordinal :math:`\omega\times 8`, and a
sequence starting at :math:`k=5`.

.. raw:: latex

   \begin{Coqsrc}
   Compute L_omega_mult 8 5.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   = 1535
        : nat
   \end{Coqanswer}

More generally, we prove the equality
:math:`L_{\omega\times i}(k)=2^i\times(k+1)-1`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma L_omega_mult_eqn (i : nat) :
     forall (k : nat),  (0 < k)%nat  ->
                        L_omega_mult i k = (exp2 i * S k - 1)%nat.
   \end{Coqsrc}

By diagonalization, we obtain a simple formula for :math:`L_{\omega^2}`.

.. raw:: latex

   \begin{Coqsrc}
   Definition L_omega_square k := iterate (fun z => S (2 * z)%nat)
                                           k
                                           (S k).

   Lemma L_omega_square_eqn k :
     (0 < k)%nat ->
     L_omega_square k = (exp2 k * (k + 2) - 1)%nat.


   Lemma L_omega_square_ok: L_spec (omega * omega) 
             L_omega_square.

   Compute L_omega_square 8.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
    = 2559
        : nat
   \end{Coqanswer}

Going further
^^^^^^^^^^^^^

Let us consider a last example, “computing” :math:`L_{\omega^3}`. Since
the canonical sequence associated with this ordinal is composed of the
:math:`\omega^2\times i\;(i\in\mathbb{N}_1)`, we have to study this
sequence.

To this end, we prove a generic lemma, which expresses
:math:`L_{\omega^\alpha\times i}` as an iterate of
:math:`L_{\omega^\alpha}`. Note that in this lemma, we assume that the
fonction associated with :math:`\alpha` is stritly monotonous and
greater or equal than the successor function, and prove that
:math:`L_{\omega^\alpha\times i}`\ satisfies the same properties.

.. raw:: latex

   \begin{Coqsrc}
   Section phi0_mult.
    Variables (alpha : T1) (f : nat -> nat).
    Hypotheses (Halpha : nf alpha)
               (f_mono : strict_mono f)
               (f_Sle : S <<= f)
               (f_ok : L_spec (phi0 alpha) f).

    Definition L_phi0_mult i := iterate f i.

   Lemma L_phi0_mult_ok i: 
     L_spec (ocons alpha i zero)  (L_phi0_mult (S i)).

    Lemma L_phi0_mult_smono i: strict_mono (L_phi0_mult i).

    Lemma L_phi0_mult_Sle i: S <<=  L_phi0_mult (S i).

   End phi0_mult.
   \end{Coqsrc}

Let us look at the ordinal :math:`\omega^2\times i`, using
``L_phi0_mult``

.. raw:: latex

   \begin{Coqsrc}
    Definition L_omega_square_times i :=  iterate L_omega_square i.

    Lemma L_omega_square_times_ok i : 
       L_spec (ocons 2 i zero) (L_omega_square_times (S i)).
    Proof.
     apply L_phi0_mult_ok.
     -  auto with T1.
     -  apply L_omega_square_Sle.
     -  apply L_omega_square_ok.
    Qed.
   \end{Coqsrc}

We are now ready to get an exact formula for :math:`L_{\omega^3}`.

.. raw:: latex

   \begin{Coqsrc}
   Definition L_omega_cube  := L_lim  L_omega_square_times .

   Lemma L_omega_cube_ok : L_spec (phi0 3) L_omega_cube.
   \end{Coqsrc}

The function :math:`L_{\omega^3}` is just obtained by diagonalization
upon :math:`L_{\omega^2\times i}`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma L_omega_cube_eqn i : 
      L_omega_cube i = L_omega_square_times i (S i).
   Proof. reflexivity. Qed.
   \end{Coqsrc}

Thus, for instance, :math:`L_{\omega^3}(3)=L_{\omega^2\times 4}(3)`.
Thus, we obtain an exact expression of this number.

.. raw:: latex

   \begin{Coqsrc}
   Lemma L_omega_cube_3_eq:
      let N := exp2 95 in
      let P := (N * 97 - 1)%nat in
      L_omega_cube 3  =  (exp2 P * (P + 2) - 1)%nat.
   \end{Coqsrc}

This number is quite big. Using ``Ocaml``\ ’s ``float`` arithmetic, we
can [under-]approximate it by
:math:`2^{3.8\times10^{30}}\times 3.8\times{10^{30}}`.

.. raw:: latex

   \begin{Coqsrc}
   # let exp2 x = 2.0 ** x;;

   val exp2 : float -> float = <fun>
   #   exp2 95.0 *. 97.0 -. 1.0;;
   - : float = 3.84256588194182037e+30
   # let n = exp2 95.0 ;;
   # let p = n *. 97.0 -. 1.0;;
   val p : float = 3.84256588194182037e+30

   Estimation :
   2 ** (3.84 e+30) * 3.84 e+30.
   \end{Coqsrc}

.. _sect:L-equations:

Using ``Equations``
~~~~~~~~~~~~~~~~~~~

Note that we did not define any function :math:`L_\alpha` *for any
:math:`\alpha<\epsilon_0`* yet. We have got no more than a collection of
proved realizations of :math:`\texttt{L\_spec}\;\alpha` for a few values
of :math:`\alpha`.

:raw-latex:`\index{coq}{Plug-ins!Equations}`

Using the ``coq-equations`` plug-in by M.
Sozeau :raw-latex:`\cite{sozeau:hal-01671777}`, we will now define a
function ``L_`` which maps any ordinal :math:`\alpha<\epsilon_0` to a
proven realization of :math:`\texttt{L\_spec}\;\alpha`. To this end, we
represent ordinals as inhabitants of the type ``E0`` of well-formed
ordinal terms (see Sect :raw-latex:`\vref{sect:E0-def}`). So, we define
a total function ``L_`` of type ``E0 -> nat -> nat``, by transfinite
recursion, considering the usual three cases : :math:`\alpha=0`,
:math:`\alpha` is a successor, :math:`\alpha` is a limit ordinal.

Definition
^^^^^^^^^^

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent` *From
Module *\ `L_alpha <../theories/html/hydras.Epsilon0.L_alpha.html#L_>`__\ *).*

:raw-latex:`\label{Functions:L-alpha}`
:raw-latex:`\index{hydras}{Library Epsilon0!Functions!L\_@L\_ (final step of a minimal path}`

.. raw:: latex

   \begin{Coqsrc}
   From Equations Require Import Equations.
   Require Import ArithRing Lia.

   Instance Olt : WellFounded Lt := Lt_wf.
   Hint Resolve Olt : E0.

   (** Using Coq-Equations for building a function which satisfies 
       Large_sets.L_spec *)

   Equations  L_ (alpha: E0) (i:nat) :  nat  by wf  alpha Lt :=
     L_ alpha  i with E0_eq_dec alpha Zero :=
       { | left _ =>  i ;
         | right nonzero
             with Utils.dec (Limitb alpha) :=
             { | left _ =>  L_ (Canon alpha i)  (S i) ;
               | right notlimit =>  L_ (Pred alpha) (S i)}}.

   Solve All Obligations with auto with E0.
   \end{Coqsrc}

It is worth looking at the answer from ``Equations`` and check (with
``About`` ) all the lemmas this plug-in gives you for free. We show here
only a part of :raw-latex:`\coq`’s anwer.

.. raw:: latex

   \begin{Coqanswer}
   L__obligations_obligation_1 is defined
   L__obligations_obligation_2 is defined
   L__obligations is defined
   L__clause_1 is defined
   L__functional is defined
   L_ is defined
   ...
   L__equation_1 is defined
   L__graph_mut is defined
   L__graph_rect is recursively defined
   L__graph_correct is defined
   L__elim has type-checked, generating 1 obligation
   L__elim is defined
   FunctionalElimination_L_ is defined
   FunctionalInduction_L_ is defined
   \end{Coqanswer}

Sometimes, these automatically generated statements may look cryptic.

.. raw:: latex

   \begin{Coqsrc}
   About L__equation_1.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   L__equation_1 :
   forall (alpha : E0) (i : nat),
   L_ alpha i = L__unfold_clause_1 alpha (E0_eq_dec alpha Zero) i
   \end{Coqanswer}

In most cases, it may be useful to write human-readable paraphrases of
these statements.

.. raw:: latex

   \begin{Coqsrc}
   Lemma L_zero_eqn : forall i, L_ Zero i = i.
   Proof. intro i; now rewrite L__equation_1. Qed.

   Lemma L_lim_eqn alpha i : Limitb alpha -> L_ alpha i =
                                           L_ (Canon alpha i) (S i).

   Lemma L_succ_eqn alpha i :  L_ (Succ alpha) i = L_  alpha (S i).

   Hint Rewrite L_zero_eqn L_succ_eqn : L_rw.
   \end{Coqsrc}

Using these three lemmas as rewrite rules, we can prove more properties
of the functions ``L_\alpha``.

.. raw:: latex

   \begin{Coqsrc}
   Lemma L_finite : forall i k :nat,  L_ i k = (i+k)%nat.  
   (* Proof by induction on i, using L_zero_eqn and L_succ_eqn *)

   Lemma L_omega : forall k, L_ omega%e0 k = S (2 * k)%nat.
   (* Proof using L_finite and L_lim_eqn *)
   \end{Coqsrc}

By well-founded induction on :math:`\alpha`, we prove the following
lemmas:

.. raw:: latex

   \begin{Coqsrc}
   Lemma L_ge_S alpha : alpha <> Zero -> S <<= L_ alpha.

   Theorem L_correct alpha : L_spec (cnf alpha) (L_ alpha).
   \end{Coqsrc}

Please note that the proof of ``L_correct`` applies the lemmas proven in
Sections :raw-latex:`\ref{sect:L-spec-zero}`,
 :raw-latex:`\ref{sect:L-spec-succ}` and
 :raw-latex:`\ref{sect:L-spec-lim}`. Our previous study of ``L_spec``
allowed us to pave the way for the definition by ``Equations`` and the
correctness proof.

Back to hydra battles
^^^^^^^^^^^^^^^^^^^^^

Theorem ``battle_length_std`` of
Module `Hydra.Hydra_Theorems <../theories/html/hydras.Hydra.Hydra_Theorems.html#battle_length_std>`__
relates the length of standard battles with the functions
:math:`L_\alpha`.

.. raw:: latex

   \begin{Coqsrc}
   Theorem battle_length_std (alpha : E0)  :
     alpha <> Zero ->
     forall k, (1 <= k)%nat ->
               battle_length standard k (iota (cnf alpha))
                            (L_ alpha (S k) - k).
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Instead of considering standard paths and battles, consider ``constant'' paths and the corresponding battles. Please use \texttt{Equations} in order to define the function that computes the length of the $k$-path which leads  from $\alpha$ to $0$.
   Prove a few  exact formulas and minoration lemmas.
   \end{project}

.. _sect:hardy:

The Wainer-Hardy hierarchy (functions :math:`H_\alpha`)
-------------------------------------------------------

In order to give a feeling on the complexity of the functions
:math:`L_\alpha`\ s, we compare them with a better known family of
functions, the so called *Wainer-Hardy hierarchy* of fast growing
functions, presented for instance in :raw-latex:`\cite{Promel2013}`.
:raw-latex:`\index{maths}{Rapidly growing functions!Hardy Hierarchy}`

For each ordinal :math:`\alpha` below :math:`\epsilon_0`,
:math:`H_\alpha` is a total arithmetic function, defined by transfinite
recursion on :math:`\alpha`, according to three cases:

:raw-latex:`\index{maths}{Transfinite induction}`

-  If :math:`\alpha=0`, then :math:`H_\alpha (k)= k` for any natural
   number :math:`k`.

-  If :math:`\alpha=\textrm{succ}(\beta)`, then
   :math:`H_\alpha(k)=H_\beta(k+1)` for any :math:`k \in \mathbb{N}`

-  If :math:`\alpha` is a limit ordinal, then
   :math:`H_\alpha(k) = H_{(\canonseq{\alpha}{k+1})}(k)` for any
   :math:`k\in \mathbb{N}`.

Hardy functions in ``Coq``
~~~~~~~~~~~~~~~~~~~~~~~~~~

We define a function ``H_`` of type ``E0 -> nat -> nat`` by transfinite
induction over the type ``E0`` of the well formed ordinals below
:math:`\epsilon_0`.

.. raw:: latex

   \vspace{4pt}

*From
Module *\ `Epsilon0.H_alpha <../theories/html/hydras.Epsilon0.H_alpha.html#H_>`__

:raw-latex:`\index{hydras}{Library Epsilon0!Functions!H\_@H\_ (Hardy hierarchy)}`
:raw-latex:`\index{coq}{Plug-ins!Equations}`
:raw-latex:`\label{Functions:H-alpha}`

.. raw:: latex

   \begin{Coqsrc}
   Equations H_ (alpha: E0) (i:nat) :  nat  by wf  alpha lt :=
     H_ alpha  i with E0_eq_dec alpha Zero :=
       { | left _ =>  i ;
         | right nonzero
             with Utils.dec (Limitb alpha) :=
             { | left _ =>  H_ (Canon alpha (S i))  i ;
               | right notlimit =>  H_ (Pred alpha) (S i)}}. 

   Solve All Obligations with auto with E0.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma H_eq1 : forall i, H_ Zero i = i.
   Proof.   intro i; now rewrite H__equation_1.  Qed.

   Lemma H_eq2 alpha i : Is_Succ alpha ->
                         H_ alpha i = H_ (Pred alpha) (S i).

   Lemma H_eq3 alpha i : Limitb alpha ->
                         H_ alpha i =  H_ (Canon alpha (S i)) i.

   Lemma H_eq4  alpha i :  H_ (Succ alpha) i = H_ alpha (S i).
   \end{Coqsrc}

First steps of the Hardy hierarchy
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Using rewrite rules from ``H_eq1`` to ``H_eq4``, we can explore the
functions :math:`H_\alpha` for some small values of :math:`\alpha`.

.. _finite-ordinals-1:

Finite ordinals
^^^^^^^^^^^^^^^

By induction on :math:`i`, we prove a simple expression of
``H_ (Fin i)``, where ``Fin i`` is the :math:`i`-th finite ordinal.

.. raw:: latex

   \begin{Coqsrc}
   Lemma H_Fin : forall i k: nat,  H_ (Fin i) k = (i+k)%nat.
   Proof with eauto with E0.
     induction i.
     - intros; simpl OF; simpl; autorewrite with H_rw E0_rw ... 
     - intros ;simpl; autorewrite with H_rw E0_rw ... 
       rewrite IHi; lia. 
   Qed.
   \end{Coqsrc}

Multiples of :math:`\omega`
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Since the canonical sequence of :math:`\omega` is composed of finite
ordinals, it is easy to get the formula associated with
:math:`H_\omega`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma H_omega : forall k, H_ Omega k = S (2 * k)%nat.
   Proof with auto with E0.
     intro k; rewrite H_eq3 ...
     - replace (Canon omega (S k)) with (Fin (S k)).
       + rewrite H_Fin; lia.
       +  now autorewrite with E0_rw.
   Qed.
   \end{Coqsrc}

Before going further, we prove a useful rewriting lemma:

.. raw:: latex

   \begin{Coqsrc}
   Lemma H_Plus_Fin alpha : forall i k : nat,
       H_ (alpha + i)%e0 k = H_ alpha (i + k)%nat.
   (* Proof by induction on i *)
   \end{Coqsrc}

Then, we get easily formulas for :math:`H_{\omega+i}`, and
:math:`H_{\omega\times i}` for any natural number :math:`i`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma H_omega_double k : H_ (omega * 2)%e0 k =  (4 * k + 3)%nat.
   Proof.
    rewrite H_lim_eqn; simpl Canon.
    - ochange  (CanonS  (omega * 2)%e0 k)  (omega + (S k))%e0.
     + rewrite H_Plus_Fin, H_omega;  lia.
     -  now compute.
   Qed.

   Lemma H_omega_3 k : H_ (omega * 3)%e0 k = (8 * k + 7)%nat.

   Lemma H_omega_4 k : H_ (omega * 4)%e0 k = (16 * k + 15)%nat.

   Lemma H_omega_i i  : forall k,
       H_ (omega * i)%e0 k = (exp2 i * k + Nat.pred (exp2 i))%nat.
   \end{Coqsrc}

Crossing a new limit, we prove the following equality:

.. math:: H_{\omega^2} (k) = 2 ^ {k+1} \times (k+1) - 1

.

.. raw:: latex

   \begin{Coqsrc}

   Lemma H_omega_sqr : forall k,
       H_ (Phi0  2)%e0 k = (exp2 (S k ) *  S k - 1)%nat.
   Proof.
     intro k; 
      rewrite H_lim_eqn; auto with E0.
     - ochange (Canon (Phi0 2) (S k)) (omega * (S k))%e0.
       +  rewrite H_omega_i; simpl (exp2 (S k)).
          *  rewrite Nat.add_pred_r.
             -- lia. 
             --   generalize (exp2_not_zero k);  lia.
       + cbn; f_equal; lia.
   Qed.
   \end{Coqsrc}

New limits
^^^^^^^^^^

Our next step would be to prove an exact formula for
:math:`H_{\omega^\omega}(k)`. Since the canonical sequence of
:math:`\omega^\omega` is composed of all the :math:`\omega^i`, we first
need to express :math:`H_{\omega^i}` for any natural number :math:`i`.

Let :math:`i` and :math:`k` be two natural numbers. The ordinal
:math:`\canonseq{\omega^(i+1)}{k}` is the product
:math:`\omega^i \times k`, so we need also to consider ordinals of this
form.

#. First, we express :math:`H_{\omega^\alpha \times (i+2)}` in terms of
   :math:`H_{\omega^\alpha \times (i+1)}`.

   .. raw:: latex

      \begin{Coqsrc}
      Lemma H_Omega_term_1 : alpha <> Zero -> forall  k,  
          H_ (Omega_term alpha (S i)) k =
          H_ (Omega_term alpha i) (H_ (Phi0 alpha) k).
      \end{Coqsrc}

#. Then, we prove by induction on :math:`i` that
   :math:`H_{\omega^\alpha \times (i+1)}` is just the :math:`(i+1)`-th
   iterate of :math:`H_{\omega^\alpha}`.

   .. raw:: latex

      \begin{Coqsrc}
      Lemma H_Omega_term (alpha : E0)  :
      alpha <> Zero -> forall i k, 
        H_ (Omega_term alpha i) k = iterate  (H_ (Phi0 alpha)) (S i) k.
      \end{Coqsrc}

#. In particular, we have got a formula for :math:`H_{\omega^{i+1}}`.

   .. raw:: latex

      \begin{Coqsrc}
      Definition H_succ_fun f k := iterate f (S k) k.

      Lemma H_Phi0_succ alpha  : alpha <> Zero -> forall k,
            H_ (Phi0 (Succ alpha)) k = H_succ_fun (H_ (Phi0 alpha)) k. 

      Lemma H_Phi0_Si : forall i k,
            H_ (Phi0 (S i)) k = iterate H_succ_fun i (H_ omega) k. 
      \end{Coqsrc}

We get now a formula for :math:`H_{\omega^3}`:

.. raw:: latex

   \begin{Coqsrc}
   Lemma H_omega_cube : forall k,
       H_ (Phi0 3)%e0 k = iterate (H_ (Phi0 2))  (S k) k.
   Proof.
     intro k; rewrite <-FinS_eq, -> Fin_Succ, H_Phi0_succ; auto.
     compute; injection 1; discriminate.
   Qed.
   \end{Coqsrc}

A numerical example
^^^^^^^^^^^^^^^^^^^

It seems hard to capture the complexity of this function by looking only
at this “exact” formula. Let us consider a simple example, the number
:math:`H_{\omega^3}(3)`.

.. raw:: latex

   \begin{Coqsrc}
   Section H_omega_cube_3.
     
   Let f k :=   (exp2 (S k ) * (S k) - 1)%nat.

   Remark R0 k :  H_ (Phi0 3)%e0 k = iterate f (S k) k.
   \end{Coqsrc}

Thus, the number :math:`H_{\omega^3}(3)` can be written as four nested
applications of :math:`f`.

.. raw:: latex

   \begin{Coqsrc}
   Fact F0 : H_ (Phi0 3) 3 = f (f (f (f 3))).
    rewrite R0; reflexivity. 
   Qed.
   \end{Coqsrc}

In order to make this statement more readable, we can introduce a local
définition.

.. raw:: latex

   \begin{Coqsrc}
   Let N := (exp2 64 * 64 - 1)%nat.
   \end{Coqsrc}

This number looks quite big; let us compute an approximation in
``Ocaml``:

.. raw:: latex

   \begin{Coqsrc}
   # (2.0 ** 64.0 *. 64.0 -. 1.0);; 
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   - : float = 1.1805916207174113e+21
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Fact F1 : H_ (Phi0 3) 3 = f (f N).
   Proof.
    rewrite H_omega_cube_0; reflexivity. 
   Qed.


   Lemma F1_simpl : H_ (Phi0 3) 3 =
                    (exp2 (exp2 (S N) * S N) * (exp2 (S N) * S N) - 1)%nat.

   \end{Coqsrc}

In a more classical writing, this number is displayed as follows:

:raw-latex:`\Large`

.. math:: H_{\omega^3}(3) =  2 ^ {(2 ^ {N + 1} \, (N+1) )}   \,  (2 ^ {N+1} \, ( N +1) ) - 1

We leave as an exercise to determine the best approximation as possible
of the size of this number (for instance its number of digits). For
instance, if we do not take into account the multiplications in the
formula above, we obtain that, in base :math:`2`, the number
:math:`H_{\omega^3}(3)` has at least :math:`2^{10^{21}}` digits. But it
is still an under-approximation !

.. raw:: latex

   \begin{Coqsrc}
   End H_omega_cube_3.
   \end{Coqsrc}

Now, we have got at last an exact formula for :math:`H_{\omega^\omega}`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma H_Phi0_omega : forall k, H_ (Phi0 omega) k =
                                  iterate H_succ_fun  k (H_ omega) k.
   Proof with auto with E0.
     intro k; rewrite H_lim_eqn, <- H_Phi0_Si ...
     -  rewrite CanonS_Canon, CanonS_Phi0_lim;  f_equal ...
   Qed.
   \end{Coqsrc}

Using extensionality of the functional ``iterate``, we can get a closed
formula.

.. raw:: latex

   \begin{Coqsrc}
   Lemma H_Phi0_omega_closed_formula k :
     H_ (Phi0 omega) k =
     iterate (fun (f: nat -> nat) (l : nat) => iterate  f (S l) l)
                  k
                  (fun k : nat => S (2 * k)%nat)
                  k.
   \end{Coqsrc}

Note that this short formula contains two occurences of the functional
``iterate``, the outer one is in fact a second-order iteration (on type
``nat -> nat)`` and the inner one first-order (on type ``nat``).

Abstract properties of Hardy functions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

 :raw-latex:`\label{sect:H-alpha-prop}`

Since pure computation seems to be useless for dealing with expressions
of the form :math:`H_\alpha(k)`, even for small values of :math:`\alpha`
and :math:`k`, we need to prove theorems for comparing
:math:`H_\alpha(k)` and :math:`H_\beta(l)`, in terms of comparison
between :math:`\alpha` and :math:`\beta` on the one hand, :math:`k` and
:math:`l` on the other hand.

But beware of non-theorems! For instance, one could believe that
:math:`H` is monotonous in its first argument. The following proof shows
this is false.

.. raw:: latex

   \begin{Coqsrc}
   Remark H_non_mono1 :
     ~ (forall alpha beta k, (alpha o<= beta)%e0 ->
                             (H_ alpha k <= H_ beta k)%nat).
   Proof.
    intros H ;specialize (H 42 omega 3).
    assert (H0 :(42 o<= omega)%e0) by (repeat split; auto).  
    apply H in H0; rewrite H_Fin, H_omega  in H0; lia.
   Qed.
   \end{Coqsrc}

On the contrary, the fonctions of the Hardy hierarchy have the following
five properties :raw-latex:`\cite{KS81}`: for any
:math:`\alpha < \epsilon_0`,

-  the function :math:`H_\alpha` is strictly monotonous : For all
   :math:`n,p \in\mathbb{N}, n < p \Rightarrow H_\alpha(n)< H_\alpha(p)`.

-  If :math:`\alpha \not= 0`, then for every :math:`n`,
   :math:`n<H_\alpha(n)`.

-  The function :math:`H_\alpha` is pointwise less or equal than
   :math:`H_{\alpha+1}`

-  For any :math:`n\geq 1`, :math:`H_\alpha(n)<H_{\alpha+1}(n)`. *We say
   that :math:`H_{\alpha+1}` dominates :math:`H_\alpha` from :math:`1`*.

-  For any :math:`n` and :math:`\beta`, if
   :math:`\alpha \xrightarrow[n]{} \beta`, then
   :math:`H_\beta(n)\leq H_\alpha(n)`.

These properties are defined in :raw-latex:`\coq{}` in the library
 `Prelude.Iterates <../theories/html/hydras.Prelude.Iterates.html>`__.

:raw-latex:`\index{maths}{Abstract properties of arithmetic functions}`
:raw-latex:`\index{hydras}{Abstract properties of arithmetic functions}`

.. raw:: latex

   \begin{Coqsrc}
   (** ** Abstract properties of arithmetic functions *)

   Definition strict_mono f := forall n p,  n < p -> f n < f p.

   Definition strict_mono1 f := forall n p,  0 < n < p -> f n < f p.

   Definition dominates_from n g f  := forall p, n <= p -> f p < g p.

   Definition dominates_strong g f  := {i : nat | dominates_from i g f}.

   Definition dominates g f := exists i : nat, dominates_from i g f .

   Definition fun_le f g  := forall n:nat,  f n <= g n.

   Infix ">>" := dominates (at level 60).

   Infix ">>s" := dominates_strong (at level 60).

   Infix "<<=" := fun_le (at level 60).
   \end{Coqsrc}

:raw-latex:`\index{maths}{Transfinite induction}`

In :raw-latex:`\coq{}`, we follow the proof in :raw-latex:`\cite{KS81}`.
This proof is mainly a single proof by transfinite induction on
:math:`\alpha` of the conjonction of the five properties. For each
:math:`\alpha`, the three cases : :math:`\alpha=0`, :math:`\alpha` is a
limit, and :math:`\alpha` is a successor are considered. Inside each
case, the five sub-properties are proved sequentially.

.. raw:: latex

   \begin{Coqsrc}
   Section Proof_of_Abstract_Properties.
     Record P (alpha:E0) : Prop :=
       mkP {
           PA : strict_mono (H_ alpha);
           PB : alpha <> Zero -> forall n,  (n < H_ alpha n)%nat;
           PC : H_ alpha <<= H_ (Succ alpha);
           PD : dominates_from 1 (H_ (Succ alpha)) (H_ alpha);
           PE : forall beta n, Canon_plus n alpha beta -> 
                               (H_ beta n <= H_ alpha n)%nat}.


   Theorem P_alpha : forall alpha, P alpha.
     Proof.
       intro alpha; apply well_founded_induction with lt.
      (* rest of proof skipped *)

   Section Proof_of_Abstract_Properties.
   \end{Coqsrc}

Comparison between ``L_`` and ``H_`` 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

By well-founded induction on :math:`\alpha`, we prove that our :math:`L`
hierachy is “almost” the Hardy hierarchy (up to a small shift).

*From
Module *\ `Epsilon0.L_alpha <../theories/html/hydras.Epsilon0.L_alpha.html#H_L_>`__

.. raw:: latex

   \begin{Coqsrc}
    Theorem H_L_ alpha: forall i:nat,  (H_ alpha i <= L_ alpha (S i))%nat.
   \end{Coqsrc}

Back to hydras
^^^^^^^^^^^^^^

The following theorem relates the length of (standard) battles with the
Hardy hierarchy.

*From
Module *\ `Epsilon0.L_alpha <../theories/html/hydras.Epsilon0.L_alpha.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Theorem battle_length_std_Hardy (alpha : E0) :
     alpha <> Zero ->
     forall k , 1 <= k -> exists l: nat,  
          H_ alpha k - k <= l /\
          battle_length standard k (iota (cnf alpha)) l.    
   \end{Coqsrc}

.. _sect:wainer:

The wainer hierarchy (functions :math:`F_\alpha`)
-------------------------------------------------

:raw-latex:`\index{maths}{Rapidly growing functions!Wainer Hierarchy}`

The Wainer hierarchy :raw-latex:`\cite{BW85, Wainer1970, KS81}`, is also
a family of fast growing functions, indexed by ordinals below
:math:`\epsilon_0`, by the following equations:

:raw-latex:`\label{F_equations}`

-  :math:`F_0(i)=i+1`

-  :math:`F_{\beta+1}(i)= (F_\beta)^{(i+1)}(i)`, where :math:`f^{(i)}`
   is the :math:`i`-th iterate of :math:`f`.

-  :math:`F_\alpha(i) = F_{\canonseq{\alpha}{i}} (i)` if :math:`\alpha`
   is a limit ordinal.

A first attempt is to write a definition of :math:`F_\alpha` by
equations, in the same as for :math:`H\_alpha`. We use the functional
``iterate`` defined in
Module `Prelude.Iterates <../theories/html/hydras.Prelude.Iterates.html#iterate>`__.

:raw-latex:`\index{hydras}{Library Prelude!iterate}`

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint iterate {A:Type}(f : A -> A) (n: nat)(x:A) :=
     match n with
     | 0 => x
     | S p => f (iterate  f p x)
     end.
   \end{Coqsrc}

The following code comes from
`../theories/html/hydras.Epsilon0.F_alpha.html <../theories/html/hydras.Epsilon0.F_alpha.html>`__.

:raw-latex:`\index{coq}{Plug-ins!Equations}`

.. raw:: latex

   \begin{Coqsrc}
   Fail Equations F_ (alpha: E0) (i:nat) :  nat  by wf  alpha Lt :=
     F_ alpha  i with E0_eq_dec alpha Zero :=
       { | left _ =>  i ;
         | right nonzero
             with Utils.dec (Limitb alpha) :=
             { | left _ =>  F_ (Canon alpha i)  i ;
               | right notlimit =>  iterate (F_ (Pred alpha))  (S i) i}}.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   The command has indeed failed with message:
   In environment
   alpha : E0
   notlimit : Limitb alpha = false
   nonzero : alpha <> Zero
   i : nat
   F_ : forall x : E0, nat -> x o< alpha -> nat
   The term "F_ (Pred alpha) ?x" has type "Pred alpha o< alpha -> nat"
   while it is expected to have type 
   "Pred alpha o< alpha -> Pred alpha o< alpha"
   (cannot unify "nat" and "Pred alpha o< alpha").
   \end{Coqanswer}

We presume that this error comes from the recursive call of ``F_``
inside an application of ``iterate``. The workaround we propose is to
define first the iteration of ``F_`` as an helper :math:`F^*`, then to
define the function :math:`F` as a “iterating :math:`F^*` once”.

``Equations`` accepts the following definition, relying on lexicographic
ordering on pairs :math:`(\alpha,n)`.

:raw-latex:`\label{sect:F-equations}`

:raw-latex:`\index{coq}{Plug-ins!Equations}`
:raw-latex:`\label{Functions:F-alpha}`
:raw-latex:`\index{maths}{Rapidly growing functions}`
:raw-latex:`\index{hydras}{Library Epsilon0!Functions!F\_@F\_ (Wainer hierarchy)}`

.. raw:: latex

   \begin{Coqsrc}
   Definition call_lt (c c' : E0 * nat) :=
     lexico Lt (Peano.lt) c c'.

   Lemma call_lt_wf : well_founded call_lt.
     unfold call_lt; apply Inverse_Image.wf_inverse_image,  wf_lexico.
     -  apply E0.Lt_wf.
     -  unfold Peano.lt; apply Nat.lt_wf_0. 
   Qed.

   Instance WF : WellFounded call_lt := call_lt_wf.

   Equations  F_star (c: E0 * nat) (i:nat) :  nat by wf  c call_lt :=
       F_star (alpha, 0) i := i;
       F_star (alpha, 1) i
         with E0_eq_dec alpha Zero :=
              { | left _ => S i ;
                | right nonzero
                    with Utils.dec (Limitb alpha) :=
                    { | left _ => F_star (Canon alpha i,1) i ;
                      | right notlimit =>
                        F_star (Pred alpha, S i)  i}};
       F_star (alpha,(S (S n))) i :=
                  F_star (alpha, 1) (F_star (alpha, (S n)) i).

   (* Finally, F_ alpha is defined as its first iterate ! *)

   Definition F_  alpha i := F_star (alpha, 1) i.
   \end{Coqsrc}

It is quite easy to prove that our function ``F_`` satisfies the
equations on page :raw-latex:`\pageref{sect:F-equations}`.
:raw-latex:`\index{hydras}{Library Prelude!iterate}`

.. raw:: latex

   \begin{Coqsrc}
   Lemma F_zero_eqn : forall i, F_ Zero i = S i.

   Lemma F_lim_eqn : forall alpha i,  Limitb alpha ->
                                  F_ alpha i = F_ (Canon alpha i) i.

   Lemma F_succ_eqn : forall alpha i,
       F_ (Succ alpha) i = iterate (F_ alpha) (S i) i.
   \end{Coqsrc}

As for the Hardy functions, we can use these equalities as rewrite rules
for “computing” some values of :math:`F_\alpha(i)`, for small values of
:math:`\alpha`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma LF1 : forall i,  F_ 1 i = S (2 * i).

   Lemma LF2 : forall i, exp2 i * i < F_ 2 i.
   \end{Coqsrc}

Like in Sect :raw-latex:`\ref{sect:H-alpha-prop}`, we prove by induction
the following properties (see :raw-latex:`\cite{KS81}`).

.. raw:: latex

   \begin{Coqsrc}
   Theorem F_alpha_mono alpha : strict_mono (F_ alpha).
    
   Theorem F_alpha_ge_S alpha : forall n, n < F_ alpha n.

   Theorem F_alpha_Succ_le alpha : F_ alpha <<= F_ (Succ alpha).

   Theorem F_alpha_dom alpha : 
        dominates_from 1 (F_ (Succ alpha)) (F_ alpha).

   Theorem F_alpha_beta alpha : 
      forall beta n, Canon_plus n alpha beta -> 
                                           F_ beta n <= F_ alpha n.
   \end{Coqsrc}

As a corollary, we prove the following proposition, p. 284
of :raw-latex:`\cite{KS81}`, which states that the function ``F_`` is
“monotonous” w.r.t. its first argument and “domination”.

   If :math:`\beta<\alpha`, :math:`F_\alpha` dominates :math:`F_\beta`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma F_mono_l: forall alpha beta : E0, 
      beta o< alpha -> dominates (F_ alpha) (F_ beta).
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove the following property:

   \begin{Coqsrc}
   Lemma LF3 : dominates_from  2 (F_ 3) (fun  n => iterate exp2 n n).
   \end{Coqsrc}

   \emph{You may start this exercise with the file
   \url{../exercises/ordinals/F_3.v}.}
   \end{exercise}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove that, for any $\alpha\geq 3$ and $n\geq 2$,
   $F_\alpha(1+n)\geq 2^{F_\alpha(n)}$.



   \emph{You may start this exercise with the file
   \url{../exercises/ordinals/F_3.v}.}
   \end{exercise}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   It is tempting to prove a simple property of monotony 
   of the function \texttt{F\_}.

   \begin{quote}
      Let $\alpha\leq\beta<\epsilon_0$. For any $n\geq 2$,
   $F_\alpha(n)\leq F_\beta(n)$. 
   \end{quote}
   Prove or disprove this statement.

   \emph{You may start this exercise with the file
   \url{../exercises/ordinals/is_F_monotonous.v}.}
   \end{exercise}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}



   Prove that for any $n\geq 2$, $\textrm{Ack}\,\,n\,n\leq  F_\omega(n)$, where \textrm{Ack} is the Ackermann function. Next, prove that $F_\alpha$ is not primitive recursive, for any $\alpha\geq\omega$  (please see Sect.~\vref{sect:ack-not-PR}).
   On the other hand, please show that for any natural number $n$, the function $F_n$ is primitive recursive.
   Thus $F\_alpha$ is primitive recursive if and only if $\alpha$ is finite.

   \emph{You may start this exercise with the file
   \url{../exercises/ordinals/F_omega.v}. Properties of the Ackermann function are studied in 
   \url{../theories/ordinals/MoreAck/Ack.v} and
   \url{../theories/ordinals/MoreAck/AcknotPR.v}.}
   \end{exercise}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Let us quote a theorem from ~\cite{KS81} (page 297).

   \begin{quote}
   \begin{align*}
     H_{\omega^\alpha}(n+1) &\geq F_{\alpha}(n) \quad (n\geq 1, \alpha<\epsilon_0) \\
    F_{\alpha}(n+1) &\geq H_{\omega^\alpha}(n) \quad (n\geq 1, \alpha<\epsilon_0) 
   \end{align*}
   Thus $H_{\omega^\alpha}$ and $F_{\alpha}$ have essentially the same order of growth.

   \end{quote}

    But, before trying to prove these facts, look at the definition of function $H$ in Ketonen and Solovay's paper ! Is it really the same as the definition we quote from Pr{\H o}mel's chapter~\cite{Promel2013},
   whereas \cite{KS81} define $H_\alpha(n)$ as ``the least integer $k$ such that $[n,k]$ is $\alpha$-large''. Thus, it may be useful to adapt the statement above.



   \end{exercise}

.. _chap:schutte:

Kurt Schütte’s axiomatic definition of countable ordinals
=========================================================

In the present chapter, we compare our implementation of the segment
:math:`[0,\epsilon_0)` with a mathematical text in order to “validate”
our constructions. Our reference here is the axiomatic definition of the
set of countable ordinals, in chapter V of Kurt Schütte’s book “Proof
Theory” :raw-latex:`\cite{schutte}`.

.. raw:: latex

   \begin{remark}
   \emph{In all this chapter, the word ``ordinal'' will be considered as a synonymous of
   ``countable ordinal''}  
   \end{remark}

Schütte’s definition of countable ordinals relies on the following three
axioms:

There exists a strictly ordered set , such that

#. :math:`(\mathbb{O},<)` is well-ordered

#. Every bounded subset of :math:`\mathbb{O}` is countable

#. Every countable subset of :math:`\mathbb{O}` is bounded.

Starting with these three axioms, Schütte re-defines the vocabulary
about ordinal numbers: the null ordinal :math:`0`, limits and
successors, the addition of ordinals, the infinite ordinals
:math:`\omega`, :math:`\epsilon_0`, :math:`\Gamma_0`, etc.

This chapter describes an adaptation to :raw-latex:`\coq{}` of Schütte’s
axiomatization. Unlike the rest of our libraries, our library
`hydras.Schutte <../theories/html/hydras.Schutte.Schutte.html>`__ is not
constructive, and relies on several axioms.

-  First, please keep in mind that the set of countable ordinals is not
   countable. Thus, we cannot hope to represent all countable ordinals
   as finite terms of an inductive type, which was possible with the set
   of ordinals strictly less than :math:`\epsilon_0` (resp.
   :math:`\Gamma_0`)

-  We tried to be as close as possible to K. Schütte’s text, which uses
   “classical” mathematics : excluded middle, Hilbert’s :math:`\epsilon`
   (choice) and Russel’s :math:`\iota` (definite description) operators.
   Both operators allow us to write definitions close to the natural
   mathematical language, such as “:math:`\textrm{succ}` is *the* least
   ordinal strictly greater than :math:`\alpha`”

-  Please note that only the library
   `Schutte/*.v <../theories/html/hydras.Schutte.Schutte.html>`__ is
   “contaminated” by axioms, and that the rest of our libraries remain
   constructive.

Declarations and axioms
-----------------------

Let us declare a type ``Ord`` for representing countable ordinals, and a
binary relation ``lt``. Note that, in our development, ``Ord`` is a
type, while the *set* of countable ordinals (called :math:`\mathbb{O}`
by Schütte) is the full set over the type ``Ord``.

:raw-latex:`\label{types:Ord}`

We use Florian Hatat’s library on countable sets, written as he was a
student of *École Normale Supérieure de Lyon*. A set :math:`A` is
countable if there is an injective function from :math:`A` to
:math:`\mathbb{N}` (see Library
```Schutte.Countable`` <../theories/html/hydras.Schutte.Countable.html>`__).

.. raw:: latex

   \vspace{6pt}

*From
Module\ *\ ```Schutte.Schutte_basics`` <../theories/html/hydras.Schutte.Schutte_basics.html>`__

:raw-latex:`\index{hydras}{Library Schutte!Types!Ord}`

.. raw:: latex

   \begin{Coqsrc}
   Parameter Ord : Type.
   Parameter lt : relation Ord.
   Infix "<" := lt : schutte_scope.

   Definition ordinal := Full_set Ord.
   \end{Coqsrc}

Schütte’s first axiom tells that ``lt`` is a well order on the set
``ordinal`` (The class ``WO`` is defined in
Module ```Well_Orders.v`` <../theories/html/hydras.Schutte.Well_Orders.html>`__).

:raw-latex:`\index{hydras}{Library Schutte!Type classes!WO@ WO (well order)}`

:raw-latex:`\label{types:WO}`

.. raw:: latex

   \begin{Coqsrc}
   Variables (M:Type)
            (Lt : relation M).
     
   Class WO : Type:=
       {
         Lt_trans : Transitive  Lt;
         Lt_irreflexive : forall a:M, ~ (Lt a a);
         well_order : forall (X:Ensemble M)(a:M),
             In X a ->
             exists a0:M, least_member  X a0
       }.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
     Axiom AX1 : WO lt.
   \end{Coqsrc}

The second and third axioms say that a subset :math:`X` of
:math:`\mathbb{O}` is (strictly) bounded if and only if it is countable.

.. raw:: latex

   \begin{Coqsrc}
   Axiom AX2 : forall X: Ensemble Ord, 
      (exists a,  (forall y, In X y -> y < a)) ->
      countable X.

   Axiom AX3 : forall X : Ensemble Ord,
                 countable X -> 
                 exists a,  forall y, In X y -> y < a.
   \end{Coqsrc}

``AX2`` and ``AX3`` could have been replaced by a single axiom (using
the ``iff`` connector), but we decide to respect as most as possible the
structure of Schütte’s definitions.

Additional axioms
-----------------

The adaptation of Schütte’s mathematical discourse to
:raw-latex:`\coq{}` led us to import a few axioms from the standard
library. We encourage the reader to consult :raw-latex:`\coq{}`’s FAQ
about the safe use of axioms
https://github.com/coq/coq/wiki/The-Logic-of-Coq#axioms.

Classical logic
^^^^^^^^^^^^^^^

In order to work with classical logic, we import the module
`Coq.Logic.Classical <https://coq.inria.fr/distrib/current/stdlib/Coq.Logic.Classical.html>`__
of :raw-latex:`\coq{}`’s standard library, specifially the following
axiom:

.. raw:: latex

   \begin{Coqsrc}
    Axiom classic : forall P:Prop, P \/ ~P.
   \end{Coqsrc}

Description operators
^^^^^^^^^^^^^^^^^^^^^

In order to respect Schütte’s style, we imported also the library
```Coq.Logic.Epsilon`` <https://coq.inria.fr/distrib/current/stdlib/Coq.Logic.Epsilon.html>`__.
The rest of this section presents a few examples of how Hilbert’s choice
operator and Church’s definite description allow us to write
understandable definitions (close to the mathematical natural language).

The definition of zero
^^^^^^^^^^^^^^^^^^^^^^

According to the definition of a well order, every non-empty subset of
``Ord`` has a least element. Furthermore, this least element is unique.

.. raw:: latex

   \begin{Coqsrc}
   Remark R : exists! z : Ord, least_member lt  ordinal z.
   Proof.
     destruct inh_Ord as [a]; apply (well_order (WO:=AX1)) with a .
     split.
   Qed.
   \end{Coqsrc}

Assume we want to call this element ``zero``.

.. raw:: latex

   \begin{Coqsrc}
   Definition zero : Ord.
   Proof.
     Fail destruct R.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   The command has indeed failed with message:
   Case analysis on sort Type is not allowed for inductive 
   definition ex.
   \end{Coqanswer}

Indeed, the basic logic of :raw-latex:`\coq{}` does not allow us to
eliminate a proof of a proposition :math:`\exists\,x:A,\,P(x)` for
building a term whose type lies in the sort ``Type``. The reasons for
this impossibility are explained in many
documents :raw-latex:`\cite{BC04, chlipalacpdt2011, Coq}`.

Let us import the library ``Coq.Logic.Epsilon``, which contains the
following axiom and lemmas.

.. raw:: latex

   \begin{Coqsrc}
   Axiom epsilon_statement:
     forall (A : Type) (P : A->Prop), inhabited A ->
       {x : A | (exists x, P x) -> P x}.
   \end{Coqsrc}

Hilbert’s :math:`\epsilon` *operator* is derived from this axiom.

.. raw:: latex

   \begin{Coqsrc}
   Definition epsilon (A : Type) (i:inhabited A) (P : A->Prop) : A
     := proj1_sig (epsilon_statement P i).

   Lemma constructive_indefinite_description :
     forall (A : Type) (P : A->Prop),
       (exists x, P x) -> { x : A | P x }.
   \end{Coqsrc}

If we consider the *unique existential* quantifier :math:`\exists!`, we
obtain Church’s *definite description operator*.

.. raw:: latex

   \begin{Coqsrc}
   Definition iota (A : Type) (i:inhabited A) (P : A->Prop) : A
     := proj1_sig (iota_statement P i).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
    Lemma constructive_definite_description :
     forall (A : Type) (P : A->Prop),
       (exists! x, P x) -> { x : A | P x }.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Definition iota_spec (A : Type) (i:inhabited A) (P : A->Prop) :
     (exists! x:A, P x) -> P (iota i P)
     := proj2_sig (iota_statement P i).
   \end{Coqsrc}

Indeed, the operators ``epsilon`` and ``iota`` allowed us to make our
definitions quite close to Schütte’s text. Our libraries
```Schutte.MoreEpsilonIota`` <../theories/html/hydras.Schutte.MoreEpsilonIota.html>`__
and
```Schutte.PartialFun`` <../theories/html/hydras.Schutte.PartialFun.html>`__
are extensions of ``Coq.logic.Epsilon`` for making easier such
definitions. See also an article in french :raw-latex:`\cite{PCiota}`.

.. raw:: latex

   \begin{Coqsrc}
   Class InH (A: Type) : Prop :=
      InHWit : inhabited A.

   Definition some {A:Type} {H : InH A} (P: A -> Prop) := 
      epsilon (@InHWit A H) P.

   Definition the {A:Type} {H : InH A} (P: A -> Prop) := 
      iota (@InHWit A H) P.
   \end{Coqsrc}

In order to use these tools, we had to tell :raw-latex:`\coq{}` that the
type ``Ord`` is not empty:

.. raw:: latex

   \begin{Coqsrc}
   Axiom inh_Ord : inhabited Ord.
   \end{Coqsrc}

We are now able to define ``zero`` as the least ordinal. For this
purpose, we define a function returning the least element of any
[non-empty] subset.

.. raw:: latex

   \begin{Coqsrc}
   Definition the_least {M: Type} {Lt}
              {inh : InH M} {WO: WO Lt} (X: Ensemble M)  : M :=
     the  (least_member  Lt X ).
   \end{Coqsrc}

.. raw:: latex

   \vspace{4pt}

From Module
``` Schutte.Schutte_basics`` <../theories/html/hydras.Schutte.Schutte_basics.html>`__

:raw-latex:`\label{Constants:zero:Ord}`
:raw-latex:`\index{hydras}{Library Schutte!Constants!zero}`

.. raw:: latex

   \begin{Coqsrc}
   Definition zero: Ord :=the_least ordinal.
   \end{Coqsrc}

We want to prove now that zero is less than or equal to any ordinal
number.

.. raw:: latex

   \begin{Coqsrc}
   Lemma zero_le (alpha : Ord) :  zero <= alpha.
   Proof.
     unfold zero, the_least, the; apply iota_ind.
   \end{Coqsrc}

According to the use of the description operator ``iota``, we have to
solve two trivial sub-goals.

#. Prove that there exists a unique least member of ``Ord``

#. Prove that being a least member of ``Ord`` entails the announced
   inequality

.. raw:: latex

   \begin{Coqanswer}
   2 subgoals (ID 155)
     
     alpha : Ord
     ============================
     exists ! x : Ord, least_member lt ordinal x

   subgoal 2 (ID 156) is:
    forall a : Ord, unique (least_member lt ordinal) a -> 
                   a <= alpha
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
     -  apply the_least_unicity, Inh_ord.
     -  destruct 1 as [[_ H1] _]; apply H1; split. 
   Qed.
   \end{Coqsrc}

Remarks on ``epsilon`` and ``iota``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

What would happen in case of a misuse of ``epsilon`` or ``iota`` ? For
instance, one could give a unsatisfiable specification to ``epsilon`` or
a specification for ``iota`` that admits several realizations.

Let us consider an example:

.. raw:: latex

   \begin{Coqbad}
   Module Bad.

    Definition bottom := the_least (Empty_set Ord).
   \end{Coqbad}

.. raw:: latex

   \begin{Coqanswer}
    bottom is defined
   \end{Coqanswer}

Since we won’t be able to prove the proposition
:raw-latex:`\linebreak `\ ``{exists! a: Ord, least_member (Empty_set Ord) a``,
the only properties we would be able to prove about ``bottom`` would be
*trivial* properties, *i.e.*, satisfied by *any* element of type
``Ord``, like for instance ``bottom = bottom``, or ``zero <= bottom``.

.. raw:: latex

   \begin{Coqbad}
   Lemma le_zero_bottom : zero <= bottom. 
   Proof. apply zero_le. Qed.

   Lemma bottom_eq : bottom = bottom.
   Proof. trivial. Qed.

   Lemma le_bottom_zero : bottom <= zero.
   Proof.
      unfold bottom, the_least, the; apply iota_ind.
   \end{Coqbad}

.. raw:: latex

   \begin{Coqanswer}
   2 subgoals (ID 413)
     
   ============================
   exists ! x : Ord, least_member lt (Empty_set Ord) x

   subgoal 2 (ID 414) is:
    forall a : Ord, unique (least_member lt (Empty_set Ord)) a -> 
         a <= zero
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqbad}
   Abort.
   End Bad.
   \end{Coqbad}

In short, using ``epsilon`` and ``iota`` in our implementation of
countable ordinals after Schütte has two main advantages.

-  It allows us to give a *name* (using ``Definition``) two witnesses of
   existential quantifiers (let us recall that, in classical logic, one
   may consider non-constructive proofs of existential statements)

-  By separating definitions from proofs of [unique] existence, one may
   make definitions more concise and readable. Look for instance at the
   definitions of ``zero``, ``succ``, ``plus``, etc. in the rest of this
   chapter.

The successor function
----------------------

The definition of the function ``succ:Ord -> Ord`` is very concise. The
successor of any ordinal :math:`\alpha` is the smallest ordinal strictly
greater than :math:`\alpha`.

:raw-latex:`\label{Functions:succ-sch}`
:raw-latex:`\index{hydras}{Library Schutte!Functions!succ}`

.. raw:: latex

   \begin{Coqsrc}
   Definition succ (alpha : Ord) := the_least (fun beta => alpha < beta).
   \end{Coqsrc}

Using ``succ``, we define the folloing predicates.

.. raw:: latex

   \begin{Coqsrc}
   Definition is_succ (alpha:Ord) := exists beta, alpha = succ beta.

   Definition is_limit (alpha:Ord) := alpha <> zero /\ ~ is_succ alpha.
   \end{Coqsrc}

How do we prove properties of the successor function? First, we make its
specification explicit.

.. raw:: latex

   \begin{Coqsrc}
   Definition succ_spec (alpha:Ord) :=
     least_member   lt (fun z => alpha < z).
   \end{Coqsrc}

Then, we prove that our function ``succ`` meets this specification.

.. raw:: latex

   \begin{Coqsrc}
   Lemma succ_ok : forall alpha,  succ_spec alpha  (succ alpha).
   Proof.
     intros; unfold succ, the_least, the;  apply iota_spec.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   1 subgoal (ID 172)
     
     alpha : Ord
     ============================
     exists ! x : Ord, succ_spec alpha x
   \end{Coqanswer}

We have now to prove that the set of all ordinals strictly greater than
:math:`\alpha` has a unique least element. But the singleton set
:math:`\{\alpha\}` is countable, hence bounded (by the axiom ``AX3``).
Hence; the set :math:`\{\beta\in\mathbb{O}|\alpha < \beta\}` is not
empty and therefore has a unique least element.

The :raw-latex:`\coq{}` proof script is quite short.

.. raw:: latex

   \begin{Coqsrc}
     destruct (@AX3 (Singleton _ alpha)).
     - apply countable_singleton.
     -  unfold succ_spec; apply the_least_unicity;  exists x; intuition.
   Qed.     
   \end{Coqsrc}

We can “uncap” the description operator for proving properties of the
``succ`` function.

.. raw:: latex

   \begin{Coqsrc}
   Lemma lt_succ (alpha : Ord) :  alpha < succ alpha.
   Proof.
     destruct  (succ_ok  alpha);  tauto.
   Qed.

   Hint Resolve lt_succ : schutte.

   Lemma lt_succ_le (alpha beta : Ord):
     alpha < beta -> succ alpha <= beta.
   Proof with eauto with schutte.
     intros  H;  pattern (succ alpha); apply the_least_ok ... 
     exists (succ alpha); red;apply lt_succ ...
   Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma lt_succ_le_2 (alpha beta : Ord):
     alpha < succ beta -> alpha <= beta.

   Lemma succ_mono (alpha beta : Ord):
     alpha < beta -> succ alpha < succ beta.

   Lemma succ_monoR (alpha beta : Ord) :
    succ alpha < succ beta -> alpha < beta.

   Lemma lt_succ_lt (alpha beta : Ord) :
     is_limit beta ->  alpha < beta -> succ alpha < beta.
   \end{Coqsrc}

.. _finite-ordinals-2:

Finite ordinals
---------------

Using ``succ``, it is now easy to define recursively all the finite
ordinals.

:raw-latex:`\label{sect:notation-F-sch}`

.. raw:: latex

   \begin{Coqsrc}
   Reserved Notation "'F' n" (at level 29) .

   Fixpoint finite (i:nat) : Ord :=
     match i with 
               | 0 => zero
               | S i => succ (F i)
     end
   where "'F' i" := (finite i)  : schutte_scope.

   Coercion finite : nat >-> Ord.
   \end{Coqsrc}

The definition of ``omega``
---------------------------

In order to define :math:`\omega`, the first infinite ordinal, we use an
operator which “returns” the least upper bound (if it exists) of a
subset :math:`X\subseteq \mathbb{O}`. For that purpose, we first use a
predicate: (``is_lub D lt X a``) if :math:`a` belongs to :math:`D` and
is the least upper bound of :math:`X` (with respect to *lt*).

.. raw:: latex

   \begin{Coqsrc}
   Definition is_lub (M:Type)
                     (D : Ensemble M)
                     (lt : relation M)
                     (X:Ensemble M)
                     (a:M) :=
      In _ D a  /\ upper_bound  D lt X a  /\
      (forall y, In _ D y -> upper_bound  D lt X y  -> 
                     y = a \/ lt a y).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Definition sup_spec X lambda := is_lub ordinal lt X lambda.

   Definition sup (X: Ensemble Ord) : Ord  := the  (sup_spec X).

   Notation "'|_|' X" := (sup X) (at level 29) : schutte_scope.
   \end{Coqsrc}

Then, we define the function ``omega_limit`` which returns the least
upper bound of the (denumerable) range of any sequence
``s: nat -> Ord``. By ``AX3`` this range is bounded, hence the set of
its upper bounds is not empty and has a least element.

.. raw:: latex

   \begin{Coqsrc}
   Definition omega_limit (s:nat->Ord) : Ord 
     := |_| (seq_range s).
   \end{Coqsrc}

Then we define ``omega`` as the limit of the sequence of finite
ordinals.

:raw-latex:`\label{sect:notation-omega}`

.. raw:: latex

   \begin{Coqsrc}
   Definition _omega := omega_limit finite.

   Notation "'omega'" := (_omega) : schutte_scope.
   \end{Coqsrc}

Among the numerous properties of the ordinal :math:`\omega`, les us
quote the following ones (proved in Module
```Schutte.Schutte_basics`` <../theories/html/hydras.Schutte.Schutte_basics.html#finite_lt_omega>`__)

.. raw:: latex

   \begin{Coqsrc}
   Lemma finite_lt_omega : forall i: nat,  i < omega.

   Lemma lt_omega_finite alpha : Ord) : 
     alpha < omega ->  exists i:nat, alpha =  i.

   Lemma is_limit_omega : is_limit omega.
   \end{Coqsrc}

Ordering functions and ordinal addition
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

After having defined the finite ordinals and the infinite ordinal
:math:`\omega`, we define the sum :math:`\alpha+\beta` of two countable
ordinals. Schütte’s definition looks like the following one:

   “:math:`\alpha+\beta` is the :math:`\beta`-th ordinal greater than or
   equal to :math:`\alpha`”

The purpose of this section is to give a meaning to the construction
“the :math:`\alpha`-th element of :math:`X`” where :math:`X` is any
non-empty subset of :math:`\mathbb{O}`. We follow Schütte’s approach, by
defining the notion of *ordering functions*, a way to associate a unique
ordinal to each element of :math:`X`. Complete definitions and proofs
can be found in Module
```Schutte.Ordering_Functions`` <../theories/html/hydras.Schutte.Ordering_Functions.html>`__
).

.. _definitions-2:

Definitions
~~~~~~~~~~~

A *segment* is a set :math:`A` of ordinals such that, whenever
:math:`\alpha\in A` and :math:`\beta<\alpha`, then :math:`\beta\in A`; a
segment is *proper* if it strictly included in :math:`\mathbb{O}`.

.. raw:: latex

   \begin{Coqsrc}
    Definition segment (A: Ensemble Ord) :=
     forall alpha beta, In A alpha -> beta < alpha -> In A  beta.

   Definition proper_segment (A: Ensemble Ord) :=
     segment A /\ ~ Same_set A ordinal.
   \end{Coqsrc}

Let :math:`A` be a segment, and :math:`B` a subset of :math:`\mathbb{O}`
: an *ordering function for :math:`A` and :math:`B`* is a strictly
increasing bijection from :math:`A` to :math:`B`. The set :math:`B` is
said to be an *ordering segment* of :math:`A`. Our definition in
:raw-latex:`\coq{}` is a direct translation of the mathematical text
of :raw-latex:`\cite{schutte}`.

:raw-latex:`\index{maths}{Ordinal numbers!Ordering functions}`
:raw-latex:`\index{hydras}{Library Schutte!Predicates!ordering function@ordering\_function}`

.. raw:: latex

   \begin{Coqsrc}
   Definition ordering_function (f : Ord -> Ord)(A B : Ensemble Ord) :=
    segment A /\
    (forall a, In A a -> In B (f a)) /\
    (forall b, B b -> exists a, In A a /\ f a = b) /\
    forall a b, In A a -> In A b -> a < b ->  f a < f b.

   Definition ordering_segment (A B : Ensemble Ord) :=
     exists f : Ord -> Ord, ordering_function f A B.
   \end{Coqsrc}

We are now able to associate with any subset :math:`B` of
:math:`\mathbb{O}` its ordering segment and ordering function.

.. raw:: latex

   \begin{Coqsrc}
   Definition the_ordering_segment (B : Ensemble Ord) :=
     the  (fun x => ordering_segment x B).

   Definition ord  (B : Ensemble Ord) := 
     some (fun f => ordering_function f (the_ordering_segment B) B).
   \end{Coqsrc}

Thus (``ord B \;\alpha``) is the :math:`\alpha`-th element of :math:`B`.
Please note that the last definition uses the epsilon-based operator
``some`` and not ``the``. This is due to the fact that we cannot prove
the unicity (w.r.t. Leibniz’ equality) of the ordering function of a
given set. By contrast, we admit the axiom ``Extensionality_Ensembles``,
from the library
`Coq.Sets.Ensembles <https://coq.inria.fr/distrib/current/stdlib/Coq.Sets.Ensembles.html>`__,
so we use the operator ``the`` in the definition of
``the_ordering_segment``.

One of the main theorems of
```Ordering_Functions`` <../theories/html/hydras.Schutte.Ordering_Functions.html#ordering_function_ex>`__
associates a unique segment and a unique (up to extensionality) ordering
function to every subset :math:`B` of :math:`\mathbb{O}`.

.. raw:: latex

   \begin{Coqsrc}
   About ordering_function_ex.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   forall B : Ensemble Ord,
    exists ! S : Ensemble Ord, 
         exists f : Ord -> Ord, ordering_function f S B
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqanswer}
   ordering_function_unicity :
   forall (B S1 S2 : Ensemble Ord) (f1 f2 : Ord -> Ord),
   ordering_function f1 S B ->
   ordering_function f2 S2 B -> 
   fun_equiv f1 f2 S1 S2
   \end{Coqanswer}

Thus, our function ``ord`` which enumerates the elements of :math:`B` is
defined in a non-ambiguous way. Let us quote the following theorems (see
Library
```Schutte.Ordering_Functions`` <../theories/html/hydras.Schutte.Ordering_Functions.html>`__
for more details).

.. raw:: latex

   \begin{Coqsrc}
   Theorem ordering_le : forall f A B,
       ordering_function f A B ->
       forall alpha, In A alpha -> alpha <= f alpha.

   Th_13_5_2 :
   forall (A B : Ensemble Ord) (f : Ord -> Ord),
   ordering_function f A B -> Closed B -> continuous f A B
   \end{Coqsrc}

Ordinal addition
~~~~~~~~~~~~~~~~

We are now ready to define and study addition on the type ``Ord``. The
following definitions and proofs can be consulted in Module
```Schutte.Addition.v`` <../theories/html/hydras.Schutte.Addition.html>`__.

:raw-latex:`\index{hydras}{Library Schutte!Functions!plus}`

.. raw:: latex

   \begin{Coqsrc}
   Definition plus alpha := ord  (ge alpha).
   Notation "alpha + beta " := (plus alpha beta) : schutte_scope.
   \end{Coqsrc}

In other words, :math:`\alpha + \beta` is the :math:`\beta`-th ordinal
greater than or equal to :math:`\alpha`. Thanks to generic properties of
ordering functions, we can show the following properties of addition on
:math:`\mathbb{O}`. First, we prove a useful lemma:

.. raw:: latex

   \begin{Coqsrc}
   Lemma plus_elim (alpha : Ord) :
     forall P : (Ord->Ord)->Prop,
       (forall f: Ord->Ord, 
           ordering_function f ordinal (ge alpha)-> P f) ->
       P (plus alpha).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma alpha_plus_zero (alpha: Ord): alpha + zero = alpha.
   Proof.
    pattern  (plus alpha); apply plus_elim; eauto.
    \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
    1 subgoal (ID 24)
     
     alpha : Ord
     ============================
     forall f : Ord -> Ord,
     ordering_function f ordinal (ge alpha) -> 
     f zero = alpha
    \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
    (* rest of proof skipped *)
    \end{Coqsrc}

The following lemmas are proved the same way.

.. raw:: latex

   \begin{Coqsrc}

   Lemma zero_plus_alpha (alpha : Ord) : zero + alpha = alpha.

   Lemma le_plus_l (alpha beta : Ord) : alpha <= alpha + beta.

   Lemma le_plus_r (alpha beta : Ord) :  beta <= alpha + beta.

   Lemma plus_mono_r (alpha beta gamma : Ord) : 
       beta < gamma -> alpha + beta < alpha + gamma.

   Lemma plus_of_succ (alpha beta : Ord) :
       alpha + (succ beta) = succ (alpha + beta).

   Theorem plus_assoc (alpha beta gamma : Ord) :
     alpha + (beta + gamma) = (alpha + beta) + gamma.

   Lemma one_plus_omega :  1 + omega = omega.

   Lemma finite_plus_infinite (n : nat) (alpha : Ord) :
     omega <= alpha -> n + alpha = alpha.
   \end{Coqsrc}

It isinteresting to compare the proof of these lemmas with the
computational proofs of the corresponding statements in Module
```Epsilon0.T1`` <../theories/html/hydras.Epsilon0.T1.html>`__. For
instance, the proof of the lemma ``one_plus_omega`` uses the continuity
of ordering functions (applied to ``(plus 1)``) and compares the limit
of the :math:`\omega`-sequences :math:`i_{(i \in \mathbb{N})}` and
:math:`(1+i)i_{(i \in \mathbb{N})}`, whereas in the library
``Epsilon0/T1``, the equality :math:`1+\omega=\omega` is just proved
with ``reflexivity``!

Multiplication by a natural number
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The multiplication of an ordinal by a natural number is defined in terms
of addition. This operation is useful for the study of Cantor normal
forms.

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint mult_Sn (alpha:Ord)(n:nat){struct n}: Ord :=
    match n with 
               | 0 => alpha
               | S p => mult_Sn  alpha p + alpha
    end.

   Definition mult_fin_r alpha n :=
     match n with
         0 => zero
       | S p => mult_Sn alpha p
     end.

   Notation "alpha * n" := (mult_fin_r alpha n) : schutte_scope.
   \end{Coqsrc}

The exponential of basis :math:`\omega`
---------------------------------------

In this section, we define the function which maps any
:math:`\alpha\in\mathbb{O}` to the ordinal :math:`\omega^\alpha`, also
written :math:`\phi_0(\alpha)`. It is an opportunity to apply the
definitions and results of the preceding section. Indeed, Schütte first
defines a subset of :math:`\mathbb{O}`: the set of additive principal
ordinals, and :math:`\phi_0` is just defined as the ordering function of
this set.

Additive principal ordinals
~~~~~~~~~~~~~~~~~~~~~~~~~~~

:raw-latex:`\index{maths}{Ordinal numbers!Additive principal ordinals}`
:raw-latex:`\index{hydras}{Library Schutte!Predicates!AP@AP (additive principal ordinals)}`

.. raw:: latex

   \begin{definition}
   A non-zero ordinal  $\alpha$ is said to be \emph{additive principal} if, for all  $\beta<\alpha$, $\beta+\alpha$ is equal to  $\alpha$.
   We call \texttt{AP} the set of additive principal ordinals.

   \end{definition}

:raw-latex:`\noindent`\ *From
Module*\ ```Schutte.AP`` <../theories/html/hydras.Schutte.AP.html>`__

.. raw:: latex

   \begin{Coqsrc}
   Definition AP : Ensemble Ord :=
     fun alpha => 
     zero < alpha /\
     (forall beta, beta < alpha ->  beta + alpha = alpha).
   \end{Coqsrc}

The function ``phi0``
~~~~~~~~~~~~~~~~~~~~~

Let us call :math:`\phi_0` the ordering function of ``AP``. In the
mathematical text, we shall use indifferently the notations
:math:`\omega^\alpha` and\ :math:`\phi_0(\alpha)`.

:raw-latex:`\index{hydras}{Library Schutte!Functions!phi0}`

.. raw:: latex

   \begin{Coqsrc}
   Definition phi0 := ord AP.

   Notation "'omega^'" := phi0 (only parsing) : schutte_scope.
   \end{Coqsrc}

Omega-towers and the ordinal :math:`\epsilon_0`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Using :math:`\phi_0`, we can define recursively the set of finite
omega-towers.

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint omega_tower (i : nat) : Ord :=
     match i with
       0 =>  1
     | S j => phi0 (omega_tower j)
     end.
   \end{Coqsrc}

:raw-latex:`\label{sect:epsilon0-as-limit}` Then, the ordinal
:math:`\epsilon_0` is defined as the limit of the sequence of all finite
towers (a kind of infinite tower).

.. raw:: latex

   \begin{Coqsrc}
   Definition epsilon0 := omega_limit omega_tower.
   \end{Coqsrc}

The rest of our library ``AP`` is devoted to the proof of properties of
additive principal ordinals, hence of the ordering function
:math:`\phi0` and the ordinal :math:`\epsilon_0` (which we could not
express within the type ``T1``).

Properties of the set ``AP``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The set of additive principal ordinals is not empty: it contains at
least the ordinals :math:`1` and :math:`\omega`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma AP_one : In AP 1.

   Lemma AP_omega : In AP omega.
   \end{Coqsrc}

Moreover, :math:`1` is the least principal ordinal and :math:`\omega` is
the second element of ``AP``.

.. raw:: latex

   \begin{Coqsrc}
   Lemma least_AP: least_member  lt AP 1. 

   Lemma omega_second_AP :
     least_member   lt 
                     (fun alpha => 1 < alpha /\ In AP alpha)
                     omega.
   \end{Coqsrc}

The set ``AP`` is *closed* under addition, and unbounded.

.. raw:: latex

   \begin{Coqsrc}
   Lemma AP_plus_closed (alpha beta gamma : Ord): 
        In AP alpha -> beta < alpha -> gamma < alpha ->
        beta + gamma < alpha.

   Theorem AP_unbounded : Unbounded AP.
   \end{Coqsrc}

Finally, ``AP`` is (topologically) *closed* and ordered by the segment
of all countable ordinals.

:raw-latex:`\index{hydras}{Library Schutte!Predicates!Closed}`

.. raw:: latex

   \begin{Coqsrc} 
   Definition Closed (B : Ensemble Ord) : Prop := 
     forall M, Included M B -> Inhabited _ M -> 
                    countable M -> In B (|_| M).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Theorem AP_closed : Closed AP.

   Lemma AP_o_segment :  the_ordering_segment AP = ordinal.
   \end{Coqsrc}

Properties of the function :math:`\phi_0`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The ordering function :math:`\phi_0` of the set ``AP`` is defined on the
full set :math:`\mathbb{O}` and is continuous (Schütte calls such a
function *normal*).

.. raw:: latex

   \begin{Coqsrc}
   Theorem normal_phi0 : normal phi0 AP.
   \end{Coqsrc}

The following properties come from the definition of :math:`\phi_0` as
the ordering function of ``AP``. It may be interesting to compare these
proofs with the computational ones described in Chapter
 :raw-latex:`\ref{chap:T1}`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma AP_phi0 (alpha : Ord) : In AP (phi0 alpha).

   Lemma phi0_zero : phi0 zero =  1.

   Lemma phi0_mono (alpha beta : Ord) :
     alpha < beta ->  phi0 alpha < phi0 beta.

   Lemma phi0_inj (alpha beta : Ord) :
       phi0 alpha = phi0 beta -> alpha = beta.

   Lemma phi0_sup : forall (U: Ensemble Ord),
      Inhabited _ U ->   countable U ->  phi0 (|_| U) = |_| (image U phi0).

   Lemma is_limit_phi0 (alpha : Ord) :
     zero < alpha ->  is_limit (phi0 alpha).

   Lemma omega_eq : omega = phi0 1. 

   Lemma phi0_le (alpha : Ord) : alpha <= phi0 alpha.
   \end{Coqsrc}

Please note that the lemma ``omega_eq`` above, is consistent with the
interpretation of the ordering function :math:`\phi_0` as the
exponential of basis :math:`\omega`. Indeed we could have written this
lemma with our alternative notation:

.. raw:: latex

   \begin{Coqsrc}
    Lemma omega_eq : omega = omega^ 1.
   \end{Coqsrc}

More about :math:`\epsilon_0`
-----------------------------

Let us recall that the limit ordinal :math:`\epsilon_0` cannot be
written within the type ``T1``. Since we are now considering the set of
all countable ordinals, we can now prove some properties of this
ordinal.

We prove the inequality :math:`\alpha<\omega^\alpha` whenever
:math:`\alpha < \epsilon_0`. *Note that this condition was implicit in
Module*\ ```Epsilon0.T1`` <../theories/html/hydras.Epsilon0/T1.html#lt_phi0>`__\ *.*

.. raw:: latex

   \begin{Coqsrc}
   Lemma lt_phi0 (alpha : Ord):
     alpha < epsilon0 -> alpha < phi0 alpha.
   \end{Coqsrc}

The proof is as follows:

#. Since :math:`\alpha<\epsilon_0`, consider the least :math:`i` such
   that :math:`\alpha` is strictly less than the omega-tower of height
   :math:`i`.

#. 

   -  If :math:`i=0`, then the result is trivial (because
      :math:`\alpha=0`)

   -  Otherwise let :math:`i=j+1`; :math:`\alpha` is greater than or
      equal to the omega-tower of height :math:`j`. By monotonicity,
      :math:`\phi_0(\alpha)` is greater than or equal to the omega-tower
      of height :math:`j+1`, thus strictly greater than :math:`\alpha`

Moreover, :math:`\epsilon_0` is the least ordinal :math:`\alpha` that
verifies the equality :math:`\alpha = \omega^\alpha`, in other words the
least fixpoint of the function :math:`\phi_0`.

.. raw:: latex

   \begin{Coqsrc}
   Theorem epsilon0_lfp : least_fixpoint lt phi0 epsilon0.
   \end{Coqsrc}

Critical ordinals
-----------------

:raw-latex:`\index{maths}{Ordinal numbers!Critical ordinals}`
:raw-latex:`\index{hydras}{Library Schutte!Predicates!Cr@Cr (critical ordinals)}`

For any (countable) ordinal :math:`\alpha`, the set
:math:`\textit{Cr}(\alpha)` is inductively defined as follows by Schütte
(p.81 of :raw-latex:`\cite{schutte}`).

   -  :math:`\textit{Cr}(0)` is the set *AP* of additive principal
      ordinals.

   -  If :math:`0<\alpha`, then :math:`\textit{Cr}(\alpha)` is the
      intersection of all the sets of fixpoints of the
      :math:`\textit{Cr}(\beta)` for :math:`\beta<\alpha`.

This definition is translated in :raw-latex:`\coq{}` in Module
```Schutte.Critical`` <../theories/html/hydras.Schutte.Critical.html>`__,
as the least fixpoint of a functional.

.. raw:: latex

   \begin{Coqsrc}
   Definition Cr_fun : forall alpha : Ord,
          (forall beta : Ord, beta < alpha -> Ensemble Ord) ->
           Ensemble Ord 
   := 
      fun (alpha :Ord)
           (Cr : forall beta, 
                   beta < alpha -> Ensemble Ord) 
           (x : Ord) => (
          (alpha = zero /\ AP x) \/
          (zero < alpha /\
           forall beta (H:beta < alpha),
             the_ordering_segment (Cr beta H) x /\ ord (Cr  beta H) x = x)).

   Definition Cr (alpha : Ord) : Ensemble Ord := 
       (Fix  all_ord_acc (fun (_:Ord) => Ensemble Ord) Cr_fun) alpha.
   \end{Coqsrc}

:raw-latex:`\label{sect:phi-schutte}`

.. raw:: latex

   \begin{Coqsrc}
   Definition phi (alpha : Ord) : Ord -> Ord 
       :=  ord (Cr alpha).

   Definition A (alpha : Ord) : Ensemble Ord :=
     the_ordering_segment (Cr alpha).
   \end{Coqsrc}

For instance, we prove that :math:`\textit{Cr}(0)` is the set of
additive principals and that :math:`\epsilon_0` belongs to
:math:`\textit{Cr}(1)`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma Cr_zero_AP :  Cr 0 = AP

   Lemma epsilon0_Cr1 : In (Cr 1) epsilon0.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
    Prove that $\epsilon_0$ is the least element of $\textit{Cr}(1)$.
   \end{exercise}

A flavor of infinity
~~~~~~~~~~~~~~~~~~~~

The family of the :math:`\textit{Cr}(\alpha)`\ s is made of infinitely
many unbounded (hence infinite) sets. Let us quote Lemma 5, p. 82
of :raw-latex:`\cite{schutte}`:

   For all :math:`\alpha`, the set :math:`\textit{Cr}(\alpha)` is closed
   (for the least upper bound of non-empty countable sets) and
   unbounded.

We prove this result by transfinite induction on :math:`\alpha` of both
properties.

The proof is still quite long, by transfinite induction over
:math:`\alpha`.

:raw-latex:`\index{maths}{Transfinite induction}`

.. raw:: latex

   \begin{Coqsrc}
   Section Proof_of_Lemma5.
     Let P (alpha:Ord) := Unbounded (Cr alpha) /\ Closed (Cr alpha).
    
    Lemma Lemma5 : forall alpha, P alpha.
   (* ... *)
    End Proof_of_Lemma5.

   Corollary Unbounded_Cr alpha : Unbounded (Cr alpha).
   Proof.
     now destruct (Lemma5 alpha).
   Qed.

   Corollary Closed_Cr alpha : Closed (Cr alpha).
   Proof.
     now destruct (Lemma5 alpha).
   Qed.
   \end{Coqsrc}

.. _cantor-normal-form-1:

Cantor normal form
------------------

The notion of Cantor normal form is defined for all countable ordinals.
Nevertheless, note that, contrary to the implementation based on type
``T1``, the Cantor normal form of an ordinal :math:`\alpha` may contain
:math:`\alpha` as a sub-term [14]_.

:raw-latex:`\index{maths}{Ordinal numbers!Cantor normal form}`
:raw-latex:`\index{hydras}{Library Schutte!Predicates!is\_cnf\_of@is\_cnf\_of (to be a Cantor normal form of}`

We represent Cantor normal forms as lists of ordinals. A list :math:`l`
is a Cantor normal form of a given ordinal :math:`\alpha` if it
satisfies two conditions:

-  The list :math:`l` is sorted (in decreasing order) w.r.t. the order
   :math:`\leq`

-  The sum of all the :math:`\omega^{\beta_i}` where the :math:`\beta_i`
   are the terms of :math:`l` (in this order) is equal to
   :math:`\alpha`.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`\ *From*\ ```Schutte.CNF`` <../theories/html/hydras.Schutte.CNF.html#cnf_t>`__

.. raw:: latex

   \begin{Coqsrc}
    Definition cnf_t := list Ord.

   Fixpoint eval (l : cnf_t) : Ord :=
     match l with nil => zero
                 | beta :: l' => phi0 beta + eval l'
     end.

   Definition sorted (l: cnf_t) :=
     LocallySorted (fun alpha beta => beta <= alpha) l.

   Definition is_cnf_of (alpha : Ord)(l : cnf_t) : Prop :=
     sorted l /\ alpha = eval l.
   \end{Coqsrc}

:raw-latex:`\index{maths}{Transfinite induction}`

By transfinite induction on :math:`\alpha`, we prove that every
countable ordinal :math:`\alpha` has at least a Cantor normal form.

.. raw:: latex

   \begin{Coqsrc}
   Theorem cnf_exists (alpha : Ord) :
     exists l: cnf_t, is_cnf_of alpha l.
   \end{Coqsrc}

By structural induction on lists, we prove that this normal form is
unique.

.. raw:: latex

   \begin{Coqsrc}
    Lemma cnf_unicity : forall l alpha, 
      is_cnf_of alpha l -> 
      forall l',  is_cnf_of alpha l' -> l=l'.
   Proof.
    induction l.
    (*  ...  *)

   Theorem cnf_exists_unique (alpha:Ord) :
     exists! l: cnf_t, is_cnf_of alpha l.
   \end{Coqsrc}

Finally, the following two lemmas relate :math:`\epsilon_0` with Cantor
normal forms.

If :math:`\alpha<\epsilon_0`, then the Cantor normal form of
:math:`\alpha` is made of ordinals strictly less than :math:`\alpha`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma cnf_lt_epsilon0 : 
    forall l alpha, 
      is_cnf_of alpha l ->  alpha < epsilon0 ->
      Forall (fun beta =>  beta < alpha) l.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Please consider the following statement :

   \begin{Coqsrc}
   Lemma cnf_lt_epsilon0_iff : 
    forall l alpha, 
      is_cnf_of alpha l ->  
      (alpha < epsilon0 <->  Forall (fun beta =>  beta < alpha) l).
   \end{Coqsrc}

   Is it true ?

   \emph{You may start this exercise with the file
   \url{../exercises/ordinals/schutte_cnf_counter_example.v}.}
   \end{exercise}

Finally, the Cantor normal form of :math:`\epsilon_0` is just
:math:`\omega^{\epsilon_0}`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma cnf_of_epsilon0 : is_cnf_of epsilon0 (epsilon0 :: nil).
   Proof.
     split.
     - constructor.  
     - simpl;  now rewrite alpha_plus_zero, epsilon0_fxp.
   Qed.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Implement pages 82 to 85 of~\cite{schutte} (critical, strongly critical, maximal critical ordinals, Feferman's ordinal $\Gamma_0$).
   \end{project}

.. raw:: latex

   \begin{remark}
   The sub-directory \href{../theories/html/hydras.Gamma0.html}%
   {\texttt{theories/Gamma0}} contains an (incomplete, still undocumented) implementation of the set of ordinals below $\Gamma_0$, represented in Veblen normal form. 
   \end{remark}

An embedding of ``T1`` into ``Ord``
-----------------------------------

Our library
```Schutte.Correctness_E0`` <../theories/html/hydras.Schutte.correctness_E0.html>`__
establishes the link between two very different modelizations of ordinal
numbers. In other words, it “validates” a data structure in terms of a
classical mathematical discourse considered as a model. First, we define
a function from ``T1`` into ``Ord`` by structural recursion.

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint inject (t:T1) : Ord :=
    match t with 
        | T1.zero => zero
        | T1.ocons a n b =>  AP.phi0 (inject a) * S n + inject b
    end.  
   \end{Coqsrc}

This function enjoys good commutation properties with respect to the
main operations which allow us to build Cantor normal form.

.. raw:: latex

   \begin{Coqsrc}
   Theorem inject_of_zero : inject T1.zero = zero.

   Theorem inject_of_finite (n : nat):
     inject (T1.fin n) =  n.

   Theorem inject_of_phi0 (alpha : T1):
     inject (phi0 alpha) = AP.phi0 (inject alpha).

   Theorem inject_plus (alpha beta : T1): nf alpha -> nf beta ->
     inject (alpha + beta)%t1 = inject alpha + inject beta.

   Theorem inject_mult_fin_r (alpha : T1)  :
     nf alpha -> forall n:nat , inject (alpha *  n)%t1 =  inject alpha * n.

   Theorem inject_mono (beta gamma : T1) :
     T1.lt  beta gamma -> 
     T1.nf beta -> T1.nf gamma -> 
     inject beta < inject gamma.

   Theorem inject_injective (beta gamma : T1) : nf beta -> nf gamma ->
     inject beta = inject gamma -> beta = gamma.
   \end{Coqsrc}

Finally, we prove that ``inject`` is a bijection from the set of all
terms of ``T1`` in normal form to the set ``members epsilon0`` of the
elements of ``Ord`` strictly less than :math:`\epsilon_0`.

.. raw:: latex

   \begin{Coqsrc}
   Theorem inject_lt_epsilon0 (alpha : T1):
         inject alpha < epsilon0.

   Theorem embedding : 
        fun_bijection (nf: Ensemble T1)  (members epsilon0) inject.
    \end{Coqsrc}

.. _remarks-1:

Remarks
~~~~~~~

Let us recall that the library
```Schutte`` <../theories/html/hydras.Schutte.Schutte.html>`__ depends
on five *axioms* and lies explicitly in the framework of classical logic
with a weak version of the axiom of choice (please look at the
documentation of
```Coq.Logic.ChoiceFacts`` <https://coq.inria.fr/distrib/current/stdlib/Coq.Logic.ChoiceFacts.html>`__).
Nevertheless, the other modules:
```Epsilon0`` <../theories/html/hydras.Epsilon0.Epsilon0.html>`__,
```Hydra`` <../theories/html/hydras.Hydra.Hydra.html>`__, et
```Gamma0`` <../theories/html/hydras.Gamma0.Gamma0.html>`__ do not
import any axioms and are really constructive.

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   There is no construction of ordinal multiplication in~\cite{schutte}. 
   It would be interesting to derive this operation from Schütte's axioms,
   and prove its consistence with multiplication in ordinal notations for 
   $\epsilon_0$ and $\Gamma_0$.
   \end{project}

Related work
------------

In :raw-latex:`\cite{grimm:hal-00911710}`, José Grimm establishes the
consistency between our ordinal notations (``T1`` and ``T2`` (Veblen
normal form) and his implementation of ordinal numbers after Bourbaki’s
set theory.

The Ordinal :math:`\Gamma_0` (first draft)
==========================================

*This chapter and the files it presents are still very incomplete,
considering the impressive properties of
:math:`\Gamma_0` :raw-latex:`\cite{Gallier91}`. We hope to add new
material soon, and accept contributions!*

.. _introduction-2:

Introduction
------------

We present a notation system for the ordinal :math:`\Gamma_0`, following
Chapter V, Section 14 of :raw-latex:`\cite{schutte}`: “A notation system
for the ordinals :math:`<\Gamma_0`”. We try to be as close as possible
to Schütte’s text and usual practices of :raw-latex:`\coq{}`
developments.

The ordinal :math:`\Gamma_0` is defined in Section 13 of
 :raw-latex:`\cite{schutte}` as the least *strongly critical ordinal*.
It is widely known as the *Feferman-Schütte ordinal*.

Section V, 13 of :raw-latex:`\cite{schutte}` defines *strongly critical*
and *maximal :math:`\alpha`-critical* ordinals:

-  :math:`\alpha` is strongly critical if :math:`\alpha` is
   :math:`\alpha`-critical,

-  :math:`\gamma` is maximal :math:`\alpha`-critical if :math:`\gamma`
   is :math:`\alpha`-critical, and, for all :math:`\xi>\alpha`,
   :math:`\gamma` is not :math:`\xi`-critical.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`\ *From*\ ```Schutte.Critical`` <../theories/html/hydras.Schutte.Critical.html#strongly_critical>`__

.. raw:: latex

   \begin{Coqsrc}
   Definition strongly_critical alpha := In (Cr alpha) alpha.

   Definition maximal_critical alpha : Ensemble Ord :=
     fun gamma =>
       In (Cr alpha) gamma /\
       forall xi, alpha < xi -> ~ In (Cr xi) gamma.

   Definition Gamma0 := the_least strongly_critical.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Prove that a (countable)  ordinal $\alpha$ is strongly critical iff 
   $\phi_\alpha(0)=\alpha$ (Theorem 13.13 of~\cite{schutte} ). 
   \end{project}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Prove that the set of strongly critical ordinals is unbounded and closed (Theorem 13.14 of~\cite{schutte} ). Thus this set is not empty,  hence has a least element. Otherwise, the definition of $\Gamma_0$ above would be useless.
   \end{project}

In the present version of this development, we only study
:math:`\Gamma_0` as a notation system, much more powerful than the
ordinal notation for :math:`\epsilon_0`.

The type ``T2`` of ordinal terms
--------------------------------

The notation system for ordinals less than :math:`\gamma_0` comes from
the following theorem of :raw-latex:`\cite{schutte}`, where
:math:`\psi\,\alpha` is the ordering function of the set of maximal
:math:`\alpha`-critical ordinals.

:raw-latex:`\index{hydras}{Library Gamma0!Types!T2}`

   Any ordinal :math:`\not= 0` which is not strongly critical can be
   expressed in terms of :math:`+` and :math:`\psi`.

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   This theorem is not formally proved in this development yet. It should be!
   \end{project}

Like in Chapter :raw-latex:`\ref{chap:T1}`, we define an inductive type
with two constructors, one for :math:`0`, the other for the construction
:math:`\psi(\alpha,\beta)\times(n+1)+\gamma`, adapting a
Manolios-Vroon-like notation :raw-latex:`\cite{Manolios2005}` to *Veblen
normal forms*. :raw-latex:`\label{types:T2}`

:raw-latex:`\noindent`\ *From*\ ```Gamma0.T2`` <../theories/html/hydras.Gamma0.T2.html#T2>`__

.. raw:: latex

   \begin{Coqsrc}
   (**  [gcons alpha beta n gamma] is : [psi(alpha,beta)*(S n)+ gamma]  *)

   Inductive T2 : Set :=
   | zero : T2
   | gcons : T2 -> T2  -> nat -> T2 -> T2.

   Notation "[ alpha , beta ]" := (gcons alpha beta 0 zero)
                                    (at level 0): t2_scope.
   \end{Coqsrc}

.. raw:: latex

   \centering

.. figure:: epsilon0.jpg
   :alt: Veblen normal form
   :name: fig:gamma0
   :width: 11cm

   Veblen normal form

Like in chapter :raw-latex:`\ref{chap:T1}`, we get familiar with the
type ``T2`` by recognising simple constructs like finite ordinals,
:math:`\omega`, etc., as inhabitants of ``T2``.

.. raw:: latex

   \begin{Coqsrc}
   Notation  "'one'"  := [zero,zero] : T2_scope.

   (** The (n+1)-th finite ordinal *)
   Notation "'FS' n" := (gcons zero zero n zero) (at level 10) : T2_scope.

   (** the [n]-th ordinal  *)
   Definition fin (n:nat) := match n with 0 => zero | S p => FS p end.

   Notation "'omega'"  := [zero,one] : T2_scope.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Notation "'epsilon0'"  := ([one,zero]) : T2_scope.

   Definition epsilon alpha := [one, alpha].
   \end{Coqsrc}

How big is :math:`\Gamma_0`?
----------------------------

Let us define a strict order on type ``T2``. The following definition is
an adaptation of Schütte’s, taking into account the multiplications by a
natural number (inspired by :raw-latex:`\cite{Manolios2005}`, and also
present in ``T1``).

:raw-latex:`\label{sect:t2-lt-def}`

.. raw:: latex

   \begin{Coqsrc}
   Inductive lt : T2 -> T2 -> Prop :=
   | (* 1 *) 
    lt_1 : forall alpha beta n gamma,  zero t2< gcons alpha beta n gamma
   | (* 2 *)
    lt_2 : forall alpha1 alpha2 beta1 beta2 n1 n2 gamma1 gamma2, 
                   alpha1 t2< alpha2 ->
                   beta1 t2< gcons alpha2 beta2 0 zero ->
                  gcons alpha1 beta1 n1 gamma1 t2<
                  gcons alpha2 beta2 n2 gamma2
   | (* 3 *)
    lt_3 : forall alpha1  beta1 beta2 n1 n2 gamma1 gamma2, 
                  beta1 t2< beta2 ->
                  gcons alpha1 beta1 n1 gamma1 t2<
                  gcons alpha1 beta2 n2 gamma2

   | (* 4 *)
    lt_4 : forall alpha1 alpha2 beta1 beta2 n1 n2 gamma1 gamma2, 
                  alpha2 t2< alpha1 ->
                  [alpha1, beta1] t2< beta2 ->
                  gcons alpha1 beta1 n1 gamma1 t2<
                  gcons alpha2 beta2 n2 gamma2

   | (* 5 *)
   lt_5 : forall alpha1 alpha2 beta1 n1 n2 gamma1 gamma2, 
                  alpha2 t2< alpha1 ->
                  gcons alpha1 beta1 n1 gamma1 t2<
                  gcons alpha2  [alpha1, beta1] n2 gamma2

   | (* 6 *)
   lt_6 : forall alpha1 beta1  n1  n2 gamma1 gamma2,  (n1 < n2)%nat ->
                                       gcons alpha1 beta1 n1 gamma1 t2< 
                                       gcons alpha1 beta1 n2 gamma2

   | (* 7 *)
     lt_7 : forall alpha1 beta1 n1   gamma1 gamma2,  gamma1 t2< gamma2 ->
                                         gcons alpha1 beta1 n1 gamma1 t2<
                                         gcons alpha1 beta1 n1 gamma2
   where  "o1 t2< o2" := (lt o1 o2): T2_scope.

   Hint Constructors lt : T2.
   \end{Coqsrc}

Seven constructors! In order to get accustomed with this definition, let
us look at a small set of examples, covering all the constructors of
``lt``.

.. _examples-1:

Examples
~~~~~~~~

Proof of :math:`0<\epsilon_0`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. raw:: latex

   \begin{Coqsrc}
   Example Ex1: 0 t2< epsilon0.
   Proof.  constructor 1. Qed.
   \end{Coqsrc}

Proof of :math:`\omega<\epsilon_0`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. raw:: latex

   \begin{Coqsrc}
   Example Ex2: omega t2< epsilon0.
   Proof. info_auto with T2. (* uses lt_1 and lt_2 *) Qed.
   \end{Coqsrc}

Proof of :math:`\psi(\omega,8)\times 13+56 < \psi(\omega,8)\times 13+57`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. raw:: latex

   \begin{Coqsrc}
   Example Ex3: gcons omega 8 12 56 t2<  gcons omega 8 12 57.
   Proof.
     constructor 7; constructor 6; auto with arith.
   Qed.
   \end{Coqsrc}

Proof of :math:`\epsilon_0<\psi(2,1)`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. raw:: latex

   \begin{Coqsrc}
   Example Ex4: epsilon0 t2< [2,1].
   Proof.
      constructor 2; auto with T2.
      - constructor 6; auto with arith.
   Qed.
   \end{Coqsrc}

Proof of :math:`\psi(2,1)<\psi(2,3)`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. raw:: latex

   \begin{Coqsrc}
   Example Ex5 : [2,1] t2< [2,3].
   Proof.
     constructor 3; auto with T2.
     - constructor 6; auto with arith.
   Qed.
   \end{Coqsrc}

.. _sect:ex6-first-proof:

Proof of :math:`\psi(1,0)\times 13+ \omega < \psi(0,\psi(2,1))`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. raw:: latex

   \begin{Coqsrc}
   Example Ex6 : gcons 1 0 12 omega t2< [0,[2,1]].
   Proof.
     constructor 4.
     - constructor 1.
     - constructor 2.
       + constructor 6; auto with arith.
       + constructor 1.
   Qed.
   \end{Coqsrc}

Proof of :math:`\psi(2,1)\times 43 + \epsilon_0 < \psi(1,\psi(2,1))`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. raw:: latex

   \begin{Coqsrc}
   Example Ex7 : gcons 2 1 42 epsilon0 t2< [1, [2,1]].
   Proof.
    constructor 5.
    constructor 6; auto with arith.
   Qed.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Write a tactic that solves automatically goals of the form (\texttt{$\alpha$ t2< $\beta$}), where $\alpha$ and $\beta$ are closed terms of type \texttt{T2}.
   \end{project}

Veblen normal form
------------------

.. raw:: latex

   \begin{definition}
     A term of the form $\psi(\alpha_1,\beta_1)\times n_1+ \psi(\alpha_2,\beta_2)\times n_2+\dots+\psi(\alpha_k,\beta_k)\times n_k$ is said to be in
    \emph{[Veblen] normal form} if for every $i<n$, $\psi(\alpha_i,\beta_i)<\psi(\alpha_{i+1},\beta_{i+1})$, all the $\alpha_i$ and $\beta_i$ are in normal form, and all the $n_i$ are strictly positive integers.
   \end{definition}

.. raw:: latex

   \begin{Coqsrc}
   Inductive nf : T2 -> Prop :=
   | zero_nf : nf zero
   | single_nf : forall a b n, nf a ->  nf b -> nf (gcons a b n zero)
   | gcons_nf : forall a b n a' b' n' c', 
                         [a', b'] t2< [a, b]  -> 
                         nf a -> nf b -> 
                         nf(gcons a' b' n' c')-> 
                         nf(gcons a b n (gcons a' b' n' c')).
   \end{Coqsrc}

Let us look at some positive examples (we have to prove some inversion
lemmas before proving counter-examples).

.. raw:: latex

   \begin{Coqsrc}
   Lemma  nf_fin i : nf (fin i).
   Proof.
     destruct i.
     - auto with T2.
     - constructor 2; auto with T2.
   Qed.

   Lemma nf_omega : nf omega.
   Proof.  compute; auto with T2. Qed.

   Lemma nf_epsilon0 : nf epsilon0.
   Proof. constructor 2; auto with T2. Qed.

   Lemma nf_epsilon : forall alpha, nf alpha -> nf (epsilon alpha).
   Proof. compute; auto with T2. Qed.

   Example Ex8: nf (gcons 2 1 42 epsilon0).
   Proof.
     constructor 3; auto with T2.
     - apply Ex4.
     - apply nf_fin.
     - apply nf_fin.
   Qed.
   \end{Coqsrc}

Length of a term
~~~~~~~~~~~~~~~~

The notion of *term length* is introduced by Schütte as a helper for
proving (at least) the *trichotomy* property and transitivity of the
strict order ``lt`` on ``T2``. These properties are proved by induction
on length.

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint nbterms (t:T2) : nat :=
     match t with zero => 0
                | gcons a b n v => (S n) + nbterms v
     end.

   Fixpoint t2_length (t:T2) : nat :=
     match t  with 
       zero => 0
     | gcons a b n v => 
          nbterms (gcons a b n v) + 
         2 * (Max.max (t2_length a)
                                 (Max.max (t2_length b) 
                                                   (t2_length_aux v)))
     end
   with t2_length_aux (t:T2) : nat :=
    match t with 
    | zero => 0
     | gcons a b n v =>
              Max.max (t2_length a) 
                               (Max.max (t2_length b) (t2_length_aux v))
    end.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Compute t2_length (gcons 2 1 42 epsilon0).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
    = 48 : nat
   \end{Coqanswer}

Trichotomy
~~~~~~~~~~

*Trichotomy* is another name for the well-known property of decidable
total ordering (like Standard Library’s ``Compare_dec.lt_eq_lt_dec``).

We first prove by induction on :math:`l` the following lemma:

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`\ *From*\ ```Gamma0.Gamma0`` <../theories/html/hydras.Gamma0.Gamma0#tricho_aux>`__

.. raw:: latex

   \begin{Coqsrc}
   Lemma tricho_aux (l: nat) : forall t t' :T2,
         t2_length t + t2_length t' < l  ->
         {t t2< t'} + {t = t'} + {t' t2<  t}.
   \end{Coqsrc}

Then we get our version of ``lt_eq_lt_dec``, and derive a comparison
function;

.. raw:: latex

   \begin{Coqsrc}
   Definition lt_eq_lt_dec (t t': T2) : {t t2< t'}+{t = t'}+{t' t2<  t}.
   Proof.
     eapply tricho_aux.
     eapply lt_n_Sn.
   Defined.

   Definition compare (t1 t2 : T2) : comparison := 
     match lt_eq_lt_dec t1 t2 with
     | inleft (left _) => Lt
     | inleft (right _) => Eq
     | inright _ => Gt
     end.
   \end{Coqsrc}

With the help of ``compare``, we get a boolean version of ``nf`` (being
in Veblen normal form).

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint nfb (alpha : T2) : bool :=
     match alpha with
       zero => true
     | gcons a b n zero => andb (nfb a) (nfb b)
     | gcons a b n ((gcons a' b' n' c') as c) =>
       match compare [a', b'] [a, b] with
              Lt => andb (nfb a) (andb (nfb b) (nfb c))
              | _ => false
              end
   end.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Compute compare (gcons 2 1 42 epsilon0) [2,2].
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
      = Lt
        : comparison
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Compute nfb  (gcons 2 1 42 epsilon0).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
      = true
        : bool
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Compute nfb (gcons 2 1 42 (gcons 2 2 4 epsilon0)).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
      = false
        : bool
   \end{Coqanswer}

.. raw:: latex

   \begin{remark}
   The connexion between the predicate \texttt{nf} and the relation \texttt{lt} on one part, and the functions \texttt{nfb} and \texttt{compare} on the other, is expressed by the following lemmas:

   \begin{Coqsrc}
   Lemma nfb_equiv gamma : nfb gamma = true <-> nf gamma.

   Lemma compare_correct alpha beta :
     CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
                 (compare alpha beta).
   \end{Coqsrc}

   The function \texttt{compare} helps to make easier proofs of inequalities of
   closed terms of type \texttt{T2}.

   First, we prove a lemma:

   \begin{Coqsrc}
   Lemma compare_Lt : forall alpha beta, compare alpha beta = Lt -> 
                                            alpha t2< beta.
   Proof.
     intros alpha beta; destruct (compare_correct alpha beta);
       trivial; discriminate. 
   Qed.
   \end{Coqsrc}

   Then, we give another version of the proof of Sect.~\vref{sect:ex6-first-proof}.

   \begin{Coqsrc}
   Example Ex6 : gcons 1 0 12 omega t2< [0,[2,1]].
   Proof. now apply compare_Lt. Qed.
   \end{Coqsrc}

   \end{remark}

Main functions on ``T2``
------------------------

.. _successor-2:

Successor
~~~~~~~~~

The successor function is defined by structural recursion.

:raw-latex:`\noindent`\ *From*\ ```Gamma0.T2`` <../theories/html/hydras.Gamma0.T2.html#succ>`__

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint succ (a:T2) : T2 :=
    match a with zero => one
                | gcons zero zero n c => fin (S (S n))
                | gcons a b n c => gcons a b n (succ c)
    end.
   \end{Coqsrc}

.. _addition-1:

Addition
~~~~~~~~

Like for Cantor normal forms (see
Sect. :raw-latex:`\ref{sect:infix-plus-T1}`), the definition of addition
in ``T2`` requires comparison between ordinal terms.

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint plus (t1 t2 : T2) {struct t1}:T2 :=
     match t1,t2 with
     |  zero, y  => y
     |  x, zero => x
     |  gcons a b n c, gcons a' b' n' c' =>
        (match compare (gcons a b 0 zero)
                       (gcons a' b' 0 zero) with
         | Lt => gcons a' b' n' c'
         | Gt => gcons a b n (c + gcons a' b' n' c')
         | Eq => gcons a b (S(n+n')) c'
         end)
     end
   where "alpha + beta" := (plus alpha beta): T2_scope.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Example Ex7 : 3 + epsilon0 = epsilon0.
   Proof. trivial. Qed.
   \end{Coqsrc}

The Veblen function :math:`\phi`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The enumeration function of critical ordinals, presented in
Sect. :raw-latex:`\vref{sect:phi-schutte}`, is recursively defined in
type ``T2``.

.. raw:: latex

   \begin{Coqsrc}
   Definition  phi (alpha beta : T2) : T2 :=
     match beta with zero => [alpha, beta] 
                | [b1, b2] => 
                  (match compare alpha b1
                   with Datatypes.Lt => [b1, b2 ]
                   | _ => [alpha,[b1, b2]]
                   end)
                | gcons b1 b2 0 (gcons zero zero  n zero) => 
                  (match compare alpha b1
                   with  Datatypes.Lt => 
                         [alpha, (gcons b1 b2 0 (fin n))]
                   | _ =>  [alpha, (gcons b1 b2 0 (fin (S n)))]
                   end)
                | any_beta => [alpha, any_beta]
     end.
   \end{Coqsrc}

Despite its complexity, the function ``phi`` is well adapted to proofs
by simplification or computation.

.. raw:: latex

   \begin{Coqsrc}
   Example Ex8:  phi 1 (succ epsilon0) = [1, [1,0] + 1].
   Proof. reflexivity. Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   (**  All epsilons are fixpoints of phi 0 *)

   Theorem epsilon_fxp : forall beta, phi zero (epsilon beta) =
                                      epsilon beta.
   Proof. reflexivity. Qed.

   Theorem epsilon0_fxp : epsilon0 = phi zero epsilon0.
   Proof. apply epsilon_fxp. Qed.
   \end{Coqsrc}

The relation between the constructor :math:`\psi` and the function
:math:`\phi` is studied in :raw-latex:`\cite{schutte}`, and partially
implemented in this development. *Please contribute!*

For instance, the following theorem states that, if :math:`\gamma` is
the sum of a limit ordinal :math:`\beta` and a finite ordinal :math:`n`,
and :math:`\beta` is a fixpoint of :math:`\phi(\alpha)`, then
:math:`\psi(\alpha,\gamma)=\phi_\alpha(\gamma+1)`.

.. raw:: latex

   \begin{Coqanswer}
   phi_psi :
   forall (alpha : T2) [beta gamma : T2] [n : nat],
   nf gamma ->
   limit_plus_fin beta n gamma ->
   phi alpha beta = beta -> [alpha, gamma] = phi alpha (succ gamma)
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Example Ex9 : [zero, epsilon 2 + 4] = phi 0 (epsilon 2 + 5).
   Proof. trivial. Qed.
   \end{Coqsrc}

On the other hand, :math:`\phi` can be expressed in terms of
:math:`\psi`.

.. raw:: latex

   \begin{Coqanswer}
   phi_of_psi:
     forall a b1 b2 : T2,
     phi a [b1, b2] = (if lt_ge_dec a b1 then [b1, b2] else [a, [b1, b2]])
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Example Ex10 : phi omega [epsilon0, 5] = [epsilon0, 5].
   Proof. reflexivity. Qed.
   \end{Coqsrc}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Please study a way to pretty print ordinal terms in Veblen normal form (see Section~\vref{sect:ppT1}).
   \end{project}

An ordinal notation for :math:`\Gamma_0`
----------------------------------------

In order to consider type ``T2`` as an ordinal notation, we have to
build an instance of class ``ON`` (See Definition
page :raw-latex:`\pageref{types:ON}`).

First, we define a type that contains only terms in Veblen normal form,
and redefine ``lt`` and ``compare`` by delegation (see for comparison
the construction of type ``E0`` in
Sect. :raw-latex:`\vref{sect:E0-def}`).

.. raw:: latex

   \begin{Coqsrc}
   Module G0.

   Class G0 := mkg0 {vnf : T2; vnf_ok : nfb vnf}.

   Definition lt (alpha beta : G0) := T2.lt (@vnf alpha) (@vnf beta).

   Definition compare alpha beta := Gamma0.compare (@vnf alpha) (@vnf beta).
   \end{Coqsrc}

Then, we prove that ``lt`` is a well-founded strict order and that the
function ``compare`` is correct.

.. raw:: latex

   \begin{Coqsrc}
   Instance lt_sto : StrictOrder lt.

   Lemma lt_wf : well_founded lt.

   Lemma compare_correct alpha beta :
     CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
                 (compare alpha beta).

   Instance Gamma0: ON lt  compare.
   Proof.
     split.
     - apply lt_sto.
     - apply lt_wf. 
     - apply compare_correct.
   Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{remark}
   The proof of \texttt{lt\_wf} has been written by \'Evelyne Contejean, using her library on the recursive path ordering (see also remark~\vref{remark:a3pat}).
   \end{remark}

:raw-latex:`\index{hydras}{Projects}`

.. raw:: latex

   \begin{project}
   Prove that \texttt{Epsilon0} (page~\pageref{instance-epsilon0})
   is a sub-notation system of \texttt{Gamma0}.

   Prove that the implemantations of \texttt{succ}, \texttt{+}, $\phi_0$, etc.
   are compatible in both notation systems.

   Note that a function \texttt{T1\_inj} from \texttt{T1} to \texttt{T2} has already been defined. It may help to complete the task.



   \noindent\emph{From \href{../theories/html/hydras.Gamma0.T2.html\#T1_to_T2}%
   {\texttt{Gamma0.T2}}}
   \begin{Coqsrc}
   (* injection from T1 *)

   Fixpoint T1_to_T2 (alpha :T1) : T2 :=
     match alpha  with
     | T1.zero => zero
     | T1.ocons a n b => gcons zero (T1_to_T2 a) n (T1_to_T2 b)
     end.
   \end{Coqsrc}

   \end{project}

.. raw:: latex

   \begin{project}
   Prove that the notation system \texttt{Gamma0} is a correct implementation 
   of the segment $[0,\Gamma_0)$ of the set of countable ordinals.
   \end{project}

.. [1]
   This class is also called *standard* in this document (text and
   proofs). The *replication factor* of the hydra is exactly :math:`i`
   at the :math:`i`-th round of the battle (see
   Sect :raw-latex:`\vref{sect:replication-def}`).

.. [2]
   :math:`h'` will be called “the wounded part of the hydra” in the
   subsequent text. In Figures :raw-latex:`\vref{fig:Hy2}` and
    :raw-latex:`\vref{fig:Hy4}`, this sub-hydra is displayed in red.

.. [3]
   Let us recall that, if the chopped-off head was at distance 1 from
   the foot, the replication factor is meaningless.

.. [4]
   In other words, the replication factor at this round is equal to
   :math:`4`.

.. [5]
   This appellation is ours. If there is a better one, we will change
   it.

.. [6]
   The name of this file means “the ordinal :math:`\omega` is too small
   for proving the termination of [free] hydra battles”. In effect, the
   elements of :math:`\omega`, considered as a set, are just the natural
   numbers (see next chapter for more details)

.. [7]
   We use the mathematical notation :math:`[a,b)` for the interval
   :math:`\{x|a\leq x < b\}`.

.. [8]
   In classical mathematics, we would say that there is no infinite
   sequence :math:`a_1>a_2> \dots a_n> a_{n+1}\dots` in :math:`A`. In
   contrast, :raw-latex:`\coq`’s standard library contains an inductive
   definition of a predicate ``Acc`` which allows us to write
   constructive proofs of accessibility (See
   `Coq.Init.Wf <https://coq.inria.fr/distrib/current/stdlib/Coq.Init.Wf.html>`__).

.. [9]
   With respect to the measure :math:`m`.

.. [10]
   Ordinal addition is formally defined a little later
   (page :raw-latex:`\ref{sect:infix-plus-T1}`)

.. [11]
   With a small difference: the :math:`0`-th term of the canonical
   sequence is not the same in our development as
   in :raw-latex:`\cite{KS81}`.

.. [12]
   This restriction did not prevent us from proving all the main
   theorems of :raw-latex:`\cite{KS81, KP82}`. Nevertheless, in a future
   version of this development, we may define
   :math:`\canonseq{\alpha}{0}` exactly as in :raw-latex:`\cite{KS81}`.
   But we are afraid this would be done at the cost of making some
   proofs much more complex.

.. [13]
   This condition allows us to ignore paths which end by a lot of
   useless :math:`0`\ \ s.

.. [14]
   This would prevent us from trying to represent Cantor normal forms as
   finite trees (like in Sect. :raw-latex:`\ref{sec:T1-inductive-def}`)
