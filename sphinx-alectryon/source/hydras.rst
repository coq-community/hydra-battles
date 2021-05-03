.. raw:: latex

   \maketitle

.. raw:: latex

   \tableofcontents

Introduction
------------

.. raw:: latex

   \vspace{16pt}

Generalities
~~~~~~~~~~~~

Proof assistants are excellent tools for exploring the structure of
mathematical proofs, studying which hypotheses are really needed, and
which proof patterns are useful and/or necessary. Since the development
of a theory is represented as a bunch of computer files, everyone is
able to read the proofs with an arbitrary level of detail, or to play
with the theory by writing alternate proofs or definitions.

Among all the theorems proved with the help of proof assistants like
:raw-latex:`\coq{}` :raw-latex:`\cite{Coq,BC04}`,
:raw-latex:`\hol{}` :raw-latex:`\cite{HOL}`,
:raw-latex:`\isabelle{}` :raw-latex:`\cite{isabelle}`, etc., several
statements and proofs share some interesting features:

-  Their statements are easy to understand, even by non-mathematicians

-  Their proof requires some non-trivial mathematical tools

-  Their mechanization on computer presents some methodological
   interest.

This is obviously the case of the four-color
theorem :raw-latex:`\cite{fourcolors}` and the Kepler
conjecture :raw-latex:`\cite{flyspeck2015}`. We do not mention
impressive works like the proof of the odd-order theorem
 :raw-latex:`\cite{oddorderthm}`, since understanding its statement
requires a quite good mathematical culture.

In this document, we present two examples which seem to have the above
properties.

-  Hydra games (a.k.a. *Hydra battles*) appear in an article published
   in 1982 by two mathematicians: L. Kirby and J.
   Paris :raw-latex:`\cite{KP82}`: *Accessible Independence Results for
   Peano Arithmetic*. Although the mathematical contents of this paper
   are quite advanced, the rules of hydra battles are very easy to
   understand. There are now several sites on Internet where you can
   find tutorials on hydra games, together with simulators you can play
   with. See, for instance, the page written by Andrej
   Bauer :raw-latex:`\cite{bauer2008}`.

   Hydra battles, as well as Goodstein
   Sequences :raw-latex:`\cite{goodstein_1944, KP82}` are a nice way to
   present complex termination problems. The article by Kirby and Paris
   presents a proof of termination based on ordinal numbers, as well as
   a proof that this termination is not provable in Peano arithmetic. In
   the book dedicated to J.P.  Jouannaud :raw-latex:`\cite{HommageJPJ}`,
   N. Dershowitz and G. Moser give a thorough survey on this
   topic :raw-latex:`\cite{Dershowitz2007}`.

   Let us underline the analogy between hydra battles and interactive
   theorem proving. Hercules is the user (you!), and hydra’s heads are
   the sub-goals: you may think that applying a tactic would solve a
   sub-goal, but it results often in the multiplication of such tasks.

-  In the second part, we are interested in computing :math:`x^n` with
   the least number of multiplications as possible. We use the notion of
   *addition
   chains* :raw-latex:`\cite{brauer1939,DBLP:journals/ipl/BerstelB87}`,
   to generate efficient certified exponentiation functions.

Warning:
        

This document is *not* an introductory text for :raw-latex:`\coq{}`, and
there are many aspects of this proof assistant that are not covered. The
reader should already have some basic experience with the
:raw-latex:`\coq{}` system. The Reference Manual and several tutorials
are available on :raw-latex:`\coq{}` page :raw-latex:`\cite{Coq}`. First
chapters of textbooks like *Interactive Theorem Proving and Program
Development* :raw-latex:`\cite{BC04}`, *Software
Foundations* :raw-latex:`\cite{SF}` or *Certified Programming with
Dependent Types*  :raw-latex:`\cite{chlipalacpdt2011}` will give you the
right background.

.. _sect:trust-in-proofs:

Trust in our proofs
^^^^^^^^^^^^^^^^^^^

Unlike mathematical literature, where definitions and proofs are spread
over many articles and books, the whole proof is now inside your
computer. It is composed of the ``.v`` files you downloaded and parts of
:raw-latex:`\coq`’s standard library. Thus, there is no ambiguity in our
definitions and the premises of the theorems. Furthermore, you will be
able to navigate through the development, using your favourite text
editor or IDE, and some commands like ``Search``, ``Locate``, etc.

Assumed redundancy
^^^^^^^^^^^^^^^^^^

It may often happen that several definitions of a given concept, or
several proofs of a given theorem are possible. If all the versions
present some interest, we will make them available, since each one may
be of some methodological interest (by illustrating some tactic of proof
pattern, for instance). We use :raw-latex:`\coq`’s module system to make
several proofs of a given theorem co-exist in our libraries (see also
Sect :raw-latex:`\vref{sect:alt-proofs}`). After some discussions of the
pros and cons of each solution, we develop only one of them, leaving the
others as exercises or projects (i.e., big or difficult exercises). In
order to discuss which assumptions are really needed for proving a
theorem, we will also present several aborted proofs. Of course, do not
hesitate to contribute nice proofs or alternative definitions!

It may also happen that some proof looks to be useless, because the
proven theorem is a trivial consequence of another (proven too) result.
For instance, let us consider the three following statements:

#. There is no measure into :math:`\mathbb{N}` for proving the
   termination of all hydra battles
   (Sect :raw-latex:`\vref{omega-case}`).

#. There is no measure into the interval [1]_ interval
   :math:`\{x\$[0,\omega^2)` for proving the termination of all hydra
   battles (Sect :raw-latex:`\vref{omega2-case}`).

#. There is no measure into :math:`[0,\mu)` for proving the termination
   of all hydra battles, for any :math:`\mu<\epsilon_0`
   (Sect:raw-latex:`\vref{sec:free-battles-case}`).

Obviously, the third theorem implies the second one, which implies the
first one. So, theoretically, a library would contain only a proof of
:math:`(3)` and remarks for :math:`(2)` and :math:`(1)`. But we found it
interesting to make all the three proofs available, allowing the reader
to compare their common structure and notice their technical
differences. In particular, the proof of :math:`(3)` uses several
non-trivial combinatorial properties of ordinal numbers up to
:math:`\epsilon_0` :raw-latex:`\cite{KS81}`, whilst :math:`(1)` and
:math:`(2)` use simple properties of :math:`\mathbb{N}` and
:math:`\mathbb{N}^2`.

About logic
^^^^^^^^^^^

Most of the proofs we present are *constructive*. Whenever possible, we
provide the user with an associated function, which she or he can apply
in :raw-latex:`\gallina{}` or :raw-latex:`\ocaml{}` in order to get a
“concrete” feeling of the meaning of the considered theorem. For
instance, in Chapter :raw-latex:`\vref{chap:ketonen}`, the notion of
*limit ordinal* is made more “concrete” thanks to a function ``canon``
which computes every item of a sequence which converges on a given limit
ordinal :math:`\alpha`. This simply typed function allows the
user/reader to make her/his own experimentations. For instance, one can
very easily compute the :math:`42`-nd item of a sequence which converges
towards :math:`\omega^{\omega^\omega}`.

Except in the ``Schutte`` library, dedicated to an axiomatic
presentation of the set of countable ordinal numbers, all our
development is axiom-free, and respects the rules of intuitionistic
logic. Note that we also use the ``Equations``
plug-in :raw-latex:`\cite{sozeau:hal-01671777}` in the definitition of
several rapidly growing hierarchy of functions, in
Chap. :raw-latex:`\ref{chap:alpha-large}`. This plug-in imports several
known-as-harmless axioms.

:raw-latex:`\index{coq}{Commands!Print Assumptions}`

At any place of our development, you may use the
``Print Assumptions ident`` command in order to verify on which axiom
the theorem *ident* may depend. The following example is extracted from
Library `hydras.Epsilon0.F_alpha <../theories/html/hydras.Epsilon0.F_alpha.html>`__,
where we use the ``coq-equations`` plug-in (see
Sect. :raw-latex:`\vref{sect:wainer}`).

.. raw:: latex

   \begin{Coqsrc}
   About F_zero_eqn.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   F_zero_eqn : forall i : nat, F_ Zero i = S i
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Print Assumptions F_zero_eqn. 
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   Axioms:
   FunctionalExtensionality.functional_extensionality_dep
     : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
       (forall x : A, f x = g x) -> f = g
   Eqdep.Eq_rect_eq.eq_rect_eq
     : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
       x = eq_rect p Q x p h
   \end{Coqanswer}

Typographical Conventions
^^^^^^^^^^^^^^^^^^^^^^^^^

Quotations from our :raw-latex:`\coq{}` source are displayed as follows:

.. raw:: latex

   \begin{Coqsrc}
    Definition square (n:nat) := n * n.

    Lemma square_double : exists n:nat, n + n = square n.
    Proof.
       exists 2. 
     \end{Coqsrc}

Answers from :raw-latex:`\coq{}` (including sub-goals, error messages,
etc.) are displayed in slanted style with a different background color.

.. raw:: latex

   \begin{Coqanswer}
    1 subgoal, subgoal 1 (ID 5)
     
     ============================
      2 + 2 = square 2
      
    \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
      reflexivity.
   Qed.
    \end{Coqsrc}

In general, we do not include full proof scripts in this document. The
only exceptions are very short proofs (*e.g.* proofs by computation, or
by application of automatic tactics). Likewise, we may display only the
important steps on a long interactive proof, for instance, in the
following lemma (:raw-latex:`\vref{lemma:L-2_6-1}`):

.. raw:: latex

   \begin{Coqsrc}
   Lemma Lemma2_6_1 (alpha : T1) :  
     nf alpha -> forall beta,  beta t1< alpha  ->
     {n:nat | const_pathS n alpha beta}.
   Proof.
     transfinite_induction alpha.
     (* ... *)
   \end{Coqsrc}

The reader may consult the full proof scripts with Proof General or
CoqIDE, for instance.

Active Links
^^^^^^^^^^^^

The links which appear in this pdf document lead are of three possible
kinds of destination:

-  Local links to the document itself,

-  External links, mainly to :raw-latex:`\coq`’s page,

-  Local links to pages generated by ``coqdoc``. According to the
   current makefile (through the commands ``make html`` and
   ``make pdf``), we assume that the page generated from a library
   ``XXX/YYY.v`` is stored as the relative address
   ``../theories/html/hydras.XXX.YYY.html`` (from the location of the
   pdf) Thus, active links towards our :raw-latex:`\coq{}` modules may
   be incorrect if you got this ``pdf`` document otherwise than by
   compiling the distribution available in
   https://github.com/coq-community/hydra-battles.

.. _sect:alt-proofs:

Alternative or bad definitions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Finally, we decided to include definitions or lemma statements, as well
as tactics, that lead to dead-ends or too complex developments, with the
following coloring. Bad definitions and encapsulation in modules called
``Bad``, ``Bad1``, etc.

.. raw:: latex

   \begin{Coqbad}
   Module Bad.

   Definition double (n:nat)  := n + 2.
    
   Lemma lt_double : forall n:nat, n < double  n.
   Proof.
      unfold double; lia.
   Qed.

   End Bad.
   \end{Coqbad}

Likewise, alternative, but still unexplored definitions will be
presented in modules ``Alt``, ``Alt1``, etc. Using these definitions is
left as an implicit exercise.

.. raw:: latex

   \begin{Coqalt}
   From hydras Require Import Iterates.
   Module Alt.
     Definition double (n : nat) := iterate S n n.
   End Alt.
   \end{Coqalt}

.. raw:: latex

   \begin{Coqsrc}
   Lemma alt_double_ok n : Nat.double n = Alt.double n.
   Proof.
     unfold Alt.double, Nat.double; induction n; cbn.
     -  trivial.
     -  rewrite <- iterate_rw, iterate_S_eqn, <- IHn; lia.
   Qed.
   \end{Coqsrc}

.. _sec:orgheadline4:

How to install the libraries
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-  The present distribution has been checked with version 8.13.0 of the
   Coq proof assistant, with the plug-ins ``coq-paramcoq``,
   ``coq-equations`` and ``coq-mathcomp-algebra``.

-  Please refer to `the README file of the
   project <https://github.com/coq-community/hydra-battles#readme>`__

Comments on exercises and projects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Although we do not plan to include complete solutions to the exercises,
we think it would be useful to include comments and hints, and
questions/answers from the users. In constrast, “projects” are supposed,
once completed, to be included in the repository.

Please consult the sub-directory ``exercises/`` of the project (in
construction).

.. _sec:orgheadline5:

Acknowledgements
~~~~~~~~~~~~~~~~

Many thanks to Yves Bertot, Évelyne Contejean, Florian Hatat, David
Ilcinkas, Pascal Manoury, Karl Palmskog, Sylvain Salvati, Alan Schmitt
and Théo Zimmerman for their help on the elaboration of this document,
and to the members of the *Formal Methods* team and the *Coq working
group* at laBRI for their helpful comments on oral presentations of this
work.

Many thanks also to the Coq development team, Yves Bertot, and the
members of the *Coq Club* for interesting discussions about the
:raw-latex:`\coq{}` system and the Calculus of Inductive Constructions.

The author of the present document wishes to express his gratitude to
the late Patrick Dehornoy, whose talk was determinant for our desire to
work on this topic. I owe my interest in discrete mathematics and their
relation to formal proofs and functional programming to Srecko Brlek.
Equally, there is W. H. Burge’s book “*Recursive Programming
Techniques*”  :raw-latex:`\cite{burge}` which was a great source of
inspiration.

Contributions
^^^^^^^^^^^^^

Yves Bertot made nice optimizations to algorithms presented in
Chapter :raw-latex:`\ref{chapter-powers}`. Évelyne Contejean contributed
libraries on the recursive path ordering (*rpo*) for proving the
well-foundedness of our representation of :math:`\epsilon_0` and
:math:`\Gamma_0`. Florian Hatat proved many useful lemmas on countable
sets, which we used in our adaptation of Schütte’s formalization of
countable ordinals. Pascal Manoury is integrating the ordinal
:math:`\omega^\omega` into our hierarchy of ordinal notations.

The formalization of primitive recursive functions was originally a part
of Russel O’Connor’s work on Gödel’s incompleteness
theorems :raw-latex:`\cite{OConnor05}`.

:raw-latex:`\label{sec:orgheadline2}`

Any form of contribution is welcome: correction of errors (typos and
more serious mistakes), improvement of Coq scripts, proposition of
inclusion of new chapters, and generally any comment or proposition that
would help us. The text contains several *projects* which, when
completed, may improve the present work. Please do not hesitate to bring
your contribution, for instance with Github’s proof requests and issues.
Thank you in advance!

Hydras and ordinals
===================

.. raw:: latex

   \include{part-hydras}

.. raw:: latex

   \include{chapter-primrec}

A few certified algorithms
==========================

.. raw:: latex

   \include{chapter-powers}

Appendices
==========

.. raw:: latex

   \bibliographystyle{alpha}

Index and tables
----------------

:raw-latex:`\Large `\ **In progress** This index is currently under
reorganization for a few days. We aplologize for its incompleteness!

.. raw:: latex

   \printindex{coq}{Coq, plug-ins and standard library}

.. raw:: latex

   \printindex{maths}{Mathematical notions and algorithmics}

.. raw:: latex

   \printindex{hydras}{Library hydras: Ordinals and hydra battles}

.. raw:: latex

   \printindex{primrec}{Library hydras.Ackermann: Primitive recursive functions}

.. raw:: latex

   \printindex{additions}{Library additions: Addition chains}

Main notations
~~~~~~~~~~~~~~

.. raw:: latex

   \centering

.. raw:: latex

   \begin{threeparttable}
       \caption{Ordinals and ordinal notations}
   \begin{tabular}{|r | c|c|c|c|l|}
   \hline
   Name & Gallina&Math& Description& Page \\\hline
   \texttt{lt : T1->T1->Prop}& lt alpha beta & $\alpha < \beta$& strict order on type \texttt{T1} \tnote{1} & \pageref{Predicates:lt-T1}\\
   \texttt{LT: T1->T1->Prop}& alpha o< beta & $\alpha < \beta$& strict order on type \texttt{T1}   \tnote{2} & \pageref{Predicates:LT-T1}\\
   \texttt{Lt : E0->E0->Prop} & alpha o< beta & $\alpha < \beta$& strict order on type \texttt{E0} \tnote{3} & \pageref{Predicates:Lt-E0} \\
   \texttt{nf: T1->Prop} & \texttt{nf alpha} && alpha is in Cantor normal form & \pageref{Predicates:nf-T1}\\
    \texttt{on\_lt} & \texttt{alpha o< beta}&$\alpha<\beta$& ordinal inequality \tnote{4} & \pageref{sect:on-lt-notation}\\
    \texttt{on\_le} & \texttt{alpha o<= beta}&$\alpha\leq\beta$& ordinal inequality & \pageref{sect:on-lt-notation}\\
   \texttt{plus} & \texttt{alpha + beta} & $\alpha + \beta$ & ordinal addition & \pageref{sect:infix-plus-T1}, \dots\\
   \texttt{oplus} & \texttt{alpha o+ beta} & $\alpha \oplus \beta$ & Hessenberg sum & \pageref{sect:infix-oplus} \\

   F & \texttt{F $n$} & $n$ & The $n$-th finite ordinal &  
   \pageref{sect:notation-F}, \pageref{sect:notation-F-sch}\\ 
   FS & \texttt{FS $n$} & $n+1$ & The $n+1$-th finite ordinal  \tnote{5} &  
   \pageref{sect:notation-FS}\\ 
   omega & \texttt{omega} & $\omega$ &   the first infinite ordinal   & \pageref{sect:notation-omega}, \pageref{sect:omega-T1}, \pageref{sect:omega-notation2}, \dots\\
   phi0     & \texttt{phi0 alpha} & $\phi_0(\alpha),\; \omega^\alpha$&exponential of base $\omega$ & \pageref{sect:notation-phi0}\\

   \hline
   \end{tabular}
   \begin{tablenotes}
     \item[1] This order is total, but not well-founded, because of not well formed terms.
   \item[2] Restriction of \texttt{lt} to terms in normal form; this order is partial, but well-founded.
   \item[3] This order is total \emph{and} well-founded.
   \item [4]
   Some notations may belong to several scopes. For instance, ``\texttt{o<}'' is
   bound in \texttt{ON\_scope}, \texttt{E0\_scope}, \texttt{t1\_scope}, etc., and locally in several libraries.
     \item [5] Note that there exist also various coercions from \texttt{nat} to types of ordinal. Depending on the current scope and  \coq's syntactic analysis algorithm, \texttt{F} may be left implicit.
   \end{tablenotes}
   \end{threeparttable}

.. raw:: latex

   \vspace{4pt}

.. raw:: latex

   \begin{threeparttable}
       \caption{hydra battles}
   \begin{tabular}{|c|c|c|c|l|}
   \hline
   Name & Gallina&Math& Description& Page \\\hline
   \texttt{round} & \texttt{h -1-> h'} & & one round of a battle & \pageref{sect:infix-round} \\
   \texttt{rounds} & \texttt{h -+-> h'} & & one or more  rounds of a battle & \pageref{sect:infix-rounds} \\
   \texttt{round\_star} & \texttt{h -*-> h'} & & any number of rounds of a battle & \pageref{sect:infix-rounds} \\
   \hline
   \end{tabular}

   %\begin{tablenotes}
   %\end{tablenotes}

     \end{threeparttable}

.. raw:: latex

   \centering

.. raw:: latex

   \begin{threeparttable}
       \caption{Addition chains}
   \begin{tabular}{|c|c|c|c|l|}
   \hline
   Name & Gallina&Math& Description& Page \\\hline
   \texttt{Mult} & \texttt{$z$ <--- $x$ times $y$} & & monadic notation & \pageref{monadic-mult} \\
   \hline
   \end{tabular}

   %\begin{tablenotes}
   %\end{tablenotes}

     \end{threeparttable}

.. [1]
   We use the notation :math:`[a,b)` for denoting the set of ordinals
   greater or equal than :math:`a` and strictly less than :math:`b`.
