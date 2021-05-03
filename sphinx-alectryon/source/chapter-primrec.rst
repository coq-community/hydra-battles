******************************
Primitive recursive functions
******************************

Introduction
------------

The definition of primitive recursive functions we use comes from Russel
O’Connors formalization in :raw-latex:`\coq{}` of Gödel’s incompleteness
theorems :raw-latex:`\cite{OConnor05}`, now hosted in the
``theories/ordinals/Ackermann`` directory.

This chapter contains some comments on Russel’s library, as well as a
few extensions. Contributions (under the form of comments, new examples
or exercises) are welcome!.

First look at the Ackermann library
-----------------------------------

O’Connor’s library on Gödel’s incompleteness theorems contains a little
more than 45K lines of scripts. The part dedicated to primitive
recursive functions and Peano arithmetics is 32K lines long and is
originally structured in 38 modules. Thus, we propose a slow exploration
of this library, through examples and exercises. Our additions to the
original library are stored in the directory
``theories/ordinals/MoreAck``. In particular, the
library `MoreAck.AckNotPR <../theories/html/hydras.MoreAck.AckNotPR.html>`__
contains the well-known proof that the Ackermann function is not
primitive recursive (see Section :raw-latex:`\vref{sect:ack-not-PR}`).

Basic definitions
-----------------

:raw-latex:`\index{maths}{Primitive recursive functions}`

The formal definition of primitive recursive functions lies in the
library
`Ackermann.primRec <../theories/html/hydras.Ackermann.primRec.html>`__,
with preliminary definitions in
`Ackermann.extEqualNat <../theories/html/hydras.Ackermann.extEqualNat.html>`__
and `Ackermann.misc <../theories/html/hydras.Ackermann.misc.html>`__.

Functions of arbitrary arity
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Library ``primRec`` allows us to consider primitive functions on
``nat``, with any number of arguments, in curried form. This is made
possible in
`Ackermann.extEqualNat <../theories/html/hydras.Ackermann.extEqualNat.html>`__
by the following definition:

:raw-latex:`\index{primrec}{Types!naryFunc}`

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint naryFunc (n : nat) : Set :=
     match n with
     | O => nat
     | S n => nat -> naryFunc n
     end.
   \end{Coqsrc}

For instance (``naryFunc 1``) is convertible to ``nat -> nat`` and
(``naryFunc 3``) to ``nat -> nat -> nat -> nat``.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`
*From\ *\ `MoreAck.PrimRecExamples <../theories/html/hydras.MoreAck.PrimRecExamples.html>`__.

.. raw:: latex

   \begin{Coqsrc}
   Require Import primRec.
   Import extEqualNat.

   Compute naryFunc 3.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   = nat -> nat -> nat -> nat
     : Set  
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Check plus: naryFunc 2.

   Check 42: naryFunc 0.

   Check (fun n p q : nat =>  n * p + q): naryFunc 3.
   \end{Coqsrc}

Likewise, arbitrary boolean predicates may have an arbitrary number of
arguments. The dependent type (``naryRel n``), defined in the same way
as ``naryFunc``, is the type of :math:`n`-ary functions from ``nat``
into ``bool``.

.. raw:: latex

   \begin{Coqsrc}
   Compute naryRel 2.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
    = nat -> nat -> bool
        : Set
   \end{Coqanswer}

The magic of dependent types makes it possible to define recursively
extensional equality between functions of the same arity.

:raw-latex:`\index{coq}{Dependent types}`
:raw-latex:`\index{coq}{Dependently typed functions}`
:raw-latex:`\vspace{4pt}` :raw-latex:`\noindent`
*From*\ `Ackermann.extEqualNat <../theories/html/hydras.Ackermann.extEqualNat.html>`__

:raw-latex:`\index{primrec}{Predicates!extEqual}`

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint  extEqual (n : nat) : forall  (a b : naryFunc n), Prop :=
     match n with
       0 => fun a b => a = b
     | S p => fun a b => forall c, extEqual p (a c) (b c)
     end.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Compute extEqual 2.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
        = fun a b : naryFunc 2 => forall x x0 : nat, a x x0 = b x x0
        : naryFunc 2 -> naryFunc 2 -> Prop
    \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   Example extEqual_ex1 : extEqual 2 mult (fun x y =>  y * x + x - x) .
   Proof.
     intros x y.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
     x, y : nat
     ============================
     extEqual 0 (x * y) (y * x)
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
     cbn.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   1 subgoal (ID 10)
     
     x, y : nat
     ============================
     x * y = y * x + x - x
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
     rewrite <- Nat.add_sub_assoc, Nat.sub_diag.
     - ring.
     - apply le_n.  
   Qed.
   \end{Coqsrc}

A Data-type for Primitive Recursive Functions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The traditional definition of the set of primitive recursive functions
is structured as an inductive definition in five rules: three base
cases, and two construction rules. Primitive recursive functions are
total functions from :math:`\mathbb{N}^n` to :math:`\mathbb{N}`, for
some :math:`n\in\mathbb{N}`.

zero
   the constant function of value :math:`0` is primitive recursive.

S
   The successor function :math:`S:\mathbb{N}\rightarrow\mathbb{N}` is
   primitive recursive.

projections
   For any pair :math:`0< i\leq n`, the projection
   :math:`\pi_{i,n}: \mathbb{N}^n\rightarrow\mathbb{N}`, defined by
   :math:`\pi_{i,n}(x_1,x_2,\dots,x_{n})=x_i`, is primitive recursive.

composition
   For any :math:`n` and :math:`m`, if
   :math:`h: \mathbb{N}^m\rightarrow\mathbb{N}`, and
   :math:`g_0,\dots, g_{m-1}` are primitive recursive of :math:`n`
   arguments, then the function which maps any tuple
   :math:`(x_0,\dots,x_{n-1})` to
   :math:`h(g_0(x0,\dots,x_{n-1}),\dots, g_{m-1}(x0,\dots,x_{n-1}))` is
   primitive recursive.

primitive recursion
   If :math:`g: \mathbb{N}^n\rightarrow\mathbb{N}` and
   :math:`h: \mathbb{N}^{n+2}\rightarrow\mathbb{N}` are primitive
   recursive, then the function from :math:`\mathbb{N}^{n+1}` into
   :math:`\mathbb{N}` defined by

   .. math::

      \begin{aligned}
      f(0,x_1,\dots,x_n)&=g(x_1,\dots,x_n)\\
      f(S(p),x_1,\dots,x_n)&=h(p,f(p, x_1,\dots,x_n),  x_1,\dots,x_n)\end{aligned}

   is primitive recursive.

O’Connor’s formalization of primitive recursive functions takes the form
of two mutually inductive dependent data types, each constructor of
which is associated with one of these rules. These two types are
(``PrimRec n``) (primitive recursive functions of :math:`n` arguments),
and (``PrimRecs n m``) (:math:`m`-tuples of primitive recursive
functions of :math:`n` arguments).

:raw-latex:`\index{coq}{Dependent types}`
:raw-latex:`\index{coq}{Mutually inductive types}`

:raw-latex:`\index{primrec}{Types!PrimRec}`
:raw-latex:`\index{primrec}{Types!PrimRecs}`
:raw-latex:`\label{def:Primrec}` :raw-latex:`\vspace{4pt}`
:raw-latex:`\noindent`
*From*\ `Ackermann.primRec <../theories/html/hydras.Ackermann.primRec.html>`__\ *.*

.. raw:: latex

   \begin{Coqsrc}
   Inductive PrimRec : nat -> Set :=
     | succFunc : PrimRec 1
     | zeroFunc : PrimRec 0
     | projFunc : forall n m : nat, m < n -> PrimRec n
     | composeFunc :
         forall (n m : nat) (g : PrimRecs n m) (h : PrimRec m), PrimRec n
     | primRecFunc :
         forall (n : nat) (g : PrimRec n) (h : PrimRec (S (S n))), 
         PrimRec (S n)
   with PrimRecs : nat -> nat -> Set :=
     | PRnil : forall n : nat, PrimRecs n 0
     | PRcons : forall n m : nat, PrimRec n -> PrimRecs n m -> 
                      PrimRecs n (S m).
   \end{Coqsrc}

.. raw:: latex

   \begin{remark}
   \label{projFunc-order-of-args}
   Beware of the conventions used in the \texttt{primRec} library!
   The constructor (\texttt{projFunc $n$ $m$})  is associated with the projection $\pi_{n-m,n}$ and \emph{not}
   $\pi_{n, m}$.
   For instance, the projection $\pi_{2,5}$ defined by $\pi_{2,5}(a,b,c,d,e)=b$ corresponds to the term
   (\texttt{projFunc 5 3 H}), where \texttt{H} is a proof of $3<5$.
    This fact is reported in the comments of \texttt{primRec.v}. We presume that this convention makes it easier to define the evaluation function \texttt{evalProjFunc $n$} (see the next sub-section). Trying the other convention is left as an exercise.
   \end{remark}

A little bit of semantics
~~~~~~~~~~~~~~~~~~~~~~~~~

Please note that inhabitants of type (``PrimRec n``) are not
:raw-latex:`\coq{}` functions like ``Nat.mul``, or factorial, etc. The
data-type (``PrimRec n``) is indeed an abstract syntax for the language
of primitive recursive functions. The bridge between this language and
the word of usual functions is an interpretation function
(``evalprimRec n``) of type
:math:`\texttt{PrimRec}\,n \rightarrow  \texttt{naryFunc}\,n` , together
with the function (``evalprimRecS n m``) of type
:math:`\texttt{PrimRecs}\,n\,m \rightarrow  \texttt{Vector.t}\,(\texttt{naryFunc}\,n)\,m`.

:raw-latex:`\index{primrec}{Functions!evalPrimRec}`
:raw-latex:`\index{primrec}{Functions!evalPrimRecs}`

:raw-latex:`\index{coq}{Dependent pattern matching}` Both functions are
mutually defined through dependent pattern matching. We advise the
readers who would feel uneasy with dependent types to consult Adam
Chlipala’s *cpdt* book :raw-latex:`\cite{chlipalacpdt2011}`. We leave it
to the reader to look also at the helper functions in
`Ackermann.primRec <../theories/html/hydras.Ackermann.primRec.html>`__.

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint evalPrimRec (n : nat) (f : PrimRec n) {struct f} : 
    naryFunc n :=
     match f in (PrimRec n) return (naryFunc n) with
     | succFunc => S
     | zeroFunc => 0
     | projFunc n m pf => evalProjFunc n m pf
     | composeFunc n m l f =>
         evalComposeFunc n m (evalPrimRecs _ _ l) (evalPrimRec _ f)
     | primRecFunc n g h =>
         evalPrimRecFunc n (evalPrimRec _ g) (evalPrimRec _ h)
     end
     with evalPrimRecs (n m : nat) (fs : PrimRecs n m) {struct fs} :
    Vector.t (naryFunc n) m :=
     match fs in (PrimRecs n m) return (Vector.t (naryFunc n) m) with
     | PRnil a => Vector.nil  (naryFunc a)
     | PRcons a b g gs =>
          Vector.cons _ (evalPrimRec _ g) _  (evalPrimRecs _ _ gs)
     end.
   \end{Coqsrc}

Looks complicated? The following examples show that, when the arity is
fixed, these definitions behave well w.r.t. :raw-latex:`\coq`’s
reduction rules. Moreover, they make the interpretation functions more
“concrete”.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`
*From*\ `MoreAck.PrimRecExamples <../theories/html/hydras.MoreAck.PrimRecExamples.html>`__\ *.*

.. raw:: latex

   \begin{Coqsrc}
   Example Ex1 : evalPrimRec 0 zeroFunc = 0.
   Proof. reflexivity. Qed.

   Example Ex2 a : evalPrimRec 1 succFunc a = S a.
   Proof. reflexivity. Qed.

   Example Ex3 a b c d e f: forall (H: 2 < 6),
       evalPrimRec 6
                   (projFunc 6 2 H) a b c d e f = d.
   Proof. reflexivity. Qed.

   Example Ex4 (x y z : PrimRec 2) (t: PrimRec 3):
     let u := composeFunc 2 3
                          (PRcons 2 _ x
                                  (PRcons 2 _ y
                                          (PRcons 2 _ z
                                                  (PRnil 2))))
                          t in
     let f := evalPrimRec 2 x in
     let g := evalPrimRec 2 y in
     let h := evalPrimRec 2 z in
     let i := evalPrimRec 3 t in
     let j := evalPrimRec 2 u in
     forall a b, j a b = i (f a b) (g a b) (h a b).
   Proof. reflexivity. Qed.

   Example Ex5 (x : PrimRec 2)(y: PrimRec 4):
     let g := evalPrimRec _ x in
     let h := evalPrimRec _ y in
     let f := evalPrimRec _ (primRecFunc _ x y) in
     forall a b,  f 0 a b = g a b.
   Proof. reflexivity.   Qed.                          

   Example Ex6 (x : PrimRec 2)(y: PrimRec 4):
     let g := evalPrimRec _ x in
     let h := evalPrimRec _ y in
     let f := evalPrimRec _ (primRecFunc _ x y) in
     forall n a b,  f (S n) a b = h n (f n a b) a b.
   Proof. reflexivity.   Qed.                          
   \end{Coqsrc}

Another example? Let us consider the following term [1]_:

:raw-latex:`\label{sect:bigfac}`

.. raw:: latex

   \begin{Coqsrc}
   Example bigPR : PrimRec 1 :=
   primRecFunc 0
     (composeFunc 0 1 (PRcons 0 0 zeroFunc (PRnil 0)) succFunc)
     (composeFunc 2 2
       (PRcons 2 1
         (composeFunc 2 1
            (PRcons 2 0 (projFunc 2 1 (le_n 2))
                    (PRnil 2))
            succFunc)
         (PRcons 2 0
           (composeFunc 2 1
             (PRcons 2 0
                (projFunc 2 0
                          (le_S 1 1 (le_n 1)))
                (PRnil 2))
             (projFunc 1 0 (le_n 1))) (PRnil 2)))
       (primRecFunc 1 (composeFunc 1 0 (PRnil 1) zeroFunc)
          (composeFunc 3 2
            (PRcons 3 1
               (projFunc 3 1 (le_S 2 2 (le_n 2)))
               (PRcons 3 0 (projFunc 3 0
                             (le_S 1 2
                                   (le_S 1 1 (le_n 1))))
                       (PRnil 3)))
            (primRecFunc 1 (projFunc 1 0 (le_n 1))
                         (composeFunc 3 1
                             (PRcons 3 0
                                     (projFunc 3 1 (le_S 2 2 (le_n 2)))
                                     (PRnil 3))
                             succFunc))))). 
   \end{Coqsrc}

Let us now interpret this term as an arithmetic function.

.. raw:: latex

   \begin{Coqsrc}
   Example  mystery_fun : nat -> nat := evalPrimRec 1 bigPR.

   Compute map mystery_fun[0;1;2;3;4;5;6] : t nat _.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
    = 1 :: 1 :: 2 :: 6 :: 24 :: 120 :: 720 :: nil
        : t nat 7
   \end{Coqanswer}

Ok, the term ``bigPR`` looks to be a primitive recursive definition of
the factorial function, although we haven’t proved this fact yet.
Fortunately, we will see in the following sections much simpler ways to
prove that a given function is primitive recursive, whithout looking at
an unreadable term.

Proving that a given arithmetic function is primitive recursive
---------------------------------------------------------------

The example in the preceding section clearly shows that, in order to
prove that a given arithmetic function (defined in
:raw-latex:`\gallina{}` as usual) is primitive recursive, trying to give
by hand a term of type ``PrimRec n`` is not a good method, since such
terms may be huge and complex, even for simple arithmetic functions. The
method proposed in Library ``primRec`` is the following one:

#. Define a type corresponding to the statement "the function
   ``f:naryFunc n`` is primitive recursive ”.

#. Prove handy lemmas which may help to prove that a given function is
   primitive recursive.

Thus, the proof that a function, like ``factorial``, is primitive
recursive may be interactive, whithout having to type complex terms at
any step of the development.

The predicate ``isPR``
~~~~~~~~~~~~~~~~~~~~~~

:raw-latex:`\index{primrec}{Predicates!isPR}`
:raw-latex:`\index{coq}{Extensionnaly equal functions}`

Let :math:`f` be an arithmetic function of arity :math:`n`. We say that
:math:`f` is primitive recursive if :math:`f` is **extensionnaly** equal
to the interpretation of some term of type ``PrimRec n``.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`
*From*\ `Ackermann.primRec <../theories/html/hydras.Ackermann.primRec.html>`__\ *.*

.. raw:: latex

   \begin{Coqsrc}
   Definition isPR (n : nat) (f : naryFunc n) : Set :=
     {p : PrimRec n | extEqual n (evalPrimRec _ p) f}.  
   \end{Coqsrc}

The library ``primRec`` contains a large catalogue of lemmas allowing to
prove statements of the form (``isPR n f``). We won’t list all these
lemmas here, but give a few examples of how they may be applied.

.. raw:: latex

   \begin{remark}
   In the library \texttt{primRec}, all these lemmas are opaque (registered with \texttt{Qed}. Thus they do not allow the user to look at the witness of a proof of a \texttt{isPR} statement. Our example of page\pageref{sect:bigfac} was built using a  copy of \texttt{primRec.v} where many \texttt{Qed}s have been replaced with
   \texttt{Defined}s.
   \end{remark}

Elementary proofs of ``isPR`` statements
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The constructors ``zeroFunc``, ``succFunc``, and ``projFunc`` of type
``PrimRec`` allows us to write trivial proofs of primitive recursivity.
Although the following lemmas are already proven in
`Ackermann.primRec.v <../theories/html/hydras.Ackermann.primRec.html>`__,
we wrote alternate proofs in
`Ackermann.MoreAck.PrimRecExamples.v <../theories/html/hydras.MoreAck.PrimRecExamples.html>`__,
in order to illustrate the main proof patterns.

.. raw:: latex

   \begin{Coqsrc}
   Module Alt.
     
   Lemma zeroIsPR : isPR 0 0.
   Proof.
     exists zeroFunc.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   1 subgoal (ID 90)
     
     ============================
     extEqual 0 (evalPrimRec 0 zeroFunc) 0
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
     cbn.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   1 subgoal (ID 91)
     
     ============================
     0 = 0
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
     reflexivity.
   Qed.
   \end{Coqsrc}

Likewise, we prove that the successor function on ``nat`` is primitive
recursive too.

.. raw:: latex

   \begin{Coqsrc}
   Lemma SuccIsPR : isPR 1 S.
   Proof.
     exists succFunc; cbn; reflexivity.
   Qed.
   \end{Coqsrc}

Projections are proved primitive recursive, case by case (many examples
in `Ackermann.primRec.v <../theories/html/hydras.primRec.html>`__).
*Please notice again that the name of the projection follows the
mathematical tradition, whilst the arguments of ``projFunc`` use another
convention (cf remark :raw-latex:`\vref{projFunc-order-of-args}`).*

.. raw:: latex

   \begin{Coqsrc}
   Lemma pi2_5IsPR : isPR 5 (fun a b c d e => b).
   Proof.
    assert (H: 3 < 5) by auto.
    exists (projFunc 5 3 H).
    cbn; reflexivity.
   Qed.
   \end{Coqsrc}

Please note that the projection :math:`\pi_{1,1}` is just the identity
on ``nat``, and is realized by (``projFunc 1 0``).

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`
*From*\ `Ackermann.primRec <../theories/html/hydras.primRec.html>`__\ *.*

.. raw:: latex

   \begin{Coqsrc}
   Lemma idIsPR : isPR 1 (fun x : nat => x).
   Proof.
     assert (H: 0 < 1) by auto.
     exists (projFunc 1 0 H); cbn; auto.
   Qed.
   \end{Coqsrc}

Using function composition
^^^^^^^^^^^^^^^^^^^^^^^^^^

Let us look at the proof that any constant :math:`n` of type ``nat`` has
type (``PR 0``) (lemma ``const1_NIsPR`` of ``primRec``). We carry out a
proof by induction on :math:`n`, the base case of which is already
proven. Now, let us assume :math:`n` is ``PR n``, with
:math:`x:\texttt{PrimRec}\,0` as a “realizer”. Thus we would like to
compose this constant function with the unary successor function.

This is exactly the role of the instance ``composeFunc 0 1`` of the
dependently typed function ``composeFunc``, as shown by the following
lemma.

.. raw:: latex

   \begin{Coqsrc}
   Fact compose_01 :
       forall (x:PrimRec 0) (t : PrimRec 1),
       let c := evalPrimRec 0 x in
       let f := evalPrimRec 1 t in
       evalPrimRec 0 (composeFunc 0 1
                                  (PRcons 0 0 x (PRnil 0))
                                  t)  =
        f c.
   Proof. reflexivity. Qed.
   \end{Coqsrc}

Thus, we get a quite simple proof of ``const1_NIsPR``.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`
*From*\ `MoreAck.PrimRecExamples <../theories/html/hydras.MoreAck.PrimRecExamples.html>`__.

.. raw:: latex

   \begin{Coqsrc}
   Lemma  const1_NIsPR n : isPR 0 n. 
   Proof.
     induction n.
     - apply zeroIsPR.
     - destruct IHn as [x Hx].
      exists (composeFunc 0 1 (PRcons 0 0 x (PRnil 0)) succFunc). 
      cbn in *; intros; now rewrite Hx.
   Qed.
   \end{Coqsrc}

Proving that ``plus`` is primitive recursive
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The lemma ``plusIsPR`` is already proven in
`Ackermann.primRec <../theories/html/hydras.primRec.html>`__. We present
in
`MoreAck.PrimRecExamples <../theories/html/hydras.MoreAck.PrimRecExamples.html>`__
a commented version of this proof,

First, we look for lemmas which may help to prove that a given function
obtained with the recursor ``nat_rec`` is primitive recursive.

.. raw:: latex

   \begin{Coqsrc}
   Search (is_PR 2 (fun _ _ => nat_rec _ _ _ _)).
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   ind1ParamIsPR:
     forall f : nat -> nat -> nat -> nat,
     isPR 3 f ->
     forall g : nat -> nat,
     isPR 1 g ->
     isPR 2
       (fun a b : nat =>
        nat_rec (fun _ : nat => nat)
                    (g b) (fun x y : nat => f x y b) a)
   \end{Coqanswer}

We prove that the library function ``plus`` is extensionally equal to a
function defined with ``nat_rec``.

.. raw:: latex

   \begin{Coqsrc}
   Definition plus_alt x y  :=
                 nat_rec  (fun n : nat => nat)
                          y
                          (fun z t =>  S t)
                          x.

   Lemma plus_alt_ok:
     extEqual 2 plus_alt plus.
   Proof.
     intro x; induction x; cbn; auto.
     intros y; cbn; now rewrite <- (IHx y).
   Qed.
   \end{Coqsrc}

A last lemma before the proof:

.. raw:: latex

   \begin{Coqsrc}
   Lemma isPR_extEqual_trans n : forall f g, isPR n f ->
                                       extEqual n f g ->
                                       isPR n g.
   Proof.
    intros f g [x Hx]; exists x.
    apply extEqualTrans with f; auto.
   Qed.
   \end{Coqsrc}

Let us start now.

.. raw:: latex

   \begin{Coqsrc}
   Lemma plusIsPR : isPR 2 plus.
   Proof.
     apply isPR_extEqual_trans with plus_alt.
     - unfold plus_alt; apply ind1ParamIsPR.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   2 subgoals (ID 126)
     
     ============================
     isPR 3 (fun _ y _ : nat => S y)

   subgoal 2 (ID 127) is:
    isPR 1 (fun b : nat => b)
   \end{Coqanswer}

We already proved that ``S`` is ``PR 1``, but we need to consider a
function of three arguments, which ignores its first and third
arguments. Fortunately, the library ``primRec`` already contains lemmas
adapted to this kind of situation.

.. raw:: latex

   \begin{Coqanswer}
   filter010IsPR :
   forall g : nat -> nat, isPR 1 g -> isPR 3 (fun _ b _ : nat => g b)
   \end{Coqanswer}

Thus, our first subgoal is solved easily and the proof ends, applying
already proven lemmas.

.. raw:: latex

   \begin{Coqsrc}
    - unfold plus_alt; apply ind1ParamIsPR.
       + apply filter010IsPR, succIsPR.
       + apply idIsPR.
     - apply plus_alt_ok. 
   Qed.
   \end{Coqsrc}

.. raw:: latex

   \begin{todo}
   Comment more examples from   \href{../theories/html/hydras.MoreAck.PrimRecExamples.html}{MoreAck.PrimRecExamples}.
   \end{todo}

:raw-latex:`\index{primrec}{Exercises}`

.. raw:: latex

   \begin{exercise}
   There is a lot of lemmas similar to \texttt{filter010IsPR} in the \texttt{primRec} library, useful to control the arity of functions.
   Thus, the reader may look at them, and invent simple examples of application for each one.
   \end{exercise}

:raw-latex:`\index{primrec}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Multiplication of natural number is already proven in the \texttt{primRec} library. Write a proof of your own, then compare to the library's version.
   \end{exercise}

More examples
^^^^^^^^^^^^^

The following proof decomposes the ``double`` function as the
composition of multiplication with the identity and the constant
function wihich returns :math:`2`. *Note that the lemma ``const1_NIsPR``
considers this function as an unary function (unlike ``const0_NIsPR``)*.

.. raw:: latex

   \begin{Coqsrc}
   Lemma doubleIsPR : isPR 1 double.
   Proof.
     unfold double; apply compose1_2IsPR.
     - apply idIsPR.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   subgoal 1 (ID 110) is:
    isPR 1 (fun _ : nat => 2)
   subgoal 2 (ID 111) is:
    isPR 2 Init.Nat.mul
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
     - apply const1_NIsPR.
     - apply multIsPR.
   Qed.
   \end{Coqsrc}

:raw-latex:`\index{primrec}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove that the following functions are primitive recursive. 

   \begin{Coqsrc}
   Fixpoint fact n :=
     match n with 
             | 0 => 1
             | S p  => n * fact p
     end.

   Fixpoint exp n p :=
     match p with
     | 0 => 1
     | S m =>  exp n m * n
     end.

   Fixpoint tower2 n :=
     match n with
     | 0 => 1
     | S p => exp 2 (tower2 p)
     end.
   \end{Coqsrc}



   \textbf{Hint:} You may have to look again at the lemmas of the library
   \href{../theories/html/hydras.Ackermann.primRec.html}{Ackermann.primRec} if you meet some difficulty.
   You may start this exercise with the file
   \url{../exercises/primrec/MorePRExamples.v}.
   \end{exercise}

:raw-latex:`\index{primrec}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Show that the function \texttt{min: naryFunc\,2} is primitive
   recursive.

   \emph{You may start this exercise with
   \url{../exercises/primrec/MinPR.v}.}

   \end{exercise}

:raw-latex:`\index{primrec}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Write a simple and readable proof that the Fibonacci function is primitive recursive.


   \begin{Coqsrc}
   Fixpoint fib (n:nat) : nat :=
     match n with
     | 0 => 1
     | 1 => 1
     | S ((S p) as q) => fib q + fib p
     end.
   \end{Coqsrc}

   \textbf{Hint:}  You may use as a helper the function which computes the pair 
   $(\texttt{fib}(n+1),\texttt{fib}(n))$. 
   Library \href{../theories/html/hydras.Ackermann.cPair.html}{Ackermann.cPair} contains
   the definition of the encoding of $\mathbb{N}^2$ into $\mathbb{N}$, and the proofs that 
   the associated constructor and projections are primitive recursive.


   \emph{You may start this exercise with the file
   \url{../exercises/primrec/FibonacciPR.v}.}

   \end{exercise}

:raw-latex:`\index{primrec}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove the following lemmas (which may help to solve the next  exercise).

   \begin{Coqsrc}
   Lemma boundedSearch3 (P: naryRel 2) (b  : nat), 
       boundedSearch P b <= b. 

   Lemma boundedSearch4 (P: naryRel 2) (b  : nat):
     P b b = true -> P b (boundedSearch P b) = true.
   \end{Coqsrc}
   \end{exercise}

:raw-latex:`\index{primrec}{Exercises}`

.. raw:: latex

   \begin{exercise}
   Prove that the function which returns the  integer square root of any natural number  is primitive recursive.

   \emph{You may start this exercise with the file
   \url{../exercises/primrec/isqrt.v}.}

   \end{exercise}

.. _sect:ack-not-PR:

Proving that a given function is *not* primitive recursive
----------------------------------------------------------

The best known example of a total recursive function which is not
primitive recursive is the Ackermann function. We show how to adapt the
classic proof (see for instance :raw-latex:`\cite{planetmath}`) to the
constraints of :raw-latex:`\gallina`. We hope this formal proof is a
nice opportunity to explore the treatment of primitive recursive
functions by R. O’Connor, and to play with dependent types.

Ackermann function
~~~~~~~~~~~~~~~~~~

Ackermann function is traditionally defined as a function from
:math:`\mathbb{N}\times \mathbb{N}` into :math:`\mathbb{N}`, through
three equations:

.. math::

   \begin{aligned}
   A(0,n)&=n+1\\
   A(m+1,0)&=A(m,1)\\
   A(m+1,n+1)&=A(m,A(m+1,n))\end{aligned}

Let us try to define this function in :raw-latex:`\coq{}` (in curried
form).

.. raw:: latex

   \begin{Coqsrc}
   Fail
     Fixpoint Ack (m n : nat) : nat :=
     match m, n with
     | 0, n => S n
     | S m, 0 => Ack m 1
     | S m0, S p => Ack m0 (Ack m p)
     end.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   The command has indeed failed with message:
   Cannot guess decreasing argument of fix.
   \end{Coqanswer}

| A possible workaround is to make
| textttm be the decreasing argument, and define — within ``m``\ ’s
  scope — a local helper function which computes ``Ack m n`` for any
  ``n``. This way, both functions ``Ack`` and ``Ackm`` have a
  (structurally) strictly decreasing argument.

.. raw:: latex

   \begin{Coqsrc}
   Module Alt.

      Fixpoint Ack (m n : nat) : nat :=
        match m with
        | O => S n
        | S p => let fix Ackm (n : nat) :=
                     match n with
                     | O => Ack p 1
                     | S q => Ack p (Ackm q)
                     end
                 in Ackm n
        end.

       Compute Ack 3 2.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
     = 29 : nat
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
   End Alt.
   \end{Coqsrc}

We prefered to define a variant which uses explicitely the functional
``iterate``, where (``iterate f n``) is the :math:`n`-th iteration of
:math:`f`  [2]_. It makes it possible to apply a few lemmas proved in
`Prelude.Iterates <../theories/html/hydras.Prelude.Iterates.html>`__,
for instance about the monotony of the :math:`n`-th iterate of a given
function.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`
*From*\ `Prelude.Iterates <../theories/html/hydras.Prelude.Iterates.html>`__.
:raw-latex:`\index{hydras}{Library Prelude!iterate}`

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint iterate {A:Type}(f : A -> A) (n: nat)(x:A) :=
     match n with
     | 0 => x
     | S p => f (iterate  f p x)
     end.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
   Lemma iterate_le_n_Sn:
   forall f : nat -> nat,
   (forall x : nat, x <= f x) ->
   forall n x : nat, iterate f n x <= iterate f (S n) x.
   \end{Coqsrc}

Thus, our definition of the Ackermann function is as follows:

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`
*From*\ `MoreAck.Ack <../theories/html/hydras.MoreAck.Ack.html>`__.
:raw-latex:`\index{maths}{Ackermann function}`
:raw-latex:`\index{primrec}{Ackermann function}`

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint Ack (m:nat) : nat -> nat :=
     match m with
     | 0 => S
     | S n => fun k =>  iterate (Ack n) (S k) 1
     end.

   Compute Ack 3 2.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
     = 29 : nat
   \end{Coqanswer}

:raw-latex:`\index{hydras}{Exercises}`

.. raw:: latex

   \begin{exercise}
   The file \href{../theories/html/hydras.MoreAck.Ack.html}{MoreAck.Ack} presents two other definitions\footnote{post on \href{https://stackoverflow.com/questions/10292421/error-in-defining-ackermann-in-coq} by Anton Trunov.} of the Ackermann functions based on the lexicographic ordering on $\mathbb{N}\times\mathbb{N}$.
   Prove that all the four functions are extensionnally equal.
   \end{exercise}

First properties of the Ackermann function
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The three firts lemmas make us sure that our function ``Ack`` satifies
the “usual” equations.

.. raw:: latex

   \begin{Coqsrc}
   Lemma Ack_0 : Ack 0 = S.
   Proof refl_equal.

   Lemma Ack_S_0 m : Ack (S m) 0 = Ack m 1. 
   Proof.  now cbn. Qed.

   Lemma Ack_S_S : forall m p,
       Ack (S m) (S p) = Ack m (Ack (S m) p).
   Proof.  now cbn. Qed.
   \end{Coqsrc}

The order of growth of the Ackermann function w.r.t. its first argument
is illustrated by the following equalities.

.. raw:: latex

   \begin{Coqsrc}
   Lemma Ack_1_n n: Ack 1 n = S  (S n).

   Lemma Ack_2_n n: Ack 2 n = 2 * n + 3.

   Lemma Ack_3_n n: Ack 3 n = exp2 (S (S (S n))) - 3.

   Lemma Ack_4_n n: Ack 4 n = hyper_exp2 (S (S (S n))) - 3.
   \end{Coqsrc}

An important property of the Ackermann function helps us to overcome the
difficulty raised by nested recursion, by climbing up the hierarchy
:math:`\texttt{Ack}\,n\,\_\;(n\in\mathbb{N})`.

.. raw:: latex

   \begin{Coqsrc}
   Lemma nested_Ack_bound : forall k m n, 
       Ack k (Ack m n) <= Ack (2 + max k m) n.
   \end{Coqsrc}

Please note also that for any given :math:`n`, the unary function
(``Ack n``) is primitive recursive.

:raw-latex:`\noindent`
*From*\ `MoreAck.AckNotPR <../theories/html/hydras.MoreAck.AckNotPR.html>`__.

.. raw:: latex

   \begin{Coqsrc}
   Theorem Ackn_IsPR (n: nat) : isPR 1 (Ack n).
   \end{Coqsrc}

A proof by induction on all primitive recursive functions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Ìn order to prove that ``Ack`` (considered as a function of two
arguments) is not primitive recursive, the usual method consists in two
steps:

#. Prove that for any primitive recursive function
   :math:`f:\mathbb{N}\rightarrow\mathbb{N}\rightarrow\mathbb{N}`, there
   exists some natural number :math:`n` depending on :math:`f`, such
   that, for any :math:`x` and :math:`y`,
   :math:`f\,x\,y \leq \texttt{Ack}\,n\,(\textrm{max}\,x\,y)` (we say
   that :math:`f` is *“majorized”* by ``Ack``).

#. Show that ``Ack`` fails to satisfy this property.

First, we prove that any primitive function of two arguments is
majorized. If we look at the inductive definition of primitive recursive
functions, page :raw-latex:`\pageref{def:Primrec}`, it is obvious that a
proof by induction on the construction of primitive recursive functions
must consider functions of any arity.

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`
*From*\ `Ackermann.primRec <../theories/html/hydras.Ackermann.primRec.html>`__\ *.*

:raw-latex:`\index{coq}{Commands!Scheme}`

.. raw:: latex

   \begin{Coqsrc}
   Scheme PrimRec_PrimRecs_ind := Induction for PrimRec
     Sort Prop
     with PrimRecs_PrimRec_ind := Induction for PrimRecs 
     Sort Prop.
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   PrimRec_PrimRecs_ind :
   forall (P : forall n : nat, PrimRec n -> Prop)
     (P0 : forall n n0 : nat, PrimRecs n n0 -> Prop),
   (* successor *)
   P 1 succFunc ->

   (* zero *)
   P 0 zeroFunc ->

   * projections *)
   (forall (n m : nat) (l : m < n), P n (projFunc n m l)) ->

   (* composition *) 
   (forall (n m : nat) (g : PrimRecs n m),
         P0 n m g -> forall h : PrimRec m, P m h -> 
         P n (composeFunc n m g h)) ->

   (* primitive recursion *)
   (forall (n : nat) (g : PrimRec n),
    P n g ->
       forall h : PrimRec (S (S n)), P (S (S n)) h -> 
        P (S n) (primRecFunc n g h)) ->

   (* empty list of functions *)
   (forall n : nat, P0 n 0 (PRnil n)) ->

   (* add a function to a list *)
   (forall (n m : nat) (p : PrimRec n),
      P n p -> 
      forall p0 : PrimRecs n m, P0 n m p0 -> 
      P0 n (S m) (PRcons n m p p0)) ->

   (* conclusion ! *)
   forall (n : nat) (p : PrimRec n), P n p
   \end{Coqanswer}

For instance, proving a property shared by any primitive recursive
function of arity 2 leads to consider the case where that function is
obtained by composition with a function of any arity :math:`m`. The same
problem happens with primitive recursion, where a function of arity
:math:`n` is built out of a function of arity :math:`n+1` and a function
of arity :math:`n-1`.

Thus the lemma we will have to prove is the following one:

   For any :math:`n`, and any primitive recursive function :math:`f` of
   arity :math:`n`, there exists some natural number :math:`q` such that
   the following inequality holds:

   .. math::

      \forall x_1,\dots,x_n, 
            f(x_1,\dots,\,x_n)\leq\textrm{Ack}(q,\textrm{max}(x_1,\dots,x_n))

But dots don’t belong to :raw-latex:`\gallina`’s syntax! So, we may use
:raw-latex:`\coq`’s vectors for denoting arbitrary tuples.

First, we extend ``max`` to vectors of natural numbers (using the
notations of module ``VectorNotations`` and some more definitions from
`Prelude.MoreVectors <../theories/html/hydras.Prelude.MoreVectors.html>`__).
So, ``t A n`` is the type of vectors of :math:`n` elements of type
:math:`A`, and the constants ``cons``, ``nil``, ``map``, etc., refer to
vectors and not to lists. Likewise, the notation ``x::v`` is an
abbreviation for ``VectorDef.cons x _ v``.

:raw-latex:`\index{coq}{Dependently typed functions}`

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint max_v {n:nat} : forall (v: Vector.t nat n) , nat :=
     match n as n0 return (Vector.t nat n0 -> nat)
     with
       0 => fun v => 0
     | S p => fun (v : Vector.t nat (S p)) =>
                (max (Vector.hd v) (max_v  (Vector.tl v)))
     end. 

   Lemma max_v_2 : forall x y,  max_v (x::y::nil) = max x y.

   Lemma max_v_lub : forall n (v: t nat n) y,
       (Forall (fun x =>  x <= y) v) -> max_v v <= y.

   Lemma max_v_ge : forall n (v: t nat n) y,  In  y  v -> y <= max_v v.
   \end{Coqsrc}

We have also to convert any application
:math:`(f\,x_1\,x_2\,\dots\,x_n)` into an application of a function to a
single argument: the vector of all the :math:`x_i`\ s. This is already
done in
Library `Ackermann.primRec <../theories/html/hydras.Ackermann.primRec.html>`__.

.. raw:: latex

   \begin{Coqsrc}
   Fixpoint evalList (m : nat) (l : Vector.t nat m) {struct l} :
    naryFunc m -> nat :=
     match l in (Vector.t _ m) return (naryFunc m -> nat) with
     | Vector.nil => fun x : naryFunc 0 => x
     | Vector.cons a n l' => fun x : naryFunc (S n) => evalList n l' (x a)
     end.
   \end{Coqsrc}

Indeed, (``evalList m v f``) is the application to the vector :math:`v`
of an uncurried version of :math:`f`. In
Library\ `MoreAck.AckNotPR <../theories/html/hydras.MoreAck.AckNotPR.html>`__,
we introduce a lighter notation.

:raw-latex:`\index{coq}{Dependently typed functions}`

.. raw:: latex

   \begin{Coqsrc}
   (**  uncurried apply:
    
   [v_apply f (x1::x2:: ... ::xn::nil)]  is [f x1 x2 ... xn] 
    *)

   Notation "'v_apply' f v" := (evalList _ v f) ( at level 10, f at level 9).

   Example Ex2 : forall (f: naryFunc 2) x y,
       v_apply f (x::y::nil) = f x y.
   Proof.   intros; now cbn. Qed.

   Example Ex4 : forall (f: naryFunc 4) x y z t,
       v_apply f (x::y::z::t::nil) = f x y z t.
   Proof.  intros; now cbn. Qed.
   \end{Coqsrc}

We are now able to translate in :raw-latex:`\gallina{}` the notion of
“majorization”:

:raw-latex:`\index{coq}{Dependently typed functions}`

.. raw:: latex

   \begin{Coqsrc}
   Definition majorized {n} (f: naryFunc n) (A: naryFunc 2) : Prop :=
     exists (q:nat), forall (v: t nat n),
         v_apply f v <= A q  (max_v v).

   Definition majorizedPR {n} (x: PrimRec n) A := 
              majorized (evalPrimRec n x) A.

   (** For vectors of functions *)

   Definition majorizedS {n m} (fs : Vector.t (naryFunc n) m)
              (A : naryFunc 2):=
     exists N, forall (v: t nat n),
         max_v (map (fun f => v_apply f v) fs) <= A N (max_v v).

   Definition majorizedSPR {n m} (x : PrimRecs n m) :=
     majorizedS (evalPrimRecs _ _ x).
   \end{Coqsrc}

Now, it remains to prove that any primitive function is majorized by
``Ack``. The three base cases of construction of primitive recursive
function are as follows:

.. raw:: latex

   \begin{Coqsrc}
   Lemma majorSucc : majorizedPR  succFunc Ack.

   Lemma majorZero : majorizedPR  zeroFunc Ack.

   Lemma majorProjection (n m:nat)(H: m < n):
     majorizedPR (projFunc n m H) Ack.
   \end{Coqsrc}

The rest of the cases are proved within a mutual induction.

:raw-latex:`\index{coq}{Mutual induction}`

.. raw:: latex

   \begin{Coqsrc}
   Lemma majorAnyPR:  forall n (x: PrimRec n),  majorizedPR  x Ack.
   Proof.
     intros n x; induction x using PrimRec_PrimRecs_ind with
                     (P0 := fun n m y => majorizedSPR  y Ack).
     - apply majorSucc.
     - apply majorZero.
     - apply majorProjection. 
     \end{Coqsrc}

.. raw:: latex

   \begin{Coqsrc}
     - (** function composition *)
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   1 subgoal (ID 265)

     n, m : nat
     g : PrimRecs n m
     x : PrimRec m
     IHx : majorizedSPR g Ack
     IHx0 : majorizedPR x Ack
     ============================
     majorizedPR (composeFunc n m g x) Ack
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
     ...
    - (** primitive recursion *)
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   1 subgoal (ID 265)
     
     n : nat
     x1 : PrimRec n
     x2 : PrimRec (S (S n))
     IHx1 : majorizedPR x1 Ack
     IHx2 : majorizedPR x2 Ack
     ============================
     majorizedPR (primRecFunc n x1 x2) Ack
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
    assert (L1 : forall i (v: t nat n) ,
                  v_apply f (i::v)  <= Ack q (i + max_v v)).
       { induction i.
         ...
       }
       ...
   -  (** empty list of functions *)
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   1 subgoal (ID 266)
     
     n : nat
     ============================
     majorizedSPR (PRnil n) Ack
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
     ...
   - (** non-empty list of functions *)
   \end{Coqsrc}

.. raw:: latex

   \begin{Coqanswer}
   1 subgoal (ID 273)
     
     n, m : nat
     x : PrimRec n
     p : PrimRecs n m
     IHx : majorizedPR x Ack
     IHx0 : majorizedSPR p Ack
     ============================
     majorizedSPR (PRcons n m x p) Ack
   \end{Coqanswer}

.. raw:: latex

   \begin{Coqsrc}
    ...
   Qed.
   \end{Coqsrc}

Looking for a contradiction
~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following lemma is just a specialization of ``majorAnyPR`` to binary
functions (forgetting vectors, coming back to usual notations).

.. raw:: latex

   \begin{Coqsrc}
   Lemma majorPR2 (f: naryFunc 2)(Hf : isPR 2 f)
     : exists (n:nat), forall x y,  f x y <= Ack n (max x  y).
   \end{Coqsrc}

We prove also a strict version of this lemma, thanks to the following
property (proved in
Library\ `MoreAck.Ack <../theories/html/hydras.MoreAck.Ack.html>`__ ).

.. raw:: latex

   \begin{Coqsrc}
   Lemma Ack_strict_mono_l : forall n m p, n < m ->
                                           Ack n (S p) < Ack m (S p).
   \end{Coqsrc}

.. raw:: latex

   \vspace{4pt}

:raw-latex:`\noindent`
*From*\ `MoreAck.AckNotPR <../theories/html/hydras.MoreAck.AcknotPR.html>`__\ *.*

.. raw:: latex

   \begin{Coqsrc}
   Lemma majorPR2_strict (f: naryFunc 2)(Hf : isPR 2 f):
       exists (n:nat),
       forall x y, 2 <= x -> 2 <= y -> f x y < Ack n (max x  y).
   \end{Coqsrc}

If the Ackermann function were primitive recursive, then there would
exist some natural number :math:`n`, such that, for all :math:`x` and
:math:`y`, the inequality
:math:`\texttt{Ack}\,x\,y\leq \texttt{Ack}\,n\,(\texttt{max}\,x\,y)`
holds. Thus, our impossibility proof is just a sequence of easy small
steps.

.. raw:: latex

   \begin{Coqsrc}
   Section Impossibility_Proof.

     Hypothesis HAck : isPR 2 Ack.
     
     Lemma Ack_not_PR : False.
     Proof.
       destruct (majorPR2_strict Ack HAck) as [m Hm];
       pose (X := max 2 m); specialize (Hm X X).
       rewrite max_idempotent in Hm; 
       assert (Ack m X <= Ack X X) by (apply Ack_mono_l; lia).
       lia.
     Qed.

   End Impossibility_Proof.
   \end{Coqsrc}

.. raw:: latex

   \begin{remark}
   It is easy to prove that any unary function which dominatates \texttt{fun n => Ack n n} fails to be primitive recursive. We use an instance of \texttt{majorAnyPR} for unary functions.
   \vspace{4pt}
   \noindent

   \emph{From \href{../theories/html/hydras.MoreAck.AckNotPR.html}{MoreAck.AckNotPR}}.
   \begin{Coqsrc}
   Lemma majorPR1  (f: naryFunc 1)(Hf : isPR 1 f)
     : exists (n:nat), forall x, f x <= Ack n x.
   (* ... *)
   \end{Coqsrc}

   Then, we write  a short proof by contradiction.

   \begin{Coqsrc}
   Section dom_AckNotPR.

     Variable f : nat -> nat.
     Hypothesis Hf : dominates f (fun n => Ack n n).

    Lemma dom_AckNotPR: isPR 1 f -> False.
     Proof.
       intros H;  destruct Hf as [N HN].
       destruct  (majorPR1 _ H) as [M HM].
       pose (X := Max.max N M).
       specialize (HN X  (Max.le_max_l N M)).
       specialize (HM X);
         assert (Ack M X <= Ack X X) by (apply Ack_mono_l; subst; lia).
       lia.
     Qed.

   End dom_AckNotPR.
   \end{Coqsrc}
   \end{remark}

.. raw:: latex

   \begin{remark}
   Note that the Ackermann function is a counter-example to the (false) statement:
   \begin{quote}
   {\color{red}
     ``Let $f$ be a function of type \texttt{naryFunc\,2}. If, for any $n$, the fonction $f(n)$ is primitive recursive, then f is primitive recursive.''}
   \end{quote}
   \end{remark}

.. [1]
   Of course, we never typed this term *verbatim*; we obtained it as the
   result of some computation we leave it the reader to guess and
   reproduce.

.. [2]
   Please not confuse with ``primRec.iterate``, which is monomorphic and
   does not share the same order of arguments.
