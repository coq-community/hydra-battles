Require Import fol folProp folProof  Languages folLogic Arith.
Require Import primRec.

Import FolNotations. 

(** ** Preliminary lemmas *)

#[local] Arguments Ensembles.In {_} .
#[local] Arguments Ensembles.Add {_} .
#[local] Arguments atomic _ _ _ : clear implicits. 
#[local] Arguments apply _ _ _ : clear implicits. 

(* begin snippet BadSubstFdef *)
Module BadSubst.

  Fixpoint substF L (F : Formula L) v (t: Term L) :=
    match F with
  | equal  t1 t2 => equal (substT t1 v t) (substT t2 v t)
  | atomic  r s =>  atomic L r (substTs s v t)
  | impH  G H => impH (substF L G v t) (substF L H v t)
  | notH  G => notH (substF L G v t)
  | forallH  w G => if Nat.eq_dec w v then F else forallH w (substF L G v t)
  end.

End BadSubst. 
(* end snippet BadSubstFdef *)

Require Import List.
Import ListNotations.

Module BadSubstF2. 

(* begin snippet BadSubstF2 *)
Fail Fixpoint substF L (F : Formula L) v (t: Term L) :=
    match F with
  | equal  t1 t2 => equal (substT L t1 v t) (substT L t2 v t)
  | atomic  r s =>  atomic L r (substTs L (arityR  L r) s v t)
  | impH  G H => impH (substF L G v t) (substF L H v t)
  | notH  G => notH (substF L G v t)
  | forallH  w G => if Nat.eq_dec w v then F else 
     let nv := newVar (w :: freeVarT L t ++ freeVarF L G)
       in let H := (substF L G w (var  nv))
          in forallH nv (substF L H v t)
  end.
(* end snippet BadSubstF2  *)

End BadSubstF2.

Require Import FolExamples. 
Import Toy. 

(* begin snippet BadSubstFexample *)
Section BadExample. 

  Let F := (allH 1, exH 2, v#1 <> f v#2)%fol. 
  Let F1: Formula L :=  (exH 2, v#1 <> f v#2)%fol.
 
  Compute BadSubst.substF L F1 1 (f v#2)%fol.

End BadExample.
(* end snippet BadSubstFexample *)

