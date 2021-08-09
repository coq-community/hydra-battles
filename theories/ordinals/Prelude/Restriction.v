(**  Pierre Casteran 
    LaBRI, University of Bordeaux and LaBRI

    Restriction of a binary relation 
 *)



From Coq Require Import Wellfounded Ensembles Relations.

(* begin snippet restrictionDef *)

Definition restrict {A:Type}(E: Ensemble A)(R: relation A) :=
  fun a b => E a /\ R a b /\ E b.

(* end snippet restrictionDef *)

Section restricted_recursion.

  Variables (A:Type)(E:A->Prop)(R:A->A->Prop).

  
  Definition well_founded_restriction :=
    forall (a:A), E a -> Acc (restrict E R) a.

  (** Induction principle for the restriction of R to E *)
  
  Definition well_founded_restriction_rect :
    well_founded_restriction  ->
    forall X : A -> Type,
      (forall x : A, E x -> (forall y : A, In _ E y -> R y x -> X y) -> X x) ->
      forall a : A, In _ E a -> X a.
  Proof. 
    intros W X H a; pattern a; 
      eapply well_founded_induction_type with (R:=restrict E R).
    - split.   intros y H0;  apply W.
      now case H0.
    -  intros; apply H.
       + assumption. 
       +  intros; apply X0; unfold restrict; auto.
  Defined.

End restricted_recursion.



Section Fix.
  Variables (A:Type)(E: Ensemble A)(R: relation A).
  Hypothesis Hwf : well_founded_restriction A E R.

  (*
Acc_inv (R:=restrict E R)
     : forall x : A,
       Acc (restrict E R) x ->
       forall y : A, restrict E R y x -> Acc (restrict E R) y
   *)



  Variable P : A -> Type.
  Variable F  : (forall x : A, E x -> (forall y : A, In _ E y -> R y x -> P y) -> P x).

  Lemma restriction_fwd : forall x y (H: restrict E R x y), E x.
  Proof.
    destruct 1; tauto.
  Defined.

  Definition restrict_build x y (Hx: E x)(Hy : E y)(H : R x y) :=
    conj Hx (conj H Hy) .

  Fixpoint FixR_F (x:A)(Hx : E x)(a: Acc  (restrict E R)x ) : P x :=
    F _ Hx (fun (y:A) (h0 : E y) (h :  R  y x) =>
              FixR_F y (restriction_fwd y x
                                        (restrict_build y x h0 Hx h))
                     (Acc_inv a (restrict_build y x h0 Hx h))).
  Lemma FixR_F_eq :
    forall (x:A)(Hx : E x) (r: Acc (restrict E R) x) ,
      F _  Hx (fun (y : A)( h0 : E y) (h :  R  y x) =>
                 FixR_F y (restriction_fwd y x                                                                               (restrict_build y x h0 Hx h))
                        (Acc_inv r (restrict_build y x h0 Hx h)))=
      FixR_F x Hx r.
  Proof.
    destruct r using Acc_inv_dep; auto.
  Qed.


  Hypothesis Rwf :  well_founded_restriction A E R.

  Definition FixR (x:A)(H:E x) := FixR_F x H (Rwf x H).


End Fix.

Arguments FixR [A E R P] _ _ _ _.

