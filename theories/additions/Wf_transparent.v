(** Transparent versions of wf_incl and wf_inverse_image 
*)


From Coq Require Export Relation_Definitions.

Lemma wf_incl_transparent  :
forall (A : Type) (R1 R2 : A -> A -> Prop),
Relation_Definitions.inclusion A R1 R2 -> well_founded R2 -> well_founded R1.
Proof.
 intros A R1 R2 H H0 a;  induction (H0 a). 
 split;  auto.
Defined.


Section Inverse_Image_transp. (* adapted from S.L. *)

  Variables A B : Type.
  Variable R : B -> B -> Prop.
  Variable f : A -> B.

  Let Rof (x y:A) : Prop := R (f x) (f y).

  Remark Acc_lemma : forall y:B, Acc R y -> forall x:A, y = f x -> Acc Rof x.
  Proof.
    induction 1 as [y _ IHAcc]; intros x H.
    apply Acc_intro; intros y0 H1.
    apply (IHAcc (f y0)); try trivial.
    rewrite H; trivial.
   Defined.

  Lemma Acc_inverse_image : forall x:A, Acc R (f x) -> Acc Rof x.
  Proof.
    intros; apply (Acc_lemma (f x)); trivial.
  Defined.

  Theorem wf_inverse_image_transparent : well_founded R -> well_founded Rof.
  Proof.
    red; intros; apply Acc_inverse_image; auto.
  Defined.

End Inverse_Image_transp.
