(** Pierre Casteran, LaBRI, University of Bordeaux *)
Set Implicit Arguments. 

From Coq Require Import Relations Basics
     Wellfounded.Inverse_Image Wellfounded.Inclusion.

Section Variants.
 Variable E: Type.
 Variable tr : relation E. (* transition *) 
 
 Definition terminates  :=  well_founded (flip tr).

 Variables (T: Type)
           (lt : relation T)
           (m : E -> T).

 Infix "<" := lt.

 Class WfVariant :=
   {
     wf : well_founded lt;
     decr : forall x y, tr x y -> m y < m x
   }.


Lemma Variant_termination (Var : WfVariant ) :  terminates .
Proof.
  intro x; apply Acc_incl with (fun  a b => m a < m b).
  - intros  a b H; now  apply decr.
  - apply Acc_inverse_image, wf.
Qed.


End Variants.



 Arguments decr {E tr T lt m} _ _ _ _.
 Arguments wf {E tr T lt m} _ _  .

