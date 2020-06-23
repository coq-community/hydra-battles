(**  Well ordered sets (after Schutte) *)

(**  Pierre Casteran LaBRI, Universite de Bordeaux  *)


Require Import Relations  Classical  Classical_sets.
Require Import RelationClasses  .


Arguments In [U].
Arguments Included [U].

Set Implicit Arguments.
Hint Unfold In : core.


Section the_context.
  Variables (M:Type)
            (Lt : relation M).
  
  Definition Le (a b:M) :=  a = b \/ Lt a b.
  
  
  Definition least_member  (X:Ensemble M)(a:M) :=
    In X a /\ forall x,  In X x -> Le a x.

  Definition least_fixpoint (f : M -> M) (x:M) :=
    f x = x /\ forall y: M,  f y = y -> Le x y.
  
  (** Well Ordering *)
  
  Class WO : Type:=
    {
      Lt_trans : Transitive  Lt;
      Lt_irreflexive : forall a:M, ~ Lt a a;
      well_order : forall (X:Ensemble M)(a:M),
          In X a ->
          exists a0:M, least_member  X a0
    }.
  
  (* Some derived properties of well ordered sets *)
  
  Section About_WO.
    Context (Wo : WO).
 
    Lemma  Lt_connect : forall a b,  Lt a b \/ a = b \/ Lt b a.
    Proof.
      intros a b ; generalize (well_order  (Couple _ a b) a ).
      destruct 1 as [ c H1].
      - left. 
      -  destruct H1  as [H2 H3].
         destruct H2.  
         +  destruct (H3 b);auto; now right.
         +  destruct (H3 a);auto; now left.       
    Qed.
 
    Lemma Le_refl : forall x:M, Le x x.
    Proof.
      red;unfold Le;auto.
    Qed.

    Lemma Le_antisym : forall a b,  Le a b -> Le b a -> a = b.
    Proof.
      intros a b  H H'; case H; case H' ; try tauto.
      - symmetry; tauto.
      - intros;case (Lt_irreflexive (a:=a)); eapply (Lt_trans );eauto. 
    Qed.

    Global Instance  Le_trans : Transitive  Le. 
    Proof.
      unfold Transitive, Le;intros.
      case H;case H0.
      - intros; left ; congruence.   
      -  intros H1 H2; right;subst x;auto.
      -  intros H1 H3; right ; subst y; auto.
      -  right;apply Lt_trans with y;eauto.
    Qed.


    Lemma Le_Lt_trans : forall x y z, Le x y -> Lt y z -> Lt x z.
    Proof.
      intros x y z Hxy Hyz; case Hxy;intros.
      -  now subst y.
      - eapply Lt_trans; eauto.
    Qed.
    
    Lemma Lt_Le_trans : forall x y z, Lt x y -> Le y z -> Lt x z.
    Proof.
      intros x y z Hxy Hyz; destruct Hyz as [H0 | H].
      - now subst.
      -  eapply Lt_trans; eauto.
    Qed.

    Lemma Lt_not_Gt : forall x y,  Lt x y -> ~ Lt y x.
    Proof.
      intros x y  H H'; case (Lt_irreflexive (a:=x)).
      eapply Lt_trans; eauto.
    Qed.
    
    Lemma least_member_lower_bound : forall X a,
        least_member  X a -> forall b, In X b ->  Le a b.
    Proof.
      intros X a H; case H.
      unfold In; intuition.
    Qed.
    
    Lemma least_member_glb :
      forall X a,
        least_member  X a -> 
        forall b, (forall c, In X c ->  Le b c) ->
                  Le b a.
    Proof.
      intros X a H b H0; case H;intros H1 H2;  apply H0; auto.
    Qed.

    
    Theorem least_member_unicity : forall  X a b, 
        least_member  X a -> least_member  X b -> a = b.
    Proof.
      intros X a b H H0;  case H;case H0;intros.
      - apply Le_antisym;auto.
    Qed.
    
    
    Theorem least_member_ex_unique :
      forall   X  x 
              (inhX: In X x), 
      exists! a,  least_member  X a.
    Proof.
      intros;destruct (well_order X x); auto.
      exists x0; split; auto.
      intros; eapply least_member_unicity;eauto.
    Qed.
    
    
    Theorem least_member_of_eq : forall (X Y : Ensemble M) a b ,
        Included X Y -> Included Y X ->
        least_member  X a ->
        least_member  Y b ->
        a = b.
    Proof.
      intros X Y a b H H0  [H3 H4 ] [H6 H7].  apply Le_antisym;auto.
    Qed.
    



  End About_WO.
  
End the_context.

(** from now on, we use ClassicalEpsilon *)

Require Import PartialFun.
Import MoreEpsilonIota.



Definition the_least {M: Type} {Lt}
           {inh : InH M} {WO: WO Lt} (X: Ensemble M)  : M :=
  the (least_member  Lt X ).

Lemma  the_least_unicity {M: Type} {Lt}
           {inh : InH M} {WO: WO Lt} (X: Ensemble M)
        (HX: Inhabited _ X ) 
  : exists! l , least_member   Lt X l.
Proof.
  destruct HX as [x Hx].
  case  WO; intros.
  destruct (well_order0 X x Hx) as [x0 H0].
  exists x0; split; auto.
  intros; eapply least_member_unicity;eauto . 
Qed.


Require Import Wf_nat.

Instance WO_nat : WO Peano.lt.
split.
- red. intros; now  transitivity y.
- intros; apply PeanoNat.Nat.lt_irrefl.
-  intros X a; pattern a; apply well_founded_induction with Peano.lt.
   + apply lt_wf.
   + intros;
       destruct (classic (least_member lt X x)).
    * exists x; auto.
    * unfold least_member in H1;     destruct (not_and_or _ _ H1).
       contradiction.
       destruct (not_all_ex_not _ _ H2).     
       destruct (imply_to_and _ _ H3).
       assert (lt x0 x). {
         destruct (Compare_dec.lt_eq_lt_dec x0 x).
         - destruct s; auto.
           + subst x0; unfold Le in H5.
             destruct H5; auto.
             - destruct H5; now right.
         }
       destruct (H x0 H6 H4);  exists x1;  auto.
Qed.

   