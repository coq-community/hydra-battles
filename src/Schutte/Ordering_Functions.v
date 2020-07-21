(** Ordering functions (after Schutte) *)


(**   Pierre Casteran, LaBRI, University of Bordeaux  

Every subset [A] of [Ord] can be enumerated in an unique way 
 by a segment of [Ord].

Thus it makes sense to consider the [alpha]-th element of [A] 

This module shows the construction of the _ordering function_  of [A], following
Schutte's definitions.



*)


Require Export Schutte_basics.
Import Ensembles  Well_Orders  Countable  PartialFun.
Import Classical  MoreEpsilonIota  Epsilon.

Set Implicit Arguments.



 (** * Main definitions *)
 
 
Definition segment (A: Ensemble Ord) :=
  forall alpha beta, In A alpha -> beta < alpha -> In A  beta.

Definition proper_segment (A: Ensemble Ord) :=
  segment A /\  ~ Same_set A ordinal.


(* to do : define it as a class *)

Definition ordering_function (f : Ord -> Ord)(A B : Ensemble Ord) :=
 segment A /\
 (forall a, In A a -> In B (f a)) /\
 (forall b, In B b -> exists a, In A a /\ f a = b) /\
 forall a b, In A a -> In A b -> a < b ->  f a < f b.

Definition ordering_segment (A B : Ensemble Ord) :=
  exists f : Ord -> Ord, ordering_function f A B.

Definition the_ordering_segment (B : Ensemble Ord) :=
  the  (fun x => ordering_segment x B).

Definition proper_segment_of (B : Ensemble Ord)(beta : Ord): Ensemble Ord  :=
  fun alpha => In B alpha /\ alpha < beta /\ In B beta.


Definition ord   (B : Ensemble Ord) := 
   some (fun f => ordering_function f (the_ordering_segment B) B).

Definition  normal (f : Ord -> Ord)(B : Ensemble Ord): Prop :=
 ordering_function f ordinal B /\ continuous f ordinal B.

Definition fun_equiv (f g : Ord -> Ord)(A B : Ensemble Ord) :=
  Same_set A B /\ forall a, In A a -> f a = g a. 

(**  **  Properties of  segments *)

Lemma ordinal_segment : segment ordinal.
Proof.
 split; eauto with schutte. 
Qed.


Lemma members_proper (alpha : Ord) :
  proper_segment (members alpha).
Proof with eauto with schutte.
  split.
 -  intros a b H H0; apply lt_trans with a ...
 -  intros [H0 H1];   destruct (@le_not_gt alpha (succ alpha)) ...
   + apply  (H1 (succ alpha)) ...
Qed.


Lemma proper_members (A: Ensemble Ord) (H :  proper_segment A) :
   exists a: Ord,  Same_set A (members a).
Proof with eauto with schutte.
  case (not_all_not_ex _ (fun b => ordinal b /\ ~ A b)).
  - intro H1;  apply H;split.
    +  unfold Included; split; auto.
    +  intros x H2; apply NNPP; intro H3.
       apply (H1 x); split;auto.
  -  intros x H1; case (@well_order _  lt AX1 (fun x => ordinal x /\ ~ A x) x). 
     + auto.
     +  intros y Hy.
        case Hy;intros H2 H3. red in H2.
        destruct H2.
        exists y;split...
        * intros a H6; tricho a y T ...
          case H;auto.
          subst a; contradiction.
          red in Hy.
          destruct Hy.
          destruct H.
          red in H.
          specialize (H a y H6 T).
          contradiction.
        *   red; unfold In;intros; apply NNPP.
          case Hy;  intros H7 H8 H10.  
          case (H8 x0 ).
          { red; split ... }
          { intro; subst. destruct (lt_irr H4). }
          intro; case (@lt_irr x0); apply lt_trans with y ...
Qed.


Lemma countable_segment_proper : forall A : Ensemble Ord,
           segment A -> countable A -> proper_segment A.
Proof.
 intros A H H0; split;[auto|idtac].
 intro H1; generalize (Extensionality_Ensembles _ _ _ H1).
 intros; subst A ; now case Non_denum.
Qed.


Lemma ordering_function_In f A B a :
   ordering_function f A B -> In A a -> In B (f a).
Proof.  destruct 1 as [_ [H _]]; auto. Qed.

  
Lemma ordering_function_mono (f : Ord -> Ord) (A B: Ensemble Ord) :
  ordering_function f A B ->
  forall alpha beta,
    In A alpha -> In A beta -> alpha < beta -> f alpha < f beta.
Proof.  destruct 1 ;  tauto. Qed.

Hint Resolve ordering_function_mono : schutte.

Lemma  ordering_function_mono_weak (f : Ord -> Ord) (A B: Ensemble Ord) : 
 ordering_function f A B ->
   forall a b, In A a -> In A b -> a <= b -> f a <= f b.
Proof.
 destruct 1 as [H [H0 [H1 H2]]].
 destruct 3.
 -  subst b;  left; auto with schutte.
 -  right;auto.
Qed.

Hint Resolve ordering_function_mono_weak : schutte.

Lemma ordering_function_monoR : forall f A B, ordering_function f A B ->
   forall a b, In A a -> In A b -> f a < f b -> a < b.
Proof.
   destruct 1 as [H [H0 [H1 H2]]]. intros a b H3 H4 H5; tricho a b Ht; auto.
  - subst b; now destruct (@lt_irr (f a)).
  - destruct (@lt_irr (f a)); apply lt_trans with (f b);auto.
Qed.

Hint Resolve ordering_function_monoR : schutte.


Lemma Ordering_bijection : forall f A B, ordering_function f A B ->
                                         fun_bijection A B f.
Proof.
  destruct 1 as [H [H0 [H1 H2]]].
  split;red;auto; intros.
  tricho a a' H7; trivial.
  -  specialize  (H2 _ _ H3 H4 H7); rewrite H5 in H2;
     destruct (lt_irr H2).
  - specialize  (H2 _ _ H4 H3 H7);  rewrite H5 in H2;
    destruct (lt_irr H2).
Qed.


Lemma  ordering_function_mono_weakR : 
  forall f A B, ordering_function f A B ->
                forall a b, In A a -> In A b ->  f a <= f b -> a <= b.
Proof with auto with schutte.
  intros f A B H a b H0 H1 H2.
  case H.
  intros H3 H4; decompose [and] H4; clear H4.
  destruct H2 as [H2  | H2].
  case (Ordering_bijection H).
  intros H10 H11 H12 ;  specialize (H8 a b H0 H1 )...
  -  right; eapply ordering_function_monoR; eauto.
Qed.

Hint Resolve ordering_function_mono_weakR : schutte.


Lemma ordering_function_seg : forall A B, ordering_segment A B ->
                                          segment A.
Proof.   now destruct 1 as [f [H _]]. Qed.

Lemma empty_ordering : forall B, (forall b, ~ B b) ->
                                 ordering_function (fun o => o)
                                                   (members zero)
                                                   B.
Proof.
  intros B H; split.
  -  intros a b H0 H1;  destruct (not_lt_zero H0);auto.
  -  repeat split.
     + intros b H0 ; now destruct (not_lt_zero H0).
     + intros x Hx; now destruct (H x). 
     +  intros a b Hb; case (@not_lt_zero a); assumption. 
Qed.


Lemma segment_lt : forall A a b, segment A -> A a -> b < a -> A b.
Proof.
 intros A a b H0  H1 H2; now apply H0 with a.
Qed.

Theorem segment_unbounded : forall A:Ensemble Ord, segment A -> 
                                        Unbounded A ->
                                        A = ordinal.
Proof with eauto with schutte.
 intros A H H0; red in H0; apply Extensionality_Ensembles; split.
 - intros; split. 
 -  intros x Hx; destruct (H0 x) as [x0 H1]...
    destruct H1; now apply H with x0. 
Qed.

(**  Theorem 13.3 of Schutte's book *)

Theorem ordering_le : forall f A B,
    ordering_function f A B ->
    forall alpha, In A alpha -> alpha  <= f alpha.
Proof with auto with schutte.
  intros f A B H alpha H0; generalize H0;
    pattern alpha; apply transfinite_induction.
  - clear alpha H0; unfold ordering_function in H; decompose [and] H.   
    unfold progressive;   intros alpha H6 H7 .
    tricho alpha (f alpha) H' ...
    +   assert (f (f alpha) < f alpha).
      {    apply H4.
           - eapply segment_lt;eauto with schutte.
           - unfold In;auto.
           - unfold In;auto.
      }
      case (le_not_gt (a:= f alpha)(b:=f (f alpha)));auto.
      apply H6;  eauto with schutte.
Qed.

(* begin hide *)  
Section ordering_function_unicity_1.
  
 Variables B A1 A2 : Ensemble Ord.
 Variables f1 f2 : Ord -> Ord.
 Hypothesis O1 : ordering_function f1 A1 B.
 Hypothesis O2 : ordering_function f2 A2 B.

 
 Remark SA1 : segment A1.
 Proof.   case O1;intuition.  Qed.

 Remark SA2 : segment A2.
 Proof.  case O2;intuition.  Qed.
 
 Hint Resolve SA2 SA1 : schutte.

  Lemma A1_A2 :forall a, In A1 a -> A2 a /\ f1 a = f2 a.
 Proof with eauto with schutte.
   intros a Ha;  generalize Ha;pattern a; apply transfinite_induction.
   {
     clear a Ha ; intros a  H0 Ha ;   assert (A2 a).
     {
       assert (forall khi, khi < a -> A2 khi /\ f1 khi = f2 khi).
       {  intros;  apply H0...
       }
       apply NNPP; intro H2.
       assert (forall y, A2 y -> y < a).
       { intros y H3;  tricho y a H4 ...
         subst y; now case H2.
         destruct H2;  apply segment_lt with y;auto with schutte.
       }

       assert (forall y, A2 y -> f1 y < f1 a).
       {   intros y H4;  case O1;intros H5 H6;  decompose [and] H6.
           apply H9 ... 
       }  

       case O2;intros H5 H6; decompose [and] H6; clear H6;  case (H8 (f1 a)).
       - case O1;intros H6 H10; decompose [and] H10;clear H10.
         apply H7;  auto.
       -  destruct 1;  generalize (H4 x H6).
          intro;  case (H0 x)...
           + intros H13 H14;  specialize (H3 _ H6);  rewrite <- H7 in H3.
            rewrite H14 in H3.
            case (@lt_irr (f2 x));auto.
     }
     {   split; trivial.
         assert (H01 : least_member  lt
                                        (fun x => B x /\ 
                                                  forall y, y < a ->
                                                            f1 y <> x)
                                        (f1 a)).

         {  split.
            +  case O1;intros;  unfold In; intuition.
               apply H3; auto.
               specialize (H5 y a ).
               assert (In A1 y) by (eapply H1 with a ; auto). 
               specialize (H5 H7 Ha H4).
               rewrite H6 in H5; now apply (@lt_irr (f1 a)).
            + destruct 1;   destruct O1.
              decompose [and] H4;   destruct (H7 x H1).
              destruct H6; subst x;  tricho a x0 H9.
              *  right;  apply H8;auto.
              *  subst x0; now left.
              * specialize (H2 _ H9); now destruct H2.
         } 

         assert (H02 : least_member  lt
                                        (fun x => B x /\ forall y, y < a ->
                                                                   f2 y <> x)
                                        (f2 a)).
         {
           split.
           +  case O2;intros;  unfold In; intuition.
              apply H3; auto.
              specialize (H5 y a ).
              assert (In A2 y) by ( eapply H1 with a ; auto). 
              specialize (H5 H7 H H4).
              rewrite H6 in H5; now apply (@lt_irr (f2 a)).
           + destruct 1, O2.
             decompose [and] H4;   destruct (H7 x H1).
             destruct H6; subst x; tricho a x0 H9.
             *  right;   apply H8;auto.
             *  subst x0; now left.
             * specialize (H2 _ H9);  now destruct H2.
         } 
         refine (least_member_of_eq AX1 _ _ H01 H02).

         - intros x Hx; split.
           + red in Hx; tauto.
           + intros y H1; destruct (H0 _ H1).
             * destruct O1;intros;   apply H2 with a; auto.
             * rewrite <- H3;  destruct Hx;  auto.
         - intros x Hx;  split.
           + red in Hx; tauto.
           + intros y H1;   destruct (H0 _ H1).
             destruct O1;intros;  apply H2 with a; auto.
             rewrite  H3;    destruct Hx;  auto.
     }
   }
 Qed.

End ordering_function_unicity_1.

(* end hide *)
 

Section ordering_function_unicity.
  
 Variables B A1 A2 : Ensemble Ord.

 Variables f1 f2 : Ord -> Ord.
 Hypothesis O1 : ordering_function f1 A1 B.
 Hypothesis O2 : ordering_function f2 A2 B.

 (* begin hide *)
 
 Lemma A2_A1 :forall a, A2 a -> A1 a /\ f2 a = f1 a.
 Proof.
  intros; eapply A1_A2.   
  - eapply O2.
  - apply O1.
  - auto.
 Qed.

 (* end hide *)
 
Theorem ordering_function_unicity  : fun_equiv f1 f2 A1 A2.
Proof.
 split.
 - split.
   +  intros x Hx; case (A1_A2 O1 O2 _ Hx);auto.
   +  intros x Hx; destruct (A2_A1 Hx);auto.
 -  intros a Ha; destruct (A1_A2 O1 O2 a Ha);auto.
Qed.

End ordering_function_unicity.

Lemma ordering_function_seg_unicity : forall A1 A2 B, 
           ordering_segment A1 B ->
           ordering_segment A2 B -> A1 = A2.
Proof.
 destruct 1 as [f1 Hf1];  destruct 1 as [f2 Hf2]; 
 apply Extensionality_Ensembles.
 assert (H : fun_equiv f1 f2 A1 A2)
   by (eapply ordering_function_unicity;eauto); now destruct H.
Qed.



(** Let us build now an ordering function, and the associated ordering segment
 of any subset B composed of ordinals *)
    

Lemma proper_of_proper : forall B beta beta',
                           ordinal beta -> In B beta ->
                           In (proper_segment_of B beta) beta' ->
                           proper_segment_of B beta' =
                           proper_segment_of (proper_segment_of B beta) beta'.
Proof with  eauto with schutte.
 intros; apply Extensionality_Ensembles; split.
 - red; destruct 1; split. 
   + split;auto.
     destruct H3; split.
     * apply lt_trans with beta'...
       case H1;tauto.
     * auto.
   + decompose [and] H3;  split;auto.
 - red; destruct 1;auto.
   split.
   +  case H2;auto.
   +  split.
    * tauto.  
    * destruct  H3, H4 ...
Qed.

Section building_ordering_function_1.
 Variable B : Ensemble Ord.

 Hypothesis H_B : forall beta, In B beta ->
                               exists! A : Ensemble Ord,
                                    ordering_segment A
                                             (proper_segment_of B beta).
  
 Section beta_fixed.

 Variable beta : Ord.
 Hypothesis beta_B : In B beta.

 (** Let us build an ordering function for (proper_segment_of B beta) *)
  
 Definition _A := the  (fun E =>
                          ordering_segment E  (proper_segment_of B beta)).
 
 
 Definition _f := some  (fun f => 
                           ordering_function f _A
			                     (proper_segment_of B beta)).


 Lemma of_beta' : ordering_function _f _A (proper_segment_of B beta).
 Proof.
   pattern _f; unfold _f; apply epsilon_spec;
     destruct (H_B  beta_B) as [x [H1 H2]].
   case H1; intros x0 H;  exists x0;auto.
   unfold _A; apply iota_ind.
   - exists x; split; auto.
   - intros a H0;  destruct H0;  replace a with x; auto.
 Qed.



 Remark Bbeta_denum : countable (proper_segment_of B beta).
 Proof.
  apply AX2; exists beta;  destruct 1;tauto.
 Qed.

Hint Resolve  of_beta': schutte.

Remark A_denum : countable _A.
Proof.
 eapply countable_bij_funR.
 - eapply Ordering_bijection;   eauto with schutte.
 - apply Bbeta_denum;eauto.
Qed.

Lemma Proper_A : proper_segment _A.
Proof.
 apply countable_segment_proper.
 - eapply SA1; eauto with schutte.
 - eapply A_denum.
Qed.

Lemma g_def1  : exists g_beta: Ord,  ordinal g_beta /\ _A = members g_beta.
Proof.
 generalize (proper_members Proper_A); intros (a,Ha);exists a;split.
 - now destruct Ha. 
 - eapply Extensionality_Ensembles; tauto.
Qed.


Lemma g_unic : forall g_beta g_beta', ordinal g_beta ->
                                      ordinal g_beta' ->
                                      _A = members g_beta ->
                                      _A = members g_beta' ->
                                      g_beta = g_beta'.
Proof.
  intros g_beta g_beta' H H0 H1 H2;  rewrite H2 in H1;clear H2.
  assert (Same_set  (members g_beta') (members g_beta)).
  { rewrite H1; split;auto with schutte. }
  case H2; unfold Included, members; intros; apply le_antisym.
 - apply not_gt_le; auto with schutte.
   intro H5; generalize (H4 g_beta'); intros H6; unfold In in H6.
   case (@lt_irr g_beta');  now apply H6. 
 - apply not_gt_le; auto with schutte.
   intro H5;  generalize (H3 g_beta);intros H6;
     destruct  (@lt_irr g_beta);  now apply H6.   
Qed.

Definition g := iota inh_Ord (fun o => ordinal o /\ _A = members o).

End beta_fixed.

Lemma g_def : forall beta, In  B beta ->  _A beta = members (g beta ).
Proof.
  intros.
  pattern (g beta); unfold g; apply iota_ind.
  - case (g_def1 H);  intros a' [Ha' Ha'']; exists a'; split;auto.
    intros x (Hx,H'x);  eapply g_unic;eauto.
  -  now intros x ((Hx,H'x),U).
Qed.


Lemma g_lemma : 
  forall beta, In B beta ->
       ordering_function (_f beta) (members (g beta))
                                       (proper_segment_of B beta).
Proof.
 intros beta H; rewrite <- g_def.
 - now   apply of_beta'.
 - assumption.
Qed.

Lemma g_mono : forall beta1 beta2, In B beta1 -> In B  beta2 ->
                                   beta1 < beta2 ->
                                   g beta1 < g beta2.
Proof with eauto with schutte.
 intros beta1 beta2 H H0 H1.
 assert( B2 : fun_bijection (members (g beta2))
                            (proper_segment_of B beta2)
                            (_f beta2)) .
 { apply Ordering_bijection, g_lemma ... }
 assert (B3 : In (proper_segment_of B beta2) beta1).
 { split.  apply H. split; assumption. }
  assert (B4 : exists alpha,  alpha < g beta2 /\ _f beta2 alpha= beta1).
 { destruct B2; case (H3 beta1) ... }

 case B4; intros alpha (Ha2,Ha3).
 assert (B5 : ordering_function (_f beta2) (members alpha) 
                                (proper_segment_of B beta1)).
 { repeat split ...
   - red;  intros;   apply lt_trans with alpha0;eauto.
   -  case B2;intros;  clear H4 H5; red in H3.
      + generalize (H3 a); intros H4;  clear H3;  case H4.
        * red; apply lt_trans with alpha; auto.
        *  auto.
   -  case (g_lemma H0). 
      intros H3 H4; decompose [and] H4; clear H4.
      replace beta1 with (_f beta2 alpha).
      apply H8;auto.
      +   red;  apply lt_trans with alpha;auto.
   -  destruct 1;  case (g_lemma H0).
      intros H4 H5;  decompose [and] H4;  clear H4;  decompose [and] H5.
       case (H7 b). 
      + split;auto.
        split;auto.
        eapply lt_trans;eauto.
        case H3;auto.
       +  intros a (Ha,Ha');exists a;split;auto.
          red;  tricho  a alpha X.
         *  auto.
         * subst a; rewrite Ha3 in Ha'.
           subst b; case H3;intros H33 _.
           case (@lt_irr _ H33).
         *  assert (beta1 < b).
           { rewrite <- Ha3; rewrite <- Ha'.
             case (g_lemma H0); intros;  decompose [and] H9.
             apply H13;auto.
           }
           case (@lt_irr beta1);  apply lt_trans with b;auto.
           case H3;auto.
   - intros; case (g_lemma H0); intros;  decompose [and] H6.
     apply H10;auto.
     red;  apply lt_trans with alpha;auto.
    red;  red; apply lt_trans with alpha;auto.
 }
 generalize (g_lemma H);intro.
 generalize (ordering_function_unicity B5 H2). 
 destruct 1.
 generalize (Extensionality_Ensembles _ _ _ H3).
 intros;  generalize (members_eq   H5).
 intro; subst alpha;auto.
Qed.


Lemma L3a : segment (image B g).
Proof.
  intros gbeta alpha  (beta,(H1,H2)) H3;  subst gbeta. 
     generalize (g_lemma H1);intro.
     case H; intros.
     decompose [and] H2;clear H2.
     assert (exists beta0, In (proper_segment_of B beta) beta0 
                      /\ _f beta alpha=beta0).
     {  exists (_f beta alpha); split;auto.
     }
     case H2;intros beta0 (H9,H10); clear H2.
     assert (B5 : ordering_function (_f beta) (members alpha) 
                 (proper_segment_of B beta0)).
     { 
       repeat split;  auto with schutte. 
       - red;  red; intros.  apply lt_trans with alpha0;eauto.
       - assert( B2 : fun_bijection (members (g beta))
                                  (proper_segment_of B beta) (_f beta)) .
        { apply Ordering_bijection ;   apply g_lemma; auto. }
         case B2;intros H77 H11 H12;  generalize (H77 a).
         intros H13;  clear H77;  case H13.
         2:auto.
        red;  apply lt_trans with alpha; auto.
 
       -  case (g_lemma H1); intros.   decompose [and] H8.
        clear H8;  replace beta0 with (_f beta alpha).
        apply H14;auto.
        red;  red;  apply lt_trans with alpha;auto.
       -  case H9;  auto.
       - destruct 1; case (g_lemma H1); intros;  decompose [and] H11.
         clear H11;  case (H14 b).
         split;auto.
         split;auto.
         apply lt_trans with beta0;auto.
         case H5;auto.
         case H9;auto.
         destruct 2; auto.
         intros a (Ha,Ha');exists a;split;auto.
         red; tricho  a alpha X.
         + auto.
        + subst a; rewrite H10 in Ha'.
          subst b;case H5; intros H77 _.
          case (@lt_irr _ H77).
        + assert (beta0 < b) by (rewrite <- H10; rewrite <- Ha'; auto).
          case (@lt_irr beta0).
          apply lt_trans with b;auto.
          case H5;auto.
        - intros; case (g_lemma H1); intros;  decompose [and] H12.
          apply H16;auto.
          red;  apply lt_trans with alpha;auto.
          red; red;  apply lt_trans with alpha;auto.
       }
     generalize (g_lemma (beta:=beta0));intros.
     case H9;intros H5 H8;  generalize (H2 H5).
     intros H12; generalize (ordering_function_unicity B5 H12). 
     destruct 1;  generalize (Extensionality_Ensembles _ _ _ H11).
     intros H14; generalize (members_eq (alpha:=alpha)(beta:=g beta0)   H14 ).
     exists beta0;split;auto.
Qed.

 Lemma g_bij : fun_bijection B (image B g) g.
 Proof.
 split.
 -  intros a H ; exists a;split;auto.
 -  red; destruct 1;  exists x;split;auto.
   +  case H;auto.
   +  case H;auto.
 - red;intros a b; tricho a b Hab; trivial.
   intros H H0 ; generalize (g_mono H H0 Hab); auto.
   + intros H1 H2.   rewrite H2 in H1;  case (@lt_irr _ H1); auto.
   + intros H H0 H1; generalize (g_mono H0 H Hab); intro; rewrite H1 in H2; 
      case (@lt_irr _ H2).
 Qed.

 Hint Resolve g_bij : schutte.


Let g_1 := inv_fun inh_Ord B (image B g) g.

Lemma g_1_bij : fun_bijection (image B g) B g_1.
Proof.
 unfold  g_1; apply inv_fun_bij; auto with schutte.
Qed.

Hint Resolve g_1_bij : schutte.


Lemma g_1_of : ordering_function g_1 (image B g) B.
Proof.
 split.
 -  apply L3a.
 - repeat split; auto.
  +   destruct 1 as [x [H0 H1]]. rewrite <- H1.
      replace (g_1 (g x)) with x;  auto.
      symmetry;unfold g_1;eapply inv_compose;eauto.
      auto with schutte.
 + intros b H;  exists (g b);  split;auto.
   *  exists b;  split;auto.
   *  unfold g_1;eapply inv_compose;eauto.
      auto with schutte.
 +  intros;  tricho (g_1 a) (g_1 b) Hab; auto with schutte.
    * case g_1_bij; intros.
      generalize (H2 a H).
      case g_1_bij; intros.
      generalize (H2 b H0).
      replace a with (g (g_1 a)) in H1.
      replace b with (g (g_1 b)) in H1.
      rewrite Hab in H1.
      case (@lt_irr _ H1).
      unfold g_1;  apply inv_composeR;  auto with schutte.
      unfold g_1;  apply inv_composeR;  auto with schutte.
    *  case (le_not_gt (a:=a)(b:= b));  auto with schutte.
       replace a with (g (g_1 a));
         replace b with (g (g_1 b)) .
       apply g_mono;auto with schutte.
       case g_1_bij;auto with schutte.
       case g_1_bij;auto with schutte.
     all :  unfold g_1;  apply inv_composeR;  auto with schutte.
Qed.

Lemma image_B_g_seg  : ordering_segment (image B g) B.
Proof.
 exists g_1;  apply g_1_of.
Qed.

(** Corresponds to Lemma 3 of Schutte's chapter :
    It is used twice in the building of ordering function for any subset B of ordinal *)


Lemma L3_u : exists! S, ordering_segment S B.
Proof.
 exists (image B g);  split.
 - apply image_B_g_seg.
 - intros ;eapply ordering_function_seg_unicity;eauto.
   apply image_B_g_seg.
Qed.

 
End building_ordering_function_1.

(** For any set [B], we build by transfinite induction the ordering segment of 
  [B] and the (unique upto extensionnality) ordering function of B 
 *)


Section building_ordering_function_by_induction.

 Variable B : Ensemble Ord.

 Lemma ordering_segments_of_B (beta : Ord) :
  In B beta ->
  exists! A : Ensemble Ord,
    ordering_segment A  (proper_segment_of B beta).
  Proof with eauto with schutte.
    intros  Hbeta; pattern beta; apply transfinite_induction.
    -  intros a  H0;  apply L3_u.
    +   intros beta0 H1;
      rewrite <- (proper_of_proper (B:=B) (beta:=a) (beta':=beta0))...
      apply H0...
        *  destruct H1 ; tauto.
        *  destruct H1; tauto.  
Qed.


 
 Theorem ordering_segment_ex_unique : exists! S, ordering_segment S B.
 Proof.
   apply L3_u,  ordering_segments_of_B.
 Qed.


Theorem ordering_function_ex : exists ! S, exists f, ordering_function f S B.
Proof with eauto.
 case ordering_segment_ex_unique;intros S (f,pi); exists S.
  split.
  -  case f;intros x H;  exists x;auto.
  -  intros x' H;  case H; intros;case f;intros.
     eapply ordering_function_seg_unicity...
Qed.

 
Lemma ord_ok :
  ordering_function (ord  B) (the_ordering_segment B) B.
Proof.
  pattern (ord  B);  apply epsilon_spec. 
  pattern (the_ordering_segment B);
    apply iota_spec,  ordering_segment_ex_unique.
Qed.

Lemma segment_the_ordering_segment  :
  segment (the_ordering_segment B).
  unfold the_ordering_segment.
  apply iota_ind.
  apply ordering_segment_ex_unique.
  destruct 1.
  destruct H.
  now  destruct H.
Qed.




Lemma ord_eq (A : Ensemble Ord) (f : Ord -> Ord) :
  ordering_function f A B ->
  fun_equiv f (ord B) A (the_ordering_segment B).
 Proof with eauto with schutte.
   intros;eapply ordering_function_unicity...
   apply ord_ok.
 Qed.


End building_ordering_function_by_induction.


Lemma of_image : forall f A B, ordering_function f A B ->
                               ordering_function f A (image A f).
Proof.
 intros f A B O; case O; intros H H0;  decompose [and] H0.
 repeat split;auto.
 intros; exists a; auto. 
Qed.


Section Th13_5.
 Variables (A B : Ensemble Ord).
 Variable f : Ord -> Ord.
 Hypothesis f_ord : ordering_function f A B.

 Section recto.

 Hypothesis f_cont : continuous f A B.
 (* begin hide *)
 
 Section M_fixed.
 Variable M : Ensemble Ord.
 Hypothesis inc : Included M B.
 Hypothesis ne : Inhabited _ M.
 Hypothesis den : countable M.

 Let U := fun u => In A u /\ In M ( f u).

 Remark fbij : fun_bijection A B f.
  apply Ordering_bijection; auto.
 Qed.

 
 Remark restrict : fun_bijection U M f.
 Proof.
   split.
   -  destruct 1;auto.
   - red; case fbij.
     intros  H H0 H1 b H2; case (H0 b).
     +   apply inc;auto.
     +  intros x (Hx,H'x); exists x;split;auto.
        red;unfold U; split;auto.
        subst b;auto.
   -  red; destruct 1.
      destruct 1.
      intros H3; case fbij;intros; now  apply H6.
Qed.
 
 Remark Inc_U_A : Included U A.
 Proof. now destruct 1. Qed.
 
 Remark den_U : countable U.
 eapply countable_bij_funR with Ord M f;auto.
 apply restrict.
 Qed.


 Remark inh_U : Inhabited _ U.
 Proof.  
   case ne;intros.
   exists (inv_fun inh_Ord A B f x).
   red; unfold U; rewrite inv_composeR.
   -  split;auto.
      generalize (Ordering_bijection f_ord); 
      intros;    generalize (inv_fun_bij inh_Ord H0).
      intros;  destruct H1.
      apply H1.
      apply inc;auto.
   -  apply fbij.
   -   apply inc;auto.
 Qed.

 
 Remark im_U_f : (image U f : Ensemble Ord)  = M.
 Proof.
   eapply Extensionality_Ensembles;    split.
   red;destruct 1;  unfold U in H;  case H.
   intros;   case H0;intros.
   subst x;auto.
   red;  intros.
   exists (inv_fun inh_Ord A B f x);  split.
   red;red;  generalize (Ordering_bijection f_ord).
   intros;   split.
   case (inv_fun_bij inh_Ord H0).  
   auto.
   intros;   destruct H0.
   rewrite inv_composeR; auto with schutte.
   apply fbij.
   apply inc;auto.
   rewrite inv_composeR; auto with schutte.
   apply fbij.
   apply inc;auto.
 Qed.

 
 Lemma sup_M_in_B : In B (|_| M).
 Proof.
  rewrite <- im_U_f.   case f_cont.  intros H [H0 H1].
  rewrite H1; auto.
  -  apply H.
     apply H0.
     + apply Inc_U_A.
     + apply inh_U.
     + apply den_U.
  -  apply Inc_U_A.
  -  apply inh_U.
  - apply den_U.
Qed.

End M_fixed.

 (* end hide *)
 
 Lemma Th_13_5_1 : Closed B.
 Proof.
    red.
   intros;    apply sup_M_in_B; auto.
 Qed.


End recto.

Section verso.
 Hypothesis B_closed : Closed B.

 (* begin hide *)
 
 Section U_fixed.
 Variable U : Ensemble Ord.
 Hypothesis U_non_empty : Inhabited _ U. 
 Hypothesis U_den : countable U.
 Hypothesis U_inc_A : Included U A.

 (* apply Virgile's technique ? *)

 Remark R1_aux : countable (image U f).
 Proof.
 apply countable_bij_fun with Ord U f.
 - case (Ordering_bijection f_ord); intros H H0 H1;  split.
  + intros u u_In_U;  exists u; auto.
  +  intros u u_In_img; case u_In_img;  intros x Hx.
      exists x; assumption.
  +  intros u1 u2 u1_In_U u2_In_U Heq; apply H1;
       try apply U_inc_A; assumption.
 -  assumption.
 Qed.

 Definition R1 := let foo := U_den in R1_aux.
 Opaque R1.


 Remark R2 : In B (|_| (image U f)). 
 Proof.
   apply  B_closed.
   -  red;red;  destruct 1.
      case f_ord; intros _ (_,(H2,_)).
      case H;intros; subst x; destruct f_ord.
      decompose [and] H3.
      apply H4; apply U_inc_A;auto. 
   -  case U_non_empty;intros x H;  exists (f x);auto.
      exists x;auto.
   - apply R1_aux.
 Qed.

Remark R3: exists alpha, In A alpha /\ f alpha = |_|  (image U f).
Proof.
 case f_ord.
 intros H H0;  decompose [and] H0.
  case (H3 (|_|image U f)).
  -  apply R2.
  -  intros x; exists x;auto.
Qed.

Let alpha_ : Ord :=
  (epsilon inh_Ord (fun alpha =>  In A alpha /\ f alpha = sup(image U f))).



Lemma alpha_A :   In A alpha_.
Proof.
  unfold alpha_;  apply epsilon_ind.
  - apply R3. 
  -  tauto.
Qed.

Lemma alpha_sup : f alpha_ = |_| (image U f). 
Proof.
 pattern alpha_; epsilon_elim.
 - apply R3.
 - tauto.
Qed.

Remark R5 : forall khi, In U khi -> f khi <= f alpha_.
Proof.
 intros; rewrite alpha_sup;  apply sup_upper_bound.
 -  apply R1.
 -  exists khi; tauto. 
Qed.


Remark R6 : forall khi, In U khi ->  khi <=  alpha_ .
Proof with eauto with schutte.
 intros khi H; case (R5 H).
 -  left.  
   +  case (Ordering_bijection f_ord). 
      intros H1 H2 H3; apply H3.
    *  apply U_inc_A;auto.
    * apply alpha_A.
    *  case H0;auto.
 -  right; case f_ord; intros _ H1; decompose [and] H1.
    tricho khi alpha_ H7; auto.
   +    subst khi; case (@lt_irr _ H0).
   + case (@lt_irr (f alpha_));auto.
     apply lt_trans with (f khi); auto.
     * apply H5; auto.
      apply alpha_A;  auto.
Qed.


Hint Resolve  alpha_A : schutte.
 
Remark R7 : |_| U <= alpha_ .
Proof. 
 apply sup_least_upper_bound; trivial.
 (*-  intros y H;  destruct f_ord as [H0 H1].
    destruct H0;  apply H0;  now apply U_inc_A.*)
 (*-  destruct f_ord as [H H0]; destruct H.
    apply H, alpha_A. *)
 - intros;now apply R6.
Qed.
 
 
Remark R4 : forall khi, In U khi -> khi <= sup U.
Proof.
 intros;  apply sup_upper_bound;auto.
Qed.

 (* Schutte's remark "hence A is closed " is out of this section *)


Lemma A_closed : In A (sup U).
Proof.
  assert (H: segment A) by (eapply SA2;  eauto).
  case R7.
  - intros  H3; rewrite H3; apply alpha_A.
  - intros;red.  eapply H with alpha_ ;auto with schutte.
Qed.


Remark R4' : forall khi, In U khi -> f khi <= f (sup U).
Proof.
 intros; case f_ord;intros. 
 decompose [and] H1.
 clear H1; case (R4 H).
 - intro;  subst khi;left;auto with schutte.
 -  right;auto.
    apply H5;auto with schutte.
    apply A_closed;auto.
Qed.

Remark R4'' : |_| (image U f) <= f (sup U).
Proof.
 apply sup_least_upper_bound.
 -  apply R1.
 - intros y H; destruct H; destruct H;subst y;
     apply ordering_function_mono_weak with A B; auto.
   +  apply  A_closed.
   +  apply sup_upper_bound;auto.
Qed.


Remark R42 : f (sup U) <= |_| (image U f).
Proof.
 apply le_trans with (f alpha_).
 -  case f_ord;intros.
    decompose [and] H0;clear H0.
    case R7.
    +  intro H5; rewrite H5;auto with schutte.
    +  right;auto.
       apply H4;auto with schutte.
       apply A_closed;auto with schutte.
 -  unfold alpha_; apply epsilon_ind.
    + apply R3.
    + destruct 1; left;   auto.
Qed.

Lemma f_sup_commutes : f (|_| U) = |_| (image U f).
Proof.
 apply le_antisym.
 -  apply R42.
 -  apply R4''. 
Qed.

End U_fixed.

 (* end hide *)

 Lemma Th_13_5_2 : continuous f A B.
 Proof.
   split.
   - red.
     case f_ord;tauto.
   - split. red. intros. 
     eapply A_closed;auto.
     intros;symmetry;apply f_sup_commutes;auto.
 Qed.


End verso.

End Th13_5.


Theorem TH_13_6 (B : Ensemble Ord)(f : Ord -> Ord) :
  normal f B ->   Closed B /\ Unbounded B.
Proof with eauto with schutte.
 destruct 1.
 split.
 -  eapply Th_13_5_1;eauto.
 -  intros x;  generalize (Ordering_bijection H).
    destruct 1 as [H3 H4 H5].
    exists (f (succ x));  split.
    +  apply H3 ... 
    +  apply le_lt_trans with (f x).
       * eapply ordering_le ... 
       *  eapply ordering_function_mono ...
Qed.


Lemma ordering_unbounded_unbounded : 
  forall A B f,  ordering_function f A B ->
                 (Unbounded B <-> Unbounded A).
Proof with auto with schutte.
  intros A B f  H0;split.
  - intro; apply not_countable_unbounded.
    intro H2;  assert (H3 : countable B).
    {  apply countable_bij_fun with Ord A  f ... 
       apply Ordering_bijection;auto.
    }
    case (countable_not_Unbounded  H3);auto.
  - intro H1;  apply not_countable_unbounded ...
    intro H2;  assert (H3 : countable A).
    { apply countable_bij_funR with Ord   B  f;auto.
      apply Ordering_bijection;auto.
    }
 case (countable_not_Unbounded (X:= A));auto.
Qed.


Theorem TH_13_6R (A B : Ensemble Ord) (f : Ord -> Ord) : 
  ordering_function f A B ->
  Closed B ->    Unbounded B ->   normal f B.
Proof with auto with schutte.
  intros  H0 H1 H2; assert (A = ordinal).
    {   apply segment_unbounded.
        - eapply SA1;  apply H0.
        - destruct (ordering_unbounded_unbounded H0); auto.
    }
    subst A; split; [trivial | now apply Th_13_5_2].
Qed.


Lemma order_function_least_least : 
 forall B f  , ordering_function f ordinal B ->
     least_member  lt B (f zero).
Proof with auto with schutte.
 intros b f H; case H; intros H0 H1; decompose [and] H1; clear H1.
 case H; intros H8 (H9,H10); split.
 -  apply H2 ...
 -  intros x  H55;  decompose [and] H10.
   case (H1 _ H55); intros x0 (Hx0,H'x0); subst x.
   generalize (ordering_function_mono_weak H (a:=zero) (b:=x0)).
   intro H6;  apply H6 ...
Qed.

Lemma segment_lt_closed : forall A a b, segment A -> 
                                          In A b -> 
                                          a < b -> 
                                          In A a. 
Proof.
 intros A a b H H0 H1; apply H with b;  auto. 
Qed.

Lemma th_In A  alpha : In (the_ordering_segment A) alpha ->
                             In A (ord A alpha). 
Proof.
  unfold ord;  intro H;   red;  unfold some;  apply epsilon_ind.
  - destruct   (ordering_function_ex A) as [X [[f Hf] H0]];  exists f. 
   rewrite <-  (H0 (the_ordering_segment A) );  auto.
   exists (ord A); apply ord_ok.
  -   intros beta H0;  eapply ordering_function_In; [ eexact H0 | trivial].
Qed. 


Arguments ord  : clear implicits.
Arguments the_ordering_segment : clear implicits.
