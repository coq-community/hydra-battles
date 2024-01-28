
(**  A notation system for the ordinal [omega^2]  *)

(** Pierre Castéran, Univ. Bordeaux and LaBRI *)

From Coq Require Import Arith Compare_dec Lia.
From hydras Require Import Simple_LexProd ON_Generic
        ON_mult  ON_Omega Compat815.

Import Relations ON_Generic.

Open Scope ON_scope.

(* begin snippet Omega2Def:: no-out *)

#[ global ] Instance compare_omega2 : Compare ON_mult.t :=
 compare_mult compare_nat compare_nat.

#[ global ] Instance Omega2: ON _ compare_omega2 := ON_mult Omega Omega.

Definition t := ON_t.
(* end snippet Omega2Def *)

Open Scope ON_scope.

(* begin snippet Defs *)

Notation omega := (1,0).
Definition zero: t := (0,0).

Definition fin (i:nat) : t := (0,i).
Coercion fin : nat >-> t.

(* end snippet Defs *)

(* begin snippet Ex1:: no-out *)
Example ex1 : (5,8) o< (5,10).
Proof. right; auto with arith. Qed.
(* end snippet Ex1 *)


Compute ON_compare omega (fin 42).

Compute ON_compare (8:t) omega.



Lemma omega_is_limit : Limit omega. 
Proof.
  split.
  + exists (fin 8); constructor.
    auto with arith.
  + inversion 1; subst.
    * assert (a= 0) by lia; subst a.
      exists (0, S b); split.
      -- constructor 2; auto.
      -- constructor 1; auto.
    * exfalso; lia. 
Qed.

(* begin snippet succ *)

Definition succ (alpha : t) := (fst alpha, S (snd alpha)).

(* end snippet succ *)

Lemma eq_dec (alpha beta: t) : {alpha = beta} + {alpha <> beta}.
Proof.  
 repeat decide equality.
Defined.


Lemma le_intror :
  forall i j k:nat, (j <= k)%nat -> (i,j) o<= (i,k).
Proof.
  intros i j k H; destruct (Compat815.le_lt_or_eq j k H).
  - left; now constructor 2.    
  - subst k; now right.
Qed.

Lemma le_0 : forall p: t,  (0,0) o<= p.
Proof.
  destruct p, n ; auto.
  - apply le_intror; lia. 
  - left; left; lia.
Qed.

(* begin snippet succLemmas *)

Lemma lt_succ_le alpha beta :
  alpha o< beta <-> succ alpha o<= beta. (* .no-out *)
(* ... *)
(*|
.. coq:: none
|*)

Proof.  
 destruct alpha, beta. unfold succ; cbn.
 split.
  - inversion_clear 1.
  + left; now left.
  +  now apply le_intror.
  -  intros;  eapply lt_le_trans .
    instantiate (1 := (n, S n0)). 
    right; auto.
   assumption.
Qed.
(*||*)
   
(*|
.. coq:: no-out
|*)
 
Lemma lt_succ alpha : alpha o< succ alpha. 
Proof. 
  destruct alpha; right; cbn; abstract lia.
Qed.

(*||*)

(* end snippet succLemmas *)

#[global] Hint Constructors clos_refl lexico : O2.
#[global] Hint Unfold lt le : O2.




Lemma compare_reflect alpha beta :
  match (ON_compare alpha beta)
  with
    Lt => alpha o< beta
  | Eq => alpha = beta
  | Gt => beta o< alpha
  end.
Proof.
  destruct alpha, beta; cbn; unfold ON_compare.
  destruct (comparable_comp_spec (n,n0) (n1,n2)).
  - rewrite H, compare_refl; reflexivity.
  - apply compare_lt_iff in H.
    rewrite H.
    apply compare_lt_iff.
    assumption.
  - apply compare_gt_iff in H.
    rewrite H.
    apply compare_gt_iff.
    assumption.
Qed.

Lemma compare_correct alpha beta :
    CompSpec eq ON_lt alpha beta (ON_compare alpha beta).
Proof.
  generalize (compare_reflect alpha beta).
  destruct (ON_compare alpha beta); now constructor. 
Qed.




Lemma zero_le alpha : zero o<= alpha.
Proof.
  destruct alpha as [i j]; destruct i.
  - destruct j.
    + right.
    + left;  right; abstract lia.  
  - left; left; abstract lia.
Qed.


Lemma Least_zero alpha : Least alpha <-> alpha = zero.
Proof.
  split.
  destruct alpha as [i j]; destruct i.
  - destruct j; [ reflexivity| ].
    intro H; specialize (H (0,j)); exfalso.
    inversion H. inversion H0; abstract lia.
    abstract lia.
  -  intro H; specialize (H (0,0)); exfalso.
     inversion H. inversion H0; abstract lia.
  - intro; subst; intro; apply zero_le.
Qed.



Definition Zero_limit_succ_dec : ZeroLimitSucc_dec.
  - intro alpha; destruct alpha as [n p].
    + destruct p.
      * destruct n.
        --   left; left; exact le_0.
        -- left;right;  split.
           ++  exists (0,0).
             constructor 1; auto with arith.
           ++  destruct y; inversion 1; subst.
               ** exists (n0, S n1); split.
                 right; auto with arith.
                 left; auto.
               ** abstract lia.
      * right; exists (n,p); split.
        -- constructor 2; auto with arith.
        -- destruct z; unfold lt; cbn.
           inversion 1; subst;
             inversion 1; subst;try lia.
Defined.

Lemma lt_eq_lt_dec alpha beta :
  {alpha o< beta} + {alpha = beta} + {beta o< alpha}.
Proof.
 generalize (compare_reflect alpha beta).
 case_eq (ON_compare alpha beta).
  - intros; left; now right.
  - intros; left; now left.
  - intros; now right.
Defined.

Lemma Successor_inv : forall i j k l : nat, Successor (k, l) (i, j) ->
                                            i = k /\ l = S j.
Proof.
  destruct 1 as [H H0].
  assert (H1 : (i< k \/ i=k /\ j <l)%nat) by (inversion_clear H; auto).
  destruct H1 as [H1 | [H1 H2]].
  - destruct  (H0 (i, (S j))).
    constructor 2; auto.
    constructor 1;auto.
  -  subst; destruct (Compat815.le_lt_or_eq _ _ H2); auto.
      destruct (H0 (k, S j));  constructor 2; auto.
Qed. 

Corollary Successor_not (i j k : nat) : ~ Successor (k,0) (i,j).
Proof.
  intro H; apply Successor_inv in H. destruct H; discriminate. 
Qed.

Lemma Successor_succ : forall alpha,  Successor (succ alpha) alpha.
Proof.
  destruct alpha;red;cbn; split.
  - right; auto.
  -  destruct z  as [n1 n2]; unfold succ; cbn; intros H H0;
     inversion H0;   subst;  inversion H;  subst; abstract lia.
Qed.

(* begin snippet succOk *)

Lemma succ_ok alpha beta :
  Successor beta alpha <-> beta = succ alpha. (* .no-out *)
(* ... *)
(*|
.. coq:: none 
|*)
Proof.
  split.  
  - destruct alpha, beta; intro H.
    apply Successor_inv in H. destruct H;subst. reflexivity.
  - intros; subst ; apply Successor_succ.
Qed.
(*||*)

(* end snippet succOk *)

Definition succb (alpha: t): bool
  := match alpha with
       (_, S _) => true
     | _ => false
     end.

Definition limitb (alpha : t): bool :=
  match alpha with
    (S _, 0) => true
  | _ => false
  end.


Lemma Omega_limit_limitb alpha s : Omega_limit s alpha ->
                                   limitb alpha.
Proof.
   destruct alpha.
   destruct 1.
   destruct n0.
   - destruct n.
    +   specialize (H 0).
       inversion H; abstract lia.
    + now  cbn.
   -   destruct (H0 (n, n0)).
    + right; auto with arith. 
    + specialize (H x).
      assert ((n,n0) o< s x).
 apply H1.
     rewrite  lt_succ_le in H2.
     assert (s x o< s x) by (eapply lt_le_trans; eauto).
     destruct (ON_mult.lt_strorder Omega  Omega) as [H4 H5].
     destruct (H4 _ H3).
Qed.

(** Canonical sequences *)

Definition canon  alpha i :=
  match alpha with
    (0,0) => (0,0)
  | (_, S p) => (0,p)
  | (S n, 0) => (n, i)
  end.



Lemma limitb_limit alpha :
  limitb alpha -> Omega_limit (canon alpha) alpha.
Proof.
  destruct alpha;  inversion 1.
  destruct n; [discriminate | unfold canon].
  split;  destruct n0; try discriminate.
  -    left; auto with arith.
  -  destruct y; inversion_clear 1.
     exists (S n1).
     assert( H0: (n0 = n \/ n0 <  n)%nat) by lia.
     destruct H0.
     + subst;  right; auto.
     + left; auto.
     + abstract lia.    
Qed.

 Example Ex1 : limitb omega.
 Proof. reflexivity.  Qed.


 (* to simplify ? *)
 
Lemma limit_is_lub_0 : forall i alpha, (forall j, (i,j) o< alpha) <->
                                 (S i, 0) o<= alpha.
Proof.
  intros i (k,l) ;split; intro  H .
  -   destruct (lt_eq_lt_dec (S i, 0) (k,l)) as [[Hlt | Heq] | Hgt].
      + now left.
      + rewrite Heq; now right.
      + destruct (limitb_limit (S i,0)) as [H1 H2].
        * red; trivial.
        * simpl in H1; destruct (H2 _ Hgt) as [x H0].
        simpl in H0.
        specialize (H x).
     destruct (ON_mult.lt_strorder Omega Omega) as [H3 H4].
     destruct (H3 (k,l)).        
     transitivity (i,x); auto.
  -    inversion_clear H.
    + inversion_clear H0.
   *    intro.  left.  abstract lia.
   *    left; left; auto. 
     + left;left;auto. 
Qed.

Lemma limit_is_lub beta :
  limitb beta -> forall alpha, 
    (forall i,  canon beta i o< alpha) <-> beta o<= alpha.
Proof.  
  destruct beta;intros H alpha;destruct n, n0; try discriminate.
  apply limit_is_lub_0.
Qed.



 Definition zero_limit_succ_dec :
  forall alpha, 
                ({alpha = zero} + {limitb alpha }) + 
                {beta : t |  alpha = succ beta} .
 Proof.
   destruct alpha as (n,p); destruct p.
   - destruct n.
     + left; left;trivial.
     +  left; now right.
   - right; now exists (n,p).
 Defined.

 (* begin snippet plusDef *)
Definition  plus (alpha beta : t) : t :=
  match alpha,beta with
  | (0, b), (0, b') => (0, b + b')
  | (0,0), y  => y
  | x, (0,0)  => x
  | (0, _b), (S n', b') => (S n', b')
  | (S n, b), (S n', b') => (S n + S n', b')
  | (S n, b), (0, b') => (S n, b + b')
   end.

Infix "+" := plus : ON_scope.

Lemma plus_compat (n p: nat) :
  fin  (n + p )%nat =  fin n + fin p. (* .no-out *)
Proof. (* .no-out *) destruct n; reflexivity. Qed.

(* end snippet plusDef *)


(* begin snippet plusExamples *)

Compute 3 + omega.

Compute omega + 3.

Example non_commutativity_of_plus: omega + 3 <> 3 + omega. (* .no-out *)
Proof.  (* .no-out *) discriminate. Qed.
(* end snippet plusExamples *)

(* begin snippet multFinDef *)

(** multiplication of an ordinal by a natural number *)

Definition mult_fin_r  (alpha : t) (p : nat): t :=
  match alpha, p with
  |  (0,0), _  => zero
  |  _, 0 => zero
  |  (0, n), p => (0, n * p)
  |  (n, b), n' => ( n *  n', b)
  end.
Infix "*" := mult_fin_r : ON_scope.

(** multiplication of  a natural number by an ordinal *)

Definition mult_fin_l (n:nat)(alpha : t) : t :=
  match n, alpha with
  |  0, _  => zero
  |  _, (0,0) => zero
  |  n , (0,n') => (0, (n*n')%nat)
  |  n, (n',p') => (n', (n * p')%nat)
  end.

(* end snippet multFinDef *)

(* begin snippet multFinExamples:: no-out *)

Example e1 : (omega * 7 + 15) * 3 = omega * 21 + 15.
Proof. reflexivity. Qed.

Example e2 :  mult_fin_l 3 (omega * 7 + 15) = omega * 7 + 45.
Proof. reflexivity. Qed.

(* end snippet multFinExamples *)


#[global] Instance plus_assoc: Assoc eq  plus. 
Proof.
  intros (n,n0) (n1, n2) (n3,n4); cbn. 
  destruct n,  n0, n1, n2, n3, n4; cbn; auto; f_equal; abstract lia.
Qed.

Lemma succ_is_plus_1  alpha : alpha + 1 = succ alpha.
Proof.
 unfold succ ; cbn; destruct alpha; cbn; destruct n, n0; 
   try f_equal; abstract lia.
Qed.

Lemma lt_omega alpha : alpha o< omega <-> exists n:nat,  alpha = fin n.
Proof.
  destruct alpha; cbn; split.
  - inversion_clear 1.
    + inversion H0.
      * exists n0; reflexivity.
      *   inversion H1.
    +   inversion H0.
  -   destruct 1.
      injection H; intros; subst; constructor; auto.
Qed.

Lemma decompose (i j : nat): (i,j) = omega * i + j.
Proof.
  destruct i, j; cbn; (reflexivity || (try f_equal; lia)). 
Qed.

(* begin snippet uniqueDecompositiona:: no-out  *)

Lemma unique_decomposition (alpha: t) :
  exists! i j: nat, alpha = omega * i + j.
Proof.
(* end snippet uniqueDecompositiona *)
(* begin snippet uniqueDecompositionb *)
  destruct alpha as [i j]; exists i; split.
  (* ... *)
  (* end snippet uniqueDecompositionb *)
  -  exists j; split.
     + now rewrite decompose. 
     + intros x; repeat rewrite <- decompose; congruence.
  - intros x [y [Hy _]]; rewrite <- decompose in Hy; congruence.
(* begin snippet uniqueDecompositionz *)    
Qed.
(* end snippet uniqueDecompositionz *)    

(** ** Additive principal ordinals  *)

Definition ap (alpha : t) :=
  alpha <> zero /\
  (forall beta gamma,  beta o< alpha -> gamma o< alpha ->
                       beta + gamma o< alpha).

Lemma omega_ap : ap omega.
Proof.
 split; [discriminate |];intros beta gamma H H0; destruct beta, gamma.
 inversion H; subst.
 -  inversion H0; subst.
  +  inversion H2; inversion H3; subst; try lia.
     *  unfold plus; destruct n0; left; auto with arith.
     +  abstract lia.
 - abstract lia.
Qed.

Lemma ap_cases alpha : ap alpha -> alpha = 1 \/ alpha = omega.
Proof.
  destruct (zero_limit_succ_dec alpha) as [[Hzero |  Hlim] | Hsucc].
  - subst alpha; intro H; assert False by (destruct H as [H _]; auto); contradiction.
  - destruct alpha; unfold ap.
    destruct n, n0; try discriminate.
    intros [_ H1]; destruct n.
    + now right.
    +  right; specialize (H1 (S n,0) (S n,0)).
       assert (H2:(S n, 0) o< (S (S n), 0)) by (left; auto).
       specialize (H1 H2 H2).
       inversion H1; abstract lia.
  -  intro H;  destruct Hsucc as [beta e]; subst.
     destruct H as [_ H].
      destruct (eq_dec beta zero).
       + subst; now left.
       +  specialize  (H beta 1 (lt_succ beta)).
          assert (fin 1 o< succ beta). {
            destruct beta;  destruct n0, n1.
            * now destruct n.
            * right; cbn; abstract lia.
            * destruct n0; cbn.
              left; auto.
              left; simpl;abstract lia.
            * left; simpl; abstract lia.
          }
          *  specialize (H H0).
             rewrite <- succ_is_plus_1 in H.       
             destruct (ON_mult.lt_strorder  Omega  Omega) as [H3 H4].
             destruct (H3 _ H).        
Qed.




Compute (omega * 3).
Compute (omega * 3) * 6.

Compute (omega * 3 + 1) * 6.
Compute mult_fin_l 3 omega.
Compute (3,2)+(2,10).

Compute (2,2)+(3,10).

Compute (0,2)+(0,10).

Compute (0,2)+(1,10).


Open Scope ON_scope.

Example L_3_plus_omega :  3 + omega = omega.
Proof.
  now  apply Comparable.compare_eq_iff.
Qed.

(* begin snippet AckOmega2:: no-out *)

From Equations Require Import Equations.
Section A_def. 

Let m (x : nat * nat): t := omega * fst x + snd x.

#[ local ] Instance WF : WellFounded (measure_lt m):=
  wf_measure m.

Equations A (p : nat * nat) : nat by wf p (measure_lt m):=
    A (0, j) := S j;
    A (S i, 0) := A(i, 1);
    A (S i, S j) := A(i, A(S i, j)).

Next Obligation.
  (* ... *)
(* end snippet AckOmega2 *)
unfold m, measure_lt; cbn; destruct i; left; auto with arith.
Defined.
Next Obligation.
  unfold m, measure_lt; cbn; destruct j; right; auto with arith.
Defined.
Next Obligation.
  unfold m, measure_lt; cbn; destruct i; cbn. 
  - left; auto with arith.
  - case (A (S (S i), j) (A_obligations_obligation_2 (S i) j A));
        left; auto with arith.
Defined.

End A_def.
