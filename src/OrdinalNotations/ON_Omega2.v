(**  The ordinal omega * omega *)



Require Import Arith Compare_dec Lia Simple_LexProd
        OrdinalNotations.Generic.
Import Relations.

Declare Scope o2_scope.
Delimit Scope o2_scope with o2.
Open Scope o2_scope.

Coercion is_true: bool >-> Sortclass.

Definition t := (nat * nat)%type.

Definition lt : relation t := lexico Peano.lt Peano.lt.

Infix "o<" := lt : o2_scope.

(** reflexive closure of lt *)

Definition le := clos_refl _ lt.

Infix "o<=" := le : o2_scope.

Hint Constructors clos_refl lexico : O2.
Hint Unfold lt le : O2.


Definition zero: t := (0,0).

Definition fin (n:nat) : t := (0, n).

Notation "'F'" := fin : o2_scope.

Coercion fin : nat >-> t.


Definition succ (alpha : t) := (fst alpha, S (snd alpha)).

Notation "'omega'" := (1,0) : o2_scope.



Example ex1 : 6 o< omega.
Proof.
  left; auto with arith.
Qed.


Example ex2 : omega o< (1,1).
Proof.
 right; auto with arith.
Qed.


Instance lt_strorder : StrictOrder lt.
Proof. apply Strict_lex; apply Nat.lt_strorder. Qed.

Instance le_preorder : PreOrder le.
Proof.
  split.
  -  right.
  - inversion_clear 1; trivial.
    + inversion 1; left.
      * now transitivity y.
      * now subst.
Qed.

Lemma eq_dec (alpha beta: t) : {alpha = beta} + {alpha <> beta}.
Proof.  
 repeat decide equality.
Defined.

Lemma lt_wf : well_founded lt.
Proof. apply wf_lexico; apply lt_wf. Qed.

Lemma le_introl :
  forall i j k:nat, (j <= k)%nat -> (i,j) o<= (i,k).
Proof.
  intros i j k H; destruct (Lt.le_lt_or_eq j k H); auto with O2.
  - subst k; now right.
Qed.

Lemma le_0 : forall p: t,  (0,0) o<= p.
Proof.
  destruct p, n ; auto with arith O2.
  - apply le_introl;  auto with arith O2.
Qed.

(** cf Peano.lt's definition  in Stdlib *)

Lemma le_lt_trans : forall p q r, p o<= q -> q o< r -> p o< r.
Proof.
  destruct 1; trivial. 
  intro; now transitivity y.  
Qed.   

Lemma lt_le_trans : forall p q r, p o< q -> q o<= r -> p o< r.
Proof.
  destruct 2; trivial; now  transitivity q.
Qed.   


Lemma lt_succ_le alpha beta : alpha o< beta <-> succ alpha o<= beta.
Proof.  
 destruct alpha, beta. unfold succ; cbn.
 split.
  - inversion_clear 1.
  + left; now left.
  +  now apply le_introl.
  -  intros; apply lt_le_trans with (n, S n0); auto.
    right; auto.
Qed.

Lemma lt_succ alpha : alpha o< succ alpha.
Proof.
  destruct alpha; right; cbn; lia.
Qed.


Definition compare (alpha beta: t) : comparison :=
  match Nat.compare (fst alpha) (fst beta) with
    Eq => Nat.compare (snd alpha) (snd beta)
  | c => c
  end.

Hint Constructors clos_refl lexico : O2.
Hint Unfold lt le : O2.

Definition lt_b alpha beta : bool :=
  match compare alpha beta with
    Lt => true
  | _ => false
  end.

Definition le_b alpha beta := negb (lt_b beta alpha).

Definition eq_b alpha beta := match compare alpha beta with
                                Eq => true
                              | _ => false
                              end.

Lemma compare_reflect alpha beta :
  match (compare alpha beta)
  with
    Lt => alpha o< beta
  | Eq => alpha = beta
  | Gt => beta o< alpha
  end.
Proof.
  destruct alpha, beta; cbn. 
  case_eq (compare (n, n0) (n1, n2)); unfold compare; cbn;
  case_eq (n ?= n1); try discriminate;
    repeat (rewrite Nat.compare_eq_iff ||
            rewrite Nat.compare_lt_iff ||
            rewrite  Nat.compare_gt_iff); intros; subst; auto.
   - now right.
   - now left.
   - now right.
   - now left. 
Qed.

Lemma compare_correct alpha beta :
    CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
                (compare alpha beta).
Proof.
  generalize (compare_reflect alpha beta).
  destruct (compare alpha beta); now constructor. 
Qed.


Instance Omega2 : ON  lt compare.
Proof.
  split.
  - apply lt_strorder.
  - apply lt_wf.
  - apply compare_correct.
Qed.

Definition Zero_limit_succ_dec : ZeroLimitSucc_dec (on := Omega2).
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
               ** lia.
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
 case_eq (compare alpha beta).
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
  -  subst; destruct (le_lt_or_eq _ _ H2); auto.
      destruct (H0 (k, S j));  constructor 2; auto.
Qed. 

Corollary Successor_not i j k : ~ Successor (k,0) (i,j).
Proof.
  intro H; apply Successor_inv in H. destruct H; discriminate. 
Qed.

Lemma Successor_succ : forall alpha,  Successor (succ alpha) alpha.
Proof.
  destruct alpha;red;cbn; split.
  - right; auto.
  -  destruct z  as [n1 n2]; unfold succ; cbn; intros H H0;
     inversion H0;   subst;  inversion H;  subst; lia.
Qed.

Lemma succ_ok alpha beta : Successor beta alpha <-> beta = succ alpha.
Proof.
  split.  
  - destruct alpha, beta; intro H.
    apply Successor_inv in H. destruct H;subst. reflexivity.
  - intros; subst ; apply Successor_succ.
Qed.


Definition succb (alpha: t) := match alpha with
                                   (_, S _) => true
                                 | _ => false
                                 end.

Definition limitb (alpha : t) := match alpha with
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
       inversion H; lia.
    + now  cbn.
   -   destruct (H0 (n, n0)).
    + right; auto with arith. 
    + specialize (H x).
     rewrite lt_succ_le in H1.
     assert (s x o< s x) by (eapply lt_le_trans; eauto).
     destruct lt_strorder as [H3 H4].
     destruct (H3 _ H2).
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
     + lia.    
Qed.

 Example Ex1 : limitb omega.
 Proof. reflexivity.  Qed.


 (* A simplifier ? *)
 
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
     destruct lt_strorder as [H3 H4].
     destruct (H3 (k,l)).        
     transitivity (i,x); auto.
  -    inversion_clear H.
    + inversion_clear H0.
   *    intro.  left.  lia.
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


Definition  plus (alpha beta : t) : t :=
  match alpha,beta with
  | (0, b), (0, b') => (0, b + b')
  |  (0,0), y  => y
  |  x, (0,0)  => x
  |   (0, b), (S n', b') => (S n', b')
  | (S n, b), (S n', b') => (S n + S n', b')
  | (S n, b), (0, b') => (S n, b + b')
 
  end.

Infix "+" := plus : o2_scope.

Definition mult_fin  (alpha : t) (p : nat): t :=
  match alpha, p with
 |  (0,0), _  => zero
 |  _, 0 => zero
 |  (0, n), p => (0, n * p)
 |  ( n, b),  n' => ( n *  n', b)
               end.
Infix "*" := mult_fin : o2_scope.

Definition fin_mult (n:nat)(beta : t) : t :=
  match n, beta with
 |  0, _  => zero
 |  _, (0,0) => zero
 |   n , (0,n') => (0, (n*n')%nat)
 |  n, (n',p') => (n', (n * p')%nat)
 end.

Compute (fin_mult 3 (omega * 7 + 15)).


Compute (fin_mult 3 (omega * 1 + 15)).

Lemma plus_assoc alpha beta gamma :
  alpha + (beta + gamma) = alpha + beta + gamma.
  destruct alpha, beta, gamma.
  destruct n,  n0, n1, n2, n3, n4; cbn; auto; f_equal; lia.
Qed.


Lemma succ_is_plus_1  alpha : alpha + 1 = succ alpha.
Proof.
 unfold succ ;
simpl; 
 destruct alpha; cbn; destruct n, n0; try f_equal; lia.
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

Lemma unique_decomposition alpha : exists! i j: nat,  alpha = omega * i + j.
Proof.
  destruct alpha as [i j]; exists i; split.
  -  exists j; split.
     + now rewrite decompose. 
     + intros x; repeat rewrite <- decompose; congruence.
  - intros x [y [Hy _]]; rewrite <- decompose in Hy; congruence.
Qed.

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
     +  lia.
 - lia.
Qed.


Lemma ap_cases alpha : ap alpha -> alpha = 1 \/ alpha = omega.
Proof.
  destruct (zero_limit_succ_dec alpha) as [[Hzero |  Hlim] | Hsucc].
  - subst alpha; intro H; elimtype False.
    destruct H as [H _]; auto.
  - destruct alpha; unfold ap.
    destruct n, n0; try discriminate.
    intros [_ H1]; destruct n.
    + now right.
    +  right; specialize (H1 (S n,0) (S n,0)).
       assert (H2:(S n, 0) o< (S (S n), 0)) by (left; auto).
       specialize (H1 H2 H2).
       inversion H1; lia.
  -  intro H;  destruct Hsucc as [beta e]; subst.
     destruct H as [_ H].
      destruct (eq_dec beta zero).
       + subst; now left.
       +  specialize  (H beta 1 (lt_succ beta)).
          assert (1 o< succ beta). {
            destruct beta;  destruct n0, n1.
            * now destruct n.
            * right; cbn; lia.
            * destruct n0; cbn.
              left; auto.
              left; simpl;lia.
            * left; simpl; lia.
          }
          *  specialize (H H0).
             rewrite <- succ_is_plus_1 in H.       
             destruct lt_strorder as [H3 H4].
             destruct (H3 _ H).        
Qed.




Compute (omega * 3).
Compute (omega * 3) * 6.

Compute (omega * 3 + 1) * 6.
Compute fin_mult 3 omega.
Compute (3,2)+(2,10).

Compute (2,2)+(3,10).

Compute (0,2)+(0,10).

Compute (0,2)+(1,10).

Goal omega * 2 + 2 + omega * 3 + 10 = omega * 5 + 10.
  reflexivity.
Qed.

Open Scope ON_scope.

Example L_3_plus_omega :  3 + omega = omega.
Proof.
  now  apply compare_Eq_eq.
Qed.

Require Import Coq.Program.Wf.

Let m (p : list nat * list nat) := omega * length (fst p) + length (snd p).

Program Fixpoint  merge  (xys: list nat * list nat) {wf (m_lt m) xys} :
  list nat :=
  match xys with
      (nil, ys) => ys
    | (xs, nil) => xs
    | (cons x xs, cons y ys) =>
      if (Nat.ltb x y) then (cons x (merge (xs, (cons y ys))))
      else (cons y (merge ((cons x xs), ys)))
  end.
Next Obligation.
  unfold m; destruct xs; simpl. 
  -  left; auto with arith.
  -  left; auto with arith.  Defined.
Next Obligation.
  unfold m;  red ;cbn; destruct ys; simpl.
  - right; lia.
  - right; lia.
Defined.
Next Obligation.
   apply   wf_measure.
Defined.


