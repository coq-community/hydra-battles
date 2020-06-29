(**  The ordinal omega * omega *)
Require Import Arith Compare_dec Lia Simple_LexProd.
Import Relations.
Declare Scope o2_scope.
Delimit Scope o2_scope with o2.
Open Scope o2_scope.

Coercion is_true: bool >-> Sortclass.

Definition t := (nat * nat)%type.

Definition zero: t := (0,0).

Definition succ (alpha : t) := (fst alpha, S (snd alpha)).

Notation "'omega'" := (1,0) : o2_scope.

Definition fin (n:nat) : t := (0, n).

Notation "'F'" := fin : o2_scope.

Coercion fin : nat >-> t.


 Definition lt : relation t := lexico Peano.lt Peano.lt.

 Infix "<" := lt : o2_scope.

(** reflexive closure of lt *)

Definition le := clos_refl _ lt.

Infix "<=" := le : o2_scope.

Hint Constructors clos_refl lexico : O2.
Hint Unfold lt le : O2.

Example ex1 : 6 < omega.
Proof.
  left; auto with arith.
Qed.


Example ex2 : omega < (1,1).
Proof.
 right; auto with arith.
Qed.

Locate StrictOrder.



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


  
Lemma lt_wf : well_founded lt.
Proof. apply wf_lexico; apply lt_wf. Qed.

Lemma le_introl :
  forall i j k:nat, (j <= k)%nat -> (i,j) <= (i,k).
Proof.
  intros i j k H; destruct (Lt.le_lt_or_eq j k H); auto with O2.
  - subst k; now right.
Qed.

Lemma le_0 : forall p: t,  (0,0) <= p.
Proof.
  destruct p, n ; auto with arith O2.
  - apply le_introl;  auto with arith O2.
Qed.

Lemma le_1 : forall i j alpha,  (i,j) < alpha -> (i, S j) <= alpha.
Proof.
  intros i j (k,l) H.
  -  inversion_clear H; auto with O2.
     + destruct (Lt.le_lt_or_eq _ _ H0); auto with O2.
       * subst l; now right.
Qed.

Lemma le_lt_trans : forall p q r, p <= q -> q < r -> p < r.
Proof.
  destruct 1; trivial. 
  intro; now transitivity y.  
Qed.   

Lemma lt_le_trans : forall p q r, p < q -> q <= r -> p < r.
Proof.
  destruct 2; trivial; now  transitivity q.
Qed.   


(** alpha is an immediate predecessor of beta *)

Definition ipred alpha beta := 
    alpha < beta /\  forall gamma ,  gamma < beta -> gamma <= alpha.

Lemma ipred_inv : forall i j k l, ipred (i, j) (k, l) ->
                     i = k /\ l = S j.
Proof.
  destruct 1 as [H H0].
  assert (H1 : (i< k \/ i=k /\ j <l)%nat) by (inversion_clear H; auto).
  destruct H1 as [H1 | [H1 H2]].
  - elimtype False.
    assert (H2: (i, S j) <= (i, j)) by (apply H0; left; auto with arith).
    inversion H2;subst. 
    inversion H3; try lia.
    lia.
  -  split; auto.
     destruct (le_lt_or_eq _ _ H2); auto.
     + subst; elimtype False.
       assert (H1: (k, S j) <= (k, j)) by (apply H0;  right; auto).
       inversion H1; try lia.
       inversion H4; lia.
Qed. 

Lemma ipred_ok : forall alpha,  ipred alpha (succ alpha).
Proof.
  destruct alpha;red;cbn; split.
  - right; auto.
  - intro; destruct gamma.  unfold succ; cbn; intro H.
  inversion H.
   subst.
left; left; lia.
subst.
destruct (le_lt_or_eq _ _ H1).
  left. right; lia.
   injection H0; intros; subst; right. 
Qed.



Lemma succ_ok alpha beta : ipred alpha beta <-> beta = succ alpha.
Proof.
  split.  
  - destruct alpha, beta; intro H.
    apply ipred_inv in H. destruct H;subst. reflexivity.
  - intros; subst ; apply ipred_ok.
Qed.


  Definition is_succ (alpha: t) := match alpha with
                                  (_, S _) => true
                                | _ => false
                                end.

Definition is_limit (alpha : t) := match alpha with
                                     (S _, 0) => true
                                   | _ => false
                                    end.

 Example Ex1 : is_limit omega.
 Proof. reflexivity.  Qed.

 Definition zero_succ_limit_dec :
  forall alpha, 
                ({alpha = zero} + {is_limit alpha }) + 
                {beta : t |  alpha = succ beta} .
 Proof.
   destruct alpha as (n,p); destruct p.
   - destruct n.
     + left; left;trivial.
     +  left; now right.
   - right; now exists (n,p).
 Defined.




Lemma limit_is_lub : forall i p, (forall j, (i,j) < p) <->
                            (S i, 0) <= p.
Proof.
  intros i (k,l) ;split; intro  H .
  -   destruct (Nat.eq_dec (S i) k).
    + subst k;  destruct l.
      *  now right.
      *   left;  right;  auto with arith.
    +  generalize (H (S l));   inversion_clear 1.
       destruct l.
      *  destruct (Lt.le_lt_or_eq _ _ H1); auto with O2.
           subst k; now right.
      * left; left; lia.
      *  now destruct (Nat.nlt_succ_diag_l l).
 -   intro j; apply lt_le_trans with (S i, 0); auto with O2.
Qed.


 Definition compare (alpha beta: t) : comparison :=
  match Nat.compare (fst alpha) ( fst beta) with
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
                                            
Lemma compare_refl alpha beta :
  match (compare alpha beta)
  with
    Lt => alpha < beta
  | Eq => alpha = beta
  | Gt => beta < alpha
  end.
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

(*
Definition lt alpha beta : Prop := lt_b alpha beta.

Definition le (alpha beta :t) :=
  match compare alpha beta with
    Gt => False
  | _ => True
  end.

Hint Unfold le : t.

Infix "<" := lt : o2_scope.
Infix "<=" := le : o2_scope.



 *)

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

Fixpoint fin_mult (n:nat)(beta : t) : t :=
  match n, beta with
 |  0, _  => zero
 |  _, (0,0) => zero
 |   n , (0,n') => (0, (n*n')%nat)
 |  n, (n',p') => (n', (n * p')%nat)
 end.

Compute (fin_mult 3 (omega * 7 + 15)).


Compute (fin_mult 3 (omega * 1 + 15)).
Search (_ + _ + _)%nat.

Lemma plus_assoc alpha beta gamma :
  alpha + (beta + gamma) = alpha + beta + gamma.
  destruct alpha, beta, gamma.
  destruct n,  n0, n1, n2, n3, n4; cbn; auto; f_equal; lia.
Qed.

Lemma lt_omega alpha : alpha < omega <-> exists n:nat,  alpha = fin n.
Proof.
 destruct alpha; simpl.
 split.
 inversion_clear 1.
 inversion H0.
   exists n0.
   auto.
   inversion H1.
 inversion H0.
    destruct 1.
    injection H. intros; subst. left. auto.
Qed.


Definition ap (alpha : t) :=
  forall beta gamma,  beta < alpha -> gamma < alpha -> beta + gamma < alpha.

Lemma omega_ap : ap omega.
Proof.
  intros beta gamma H H0.
  destruct beta, gamma.
  compute in H, H0.
  inversion H.
  subst.
  inversion H0; subst.
  inversion H2; inversion H3; subst.
  unfold plus. destruct n0; left. auto with arith.
  auto with arith.
  all : try lia.
Qed.


Compute (omega * 3)%o2.
Compute (omega * 3) * 6.

Compute (omega * 3 + 1) * 6.
Compute fin_mult 3 omega.
Compute (3,2)+(2,10).

Compute (2,2)+(3,10).

Compute (0,2)+(0,10).

Compute (0,2)+(1,10).
