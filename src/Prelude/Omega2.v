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


 Definition lt : relation t := lexico Peano.lt Peano.lt.

 Infix "<" := lt : o2_scope.

(** reflexive closure of lt *)

Definition le := clos_refl _ lt.

Infix "<=" := le : o2_scope.

Hint Constructors clos_refl lexico : O2.
Hint Unfold lt le : O2.


Instance Sto_lt : StrictOrder lt.
Proof. apply Strict_lex; apply Nat.lt_strorder. Qed.

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

Lemma le_1 : forall i j p,  (i,j) < p -> (i, S j) <= p.
Proof.
  intros i j p H; destruct p as (k,l).
  -  inversion_clear H; auto with O2.
     + destruct (Lt.le_lt_or_eq _ _ H0); auto with O2.
       * subst l; now right.
Qed.

Lemma le_lt_trans : forall p q r, p <= q -> q < r -> p < r.
Proof.
  destruct 1; try trivial. 
  intro; now transitivity y.  
Qed.   

Lemma lt_le_trans : forall p q r, p < q -> q <= r -> p < r.
Proof.
  destruct 2; try trivial; now  transitivity q.
Qed.   


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

(*

Lemma le_1 : forall i j p,  (i,j) < p -> (i, S j) <= p.
Proof.
  intros i j p H; destruct p as (k,l).
  -  inversion_clear H; auto with hydra.
     + destruct (Lt.le_lt_or_eq _ _ H0); auto with hydra.
       * subst l; now right.
Qed.

Lemma le_lt_trans : forall p q r, p <= q -> q < r -> p < r.
Proof.
  destruct 1; try trivial. 
  intro; now transitivity y.  
Qed.   

Lemma lt_le_trans : forall p q r, p < q -> q <= r -> p < r.
Proof.
  destruct 2; try trivial; now  transitivity q.
Qed.   


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
      *  destruct (Lt.le_lt_or_eq _ _ H1); auto with hydra.
           subst k; now right.
      * left; left; lia.
      *  now destruct (Nat.nlt_succ_diag_l l).
 -   intro j; apply lt_le_trans with (S i, 0); auto with hydra.
Qed.

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
