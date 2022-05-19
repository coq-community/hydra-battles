
Require Import Arith NArith Pow Compatibility Lia.
Open Scope positive_scope.
Import Monoid_def.
Require Import Recdef  Wf_transparent. 

(** * Basic lemmas about positive and N *)

Definition pos_eq_dec : forall p p':positive, {p = p'}+{p <> p'}.
Proof.  decide equality. Defined.

Lemma N_0_le_n: forall n:N, (0 <= n)%N.
Proof.
 destruct n; simpl;[reflexivity | discriminate].
Qed.   

Lemma Pos_to_nat_neq_0 : forall p, Pos.to_nat p <> 0%nat.
Proof.
 induction p; cbn.
  discriminate.
 rewrite Pos2Nat.inj_xO.
      simpl; lia.
  discriminate.
Qed.

#[global] Hint Resolve Pos_to_nat_neq_0 : chains.


(** ** Relationship with [nat] and [N] 
*)
Lemma Npos_diff_zero : forall p, N.pos p <> 0%N.
Proof. discriminate. Qed.

Lemma Npos_gt_0 : forall p, (0 < N.pos p)%N.
Proof. reflexivity. Qed.

#[global] Hint Resolve Npos_diff_zero  Npos_gt_0 : chains.


Lemma pos2N_inj_lt : forall n p, (n < p)%positive <-> (N.pos n < N.pos p)%N.
Proof.
 intros n p; tauto. 
Qed.


Lemma pos2N_inj_add : forall n p, N.pos (n + p) = (N.pos n + N.pos p)%N.
Proof. reflexivity. Qed.


Ltac pos2nat_inj_tac :=
  repeat (rewrite Pos2Nat.inj_add || rewrite Pos2Nat.inj_mul ||
          rewrite Pos2Nat.inj_lt  || rewrite Pos2Nat.inj_le).

Lemma Pos2Nat_le_1_p : forall p, (1 <= Pos.to_nat p)%nat.
intro p;  change (Pos.to_nat 1 <= Pos.to_nat p)%nat;
              rewrite <-  Pos2Nat.inj_le.
            apply Pos.le_1_l.
Qed.


Lemma N_le_1_pos : forall p, (1 <= N.pos p)%N.
Proof. destruct p; discriminate. Qed.

Lemma pos_le_mul : forall p q , (p <= p * q)%positive.
Proof.
  intros p q; replace p with (p * 1)%positive at 1
              by ( now rewrite Pos.mul_1_r). 
  apply Pos.mul_le_mono_l; apply Pos.le_1_l.
Qed.


Lemma pos_lt_mul : forall p q , (1 < q -> p < p * q)%positive.
Proof.
  intros p q H; replace p with (p * 1)%positive at 1
              by ( now rewrite Pos.mul_1_r). 
  apply Pos.mul_lt_mono_l; auto. 
Qed.


Lemma Pos2Nat_le_n_pn :
  forall p q,
    (Pos.to_nat p <= Pos.to_nat p  * Pos.to_nat q)%nat.
Proof.
 intros p q;
 replace (Pos.to_nat p  * Pos.to_nat q)%nat with (Pos.to_nat (p * q))
 by (now rewrite Pos2Nat.inj_mul).
 apply Pos2Nat.inj_le; apply pos_le_mul.
Qed.

#[global] Hint Resolve Pos2Nat_le_1_p : chains.

(** ** Surjection from [N] into [positive] 
*)

Definition N2pos (n:N) : positive :=
 match n with 0%N => xH | Npos p => p end.

Lemma N2pos_pos :
  forall i,  N2pos (Npos i) = i.
Proof. reflexivity. Qed. 

Lemma N_pos_N2pos : forall n, 0%N <> n ->  n = Npos (N2pos n).
Proof. 
 destruct n;[ now destruct 1 | reflexivity].
Qed. 

Lemma N2pos_lt_switch : forall  n p, (0%N < n)%N ->
                                     ( (N.pos p < n)%N <-> (p < N2pos n)%positive).
Proof.
destruct n.
- split; discriminate.
-  intros;simpl;split; now  rewrite pos2N_inj_lt.
Qed.




Ltac N2pos_simpl x := simpl (N2pos (N.pos x)) in *.

Ltac N2pos_destruct t y :=
 destruct t as [| y] ; [try (discriminate || contradiction) | N2pos_simpl y].


Lemma N2pos_lt_switch2 : forall  n p, (0%N < n)%N ->
                                      ((N2pos n < p)%positive 
                                       <-> (n < N.pos p)%N).
Proof.
 intros n p H;  N2pos_destruct n n;
 split; simpl;now  rewrite pos2N_inj_lt.
Qed.

Lemma pos_lt_wf : well_founded Pos.lt.
Proof.
  intros x.
  assert (H:= wf_inverse_image_transparent  _ _ Nat.lt Pos.to_nat lt_wf).
  assert (H0 : Relation_Definitions.inclusion
            positive Pos.lt
            (fun x y : positive =>
               Nat.lt (Pos.to_nat x) (Pos.to_nat y))).
  -  red;  intros x0 y0 ;  now rewrite Pos2Nat.inj_lt . 
  - apply  (wf_incl_transparent positive  _ _ H0 H ).
Defined.

(** Partial exact log2 function  *)

Fixpoint  exact_log2(p:positive) : option positive :=
match p with
  | 1%positive | xI _ => None
  | 2%positive =>  Some xH
  | xO q => match exact_log2 q with
              | Some l => Some (l+1)%positive
              | _ => None
            end
end.



(**
Compute exact_log2 16.
 = Some 4
     : option positive

Compute exact_log2 10.
= None
    : option positive
*)


Lemma exact_log2xOx0 :
  forall p i, exact_log2 (xO p) = Some i ->
              exact_log2 (xO (xO p)) = Some (i+1)%positive.
Proof.
  simpl; destruct p.
  -  intro i; cbn; discriminate.
  -  destruct (exact_log2 p~0) . 
     +  injection 1; intro; now subst i.
     +  discriminate.
  -  injection 1; intro; now subst i.
Qed.

Lemma exact_log2_spec :
  forall p i: positive, exact_log2 p = Some i -> p = (2 ^ i)%positive.
Proof.
  induction p. 
  -  simpl; discriminate.
  - intro i; destruct p.
    + destruct p; discriminate.
        
    +  case_eq (exact_log2 (xO p)).   
       *  intros p0 H H0; generalize (exact_log2xOx0 _ _ H); intro H1.
          generalize (IHp _ H); intro H2; rewrite H0 in H1; injection H1;
          rewrite H2;  intro; subst i.
          repeat rewrite Pos_pow_power.
          rewrite Pos2Nat.inj_add.
          rewrite power_of_plus.
          replace (2%positive ^ Pos.to_nat 1)%M with 2%positive by reflexivity.
          rewrite Pos.mul_xO_r.
          now rewrite Pos.mul_1_r.
       * cbn; destruct p.
         destruct (exact_log2 p~1);  discriminate.
         destruct (exact_log2 p~0);  discriminate.
         discriminate.

    + cbn;   injection 1;intro; now subst i.
  - discriminate.
Qed.




(** Another induction principle for positive *)

Lemma positive_4step_ind : forall P : positive -> Prop,
   P 1%positive -> P 2%positive -> P 3%positive ->
  (forall p, P p -> P (xO (xO p)) /\ P (xI (xO p)) /\ P (xO (xI p)) /\
               P (xI (xI p))) ->
  forall p, P p.
Proof.
  intros P H H0 H1 H2 p;  assert (P p /\ P (xO p) /\ P (xI p)).
  -   induction p.
      + repeat split; try tauto.
        * destruct (H2 p);tauto.
        * destruct (H2 p);tauto.
      + repeat split; try tauto.
        * destruct (H2 p);tauto.
        * destruct (H2 p);tauto.
      + repeat split;tauto.
  - tauto.
Qed.


Lemma pos_gt_3 : forall p:positive, 
  p <> 1  -> p <> 3  ->  exact_log2 p = None ->  3 < p.
Proof.
 intro p;pattern p; apply  positive_4step_ind.
 -  destruct 1;auto.
 -  discriminate.
 -  destruct 2;auto.
 -  split; intros; now compute.
Qed.

#[global] Hint Resolve pos_gt_3 : chains.

(** ** Lemmas on Euclidean division 
    N.pos_div_eucl (a:positive) (b:N) : N * N 
*)
  
Lemma pos_div_eucl_quotient_pos : forall a b q r,
                                    N.pos_div_eucl a b = (q, r) ->
                                    (b <= N.pos a)%N ->
                                    b <> 0%N -> 
                                    (q <> 0%N).
Proof.
  intros a b q r H H1; generalize (N.pos_div_eucl_spec a b); rewrite H.
  intros  H0 H2 H3. rewrite H3 in H0 ;   simpl in H0.
  generalize (N.pos_div_eucl_remainder a b H2);  rewrite H;  simpl;
  intro; subst r.
  destruct (N.lt_irrefl b);auto.
  apply N.le_lt_trans with (N.pos a);auto.
Qed.

Lemma pos_div_eucl_quotient_lt : forall a b q r,
                                   N.pos_div_eucl a b = (q, r) ->
                                   (1 < b)%N ->
                                   (q < N.pos a)%N.
Proof.
  intros a b q r H H1; generalize (N.pos_div_eucl_spec a b); rewrite H.
  destruct q.
  - reflexivity.
  -  intro H2; rewrite H2;  apply N.lt_le_trans with (N.pos p * b)%N.
      + replace (N.pos p)  with ((N.pos p) * 1)%N at 1
       by (now rewrite N.mul_1_r).
       apply N.mul_lt_mono_pos_l; auto with chains.
      +  apply N.le_add_r.
Qed.


Lemma N_pos_div_eucl_divides : forall i b q,
                                 N.pos_div_eucl i (N.pos b) = (q, 0%N) ->
                                 (b * N2pos q)%positive = i.
Proof.
  intros i b q H;  generalize  (N.pos_div_eucl_spec   i (N.pos b)).
  rewrite H,  N.add_0_r.
  intro H3;  destruct q ; [discriminate | ].
  rewrite Pos.mul_comm; injection H3; symmetry; assumption.
Qed.


 Lemma N_pos_div_eucl_rest : forall i b q r,
                               N.pos_div_eucl i (N.pos b) = (q,  r) ->
                               (0 < r)%N -> (0 < q)%N ->
                               (b * N2pos q + N2pos r)%positive = i.
 Proof.
   intros i b q r H H0 H1.   generalize  (N.pos_div_eucl_spec   i (N.pos b)).
   rewrite H.
   destruct r ;[discriminate | ].
   destruct q ; [discriminate | ].
   injection 1.
   cbn. 
   intro H3;subst i.
   now rewrite Pos.mul_comm.
 Qed.

 Lemma N_pos_div_eucl_q0 : forall i b  r,
                             N.pos_div_eucl i (N.pos b) = (0%N,   r) ->
                             i = N2pos r.

 Proof.
   intros i b  r H;   generalize  (N.pos_div_eucl_spec   i (N.pos b)).
   rewrite H.
   simpl.
   destruct r.
   discriminate.
   injection 1;now cbn.
 Qed.




(** An auxiliary lemma *)
Lemma lt_S_2i : 
forall i j:nat, (i < j -> 2 * i + 1 < 2 * j)%nat.
Proof.  intros; lia. Qed.

Lemma N_le_mul_pos  : forall q p, (q <= q * N.pos p)%N.
Proof. 
  intros q p; replace q with (q * 1)%N at 1.
  apply N.mul_le_mono_nonneg_l.
  apply N_0_le_n.
  destruct p;discriminate.
  rewrite N.mul_1_r; auto.
Qed.
  







Ltac quotient_small div_equation H :=
  match type of div_equation with
    (N.pos_div_eucl ?a ?b = (?q,?r)) =>
    assert  (H : (q < N.pos a)%N);
    [apply (pos_div_eucl_quotient_lt _ _ _ _ div_equation); auto|]
  end.

Ltac rest_small div_equation H :=
  match type of div_equation with
    (N.pos_div_eucl ?a ?b = (?q,?r)) =>
    let H0 := fresh "H" in
    assert  (H : (r < b)%N);
    [generalize (N.pos_div_eucl_remainder a b); simpl; intro  H0;
     rewrite div_equation in H0; apply H0 ; try discriminate| ]
  end.







