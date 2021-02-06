(** * Proof that Ack is not primitive recursive

  after the following documents :
#<a href="https://planetmath.org/ackermannfunctionisnotprimitiverecursive">
planetmath page </a>#
and
#<a href="http://www.enseignement.polytechnique.fr/informatique/INF412/uploads/Main/pc-primrec-sujet2014.pdf"> Bruno Salvy's lecture</a>#.
 *)



Require Import primRec Arith ArithRing List Ack MoreVectors Lia.
Require Import Compare_dec Max.
Import extEqualNat  VectorNotations. 





(** Maximum in a vector of nat *)

Fixpoint max_v {n:nat} : forall (v: Vector.t nat n) , nat :=
  match n as n0 return (Vector.t nat n0 -> nat)
  with
    0 => fun v => 0
  | S p => fun (v : Vector.t nat (S p)) =>
             (max (Vector.hd v) (max_v  (Vector.tl v)))
  end. 

Lemma max_v_lub : forall n (v: t nat n) y,
    (Forall (fun x =>  x <= y) v) ->
    max_v v <= y.
Proof.
  induction n.  
  -  intros v; rewrite (zero_nil _ v); cbn.
     intros; auto with arith.
  -   intros v; rewrite (decomp _ _ v); cbn.
      intros;  destruct (Forall_inv _ _ _  _ H). apply max_lub; auto. 
Qed.


Lemma max_v_ge : forall n (v: t nat n) y,
    In  y  v -> y <= max_v v.
Proof.
  induction n.  
  -  intros v; rewrite (zero_nil _ v); cbn; inversion 1.
  -  intros v; rewrite (decomp _ _ v); cbn; intros; destruct (In_cases _ _ H).
     +  cbn in H0; subst; apply le_max_l. 
     + cbn in H0; specialize (IHn _ _ H0); lia.
Qed.



(**  uncurried apply *)

(*
Notation "'v_apply' f v" := (evalList _ v f) (no associativity, at level 30, f at level 20, v at  level 20).
 *)



Lemma evalList_Const : forall n (v:t nat n) x,
    evalList n  v (evalConstFunc n x)  = x.
Proof.
  induction n; cbn.
  - intros; cbn ; replace v with (@nil nat).
    + now  cbn.
    +  symmetry; apply zero_nil.
  - intros; cbn; rewrite (decomp _ _ v); cbn; auto.
Qed.



Lemma proj_le_max : forall n, forall v : t nat n, forall k (H: k < n),
        evalList n v (evalProjFunc n k H) <= max_v v.
Proof.
  induction n.
  -  cbn; intros; lia.
  - intros; specialize (IHn (tl v));  cbn.
    destruct (Nat.eq_dec k n).
    +  cbn;  rewrite (decomp _ _ v);  cbn; rewrite  evalList_Const;
         apply le_max_l.
    + destruct (le_lt_or_eq k n (lt_n_Sm_le k n H)).
      *  replace v with (cons (hd v) (tl v)) at 1; cbn.
         --   transitivity (max_v (tl v));  auto. 
              apply le_max_r.
         --  symmetry; apply decomp. 
      *  destruct( n0 e).
Qed. 

Lemma evalListComp : forall n  (v: t nat n) m (gs: t (naryFunc n) m)
                            (h: naryFunc  m),
    evalList n v (evalComposeFunc _ _ gs h) =
    evalList m (map (fun g =>  evalList _ v g) gs) h.
Proof.
  induction n.
  - intros; rewrite (zero_nil _ v); cbn.
    induction m.
    + rewrite (zero_nil _ gs); cbn; auto.  
    + rewrite (decomp _ _ gs);  cbn. 
      simpl naryFunc in *.
      specialize (IHm (tl gs) (h (vfst gs))); now rewrite IHm.
  -   intros; induction m.
      + rewrite (zero_nil _ gs);  cbn.
        rewrite (decomp _ _ v); cbn.   
        specialize (IHn (tl v) 0 (nil) h); rewrite IHn;  cbn;  auto.
      +  rewrite (decomp _ _ v).
         rewrite (decomp _ _ gs).
         specialize (IHm  (tl gs));  cbn.
         specialize (IHn (tl v));  rewrite IHn; cbn.
         f_equal; f_equal.
         generalize m gs; intro m0;  induction m0.
         * cbn; intros; rewrite (decomp1  gs0); cbn; auto.
         *   intros; replace gs0 with
                         (cons (hd gs0) (cons (hd (tl gs0)) (tl (tl gs0)))).
             -- cbn; cbn in *; specialize (IHm0  (tl gs0));  rewrite IHm0; auto.
             --  rewrite decomp;  f_equal.
                 now rewrite decomp.
Qed.

Lemma evalListCompose2 : forall n  (v: t nat n)  (f: naryFunc n)
                                (g : naryFunc (S n)),
    evalList n v (compose2 n f g) =
    evalList (S n) (cons (evalList n v f) v) g.
Proof.
  induction n.
  - cbn;  intros;  rewrite (zero_nil _ v);  now cbn. 
  -  intros; rewrite (decomp _ _ v);  cbn; rewrite IHn;  now cbn.
Qed.

Lemma evalListPrimrec_0 : forall n  (v: t nat n) (f : naryFunc n)
                                 (g : naryFunc (S (S n))),
    evalList (S n) (cons 0 v) (evalPrimRecFunc  _ f g)
    = evalList n v f.
Proof.
  induction n.                                                
  - intros; rewrite (zero_nil _ v); now cbn.
  - intros; rewrite (decomp _ _ v); now cbn.
Qed.

Lemma evalListPrimrec_S : forall n  (v: t nat n) (f : naryFunc n)
                                 (g : naryFunc (S (S n))) a,
    evalList (S n) (cons (S a) v) (evalPrimRecFunc  _ f g)
    = evalList (S (S n)) (cons a
                               (cons (evalList (S n) (cons a   v)
                                               (evalPrimRecFunc  _ f g)) v)
                         )
               g.
Proof.
  induction n.                                                
  - intros; rewrite (zero_nil _ v); now cbn.
  - intros; rewrite (decomp _ _ v);  cbn.
    specialize (IHn (tl v));  cbn; rewrite evalListCompose2.
    cbn; auto.
Qed.

(** A property shared by any PR function *)

Definition P n (f: naryFunc n) := exists (N:nat),
    forall (v: Vector.t nat n), evalList _ v f <= Ack N (max_v  v).


Definition P_PR n (x : PrimRec n) :=  P _ (evalPrimRec _ x).

Definition Ps n m (fs : Vector.t (naryFunc n) m) :=
  exists N, forall (v: t nat n),
      max_v (map (fun f => evalList _ v f) fs) <= Ack N (max_v v).

Definition Ps_PR n m (x : PrimRecs n m) :=  Ps _ _ (evalPrimRecs _ _ x).



Lemma P_PR_Succ : P_PR _ succFunc.
Proof.
  exists 1; intro v.
  rewrite (decomp1 v).
  simpl evalList; simpl max_v; rewrite max_0_r.
  -   rewrite Ack_1_n; auto with arith.
Qed.


Lemma P_PR_Zero : P_PR _ zeroFunc.
Proof.
  exists 0;
    intro v; rewrite  (zero_nil _ v), Ack_0. cbn; auto with arith.
Qed.


(** By induction on x, we prove that every PR function staisfies [P] *)

Lemma L: forall n (x: PrimRec n),  P_PR n x.
Proof.
  intros n x; induction x using PrimRec_PrimRecs_ind with
                  (P0 := fun n m y => Ps_PR n m y).
  - apply P_PR_Succ.
  - apply P_PR_Zero.
  - (** projection functions *)
    red; cbn; red; exists 0.
    rewrite Ack_0; intro v; transitivity (max_v v).
    + apply proj_le_max.
    + auto with arith.
  -  (** function composition *)
    destruct IHx, IHx0; red; exists (2 + max x0 x1). 
    intro v; simpl evalPrimRec; rewrite evalListComp.
    generalize 
     (H0  (map (fun g0 : naryFunc n => evalList n v g0) (evalPrimRecs n m g)));
    intro H00; eapply Le.le_trans.
    +  auto.
    + generalize (H v); intro HH; transitivity (Ack x1 (Ack x0 (max_v v))).
      * apply Ack_mono_r; apply max_v_lub.
         rewrite MoreVectors.Forall_forall; intros.

        generalize ( max_v_ge m (map (fun g : naryFunc n => evalList n v g)
                                     (evalPrimRecs n m g)) a H1).
         intro H2;lia.
      * rewrite max_comm; apply Ack_Ack_le.
  - (** Primitive recursion *)
     (* use the notation of planetmath.org page *)
    destruct IHx1 as [r Hg]; destruct IHx2 as [s Hh].
    remember  (evalPrimRec n x1) as g.
    remember (evalPrimRec _ x2) as h.
    pose(q := S  (max r s)); red.
    remember  (evalPrimRecFunc _ (evalPrimRec _ x1)
                               (evalPrimRec _ x2)) as f.
    
    assert (L1 : forall i (v: t nat n) ,
               evalList _ (cons i v) f  <= Ack q (i + max_v v)).
    {
      induction i.
      - intros; subst f;  rewrite evalListPrimrec_0.
        simpl plus; subst g; transitivity (Ack r (max_v  v)).
        + auto.
        + apply Ack_mono_l; unfold q; lia.
      - intros; rewrite Heqf; rewrite evalListPrimrec_S;
          rewrite <- Heqf; rewrite <- Heqh.
        pose (z:= max_v (i :: evalList (S n) (i :: v) f :: v)).
        assert (H: evalList (S (S n))
                         (cons i (cons (evalList (S n) (cons i v) f) v)) h
                <= Ack s z) by ( unfold z; apply Hh).
        assert (H0: z <= Ack q (i+ max_v v)).
        {              
          clear H; specialize (IHi v).
          remember (evalList (S n) (cons i v) f) as p.
          remember (Ack q (i + max_v v)) as t.
          simpl max_v in z; remember (max_v v) as u.
          assert (H: i <= t).
          { rewrite Heqt; transitivity (S i); auto.
            transitivity (Ack q i).
            apply le_S_Ack.
            apply Ack_mono_r.
            lia.
          }
          assert (H0: u <= t).
          { rewrite Hequ, Heqt; rewrite Hequ.
            transitivity (i + max_v v).
            - lia.
            - transitivity (S (i + max_v v)).
              lia.
          apply le_S_Ack.
        }
        lia.
        }
        assert (Ack s z <= Ack q (S i + max_v v)).
        {
          unfold q; simpl plus; rewrite Ack_S_S; fold q.
          transitivity (Ack (max r s) z).
          - apply Ack_mono_l; lia.
          - apply Ack_mono_r; auto.
        }
        lia.
    }
    exists (4+ q); intros.
    pose (z := max (hd v) (max_v (tl v))).
    simpl evalPrimRec; rewrite <- Heqf; rewrite (decomp _ _ v).
    remember (vfst v) as x; remember (tl v) as y.
    transitivity (Ack q (x + max_v y)).
    + apply L1.
    + transitivity (Ack q (2 * z)).
      * apply Ack_mono_r; unfold z; lia.
      * transitivity (Ack q (Ack 2 z)).
      -- rewrite Ack_2_n; apply Ack_mono_r; lia.
      -- simpl max_v; fold z; transitivity (Ack (2 + max 2 q) z).
         ++ rewrite max_comm; apply Ack_Ack_le.
         ++ apply Ack_mono_l;  lia. 
  - (* Lists of PR functions *)
    red;cbn;  red; exists 0.
    intro; rewrite Ack_0.
    cbn; auto with arith.
  - red; cbn; red; destruct IHx, IHx0; exists (max x0 x1).
    intros v;  cbn; specialize (H0 v).
    pose (X :=
            (max_v (map (fun f : naryFunc n => evalList n v f)
                        (evalPrimRecs n m p)))).
    fold X ; fold X in H0;  specialize (H v).
    pose (Y := evalList n v (evalPrimRec n x)).
    fold Y; fold Y in H;  apply Nat.max_lub.
    + transitivity (Ack x0 (max_v v)); auto.
      *  apply Ack_mono_l; apply le_max_l.
    + transitivity (Ack x1 (max_v v)); auto.
    * apply Ack_mono_l; apply le_max_r.
Qed. 


Section Impossibility_Proof.

  Hypothesis HAck : isPR 2 Ack.
  
  (** we specialize Lemma [L] to n-binary functions *)
  
  Lemma L1 : exists (n:nat), forall x y,  Ack x y <= Ack n (x + y).
  Proof.
    destruct HAck as [x Hx]; generalize (L 2 x).
    intros.
    red in H;red in H; destruct H as [N HN];  exists N.
    intros; specialize (HN [x0; y]);  cbn in HN.
    replace (evalPrimRec 2 x x0 y) with (Ack x0 y) in HN.
    - rewrite max_0_r in HN; transitivity  (Ack N (Nat.max x0 y)); auto.
      apply Ack_mono_r;  lia.
    - symmetry; apply Hx.
  Qed.


  Section Contrad.
    Variable n: nat.
    Hypothesis  Hn :  forall x y,  Ack x y <= Ack n (x + y) .

    Remark R01 : n <> 0.
    Proof.
      intro H;  subst; specialize (Hn 2 1); compute in Hn; lia.
    Qed.


    Remark R02: n <> 1.
    Proof. 
      intro H; subst; specialize (Hn 2 2);  compute in Hn;  lia.
    Qed.

    Remark R03 : max 2 n = n.
    Proof.
      apply PeanoNat.Nat.max_r; case_eq  n; intros.
      -  destruct (R01 H).
      -  destruct n0.
         +   destruct (R02 H).
         + subst; auto with arith.
    Qed.

    Remark R04 : Ack n (2 * n + 3) = Ack n (Ack 2 n).
    Proof.
      now rewrite Ack_2_n.
    Qed.
    
    Remark R05 : Ack n (2 * n + 3) <= Ack (n + 2) n.
    Proof.
      transitivity (Ack n (Ack 2 n)).
      -  now  rewrite  R04.
      - replace (n+2) with  (2 + max n 2).
        +  apply  Ack_Ack_le.
        + rewrite PeanoNat.Nat.add_comm;  now rewrite Max.max_comm, R03.
    Qed.  

    Remark R06 : Ack (n+ 2) n <= Ack n (2 * n + 2).
    Proof.
      specialize (Hn (n+2) n).
      replace (2* n + 2) with (n+2 + n) by lia;  auto.
    Qed.

    Remark R07 : Ack n (2 * n + 3) <= Ack n (2* n + 2).
    Proof.
      eapply Le.le_trans.
      - apply R05.
      - apply R06.
    Qed.


    Remark R08 :  Ack n (2* n + 2) < Ack n (2 * n + 3).
    Proof.
      destruct (Ack_properties n) as [H _]; apply H; lia.
    Qed.

    Lemma contrad : False.
    Proof.
      generalize R07, R08; intros; lia.
    Qed.

  End Contrad.

  Lemma Ack_not_PR : False.
    destruct L1 as [n Hn].
    now apply contrad with n.
  Qed.

End Impossibility_Proof.







