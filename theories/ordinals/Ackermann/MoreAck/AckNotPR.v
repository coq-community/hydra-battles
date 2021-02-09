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

(** Maximum of a vector of nat *)

Fixpoint max_v {n:nat} : forall (v: Vector.t nat n) , nat :=
  match n as n0 return (Vector.t nat n0 -> nat)
  with
    0 => fun v => 0
  | S p => fun (v : Vector.t nat (S p)) =>
             (max (Vector.hd v) (max_v  (Vector.tl v)))
  end. 

Lemma max_v_2 : forall x y,  max_v (x::y::nil) = max x y.
Proof.
  intros; cbn. now rewrite max_0_r.
Qed.

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



(**  uncurried apply 
 
[v_apply f (x1::x2:: ... ::xn::nil)]  is [f x1 x2 ... xn] 

 *)


Notation "'v_apply' f v" := (evalList _ v f) ( at level 10, f at level 9).


Example Ex2 : forall (f: naryFunc 2) x y,
    v_apply f (x::y::nil) = f x y.
Proof.
  intros; now cbn.
Qed.

Example Ex4 : forall (f: naryFunc 4) x y z t,
    v_apply f (x::y::z::t::nil) = f x y z t.
Proof.
  intros; now cbn.
Qed.

Definition majorized {n} (f: naryFunc n) (A: naryFunc 2) : Prop :=
  exists (q:nat), forall (v: t nat n),
      v_apply f v <= A q  (max_v v).

Definition majorizedPR {n} (x: PrimRec n) A := majorized (evalPrimRec n x) A.

(** For vectors of functions *)

Definition majorizedS {n m} (fs : Vector.t (naryFunc n) m)
           (A : naryFunc 2):=
  exists N, forall (v: t nat n),
      max_v (map (fun f => v_apply f v) fs) <= A N (max_v v).

Definition majorizedSPR {n m} (x : PrimRecs n m) :=
  majorizedS (evalPrimRecs _ _ x).

(**  ** Technical lemmas *)

Lemma evalList_Const : forall n (v:t nat n) x,
    v_apply (evalConstFunc n x) v = x.
Proof.
  induction n; cbn.
  - intros; cbn ; replace v with (@nil nat).
    + now  cbn.
    +  symmetry; apply zero_nil.
  - intros; cbn; rewrite (decomp _ _ v); cbn; auto.
Qed.



Lemma proj_le_max : forall n, forall v : t nat n, forall k (H: k < n),
        v_apply (evalProjFunc n k H) v <= max_v v.
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
    v_apply  (evalComposeFunc _ _ gs h) v =
    v_apply  h (map (fun g =>  evalList _ v g) gs).
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
    v_apply (compose2 n f g) v =
    v_apply g  ((evalList n v f) :: v).
Proof.
  induction n.
  - cbn;  intros;  rewrite (zero_nil _ v);  now cbn. 
  -  intros; rewrite (decomp _ _ v);  cbn; rewrite IHn;  now cbn.
Qed.

Lemma evalListPrimrec_0 : forall n  (v: t nat n) (f : naryFunc n)
                                 (g : naryFunc (S (S n))),
    v_apply (evalPrimRecFunc  _ f g) (cons 0 v)
    = v_apply f v.
Proof.
  induction n.                                                
  - intros; rewrite (zero_nil _ v); now cbn.
  - intros; rewrite (decomp _ _ v); now cbn.
Qed.


Lemma evalListPrimrec_S : forall n  (v: t nat n) (f : naryFunc n)
                                 (g : naryFunc (S (S n))) a,
    v_apply  (evalPrimRecFunc  _ f g) (cons (S a) v)
    = v_apply g
              (a :: v_apply (evalPrimRecFunc n f g) (a :: v) :: v).
Proof.
  induction n.                                                
  - intros; rewrite (zero_nil _ v); now cbn.
  - intros; rewrite (decomp _ _ v);  cbn.
    specialize (IHn (tl v));  cbn; rewrite evalListCompose2.
    cbn; auto.
Qed.

Lemma majorSucc : majorizedPR  succFunc Ack.
Proof.
  exists 1; intro v.
  rewrite (decomp1 v).
  simpl evalList; simpl max_v; rewrite max_0_r.
  -   rewrite Ack_1_n; auto with arith.
Qed.


Lemma majorZero : majorizedPR  zeroFunc Ack.
Proof.
  exists 0;
    intro v; rewrite  (zero_nil _ v), Ack_0. cbn; auto with arith.
Qed.

Lemma majorProjection (n m:nat)(H: m < n):
  majorizedPR (projFunc n m H) Ack.
Proof. 
  red; cbn; red; exists 0.
    rewrite Ack_0; intro v; transitivity (max_v v).
    + apply proj_le_max.
    + auto with arith.
Qed.

(** By induction on x, we prove that every PR function satisfies [P] *)

Lemma majorAnyPR: forall n (x: PrimRec n),  majorizedPR  x Ack.
Proof.
  intros n x; induction x using PrimRec_PrimRecs_ind with
                  (P0 := fun n m y => majorizedSPR  y Ack).
  - apply majorSucc.
  - apply majorZero.
  - apply majorProjection. 
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
    destruct IHx1 as [r Hg]; destruct IHx2 as [s Hh].
    remember  (evalPrimRec n x1) as g.
    remember (evalPrimRec _ x2) as h.
    pose(q := S  (max r s)); red.
    remember  (evalPrimRecFunc _ (evalPrimRec _ x1)
                               (evalPrimRec _ x2)) as f.
    (* begin show *)
    assert (L1 : forall i (v: t nat n) ,
               v_apply f (i::v)  <= Ack q (i + max_v v)).
    {
      induction i.
    (* end show *)
      - intros; subst f;  rewrite evalListPrimrec_0.
        simpl plus; subst g; transitivity (Ack r (max_v  v)).
        + auto.
        + apply Ack_mono_l; unfold q; lia.
      - intros; rewrite Heqf; rewrite evalListPrimrec_S;
          rewrite <- Heqf; rewrite <- Heqh.
        pose (z:= max_v (i :: evalList (S n) (i :: v) f :: v)).
        assert (H: v_apply h (i:: (v_apply f (i::v) :: v)) <= Ack s z)
          by ( unfold z; apply Hh).
        assert (H0: z <= Ack q (i+ max_v v)).
        {              
          clear H; specialize (IHi v).
          remember (v_apply f (i::v))  as p.
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
        (* begin show *)
    }
    (* end show *)
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
  - (**  Lists of PR functions *)
    red;cbn;  red; exists 0.
    intro; rewrite Ack_0.
    cbn; auto with arith.
  - red; cbn; red; destruct IHx, IHx0; exists (max x0 x1).
    intros v;  cbn; specialize (H0 v).
    pose (X :=
            (max_v (map (fun f : naryFunc n => v_apply f v)
                        (evalPrimRecs n m p)))).
    fold X ; fold X in H0;  specialize (H v).
    pose (Y := v_apply (evalPrimRec n x) v).
    fold Y; fold Y in H;  apply Nat.max_lub.
    + transitivity (Ack x0 (max_v v)); auto.
      *  apply Ack_mono_l; apply le_max_l.
    + transitivity (Ack x1 (max_v v)); auto.
      * apply Ack_mono_l; apply le_max_r.
Qed. 


(** we specialize Lemma [majorAnyPR] to binary functions *)

Lemma majorPR2 (f: naryFunc 2)(Hf : isPR 2 f)
  : exists (n:nat), forall x y,  f x y <= Ack n (max x  y).
Proof.
  destruct Hf as [x Hx]; generalize (majorAnyPR 2 x).
  intros.
  red in H;red in H.  destruct H as [N HN];  exists N.
  intros; specialize (HN [x0; y]);  cbn in HN.
  replace (evalPrimRec 2 x x0 y) with (f x0 y) in HN.
  - rewrite max_0_r in HN; transitivity  (Ack N (Nat.max x0 y)); auto.
  - symmetry; apply Hx.
Qed.

Section Impossibility_Proof.

  Hypothesis HAck : isPR 2 Ack.

  Fact Ack_majorized : majorized (Ack: naryFunc 2)  Ack.
  Proof. 
    generalize  (majorPR2 Ack HAck).   intros [q Hq]. red.
    exists q; intro v; rewrite (decomp2  v), max_v_2. 
    apply Hq.
  Qed.

  Section Contrad.
    Variable n: nat.
    Hypothesis  Hn: forall x y,  Ack x y <= Ack n (max x  y).

    Remark R01 : n <> 0.
    Proof.
      intro H;  subst; specialize (Hn 2 1); compute in Hn; lia.
    Qed.


    Remark R02: n <> 1.
    Proof. 
      intro H; subst; specialize (Hn 2 2);  compute in Hn;  lia.
    Qed.

    Remark R03 : max n 2 = n.
    Proof.
      generalize R01, R02; lia.
    Qed.

    Remark R04 : Ack n (2 * n + 3) = Ack n (Ack 2 n).
    Proof.
      now rewrite Ack_2_n.
    Qed.
    
    Remark R05 : Ack n (2 * n + 3) <= Ack (n + 2) n.
    Proof.
      rewrite R04; replace (n+2) with  (2 + max n 2).
       - apply Ack_Ack_le.
       - rewrite R03; lia. 
    Qed.  
    
    Remark R06 : Ack (n + 2) n <= Ack n (n + 2).
    Proof.
      specialize (Hn (n+2) n);
        replace (max (n + 2) n) with (n + 2) in Hn by lia;  auto.
    Qed.
  
    Remark R07 :  Ack n (n + 2) < Ack n (2 * n + 3).
    Proof.
      destruct (Ack_properties n) as [H _]; apply H; lia.
    Qed.

    Lemma contrad : False.
    Proof.
      generalize R04, R05, R06,  R07; intros; lia.
    Qed.

  End Contrad.

  Lemma Ack_not_PR : False.
  Proof.
    destruct Ack_majorized as [n Hn].
    apply (contrad n); intros x y; specialize (Hn (x::y::nil)).
    cbn in Hn;  now   rewrite max_0_r in Hn.
  Qed.

End Impossibility_Proof.

(** * Remark: for any [n], [Ack n] is primitive recursive. *)

Lemma AckSn_as_iterate (n:nat) : extEqual 1 (Ack (S n))
                                          (fun k => iterate (Ack n) (S k) 1).
Proof. intro;reflexivity. Qed. 


Lemma AckSn_as_PRiterate (n:nat):
  extEqual 1 (Ack (S n)) (fun k => primRec.iterate (Ack n) (S k) 1).
Proof.
  intros k; rewrite AckSn_as_iterate.
  generalize (Ack n); intro f.
  generalize 1; generalize (S k); induction n0.
  - cbn; auto.
  - cbn;  intro n1; rewrite IHn0; auto.
Qed.

Lemma iterate_nat_rec (g: nat->nat) (n:nat) x :
  iterate g n x = nat_rec (fun _ => nat) x (fun x y => g y) n.
Proof.
  induction n; cbn; auto.
Qed.


Section Proof_of_Ackn_PR.

  Section S_step.
    Variable n:nat.

    Hypothesis IHn: isPR 1 (Ack n).

    Remark R1 : extEqual 1 (Ack (S n))
                         (fun a : nat =>
                            nat_rec (fun _ : nat => nat) 1
                                    (fun _ y : nat => Ack n y)
                                    (S a)).
    
    Proof.
      intro a; cbn; now rewrite iterate_nat_rec.
    Qed.

    Remark R2 : isPR 1
                     (fun a : nat =>
                        nat_rec (fun _ : nat => nat) 1
                                (fun _ y : nat => Ack n y)
                                (S a)).
    Proof.
      apply compose1_1IsPR.
      - apply succIsPR.
      - eapply indIsPR; now apply filter01IsPR.  
    Qed.


    Remark R3 : isPR 1 (Ack (S n)).
    Proof.
      destruct R2 as [x Hx]; exists x.
      eapply extEqualTrans with (1:= Hx).
      intro; symmetry; apply R1.
    Qed.

  End S_step.

  Theorem Ackn_IsPR (n: nat) : isPR 1 (Ack n).
  Proof.
    induction n.
    - cbn; apply succIsPR.
    -  apply R3; auto.  
  Qed.

End Proof_of_Ackn_PR.













