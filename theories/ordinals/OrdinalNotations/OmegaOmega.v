(** * An implementation of # &omega;<sup>&omega;</sup> *)

(** New implementation as a refinement of epsilon0 *)

Require T1 E0.
Require Import Arith.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Require Import List Bool.
Require Import Recdef Lia.
Require Import Coq.Wellfounded.Inverse_Image
        Coq.Wellfounded.Inclusion RelationClasses.

Coercion is_true: bool >-> Sortclass.
Require Import Comparable.
Require Import Logic.Eqdep_dec.

(** * Representation by lists of pairs of integers *)

Module LO.
  
  Definition t := list (nat*nat).

  Definition  zero : t := (@nil (nat * nat): t).

  (** omega^ i * S n + alpha *)

  Notation ocons i n alpha := ((i,n)::alpha).

  (** Finite ordinals *)
  
  Notation  FS n := (ocons 0 n zero: t).

  Definition fin (n:nat): t := match n with 0 => zero | S p => FS p end.

  (** [omega ^i ] *)

  Notation phi0 i := (ocons i 0 nil).

  (** [omega ^i * (k+1)] *)
  
  Definition omega_term (i k: nat) : t :=
    ocons i k zero.

  Notation omega := (phi0 1). 

  Coercion fin  : nat >-> t.

  (** data refinement *)

  Fixpoint refine (a : t) : T1.T1 :=
    match a with
      nil => T1.zero
    | ocons i n b => T1.ocons (T1.fin i) n (refine b)
    end.

  (**  Examples 
  Compute T1.pp (refine (fin 42)).
  Compute T1.pp (refine omega).
  Compute T1.pp (refine (phi0 33)).
   *)


  Inductive ap : t -> Prop :=
    ap_intro : forall a, ap (phi0 a).

  (** Successor and limits (syntactic definitions) *)

  Fixpoint succb (alpha:t) :=
    match alpha with
      nil => false
    | ocons 0 _ _ => true
    | ocons i n beta => succb beta
    end.
  
  Fixpoint limitb (alpha:t) :=
    match alpha with
      nil => false
    | ocons 0 _ _ => false
    | ocons i n nil => true
    | ocons i n beta => limitb beta
    end.


  Lemma succb_ref (a:t): succb a -> T1.succb (refine a).
  Proof.
    induction a as [| a l]; cbn.
    - trivial.
    - destruct a as [n n0]; now destruct n.
  Qed.

  Lemma limitb_ref (a:t): limitb a -> T1.limitb (refine a).
  Proof.
    induction a as [| a l]; cbn.
    - trivial.
    -  destruct a as [n n0].
       destruct n.
       + discriminate.
       + simpl T1.limitb; destruct l. 
         * trivial.
         * intro H; rewrite IHl; case (refine (p::l)); auto.
  Qed.


  Fixpoint compare (alpha beta:t):comparison :=
    match alpha, beta with
    | nil, nil => Eq
    | nil, ocons a' n' b' => Lt
    | _   , nil => Gt
    | (ocons a n b),(ocons a' n' b') =>
      (match Nat.compare a a' with 
       | Lt => Lt
       | Gt => Gt
       | Eq => (match Nat.compare n n' with
                | Eq => compare b b'
                | comp => comp
                end)
       end)
    end.
  
  Lemma compare_ref (alpha beta:t) :
    compare alpha beta = T1.compare (refine alpha) (refine beta).
  Proof.
    revert beta. induction alpha.
    - destruct beta.
      + easy.
      + cbn. now destruct p.
    - destruct a, beta.
      + now cbn.
      + destruct  p; cbn.
        destruct (n ?= n1) eqn: cn_n1;
          destruct (n0 ?= n2) eqn: c_n0_n2;
          rewrite  T1.compare_fin_rw; now rewrite cn_n1.
  Qed.


  Definition lt alpha beta : Prop :=
    compare alpha beta = Lt.


  Lemma compare_rev :
    forall alpha beta,
      compare beta alpha = CompOpp (compare alpha beta).
  Proof.
    induction alpha,  beta.
    - easy.
    - cbn; destruct p; cbn; trivial. 
    - cbn; destruct a; reflexivity. 
    - cbn; rewrite IHalpha. destruct p, a;  rewrite Nat.compare_antisym.
      destruct (Nat.compare n1 n) eqn:? ; cbn; trivial.
      rewrite Nat.compare_antisym;
        destruct  (Nat.compare n2 n0) eqn:? ; now cbn.
  Qed.


  Lemma compare_reflect :
    forall alpha beta,
      match compare alpha beta with
      | Lt => lt alpha beta
      | Eq => alpha = beta
      | Gt => lt beta alpha
      end.
  Proof.
    unfold lt; induction alpha  as [ | [p n]].
    - destruct beta.
      + easy.
      + cbn; now destruct p.
    - destruct beta as [ | [p0 n0] beta]. 
      + cbn; trivial.
      + cbn; specialize (IHalpha beta);
          rewrite compare_rev with alpha beta; 
          rewrite Nat.compare_antisym in * ;
          destruct (compare alpha beta), (p0 ?= p) eqn:Heq; simpl in *;
            subst; try easy;
              apply Nat.compare_eq_iff in Heq as -> ;
              destruct (n ?= n0) eqn:Heqc; trivial.
        * now apply Nat.compare_eq_iff in Heqc as ->.
        * destruct (n ?= n0) eqn:Heqn; trivial;
            now rewrite Nat.compare_antisym, Heqn.
        * rewrite Nat.compare_antisym;   now rewrite Heqc.
        * destruct (n ?= n0) eqn:?; trivial; try discriminate.
          rewrite Nat.compare_antisym; now rewrite Heqc0.
        *  rewrite Nat.compare_antisym; now rewrite Heqc.
  Qed.

  Lemma compare_correct (alpha beta: t):
    CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
                (compare alpha beta).
  Proof.
    unfold lt;  generalize (compare_reflect alpha beta).
    destruct (compare alpha beta); now constructor.
  Qed.

  Lemma lt_ref (a b : t) : lt a b <-> T1.lt (refine a) (refine b).
  Proof.
    unfold lt, T1.lt; rewrite compare_ref; now split.
  Qed.

  Lemma eq_ref  (a b : t) : a = b <-> refine a = refine b.
  Proof.
    destruct (compare_correct a b).
    - split.
      + intro; now subst.  
      + trivial.
    - split.
      + intro; now subst.
      + rewrite lt_ref in H. intros H0; rewrite H0 in H.
        destruct (T1.lt_irrefl H).    
    -  split.
       + intro; now subst.
       + rewrite lt_ref in H. intros H0; rewrite H0 in H.
         destruct (T1.lt_irrefl H).
  Qed.

  Lemma lt_irrefl (alpha: t): ~ lt alpha alpha.
  Proof.
    rewrite lt_ref; now apply T1.lt_irrefl.
  Qed.


  Lemma lt_trans (alpha beta gamma : t):
    lt alpha beta -> lt beta gamma -> lt alpha gamma.
  Proof.
    rewrite !lt_ref; apply T1.lt_trans.
  Qed.

  #[global] Instance lo_strorder: StrictOrder lt.
  Proof.
    constructor. 
    - intro a; apply lt_irrefl.
    - intros a b c; eapply lt_trans.
  Qed.
  
  #[global] Instance lo_comparable : Comparable lt compare.
  Proof.
    constructor.
    - exact lo_strorder. 
    - apply compare_correct.
  Qed.


  Fixpoint nf_b (alpha : t) : bool :=
    match alpha with
    | nil => true
    | ocons a n nil => true
    | ocons a n ((ocons a' n' b') as b) =>
      (nf_b b && Nat.ltb a' a)%bool
    end.

  Definition nf alpha :Prop := 
    nf_b alpha.

  (** refinements of T1's lemmas *)

  Lemma zero_nf : nf zero.
  Proof. reflexivity. Qed.

  Lemma fin_nf (i:nat) : nf (fin i).
  Proof.
    destruct i; red; now cbn.
  Qed. 


  Lemma single_nf :
    forall i n, nf (ocons i n zero).
  Proof. unfold nf; now cbn. Qed. 

  Lemma ocons_nf :
    forall i n j n' b, 
      Nat.lt j i ->
      nf(ocons j n' b)->
      nf(ocons i n (ocons j n' b)).
  Proof.
    unfold nf; simpl; intros i n j n' b' Hltji Ha.
    apply Nat.ltb_lt in Hltji as ->.
    destruct b'; auto with bool. 
  Qed.

  #[local] Hint Resolve zero_nf  single_nf ocons_nf : core.


  Lemma nf_inv2 :
    forall i n b, nf (ocons i n b) -> nf b.
  Proof.
    unfold nf; cbn; destruct i, b;  auto.
    destruct p; cbn; destruct b.
    - auto with bool. 
    - destruct p; auto with bool. 
      rewrite andb_false_r; discriminate.
    - destruct p; intro H; apply andb_prop in H; now destruct H. 
  Qed.


  Lemma nf_inv3 :
    forall i n  j n' b',
      nf (ocons i n (ocons j n' b')) -> Nat.lt j i.
  Proof.
    unfold nf; cbn;
      destruct  b'; try discriminate; auto with T1;
        intro H; red in H; repeat rewrite andb_true_iff in H.
    - destruct H as [_ H]; destruct i. 
      + discriminate.
      + rewrite  Nat.leb_le in H; lia.
    - destruct p; destruct i.
      + destruct j; destruct H; discriminate.
      + destruct H; rewrite  Nat.leb_le in H0; lia.
  Qed.


  Lemma nf_ref: forall alpha, T1.nf (refine alpha) <-> nf alpha.
  Proof.
    induction alpha.
    - cbn; split; trivial.
    - destruct a as [i n];  split.
      + intro H;  destruct alpha.
        * apply single_nf.
        * destruct p.
          apply ocons_nf.
          -- cbn in H; apply T1.nf_inv3 in H; now apply T1.lt_fin_iff. 
          -- cbn in H; apply IHalpha; apply T1.nf_inv2 in H; apply H.
      + intro H; destruct alpha.
        * apply T1.single_nf, T1.nf_fin.
        * destruct p; cbn; apply T1.ocons_nf.
          --  apply nf_inv3 in H; now apply T1.lt_fin_iff.
          -- apply T1.nf_fin.
          -- apply nf_inv2 in H; now rewrite IHalpha.
  Qed.


  Declare Scope lo_scope.
  Delimit Scope lo_scope with lo.
  Open Scope lo_scope.

  Fixpoint succ (alpha : t) : t :=
    match alpha with
      nil => fin 1
    | ocons 0 n _  => ocons 0 (S n) nil
    | ocons a n beta => ocons a n (succ beta)
    end.

  Fixpoint plus (alpha beta : t) :t :=
    match alpha,beta with
    |  nil, y  => y
    |  x, nil  => x
    |  ocons a n b, ocons a' n' b' =>
       (match Nat.compare a a' with
        | Lt => ocons a' n' b'
        | Gt => (ocons a n (plus b (ocons a' n' b')))
        | Eq  => (ocons a (S (n+n')) b')
        end)
    end
  where "alpha + beta" := (plus alpha beta) : lo_scope.

  Fixpoint mult (alpha beta : t) : t :=
    match alpha,beta with
    |  nil, _  => zero
    |  _, nil => zero
    |  ocons 0 n _, ocons 0 n' _ =>
       ocons 0 (Peano.pred((S n) * (S n'))) zero
    |  ocons a n b, ocons 0 n' _ =>
       ocons a (Peano.pred ((S n) * (S n'))) b
    |  ocons a n b, ocons a' n' b' =>
       ocons (a + a')%nat n' ((ocons a n b) * b')
    end
  where "alpha * beta" := (mult alpha beta) : lo_scope.


  Compute omega * omega.
  Compute fin 1 * omega.
  Compute fin 42 * omega.

  Lemma phi0_ref (i:nat) : refine (phi0 i) = T1.phi0 (T1.fin i).
  Proof. reflexivity. Qed.

  Lemma phi0_nf  (i:nat) : nf (phi0 i).
  Proof. unfold nf;  now cbn. Qed.
  
  Lemma succ_ref (alpha : t) :
    refine (succ alpha) = T1.succ (refine alpha).
  Proof.  
    induction alpha.
    - now cbn.
    - destruct alpha.
      + destruct a;  cbn; destruct n; now cbn.
      + destruct a; destruct n.
        * now cbn.
        * destruct p; destruct n1. 
          -- now cbn.
          -- cbn in *; now rewrite IHalpha.
  Qed.

  Lemma succ_nf alpha : nf alpha -> nf (succ alpha).
  Proof.
    intro H; rewrite <- nf_ref in *; rewrite succ_ref; now apply T1.succ_nf.
  Qed.
  
  Lemma plus_ref : forall alpha beta: t,
      refine (alpha + beta) = T1.plus (refine alpha) (refine beta).
  Proof.
    induction alpha, beta.
    - now cbn.
    - now cbn.
    - cbn; destruct a. now cbn.
    - destruct a, p; cbn;  destruct (n ?= n1) eqn:cn_n1.
      1,2:   rewrite T1.compare_fin_rw in *; rewrite cn_n1; now cbn.
      rewrite T1.compare_fin_rw in *; cbn;rewrite cn_n1, IHalpha; now cbn.
  Qed.


  Lemma plus_nf alpha beta : nf alpha -> nf beta -> nf (alpha + beta).
  Proof.
    intros Halpha Hbeta; rewrite <- nf_ref in *; rewrite plus_ref;
      now   apply T1.plus_nf.
  Qed.


  Lemma mult_ref : forall alpha beta: t,
      refine (alpha * beta) = T1.mult (refine alpha) (refine beta).
  Proof.
    induction alpha.  
    -  cbn; destruct beta. 
       + now cbn.
       + cbn; destruct p; now cbn.
    - induction beta.
      +  destruct a; cbn. destruct n; now cbn.
      +  destruct a, a0; cbn. destruct n; cbn. destruct n1; cbn; trivial.
         * f_equal; rewrite IHbeta; f_equal.
         * cbn. destruct n1. cbn. reflexivity.
           cbn. f_equal. f_equal. lia.
           rewrite IHbeta; f_equal.
  Qed.


  Lemma mult_nf alpha beta : nf alpha -> nf beta -> nf (alpha * beta).
  Proof.
    intros Halpha Hbeta; rewrite <- nf_ref in *; rewrite mult_ref;
      now   apply T1.mult_nf.
  Qed.


 Lemma plus_assoc (a b c: t) : a + (b + c) = a + b + c.
 Proof. apply eq_ref; rewrite !plus_ref; apply T1.plus_assoc. Qed.

End LO.

Declare Scope OO_scope.

Delimit Scope OO_scope with oo.
Open Scope OO_scope.
Import LO.

(** * well formed ordinal representation *)

Module OO.
  
  Class OO : Type := mkord {data: LO.t ; data_ok : LO.nf data}.
  
  Arguments data : clear implicits.
  #[local] Hint Resolve data_ok : core.

  Definition lt (alpha beta: OO) := LO.lt (data alpha) (data beta).
  Definition le := leq lt.
  Definition compare (alpha beta: OO):= LO.compare (data alpha) (data beta).

  Instance Zero : OO := @mkord nil refl_equal.

  Instance _Omega : OO.
  Proof.
    now exists omega%lo.  
  Defined. 


  Instance Fin (i:nat) : OO.
  Proof.
    exists (LO.fin i); apply fin_nf.
  Defined.
  
  Notation omega  := _Omega.

  Instance Succ (alpha : OO) : OO.
  Proof.
    refine (@mkord (LO.succ (@data alpha)) _); 
      apply succ_nf,  data_ok.
  Defined.


  Instance plus (alpha beta : OO) : OO.
  Proof.
    refine (@mkord (LO.plus (@data alpha) (@data beta))_ );
      apply plus_nf; apply data_ok.
  Defined.

  Infix "+" := plus : OO_scope.

  Instance mult (alpha beta : OO) : OO.
  Proof.
    refine (@mkord (LO.mult (@data alpha) (@data beta))_ );
      apply mult_nf; apply data_ok.
  Defined.

  Infix "*" := mult : OO_scope.

  Instance phi0 (i : nat): OO.
  Proof.
    refine (@mkord (LO.phi0 i) _). 
    apply phi0_nf; apply data_ok.
  Defined.



  Infix "*" := mult : OO_scope.

  Instance embed (alpha: OO) : E0.E0.
  Proof.
    destruct alpha as [data Hdata].
    refine (@E0.mkord (LO.refine data) _).
    now apply nf_ref.  
  Defined.

  Lemma lt_embed (alpha beta : OO): lt alpha beta ->
                                    E0.Lt (embed alpha) (embed beta).
  Proof.
    destruct alpha, beta; unfold lt, E0.Lt, T1.LT; cbn; repeat split.
    - now apply nf_ref.
    - now apply lt_ref.
    - now apply nf_ref.
  Qed.

  Instance oo_str : StrictOrder lt.
  split.
  - intros x H; destruct x.
    unfold lt in H; cbn; destruct (LO.lt_irrefl _ H).
  - intros x y z; destruct x, y, z.
    unfold lt ; cbn; intros; eapply LO.lt_trans; eauto.
  Qed.

  Lemma nf_proof_unicity :
    forall (alpha:t) (H H': nf alpha), H = H'.
  Proof.
    intros; red in H, H'; apply eq_proofs_unicity_on.
    destruct y. 
    - rewrite H; auto. 
    - rewrite H; right; discriminate. 
  Qed.

  Lemma OO_eq_intro : forall alpha beta : OO,
      data alpha = data beta -> alpha = beta.
  Proof.
    destruct alpha, beta; simpl; intros; subst; f_equal; auto; 
      apply nf_proof_unicity.
  Qed.


  Instance OO_comp : Comparable lt compare.
  Proof.
    split.
    - apply oo_str.
    - destruct a, b; unfold compare; cbn.
      destruct (LO.compare_correct data0 data1).
      + constructor; subst; apply OO_eq_intro; now cbn.
      + constructor; red; now cbn.
      + constructor; red; now cbn.
  Qed. 

  Lemma lt_wf : well_founded lt.
  Proof.
    specialize  (ON_Generic.wf_measure (B:= OO) embed); intro Hm;
      unfold ON_Generic.measure_lt in Hm; eapply wf_incl.
    2: eassumption.
    intros x y Hxy; red; now apply lt_embed.
  Qed.

  Import ON_Generic.
  Instance ON_OO : ON lt compare.
  Proof.
    split.  
    - apply OO_comp.
    - apply lt_wf.
  Qed.

End OO.








