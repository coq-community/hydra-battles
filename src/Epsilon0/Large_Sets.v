(** An implementation through lists of "alpha-large" sets 
    (After Ketonen and Solovay's "rapidly growing Ramsey functions" )
*)

(*  Pierre Casteran 
    Univ. Bordeaux, laBRI
*)

 



Require Import E0 Canon Paths MoreLists Lia Iterates Exp2.
Require Import Compare_dec.
Import Relation_Operators Sorted  Operators_Properties.
Open Scope t1_scope.

(** * Definitions *)


(** ** minimal large sequences *)

Definition mlarge alpha s := path_to zero s alpha.

Definition mlargeS alpha s := path_toS zero s alpha.


(** *  Last step of a minimal path  *)

Inductive L_spec : T1 -> (nat -> nat) -> Prop :=
  L_spec0 :
    forall f, (forall k, f (S k) = S k) ->  L_spec zero f
| L_spec1 : forall alpha f,
    alpha <> zero ->
    (forall k, mlarge alpha (interval (S k) (Nat.pred (f (S k))))) ->
    L_spec alpha f.




(** Test functions 
  - If f is correct w.r.t. [L_spec]
 : "Compute L_test alpha f k" should return (one=one).
  - If f k is too small, returns (alpha = one) (with one < alpha)
  - If f k is too big, returns (zero = one)
 *)


Definition L_test (alpha:T1) f k :=
  gnaw alpha (interval k (f k - 2)%nat) = one.


Compute L_test omega (fun i => S (2 * i))%nat 23.


(** ** n-large intervals *)

Lemma gnaw_finite_1_iota :
  forall n i, gnaw (S n) (iota_from (S i) n) = 1.
Proof.
  induction n.  
  - now cbn.
  - intro i; specialize (IHn (S i)).
    rewrite <- FS_rw.  rewrite <- succ_compat. simpl iota_from.
    rewrite gnaw_succ;  auto with T1. 
Qed.


Lemma gnaw_finite_1 : forall n i, gnaw (S n) (interval (S i) (n + i)%nat) = 1.
Proof.
  intros ; unfold interval.
  replace (S (n + i) - S i)%nat with n; [| lia].
  apply gnaw_finite_1_iota.
Qed.

Lemma gnaw_finite : forall n i, gnaw (S n) (iota_from  (S i) (S n)) = 0.
Proof.
  intros;  now rewrite  iota_from_app, gnaw_app, gnaw_finite_1_iota.
Qed.



Lemma gnaw_n_R : forall s n,  ~ In 0 s -> 
                              (n < List.length s)%nat ->
                              gnaw (S n) s = zero.
Proof.
  induction s.
  -   cbn;  intros;  destruct n;  inversion H0.
  -   cbn;  destruct n. 
    +   cbn; auto.
        destruct a.
      * destruct 1; auto.  
      * now rewrite gnaw_zero. 
    +   intros H; destruct a.
        * destruct H; auto.
        * intro; apply IHs; [tauto | auto with arith].
Qed.


(** * Properties of m-largeness and L-functions *)

Lemma mlarge_unicity alpha k l l' : 
  mlarge alpha (interval (S k) l) ->
  mlarge alpha (interval (S k) l') ->
  l = l'.
Proof.
  intros H H0; assert (H1 : (S k<= l)%nat) by
      (eapply path_to_interval_inv_le; eauto).
  assert (H2 : (S k <= l')%nat) by
      (eapply path_to_interval_inv_le; eauto). 
  destruct (Compare_dec.lt_eq_lt_dec l l') as [[Hlt | Heq] | Hgt]; auto.
  - rewrite (interval_app (S k) l l') in H0;
      [|try lia| try lia].
    destruct (@path_to_appR _ _ _ H0 (interval (S k) l)
                            (interval (S l) l')); trivial.
    + apply interval_not_empty; auto.
    + apply interval_not_empty; auto.
    + intro H3; destruct (in_app_or _ _ _ H3).
      *  apply (@interval_lt_not_In 0 (S k) l); auto with arith.
      *  apply (@interval_lt_not_In 0 (S l) l'); auto with arith.
    + destruct H3 as [H3 H4].
      assert (x = zero).
      { apply path_to_gnaw in H; apply path_to_gnaw in H3; congruence. }
      subst; destruct (path_to_zero H4).
  - rewrite (interval_app (S k) l' l) in H;
      [| try lia | try lia].
    destruct (@path_to_appR _ _ _ H (interval (S k) l')
                            (interval (S l') l)); trivial.
    apply interval_not_empty; auto.
    apply interval_not_empty; auto.
    + intro H3; destruct (in_app_or _ _ _ H3).
      apply (@interval_lt_not_In 0 (S k) l'); auto with arith.
      apply (@interval_lt_not_In 0 (S l') l);
        auto with arith.
    + destruct H3.
      assert (x = zero).
      { apply path_to_gnaw in H0; apply path_to_gnaw in H3; congruence. }
      subst; destruct (path_to_zero H4).
Qed.


Lemma mlargeS_iff alpha x s : s <>nil ->
                              mlargeS alpha (x::s) <->
                              gnawS alpha (but_last x s) = one.
Proof.
  intro H; split.
  - intros H0; generalize (path_toS_zero_but_last H0 H); intro H1;
      apply path_toS_gnawS in H1; auto.
  -  intro H0; red; rewrite <- but_last_app;
       apply path_toS_app with one; auto.
     + left;  split; auto;  discriminate.
     + rewrite <- H0; apply gnawS_path_toS.
      * destruct s.
       --  now destruct H.
       --  discriminate.
      * rewrite  H0; discriminate.
Qed.

Lemma mlarge_unshift alpha s :
   ~In 0 s ->  mlarge alpha s <-> mlargeS alpha (unshift s).
Proof.
  unfold mlarge, mlargeS; intros; rewrite path_to_path_toS_iff; auto;
    now split.
Qed.


Lemma mlarge_iff alpha x (s:list nat) :
  s <> nil -> ~ In 0 (x::s) ->
  mlarge alpha (x::s) <-> gnaw alpha (but_last x s) = one.
Proof.
  intros H H0; split.
  - intros H1; rewrite mlarge_unshift in H1; auto.
     rewrite gnaw_gnawS,  unshift_but_last; auto.
     + simpl in H1;  destruct x.
       * destruct H0; left; auto.
       * simpl; simpl in H1; rewrite mlargeS_iff in H1; auto.
         apply unshift_not_nil; auto.
         -- intro; apply H0; now right.
  - rewrite mlarge_unshift; auto.
     rewrite gnaw_gnawS; destruct x.
    + destruct H0; now left.
     + simpl; rewrite unshift_but_last; auto.
       simpl; rewrite mlargeS_iff;  auto.
       apply unshift_not_nil; intro; apply H0; now right.
Qed.







(** About the length of mlarge intervals *)


Lemma L_spec_inv2 alpha f :
  L_spec alpha f -> alpha <> zero ->
  (forall k,  mlarge alpha (interval (S k) (Nat.pred (f (S k))))).
Proof.  
   inversion_clear 1; [now destruct 1 | auto].
Qed.

Lemma L_spec_compat alpha (f g : nat -> nat) :
  L_spec alpha f -> (forall n, f n = g n) -> L_spec alpha g.
Proof.
  destruct 1.
  - left; congruence.
  -  right; [trivial | intros ;  rewrite <- H1; auto].
Qed.



(** 

Properties of [L_spec]

*)

Lemma L_zero_inv f : L_spec zero f -> forall k, f (S k) = S k.
Proof.
  inversion_clear 1; [auto | now destruct H0]. 
Qed.

Lemma L_pos_inv alpha  f : alpha <> zero -> L_spec alpha f ->
                        forall k, (S k < f (S k))%nat.
Proof.
  destruct alpha; [now destruct 1 | intros _ H].
    inversion_clear H as [H0 H1 |].
    intro k; specialize (H1 k).      
    generalize (path_to_not_nil H1); intro H2.
    rewrite interval_not_empty_iff in H2; lia.
Qed.

Lemma L_spec_unicity alpha f g :
  L_spec alpha f -> L_spec alpha g ->
  forall k, f (S k) = g (S k).
Proof.
  inversion 1.
  - subst; inversion 1.
    +    intros; now rewrite H0, H2.    
    +    now destruct H2.
  -  inversion 1.
     + subst; now destruct H0.
     + intro k;  specialize (mlarge_unicity alpha _ _ _ (H1 k) (H6 k)).
       intro H9; assert (S k < f (S k))%nat by
           (eapply L_pos_inv; eauto).
       assert (S k < g (S k))%nat by (eapply L_pos_inv; eauto).
     lia.
Qed.


(** Composition lemmas *)

Section succ.
   Variables (beta : T1) (f : nat -> nat).

   Hypotheses (Hbeta : nf beta)
              (f_mono : strict_mono f)
              (f_Sle : S <<= f)
              (f_ok : L_spec beta f).


   Definition L_succ := fun k => f (S k).

   Lemma L_succ_mono : strict_mono L_succ.
   Proof.
    intros x y Hxy; unfold L_succ; apply f_mono; lia.
   Qed.

   Lemma L_succ_Sle : S <<= L_succ.
   Proof.
     intro k; unfold L_succ; specialize (f_Sle (S k)); lia.
   Qed.

   Lemma L_succ_ok : L_spec (succ beta) L_succ.
   Proof.
     inversion_clear f_ok.
     - unfold L_succ; right.
       + discriminate.
       + intros; rewrite H;
           simpl;red; rewrite interval_singleton; left.
       * discriminate.
       * split.
         -- discriminate.
         -- reflexivity.
     -  unfold L_succ; right.
      +  apply succ_not_zero.
      + intro k; red; path_decompose (S k).
        instantiate (1 := beta).
        --  apply H0.
        --  rewrite interval_singleton; left.
            ++ discriminate.
            ++ split.
               **  apply succ_not_zero.
               **  now rewrite canonS_succ.
        --  apply  Nat.lt_le_pred.
            generalize (f_Sle  (S (S k))); lia.
   Qed.
   
End succ.


Section lim.
  Variables (lambda : T1)
            (Hnf : nf lambda)
            (Hlim : limitb lambda)
            (f : nat -> nat -> nat)
            (H : forall k, L_spec (canonS lambda k) (f (S k))).
  
  Remark canon_not_null : forall k,  canonS lambda k <> zero.
  Proof.
   intro; apply limitb_canonS_not_zero; auto.  
  Qed.

  Definition  L_lim k := f k (S k).

  Lemma L_lim_ok : L_spec lambda L_lim.
  Proof.
    right.
    - apply limitb_not_zero; auto.
    - intro k;  unfold L_lim.  red; path_decompose (S k).
      instantiate (1:= canon lambda (S k)).
      *  specialize (H k); inversion H.
       --  generalize (canon_not_null k); rewrite <- H0; now destruct 1.
       --  apply H1.
      * rewrite interval_singleton; left.
       --    discriminate.
       -- split.
        ++  apply limitb_not_zero; auto.
        ++  reflexivity.
     *  specialize (L_pos_inv (canonS lambda k) (f (S k))
                              (canon_not_null k) (H k) (S k));  lia.       
  Qed.
  
End lim.

(** ** Finite ordinals *)


Definition L_fin i := fun k => (i + k)%nat.

Lemma L_finS_S_le i : S <<= L_fin (S i).
Proof.
 intro k; unfold L_fin.  lia.
Qed.

Lemma L_fin_smono i: strict_mono (L_fin i).
Proof.
  intros k l Hlt; unfold L_fin, id;  lia.
Qed.

Lemma L_S_succ_rw i : forall k,  L_fin (S i) k = L_succ (L_fin i) k.
Proof. unfold L_succ, L_fin; intros; lia.
Qed.


Lemma L_fin_ok i : L_spec (fin i) (L_fin i).
Proof.
  induction i.  
  - left; reflexivity.
  -  apply L_spec_compat with (L_succ (L_fin i)).
     change (fin (S i)) with (FS i); rewrite <- succ_compat.
     destruct i.
     + simpl. unfold L_succ, L_fin; right.
       * discriminate.
       * intro k; red; simpl.
         rewrite interval_singleton;  left.
         -- discriminate.
         --  split; [ discriminate |  reflexivity].
     + apply L_succ_ok; auto with T1.
       apply  L_finS_S_le.
     + intros ; unfold L_fin, L_succ; lia.
  Qed.


Lemma mlarge_FS :
  forall i k,  mlarge (FS i) (interval (S k) (S (i+k)%nat)). 
Proof.
  intro i. assert (FS i <> zero) by discriminate.
  generalize  (L_fin_ok (S i)); intro H0.
  inversion H0.
  intro k; specialize (H2 k).
  unfold L_fin in H2.
   replace (Nat.pred (S i + S k))%nat with  (S (i + k))%nat in H2; auto;lia.
Qed.


Definition L_omega k := S (2 * k)%nat.

Lemma L_omega_Sle : S <<= L_omega.
Proof.
  intro k; unfold L_omega; lia.
Qed.


Lemma L_omega_smono : strict_mono L_omega.
Proof.
  intros k l Hlt; unfold L_omega; lia.
Qed.


Lemma mlarge_omega k : mlarge omega (interval (S k) (2 * (S k))%nat).
Proof.
  specialize (L_lim_ok omega nf_omega refl_equal L_fin (fun i => L_fin_ok (S i))).
  intros.
  inversion H; auto.
  unfold L_fin  in H1; specialize (H1 k).   simpl in H1. 
  now replace ( (2 * S k))%nat with   (k + S (S k))%nat by lia.
Qed.

Lemma L_omega_ok : L_spec omega L_omega.
Proof.
  About L_lim.
  specialize (L_lim_ok omega nf_omega refl_equal L_fin
                       (fun i => L_fin_ok (S i))) ; intro H.
   eapply L_spec_compat with (1:=H).
   intro ; unfold L_lim,  L_fin, L_omega; lia.
Qed.

Lemma path_to_omega_mult (i k:nat) :
  path_to (omega * i)
          (interval (S k) (2 * (S k))%nat)
          (omega * (S i)).
Proof.
  destruct i.
  - simpl; apply mlarge_omega.
  -   path_decompose (S k).
      instantiate (1:=ocons one i (S k)). 
      + simpl (omega * S i). replace (i + 0)%nat with i.
        apply path_to_tail; auto with T1.
      *  assert (H := mlarge_FS k  (S k)). 
         replace (2 * S k)%nat with (S (k + S k))%nat by lia; auto.
      *  lia.
    +  rewrite interval_singleton; left; [discriminate | ].
      simpl; replace (i + 0)%nat with i.  split; [ discriminate | reflexivity].
      lia.
Qed.


Lemma omega_mult_mlarge_0 i  : forall k,
    mlarge  (omega * (S i))
            (interval (S k)
                      (Nat.pred (iterate (fun p =>  S (2 * p)%nat)
                                         (S i)
                                         (S k)))).
Proof.
  unfold mlarge; induction i.
  - simpl; intro k;
      replace (S (k + S (k + 0)))%nat with (2 * S k)%nat by lia; 
      apply mlarge_omega.
  - intro k;  path_decompose (2 * (S k))%nat.
    + instantiate (1:= omega * S i).
      * specialize (IHi (2 * S k)%nat); rewrite iterate_rw; auto.
    +   apply path_to_omega_mult.
    + clear IHi; induction i.
      * cbn; lia.
      * eapply Nat.le_trans.
        --  eapply IHi.
        --  apply Nat.pred_le_mono;  apply iterate_mono_weak; lia.
Qed.


Definition L_omega_mult i (x:nat) :=  iterate L_omega i x.


Example Ex : L_omega_mult 8 5 = 1535.
Proof. reflexivity.  Qed.

Lemma L_omega_mult_Sle i : S <<= L_omega_mult (S i).
Proof.
  unfold L_omega_mult;apply iterate_Sge,  L_omega_Sle.
Qed.



Lemma L_omega_mult_ok (i: nat) :
  L_spec (omega * i) (L_omega_mult i).
Proof.
 destruct i.
 - left;  intro k. reflexivity. 
 - right.
   + cbn; discriminate.
   + intros k; unfold L_omega_mult, L_omega;
       apply omega_mult_mlarge_0.
 Qed.

Lemma L_omega_mult_eqn (i : nat) :
  forall (k : nat),  (0 < k)%nat  ->
                     L_omega_mult i k = (exp2 i * S k - 1)%nat.
Proof.
  induction i.
  - unfold L_omega_mult; simpl; intro; lia.
  - intros k Hk; simpl; unfold L_omega_mult;  simpl.
    rewrite IHi;    unfold L_omega;  simpl; auto.
    repeat   rewrite Nat.mul_succ_r;  ring_simplify.
    generalize (exp2_ge_S i); intro; lia.
Qed.



(** ** [omega * omega]  *)

Definition L_omega_square k := iterate (fun z => S (2 * z)%nat)
                                        k
                                        (S k).

Remark L_omega_square_eqn1 k : L_omega_square k =
                                L_omega_mult k (S k).
Proof. reflexivity. Qed.

(** *** Closed formula *)
  
Lemma L_omega_square_eqn k :
  (0 < k)%nat ->
  L_omega_square k = (exp2 k * (k + 2) - 1)%nat.
Proof.
  intro Hk; rewrite L_omega_square_eqn1. 
   -  rewrite L_omega_mult_eqn; auto.
      f_equal; lia.
Qed.

Lemma L_omega_square_Sle : S <<= L_omega_square.
Proof.
  intro k; destruct k.
  - cbn. auto with arith.
  -  unfold L_omega_square.
     generalize  (iterate_Sge (fun z => S (2 * z)%nat)); intro H.
     specialize (H k).
     transitivity (S (S (S k))); auto with arith.
     apply H.
     apply L_omega_Sle.
Qed.

Lemma L_omega_square_smono : strict_mono L_omega_square.
Proof.
  unfold L_omega_square.
  generalize (iterate_mono (fun z : nat => S (2 * z))
                           L_omega_smono L_omega_Sle).
  intros H x y Hxy.
  apply lt_le_trans with (iterate (fun z : nat => S (2 * z)) x (S y)).
  - apply iterate_mono.
   + apply L_omega_smono.
   + apply L_omega_Sle.
   + auto with arith.
  -  apply Nat.lt_le_incl;  apply iterate_lt; auto.
    + split.
      * apply L_omega_smono.
      * apply L_omega_Sle.

Qed.


Lemma L_omega_square_ok: L_spec (omega * omega) L_omega_square.
Proof.
  right; [cbn; discriminate | ].
  intro k; rewrite L_omega_square_eqn1. 
  red; path_decompose (S k).
  - instantiate (1 := omega * S k).
    specialize (L_omega_mult_ok (S k)).
    inversion 1.
    apply (H1 (S k)).
  - rewrite interval_singleton; left.
    + discriminate.
    + split.
      * discriminate.
     * simpl; f_equal; try lia.
  - generalize (L_omega_mult_Sle k (S (S  k))); lia.
Qed.

Compute L_omega_square 8.



Section phi0_mult.
 Variables (alpha : T1) (f : nat -> nat).
 Hypotheses (Halpha : nf alpha)
            (f_mono : strict_mono f)
            (f_Sle : S <<= f)
            (f_ok : L_spec (phi0 alpha) f).

 Remark f_ok_inv :
   forall k, mlarge (phi0 alpha) (interval (S k) (Nat.pred (f (S k)))).
 Proof.
   inversion_clear f_ok; assumption.   
 Qed.

Definition L_phi0_mult i := iterate f i.

Lemma L_phi0_mult_ok i: L_spec (ocons alpha i zero) (L_phi0_mult (S i)).
Proof.
  induction i.
  - unfold L_phi0_mult; simpl. assumption.
  - unfold L_phi0_mult.
    + right.
      * discriminate.
      * intro k; red; path_decompose (Nat.pred (f (S k))).
        instantiate (1:= (ocons alpha i zero)).
            -- rewrite iterate_rw;  inversion_clear IHi.
               specialize (H0 (Nat.pred (f (S k)))).
               rewrite S_pred_rw in *; auto.
            --  apply path_to_mult; auto;  apply f_ok_inv.
        --  generalize (f_Sle (S k)); lia.
        --    generalize (iterate_Sge f  i f_Sle (f (S k)));
                intro; rewrite iterate_rw; lia.
Qed.


Lemma L_phi0_mult_smono i: strict_mono (L_phi0_mult i).
Proof.  now  apply iterate_mono. Qed.

Lemma L_phi0_mult_Sle i: S <<=  L_phi0_mult (S i).
Proof.   now apply iterate_Sge. Qed.

End phi0_mult.

Definition L_omega_square_times i :=  iterate L_omega_square i.

Lemma L_omega_square_times_ok i : L_spec (ocons 2 i zero)
                                         (L_omega_square_times (S i)).
Proof.
  apply L_phi0_mult_ok.
  -  auto with T1.
  -  apply L_omega_square_Sle.
  -  apply L_omega_square_ok.
Qed.
  
Definition L_omega_cube  := L_lim  L_omega_square_times .

Lemma L_omega_cube_ok : L_spec (phi0 3) L_omega_cube.
Proof.
  unfold L_omega_cube.
  apply L_lim_ok.
  - auto with T1.
  - auto with T1.
  - intro k; simpl canonS; apply L_omega_square_times_ok.
Qed.

Lemma L_omega_cube_eqn i : L_omega_cube i = L_omega_square_times i (S i).
Proof.   reflexivity. Qed.



Lemma exp2_k_mult_pos k:
  (0 < k -> 4 <= exp2 k * (k + 2))%nat.
Proof.
  change 4 with (2 * 2)%nat; intro Hk; apply mult_le_compat; auto.
  - generalize (exp2_ge_S k);  lia.
  - lia. 
Qed.



Example omega_square_thrice_eqn : forall k,
    (0 < k)%nat ->
    let M := (exp2 k * (k + 2) - 1)%nat in
    let N := exp2 M in
    let P := (N * (M + 2) - 1)%nat in
    L_omega_square_times 3 k  =
    (exp2 P  * (P + 2) - 1)%nat.
Proof.
  intros.  unfold P, N, M.
  unfold L_omega_square_times; simpl.
  generalize (exp2_k_mult_pos k H); intro H0.
  repeat rewrite L_omega_square_eqn; auto; try lia.
  assert (1 * 4 <=
          exp2 (exp2 k * (k + 2) - 1) * (exp2 k * (k + 2) - 1 + 2))%nat
  by (apply mult_le_compat; [apply exp2_positive | lia]); lia.
Qed.


Compute let k := 4 in (exp2 k * (k + 2) -1 )%nat.

Lemma L_omega_cube_3_eq:
  let N := exp2 95 in
  let P := (N * 97 - 1)%nat in
  L_omega_cube 3  = (exp2 P * (P + 2) - 1)%nat.
Proof.
  rewrite L_omega_cube_eqn,
  omega_square_thrice_eqn; [reflexivity | auto with arith]. 
Qed.



(*
# let exp2 x = 2.0 ** x;;

val exp2 : float -> float = <fun>
#   exp2 95.0 *. 97.0 -. 1.0;;
- : float = 3.84256588194182037e+30
# let n = exp2 95.0 ;;
# let p = n *. 97.0 -. 1.0;;
val p : float = 3.84256588194182037e+30
# p *. (log 2.0) /. (log 10.0);;
- : float = 1.15672759077950807e+30
# 

Estimation :
2 ** (3.84 e+30) * 3.84 e+30.

10 ** (1.15 e+30) * 1.15 e+30 

*)
                
(** * Plain large sequences (not necessarily minimal) 

Note : Some names of lemmas and theorem like [Theorem_4_5] or
[Lemma_4_5_2] refer to sections in Ketonen and Solovay's article.

*)

(** ** large sequences (as in KS ) (may contain zeros) *)
Locate eqb.
Definition largeb (alpha : T1) (s: list nat) :=
  match (gnaw alpha s)
          with zero => true | _ => false end.


Definition large (alpha : T1) (s : list nat) : Prop :=
  largeb alpha s.



Definition largeSb (alpha : T1) (s: list nat) :=
  match gnawS alpha s with
    | T1.zero => true
    | _ => false
  end.

Definition largeS (alpha : T1) (s : list nat) : Prop :=
  largeSb alpha s.


Definition Large alpha s := large (@cnf alpha) s.




Lemma large_iff (alpha : T1) (s : list nat) :
  large alpha s <-> gnaw alpha s = 0.
Proof.  
  unfold large, largeb; destruct (gnaw alpha s).
  - split;auto.  
  - split; discriminate.
Qed.


Lemma largeSb_b (alpha : T1) (s: list nat) :
  largeSb alpha s = largeb alpha (shift s). 
Proof.
   induction s;cbn.
  -   unfold largeb, largeSb; now rewrite gnaw_gnawS. 
  - cbn; unfold largeb, largeSb;
    cbn; intros;  now rewrite gnaw_gnawS, shift_unshift.
Qed. 

Lemma largeb_Sb alpha s :
  largeb alpha s = largeSb alpha (unshift s).
Proof.
  unfold largeb, largeSb; now rewrite  gnaw_gnawS.
Qed.


Lemma largeS_iff (alpha : T1) (s : list nat) :
  largeS alpha s <-> gnawS alpha s = T1.zero.
Proof.  
  unfold largeS, largeSb; destruct (gnawS alpha s).
  - split;auto.  
  - split; discriminate.
Qed.

Section Lemma_4_4_Proof.
  Variables alpha beta : T1.
  Hypothesis Halpha : nf alpha.
  Hypothesis Hbeta : nf beta.
  Variable n : nat.
  Variable s : list nat.
  
  Hypothesis Hs : sorted_ge n s.
  Hypothesis H :  const_pathS_eps n alpha beta.
  Hypothesis H0 : largeS alpha s.

  Lemma Lemma4_4 : largeS beta s.
  Proof.
     specialize (@Lemma_4_4_1 s n alpha beta Halpha Hbeta Hs H);  intro H1.
     repeat red in H0; unfold largeSb in H0; destruct (gnawS alpha s).
     -   apply const_pathS_eps_zero in H1;  now rewrite largeS_iff. 
     -  discriminate. 
  Qed.

End Lemma_4_4_Proof.

Lemma Lemma_4_4_2 : (* K-P-6 *)
  forall (s : list nat) (n : nat) (alpha beta : T1),
    nf alpha -> nf beta ->   sorted_ge n s ->
    const_pathS_eps n alpha beta ->  gnawS beta s o<= gnawS alpha s.
Proof.
  intros;  specialize (@Lemma_4_4_1 s n alpha beta H H0 H1 H2).
  intro H4;  eapply const_pathS_eps_LE_2; eauto.                              
  all: eapply gnawS_nf; eauto.
Qed.

    
Lemma Lemma_4_5_1  n alpha:
  nf alpha ->
  forall s t ,
    ptwise_le s t ->
    sorted_ge n s ->
    sorted_ge n t ->
    const_pathS_eps (simple_last n t)
                    (gnawS alpha t) (gnawS alpha s).
Proof. 
  intros Halpha s t H; unfold ptwise_le in H.
  pattern s , t; eapply  Forall2_indR with Peano.le; eauto.
  - intros; cbn; now right.
  -  intros; subst; repeat rewrite gnawS_app.
     replace (simple_last n (l' ++ y :: nil)) with y.
     assert (const_pathS_eps y (gnawS  alpha l') (gnawS alpha l)).
     {
       eapply Cor12_2 with (simple_last n l'); eauto.
       eapply gnawS_nf; auto.
       eapply sorted_cut;eauto. 
       eapply H1.
       all : eapply sorted_ge_prefix; eauto. 
     }
     eapply  Lemma_4_3 with (simple_last n l'); auto.
     eapply gnawS_nf; eauto.
     eapply gnawS_nf; eauto.
     eapply sorted_cut;eauto. 
     eapply H1.
     eapply sorted_ge_prefix; eauto. 
     eapply sorted_ge_prefix; eauto. 
     now rewrite simple_last_app1.
Qed.



Section Proof_of_4_5_2.
  Variables (A B1 B2 : list nat).
  Variable alpha : T1.
  Hypothesis Halpha : nf alpha.
  Hypothesis HA : sorted_ge 0 A.
  Hypothesis HB : sorted_ge 0 (B1 ++ B2).
  Hypothesis HAB1 : ptwise_le B1 A.
  Hypothesis HlargeA : largeS alpha  A .
  
  Remark R1 : gnawS alpha A = T1.zero.
  Proof. now   rewrite <- largeS_iff. Qed.
  
  Remark R2 : gnawS  alpha B1 = T1.zero.
    assert (H: sorted_ge 0 B1) by 
        (eapply sorted_ge_prefix; eauto).
    specialize (Lemma_4_5_1 0 alpha Halpha _ _ HAB1 H HA).  
    rewrite R1.
    intro H0; now rewrite (const_pathS_eps_zero  H0).
  Qed. 
  
  Lemma Lemma_4_5_2: gnawS alpha (B1 ++ B2) = zero.
  Proof. 
    rewrite gnawS_app, R2; now rewrite gnawS_zero.
  Qed. 
  
End Proof_of_4_5_2.


Theorem Theorem_4_5 (alpha: T1)(Halpha : nf alpha)
        (A B : list nat)
        (HA : Sorted Peano.lt A)
        (HB : Sorted Peano.lt B)
        (HAB : incl A B) :
  largeS alpha A -> largeS alpha B.
Proof.
  intro H; destruct (incl_decomp A B HA HB HAB) as [C [D [H1 H2]]];auto.
  subst B; rewrite largeS_iff in *; eapply Lemma_4_5_2 with A;auto.
  rewrite  sorted_ge_iff;  split;auto.
  clear HA H H2 HB HAB; induction A; constructor;auto with arith.
  rewrite  sorted_ge_iff; split; auto.
  generalize (C++D); intro E; induction E; constructor;auto with arith.
  now rewrite largeS_iff in *.
Qed.


Lemma gnaw_last_step alpha s i :
  gnaw alpha s = 1 -> gnaw alpha (s ++ S i :: nil) = 0.
Proof.
  intro H; now rewrite gnaw_app, H.
Qed.



(**  For alpha in class E0 *)


Definition LargeS (alpha : E0) s := largeS (@cnf alpha) s.

Definition Gnaw alpha s := gnaw (@cnf alpha) s.
Definition GnawS alpha s := gnawS (@cnf alpha) s.

Lemma Gnaw_GnawS s alpha :
  GnawS alpha s = Gnaw alpha (shift s).
Proof.
  unfold Gnaw, GnawS; apply gnawS_gnaw.
Qed.

Lemma GnawS_Gnaw (s:list nat) :
  forall alpha,  Gnaw alpha s = GnawS alpha (unshift s).
Proof.
  unfold Gnaw, GnawS.  intros; apply gnaw_gnawS.
Qed.

Lemma GnawS_omega : forall i s, GnawS omega%e0 (i::s)  = GnawS (FinS i) s.
Proof.
  intros; cbn; now unfold GnawS.
Qed.


Lemma Gnaw_omega i s : Gnaw  omega%e0 (S i::s) = Gnaw (FinS i) s.
Proof.
 reflexivity.
Qed.

Definition Largeb (alpha: E0) (s: list nat) :=
  largeb (@cnf alpha) s.

Definition LargeSb (alpha: E0) (s: list nat) :=
  largeSb (@cnf alpha) s.

Lemma LargeSb_b (alpha : E0) (s: list nat) :
  LargeSb alpha s = Largeb alpha (List.map S s). 
Proof.
   unfold LargeSb, Largeb; apply largeSb_b.
Qed.

Lemma Largeb_Sb alpha s :
  Largeb alpha s = LargeSb alpha (unshift s).
Proof.
  unfold Largeb, LargeSb; apply largeb_Sb.
Qed.







Lemma largeb_finite :
  forall n i, largeb (S n) (iota_from (S i) (S n)) = true.
Proof.
  intros; unfold largeb; now rewrite  gnaw_finite. 
Qed.

Lemma largeb_n (n:nat): forall s,   ~ In 0 s -> 
                                    large n s  ->
                                    (n <= List.length s)%nat.
Proof.   
  induction n.
  -  intros; cbn; auto with arith. 
  -  destruct s; cbn.
     +   discriminate. 
     +  destruct n0.
       * destruct 1; now left.   
        * unfold largeb. intro; cbn. 
        destruct n.
          -- replace (gnaw zero s) with zero.      
             ++ auto with arith.
             ++  now rewrite gnaw_zero.
          -- intros;  apply le_n_S, IHn.
             ++   intro;destruct H;auto.
             ++ auto. 
Qed. 


Lemma largeb_n_R : forall s n,  ~ In 0 s ->
                                (n < List.length s)%nat ->
                                largeb (S n) s  = true.
Proof.   
  intros; unfold largeb. rewrite gnaw_n_R; auto.
Qed.

Lemma large_n_iff : forall s (n:nat) , ~ In 0 s  ->
                                large n s  <-> (n <= List.length s)%nat.
Proof.
  split.
  -   now apply largeb_n.
  -  destruct n.
     + unfold large, largeb; cbn; now rewrite gnaw_zero.
     + unfold large; now apply largeb_n_R.
 Qed. 


Example ex3 : ~ large 156 (interval 100 254).
Proof.
  rewrite large_n_iff.
  - compute; lia.
  - apply sorted_ge_not_In, interval_sorted_ge; auto with arith.
Qed.


(** Gnawing omega *)
(** omega-large intervals *)

Lemma gnaw_omega_n_SSn :
  forall n, gnaw omega (iota_from (S n) (S (S n))) = zero.
Proof. 
  intro n;  destruct n.  
  -  reflexivity. 
  -  apply gnaw_finite.
Qed.


Lemma gnaw_omega_1 (n:nat) :
  gnaw omega (interval (S n) (S n + n)%nat) = 1.
Proof.
  unfold interval.
  replace (S (S n + n) - S n)%nat with (S n).
     destruct n.  
  -  reflexivity. 
  -  apply gnaw_finite_1_iota.
  - simpl; destruct n.
    + reflexivity.
    + lia.
Qed.


Example omega_ex1 : gnaw omega (interval 7 13) = 1.
reflexivity.
Qed.

Example omega_ex2 : gnaw omega (interval  1000 1999) = 1.
change 1999 with (1000 + 999)%nat; apply gnaw_omega_1.
Qed.


Lemma large_omega_1 : forall s n,  ~ In 0 (n::s) -> 
                                     gnaw omega (n::s) = 0 ->
                                     (n <= List.length s)%nat.
Proof. 
  intros s n; destruct n.
  - auto with arith. 
  - intros H H0; 
    cbn in H0.
    generalize (largeb_n (S n) s).  
    intros.
    apply H1;auto.
    intro; destruct H; now right.
    unfold largeb. rewrite FS_rw in H0. 
    red. red. unfold largeb.   rewrite H0. auto.
Qed. 


Lemma large_omega_2 : forall s n,   ~In 0 (n::s) -> 
                                    (n <=  List.length s)%nat ->
                                    gnaw omega (n::s)  = zero.
Proof. 
  intros;  cbn;  destruct n.
  destruct H; now left.
  apply gnaw_n_R; auto.
  intro; destruct H; now right.
Qed.

Lemma large_omega_iff : forall s n,  ~ In 0 (n::s) ->
                                     large omega (n::s) <->
                                     (n <= List.length s)%nat.
                                     
Proof.
 intros s n H; split; rewrite large_iff; intro H0.
 - now apply large_omega_1.
 - now apply large_omega_2.  
Qed.




