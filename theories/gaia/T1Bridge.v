(**  * Bridge between Hydra-battle's and Gaia's [T1]  (Experimental) 

This library introduces tools for making  definitions and lemmas from
 #<a href="../ordinals/"> Hydra battles's ordinals</a>#  compatible with 
 #<a href="https://github.com/coq-community/gaia/tree/master/theories/schutte">Gaia's ssete9 library</a>#.
 *)

(* begin snippet Requirements:: no-out  *)
From mathcomp Require Import all_ssreflect zify.
From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder ON_Generic  T1 E0.
From gaia Require Export ssete9.
(* end snippet Requirements *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
The name [T1] denotes Gaia's data type. We use [T1.T1] or [hT1] for Hydra battles ordinal terms.
*)

(* begin snippet hT1gT1 *)
#[global] Notation hT1 := T1.T1.
#[global] Notation T1 := ssete9.CantorOrdinal.T1.
(* end snippet hT1gT1 *)

(** We rename Hydra battle's total order on [hT1] *)

(* begin snippet MoreNotations:: no-out *)

(** Restrictions to terms in normal form *)

#[global] Notation LT := (restrict T1nf T1lt).
#[global] Notation LE := (restrict T1nf T1le).

(* end snippet MoreNotations *)

(** Translation functions *)

(* begin snippet h2gG2hDef *)
Fixpoint h2g (a : hT1) : T1 :=
  if a is T1.cons a n b then cons (h2g a) n (h2g b) else zero.

Fixpoint g2h (a : T1) : hT1 :=
  if a is cons a n b then T1.cons (g2h a) n (g2h b) else T1.zero.
(* end snippet h2gG2hDef *)


(* begin snippet h2gG2hRw:: no-out *)
Lemma h2g_g2hK : cancel g2h h2g.
Proof. elim => // => a1 IH1 n t2 IH2 /=; by rewrite IH1 IH2. Qed.
(* end snippet h2gG2hRw *)


(* begin snippet g2hH2gRw:: no-out *)
Lemma g2h_h2gK : cancel h2g g2h.
(* ... *)
(* end snippet g2hH2gRw *)
Proof.
   elim => // => a1 IH1 n t2 IH2 /=; by rewrite IH1 IH2. 
Qed.

(* begin snippet g2hEqIff:: no-out *)
Lemma g2h_eqE (a b: T1): g2h a = g2h b <-> a = b.
(* end snippet g2hEqIff *)
Proof. 
    split; [| by move => ->].
    rewrite -(h2g_g2hK a) -(h2g_g2hK b) !g2h_h2gK => -> //.
Qed.

(* begin snippet h2gEqIff:: no-out *)
Lemma h2g_eqE (a b :hT1): h2g a = h2g b <-> a = b.
(* end snippet h2gEqIff *)
Proof. 
  split; [| by move => ->].
  rewrite  -(g2h_h2gK a) -(g2h_h2gK b) !h2g_g2hK  => ->  //.
Qed.

Lemma g2h_diffE (a b : T1) : g2h a <> g2h b <-> a <> b.
Proof.
  split => H Heq; [subst; by apply: H | by apply  H , g2h_eqE].
Qed.

Lemma h2g_diffE (a b : hT1) : h2g a <> h2g b <-> a <> b.
Proof.
  split => H Heq; [subst; by apply: H | by apply  H, h2g_eqE].
Qed. 

(** Pretty printing *)
(* begin snippet T1ppDef *)
Definition T1pp (a:T1) : ppT1 := pp (g2h a).
(* end snippet T1ppDef *)


(** * refinement of constants, functions, etc. *)

(* begin snippet refineDefs *)

Definition refines0 (x:hT1)(y:T1) :=  y = h2g x.

Definition refines1 (f:hT1 -> hT1) (f': T1 -> T1) :=
  forall x: hT1, f' (h2g x) = h2g (f x).

Definition refines2 (f:hT1 -> hT1 -> hT1) (f': T1 -> T1 -> T1 ) :=
  forall x y : hT1, f' (h2g x) (h2g y) = h2g (f x y).

Definition refinesPred (hP: hT1 -> Prop) (gP: T1 -> Prop) :=
  forall x : hT1, hP x <-> gP (h2g x).

Definition refinesRel (hR: hT1 -> hT1 -> Prop)
  (gR: T1 -> T1 -> Prop) :=
  forall x y : hT1, hR x y <-> gR (h2g x) (h2g y).

(* end snippet refineDefs *)

(* begin snippet refines1R:: no-out *)
Lemma refines1_R f f' :
  refines1 f f' <-> forall y: T1, f (g2h y) = g2h (f' y).
(* end snippet refines1R *)
Proof.
  split => [Href y | H x]. 
  - by rewrite -{2}(h2g_g2hK y) Href g2h_h2gK. 
  - by rewrite -{2}(g2h_h2gK x) ?H ?h2g_g2hK.
Qed.

(* begin snippet refines2R:: no-out *)
Lemma refines2_R f f' :
  refines2 f f' <-> forall y z: T1, f (g2h y) (g2h z) = g2h (f' y z).
(* end snippet refines2R *)
Proof.
  split => [Href y z | H x y]. 
  by rewrite -{2}(h2g_g2hK y) -{2}(h2g_g2hK z) ?Href ?g2h_h2gK. 
  by rewrite -{2}(g2h_h2gK x)  -{2}(g2h_h2gK y) H h2g_g2hK. 
Qed.

(** ** Refinements of usual constants *)

(* begin snippet constantRefs:: no-out *)

Lemma zero_ref : refines0 T1.zero zero.
Proof. done. Qed.

Lemma one_ref : refines0 T1.one one.
Proof. done. Qed.

Lemma Finite_ref (n:nat) : refines0 (T1.T1nat n) (\F n).
Proof. by case: n. Qed.

Lemma omega_ref : refines0 T1.T1omega T1omega.
Proof. done. Qed.
(* end snippet constantRefs *)

(** ** unary functions and predicates  *)

(* begin snippet unaryRefs:: no-out *)
Lemma succ_ref: refines1 T1.succ T1succ.
(*| .. coq:: none |*)
Proof.
  elim => [// |//  x] => //;  by case: x => // ? ? ? ? ? ? /= -> .
Qed.
(*||*)
Lemma phi0_ref x: refines0 (T1.phi0 x) (phi0 (h2g x)). (* .no-out *)
(*| .. coq:: none |*)
Proof. done. Qed.
(* end snippet unaryRefs *)

Lemma g2h_phi0 a : g2h (phi0 a) = T1.phi0 (g2h a). 
Proof. by rewrite /phi0. Qed.

Lemma ap_ref : refinesPred Epsilon0.T1.ap T1ap. 
Proof.
  move => a; split => Hap; first by case: Hap.
  move: Hap; case: a => //= a n b /andP [Hn Hz].
  move/eqP: Hn Hz =>->; move/eqP; by case: b.
Qed.

(** ** Equality and comparison *)

Lemma T1eq_refl (a: T1) : T1eq a a.
Proof. by apply /T1eqP. Qed.

Lemma T1eqE a b: T1eq a b -> g2h a = g2h b.
Proof. by move => /T1eqP ->. Qed. 

Lemma T1eq_h2g (a b : hT1) : T1eq (h2g a) (h2g b) -> a = b.
Proof.  move => /T1eqE; by rewrite !g2h_h2gK. Qed.

(* begin snippet compareRef:: no-out *)
Lemma compare_ref (x y: hT1) :
  match T1.compare_T1 x y with
  | Datatypes.Lt => T1lt (h2g x) (h2g y)
  | Datatypes.Eq => h2g x = h2g y
  | Datatypes.Gt => T1lt (h2g y) (h2g x)
  end.
(* end snippet compareRef *)
Proof.
  move: y; elim: x => [|x1 IHx1 n x2 IHx2]; case => //= y1 n0 y2.
  case H: (Epsilon0.T1.compare_T1 x1 y1).
  - move: (IHx1 y1); rewrite H => {}IHx1. 
    case H0: (PeanoNat.Nat.compare n n0).
    + have ->: (n = n0) by apply: Compare_dec.nat_compare_eq.
      case H1: (Epsilon0.T1.compare_T1 x2 y2).
      * rewrite IHx1; congr cons.
        move: (IHx2 y2); rewrite H1 => {}IHx2.
        case (h2g x1 < h2g y1); [trivial|]; by []. 
        rewrite IHx1 eqxx /= eqxx ltnn.
        move: (IHx2 y2); rewrite H1 => {}IHx2; by rewrite T1ltnn.
        rewrite -IHx1 T1ltnn eqxx  ltnn  eqxx.
        move: (IHx2 y2);  by rewrite H1.  
    + rewrite IHx1 T1ltnn eqxx.
      have {}H0 : (n < n0)%coq_nat by
        apply: Compare_dec.nat_compare_Lt_lt.  
      by move/ltP: H0 =>->.
    + rewrite IHx1 T1ltnn eqxx.
      apply Compare_dec.nat_compare_Gt_gt in H0.
      by move/ltP: H0 => ->.
  all:  move: (IHx1 y1); by rewrite H => ->. 
Qed.

(* begin snippet decideHLtRw:: no-out *)
Lemma decide_hltE (a b : hT1):
  bool_decide (T1.lt a b) = (h2g a < h2g b).
(* end snippet decideHLtRw *)
Proof.
  rewrite /Epsilon0.T1.lt; generalize (compare_ref a b);
    rewrite /Comparable.compare /=.
  destruct (decide (Epsilon0.T1.compare_T1 a b = Datatypes.Lt)).
  - have bd := e ; apply (bool_decide_eq_true _) in bd.
    by rewrite bd e.
  - have bd := n; apply (bool_decide_eq_false _) in bd.
    rewrite bd.
    destruct (Epsilon0.T1.compare_T1 a b) => //.
    * by move => ->; rewrite T1ltnn.
    * move => Hlt; symmetry;  apply/negP => Hlt'.
      have H1 : (h2g b < h2g b) by apply T1lt_trans with (h2g a).
      move: H1; by rewrite T1ltnn.
Qed.

(* begin snippet ltRef:: no-out *)
Lemma lt_ref : refinesRel T1.lt T1lt.
(* end snippet ltRef *)
Proof.
  move=> a b; split.
  - rewrite /Epsilon0.T1.lt /Comparable.compare; move => Hab. 
    generalize (compare_ref a b); now rewrite Hab.
  - move => Hab; rewrite /T1.lt.  
    case_eq (Epsilon0.T1.compare_T1 a b) => [Heq |//| Hgt].
    +  generalize (compare_ref a b); rewrite Heq.
       move => H0; move: Hab; rewrite H0; by rewrite T1ltnn.
    +  generalize (compare_ref a b); rewrite Hgt.
       move =>  H1; have H2: (h2g a < h2g a).
       * eapply T1lt_trans; eauto.
       *  move :H2; by rewrite T1ltnn. 
Qed.

(* begin snippet leRef:: no-out *)
Lemma le_ref : refinesRel T1.le T1le.
(* end snippet leRef *)
Proof.
  move=> a b; split.
  - rewrite /T1le /Comparable.compare => Hab;  elim: Hab. 
    + move => y Hy; have H: (h2g a < h2g y) by apply lt_ref. 
      * by rewrite H orbT.
      * by rewrite eq_refl. 
  - rewrite T1le_eqVlt; move => /orP; destruct 1; last first. 
    + left; by rewrite lt_ref. 
    +  move: H => /eqP; by rewrite h2g_eqE => ->; right. 
Qed. 

(** ** Ordinal addition *)

(* begin snippet plusRef:: no-out *)
Lemma plus_ref : refines2 T1.T1add T1add.
(* end snippet plusRef *)
Proof.
  move => x; elim: x => [|x1 IHx1 n x2 IHx2]; case => //= y1 n0 y2.
  case Hx1y1: (Epsilon0.T1.compare_T1 x1 y1); move: (compare_ref x1 y1);
    rewrite Hx1y1 => H.
  - rewrite /Comparable.compare H T1ltnn /=.
    by rewrite Hx1y1 -H /=.
  - by rewrite /Comparable.compare H Hx1y1.
  - replace (h2g x1 < h2g y1) with false; last first.
    + by apply T1lt_anti in H.
    + rewrite /Comparable.compare H /= Hx1y1.
      change (cons (h2g y1) n0 (h2g y2))
        with (h2g (T1.cons y1 n0 y2)); 
        by rewrite IHx2.
Qed.

(** ** Ordinal multiplication *)

Section Proof_of_mult_ref.

  Lemma T1mul_a0E (c : T1) : c * zero = zero. 
  Proof. done. Qed.

  Lemma T1mul_cons_cons_E n b n' b' :
    cons zero n b * cons zero n' b' =
      cons zero (n * n' + n + n') b'.      
  Proof. done.  Qed. 

 
  Lemma T1mulE4 a n b n' b' :
    a != zero -> (cons a n b) * (cons zero n' b') =
                   cons a (n * n' + n + n') b.
  Proof. 
    move => /T1eqP; cbn =>  Ha'.
    have Heq: T1eq a zero = false by  case: a Ha' => // /=.
    by rewrite Heq.
  Qed.

  Lemma multE4 a n b n' b' :
    a <> Epsilon0.T1.zero ->
    Epsilon0.T1.T1mul (T1.cons a n b)
      (T1.cons Epsilon0.T1.zero n' b') =
      T1.cons a (n * n' + n + n') b.
  Proof. 
    cbn; case: a => [// | a n0 ? _ ]; congr T1.cons; nia. 
  Qed.

  Lemma T1mulE5 a n b a' n' b' :
    a' != zero ->
    (cons a n b) * (cons a' n' b') =
      cons (a + a') n' (T1mul (cons a n b) b').
  Proof. 
    move => H /=;  cbn;  have Ha' : T1eq a' zero = false
              by ( move: a' H; case => //). 
    case (T1eq a zero); cbn; by rewrite Ha'. 
  Qed.

  Lemma multE5 a n b a' n' b' :
    a' <>  T1.zero ->
    Epsilon0.T1.T1mul (T1.cons a n b)  (T1.cons a' n' b') =
      T1.cons (T1.T1add a  a') n' (T1.T1mul (T1.cons a n b) b').
  Proof.
    move => Ha'; cbn; case: a; move: Ha'; case: a' => //.
  Qed.

  Lemma h2g_cons a n b : h2g (T1.cons a n b)= cons (h2g a) n (h2g b). 
  Proof. done. Qed.

  Lemma g2h_cons a n b : g2h (cons a n b) = T1.cons (g2h a) n (g2h b).
  Proof. done. Qed.
  
  Lemma h2g_zero  : h2g T1.zero = zero. 
  Proof. done. Qed.

  Lemma g2h_zero : g2h zero = T1.zero.
    Proof. done. Qed. 

  Lemma mult_ref0 : refines2 T1.T1mul T1mul.
  Proof.
    move => x y;  move: x; induction y. 
    -  move => x; simpl h2g; rewrite T1mul_a0E; case x => //; by case.
    -  case.
       + simpl h2g => // /=.
       + move => a n0 b.
         destruct (Epsilon0.T1.T1_eq_dec  a Epsilon0.T1.zero).
         *  subst;
              destruct (Epsilon0.T1.T1_eq_dec y1 Epsilon0.T1.zero).
            -- subst y1; simpl h2g;
                 rewrite T1mul_cons_cons_E; congr cons; nia.
            -- repeat rewrite !h2g_cons !h2g_zero.
               rewrite T1mulE5.
               ++ rewrite multE5 => //.
                  ** simpl h2g; simpl T1add; congr cons.
                     destruct
                       (Epsilon0.T1.T1_eq_dec y2 Epsilon0.T1.zero).
                     { subst; by cbn. }
                     { change (cons zero n0 (h2g b)) with
                         (h2g (T1.cons Epsilon0.T1.zero n0 b));
                         now rewrite IHy2.
                     }
               ++  destruct y1; [now destruct n1| now compute].
         * destruct (Epsilon0.T1.T1_eq_dec y1 Epsilon0.T1.zero).
           --   subst; rewrite !h2g_cons !h2g_zero;
                  rewrite T1mulE4.
                ++ by rewrite multE4. 
                ++ by case :a n1 . 
           --   rewrite !h2g_cons. 
                ++ rewrite T1mulE5.
                   ** rewrite  multE5 => //. 
                      simpl h2g; rewrite plus_ref; congr cons.
                      change (cons (h2g a) n0 (h2g b))
                        with (h2g (T1.cons a n0 b));
                        now rewrite IHy2.
                   **  case: y1 n2 IHy1 => //.
  Qed.

End Proof_of_mult_ref.

(* begin snippet multRef:: no-out *)
Lemma mult_ref : refines2 T1.T1mul T1mul.
(* end snippet multRef *)
Proof mult_ref0.
(* begin snippet multA:: no-out *)

Lemma g2h_multE (a b : T1) : g2h (a * b) = T1.T1mul (g2h a) (g2h b).
Proof. apply symmetry, refines2_R,  mult_ref. Qed.

(* end snippet multA *)

Lemma g2h_plusE (a b: T1) : g2h (a + b) = T1.T1add (g2h a) (g2h b).
Proof. apply symmetry, refines2_R, plus_ref. Qed.
       
(** * Ordinal terms in normal form *)


(* begin snippet nfRef:: no-out *)

Lemma nf_ref (a: hT1)  : T1.nf_b a = T1nf (h2g a).
(* end snippet nfRef *)
Proof.
  elim: a => //.
  - move => a IHa n b IHb; rewrite T1.nf_b_cons_eq; simpl T1nf. 
    by rewrite IHa IHb [phi0 (h2g a)]/(h2g (T1.phi0 a))
         andbA decide_hltE.
Qed.

Lemma LT_ref : refinesRel  T1.LT  LT.
Proof.
  split.   
  - destruct 1 as [H [H0 H1]]; split. 
    +  by rewrite  -nf_ref.
    + by apply lt_ref. 
    + by rewrite -nf_ref. 
  -  case => H H0 H1; repeat  split;
             red; rewrite ?nf_ref ?lt_ref => // ;
                                               by apply lt_ref. 
Qed. 

Lemma LE_ref : refinesRel T1.LE LE.
Proof. 
  split. 
  - case => a b; split. 
    + rewrite -nf_ref => //.
    + case: b => c _; case :c => [y0 Hy0 |].
      apply T1ltW. 
      * rewrite - decide_hltE => //.
        red;  rewrite bool_decide_eq_true => //.
      *  apply T1lenn. 
    +  case b => _ ?; rewrite - nf_ref => //. 
  - case; rewrite /T1.LE; repeat split => //.
   +  move: p p1; rewrite -nf_ref => //.
   +  move: p0; rewrite T1le_eqVlt => /orP.
      case => /eqP Heq; subst.
      * move: Heq; rewrite h2g_eqE => ?; subst; right.
      * left; move: Heq; rewrite -decide_hltE => // Heq.
           move: Heq => /eqP; rewrite bool_decide_eq_true => //. 
   + move: p1 ; rewrite -nf_ref => //.
Qed.


(** Limits, successors, etc *)

(* begin snippet limitbRef:: no-out *)
Lemma T1limit_ref (a:Epsilon0.T1.T1) : T1.T1limit a = T1limit (h2g a).
(* end snippet limitbRef *)
Proof.
  elim: a => /= //.
  move => a IHa n b IHb; cbn; rewrite IHb. 
  move: IHa; case:a => //.
  move => a n0 b0 IH;  cbn; move: IHb; case: b => //.
Qed.

(* begin snippet isSuccRef:: no-out *)
Lemma T1is_succ_ref (a:Epsilon0.T1.T1): T1.T1is_succ a = T1is_succ (h2g a).
(* end snippet isSuccRef *)
Proof. 
  elim: a => /= //.
  move => a IHa n b /= -> ; case: a IHa => //. 
Qed.


(* rewriting lemmas *)

(* begin snippet rewritingRules:: no-out *) 
Lemma hnf_g2h a : T1.nf (g2h a) = T1nf a.
Proof.  by rewrite /T1.nf (nf_ref (g2h a)) h2g_g2hK. Qed. 

Lemma g2h_succ a : g2h (T1succ a) = T1.succ (g2h a).
Proof. by rewrite -(h2g_g2hK a) succ_ref !g2h_h2gK. Qed.

Lemma hlt_iff a b: T1.lt a b <-> h2g a < h2g b.
Proof. by rewrite lt_ref. Qed.

(* end snippet rewritingRules *)

(* begin snippet T1ltIff:: no-out *)
Lemma T1lt_iff a b: T1nf a -> T1nf b ->
                          a < b <->  g2h a t1<  g2h b. 
(* end snippet T1ltIff *)
Proof. 
  move => Ha Hb; split. 
  - rewrite -(h2g_g2hK a) -(h2g_g2hK b);  repeat split.
    1, 3:  by rewrite g2h_h2gK hnf_g2h. 
    + by rewrite !h2g_g2hK hlt_iff.
  -  destruct 1 as [H0 [H1 H2]].
     by rewrite -(h2g_g2hK a) -(h2g_g2hK b) -hlt_iff. 
Qed.


(* begin snippet T1leIff:: no-out *)
Lemma T1le_iff (a b: T1):
  a <= b <->  T1.le (g2h a) (g2h b).
(* end snippet T1leIff *)
Proof.
  split. 
  -  rewrite T1le_eqVlt => /orP; case.
     move =>  /eqP Heq; subst; right.
     move => Hlt; left; by rewrite hlt_iff !h2g_g2hK.  
  -  rewrite le_ref; by rewrite !h2g_g2hK.  
Qed.

(** *  Well formed ordinals as a data type  *)
#[global] Notation hE0 := E0.E0.
#[global] Notation hcnf := E0.cnf.
#[global] Notation hE0lt := E0.E0lt.
#[global] Notation hE0le := E0.E0le.
#[global] Notation hE0zero := E0.E0zero.
#[global] Notation hE0omega := E0.E0omega.
#[global] Notation hE0phi0 := E0.E0phi0.
#[global] Notation hE0fin := E0.E0fin.
#[global] Notation hE0limit := E0.E0limit.
#[global] Notation hE0is_succ := E0.E0is_succ.

(* begin snippet E0Def:: no-out *)
Record E0 := mkE0 { cnf : T1 ; _ : T1nf cnf == true}.
Coercion cnf: E0 >-> T1.
(* end snippet E0Def *)

Canonical e0Sub := [subType for cnf].

Check fun (x:E0) => val x. 


Remark omeganf : T1nf T1omega == true. 
  by reflexivity. Qed.

Check (Sub T1omega). 

Check (Sub T1omega omeganf : e0Sub).


Check (Sub T1omega omeganf : E0).








Definition E0eqb (a b: E0):= cnf a == cnf b.

Lemma gE0_eq_intro a b : cnf a = cnf b -> a = b. 
Proof.
  destruct a, b; cbn. 
  move => H; subst => //; congr mkE0; apply eq_proofs_unicity_on;
                      decide equality. 
Qed.

(* begin snippet E0EqMixin:: no-out  *)
Definition E0_eq_mixin :  Equality.mixin_of E0.
(* end snippet E0EqMixin *)
Proof. 
  exists E0eqb; move  => [x Hx] [y Hy] => /=. 
  case E: (T1eq x y); cbn; rewrite E. 
  - left; apply: gE0_eq_intro; by apply /eqP. 
  - right => H; injection H => /eqP; by rewrite /eq_op /= E. 
Defined. 

(* begin snippet E0Eqtype *)
Definition E0_eqtype :=  Equality.Pack E0_eq_mixin.
Canonical Structure E0_eqtype. 
(* end snippet E0Eqtype *)

(* begin snippet E0Defb:: no-out *)

Definition ppE0 (a: E0) := T1pp (cnf a).

Definition E0lt (a b: E0) := cnf a < cnf b.
Definition E0le  (a b: E0) := cnf a <= cnf b.

#[global, program] Definition E0zero: E0 := @mkE0 zero _. 

#[global, program]
 Definition E0succ (a: E0): E0 :=  @mkE0 (T1succ (cnf a)) _.
Next Obligation.
  rewrite nf_succ => //; case: a => ? i //=; by apply /eqP. 
Defined.


#[global, program]
 Definition E0pred (a:E0) : E0:=  @mkE0 (T1pred (cnf a)) _.
Next Obligation. 
  case: a => ? ?; rewrite nf_pred  => //= ; by apply /eqP.
Defined. 


Fixpoint E0fin (n:nat) : E0 :=
  if n is p.+1 then E0succ (E0fin p) else E0zero. 

#[program] Definition E0omega: E0 := @mkE0 T1omega _. 

#[program]  Definition E0phi0 (a: E0) : E0 := @mkE0 (phi0 (cnf a)) _.
(* end snippet E0Defb *)
Next Obligation. 
  case : a => ? ?; apply /eqP => //=. 
  rewrite Bool.andb_true_r; by apply /eqP.  
Defined.


(* begin snippet E0plusMultDef:: no-out *)
#[program] Definition E0plus (a beta: E0) : E0 :=
  @mkE0 (T1add (cnf a) (cnf beta)) _.
Next Obligation. 
  rewrite nf_add => //.
  case :a; cbn => t Ht; apply /eqP => //.
  case :beta; cbn => t Ht; apply /eqP => //.
Defined.

#[program] Definition E0mul (a beta: E0) : E0 :=
  @mkE0 (T1mul (cnf a) (cnf beta)) _.
  (* ... *)
  (* end snippet E0plusMultDef *)  
Next Obligation.
  rewrite nf_mul => //.
  case :a; cbn => t Ht; apply /eqP => //.
  case :beta; cbn => t Ht; apply /eqP => //.
Defined.


Lemma E0fin_cnf (n:nat) : cnf (E0fin n) = \F n.
Proof. elim: n => // n /= ->; by rewrite T1succ_nat. Qed.

(* begin snippet gE0h2gG2h:: no-out *)
#[program] Definition E0_h2g (a: hE0): E0:= @mkE0 (h2g (E0.cnf a)) _. 
Next Obligation.
  rewrite -nf_ref; case: a => /= cnf cnf_ok; by rewrite cnf_ok.
Defined.


#[program] Definition E0_g2h (a: E0): hE0 := @E0.mkord (g2h (cnf a)) _.  
Next Obligation.
  case: a  => /= cnf0 /eqP; by rewrite hnf_g2h.    
Defined.

(* end snippet gE0h2gG2h *)

Definition E0limit a := hE0limit (E0_g2h a).

Definition E0is_succ a := hE0is_succ (E0_g2h a).


Lemma E0_h2g_nf (a:hE0) : T1nf (cnf (E0_h2g a)).
Proof.
  case: a => /= cnf Hnf; by rewrite -nf_ref. 
Qed.


Lemma gE0lt_iff a beta : E0lt a beta <-> E0_g2h a o< E0_g2h beta.
Proof. 
  split. 
    - rewrite /E0lt;  destruct a, beta. 
     rewrite /Lt /T1.LT => /=; repeat split. 
      + rewrite /T1.nf nf_ref h2g_g2hK; by apply /eqP.
      + by rewrite hlt_iff !h2g_g2hK.
      + rewrite /T1.nf nf_ref h2g_g2hK;  by apply /eqP.
    - rewrite /E0lt; destruct a, beta. 
      rewrite /Lt /T1.LT; destruct 1 as [H [H0 H1]].
      move: H0 ; by rewrite hlt_iff !h2g_g2hK. 
Qed.


Lemma gE0le_iff a beta : E0le a beta <-> E0_g2h a o<= E0_g2h beta.
Proof. 
  split. 
  - rewrite /E0le;  destruct a, beta. 
    rewrite /hE0le /T1.LE => /=; repeat split.
    rewrite T1le_eqVlt => Hle.
    have Hor : (cnf0 =cnf1 \/ cnf0 < cnf1).
    { apply Bool.orb_prop in Hle;  destruct Hle as [? | ?].
      left;  apply /eqP => //.
      right => //. 
    }
    destruct Hor as [? | Hneq].
    * subst; replace i0 with i. 
      -- right. 
      -- apply eq_proofs_unicity_on;  decide equality.
    * left; apply gE0lt_iff; rewrite /E0lt => //.
  - rewrite /E0le; destruct a, beta; cbn => Hle. 
    destruct (le_lt_eq_dec Hle) as [l | e].
    + move: l; rewrite /hE0lt ; cbn;  rewrite -T1lt_iff.
     * by apply T1ltW.
     * by apply /eqP. 
     * by apply /eqP. 
    + injection e; rewrite g2h_eqE =>  Heq; subst; apply T1lenn. 
Qed.


Lemma E0_h2g_g2hK : cancel E0_g2h E0_h2g.
Proof.
  case => a Ha /=; rewrite /E0_g2h /E0_h2g.
  apply  gE0_eq_intro=> /=;  by rewrite h2g_g2hK.
Qed.

Lemma E0_g2h_h2gK : cancel E0_h2g E0_g2h.
Proof.
  case => a Ha /=. rewrite /E0_g2h /E0_h2g; f_equal.
  apply  E0_eq_intro=> /=;  by rewrite g2h_h2gK. 
Qed.

Lemma g2h_E0succ a : E0_g2h (E0succ a)= E0.E0succ (E0_g2h a). 
Proof.
  rewrite /E0succ; apply E0_eq_intro => /=; by rewrite g2h_succ. 
Qed.

Lemma  E0is_succ_succ a : E0is_succ  (E0succ a).
Proof.
 rewrite /E0is_succ g2h_E0succ; apply Succ_Succb. 
Qed. 

(* To do : clean up ! *)

Lemma E0is_succE a: E0is_succ a -> {beta: E0 | a = E0succ beta}.
Proof. 
 rewrite /E0is_succ => H. 
 case (Succb_Succ _ H) => beta Hbeta; exists (E0_h2g beta).
 rewrite -(E0_h2g_g2hK a) Hbeta.
 have H0:= g2h_E0succ (E0_h2g beta).
 move: H0; rewrite E0_g2h_h2gK.
 move => H0;  rewrite -H0. 
by rewrite E0_h2g_g2hK.
Qed.

Lemma E0_eqE (x y: E0) : x = y <-> (E0_g2h x = E0_g2h y). 
  split.
   move => Heq; by subst.   
   move => H; by rewrite -(E0_h2g_g2hK x) -(E0_h2g_g2hK y) H. 
Qed. 

Lemma E0_diffE (x y: E0) : x <> y <-> (E0_g2h x <> E0_g2h y).
Proof. 
 split => Hdiff Heq.
  - apply: Hdiff; by apply /E0_eqE. 
  - subst; by apply: Hdiff. 
Qed.

(* clean up!  *)

Lemma E0pred_succK x : E0pred (E0succ x) = x. 
Proof.
  apply E0_eqE; rewrite /E0pred. 
  apply E0_eq_intro => //=.
  rewrite pred_succ => //.
  case: x => c Hc //=.  by apply /eqP.
Qed. 


Lemma g2h_E0zero : E0_g2h E0zero = E0.E0zero.
Proof.  rewrite /E0zero; by apply E0_eq_intro. Qed.

Lemma E0g2h_Fin i: E0_g2h (E0fin i) = E0.E0fin i.
Proof.  apply E0_eq_intro => /=; rewrite E0fin_cnf; by case: i. Qed.


Lemma E0g2h_phi0 a : E0_g2h (E0phi0 a) = E0.E0phi0 (E0_g2h a).
Proof.  apply E0_eq_intro => //. Qed.

Lemma E0g2h_mulE (a b: E0): E0_g2h (E0mul a b) = E0.E0mul (E0_g2h a) (E0_g2h b).
Proof. 
  destruct a, b; apply E0_eq_intro => /=;  by rewrite g2h_multE. 
Qed.

Lemma E0g2h_plusE (a b: E0): E0_g2h (E0plus a b)= E0.E0add (E0_g2h a) (E0_g2h b).
Proof. 
  case: a ; case: b => a ? b ?;  apply E0_eq_intro => /=;
         by rewrite g2h_plusE. 
Qed.

Lemma E0g2h_omegaE : E0_g2h E0omega = hE0omega. 
 Proof.  by  apply E0_eq_intro => /=.  Qed. 

From Coq Require Import Relations Basics
     Wellfounded.Inverse_Image Wellfounded.Inclusion.

(** TODO: simplify this proof !!! *)

(* begin snippet gE0LtWf:: no-out *)
Lemma gE0lt_wf : well_founded E0lt.
Proof.
  move => ?; apply Acc_incl with (fun x y =>  hE0lt (E0_g2h x) (E0_g2h y)).
  (* ... *)
  (* end snippet gE0LtWf *)
  - move => a b ; rewrite /E0lt => Hab. 
    case: a Hab => cnf0 i0 Hb.
    case: b Hb => cnf1 i1 /= Hlt ; rewrite /E0.E0lt => /=.
    move: Hlt i0 i1; rewrite -(h2g_g2hK cnf0).
    rewrite -(h2g_g2hK cnf1)  -decide_hltE;  repeat split. 
    + move: i0 i1; rewrite -!nf_ref => i0 i1; rewrite g2h_h2gK => //.
      red. move: i0 => /eqP. by [].
    + red in Hlt; move: Hlt;  rewrite bool_decide_eq_true  => //.
      by rewrite !g2h_h2gK. 
    + move: i1; rewrite -!nf_ref  g2h_h2gK /eqP => i1  //.  
      by move: i1 => /eqP. 
  -  apply Acc_inverse_image, E0lt_wf. 
Qed. 

Lemma L1' (a: T1) : T1omega * (a * T1omega) = T1omega * a * T1omega.
Proof. by  rewrite mulA. Qed. 

(** Sequences and limits *)

Definition g2h_seq (s: nat-> T1) n := g2h (s n).
Definition h2g_seq (s: nat -> hT1) n := h2g (s n).

Definition gstrict_lub (s : nat -> T1) (lambda : T1) :=
  (forall i : nat, LT (s i) lambda) /\
    (forall a : T1, (forall i : nat, LE (s i) a) -> LE lambda  a).


Lemma strict_lub_ref (s:nat-> hT1) (lambda: hT1) :
  strict_lub s lambda <-> gstrict_lub (h2g_seq s) (h2g lambda).
Proof. 
  rewrite /gstrict_lub; split. 
  -  case => Ha Hb;  split. 
     + move => i; rewrite -!LT_ref => //.
     + move => a Ha1; rewrite -(h2g_g2hK a) -LE_ref.
       apply Hb => i; destruct (Ha1 i) as [H H0 H1]; split. 
       * move: H; rewrite -hnf_g2h /h2g_seq g2h_h2gK => //.
       * split. 
         --  move: H0; rewrite T1le_iff /h2g_seq g2h_h2gK  => //.
         --  by rewrite hnf_g2h.
  -   destruct 1 as [H H0]; split. 
      + move => i; move:  (H i); rewrite LT_ref =>//.
      +  move => a Ha; rewrite LE_ref;  apply H0. 
         move => i; rewrite -LE_ref; apply Ha. 
Qed.

(* begin snippet SearchDemoa *)
Search ( _ * ?beta = ?beta)%ca.
(* end snippet SearchDemoa *)

(* begin snippet SearchDemob *)
Search ( _ * ?beta = ?beta)%t1.
(* end snippet SearchDemob *)

(* begin snippet T1compareDef *)                                
#[global] Instance  T1compare : Compare T1:=
  fun a beta => compare (g2h a) (g2h beta).

Compute compare (\F 6 + T1omega) T1omega. 
(* end snippet T1compareDef *)                                

(* begin snippet T1compareG2h:: no-out *)
Lemma compare_g2h (a beta : T1):
  compare (g2h a) (g2h beta) = compare a beta .
 Proof.  by []. Qed. 

 Lemma compare_h2g (a beta: hT1) :
   compare (h2g a) (h2g beta) =compare a beta .
Proof. 
  rewrite -(g2h_h2gK a)  -(g2h_h2gK beta).
   by rewrite compare_g2h !g2h_h2gK.
Qed.   
(* end snippet T1compareG2h *)


(** * Make E0 an ordinal notation *)

(* begin snippet T1compareCorrect:: no-out *)                                
Lemma T1compare_correct (a b:  T1):
  CompSpec eq T1lt a b (compare a b). 
(* end snippet T1compareCorrect *)                                
Proof. 
  rewrite /compare /T1compare.
  case  (T1.compare_correct (g2h a) (g2h b)). 
  rewrite g2h_eqE => H; subst;  by constructor. 
  all:  constructor; move:H; by rewrite  lt_ref !h2g_g2hK .
Qed.

(* begin snippet E0compare:: no-out *)                                
#[global] Instance E0compare: Compare E0 :=
  fun (alpha beta: E0) => T1compare (cnf alpha) (cnf beta).

Lemma E0compare_correct (alpha beta : E0) :
  CompSpec eq E0lt alpha beta (compare alpha beta).
(* ... *)
(* end snippet E0compare *)                                
Proof.
  destruct alpha, beta; rewrite /compare;
    case  (T1compare_correct cnf0 cnf1) => Hcomp.
  { subst; replace i0 with i. 
    + rewrite /E0compare; cbn. 
      replace (compare (g2h cnf1) (g2h cnf1)) with Datatypes.Eq => //.
      * by constructor. 
      * by rewrite compare_refl. 
    + apply eq_proofs_unicity_on;
       by  destruct y, (T1nf cnf1) => //; [left | right] => //. 
  } {
    rewrite /E0compare; cbn. 
    replace (compare (g2h cnf0) (g2h cnf1)) with Datatypes.Lt.
    + constructor; rewrite /E0lt => //.
    + move: Hcomp;  rewrite /compare T1lt_iff. 
      case ; rewrite -compare_lt_iff => _ [Hcomp _].
      symmetry; by rewrite compare_lt_iff.  
      1, 2: by apply /eqP. 
  }
  rewrite /E0compare; cbn. 
  replace (compare (g2h cnf0) (g2h cnf1)) with Datatypes.Gt.
  + constructor; rewrite /E0lt => //.
  +  move: Hcomp; rewrite /compare T1lt_iff.
     case ; rewrite -compare_gt_iff => // _ [Hcomp _] //. 
     all: by apply /eqP. 
Qed.   



(* begin snippet E0Sto:: no-out *)                                
#[global] Instance E0_sto : StrictOrder E0lt.
(* end snippet E0Sto *)                                
Proof.
  split.
  - move => x. case :x => x Hx.  rewrite /complement /E0lt=> /=.  
    by rewrite T1ltnn.
  -  rewrite /Transitive; case => x Hx; case => y Hy; case => z Hz.
     by rewrite /E0lt; cbn; apply T1lt_trans. 
Qed.

(* begin snippet compEpsilon0:: no-out *)
#[global] Instance E0_comp : Comparable E0lt compare.
Proof. split; [apply  E0_sto | apply E0compare_correct]. Qed.
(* end snippet compEpsilon0 *)

(* begin snippet ExampleComp *)
Compute compare (E0phi0 (E0fin 2)) (E0mul (E0succ E0omega) E0omega).
(* end snippet ExampleComp *)

(* begin snippet gEpsilon0:: no-out *)
#[global] Instance Epsilon0 : ON E0lt compare.
Proof. split; [apply: E0_comp | apply: gE0lt_wf]. Qed.
(* end snippet gEpsilon0:: no-out *)

(* begin snippet LocateExample *)
Locate T1omega.
(* end snippet LocateExample *)


(** * Abstract properties of arithmetic functions (with SSreflect inequalities)
 *)

(* begin snippet MonoDef *)
Definition strict_mono (f: nat -> nat) :=
  forall n p, (n< p)%N -> (f n < f p)%N.

Definition dominates_from (n : nat) (g f : nat -> nat) :=
  forall p : nat, (n <= p)%N -> (f p < g p)%N.

Definition dominates g f := exists n : nat, dominates_from n g f .

Definition dominates_strong g f  := {n : nat | dominates_from n g f}.

Definition fun_le  f g := forall n:nat, (f n <=  g n)%N.

(* end snippet MonoDef *)
