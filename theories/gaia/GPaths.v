(** Gaia-compatible accessibility in epsilon0  

(imported from [hydras.Epsilon0.Paths]) *)


From mathcomp Require Import all_ssreflect zify.
From hydras Require Import Canon Paths.
Require Import T1Bridge GCanon.


From hydras Require Import T1.
From gaia Require Import ssete9.
Import CantorOrdinal. 

Set Bullet Behavior "Strict Subproofs".

(* begin snippet importationsa:: no-out *)

(** Importation of Ketonen-Solovay's  machinery into gaia's world
    (work in progress) 
*)

#[global] Notation htransition := transition.

Definition transition i (alpha beta: T1) :=
  [/\ i != 0 , alpha != zero & beta == canon alpha i]. 

#[global] Notation hbounded_transitionS := bounded_transitionS.

Definition bounded_transitionS n (alpha beta: T1) :=
  exists i, (i <= n)%N /\ transition (S i) alpha beta.

(* end snippet importationsa *)

(* begin snippet pathsDefs:: no-out *)

#[global] Notation hpath_to := path_to. 
(** [path_to beta s alpha] : [beta] is accessible from [alpha] with trace [s] *)

Definition path_to (to: T1)(s: seq nat) (from:T1) : Prop :=
  hpath_to (g2h to) s (g2h from).

#[global] Notation hpath := path. 

Notation path from s to := (path_to to s from).

Definition acc_from alpha beta := exists s,  path alpha s beta.

#[global] Notation hpathS from s to := (path_toS to s from).

Definition pathS (from: T1)(s: seq nat) (to: T1) : Prop :=
  hpathS (g2h from) s (g2h to).

#[global] Notation hKP_arrowS  := KP_arrowS.

Definition KP_arrowS n := 
  Relation_Operators.clos_trans_1n T1 (bounded_transitionS n).

#[global] Notation hconst_pathS  := const_pathS.
#[global] Notation hconst_path  := const_path.

Definition const_pathS i alpha beta  :=
  hconst_pathS i (g2h alpha) (g2h beta).

Definition const_path i alpha beta :=
  hconst_path i (g2h alpha) (g2h beta).

#[global] Notation hgnawS := gnawS.
#[global] Notation hgnaw := gnaw.

Definition gnawS alpha s := h2g (hgnawS (g2h alpha) s).
Definition gnaw alpha s := h2g (hgnaw (g2h alpha) s).

#[global] Notation hstandard_gnaw := standard_gnaw.
Definition standard_gnaw i alpha l := h2g (hstandard_gnaw i (g2h alpha) l).

(* end snippet pathsDefs *)

(** SSreflect's iota was already defined in Prelude *)

(** To simplify *)

Lemma path_to_iff1 to i from :
  T1nf from -> i <> 0 -> from <> zero ->
  path_to to [:: i] from <-> to = canon from i /\ T1nf from.
Proof.
  move => H H0 H1 ; split; rewrite /path_to.
  -   move => H2; inversion H2 . split. subst. rewrite /htransition in H5.
      destruct i.
      + contradiction.
      + rewrite /canon -(h2g_g2hK to); f_equal. 
        rewrite /transition_S in H5 => //; case H5 => //.
      + rewrite /transition_S in H5 => //.
      + split.
        * inversion H8. 
        * by [].
  - case => -> H2; left => //.      
    rewrite /htransition;  destruct i.
    by destruct H0. 
    split. 
    + move => H3; apply H1; rewrite -g2h_zero in H3. 
      by rewrite -g2h_eq_iff. 
    + by rewrite g2h_canon. 
Qed. 

Lemma iota_adapt i l: iota i l = MoreLists.iota_from i l. 
Proof. elim: i => /= //. Qed. 


Lemma standard_gnaw_iota_from i alpha l :
  i <> 0 -> standard_gnaw i alpha l = gnaw alpha (iota i l).
Proof. 
  move: l i alpha ; elim => // /=. 
  rewrite !/standard_gnaw => n Hn i alpha Hi.
  specialize (Hn (S i) (canon alpha i)); rewrite /canon g2h_h2gK in Hn.
  rewrite Hn /gnaw ?g2h_h2gK => // /=.  
  move: Hi Hn; case :i => //.  
Qed.


Notation hstandard_path i alpha j beta :=
  (standard_path_to j beta i alpha). 

Definition standard_path i alpha j beta :=
  hstandard_path i (g2h alpha) j (g2h beta).

Lemma interval_def i j: MoreLists.interval i j = index_iota i (S j).
Proof.
  by rewrite /index_iota /MoreLists.interval iota_adapt. 
Qed.

(* begin snippet pathToLT:: no-out *)
Lemma path_to_LT beta s alpha :
  path_to beta s alpha -> T1nf alpha -> T1nf beta -> beta < alpha. 
Proof.
    rewrite -!hnf_g2h /path_to => Hpath Halpha Hbeta. 
    generalize (path_to_LT Hpath Halpha).    
    rewrite T1lt_iff => //; by rewrite -hnf_g2h. 
Qed.
(* end snippet pathToLT *)

Theorem KS_thm_2_4 (lambda : T1) :
  T1nf lambda ->
  T1limit lambda  ->
  forall i j, (i < j)%N ->
              const_pathS 0 (canon lambda (S j))
                            (canon lambda (S i)).
Proof. 
  rewrite -hnf_g2h => Hlambda Hlim i j Hij. 
  rewrite -(h2g_g2hK lambda) -limitb_ref in Hlim. 
  have H'ij: (i < j)%coq_nat by apply /ltP. 
  generalize (KS_thm_2_4 Hlambda Hlim H'ij). 
  by rewrite /const_pathS !g2h_canon.
Qed. 

(* begin snippet Cor12:: no-out *)
Lemma Cor12 (alpha : T1) :
  T1nf alpha ->
  forall beta i n, T1nf beta -> beta  < alpha  ->
                   (i < n)%N ->
                   const_pathS i alpha beta ->
                   const_pathS n alpha beta.
(* end snippet Cor12 *)
Proof.
  rewrite -hnf_g2h => Hnf beta i n Hbeta Hlt Hij; rewrite /const_pathS.
  apply Cor12 => //.
  rewrite -T1lt_iff => //.
  by rewrite -hnf_g2h => //. 
  by apply /ltP. 
Qed.

(* begin snippet Lemma261:: no-out *)
Lemma Lemma2_6_1 (alpha:T1) :
T1nf alpha ->
  forall beta, T1nf beta -> 
    T1lt beta  alpha  ->
    {n:nat | const_pathS n alpha beta}.
(* end snippet Lemma261 *)
Proof.
  rewrite -hnf_g2h => Hnf beta Hbeta Hlt.
  have H: hnf (g2h beta) by rewrite hnf_g2h. 
  have H'lt : g2h beta t1< g2h alpha; repeat split => //.
  rewrite T1lt_iff in Hlt => //.
  case: Hlt => ? [? ?] //.  
  by rewrite -hnf_g2h. 
  case (Lemma2_6_1 Hnf H'lt) => x Hx; exists x. 
  by rewrite /const_pathS. 
Qed. 

(* begin snippet constantToStandard:: no-out *)
Lemma constant_to_standard_path 
  (alpha beta : T1) (i : nat):
  T1nf alpha -> const_pathS i alpha beta -> zero  < alpha ->
  {j:nat | standard_path (S i) alpha j beta}.
(* end snippet constantToStandard *)
Proof.  
  rewrite -hnf_g2h => nfalpha Hpath Hpos.
  case (@constant_to_standard_path (g2h alpha) (g2h beta) i) => //.
   rewrite T1lt_iff -?hnf_g2h in Hpos =>  //.  
  move => x Hx; exists x; by rewrite /standard_path. 
Qed.

(* begin snippet LTToStandard:: no-out *)
Theorem  LT_to_standard_path (alpha beta : T1) :
  T1nf alpha -> T1nf beta -> beta < alpha ->
  {n : nat & {j:nat | standard_path (S n) alpha j beta}}. 
Proof.
  (* end snippet LTToStandard *)
  rewrite    -!hnf_g2h => nfalpha nfbeta  Hlt.
  case (@LT_to_standard_path (g2h alpha) (g2h beta)).  
  rewrite -T1lt_iff -?hnf_g2h  => //.
  move => x; case => j Hj; exists x, j; by rewrite /standard_path. 
Qed.

(** * Adaptation to E0 *)

Notation hCanon_plus := Canon_plus. 
Definition Canon_plus i alpha beta :=
  hCanon_plus i (E0_g2h alpha) (E0_g2h beta).




(** * Examples *)

Example ex_path1 : path (T1omega * (\F 2)) [:: 2; 2; 2] T1omega.
Proof. rewrite /path_to;  path_tac. Qed.

Example ex_path2: path (T1omega * \F 2) [:: 3; 4; 5; 6] T1omega.
Proof. rewrite /path_to;  path_tac. Qed.

Example ex_path3: path (T1omega * \F 2) (index_iota 3 15) zero.
Proof. rewrite /path_to /index_iota => /=.  path_tac. Qed.

Example ex_path4: path (T1omega * \F 2) (List.repeat 3 8) zero.
Proof. rewrite /path_to => /=. path_tac. Qed.

Example ex_path5: pathS (T1omega * \F 2) (List.repeat 2 8) zero.
Proof. rewrite /pathS path_toS_path_to => /=; path_tac. Qed.

(*
Compute T1pp (gnaw (phi0 T1omega) [:: 2; 3; 4; 5]).

Compute T1pp (gnaw (phi0 T1omega) (index_iota 2 10)).

Compute T1pp (gnaw (phi0 T1omega) (index_iota 2 19)).

Compute T1pp (gnaw (phi0 T1omega) (index_iota 2 38)).

Compute T1pp (gnawS (phi0 T1omega) (index_iota 1 37)).

Compute T1pp (standard_gnaw  2 (phi0 T1omega * \F 2) 22).

Compute T1pp (standard_gnaw  2 (phi0 T1omega * \F 2) 37).

Compute T1pp (standard_gnaw  2 (phi0 T1omega * \F 2) 75).
 
*)


  
