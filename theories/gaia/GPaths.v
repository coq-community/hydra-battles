(** Gaia-compatible accessibility in epsilon0  

(imported from [hydras.Epsilon0.Paths]) *)


From mathcomp Require Import all_ssreflect zify.
From hydras Require Import Canon Paths.
Require Import T1Bridge GCanon.


From hydras Require Import T1.
From gaia Require Import ssete9.
Import CantorOrdinal. 

(** Importation of Ketonen-Solovay's  machinery into gaia's world
    (work in progress) 
 *)

(** small transition step associated with canonical sequences *)
(* begin snippet importationsa:: no-out *)

#[global] Notation htransition := Epsilon0.Paths.transition.
#[global] Notation hbounded_transitionS := Paths.bounded_transitionS.


Definition transition i (a b: T1) :=
  [/\ i != 0 , a!= zero & b == canon a i].

Definition bounded_transitionS n (a b: T1) :=
  exists i, (i <= n)%N /\ transition (S i) a b.
(* end snippet importationsa *)

Definition transitionb i (a b: T1) :=
  [&& i != 0 , a!= zero & b == canon a i]. 

Lemma transitionP i a b : reflect (transition i a b )
                                  (transitionb i a b). 
Proof. rewrite /transition /transitionb => //; by apply and3P. Qed. 


(** TODO : define [path_to] as a boolean function *)
#[global] Notation hpath_to := path_to.
#[global] Notation hpath := path.
#[global] Notation hpathS from s to := (path_toS to s from).
#[global] Notation hconst_pathS  := const_pathS.
#[global] Notation hconst_path  := const_path.
#[global] Notation hgnawS := gnawS.
#[global] Notation hgnaw := gnaw.
#[global] Notation hstandard_gnaw := standard_gnaw.



(* begin snippet pathsDefs:: no-out *)
(** [path_to b s alpha] : [b] is accessible from [alpha] with trace [s] *)

Definition path_to (to: T1)(s: seq nat) (from:T1) : Prop :=
  hpath_to (g2h to) s (g2h from).

Notation path from s to := (path_to to s from).

Definition acc_from a b := exists s, path a s b.

(* end snippet pathsDefs *)



(* begin snippet pathsDefsb:: no-out *)
Definition const_path i a b :=  hconst_path i (g2h a) (g2h b).

Definition standard_path i a j b :=
   Paths.standard_path i (g2h a) j (g2h b).
(* end snippet pathsDefsb:: no-out *)

Definition standard_gnaw i a l := h2g (hstandard_gnaw i (g2h a) l).


Definition gnaw a s := h2g (hgnaw (g2h a) s).
Definition gnawS a s := h2g (hgnawS (g2h a) s).

Definition pathS (from: T1)(s: seq nat) (to: T1) : Prop :=
  hpathS (g2h from) s (g2h to).

Fixpoint path_tob (b: T1) (s: seq nat) (a:T1): bool :=
  match s with
  | [::] => false
  | [:: i] =>  (i != 0) && transitionb i a b
  | i :: s =>  (i != 0) && path_tob  b s (canon a i)
  end.

(** SSreflect's iota was already defined in Prelude *)

(** To simplify *)

Lemma path_to_inv1 to i from : path_to to [:: i] from ->
                               i <> 0 /\ transition i from to.
  inversion 1.
  split; trivial. 
move: H2; rewrite /transition; rewrite /htransition.

destruct i. 
contradiction. 
rewrite /transition_S. 
destruct 1. 
repeat split. 
destruct from. 
destruct H4. by []. 
by [].
rewrite /canon. 
apply /eqP. 
Search g2h eq. 
by rewrite -g2h_eqE g2h_h2gK. 

split; trivial. 
inversion H5. 
Qed. 


Lemma path_to_iff1 to i from :
  T1nf from -> i <> 0 -> from <> zero ->
  path_to to [:: i] from <-> to = canon from i /\ T1nf from.
Proof.
  move => H H0 H1 ; split; rewrite /path_to.
  move => H2; case (path_to_inv1 _ _ _ H2) => {}H2 H3. 
  case: H3;  repeat split => //;  by apply /eqP. 
  constructor => //.
  destruct i => //.
  case: H2 => H2 H3; constructor.
   move => H4; apply H1; by rewrite -g2h_eqE. 
   move: H2; rewrite -g2h_eqE ; by rewrite -g2h_canon. 
Qed. 

Lemma iota_adapt i l: iota i l = MoreLists.iota_from i l. 
Proof. elim: i => /= //. Qed. 

Lemma standard_gnaw_iota_from i a l :
  i <> 0 -> standard_gnaw i a l = gnaw a (iota i l).
Proof. 
  move: l i a; elim => // /=. 
  rewrite !/standard_gnaw => n Hn i a Hi.
  move: (Hn (S i) (canon a i)); rewrite /canon g2h_h2gK.  
  move => {}Hn; rewrite Hn /gnaw ?g2h_h2gK => // /=; by case :i Hn Hi. 
Qed.



Lemma interval_def i j: MoreLists.interval i j = index_iota i (S j).
Proof.
  by rewrite /index_iota /MoreLists.interval iota_adapt. 
Qed.

(* begin snippet pathToLT:: no-out *)
Lemma path_to_LT b s a:
  path_to b s a -> T1nf a -> T1nf b -> b < a. 
(* end snippet pathToLT *)
Proof.
    rewrite -!hnf_g2h /path_to => Hpath Ha Hb. 
    move: (path_to_LT Hpath Ha);
      rewrite T1lt_iff => //; by rewrite -hnf_g2h. 
Qed.


(* begin snippet LTPathTo:: no-out *)
Lemma LT_path_to (a b : T1) :
  T1nf a -> T1nf b -> b < a ->
  {s : list nat | path_to b s a}.
(* end snippet LTPathTo *)
Proof. 
  move => Ha Hb Hlt;
          generalize (@LT_path_to (g2h a) (g2h  b)) => H.
  rewrite /path_to; apply H, T1lt_iff => //.
Qed. 

(* begin snippet KSThm24:: no-out *)
Theorem KS_thm_2_4 (lambda : T1) :
  T1nf lambda -> T1limit lambda  ->
  forall i j, (i < j)%N ->
              const_path 1 (canon lambda (S j))
                         (canon lambda (S i)).
(* end snippet KSThm24 *)
Proof. 
  rewrite -hnf_g2h => Hlambda Hlim i j Hij. 
  move: Hlim; rewrite -(h2g_g2hK lambda) -limitb_ref => Hlim. 
  have H'ij: (i < j)%coq_nat by apply /ltP. 
  generalize (KS_thm_2_4 Hlambda Hlim H'ij). 
  by rewrite /const_path !g2h_canon !h2g_g2hK. 
Qed. 

(* begin snippet Cor12:: no-out *)
Lemma Cor12 (a: T1) :
  T1nf a ->
  forall b i n, T1nf b -> b < a -> (i < n)%N ->
                   const_path i.+1 a b ->
                   const_path n.+1 a b.
(* end snippet Cor12 *)
Proof.
  rewrite -hnf_g2h => Hnf b i n Hb Hlt Hij; apply Cor12 => //.
  rewrite -T1lt_iff => //;  by rewrite -hnf_g2h.
  by apply /ltP. 
Qed.

(* begin snippet Lemma261:: no-out *)
Lemma Lemma2_6_1 (a:T1) :
T1nf a -> forall b, T1nf b -> b < a -> {n:nat | const_path n.+1 a b}.
(* end snippet Lemma261 *)
Proof.
  rewrite -hnf_g2h => Hnf b Hb Hlt.
  have H: T1.nf (g2h b) by rewrite hnf_g2h. 
  have H'lt : g2h b t1< g2h a; repeat split => //.
  move: Hlt; rewrite T1lt_iff => //.
  case => ? [? ?] //.  
  by rewrite -hnf_g2h. 
  case (Lemma2_6_1 Hnf H'lt) => x Hx; exists x. 
  by rewrite /const_pathS. 
Qed. 

(* begin snippet constantToStandard:: no-out *)
Lemma constant_to_standard_path (a b : T1) (i : nat):
  T1nf a -> const_path i.+1 a b -> zero  < a ->
  {j:nat | standard_path i.+1 a j b}.
(* end snippet constantToStandard *)
Proof.  
  rewrite -hnf_g2h => nfa Hpath Hpos.
  case (@constant_to_standard_path (g2h a) (g2h b) i) => //.
   move: Hpos; rewrite T1lt_iff -?hnf_g2h  =>  //.  
  move => x Hx; exists x; by rewrite /standard_path. 
Qed.

(* begin snippet LTToStandard:: no-out *)
Theorem  LT_to_standard_path (a b : T1) :
  T1nf a -> T1nf b -> b < a ->
  {n : nat & {j:nat | standard_path n.+1 a j b}}. 
Proof.
  (* end snippet LTToStandard *)
  rewrite -!hnf_g2h => nfa nfb  Hlt.
  case (@LT_to_standard_path (g2h a) (g2h b)).  
  rewrite -T1lt_iff -?hnf_g2h  => //.
  move => x; case => j Hj; exists x, j; by rewrite /standard_path. 
Qed.

(** * Adaptation to E0 *)

Notation hCanon_plus := Canon_plus. 
Definition Canon_plus i a b :=
  hCanon_plus i (E0_g2h a) (E0_g2h b).




(** * Examples *)
(* begin snippet pathExamples:: no-out *)
Example ex_path1 : path (T1omega * (\F 2)) [:: 2; 2; 2] T1omega.
Proof. rewrite /path_to;  Epsilon0.Paths.path_tac. Qed.

Example ex_path2: path (T1omega * \F 2) [:: 3; 4; 5; 6] T1omega.
Proof. rewrite /path_to;  path_tac. Qed.

Example ex_path3: path (T1omega * \F 2) (index_iota 3 15) zero.
Proof. rewrite /path_to /index_iota => /=; path_tac. Qed.

Example ex_path4: path (T1omega * \F 2) (List.repeat 3 8) zero.
Proof. rewrite /path_to => /=;  path_tac. Qed.
(* end snippet pathExamples *)

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


  
