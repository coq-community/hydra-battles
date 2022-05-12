(** Learning ssreflect:  *)

From mathcomp Require Import all_ssreflect zify.
Lemma diffP {T:eqType}(i j:T): reflect (i <> j) (i != j). 
Proof.
  case E: (i ==  j) => //=; constructor => H.
  - have H1: i = j by apply /eqP => //.
    done. 
  -  move: E; by rewrite  H eq_refl.  
Qed.


