(** Learning ssreflect:  *)

From mathcomp Require Import all_ssreflect zify.

Lemma diffP {T:eqType}(i j:T): reflect (i <> j) (i != j). 
Proof.
  case E: (i ==  j) => //=; constructor => H.
  - have H1: i = j by apply /eqP => //.
    done. 
  -  move: E; by rewrite  H eq_refl.  
Qed.

Lemma eq_op_sym {T:eqType}{x y: T}: (x == y) = (y == x). 
Proof. 
  case E: (x == y) => //.
  case E': (y == x) => //.
  have H: x = y by apply /eqP; subst.
  move: E; subst; by rewrite E'.
  have H: x <> y. apply /diffP ;  by rewrite E.  
  have H': y<>x by congruence. 
  symmetry; have H0: y != x by apply /diffP. 
  move : H0; case (y == x) => //.
Qed.

Lemma diffsym {T:eqType}{x y: T}: (x != y) = (y != x). 
Proof. 
 by rewrite eq_op_sym.  Qed. 
  
