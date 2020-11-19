(** A _strategy_ is any function $\gamma$ of type [positive -> positive] 
such that, if $n>3$, then $1<\gamma(n)<n$.

 
*)
    

Require Import Arith NArith Pow Compatibility More_on_positive.
Open Scope positive_scope.

Open Scope positive_scope.
Class Strategy (gamma : positive -> positive):=
{
gamma_lt :forall p:positive, 3 < p -> gamma  p < p;
gamma_gt : forall p:positive, 3 < p -> 1 < gamma  p
}.

Ltac gamma_bounds gamma i H1 H2 :=
  assert (H1 : 1 < gamma i) by (apply gamma_gt;auto with chains);
  assert (H2 : gamma i < i) by (apply gamma_lt; auto with chains).

Lemma div_gamma_pos {gamma}{Hgamma : Strategy gamma}
: forall (p:positive) q r, 
    N.pos_div_eucl p (N.pos (gamma p)) = (q, r) ->
    3 < p ->
    (0 < q)%N.
Proof.
  destruct q; [ | reflexivity].
  intros r H H0;assert (H1  : p = N2pos r) by 
                   (apply (N_pos_div_eucl_q0 _ _ _ H);auto).
  destruct (Pos.lt_irrefl p).
  transitivity (gamma  p).  
  -   rewrite H1 at 1.
      generalize  (N.pos_div_eucl_remainder  p
                                             (N.pos (gamma p)));
        rewrite H; cbn.  
      intros H2; destruct r.
      +  apply gamma_gt; auto. 
      +  rewrite  <- pos2N_inj_lt in H2;  cbn; auto with chains.
  -  apply gamma_lt;auto with chains. 
Qed.



