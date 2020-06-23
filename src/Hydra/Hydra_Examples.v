Require Import Hydra_Lemmas Lia  Max More_Arith.
Open Scope nat_scope.


Module Examples.


  Example ex1 : forall h h', R1 (hyd3 h head h') (hyd2 h h').
  Proof. split.  right; left. Qed.


  Example Hy := hyd3 head
                     (hyd2
                        (hyd1 
                           (hyd2 head head))
                        head) 
                     head.
  
  Example Hy' := hyd2 head
                      (hyd2
                         (hyd1 
                            (hyd2 head head))
                         head).
  
  
  Example ex4:  round Hy Hy'.
  Proof.  round_1 2. Qed.

  
  Example Hy'' := 
    hyd2 head
         (hyd2
            (hyd_mult (hyd1 head) 5)
            head).
  
  Example Hy'H'' : round Hy' Hy''.
  Proof.
    round_2 4; R2_up 1; R2_up 0; R2_here 0.
    hremove 1.
  Qed.
  
  Example R2_example:  R2 4 Hy' Hy''.
  Proof.
    right;  right;  left;  right; left; left; left; split; left.
  Qed.
  
  
  Example Exx :  {h' | round Hy' h'}.
  Proof.
    eexists; round_2 4 .
    R2_up 1; R2_up 0; R2_here 0.
    hremove 1.
  Defined. 
  
  
  Example Ex5 : {h' | Hy -*-> h'}.
  Proof.
    eexists.
    forward.
    - round_1 2.
    - forward.
    + round_2 4.
      R2_here 1.
      hremove 1.
    + stop.
  Defined.


  Example Hy''' :=
    node (hcons head
                (hcons_mult (hyd1 (hyd_mult (hyd1 head) 5)) 3 hnil)).
  
  
  
  Example hsize_bigger : (hsize Hy'' < hsize Hy''')%nat.
  Proof.  compute. lia.  Qed.
  
  
  Example height_not_strictly_decreasing : height Hy'' = height Hy'''.
  Proof. reflexivity.  Qed.
  
  
  Example Hy_1 : R1 Hy Hy'.
  Proof.
    repeat constructor.
  Qed.
  
  
  Example Hy_2 : R2 4 Hy' Hy''.
  Proof.
    right.  right. left.  right; left;  left; left.
    split; hremove 0%nat.
  Qed.
  


  Example ex_2 :{Hy'' | R2 4 Hy' Hy''}.
  Proof.
    eexists.
    unfold Hy'.
    R2_up 1.
    R2_up 0. 
    R2_here 0.
    hremove 0%nat.
  Defined.
  
  
  Example Hy_3 : R2 2 Hy'' Hy'''.
  Proof.
    left;right;left;split;right;left.
  Qed.

  Example Hy''_Hy''' : Hy'' -1-> Hy'''.
  Proof.
    exists 2;  right; apply  Hy_3.
  Qed.

  Example Hy_Hy''' :  Hy  -+-> Hy'''.
  Proof.
    eright.
    - eexists;  left; apply Hy_1.
    -  eright.
       + eexists.  right; apply Hy_2.
       + left.  eexists; right;apply Hy_3.
         Unshelve. 
         exact 0. 
  Qed.


End Examples.


Module Bad.

  Lemma  height_lt_size (h:Hydra) :
    height h < hsize h.
  Proof.
    induction h as [s].
    induction s as [| h s'].
    - simpl.  auto with arith.
    - cbn.
  Abort.  

End Bad.


Fixpoint h_forall (P: Hydra -> Prop) (s: Hydrae) :=
  match s with
    hnil => True
  | hcons h s' => P h /\ h_forall P s'
  end.

Lemma  height_lt_size (h:Hydra) :
  height h < hsize h.
Proof.
  induction h using Hydra_rect2  with 
      (P0 :=  h_forall (fun h =>  height h < hsize h)).
  -  destruct h as [ | h s'].
     + cbn; auto with arith.
     +  simpl.  destruct IHh; assert (lheight s' <= lhsize s').
        { clear H; induction s'. 
          -     cbn; auto with arith. 
          -     simpl.  destruct (lheight s').
                + cbn in H0; destruct H0; apply IHs' in H0 .
                  red in H;  transitivity (hsize h0); auto.
                  auto with arith. 
                +  
                  cbn in H0; destruct H0. 
                  apply IHs' in H0.    clear IHs'.            
                  rewrite succ_max_distr; 
                    transitivity (S (height h0) + (S n)).
                  apply max_le_plus; auto.    cbn.
                  lia.
        }
        clear H0; cbn; destruct (lheight s').
        *   lia. 
        *   specialize (max_le_plus (height h) n); lia.
  -  easy.   
  -  split;auto. 
Qed. 


