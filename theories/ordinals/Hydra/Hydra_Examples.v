From Coq Require Import  Lia  Max.
From hydras Require Import Hydra_Lemmas More_Arith.
Open Scope nat_scope.

(* begin snippet HydraRect2Check *)

Check Hydra_rect2.

(* end snippet HydraRect2Check *)


Module Examples.


  Example ex1 : forall h h', R1 (hyd3 h head h') (hyd2 h h').
  Proof. split.  right; left. Qed.

  (* begin snippet Hy *)
  
  Example Hy := hyd3 head
                     (hyd2
                        (hyd1 
                           (hyd2 head head))
                        head) 
                     head.
  (* end snippet Hy *)

  (* begin snippet HySize *)

  Compute hsize Hy.

  (* end snippet HySize *)


  (* begin snippet HyHeight *)

  Compute height Hy.

  (* end snippet HyHeight *)
  
  Example Hy' := hyd2 head
                      (hyd2
                         (hyd1 
                            (hyd2 head head))
                         head).
  
  
  Example ex4:  round Hy Hy'.
  Proof.  chop_off 2. Qed.

  (* begin snippet HySecond *)
  
  Example Hy'' := 
    hyd2 head
         (hyd2
            (hyd_mult (hyd1 head) 5)
            head).

  (* end snippet HySecond *)
  
  Example Hy'H'' : round Hy' Hy''.
  Proof.
    h_search_n 4; r2_up 1; r2_up 0; r2_d2 0 1.
  Qed.
  
  Example R2_example:  R2 4 Hy' Hy''.
  Proof.
    (** move to 2nd sub-hydra (0-based indices) *) r2_up 1. 
    (** move to first sub-hydra *)  r2_up 0.
    (** we're at distance 2 from the to-be-chopped-off head 
        let's go to the first daughter, then chop-off the leftmost head *)
    r2_d2 0 0. 
  Qed.
  
  
  Example Exx :  {h' | round Hy' h'}.
  Proof.
    eexists; h_search_n 4 .
    r2_up 1; r2_up 0; r2_d2 0 1.
  Defined. 
  
  
  Example Ex5 : {h' | Hy -*-> h'}.
  Proof.
    eexists.
    forward.
    - chop_off 2.
    - forward.
      + h_search_n 4; r2_d2 1 1.
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
    split; chop_off 0%nat.
  Qed.
  


  Example ex_2 :{Hy'' | R2 4 Hy' Hy''}.
  Proof.
    eexists; unfold Hy'.
    r2_up 1;  r2_up 0;  r2_d2 0 0.
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

(* begin snippet HydraInd *)

Check Hydra_ind.

(* end snippet HydraInd *)

(* begin snippet BadInductiona *)

Module Bad.

  Lemma  height_lt_size (h:Hydra) :
    height h < hsize h. (* .no-out *)
  Proof. (* .no-out *)
    induction h as [s].

    (* end snippet BadInductiona *)

    (* begin snippet BadInductionb *)
    
    induction s as [| h s']. (* .no-out *)

    (* end snippet BadInductionb *)

    (* begin snippet BadInductionc *)
    
    -  (* .no-in  .unfold *) simpl; auto with arith. (* .no-out *)

    (* end snippet BadInductionc *)

    (* begin snippet BadInductiond *)
       
    -  (* .no-in .unfold *)
      (* end snippet BadInductiond *)
      
      (* begin snippet BadInductione *)
      
  Abort.  

End Bad.
(* end snippet BadInductione *)

(* begin snippet heightLtSizea *)

(*|
.. coq:: no-out
|*)

Lemma  height_lt_size (h:Hydra) :  height h < hsize h. 
Proof. 
  induction h using Hydra_rect2  with 
      (P0 :=  h_forall (fun h =>  height h < hsize h)).
(*||*)

(* end snippet heightLtSizea *)
  
  -  destruct h as [ | h s']. 
     + cbn; auto with arith.
     +  simpl.  destruct IHh; assert (lheight s' <= lhsize s').
        { clear H; induction s'. 
          -     cbn; auto with arith. 
          -     simpl.  destruct (lheight s').
                + cbn in H0; destruct H0; apply IHs' in H0 .
                  red in H;  transitivity (hsize h0); auto.
                  auto with arith. 
                + cbn in H0; destruct H0. 
                  apply IHs' in H0.    clear IHs'.            
                  rewrite succ_max_distr; 
                    transitivity (S (height h0) + (S n)).
                  apply max_le_plus; auto.
                  cbn; lia.
        }
        clear H0; cbn; destruct (lheight s').
        *   lia. 
        *   specialize (max_le_plus (height h) n); lia.
  -  easy.   
  -  split;auto.
Qed. 

