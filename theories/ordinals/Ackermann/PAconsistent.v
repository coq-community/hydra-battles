(** PAconsistent.v

    Original file by Russel O' Connor *)

From Coq Require Import Arith.
Require Import folProof  folProp  PA model.

Definition natModel : Model LNT :=
  model LNT nat
    (fun f : Functions LNT =>
     match f return (naryFunc nat (arityF LNT f)) with
     | Languages.Plus_ => fun x y : nat => y + x
     | Languages.Times_ => fun x y : nat => y * x
     | Languages.Succ_ => S
     | Languages.Zero_ => 0
     end) 
    (fun r : Relations LNT => match r with end).

Theorem PAconsistent : Consistent LNT PA.
Proof.
  apply ModelConsistent with (M := natModel) (value := fun _ : nat => 0).
  generalize (fun _ : nat => 0) ; intros n f H.
  do 8 try induction H; try solve [ simpl in |- *; auto ].
  - rewrite H; clear H; unfold PA7.
    unfold close, nnTranslate in |- *.
    simpl in |- *.
    intros H; apply H; clear H.
    generalize n; clear n.
    induction
      (List.nodup  eq_nat_dec
         (List.app (freeVarFormula LNT (substF LNT x0 x1 Zero))
            (List.app
               (List.remove  eq_nat_dec x1
                  (List.app (freeVarFormula LNT x0)
                     (freeVarFormula LNT
                        (substF LNT x0 x1 (Succ (var x1))))))
               (List.remove eq_nat_dec x1 
                  (freeVarFormula LNT x0)))));
      intros n.
    + simpl; intros H H0 x2 H1. 
      induction x2 as [| x2 Hrecx2].
      * apply H1.
        replace 0 with (interpTerm LNT natModel n Zero).
        { apply subInterpFormula2.
          now rewrite subNNHelp.
        }
        reflexivity.
      * apply H0 with x2; clear H0.
        intros H0; apply Hrecx2.
        intros H2; clear Hrecx2.
        apply H1; clear H1.
        rewrite <- subNNHelp in H0.
        assert
          (H1: interpFormula LNT natModel
                 (updateValue LNT natModel (updateValue LNT natModel n x1 x2) x1
                    (interpTerm LNT natModel (updateValue LNT natModel n x1 x2)
                       (Succ (var x1)))) (nnHelp LNT x0)) 
          by (apply subInterpFormula2; auto ); clear H0 H2.
        apply
          freeVarInterpFormula
          with
          (updateValue LNT natModel (updateValue LNT natModel n x1 x2) x1
             (interpTerm LNT natModel (updateValue LNT natModel n x1 x2)
                (Succ (var x1)))).
        -- intros x3 H0; unfold updateValue; 
             induction (eq_nat_dec x1 x3) as [a | b].
           ++ replace
               (interpTerm LNT natModel
                  (fun x4 : nat =>
                     match eq_nat_dec x1 x4 with
                     | left _ => x2
                     | right _ => n x4
                     end) (Succ (var x1))) with
               (interpTerm LNT natModel (fun _ : nat => x2) (Succ (var x1)));
               [reflexivity | ]. 
              apply freeVarInterpTerm.
              intros x4 [H2| H2].
              ** rewrite H2.
                 destruct (eq_nat_dec x4 x4) as [_ | b]. 
                 reflexivity.
                 now elim b.
              ** destruct H2. 
           ++ reflexivity.
        -- exact H1. 
    + cbn; auto.
  - cbn; intros H; apply H.
    intros x H0; apply H0; intros ?; discriminate. 
Qed.
