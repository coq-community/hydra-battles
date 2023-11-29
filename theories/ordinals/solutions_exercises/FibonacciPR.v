From hydras Require Import primRec cPair extEqualNat.

(** The famous Fibonacci function *)

(* begin snippet fibDef *)

Fixpoint fib (n:nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | S ((S p) as q) => fib q + fib p
  end.

(* end snippet fibDef *)

Section Proof_of_FibIsPR.

  (** To do :  Some parts of this proof may be made more generic *)

  (** let us consider another definition of fib, as an application of
      [nat_rec]
   *)


  Let fib_step (p: nat * nat) := (fst p + snd p, fst p).

  Let fib_iter n p:= (nat_rec (fun _ => (nat*nat)%type)
                              p
                              (fun _ p => fib_step p)
                              n).
  Definition fib_alt n := snd (fib_iter n (1,1)).

  Compute fib_alt 10.

  (** The theory of primitive functions deals only with functions
    of type [naryFunc n].

   So, let us define a variant of [fib_alt] 

   *)

  (* begin snippet AboutCPair *)
  Import LispAbbreviations. 
  Check cPair. 
  Print car.
  Check car.
  Check cdr.
  Search cPair isPR. 
  Search car isPR.
  Search car cdr cPair.
  (* end snippet AboutCPair *)


  Let fib_step_cPair p := cPair (car p + cdr p)
                                (car p).

  Let fib_iter_cPair n p := nat_rec (fun _ => nat)
                                    p
                                    (fun _ p => fib_step_cPair p)
                                    n.

  Definition fibPR n := cdr (fib_iter_cPair n (cPair 1 1)).


  (** Let us prove that [fibPR] is PR *)

  #[export] Instance fibPRIsPR: isPR 1 fibPR.
  Proof.
    unfold fibPR; apply compose1_1IsPR.
    - apply indIsPR.
      unfold fib_step_cPair; apply filter01IsPR.
      apply compose1_2IsPR.
      + apply compose1_1IsPR.
        * apply idIsPR.
        * apply compose1_2IsPR.
          --  apply cPairPi1IsPR.
          -- apply cPairPi2IsPR.
          -- apply plusIsPR.
      + apply cPairPi1IsPR.
      + apply cPairIsPR.
    - apply cPairPi2IsPR.
  Qed.

  (** Ok, but we must prove that [fibPR] is extensionaly equal to [fib] *)

  (** let us consider the following relation *)

  Definition inv (p: nat*nat) (c: nat) :=  c = cPair (fst p) (snd p).

  Lemma inv_Pi : forall p c, inv p c ->  snd p = cPairPi2 c.
  Proof. 
    intros;  unfold inv in H;  subst; now rewrite cPairProjections2.
  Qed.

  Lemma L0: inv (1,1) (cPair 1 1).
  Proof. reflexivity. Qed.

  Lemma LS : forall p c,  inv p c -> inv (fib_step p) (fib_step_cPair c).
  Proof.
    destruct p as (a,b); intros.
    unfold inv in *. simpl fst  in *. simpl snd in *.
    unfold fib_step_cPair.
    subst;  now rewrite cPairProjections1, cPairProjections2.
  Qed.

  Lemma L1 : forall  p c,
      inv p c -> forall n,
        inv (fib_iter n p)
            (fib_iter_cPair n c).
  Proof.
    induction n.      
    - cbn; assumption.
    - cbn; now  apply LS. 
  Qed.

  Lemma L2 : extEqual 1 fib_alt fibPR.
  Proof.
    intro n; unfold fib_alt, fibPR. 
    rewrite (inv_Pi _ _ (L1 _ _ L0 n ));  reflexivity.
  Qed.

  #[export] Instance fib_altIsPR : isPR 1 fib_alt.
  Proof.    
    destruct fibPRIsPR  as [x Hx]; exists x.
    apply extEqualTrans with fibPR; auto.
    apply extEqualSym, L2.
  Qed.


  (** It remains to prove that fib_alt is equivalent to the "classical" fib *)
  
  Lemma fib_OK0 : forall n,
      fib_iter n (1,1) = (fib (S n), fib n).
  Proof.
    induction n; simpl; auto.
    destruct n.
    -  cbn;  reflexivity.
    - rewrite IHn; unfold fib_step.
        simpl fst; simpl snd; auto.
  Qed.

  Lemma fib_alt_Ok : extEqual 1 fib fib_alt.
  Proof.
    intro n;  change (fib n) with (snd (fib (S n), fib n)).
    rewrite <- fib_OK0; reflexivity. 
  Qed.


  #[export] Instance fibIsPR : isPR 1 fib.
  Proof.
    destruct fib_altIsPR as [x Hx].
    exists x;  apply extEqualTrans with fib_alt; auto.
    apply extEqualSym, fib_alt_Ok.
  Qed.

End Proof_of_FibIsPR.



Compute fibPR 1.

Compute fibPR 2.


(** Too long !

Time Compute fibPR 3.
 *)

