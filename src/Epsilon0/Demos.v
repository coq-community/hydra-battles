Require Import E0 Canon Paths Hessenberg.
Require Import Extraction.


(* Coercion fin : nat >-> T1. *)

Import T1.

Example alpha_0 : T1 :=
  ocons (ocons (ocons zero 0 zero)
               0
               zero)
        0
       (ocons (ocons zero 2 zero)
              4
              (ocons zero 1 zero)).

Compute alpha_0.

Compute succ omega.

Compute succ 8.

Example succ8 :  succ 8 = 9.
Proof. reflexivity. Qed.

Compute  ocons omega 0 (ocons 3 4 2).

Example alpha_0_eq : alpha_0 = phi0 omega  +
                               phi0 3  * 5 +
                                2.
Proof. reflexivity. Qed.

(** An example of a term which is not in Cantor Normal Form *)
Example bad_term  : T1 := ocons 1 1 (ocons omega 2 zero).

Remark bad_term_not_nf : not (nf bad_term).
Proof.
intro H; inversion H.
Qed.

Compute nf bad_term.

Compute (succ 5).

Example E0: ~ zero <= bad_term.
Proof.
  compute; firstorder.
Qed.

Example E'0 : ~ bad_term <= zero.
Proof.
  compute; firstorder.
Qed.


Example omega_In_epsilon0  : Ensembles.In _ epsilon_0 omega.
Proof.  repeat    constructor. Qed.



Example e2 : 7  + omega = omega.
Proof. reflexivity. Qed.

Example e'2 : omega < omega + 6.
Proof. now compute. Qed.

Example e''2 : 6 * omega = omega.
Proof. reflexivity. Qed.

Example e'''2 : omega < omega * 6.
Proof. now compute. Qed.

Lemma plus_not_monotonous : exists alpha beta gamma : T1,
    alpha < beta /\ alpha + gamma = beta + gamma.
Proof.
  exists 3, 5, omega; now  compute.
Qed.

Example oplus_example :   3 o+ (omega + 5) = omega + 8.
Proof. reflexivity. Qed.


Example oplus_example_2 :   (omega ^ 2  + 3)  o+ (omega ^ 2 + omega + 5) =
                            omega ^ 2 * 2 + omega  + 8.
Proof. reflexivity. Qed.


Lemma mult_not_monotonous :  exists alpha beta gamma : T1,
      alpha < beta /\ alpha * gamma = beta * gamma.
Proof.
  exists 3, 5, omega; now compute.
Qed.

Compute alpha_0.

Compute pp alpha_0.

Example e3 : omega + ocons omega 1 zero = ocons omega 1 zero.
Proof. reflexivity. Qed.


Compute pp (omega - 1).

Example plus_not_comm : {a:T1 & {b :T1 |
                          nf a /\ nf b /\ a + b  <> b + a}}.
Proof.
 exists (FS 0); exists omega; repeat split.
 - repeat constructor. compute.  discriminate 1. 
Defined.

(** Experimenting canonical sequences


*)

Example exp_ex :  (omega + 1) ^ omega = phi0 omega.
Proof.
  reflexivity.
Qed.

Compute omega * 42 + (omega + 1) ^ omega.


Compute canon (omega ^ omega) 3.

Compute pp (canon (omega ^ omega) 3).

Compute pp (canon (omega ^ omega * 2) 3).

Compute pp (canon (omega ^ omega * 12) 3).


Compute canon (omega ^ omega * 12) 3.

Example canon_omega : canon omega 42 =  42.
Proof. trivial. Qed.

Compute pp (canon (omega ^ omega * 3) 42).

Example canon_ex : canon (omega ^ omega * 3) 42 =
                   omega ^ omega * 2 + omega ^ 42.
Proof. reflexivity.  Qed.

Example canon_ex' :  canon (tower 2) 3 = phi0 3.
Proof.  reflexivity.  Qed.

Example canon_ex'' :  canon (tower 4) 3 = phi0 (phi0 (phi0 3)).
Proof.  reflexivity.  Qed.

Example canon_ex3 : canon (omega ^ omega + 2) 42 = omega ^ omega + 1.
Proof.  reflexivity.  Qed.



(* some tests ... *)

Goal omega * phi0 omega = phi0 omega.
Proof.  reflexivity. Qed.

Goal phi0 omega * FS 9 + phi0(FS 1) * FS 2 + omega * FS  7 =
      omega * ((phi0 omega * FS 9 + omega * FS 2 + FS  6) + FS 0).
Proof. trivial. Qed.


Goal canon (phi0 (phi0 omega)) 3 = phi0 (phi0 (FS 2)).
Proof.   trivial. Qed.


Goal canon (phi0 (omega * FS 1) + phi0 (omega + FS 1) * FS 1) 4 =
phi0 (omega * FS 1) + phi0 (omega + FS 1) + phi0 (omega + FS 0) * FS 3.
Proof.  reflexivity. Qed.


Example ex: canon (omega^omega^omega) 42 = omega^(omega^42).
Proof. trivial. Qed.


Example E1 : 42 * omega < omega + 1.
Proof.  easy.   Qed.

Recursive Extraction canon_limit_strong.


Section Example2.

  Remark R1 : nf (omega^omega^omega).
  Proof. auto with T1.  Qed. 

  Remark R2 : is_limit (omega^omega^omega) = true.
  Proof. reflexivity.  Qed.

  Remark R3 : omega ^ (omega * 50) < (omega^omega^omega).
  Proof.
    compute; auto with bool.
  Qed.
  
 
End Example2.

Example E1' : lt (ocons omega 56 zero) (tower 3).
Proof. reflexivity. Qed.

Example E2 : ~ lt (tower 3) (tower 3).
 discriminate. 
Qed.



Example ten : T1 := 10.

Compute is_limit omega.




Compute is_succ 42.


Open Scope E0_scope.
Example E3:  Zero < omega.
  compute; firstorder.
Qed.


Open Scope t1_scope.


Fixpoint find_approximant alpha beta i fuel :=
  match compare (canon  alpha i) beta with
    Gt | Eq => Some i
  | Lt => match fuel with 0 => None |
                     S f => find_approximant alpha beta (S i) f
          end
  end.


Compute find_approximant (phi0 omega) (omega ^ 5 + 6) 0 7.

Compute find_approximant (phi0 omega * 3) (omega ^ 4 + 3)%t1 0 6.

Require Import List.

Fixpoint get_path alpha beta rev_path fuel :=
  match compare alpha beta with
    Datatypes.Eq => Some (rev rev_path)
  | Datatypes.Lt => None
  | Datatypes.Gt => match fuel with
            O => None
          | S f =>
            match find_approximant alpha beta 0 fuel with
              Some i => get_path (canon alpha i) beta (i::rev_path) f
            | None => None
            end
          end
  end.


           

Section Get_path_examples.

  Let x := (phi0 omega * 3).
  Let y :=  omega ^ 4 + 3.

 Compute
   get_path x y  nil 67.

 (*= Some (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 5 :: 2 :: 1 :: 1 :: 1 :: 3 :: nil)
     : option (list nat)
  *)


Fixpoint follow_path p alpha :=
  match p with nil => alpha
          | i :: p' => follow_path p' (canon alpha i)
  end.

Compute compare y (follow_path (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 5 :: 2 :: 1 :: 1 :: 1 :: 3 :: nil) x).


Compute (follow_path (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 5 :: 2 :: 1 :: 1 :: 1 :: 3 :: nil) x).


Compute standard_gnaw 1 (phi0 omega * 3) 12.

End Get_path_examples.

(*

 = ocons omega 0
         (ocons (FS 3) 4 (ocons (FS 2) 5 (ocons (FS 1) 6 (ocons one 7 (FS 7)))))
 *)

Goal standard_gnaw 1 (phi0 omega * 3) 12 =
phi0 omega + omega  ^ 4 * 5 + omega ^ 3 * 6 + omega ^ 2 * 7 + omega * 8 + 8.
  reflexivity.

Qed.


Compute pp (standard_gnaw 1 (phi0 omega * 3) 12).

Section Typical_transfinite_induction.
  Variables (X: T1 -> Type)
            (alpha  :  T1).
  Lemma L : X alpha.
  Proof.
    transfinite_induction alpha.
    clear alpha; intros alpha IHalpha.
  
  Abort.  (* It was just a demo *)
End Typical_transfinite_induction.

Module infinity.

  Definition f (alpha: T1) (i: nat) := alpha + S i.

 
  (* to do : use the monadic notation *)
  
           
  Definition opt {A B:Type} (f : A -> B) (a_opt: option A) :=
    match a_opt  with
      Some a => Some (f a)
    | _ => None
    end.


  Notation "z '<---'  x ';' e2 " :=
  (opt   (fun z => e2) x)
    (right associativity, at level 60).


   Fixpoint g0 (lambda alpha : T1) (i n: nat) :=
     match n with
       0%nat => None
     | S p => let gamma := canonS lambda i  in
              if lt_b  alpha gamma
              then Some gamma
              else g0 lambda alpha (S i) p
     end.

   Definition  g (lambda alpha : T1) (n: nat) :=
     if (andb (is_limit lambda) (lt_b alpha lambda))
     then g0 lambda alpha 1 n
     else None.
   

   Compute pp (f omega 3).
   
Compute  x <---  (g (omega ^ omega) (omega ^ 2 * 78 + omega) 1) ; pp x.
Compute  x <---  (g (omega ^ omega) (omega ^ 2 * 78 + omega) 2) ; pp x.
Compute  x <--- (g (omega ^ omega) (omega ^ 2 * 78 + omega) 3) ; pp x.


Compute x <--- (g (omega ^ omega) (omega ^ 4 * 78 + omega) 5); pp x.

Compute pp (gnawS  (omega ^ omega) (repeat 2 15)).

Compute pp (gnawS  (omega ^ omega) (repeat 2 55)).

Compute pp (gnawS  (omega^omega)  (repeat 4 100)).
(*
 = (omega ^ 4 * 4 + omega ^ 3 * 4 + omega ^ 2 + omega * 4 + 4)%pT1
     : ppT1

 *)

Compute pp (gnawS (omega^omega)  (repeat 3 100)).
(*
 = (omega ^ 3 * 2 + omega ^ 2 * 3 + omega + 4)%pT1
     : ppT1
 *)
Compute pp (gnawS (omega^omega)  (repeat 3 200)).
(*
 = (omega ^ 3 + omega ^ 2 * 2 + omega * 3)%pT1
     : ppT1

 *)


Section alpha_beta.

  Variables alpha beta : T1.
  Hypothesis Hlt : alpha < beta.
  Hypothesis Hlim : is_limit beta.

  Lemma Lf : forall i :  nat,  alpha < f alpha i < beta.
  Proof with eauto with T1.
  split.
  - unfold f; induction i.
   + rewrite <- succ_is_plus_one; apply LT_succ ...
   + rewrite <- succ_of_plus_finite ...
     apply LT_trans with (alpha + S i) ...
     apply LT_succ ...
  - induction i.
    + unfold f;simpl; rewrite <- succ_is_plus_one ...
      apply succ_lt_limit ...
    + unfold f; rewrite <- succ_of_plus_finite ...
     apply succ_lt_limit; eauto with T1.
  Qed.

  Lemma Lf2 : forall i, f alpha i < f alpha (S i).
  Proof with eauto with T1.
    intro i; unfold f;
    repeat rewrite <- succ_of_plus_finite ...
    apply LT_succ ...
    apply succ_nf, plus_nf ...
    destruct i ...
  Qed.

End alpha_beta.

Check Lf2.


End infinity.
