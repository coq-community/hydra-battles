(** ** Proof of termination of all hydra battles *)

(** Pierre Casteran, Univ. Bordeaux, LaBRI, UMR 5800 *)


From hydras Require Export Hydra_Lemmas.
From hydras Require Import E0 Hessenberg.



(** ***  Converting any hydra into an ordinal less than 
  #epsilon0# $\epsilon_0$  

*)

Fixpoint m (h:Hydra) : T1 :=
  match h with head => T1.zero
             | node hs => ms hs
end 
with ms (s:Hydrae) :  T1 :=
  match s with  hnil => T1.zero
              | hcons h s' => phi0 (m h) o+  ms s'
 end.




(* for rewriting ... *)

Lemma ms_eqn2 :  forall h s, ms (hcons h s) = phi0 (m h) o+  ms s.
Proof.   reflexivity. Qed.

Lemma o_finite_mult_S_rw :
  forall n a, o_finite_mult (S n) a =  a o+ o_finite_mult n a.
Proof.   reflexivity.  Qed.

(**  The functions [m] and [ms] return well formed ordinals (less than epsilon0)
 *)

Theorem m_nf : forall h, nf (m h).
Proof.
  induction h using Hydra_rect2 
              with (P0 := fun s =>  nf (ms s)).
 -  destruct h; simpl; auto.
 - constructor.
 -  intros;  rewrite ms_eqn2; apply oplus_nf.
  + now apply nf_phi0.
  + assumption.
Qed.


Theorem ms_nf : forall s, nf (ms s).
Proof with auto with T1.
  induction s...
   rewrite ms_eqn2...
  apply oplus_nf...
  apply nf_phi0; now  apply m_nf.   
Qed.   

Hint Resolve m_nf nf_phi0 ms_nf : T1.

Lemma ms_eqn3 :  forall h n s,  ms (hcons_mult h  n s) =
                                o_finite_mult n (phi0 (m h)) o+ ms s.
Proof with auto with T1.
 induction n.
 - intros; simpl (hcons_mult h  0 s); simpl o_finite_mult.
   rewrite oplus_0_beta; reflexivity.
 -  intros; simpl hcons_mult;  rewrite ms_eqn2.
    rewrite o_finite_mult_S_rw, IHn, oplus_assoc ...
    apply o_finite_mult_nf ...
Qed. 

(** ** Monotonicity lemmas for S0, R1, etc . *)

Open Scope t1_scope.

Lemma S0_decr_0 :
  forall s s', S0  s s' -> T1.lt (ms s') (ms s).
Proof with auto with T1.
 induction 1.
 -  rewrite ms_eqn2;  apply oplus_lt2...
 -  repeat rewrite ms_eqn2; apply oplus_strict_mono_r ...
 Qed.


Lemma S0_decr :  forall s s', S0  s s' -> ms s' t1< ms s.
Proof.
  repeat split; auto with T1; now apply S0_decr_0.
Qed.

Lemma R1_decr_0 : forall h h',
                  R1 h h' -> T1.lt (m h') (m h).
Proof with auto with T1.
  destruct 1;  simpl;  destruct s, s'.
  -  inversion H.
  -  inversion H.
  -  rewrite ms_eqn2; apply lt_le_trans with (phi0 (m h))...
(*      +  simpl. constructor. *)
     +  apply oplus_le...
  -  now apply   S0_decr. (* simpl in H  en V8.6 ??? *)
Qed.

Lemma R1_decr : forall h h',
                  R1 h h' -> m h' t1< m h.
Proof.
  repeat split; auto with T1; now apply R1_decr_0.
Qed.


Lemma S1_decr_0 n:
  forall s s', S1 n s s' -> T1.lt (ms s') (ms s).
Proof with auto with T1.
  induction 1.
   -  rewrite  ms_eqn2.
      simpl hcons_mult.
      rewrite  ms_eqn2.
      rewrite ms_eqn3.
      rewrite oplus_assoc...
      apply oplus_strict_mono_l...
      apply oplus_nf...
      apply o_finite_mult_nf...
      rewrite <- o_finite_mult_S_rw.
      apply o_finite_mult_lt_phi0_1.
      now apply R1_decr.
      apply o_finite_mult_nf...
   -  repeat rewrite ms_eqn2 ...
      apply oplus_strict_mono_r ...
Qed.


Lemma S1_decr n:
  forall s s', S1 n s s' -> ms s' t1< ms s.
Proof.
  repeat split; auto with T1; now eapply S1_decr_0 with n.
Qed.

Lemma m_ms : forall s, m (node s) = ms s.
Proof. 
 destruct s; reflexivity.
Qed.

Lemma R2_decr_0 n : forall h h', R2 n h h' -> T1.lt (m h') (m h).
Proof with auto with T1.
  induction 1 using R2_ind2 with
  (P0 := fun s s' (H : S2 n s s') => T1.lt (ms s') (ms s))...
  - repeat rewrite m_ms.
    now  apply S1_decr with n.
  - now repeat rewrite m_ms.
  -  apply oplus_strict_mono_l ...
     
  - repeat rewrite ms_eqn2.
    apply oplus_strict_mono_r...
Qed.

Lemma R2_decr n : forall h h', R2 n h h' -> m h' t1<  m h.
Proof.
  repeat split; auto with T1; now eapply R2_decr_0 with n.
Qed.



Lemma round_decr : forall h h', h -1-> h' -> m h' t1< m h.
Proof.
  destruct 1 as [n [H | H]]. 
  -  now apply R1_decr.
  -  now apply R2_decr with n.
Qed.

Instance var (h:Hydra) : E0.
Proof.
  refine (@mkord (m h) _);  apply m_nf.
Defined.



Global Instance HVariant_0 : Hvariant T1_wf free m.
Proof.
 split; intros; eapply round_decr; eauto.
Qed.



Global Instance HVariant : Hvariant E0.Lt_wf free var.
Proof.
 split; intros; eapply round_decr; eauto.
Qed.


Theorem every_battle_terminates : Termination.
Proof. 
  red; apply Inclusion.wf_incl with (R2 := fun h h' =>  m h t1< m h').
   red; intros;  now apply round_decr.
   apply Inverse_Image.wf_inverse_image, T1_wf.
Qed.
