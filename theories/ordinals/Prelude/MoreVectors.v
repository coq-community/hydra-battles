Require Export Bool Arith Vector Max Lia.
Import VectorNotations.

(** generalities on vectors *)

Arguments cons {A} _ {n}  _ .
Arguments nil {A}.

Definition Vid {A : Type} {n:nat} : t A n -> t A n :=
  match n with
    0 => fun v =>  []
  | S p => fun v => hd v :: tl v
  end.

(* The decomposition Lemma *)

Lemma Vid_eq : forall (n:nat) (A:Type)(v:t A n), v = Vid   v.
Proof.
 destruct v; reflexivity.
Defined.


Theorem t_0_nil : forall (A:Type) (v:t A 0), v = nil.
Proof.
 intros.
 change (nil (A:=A)) with (@Vid _  0 v). 
 apply Vid_eq.
Defined.


Theorem decomp :
  forall (A : Type) (n : nat) (v : t A (S n)),
  v = cons (hd v) (tl v).
Proof.
 intros.
 change (cons (hd v) (tl v)) with (@Vid _  (S n) v).
 apply Vid_eq.
Defined.

Lemma decomp1  {A : Type}  (v : t A 1):
  v = cons (hd v) (nil).
Proof.
 rewrite (decomp _ _ v); cbn. now rewrite (t_0_nil A (tl v)).
Qed.

Definition vector_double_rect : 
    forall (A:Type) (X: forall (n:nat),(t A n)->(t A n) -> Type),
        X 0 nil nil ->
        (forall n (v1 v2 : t A n) a b, X n v1 v2 ->
             X (S n) (cons a v1) (cons  b v2)) ->
        forall n (v1 v2 : t A n), X n v1 v2.
 induction n.
 intros; rewrite (t_0_nil _ v1); rewrite (t_0_nil _ v2).
 auto.
 intros v1 v2; rewrite (decomp _ _ v1);rewrite (decomp _ _ v2).
 apply X1; auto.
Defined.

Definition vector_triple_rect : 
  forall (A:Type)
         (X: forall (n:nat),
             t A n -> t A n -> t A n ->Type),
    X 0 nil nil nil ->
        (forall n (v1 v2 v3: t A n) a b c, X n v1 v2 v3->
             X (S n) (cons a v1) (cons  b v2)(cons c v3)) ->
        forall n (v1 v2 v3: t A n), X n v1 v2 v3.
 induction n.
 intros; rewrite (t_0_nil _ v1),(t_0_nil _ v2), (t_0_nil _ v3).
 auto.
 intros v1 v2 v3; rewrite (decomp _ _ v1), (decomp _ _ v2), (decomp _ _ v3).
 apply X1; auto.
Defined.


Fixpoint vector_nth (A:Type)(n:nat)(p:nat)(v:t A p){struct v}
                  : option A :=
  match n,v  with
    _   , nil  => None
  | 0   , cons  b  _  => Some b
  | S n', @cons  _  _ p'  v' => vector_nth A n'  p' v'
  end.

Arguments vector_nth {A } n {p}.


Lemma Forall_inv {A :Type}(P: A -> Prop)(n:nat)
      a  v  : Vector.Forall P (n:= S n) (Vector.cons a v)  ->
                P a  /\ Vector.Forall P v .
Proof.
  intro H. inversion H.
  assert (v0 = v) by
      (refine (Eqdep_dec.inj_pair2_eq_dec nat _  _ _ _ _ H2);
       apply eq_nat_dec).
 now subst.
Qed.

Lemma Forall2_inv {A B:Type}(P: A -> B -> Prop)(n:nat)
      a b v w : Vector.Forall2 P (n:=S n)
                               (Vector.cons a v)
                               (Vector.cons b w) ->
                P a b /\ Vector.Forall2 P v w.
Proof.
  intro H.
  inversion H.
  assert (v1 = v) by (refine (Eqdep_dec.inj_pair2_eq_dec nat _  _ _ _ _ H2);
       apply eq_nat_dec).
  assert (v2 = w) by (refine (Eqdep_dec.inj_pair2_eq_dec nat _  _ _ _ _ H5);
       apply eq_nat_dec).
  subst; auto.
 Qed.






(** calcule le vecteur f(from),f(from+1),f(from+2),...,f(from+n-1)  *)

Fixpoint vect_from_fun {A} (f :  nat ->  A) n from : t A n :=
  match n return t A n with
    0%nat => nil
  | S p => cons (f from) (vect_from_fun f p (S from))
  end.








(** experimentation sur la decomposition des vecteurs *)

Notation "'vfst'" := Vector.hd.
Notation "'vsnd' v" := (Vector.hd (Vector.tl v)) (at level 35).
Notation "'vthird' v" := (Vector.hd (Vector.tl (Vector.tl v))) (at level 35).
Notation "'vfourth' v" := (Vector.hd (Vector.tl (Vector.tl (Vector.tl v)))) (at level 35).


Lemma decomp2 {A}  :  forall v : Vector.t A 2,
    v = [Vector.hd v; Vector.hd (Vector.tl v)].
Proof.
  intro v;
    rewrite (decomp _ 1 v), (decomp _ _ (Vector.tl v)).
    simpl.
    rewrite (t_0_nil _ (Vector.tl (Vector.tl v))).
    reflexivity.
Defined. 

Lemma decompos2 {A} : forall v: Vector.t A 2, {a : A & {b : A | v = [a;b]}}.
  intros.
  rewrite  (decomp2 v).
  exists (Vector.hd v).
  now exists (Vector.hd (Vector.tl v)).
Defined.

Definition match2 {A B:Type} (f : A -> A -> B) (v: Vector.t A 2): B :=
  match   (decompos2 v )
            with existT _ x Hx =>
                 match Hx with exist _ y _ => f x y end end.


Definition Vec2_proj {A} (P2 : A -> A -> Prop) : Vector.t A 2 -> Prop.
intro v.
destruct (decompos2  v).
destruct s.
exact (P2 x x0).
Defined.

(*  Replaces a vector of dimension 2 with [a ; b] *)

Ltac vdec2 v a b :=
  let x := fresh a in
  let y :=fresh b in
  let tmp := fresh "tmp" in
  let e :=fresh "e" in 
    destruct (decompos2 v) as [x tmp]; destruct tmp as [y e]; subst v.



Lemma In_cases {A:Type}{n:nat} (v: t A (S n)) :
  forall x, In x v ->
            x = hd v \/ In x (tl v).
Proof.
  intros; rewrite (decomp _ _ v) in *.
  inversion H.
  - left; auto.
  - apply Eqdep_dec.inj_pair2_eq_dec in H3.
    + right; cbn; now subst.
    + decide equality.
Qed.


Lemma Forall_and {A:Type}(P: A -> Prop) {n:nat} (v: t A (S n)) :
  Forall P v -> P (hd v) /\ Forall P (tl v).
Proof.
  rewrite (decomp _ _ v); cbn.
  inversion 1; split; auto.
  apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; auto.
  decide equality. 
Qed.

(** For V8.11 *)

Lemma Forall_forall {A:Type}(P: A -> Prop) :
  forall {n:nat} (v: t A n) ,
    Forall P v <-> (forall a, In a v -> P a).
  Proof.
  induction n.
  -  intro v; rewrite (t_0_nil _ v).
     split.
     + inversion 2.
     + left.
  -   intro v; rewrite (decomp _ _ v); split.
      + intros H a H0; destruct (Forall_and   _ _ H ).
        destruct (In_cases _ _ H0) as [H3 | H3].
        * now subst.
        * cbn in H2; rewrite IHn in H2;  apply H2, H3.
      +  intros H;  right.
         * apply H; left.
         * rewrite IHn; auto.
           intros; apply H.
           right; auto.
Qed.




  (** Vectors of natural numbers *)

  (** Maximum of a vector of nat *)

Fixpoint max_v {n:nat} : forall (v: Vector.t nat n) , nat :=
  match n as n0 return (Vector.t nat n0 -> nat)
  with
    0 => fun v => 0
  | S p => fun (v : Vector.t nat (S p)) =>
             (max (Vector.hd v) (max_v  (Vector.tl v)))
  end. 

Lemma max_v_2 : forall x y,  max_v (x::y::nil) = max x y.
Proof.
  intros; cbn. now rewrite max_0_r.
Qed.

Lemma max_v_lub : forall n (v: t nat n) y,
    (Forall (fun x =>  x <= y) v) ->
    max_v v <= y.
Proof.
  induction n.  
  -  intros v; rewrite (t_0_nil _ v); cbn.
     intros; auto with arith.
  -   intros v; rewrite (decomp _ _ v); cbn.
      intros;  destruct (Forall_inv _ _ _  _ H). apply max_lub; auto. 
Qed.


Lemma max_v_ge : forall n (v: t nat n) y,
    In  y  v -> y <= max_v v.
Proof.
  induction n.  
  -  intros v; rewrite (t_0_nil _ v); cbn; inversion 1.
  -  intros v; rewrite (decomp _ _ v); cbn; intros; destruct (In_cases _ _ H).
     +  cbn in H0; subst; apply le_max_l. 
     + cbn in H0; specialize (IHn _ _ H0); lia.
Qed.


(*
Fixpoint vector_nth (A:Type)(n:nat)(p:nat)(v:t A p){struct v}
                  : option A :=
  match n,v  with
    _   , nil  => None
  | O   , cons  b  _  => Some b
  | S n', @cons  _  _ p'  v' => vector_nth A n'  p' v'
  end.
*)
