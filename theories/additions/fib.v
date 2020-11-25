(** author Yves Bertot, Inria  *)


Require Import Extraction.
Require Import ZArith Lia.

From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint fib (n : nat) :=
  if n is S (S p as p') then fib p + fib p' else 1.

Fixpoint fibt (n : nat) (acc1 acc2 : nat) : nat :=
  if n is S p then fibt p (acc2 + acc1) acc1 else acc1.

Fixpoint Zfibt (n : nat) (acc1 acc2 : Z) : Z :=
  if n is S p then Zfibt p (Z.add acc2 acc1) acc1 else acc1.

Lemma fibt_aux (n k: nat) : fibt n (fib k.+1) (fib k) = fib (n + k).+1.
Proof.
elim: n k => [ | n Ih] k.
  by [].
rewrite -[fibt n.+1 _ _]/(fibt n (fib k.+2) (fib k.+1)).
rewrite Ih.
by rewrite addnS addSn.
Qed.

Lemma fibtP (n : nat) : fibt n 1 0 = fib n.
Proof.
case: n => [ | p].
  by [].
rewrite [LHS]/= add0n -[in RHS](addn0 p).
by rewrite -fibt_aux.
Qed.

Fixpoint bits p acc : list bool :=
  match p with
  | xH => true :: acc
  | xI p => bits p (true :: acc)
  | xO p => bits p (false :: acc)
  end.

Lemma bits_cat p a : bits p a = bits p [::] ++ a.
Proof.
elim: p a => [ p Ih | p Ih | ] /= a;
  rewrite ?(Ih (_ :: a)) ?(Ih (_ :: nil)) -?catA //.
Qed.

Lemma bitsP p :
  Pos.to_nat p =
  \sum_(i < size (bits p [::])) nth false (bits p [::])
      (size (bits p [::]) - 1 - i) * 2 ^ i.
Proof.
have body_simp p' b:
  forall i : 'I_(size (bits p' [::])),
    true ->
    nth false (bits p' [::] ++ [:: b]) (size (bits p' [::]) - bump 0 i) *
    2 ^ bump 0 i =
    2 * (nth false (bits p' [::]) (size (bits p' [::]) - 1 - i) * 2 ^ i).
  move=> i _; rewrite /bump leq0n add1n (mulnC 2) -mulnA -expnSr -subnDA.
  rewrite add1n nth_cat.
  set e := (X in if X then _ else _).
  have -> // : e.
  rewrite /e {e}; case: i => [ i] /=; case: (size _) => // n _.
  by rewrite subSS ltnS leq_subr.
elim:p => [ p IH | p IH | ].
    rewrite /= Pos2Nat.inj_xI multE bits_cat size_cat /= addn1.
    rewrite [RHS]big_ord_recl subSS 2!subn0 expn0 muln1.
    rewrite nth_cat ltnn subnn /= add1n; congr (_.+1).
    rewrite (eq_bigr _ (body_simp p true)).
    by rewrite IH -big_distrr.
  rewrite /= Pos2Nat.inj_xO multE bits_cat size_cat /= addn1.
  rewrite [RHS]big_ord_recl subSS 2!subn0 expn0 muln1.
  rewrite nth_cat ltnn subnn /=.
  rewrite (eq_bigr _ (body_simp p false)).
  by rewrite IH -big_distrr.
by rewrite /= big_ord_recl big_ord0.
Qed.

Section with_matrices.

Variable R : comUnitRingType.

Import GRing.Theory.
Open Scope ring_scope.

Definition ZtoR (x : Z) : R :=
  if (Z.ltb x 0) then
    -(Z.abs_nat (-x))%:R else (Z.abs_nat x)%:R.

Lemma ZtoRD (x y : Z) : ZtoR (x + y) = ZtoR x + ZtoR y.
Proof.
rewrite /ZtoR.
case: ifP => [/Z.ltb_lt lt0 | /Z.ltb_ge ge0].
  case: ifP => [/Z.ltb_lt xlt0 | /Z.ltb_ge xge0 ].
    case: ifP => [/Z.ltb_lt ylt0 | /Z.ltb_ge yge0].
      rewrite -!mulNrn -mulrnDr; congr (_ *+ _).
      rewrite Z.opp_add_distr Zabs2Nat.inj_add ?plusE //.
        rewrite Z.opp_nonneg_nonpos.
        by apply: Z.lt_le_incl.
      by apply /Z.opp_nonneg_nonpos/Z.lt_le_incl.
    rewrite -!mulNrn -[X in _ + X *+ _]opprK.
    rewrite (mulNrn (-1)).
    rewrite -mulrnBr; last by apply/leP; lia.      
    rewrite -minusE.
    rewrite -Zabs2Nat.inj_sub; last by lia.
    by rewrite Z.opp_add_distr.
  case: ifP => [/Z.ltb_lt ylt0 | /Z.ltb_ge yge0].
    rewrite -!mulNrn -[X in X *+ _ + _]opprK.
    rewrite (mulNrn (-1)).
    rewrite addrC -mulrnBr; last by apply/leP; lia.
    rewrite -minusE.
    rewrite -Zabs2Nat.inj_sub; last by lia.
    by rewrite Z.add_comm Z.opp_add_distr.
  suff : False by [].
  lia.
case: ifP => [/Z.ltb_lt xlt0 | /Z.ltb_ge xge0 ].
  case: ifP => [/Z.ltb_lt ylt0 | /Z.ltb_ge yge0].
    suff : False by [].
    lia.
  rewrite addrC -mulrnBr; last by apply/leP; lia.
  rewrite -minusE -Zabs2Nat.inj_sub; last by lia.
  by rewrite Z.sub_opp_r Z.add_comm.
case: ifP => [/Z.ltb_lt ylt0 | /Z.ltb_ge yge0].
  rewrite -mulrnBr; last by apply/leP; lia.
  rewrite -minusE -Zabs2Nat.inj_sub; last by lia.
  by rewrite Z.sub_opp_r Z.add_comm.
rewrite -mulrnDr.
by rewrite -plusE -Zabs2Nat.inj_add.
Qed.
  
Lemma ZtoRM x y : ZtoR (x * y) = ZtoR x * ZtoR y.
Proof.
rewrite /ZtoR.
case: ifP => [/Z.ltb_lt lt0 | /Z.ltb_ge ge0].
  case: ifP => [/Z.ltb_lt xlt0 | /Z.ltb_ge xge0].
    case: ifP => [/Z.ltb_lt ylt0 | /Z.ltb_ge yge0].
      suff : Z.lt 0 (x * y) by lia.
      by apply Z.mul_neg_neg.
    rewrite !mulNr mulr_natl.
    rewrite -mulrnA.
    rewrite !Zabs2Nat.abs_nat_spec !Z.abs_opp Z.abs_mul.
    rewrite Z2Nat.inj_mul; auto with zarith.
    by rewrite multE mulnC.
  case: ifP => [/Z.ltb_lt ylt0 | /Z.ltb_ge yge0].
    rewrite mulr_natl.
    rewrite mulNrn -mulrnA.
    rewrite !Zabs2Nat.abs_nat_spec !Z.abs_opp Z.abs_mul.
    rewrite Z2Nat.inj_mul; auto with zarith.
    by rewrite multE mulnC.
  suff : Z.le 0 (x * y) by lia.
  by apply Z.mul_nonneg_nonneg.
case: ifP => [/Z.ltb_lt xlt0 | /Z.ltb_ge xge0].
  case: ifP => [/Z.ltb_lt ylt0 | /Z.ltb_ge yge0].
    rewrite !mulNr mulr_natl.
    rewrite mulNrn opprK.
    rewrite -mulrnA.
    rewrite !Zabs2Nat.abs_nat_spec !Z.abs_opp Z.abs_mul.
    rewrite Z2Nat.inj_mul; auto with zarith.
    by rewrite multE mulnC.
  have [/Z.ltb_lt ygt0 | /negbTE/Z.ltb_ge yeq0] := boolP (Z.ltb 0 y).
    suff : Z.lt (x * y) 0 by lia.
    by apply Z.mul_neg_pos.
  have ->/= : y = Z0 by lia.
  by rewrite mulr0 Z.mul_0_r.
have [/Z.ltb_lt ygt0 | /negbTE/Z.ltb_ge yeq0] := boolP (Z.ltb 0 x); last first.
  have -> /= : x =Z0 by lia.
  by rewrite mul0r.
case: ifP => [/Z.ltb_lt ylt0 | /Z.ltb_ge yge0].
  suff : Z.lt (x * y) 0 by lia.
  by apply Z.mul_pos_neg.
rewrite mulr_natl.
rewrite -mulrnA.
rewrite !Zabs2Nat.abs_nat_spec Z.abs_mul.
rewrite Z2Nat.inj_mul; auto with zarith.
by rewrite multE mulnC.
Qed.

Lemma iter_mul (n : nat) (m v : 'M[R]_2) :
  iter n [eta *%R m] v = m ^+ n * v.
Proof.
elim: n => [ | n Ih].
  by rewrite /= expr0 mul1r.
by rewrite /= Ih mulrA exprS.
Qed.

(* 1 1
   1 0 *)
Definition fibm : 'M[R]_2 :=
  \matrix_(i, j) if (val i == 1%N) && (val j == 1%N) then 0%R else 1%R.

Lemma fibmP n : fibm ^+ n.+2 =
  \matrix_(i, j) 
     if (val i == 0%N) && (val j == 0%N) then (fib n.+2)%:R else
     if ((val i + val j == 1)%N) then (fib n.+1)%:R else
      (fib n)%:R.
Proof.
elim: n => [ | n Ih].
  rewrite /=.
  by apply/matrixP=> [][[ | [ | i]] b_i][[ | [ | j]] b_j] //=;
  rewrite mxE /= expr2 mxE /fibm 2!big_ord_recr /= big_ord0;
    rewrite !mxE /= ?(add0r, addr0, mulr1, mul1r, mul0r).
  rewrite exprS Ih.
  have [fn1 fn1P] : exists fn1, fn1 = fib n.+1 by exists (fib n.+1).
  have [fn2 fn2P] : exists fn2, fn2 = fib n.+2 by exists (fib n.+2).
  have [fn3 fn3P] : exists fn3, fn3 = fib n.+3 by exists (fib n.+3).
  rewrite -!(fn1P, fn2P, fn3P).
  apply/matrixP=> [][[ | [ | i]] b_i][[ | [ | j]] b_j] //=;
 rewrite !mxE /= 2!big_ord_recr /= big_ord0 add0r /= !mxE /=
 ?(add0r, addr0, mulr1, mul1r, mul0r) -?natrD //.
 by rewrite fn2P fn1P fn3P addnC.
by rewrite fn2P fn1P addnC.
Qed.

(* Represent 2x2 matrices by lists of 4 coefficients, given line by line *)

Definition m4lval (l : seq Z) (i j : nat) :=
  nth Z0 l (j + 2 * i).

Definition m4lmx (l : seq Z) : 'M[R]_2 :=
  \matrix_(i, j) (ZtoR (m4lval l i j)).

Definition m4lmul (l1 l2 : seq Z) :=
  (Z.add (m4lval l1 0 0 * m4lval l2 0 0) (m4lval l1 0 1 * m4lval l2 1 0)) ::
  (Z.add (m4lval l1 0 0 * m4lval l2 0 1) (m4lval l1 0 1 * m4lval l2 1 1)) ::
  (Z.add (m4lval l1 1 0 * m4lval l2 0 0) (m4lval l1 1 1 * m4lval l2 1 0)) ::
  (Z.add (m4lval l1 1 0 * m4lval l2 0 1) (m4lval l1 1 1 * m4lval l2 1 1)) :: nil.

Open Scope Z_scope.
Definition m4lfib :=
  [:: 1; 1;
      1; 0].

Close Scope Z_scope.

(* Represent symetric 2x2 matrices by list of 3 coefficients, given in order
  (0,0), (1,1), (0,1). *)

Definition m3lmx (l : seq Z) : 'M[R]_2 :=
  \matrix_(i, j)
   if (i == j) then
     ZtoR (nth Z0 l i)
   else
     ZtoR (nth Z0 l 2).

Definition m3lmul (l1 l2 : seq Z) :=
  (Z.add (nth Z0 l1 0 * nth Z0 l2 0) (nth Z0 l1 2 * nth Z0 l2 2)) ::
  (Z.add (nth Z0 l1 2 * nth Z0 l2 2) (nth Z0 l1 1 * nth Z0 l2 1)) ::
(Z.add (nth Z0 l1 0 * nth Z0 l2 2) (nth Z0 l1 2 * nth Z0 l2 1)) :: nil.

Definition m3lfib := [:: Z.pos xH ; Z0; Z.pos xH].

(* This code is correct, but hot tail recursive. *)
Fixpoint fastexp (m : list Z) (p : positive) : list Z :=
  match p with
  | xH => m
  | xI p => 
    let r := fastexp m p in
    m3lmul (m3lmul r r) m
  | xO p =>
    let r := fastexp m p in
      m3lmul r r
  end.

(* This code is wrong, the bits are not processed in the right order. *)
Fixpoint fastexp2 (m : list Z) (p : positive) (acc : list Z) : list Z :=
  match p with
  | xH => acc
  | xO p => fastexp2 m p (m3lmul acc acc)
  | xI p => fastexp2 m p (m3lmul m (m3lmul acc acc))
  end.

(* This is my best solution. *)
Definition fastexp3 {A : Type} (mul : A -> A -> A)
  (m : A) :=
  fix f (l : list bool) (acc : A) : A :=
  match l with
  | nil => acc
  | true :: l => f l (mul (mul acc acc) m)
  | false :: l => f l (mul acc acc)
  end.

Definition my_pow {A : Type} (mul : A -> A -> A) (m : A)
  (p : positive) 
  : A :=
  fastexp3 mul m (behead (bits p nil)) m.

Definition m3lid := [:: Z.pos xH; Z0; Z0; Z.pos xH].

Definition slowexp (m : list Z) p :=
  Pos.iter (m3lmul m) m3lid p.

Compute slowexp m3lfib 12.

Compute my_pow m3lmul m3lfib 12.

Compute Zfibt 12 1 0.
Compute all id
  (map (fun x => Z.eqb (Z.of_nat (fib x)) (Zfibt x 1 0)) (iota 1 12)).

Definition binary_power_mult (mul : list Z -> list Z -> list Z) :
  list Z -> list Z -> positive -> list Z :=
  fix f (x a : list Z) (p : positive) : list Z :=
  match p with
  | xH => mul a x
  | xO q => f (mul x x) a q
  | xI q => f (mul x x) (mul a x) q
end.

Definition fastexp4 (mul : list Z -> list Z -> list Z)
  : list Z -> positive -> list Z :=
  fix f (x : list Z) (p : positive) :=
  match p with
  | xH => x
  | xO q => f (mul x x) q
  | xI q => binary_power_mult mul (mul x x) x q
  end.

Lemma m3lmulP l1 l2:
  GRing.comm (m3lmx l1) (m3lmx l2) ->
  m3lmx (m3lmul l1 l2) = m3lmx l1 * m3lmx l2.
Proof.
move=> hcomm.
apply/matrixP=> [][ [ | [| i]] ip] [ [ | [| j]] jp] //=;
  rewrite /m3lmx /m3lmul !mxE;
  set a1 := nth Z0 l1 0;
  set b1 := nth Z0 l1 2;
  set d1 := nth Z0 l1 1;
  set a2 := nth Z0 l2 0;
  set b2 := nth Z0 l2 2;
  set d2 := nth Z0 l2 1;
  rewrite /=;
  rewrite !big_ord_recr /= big_ord0 /= add0r /=;
  rewrite !mxE; cbn -[nth];
  rewrite -/a1 -/a2 -/b1 -/b2 -/d1 -/d2 /=;
  rewrite ?(ZtoRD, ZtoRM).
apply erefl.
apply erefl.
move: hcomm => /matrixP/(_ ord0 (inord 1)).
  rewrite !mxE 2!big_ord_recr big_ord0 /= add0r.
  rewrite /m3lmx !mxE -/a1 -/a2 -/b1 -/b2 -/d1 -/d2 /=.
  rewrite -!(inj_eq val_inj) /= inordK //=.
  rewrite 2!big_ord_recr big_ord0 /= add0r.
  rewrite /m3lmx !mxE -/a1 -/a2 -/b1 -/b2 -/d1 -/d2 /=.
  rewrite -!(inj_eq val_inj) /= inordK //= => ->.
  by congr (_ + _); rewrite mulrC.
apply erefl.
Qed.

Lemma m3lfibP : m3lmx m3lfib = fibm.
Proof.
by apply/matrixP=> [][[ | [ | i]] iP] [[ | [ | j]] jP] //; rewrite !mxE.
Qed.

Lemma iter_comm {A : Type} (op : A -> A -> A) (e1 e2 : A)
  (assoc: associative op)(cm : op e1 e2 = op e2 e1) n :
  op e1 (iter n (op e1) e2) = op (iter n (op e1) e2) e1.
Proof.
elim: n => [ | n Ih] //.
by rewrite [in RHS]iterS -assoc -Ih -iterS.
Qed.

Lemma iter_combine  {A : Type} (op : A -> A -> A) (e1 e2 : A)
  (assoc: associative op)(cm : op e1 e2 = op e2 e1) n m :
  op (iter n (op e1) e2) (iter m (op e1) e2) =
  (iter (n + m) (op e1) (op e2 e2)).
Proof.
elim: m n => [ | m Ih] n.
  rewrite addn0 /=.
  elim:n => [| n Ih] //=.
  by rewrite -assoc; congr op.
by rewrite !iterS assoc -iter_comm // -iterS Ih addnS addSn.
Qed.

Lemma fastexp3P {A : Type} (op : A -> A -> A) (id e : A) (h l : nat)
  (v : list bool) (assoc : associative op) (cm : op id e = op e id)
  (idn : forall a, op id a = a):
  l = (\sum_(i < size v) nth false v (size v - 1 - i) * 2 ^ i)%N ->
  iter (h * 2 ^ size v + l) (op e) id =
  fastexp3 op e v (iter h (op e) id).
Proof.
elim: v h l => [| b v Ih] h l.
  rewrite /= big_ord0 => ->.
  by rewrite expn0 muln1 addn0.
rewrite /= big_ord_recr /=.
rewrite -subnDA subnn /=.
have body_simp : forall i : 'I_(size v), true ->
   (nth false (b :: v) ((size v).+1 - 1 - i) * 2 ^ i =
   nth false v (size v - 1 - i) * 2 ^ i)%N.
  move=> i _; congr (_ * _)%N.
  have -> // : ((size v).+1 - 1 - i = ((size v) - 1 - i).+1)%N.
  case: i =>[i]; case:(size v)=> // n ip /=.
  by rewrite subSS subn0 -subnDA add1n subSS subSn.
rewrite (eq_bigr _ body_simp) {body_simp}.
set l' := (l - b * 2 ^ size v)%N.
move=> lq.
have lq' : l' = (\sum_(i < size v) nth false v (size v - 1 - i) * 2 ^ i)%N.
  by rewrite /l' lq addnK.
have hlq : (h * 2 ^ (size v).+1 + l = (2 * h + b) * 2 ^ (size v) + l')%N.
  by rewrite expnS mulnA lq addnA addnAC -mulnDl -lq' (mulnC h).
rewrite hlq Ih; last by [].
clear -assoc cm idn.
case: b.
  congr (fastexp3 op e v).
  rewrite -!assoc -iter_comm // assoc -iter_comm // -assoc.
  by rewrite iter_combine // idn -iterS addn1 mulSn mul1n.
congr fastexp3.
by rewrite iter_combine // idn addn0 mulSn mul1n.
Qed.

Lemma headbits p l : bits p l = true :: behead (bits p l).
Proof.
by elim: p l => [ p Ih | p Ih | ] l /=; rewrite 1?Ih.
Qed.

Lemma my_powP m p :
  @my_pow 'M[R]_2 *%R m p = m ^ Pos.to_nat p.
Proof.
have cm : 1 * m = m * 1.
  by rewrite mulr1 mul1r.
have:= @fastexp3P 'M[R]_2 *%R 1%R m 0 (Pos.to_nat p) (bits p [::])
   (@mulrA _) cm (fun a => mul1r a) (bitsP _).
rewrite /my_pow mul0n add0n /=.
rewrite [in RHS]headbits /= !mul1r => <-.
by rewrite iter_mul mulr1.
Qed.

Lemma my_pow_m3lmul m p :
  m3lmx (my_pow m3lmul m p) = my_pow *%R (m3lmx m) p.
Proof.
rewrite /my_pow.
have : GRing.comm (m3lmx m) (m3lmx m) by [].
elim: (behead (bits p [::])) {1 4 6}m => [ | b bits Ih] acc comh //.
rewrite /=.
have comma2m : GRing.comm (m3lmx acc * m3lmx acc) (m3lmx m).
  by rewrite /GRing.comm -mulrA comh !mulrA comh.
case: b; rewrite Ih !m3lmulP //.
  by rewrite /GRing.comm comma2m -(mulrA (m3lmx m)) comma2m.
Qed.

Definition m2lmul : list Z -> list Z -> list Z :=
 fun l1 l2 =>
 let a := nth Z0 l1 0 in
 let b := nth Z0 l1 1 in
 let c := nth Z0 l2 0 in
 let d := nth Z0 l2 1 in
   [:: Z.add (a * (c + d)) (b * c) ; Z.add (a * c) (b * d)].

Definition m2lmx (l : list Z) : 'M[R]_2 :=
  let a := nth Z0 l 0 in
  let b := nth Z0 l 1 in
  \matrix_(i, j) 
      if ((val i == 0%N) && (val j == 0%N)) then
         ZtoR (a + b)
      else if (i == j) then 
         ZtoR b
      else ZtoR a.

Definition m2lfib := [:: Zpos xH; Z0].

Lemma m2lfibP : m2lmx m2lfib = fibm.
Proof.
by apply/matrixP=> [] [[ | [ | i]] ip] [[ | [ | j]] jp] //;
 rewrite /m2lmx /m2lfib !mxE.
Qed.

Lemma m2lmulP m1 m2 :
  m2lmx (m2lmul m1 m2) = m2lmx m1 * m2lmx m2.
Proof.
rewrite /m2lmul /m2lmx.
set a := nth Z0 m1 0.
set b := nth Z0 m1 1.
set c := nth Z0 m2 0.
set d := nth Z0 m2 1.
apply/matrixP=> [][[ | [ | i]] ip] // [[ | [ | j]] jp] //.
      rewrite !mxE /= 2!big_ord_recr /= big_ord0 add0r !mxE /=.
      rewrite !(ZtoRM, ZtoRD) !(mulrDr, mulrDl) !addrA.
      rewrite !(addrAC _ (ZtoR a * ZtoR c)); congr (_ + _ + _).
      by rewrite addrAC.
    rewrite !mxE /= 2!big_ord_recr /= big_ord0 add0r !mxE /=.
    rewrite !(ZtoRM, ZtoRD) !(mulrDr, mulrDl).
    by rewrite addrAC.    
  rewrite !mxE /= 2!big_ord_recr /= big_ord0 add0r !mxE /=.
  by rewrite !(ZtoRM, ZtoRD) !(mulrDr, mulrDl).
rewrite !mxE /= 2!big_ord_recr /= big_ord0 add0r !mxE /=.
by rewrite !(ZtoRM, ZtoRD).
Qed.

Lemma my_pow_m2lmul m p :
  m2lmx (my_pow m2lmul m p) = my_pow *%R (m2lmx m) p.
Proof.
rewrite /my_pow.
elim: (behead (bits p [::])) {2 4}m => [ | b bits Ih] acc //=.
by case: b; rewrite Ih !m2lmulP.
Qed.

Lemma fibZ3P p :
  ZtoR (nth Z0 (my_pow m3lmul m3lfib p) 0) = (fib (Pos.to_nat p))%:R.
Proof.
rewrite [LHS](_ : _ = m3lmx (my_pow m3lmul m3lfib p) 0 0); last first.
  by rewrite /m3lmx mxE eqxx.
rewrite my_pow_m3lmul my_powP.
have : (1 <= Pos.to_nat p)%N.
  by apply/leP; rewrite -(Pos2Nat.inj_le xH); apply: Pos.le_1_l.
rewrite leq_eqVlt=> /orP[/eqP <- | pge2].
  by rewrite expr1z mxE eqxx.
case: (Pos.to_nat p) pge2 => [ | [ | {}p]] // _.
by rewrite m3lfibP /exprz fibmP mxE.
Qed.

Lemma fibZ2P p :
  ZtoR (nth Z0 (my_pow m2lmul m2lfib p) 0 +
        nth Z0 (my_pow m2lmul m2lfib p) 1) = (fib (Pos.to_nat p))%:R.
Proof.
rewrite [LHS](_ : _ = m2lmx (my_pow m2lmul m2lfib p) 0 0); last first.
  by rewrite /m3lmx mxE !eqxx andbT.
rewrite my_pow_m2lmul my_powP.
have : (1 <= Pos.to_nat p)%N.
  by apply/leP; rewrite -(Pos2Nat.inj_le xH); apply: Pos.le_1_l.
rewrite leq_eqVlt=> /orP[/eqP <- | pge2].
  by rewrite expr1z mxE eqxx.
case: (Pos.to_nat p) pge2 => [ | [ | {}p]] // _.
by rewrite m2lfibP /exprz fibmP mxE.
Qed.

Definition m3lpow (m : list Z) (n : positive) :=
  fastexp3 m3lmul m (behead (bits n nil)) m.

Definition m2lpow (m : list Z) (n : positive) :=
  fastexp3 m2lmul m (behead (bits n nil)) m.

End with_matrices.

Definition bigarg := 30000%positive.

Extraction "bigfib" Z.ltb Z.div_eucl Pos.iter Z.log2 fastexp4
  my_pow m4lmul m3lmul m2lmul m4lfib m3lfib m2lfib bigarg.

