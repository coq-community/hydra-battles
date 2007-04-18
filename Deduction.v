Require Import Ensembles.
Require Import List.

Require Import folProof.
Require Import folProp.

Section Deduction_Theorem.

Variable L : Language.
Hypothesis lang_dec : language_decideable L.
Let formula_dec := formula_dec L lang_dec.

Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.
Let equal := equal L.
Let atomic := atomic L.
Let impH := impH L.
Let notH := notH L.
Let forallH := forallH L.
Let Prf := Prf L.
Let SysPrf := SysPrf L.

Theorem DeductionTheorem :
 forall (T : System) (f g : Formula) (prf : SysPrf (Add _ T g) f),
 SysPrf T (impH g f).
Proof.
assert
 (EasyCase :
  forall (F : Formulas) (g z : Formula),
  Prf nil z -> SysPrf (fun x : Formula => In x F /\ x <> g) (impH g z)).
intros.
set (A1 := IMP1 L z g) in *.
set (A2 := MP L _ _ _ _ A1 H) in *.
exists (nil ++ nil:list Formula).
exists A2.
intros.
elim H0.
assert
 (forall (F : Formulas) (f g : Formula),
  Prf F f -> SysPrf (fun x : Formula => In x F /\ x <> g) (impH g f)).
intros.
induction  H
 as
  [A|
   Axm1
   Axm2
   A
   B
   H1
   HrecH1
   H0
   HrecH0|
   Axm
   A
   v
   n
   H
   HrecH|
   A
   B|
   A
   B
   C|
   A
   B|
   A
   v
   t|
   A
   v
   n|
   A
   B
   v|
   |
   |
   |
   R|
   f].
induction (formula_dec A g).
rewrite a.
set (A1 := IMP2 L g (impH g g) g) in *.
set (A2 := IMP1 L g (impH g g)) in *.
set (A3 := MP L _ _ _ _ A1 A2) in *.
set (A4 := IMP1 L g g) in *.
set (A5 := MP L _ _ _ _ A3 A4) in *.
exists ((nil ++ nil) ++ nil:list Formula).
exists A5.
contradiction.
set (A1 := AXM L A) in *.
set (A2 := IMP1 L A g) in *.
set (A3 := MP L _ _ _ _ A2 A1) in *.
exists (nil ++ A :: nil).
exists A3.
simpl in |- *.
intros.
induction  H as [H| H].
rewrite <- H.
unfold Ensembles.In in |- *.
auto.
elim H.
induction  HrecH0 as (x, H).
induction  H as (x0, H).
induction  HrecH1 as (x1, H2).
induction  H2 as (x2, H2).
set (A1 := IMP2 L g A B) in *.
set (A2 := MP L _ _ _ _ A1 x2) in *.
set (A3 := MP L _ _ _ _ A2 x0) in *.
exists ((nil ++ x1) ++ x).
exists A3.
simpl in |- *.
intros.
unfold Ensembles.In in |- *.
induction (in_app_or _ _ _ H3).
induction (H2 _ H4).
split.
apply in_or_app.
auto.
auto.
induction (H _ H4).
split.
apply in_or_app.
auto.
auto.
induction  HrecH as (x, H0).
induction  H0 as (x0, H0).
induction (In_dec formula_dec g Axm).
assert (~ In v (freeVarListFormula L x)).
clear x0 H.
induction  x as [| a0 x Hrecx].
auto.
unfold not in |- *; intro.
simpl in H.
induction (in_app_or _ _ _ H).
assert
 (Ensembles.In (fol.Formula L) (fun x : Formula => In x Axm /\ x <> g) a0).
apply H0.
simpl in |- *; tauto.
unfold Ensembles.In in H2.
induction  H2 as (H2, H3).
elim n.
eapply In_freeVarListFormula.
apply H1.
auto.
elim Hrecx.
intros.
apply H0.
simpl in |- *; tauto.
assumption.
assert (~ In v (freeVarFormula L g)).
unfold not in |- *; intros; elim n.
eapply In_freeVarListFormula.
apply H2.
assumption.
set (A1 := GEN L _ _ _ H1 x0) in *.
set (A2 := FA3 L g A v) in *.
set (A3 := MP L _ _ _ _ A2 A1) in *.
set (A4 := FA2 L g v H2) in *.
set (A5 := IMP2 L g (forallH v g) (forallH v A)) in *.
set (A6 := IMP1 L (impH (forallH v g) (forallH v A)) g) in *.
set (A7 := MP L _ _ _ _ A6 A3) in *.
set (A8 := MP L _ _ _ _ A5 A7) in *.
set (A9 := MP L _ _ _ _ A8 A4) in *.
exists ((nil ++ nil ++ nil ++ x) ++ nil).
exists A9.
clear A9 A8 A7 A6 A5 A4 A3 A2 A1.
simpl in |- *.
intros.
apply H0.
induction (in_app_or _ _ _ H3).
auto.
elim H4.
set (A1 := GEN L _ _ _ n H) in *.
set (A2 := IMP1 L (forallH v A) g) in *.
set (A3 := MP L _ _ _ _ A2 A1) in *.
exists (nil ++ Axm).
exists A3.
simpl in |- *.
intros.
unfold Ensembles.In in |- *.
split.
auto.
unfold not in |- *; intros; elim b.
rewrite H2 in H1.
auto.
apply EasyCase.
apply (IMP1 L).
apply EasyCase.
apply (IMP2 L).
apply EasyCase.
apply (CP L).
apply EasyCase.
apply (FA1 L).
apply EasyCase.
apply (FA2 L); assumption.
apply EasyCase.
apply (FA3 L).
apply EasyCase.
apply (EQ1 L).
apply EasyCase.
apply (EQ2 L).
apply EasyCase.
apply (EQ3 L).
apply EasyCase.
apply (EQ4 L).
apply EasyCase.
apply (EQ5 L).
intros.
induction  prf as (x, H0).
induction  H0 as (x0, H0).
induction (H _ _ g x0).
induction  H1 as (x2, H1).
exists x1.
exists x2.
intros.
unfold Ensembles.In in H1.
induction (H1 _ H2).
assert (Ensembles.In (fol.Formula L) (Add (fol.Formula L) T g) g0).
auto.
induction  H5 as [x3 H5| x3 H5].
assumption.
induction  H5 as [].
elim H4.
reflexivity.
Qed.

End Deduction_Theorem.