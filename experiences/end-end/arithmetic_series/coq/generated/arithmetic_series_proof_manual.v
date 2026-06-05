Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260604_165821_arithmetic_series Require Import arithmetic_series_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import arithmetic_series.
Local Open Scope sac.

Lemma arithmetic_series_sum_z_step :
  forall a d i,
    arithmetic_series_sum_z a d (i + 1) =
    arithmetic_series_sum_z a d i + (a + i * d).
Proof.
  intros.
  unfold arithmetic_series_sum_z.
  replace (i + 1 - 1) with i by lia.
  replace (d * (i + 1) * i) with (d * i * (i - 1) + (d * i) * 2) by lia.
  rewrite Z.div_add by lia.
  replace (i * d * 2 / 2) with (i * d).
  2:{
    symmetry.
    apply Z.div_mul.
    lia.
  }
  lia.
Qed.

Lemma proof_of_arithmetic_series_safety_wit_3 : arithmetic_series_safety_wit_3.
Proof.
  pre_process.
  match goal with
  | Hpre : arithmetic_series_pre _ _ _ |- _ =>
      pose proof Hpre as Hpre_keep;
      unfold arithmetic_series_pre in Hpre;
      destruct Hpre as [Hn [Hterm Hsum]]
  end.
  assert (0 <= i + 1 <= n_pre) as Hrange by lia.
  specialize (Hsum (i + 1) Hrange).
  rewrite arithmetic_series_sum_z_step in Hsum.
  assert (Hint : int_min <= sum + cur <= int_max).
  {
    rewrite H2, H3.
    exact Hsum.
  }
  entailer!.
Qed.

Lemma proof_of_arithmetic_series_safety_wit_4 : arithmetic_series_safety_wit_4.
Proof.
  pre_process.
  match goal with
  | Hpre : arithmetic_series_pre _ _ _ |- _ =>
      unfold arithmetic_series_pre in Hpre;
      destruct Hpre as [Hn [Hterm Hsum]]
  end.
  assert (0 <= i + 1 <= n_pre) as Hrange by lia.
  specialize (Hterm (i + 1) Hrange).
  unfold arithmetic_series_term_z in Hterm.
  assert (Hint : int_min <= cur + d_pre <= int_max).
  {
    rewrite H2.
    lia.
  }
  entailer!.
Qed.

Lemma proof_of_arithmetic_series_entail_wit_1 : arithmetic_series_entail_wit_1.
Proof.
  pre_process.
  match goal with
  | Hpre : arithmetic_series_pre _ _ _ |- _ =>
      pose proof Hpre as Hpre_keep;
      unfold arithmetic_series_pre in Hpre;
      destruct Hpre as [Hn [Hterm Hsum]]
  end.
  assert (Hsum0 : 0 = arithmetic_series_sum_z a_pre d_pre 0).
  {
    unfold arithmetic_series_sum_z.
    replace (d_pre * 0 * (0 - 1)) with 0 by ring.
    cbn.
    reflexivity.
  }
  entailer!.
Qed.

Lemma proof_of_arithmetic_series_entail_wit_2 : arithmetic_series_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  rewrite arithmetic_series_sum_z_step.
  lia.
Qed.

Lemma proof_of_arithmetic_series_return_wit_1 : arithmetic_series_return_wit_1.
Proof.
  pre_process.
  assert (Heq : i = n_pre) by lia.
  subst i.
  entailer!.
Qed.
