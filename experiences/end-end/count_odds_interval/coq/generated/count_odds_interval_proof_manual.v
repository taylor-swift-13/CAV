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
From SimpleC.EE.CAV.verify_20260605_055555v_count_odds_interval Require Import count_odds_interval_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma count_odds_interval_quot2_bounds:
  forall x, 0 <= x -> 0 <= x ÷ 2 <= x.
Proof.
  intros x Hx.
  destruct (Z.eq_dec x 0) as [Hx0 | Hx0].
  - subst. change (0 ÷ 2) with 0. lia.
  - split.
    + apply Z.quot_pos; lia.
    + assert (x ÷ 2 < x) by (apply Z.quot_lt; lia).
      lia.
Qed.

Lemma count_odds_interval_quot2_plus1_int_max:
  forall x, 0 <= x <= 2147483647 -> x ÷ 2 + 1 <= 2147483647.
Proof.
  intros x Hx.
  destruct (Z.eq_dec x 0) as [Hx0 | Hx0].
  - subst. change (0 ÷ 2) with 0. lia.
  - assert (x ÷ 2 < x) by (apply Z.quot_lt; lia).
    lia.
Qed.

Lemma proof_of_count_odds_interval_safety_wit_10 : count_odds_interval_safety_wit_10.
Proof.
  pre_process.
  sep_apply store_int_range.
  sep_apply store_int_range.
  Intros.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  assert (Hdiff : 0 <= high_pre - low_pre <= 2147483647) by lia.
  assert (Hq : 0 <= (high_pre - low_pre) ÷ 2 <= high_pre - low_pre)
    by (apply count_odds_interval_quot2_bounds; lia).
  assert (Hq1 : (high_pre - low_pre) ÷ 2 + 1 <= 2147483647)
    by (apply count_odds_interval_quot2_plus1_int_max; lia).
  entailer!.
Qed.

Lemma proof_of_count_odds_interval_safety_wit_11 : count_odds_interval_safety_wit_11.
Proof.
  pre_process.
  sep_apply store_int_range.
  sep_apply store_int_range.
  Intros.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  assert (Hdiff : 0 <= high_pre - low_pre <= 2147483647) by lia.
  assert (Hq : 0 <= (high_pre - low_pre) ÷ 2 <= high_pre - low_pre)
    by (apply count_odds_interval_quot2_bounds; lia).
  assert (Hq1 : (high_pre - low_pre) ÷ 2 + 1 <= 2147483647)
    by (apply count_odds_interval_quot2_plus1_int_max; lia).
  entailer!.
Qed.
