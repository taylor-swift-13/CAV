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
From SimpleC.EE.CAV.verify_20260608_125304_p135_can_arrange Require Import p135_can_arrange_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p135_can_arrange.
Local Open Scope sac.

Lemma proof_of_p135_can_arrange_entail_wit_1 : p135_can_arrange_entail_wit_1.
Proof.
  pre_process.
  unfold can_arrange_prefix, can_arrange_hit.
  entailer!.
Qed.

Lemma proof_of_p135_can_arrange_entail_wit_2_1 : p135_can_arrange_entail_wit_2_1.
Proof.
  pre_process.
  unfold can_arrange_prefix, can_arrange_hit in *.
  entailer!.
Qed.

Lemma proof_of_p135_can_arrange_entail_wit_2_2 : p135_can_arrange_entail_wit_2_2.
Proof.
  pre_process.
  unfold can_arrange_prefix, can_arrange_hit in *.
  destruct H7 as [Hi_range [Hmax_range [Hmax_case Hprefix]]].
  assert (Hnext:
    0 <= i + 1 <= Zlength input_l /\
    -1 <= max < i + 1 /\
    (max = -1 \/ 0 <= max < Zlength input_l /\ Znth max input_l 0 <= max) /\
    (forall j : Z,
      0 <= j < i + 1 ->
      0 <= j < Zlength input_l /\ Znth j input_l 0 <= j -> j <= max)).
  {
    split.
    - lia.
    - split.
      + lia.
      + split.
        * exact Hmax_case.
        * intros j HjRange HjHit.
          assert (j < i \/ j = i) by lia.
          destruct H7 as [Hlt | Heq].
          -- apply Hprefix; lia.
          -- subst j. lia.
  }
  entailer!.
Qed.

Lemma proof_of_p135_can_arrange_return_wit_1 : p135_can_arrange_return_wit_1.
Proof.
  pre_process.
  unfold can_arrange_prefix, can_arrange_hit, problem_135_spec in *.
  assert (i = arr_size_pre) by lia.
  subst i.
  destruct H6 as [Hi_range [Hmax_range [Hmax_case Hprefix]]].
  assert (Hspec:
    (max = -1 /\ (forall k : Z, ~ can_arrange_hit input_l k)) \/
    (exists k : Z,
      max = k /\
      can_arrange_hit input_l k /\
      (forall j : Z, can_arrange_hit input_l j -> j <= k))).
  {
    destruct Hmax_case as [Hmax_neg1 | Hmax_hit].
    - left.
      split; [exact Hmax_neg1 |].
      intros k Hhit.
      destruct Hhit as [Hk_range Hk_le].
      pose proof (Hprefix k) as Hkmax.
      assert (0 <= k < arr_size_pre) by lia.
      specialize (Hkmax H6 (conj Hk_range Hk_le)).
      lia.
    - right.
      exists max.
      split.
      + reflexivity.
      + split.
        * exact Hmax_hit.
        * intros j HjHit.
          destruct HjHit as [Hj_range Hj_le].
          apply Hprefix.
          -- rewrite <- H2 in Hj_range. lia.
          -- exact (conj Hj_range Hj_le).
  }
  entailer!.
Qed.
