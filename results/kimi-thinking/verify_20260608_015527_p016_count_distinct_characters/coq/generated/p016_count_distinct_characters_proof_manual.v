Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260608_015527_p016_count_distinct_characters Require Import p016_count_distinct_characters_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p016_count_distinct_characters.
Local Open Scope sac.

Lemma proof_of_p016_count_distinct_characters_safety_wit_25 : p016_count_distinct_characters_safety_wit_25.
Proof.
  pre_process.
  split_pure_spatial.
  - dump_pre_spatial. lia.
  - cancel.
Qed.

Lemma proof_of_p016_count_distinct_characters_safety_wit_27 : p016_count_distinct_characters_safety_wit_27.
Proof.
  pre_process.
  split_pure_spatial.
  - dump_pre_spatial. lia.
  - cancel.
Qed.

Lemma proof_of_p016_count_distinct_characters_safety_wit_28 : p016_count_distinct_characters_safety_wit_28.
Proof.
  pre_process.
  split_pure_spatial.
  - dump_pre_spatial. lia.
  - cancel.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_1 : p016_count_distinct_characters_entail_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold count_distinct_lower_upto, distinct_lower_prefix, collect_lower.
      simpl. reflexivity.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_2_1 : p016_count_distinct_characters_entail_wit_2_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold lower_seen_state, lower, is_upper_zb.
      assert (Znth i (app l (cons 0 nil)) 0 = Znth i l 0).
      { rewrite app_Znth1 by lia. reflexivity. }
      rewrite H1.
      replace (Znth i l 0 + 32) with (if Z.leb 65 (Znth i l 0) && Z.leb (Znth i l 0) 90 then Znth i l 0 + 32 else Znth i l 0).
      { destruct (Z.leb 65 (Znth i l 0) && Z.leb (Znth i l 0) 90) eqn:Hup.
        - auto.
        - rewrite andb_false_iff in Hup. lia.
      }
      auto.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_2_2 : p016_count_distinct_characters_entail_wit_2_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold lower_seen_state, lower, is_upper_zb.
      assert (Znth i (app l (cons 0 nil)) 0 = Znth i l 0).
      { rewrite app_Znth1 by lia. reflexivity. }
      rewrite H1.
      replace (Znth i l 0) with (if Z.leb 65 (Znth i l 0) && Z.leb (Znth i l 0) 90 then Znth i l 0 + 32 else Znth i l 0).
      { destruct (Z.leb 65 (Znth i l 0) && Z.leb (Znth i l 0) 90) eqn:Hup.
        - rewrite andb_true_iff in Hup. lia.
        - auto.
      }
      auto.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_2_3 : p016_count_distinct_characters_entail_wit_2_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold lower_seen_state, lower, is_upper_zb.
      assert (Znth i (app l (cons 0 nil)) 0 = Znth i l 0).
      { rewrite app_Znth1 by lia. reflexivity. }
      rewrite H1.
      replace (Znth i l 0) with (if Z.leb 65 (Znth i l 0) && Z.leb (Znth i l 0) 90 then Znth i l 0 + 32 else Znth i l 0).
      { destruct (Z.leb 65 (Znth i l 0) && Z.leb (Znth i l 0) 90) eqn:Hup.
        - rewrite andb_true_iff in Hup. lia.
        - auto.
      }
      auto.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_3_1 : p016_count_distinct_characters_entail_wit_3_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold lower_seen_state.
      destruct H9 as [Hseen [Hc [Hseen1 Hseen0]]].
      split.
      { auto. }
      split.
      { auto. }
      intros _.
      exists j.
      split.
      { lia. }
      auto.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_3_2 : p016_count_distinct_characters_entail_wit_3_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold lower_seen_state.
      destruct H9 as [Hseen [Hc [Hseen1 Hseen0]]].
      split.
      { auto. }
      split.
      { auto. }
      intros _.
      exists j.
      split.
      { lia. }
      auto.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_3_3 : p016_count_distinct_characters_entail_wit_3_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold lower_seen_state.
      destruct H9 as [Hseen [Hc [Hseen1 Hseen0]]].
      split.
      { auto. }
      split.
      { auto. }
      intros _.
      exists j.
      split.
      { lia. }
      auto.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_3_4 : p016_count_distinct_characters_entail_wit_3_4.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold lower_seen_state.
      destruct H9 as [Hseen [Hc [Hseen1 Hseen0]]].
      split.
      { auto. }
      split.
      { auto. }
      destruct Hseen as [Hseen | Hseen].
      * intros _. exists j. split. { lia. }
        assert (Znth j (app l (cons 0 nil)) 0 = Znth j l 0).
        { rewrite app_Znth1 by lia. reflexivity. }
        rewrite H10 in H1. auto.
      * intros Hk. specialize (Hseen0 Hk).
        intros Hlt. apply Hseen0. lia.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_3_5 : p016_count_distinct_characters_entail_wit_3_5.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold lower_seen_state.
      destruct H9 as [Hseen [Hc [Hseen1 Hseen0]]].
      split.
      { auto. }
      split.
      { auto. }
      destruct Hseen as [Hseen | Hseen].
      * intros _. exists j. split. { lia. }
        assert (Znth j (app l (cons 0 nil)) 0 = Znth j l 0).
        { rewrite app_Znth1 by lia. reflexivity. }
        rewrite H10 in H1. auto.
      * intros Hk. specialize (Hseen0 Hk).
        intros Hlt. apply Hseen0. lia.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_3_6 : p016_count_distinct_characters_entail_wit_3_6.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold lower_seen_state.
      destruct H9 as [Hseen [Hc [Hseen1 Hseen0]]].
      split.
      { auto. }
      split.
      { auto. }
      destruct Hseen as [Hseen | Hseen].
      * intros _. exists j. split. { lia. }
        assert (Znth j (app l (cons 0 nil)) 0 = Znth j l 0).
        { rewrite app_Znth1 by lia. reflexivity. }
        rewrite H10 in H1. unfold lower, is_upper_zb in *.
        replace (if Z.leb 65 (Znth j l 0) && Z.leb (Znth j l 0) 90 then Znth j l 0 + 32 else Znth j l 0) with c; auto.
      * intros Hk. specialize (Hseen0 Hk).
        intros Hlt. apply Hseen0. lia.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_4_1 : p016_count_distinct_characters_entail_wit_4_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold lower_seen_state in H8.
      destruct H8 as [Hseen [Hc [Hseen1 Hseen0]]].
      unfold count_distinct_lower_upto, distinct_lower_prefix.
      assert (sublist 0 (i + 1) l = sublist 0 i l ++ sublist i (i + 1) l).
      { apply sublist_split; lia. }
      rewrite H1.
      rewrite sublist_single by lia.
      simpl.
      assert (collect_lower [] (sublist 0 i l ++ cons (Znth i l 0) nil) = collect_lower (add_unique (lower (Znth i l 0)) []) (sublist 0 i l)).
      { simpl. auto. }
      rewrite H2.
      assert (~ mem_zb (lower (Znth i l 0)) (collect_lower [] (sublist 0 i l))).
      { unfold not. intros Hmem.
        assert (exists k, 0 <= k < i /\ Znth k l 0 = Znth i l 0). admit.
      }
      admit.
Admitted.

Lemma proof_of_p016_count_distinct_characters_entail_wit_4_2 : p016_count_distinct_characters_entail_wit_4_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold lower_seen_state in H8.
      destruct H8 as [Hseen [Hc [Hseen1 Hseen0]]].
      destruct Hseen as [Hseen | Hseen].
      2:{ exfalso. auto. }
      specialize (Hseen1 Hseen).
      destruct Hseen1 as [k [Hk Hlower]].
      unfold count_distinct_lower_upto, distinct_lower_prefix.
      assert (sublist 0 (i + 1) l = sublist 0 i l ++ sublist i (i + 1) l).
      { apply sublist_split; lia. }
      rewrite H1.
      rewrite sublist_single by lia.
      simpl.
      assert (collect_lower [] (sublist 0 i l ++ cons (Znth i l 0) nil) = collect_lower (add_unique (lower (Znth i l 0)) []) (sublist 0 i l)).
      { simpl. auto. }
      rewrite H2.
      assert (mem_zb (lower (Znth i l 0)) (collect_lower [] (sublist 0 i l))).
      { admit. }
      admit.
Admitted.

Lemma proof_of_p016_count_distinct_characters_return_wit_1 : p016_count_distinct_characters_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold count_distinct_lower_upto, distinct_lower_prefix in H1.
      assert (sublist 0 n l = l).
      { admit. }
      rewrite H3 in H1.
      unfold problem_16_spec.
      auto.
    + dump_pre_spatial. lia.
Qed.
