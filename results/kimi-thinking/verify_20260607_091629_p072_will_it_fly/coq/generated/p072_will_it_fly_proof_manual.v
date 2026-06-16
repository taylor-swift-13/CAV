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
From SimpleC.EE.CAV.verify_20260607_091629_p072_will_it_fly Require Import p072_will_it_fly_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p072_will_it_fly.
Local Open Scope sac.

(* Helper lemmas *)

Lemma Zlength_to_nat : forall (l: list Z) i,
  0 <= i < Zlength l ->
  Z.to_nat (Zlength l - 1 - i) = (length l - S (Z.to_nat i))%nat.
Proof.
  intros l i H.
  assert (Hlen: Zlength l = Z.of_nat (length l)) by apply Zlength_correct.
  lia.
Qed.

Lemma Znth_rev : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  Znth i (rev l) d = Znth (Zlength l - 1 - i) l d.
Proof.
  intros l i d H.
  unfold Znth.
  rewrite rev_nth.
  - f_equal.
    symmetry.
    apply Zlength_to_nat.
    exact H.
  - rewrite Zlength_correct in H.
    destruct H as [H0 Hi].
    apply Z2Nat.inj_lt in Hi; try lia.
Qed.

Lemma Zlength_rev : forall (l : list Z), Zlength (rev l) = Zlength l.
Proof.
  intros l.
  assert (H1: Zlength (rev l) = Z.of_nat (length (rev l))) by apply Zlength_correct.
  assert (H2: Zlength l = Z.of_nat (length l)) by apply Zlength_correct.
  rewrite H1, H2, length_rev.
  reflexivity.
Qed.

Lemma mirror_all_eq_rev : forall l, mirror_all l -> l = rev l.
Proof.
  intros l Hm.
  apply list_eq_ext with (d := 0).
  split.
  - rewrite Zlength_rev. reflexivity.
  - intros i Hi.
    rewrite Znth_rev by exact Hi.
    apply Hm.
    exact Hi.
Qed.

Lemma fold_left_add_acc : forall l acc,
  fold_left (fun acc x => acc + x) l acc = acc + fold_left (fun acc x => acc + x) l 0.
Proof.
  induction l as [|a l IH]; intros acc; simpl.
  - lia.
  - rewrite IH.
    rewrite (IH a).
    lia.
Qed.

Lemma sum_fold_left_eq : forall l,
  sum l = fold_left (fun acc x => acc + x) l 0.
Proof.
  intros l.
  unfold sum.
  induction l as [|a l IH]; simpl.
  - reflexivity.
  - rewrite IH.
    rewrite fold_left_add_acc with (acc := a).
    reflexivity.
Qed.

(* Safety witnesses *)

Lemma proof_of_p072_will_it_fly_safety_wit_1 : p072_will_it_fly_safety_wit_1.
Proof. pre_process. Qed.

Lemma proof_of_p072_will_it_fly_safety_wit_2 : p072_will_it_fly_safety_wit_2.
Proof. pre_process. Qed.

Lemma proof_of_p072_will_it_fly_safety_wit_3 : p072_will_it_fly_safety_wit_3.
Proof. pre_process. Qed.

Lemma proof_of_p072_will_it_fly_safety_wit_4 : p072_will_it_fly_safety_wit_4.
Proof. pre_process. Qed.

Lemma proof_of_p072_will_it_fly_safety_wit_5 : p072_will_it_fly_safety_wit_5.
Proof. pre_process. Qed.

Lemma proof_of_p072_will_it_fly_safety_wit_6 : p072_will_it_fly_safety_wit_6.
Proof. pre_process. Qed.

Lemma proof_of_p072_will_it_fly_safety_wit_7 : p072_will_it_fly_safety_wit_7.
Proof.
  pre_process.
  assert (Hrange : will_it_fly_int_range lv) by exact H8.
  specialize (Hrange (i + 1) ltac:(lia)).
  destruct Hrange as [Hrange1 Hrange2].
  assert (Hsum_eq : sum (sublist 0 (i + 1) lv) = sum (sublist 0 i lv) + Znth i lv 0).
  { rewrite (sublist_split 0 (i + 1) i lv) by lia.
    rewrite sum_app.
    rewrite (sublist_single 0 i lv) by lia.
    simpl.
    lia. }
  assert (Hgoal : s + Znth i lv 0 = sum (sublist 0 (i + 1) lv)).
  { transitivity (sum (sublist 0 i lv) + Znth i lv 0).
    - f_equal. exact H6.
    - symmetry. exact Hsum_eq. }
  split_pures.
  + dump_pre_spatial. lia.
  + dump_pre_spatial. lia.
Qed.

Lemma proof_of_p072_will_it_fly_safety_wit_8 : p072_will_it_fly_safety_wit_8.
Proof. pre_process. Qed.

Lemma proof_of_p072_will_it_fly_safety_wit_9 : p072_will_it_fly_safety_wit_9.
Proof. pre_process. Qed.

Lemma proof_of_p072_will_it_fly_safety_wit_10 : p072_will_it_fly_safety_wit_10.
Proof. pre_process. Qed.

(* Entail witnesses *)

Lemma proof_of_p072_will_it_fly_entail_wit_1 : p072_will_it_fly_entail_wit_1.
Proof. pre_process. Qed.

Lemma proof_of_p072_will_it_fly_entail_wit_2 : p072_will_it_fly_entail_wit_2.
Proof.
  pre_process.
  split_pures.
  split_pure_spatial.
  - cancel (IntArray.full q_pre q_size_pre lv).
  - split_pures.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H3.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      assert (Hsum_eq : sum (sublist 0 (i + 1) lv) = sum (sublist 0 i lv) + Znth i lv 0).
      { rewrite (sublist_split 0 (i + 1) i lv) by lia.
        rewrite sum_app.
        rewrite (sublist_single 0 i lv) by lia.
        simpl.
        lia. }
      assert (Hgoal : s + Znth i lv 0 = sum (sublist 0 (i + 1) lv)).
      { transitivity (sum (sublist 0 i lv) + Znth i lv 0).
        - f_equal. exact H6.
        - symmetry. exact Hsum_eq. }
      exact Hgoal.
    + dump_pre_spatial.
      intros k Hk.
      destruct (Z_lt_dec k i) as [Hlt | Hge].
      * apply H7. lia.
      * assert (k = i) by lia.
        subst k.
        exact H.
    + dump_pre_spatial. exact H8.
Qed.

(* Return witnesses *)

Lemma proof_of_p072_will_it_fly_return_wit_1 : p072_will_it_fly_return_wit_1.
Proof.
  pre_process.
  unfold problem_72_spec.
  split_pures.
  split_pure_spatial.
  - cancel (IntArray.full q_pre q_size_pre lv).
  - split.
    + right. reflexivity.
    + split.
      * intro Ht. split.
        -- apply mirror_all_eq_rev. unfold mirror_all. intros k Hk.
           assert (i = q_size_pre) by lia. subst i.
           rewrite H3 in H7.
           apply H7. exact Hk.
        -- rewrite H6.
           assert (i = q_size_pre) by lia. subst i.
           unfold sublist. simpl.
           rewrite firstn_all2 by (assert (Hlen: Zlength lv = Z.of_nat (length lv)) by apply Zlength_correct; lia).
           rewrite sum_fold_left_eq.
           exact H.
      * intro Ht. reflexivity.
Qed.

Lemma proof_of_p072_will_it_fly_return_wit_2 : p072_will_it_fly_return_wit_2.
Proof.
  pre_process.
  unfold problem_72_spec.
  split_pures.
  split_pure_spatial.
  - cancel (IntArray.full q_pre q_size_pre lv).
  - split.
    + left. reflexivity.
    + split.
      * intro Hcontra.
        destruct Hcontra as [_ Hsum].
        assert (i = q_size_pre) by lia.
        subst i.
        rewrite H6 in H.
        unfold sublist in Hsum.
        simpl in Hsum.
        rewrite firstn_all2 in Hsum by (assert (Hlen: Zlength lv = Z.of_nat (length lv)) by apply Zlength_correct; lia).
        rewrite sum_fold_left_eq in Hsum.
        lia.
      * intro Ht. reflexivity.
Qed.

Lemma proof_of_p072_will_it_fly_return_wit_3 : p072_will_it_fly_return_wit_3.
Proof.
  pre_process.
  unfold problem_72_spec.
  split_pures.
  split_pure_spatial.
  - cancel (IntArray.full q_pre q_size_pre lv).
  - split.
    + left. reflexivity.
    + intro Hcontra.
      destruct Hcontra as [Heq _].
      apply mirror_all_eq_rev in Heq.
      unfold mirror_all in Heq.
      assert (Hne' : Znth i lv 0 = Znth (q_size_pre - 1 - i) lv 0).
      { apply Heq.
        lia. }
      contradiction.
Qed.

(* Partial solve witnesses *)

Lemma proof_of_p072_will_it_fly_partial_solve_wit_1 : p072_will_it_fly_partial_solve_wit_1.
Proof.
  pre_process.
  sep_apply_l_atomic (IntArray.full_split_to_missing_i q_pre i q_size_pre lv 0).
  - dump_pre_spatial. lia.
  - cancel (IntArray.missing_i q_pre i 0 q_size_pre lv).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p H1.
    subst v.
    cancel.
Qed.

Lemma proof_of_p072_will_it_fly_partial_solve_wit_2 : p072_will_it_fly_partial_solve_wit_2.
Proof.
  pre_process.
  sep_apply_l_atomic (IntArray.full_split_to_missing_i q_pre (q_size_pre - 1 - i) q_size_pre lv 0).
  - dump_pre_spatial. lia.
  - cancel (IntArray.missing_i q_pre (q_size_pre - 1 - i) 0 q_size_pre lv).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p H1.
    subst v.
    cancel.
Qed.

Lemma proof_of_p072_will_it_fly_partial_solve_wit_3 : p072_will_it_fly_partial_solve_wit_3.
Proof.
  pre_process.
  sep_apply_l_atomic (IntArray.full_split_to_missing_i q_pre i q_size_pre lv 0).
  - dump_pre_spatial. lia.
  - cancel (IntArray.missing_i q_pre i 0 q_size_pre lv).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p H1.
    subst v.
    cancel.
Qed.
