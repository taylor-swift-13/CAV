Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import p007_filter_by_substring_goal.
From SimpleC.EE Require Import p007_filter_by_substring_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p007_filter_by_substring.
Local Open Scope sac.
Local Open Scope bool_scope.
Local Open Scope list_scope.

Lemma rows_well_formed_7_row : forall rows n k,
  rows_well_formed_7 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_7 row in
  row = c_string payload /\
  valid_string payload /\
  string_length payload < INT_MAX /\
  Zlength row = string_length payload + 1.
Proof.
  intros rows n k [Hlen Hwf] Hk row payload.
  specialize (Hwf k Hk).
  destruct Hwf as [Hrow [Hvalid Hlt]].
  split; [exact Hrow|].
  split; [exact Hvalid|].
  split; [exact Hlt|].
  subst row payload.
  rewrite Hrow at 1.
  unfold c_string, string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma filter_substring_state_7_initial : forall rows substring,
  filter_substring_state_7 rows substring 0 nil.
Proof.
  intros rows substring.
  unfold filter_substring_state_7, filter_substring_prefix_7.
  split; [rewrite Zlength_correct; lia|].
  reflexivity.
Qed.

Local Close Scope bool_scope.

Ltac c7_row_facts Hwf :=
  let Hrow := fresh "Hrow" in
  match goal with
  | r : list (list Z), n : Z |- _ =>
      match goal with
      | |- context[Znth ?idx r nil] =>
          pose proof (rows_well_formed_7_row r n idx Hwf ltac:(lia)) as Hrow;
          simpl in Hrow;
          destruct Hrow as [? [? [? ?]]]
      end
  end.

Lemma proof_of_filter_by_substring_entail_wit_1 : filter_by_substring_entail_wit_1.
Proof.
  constructor.
  - pre_process_default.
    Exists (@nil Z) (@nil (list Z)).
    sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval_2 strings_size_pre).
    rewrite PtrArray.seg_empty.
    unfold store_string.
    entailer!.
    apply filter_substring_state_7_initial.
Qed.

Lemma proof_of_filter_by_substring_entail_wit_2 : filter_by_substring_entail_wit_2.
Proof. Admitted.

Lemma proof_of_filter_by_substring_entail_wit_4 : filter_by_substring_entail_wit_4.
Proof. Admitted.

Lemma proof_of_filter_by_substring_entail_wit_5 : filter_by_substring_entail_wit_5.
Proof. Admitted.

Lemma proof_of_filter_by_substring_entail_wit_6 : filter_by_substring_entail_wit_6.
Proof. Admitted.

Lemma proof_of_filter_by_substring_entail_wit_7 : filter_by_substring_entail_wit_7.
Proof. Admitted.

Lemma proof_of_filter_by_substring_return_wit_1 : filter_by_substring_return_wit_1.
Proof. Admitted.
