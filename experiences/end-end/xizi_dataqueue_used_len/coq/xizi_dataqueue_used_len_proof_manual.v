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
From SimpleC.EE.CAV.verify_20260602_233819v_xizi_dataqueue_used_len Require Import xizi_dataqueue_used_len_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_xizi_dataqueue_used_len_return_wit_1 : xizi_dataqueue_used_len_return_wit_1.
Proof.
  pre_process.
  entailer!.
  - intro Hlt.
    replace (rear_pre - front_pre + max_len_pre) with (max_len_pre - (front_pre - rear_pre)) by lia.
    apply Z.rem_small.
    lia.
  - intro Hge.
    assert (Hdiff: 0 <= rear_pre - front_pre) by lia.
    replace (rear_pre - front_pre + max_len_pre) with ((rear_pre - front_pre) + 1 * max_len_pre) by lia.
    rewrite (Z.rem_add (rear_pre - front_pre) 1 max_len_pre).
    2: lia.
    2: nia.
    apply Z.rem_small.
    lia.
Qed.
