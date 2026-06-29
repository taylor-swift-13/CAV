Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p005_intersperse Require Import p005_intersperse_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p005_intersperse.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p005_intersperse.v so public contract files expose definitions only. *)

Lemma intersperse_list_snoc_nonempty : forall l x d,
  l <> nil ->
  intersperse_list (l ++ [x]) d = intersperse_list l d ++ [d; x].
Proof.
  intros l x d Hnonempty.
  destruct l as [| a xs]; [contradiction Hnonempty; reflexivity |].
  clear Hnonempty.
  revert a.
  induction xs as [| b xs IH]; intros a; simpl; auto.
  destruct xs as [| c xs].
  - reflexivity.
  - change (a :: d :: intersperse_list ((b :: c :: xs) ++ [x]) d =
            a :: d :: (intersperse_list (b :: c :: xs) d ++ [d; x])).
    rewrite (IH b). reflexivity.
Qed.
Lemma intersperse_list_sublist_one : forall l d,
  0 < Z.of_nat (length l) ->
  intersperse_list (sublist 0 1 l) d = [Znth 0 l 0].
Proof.
  intros.
  change 1 with (0 + 1).
  rewrite (sublist_single 0 0 l) by (rewrite Zlength_correct; lia).
  reflexivity.
Qed.
Lemma intersperse_list_sublist_snoc : forall l i d,
  1 <= i < Z.of_nat (length l) ->
  intersperse_list (sublist 0 (i + 1) l) d =
  intersperse_list (sublist 0 i l) d ++ [d; Znth i l 0].
Proof.
  intros.
  rewrite (sublist_split 0 (i + 1) i l) by (try rewrite Zlength_correct in *; lia).
  rewrite (sublist_single 0 i l) by (rewrite Zlength_correct; lia).
  apply intersperse_list_snoc_nonempty.
  intro Hempty.
  pose proof (Zlength_sublist 0 i l).
  assert (0 <= 0 <= i /\ i <= Zlength l) by (rewrite Zlength_correct; lia).
  specialize (H0 H1).
  rewrite Hempty in H0.
  rewrite Zlength_correct in H0.
  simpl in H0.
  lia.
Qed.
Lemma intersperse_list_length : forall (l : list Z) d,
  l <> nil ->
  Zlength (intersperse_list l d) = 2 * Zlength l - 1.
Proof.
  induction l as [| x xs IH]; intros d Hne.
  - contradiction.
  - destruct xs as [| y ys].
    + cbn [intersperse_list]. rewrite !Zlength_cons. simpl. lia.
    + assert (Hne' : y :: ys <> nil) by discriminate.
      specialize (IH d Hne').
      cbn [intersperse_list].
      change (match ys with
              | [] => [y]
              | _ :: _ => y :: d :: intersperse_list ys d
              end) with (intersperse_list (y :: ys) d).
      rewrite !Zlength_cons.
      rewrite IH.
      rewrite !Zlength_cons.
      lia.
Qed.


Lemma proof_of_p005_intersperse_entail_wit_1 : p005_intersperse_entail_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_length numbers_pre). Intros.
  rewrite intersperse_list_sublist_one by lia.
  sep_apply (IntArray.seg_single out_pre 0 (Znth 0 l 0)).
  entailer!.
Qed.

Lemma proof_of_p005_intersperse_entail_wit_2 : p005_intersperse_entail_wit_2.
Proof.
  pre_process.
  prop_apply (IntArray.full_length numbers_pre). Intros.
  rewrite intersperse_list_sublist_snoc by lia.
  rewrite <- app_assoc.
  entailer!.
Qed.

Lemma proof_of_p005_intersperse_return_wit_1 : p005_intersperse_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = numbers_size_pre) by lia.
  subst i.
  assert (Hk : k = 2 * numbers_size_pre - 1) by lia.
  subst k.
  prop_apply (IntArray.full_length numbers_pre). Intros.
  assert (Hsl : sublist 0 numbers_size_pre l = l).
  {
    apply sublist_self.
    rewrite Zlength_correct.
    match goal with
    | Hlen : Z.of_nat (Datatypes.length l) = numbers_size_pre |- _ =>
        symmetry; exact Hlen
    end.
  }
  rewrite Hsl.
  Exists (intersperse_list l delimeter_pre).
  rewrite (IntArray.undef_seg_empty out_pre (2 * numbers_size_pre - 1)).
  sep_apply (IntArray.seg_to_full out_pre 0 (2 * numbers_size_pre - 1)).
  replace (out_pre + 0 * sizeof (INT)) with out_pre by lia.
  replace (2 * numbers_size_pre - 1 - 0) with (2 * numbers_size_pre - 1) by lia.
  entailer!.
  rewrite intersperse_list_length.
  - rewrite H2. lia.
  - intro Hnil.
    subst l.
    rewrite Zlength_nil in H2.
    lia.
Qed.
