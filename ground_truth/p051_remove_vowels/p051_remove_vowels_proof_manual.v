Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p051_remove_vowels Require Import p051_remove_vowels_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p051_remove_vowels.
Local Open Scope sac.

Ltac simplify_vowel_case :=
  repeat rewrite app_Znth1 in * by lia;
  unfold is_vowel;
  repeat match goal with
  | |- context[Z.eqb ?x ?y] =>
      destruct (Z.eqb_spec x y); simpl
  end;
  try lia.

Ltac rewrite_signed_input :=
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | Hrange : char_range ?l |- context[signed_last_nbits (Znth ?i ?l 0) 8] =>
      let Hr := fresh "Hchar" in
      pose proof (Hrange i ltac:(lia)) as Hr;
      rewrite (signed_last_nbits_eq (Znth i l 0) 8) by lia
  end.

Ltac solve_appended_nonzero :=
  intros k Hk;
  match goal with
  | Hprefix_nz : forall q : Z, _ -> Znth q ?prefix 0 <> 0,
    Hinput_nz : forall q : Z, _ -> Znth q ?l 0 <> 0
    |- Znth k (app ?prefix (cons (Znth ?i ?l 0) nil)) 0 <> 0 =>
      destruct (Z_lt_ge_dec k (Zlength prefix)) as [Hlt | Hge];
      [ rewrite app_Znth1 by lia;
        apply Hprefix_nz; lia
      | assert (k = Zlength prefix) by lia;
        subst k;
        rewrite app_Znth2 by lia;
        replace (Zlength prefix - Zlength prefix) with 0 by lia;
        rewrite Znth0_cons;
        apply Hinput_nz; lia ]
  end.

Ltac solve_vowel_step :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | |- context[CharArray.full ?out ?j (remove_vowels_prefix ?i ?l)] =>
      Exists (remove_vowels_prefix i l)
	  end;
	  entailer!;
	  try (rewrite remove_vowels_prefix_step by lia;
	       simplify_vowel_case;
	       reflexivity).

Ltac solve_nonvowel_step :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia;
  rewrite_signed_input;
  match goal with
  | |- context[CharArray.full ?out (?j + 1) (app (remove_vowels_prefix ?i ?l) (cons (Znth ?i ?l 0) nil))] =>
      Exists (app (remove_vowels_prefix i l) (cons (Znth i l 0) nil))
	  end;
	  entailer!;
	  try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
	  try solve_appended_nonzero;
	  try (rewrite remove_vowels_prefix_step by lia;
	       simplify_vowel_case;
	       reflexivity).

Lemma proof_of_p051_remove_vowels_entail_wit_1 : p051_remove_vowels_entail_wit_1.
Proof.
  unfold p051_remove_vowels_entail_wit_1.
  intros.
  pre_process.
  subst.
  Exists nil.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (Zlength l + 1)).
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  rewrite remove_vowels_prefix_0.
  entailer!.
  lia.
Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_1 : p051_remove_vowels_entail_wit_2_1.
Proof. unfold p051_remove_vowels_entail_wit_2_1; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_2 : p051_remove_vowels_entail_wit_2_2.
Proof. unfold p051_remove_vowels_entail_wit_2_2; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_3 : p051_remove_vowels_entail_wit_2_3.
Proof. unfold p051_remove_vowels_entail_wit_2_3; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_4 : p051_remove_vowels_entail_wit_2_4.
Proof. unfold p051_remove_vowels_entail_wit_2_4; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_5 : p051_remove_vowels_entail_wit_2_5.
Proof. unfold p051_remove_vowels_entail_wit_2_5; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_6 : p051_remove_vowels_entail_wit_2_6.
Proof. unfold p051_remove_vowels_entail_wit_2_6; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_7 : p051_remove_vowels_entail_wit_2_7.
Proof. unfold p051_remove_vowels_entail_wit_2_7; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_8 : p051_remove_vowels_entail_wit_2_8.
Proof. unfold p051_remove_vowels_entail_wit_2_8; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_9 : p051_remove_vowels_entail_wit_2_9.
Proof. unfold p051_remove_vowels_entail_wit_2_9; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_10 : p051_remove_vowels_entail_wit_2_10.
Proof. unfold p051_remove_vowels_entail_wit_2_10; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_11 : p051_remove_vowels_entail_wit_2_11.
Proof. unfold p051_remove_vowels_entail_wit_2_11; intros; solve_nonvowel_step. Qed.

Lemma proof_of_p051_remove_vowels_return_wit_1 : p051_remove_vowels_return_wit_1.
Proof.
  unfold p051_remove_vowels_return_wit_1.
  intros.
  pre_process.
  assert (i = len) by lia.
  subst i.
  Exists out_l_2.
  Exists j.
  entailer!.
  eapply problem_51_spec_intro; eauto.
  rewrite H1.
  assumption.
Qed.
