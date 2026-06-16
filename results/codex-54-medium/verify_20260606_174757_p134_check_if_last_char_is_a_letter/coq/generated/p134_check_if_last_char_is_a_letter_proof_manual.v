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
From SimpleC.EE.CAV.verify_20260606_174757_p134_check_if_last_char_is_a_letter Require Import p134_check_if_last_char_is_a_letter_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p134_check_if_last_char_is_a_letter.
Local Open Scope sac.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_1 : p134_check_if_last_char_is_a_letter_return_wit_1.
Proof.
  pre_process.
  subst retval len.
  entailer!.
  assert (Hprev_app :
    Znth (Zlength l - 2) (l ++ 0 :: nil) 0 = Znth (Zlength l - 2) l 0).
  { apply app_Znth1. lia. }
  rewrite Hprev_app in H.
  unfold problem_134_spec, bool_of, ends_with_single_letter, is_alpha.
  split.
  + intro Hspec. discriminate Hspec.
  + intro Hends.
    exfalso.
    destruct Hends as [Hlen [_ [Hone | Hspace]]].
    * lia.
    * exact (H Hspace).
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_2 : p134_check_if_last_char_is_a_letter_return_wit_2.
Proof.
  pre_process.
  subst retval len.
  entailer!.
  assert (Hprev_app :
    Znth (Zlength l - 2) (l ++ 0 :: nil) 0 = Znth (Zlength l - 2) l 0).
  { apply app_Znth1. lia. }
  rewrite Hprev_app in H.
  unfold problem_134_spec, bool_of, ends_with_single_letter, is_alpha.
  split.
  + intro Hspec. discriminate Hspec.
  + intro Hends.
    exfalso.
    destruct Hends as [Hlen [_ [Hone | Hspace]]].
    * lia.
    * exact (H Hspace).
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_3 : p134_check_if_last_char_is_a_letter_return_wit_3.
Proof.
  pre_process.
  subst retval len.
  entailer!.
  assert (Hlast_app :
    Znth (Zlength l - 1) (l ++ 0 :: nil) 0 = Znth (Zlength l - 1) l 0).
  { apply app_Znth1. lia. }
  assert (Hprev_app :
    Znth (Zlength l - 2) (l ++ 0 :: nil) 0 = Znth (Zlength l - 2) l 0).
  { apply app_Znth1. lia. }
  rewrite Hprev_app in H.
  assert (Halpha_l : 65 <= Znth (Zlength l - 1) l 0 <= 90).
  { rewrite <- Hlast_app. lia. }
  unfold problem_134_spec, bool_of, ends_with_single_letter, is_alpha.
  split.
  - intro Hspec.
    repeat split.
    + lia.
    + left. exact Halpha_l.
    + right. exact H.
  - intro Hends. reflexivity.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_4 : p134_check_if_last_char_is_a_letter_return_wit_4.
Proof.
  pre_process.
  subst retval len.
  entailer!.
  assert (Hlast_app :
    Znth (Zlength l - 1) (l ++ 0 :: nil) 0 = Znth (Zlength l - 1) l 0).
  { apply app_Znth1. lia. }
  assert (Hprev_app :
    Znth (Zlength l - 2) (l ++ 0 :: nil) 0 = Znth (Zlength l - 2) l 0).
  { apply app_Znth1. lia. }
  rewrite Hprev_app in H.
  assert (Halpha_l : 97 <= Znth (Zlength l - 1) l 0 <= 122).
  { rewrite <- Hlast_app. lia. }
  unfold problem_134_spec, bool_of, ends_with_single_letter, is_alpha.
  split.
  - intro Hspec.
    repeat split.
    + lia.
    + right. exact Halpha_l.
    + right. exact H.
  - intro Hends. reflexivity.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_5 : p134_check_if_last_char_is_a_letter_return_wit_5.
Proof.
  pre_process.
  subst retval len.
  entailer!.
  assert (Hlast_app :
    Znth (Zlength l - 1) (l ++ 0 :: nil) 0 = Znth (Zlength l - 1) l 0).
  { apply app_Znth1. lia. }
  rewrite H8 in Hlast_app.
  cbn in Hlast_app, H1, H2.
  assert (Halpha_l : 65 <= Znth 0 l 0 <= 90).
  { rewrite <- Hlast_app. lia. }
  unfold problem_134_spec, bool_of, ends_with_single_letter, is_alpha.
  rewrite H8.
  cbn.
  split.
  - intro Hspec.
    repeat split.
    + lia.
    + left. exact Halpha_l.
    + left. reflexivity.
  - intro Hends. reflexivity.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_6 : p134_check_if_last_char_is_a_letter_return_wit_6.
Proof.
  pre_process.
  subst retval len.
  entailer!.
  assert (Hlast_app :
    Znth (Zlength l - 1) (l ++ 0 :: nil) 0 = Znth (Zlength l - 1) l 0).
  { apply app_Znth1. lia. }
  rewrite H9 in Hlast_app.
  cbn in Hlast_app, H0, H1, H2, H3.
  assert (Halpha_l : 97 <= Znth 0 l 0 <= 122).
  { rewrite <- Hlast_app. lia. }
  unfold problem_134_spec, bool_of, ends_with_single_letter, is_alpha.
  rewrite H9.
  cbn.
  split.
  - intro Hspec.
    repeat split.
    + lia.
    + right. exact Halpha_l.
    + left. reflexivity.
  - intro Hends. reflexivity.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_7 : p134_check_if_last_char_is_a_letter_return_wit_7.
Proof.
  pre_process.
  subst retval len.
  entailer!.
  assert (Hlast_app :
    Znth (Zlength l - 1) (l ++ 0 :: nil) 0 = Znth (Zlength l - 1) l 0).
  { apply app_Znth1. lia. }
  assert (Hgt122_l : Znth (Zlength l - 1) l 0 > 122).
  { rewrite <- Hlast_app. exact H. }
  unfold problem_134_spec, bool_of, ends_with_single_letter, is_alpha.
  split.
  - intro Hspec. discriminate Hspec.
  - intro Hends.
    exfalso.
    destruct Hends as [_ [Halpha _]].
    destruct Halpha as [[? ?] | [? ?]]; lia.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_8 : p134_check_if_last_char_is_a_letter_return_wit_8.
Proof.
  pre_process.
  subst retval len.
  entailer!.
  assert (Hlast_app :
    Znth (Zlength l - 1) (l ++ 0 :: nil) 0 = Znth (Zlength l - 1) l 0).
  { apply app_Znth1. lia. }
  assert (Hlt97_l : Znth (Zlength l - 1) l 0 < 97).
  { rewrite <- Hlast_app. exact H. }
  assert (Hgt90_l : Znth (Zlength l - 1) l 0 > 90).
  { rewrite <- Hlast_app. exact H0. }
  unfold problem_134_spec, bool_of, ends_with_single_letter, is_alpha.
  split.
  - intro Hspec. discriminate Hspec.
  - intro Hends.
    exfalso.
    destruct Hends as [_ [Halpha _]].
    destruct Halpha as [[? ?] | [? ?]]; lia.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_9 : p134_check_if_last_char_is_a_letter_return_wit_9.
Proof.
  pre_process.
  subst retval len.
  entailer!.
  assert (Hlast_app :
    Znth (Zlength l - 1) (l ++ 0 :: nil) 0 = Znth (Zlength l - 1) l 0).
  { apply app_Znth1. lia. }
  assert (Hlt65_l : Znth (Zlength l - 1) l 0 < 65).
  { rewrite <- Hlast_app. exact H. }
  unfold problem_134_spec, bool_of, ends_with_single_letter, is_alpha.
  split.
  - intro Hspec. discriminate Hspec.
  - intro Hends.
    exfalso.
    destruct Hends as [_ [Halpha _]].
    destruct Halpha as [[? ?] | [? ?]]; lia.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_10 : p134_check_if_last_char_is_a_letter_return_wit_10.
Proof.
  pre_process.
  subst retval len.
  entailer!.
  unfold problem_134_spec, bool_of, ends_with_single_letter, is_alpha.
  split.
  + intro Hspec. discriminate Hspec.
  + intro Hends.
    exfalso.
    destruct Hends as [Hlen _].
    lia.
Qed.
