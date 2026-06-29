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
From SimpleC.EE.CAV.ground_truth_p093_encode Require Import p093_encode_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Arith.

Import naive_C_Rules.
Require Import string_bridge.
Require Import p093_encode.
Local Open Scope sac.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p093_encode.v so public contract files expose definitions only. *)

Lemma problem_93_pre_char : forall s k,
  problem_93_pre s ->
  ascii_range s ->
  0 <= k < Zlength s ->
  is_upper (Znth k s 0) \/ is_lower (Znth k s 0) \/ is_space (Znth k s 0).
Proof.
  intros s k Hpre _ Hk.
  apply Hpre.
  exact Hk.
Qed.
Lemma encode_char_nonzero : forall c,
  is_upper c \/ is_lower c \/ is_space c ->
  encode_char c <> 0.
Proof.
  intros c Hclass.
  unfold is_upper, is_lower, is_space in Hclass.
  unfold encode_char, swap_case, is_vowel.
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      destruct (Z.leb_spec x y); simpl
  | |- context[Z.eqb ?x ?y] =>
      destruct (Z.eqb_spec x y); simpl
  end;
  lia.
Qed.
Lemma problem_93_spec_intro : forall input output n,
  Zlength input = n ->
  Zlength output = n ->
  problem_93_pre input ->
  ascii_range input ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = encode_char (Znth k input 0)) ->
  problem_93_spec input output.
Proof.
  intros input output n Hin Hout _ _ Hpoint.
  unfold problem_93_spec.
  split.
  - lia.
  - intros k Hk.
    apply Hpoint.
    lia.
Qed.


Ltac normalize_input_char :=
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | Hpre : problem_93_pre ?l,
    Hrange : ascii_range ?l |- context[Znth ?i ?l 0] =>
      let Hchar := fresh "Hchar" in
      pose proof (problem_93_pre_char l i Hpre Hrange ltac:(lia)) as Hchar;
      unfold is_upper, is_lower, is_space in Hchar;
      destruct Hchar as [Hchar | [Hchar | Hchar]]
  | _ => idtac
  end;
  try lia.

Ltac simplify_encode_char :=
  normalize_input_char;
  repeat match goal with
  | |- context[signed_last_nbits (Znth ?i ?l 0) 8] =>
      rewrite (signed_last_nbits_eq (Znth i l 0) 8) by lia
  end;
  unfold encode_char, swap_case, is_vowel;
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      destruct (Z.leb_spec x y); simpl
  | |- context[Z.eqb ?x ?y] =>
      destruct (Z.eqb_spec x y); simpl
  end;
  lia.

Ltac solve_encode_step_value :=
  intros k Hk;
  match goal with
  | Hlen : Zlength ?ol = ?idx |- _ =>
      destruct (Z_lt_ge_dec k idx) as [Hlt | Hge];
      [ rewrite app_Znth1 by (rewrite Hlen; lia);
        match goal with
        | Hprefix : forall _ : Z, _ -> _ = _ |- _ =>
            apply Hprefix; lia
        end
      | assert (k = idx) by lia;
        subst k;
        rewrite app_Znth2 by (rewrite Hlen; lia);
        replace (idx - Zlength ol) with 0 by (rewrite Hlen; lia);
        rewrite Znth0_cons;
        simplify_encode_char ]
  end.

Ltac solve_encode_step :=
  pre_process;
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | |- context[CharArray.full ?out (?i + 1) (app ?ol (cons ?v nil))] =>
      Exists (app ol (cons v nil))
  end;
  entailer!;
  [ solve_encode_step_value
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Lemma proof_of_p093_encode_entail_wit_1 : p093_encode_entail_wit_1.
Proof.
  unfold p093_encode_entail_wit_1.
  intros.
  pre_process.
  subst.
  Exists nil.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (Zlength l + 1)).
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  lia.
Qed. 

Lemma proof_of_p093_encode_entail_wit_2_1 : p093_encode_entail_wit_2_1.
Proof. unfold p093_encode_entail_wit_2_1; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_2 : p093_encode_entail_wit_2_2.
Proof. unfold p093_encode_entail_wit_2_2; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_3 : p093_encode_entail_wit_2_3.
Proof. unfold p093_encode_entail_wit_2_3; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_4 : p093_encode_entail_wit_2_4.
Proof. unfold p093_encode_entail_wit_2_4; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_5 : p093_encode_entail_wit_2_5.
Proof. unfold p093_encode_entail_wit_2_5; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_6 : p093_encode_entail_wit_2_6.
Proof. unfold p093_encode_entail_wit_2_6; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_7 : p093_encode_entail_wit_2_7.
Proof. unfold p093_encode_entail_wit_2_7; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_8 : p093_encode_entail_wit_2_8.
Proof. unfold p093_encode_entail_wit_2_8; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_9 : p093_encode_entail_wit_2_9.
Proof. unfold p093_encode_entail_wit_2_9; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_10 : p093_encode_entail_wit_2_10.
Proof. unfold p093_encode_entail_wit_2_10; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_11 : p093_encode_entail_wit_2_11.
Proof. unfold p093_encode_entail_wit_2_11; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_12 : p093_encode_entail_wit_2_12.
Proof. unfold p093_encode_entail_wit_2_12; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_13 : p093_encode_entail_wit_2_13.
Proof. unfold p093_encode_entail_wit_2_13; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_14 : p093_encode_entail_wit_2_14.
Proof. unfold p093_encode_entail_wit_2_14; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_entail_wit_2_15 : p093_encode_entail_wit_2_15.
Proof. unfold p093_encode_entail_wit_2_15; intros; solve_encode_step. Qed. 

Lemma proof_of_p093_encode_return_wit_1 : p093_encode_return_wit_1.
Proof.
  unfold p093_encode_return_wit_1.
  intros.
  pre_process.
  assert (i = len) by lia.
  subst i.
  Exists out_l_2.
  match goal with
  | Hlen : Zlength out_l_2 = len |- _ => rewrite Hlen
  end.
  rewrite (CharArray.undef_seg_empty out (len + 1)).
  entailer!.
  - apply problem_93_spec_intro with (n := len); try lia; try assumption.
    intros k Hk.
    match goal with
    | Hprefix : forall _ : Z, _ -> _ = _ |- _ =>
        apply Hprefix; lia
    end.
  - intros k Hk.
    match goal with
    | Hprefix : forall _ : Z, _ -> _ = _ |- _ =>
        rewrite Hprefix by lia
    end.
    apply encode_char_nonzero.
    eapply problem_93_pre_char; eauto; lia.
Qed. 
