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
From SimpleC.EE.CAV.ground_truth_p038_decode_cyclic Require Import p038_decode_cyclic_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import naive_C_Rules.
Require Import string_bridge.
Require Import p038_decode_cyclic.
Local Open Scope sac.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p038_decode_cyclic.v so public contract files expose definitions only. *)

Lemma string_of_list_length : forall l,
  String.length (string_of_list l) = List.length l.
Proof.
  induction l; simpl; auto.
Qed.
Lemma string_of_list_Zlength : forall l,
  Z.of_nat (String.length (string_of_list l)) = Zlength l.
Proof.
  intros l.
  rewrite string_of_list_length.
  rewrite Zlength_correct.
  reflexivity.
Qed.
Lemma string_get_string_of_list_nth : forall l i,
  (i < List.length l)%nat ->
  String.get i (string_of_list l) =
    Some (ascii_of (Znth (Z.of_nat i) l 0)).
Proof.
  induction l as [| x xs IH]; intros [| i] Hi; simpl in *; try lia.
  - unfold Znth. simpl. reflexivity.
  - rewrite Znth_cons by lia.
    replace (Z.pos (Pos.of_succ_nat i) - 1) with (Z.of_nat i) by lia.
    apply IH. lia.
Qed.
Lemma string_get_string_of_list_Znth : forall l k,
  0 <= k < Zlength l ->
  String.get (Z.to_nat k) (string_of_list l) =
    Some (ascii_of (Znth k l 0)).
Proof.
  intros l k Hk.
  rewrite string_get_string_of_list_nth.
  - replace (Z.of_nat (Z.to_nat k)) with k by lia.
    reflexivity.
  - rewrite <- string_of_list_length.
    apply Nat2Z.inj_lt.
    rewrite string_of_list_Zlength.
    lia.
Qed.
Lemma full_decode_len_bounds : forall len,
  0 <= len ->
  0 <= full_decode_len len <= len /\ full_decode_len len mod 3 = 0.
Proof.
  intros len Hlen.
  unfold full_decode_len.
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod len 3 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound len 3 ltac:(lia)) as Hmod.
  split; [lia |].
  rewrite Z_mod_mult.
  reflexivity.
Qed.
Lemma mod_full_tail_case_38 : forall full i,
  0 <= i < full ->
  full mod 3 = 0 ->
  (i + 1) mod 3 = 1 ->
  i + 2 < full.
Proof.
  intros full i Hi Hfull Hmod.
  assert (Hcase : i + 2 < full \/ i + 2 >= full) by lia.
  destruct Hcase as [| Hge]; [lia |].
  assert (Hcases : i = full - 1 \/ i = full - 2) by lia.
  destruct Hcases as [Hi1 | Hi2].
  - subst i.
    replace (full - 1 + 1) with full in Hmod by lia.
    lia.
  - subst i.
    replace (full - 2 + 1) with (full - 1) in Hmod by lia.
    replace (full - 1) with (2 + (full / 3 - 1) * 3) in Hmod.
    + rewrite Z_mod_plus_full in Hmod. cbn in Hmod. lia.
    + pose proof (Z.div_mod full 3 ltac:(lia)) as Hdiv.
      lia.
Qed.
Lemma decode_source_index_range : forall len i,
  0 <= len ->
  0 <= i < len ->
  0 <= decode_source_index len i < len.
Proof.
  intros len i Hlen Hi.
  unfold decode_source_index.
  pose proof (full_decode_len_bounds len Hlen) as [[Hfull_nonneg Hfull_le] Hfull_mod].
  destruct (Z.ltb_spec i (full_decode_len len)) as [Hin_full | Htail].
  - destruct (Z.eqb_spec (Z.rem (i + 1) 3) 1) as [Hmod | Hmod].
    + split; [lia |].
      rewrite Z.rem_mod_nonneg in Hmod by lia.
      pose proof (mod_full_tail_case_38 (full_decode_len len) i ltac:(lia) Hfull_mod Hmod).
      lia.
    + split; [| lia].
      destruct (Z.eq_dec i 0) as [-> | Hnz]; [| lia].
      exfalso.
      apply Hmod.
      reflexivity.
  - lia.
Qed.
Lemma decode_source_index_nat : forall len i,
  Z.to_nat (decode_source_index (Z.of_nat len) (Z.of_nat i)) =
  decode_cyclic_source_index len i.
Proof.
  intros len i.
  unfold decode_source_index, decode_cyclic_source_index, full_decode_len.
  rewrite Z.quot_div_nonneg by lia.
  replace (Z.of_nat len / 3 * 3) with (Z.of_nat (len / 3 * 3)).
  2:{ rewrite Nat2Z.inj_mul, Nat2Z.inj_div. reflexivity. }
  destruct (Z.ltb_spec (Z.of_nat i) (Z.of_nat (len / 3 * 3))) as [Hlt | Hge].
  - replace (i <? len / 3 * 3)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    replace (Z.of_nat (i + 1)) with (Z.of_nat i + 1) by lia.
    rewrite Z.rem_mod_nonneg by lia.
    replace ((Z.of_nat i + 1) mod 3) with (Z.of_nat ((i + 1) mod 3)).
    2:{
      replace (Z.of_nat i + 1) with (Z.of_nat (i + 1)) by lia.
      change 3 with (Z.of_nat 3).
      apply Nat2Z.inj_mod.
    }
    destruct (Z.eqb_spec (Z.of_nat ((i + 1) mod 3)) 1) as [Hmod | Hmod].
    + replace ((i + 1) mod 3 =? 1)%nat with true.
      * lia.
      * symmetry. apply Nat.eqb_eq. lia.
    + replace ((i + 1) mod 3 =? 1)%nat with false.
      * assert (0 < i)%nat.
        {
          destruct i; [cbn in Hmod; contradiction | lia].
        }
        lia.
      * symmetry. apply Nat.eqb_neq. lia.
  - replace (i <? len / 3 * 3)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    lia.
Qed.
Lemma problem_38_spec_intro : forall input output len,
  ascii_range input ->
  Zlength input = len ->
  Zlength output = len ->
  (forall k, 0 <= k < len ->
    Znth k output 0 = decode_char len input k) ->
  problem_38_spec input output.
Proof.
  intros input output len Hrange Hin Hout Hpoint.
  unfold problem_38_spec, problem_38_spec.
  split.
  - apply Nat2Z.inj.
    repeat rewrite string_of_list_Zlength.
    lia.
  - intros i Hi.
    assert (Hiz : 0 <= Z.of_nat i < len).
    {
      apply Nat2Z.inj_lt in Hi.
      rewrite string_of_list_length in Hi.
      rewrite <- Zlength_correct in Hi.
      lia.
    }
    pose proof (decode_source_index_range len (Z.of_nat i) ltac:(lia) Hiz) as Hsrc.
    unfold get_char.
    replace (String.get i (string_of_list output)) with
      (String.get (Z.to_nat (Z.of_nat i)) (string_of_list output))
      by now rewrite Nat2Z.id.
    rewrite (string_get_string_of_list_Znth output (Z.of_nat i)).
    2:{ rewrite Hout. lia. }
    rewrite Hpoint by lia.
    unfold decode_char.
    assert (Hsrc_input : 0 <= decode_source_index len (Z.of_nat i) < Zlength input) by lia.
    replace (decode_cyclic_source_index (String.length (string_of_list input)) i)
      with (Z.to_nat (decode_source_index len (Z.of_nat i))).
    2:{
      assert (Hlen_eq_nat : len = Z.of_nat (String.length (string_of_list input))).
      {
        rewrite string_of_list_Zlength.
        lia.
      }
      rewrite Hlen_eq_nat.
      apply decode_source_index_nat.
    }
    rewrite (string_get_string_of_list_Znth input (decode_source_index len (Z.of_nat i))) by exact Hsrc_input.
    reflexivity.
Qed.


Ltac decode_pre :=
  pre_process;
  repeat rewrite app_Znth1 in * by lia.

Ltac decode_source_open_true :=
  unfold decode_source_index;
  replace (Z.ltb _ _) with true by (symmetry; apply Z.ltb_lt; lia);
  replace (Z.eqb (Z.rem (_ + 1) 3) 1) with true by
    (symmetry; apply Z.eqb_eq; assumption).

Ltac decode_source_open_false :=
  unfold decode_source_index;
  replace (Z.ltb _ _) with true by (symmetry; apply Z.ltb_lt; lia);
  replace (Z.eqb (Z.rem (_ + 1) 3) 1) with false by
    (symmetry; apply Z.eqb_neq; assumption).

Ltac decode_source_tail :=
  unfold decode_source_index;
  replace (Z.ltb _ _) with false by (symmetry; apply Z.ltb_ge; lia).

Ltac prove_source_range :=
  match goal with
  | Hsrc : decode_source_index ?len ?i = ?src |- _ =>
      pose proof (decode_source_index_range len i ltac:(lia) ltac:(lia)) as Hrange;
      rewrite Hsrc in Hrange;
      lia
  end.

Ltac finish_decode_step :=
  entailer!;
  [ intros k Hk;
    match goal with
    | Hlen : Zlength ?old = ?idx,
      Hpref : forall k : Z, _ -> Znth k ?old 0 = decode_char ?len ?l k |- _ =>
        destruct (Z_lt_ge_dec k idx) as [Hlt | Hge]
        ; [ rewrite app_Znth1 by lia; apply Hpref; lia
          | assert (k = idx) by lia; subst k;
            rewrite app_Znth2 by lia;
            replace (idx - Zlength old) with 0 by lia;
            rewrite Znth0_cons;
            repeat rewrite app_Znth1 by lia;
            unfold decode_char;
            match goal with
            | Hsrc : decode_source_index len idx = _ |- _ => rewrite Hsrc
            end;
            reflexivity ]
    end
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Lemma proof_of_p038_decode_cyclic_safety_wit_3 : p038_decode_cyclic_safety_wit_3.
Proof.
  unfold p038_decode_cyclic_safety_wit_3.
  intros.
  pre_process.
  subst.
  entailer!.
  all: pose proof (full_decode_len_bounds (Zlength l) ltac:(lia)) as [[Hge Hle] _];
       unfold full_decode_len in *;
       lia.
Qed.

Lemma proof_of_p038_decode_cyclic_entail_wit_1 : p038_decode_cyclic_entail_wit_1.
Proof.
  unfold p038_decode_cyclic_entail_wit_1.
  intros.
  decode_pre.
  subst retval.
  Exists nil.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval_2 0 (len + 1)).
  rewrite (CharArray.undef_seg_empty retval_2 0).
  rewrite (CharArray.full_empty retval_2 0).
  unfold full_decode_len.
  entailer!.
  lia.
Qed.

Lemma proof_of_p038_decode_cyclic_entail_wit_2 : p038_decode_cyclic_entail_wit_2.
Proof.
  unfold p038_decode_cyclic_entail_wit_2.
  intros.
  decode_pre.
  Exists out_l_2.
  assert (Hsrc : decode_source_index len i = i + 2).
  {
    decode_source_open_true.
    reflexivity.
  }
  entailer!.
  prove_source_range.
Qed.

Lemma proof_of_p038_decode_cyclic_entail_wit_3 : p038_decode_cyclic_entail_wit_3.
Proof.
  unfold p038_decode_cyclic_entail_wit_3.
  intros.
  decode_pre.
  Exists out_l_2.
  assert (Hsrc : decode_source_index len i = i - 1).
  {
    decode_source_open_false.
    reflexivity.
  }
  entailer!.
  prove_source_range.
Qed.

Lemma proof_of_p038_decode_cyclic_entail_wit_4 : p038_decode_cyclic_entail_wit_4.
Proof.
  unfold p038_decode_cyclic_entail_wit_4.
  intros.
  decode_pre.
  Exists out_l_2.
  assert (Hsrc : decode_source_index len i = i).
  {
    decode_source_tail.
    reflexivity.
  }
  entailer!.
Qed.

Lemma proof_of_p038_decode_cyclic_entail_wit_5_1 : p038_decode_cyclic_entail_wit_5_1.
Proof.
  unfold p038_decode_cyclic_entail_wit_5_1.
  intros.
  decode_pre.
  Exists (app out_l_2 (cons (Znth (i + 2) l 0) nil)).
  entailer!.
  - intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      match goal with
      | Hpref : forall k : Z, _ -> Znth k out_l_2 0 = decode_char len l k |- _ =>
          apply Hpref; lia
      end.
    + assert (k = i) by lia. subst k.
      rewrite app_Znth2 by lia.
      replace (i - Zlength out_l_2) with 0 by lia.
      rewrite Znth0_cons.
      unfold decode_char.
      match goal with
      | Hsrc : decode_source_index len i = _ |- _ => rewrite Hsrc
      end.
      reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_p038_decode_cyclic_entail_wit_5_2 : p038_decode_cyclic_entail_wit_5_2.
Proof.
  unfold p038_decode_cyclic_entail_wit_5_2.
  intros.
  decode_pre.
  Exists (app out_l_2 (cons (Znth (i - 1) l 0) nil)).
  entailer!.
  - intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      match goal with
      | Hpref : forall k : Z, _ -> Znth k out_l_2 0 = decode_char len l k |- _ =>
          apply Hpref; lia
      end.
    + assert (k = i) by lia. subst k.
      rewrite app_Znth2 by lia.
      replace (i - Zlength out_l_2) with 0 by lia.
      rewrite Znth0_cons.
      unfold decode_char.
      match goal with
      | Hsrc : decode_source_index len i = _ |- _ => rewrite Hsrc
      end.
      reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_p038_decode_cyclic_entail_wit_5_3 : p038_decode_cyclic_entail_wit_5_3.
Proof.
  unfold p038_decode_cyclic_entail_wit_5_3.
  intros.
  decode_pre.
  Exists (app out_l_2 (cons (Znth i l 0) nil)).
  entailer!.
  - intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      match goal with
      | Hpref : forall k : Z, _ -> Znth k out_l_2 0 = decode_char len l k |- _ =>
          apply Hpref; lia
      end.
    + assert (k = i) by lia. subst k.
      rewrite app_Znth2 by lia.
      replace (i - Zlength out_l_2) with 0 by lia.
      rewrite Znth0_cons.
      unfold decode_char.
      match goal with
      | Hsrc : decode_source_index len i = _ |- _ => rewrite Hsrc
      end.
      reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_p038_decode_cyclic_return_wit_1 : p038_decode_cyclic_return_wit_1.
Proof.
  unfold p038_decode_cyclic_return_wit_1.
  intros.
  decode_pre.
  assert (i = len) by lia.
  subst i.
  Exists out_l_2.
  rewrite (CharArray.undef_seg_empty out (len + 1)).
  replace (Zlength out_l_2 + 1) with (len + 1) by lia.
  entailer!.
  - apply problem_38_spec_intro with (len := len); try lia.
    + match goal with
      | Hrange : ascii_range l |- _ => exact Hrange
      end.
    + intros k Hk.
      match goal with
      | Hpref : forall k : Z, _ -> Znth k out_l_2 0 = decode_char len l k |- _ =>
          apply Hpref; lia
      end.
  - intros k Hk.
    match goal with
    | Hpref : forall k0 : Z, _ -> Znth k0 out_l_2 0 = _ |- _ =>
        rewrite (Hpref k ltac:(lia))
    end;
    unfold decode_char;
    match goal with
    | Hnz : forall k0 : Z, _ -> Znth k0 l 0 <> 0 |- _ =>
        apply Hnz;
        pose proof (decode_source_index_range len k ltac:(lia) ltac:(lia));
        lia
    end.
Qed.
