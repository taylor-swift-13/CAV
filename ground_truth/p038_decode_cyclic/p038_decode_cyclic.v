(* spec/38 *)
(* def encode_cyclic(s: str):
"""
returns encoded string by cycling groups of three characters.
"""

def decode_cyclic(s: str):
"""
takes as input string encoded with encode_cyclic function. Returns decoded string.
"""
*)

(*
  Spec(input ：string, output : string) :=

​	∃n， n = (length(input) / 3) *3 -1  /\
​		(∀i ∈ [0, length(input)),   i+1 % 3 = 0  → i ≤ n) /\
​		(∀i ∈ [0, n], i+1 % 3 = 2 → output[i] = input[i-1] /\
​							  i+1 % 3 = 1 → output[i] = input[i+2] /\
​							  i+1 % 3 =0 → output[i] = input[i-1]) /\
​		(∀i ∈ (n, length(input)), output[i] = input[i]) *)

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope string_scope.

Definition get_char (s : string) (n : nat) : ascii :=
  match String.get n s with
  | Some c => c
  | None => " "%char
  end.

(* Pre: no additional constraints for `encode/decode_cyclic` by default *)

Definition decode_cyclic_source_index (len i : nat) : nat :=
  let full_len := ((len / 3) * 3)%nat in
  if (i <? full_len)%nat then
    if ((i + 1) mod 3 =? 1)%nat then i + 2 else i - 1
  else i.


Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Export string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition problem_38_pre (input : list Z) : Prop :=
  True.

Definition full_decode_len (len : Z) : Z :=
  (len ÷ 3) * 3.

Definition decode_source_index (len i : Z) : Z :=
  if Z.ltb i (full_decode_len len) then
    if Z.eqb (Z.rem (i + 1) 3) 1 then i + 2 else i - 1
  else i.

Definition decode_char (len : Z) (input : list Z) (i : Z) : Z :=
  Znth (decode_source_index len i) input 0.

Definition problem_38_spec (input output : list Z) : Prop :=
  ((String.length ((string_of_list input)) = String.length ((string_of_list output)) /\
    forall i, (i < String.length ((string_of_list input)))%nat ->
      get_char ((string_of_list output)) i =
      get_char ((string_of_list input)) (decode_cyclic_source_index (String.length ((string_of_list input))) i))%nat).

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
