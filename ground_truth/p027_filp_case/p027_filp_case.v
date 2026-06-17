(* spec/27 *)
(* """ For a given string, flip lowercase characters to uppercase and uppercase to lowercase.
>>> flip_case('Hello')
'hELLO'
""" *)

(* Spec(input : string, output : string) :=

​	length(input) = length(output) ∧
​	∀i ∈ [0, length(input)),  IsLow(input[i]) → output[i] = Upper(input[i]) ∧ IsUp(input[i]) → output[i] = Lower(input[i])*)

Require Import String Ascii Arith Bool.

Definition IsLow (c : ascii) : Prop :=
  (nat_of_ascii "a" <= nat_of_ascii c)%nat /\
  (nat_of_ascii c <= nat_of_ascii "z")%nat.

Definition IsUp (c : ascii) : Prop :=
  (nat_of_ascii "A" <= nat_of_ascii c)%nat /\
  (nat_of_ascii c <= nat_of_ascii "Z")%nat.

Definition Upper (c : ascii) : ascii :=
  if (nat_of_ascii "a" <=? nat_of_ascii c)%nat &&
     (nat_of_ascii c <=? nat_of_ascii "z")%nat
  then ascii_of_nat (nat_of_ascii c - 32)
  else c.

Definition Lower (c : ascii) : ascii :=
  if (nat_of_ascii "A" <=? nat_of_ascii c)%nat &&
     (nat_of_ascii c <=? nat_of_ascii "Z")%nat
  then ascii_of_nat (nat_of_ascii c + 32)
  else c.

(* Pre: no additional constraints for `flip_case` by default *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition is_lower (c : Z) : Prop :=
  97 <= c <= 122.

Definition is_upper (c : Z) : Prop :=
  65 <= c <= 90.

Definition flip_char (c : Z) : Z :=
  if (Z.leb 97 c) && (Z.leb c 122) then c - 32
  else if (Z.leb 65 c) && (Z.leb c 90) then c + 32
  else c.

Definition char_range (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition problem_27_pre (s : list Z) : Prop :=
  True.

Definition problem_27_spec (input output : list Z) : Prop :=
  ((String.length ((string_of_list input)) = String.length ((string_of_list output)) /\
    (forall (i : nat) (c : ascii),
      i < String.length ((string_of_list input)) ->
      String.get i ((string_of_list input)) = Some c ->
      (IsLow c -> String.get i ((string_of_list output)) = Some (Upper c)) /\
      (IsUp c -> String.get i ((string_of_list output)) = Some (Lower c)) /\
      (~IsLow c /\ ~IsUp c -> String.get i ((string_of_list output)) = Some c)))%nat).

Lemma string_of_list_length_nat : forall l,
  String.length (string_of_list l) = List.length l.
Proof.
  induction l; simpl; auto.
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

Lemma nat_of_ascii_ascii_of : forall c,
  0 <= c <= 127 ->
  nat_of_ascii (ascii_of c) = Z.to_nat c.
Proof.
  intros c Hc.
  unfold ascii_of.
  apply nat_ascii_embedding.
  lia.
Qed.

Lemma flip_char_range : forall c,
  0 <= c <= 127 ->
  0 <= flip_char c <= 127.
Proof.
  unfold flip_char.
  intros c Hrange.
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      destruct (Z.leb_spec x y); simpl
  end; lia.
Qed.

Lemma flip_char_nonzero : forall c,
  0 <= c <= 127 ->
  c <> 0 ->
  flip_char c <> 0.
Proof.
  unfold flip_char.
  intros c Hrange Hnz.
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      destruct (Z.leb_spec x y); simpl
  end; lia.
Qed.

Lemma IsLow_ascii_of_to_is_lower : forall c,
  0 <= c <= 127 ->
  IsLow (ascii_of c) ->
  is_lower c.
Proof.
  unfold IsLow, is_lower.
  intros c Hrange H.
  rewrite nat_of_ascii_ascii_of in H by lia.
  cbn in H.
  lia.
Qed.

Lemma IsUp_ascii_of_to_is_upper : forall c,
  0 <= c <= 127 ->
  IsUp (ascii_of c) ->
  is_upper c.
Proof.
  unfold IsUp, is_upper.
  intros c Hrange H.
  rewrite nat_of_ascii_ascii_of in H by lia.
  cbn in H.
  lia.
Qed.

Lemma Upper_ascii_of_lower : forall c,
  is_lower c ->
  Upper (ascii_of c) = ascii_of (flip_char c).
Proof.
  unfold is_lower, flip_char.
  intros c Hc.
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
  end.
  simpl.
  unfold Upper.
  rewrite nat_of_ascii_ascii_of by lia.
  replace ((nat_of_ascii "a" <=? Z.to_nat c)%nat) with true
    by (symmetry; apply Nat.leb_le; cbn; lia).
  replace ((Z.to_nat c <=? nat_of_ascii "z")%nat) with true
    by (symmetry; apply Nat.leb_le; cbn; lia).
  simpl.
  unfold ascii_of.
  replace (Z.to_nat (c - 32)) with (Z.to_nat c - 32)%nat by lia.
  reflexivity.
Qed.

Lemma Lower_ascii_of_upper : forall c,
  is_upper c ->
  Lower (ascii_of c) = ascii_of (flip_char c).
Proof.
  unfold is_upper, flip_char.
  intros c Hc.
  replace (Z.leb 97 c) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb 65 c) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb c 90) with true by (symmetry; apply Z.leb_le; lia).
  simpl.
  unfold Lower.
  rewrite nat_of_ascii_ascii_of by lia.
  replace ((nat_of_ascii "A" <=? Z.to_nat c)%nat) with true
    by (symmetry; apply Nat.leb_le; cbn; lia).
  replace ((Z.to_nat c <=? nat_of_ascii "Z")%nat) with true
    by (symmetry; apply Nat.leb_le; cbn; lia).
  simpl.
  unfold ascii_of.
  replace (Z.to_nat (c + 32)) with (Z.to_nat c + 32)%nat by lia.
  reflexivity.
Qed.

Lemma flip_char_other : forall c,
  0 <= c <= 127 ->
  ~ IsLow (ascii_of c) ->
  ~ IsUp (ascii_of c) ->
  flip_char c = c.
Proof.
  intros c Hrange Hnotlow Hnotup.
  unfold flip_char.
  destruct (Z.leb_spec 97 c); simpl.
  - destruct (Z.leb_spec c 122); simpl.
    + exfalso. apply Hnotlow.
      unfold IsLow.
      rewrite nat_of_ascii_ascii_of by lia.
      cbn. lia.
    + destruct (Z.leb_spec 65 c); simpl.
      * destruct (Z.leb_spec c 90); simpl; [lia | reflexivity].
      * reflexivity.
  - destruct (Z.leb_spec 65 c); simpl.
    + destruct (Z.leb_spec c 90); simpl.
      * exfalso. apply Hnotup.
        unfold IsUp.
        rewrite nat_of_ascii_ascii_of by lia.
        cbn. lia.
      * reflexivity.
    + reflexivity.
Qed.

Lemma problem_27_spec_intro : forall input output n,
  char_range input ->
  Zlength input = n ->
  Zlength output = n ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = flip_char (Znth k input 0)) ->
  problem_27_spec input output.
Proof.
  intros input output n Hrange Hin Hout Hpoint.
  unfold problem_27_spec.
  split.
  - rewrite !string_of_list_length_nat.
    apply Nat2Z.inj.
    rewrite <- !Zlength_correct.
    lia.
  - intros i c Hi Hget.
    assert (Hiz : 0 <= Z.of_nat i < Zlength input).
    {
      split; [lia |].
      rewrite string_of_list_length_nat in Hi.
      apply Nat2Z.inj_lt in Hi.
      rewrite <- Zlength_correct in Hi.
      lia.
    }
    pose proof (string_get_string_of_list_nth input i) as Hin_get.
    specialize (Hin_get ltac:(rewrite <- string_of_list_length_nat; exact Hi)).
    rewrite Hget in Hin_get.
    inversion Hin_get; subst c; clear Hin_get.
    pose proof (Hrange (Z.of_nat i) Hiz) as Hchar.
    assert (Houtz : 0 <= Z.of_nat i < Zlength output) by lia.
    rewrite (string_get_string_of_list_nth output i).
    2:{
      apply Nat2Z.inj_lt.
      rewrite <- Zlength_correct.
      lia.
    }
    rewrite Hpoint by lia.
    split.
    + intro Hlow.
      pose proof (IsLow_ascii_of_to_is_lower _ Hchar Hlow) as Hzlow.
      rewrite <- Upper_ascii_of_lower by exact Hzlow.
      reflexivity.
    + split.
      * intro Hup.
        pose proof (IsUp_ascii_of_to_is_upper _ Hchar Hup) as Hzup.
        rewrite <- Lower_ascii_of_upper by exact Hzup.
        reflexivity.
      * intros [Hnotlow Hnotup].
        rewrite (flip_char_other _ Hchar Hnotlow Hnotup).
        reflexivity.
Qed.
