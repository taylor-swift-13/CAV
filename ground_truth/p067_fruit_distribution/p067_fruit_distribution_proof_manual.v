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
From SimpleC.EE.CAV.ground_truth_p067_fruit_distribution Require Import p067_fruit_distribution_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import ZArith Strings.String.
Require Import Coq.Strings.Ascii.

Import naive_C_Rules.
Require Import p067_fruit_distribution.
Local Open Scope sac.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p067_fruit_distribution.v so public contract files expose definitions only. *)

Lemma fruit_state_after_step : forall i s st,
  0 <= i ->
  fruit_state_after_nat (Z.to_nat i) s = st ->
  fruit_state_after_nat (Z.to_nat (i + 1)) s =
  fruit_step st (Znth i s 0).
Proof.
  intros i s st Hi Hst.
  rewrite Z2Nat.inj_add by lia.
  change (Z.to_nat 1) with 1%nat.
  rewrite Nat.add_1_r.
  simpl.
  rewrite Z2Nat.id by lia.
  rewrite Hst.
  reflexivity.
Qed.
Lemma fruit_prefix_step : forall i s,
  0 <= i ->
  (fruit_num1_prefix (i + 1) s,
   fruit_num2_prefix (i + 1) s,
   fruit_cur_prefix (i + 1) s) =
  fruit_step
    (fruit_num1_prefix i s, fruit_num2_prefix i s, fruit_cur_prefix i s)
    (Znth i s 0).
Proof.
  intros i s Hi.
  unfold fruit_num1_prefix, fruit_num2_prefix, fruit_cur_prefix.
  destruct (fruit_state_after_nat (Z.to_nat i) s) as [[num1 num2] cur] eqn:Hst.
  rewrite (fruit_state_after_step i s (num1, num2, cur) Hi Hst).
  destruct (fruit_step (num1, num2, cur) (Znth i s 0)) as [[num1' num2'] cur'].
  reflexivity.
Qed.
Lemma fruit_state_range_from_safe : forall s i,
  fruit_state_safe s ->
  0 <= i <= Zlength s ->
  fruit_state_range_at i s.
Proof.
  intros s i [Hrange _] Hi.
  apply Hrange; lia.
Qed.
Lemma fruit_digit_update_safe_from_safe : forall s i,
  fruit_state_safe s ->
  0 <= i < Zlength s ->
  fruit_digit_update_safe i s.
Proof.
  intros s i [_ Hsafe] Hi.
  apply Hsafe; lia.
Qed.
Lemma fruit_output_safe_from_safe : forall s total,
  fruit_output_safe s total ->
  fruit_output_safe s total.
Proof.
  auto.
Qed.
Lemma nat_of_ascii_ascii_of_67 : forall z,
  0 <= z < 256 ->
  nat_of_ascii (ascii_of z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.
Lemma spec67_scan_step_ascii_of : forall st c,
  0 <= c < 256 ->
  fruit_step st c = spec67_scan_step st (ascii_of c).
Proof.
  intros [[num1 num2] cur] c Hc.
  unfold fruit_step, spec67_scan_step, digit_value, spec67_digit,
         fruit_commit_num1, fruit_commit_num2,
         spec67_commit_num1, spec67_commit_num2.
  rewrite nat_of_ascii_ascii_of_67 by exact Hc.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma list_ascii_of_string_string_of_list_67 : forall l,
  list_ascii_of_string (string_of_list l) = map ascii_of l.
Proof.
  induction l; simpl; congruence.
Qed.
Lemma spec67_scan_state_left_app : forall l1 l2 st,
  spec67_scan_state_left st (l1 ++ l2) =
  spec67_scan_state_left (spec67_scan_state_left st l1) l2.
Proof.
  induction l1 as [| c rest IH]; intros l2 st; simpl; auto.
Qed.
Lemma firstn_succ_nth_67 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = (firstn n l ++ [nth n l d])%list.
Proof.
  induction n as [| n IH]; intros l d Hlen.
  - destruct l; simpl in *; try lia; reflexivity.
  - destruct l; simpl in *; try lia.
    f_equal.
    apply IH.
    lia.
Qed.
Lemma spec67_scan_state_left_prefix_ascii : forall k l,
  ascii_range l ->
  (k <= List.length l)%nat ->
  spec67_scan_state_left ((-1)%Z, (-1)%Z, (-1)%Z)
    (firstn k (map ascii_of l)) =
  fruit_state_after_nat k l.
Proof.
  induction k as [| k IH]; intros l Hrange Hk.
  - reflexivity.
  - rewrite (firstn_succ_nth_67 k (map ascii_of l) (ascii_of 0%Z))
      by (rewrite map_length; lia).
    rewrite spec67_scan_state_left_app.
    rewrite IH by (assumption || lia).
    rewrite map_nth with (d := 0%Z) by lia.
    simpl.
    unfold Znth.
    rewrite Nat2Z.id.
    rewrite spec67_scan_step_ascii_of.
    + reflexivity.
    + specialize (Hrange (Z.of_nat k)).
      unfold Znth in Hrange.
      rewrite Nat2Z.id in Hrange.
      apply Hrange.
      rewrite Zlength_correct.
      lia.
Qed.
Lemma spec67_scan_state_full_ascii_of : forall l,
  ascii_range l ->
  spec67_scan_state_full (map ascii_of l) =
  fruit_state_after_nat (List.length l) l.
Proof.
  intros l Hrange.
  unfold spec67_scan_state_full.
  replace (map ascii_of l) with
    (firstn (List.length l) (map ascii_of l)) at 1.
  - apply spec67_scan_state_left_prefix_ascii.
    + exact Hrange.
    + lia.
  - replace (List.length l) with (List.length (map ascii_of l))
      by (rewrite map_length; reflexivity).
    exact (firstn_all (map ascii_of l)).
Qed.
Lemma fruit_output_spec67_scan_output : forall s total,
  ascii_range s ->
  0 <= total ->
  spec67_scan_output (string_of_list s) (Z.to_nat total) =
  fruit_output s total.
Proof.
  intros s total Hrange Htotal.
  unfold spec67_scan_output, fruit_output.
  rewrite list_ascii_of_string_string_of_list_67.
  rewrite spec67_scan_state_full_ascii_of by exact Hrange.
  rewrite Z2Nat.id by lia.
  unfold fruit_final_num1, fruit_final_num2,
         fruit_flush_num1, fruit_flush_num2,
         fruit_num1_prefix, fruit_num2_prefix, fruit_cur_prefix.
  replace (Z.to_nat (Zlength s)) with (List.length s).
  - destruct (fruit_state_after_nat (List.length s) s) as [[num1 num2] cur].
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma list_ascii_of_string_app_67 : forall a b,
  list_ascii_of_string (a ++ b) =
  (list_ascii_of_string a ++ list_ascii_of_string b)%list.
Proof.
  induction a; intros b; simpl; auto.
  rewrite IHa; reflexivity.
Qed.
Lemma spec67_digit_z_nat : forall c,
  (48 <= nat_of_ascii c <= 57)%nat ->
  spec67_digit c = Z.of_nat (char_to_digit c).
Proof.
  intros c Hc.
  unfold spec67_digit, char_to_digit.
  change (nat_of_ascii "0"%char) with 48%nat.
  rewrite Nat2Z.inj_sub by lia.
  lia.
Qed.
Lemma spec67_scan_digits_acc : forall s n1 n2 acc,
  (forall c, In c (list_ascii_of_string s) ->
    (48 <= nat_of_ascii c <= 57)%nat) ->
  spec67_scan_state_left (n1, n2, Z.of_nat acc) (list_ascii_of_string s) =
    (n1, n2, Z.of_nat (string_to_nat_aux s acc)).
Proof.
  induction s as [| c rest IH]; intros n1 n2 acc Hdigits.
  - reflexivity.
  - simpl in Hdigits |- *.
    assert (Hc : (48 <= nat_of_ascii c <= 57)%nat) by
      (apply Hdigits; left; reflexivity).
    assert (Hrest : forall x, In x (list_ascii_of_string rest) ->
      (48 <= nat_of_ascii x <= 57)%nat) by
      (intros x Hx; apply Hdigits; right; exact Hx).
    unfold spec67_scan_step.
    replace (andb (Z.leb 48 (Z.of_nat (nat_of_ascii c)))
                  (Z.leb (Z.of_nat (nat_of_ascii c)) 57)) with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    replace (Z.ltb (Z.of_nat acc) 0) with false
      by (symmetry; apply Z.ltb_ge; lia).
    rewrite spec67_digit_z_nat by exact Hc.
    replace ((Z.of_nat acc * 10 + Z.of_nat (char_to_digit c))%Z)
      with (Z.of_nat (acc * 10 + char_to_digit c)) by lia.
    apply IH.
    exact Hrest.
Qed.
Lemma spec67_scan_digits_first : forall s n1 n2,
  s <> EmptyString ->
  (forall c, In c (list_ascii_of_string s) ->
    (48 <= nat_of_ascii c <= 57)%nat) ->
  spec67_scan_state_left (n1, n2, (-1)%Z) (list_ascii_of_string s) =
    (n1, n2, Z.of_nat (string_to_nat s)).
Proof.
  destruct s as [| c rest]; intros n1 n2 Hnonempty Hdigits; [contradiction|].
  simpl in Hdigits |- *.
  assert (Hc : (48 <= nat_of_ascii c <= 57)%nat) by
    (apply Hdigits; left; reflexivity).
  assert (Hrest : forall x, In x (list_ascii_of_string rest) ->
    (48 <= nat_of_ascii x <= 57)%nat) by
    (intros x Hx; apply Hdigits; right; exact Hx).
  unfold spec67_scan_step.
  replace (andb (Z.leb 48 (Z.of_nat (nat_of_ascii c)))
                (Z.leb (Z.of_nat (nat_of_ascii c)) 57)) with true
    by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  replace (Z.ltb (-1) 0) with true by reflexivity.
  rewrite spec67_digit_z_nat by exact Hc.
  change (if true then 0%Z else (-1)%Z) with 0%Z.
  change (string_to_nat (String c rest)) with
    (string_to_nat_aux rest (char_to_digit c)).
  replace ((0 * 10 + Z.of_nat (char_to_digit c))%Z)
    with (Z.of_nat (char_to_digit c)) by lia.
  apply spec67_scan_digits_acc.
  exact Hrest.
Qed.
Lemma spec67_scan_step_non_digit_no_cur : forall n1 n2 c,
  (Z.of_nat (nat_of_ascii c) < 48 \/
   57 < Z.of_nat (nat_of_ascii c))%Z ->
  spec67_scan_step (n1, n2, (-1)%Z) c = (n1, n2, (-1)%Z).
Proof.
  intros n1 n2 c Hnot.
  unfold spec67_scan_step.
  replace (andb (Z.leb 48 (Z.of_nat (nat_of_ascii c)))
                (Z.leb (Z.of_nat (nat_of_ascii c)) 57)) with false.
  - reflexivity.
  - symmetry.
    apply andb_false_iff.
    destruct Hnot as [Hlt | Hgt].
    + left. apply Z.leb_gt. lia.
    + right. apply Z.leb_gt. lia.
Qed.
Lemma spec67_scan_step_non_digit_commit : forall n1 n2 cur c,
  0 <= cur ->
  (Z.of_nat (nat_of_ascii c) < 48 \/
   57 < Z.of_nat (nat_of_ascii c))%Z ->
  spec67_scan_step (n1, n2, cur) c =
    (spec67_commit_num1 n1 cur,
     spec67_commit_num2 n1 n2 cur,
     (-1)%Z).
Proof.
  intros n1 n2 cur c Hcur Hnot.
  unfold spec67_scan_step.
  replace (andb (Z.leb 48 (Z.of_nat (nat_of_ascii c)))
                (Z.leb (Z.of_nat (nat_of_ascii c)) 57)) with false.
  - replace (Z.leb 0 cur) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity.
  - symmetry.
    apply andb_false_iff.
    destruct Hnot as [Hlt | Hgt].
    + left. apply Z.leb_gt. lia.
    + right. apply Z.leb_gt. lia.
Qed.
Ltac solve_ascii_non_digit :=
  first [left; vm_compute; lia | right; vm_compute; lia].
Lemma spec67_scan_apples_sep : forall apples,
  spec67_scan_state_left ((-1)%Z, (-1)%Z, Z.of_nat apples)
    (list_ascii_of_string " apples and ") =
    (Z.of_nat apples, (-1)%Z, (-1)%Z).
Proof.
  intros apples.
  cbn [list_ascii_of_string spec67_scan_state_left].
  pose proof (spec67_scan_step_non_digit_commit
    (-1)%Z (-1)%Z (Z.of_nat apples) " "%char
    ltac:(lia)
    ltac:(left; change (Z.of_nat (nat_of_ascii " "%char)) with 32%Z; lia)) as Hstep.
  rewrite Hstep; clear Hstep.
  unfold spec67_commit_num1, spec67_commit_num2.
  replace (Z.ltb (Z.of_nat apples) 0) with false
    by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.ltb (-1) 0) with true by reflexivity.
  cbn.
  repeat rewrite spec67_scan_step_non_digit_no_cur by solve_ascii_non_digit.
  reflexivity.
Qed.
Lemma spec67_scan_oranges_sep : forall apples oranges,
  spec67_scan_state_left (Z.of_nat apples, (-1)%Z, Z.of_nat oranges)
    (list_ascii_of_string " oranges") =
    (Z.of_nat apples, Z.of_nat oranges, (-1)%Z).
Proof.
  intros apples oranges.
  cbn [list_ascii_of_string spec67_scan_state_left].
  pose proof (spec67_scan_step_non_digit_commit
    (Z.of_nat apples) (-1)%Z (Z.of_nat oranges) " "%char
    ltac:(lia)
    ltac:(left; change (Z.of_nat (nat_of_ascii " "%char)) with 32%Z; lia)) as Hstep.
  rewrite Hstep; clear Hstep.
  unfold spec67_commit_num1, spec67_commit_num2.
  replace (Z.ltb (Z.of_nat apples) 0) with false
    by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.ltb (-1) 0) with true by reflexivity.
  cbn.
  repeat rewrite spec67_scan_step_non_digit_no_cur by solve_ascii_non_digit.
  reflexivity.
Qed.
Lemma Z_to_nat_sub_two : forall n a b,
  Z.to_nat (Z.of_nat n - Z.of_nat a - Z.of_nat b) =
  (n - (a + b))%nat.
Proof.
  intros n a b.
  replace (Z.of_nat n - Z.of_nat a - Z.of_nat b)%Z
    with (Z.of_nat n - Z.of_nat (a + b))%Z by lia.
  destruct (le_gt_dec (a + b) n) as [Hle | Hgt].
  - apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite Nat2Z.inj_sub by lia.
    lia.
  - replace (n - (a + b))%nat with 0%nat by lia.
    destruct (Z.of_nat n - Z.of_nat (a + b))%Z eqn:Hz; try reflexivity;
      exfalso; lia.
Qed.
Lemma spec67_scan_output_format : forall s_apples s_oranges n,
  s_apples <> EmptyString ->
  s_oranges <> EmptyString ->
  (forall c, In c (list_ascii_of_string s_apples) ->
    (48 <= nat_of_ascii c <= 57)%nat) ->
  (forall c, In c (list_ascii_of_string s_oranges) ->
    (48 <= nat_of_ascii c <= 57)%nat) ->
  spec67_scan_output
    (s_apples ++ " apples and " ++ s_oranges ++ " oranges") n =
  (Z.of_nat n - Z.of_nat (string_to_nat s_apples) -
   Z.of_nat (string_to_nat s_oranges))%Z.
Proof.
  intros s_apples s_oranges n Happles_nonempty Horanges_nonempty
    Happles_digits Horanges_digits.
  unfold spec67_scan_output, spec67_scan_state_full.
  repeat rewrite list_ascii_of_string_app_67.
  repeat rewrite spec67_scan_state_left_app.
  rewrite spec67_scan_digits_first by assumption.
  rewrite spec67_scan_apples_sep.
  rewrite spec67_scan_digits_first by assumption.
  rewrite spec67_scan_oranges_sep.
  unfold spec67_final_num1, spec67_final_num2,
         spec67_flush_num1, spec67_flush_num2,
         spec67_commit_num1, spec67_commit_num2.
  cbn.
  replace (Z.ltb (Z.of_nat (string_to_nat s_apples)) 0) with false
    by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.ltb (Z.of_nat (string_to_nat s_oranges)) 0) with false
    by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.
Lemma string_of_list_app : forall a b,
  string_of_list (a ++ b)%list =
  (string_of_list a ++ string_of_list b)%string.
Proof.
  induction a as [| c rest IH]; intros b; simpl; auto.
  rewrite IH; reflexivity.
Qed.
Lemma string_of_list_fruit_apples_and :
  string_of_list fruit_apples_and = " apples and ".
Proof. reflexivity. Qed.
Lemma string_of_list_fruit_oranges :
  string_of_list fruit_oranges = " oranges".
Proof. reflexivity. Qed.
Lemma string_of_list_nonempty : forall l,
  l <> [] ->
  string_of_list l <> EmptyString.
Proof.
  destruct l; simpl; congruence.
Qed.
Lemma char_to_digit_ascii_of : forall z,
  is_digit z ->
  Z.of_nat (char_to_digit (ascii_of z)) = digit_value z.
Proof.
  intros z Hdigit.
  unfold char_to_digit, digit_value, is_digit in *.
  change (nat_of_ascii "0"%char) with 48%nat.
  rewrite nat_of_ascii_ascii_of_67 by lia.
  rewrite Nat2Z.inj_sub by lia.
  rewrite Z2Nat.id by lia.
  lia.
Qed.
Lemma parse_digits_z_aux_string_to_nat_aux : forall l acc,
  all_digits_z l ->
  0 <= acc ->
  Z.of_nat (string_to_nat_aux (string_of_list l) (Z.to_nat acc)) =
  parse_digits_z_aux l acc.
Proof.
  induction l as [| c rest IH]; intros acc Hdigits Hacc.
  - simpl. rewrite Z2Nat.id by lia. reflexivity.
  - simpl in *.
    assert (Hc : is_digit c) by (apply Hdigits; left; reflexivity).
    assert (Hrest : all_digits_z rest) by
      (intros x Hx; apply Hdigits; right; exact Hx).
    replace (Z.to_nat acc * 10 + char_to_digit (ascii_of c))%nat with
      (Z.to_nat (acc * 10 + digit_value c)).
    + rewrite IH by (exact Hrest || unfold digit_value, is_digit in *; lia).
      reflexivity.
    + apply Nat2Z.inj.
      assert (Hnext : 0 <= acc * 10 + digit_value c) by
        (unfold digit_value, is_digit in *; lia).
      rewrite Nat2Z.inj_add.
      rewrite Nat2Z.inj_mul.
      rewrite Z2Nat.id by lia.
      rewrite char_to_digit_ascii_of by exact Hc.
      rewrite Z2Nat.id by (unfold digit_value, is_digit in *; lia).
      lia.
Qed.
Lemma string_to_nat_string_of_list_parse_digits : forall l,
  all_digits_z l ->
  Z.of_nat (string_to_nat (string_of_list l)) = parse_digits l.
Proof.
  intros l Hdigits.
  unfold string_to_nat, parse_digits.
  change 0%nat with (Z.to_nat 0).
  apply parse_digits_z_aux_string_to_nat_aux; auto; lia.
Qed.
Lemma string_of_list_digit_ascii_range : forall l,
  all_digits_z l ->
  forall c,
    In c (list_ascii_of_string (string_of_list l)) ->
    (48 <= nat_of_ascii c <= 57)%nat.
Proof.
  intros l Hdigits c Hc.
  rewrite list_ascii_of_string_string_of_list_67 in Hc.
  apply in_map_iff in Hc.
  destruct Hc as [z [Hz Hzin]]; subst c.
  specialize (Hdigits z Hzin).
  unfold is_digit in Hdigits.
  rewrite nat_of_ascii_ascii_of_67 by lia.
  lia.
Qed.
Lemma problem_67_spec_intro : forall s total output,
  problem_67_pre s total ->
  ascii_range s ->
  0 <= total ->
  output = fruit_output s total ->
  problem_67_spec s total output.
Proof.
  intros s total output Hpre Hrange Htotal Hout.
  unfold problem_67_pre in Hpre.
  destruct Hpre as [_ [s_apples [s_oranges
    [Happles_nonempty [Horanges_nonempty [Happles_digits
      [Horanges_digits Hs]]]]]]].
  unfold problem_67_spec.
  exists s_apples, s_oranges.
  split; [exact Happles_nonempty|].
  split; [exact Horanges_nonempty|].
  split; [exact Happles_digits|].
  split; [exact Horanges_digits|].
  split; [exact Hs|].
  subst output.
    rewrite <- fruit_output_spec67_scan_output by auto.
    rewrite Hs.
    repeat rewrite string_of_list_app.
    rewrite string_of_list_fruit_apples_and, string_of_list_fruit_oranges.
    rewrite spec67_scan_output_format.
  - rewrite Z2Nat.id by lia.
    repeat rewrite string_to_nat_string_of_list_parse_digits by assumption.
    reflexivity.
  - apply string_of_list_nonempty; exact Happles_nonempty.
  - apply string_of_list_nonempty; exact Horanges_nonempty.
  - apply string_of_list_digit_ascii_range; exact Happles_digits.
  - apply string_of_list_digit_ascii_range; exact Horanges_digits.
Qed.


Ltac fruit_pre :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia;
  unfold int_min, int_max, int_cur_mul10_bound in *.

Ltac simplify_zbool :=
  repeat match goal with
  | H : ?x <= ?y |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
  | H : ?y >= ?x |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
  | H : ?x > ?y |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with false by (symmetry; apply Z.leb_gt; lia)
  | H : ?y < ?x |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with false by (symmetry; apply Z.leb_gt; lia)
  | H : ?x < ?y |- context[Z.ltb ?x ?y] =>
      replace (Z.ltb x y) with true by (symmetry; apply Z.ltb_lt; lia)
  | H : ?y > ?x |- context[Z.ltb ?x ?y] =>
      replace (Z.ltb x y) with true by (symmetry; apply Z.ltb_lt; lia)
  | H : ?x >= ?y |- context[Z.ltb ?x ?y] =>
      replace (Z.ltb x y) with false by (symmetry; apply Z.ltb_ge; lia)
  | H : ?y <= ?x |- context[Z.ltb ?x ?y] =>
      replace (Z.ltb x y) with false by (symmetry; apply Z.ltb_ge; lia)
  end;
  simpl in *.

Ltac simplify_zbool_in Hctx :=
  repeat match type of Hctx with
  | context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with true in Hctx by (symmetry; apply Z.leb_le; lia)
  | context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with false in Hctx by (symmetry; apply Z.leb_gt; lia)
  | context[Z.ltb ?x ?y] =>
      replace (Z.ltb x y) with true in Hctx by (symmetry; apply Z.ltb_lt; lia)
  | context[Z.ltb ?x ?y] =>
      replace (Z.ltb x y) with false in Hctx by (symmetry; apply Z.ltb_ge; lia)
  end;
  simpl in Hctx.

Ltac use_digit_safe :=
  match goal with
  | Hsafe_all : fruit_state_safe ?l,
    Hi : ?i < Zlength ?l |- _ =>
      let Hsafe := fresh "Hdigit_safe" in
      pose proof (fruit_digit_update_safe_from_safe l i Hsafe_all ltac:(lia)) as Hsafe;
      unfold fruit_digit_update_safe, is_digit in Hsafe;
      specialize (Hsafe ltac:(lia));
      destruct Hsafe as [? | [? ?]];
      unfold int_cur_mul10_bound in *;
      lia
  end.

Ltac solve_digit_safety :=
  fruit_pre;
  entailer!;
  try use_digit_safe;
  lia.

Ltac solve_output_safety :=
  fruit_pre;
  match goal with
  | idx : Z, l : list Z |- _ =>
      assert (idx = Zlength l) by lia;
      subst idx
  end;
  entailer!;
  match goal with
  | Hsafe_out : fruit_output_safe ?l ?total |- _ =>
      let Hout := fresh "Hout" in
      pose proof (fruit_output_safe_from_safe l total Hsafe_out) as Hout;
      unfold fruit_output_safe, fruit_output in Hout;
      first
        [ match goal with
          | |- context[total - ?a - ?b] =>
              let Hf1 := fresh "Hf1" in
              let Hf2 := fresh "Hf2" in
              assert (Hf1 : fruit_final_num1 l = a) by
                (unfold fruit_final_num1, fruit_flush_num1,
                        fruit_commit_num1;
                 simplify_zbool; reflexivity);
              assert (Hf2 : fruit_final_num2 l = b) by
                (unfold fruit_final_num2, fruit_flush_num2,
                        fruit_commit_num2, fruit_commit_num1;
                 simplify_zbool; reflexivity);
              rewrite Hf1, Hf2 in Hout
          end
        | match goal with
          | |- context[total - ?a] =>
              let Hf1 := fresh "Hf1" in
              assert (Hf1 : fruit_final_num1 l = a) by
                (unfold fruit_final_num1, fruit_flush_num1,
                        fruit_commit_num1;
                 simplify_zbool; reflexivity);
              rewrite Hf1 in Hout
          end ];
      unfold int_min, int_max in Hout;
      lia
  end.

Ltac unfold_fruit_step :=
  match goal with
  | i : Z, l : list Z |- _ =>
      let Hstep := fresh "Hstep" in
      pose proof (fruit_prefix_step i l ltac:(lia)) as Hstep;
      unfold fruit_step, fruit_commit_num1, fruit_commit_num2,
             digit_value in Hstep;
      simplify_zbool_in Hstep;
      inversion Hstep;
      subst;
      clear Hstep
  end.

Ltac solve_fruit_step :=
  fruit_pre;
  unfold_fruit_step;
  entailer!;
  try use_digit_safe;
  lia.

Ltac solve_fruit_return :=
  fruit_pre;
  match goal with
  | idx : Z, l : list Z |- _ =>
      assert (idx = Zlength l) by lia;
      subst idx
  end;
  entailer!;
  apply problem_67_spec_intro; try assumption; try lia;
  unfold fruit_output;
  match goal with
  | |- ?total - ?a - ?b = ?total - fruit_final_num1 ?l - fruit_final_num2 ?l =>
      let Hf1 := fresh "Hf1" in
      let Hf2 := fresh "Hf2" in
      assert (Hf1 : fruit_final_num1 l = a) by
        (unfold fruit_final_num1, fruit_flush_num1,
                fruit_commit_num1;
         simplify_zbool; reflexivity);
      assert (Hf2 : fruit_final_num2 l = b) by
        (unfold fruit_final_num2, fruit_flush_num2,
                fruit_commit_num2, fruit_commit_num1;
         simplify_zbool; reflexivity);
      rewrite Hf1, Hf2;
      reflexivity
  end.

Lemma proof_of_p067_fruit_distribution_safety_wit_12 : p067_fruit_distribution_safety_wit_12.
Proof. unfold p067_fruit_distribution_safety_wit_12; intros; solve_digit_safety. Qed. 

Lemma proof_of_p067_fruit_distribution_safety_wit_14 : p067_fruit_distribution_safety_wit_14.
Proof. unfold p067_fruit_distribution_safety_wit_14; intros; solve_digit_safety. Qed. 

Lemma proof_of_p067_fruit_distribution_safety_wit_74 : p067_fruit_distribution_safety_wit_74.
Proof. unfold p067_fruit_distribution_safety_wit_74; intros; solve_output_safety. Qed. 

Lemma proof_of_p067_fruit_distribution_safety_wit_75 : p067_fruit_distribution_safety_wit_75.
Proof. unfold p067_fruit_distribution_safety_wit_75; intros; solve_output_safety. Qed. 

Lemma proof_of_p067_fruit_distribution_safety_wit_76 : p067_fruit_distribution_safety_wit_76.
Proof. unfold p067_fruit_distribution_safety_wit_76; intros; solve_output_safety. Qed. 

Lemma proof_of_p067_fruit_distribution_safety_wit_77 : p067_fruit_distribution_safety_wit_77.
Proof. unfold p067_fruit_distribution_safety_wit_77; intros; solve_output_safety. Qed. 

Lemma proof_of_p067_fruit_distribution_entail_wit_1 : p067_fruit_distribution_entail_wit_1.
Proof.
  unfold p067_fruit_distribution_entail_wit_1.
  intros.
  fruit_pre.
  unfold fruit_num1_prefix, fruit_num2_prefix, fruit_cur_prefix.
  simpl.
  entailer!.
Qed. 

Lemma proof_of_p067_fruit_distribution_entail_wit_2_1 : p067_fruit_distribution_entail_wit_2_1.
Proof. unfold p067_fruit_distribution_entail_wit_2_1; intros; solve_fruit_step. Qed. 

Lemma proof_of_p067_fruit_distribution_entail_wit_2_2 : p067_fruit_distribution_entail_wit_2_2.
Proof. unfold p067_fruit_distribution_entail_wit_2_2; intros; solve_fruit_step. Qed. 

Lemma proof_of_p067_fruit_distribution_entail_wit_2_3 : p067_fruit_distribution_entail_wit_2_3.
Proof. unfold p067_fruit_distribution_entail_wit_2_3; intros; solve_fruit_step. Qed. 

Lemma proof_of_p067_fruit_distribution_entail_wit_2_4 : p067_fruit_distribution_entail_wit_2_4.
Proof. unfold p067_fruit_distribution_entail_wit_2_4; intros; solve_fruit_step. Qed. 

Lemma proof_of_p067_fruit_distribution_entail_wit_2_5 : p067_fruit_distribution_entail_wit_2_5.
Proof. unfold p067_fruit_distribution_entail_wit_2_5; intros; solve_fruit_step. Qed. 

Lemma proof_of_p067_fruit_distribution_entail_wit_2_6 : p067_fruit_distribution_entail_wit_2_6.
Proof. unfold p067_fruit_distribution_entail_wit_2_6; intros; solve_fruit_step. Qed. 

Lemma proof_of_p067_fruit_distribution_entail_wit_2_7 : p067_fruit_distribution_entail_wit_2_7.
Proof. unfold p067_fruit_distribution_entail_wit_2_7; intros; solve_fruit_step. Qed. 

Lemma proof_of_p067_fruit_distribution_entail_wit_2_8 : p067_fruit_distribution_entail_wit_2_8.
Proof. unfold p067_fruit_distribution_entail_wit_2_8; intros; solve_fruit_step. Qed. 

Lemma proof_of_p067_fruit_distribution_entail_wit_2_9 : p067_fruit_distribution_entail_wit_2_9.
Proof. unfold p067_fruit_distribution_entail_wit_2_9; intros; solve_fruit_step. Qed. 

Lemma proof_of_p067_fruit_distribution_entail_wit_2_10 : p067_fruit_distribution_entail_wit_2_10.
Proof. unfold p067_fruit_distribution_entail_wit_2_10; intros; solve_fruit_step. Qed. 

Lemma proof_of_p067_fruit_distribution_return_wit_1 : p067_fruit_distribution_return_wit_1.
Proof. unfold p067_fruit_distribution_return_wit_1; intros; solve_fruit_return. Qed. 

Lemma proof_of_p067_fruit_distribution_return_wit_2 : p067_fruit_distribution_return_wit_2.
Proof. unfold p067_fruit_distribution_return_wit_2; intros; solve_fruit_return. Qed. 

Lemma proof_of_p067_fruit_distribution_return_wit_3 : p067_fruit_distribution_return_wit_3.
Proof. unfold p067_fruit_distribution_return_wit_3; intros; solve_fruit_return. Qed. 

Lemma proof_of_p067_fruit_distribution_return_wit_4 : p067_fruit_distribution_return_wit_4.
Proof. unfold p067_fruit_distribution_return_wit_4; intros; solve_fruit_return. Qed. 

Lemma proof_of_p067_fruit_distribution_return_wit_5 : p067_fruit_distribution_return_wit_5.
Proof. unfold p067_fruit_distribution_return_wit_5; intros; solve_fruit_return. Qed. 

Lemma proof_of_p067_fruit_distribution_return_wit_6 : p067_fruit_distribution_return_wit_6.
Proof. unfold p067_fruit_distribution_return_wit_6; intros; solve_fruit_return. Qed. 

Lemma proof_of_p067_fruit_distribution_return_wit_7 : p067_fruit_distribution_return_wit_7.
Proof. unfold p067_fruit_distribution_return_wit_7; intros; solve_fruit_return. Qed. 

Lemma proof_of_p067_fruit_distribution_return_wit_8 : p067_fruit_distribution_return_wit_8.
Proof. unfold p067_fruit_distribution_return_wit_8; intros; solve_fruit_return. Qed. 
