(* spec/152 *)
(* def compare(game,guess):
"""I think we all remember that feeling when the result of some long-awaited
event is finally known. The feelings and thoughts you have at that moment are
definitely worth noting down and comparing.
Your task is to determine if a person correctly guessed the results of a number of matches.
You are given two arrays of scores and guesses of equal length, where each index shows a match.
Return an array of the same length denoting how far off each guess was. If they have guessed correctly,
the value is 0, and if not, the value is the absolute difference between the guess and the score.

example:

compare([1,2,3,4,5,1],[1,2,3,4,2,-2]) -> [0,0,0,0,3,3]
compare([0,5,0,0,0,4],[4,1,1,0,0,-2]) -> [4,4,1,0,0,6]
""" *)
(* 导入整数库 ZArith 和列表库 List *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(* 输入两个列表长度必须相等 *)

(*
  compare_spec 定义了 'compare' 函数的规约。

  参数:
  - game: 一个 Z（整数）列表，代表实际分数。
  - guess: 一个 Z 列表，代表猜测的分数。
  - result: 一个 Z 列表，代表函数的输出。

  规约内容:
  该规约包含三个部分的合取（AND）：
  1. 输入列表 'game' 和 'guess' 的长度必须相等。
  2. 输出列表 'result' 的长度必须与输入列表的长度相等。
  3. 对于任意一个在列表长度范围内的合法索引 'i'（即 0 <= i < length game），
     输出列表 'result' 在索引 'i' 处的值，必须等于 'game' 和 'guess'
     在各自索引 'i' 处的值的差的绝对值。

  注意: `nth i l 0%Z` 用于获取列表 l 在索引 i 处的元素。
  第三个参数 `0%Z` 是一个默认值，如果索引越界则返回该值。
  但在我们的 `forall` 语句中，因为有 `(i < length game)%nat` 的前提条件，
  所以索引 `i` 永远不会越界。
*)

Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Fixpoint compare_list (game guess : list Z) : list Z :=
  match game, guess with
  | g :: gs, q :: qs => Z.abs (g - q) :: compare_list gs qs
  | _, _ => nil
  end.

Definition compare_prefix_list (i : Z) (game guess : list Z) : list Z :=
  compare_list (sublist 0 i game) (sublist 0 i guess).

Definition compare_prefix (i : Z) (game guess output : list Z) : Prop :=
  0 <= i <= Zlength game /\
  i <= Zlength guess /\
  output = compare_prefix_list i game guess.

Definition problem_152_pre (game guess : list Z) : Prop :=
  Zlength game = Zlength guess.

Definition problem_152_spec (game guess output : list Z) : Prop :=
  Zlength game = Zlength guess /\
  Zlength output = Zlength game /\
  forall i, 0 <= i < Zlength game ->
    Znth i output 0 = Z.abs (Znth i game 0 - Znth i guess 0).

Definition compare_int_range (game guess : list Z) : Prop :=
  forall i,
    0 <= i < Zlength game ->
    INT_MIN < Znth i game 0 - Znth i guess 0 <= INT_MAX.

Lemma compare_list_length : forall game guess,
  length game = length guess ->
  length (compare_list game guess) = length game.
Proof.
  induction game as [|g gs IH]; intros guess Hlen.
  - reflexivity.
  - destruct guess as [|q qs]; simpl in *; [lia|].
    f_equal.
    apply IH.
    lia.
Qed.

Lemma compare_prefix_0 : forall game guess,
  0 <= Zlength game ->
  0 <= Zlength guess ->
  compare_prefix 0 game guess nil.
Proof.
  intros.
  unfold compare_prefix, compare_prefix_list.
  rewrite !Zsublist_nil by lia.
  repeat split; try lia; reflexivity.
Qed.

Lemma compare_prefix_Zlength : forall i game guess output,
  compare_prefix i game guess output ->
  problem_152_pre game guess ->
  Zlength output = i.
Proof.
  intros i game guess output [Hbounds [Hguess Hout]] Hpre.
  subst output.
  unfold compare_prefix_list.
  unfold problem_152_pre, problem_152_pre in Hpre.
  rewrite Zlength_correct.
  rewrite compare_list_length.
  - assert (Hsub : length (sublist 0 i game) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - destruct Hbounds as [_ Hile].
        exact Hile.
    }
    rewrite Hsub.
    rewrite Z2Nat.id by lia.
    reflexivity.
  - assert (Hg : length (sublist 0 i game) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - destruct Hbounds as [_ Hile].
        exact Hile.
    }
    assert (Hq : length (sublist 0 i guess) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - exact Hguess.
    }
    rewrite Hg, Hq.
    reflexivity.
Qed.

Lemma compare_prefix_snoc : forall i game guess output diff value,
  compare_prefix i game guess output ->
  0 <= i < Zlength game ->
  i < Zlength guess ->
  diff = Znth i game 0 - Znth i guess 0 ->
  value = Z.abs diff ->
  compare_prefix (i + 1) game guess (output ++ [value]).
Proof.
  intros i game guess output diff value [Hbounds [Hguess Hout]] Hi Higuess Hdiff Hvalue.
  subst output diff value.
  unfold compare_prefix, compare_prefix_list in *.
  repeat split; try lia.
  rewrite (sublist_split 0 (i + 1) i game)
    by lia.
  rewrite (sublist_split 0 (i + 1) i guess)
    by lia.
  rewrite (sublist_single 0 i game) by lia.
  rewrite (sublist_single 0 i guess) by lia.
  clear Hbounds Hguess.
  remember (sublist 0 i game) as gs.
  remember (sublist 0 i guess) as qs.
  assert (Hlen : length gs = length qs).
  {
    subst gs qs.
    assert (Hg : length (sublist 0 i game) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - lia.
    }
    assert (Hq : length (sublist 0 i guess) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - lia.
    }
    rewrite Hg, Hq.
    reflexivity.
  }
  clear Heqgs Heqqs.
  revert qs Hlen.
  induction gs as [|g gs IH]; intros qs Hlen; destruct qs as [|q qs]; simpl in *; try lia.
  - reflexivity.
  - f_equal.
    apply IH.
    lia.
Qed.

Lemma compare_prefix_snoc_Zlength : forall i game guess output diff value,
  compare_prefix i game guess output ->
  problem_152_pre game guess ->
  0 <= i < Zlength game ->
  diff = Znth i game 0 - Znth i guess 0 ->
  value = Z.abs diff ->
  Zlength (output ++ [value]) = i + 1.
Proof.
  intros.
  rewrite Zlength_app.
  rewrite (compare_prefix_Zlength i game guess output); try assumption.
  change (Zlength [value]) with 1.
  lia.
Qed.

Lemma compare_list_Znth : forall game guess i,
  Zlength game = Zlength guess ->
  0 <= i < Zlength game ->
  Znth i (compare_list game guess) 0 =
    Z.abs (Znth i game 0 - Znth i guess 0).
Proof.
  induction game as [|g gs IH]; intros guess i Hlen Hi.
  - rewrite Zlength_correct in Hi; simpl in Hi; lia.
  - destruct guess as [|q qs].
    + rewrite !Zlength_correct in Hlen; simpl in Hlen; lia.
    + destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
      * subst i.
        simpl compare_list.
        repeat rewrite Znth0_cons.
        reflexivity.
      * assert (0 < i) by lia.
        simpl compare_list.
        rewrite !Znth_cons by lia.
        apply IH.
        -- rewrite !Zlength_cons in Hlen; lia.
        -- rewrite Zlength_cons in Hi; lia.
Qed.

Lemma compare_int_range_at : forall game guess i,
  compare_int_range game guess ->
  0 <= i < Zlength game ->
  INT_MIN < Znth i game 0 - Znth i guess 0 <= INT_MAX.
Proof.
  intros.
  apply H; assumption.
Qed.

Lemma compare_prefix_full_spec : forall game guess output,
  compare_prefix (Zlength game) game guess output ->
  problem_152_pre game guess ->
  problem_152_spec game guess output.
Proof.
  intros game guess output Hpref Hpre.
  unfold problem_152_spec, problem_152_spec.
  unfold problem_152_pre, problem_152_pre in Hpre.
  split; [assumption|].
  split.
  - rewrite (compare_prefix_Zlength (Zlength game) game guess output); try assumption.
    reflexivity.
  - intros n Hn.
    destruct Hpref as [_ [_ Hout]].
    subst output.
    unfold compare_prefix_list.
    rewrite sublist_self by reflexivity.
    rewrite (sublist_self guess) by exact Hpre.
    apply compare_list_Znth; assumption.
Qed.
