(* spec/118 *)
(* You are given a word. Your task is to find the closest vowel that stands between
two consonants from the right side of the word (case sensitive).

Vowels in the beginning and ending doesn't count. Return empty string if you didn't
find any vowel met the above condition.

You may assume that the given string contains English letter only.

Example:
get_closest_vowel("yogurt") ==> "u"
get_closest_vowel("FULL") ==> "U"
get_closest_vowel("quick") ==> ""
get_closest_vowel("ab") ==> ""*)

(* 导入所需的 Coq 库 *)
Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Arith.
Require Import Coq.Logic.FunctionalExtensionality.

(*
 * 辅助定义
 *)

(* 定义：检查一个字符是否为元音（区分大小写） *)
Definition is_vowel_nat (c : ascii) : Prop :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => True
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => True
  | _ => False
  end.

(* 定义：检查一个字符是否为英文字母 *)
Definition is_alpha_nat (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122).

(* 定义：检查一个字符是否为辅音 *)
Definition is_consonant_nat (c : ascii) : Prop :=
  is_alpha_nat c /\ ~ is_vowel_nat c.

(* 输入字符串只包含英文字母 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_vowel (x : Z) : Prop :=
  x = 65 \/ x = 69 \/ x = 73 \/ x = 79 \/ x = 85 \/
  x = 97 \/ x = 101 \/ x = 105 \/ x = 111 \/ x = 117.

Definition is_alpha (x : Z) : Prop :=
  65 <= x <= 90 \/ 97 <= x <= 122.

Definition is_consonant (x : Z) : Prop :=
  is_alpha x /\ ~ is_vowel x.

Definition alpha_range (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> is_alpha (Znth i l 0).

Definition closest_vowel_candidate (l : list Z) (i : Z) : Prop :=
  1 <= i < Zlength l - 1 /\
  is_consonant (Znth (i - 1) l 0) /\
  is_vowel (Znth i l 0) /\
  is_consonant (Znth (i + 1) l 0).

Definition no_candidate_after (i : Z) (l : list Z) : Prop :=
  forall j, i < j < Zlength l - 1 -> ~ closest_vowel_candidate l j.

Definition problem_118_pre (word : list Z) : Prop :=
  let fix all_letters (w : string) : Prop :=
    match w with
    | EmptyString => True
    | String ch rest =>
        let n := Z.of_nat (nat_of_ascii ch) in ((65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) /\ all_letters rest
    end in all_letters ((string_of_list word)).

Definition problem_118_spec (word output : list Z) : Prop :=
  (((* 情况一：找到了符合条件的元音 *)
    (exists i c_curr,
      1 <= i < String.length ((string_of_list word)) - 1 /\
      (*
       * 断言在 i-1, i, i+1 的位置上确实存在字符 (c_prev, c_curr, c_next)，
       * 并且这些字符满足 "辅音-元音-辅音" 的模式。
       * 这是处理 `option ascii` 类型的关键。
       *)
      (exists c_prev c_next,
          String.get (i - 1) ((string_of_list word)) = Some c_prev /\
          String.get i ((string_of_list word)) = Some c_curr /\
          String.get (i + 1) ((string_of_list word)) = Some c_next /\
          is_consonant_nat c_prev /\ is_vowel_nat c_curr /\ is_consonant_nat c_next) /\
      ((string_of_list output)) = String c_curr ""%string /\
      (* 并且，这是最右边（即索引最大）的一个 *)
      (forall j,
        i < j < String.length ((string_of_list word)) - 1 ->
        ~ (exists j_prev j_curr j_next,
              String.get (j - 1) ((string_of_list word)) = Some j_prev /\
              String.get j ((string_of_list word)) = Some j_curr /\
              String.get (j + 1) ((string_of_list word)) = Some j_next /\
              is_consonant_nat j_prev /\ is_vowel_nat j_curr /\ is_consonant_nat j_next))
    )
    \/
    (* 情况二：不存在符合条件的元音 *)
    (
      (forall i,
        1 <= i < String.length ((string_of_list word)) - 1 ->
        ~ (exists c_prev c_curr c_next,
              String.get (i - 1) ((string_of_list word)) = Some c_prev /\
              String.get i ((string_of_list word)) = Some c_curr /\
              String.get (i + 1) ((string_of_list word)) = Some c_next /\
              is_consonant_nat c_prev /\ is_vowel_nat c_curr /\ is_consonant_nat c_next)) /\
      ((string_of_list output)) = ""%string
    ))%nat).
