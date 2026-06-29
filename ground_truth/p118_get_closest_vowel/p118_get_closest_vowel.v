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
  alpha_range word.

Definition problem_118_spec (word output : list Z) : Prop :=
  (exists i,
     closest_vowel_candidate word i /\
     no_candidate_after i word /\
     output = [Znth i word 0]) \/
  ((forall i, 1 <= i < Zlength word - 1 -> ~ closest_vowel_candidate word i) /\
   output = []).
