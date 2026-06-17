(* spec/89 *)
(* def encrypt(s):
"""Create a function encrypt that takes a string as an argument and
returns a string encrypted with the alphabet being rotated.
The alphabet should be rotated in a manner such that the letters
shift down by two multiplied to two places.
For example:
encrypt('hi') returns 'lm'
encrypt('asdfghjkl') returns 'ewhjklnop'
encrypt('gf') returns 'kj'
encrypt('et') returns 'ix'
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.
Local Open Scope char_scope.

(*
  char_relation 定义了单个输入字符 c_in 和输出字符 c_out 之间的关系。
  这遵循字母表向下移动 4 (2*2) 位的规则。
*)
Definition char_relation (c_in c_out : ascii) : Prop :=
  match c_in with
  | "a" => c_out = "e" | "b" => c_out = "f" | "c" => c_out = "g" | "d" => c_out = "h"
  | "e" => c_out = "i" | "f" => c_out = "j" | "g" => c_out = "k" | "h" => c_out = "l"
  | "i" => c_out = "m" | "j" => c_out = "n" | "k" => c_out = "o" | "l" => c_out = "p"
  | "m" => c_out = "q" | "n" => c_out = "r" | "o" => c_out = "s" | "p" => c_out = "t"
  | "q" => c_out = "u" | "r" => c_out = "v" | "s" => c_out = "w" | "t" => c_out = "x"
  | "u" => c_out = "y" | "v" => c_out = "z" | "w" => c_out = "a" | "x" => c_out = "b"
  | "y" => c_out = "c" | "z" => c_out = "d"
  (* 对于非小写字母的任何其他字符，它保持不变 *)
  | _ => c_out = c_in
  end.

Definition is_lowercase_ascii (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a"%char <= n <= nat_of_ascii "z"%char)%nat.

Fixpoint all_lowercase_ascii (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String c rest => is_lowercase_ascii c /\ all_lowercase_ascii rest
  end.


(*
  encrypt_spec (程序规约)
  它规定：
  1. 输入列表 s 和输出列表 output 的长度必须相等.
  2. 对于两个列表中每个位置上对应的字符 (c_in, c_out)，
     它们必须满足 char_relation 定义的关系。
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Export string_bridge.

Local Open Scope Z_scope.

Definition lower_char (c : Z) : Prop := 97 <= c <= 122.

Definition problem_89_pre (s : list Z) : Prop :=
  all_lowercase_ascii (string_of_list s).

Definition encrypt_char (c : Z) : Z :=
  Z.rem (c + 4 - 97) 26 + 97.

Definition problem_89_spec (input output : list Z) : Prop :=
  Forall2 char_relation
    (list_ascii_of_string (string_of_list input))
    (list_ascii_of_string (string_of_list output)).

Lemma nat_of_ascii_ascii_of : forall z,
  0 <= z < 256 ->
  nat_of_ascii (ascii_of z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.

Lemma encrypt_output_range : forall x,
  lower_char x ->
  97 <= encrypt_char x <= 122.
Proof.
  intros x Hlower.
  unfold encrypt_char, lower_char in *.
  pose proof (Z.rem_bound_pos (x + 4 - 97) 26 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma encrypt_char_nonzero : forall x,
  lower_char x ->
  encrypt_char x <> 0.
Proof.
  intros x Hlower.
  pose proof (encrypt_output_range x Hlower).
  lia.
Qed.

Lemma lower_char_cases : forall x,
  lower_char x ->
  x = 97 \/ x = 98 \/ x = 99 \/ x = 100 \/ x = 101 \/ x = 102 \/
  x = 103 \/ x = 104 \/ x = 105 \/ x = 106 \/ x = 107 \/ x = 108 \/
  x = 109 \/ x = 110 \/ x = 111 \/ x = 112 \/ x = 113 \/ x = 114 \/
  x = 115 \/ x = 116 \/ x = 117 \/ x = 118 \/ x = 119 \/ x = 120 \/
  x = 121 \/ x = 122.
Proof.
  unfold lower_char.
  intros; lia.
Qed.

Lemma encrypt_char_relation : forall x,
  lower_char x ->
  char_relation (ascii_of x) (ascii_of (encrypt_char x)).
Proof.
  intros x Hlower.
  pose proof (lower_char_cases x Hlower) as Hcases.
  repeat
    match type of Hcases with
    | _ \/ _ => destruct Hcases as [-> | Hcases]; [vm_compute; reflexivity |]
    | _ => subst x; vm_compute; reflexivity
    end.
Qed.

Lemma lower_char_from_problem_89_pre : forall s k,
  problem_89_pre s ->
  ascii_range s ->
  0 <= k < Zlength s ->
  lower_char (Znth k s 0).
Proof.
  induction s as [| a rest IH]; intros k Hpre Hrange Hk.
  - rewrite Zlength_nil in Hk; lia.
  - simpl in Hpre.
    destruct Hpre as [Ha Hrest].
    destruct (Z.eq_dec k 0) as [-> | Hnz].
    + unfold is_lowercase_ascii, lower_char in *.
      pose proof (Hrange 0 Hk) as Harange.
      rewrite Znth0_cons in Harange.
      rewrite nat_of_ascii_ascii_of in Ha by exact Harange.
      cbn in Ha.
      destruct Ha as [Ha_low Ha_high].
      apply Nat2Z.inj_le in Ha_low.
      apply Nat2Z.inj_le in Ha_high.
      rewrite Z2Nat.id in Ha_low by lia.
      rewrite Z2Nat.id in Ha_high by lia.
      rewrite Znth0_cons.
      lia.
    + rewrite Znth_cons by lia.
      apply IH.
      * exact Hrest.
      * intros i Hi.
        specialize (Hrange (i + 1) ltac:(rewrite Zlength_cons; lia)).
        rewrite Znth_cons in Hrange by lia.
        replace (i + 1 - 1) with i in Hrange by lia.
        exact Hrange.
      * rewrite Zlength_cons in Hk; lia.
Qed.

Lemma list_ascii_of_string_of_list : forall l,
  list_ascii_of_string (string_of_list l) = map ascii_of l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma problem_89_spec_intro_map : forall input output n,
  Zlength input = n ->
  Zlength output = n ->
  problem_89_pre input ->
  ascii_range input ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = encrypt_char (Znth k input 0)) ->
  Forall2 char_relation (map ascii_of input) (map ascii_of output).
Proof.
  induction input as [| x xs IH]; intros output n Hin Hout Hpre Hrange Hpoint.
  - destruct output as [| y ys].
    + constructor.
    + rewrite Zlength_nil in Hin.
      rewrite Zlength_cons in Hout.
      pose proof (Zlength_nonneg ys).
      lia.
  - destruct output as [| y ys].
    + rewrite Zlength_cons in Hin.
      rewrite Zlength_nil in Hout.
      pose proof (Zlength_nonneg xs).
      lia.
    + simpl.
      constructor.
      * assert (Hy : y = encrypt_char x).
        {
          assert (H0n : 0 <= 0 < n).
          { rewrite <- Hin. rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia. }
          specialize (Hpoint 0 H0n).
          rewrite !Znth0_cons in Hpoint.
          exact Hpoint.
        }
        subst y.
        apply encrypt_char_relation.
        eapply lower_char_from_problem_89_pre with (s := x :: xs) (k := 0); eauto.
        rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
      * apply IH with (n := n - 1).
        -- rewrite Zlength_cons in Hin; lia.
        -- rewrite Zlength_cons in Hout; lia.
        -- simpl in Hpre. destruct Hpre as [_ Hpre_tail]. exact Hpre_tail.
        -- intros k Hk.
           specialize (Hrange (k + 1) ltac:(rewrite Zlength_cons; lia)).
           rewrite Znth_cons in Hrange by lia.
           replace (k + 1 - 1) with k in Hrange by lia.
           exact Hrange.
        -- intros k Hk.
           specialize (Hpoint (k + 1) ltac:(rewrite Zlength_cons in Hin; lia)).
           rewrite !Znth_cons in Hpoint by lia.
           replace (k + 1 - 1) with k in Hpoint by lia.
           exact Hpoint.
Qed.

Lemma problem_89_spec_intro : forall input output n,
  Zlength input = n ->
  Zlength output = n ->
  problem_89_pre input ->
  ascii_range input ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = encrypt_char (Znth k input 0)) ->
  problem_89_spec input output.
Proof.
  intros input output n Hin Hout Hpre Hrange Hpoint.
  unfold problem_89_spec.
  rewrite !list_ascii_of_string_of_list.
  eapply problem_89_spec_intro_map; eauto.
Qed.
