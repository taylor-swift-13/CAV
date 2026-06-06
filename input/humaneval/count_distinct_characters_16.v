(* spec/16 *)
(* """ Given a string, find out how many distinct characters (regardless of case) does it consist of
>>> count_distinct_characters('xyzXYZ')
3
>>> count_distinct_characters('Jerry')
4
""" *)

(* Spec(s, k) :=
∃ D : set(Char),
  (* 1. 每个 s(i) 的小写形式都在 D 中 *)
  (∀ i ∈ [0, length(s)), ∃ d ∈ D, d = lower_nat(s[i])) ∧

  (* 2. D 中的每个字符都能由某个 s(i) 得到 *)
  (∀ d ∈ D, ∃ i ∈ [0, length(s)), d = lower_nat(s[i])) ∧

  (* 3. 输出等于集合大小 *)
  k = |D| *)

Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope nat_scope.
Open Scope string_scope.

(* 判断字符是否是大写字母 *)
Definition is_upper (a: ascii) : bool :=
  let n := nat_of_ascii a in
  (65 <=? n)%nat && (n <=? 90)%nat.

(* 转换大写字符到小写 *)
Definition lower_nat (a: ascii) : ascii :=
  if is_upper a then
    ascii_of_nat (nat_of_ascii a + 32)
  else a.

(* Pre: no additional constraints for `count_distinct_characters` by default *)

(* Spec定义 *)

Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Open Scope Z_scope.

Definition is_upper_zb (c : Z) : bool :=
  Z.leb 65 c && Z.leb c 90.

Definition lower (c : Z) : Z :=
  if is_upper_zb c then c + 32 else c.

Definition problem_16_pre (s : list Z) : Prop :=
  True.

Definition problem_16_spec (s : list Z) (output : Z) : Prop :=
  0 <= output /\
    ((exists D: list ascii,
      NoDup D /\
  
      (* ((string_of_list s))中每个字符小写版都在D中 *)
      (forall i : nat, (i < String.length ((string_of_list s)))%nat ->
        match String.get i ((string_of_list s)) with
        | Some c => In (lower_nat c) D
        | None => False
        end) /\
  
      (* D中每个字符都来源于((string_of_list s))中某字符的小写版 *)
      (forall d, In d D -> exists i : nat, (i < String.length ((string_of_list s)))%nat /\
        match String.get i ((string_of_list s)) with
        | Some c => d = lower_nat c
        | None => False
        end) /\
  
      (* k等于D长度 *)
      output = Z.of_nat (List.length D))).

Fixpoint mem_zb (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | y :: ys => if Z.eqb x y then true else mem_zb x ys
  end.

Definition add_unique (x : Z) (seen : list Z) : list Z :=
  if mem_zb x seen then seen else x :: seen.

Fixpoint collect_lower (seen input : list Z) : list Z :=
  match input with
  | [] => seen
  | x :: xs => collect_lower (add_unique (lower x) seen) xs
  end.

Definition distinct_lower_prefix (i : Z) (input : list Z) : list Z :=
  collect_lower [] (sublist 0 i input).

Definition count_distinct_lower_upto (i : Z) (input : list Z) : Z :=
  Z.of_nat (List.length (distinct_lower_prefix i input)).

Definition lower_seen_state
  (j i : Z) (input : list Z) (c seen : Z) : Prop :=
  (seen = 0 \/ seen = 1) /\
  c = lower (Znth i input 0) /\
  (seen = 1 ->
    exists k, 0 <= k < j /\ lower (Znth k input 0) = c) /\
  (seen = 0 ->
    forall k, 0 <= k < j -> lower (Znth k input 0) <> c).
