(* spec/44 *)
(* Change numerical base of input number x to base.
return string representation after the conversion.
base numbers are less than 10.
>>> change_base(8, 3)
'22'
>>> change_base(8, 2)
'1000'
>>> change_base(7, 2)
'111' *)

(* Spec(x : int, base : int, output : string) :=

​	∀i ∈ [0, length(output)), output[i] < base /\
​	$∑_{i=0}^{length(output)-1}$ ToNum(output[i]) * base^(length(output) - i - 1) = x *)

(* 引入所需的Coq库 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

Import ListNotations.

(*
  辅助函数，用于将一个数字字符（如 '0', '1', ...）
  转换为其对应的自然数（如 0, 1, ...）。
*)
Definition nat_of_digit (c : ascii) : nat :=
  Ascii.nat_of_ascii c - Ascii.nat_of_ascii "0"%char.

(*
  程序规约 Spec 的定义。
  - x:      输入的非负整数。
  - base:   转换的目标基数 (>= 2)。
  - output: 转换后得到的字符串。
*)
(* Pre: base must be at least 2 for a valid base conversion *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Wf_Z.
Require Import Coq.micromega.Lia.
Require Import Recdef.
From compcert.lib Require Import Coqlib.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import string_bridge.

Local Open Scope Z_scope.

Definition SingleSome {A : Type} (l : list (option A)) (n : Z) (a : A) : Prop :=
  Znth n l None = Some a /\
  forall m, 0 <= m < Zlength l -> m <> n -> Znth m l None = None.

Definition repeat_Z {A: Type} (a: A) (n: Z): list A :=
  repeat a (Z.to_nat n).

Function base_digits (n base : Z) {measure Z.to_nat n} : list Z :=
  if Z.leb base 1 then [48]
  else if Z.leb n 0 then [48]
  else if Z.ltb n base then [48 + n]
  else base_digits (n / base) base ++ [48 + (n mod base)].
Proof.
  intros n base Hbase Hnpos Hnotlt.
  apply Z.leb_gt in Hbase.
  apply Z.leb_gt in Hnpos.
  apply Z.ltb_ge in Hnotlt.
  apply Z2Nat.inj_lt.
  - apply Z.div_pos; lia.
  - lia.
  - apply Z.div_lt; lia.
Defined.

Definition base_digits_pos (n base : Z) : list Z :=
  if Z.leb n 0 then [] else base_digits n base.

Definition problem_44_pre (x base : Z) : Prop :=
  0 <= x /\ 2 <= base < 10.

Definition problem_44_spec (x base : Z) (output : list Z) : Prop :=
  Forall (fun c => 48 <= c < 48 + base) output /\
  fold_left (fun acc c => acc * base + (c - 48)) output 0 = x.

Definition digit_value (c : Z) : Z := c - 48.

Fixpoint digits_value (base : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | c :: rest => digits_value base rest + digit_value c * Z.pow base (Zlength rest)
  end.

Definition base_count_state (orig base t digits : Z) : Prop :=
  0 <= t /\
  0 <= digits /\
  digits + Zlength (base_digits_pos t base) =
    Zlength (base_digits_pos orig base).

Definition base_fill_state
  (orig base x digits : Z) (suffix : list Z) : Prop :=
  0 <= x /\
  0 <= digits /\
  digits = Zlength (base_digits_pos x base) /\
  base_digits orig base = base_digits_pos x base ++ suffix.

Definition base_fill_full_state
  (orig base x digits : Z) (out_l : list Z) : Prop :=
  exists suffix,
    base_fill_state orig base x digits suffix /\
    out_l = repeat_Z 0 digits ++ suffix.
