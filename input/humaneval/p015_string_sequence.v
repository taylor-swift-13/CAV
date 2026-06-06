(* spec/15 *)
(* """ Return a string containing space-delimited numbers starting from 0 upto n inclusive.
>>> string_sequence(0)
'0'
>>> string_sequence(5)
'0 1 2 3 4 5'
""" *)

(*  *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

(* 将自然数转换为十进制字符串的实现 *)
Definition string_of_nat (n : nat) : string :=
  (* 对 0 做特殊处理 *)
  match n with
  | 0 => "0"
  | _ =>
    (* 生成数字的倒序 ascii 列表，然后反转并组装为 string.
     为了满足 Coq 的递归终止检查，我们使用带有 fuel 参数的辅助递归，
     对 fuel 进行结构递归（每次递归 fuel-1）。初始时传入 fuel = n，
     这对于所有 n>0 来说足够大以完成所有位的拆分。 *)
    let fix digits_rev_aux (m fuel : nat) : list ascii :=
      match fuel with
      | 0 => [] (* unreachable for adequate initial fuel; 保守返回空列表 *)
      | S fuel' =>
        if Nat.ltb m 10 then [Ascii.ascii_of_nat (48 + m)]
        else Ascii.ascii_of_nat (48 + (Nat.modulo m 10)) :: digits_rev_aux (Nat.div m 10) fuel'
      end in
    let digits := rev (digits_rev_aux n n) in
      fold_right (fun a acc => String a acc) EmptyString digits
  end.

(* 用来连接数字字符串，中间用空格隔开 *)
Fixpoint seq_string (start limit : nat) : string :=
  match limit with
  | 0 => string_of_nat start
  | S n' => string_of_nat start ++ " " ++ seq_string (S start) n'
  end.

(* 规约 Spec *)
Definition string_sequence_impl (n : nat) : string :=
  seq_string 0 n.

(* Pre: no additional constraints for `string_sequence` by default *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.
Require Import string_bridge.
Require Import base_conversion_lib.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_15_pre (n : Z) : Prop :=
  True.

Fixpoint digits_rev_aux_15 (m fuel : nat) : list ascii :=
  match fuel with
  | O => []
  | S fuel' =>
      if Nat.ltb m 10 then [Ascii.ascii_of_nat (48 + m)]
      else Ascii.ascii_of_nat (48 + (Nat.modulo m 10)) ::
           digits_rev_aux_15 (Nat.div m 10) fuel'
  end.

Definition string_of_nat_model_15 (n : nat) : string :=
  match n with
  | O => "0"
  | _ =>
      fold_right (fun a acc => String a acc) EmptyString
        (rev (digits_rev_aux_15 n n))
  end.

Fixpoint sequence_range_string_15 (start count : nat) : string :=
  match count with
  | O => EmptyString
  | S O => string_of_nat start
  | S count' =>
      (sequence_range_string_15 start count' ++
       " " ++ string_of_nat (start + count')%nat)%string
  end.

Definition zlist_of_string (s : string) : list Z :=
  map (fun c => Z.of_nat (nat_of_ascii c)) (list_ascii_of_string s).

Definition sequence_prefix_nat (i : nat) : list Z :=
  zlist_of_string (sequence_range_string_15 0 i).

Definition sequence_prefix (i : Z) : list Z :=
  sequence_prefix_nat (Z.to_nat i).

Definition sequence_output (n : Z) : list Z :=
  sequence_prefix (n + 1).

Definition problem_15_spec (n : Z) (output : list Z) : Prop :=
  output = sequence_output n.

Definition sequence_output_bound (n : Z) : Prop :=
  Zlength (sequence_output n) + 1 <= 12 * (n + 1) + 1.
