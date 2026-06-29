(* spec/67 *)
(* def fruit_distribution(s,n):
"""
In this task, you will be given a string that represents a number of apples and oranges
that are distributed in a basket of fruit this basket contains
apples, oranges, and mango fruits. Given the string that represents the total number of
the oranges and apples and an integer that represent the total number of the fruits
in the basket return the number of the mango fruits in the basket.
for examble:
fruit_distribution("5 apples and 6 oranges", 19) ->19 - 5 - 6 = 8
fruit_distribution("0 apples and 1 oranges",3) -> 3 - 0 - 1 = 2
fruit_distribution("2 apples and 3 oranges", 100) -> 100 - 2 - 3 = 95
fruit_distribution("100 apples and 1 oranges",120) -> 120 - 100 - 1 = 19
""" *)
(* 引入Coq自带的库，用于处理整数（Z）和字符串（string） *)
Require Import ZArith Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope string_scope.

Definition char_to_digit (c : ascii) : nat :=
  nat_of_ascii c - nat_of_ascii "0"%char.

(* 辅助函数：将字符串转换为自然数 *)
Fixpoint string_to_nat_aux (s : string) (acc : nat) : nat :=
  match s with
  | EmptyString => acc
  | String c s' => string_to_nat_aux s' (acc * 10 + char_to_digit c)
  end.

(* 主函数：将字符串转换为自然数 *)
Definition string_to_nat (s : string) : nat :=
  string_to_nat_aux s 0.

(*
  辅助规约: parse_fruit_string
  这个规约描述了从输入字符串 s 中解析出苹果和橘子数量的逻辑。
*)
Definition parse_fruit_string (s : string) (apples oranges : nat) : Prop :=
  exists s_apples s_oranges,
    apples = string_to_nat s_apples /\
    oranges = string_to_nat s_oranges /\
    s = (s_apples ++ " apples and " ++ s_oranges ++ " oranges")%string.



Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Lia.
From AUXLib Require Import ListLib.

Local Open Scope Z_scope.

Definition int_min : Z := -2147483648.
Definition int_max : Z := 2147483647.
Definition int_cur_mul10_bound : Z := 214748363.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Definition char_list_string (l : list Z) (s : string) : Prop :=
  list_ascii_of_string s = map (fun z => ascii_of_nat (Z.to_nat z)) l.

Definition ascii_of (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of c) (string_of_list rest)
  end.

Definition ascii_range (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 < 256.

Definition is_digit (c : Z) : Prop :=
  48 <= c <= 57.

Definition digit_value (c : Z) : Z :=
  c - 48.

Definition fruit_commit_num1 (num1 cur : Z) : Z :=
  if num1 <? 0 then cur else num1.

Definition fruit_commit_num2 (num1 num2 cur : Z) : Z :=
  if num1 <? 0 then num2 else if num2 <? 0 then cur else num2.

Definition fruit_step (st : Z * Z * Z) (c : Z) : Z * Z * Z :=
  let '(num1, num2, cur) := st in
  if (48 <=? c) && (c <=? 57) then
    let cur0 := if cur <? 0 then 0 else cur in
    (num1, num2, cur0 * 10 + digit_value c)
  else if 0 <=? cur then
    (fruit_commit_num1 num1 cur,
     fruit_commit_num2 num1 num2 cur,
     -1)
  else st.

Fixpoint fruit_state_after_nat (k : nat) (s : list Z) : Z * Z * Z :=
  match k with
  | O => (-1, -1, -1)
  | S k' => fruit_step (fruit_state_after_nat k' s) (Znth (Z.of_nat k') s 0)
  end.

Definition fruit_num1_prefix (i : Z) (s : list Z) : Z :=
  let '(num1, _, _) := fruit_state_after_nat (Z.to_nat i) s in num1.

Definition fruit_num2_prefix (i : Z) (s : list Z) : Z :=
  let '(_, num2, _) := fruit_state_after_nat (Z.to_nat i) s in num2.

Definition fruit_cur_prefix (i : Z) (s : list Z) : Z :=
  let '(_, _, cur) := fruit_state_after_nat (Z.to_nat i) s in cur.

Definition fruit_flush_num1 (s : list Z) : Z :=
  let num1 := fruit_num1_prefix (Zlength s) s in
  let cur := fruit_cur_prefix (Zlength s) s in
  if 0 <=? cur then fruit_commit_num1 num1 cur else num1.

Definition fruit_flush_num2 (s : list Z) : Z :=
  let num1 := fruit_num1_prefix (Zlength s) s in
  let num2 := fruit_num2_prefix (Zlength s) s in
  let cur := fruit_cur_prefix (Zlength s) s in
  if 0 <=? cur then fruit_commit_num2 num1 num2 cur else num2.

Definition fruit_final_num1 (s : list Z) : Z :=
  let num1 := fruit_flush_num1 s in
  if num1 <? 0 then 0 else num1.

Definition fruit_final_num2 (s : list Z) : Z :=
  let num2 := fruit_flush_num2 s in
  if num2 <? 0 then 0 else num2.

Definition fruit_output (s : list Z) (total : Z) : Z :=
  total - fruit_final_num1 s - fruit_final_num2 s.

Fixpoint parse_digits_z_aux (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | c :: rest => parse_digits_z_aux rest (acc * 10 + digit_value c)
  end.

Definition parse_digits (l : list Z) : Z :=
  parse_digits_z_aux l 0.

Definition all_digits_z (l : list Z) : Prop :=
  forall c, In c l -> is_digit c.

Definition fruit_apples_and : list Z :=
  [32; 97; 112; 112; 108; 101; 115; 32; 97; 110; 100; 32].

Definition fruit_oranges : list Z :=
  [32; 111; 114; 97; 110; 103; 101; 115].

Definition fruit_state_range_at (i : Z) (s : list Z) : Prop :=
  -1 <= fruit_num1_prefix i s <= int_max /\
  -1 <= fruit_num2_prefix i s <= int_max /\
  -1 <= fruit_cur_prefix i s <= int_max.

Definition fruit_digit_update_safe (i : Z) (s : list Z) : Prop :=
  is_digit (Znth i s 0) ->
  fruit_cur_prefix i s < 0 \/
  0 <= fruit_cur_prefix i s <= int_cur_mul10_bound.

Definition fruit_state_safe (s : list Z) : Prop :=
  (forall i, 0 <= i <= Zlength s -> fruit_state_range_at i s) /\
  (forall i, 0 <= i < Zlength s -> fruit_digit_update_safe i s).

Definition fruit_output_safe (s : list Z) (total : Z) : Prop :=
  int_min <= total - fruit_final_num1 s <= int_max /\
  int_min <= fruit_output s total <= int_max.

Definition problem_67_pre (s : list Z) (total : Z) : Prop :=
  0 <= total /\
  exists s_apples s_oranges,
    s_apples <> [] /\
    s_oranges <> [] /\
    all_digits_z s_apples /\
    all_digits_z s_oranges /\
    s = (s_apples ++ fruit_apples_and ++ s_oranges ++ fruit_oranges)%list.

Definition problem_67_spec (s : list Z) (total output : Z) : Prop :=
  exists s_apples s_oranges,
    s_apples <> [] /\
    s_oranges <> [] /\
    all_digits_z s_apples /\
    all_digits_z s_oranges /\
    s = (s_apples ++ fruit_apples_and ++ s_oranges ++ fruit_oranges)%list /\
    output = total - parse_digits s_apples - parse_digits s_oranges.

Definition spec67_digit (c : ascii) : Z :=
  (Z.of_nat (nat_of_ascii c) - 48)%Z.

Definition spec67_commit_num1 (num1 cur : Z) : Z :=
  if Z.ltb num1 0 then cur else num1.

Definition spec67_commit_num2 (num1 num2 cur : Z) : Z :=
  if Z.ltb num1 0 then num2 else if Z.ltb num2 0 then cur else num2.

Definition spec67_scan_step (st : Z * Z * Z) (c : ascii) : Z * Z * Z :=
  let '(num1, num2, cur) := st in
  let z := Z.of_nat (nat_of_ascii c) in
  if andb (Z.leb 48 z) (Z.leb z 57) then
    let cur0 := if Z.ltb cur 0 then 0%Z else cur in
    (num1, num2, (cur0 * 10 + spec67_digit c)%Z)
  else if Z.leb 0 cur then
    (spec67_commit_num1 num1 cur,
     spec67_commit_num2 num1 num2 cur,
     (-1)%Z)
  else st.

Fixpoint spec67_scan_state_left (st : Z * Z * Z) (l : list ascii) : Z * Z * Z :=
  match l with
  | [] => st
  | c :: rest => spec67_scan_state_left (spec67_scan_step st c) rest
  end.

Definition spec67_scan_state_full (l : list ascii) : Z * Z * Z :=
  spec67_scan_state_left ((-1)%Z, (-1)%Z, (-1)%Z) l.

Definition spec67_flush_num1 (st : Z * Z * Z) : Z :=
  let '(num1, _, cur) := st in
  if Z.leb 0 cur then spec67_commit_num1 num1 cur else num1.

Definition spec67_flush_num2 (st : Z * Z * Z) : Z :=
  let '(num1, num2, cur) := st in
  if Z.leb 0 cur then spec67_commit_num2 num1 num2 cur else num2.

Definition spec67_final_num1 (st : Z * Z * Z) : Z :=
  let n1 := spec67_flush_num1 st in
  if Z.ltb n1 0 then 0%Z else n1.

Definition spec67_final_num2 (st : Z * Z * Z) : Z :=
  let n2 := spec67_flush_num2 st in
  if Z.ltb n2 0 then 0%Z else n2.

Definition spec67_scan_output (s : string) (n : nat) : Z :=
  let st := spec67_scan_state_full (list_ascii_of_string s) in
  (Z.of_nat n - spec67_final_num1 st - spec67_final_num2 st)%Z.


(* Ground-truth proof helpers. *)
