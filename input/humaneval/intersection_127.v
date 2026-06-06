(* spec/127 *)
(*You are given two intervals,
where each interval is a pair of integers. For example, interval = (start, end) = (1, 2).
The given intervals are closed which means that the interval (start, end)
includes both start and end.
For each given interval, it is assumed that its start is less or equal its end.
Your task is to determine whether the length of intersection of these two
intervals is a prime number.
Example, the intersection of the intervals (1, 3), (2, 4) is (2, 3)
which its length is 1, which not a prime number.
If the length of the intersection is a prime number, return "YES",
otherwise, return "NO".
If the two intervals don't intersect, return "NO".

[input/output] samples:
intersection((1, 2), (2, 3)) ==> "NO"
intersection((-1, 1), (0, 4)) ==> "NO"
intersection((-3, -1), (-5, 5)) ==> "YES" *)

(* 引入所需的基础 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
(* 提供 Nat 的比较和取模运算 *)

(* 允许使用列表和作用域的标准表示法 *)
Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope string_scope.

(* 区间为闭区间，且满足 start <= end *)


Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import naive_C_Rules.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition yesno_of (z : Z) : string :=
  if Z.eqb z 1 then "YES" else "NO".

Definition interval_pair (l : list Z) : Z * Z :=
  (Znth 0 l 0, Znth 1 l 0).

Definition inter_start (i1 i2 : list Z) : Z :=
  Z.max (Znth 0 i1 0) (Znth 0 i2 0).

Definition inter_end (i1 i2 : list Z) : Z :=
  Z.min (Znth 1 i1 0) (Znth 1 i2 0).

Definition inter_len (i1 i2 : list Z) : Z :=
  inter_end i1 i2 - inter_start i1 i2.

Definition problem_127_pre (i1 i2 : list Z) : Prop :=
  let '(s1,e1) := ((interval_pair i1)) in
  let '(s2,e2) := ((interval_pair i2)) in (s1 <= e1)%Z /\ (s2 <= e2)%Z.

Definition problem_127_spec (i1 i2 : list Z) (output : Z) : Prop :=
  ((let (s1, e1) := ((interval_pair i1)) in
    let (s2, e2) := ((interval_pair i2)) in
  
    (* 计算交集的起始点和结束点 *)
    let s_inter := Z.max s1 s2 in
    let e_inter := Z.min e1 e2 in
  
    (* 分情况讨论：区间是否相交 *)
    if Z.leb s_inter e_inter then
      (* 情况1: 区间相交 *)
      let len_nat := Z.to_nat (e_inter - s_inter) in
      (* 规约：
         - 如果交集长度是素数，那么输出必须是 "YES"。
         - 如果交集长度不是素数，那么输出必须是 "NO"。
         我们用逻辑 "或" (\/) 来连接这两种可能。*)
      (prime (Z.of_nat len_nat) /\ ((yesno_of output)) = "YES") \/
      (~prime (Z.of_nat len_nat) /\ ((yesno_of output)) = "NO")
    else
      (* 情况2: 区间不相交，输出必须是 "NO" *)
      ((yesno_of output)) = "NO")%nat).

Definition interval_int_range (l : list Z) : Prop :=
  Zlength l = 2 /\
  forall i, 0 <= i < 2 -> -1000000000 <= Znth i l 0 <= 1000000000.

Definition prime_prefix (i n : Z) : Prop :=
  forall d, 2 <= d < i -> Z.rem n d <> 0.

Definition prime_len (n : Z) : Prop :=
  2 <= n /\ forall d, 2 <= d /\ d * d <= n -> Z.rem n d <> 0.
