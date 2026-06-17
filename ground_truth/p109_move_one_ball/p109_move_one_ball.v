(* spec/109 *)
(* We have an array 'arr' of N integers arr[1], arr[2], ..., arr[N].The
numbers in the array will be randomly ordered. Your task is to determine if
it is possible to get an array sorted in non-decreasing order by performing
the following operation on the given array:
You are allowed to perform right shift operation any number of times.

One right shift operation means shifting all elements of the array by one
position in the right direction. The last element of the array will be moved to
the starting position in the array i.e. 0th index.

If it is possible to obtain the sorted array by performing the above operation
then return True else return False.
If the given array is empty then return True.

Note: The given list is guaranteed to have unique elements.

For Example:

move_one_ball([3, 4, 5, 1, 2])==>True
Explanation: By performin 2 right shift operations, non-decreasing order can
be achieved for the given array.
move_one_ball([3, 5, 4, 1, 2])==>False
Explanation:It is not possible to get non-decreasing order for the given
array by performing any number of right shift operations. *)

(* 导入列表、整数和自然数所需的基础库 *)
Require Import List ZArith Arith.
Require Import Coq.Sorting.Sorted.
Open Scope Z_scope.
Import ListNotations.

Fixpoint is_sorted_bool (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | h1 :: t =>
      match t with
      | [] => true
      | h2 :: t' => if Z.leb h1 h2 then is_sorted_bool t else false
      end
  end.

Definition right_shift (l : list Z) : list Z :=
  match rev l with
  | [] => []
  | hd :: tl => hd :: rev tl
  end.

Fixpoint n_shifts (n : nat) (l : list Z) : list Z :=
  match n with
  | 0%nat => l
  | S n' => right_shift (n_shifts n' l)
  end.

Fixpoint check_all_shifts (arr : list Z) (n : nat) : bool :=
  match n with
  | O => is_sorted_bool arr
  | S n' => orb (is_sorted_bool (n_shifts n arr)) (check_all_shifts arr n')
  end.

Definition move_one_ball_impl (arr : list Z) : bool :=
  match arr with
  | [] => true
  | _ :: _ => check_all_shifts arr (length arr)
  end.

(* 输入数组元素互不相同（唯一性），可空列表允许直接返回 True *)


Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition problem_109_pre (arr : list Z) : Prop :=
  NoDup (arr).

Fixpoint count_descents_prefix_nat (n : nat) (arr : list Z) : Z :=
  match n with
  | O => 0
  | S O => 0
  | S n' =>
      count_descents_prefix_nat n' arr +
      (if Z.ltb (Znth (Z.of_nat n') arr 0) (Znth (Z.of_nat n' - 1) arr 0)
       then 1
       else 0)
  end.

Definition count_descents_prefix (i : Z) (arr : list Z) : Z :=
  count_descents_prefix_nat (Z.to_nat i) arr.

Definition cyclic_descents (arr : list Z) : Z :=
  count_descents_prefix (Zlength arr) arr +
  (if Z.ltb (Znth 0 arr 0) (Znth (Zlength arr - 1) arr 0)
   then 1
   else 0).

Definition problem_109_spec (arr : list Z) (result : Z) : Prop :=
  (result = 1 /\ cyclic_descents arr < 2) \/
  (result = 0 /\ 2 <= cyclic_descents arr).

Definition cyclic_result_bool (arr : list Z) : bool :=
  if Z.ltb (cyclic_descents arr) 2 then true else false.

Definition descents_int_range (arr : list Z) : Prop :=
  (forall i,
      1 <= i < Zlength arr ->
      INT_MIN <= count_descents_prefix i arr + 1 <= INT_MAX) /\
  INT_MIN <= cyclic_descents arr <= INT_MAX /\
  (cyclic_result_bool arr = true <-> move_one_ball_impl arr = true).

Lemma count_descents_prefix_1 : forall arr,
  count_descents_prefix 1 arr = 0.
Proof.
  reflexivity.
Qed.

Lemma count_descents_prefix_step_lt : forall arr i,
  1 <= i ->
  Znth i arr 0 < Znth (i - 1) arr 0 ->
  count_descents_prefix (i + 1) arr =
    count_descents_prefix i arr + 1.
Proof.
  intros arr i Hi Hlt.
  unfold count_descents_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  simpl.
  change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)).
  change match Pos.of_succ_nat n with
         | (p~1)%positive => Z.pos p~0
         | (p~0)%positive => Z.pos (Pos.pred_double p)
         | 1%positive => 0
         end with (Z.of_nat (S n) - 1).
  replace (Z.of_nat (S n)) with i by lia.
  apply Z.ltb_lt in Hlt.
  rewrite Hlt.
  reflexivity.
Qed.

Lemma count_descents_prefix_step_ge : forall arr i,
  1 <= i ->
  Znth i arr 0 >= Znth (i - 1) arr 0 ->
  count_descents_prefix (i + 1) arr =
    count_descents_prefix i arr.
Proof.
  intros arr i Hi Hge.
  unfold count_descents_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  simpl.
  change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)).
  change match Pos.of_succ_nat n with
         | (p~1)%positive => Z.pos p~0
         | (p~0)%positive => Z.pos (Pos.pred_double p)
         | 1%positive => 0
         end with (Z.of_nat (S n) - 1).
  replace (Z.of_nat (S n)) with i by lia.
  assert ((Znth i arr 0 <? Znth (i - 1) arr 0) = false) as Hfalse.
  { apply Z.ltb_ge. lia. }
  rewrite Hfalse.
  lia.
Qed.

Lemma cyclic_descents_tail_gt : forall arr,
  1 <= Zlength arr ->
  Znth (Zlength arr - 1) arr 0 > Znth 0 arr 0 ->
  cyclic_descents arr =
    count_descents_prefix (Zlength arr) arr + 1.
Proof.
  intros arr Hlen Hgt.
  unfold cyclic_descents.
  assert ((Znth 0 arr 0 <? Znth (Zlength arr - 1) arr 0) = true) as Htrue.
  { apply Z.ltb_lt. lia. }
  rewrite Htrue.
  reflexivity.
Qed.

Lemma cyclic_descents_tail_le : forall arr,
  1 <= Zlength arr ->
  Znth (Zlength arr - 1) arr 0 <= Znth 0 arr 0 ->
  cyclic_descents arr =
    count_descents_prefix (Zlength arr) arr.
Proof.
  intros arr Hlen Hle.
  unfold cyclic_descents.
  assert ((Znth 0 arr 0 <? Znth (Zlength arr - 1) arr 0) = false) as Hfalse.
  { apply Z.ltb_ge. lia. }
  rewrite Hfalse.
  lia.
Qed.

Lemma problem_109_spec_of_cyclic_true : forall arr,
  descents_int_range arr ->
  cyclic_descents arr < 2 ->
  problem_109_spec arr 1.
Proof.
  intros arr _ Hcyc.
  unfold problem_109_spec.
  left.
  lia.
Qed.

Lemma problem_109_spec_of_cyclic_false : forall arr,
  descents_int_range arr ->
  cyclic_descents arr >= 2 ->
  problem_109_spec arr 0.
Proof.
  intros arr _ Hcyc.
  unfold problem_109_spec.
  right.
  lia.
Qed.
