(* spec/33 *)
(* This function takes a list l and returns a list l' such that
l' is identical to l in the indicies that are not divisible by three, while its values at the indicies that are divisible by three are equal
to the values of the corresponding indicies of l, but sorted.
>>> sort_third([1, 2, 3])
[1, 2, 3]
>>> sort_third([5, 6, 3, 4, 8, 9, 2])
[2, 6, 3, 4, 8, 9, 5] *)

(* Spec(input : list int, output : list int) :=

​	length(input) = length(output) /\
​	∀i ∈ [0, length(input)), i % 3 <> 0 → output[i] = input[i]  /\
​	∀i ∈ [0, length(output)), ∃  j ∈ [0, length(intput))  i %3 = 0 -> j % 3 = 0 /\ input[j] = output[i]
​	∀i ∈ [0, length(input)), ∃  j ∈ [0, length(output))  i %3 = 0 -> j % 3 = 0 /\ output[j] = input[i] /\
​	∀i,j ∈ [0, length(input)), i,j % 3 == 0 /\ i < j → output[i] ≤ output[j]

*)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Import ListNotations.
(* Pre: no additional constraints for `sort_third` by default *)

(* Spec 的定义 *)

Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition problem_33_pre (input : list Z) : Prop :=
  True.

Definition problem_33_spec (input output : list Z) : Prop :=
  (((* 1. input 是 output 的排列 (Permutation) *)
    Permutation input output /\

    (* 2. 如果索引 i 不能被 3 整除，则 output[i] 必须等于 input[i] *)
    (forall i, 0 <= i < Zlength input -> Z.rem i 3 <> 0 ->
      Znth i output 0 = Znth i input 0) /\

    (* 3. output 中所有索引能被 3 整除的元素，必须是按索引顺序排好序的 (非递减) *)
    (forall i j, 0 <= i < Zlength output /\ 0 <= j < Zlength output /\
      Z.rem i 3 = 0 /\ Z.rem j 3 = 0 /\ i < j ->
      Znth i output 0 <= Znth j output 0))).

Definition third_count (n : Z) : Z :=
  (n + 2) ÷ 3.

Fixpoint third_values_prefix_nat (n : nat) (input : list Z) : list Z :=
  match n with
  | O => nil
  | S n' =>
      third_values_prefix_nat n' input ++
      cons (Znth (3 * Z.of_nat n') input 0) nil
  end.

Definition third_values_prefix (n : Z) (input : list Z) : list Z :=
  third_values_prefix_nat (Z.to_nat n) input.

Definition choose_sort_third_value (i : Z) (input sorted_third : list Z) : Z :=
  if Z.eqb (Z.rem i 3) 0
  then Znth (i ÷ 3) sorted_third 0
  else Znth i input 0.

Fixpoint sort_third_output_prefix_nat
  (n : nat) (input sorted_third : list Z) : list Z :=
  match n with
  | O => nil
  | S n' =>
      sort_third_output_prefix_nat n' input sorted_third ++
      cons (choose_sort_third_value (Z.of_nat n') input sorted_third) nil
  end.

Definition sort_third_output_prefix
  (n : Z) (input sorted_third : list Z) : list Z :=
  sort_third_output_prefix_nat (Z.to_nat n) input sorted_third.

Definition sort_third_output (input sorted_third : list Z) : list Z :=
  sort_third_output_prefix (Zlength input) input sorted_third.

Fixpoint nonthird_values_prefix_nat (n : nat) (input : list Z) : list Z :=
  match n with
  | O => nil
  | S n' =>
      let i := Z.of_nat n' in
      nonthird_values_prefix_nat n' input ++
      if Z.eqb (Z.rem i 3) 0 then nil else [Znth i input 0]
  end.

Definition nonthird_values_prefix (n : Z) (input : list Z) : list Z :=
  nonthird_values_prefix_nat (Z.to_nat n) input.

Definition sorted_ascending (l : list Z) : Prop :=
  forall i j,
    0 <= i < j ->
    j < Zlength l ->
    Znth i l 0 <= Znth j l 0.

Definition sorted_descending (l : list Z) : Prop :=
  forall i j,
    0 <= i < j ->
    j < Zlength l ->
    Znth j l 0 <= Znth i l 0.

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then sorted_descending l else sorted_ascending l.

Definition sorted_int_list (l : list Z) : Prop :=
  sorted_ascending l.
