(* spec/26 *)
(*  From a list of integers, remove all elements that occur more than once.
Keep order of elements left the same as in the input.
>>> remove_duplicates([1, 2, 3, 2, 4])
[1, 3, 4]
 *)

(* Spec(input : list int, output : list int) :=

(∀j ∈ [0, length(output)),
  ∃i ∈ [0, length(input)),
    input(i) = output(j)
    ∧ ∀k ∈ [0, length(input)), input(k) = input(i) → (k = i) )      ∧ -- output中每个元素都在input里面，且在input 中只出现过一次

 (∀i ∈ [0, length(input)):
      (∀k ∈ [0, length(input) ), input(k) = input(i) → (k = i)) →        -- input(i) 只出现一次
        ∃j ∈ [0, m), output(j) = input(i) ）∧                  -- 就一定出现在 output 中

（∀j1, j2 ∈ [0, length(output)), ∃i1, i2 ∈ [0, length(input)):
      output(j1) = input(i1) ∧ output(j2) = input(i2)  ∧ j1 < j2 → i1 < i2）     -- 保持顺序 *)

(* 引入必要的库 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.

Definition problem_26_pre (input : list Z): Prop := True.

Definition occurs_once_at (l : list Z) (x i : Z) : Prop :=
  0 <= i < Zlength l /\
  Znth i l 0 = x /\
  forall k, 0 <= k < Zlength l -> Znth k l 0 = x -> k = i.

Definition occurs_once (l : list Z) (x : Z) : Prop :=
  exists i, occurs_once_at l x i.

(* 程序规约 Spec 的 Coq 定义 *)
Definition problem_26_spec (input : list Z) (output : list Z) : Prop :=
  (*  1: output 中的每个元素 v 都存在于 input 中，
     并且 v 在 input 中是唯一的。 *)
  (forall j, 0 <= j < Zlength output ->
     occurs_once input (Znth j output 0)) /\

  (*  2: input 中任何只出现一次的元素，也必须出现在 output 中。 *)
  (forall i, 0 <= i < Zlength input ->
     occurs_once_at input (Znth i input 0) i ->
     In (Znth i input 0) output) /\

  (*  3: output 中元素的相对顺序与它们在 input 中的相对顺序保持一致。 *)
  (forall j1 j2, 0 <= j1 < j2 -> j2 < Zlength output ->
     exists i1 i2,
       0 <= i1 < i2 /\
       i2 < Zlength input /\
       Znth i1 input 0 = Znth j1 output 0 /\
       Znth i2 input 0 = Znth j2 output 0).

Require Import Lia.

Definition list_contains (x : Z) (l : list Z) : Prop :=
  In x l.

Definition list_not_contains (x : Z) (l : list Z) : Prop :=
  ~ In x l.

Definition appears_twice (x : Z) (l : list Z) : Prop :=
  exists i j,
    i <> j /\
    nth_error l i = Some x /\
    nth_error l j = Some x.

Fixpoint seen_values_aux (seen rest : list Z) : list Z :=
  match rest with
  | [] => seen
  | x :: xs =>
      if in_dec Z.eq_dec x seen
      then seen_values_aux seen xs
      else seen_values_aux (seen ++ [x]) xs
  end.

Definition seen_values (l : list Z) : list Z :=
  seen_values_aux [] l.

Fixpoint duplicate_values (seen duplicates rest : list Z) : list Z :=
  match rest with
  | [] => duplicates
  | x :: xs =>
      if in_dec Z.eq_dec x duplicates then
        duplicate_values seen duplicates xs
      else if in_dec Z.eq_dec x seen then
        duplicate_values seen (duplicates ++ [x]) xs
      else
        duplicate_values (seen ++ [x]) duplicates xs
  end.

Definition remove_duplicates_first_loop
  (input : list Z) (i : Z) (has1 has2 : list Z) : Prop :=
  0 <= i <= Zlength input /\
  has1 = seen_values (sublist 0 i input) /\
  has2 = duplicate_values [] [] (sublist 0 i input).

Fixpoint filter_not_in (duplicates input : list Z) : list Z :=
  match input with
  | [] => []
  | x :: xs =>
      if in_dec Z.eq_dec x duplicates
      then filter_not_in duplicates xs
      else x :: filter_not_in duplicates xs
  end.

Definition remove_duplicates_second_loop
  (input has2 : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= Zlength input /\
  output = filter_not_in has2 (sublist 0 i input).
