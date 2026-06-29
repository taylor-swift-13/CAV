Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import FunInd.
From AUXLib Require Import ListLib.
Require Import base_conversion_lib.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition problem_15_pre (n : Z) : Prop :=
  True.

Fixpoint sequence_prefix_nat (count : nat) : list Z :=
  match count with
  | O => []
  | S O => base_digits 0 10
  | S count' => sequence_prefix_nat count' ++ 32 :: base_digits (Z.of_nat count') 10
  end.

Definition sequence_prefix (i : Z) : list Z :=
  sequence_prefix_nat (Z.to_nat i).

Definition sequence_output (n : Z) : list Z :=
  sequence_prefix (n + 1).

Definition problem_15_spec (n : Z) (output : list Z) : Prop :=
  output = sequence_output n.

Definition sequence_output_bound (n : Z) : Prop :=
  Zlength (sequence_output n) + 1 <= 12 * (n + 1) + 1.
