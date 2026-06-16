(* spec/138 *)
(* def is_equal_to_sum_even(n):
"""Evaluate whether the given number n can be written as the sum of exactly 4 positive even numbers
Example
is_equal_to_sum_even(4) == False
is_equal_to_sum_even(6) == False
is_equal_to_sum_even(8) == True
""" *)
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* 任意整数 n 均可 *)
Definition problem_138_pre (n : Z) : Prop := True.

(* A number is the sum of four positive even integers exactly when it is
   even and at least 8. Adapt bool result to Z: r <> 0 means true. *)
Definition problem_138_spec (n r : Z) : Prop :=
  r <> 0 <-> 8 <= n /\ n mod 2 = 0.
