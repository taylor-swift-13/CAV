Require Import ZArith.

Open Scope Z_scope.

Definition int_min : Z := -2147483648.
Definition int_max : Z := 2147483647.

Definition arithmetic_series_term_z (a d k : Z) : Z :=
  a + k * d.

Definition arithmetic_series_sum_z (a d n : Z) : Z :=
  n * a + d * n * (n - 1) / 2.

Definition arithmetic_series_pre (a d n : Z) : Prop :=
  0 <= n /\
  (forall k,
      0 <= k <= n ->
      int_min <= arithmetic_series_term_z a d k <= int_max) /\
  (forall k,
      0 <= k <= n ->
      int_min <= arithmetic_series_sum_z a d k <= int_max).
