## Iteration 1

Phenomenon: The annotated function had no loop invariant for the `for (int i = 0; i < n; i++)` scan in [verify_20260605_010426v_array_sum_nonnegative.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_010426v_array_sum_nonnegative.c). A single-loop accumulator over an array will not survive symbolic execution without an invariant at the loop head.

Location: `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_010426v_array_sum_nonnegative.c`, target function `array_sum_nonnegative`, loop index `i`, accumulator `sum`.

Fix action: Add a loop invariant at the `for` statement describing the real control point: `0 <= i <= n`, `sum` equals `array_sum_nonnegative_spec (sublist 0 i l)`, the sum remains within `int` range, and the read-only array predicate `IntArray::full(a, n, l)` is preserved.

Key annotation fragment:

```c
/*@ Inv
      0 <= i && i <= n &&
      sum == array_sum_nonnegative_spec(sublist(0, i, l)) &&
      0 <= sum &&
      sum <= 2147483647 &&
      IntArray::full(a, n, l)
*/
```

Why this change: The loop processes exactly one new array element per iteration and conditionally adds `max(a[i], 0)`. Modeling `sum` as the spec of the processed prefix is the natural closed form for initialization (`i = 0`, empty prefix), preservation (extend prefix by one element), and exit (`i = n`, whole list).

## Iteration 2

Phenomenon: The first `symexec` run succeeded, but the generated return witness in `/home/yangfp/CAV/C/CAV/output/verify_20260605_010426v_array_sum_nonnegative/coq/generated/array_sum_nonnegative_goal.v` quantified both current `a, n` and pre-state `a_pre, n_pre` while only assuming `IntArray.full a n l` in the loop-exit premise. The conclusion required `IntArray.full a_pre n_pre l`, so the VC was missing the parameter-unchanged facts.

Location: `array_sum_nonnegative_return_wit_1` in `coq/generated/array_sum_nonnegative_goal.v`, rooted in the loop invariant of [verify_20260605_010426v_array_sum_nonnegative.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_010426v_array_sum_nonnegative.c).

Fix action: Strengthen the loop invariant with explicit parameter preservation facts `a == a@pre` and `n == n@pre`, then rerun `symexec` to regenerate cleaner witnesses instead of forcing an impossible manual proof.

Key annotation fragment:

```c
/*@ Inv
      ...
      a == a@pre &&
      n == n@pre &&
      ...
*/
```

Why this change: For a read-only scan, the input pointer and length are semantically constant across the loop. Keeping those equalities in the invariant lets the exit VC reuse the original postcondition shape directly and avoids spurious `a` versus `a_pre` / `n` versus `n_pre` proof obligations.
