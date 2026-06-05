## 2026-06-05 01:30:59 CST

Phenomenon: `annotated/verify_20260605_012416v_array_sum_positive.c` had the original contract but no loop annotation, so `symexec` would have no summary for the `for` loop in `array_sum_positive`.

Location: `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_012416v_array_sum_positive.c`, function `array_sum_positive`, `for (int i = 0; i < n; i++)`.

Repair action: add a loop invariant that models the executable state as a processed-prefix summary:

```c
/*@ Inv
      0 <= i && i <= n &&
      sum == array_sum_positive_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

Why this change: the loop is a forward scan with one accumulator, so the stable semantic fact is "current `sum` equals the spec on the already processed prefix `sublist(0, i, l)`". This invariant is initialized by `i == 0` and `sum == 0`, preserved by either skipping a non-positive element or adding a positive one, and at loop exit `i == n` it should collapse directly to the postcondition over the full list.

## 2026-06-05 01:30:59 CST

Phenomenon: after the first successful `symexec`, generated `array_sum_positive_return_wit_1` in `/home/yangfp/CAV/C/CAV/output/verify_20260605_012416v_array_sum_positive/coq/generated/array_sum_positive_goal.v` required proving `IntArray.full a_pre n_pre l` from antecedent state that only carried `IntArray.full a n l`, with no pure fact connecting `a` to `a_pre` or `n` to `n_pre`.

Location: generated witness `array_sum_positive_return_wit_1`; root cause in `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_012416v_array_sum_positive.c`, loop invariant for `array_sum_positive`.

Repair action: strengthen the invariant with parameter-stability facts and an explicit nonnegativity fact for the accumulator:

```c
      a == a@pre &&
      n == n@pre &&
      0 <= sum &&
```

Why this change: `a` and `n` are read-only parameters, so failing to preserve `a == a@pre` and `n == n@pre` pollutes the return witness with an avoidable current/pre mismatch. Carrying `0 <= sum` also matches the semantic meaning of the positive-prefix sum and reduces later safety side conditions to local arithmetic instead of re-deriving nonnegativity from the recursive spec in every witness.
