## Iteration 1

- Phenomenon: `annotated/verify_20260604_165821_arithmetic_series.c` had no loop invariant, so `symexec` would have no preserved relationship between the loop counter `i`, the current term `cur`, and the accumulated prefix sum `sum`.
- Location: `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_165821_arithmetic_series.c`, the `while (i < n)` loop for target function `arithmetic_series`.
- Repair action: Add one loop invariant that states `0 <= i <= n`, preserves parameter equality to `@pre`, expresses `cur == a + i * d`, and expresses `sum == arithmetic_series_sum_z(a, d, i)`.
- Key annotation snippet:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre && d == d@pre && n == n@pre &&
      cur == a + i * d &&
      sum == arithmetic_series_sum_z(a, d, i)
*/
```

- Why this fix: the postcondition is a closed form over `n`, so the loop invariant needs the same closed form over the processed prefix `i`; `cur == a + i * d` makes one-step preservation match the loop body updates exactly, and the preserved parameter equalities prevent witness pollution from current-vs-`@pre` symbols.
