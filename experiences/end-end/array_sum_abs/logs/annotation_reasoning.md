2026-06-05T00:00:00+08:00

Symptom: the first `symexec` run stopped at [verify_20260605_005812v_array_sum_abs.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_005812v_array_sum_abs.c:22) with `Error: Lack of assertions in some paths for the loop!`, so the loop had no head-state description at all.

Location: the only failing control point is the `while (i < n)` loop in [verify_20260605_005812v_array_sum_abs.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_005812v_array_sum_abs.c:22). The postcondition requires the final return value to equal `sum_abs(l)` while preserving `IntArray::full(a, n, l)`, so the loop needs a prefix-summary invariant.

Fix action: add a single `Inv Assert` directly on the loop. The invariant states that `i` is the next unread index (`0 <= i <= n`), `a` and `n` remain equal to their pre-state values, the input list facts from the contract remain available, `sum` equals `sum_abs(sublist(0, i, l))`, and the array heap is still `IntArray::full(a, n, l)`.

Key annotation shape:

```c
/*@ Inv Assert
      a == a@pre && n == n@pre &&
      0 <= i && i <= n &&
      Zlength(l) == n &&
      (forall (j: Z), (0 <= j && j < n) => (-2147483647 <= l[j])) &&
      0 <= sum_abs(l) && sum_abs(l) <= 2147483647 &&
      sum == sum_abs(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

Why this change: at the loop head, `i` counts exactly the processed prefix `[0, i)`, so `sum == sum_abs(sublist(0, i, l))` is the natural closed-form summary of the accumulator. Carrying `a == a@pre`, `n == n@pre`, and `IntArray::full(a, n, l)` avoids forcing later witnesses to reconstruct parameter preservation or heap stability. Keeping the original element lower bound and whole-array sum bound available should be enough for the branch `v = -v` and the eventual integer-range proof obligations after the next `symexec`.
