# Absolute-value scan: guard `-INT_MIN` and bound the total spec

Symptom:

- The implementation does `if (v < 0) v = -v; sum += v;` while scanning a read-only `int` array.
- A contract that only states the final mathematical result is often too weak for C safety: verify later still has to prove both the negation and the accumulation stay inside signed `int`.

Cause:

- There are two distinct UB sites:
  - `v = -v` is undefined at `v == INT_MIN`
  - `sum += v` is undefined if some running total exceeds `INT_MAX`
- For `abs`-sum scans, every per-step contribution is nonnegative, so every prefix sum is bounded by the final `sum_abs(l)`.

Rule:

- Put the negation guard in the contract as an elementwise lower bound:
  - `(forall (j: Z), (0 <= j && j < n) => (-2147483647 <= l[j]))`
- Also bound the whole mathematical result:
  - `0 <= sum_abs(l) && sum_abs(l) <= 2147483647`
- Then keep the postcondition simple: return the mathematical `sum_abs(l)` and preserve the read-only array shape.

Minimal shape:

```c
/*@ Require
      0 <= n &&
      IntArray::full(a, n, l) &&
      Zlength(l) == n &&
      (forall (j: Z), (0 <= j && j < n) => (-2147483647 <= l[j])) &&
      0 <= sum_abs(l) && sum_abs(l) <= 2147483647
    Ensure
      __return == sum_abs(l) &&
      IntArray::full(a, n, l)
*/
```

Why this is enough:

- The elementwise lower bound excludes the only signed-negation overflow case.
- Because `abs(x) >= 0`, every processed-prefix sum is `<= sum_abs(l)`, so the final bound also protects all intermediate accumulator states.

Scope:

- Read-only `int` array scans that accumulate absolute values
- Equivalent loops where the per-step update is mathematically nonnegative and the accumulator is a monotone prefix summary
