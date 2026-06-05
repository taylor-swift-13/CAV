2026-06-04 23:12:14 +0800

Phenomenon: `annotated/verify_20260604_230601v_array_count_between.c` had no loop annotation, so `symexec` would not be able to connect the running variable `count` to the postcondition `array_count_between_spec(l, lo@pre, hi@pre)`.

Location: `annotated/verify_20260604_230601v_array_count_between.c`, the `while (i < n)` loop in `array_count_between`.

Repair action: introduce a loop invariant that treats `count` as the summary of the already processed prefix `sublist 0 i l`, while also preserving the array ownership and the unchanged parameters needed later in return witnesses.

Key annotation shape:

```c
/*@ Inv
      0 <= i && i <= n &&
      count == array_count_between_spec(sublist(0, i, l), lo@pre, hi@pre) &&
      n == n@pre &&
      a == a@pre &&
      lo == lo@pre &&
      hi == hi@pre &&
      IntArray::full(a, n, l)
*/
```

Why this change: this is the standard prefix-summary invariant for a counting scan. At loop exit, `i == n` should let the proof reduce `sublist(0, n, l)` to `l`, yielding the postcondition directly up to list/arithmetic rewrites.

2026-06-04 23:12:14 +0800

Phenomenon: `proof_of_array_count_between_safety_wit_3` could prove `count + 1 >= INT_MIN` from the prefix-count nonnegativity bound, but the generated VC had no pure hypothesis implying `n_pre <= INT_MAX`, so the upper safety goal `count + 1 <= INT_MAX` was not derivable even though `n` is a C `int`.

Location: loop-entry facts for `while (i < n)` in `annotated/verify_20260604_230601v_array_count_between.c`; proof failure surfaced in `coq/generated/array_count_between_proof_manual.v` at `proof_of_array_count_between_safety_wit_3`.

Repair action: extract `n <= INT_MAX` from the local `int` store with a `by local` assertion before the loop and preserve that fact in the invariant.

Key missing proof context:

```text
H1 : i < n_pre
H5 : 0 <= n_pre
...
============================
count + 1 <= 2147483647
```

Why this change: the arithmetic safety theorem is about representability of updated C integers. The front-end already knows `n` is stored as an `Int`; the right fix is to carry that representability fact through symbolic execution, not to force the Coq proof to reason from a hypothesis that is absent.
