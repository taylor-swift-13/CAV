2026-06-05T00:00:00Z
Phenomenon: The function [annotated/verify_20260605_001513v_array_fill_value.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_001513v_array_fill_value.c) has a `while (i < n)` loop that overwrites `a[i]` with `k`, but it currently has no loop invariant, so `symexec` cannot preserve the array-shape/value relation across iterations.
Location: loop in `array_fill_value`, control point immediately before the `while (i < n)` guard.
Repair action: Add an invariant that splits the array into a processed prefix and an unprocessed suffix, with `0 <= i <= n`, `Zlength(l) == n`, and `(forall j, 0 <= j < i -> l[j] == k)` describing the processed prefix while keeping `IntArray::full(a, n, l)` for the whole current heap state.
Key annotation shape:
```c
/*@ Inv
      0 <= i && i <= n &&
      Zlength(l) == n &&
      (forall (j: Z), (0 <= j && j < i) => l[j] == k) &&
      IntArray::full(a, n, l)
*/
```
Why this change: At loop entry `i == 0`, so the prefix property is vacuous. After executing `a[i] = k; i++;`, the processed prefix grows by one element and the array predicate tracks the updated contents. On loop exit `i >= n` plus the invariant yields `i == n`, so the prefix fact covers the full array and matches the postcondition directly.

2026-06-05T00:00:00Z
Phenomenon: The first `symexec` run generated [array_fill_value_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_001513v_array_fill_value/coq/generated/array_fill_value_proof_manual.v) with `array_fill_value_return_wit_1` quantified over both current parameters `(a, k, n)` and pre-state parameters `(a_pre, k_pre, n_pre)`, but the theorem premise retained no equality connecting them. The goal requires `IntArray::full a_pre n_pre lr` and `lr[i] = k_pre`, so the VC is underconstrained.
Location: generated theorem `array_fill_value_return_wit_1`, caused by the loop invariant in [annotated/verify_20260605_001513v_array_fill_value.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_001513v_array_fill_value.c).
Repair action: Extend the invariant with `a == a@pre`, `k == k@pre`, and `n == n@pre` so symbolic execution carries unchanged-parameter facts through the loop and into the return witness.
Key annotation fragment:
```c
a == a@pre &&
k == k@pre &&
n == n@pre &&
```
Why this change: The loop does not modify the pointer `a` or scalar parameters `k` and `n`. Preserving those equalities at the annotation layer is the stable way to relate the final heap/value facts back to the function postcondition; without them, the manual proof would have to prove arbitrary equalities that are not derivable from the current VC.

2026-06-05T00:00:00Z
Phenomenon: Even after carrying `a == a@pre`, `k == k@pre`, and `n == n@pre`, the regenerated `array_fill_value_entail_wit_2` still required proving `IntArray.full ... (replace_Znth i k lr) |-- IntArray.full ... lr` with no existential on the target list. That means the invariant is naming the mutable array contents with the wrong logical variable across the store.
Location: loop invariant in [annotated/verify_20260605_001513v_array_fill_value.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_001513v_array_fill_value.c); confirmed by comparison with the allowed fill-style reference [experiences/end-end/string_fill_char/coq/generated/string_fill_char_goal.v](/home/yangfp/CAV/C/CAV/experiences/end-end/string_fill_char/coq/generated/string_fill_char_goal.v:1).
Repair action: Replace the single-list invariant with `exists lr`, where `l` stays the original input list and `lr` tracks the current array contents. The invariant records that the prefix `[0, i)` of `lr` is already filled with `k`, while the suffix `[i, n@pre)` still matches the original list `l`.
Key annotation shape:
```c
/*@ Inv exists lr,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      k == k@pre &&
      n == n@pre &&
      Zlength(lr) == n@pre &&
      (forall (j: Z), (0 <= j && j < i) => lr[j] == k) &&
      (forall (j: Z), (i <= j && j < n@pre) => lr[j] == l[j]) &&
      IntArray::full(a, n@pre, lr)
*/
```
Why this change: After `a[i] = k`, the concrete heap is naturally described as `replace_Znth i k lr`. The next loop-head state should therefore choose a fresh witness list for the updated heap rather than force the old `lr` to remain unchanged. Keeping `l` fixed as the original contents preserves the postcondition’s meaning, and the suffix clause provides the fact `lr[i] == l[i]` exactly at the write index before the update.
