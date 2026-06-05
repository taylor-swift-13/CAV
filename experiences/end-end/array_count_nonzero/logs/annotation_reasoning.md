2026-06-05 iteration 1

Phenomenon: The active annotated file `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_000102v_array_count_nonzero.c` had no loop invariant for the `for (i = 0; i < n; ++i)` scan in `array_count_nonzero`, so the first symbolic-execution pass would not be able to preserve the accumulator semantics across iterations.

Location: `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_000102v_array_count_nonzero.c`, target function `array_count_nonzero`, loop over `i`.

Repair action: Add a loop invariant that models `count` as the specification value on the processed prefix `sublist 0 i l`, keeps the scan boundary `0 <= i <= n`, and preserves the read-only array ownership `IntArray::full(a, n, l)`.

Key annotation fragment:

```c
/*@ Inv
      0 <= i &&
      i <= n &&
      count == array_count_nonzero_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

Why this change: The implementation is a single left-to-right scan where each iteration either leaves `count` unchanged or increments it by 1 according to whether `a[i]` is zero. The natural closed form is therefore "accumulator equals spec on the processed prefix". At loop exit, `i == n` plus `Zlength(l) == n` should reduce the postcondition to the full-list specification without reconstructing extra semantic state.

2026-06-05 iteration 2

Phenomenon: The first generated `return_wit` in `/home/yangfp/CAV/C/CAV/output/verify_20260605_000102v_array_count_nonzero/coq/generated/array_count_nonzero_goal.v` required proving `IntArray.full a n l |-- IntArray.full a_pre n_pre l` with no explicit equalities connecting current parameters to pre-state parameters.

Location: `array_count_nonzero_return_wit_1` in `array_count_nonzero_goal.v`, caused by the loop invariant in `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_000102v_array_count_nonzero.c`.

Repair action: Strengthen the invariant with the parameter-preservation facts `a == a@pre` and `n == n@pre`.

Key annotation fragment:

```c
a == a@pre &&
n == n@pre &&
```

Why this change: The function never mutates the pointer value `a` or the integer `n`. If the invariant does not carry those equalities, the generated return witness has to reconstruct pre-state array ownership from a logically unrelated current-state `IntArray::full(a, n, l)`, which is the classic "parameter unchanged relation leaked into proof" failure mode described in the invariant/proof guidance.

2026-06-05 iteration 3

Phenomenon: `proof_of_array_count_nonzero_safety_wit_4` reduced to the arithmetic goal `count + 1 <= INT_MAX`, but the proof state only exposed `i < n_pre`, `count = array_count_nonzero_spec (sublist 0 i l)`, and array-length facts; it did not carry an explicit `n_pre <= INT_MAX` fact, so the safety side condition still depended on local-int range extraction.

Location: `array_count_nonzero_safety_wit_4` in `array_count_nonzero_goal.v`, sourced from the loop setup and invariant in `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_000102v_array_count_nonzero.c`.

Repair action: Add a local range fact `n <= INT_MAX by local` before the loop and strengthen the loop invariant with the natural accumulator bound `0 <= count && count <= i`.

Key annotation fragment:

```c
/*@ n <= INT_MAX by local */
...
0 <= count &&
count <= i &&
```

Why this change: The executable program uses `n` as a C `int`, and the loop body increments `count` at most once per processed element. Recording the machine-int upper bound at the annotation layer avoids a fragile proof that depends on spatial local-store reasoning, while `count <= i` makes the accumulator-range fact explicit at the actual loop control point instead of rebuilding it in Coq from the recursive spec every time a safety VC appears.
