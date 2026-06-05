2026-06-05T00:00:00Z

Phenomenon: `annotated/verify_20260605_002002v_array_index_of_max.c` had no loop annotation for the single scan in `array_index_of_max`, so `symexec` would have no preserved summary for the processed prefix and no path to the postcondition.

Location: `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_002002v_array_index_of_max.c`, function `array_index_of_max`, loop `while (i < n)`.

Repair action: Added one loop invariant describing the exact processed-prefix semantics:
`1 <= i <= n`, `0 <= idx < i`, every processed position `j < i` satisfies `l[j] <= l[idx]`, every earlier position `j < idx` satisfies `l[j] < l[idx]`, and `IntArray::full(a, n, l)` preserves the read-only array model.

Key code: the invariant is attached immediately before `while (i < n)` and uses the prefix `[0, i)` because the control point is the loop guard, not the loop-body exit.

Why this change: the postcondition asks for both global maximality and earliest-index tie breaking. Maintaining `idx` as the earliest maximum of the processed prefix is the smallest loop summary that initializes at `i = 1`, is preserved by the `if (a[i] > a[idx]) idx = i;` update, and should yield the final result when the loop exits with `i == n`.

2026-06-05T00:00:00Z

Phenomenon: after proving the loop-preservation witnesses, the remaining return VC still asked to prove `IntArray.full a_pre n_pre l` from `IntArray.full a n l`, plus `idx < n_pre` and the max-property over `n_pre`.

Location: generated return witness `array_index_of_max_return_wit_1` in `/home/yangfp/CAV/C/CAV/output/verify_20260605_002002v_array_index_of_max/coq/generated/array_index_of_max_goal.v`.

Repair action: strengthen the loop invariant with explicit parameter-preservation facts `a == a@pre` and `n == n@pre`.

Key proof-state fragment after `pre_process; entailer!`:
`IntArray.full a n l |-- IntArray.full a_pre n_pre l`
with no pure equality bridge between current and pre-state parameters.

Why this change: this is exactly the invariant-gap pattern from the verify guidance. `array_index_of_max` never mutates `a` or `n`, so the correct place to preserve those equalities is the loop invariant; once regenerated, the return VC should be phrased over the same array base and bound as the postcondition.
