2026-06-05 iteration 1

Phenomenon: The initial annotated loop had no invariant, so verification had no preserved semantic summary for the left-to-right scan.

Location: `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_000102v_array_count_nonzero.c`, loop in `array_count_nonzero`.

Repair action: Added a loop invariant stating that `count` equals `array_count_nonzero_spec(sublist(0, i, l))` and that the array ownership `IntArray::full(a, n, l)` is preserved.

Key fragment:

```c
count == array_count_nonzero_spec(sublist(0, i, l))
```

Why this worked: The loop processes exactly the prefix `[0, i)`, so the recursive spec on that prefix is the right closed form for the accumulator.

2026-06-05 iteration 2

Phenomenon: The first regenerated `return_wit` required proving `IntArray.full a n l |-- IntArray.full a_pre n_pre l` without any explicit connection between current and pre-state parameters.

Location: `array_count_nonzero_return_wit_1` in `/home/yangfp/CAV/C/CAV/output/verify_20260605_000102v_array_count_nonzero/coq/generated/array_count_nonzero_goal.v`.

Repair action: Strengthened the invariant with `a == a@pre` and `n == n@pre`, then reran `symexec`.

Key fragment:

```c
a == a@pre &&
n == n@pre &&
```

Why this worked: The function never mutates those parameters, so the invariant should carry those equalities instead of forcing Coq to reconstruct them from unrelated heap facts.

2026-06-05 iteration 3

Phenomenon: `proof_of_array_count_nonzero_safety_wit_4` still reduced to `count + 1 <= INT_MAX`, but the proof state did not expose the needed machine-int upper bound on `n_pre`.

Location: `array_count_nonzero_safety_wit_4` in `array_count_nonzero_goal.v`.

Repair action: Added `/*@ n <= INT_MAX by local */` before the loop and strengthened the invariant with `0 <= count && count <= i`, then reran `symexec`.

Key fragment:

```c
/*@ n <= INT_MAX by local */
0 <= count &&
count <= i &&
```

Why this worked: The loop increments `count` at most once per processed element, so `count <= i < n` plus the explicit local-int bound is the right source-level justification for the overflow safety witness.

2026-06-05 iteration 4

Phenomenon: Full Coq replay first failed at `array_count_nonzero_goal.v` with `Required library int_array_strategy_goal matches several files in path`, because the generated file imported short strategy names that were ambiguous between `QCP_demos_LLM` and `QCP_demos_human`.

Location: `array_count_nonzero_goal.v`, compile gate `coqc goal.v`.

Repair action: Added workspace-local wrapper modules in `/home/yangfp/CAV/C/CAV/output/verify_20260605_000102v_array_count_nonzero/original/` for `int_array`, `uint_array`, `undef_uint_array`, and `array_shape` strategy goal/proof modules, each re-exporting or including the `SimpleC.EE.QCP_demos_LLM` implementation.

Key fragment:

```coq
From SimpleC.EE.QCP_demos_LLM Require Export int_array_strategy_goal.
```

Why this worked: `-Q "$ORIG" ""` then resolves the short import names to a unique module inside the current workspace before Coq searches the ambiguous shared examples tree.

2026-06-05 iteration 5

Phenomenon: The manual proof initially failed on helper-lemma and rewrite-shape issues (`Cannot find witness`, then `Unable to find an instance for the variable d`, then a return-witness rewrite mismatch).

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_000102v_array_count_nonzero/coq/generated/array_count_nonzero_proof_manual.v`, lemmas `array_count_nonzero_spec_prefix_succ` and `proof_of_array_count_nonzero_return_wit_1`.

Repair action: Proved the branch witnesses with helper lemmas `array_count_nonzero_spec_app` and `array_count_nonzero_spec_prefix_succ`, instantiated `sublist_single` as `(sublist_single 0 i l)`, and rewrote the return goal via the preserved equality `count = array_count_nonzero_spec (sublist 0 i l)` before using `sublist_self`.

Key fragment:

```coq
rewrite array_count_nonzero_spec_prefix_succ by lia.
...
rewrite H.
subst i.
rewrite sublist_self by lia.
```

Why this worked: After the annotation cleanup, the remaining VCs were pure list/arithmetic obligations. The helper lemma matches the exact prefix-extension shape of the loop body, and the return witness needed the generated equality to expose the `sublist 0 i l` term before rewriting it to the full list.
