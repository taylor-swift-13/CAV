2026-06-05 iteration 1

Gate: `symexec`

Phenomenon: The first symbolic-execution pass on `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_001431v_array_count_odd.c` failed at the `while (i < n)` loop with `Error: Lack of assertions in some paths for the loop!`.

Location: annotated C file `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_001431v_array_count_odd.c`, target function `array_count_odd`, loop header around line 22 in the initial version.

Repair action: Add a loop invariant summarizing the processed prefix with `count == array_count_odd_spec(sublist(0, i, l))`, preserve `a == a@pre` and `n == n@pre`, keep `IntArray::full(a, n, l)`, and add `n <= INT_MAX by local`.

Key fragment:

```c
/*@ Inv Assert
      a == a@pre &&
      n == n@pre &&
      0 <= i &&
      i <= n &&
      0 <= count &&
      count <= i &&
      count == array_count_odd_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

Why this worked: The loop is a standard read-only prefix scan, so the accumulator should be modeled as the spec value of the processed prefix at the loop head.

2026-06-05 iteration 2

Gate: `coqc proof_manual.v`

Phenomenon: The first manual-proof replay failed in `proof_of_array_count_odd_entail_wit_3_1` when trying to rewrite the one-step prefix lemma. After `pre_process; entailer!`, the generated witness no longer exposed `Zlength(l) == n_pre` or `n_pre <= INT_MAX`, so the proof could not discharge the helper lemma side condition from the VC shape alone.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_001431v_array_count_odd/coq/generated/array_count_odd_goal.v`, theorem `array_count_odd_entail_wit_3_1`; failing script in `/home/yangfp/CAV/C/CAV/output/verify_20260605_001431v_array_count_odd/coq/generated/array_count_odd_proof_manual.v`.

Repair action: Strengthen the loop invariant in the annotated C with the preserved pure facts `n <= INT_MAX` and `Zlength(l) == n`, rerun `symexec`, then regenerate the helper-based manual proof against the new witnesses.

Key fragment:

```c
n <= INT_MAX &&
Zlength(l) == n &&
```

Why this worked: These facts are stable across the loop and belong in the invariant. Keeping them in the VC avoids brittle proof-layer extraction from the spatial array predicate.

2026-06-05 iteration 3

Gate: `coqc goal.v`

Phenomenon: The first full replay compile stopped before theorem checking with `Required library int_array_strategy_goal matches several files in path`, because the generated short-name strategy imports were ambiguous between `QCP_demos_LLM` and `QCP_demos_human`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_001431v_array_count_odd/coq/generated/array_count_odd_goal.v`, import section; duplicate libraries under `/home/yangfp/CAV/C/CAV/QualifiedCProgramming/SeparationLogic/examples/`.

Repair action: Add workspace-local short-name wrapper modules in `/home/yangfp/CAV/C/CAV/output/verify_20260605_001431v_array_count_odd/original/` for `int_array`, `uint_array`, `undef_uint_array`, and `array_shape`, with `Require Export` wrappers for `*_goal` and `Require Import` plus `Include` wrappers for `*_proof`.

Key fragment:

```coq
From SimpleC.EE.QCP_demos_LLM Require Export int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.int_array_strategy_proof.
```

Why this worked: The generated files remained unchanged, while `-Q "$ORIG" ""` resolved the ambiguous short imports to a unique workspace-local wrapper path during replay.
