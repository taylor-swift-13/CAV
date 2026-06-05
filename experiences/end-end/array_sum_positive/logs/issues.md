## 2026-06-05 01:40:00 CST

Phenomenon: the initial loop invariant in `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_012416v_array_sum_positive.c` tracked only `sum == array_sum_positive_spec(sublist(0, i, l))` and omitted parameter-stability facts.

Location: generated witness `array_sum_positive_return_wit_1` in `/home/yangfp/CAV/C/CAV/output/verify_20260605_012416v_array_sum_positive/coq/generated/array_sum_positive_goal.v`.

Repair action: strengthen the invariant with:

```c
a == a@pre &&
n == n@pre &&
0 <= sum &&
```

Why this fixed it: without `a == a@pre` and `n == n@pre`, the return witness had to rebuild `IntArray.full a_pre n_pre l` from `IntArray.full a n l` with no connecting fact, which is an annotation-layer defect rather than a proof-layer gap.

## 2026-06-05 01:40:00 CST

Phenomenon: replay compilation of `array_sum_positive_goal.v` failed before proof work with:

```text
Error: Required library int_array_strategy_goal matches several files in path
```

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_012416v_array_sum_positive/coq/generated/array_sum_positive_goal.v`, during `coqc`.

Repair action: add workspace-local short-name wrappers in `/home/yangfp/CAV/C/CAV/output/verify_20260605_012416v_array_sum_positive/coq/deps/` for:

- `int_array_strategy_{goal,proof}.v`
- `uint_array_strategy_{goal,proof}.v`
- `undef_uint_array_strategy_{goal,proof}.v`
- `array_shape_strategy_{goal,proof}.v`

Each wrapper re-exports or includes the `QCP_demos_LLM` strategy module, and replay compilation then uses `-Q "$DEPS" ""`.

Why this fixed it: the generated files import short strategy names, and the shared examples tree contains both `QCP_demos_LLM` and `QCP_demos_human` variants. The wrappers make those short imports resolve deterministically without modifying generated files or shared libraries.

## 2026-06-05 01:40:00 CST

Phenomenon: the first helper proof attempt for `array_sum_positive_spec_prefix_le` failed at `sublist_split` with `Cannot find witness`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_012416v_array_sum_positive/coq/generated/array_sum_positive_proof_manual.v`, helper lemma `array_sum_positive_spec_prefix_le`.

Repair action: make both rewrites explicit and targeted:

```coq
rewrite <- (sublist_self l (Zlength l)) at 1 by reflexivity.
rewrite (sublist_split 0 (Zlength l) hi l) by lia.
rewrite Hsplit at 2.
```

Why this fixed it: the generic rewrite was changing both sides of the inequality, including the `sublist` already present on the left. Rewriting only the right-hand full-list occurrence preserved the intended prefix-vs-full comparison and let the arithmetic finish.

Final Result: Success
## 2026-06-05 01:42:30 +0800

Phenomenon: runner audit replay still failed in this retry round before any manual proof theorem, with the same duplicate short-name strategy import class reported in `logs/audit_check_coqc.log`:

```text
File ".../coq/generated/array_sum_positive_goal.v", line 21, characters 0-39:
Error: Required library int_array_strategy_goal matches several files in path
```

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_012416v_array_sum_positive/coq/generated/array_sum_positive_goal.v`, imports `int_array_strategy_goal`, `int_array_strategy_proof`, `uint_array_strategy_goal`, `uint_array_strategy_proof`, `undef_uint_array_strategy_goal`, `undef_uint_array_strategy_proof`, `array_shape_strategy_goal`, and `array_shape_strategy_proof` by short name.

Repair action: add the eight corresponding wrapper modules under `/home/yangfp/CAV/C/CAV/output/verify_20260605_012416v_array_sum_positive/original/`, each pinning the short name to `SimpleC.EE.QCP_demos_LLM`. Goal wrappers use `Require Export`; proof wrappers use `Require Import` plus `Include`. Then replay compile in `QualifiedCProgramming/SeparationLogic` with `-Q "$ORIG" ""` before compiling `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.

Why this fixed it: the audit compiler did not have a unique physical file for those short names because both `QCP_demos_LLM` and `QCP_demos_human` export them under `examples/`. Putting the wrappers in `original/` makes the short names resolve deterministically through the task-local `-Q "$ORIG" ""` path without modifying generated VCs or shared libraries. This supersedes the earlier `coq/deps/` workaround note; the durable replay fix for this workspace is the `original/` wrapper set.

Final Result: Success
