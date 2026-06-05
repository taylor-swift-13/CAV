2026-06-03 Round 1

Phenomenon: `coq/generated/xizi_fifo_timeslice_init_proof_manual.v` contains exactly one manual theorem, `proof_of_xizi_fifo_timeslice_init_return_wit_1`, and it is still `Admitted`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_181352v_xizi_fifo_timeslice_init/coq/generated/xizi_fifo_timeslice_init_proof_manual.v`, theorem `proof_of_xizi_fifo_timeslice_init_return_wit_1`.

Fix action: Prove the return witness by choosing `l0 = replace_Znth 1 0 (replace_Znth 0 0 l)` so the spatial goal `IntArray.full state_pre 2 l0` cancels directly, then discharge the pure obligations with `Zlength_replace_Znth` and `Znth_replace_Znth_Same`.

Key proof sketch:

```coq
pre_process.
Exists (replace_Znth 1 0 (replace_Znth 0 0 l)).
entailer!.
```

Why this change: In proof-only mode the generated VC and annotated C are fixed, so the stable path is to reuse the exact list already present on the left-hand side of the entailment instead of inventing `[0; 0]` and proving extensional equality.

2026-06-03 Round 2

Phenomenon: The required compile replay failed before reaching the manual theorem because `xizi_fifo_timeslice_init_goal.v` imports bare strategy modules such as `int_array_strategy_goal`, but this environment has no precompiled strategy `.vo` files on the default load path.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_181352v_xizi_fifo_timeslice_init/coq/generated/xizi_fifo_timeslice_init_goal.v`, import block around `Require Import int_array_strategy_goal.`; compile gate `coqc ... xizi_fifo_timeslice_init_goal.v`.

Fix action: Stage workspace-local copies of the four strategy goal/proof pairs under `coq/deps/`, then normalize each copied `*_strategy_proof.v` import from `From SimpleC.EE.QCP_demos_human Require Import ...` to bare `Require Import ...` so the generated older-format file and the local dependency copies share the same namespace.

Key compile blocker:

```text
Error: Cannot find a physical path bound to logical path int_array_strategy_goal.
```

Why this change: The blocker is a workspace-local dependency gap rather than a contract or VC defect. Keeping the shim inside `coq/deps/` preserves the generated files and allows the mandated compile replay to proceed without editing `goal.v`, `proof_auto.v`, or `goal_check.v`.

2026-06-03 Round 3

Phenomenon: `coqc` reached `proof_manual.v` but failed on the first bullet because after `entailer!` the generated subgoal order is `Znth 1`, `Znth 0`, `Zlength`, not `Zlength` first. The previous script tried `rewrite Zlength_replace_Znth` while the focused goal was a `Znth` equation.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_181352v_xizi_fifo_timeslice_init/coq/generated/xizi_fifo_timeslice_init_proof_manual.v:27`, theorem `proof_of_xizi_fifo_timeslice_init_return_wit_1`.

Fix action: Reorder the bullets to match the actual proof state. For the `Znth 0` branch, use `Znth_replace_Znth_Diff` on the outer replacement followed by `Znth_replace_Znth_Same` on the inner replacement; keep the final length branch as two `Zlength_replace_Znth` rewrites ending with `exact H`.

Key proof-state excerpt after `entailer!`:

```coq
1. Znth 1 (replace_Znth 1 0 (replace_Znth 0 0 l)) 0 = 0
2. Znth 0 (replace_Znth 1 0 (replace_Znth 0 0 l)) 0 = 0
3. Zlength (replace_Znth 1 0 (replace_Znth 0 0 l)) = 2
```

Why this change: This theorem does not need stronger automation; it only needs the proof script to follow the generated subgoal order and make the outer-vs-inner `replace_Znth` distinction explicit.

2026-06-03 Round 4

Phenomenon: The second compile attempt still failed in the `Znth 0` branch because after rewriting the outer update with `Znth_replace_Znth_Diff`, the inner `Znth_replace_Znth_Same` side condition is stated over `l` directly, not over another `replace_Znth` term.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_181352v_xizi_fifo_timeslice_init/coq/generated/xizi_fifo_timeslice_init_proof_manual.v:37`, theorem `proof_of_xizi_fifo_timeslice_init_return_wit_1`.

Fix action: Remove the extra `rewrite Zlength_replace_Znth` under the inner `Same` side-condition proof and close that side condition with `lia` from `H : Zlength l = 2`.

Key failure:

```text
Error: Found no subterm matching
"Zlength (replace_Znth ...)" in the current goal.
```

Why this change: Once the outer replacement is discharged as a different index, only the original list length matters. Keeping the side-condition proof on `l` avoids rewriting a term that is no longer present.
