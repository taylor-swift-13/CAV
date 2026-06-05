## 2026-06-03 Round 1

Phenomenon: `coq/generated/xizi_rr_timeslice_init_proof_manual.v` contains exactly one manual theorem, `proof_of_xizi_rr_timeslice_init_return_wit_1`, still left as `Admitted`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_183100v_xizi_rr_timeslice_init/coq/generated/xizi_rr_timeslice_init_goal.v`, definition `xizi_rr_timeslice_init_return_wit_1`.

Repair action: Use the concrete post-state list `replace_Znth 1 10 (replace_Znth 0 10 l)` as the existential witness, then discharge the three pure goals by rewriting `Zlength_replace_Znth` and `Znth_replace_Znth` under the contract fact `Zlength l = 2`.

Key proof fragment:

```coq
pre_process.
Exists (replace_Znth 1 10 (replace_Znth 0 10 l)).
entailer!.
```

Why this change: the spatial postcondition already matches `IntArray.full state_pre 2 l0`, so the only real work is to expose the exact list written by the two stores and prove it has length 2 with indices 0 and 1 both equal to 10.

## 2026-06-03 Round 2

Phenomenon: full Coq replay stopped before the manual theorem was checked. `coqc` failed while compiling `coq/generated/xizi_rr_timeslice_init_goal.v`, so `proof_manual.v` and `goal_check.v` could not be validated.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_183100v_xizi_rr_timeslice_init/coq/generated/xizi_rr_timeslice_init_goal.v:20`, on `Require Import int_array_strategy_goal`.

Repair action attempted: retried compilation from `QualifiedCProgramming/SeparationLogic` with the standard base `-R` flags and then with extra `-Q examples/QCP_demos_human ""` and `-Q examples/QCP_demos_LLM ""` mappings to satisfy the unqualified strategy imports.

Key compiler error:

```text
File ".../xizi_rr_timeslice_init_goal.v", line 20, characters 15-38:
Error: Cannot find a physical path bound to logical path
int_array_strategy_goal.
```

Why this blocks verification: the workspace has only the strategy source `.v` files under `SeparationLogic/examples/...` and no corresponding compiled `.vo/.vos/.vio` artifacts. In proof-only mode I cannot rewrite generated imports or create a fallback `coq/deps/`, so the compile gate fails for an external environment reason before the manual witness can be machine-checked.

## 2026-06-03 Round 3

Phenomenon: the retry audit disproved the previous environment diagnosis. `logs/audit_check_coqc.log` shows all dependency and generated files up to `proof_manual.v` already compile, and the first stable error is now inside the manual theorem itself:

```text
File ".../xizi_rr_timeslice_init_proof_manual.v", line 27, characters 4-32:
Error: Found no subterm matching
"Zlength (replace_Znth ?M4086 ?M4087 ?M4085)" in the current goal.
```

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_183100v_xizi_rr_timeslice_init/coq/generated/xizi_rr_timeslice_init_proof_manual.v`, theorem `proof_of_xizi_rr_timeslice_init_return_wit_1`.

Repair action: keep the same existential witness `replace_Znth 1 10 (replace_Znth 0 10 l)`, but replace the generic rewrite script with the nested-`replace_Znth` pattern from `experiences/general/PROOF/README.md §31`: normalize length facts with `repeat rewrite Zlength_replace_Znth in *`, then prove the two index equalities by explicitly traversing the outer `replace_Znth 1 10 (...)` and inner `replace_Znth 0 10 l` layers using `Znth_replace_Znth_diff` and `Znth_replace_Znth_same` with full list arguments.

Key intended proof fragment:

```coq
repeat rewrite Zlength_replace_Znth in *.
rewrite (Znth_replace_Znth_diff 0 1 10 0 (replace_Znth 0 10 l))
  by (rewrite ?Zlength_replace_Znth in *; lia).
rewrite (Znth_replace_Znth_same 0 10 0 l) by lia.
```

Why this change: the witness is semantically right, but `rewrite Zlength_replace_Znth` after `entailer!` is too weak because the current goal is not syntactically headed by that exact subterm. The failure matches the documented nested-update symptom, so the stable fix is to make each rewrite target explicit instead of relying on Coq inference.

## 2026-06-03 Round 4

Phenomenon: after switching to the documented deps-based compile command from `QualifiedCProgramming/SeparationLogic`, `goal.v` and `proof_auto.v` compiled, but `proof_manual.v` still failed once with `The variable Znth_replace_Znth_same was not found in the current environment.` A quick `Search replace_Znth.` in the same load-path showed that this environment exports the capitalized lemmas `Znth_replace_Znth_Same` and `Znth_replace_Znth_Diff`, not the lowercase names used in the previous patch.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_183100v_xizi_rr_timeslice_init/coq/generated/xizi_rr_timeslice_init_proof_manual.v:27-31`, theorem `proof_of_xizi_rr_timeslice_init_return_wit_1`.

Repair action: replaced the lowercase lemma calls with `Znth_replace_Znth_Same` / `Znth_replace_Znth_Diff`, using the actual library argument order `(default, list, index, value)`, and kept the explicit nested-list rewrites. I also reordered the three bullets to match the true `entailer!` goal order observed in `coqtop`: first `Znth 1`, then `Znth 0`, then `Zlength`.

Key final proof fragment:

```coq
+ rewrite (Znth_replace_Znth_Same 0 (replace_Znth 0 10 l) 1 10)
    by (rewrite ?Zlength_replace_Znth in *; lia).
+ rewrite (Znth_replace_Znth_Diff 0 (replace_Znth 0 10 l) 1 0 10)
    by (rewrite ?Zlength_replace_Znth in *; lia).
  rewrite (Znth_replace_Znth_Same 0 l 0 10) by lia.
+ repeat rewrite Zlength_replace_Znth in *; lia.
```

Why this change: the witness itself was already correct; the remaining instability came from two proof-engineering details only: matching the exported lemma names from `ListLib`, and matching the post-`entailer!` subgoal order exactly. After those adjustments, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compiled successfully under the deps fallback load-path.
