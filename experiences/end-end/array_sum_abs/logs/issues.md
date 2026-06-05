2026-06-05T00:00:00+08:00

Issue 1
Symptom: the first `symexec` run failed with `Error: Lack of assertions in some paths for the loop!` at [verify_20260605_005812v_array_sum_abs.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_005812v_array_sum_abs.c:30).
Location: `while (i < n)` in [verify_20260605_005812v_array_sum_abs.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_005812v_array_sum_abs.c:30).
Fix action: added a loop `Inv Assert` carrying `a == a@pre`, `n == n@pre`, `0 <= i <= n`, `sum == sum_abs(sublist(0, i, l))`, preserved contract facts, and `IntArray::full(a, n, l)`.
Key snippet:
```c
sum == sum_abs(sublist(0, i, l)) &&
IntArray::full(a, n, l)
```
Why this fixed it: the loop head now records the processed-prefix summary required both for the accumulator and for preserving the read-only array heap across iterations, so `symexec` could regenerate aligned VCs.

Issue 2
Symptom: the first compile replay failed in [array_sum_abs_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/coq/generated/array_sum_abs_goal.v:21) with `Required library int_array_strategy_goal matches several files in path`.
Location: short-name strategy imports generated into [array_sum_abs_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/coq/generated/array_sum_abs_goal.v:21) and reused by the other generated Coq files.
Fix action: added local wrapper modules in `output/verify_20260605_005812v_array_sum_abs/coq/deps/` for `int_array`, `uint_array`, `undef_uint_array`, and `array_shape` goal/proof pairs, each redirecting the short name to `SimpleC.EE.QCP_demos_LLM`.
Key snippet:
```coq
From SimpleC.EE.QCP_demos_LLM Require Export int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.int_array_strategy_proof.
```
Why this fixed it: `coqc` now sees exactly one physical module for each generated short-name import without modifying `goal.v`, `proof_auto.v`, or `goal_check.v`.

Issue 3
Symptom: [array_sum_abs_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/coq/generated/array_sum_abs_proof_manual.v:117) initially contained seven admitted witnesses, and several first-draft proofs failed because list decompositions and goal ordering were underspecified.
Location: `proof_of_array_sum_abs_safety_wit_4`, `proof_of_array_sum_abs_safety_wit_5`, `proof_of_array_sum_abs_safety_wit_6`, `proof_of_array_sum_abs_entail_wit_2_1`, `proof_of_array_sum_abs_entail_wit_2_2`, and `proof_of_array_sum_abs_return_wit_1` in [array_sum_abs_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/coq/generated/array_sum_abs_proof_manual.v:117).
Fix action: added local helper lemmas `sum_abs_app`, `sum_abs_nonneg`, `sum_abs_prefix_le`, `sum_abs_singleton_nonneg`, `sum_abs_singleton_neg`, `sum_abs_sublist_succ_nonneg`, and `sum_abs_sublist_succ_neg`; then rewrote the manual witnesses to use those lemmas plus explicit bound facts from the contract.
Key snippet:
```coq
assert (Hstep: sum + Znth i l 0 = sum_abs (sublist 0 (i + 1) l)) by
  (rewrite H7; symmetry; apply sum_abs_sublist_succ_nonneg; lia).
```
Why this fixed it: the helper lemmas isolate the exact prefix-extension fact needed by both the safety and entailment VCs, while the witness proofs stop depending on fragile automation or hypothesis-number guesses.

Issue 4
Symptom: intermediate `.aux/.glob/.vo/.vok/.vos` files were produced under `coq/` and `original/` during replay compilation.
Location: `output/verify_20260605_005812v_array_sum_abs/coq/**` and `output/verify_20260605_005812v_array_sum_abs/original/**`.
Fix action: deleted all non-`.v` files under `coq/`, deleted replay byproducts under `original/`, and verified that `input/` contains only `.c`/`.v` files.
Why this fixed it: the workspace now satisfies the verify cleanup requirement while retaining the source `.c`/`.v` artifacts and the generated proof sources.

Issue 5
Symptom: runner audit replay still failed after attempt 1 even though manual proofs were complete, because the duplicate short-name strategy import fix had been recorded against `coq/deps/`, while the replay load path that compiled `array_sum_abs_goal.v` only gave `-Q "$ORIG" ""` and `-R "$GEN" "$LP"`.
Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/logs/audit_check_coqc.log`, first failure at `/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/coq/generated/array_sum_abs_goal.v:21`; corrected files now live in `/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/original/{int_array,uint_array,undef_uint_array,array_shape}_strategy_{goal,proof}.v`.
Fix action: added replay-facing wrappers in `original/` for all four conflicting strategy goal/proof pairs, each exporting or including the `SimpleC.EE.QCP_demos_LLM` module under the short name that generated files import, then reran `coqc` through `goal_check`.
Key snippet:
```coq
From SimpleC.EE.QCP_demos_LLM Require Export int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.int_array_strategy_proof.
```
Why this fixed it: under `-Q "$ORIG" ""`, these wrappers become the unique first match for `Require Import int_array_strategy_goal.` and the other short names, so replay compilation no longer depends on ambiguous duplicates in the shared `examples/` tree.

Issue 6
Symptom: on attempt 3, the workspace still reproduced the same duplicate-library error in `array_sum_abs_goal.v` even though the eight short-name wrapper source files already existed in `original/`.
Location: first failing replay step remained `/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/coq/generated/array_sum_abs_goal.v:21`; diagnostic inspection showed `original/` contained only `.v` wrapper sources and no compiled `.vo` for those short names at replay start.
Fix action: compiled the eight wrapper modules in `/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/original/` first, then replayed `array_sum_abs.v`, `array_sum_abs_goal.v`, `array_sum_abs_proof_auto.v`, `array_sum_abs_proof_manual.v`, and `array_sum_abs_goal_check.v` in order, and finally cleaned all generated non-`.v` byproducts again.
Key snippet:
```text
== coqc int_array_strategy_goal.v ==
...
== coqc array_sum_abs_goal_check.v ==
```
Why this fixed it: the wrappers only disambiguate `Require Import int_array_strategy_goal.` once Coq can resolve them as compiled local modules under `-Q "$ORIG" ""`; merely placing the `.v` sources in `original/` was not sufficient for this replay path.

Issue 7
Symptom: the latest retry started from a stale "success" self-report, but the actual workspace state still matched the runner failure: `audit_check_coqc.log` stopped at `/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/coq/generated/array_sum_abs_goal.v:21` with `Required library int_array_strategy_goal matches several files in path`, and `find original -name '*.vo'` returned empty before replay.
Location: stale success claim in `/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/logs/agent_last_message_20260605_012710.txt`; concrete blocker remained `/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/logs/audit_check_coqc.log` and the missing replay artifacts under `/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/original/`.
Fix action: ignored the stale summary, revalidated the live workspace, recompiled the eight `original/*strategy*.v` wrappers plus `original/array_sum_abs.v` and the four generated Coq files from `QualifiedCProgramming/SeparationLogic` with the documented `-Q "$ORIG" ""` and `-R "$GEN" "$LP"` load path, then deleted the regenerated `.aux/.glob/.vo/.vok/.vos` files under `coq/` and `original/`.
Key snippet:
```text
coqc ... -Q /home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/original '' /home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/original/int_array_strategy_goal.v
...
coqc ... /home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/coq/generated/array_sum_abs_goal_check.v
```
Why this fixed it: verifying the live filesystem rather than trusting the prior message exposed that the needed wrapper compilation had not actually been preserved in the current workspace; replaying the documented compile order repaired the ambiguous-import failure, and the follow-up cleanup restored the required post-compile state.

Issue 8
Symptom: after replay succeeded, `metrics.md` still claimed that `original/` had been fully cleaned to only `.c`/`.v`, but the live replayable workspace required compiled local modules for `array_sum_abs.v` and the short-name strategy wrappers. At the same time, `coq/generated/` still contained fresh `.aux/.glob/.vo/.vok/.vos` byproducts from the successful replay.
Location: inaccurate summary in `/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/logs/metrics.md`; disposable byproducts under `/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/coq/generated/`; replay-critical compiled modules under `/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/original/*.vo`.
Fix action: deleted all non-`.v` files under `coq/`, pruned `original/` down to sources plus the required `.vo` files by removing only `.aux/.glob/.vok/.vos`, reran the documented replay order (`original/array_sum_abs.v -> goal.v -> proof_auto.v -> proof_manual.v -> goal_check.v`) in that cleaned state, and confirmed it still ended with `replay-ok`.
Key snippet:
```text
coq-extra:
orig-extra:
replay-ok
```
Why this fixed it: the workspace now satisfies the verify cleanup rule for `coq/`, preserves the minimal compiled artifacts that the audit replay needs under `-Q "$ORIG" ""`, and the logs describe the actual final filesystem state instead of the stale earlier claim.
