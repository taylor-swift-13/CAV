2026-06-05 08:xx symexec blocker

Phenomenon: `symexec` failed with `Cannot derive the precondition of Memory Read.` at [annotated/verify_20260605_080838v_ex_hamming_distance.c:42](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_080838v_ex_hamming_distance.c:42), the `b[i]` read in `if (a[i] != b[i])`.

Location: loop body of `ex_hamming_distance`.

Fix: strengthened the loop invariant with concrete arithmetic equal-length facts:
```c
i <= nb &&
na == nb &&
```
This let symbolic execution carry the second-string bound directly instead of relying on unfolding `ex_hamming_distance_pre`.

Result: rerunning `symexec` succeeded and regenerated fresh `goal/proof_auto/proof_manual/goal_check` files.

2026-06-05 08:xx replay compile blocker

Phenomenon: compiling [coq/generated/ex_hamming_distance_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080838v_ex_hamming_distance/coq/generated/ex_hamming_distance_goal.v) failed with:
```text
Required library char_array_strategy_goal matches several files in path
```

Location: short-name imports `char_array_strategy_goal` and `char_array_strategy_proof` in generated Coq files.

Fix: added workspace-local generated wrappers:
- [char_array_strategy_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080838v_ex_hamming_distance/coq/generated/char_array_strategy_goal.v)
- [char_array_strategy_proof.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080838v_ex_hamming_distance/coq/generated/char_array_strategy_proof.v)

These export the `SimpleC.EE.QCP_demos_LLM` strategy modules without editing the generated VC text.

Result: replay compilation of `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` succeeded.

2026-06-05 08:xx manual proof blockers

Phenomenon: the generated [ex_hamming_distance_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080838v_ex_hamming_distance/coq/generated/ex_hamming_distance_proof_manual.v) started with five `Admitted` lemmas and several compile failures while replacing them.

Location: manual witnesses `safety_wit_5`, `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, and `return_wit_1`.

Fixes:
- added local helper lemmas for spec bounds, prefix-extension by one element, and locating the terminator in `l ++ 0 :: nil`
- normalized QCP library names from assumed `Znth_app1/Znth_app2` to the actual `app_Znth1/app_Znth2`
- split `entailer!` results into explicit arithmetic subgoals so the successor bounds `i + 1 <= na/nb` were proved separately from the semantic step witness
- rewrote the return witness through `i = na`, `sublist 0 na la = la`, and `sublist 0 na lb = lb`

Result: `proof_manual.v` compiles with no `Admitted`, `admit`, `Abort`, or added `Axiom`.

2026-06-05 08:xx retry audit replay blocker

Phenomenon: runner attempt 2 reported `audit_check_coqc_failed` and `audit_check_coqc.log` showed bare replay of [coq/generated/ex_hamming_distance_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080838v_ex_hamming_distance/coq/generated/ex_hamming_distance_goal.v) failing at `Require Import char_array_strategy_goal.` with:
```text
Required library char_array_strategy_goal matches several files in path
```

Location: generated short-name strategy import, with duplicate shared libraries under `QualifiedCProgramming/SeparationLogic/examples/QCP_demos_LLM/` and `.../QCP_demos_human/`.

Repair action: keep the workspace-local sibling wrappers in `coq/generated/` and explicitly replay-compile them before the generated VC files:
- [char_array_strategy_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080838v_ex_hamming_distance/coq/generated/char_array_strategy_goal.v)
- [char_array_strategy_proof.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080838v_ex_hamming_distance/coq/generated/char_array_strategy_proof.v)

Key replay sequence:
```text
coqc ... original/ex_hamming_distance.v
coqc ... coq/generated/char_array_strategy_goal.v
coqc ... coq/generated/char_array_strategy_proof.v
coqc ... coq/generated/ex_hamming_distance_goal.v
coqc ... coq/generated/ex_hamming_distance_proof_auto.v
coqc ... coq/generated/ex_hamming_distance_proof_manual.v
coqc ... coq/generated/ex_hamming_distance_goal_check.v
```

Why this works: the generated wrappers provide a unique local short-name resolution for the conflicting strategy modules without editing `goal.v` or shared example trees. The wrappers must remain precompiled as `.vo` files because this duplicate-path case is a replay-path dependency, not an ordinary disposable compile artifact.
