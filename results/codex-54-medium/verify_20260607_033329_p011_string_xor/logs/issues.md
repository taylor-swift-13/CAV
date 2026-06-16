## 2026-06-07 goal_check duplicate-label blocker

- Gate: `coqc p011_string_xor_goal_check.v`
- Location: `/home/yangfp/CAV/C/CAV/output/verify_20260607_033329_p011_string_xor/coq/generated/p011_string_xor_goal_check.v:6`
- Error:
  `Error: The label proof_of_p011_string_xor_safety_wit_1 is already declared.`
- Reproduction command context: compile order `p011_string_xor_goal.v` -> `p011_string_xor_proof_auto.v` -> `p011_string_xor_proof_manual.v` succeeds, then `p011_string_xor_goal_check.v` fails on `Include p011_string_xor_proof_auto`.
- Diagnosis:
  `p011_string_xor_goal_check.v` and `p011_string_xor_proof_auto.v` are generated files. The failing collision is inside generated integration code, not inside the annotated C or manual proof. Reducing `p011_string_xor_proof_manual.v` to an empty companion module does not remove the collision. A stock example (`QualifiedCProgramming/SeparationLogic/examples/QCP_demos_human/sum_goal_check.v`) compiles, so this is specific to the generated files for this target/output namespace.
- Workspace files involved:
  `/home/yangfp/CAV/C/CAV/annotated/verify_20260607_033329_p011_string_xor.c`
  `/home/yangfp/CAV/C/CAV/output/verify_20260607_033329_p011_string_xor/coq/generated/p011_string_xor_goal.v`
  `/home/yangfp/CAV/C/CAV/output/verify_20260607_033329_p011_string_xor/coq/generated/p011_string_xor_proof_auto.v`
  `/home/yangfp/CAV/C/CAV/output/verify_20260607_033329_p011_string_xor/coq/generated/p011_string_xor_proof_manual.v`
  `/home/yangfp/CAV/C/CAV/output/verify_20260607_033329_p011_string_xor/coq/generated/p011_string_xor_goal_check.v`
- Why blocked:
  The repository write boundary and skill rules forbid editing `*_goal.v`, `*_proof_auto.v`, and `*_goal_check.v`. The remaining failing gate depends on one of those generated files changing.

## 2026-06-07 retry-3 manual entail proof blow-up after symexec refresh

- Gate: `coqc p011_string_xor_proof_manual.v`
- Current workspace state:
  Symexec succeeds on `/home/yangfp/CAV/C/CAV/annotated/verify_20260607_033329_p011_string_xor.c` after shrinking the loop invariant/post-loop assert to remove `a@pre`/`b@pre` and most duplicated preserved pure facts, while keeping `n1 == na` and `n2 == nb` for local-resource reclamation.
- Concrete blocker:
  Under the explicit workspace load-path compile, `coqc -time` consistently stalls in `proof_of_p011_string_xor_entail_wit_1_1` after `pre_process; subst; destruct ...; right; exists l.` The next tactic `split_pure_spatial` does not finish in reasonable time even after the witness reduction.
- What was repaired first:
  The over-trimmed invariant initially caused symexec failures:
  `Error: Fail to Remove Memory Permission of n2 ...` at line 103, then `Assign Exec fail` at `output[n] = 0` on line 94. Restoring only `n1 == na`, `n2 == nb`, and `0 <= na/nb < INT_MAX` fixed those and yielded a successful refreshed symexec.
- Useful current artifacts:
  `/home/yangfp/CAV/C/CAV/output/verify_20260607_033329_p011_string_xor/coq/generated/p011_string_xor_goal.v`
  `/home/yangfp/CAV/C/CAV/output/verify_20260607_033329_p011_string_xor/coq/generated/p011_string_xor_proof_manual.v`
  `/home/yangfp/CAV/C/CAV/output/verify_20260607_033329_p011_string_xor/coq/last/p011_string_xor_proof_manual.v`
- Next concrete step:
  Keep the current annotated C, stay on the refreshed generated files, and replace `split_pure_spatial` in `proof_of_p011_string_xor_entail_wit_1_1` with a more explicit derivation for `EX buf_l, pure && spatial` under the smaller witness shape. If that works, propagate the same style to `entail_wit_1_2`, then `entail_wit_2_*`, then the return witnesses.

## 2026-06-07 retry-4 manual proof placeholders removed, but coqc still times out

- Gate: `coqc p011_string_xor_proof_manual.v`
- File: `/home/yangfp/CAV/C/CAV/output/verify_20260607_033329_p011_string_xor/coq/generated/p011_string_xor_proof_manual.v`
- What changed:
  Replaced the previous `Admitted` blocks in `proof_of_p011_string_xor_entail_wit_{2_1,2_2,2_3,2_4}` and `proof_of_p011_string_xor_return_wit_{1,2}` with explicit proofs. `rg -n "Admitted|admit|Abort|Axiom"` on `proof_manual.v` now finds no proof placeholders.
- Current failing behavior:
  With the workspace load-paths, `timeout 130s coqc ... p011_string_xor_proof_manual.v` exits `124` with no later theorem error. A `coqc -time` run shows the compile still spends its budget in the early entry witness area before reporting anything beyond the first lemmas.
- Precise hotspot:
  Interactive `coqtop` runs confirm the proof search blow-up is still centered on `proof_of_p011_string_xor_entail_wit_1_1` (and by symmetry likely `1_2`), specifically around turning the branch-selected witness `exists l` into the mixed pure/spatial postcondition. Lightweight rewrites using `entailer!` reduce quickly but leave unresolved subgoals; reverting to the known-correct `split_pure_spatial` script restores correctness but not performance.
- Reproduction commands used:
  `timeout 40s coqc -time ... p011_string_xor_proof_manual.v`
  `timeout 130s coqc ... p011_string_xor_proof_manual.v`
  both under the workspace-specific `-Q generated SimpleC.EE.CAV.verify_20260607_033329_p011_string_xor` plus the standard SeparationLogic `-R` paths.
- Next concrete step:
  Rewrite `proof_of_p011_string_xor_entail_wit_1_1` and `proof_of_p011_string_xor_entail_wit_1_2` into a lower-level explicit entailment proof that avoids `split_pure_spatial` on the branch-selected `EX buf_l, pure && spatial` goal; only after that is stable should the whole-file compile be retried.

## 2026-06-07 retry-5 entry witness proof-shape blocker after timeout reduction

- Gate: `coqc p011_string_xor_proof_manual.v`
- File: `/home/yangfp/CAV/C/CAV/output/verify_20260607_033329_p011_string_xor/coq/generated/p011_string_xor_proof_manual.v`
- Current theorem/blocker:
  `proof_of_p011_string_xor_entail_wit_1_1` is still the first failing/timeout hotspot. The local edits also apply to `proof_of_p011_string_xor_entail_wit_1_2`, which has the same shape.
- What was repaired:
  Moving `prop_apply (CharArray.full_Zlength ...)` ahead of branch selection removes the previous `No matching clauses for match` failure, and replacing the old script removes the 45s blind timeout. `coqc -time` now reaches the first branch of `proof_of_p011_string_xor_entail_wit_1_1` and reports the structural proof mismatch instead of hanging earlier.
- Precise remaining problem:
  After choosing the disjunction branch and buffer witness, the goal no longer behaves like a top-level entailment that `split_pure_spatial` or `split_pure_and_spatial_goals` can cheaply decompose. Interactive checks show the proof quickly reduces to a model-level obligation of the form
  `exists buf_l, (pure && spatial) m`
  with witness `l` and pure fact `Hlen : Zlength l = ...`, but:
  1. `split_pure_spatial` still times out when run before that reduction,
  2. `apply split_pure_and_spatial_goals` does not unify once the goal is already at model level,
  3. `entailer!` reaches the model-level conjunction quickly, but does not finish the remaining pure/spatial reconstruction automatically.
- Concrete failing context:
  `timeout 45s coqc -time ... p011_string_xor_proof_manual.v` stops after:
  `pre_process; subst; prop_apply ...; Intros_p Hlen; destruct ...; right; exists l`
  and the direct `apply split_pure_and_spatial_goals` attempt errors at line 31 with an inability to unify
  `forall m, P m -> (pure && spatial) m`
  against the already-reduced model-level conjunction.
- Useful reproduction:
  An interactive `coqtop` run under the workspace load-paths on `Goal p011_string_xor_entail_wit_1_2.` confirms:
  `entailer!` reduces immediately to one model-level `EX buf_l, pure && spatial` goal with witness `l` and `Hlen`,
  but neither `entailer!` nor direct `split`/`cancel` closes the residual conjunction without additional low-level assertion lemmas.
- Next concrete correction needed:
  Rebuild `proof_of_p011_string_xor_entail_wit_{1_1,1_2}` with the right low-level assertion combinators for a model-level `EX ... (pure && spatial)` goal, or adjust the annotation/invariant again so the initial entry witness no longer requires constructing this mixed whole-buffer assertion directly.

## External Codex Failure

- Stage: `external-agent-run`
- Exit code: `124`
- Stderr log: `/home/yangfp/CAV/C/CAV/output/verify_20260607_033329_p011_string_xor/logs/agent_stderr_20260607_052630.log`
- Detail: `external agent run exceeded remaining timeout budget of 418 seconds`
