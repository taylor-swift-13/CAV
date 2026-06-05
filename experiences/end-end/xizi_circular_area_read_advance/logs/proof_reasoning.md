[2026-06-02 19:40:26+08:00] First proof attempt
Phenomenon: In proof-only mode, the only writable proof file is output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/generated/xizi_circular_area_read_advance_proof_manual.v, which currently contains two Admitted lemmas: proof_of_xizi_circular_area_read_advance_return_wit_1 and proof_of_xizi_circular_area_read_advance_return_wit_2.
Location: output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/generated/xizi_circular_area_read_advance_proof_manual.v; theorems xizi_circular_area_read_advance_return_wit_1 and xizi_circular_area_read_advance_return_wit_2 from xizi_circular_area_read_advance_goal.v.
Repair action: Start with the proof README try-first skeleton for straight-line scalar entailments: use pre_process; entailer!, then discharge the remaining arithmetic with Z.mod_pos_bound and lia. For return_wit_1, also normalize data_length_pre - (area_length_pre - readidx_pre) into readidx_pre + data_length_pre - area_length_pre and prove it is the branch-specific modulo result under area_length_pre < readidx_pre + data_length_pre < 2 * area_length_pre.
Key proof shape: The generated VC is pure arithmetic with emp on both sides, so no annotation or contract edits are allowed or needed in proof-only mode.
Why this change: The contract already states 0 < area_length_pre, 0 <= readidx_pre < area_length_pre, and 0 <= data_length_pre <= area_length_pre. That is enough to prove the modulo range facts and the branch equality for the two returns if the proof script explicitly exposes the arithmetic facts.
[2026-06-02 19:40:26+08:00] Compile iteration 1
Phenomenon: coqc on output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/generated/xizi_circular_area_read_advance_proof_manual.v failed at line 32 with `Tactic failure: Cannot find witness.` The subsequent goal_check failure is only a load-path consequence because proof_manual.vo was not produced.
Location: theorem proof_of_xizi_circular_area_read_advance_return_wit_1, line 32 (`entailer!`).
Repair action: Inspect the exact proof state for return_wit_1 before changing tactics again. The current script likely asks `entailer!` to synthesize the modulo equality witness too early, while the branch-specific arithmetic normalization has not been exposed in a shape the tactic can consume.
Key error text: `Error: Tactic failure: Cannot find witness.`
Why this change: The proof README explicitly warns that `Cannot find witness` often means a missing explicit arithmetic bridge, not that the VC is impossible. I need the concrete subgoal shape before choosing between `assert`, `Exists`, or direct `Z.mod_*` rewriting.
[2026-06-02 19:40:26+08:00] Proof-state inspection for return_wit_1
Phenomenon: After `pre_process`, the return_wit_1 VC reduces to a single pure arithmetic goal: `readidx_pre + data_length_pre - area_length_pre = (readidx_pre + data_length_pre) % area_length_pre` under `readidx_pre + data_length_pre > area_length_pre`, `0 < area_length_pre`, `0 <= readidx_pre < area_length_pre`, and `0 <= data_length_pre <= area_length_pre`.
Location: coqtop probe of theorem xizi_circular_area_read_advance_return_wit_1 after `entailer!`.
Repair action: Replace the failed `rewrite Z.mod_unique ...` step with a direct modulo-characterization proof: prove the remainder range `0 <= readidx_pre + data_length_pre - area_length_pre < area_length_pre`, rewrite the dividend as `area_length_pre * 1 + (readidx_pre + data_length_pre - area_length_pre)`, and apply `Z.mod_unique` under symmetry.
Key proof state:
`readidx_pre + data_length_pre - area_length_pre = (readidx_pre + data_length_pre) % area_length_pre`
Why this change: The previous script asked Coq to rewrite in a direction that did not match the theorem statement of `Z.mod_unique`. The inspected goal matches the theorem exactly after taking symmetry and providing the explicit remainder side conditions.
[2026-06-02 19:40:26+08:00] Compile iteration 2
Phenomenon: coqc now fails at line 29 in proof_of_xizi_circular_area_read_advance_return_wit_1 with an explicit unification mismatch: `Z.mod_unique` concludes `r = a mod b`, while the edited script first flipped the goal with `symmetry`, producing `a mod b = r`.
Location: output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/generated/xizi_circular_area_read_advance_proof_manual.v line 29.
Repair action: Remove the `symmetry` step and apply `Z.mod_unique` directly to the original goal `readidx_pre + data_length_pre - area_length_pre = (readidx_pre + data_length_pre) % area_length_pre`.
Key error text: `Unable to unify "?M5462 = ?M5459 mod ?M5460" with "(readidx_pre + data_length_pre) % area_length_pre = readidx_pre + data_length_pre - area_length_pre"`.
Why this change: The proof state already had exactly the theorem conclusion shape before symmetry. The theorem itself was fine; only the orientation was wrong.
[2026-06-02 19:40:26+08:00] Compile iteration 3
Phenomenon: The proof still fails in return_wit_1, but now the error is a raw unification failure while applying `Z.mod_unique`; the goal itself is unchanged and still matches the modulo characterization semantically.
Location: output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/generated/xizi_circular_area_read_advance_proof_manual.v line 28.
Repair action: Instantiate all `Z.mod_unique` arguments explicitly (`a`, `b`, `q`, `r`) instead of relying on `apply ... with (q := 1)` inference.
Key error text: `Unable to unify "?M5458 = ?M5455 mod ?M5456" with "readidx_pre + data_length_pre - area_length_pre = (readidx_pre + data_length_pre) % area_length_pre"`.
Why this change: The remaining problem is theorem application shape, not proof content. Explicit instantiation is the conservative proof style recommended by the proof guide when inference is brittle.
[2026-06-02 19:40:26+08:00] Compile iteration 4
Phenomenon: coqc rejects the named argument form for `Z.mod_unique` with `Wrong argument name r.` The theorem itself is still the right one; only the application syntax is wrong in this Coq environment.
Location: output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/generated/xizi_circular_area_read_advance_proof_manual.v line 32.
Repair action: Apply `Z.mod_unique` positionally instead of by named arguments.
Key error text: `Wrong argument name r.`
Why this change: The proof guide favors conservative scripts. Positional application avoids version-sensitive binder-name issues while keeping the same arithmetic argument.
[2026-06-02 19:40:26+08:00] Compile iteration 5
Phenomenon: The remaining failure is a notation-level unification mismatch between the goal term `(readidx_pre + data_length_pre) % area_length_pre` and the theorem conclusion `(readidx_pre + data_length_pre) mod area_length_pre`.
Location: output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/generated/xizi_circular_area_read_advance_proof_manual.v line 28.
Repair action: Insert an explicit `change` to normalize the `%` notation into `Z.modulo` before applying `Z.mod_unique`.
Key error text: `Unable to unify ... mod ... with ... % ...`.
Why this change: The arithmetic content is already correct; Coq just needs the target term presented in the same head symbol as the theorem conclusion.
[2026-06-02 19:40:26+08:00] Compile iteration 6
Phenomenon: The explicit `% ... %Z` normalization was parsed as a scope delimiter instead of a modulo term, producing `Unknown scope delimiting key area_length_pre`.
Location: output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/generated/xizi_circular_area_read_advance_proof_manual.v line 28.
Repair action: Normalize the whole equality target with an explicit `Z.modulo` term instead of embedding `%` notation inside `change`.
Key error text: `Unknown scope delimiting key area_length_pre`.
Why this change: The issue is purely parser-level. Using `Z.modulo` directly removes scope ambiguity and should leave the arithmetic proof unchanged.
[2026-06-02 19:40:26+08:00] Proof-state inspection for modulo notation
Phenomenon: `Set Printing All` reveals that the generated `%` in this workspace is `Z.rem`, not `Z.modulo`. The return_wit_1 post-entailer goal prints as `@eq Z (Z.sub ...) (Z.rem ...)`.
Location: coqtop probe of theorem xizi_circular_area_read_advance_return_wit_1 after `entailer!`.
Repair action: Replace the `Z.mod_unique` attempt with `Z.rem_unique`, and use `Z.rem_bound_pos` instead of `Z.mod_pos_bound` in return_wit_2.
Key proof state: `@eq Z (Z.sub (Z.add readidx_pre data_length_pre) area_length_pre) (Z.rem (Z.add readidx_pre data_length_pre) area_length_pre)`.
Why this change: The earlier failures were caused by targeting the wrong arithmetic operator. The branch proof is straightforward once it is stated against `Z.rem`.
[2026-06-02 19:40:26+08:00] Compile iteration 7
Phenomenon: coqc now reaches the end of proof_of_xizi_circular_area_read_advance_return_wit_2 and fails with `Attempt to save an incomplete proof`, which means return_wit_1 is discharged and only return_wit_2 still has unresolved arithmetic goals.
Location: output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/generated/xizi_circular_area_read_advance_proof_manual.v line 44.
Repair action: Inspect the post-`entailer!` proof state for return_wit_2 and close the remaining range goal explicitly, likely with `Z.rem_bound_pos` or `Z.rem_small` depending on the exact residual target.
Key error text: `Attempt to save an incomplete proof (there are remaining open goals).`
Why this change: This is no longer a theorem-selection problem. The remaining work is to match the exact arithmetic goal shape left by `entailer!` in the non-wrap branch.
[2026-06-02 19:40:26+08:00] Proof-state inspection for return_wit_2
Phenomenon: After `entailer!`, return_wit_2 leaves exactly two pure goals: `0 <= (readidx_pre + data_length_pre) % area_length_pre` and `(readidx_pre + data_length_pre) % area_length_pre < area_length_pre`.
Location: coqtop probe of theorem xizi_circular_area_read_advance_return_wit_2 after `entailer!`.
Repair action: Explicitly derive `0 <= readidx_pre + data_length_pre`, specialize `Z.rem_bound_pos` with that fact and `0 < area_length_pre`, then discharge both residual goals with `lia`.
Key proof state: two goals for the lower and upper bounds of `Z.rem`.
Why this change: The theorem choice was already correct. The missing step was to feed its premises to obtain the concrete bound pair that `lia` can use.
[2026-06-02 19:40:26+08:00] Compile iteration 8
Phenomenon: return_wit_2 still ends with open goals even after specializing `Z.rem_bound_pos`, which indicates the bound fact was introduced only in the currently focused subgoal, not in both subgoals created by `entailer!`.
Location: output/verify_20260602_194026v_xizi_circular_area_read_advance/coq/generated/xizi_circular_area_read_advance_proof_manual.v line 46.
Repair action: Move the arithmetic setup (`0 <= readidx_pre + data_length_pre` and `Hmod : 0 <= Z.rem ... < area_length_pre`) before `entailer!`, so the fact is inherited by both residual pure goals.
Key error text: `Attempt to save an incomplete proof (there are remaining open goals).`
Why this change: This is a goal-sharing issue, not a math issue. Facts established before `entailer!` persist across all subgoals that it generates.
