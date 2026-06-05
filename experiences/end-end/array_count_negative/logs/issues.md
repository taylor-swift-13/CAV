# Verification Issues

## Issue 1: workspace fingerprint was still in placeholder state

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`, which violates the verify workflow metadata requirement.
- Localization: `/home/yangfp/CAV/C/CAV/output/verify_20260604_233715v_array_count_negative/logs/workspace_fingerprint.json`.
- Fix action: filled the semantic description for a read-only array scan that counts negative entries and set controlled-vocabulary keywords `{problem_kind: count, data: array, pattern: single_loop}`. After successful replay, also marked `verification_status` as `goal_check_passed`.
- Why this was the right fix: the fingerprint is used for retrieval and audit; leaving it empty would fail the workspace-completeness gate even if the proof succeeded.

## Issue 2: the first symexec run failed because the only loop had no invariant

- Phenomenon: the initial active annotated file matched the input exactly and `symexec` stopped with:

```text
Error: Lack of assertions in some paths for the loop!
```

- Localization: `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_233715v_array_count_negative.c:20`.
- Fix action: added a loop invariant describing the processed prefix and unchanged array state:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      count == array_count_negative_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

and a minimal exit assertion fixing `i == n` and `count == array_count_negative_spec(l)` before `return`.
- Why this fixed the issue: the loop is a pure prefix scan, so the stable semantic state is “accumulator equals spec on the processed prefix”. That is exactly the information missing from the initial bare loop.

## Issue 3: the first invariant edit used the wrong attachment syntax for a `for` loop

- Phenomenon: after the first annotation edit, symexec failed again with:

```text
Expected loop after loop invariant.
```

- Localization: `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_233715v_array_count_negative.c:28`.
- Fix action: moved `int i;` into the enclosing block and placed `/*@ Inv ... */` immediately before the `for` statement, matching the accepted parser pattern for this toolchain.
- Why this fixed the issue: this front-end parses loop invariants as annotations attached to the upcoming loop statement, not as a comment inserted between the `for (...)` header and the body.

## Issue 4: replay compile hit duplicate short-name strategy imports

- Phenomenon: the first `coqc` replay failed before checking the manual proof bodies:

```text
File ".../array_count_negative_goal.v", line 21, characters 0-39:
Error: Required library int_array_strategy_goal matches several files in path
```

- Localization: `/home/yangfp/CAV/C/CAV/output/verify_20260604_233715v_array_count_negative/coq/generated/array_count_negative_goal.v`, import `Require Import int_array_strategy_goal.`.
- Fix action: added workspace-local wrapper modules under `/home/yangfp/CAV/C/CAV/output/verify_20260604_233715v_array_count_negative/coq/deps/` for `int_array`, `uint_array`, `undef_uint_array`, and `array_shape` strategy `goal/proof` files, each redirecting the short name to `SimpleC.EE.QCP_demos_LLM.*`. Replay then used `-Q "$DEPS" ""` so those wrappers took precedence.
- Why this fixed the issue: the generated files remained unchanged, shared library files remained untouched, and the short-name imports resolved deterministically to a single physical module.

## Issue 5: the generated manual proof contained five admitted witnesses

- Phenomenon: after successful symexec, the generated manual file contained five admitted lemmas:

```coq
proof_of_array_count_negative_safety_wit_4
proof_of_array_count_negative_entail_wit_1
proof_of_array_count_negative_entail_wit_2_1
proof_of_array_count_negative_entail_wit_2_2
proof_of_array_count_negative_entail_wit_3
```

- Localization: `/home/yangfp/CAV/C/CAV/output/verify_20260604_233715v_array_count_negative/coq/generated/array_count_negative_proof_manual.v`.
- Fix action: added two local helper lemmas,

```coq
array_count_negative_spec_app_single
array_count_negative_spec_bounds
```

and replaced all five `Admitted` bodies with proofs based on prefix splitting, branch-specific `Z_lt_dec` case analysis, the sublist-length bound, and loop-exit normalization to `sublist 0 n_pre l = l`.
- Why this fixed the issue: the remaining VCs were pure list/arithmetic obligations produced by the prefix-count invariant; no further annotation changes were needed once the proof-side helper lemmas were in place.

## Final gate result

- `symexec` on the current annotated file succeeded and regenerated `goal/proof_auto/proof_manual/goal_check`.
- `coqc` replay for `original/array_count_negative.v`, `array_count_negative_goal.v`, `array_count_negative_proof_auto.v`, `array_count_negative_proof_manual.v`, and `array_count_negative_goal_check.v` succeeded after the workspace-local strategy wrappers were added.
- `proof_manual.v` has no `Admitted`, `admit`, `Abort`, or new `Axiom`.

## Issue 6: retry audit found replay-visible path mismatch and source-integrity drift

- Phenomenon: attempt 2 started from runner feedback that `audit_check_coqc.log` failed at `Require Import int_array_strategy_goal.` with a duplicate-path error, and `source_integrity_gate.log` reported that the annotated C changed executable implementation after stripping annotations.
- Localization: duplicate import resolution is in `/home/yangfp/CAV/C/CAV/output/verify_20260604_233715v_array_count_negative/coq/generated/array_count_negative_goal.v`; implementation drift is in `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_233715v_array_count_negative.c`.
- Fix action: restore the annotated function body to the exact original executable loop form and move the short-name strategy wrappers onto the replay-visible `original/` path so the standard `-Q "$ORIG" ""` audit compile resolves the generated short-name imports deterministically.
- Why this is the right repair: the source-integrity gate only allows added annotations, not executable reshaping, and the compile guidance for duplicate short-name strategy modules states that replay should prefer unique wrappers under `original/` before compiling the generated files.
