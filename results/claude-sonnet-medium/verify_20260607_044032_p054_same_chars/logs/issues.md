# Issues Log — p054_same_chars

## Issue 1: `string_bridge` not found in Coq loadpath
- **Symptom**: `Cannot find library string_bridge in loadpath`
- **Root cause**: `-I $INPUT` adds a filesystem search path for `.v` source files but does not make `.vo` compiled files visible under a logical name. Coq requires `-Q` for logical namespace mapping.
- **Fix**: Changed compilation flags to `-Q $WS/coq/deps "" -Q $INPUT ""`.

## Issue 2: `subst` needed in entail_wit_1
- **Symptom**: `cancel.` failed in the spatial bullet of `entail_wit_1` because the heap predicate contained `|-> retval` but the goal expected `|-> n0`.
- **Root cause**: The precondition carries equalities `retval = n0` and `retval_2 = n1` that `pre_process` does not automatically substitute.
- **Fix**: Added `subst.` after `pre_process.` in `proof_of_p054_same_chars_entail_wit_1`.

## Issue 3: `dump_pre_spatial` required after `split_pures`
- **Symptom**: `lia` and `assumption` failed on goals produced by `split_pures` with error about no matching hypothesis.
- **Root cause**: `split_pures` leaves each sub-goal in sep-logic entailment form `<LHS> |-- " P "`. Standard Coq tactics (`lia`, `assumption`, `intro`) do not operate on this wrapped form directly.
- **Fix**: Applied `dump_pre_spatial` after `split_pures` to convert each goal to a plain Coq proposition before dispatching with `lia`/`assumption`.

## Issue 4: `intro _` parse error
- **Symptom**: `Syntax error: [ltac_use_default] expected after [tactic]` at `intro _.`
- **Root cause**: In this Coq/Rocq version, `intro _` with a wildcard pattern has a parsing ambiguity.
- **Fix**: Changed all `intro _` to `intros _`.

## Issue 5: Duplicate label in goal_check
- **Symptom**: `The label proof_of_p054_same_chars_partial_solve_wit_1_pure is already declared.`
- **Root cause**: `proof_auto.v` already contains `partial_solve_wit_1_pure` and `partial_solve_wit_2_pure` as `Admitted` lemmas. `goal_check.v` uses `Include` for both files, so duplicate names cause a module error.
- **Fix**: Removed the `partial_solve_wit` proofs from `proof_manual.v`; those goals are owned by `proof_auto.v`.

## Issue 6: `entail_wit_3` spatial mismatch
- **Symptom**: `cancel.` failed because loop counter `i` had advanced to `n0` but the spatial predicate still referred to `i`.
- **Root cause**: The exit condition `i >= n0` combined with the invariant `i <= n0` implies `i = n0`, but `cancel` needs syntactic equality.
- **Fix**: Added `replace i with n0 by lia.` before `cancel.` in `proof_of_p054_same_chars_entail_wit_3`.

## External Codex Failure

- Stage: `external-agent-run`
- Exit code: `124`
- Stderr log: `/home/yangfp/CAV/C/CAV/output/verify_20260607_044032_p054_same_chars/logs/agent_stderr_20260607_062350.log`
- Detail: `external agent run exceeded remaining timeout budget of 1002 seconds`
