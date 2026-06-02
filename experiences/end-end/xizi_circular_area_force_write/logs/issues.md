## 2026-06-02 Proof-only failure summary

Failure gate: `coqc proof_manual.v`

Exit / location:
- command failed while compiling `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/generated/xizi_circular_area_force_write_proof_manual.v`
- latest stable failure site: theorem `proof_of_xizi_circular_area_force_write_return_wit_2`
- compiler location: line 215, characters 38-41

Key error:

```text
File ".../xizi_circular_area_force_write_proof_manual.v", line 215, characters 38-41:
Error: Tactic failure:  Cannot find witness.
```

Relevant files:
- annotated C: `/home/yangfp/CAV/OS/CAV/annotated/verify_20260602_212502v_xizi_circular_area_force_write.c`
- goal VC: `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/generated/xizi_circular_area_force_write_goal.v`
- manual proof: `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/generated/xizi_circular_area_force_write_proof_manual.v`

What was fixed before this blocker:
- resolved missing bare strategy imports by staging local copies under `coq/deps/`
- proved the arithmetic safety witnesses with `pre_process; entailer!; lia`
- added local `replace_Znth` helper lemmas
- refined `return_wit_1` around `% = Z.rem`, explicit `Znth_replace_Znth_*` rewrites, and `Z.rem_small` / `Z.rem_same`

Current blocker detail:
- `return_wit_2` still uses the same nested `replace_Znth` shape as `return_wit_1`, but the proof script at line 215 is still relying on implicit inference:

```coq
rewrite Znth_replace_Znth_Same by lia.
rewrite Znth_replace_Znth_Diff by lia.
rewrite Znth_replace_Znth_Diff by lia.
rewrite Znth_replace_Znth_Same by lia.
```

- this is too weak for the generated term shape and leaves Coq unable to infer the witness/list arguments inside the nested replacements

Next concrete fix:
- rewrite `proof_of_xizi_circular_area_force_write_return_wit_2` exactly like `return_wit_1`:
  1. `set (w := data_length_pre - (area_length_pre - Znth 1 l 0))` before `Exists`
  2. replace each generic `rewrite Znth_replace_Znth_* by lia` with explicit-argument rewrites naming the concrete list (`replace_Znth 2 1 (replace_Znth 1 w l)`, then `replace_Znth 1 w l`, then `l`)
  3. after the final same-index rewrite, finish the branch equation with `lia`
- after `return_wit_2`, repeat the same explicit-rewrite treatment for `return_wit_3` and `return_wit_4`, then rerun `coqc proof_manual.v` and `coqc goal_check.v`

Final Result: Fail

## 2026-06-02 Retry attempt 2 success closure

Recovered gate sequence:
- `proof_of_xizi_circular_area_force_write_return_wit_2` was rewritten with an explicit local alias `w := data_length_pre - (area_length_pre - Znth 1 l 0)` and concrete `Znth_replace_Znth_same` / `Znth_replace_Znth_diff` rewrites over the nested `replace_Znth` stack; this removed the `Cannot find witness` failure at `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/generated/xizi_circular_area_force_write_proof_manual.v:215`.
- `proof_of_xizi_circular_area_force_write_return_wit_3` and `proof_of_xizi_circular_area_force_write_return_wit_4` needed the same explicit rewrite pattern plus bullet reordering after `entailer!`, because the actual subgoal order put the `force_pre = 0` branch before the `Znth 2 lr 0 = 1` goal.
- `goal_check.v` then failed with duplicate labels because `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/generated/xizi_circular_area_force_write_proof_auto.v` already defines all `safety_wit_*` and `partial_solve_wit_*` lemmas. The fix was to keep those lemmas out of `proof_manual.v` and leave only the four return witnesses there.

Key verification results:
- compiled in fallback workspace mode with `-R /home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/deps SimpleC.EE` and `-R /home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/generated SimpleC.EE.CAV.verify_20260602_212502v_xizi_circular_area_force_write`
- `coqc ... xizi_circular_area_force_write_goal.v` passed
- `coqc ... xizi_circular_area_force_write_proof_auto.v` passed
- `coqc ... xizi_circular_area_force_write_proof_manual.v` passed
- `coqc ... xizi_circular_area_force_write_goal_check.v` passed
- `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/generated/xizi_circular_area_force_write_proof_manual.v` contains no `Admitted` / `admit` / `Abort` / `Axiom`
- non-`.v` intermediates under `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/` were cleaned after the successful compile replay

Scope/integrity note:
- this was a proof-only retry, so `/home/yangfp/CAV/OS/CAV/annotated/verify_20260602_212502v_xizi_circular_area_force_write.c` was not modified in this round
- the fix stayed within `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/generated/xizi_circular_area_force_write_proof_manual.v` and `logs/*`

Final Result: Success

## External Codex Failure

- Stage: `external-agent-run`
- Exit code: `124`
- Stderr log: `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/logs/agent_stderr_20260602_214904.log`
- Detail: `external agent run exceeded remaining timeout budget of 772 seconds`
