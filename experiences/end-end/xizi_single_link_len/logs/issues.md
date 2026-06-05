2026-06-03 issue 1

Phenomenon:
The initial loop annotations repeatedly failed before VC generation with parser-level errors such as:
`Use of undeclared identifier 'Z'`,
`Expected C expression`,
and
`The number of now assertions and loop inv pre assertions does not match.`

Location:
`/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c`, loop invariant before `while (node != -1)`.

Repair action:
I normalized the loop head to the accepted plain `Inv` form, removed unsupported nat-to-Z surface syntax, and flattened the invariant into implication-style facts:
`(node == -1) => ...`
and
`(node != -1) => ...`.
The accepted invariant is the current one in the annotated C file.

Key C fragment:
`((node != -1) => xizi_single_link_wf(node, l))`
and
`((node != -1) => length + 1 + xizi_single_link_len_spec(node, l) == xizi_single_link_len_spec(head, l))`

Why this change:
The front end is sensitive to both annotation header form and case-split shape. Flattening the semantic split was required to get `symexec` through.

2026-06-03 issue 2

Phenomenon:
The compile pipeline could not find strategy imports from `xizi_single_link_len_goal.v` using the default `examples/` load path alone:
`Cannot find a physical path bound to logical path int_array_strategy_goal.`

Location:
`/home/yangfp/CAV/OS/CAV/output/verify_20260603_193124v_xizi_single_link_len/coq/generated/xizi_single_link_len_goal.v:21`

Repair action:
I staged strategy sources into
`/home/yangfp/CAV/OS/CAV/output/verify_20260603_193124v_xizi_single_link_len/coq/deps/`
and compiled them with both
`-Q "$DEPS" ""`
and
`-R "$DEPS" SimpleC.EE.QCP_demos_LLM`.

Key compile snippet:
`coqc ... -Q "$DEPS" "" -R "$DEPS" SimpleC.EE.QCP_demos_LLM "$DEPS/int_array_strategy_goal.v"`

Why this change:
The generated files import those strategies both unqualified and through their original example-path dependencies, so a dual-path local staging area was the smallest fix that preserved generated sources.

2026-06-03 issue 3

Phenomenon:
The verify pipeline still fails at the manual proof gate. The latest stable failing gate is:
`coqc xizi_single_link_len_proof_manual.v`
with the unresolved helper proof inside `xizi_single_link_wf_step`.

Location:
`/home/yangfp/CAV/OS/CAV/output/verify_20260603_193124v_xizi_single_link_len/coq/generated/xizi_single_link_len_proof_manual.v`

Repair action attempted:
I added helper lemmas for `xizi_next_at`, `xizi_single_link_len_nat`, nonnegativity, and spec bounds, then iterated compile-driven fixes.
The remaining proof gap is exposing the recursive validity one step from
`xizi_single_link_wf node l`
by proving the hidden fuel is a successor under the node-range hypothesis.

Key error / theorem:
Latest stable blocker during the helper proof:
`proof_manual.v`, helper theorem `xizi_single_link_wf_step`,
after multiple iterations ending at a non-simplified recursive-validity proof state.

Why this is still failing:
The current manual proof file does not yet provide the bridge from the top-level well-formedness predicate to the one-step successor facts required by `entail_wit_1`, `entail_wit_2`, and `safety_wit_4`.

Current relevant paths:
`/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c`
`/home/yangfp/CAV/OS/CAV/output/verify_20260603_193124v_xizi_single_link_len/coq/generated/xizi_single_link_len_goal.v`
`/home/yangfp/CAV/OS/CAV/output/verify_20260603_193124v_xizi_single_link_len/coq/generated/xizi_single_link_len_proof_manual.v`

Next verify round should:
1. Add a helper lemma that rewrites the hidden fuel in `xizi_single_link_wf` into a successor form when the node range proves the list length is positive.
2. Finish `xizi_single_link_wf_step` using that lemma, then reuse it to close `entail_wit_1`, `entail_wit_2`, `safety_wit_4`, and `return_wit_1`.
3. Re-run the full compile chain including `goal_check.v`.

Final Result: Fail

2026-06-03 issue 4

Phenomenon:
Retry attempt 2 fixed the original `Not an inductive definition` failure in `xizi_single_link_wf_step`, but `coqc` still fails in the same theorem after the proof reaches the nonterminal successor case.

Location:
`/home/yangfp/CAV/OS/CAV/output/verify_20260603_193124v_xizi_single_link_len/coq/generated/xizi_single_link_len_proof_manual.v:251`
inside helper theorem `xizi_single_link_wf_step`.

Repair action attempted:
I replaced the earlier broken destruct pattern with helper lemmas over
`xizi_single_link_valid_nat`,
proved range / seen weakening / fuel monotonicity helpers,
and rewrote the arithmetic branch to use explicit case splits on
`Znth node ...`
and
`xizi_next_at (Znth node ...) ...`.

Key error:
`coqc` now reports a mismatch between a two-layer nested match on
`xizi_single_link_len_nat (Datatypes.length tl') ...`
and a three-layer expression whose innermost branch is still guarded by
`Z.eq_dec (xizi_next_at (xizi_next_at ...)) (-1)`.
The failing compile snapshot is the latest manual compile run from
`/home/yangfp/CAV/OS/CAV/QualifiedCProgramming/SeparationLogic`.

Why this is still failing:
The final arithmetic branch needs one more bridge from the suffix-validity witness `Htail` to the recursive unfolding of `xizi_single_link_len_nat` on the successor-of-successor term. The current script only unfolds one side deeply enough, so reflexivity cannot close the branch.

Current relevant paths:
`/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c`
`/home/yangfp/CAV/OS/CAV/output/verify_20260603_193124v_xizi_single_link_len/coq/generated/xizi_single_link_len_proof_manual.v`
`/home/yangfp/CAV/OS/CAV/output/verify_20260603_193124v_xizi_single_link_len/coq/generated/xizi_single_link_len_goal.v`

Next verify round should:
1. Inspect the proof state at `xizi_single_link_wf_step` line 251 and add a helper that unfolds the nonterminal successor branch one level deeper under `Htail`.
2. Recompile `proof_manual.v` first, then rerun the full compile chain through `goal_check.v`.
3. If that helper changes the semantic step lemma shape, update only `proof_manual.v`; the annotated C currently does not need a contract or implementation change.

Final Result: Fail

## External Codex Failure

- Stage: `external-agent-run`
- Exit code: `124`
- Stderr log: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_193124v_xizi_single_link_len/logs/agent_stderr_20260603_200733.log`
- Detail: `external agent run exceeded remaining timeout budget of 1933 seconds`

2026-06-04 issue 5

Phenomenon:
Manual continuation showed that the old VC was not provable at return: the loop invariant did not preserve `head == head@pre` or `next == next@pre`, so `return_wit_1` could not prove either `length = xizi_single_link_len_spec head_pre l` or `IntArray.full next_pre n l`.

Location:
`/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_193124v_xizi_single_link_len.c`, loop invariant before `while (node != -1)`.

Repair action:
Added `head == head@pre` and `next == next@pre` to the loop invariant, reran `symexec`, and regenerated `goal/proof_auto/proof_manual/goal_check`. The new VC moved `return_wit_1` to `proof_auto.v`, leaving only `safety_wit_4`, `entail_wit_1`, and `entail_wit_2` in `proof_manual.v`.

Proof repair:
Completed `xizi_single_link_wf_step` with the helper `xizi_single_link_len_nat_valid_step`, plus a fuel bound `xizi_single_link_len_spec_bound_any` used to prove `length + 1 <= n` in the loop step. Reordered entailment witness scripts to match the generated goal order.

Result:
`coqc` passes for all generated files and runner audit passes: `audit_check`, `source_integrity`, `fingerprint`, and `symexec_freshness`.

Final Result: Success
