2026-06-05 verify issue log

Issue: `symexec` failed at the loop header with `The number of now assertions and loop inv pre assertions does not match` on the first invariant draft.
Location: `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_054012v_count_asterisks_between_bars.c:35`.
Repair: replaced `(inside == 0 || inside == 1)` with `0 <= inside && inside <= 1`.
Why: the frontend was splitting the disjunctive invariant into mismatched assertion cases; the range fact keeps the same semantics as one assertion.

Issue: compile replay failed before proof checking because `char_array_strategy_goal` and `char_array_strategy_proof` matched both `QCP_demos_LLM` and `QCP_demos_human`.
Location: `count_asterisks_between_bars_goal.v` short-name strategy imports.
Repair: added wrapper modules in `original/` and `coq/generated/` that re-export the `QCP_demos_LLM` versions.
Why: this gives deterministic short-name resolution for both standard `-Q "$ORIG" ""` replay and generated-file sibling replay.

Issue: manual proof of `return_wit_1` revealed that the post-loop `Assert` had dropped `Zlength(l) == n`, so the proof could not derive `suffix = nil`.
Location: loop-exit `Assert` in `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_054012v_count_asterisks_between_bars.c`, theorem `count_asterisks_between_bars_return_wit_1`.
Repair: added `Zlength(l) == n` and the original no-zero fact back into the exit assertion, reran `symexec`, and replayed the manual proofs.
Why: `Assert` is a cutpoint; omitted contract facts are lost to later witnesses.

Final Result: Success
