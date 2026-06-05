2026-06-04 issue 1

Phenomenon:
Initial `symexec` run failed with `Error: Lack of assertions in some paths for the loop!` at `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_210529v_array_any_zero.c:22:4`.

Location:
Loop head of `array_any_zero` in `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_210529v_array_any_zero.c`.

Repair action:
Added a loop invariant summarizing the already checked prefix as nonzero, preserved `a == a@pre` and `n == n@pre`, and retained `IntArray::full(a, n, l)`. Also added a loop-exit assertion to fix `i == n` for the `return 0` branch.

Key code / error fragment:
`for (i = 0; i < n; i++)` without any `Inv`
and
`Error: Lack of assertions in some paths for the loop!`

Why this fixed it:
The function is a read-only existence scan. The invariant exactly captures the processed-prefix summary needed for both the early `return 1` witness and the final `return 0` witness.

2026-06-04 issue 2

Phenomenon:
The first invariant placement caused `symexec` to fail with `Expected loop after loop invariant.` at `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_210529v_array_any_zero.c:30:5`.

Location:
Same loop in `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_210529v_array_any_zero.c`.

Repair action:
Moved the `Inv` comment to the accepted position immediately before the `for` statement and normalized the loop step to `++i`, matching nearby working end-to-end examples.

Key code / error fragment:
Rejected shape:
`for (...)`
`/*@ Inv ... */`
`{`
Accepted shape:
`/*@ Inv ... */`
`for (...) {`

Why this fixed it:
This was a front-end syntax requirement, not a semantic issue.

2026-06-04 issue 3

Phenomenon:
Replay compile of `array_any_zero_goal.v` failed with:
`Error: Required library int_array_strategy_goal matches several files in path`
because both `QCP_demos_LLM` and `QCP_demos_human` export the same short strategy module names.

Location:
`/home/yangfp/CAV/C/CAV/output/verify_20260604_210529v_array_any_zero/coq/generated/array_any_zero_goal.v:20`.

Repair action:
Added eight wrapper modules under `/home/yangfp/CAV/C/CAV/output/verify_20260604_210529v_array_any_zero/original/`:
`int_array_strategy_{goal,proof}.v`,
`uint_array_strategy_{goal,proof}.v`,
`undef_uint_array_strategy_{goal,proof}.v`,
`array_shape_strategy_{goal,proof}.v`.
Each wrapper re-exports or includes the `SimpleC.EE.QCP_demos_LLM` strategy module with the short name expected by the generated files.

Key code / error fragment:
`From SimpleC.EE.QCP_demos_LLM Require Export int_array_strategy_goal.`
and
`From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.`
`Include SimpleC.EE.QCP_demos_LLM.int_array_strategy_proof.`

Why this fixed it:
`-Q "$ORIG" ""` gives the generated short imports a unique local resolution target without editing generated VC files or shared example trees.

2026-06-04 issue 4

Phenomenon:
`proof_manual.v` initially failed on small witness-shape mismatches:
- `proof_of_array_any_zero_entail_wit_3`: `Cannot find witness`
- `proof_of_array_any_zero_return_wit_1`: `No such goal`
- `proof_of_array_any_zero_return_wit_2`: existential introduced at the wrong layer

Location:
`/home/yangfp/CAV/C/CAV/output/verify_20260604_210529v_array_any_zero/coq/generated/array_any_zero_proof_manual.v`.

Repair action:
Adjusted each lemma to the actual proof state exposed by `pre_process` / `entailer!`:
- `entail_wit_3`: after `entailer!`, introduced `j` and applied the invariant hypothesis directly.
- `return_wit_1`: shortened to `pre_process.` because the goal was already closed.
- `return_wit_2`: ran `entailer!` first, then proved `1 = 1 -> exists ...` with witness `i_3`.

Key code / error fragment:
`Error: Tactic failure: Cannot find witness.`
`Error: No such goal.`
and the remaining goal
`1 = 1 -> exists i0 : Z, 0 <= i0 < n_pre /\ Znth i0 l 0 = 0`.

Why this fixed it:
These were proof-layer mismatches, not contract or annotation gaps. Matching the tactic order to the actual assertion-level vs Coq-level goal shape discharged the remaining manual obligations cleanly.

2026-06-04 issue 5

Phenomenon:
Runner retry audit failed with `annotated C changes executable implementation after removing comments/QCP annotations`.

Location:
`/home/yangfp/CAV/C/CAV/output/verify_20260604_210529v_array_any_zero/logs/source_integrity_gate.log` and the loop header in `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_210529v_array_any_zero.c`.

Repair action:
Compared `/home/yangfp/CAV/C/CAV/input/array_any_zero.c` and the annotated file after stripping QCP comments, found the only executable drift at the `for` increment (`++i` in annotated vs `i++` in input), and changed the annotated loop back to `for (i = 0; i < n; i++)`. Then reran `symexec`, restored the four manual witness proofs that `symexec` regenerated as `Admitted`, replay-compiled `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`, and cleaned non-`.v` artifacts under `coq/`.

Key code / log fragment:
Input executable fragment:
`for (i = 0; i < n; i++)`
Annotated retry fragment before fix:
`for (i = 0; i < n; ++i)`
Source-integrity check after fix:
`diff -u <(sed '/\\/\\*@/,/\\*\\//d' input/array_any_zero.c) <(sed '/\\/\\*@/,/\\*\\//d' annotated/verify_20260604_210529v_array_any_zero.c)`
returned no differences.

Why this fixed it:
The audit compares executable C after annotations are removed, so semantic equivalence was not enough. Restoring the exact original increment token eliminated the integrity mismatch while leaving the verification annotations and proof obligations unchanged.
