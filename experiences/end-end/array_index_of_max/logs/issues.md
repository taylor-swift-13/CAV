2026-06-04T16:34:42Z

Phenomenon: initial annotation had no loop invariant, so the scan over `a` had no preserved processed-prefix semantics for `symexec`.

Location: `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_002002v_array_index_of_max.c`, `while (i < n)`.

Repair action: added a loop invariant capturing `1 <= i <= n`, `0 <= idx < i`, prefix maximality of `idx`, earliest-index tie breaking for `idx`, and preservation of `IntArray::full(a, n, l)`.

Key annotation fragment:
`(forall (j: Z), (0 <= j && j < i) => l[j] <= l[idx])`
`(forall (j: Z), (0 <= j && j < idx) => l[j] < l[idx])`

Why this mattered: without that prefix summary, the generated VC cannot derive the postcondition for the final index of the maximum.

2026-06-04T16:34:42Z

Phenomenon: first proof attempt reached `return_wit_1` with the unresolved goal
`IntArray.full a n l |-- IntArray.full a_pre n_pre l`.

Location: generated return witness `array_index_of_max_return_wit_1` in `coq/generated/array_index_of_max_goal.v`.

Repair action: strengthened the loop invariant with `a == a@pre` and `n == n@pre`, then deleted the generated Coq files and reran `symexec`.

Key proof-state fragment after `pre_process; entailer!`:
`goal 1: IntArray.full a n l |-- IntArray.full a_pre n_pre l`
`goal 2: forall j, 0 <= j < n_pre -> Znth j l 0 <= Znth idx l 0`
`goal 3: idx < n_pre`

Why this mattered: the function never mutates `a` or `n`, so parameter-preservation belongs in the annotation layer, not as an ad hoc Coq proof obligation.

2026-06-04T16:34:42Z

Phenomenon: replay compilation of `goal.v` initially failed before any proof checking with a duplicate-library-path error for short strategy imports.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_002002v_array_index_of_max/coq/generated/array_index_of_max_goal.v`, import `Require Import int_array_strategy_goal.` and the corresponding proof/shape strategy imports.

Repair action: added local wrapper modules under `/home/yangfp/CAV/C/CAV/output/verify_20260605_002002v_array_index_of_max/original/` for `int_array`, `uint_array`, `undef_uint_array`, and `array_shape` goal/proof pairs, re-exporting the `QCP_demos_LLM` versions to give replay a unique short-name resolution.

Key compile error:
`Required library int_array_strategy_goal matches several files in path`

Why this mattered: the generated Coq files must stay unchanged; wrapper modules are the least invasive way to disambiguate those imports for this workspace only.

2026-06-04T16:34:42Z

Phenomenon: after the invariant fix and replay wrapper setup, all generated gates succeeded.

Location: current workspace `/home/yangfp/CAV/C/CAV/output/verify_20260605_002002v_array_index_of_max/`.

Repair action: proved the three manual witnesses in `coq/generated/array_index_of_max_proof_manual.v`, compiled `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`, removed non-`.v` artifacts from `coq/` and non-`.c`/`.v` artifacts from `input/`, and updated the workspace fingerprint.

Key result:
- `symexec` on `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_002002v_array_index_of_max.c` completed successfully.
- `proof_manual.v` contains no `Admitted`, `admit`, `Abort`, or `Axiom`.
- `goal_check.v` compiled successfully.

2026-06-05T00:36:30Z

Phenomenon: the previous round still failed runner audit despite the successful proof because replay of `/home/yangfp/CAV/C/CAV/output/verify_20260605_002002v_array_index_of_max/coq/generated/array_index_of_max_goal.v` resolved `int_array_strategy_goal` to multiple shared libraries.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_002002v_array_index_of_max/logs/audit_check_coqc.log`, first command compiling `array_index_of_max_goal.v`.

Repair action: compiled the existing wrapper sources in `/home/yangfp/CAV/C/CAV/output/verify_20260605_002002v_array_index_of_max/original/` for `int_array`, `uint_array`, `undef_uint_array`, and `array_shape`, then reran `coqc` for `array_index_of_max_goal.v`, `array_index_of_max_proof_auto.v`, `array_index_of_max_proof_manual.v`, and `array_index_of_max_goal_check.v` from a clean `coq/generated/` state. After the replay succeeded, I cleaned only `coq/` intermediates and deliberately kept the wrapper compile artifacts in `original/`.

Key compile symptom:
`Error: Required library int_array_strategy_goal matches several files in path`

Why this fix is correct: the generated imports are fixed short names, so the repair has to be in workspace-local load-path resolution rather than in `goal.v` or the proof script. Keeping the wrapper `.vo` files under `-Q "$ORIG" ""` gives audit replay a unique physical path for each short strategy module.
