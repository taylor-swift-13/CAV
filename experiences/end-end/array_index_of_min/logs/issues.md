## Verification Notes

- Symptom: initial `symexec` run failed with `Error: Lack of assertions in some paths for the loop!` at `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_002314v_array_index_of_min.c:22:4`.
- Location: `while (i < n)` loop in `array_index_of_min`.
- Repair action: added a loop invariant expressing that `idx` is the first minimum index over the processed prefix `[0, i)`.
- Key snippet:
  ```c
  0 <= idx && idx < i &&
  (forall (j: Z), (0 <= j && j < i) => l[idx] <= l[j]) &&
  (forall (j: Z), (0 <= j && j < idx) => l[j] > l[idx])
  ```
- Why this worked: the postcondition is exactly the whole-array version of that prefix fact, so `symexec` needed the invariant to preserve it across loop iterations.

- Symptom: first replay compile of `array_index_of_min_goal.v` failed with `Required library int_array_strategy_goal matches several files in path`.
- Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_002314v_array_index_of_min/coq/generated/array_index_of_min_goal.v:20`.
- Repair action: added workspace-local wrapper modules in `output/verify_20260605_002314v_array_index_of_min/original/` for the four strategy pairs (`int_array`, `uint_array`, `undef_uint_array`, `array_shape`) that re-export the `QCP_demos_LLM` versions.
- Key snippet:
  ```coq
  From SimpleC.EE.QCP_demos_LLM Require Export int_array_strategy_goal.
  From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
  Include SimpleC.EE.QCP_demos_LLM.int_array_strategy_proof.
  ```
- Why this worked: it gives `-Q "$ORIG" ""` a unique short-name resolution before Coq searches the duplicate modules under `examples/`.

- Symptom: the original manual proof attempt for `array_index_of_min_return_wit_1` could not complete because the goal still required converting `IntArray.full a n l` into `IntArray.full a_pre n_pre l`.
- Location: `coqtop` inspection of `array_index_of_min_return_wit_1`.
- Repair action: strengthened the loop invariant with `a == a@pre && n == n@pre`, then cleared generated files and reran `symexec`.
- Key snippet:
  ```c
  a == a@pre &&
  n == n@pre &&
  ```
- Why this worked: the function never mutates `a` or `n`, and the proof workflow expects `x`/`x_pre` mismatches to be fixed in annotations rather than reconstructed from memory predicates in Coq.

- Final gate status: latest `symexec` succeeded, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compiled, `proof_manual.v` contains no `Admitted`/`admit`/`Abort`/new `Axiom`, annotated C differs from original only by added verification annotations, and `coq/` intermediate artifacts were cleaned back to `.v` files only.
