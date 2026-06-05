## 2026-06-05 20:36:00 +0800 - Verify summary for `ex_perfect_number_code`

- Gate: `symexec`
  - Phenomenon: the first annotated attempt failed before VC generation with `Use of undeclared identifier d` in the post-loop assertion.
  - Location: [verify_20260605_200638v_ex_perfect_number_code.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_200638v_ex_perfect_number_code.c)
  - Cause: `d` was declared in the `for` initializer, so it was out of scope after the loop where the exit assertion needed it.
  - Fix: moved `int d;` to a standalone local declaration before the loop and kept the same executable loop behavior with `for (d = 1; d < n; d++)`.
  - Result: `symexec_keep_proofs.py --name ex_perfect_number_code --stamp 20260605_200638v` completed successfully and generated fresh `goal/proof_auto/proof_manual/goal_check`.

- Gate: `annotation`
  - Phenomenon: the contract postcondition depends on `aliquot_sum_z(n)`, but direct `Z.to_nat` fuel expressions are not parser-stable in C annotations.
  - Location: [ex_perfect_number_code_helper.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/coq/deps/ex_perfect_number_code_helper.v), [verify_20260605_200638v_ex_perfect_number_code.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_200638v_ex_perfect_number_code.c)
  - Fix: added a workspace-local helper `aliquot_sum_tail_z (n d : Z)` and imported it into the annotated file. The loop invariant now preserves `sum + aliquot_sum_tail_z(n, d) == aliquot_sum_z(n@pre)` together with the loop bounds and nonnegativity facts.
  - Result: the generated VCs matched the intended semantic decomposition of processed divisor sum plus remaining tail sum.

- Gate: `proof_manual`
  - Phenomenon: repeated `coqc` failures were caused by generated-environment notation/closure details rather than invalid VCs:
    - bare remainder notation `n % d` triggered `Unknown scope delimiting key d`;
    - the stop helper initially used unavailable library names (`Z.geb_lt`);
    - direct `lia`/`reflexivity` left entailment goals open in `safety_wit_5`, `entail_wit_1`, and the return witnesses;
    - one exit-witness rewrite targeted the wrong hypothesis number after `subst d`.
  - Location: [ex_perfect_number_code_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/coq/generated/ex_perfect_number_code_proof_manual.v), [proof_reasoning.md](/home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/logs/proof_reasoning.md)
  - Fix:
    - normalized helper statements to the generated `% ( d )` shape;
    - proved local tail helpers `aliquot_sum_from_fuel_nonneg`, `aliquot_sum_tail_z_nonneg`, `aliquot_sum_tail_z_start`, `aliquot_sum_tail_z_stop`, `aliquot_sum_tail_z_step_divides`, and `aliquot_sum_tail_z_step_not_divides`;
    - switched witness closures from raw arithmetic tactics to `entailer!` once the helper rewrites had normalized the pure facts;
    - reran fingerprint retrieval after the second `Cannot find witness` class failure and recorded the adopted/rejected patterns.
  - Result: `proof_manual.v` compiled without `Admitted`, and `goal_check.v` compiled successfully.

- Gate: `compile cleanup`
  - Phenomenon: replay compilation produced `.vo/.vos/.vok/.glob/.aux` artifacts under `coq/` and `original/`.
  - Fix: removed all non-`.v` files under `coq/` and all non-`.v`/`.c` files under `original/`.
  - Result: the workspace keeps only source `.v` files plus the original C/V inputs.

## 2026-06-05 20:54:21 +0800 - Retry repair for audit replay and source integrity

- Gate: `source_integrity`
  - Phenomenon: runner rejected the previous annotated C with `annotated C changes executable implementation after removing comments/QCP annotations`.
  - Location: [verify_20260605_200638v_ex_perfect_number_code.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_200638v_ex_perfect_number_code.c)
  - Cause: the first working proof hoisted `d` out of the original loop header into a separate `int d;` declaration so a post-loop assertion could mention it.
  - Fix: restored the exact executable loop form `for (int d = 1; d < n; d++)` and reduced the exit bridge to facts over `sum` and `n@pre`, which are available after the loop without changing executable code.
  - Result: the annotated copy now differs from `input/ex_perfect_number_code.c` only by QCP comments/imports, not by executable statements.

- Gate: `audit_check_coqc`
  - Phenomenon: runner replay stopped at `goal.v` with `Cannot find a physical path bound to logical path ex_perfect_number_code_helper`.
  - Location: [ex_perfect_number_code_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/coq/generated/ex_perfect_number_code_goal.v), helper source previously only in `coq/deps/`
  - Cause: `symexec` hard-coded `Require Import ex_perfect_number_code_helper.` into generated files, but the helper lived only in `coq/deps/`, outside the replay path used by generated-file compilation.
  - Fix: moved the helper source to [ex_perfect_number_code_helper.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/coq/generated/ex_perfect_number_code_helper.v) and made it self-contained by defining `aliquot_sum_from_fuel_tail` locally instead of importing `ex_perfect_number_code`.
  - Result: normal replay compilation now succeeds for `goal`, `proof_auto`, `proof_manual`, and `goal_check` with the helper resolved from `coq/generated/`.

- Gate: `proof_manual`
  - Phenomenon: rerunning `symexec_keep_proofs.py` after the source-integrity fix preserved only 4 of 8 proofs and reopened the loop-exit witness plus the three return witnesses.
  - Location: [ex_perfect_number_code_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/coq/generated/ex_perfect_number_code_proof_manual.v)
  - Fix: re-proved `entail_wit_3` by deriving `d = n_pre`, rewriting the stop lemma into the invariant equation, and re-proved `return_wit_1/2/3` by unfolding `ex_perfect_number_code_spec` and splitting on `Z.eqb` / `Z.gtb`.
  - Result: `proof_manual.v` is again free of `Admitted` / `Abort` / proof placeholders, and `goal_check.v` compiles.

- Gate: `cleanup`
  - Phenomenon: replay compilation recreated `.vo/.vos/.vok/.glob/.aux` files under `coq/generated/`.
  - Fix: deleted all non-`.v` files under the current workspace `coq/` tree after the final successful replay.
  - Result: the current workspace keeps only source artifacts needed for rerun and audit.
Final Result: Success

## 2026-06-05 21:05:40 +0800 - Retry replay split requires two helper locations and minimal retained `.vo` files

- Gate: `audit_check_coqc` plus standard generated replay
  - Phenomenon: after source-integrity was fixed, the remaining blocker was the helper import baked into generated files:
    ```text
    Require Import ex_perfect_number_code_helper.
    ```
    Bare audit replay runs `coqc original/ex_perfect_number_code.v` followed by `coqc coq/generated/ex_perfect_number_code_goal.v`, while the normal verification replay compiles generated files under the prefixed logic path `SimpleC.EE.CAV.verify_20260605_200638v_ex_perfect_number_code`.
  - Localization: [ex_perfect_number_code_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/coq/generated/ex_perfect_number_code_goal.v), [ex_perfect_number_code_helper.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/coq/generated/ex_perfect_number_code_helper.v), [ex_perfect_number_code_helper.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_200638v_ex_perfect_number_code/original/ex_perfect_number_code_helper.v)
  - Failed intermediate attempt: compiling only a bare helper `.vo` in `coq/generated/` made audit-style short-name lookup plausible, but the standard prefixed replay then failed with:
    ```text
    contains library ex_perfect_number_code_helper and not library
    SimpleC.EE.CAV.verify_20260605_200638v_ex_perfect_number_code.ex_perfect_number_code_helper
    ```
  - Fix: keep the generated helper source for prefixed replay, add the same helper source under `original/` for unprefixed audit replay, and retain exactly two helper `.vo` files after cleanup:
    - `coq/generated/ex_perfect_number_code_helper.vo` for `-R "$GEN" "$LP"` replay
    - `original/ex_perfect_number_code_helper.vo` for bare short-name audit replay
  - Why this is the minimal stable shape: deleting either helper `.vo` reintroduces a replay-specific load-path failure, while all other `.vo/.glob/.vok/.vos/.aux` files can be removed because runner replay regenerates the main compiled outputs itself.
