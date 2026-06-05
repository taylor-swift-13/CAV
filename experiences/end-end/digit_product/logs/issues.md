## 2026-06-05 06:33 CST - Missing loop invariant blocked the first `symexec`

- Gate: `symexec`
- Exit code / location: process exit code `1`; `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_062321v_digit_product.c:21:4`
- Key error:

```text
fatal error: Error: Lack of assertions in some paths for the loop!
```

- Triggering code fragment:

```c
int product = 1;

while (n > 0) {
    product *= n % 10;
    n /= 10;
}
```

- Repair: added a workspace-local helper `/home/yangfp/CAV/C/CAV/output/verify_20260605_062321v_digit_product/coq/deps/digit_product_helper.v` exposing `digit_product_acc_z` and `digit_product_safe_z`, imported those symbols into the active annotated C, and added the loop invariant

```c
/*@ Inv
      0 <= n &&
      0 <= product &&
      digit_product_safe_z(n, product) &&
      digit_product_acc_z(n, product) == digit_product_z(n@pre)
*/
```

- Why this fixed it: the invariant records both the semantic accumulator summary and the recursive overflow-safety predicate already present in `input/digit_product.v`, which is exactly the information needed at the loop head for `symexec` to generate stable VCs.
- Result: rerunning `symexec` succeeded and regenerated `digit_product_goal.v`, `digit_product_proof_auto.v`, `digit_product_proof_manual.v`, and `digit_product_goal_check.v`.

## 2026-06-05 06:38 CST - Manual proof needed fuel-stability lemmas instead of further annotation changes

- Gate: manual proof replay of `/home/yangfp/CAV/C/CAV/output/verify_20260605_062321v_digit_product/coq/generated/digit_product_proof_manual.v`
- Theorems involved:
  - `proof_of_digit_product_safety_wit_5`
  - `proof_of_digit_product_entail_wit_1`
  - `proof_of_digit_product_entail_wit_2`
  - `proof_of_digit_product_return_wit_1`
  - `proof_of_digit_product_return_wit_2`
- Phenomenon: the generated VCs were pure semantic/safety bridges over the imported fuelled definitions, for example:

```coq
digit_product_safe_z (n ÷ 10) (product * (n % 10))
digit_product_acc_z (n ÷ 10) (product * (n % 10)) = digit_product_z n_pre
```

while the imported recursive definitions step through `digit_product_loop_fuel` / `digit_product_safe_fuel` with a predecessor fuel.
- Repair: kept the annotation unchanged and added helper lemmas in `proof_manual.v`:

```coq
digit_product_loop_fuel_stable
digit_product_safe_fuel_stable
digit_product_acc_z_step
digit_product_safe_z_step
```

plus the standard decimal arithmetic facts `div_10_lt_pos`, `quot_10_lt_pos`, and `rem_10_bounds_pos`.
- Why this fixed it: the blocker was purely Coq-side normalization of the imported helper definitions, not missing program-state information. Proving stability and one-step unfold lemmas in `proof_manual.v` lets the generated witnesses rewrite from the current loop state to the next loop state without changing the verified C.
- Result: `coqc` compiled `original/digit_product.v`, `coq/deps/digit_product_helper.v`, `digit_product_goal.v`, `digit_product_proof_auto.v`, `digit_product_proof_manual.v`, and `digit_product_goal_check.v` successfully. The final `proof_manual.v` contains no `Admitted.`, no `admit`, no `Abort.`, and no manual `Axiom`.

## 2026-06-05 06:44 CST - Final cleanup and integrity checks

- Gate: workspace hygiene / source-integrity audit
- Checks performed:
  - `sha256sum` confirmed `input/digit_product.c` matches `original/digit_product.c`, and `input/digit_product.v` matches `original/digit_product.v`.
  - The active annotated file `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_062321v_digit_product.c` keeps the original executable statements and contract intact and only adds verification annotations plus helper imports.
  - Removed all non-`.v` artifacts under `/home/yangfp/CAV/C/CAV/output/verify_20260605_062321v_digit_product/coq/`.
  - Removed stale non-`.c`/non-`.v` artifacts from `/home/yangfp/CAV/C/CAV/input/` so the final audit sees a clean input directory.
- Result: cleanup verification found no remaining non-`.v` files under the workspace `coq/` tree and no remaining non-`.c`/non-`.v` files under `input/`.

## 2026-06-05 06:47 CST - Runner audit replay needed the helper on the generated/original short-name path

- Gate: runner audit replay from `/home/yangfp/CAV/C/CAV/output/verify_20260605_062321v_digit_product/logs/audit_check_coqc.log`
- Exit code / location: bare `coqc` failed on `/home/yangfp/CAV/C/CAV/output/verify_20260605_062321v_digit_product/coq/generated/digit_product_goal.v` line 20 at `Require Import digit_product_helper.`
- Key error:

```text
Error: Cannot find a physical path bound to logical path
digit_product_helper.
```

- Triggering files:
  - generated VC import site: `/home/yangfp/CAV/C/CAV/output/verify_20260605_062321v_digit_product/coq/generated/digit_product_goal.v`
  - existing helper before repair: `/home/yangfp/CAV/C/CAV/output/verify_20260605_062321v_digit_product/coq/deps/digit_product_helper.v`
- Repair: kept the generated VC text unchanged, added the same helper module as workspace-local short-name sources at
  - `/home/yangfp/CAV/C/CAV/output/verify_20260605_062321v_digit_product/original/digit_product_helper.v`
  - `/home/yangfp/CAV/C/CAV/output/verify_20260605_062321v_digit_product/coq/generated/digit_product_helper.v`

  and replayed the standard compile chain with the helper compiled from `original/`:

```text
coqc ... -Q "$ORIG" "" "$ORIG/digit_product.v"
coqc ... -Q "$ORIG" "" "$ORIG/digit_product_helper.v"
coqc ... -Q "$ORIG" "" -R "$GEN" "$LP" "$GEN/digit_product_goal.v"
coqc ... -Q "$ORIG" "" -R "$GEN" "$LP" "$GEN/digit_product_proof_auto.v"
coqc ... -Q "$ORIG" "" -R "$GEN" "$LP" "$GEN/digit_product_proof_manual.v"
coqc ... -Q "$ORIG" "" -R "$GEN" "$LP" "$GEN/digit_product_goal_check.v"
```

- Why this fixed it: the proof obligations were already solved; the failure was only that the helper lived under `coq/deps/`, which neither the bare audit replay nor the standard `-Q "$ORIG" "" -R "$GEN" "$LP"` compile uses for a short-name `Require Import`. Moving a source copy onto the unprefixed workspace path makes `digit_product_helper` resolve without changing the function contract, executable C, or any generated theorem statements.
- Result: the full documented replay compiled `original/digit_product.v`, `original/digit_product_helper.v`, `digit_product_goal.v`, `digit_product_proof_auto.v`, `digit_product_proof_manual.v`, and `digit_product_goal_check.v` successfully. After that replay, non-`.v` artifacts under `coq/` were deleted again so the workspace returned to the required clean state.
