# Issues Log

## Iteration 1: missing loop assertions blocked symexec

- Phenomenon: the first symbolic execution on `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_162058_add_digits.c` failed with `Error: Lack of assertions in some paths for the loop!`.
- Location: outer and inner `while` loops in [verify_20260604_162058_add_digits.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260604_162058_add_digits.c:14).
- Repair action: added an outer invariant preserving `digital_root_z(num)` and an inner invariant preserving `sum + digit_sum_z(num) == digit_sum_z(n0)` with explicit nonnegativity/range facts.
- Key snippet:
```c
/*@ Inv Assert
      exists n0,
        0 <= n0 &&
        n0 <= INT_MAX &&
        0 <= num &&
        num <= INT_MAX &&
        0 <= sum &&
        sum <= INT_MAX &&
        digital_root_z(n0) == digital_root_z(num@pre) &&
        sum + digit_sum_z(num) == digit_sum_z(n0) &&
        emp
*/
```
- Why this fixed it: `symexec` needed one preserved fact per loop boundary. The inner invariant captures the processed-digit / remaining-digit decomposition exactly, which is the semantic shape the generated VC uses.

## Iteration 2: inner-loop existential lost the `int` upper bound

- Phenomenon: generated `add_digits_safety_wit_4` required proving `sum + num % 10 <= INT_MAX`, but the first inner invariant version only preserved `0 <= n0`.
- Location: [add_digits_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_goal.v:65).
- Repair action: strengthened the outer and inner invariants with `num <= INT_MAX`, `n0 <= INT_MAX`, and `sum <= INT_MAX`.
- Key VC fragment:
```coq
“ (n0 <= INT_MAX) ”
...
“ ((sum + (num % ( 10 ) ) ) <= INT_MAX) ”
```
- Why this fixed it: the bounded-addition witness then reduced to pure arithmetic over the invariant instead of depending on hidden local-store range information for an existential witness.

## Iteration 3: false pure entry witness for `num_pre <= INT_MAX`

- Phenomenon: `coq/generated/add_digits_goal.v` generated a false pure theorem `0 <= num_pre |- num_pre <= INT_MAX` while initializing the strengthened outer invariant.
- Location: [add_digits_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_goal.v:155).
- Repair action: added `/*@ num <= INT_MAX by local */` immediately before the outer loop and reran `symexec`.
- Key annotation:
```c
/*@ num <= INT_MAX by local */
```
- Why this fixed it: the witness changed from a false pure arithmetic goal to a local-store range fact extracted from the typed C parameter, which Verify is allowed to preserve via annotations.

## Iteration 4: proof-level `%`/`rem`, `÷`/`/`, and branch-order mismatches

- Phenomenon: several `coqc` runs failed in `/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_proof_manual.v` on helper lemmas and witness proofs:
  - `Cannot find witness` inside helper lemmas using `Z.rem`/`Z.mod`
  - orientation mismatches such as `n / 10 = n ÷ 10`
  - wrong bullet assumptions about `entailer!` branch ordering
- Location:
  - helper lemmas `digit_sum_fuel_le`, `digit_sum_z_single_digit`, `digit_sum_z_lt_self_gt9`
  - witness lemmas `proof_of_add_digits_safety_wit_4`, `proof_of_add_digits_entail_wit_4`, `proof_of_add_digits_entail_wit_5`
- Repair action:
  - imported the stable `digit_sum` helper pattern from the allowed `experiences/end-end/digit_sum` case
  - added explicit bridges `symmetry; apply Z.rem_mod_nonneg` and `apply Z.quot_div_nonneg`
  - replayed `proof_of_add_digits_entail_wit_4` with `Show.` to confirm the exact post-`entailer!` goal order:
```text
goal 1: sum + num % 10 + digit_sum_z (num ÷ 10) = digit_sum_z n0_2
goal 2: sum + num % 10 <= 2147483647
goal 3: 0 <= sum + num % 10
goal 4: num ÷ 10 <= 2147483647
goal 5: 0 <= num ÷ 10
```
  - corrected `proof_of_add_digits_entail_wit_5` to rewrite `H7 : sum + digit_sum_z num = digit_sum_z n0` after deriving `num = 0`, not `H6`
- Why this fixed it: the manual proof now matches the exact generated witness structure instead of an assumed one, and every arithmetic bridge is proved in the operator orientation Coq actually expects.

## Final machine checks

- `symexec` rerun after the final annotation changes succeeded.
- `coqc` succeeded on:
  - `original/add_digits.v`
  - `coq/generated/add_digits_goal.v`
  - `coq/generated/add_digits_proof_auto.v`
  - `coq/generated/add_digits_proof_manual.v`
  - `coq/generated/add_digits_goal_check.v`
- Non-`.v` build artifacts under `coq/` were deleted after compilation.

Final Result: Success
