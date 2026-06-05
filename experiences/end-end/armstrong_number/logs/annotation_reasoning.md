
## 2026-06-05T16:31:11+08:00

- Symptom: Initial symexec failed with `Lack of assertions in some paths for the loop` at annotated/verify_20260605_162851v_armstrong_number.c:22, which is the first digit-counting `while` loop.
- Location: annotated/verify_20260605_162851v_armstrong_number.c lines 22-40. The function has three loops with no `Inv`: digit-counting `while`, digit-sum `while`, and inner power `for`.
- Repair plan: add loop invariants that track the remaining quotient `temp`, the computed digit count, and the accumulated Armstrong sum. To keep the VC aligned with the provided spec in input/armstrong_number.v, use the imported Coq helpers for digit counting and digit-power summation rather than inventing a new contract.
- Why this shape: the first loop should establish `digits == count_digits_z(n)` once `temp` reaches 0; the second loop should express `sum + armstrong_sum_z(temp, digits) == armstrong_sum_z(n, digits)` so the exit state directly yields the final comparison against `is_armstrong_z(n)`. The inner `for` loop should maintain repeated multiplication for the current decimal digit.

## 2026-06-05T16:33:10+08:00

- Symptom: the inner power loop needs a semantic invariant for repeated multiplication, but the imported Coq helper `zpow_nat` takes a `nat` exponent.
- Location: annotated/verify_20260605_162851v_armstrong_number.c around the `for (int i = 0; i < digits; i++)` loop.
- Repair action: add a workspace-local helper module `output/verify_20260605_162851v_armstrong_number/coq/deps/armstrong_number_helper.v` defining `zpow_nat_z base exp := zpow_nat base (Z.to_nat exp)`, import it from the annotated C file, and use `zpow_nat_z` in the inner-loop invariant instead of direct `Z.to_nat(...)`.
- Why this shape: the parser-facing helper keeps the executable C and original spec unchanged, while making the invariant type-correct and parser-stable for the digit-power loop. The outer invariants can then talk directly about `count_digits_z`, `armstrong_sum_z`, and the digit power computed by the inner loop.

## 2026-06-05T16:34:50+08:00

- Symptom: `symexec` progressed past all loop heads but failed with `Fail to Remove Memory Permission of temp` at annotated/verify_20260605_162851v_armstrong_number.c:144, immediately after the outer digit-sum loop.
- Location: the bridge `Assert` after `while (temp > 0)` only summarized `n`, `digits`, and `sum`, but omitted the still-live local `temp`.
- Repair action: strengthen that post-loop `Assert` with the exit fact `temp == 0`.
- Why this change: for a `while` loop, the loop-local summary at the cutpoint must retain enough information to discharge local-store cleanup. This is the same class of control-point bug documented for post-inner-loop bridges; it is not a manual-proof issue.

## 2026-06-05T23:57:22+08:00

- Symptom: after successful `symexec`, the generated theorem `armstrong_number_entail_wit_5` in `coq/generated/armstrong_number_goal.v` requires proving `0 <= n_pre` and `n_pre <= 99999999` from an antecedent that only retained `digits == count_digits_z(n_pre)`, `sum == 0`, and the Armstrong-sum equality.
- Location: the bridge `Assert` after `temp = n; int sum = 0;` in `annotated/verify_20260605_162851v_armstrong_number.c`.
- Repair action: strengthen that bridge `Assert` by carrying forward the numeric bounds `0 <= n` and `n <= 99999999` in addition to `n == n@pre`.
- Why this change: the second `while` invariant explicitly requires the original input range facts. If the bridge cuts them away, the resulting entailment VC is false as a pure theorem, so this must be repaired in annotation rather than in `proof_manual.v`.

## 2026-06-05T18:22:22+08:00

- Symptom: the generated theorem `armstrong_number_entail_wit_10` in `coq/generated/armstrong_number_goal.v` lost the semantic link between the current decimal digit and the power term, keeping only `0 <= d <= 9` and `p = zpow_nat_z(d, digits_2)`.
- Location: the bridge `Assert`, inner `for` invariant, and post-`for` `Assert` around `int d = temp % 10; int p = 1;` in `annotated/verify_20260605_162851v_armstrong_number.c`.
- Repair action: add `d == temp % 10` to those three annotation cutpoints.
- Why this change: `Assert` is a semantic reset point, and the current invariant only keeps the numeric range for `d`. The outer Armstrong-sum update needs the stronger consumed-digit equation to justify replacing the next-step contribution by `zpow_nat_z(temp % 10, digits)`. Preserving that equation in the annotation is cheaper and more accurate than trying to prove a witness whose premises no longer mention the consumed digit.

## 2026-06-05T18:22:22+08:00

- Symptom: after regenerating with `d == temp % 10`, the new `coq/generated/armstrong_number_goal.v` still allows impossible models for `entail_wit_10` because the second loop invariant only kept `0 <= temp`, not the program fact that repeated `/= 10` keeps `temp <= n@pre`.
- Location: both `while (temp > 0)` invariants in `annotated/verify_20260605_162851v_armstrong_number.c`, plus the bridge assert and inner-`for` cutpoints inside the second loop that currently restate only partial outer-loop facts.
- Repair action: carry `temp <= n@pre` through the digit-count loop invariant, the outer Armstrong-sum loop invariant, and the digit/power bridge assert, inner-loop invariant, and post-`for` assert.
- Why this change: the proof obligations for `count_digits_z_step` and `armstrong_sum_z` both rely on the decimal fuel matching the actual number of remaining digits. Since `temp` starts at `n` and only decreases by quotienting by `10`, `temp <= n@pre` is a real control-state invariant and should be preserved explicitly at every annotation cutpoint that can drop context.
