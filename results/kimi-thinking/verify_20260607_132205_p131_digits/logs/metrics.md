# metrics.md for p131_digits

- **Target**: p131_digits
- **Symexec**: succeeded on annotated C with loop invariant using `digits_state`
- **Generated VCs**: `goal.v`, `proof_auto.v`, `proof_manual.v`, `goal_check.v`
- **Manual obligations**: `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, `entail_wit_2_3`, `entail_wit_2_4`, `return_wit_1`, `return_wit_2`
- **Blocker**: `entail_wit_2_1` (and `entail_wit_2_2`) are mathematically false for single-digit inputs due to contract definition `digits_state(0, prod, 1) = 0` instead of `prod`.
- **Repairable within workspace**: No. Requires editing `input/humaneval/p131_digits.v` to fix the Coq spec.

Final Result: Fail
