# Issues Log

## Issue 1: Coq `%` notation is `Z.rem`, not `Z.mod`

- **Location**: `p138_is_equal_to_sum_even_proof_manual.v`, return_wit_1
- **Phenomenon**: `assert (n_pre mod 2 = 0)` failed to match hypothesis `H : n_pre % 2 <> 0`
- **Root cause**: `IntLib.v` defines `%` as `Z.rem`, while `mod` is `Z.mod`
- **Fix**: Use `%` consistently with hypotheses; use `Z.rem_mul` instead of `Z.mod_mul`

## Issue 2: `Z.quot_exact` gives `<->`, requires destruct + apply

- **Location**: `p138_is_equal_to_sum_even_proof_manual.v`, return_wit_3
- **Phenomenon**: `apply Z.quot_exact` directly failed because it produces a conjunction
- **Fix**: `destruct Hq as [Hq1 Hq2]; apply Hq2; exact H0`

## Issue 3: `lia` vs `nia` on equality goals

- **Location**: `p138_is_equal_to_sum_even_proof_manual.v`, return_wit_3
- **Phenomenon**: `lia` failed on `n_pre = 2 + 2 + 2 + (n_pre - 6)`
- **Fix**: Use `nia` for the pure arithmetic equality goal
