# issues.md for p131_digits

## Issue: Contract definition `digits_state` is incompatible with loop invariant semantics

### Symptom
After adding a loop invariant using `digits_state(n@pre, 1, 0) == digits_state(n, prod, has)`, symexec generates the VC file successfully, but the generated `entail_wit_2_1` (and related entail witnesses) contain goals that are mathematically false for single-digit inputs (e.g., n=5).

### Root cause
The Coq contract in `input/humaneval/p131_digits.v` defines:
```coq
Definition tail_odd_prod (n : Z) : Z :=
  tail_odd_prod_fuel (Z.to_nat n) n 1 0.

Definition digits_state (n prod has : Z) : Z :=
    if Z.eqb has 0 then tail_odd_prod n
    else prod * tail_odd_prod n.
```
For `n <= 0`, `tail_odd_prod n = 0`. Consequently, for `has = 1` and `n = 0`:
`digits_state(0, prod, 1) = prod * 0 = 0`.
But the correct accumulated result at loop exit (when `has = 1`) is `prod` (e.g., for input 5, `prod = 5`).

This makes the loop invariant preservation VC false. Specifically, in `entail_wit_2_1`:
- Antecedent: `digits_state(n_pre, 1, 0) = digits_state(n, prod, 0)` with `n > 0`, `has = 0`, `d = n % 10` odd.
- This gives `tail_odd_prod(n_pre) = tail_odd_prod(n)`.
- Consequent requires: `tail_odd_prod(n_pre) = digits_state(n/10, prod*d, 1)`.
- For `n = 5`: LHS = 5, RHS = `digits_state(0, 5, 1) = 5 * tail_odd_prod(0) = 0`.
- Goal becomes `5 = 0`, which is unprovable.

### Attempted fixes
1. Tried using `tail_odd_prod_fuel` directly with fuel `Z.to_nat(n)` or `to_nat(n)` in the annotation. The QCP parser rejects `Z.to_nat` ("undeclared identifier `Z`") and `to_nat` ("undeclared identifier `to_nat`"), because these are not declared via `Extern Coq` and the parser does not support module-qualified names.
2. Tried using a fixed `nat` literal fuel (e.g., `10`) in the annotation. The parser rejects it because integer literals are typed as `Z`, not `nat`.
3. Tried using only `digits_state` in the invariant. This generates VCs but they are false as shown above.
4. Considered adding a helper Coq module, but the workspace load paths are fixed by the runner and editing `input/` or `QualifiedCProgramming/` is forbidden.

### Conclusion
The contract definition `digits_state` is fundamentally flawed for use as a loop invariant in this program: it conflates the "no odd digits" base case (return 0) with the intermediate state where odd digits have been accumulated (`has = 1`). Fixing this requires changing the Coq specification in `input/humaneval/p131_digits.v` (e.g., making `tail_odd_prod(0) = 1` and handling the all-even case at the top level, or redefining `digits_state` to treat `n <= 0` specially when `has = 1`). This is outside the allowed write boundary.

- **Gate blocked at**: `entail_wit_2_1` / `entail_wit_2_2` in `coq/generated/p131_digits_goal.v`
- **Next step for contract stage**: Fix `digits_state` or `tail_odd_prod_fuel` definition in `input/humaneval/p131_digits.v` so that intermediate state with `has = 1` and `n = 0` evaluates to `prod` rather than `0`.
