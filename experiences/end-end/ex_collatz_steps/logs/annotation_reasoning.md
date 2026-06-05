# Annotation Reasoning

## Iteration 1: add loop invariant for remaining fuel and accumulated steps

- Phenomenon: the first `symexec` run on `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_073258v_ex_collatz_steps.c` failed with `Error: Lack of assertions in some paths for the loop!` at the only loop `while (x != 1)`.
- Location: `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_073258v_ex_collatz_steps.c`, target function `ex_collatz_steps`, loop head around line 23.
- Repair action: add one loop invariant that preserves:
  - the processed-step counter bounds `0 <= steps <= fuel`,
  - the original parameter equality `n == n@pre`,
  - the remaining Collatz safety obligation `ex_collatz_safe_fuel(x, fuel - steps)`,
  - the semantic decomposition `steps + ex_collatz_steps_fuel(x, fuel - steps) == ex_collatz_steps_fuel(n@pre, fuel)`.
- Key annotation snippet:

```c
/*@ Inv
      n == n@pre &&
      0 <= steps &&
      steps <= fuel &&
      ex_collatz_safe_fuel(x, fuel - steps) &&
      steps + ex_collatz_steps_fuel(x, fuel - steps) == ex_collatz_steps_fuel(n@pre, fuel)
*/
while (x != 1) {
```

- Why this fix: the contract already gives a fuel-bounded recursive model. At the loop head, `steps` is the prefix length already executed and `fuel - steps` is the remaining budget for current state `x`. The invariant exactly matches the one-step operational shape of the body: one branch replaces `x` by the next Collatz state and increments `steps` by 1. Keeping `n == n@pre` avoids current-vs-pre witness pollution in the return VC. At loop exit, `x == 1` makes `ex_collatz_steps_fuel(x, fuel - steps)` reduce to `0`, so the invariant should directly imply `steps == ex_collatz_steps_fuel(n@pre, fuel)`.
