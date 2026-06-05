# Nonnegative scalar doubling: solve the overflow promise into a direct input cap

Symptom:

- The implementation is a straight-line scalar function such as `return n + n;`.
- The raw statement gives both:
  - an input-side semantic restriction such as `n >= 0`;
  - a promise that the returned mathematical result fits in signed 32-bit `int`.
- A first-pass contract is tempted to restate the result-fit promise literally, for example:
  - `n + n <= 2147483647`

Cause:

- For this shape, the safety obligation is really about the executable C expression `n + n`.
- Keeping the precondition in the same derived expression shape is logically fine, but it is less direct than the actual safe input domain.
- For monotone scalar arithmetic on a restricted sign domain, the overflow promise can often be solved exactly into a simple bound on the input.

Rule:

- When the function is straight-line scalar arithmetic and the raw problem already fixes a sign/domain restriction, solve the result-fit promise into the smallest direct input bound you can express in linear integer arithmetic.
- For `n >= 0` and `return n + n`, use:
  - `0 <= n`
  - `n <= 1073741823`
- Keep the postcondition exact:
  - `__return == n@pre + n@pre`
- If the result is semantically constrained to stay nonnegative, state that directly in `Ensure`; it is cheap and keeps eval mechanical.

Minimal shape:

```c
int double_nonnegative(int n)
/*@ Require
      0 <= n &&
      n <= 1073741823 &&
      emp
    Ensure
      __return == n@pre + n@pre &&
      0 <= __return &&
      emp
*/
```

Why this shape is better:

- It describes the real safe input domain, instead of restating a derived arithmetic promise.
- The bound is literal-only and QCP-friendly.
- Eval can hit the exact boundary with a concrete positive case (`1073741823`) and the first unsafe point with a concrete negative case (`1073741824`).

Scope:

- Loop-free scalar functions whose body is a fixed arithmetic expression over `int` inputs.
- Especially useful when the raw statement says the mathematical result fits in signed `int`, and that promise can be algebraically solved into a direct bound on one input.
