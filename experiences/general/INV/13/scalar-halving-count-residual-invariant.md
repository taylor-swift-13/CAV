# Scalar halving count loops should keep "counted so far + bits remaining"

Symptom:

- The loop mutates only scalar locals, repeatedly tests `n % 2`, increments `count`, and updates `n = n / 2`.
- A naive invariant like `0 <= count` or even `count <= count_set_bits_z(n@pre)` is too weak: it does not explain how the current `n` still contributes to the final answer.
- The return witness then has no direct bridge from the loop state back to `__return == count_set_bits_z(n@pre)`.

Cause:

- This loop is not a plain prefix-summary over an external array. The remaining semantic work is stored in the current scalar `n` itself.
- Each iteration consumes one low bit and replaces `n` by its quotient by `2`, so the stable quantity is "bits already counted + bits still present in current `n`".

Rule:

- Keep the loop summary as a residual equation:
  `count + count_set_bits_z(n) == count_set_bits_z(n@pre)`.
- Pair it with the cheap numeric facts that generated quotient and safety witnesses need:
  `0 <= n`, `n <= n@pre`, and `0 <= count`.
- On loop exit, restate the same summary plus `n <= 0`; this lets the return proof collapse once `count_set_bits_z(n) = 0`.

Minimal shape:

```c
/*@ Inv
      0 <= n &&
      n <= n@pre &&
      0 <= count &&
      count + count_set_bits_z(n) == count_set_bits_z(n@pre)
*/
while (n > 0) {
  ...
}

/*@ Assert
      n <= 0 &&
      0 <= count &&
      count + count_set_bits_z(n) == count_set_bits_z(n@pre)
*/
```

Scope:

- `problem_kind = count`
- `data = scalar`
- `pattern = single_loop`
- Loops that repeatedly shrink the current scalar state (for example by division) while accumulating part of the final answer
