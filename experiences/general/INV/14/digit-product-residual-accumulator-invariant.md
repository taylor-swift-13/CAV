# Scalar digit-product loops should keep a residual accumulator equation plus safety

Symptom:

- The loop mutates only scalar locals, repeatedly multiplies `product` by `n % 10`, and updates `n = n / 10`.
- A naive invariant such as `0 <= n`, `0 <= product`, or even `product <= digit_product_z(n@pre)` is too weak: it does not explain how the current residual `n` and current accumulator `product` still combine to the final postcondition.
- `symexec` then fails at the loop head with missing assertions, or later generates return/preservation witnesses that have no direct bridge back to `digit_product_z(n@pre)`.

Cause:

- This loop is not a pure "prefix summary" over immutable external data. The remaining semantic work is stored inside the current scalar `n`.
- Each iteration consumes one decimal digit and shrinks `n` by quotienting by `10`, so the stable summary is not just the current `product`, but "running accumulator applied to the remaining suffix of digits".
- If the contract also tracks signed-overflow safety, the loop invariant must preserve that residual safety fact too; a final-range-only fact is not enough.

Rule:

- Introduce helper wrappers for the residual semantic summary and residual safety predicate if the raw fuelled definitions are too awkward for C annotations.
- Keep the loop summary as a residual equation of the form:
  `digit_product_acc_z(n, product) == digit_product_z(n@pre)`.
- Pair it with the safety fact for the current residual state:
  `digit_product_safe_z(n, product)`.
- Also retain the cheap numeric facts the generated witnesses need:
  `0 <= n` and `0 <= product`.
- On loop exit, `0 <= n` together with `!(n > 0)` gives `n == 0`, so the residual equation collapses directly to `product == digit_product_z(n@pre)`.

Minimal shape:

```c
/*@ Inv
      0 <= n &&
      0 <= product &&
      digit_product_safe_z(n, product) &&
      digit_product_acc_z(n, product) == digit_product_z(n@pre)
*/
while (n > 0) {
  ...
}
```

Scope:

- `problem_kind = product`
- `data = scalar`
- `pattern = single_loop`
- Loops that repeatedly consume low-order decimal digits from a nonnegative scalar while multiplying an accumulator and where correctness and overflow safety both depend on the residual state
