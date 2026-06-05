# Fixed-width bit-scan loops should summarize the processed prefix with a low-bit mask

Symptom:

- The loop keeps the input scalar unchanged, advances an index `i` through a fixed range such as `0 .. 7`, and conditionally increments `count` from tests like `(score & (1 << i)) != 0`.
- A naive invariant such as `0 <= count <= i` is too weak: it records progress but not which bits have already been accounted for.
- `symexec` then either rejects the loop for missing assertions or leaves preservation / return witnesses with no direct bridge to the final bit-count spec.

Cause:

- This is not the same shape as a residual loop that shrinks `n` by division. The remaining work is not stored in a changing scalar state.
- The stable summary is instead: "the current accumulator equals the specification applied to exactly the low-bit prefix already scanned".
- A low-bit mask isolates that prefix in a form that remains executable in C annotations and matches the branch condition on `1 << i`.

Rule:

- Keep the loop summary as a prefix-mask equation:
  `count == spec(score & ((1 << i) - 1))`.
- Also retain the cheap facts the generated VCs need:
  `0 <= i <= WIDTH`, `0 <= count <= i`, and `score == score@pre`.
- On loop exit, instantiate `i == WIDTH` and restate the summary against the full input, so the return witness can target the postcondition directly.

Minimal shape:

```c
/*@ Inv
      0 <= i && i <= 8 &&
      score == score@pre &&
      0 <= count && count <= i &&
      count == ex_allergies_score_count_spec(score & ((1 << i) - 1)) &&
      emp
*/
for (i = 0; i < 8; i++) {
  ...
}

/*@ Assert
      i == 8 &&
      score == score@pre &&
      0 <= count &&
      count == ex_allergies_score_count_spec(score) &&
      emp
*/
```

Scope:

- `problem_kind = count`
- `data = scalar`
- `pattern = single_loop`
- Fixed-width bit-scan loops over an unchanged nonnegative scalar where each iteration decides whether to add one contribution from bit `i`
