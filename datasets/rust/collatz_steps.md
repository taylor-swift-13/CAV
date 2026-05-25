# collatz_steps

## Problem

Return the number of Collatz steps needed for positive integer `n` to reach 1.

## Requirements

- Implement exactly the named function shown in the reference implementation.
- Use only the language standard library.
- The function must be deterministic and must not read stdin or write stdout.
- Inputs satisfy the stated problem preconditions; behavior outside those preconditions is intentionally unspecified.

## Source

- Source: Exercism practice exercise `collatz-conjecture`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/collatz-conjecture
- License note: prompt rewrite and implementations are local; upstream inspiration is Exercism MIT licensed.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn collatz_steps(mut n: i32) -> i32 {
    let mut steps = 0;
    while n != 1 {
        if n % 2 == 0 { n /= 2; }
        else { n = 3 * n + 1; }
        steps += 1;
    }
    steps
}
```
