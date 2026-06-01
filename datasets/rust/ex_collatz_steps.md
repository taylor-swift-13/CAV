# Exercism Collatz Steps

## Problem

Return the number of Collatz steps needed to reach `1`.

## Requirements

- `n > 0`.
- Intermediate values fit in signed 64-bit integer range.

## Source

- Source: Exercism problem `collatz-conjecture`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/collatz-conjecture
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_collatz_steps(n: i32) -> i32 {
    let mut x = n as i64; let mut steps = 0; while x != 1 { if x % 2 == 0 { x /= 2; } else { x = 3 * x + 1; } steps += 1; } steps
}
```
