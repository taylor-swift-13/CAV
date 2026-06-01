# Exercism Armstrong Number Bool

## Problem

Return true if `n` is an Armstrong number.

## Requirements

- `n >= 0`.
- Use the decimal digit count as the exponent.

## Source

- Source: Exercism problem `armstrong-numbers`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/armstrong-numbers
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_armstrong_number_bool(n: i32) -> bool {
    let mut tmp = n; let mut digits = 0; if tmp == 0 { digits = 1; } while tmp > 0 { digits += 1; tmp /= 10; }
    tmp = n; let mut sum = 0; while tmp > 0 { let d = tmp % 10; let mut p = 1; let mut i = 0; while i < digits { p *= d; i += 1; } sum += p; tmp /= 10; }
    sum == n
}
```
