# Exercism Allergies Score Count

## Problem

Return how many of the standard 8 allergy flags are present in `score`.

## Requirements

- Use bit positions 0 through 7 only.
- `score >= 0`.

## Source

- Source: Exercism problem `allergies`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/allergies
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_allergies_score_count(score: i32) -> i32 {
    let mut count = 0;
    let mut i = 0;
    while i < 8 { if (score & (1 << i)) != 0 { count += 1; } i += 1; }
    count
}
```
