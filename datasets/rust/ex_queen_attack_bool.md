# Exercism Queen Attack Bool

## Problem

Return true if two queens can attack each other.

## Requirements

- Coordinates are zero-based row/column pairs.
- Queens attack along the same row, column, or diagonal.

## Source

- Source: Exercism problem `queen-attack`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/queen-attack
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_queen_attack_bool(r1: i32, c1: i32, r2: i32, c2: i32) -> bool {
    r1 == r2 || c1 == c2 || (r1 - r2).abs() == (c1 - c2).abs()
}
```
