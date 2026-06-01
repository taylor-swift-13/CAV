# Exercism Darts Score

## Problem

Return the dart score for integer coordinates using radii 1, 5, and 10.

## Requirements

- Coordinates are integer grid points.
- Use squared-distance comparisons to avoid floating point.

## Source

- Source: Exercism problem `darts`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/darts
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_darts_score(x: i32, y: i32) -> i32 {
    let d = x * x + y * y; if d <= 1 { 10 } else if d <= 25 { 5 } else if d <= 100 { 1 } else { 0 }
}
```
