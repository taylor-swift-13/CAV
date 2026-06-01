# Exercism Matrix Row Sum

## Problem

Return the sum of a one-based row from a matrix string.

## Requirements

- Rows are semicolon-separated and values inside a row are comma-separated.
- `row` is one-based.

## Source

- Source: Exercism problem `matrix`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/matrix
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_matrix_row_sum(rows: &str, row: i32) -> i32 {
    rows.split(';').nth((row - 1) as usize).unwrap().split(',').map(|x| x.parse::<i32>().unwrap()).sum()
}
```
