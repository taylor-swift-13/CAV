# LC Toeplitz Matrix Bool Rows

## Problem

Return true if every diagonal from top-left to bottom-right has the same value.

## Requirements

- Rows are semicolon-separated and values in a row are comma-separated.
- All rows have equal positive length.

## Source

- Source: LeetCode problem `toeplitz-matrix`.
- URL: https://leetcode.com/problems/toeplitz-matrix/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_toeplitz_matrix_bool_rows(rows: &str) -> bool {
    let a: Vec<Vec<i32>> = rows.split(';').map(|r| r.split(',').map(|x| x.parse::<i32>().unwrap()).collect()).collect(); let mut i = 1usize; while i < a.len() { let mut j = 1usize; while j < a[0].len() { if a[i][j] != a[i - 1][j - 1] { return false; } j += 1; } i += 1; } true
}
```
