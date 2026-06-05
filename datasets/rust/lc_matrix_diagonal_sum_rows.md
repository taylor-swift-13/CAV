# LC Matrix Diagonal Sum Rows

## Problem

Return the sum of both diagonals of a square matrix, counting the center once.

## Requirements

- Rows are semicolon-separated comma lists of integers.

## Source

- Source: LeetCode problem `matrix-diagonal-sum`.
- URL: https://leetcode.com/problems/matrix-diagonal-sum/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_matrix_diagonal_sum_rows(rows: &str) -> i32 {
    let a: Vec<Vec<i32>> = rows.split(';').map(|r| r.split(',').map(|x| x.parse::<i32>().unwrap()).collect()).collect(); let n = a.len(); let mut sum = 0; let mut i = 0usize; while i < n { sum += a[i][i]; if i != n - 1 - i { sum += a[i][n - 1 - i]; } i += 1; } sum
}
```
