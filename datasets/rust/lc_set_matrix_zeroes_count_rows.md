# LC Set Matrix Zeroes Count Rows

## Problem

Apply the set-matrix-zeroes rule to a semicolon-separated 0/1 matrix and return the final number of zero cells.

## Requirements

- Rows use comma-separated `0` or `1` values.
- All rows have equal positive length.

## Source

- Source: LeetCode problem `set-matrix-zeroes`.
- URL: https://leetcode.com/problems/set-matrix-zeroes/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_set_matrix_zeroes_count_rows(rows: &str) -> i32 {
    let rs: Vec<&str> = rows.split(';').collect(); let r = rs.len(); let c = rs[0].split(',').count(); let mut row = vec![false; r]; let mut col = vec![false; c];
    for (i, line) in rs.iter().enumerate() { for (j, part) in line.split(',').enumerate() { if part.parse::<i32>().unwrap() == 0 { row[i] = true; col[j] = true; } } }
    let mut zeros = 0; let mut i = 0usize; while i < r { let mut j = 0usize; while j < c { if row[i] || col[j] { zeros += 1; } j += 1; } i += 1; } zeros
}
```
