# LC Search A 2D Matrix Bool Rows

## Problem

Return true if `target` appears in a row-major sorted matrix.

## Requirements

- Rows are semicolon-separated.
- Numbers inside each row are comma-separated signed integers.

## Source

- Source: LeetCode problem `search-a-2d-matrix`.
- URL: https://leetcode.com/problems/search-a-2d-matrix/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_search_matrix_bool_rows(rows: &str, target: i32) -> bool {
    let a: Vec<i32> = rows.split(|ch| ch == ',' || ch == ';').map(|x| x.parse::<i32>().unwrap()).collect(); let mut l = 0i32; let mut r = a.len() as i32 - 1; while l <= r { let m = l + (r - l) / 2; let v = a[m as usize]; if v == target { return true; } if v < target { l = m + 1; } else { r = m - 1; } } false
}
```
