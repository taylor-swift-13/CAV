# LC Kth Smallest Matrix Rows

## Problem

Return the `k`th smallest element in a sorted matrix.

## Requirements

- Rows are semicolon-separated comma lists.
- Rows and columns are sorted ascending.

## Source

- Source: LeetCode problem `kth-smallest-element-in-a-sorted-matrix`.
- URL: https://leetcode.com/problems/kth-smallest-element-in-a-sorted-matrix/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_kth_smallest_matrix_rows(rows: &str, k: i32) -> i32 {
    let mut a: Vec<i32> = rows.split(|ch| ch == ',' || ch == ';').map(|x| x.parse::<i32>().unwrap()).collect(); a.sort(); a[k as usize - 1]
}
```
