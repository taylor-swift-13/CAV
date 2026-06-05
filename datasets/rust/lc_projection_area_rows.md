# LC Projection Area 3D Shapes Rows

## Problem

Return the total projection area of a 3D shape grid.

## Requirements

- Rows are semicolon-separated comma lists of nonnegative heights.

## Source

- Source: LeetCode problem `projection-area-of-3d-shapes`.
- URL: https://leetcode.com/problems/projection-area-of-3d-shapes/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_projection_area_rows(rows: &str) -> i32 {
    let a: Vec<Vec<i32>> = rows.split(';').map(|r| r.split(',').map(|x| x.parse::<i32>().unwrap()).collect()).collect(); let r = a.len(); let c = a[0].len(); let mut xy = 0; let mut yz = 0; let mut zx = 0; let mut i = 0usize; while i < r { let mut row_max = 0; let mut j = 0usize; while j < c { if a[i][j] > 0 { xy += 1; } if a[i][j] > row_max { row_max = a[i][j]; } j += 1; } yz += row_max; i += 1; } let mut j = 0usize; while j < c { let mut col_max = 0; i = 0; while i < r { if a[i][j] > col_max { col_max = a[i][j]; } i += 1; } zx += col_max; j += 1; } xy + yz + zx
}
```
