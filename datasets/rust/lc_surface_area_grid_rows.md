# LC Surface Area 3D Shapes Rows

## Problem

Return the surface area of stacked cubes in a grid.

## Requirements

- Rows are semicolon-separated comma lists of nonnegative heights.

## Source

- Source: LeetCode problem `surface-area-of-3d-shapes`.
- URL: https://leetcode.com/problems/surface-area-of-3d-shapes/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_surface_area_grid_rows(rows: &str) -> i32 {
    let a: Vec<Vec<i32>> = rows.split(';').map(|r| r.split(',').map(|x| x.parse::<i32>().unwrap()).collect()).collect(); let r = a.len(); let c = a[0].len(); let mut area = 0; let mut i = 0usize; while i < r { let mut j = 0usize; while j < c { if a[i][j] > 0 { area += 2 + 4 * a[i][j]; if i > 0 { area -= 2 * a[i][j].min(a[i - 1][j]); } if j > 0 { area -= 2 * a[i][j].min(a[i][j - 1]); } } j += 1; } i += 1; } area
}
```
