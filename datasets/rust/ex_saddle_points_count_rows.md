# Exercism Saddle Points Count Rows

## Problem

Count saddle points in an integer matrix.

## Requirements

- Rows are semicolon-separated and values inside a row are comma-separated.
- A saddle point is at least every value in its row and at most every value in its column.

## Source

- Source: Exercism problem `saddle-points`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/saddle-points
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_saddle_points_count_rows(rows: &str) -> i32 {
    let a: Vec<Vec<i32>> = rows.split(';').map(|r| r.split(',').map(|x| x.parse::<i32>().unwrap()).collect()).collect(); let r = a.len(); let c = a[0].len(); let mut ans = 0;
    let mut i = 0usize; while i < r { let mut j = 0usize; while j < c { let mut ok = true; let mut y = 0usize; while y < c { if a[i][y] > a[i][j] { ok = false; } y += 1; } let mut x = 0usize; while x < r { if a[x][j] < a[i][j] { ok = false; } x += 1; } if ok { ans += 1; } j += 1; } i += 1; } ans
}
```
