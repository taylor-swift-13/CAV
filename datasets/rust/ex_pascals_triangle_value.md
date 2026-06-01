# Exercism Pascal Triangle Value

## Problem

Return the value at zero-based `row` and `col` in Pascal's triangle.

## Requirements

- `0 <= col <= row <= 30`.
- The result fits in signed 32-bit integer range.

## Source

- Source: Exercism problem `pascals-triangle`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/pascals-triangle
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_pascals_triangle_value(row: i32, col: i32) -> i32 {
    let mut v = [[0i32; 31]; 31];
    let mut i = 0;
    while i <= row { v[i as usize][0] = 1; v[i as usize][i as usize] = 1; let mut j = 1; while j < i { v[i as usize][j as usize] = v[(i - 1) as usize][(j - 1) as usize] + v[(i - 1) as usize][j as usize]; j += 1; } i += 1; }
    v[row as usize][col as usize]
}
```
