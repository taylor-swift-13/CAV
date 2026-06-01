# FormalBench Grid Paths Mod

## Problem

Return the number of right/down paths from the top-left to bottom-right cell of a `rows` by `cols` grid, modulo `1000000007`.

## Requirements

- `0 <= rows, cols <= 30`.
- Return `0` if either dimension is `0`.
- A `1` by `1` grid has one path.

## Source

- Source: FormalBench problem `FormalBenchHF/base/programs/NcrModP.java`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: local rewrite from SESpec java_flat.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_ext_grid_paths_mod(rows: i32, cols: i32) -> i32 {
    if rows <= 0 || cols <= 0 { return 0; }
    let mut dp = [[0i32; 31]; 31];
    let mut i = 0;
    while i < rows { dp[i as usize][0] = 1; i += 1; }
    let mut j = 0;
    while j < cols { dp[0][j as usize] = 1; j += 1; }
    i = 1;
    while i < rows {
        j = 1;
        while j < cols {
            dp[i as usize][j as usize] = (dp[(i - 1) as usize][j as usize] + dp[i as usize][(j - 1) as usize]) % 1000000007;
            j += 1;
        }
        i += 1;
    }
    dp[(rows - 1) as usize][(cols - 1) as usize]
}
```
