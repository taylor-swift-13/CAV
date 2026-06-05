# LC Out Of Boundary Paths Count

## Problem

Return how many paths move out of grid boundary within at most `max_move` moves.

## Requirements

- Start at `(start_row,start_column)` in an `m x n` grid.
- Return the count modulo `1_000_000_007`.

## Source

- Source: LeetCode problem `out-of-boundary-paths`.
- URL: https://leetcode.com/problems/out-of-boundary-paths/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_out_boundary_paths_count(m: i32, n: i32, max_move: i32, start_row: i32, start_column: i32) -> i32 {
    let mm = m as usize; let nn = n as usize; let modu = 1000000007i32; let mut dp = vec![vec![0; nn]; mm]; dp[start_row as usize][start_column as usize] = 1; let dirs = [(1i32,0i32),(-1,0),(0,1),(0,-1)]; let mut ans = 0; let mut mv = 0; while mv < max_move { let mut next = vec![vec![0; nn]; mm]; let mut i = 0usize; while i < mm { let mut j = 0usize; while j < nn { if dp[i][j] != 0 { for &(dx,dy) in &dirs { let ni = i as i32 + dx; let nj = j as i32 + dy; if ni < 0 || ni >= m || nj < 0 || nj >= n { ans = (ans + dp[i][j]) % modu; } else { next[ni as usize][nj as usize] = (next[ni as usize][nj as usize] + dp[i][j]) % modu; } } } j += 1; } i += 1; } dp = next; mv += 1; } ans
}
```
