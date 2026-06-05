# LC Shortest Path Binary Matrix Rows

## Problem

Return the shortest 8-direction path length from top-left to bottom-right, or `-1`.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.
- `0` means open and `1` means blocked.

## Source

- Source: LeetCode problem `shortest-path-in-binary-matrix`.
- URL: https://leetcode.com/problems/shortest-path-in-binary-matrix/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_shortest_path_binary_matrix_rows(rows: &str) -> i32 {
    let mut g: Vec<Vec<u8>> = rows.split(';').map(|s| s.as_bytes().to_vec()).collect(); let n = g.len(); let c = g[0].len(); if g[0][0] == b'1' || g[n - 1][c - 1] == b'1' { return -1; } let dirs = [(1i32,-1i32),(1,0),(1,1),(0,-1),(0,1),(-1,-1),(-1,0),(-1,1)]; let mut q = vec![(0usize,0usize,1i32)]; let mut head = 0usize; g[0][0] = b'1'; while head < q.len() { let (x,y,d) = q[head]; head += 1; if x == n - 1 && y == c - 1 { return d; } for &(dx,dy) in dirs.iter() { let nx = x as i32 + dx; let ny = y as i32 + dy; if nx >= 0 && nx < n as i32 && ny >= 0 && ny < c as i32 && g[nx as usize][ny as usize] == b'0' { g[nx as usize][ny as usize] = b'1'; q.push((nx as usize, ny as usize, d + 1)); } } } -1
}
```
