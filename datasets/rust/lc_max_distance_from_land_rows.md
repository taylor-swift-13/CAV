# LC As Far From Land As Possible Rows

## Problem

Return the maximum Manhattan distance from any water cell to nearest land, or `-1` if no answer exists.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.
- `1` is land and `0` is water.

## Source

- Source: LeetCode problem `as-far-from-land-as-possible`.
- URL: https://leetcode.com/problems/as-far-from-land-as-possible/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_max_distance_from_land_rows(rows: &str) -> i32 {
    let mut g: Vec<Vec<u8>> = rows.split(';').map(|s| s.as_bytes().to_vec()).collect(); let r = g.len(); let c = g[0].len(); let mut q: Vec<(usize,usize,i32)> = Vec::new(); let mut water = 0; let mut i = 0usize; while i < r { let mut j = 0usize; while j < c { if g[i][j] == b'1' { q.push((i,j,0)); } else { water += 1; } j += 1; } i += 1; } if q.is_empty() || water == 0 { return -1; } let dirs = [(1i32,0i32),(-1,0),(0,1),(0,-1)]; let mut head = 0usize; let mut ans = 0; while head < q.len() { let (x,y,d) = q[head]; head += 1; if d > ans { ans = d; } for &(dx,dy) in dirs.iter() { let nx = x as i32 + dx; let ny = y as i32 + dy; if nx >= 0 && nx < r as i32 && ny >= 0 && ny < c as i32 && g[nx as usize][ny as usize] == b'0' { g[nx as usize][ny as usize] = b'1'; q.push((nx as usize, ny as usize, d + 1)); } } } ans
}
```
