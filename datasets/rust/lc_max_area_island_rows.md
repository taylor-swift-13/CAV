# LC Max Area Of Island Rows

## Problem

Return the maximum area of a 4-directionally connected island in a 0/1 grid.

## Requirements

- Rows are semicolon-separated.
- Rows contain only `0` and `1`.

## Source

- Source: LeetCode problem `max-area-of-island`.
- URL: https://leetcode.com/problems/max-area-of-island/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_max_area_island_rows(rows: &str) -> i32 {
    let mut g: Vec<Vec<u8>> = rows.split(';').map(|s| s.as_bytes().to_vec()).collect(); let r = g.len(); let c = g[0].len(); let dirs = [(1i32,0i32),(-1,0),(0,1),(0,-1)]; let mut best = 0; let mut i = 0usize; while i < r { let mut j = 0usize; while j < c { if g[i][j] == b'1' { let mut area = 0; let mut st = vec![(i,j)]; g[i][j] = b'0'; while let Some((x,y)) = st.pop() { area += 1; for (dx,dy) in dirs { let nx = x as i32 + dx; let ny = y as i32 + dy; if nx >= 0 && nx < r as i32 && ny >= 0 && ny < c as i32 && g[nx as usize][ny as usize] == b'1' { g[nx as usize][ny as usize] = b'0'; st.push((nx as usize, ny as usize)); } } } if area > best { best = area; } } j += 1; } i += 1; } best
}
```
