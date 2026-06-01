# LC Rotting Oranges Minutes Rows

## Problem

Return the minimum minutes until no fresh orange remains, or `-1` if impossible.

## Requirements

- Rows are semicolon-separated strings of digits.
- `0` is empty, `1` fresh, and `2` rotten.

## Source

- Source: LeetCode problem `rotting-oranges`.
- URL: https://leetcode.com/problems/rotting-oranges/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_rotting_oranges_minutes_rows(rows: &str) -> i32 {
    let mut g: Vec<Vec<u8>> = rows.split(';').map(|s| s.as_bytes().to_vec()).collect(); let r = g.len(); let c = g[0].len(); let mut fresh = 0; let mut q: Vec<(usize,usize,i32)> = Vec::new(); let mut i = 0usize; while i < r { let mut j = 0usize; while j < c { if g[i][j] == b'1' { fresh += 1; } if g[i][j] == b'2' { q.push((i,j,0)); } j += 1; } i += 1; } let dirs = [(1i32,0i32),(-1,0),(0,1),(0,-1)]; let mut head = 0usize; let mut minutes = 0; while head < q.len() { let (x,y,t) = q[head]; head += 1; if t > minutes { minutes = t; } for &(dx,dy) in dirs.iter() { let nx = x as i32 + dx; let ny = y as i32 + dy; if nx >= 0 && nx < r as i32 && ny >= 0 && ny < c as i32 && g[nx as usize][ny as usize] == b'1' { g[nx as usize][ny as usize] = b'2'; fresh -= 1; q.push((nx as usize, ny as usize, t + 1)); } } } if fresh == 0 { minutes } else { -1 }
}
```
