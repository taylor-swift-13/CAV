# LC Number Of Islands Rows

## Problem

Count 4-directionally connected islands of `1` cells in a semicolon-separated binary grid.

## Requirements

- Rows contain only `0` and `1`.
- All rows have equal positive length.
- The empty string returns `0`.

## Source

- Source: LeetCode problem `number-of-islands`.
- URL: https://leetcode.com/problems/number-of-islands/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_number_of_islands_rows(rows: &str) -> i32 {
    if rows.is_empty() { return 0; } let mut g: Vec<Vec<u8>> = rows.split(';').map(|s| s.as_bytes().to_vec()).collect(); let r = g.len(); let c = g[0].len(); let mut ans = 0;
    let dirs = [(1i32,0i32),(-1,0),(0,1),(0,-1)]; let mut x = 0usize; while x < r { let mut y = 0usize; while y < c { if g[x][y] == b'1' { ans += 1; let mut st = vec![(x,y)]; g[x][y] = b'0'; while let Some((cx,cy)) = st.pop() { for (dx,dy) in dirs { let nx = cx as i32 + dx; let ny = cy as i32 + dy; if nx >= 0 && nx < r as i32 && ny >= 0 && ny < c as i32 && g[nx as usize][ny as usize] == b'1' { g[nx as usize][ny as usize] = b'0'; st.push((nx as usize, ny as usize)); } } } } y += 1; } x += 1; }
    ans
}
```
