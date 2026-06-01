# LC Island Perimeter Rows

## Problem

Return the perimeter of land cells in a semicolon-separated 0/1 grid.

## Requirements

- Rows contain only `0` and `1`.
- All rows have equal positive length.

## Source

- Source: LeetCode problem `island-perimeter`.
- URL: https://leetcode.com/problems/island-perimeter/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_island_perimeter_rows(rows: &str) -> i32 {
    let g: Vec<&[u8]> = rows.split(';').map(|s| s.as_bytes()).collect(); let r = g.len(); let c = g[0].len(); let mut ans = 0; let mut i = 0usize; while i < r { let mut j = 0usize; while j < c { if g[i][j] == b'1' { ans += 4; if i > 0 && g[i - 1][j] == b'1' { ans -= 2; } if j > 0 && g[i][j - 1] == b'1' { ans -= 2; } } j += 1; } i += 1; } ans
}
```
