# LC Number Of Provinces Rows

## Problem

Return the number of connected components in an adjacency matrix.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.
- The matrix is square.

## Source

- Source: LeetCode problem `number-of-provinces`.
- URL: https://leetcode.com/problems/number-of-provinces/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_number_of_provinces_rows(rows: &str) -> i32 {
    let g: Vec<&[u8]> = rows.split(';').map(|s| s.as_bytes()).collect(); let n = g.len(); let mut seen = vec![false; n]; let mut ans = 0; let mut s = 0usize; while s < n { if !seen[s] { ans += 1; let mut st = vec![s]; seen[s] = true; while let Some(v) = st.pop() { let mut to = 0usize; while to < n { if g[v][to] == b'1' && !seen[to] { seen[to] = true; st.push(to); } to += 1; } } } s += 1; } ans
}
```
