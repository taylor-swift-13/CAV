# LC Count Servers That Communicate Rows

## Problem

Return how many servers can communicate with at least one other server in the same row or column.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.

## Source

- Source: LeetCode problem `count-servers-that-communicate`.
- URL: https://leetcode.com/problems/count-servers-that-communicate/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_count_servers_rows(rows: &str) -> i32 {
    let g: Vec<&[u8]> = rows.split(';').map(|s| s.as_bytes()).collect(); let r = g.len(); let c = g[0].len(); let mut row = vec![0; r]; let mut col = vec![0; c]; let mut i = 0usize; while i < r { let mut j = 0usize; while j < c { if g[i][j] == b'1' { row[i] += 1; col[j] += 1; } j += 1; } i += 1; } let mut ans = 0; i = 0; while i < r { let mut j = 0usize; while j < c { if g[i][j] == b'1' && (row[i] > 1 || col[j] > 1) { ans += 1; } j += 1; } i += 1; } ans
}
```
