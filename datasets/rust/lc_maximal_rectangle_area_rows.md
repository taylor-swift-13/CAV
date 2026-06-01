# LC Maximal Rectangle Area Rows

## Problem

Return the area of the largest all-1 rectangle in a semicolon-separated binary matrix.

## Requirements

- Rows contain only `0` and `1`.
- All rows have equal positive length.
- The empty string returns `0`.

## Source

- Source: LeetCode problem `maximal-rectangle`.
- URL: https://leetcode.com/problems/maximal-rectangle/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_maximal_rectangle_area_rows(rows: &str) -> i32 {
    if rows.is_empty() { return 0; } let rs: Vec<&[u8]> = rows.split(';').map(|s| s.as_bytes()).collect(); let c = rs[0].len(); let mut h = vec![0i32; c]; let mut best = 0;
    for row in rs { let mut j = 0usize; while j < c { h[j] = if row[j] == b'1' { h[j] + 1 } else { 0 }; j += 1; } let mut st: Vec<usize> = Vec::new(); j = 0; while j <= c { let cur = if j == c { 0 } else { h[j] }; while !st.is_empty() && h[*st.last().unwrap()] > cur { let idx = st.pop().unwrap(); let left = if st.is_empty() { -1 } else { *st.last().unwrap() as i32 }; let area = h[idx] * (j as i32 - left - 1); if area > best { best = area; } } st.push(j); j += 1; } }
    best
}
```
