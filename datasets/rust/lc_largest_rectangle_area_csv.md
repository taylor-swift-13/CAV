# LC Largest Rectangle Area CSV

## Problem

Return the largest rectangle area in a histogram.

## Requirements

- `heights` is a nonempty comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `largest-rectangle-in-histogram`.
- URL: https://leetcode.com/problems/largest-rectangle-in-histogram/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_largest_rectangle_area_csv(heights: &str) -> i32 {
    let mut h: Vec<i32> = heights.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); h.push(0); let mut st: Vec<usize> = Vec::new(); let mut best = 0; let mut i = 0usize; while i < h.len() { while !st.is_empty() && h[*st.last().unwrap()] > h[i] { let height = h[st.pop().unwrap()]; let left = if st.is_empty() { -1 } else { *st.last().unwrap() as i32 }; let area = height * (i as i32 - left - 1); if area > best { best = area; } } st.push(i); i += 1; } best
}
```
