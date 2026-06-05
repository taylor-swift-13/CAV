# LC Longest Turbulent Subarray Length CSV

## Problem

Return the length of the longest turbulent subarray.

## Requirements

- Adjacent comparisons must alternate between greater-than and less-than.

## Source

- Source: LeetCode problem `longest-turbulent-subarray`.
- URL: https://leetcode.com/problems/longest-turbulent-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_turbulent_subarray_len_csv(arr: &str) -> i32 {
    let a: Vec<i32> = arr.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut up = 1; let mut down = 1; let mut best = 1; let mut i = 1usize; while i < a.len() { if a[i] > a[i - 1] { up = down + 1; down = 1; } else if a[i] < a[i - 1] { down = up + 1; up = 1; } else { up = 1; down = 1; } best = best.max(up.max(down)); i += 1; } best
}
```
