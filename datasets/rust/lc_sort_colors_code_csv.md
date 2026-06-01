# LC Sort Colors Code CSV

## Problem

Sort comma-separated colors `0`, `1`, and `2`, then return the decimal code formed by the sorted colors.

## Requirements

- This scalar return is a deterministic encoding of the original sorted-array output.
- The supplied arrays have at most 9 elements.

## Source

- Source: LeetCode problem `sort-colors`.
- URL: https://leetcode.com/problems/sort-colors/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_sort_colors_code_csv(colors: &str) -> i32 {
    let mut cnt = [0; 3]; for p in colors.split(',') { cnt[p.parse::<usize>().unwrap()] += 1; } let mut code = 0; let mut v = 0usize; while v < 3 { let mut k = 0; while k < cnt[v] { code = code * 10 + v as i32; k += 1; } v += 1; } code
}
```
