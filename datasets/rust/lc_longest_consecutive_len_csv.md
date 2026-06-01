# LC Longest Consecutive Sequence Length CSV

## Problem

Return the length of the longest consecutive integer run in a comma-separated list.

## Requirements

- The empty string returns `0`.
- Duplicate values do not extend a run.

## Source

- Source: LeetCode problem `longest-consecutive-sequence`.
- URL: https://leetcode.com/problems/longest-consecutive-sequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_longest_consecutive_len_csv(nums: &str) -> i32 {
    if nums.is_empty() { return 0; } let mut a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.sort();
    let mut best = 1; let mut cur = 1; let mut i = 1usize; while i < a.len() { if a[i] != a[i - 1] { if a[i] == a[i - 1] + 1 { cur += 1; } else { cur = 1; } if cur > best { best = cur; } } i += 1; }
    best
}
```
