# LC Wiggle Subsequence Max Length CSV

## Problem

Return the length of the longest wiggle subsequence.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.

## Source

- Source: LeetCode problem `wiggle-subsequence`.
- URL: https://leetcode.com/problems/wiggle-subsequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_wiggle_max_length_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut up = 1; let mut down = 1; let mut i = 1usize; while i < a.len() { if a[i] > a[i - 1] { up = down + 1; } else if a[i] < a[i - 1] { down = up + 1; } i += 1; } up.max(down)
}
```
