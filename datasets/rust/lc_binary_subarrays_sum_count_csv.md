# LC Binary Subarrays With Sum Count CSV

## Problem

Return how many nonempty contiguous subarrays have sum exactly `goal`.

## Requirements

- `nums` is a comma-separated binary array.

## Source

- Source: LeetCode problem `binary-subarrays-with-sum`.
- URL: https://leetcode.com/problems/binary-subarrays-with-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_binary_subarrays_sum_count_csv(nums: &str, goal: i32) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut ans = 0; let mut l = 0usize; while l < a.len() { let mut sum = 0; let mut r = l; while r < a.len() { sum += a[r]; if sum == goal { ans += 1; } r += 1; } l += 1; } ans
}
```
