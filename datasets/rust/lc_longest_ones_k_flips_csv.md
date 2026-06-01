# LC Max Consecutive Ones III Length CSV

## Problem

Return the longest subarray of ones after flipping at most `k` zeroes.

## Requirements

- `nums` is a comma-separated list containing only `0` and `1`.

## Source

- Source: LeetCode problem `max-consecutive-ones-iii`.
- URL: https://leetcode.com/problems/max-consecutive-ones-iii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_longest_ones_k_flips_csv(nums: &str, k: i32) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut left = 0usize; let mut zeros = 0; let mut best = 0; let mut right = 0usize; while right < a.len() { if a[right] == 0 { zeros += 1; } while zeros > k { if a[left] == 0 { zeros -= 1; } left += 1; } let len = (right - left + 1) as i32; if len > best { best = len; } right += 1; } best
}
```
