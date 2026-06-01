# LC Combination Sum IV Count CSV

## Problem

Return the number of ordered combinations from `nums` that sum to `target`.

## Requirements

- `nums` is a nonempty comma-separated list of positive distinct integers.
- `target >= 0`.
- The count fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `combination-sum-iv`.
- URL: https://leetcode.com/problems/combination-sum-iv/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_combination_sum4_count_csv(nums: &str, target: i32) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut dp = vec![0; (target + 1) as usize]; dp[0] = 1;
    let mut s = 1; while s <= target { for &v in &a { if s >= v { dp[s as usize] += dp[(s - v) as usize]; } } s += 1; } dp[target as usize]
}
```
