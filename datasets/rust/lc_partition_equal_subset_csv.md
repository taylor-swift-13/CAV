# LC Partition Equal Subset CSV

## Problem

Return true if comma-separated positive integers can be partitioned into two subsets with equal sum.

## Requirements

- The empty string returns false.
- The total sum is at most `2000`.

## Source

- Source: LeetCode problem `partition-equal-subset-sum`.
- URL: https://leetcode.com/problems/partition-equal-subset-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_partition_equal_subset_csv(nums: &str) -> bool {
    if nums.is_empty() { return false; }
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut sum = 0; for &v in &a { sum += v; }
    if sum % 2 != 0 { return false; }
    let target = (sum / 2) as usize; let mut dp = vec![false; target + 1]; dp[0] = true;
    for &v in &a { let vv = v as usize; let mut s = target; while s >= vv { if dp[s - vv] { dp[s] = true; } if s == 0 { break; } s -= 1; } }
    dp[target]
}
```
