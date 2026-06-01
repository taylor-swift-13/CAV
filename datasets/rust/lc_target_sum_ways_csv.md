# LC Target Sum Ways CSV

## Problem

Return how many sign assignments make comma-separated nonnegative integers sum to `target`.

## Requirements

- `nums` contains nonnegative integers.
- The transformed subset sum fits the fixed DP capacity used by the tests.

## Source

- Source: LeetCode problem `target-sum`.
- URL: https://leetcode.com/problems/target-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_target_sum_ways_csv(nums: &str, target: i32) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let total: i32 = a.iter().sum(); let mut want = total + target; if want < 0 || want % 2 != 0 { return 0; } want /= 2; let mut dp = vec![0; (want + 1) as usize]; dp[0] = 1;
    for &v in &a { let mut s = want; while s >= v { dp[s as usize] += dp[(s - v) as usize]; s -= 1; } } dp[want as usize]
}
```
