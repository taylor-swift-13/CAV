# LC Predict The Winner Bool CSV

## Problem

Return true if player 1 can win or tie under optimal play.

## Requirements

- `nums` is a nonempty comma-separated list of scores.
- Each turn takes one number from either end.

## Source

- Source: LeetCode problem `predict-the-winner`.
- URL: https://leetcode.com/problems/predict-the-winner/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_predict_winner_bool_csv(nums: &str) -> bool {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let n = a.len(); let mut dp = a.clone(); let mut len = 2usize; while len <= n { let mut l = 0usize; while l + len <= n { let r = l + len - 1; dp[l] = (a[l] - dp[l + 1]).max(a[r] - dp[l]); l += 1; } len += 1; } dp[0] >= 0
}
```
