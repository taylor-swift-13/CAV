# missing_number_csv

## Problem

Given `n` and a comma-separated list containing `n` distinct numbers from `0..n`, return the missing number.

## Requirements

- `n >= 1`.
- `nums` encodes exactly `n` distinct integers unless `n == 1` and the encoded list is empty.
- The represented set is a subset of `0..n` with one value missing.
- Return the missing value, not its position.

## Source

- Source: LeetCode problem `missing-number`.
- URL: https://leetcode.com/problems/missing-number/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn missing_number_csv(n: i32, nums: &str) -> i32 {
    let expected = n * (n + 1) / 2;
    if nums.is_empty() { return expected; }
    let sum: i32 = nums.split(',').map(|x| x.parse::<i32>().unwrap()).sum();
    expected - sum
}
```
