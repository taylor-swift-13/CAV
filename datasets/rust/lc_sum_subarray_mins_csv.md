# LC Sum Of Subarray Minimums CSV

## Problem

Return the sum of the minimum value of every contiguous subarray.

## Requirements

- `arr` is a comma-separated list of positive integers.
- The supplied sums fit in signed 32-bit range.

## Source

- Source: LeetCode problem `sum-of-subarray-minimums`.
- URL: https://leetcode.com/problems/sum-of-subarray-minimums/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_sum_subarray_mins_csv(arr: &str) -> i32 {
    let a: Vec<i32> = arr.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut sum = 0; let mut l = 0usize; while l < a.len() { let mut mn = a[l]; let mut r = l; while r < a.len() { if a[r] < mn { mn = a[r]; } sum += mn; r += 1; } l += 1; } sum
}
```
