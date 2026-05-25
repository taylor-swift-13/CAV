# running_sum_csv

## Problem

Return the running sum of comma-separated integer array `nums`.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Each output value is the sum from index `0` through that index.
- Return the output as comma-separated integers.

## Source

- Source: LeetCode problem `running-sum-of-1d-array`.
- URL: https://leetcode.com/problems/running-sum-of-1d-array/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn running_sum_csv(nums: &str) -> String {
    if nums.is_empty() { return String::new(); }
    let mut sum = 0; let mut out: Vec<String> = Vec::new();
    for p in nums.split(',') { sum += p.parse::<i32>().unwrap(); out.push(sum.to_string()); }
    out.join(",")
}
```
