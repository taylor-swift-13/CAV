# LC Range Sum Query CSV

## Problem

Return the sum of comma-separated `nums[left..right]` inclusive.

## Requirements

- `nums` is nonempty.
- `0 <= left <= right < len(nums)`.

## Source

- Source: LeetCode problem `range-sum-query-immutable`.
- URL: https://leetcode.com/problems/range-sum-query-immutable/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_range_sum_query_csv(nums: &str, left: i32, right: i32) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut sum = 0; let mut i = left as usize; while i <= right as usize { sum += a[i]; i += 1; } sum
}
```
