# LC Kth Largest Element CSV

## Problem

Return the `k`th largest value in comma-separated `nums`.

## Requirements

- `nums` is nonempty.
- `1 <= k <= len(nums)`.

## Source

- Source: LeetCode problem `kth-largest-element-in-an-array`.
- URL: https://leetcode.com/problems/kth-largest-element-in-an-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_kth_largest_csv(nums: &str, k: i32) -> i32 {
    let mut a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.sort(); a[a.len() - k as usize]
}
```
