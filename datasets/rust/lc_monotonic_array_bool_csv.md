# LC Monotonic Array Bool CSV

## Problem

Return true if comma-separated `nums` is monotone nondecreasing or nonincreasing.

## Requirements

- `nums` is nonempty.

## Source

- Source: LeetCode problem `monotonic-array`.
- URL: https://leetcode.com/problems/monotonic-array/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_monotonic_array_bool_csv(nums: &str) -> bool {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut inc = true; let mut dec = true; let mut i = 1usize; while i < a.len() { if a[i] < a[i - 1] { inc = false; } if a[i] > a[i - 1] { dec = false; } i += 1; } inc || dec
}
```
