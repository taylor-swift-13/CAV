# LC Rotate Array First CSV

## Problem

Rotate comma-separated `nums` to the right by `k` steps and return the first element after rotation.

## Requirements

- `nums` is nonempty.
- `k >= 0`.

## Source

- Source: LeetCode problem `rotate-array`.
- URL: https://leetcode.com/problems/rotate-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_rotate_array_first_csv(nums: &str, k: i32) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let n = a.len(); let kk = k as usize % n; a[(n - kk) % n]
}
```
