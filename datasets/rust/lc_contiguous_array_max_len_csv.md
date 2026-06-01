# LC Contiguous Array Max Length CSV

## Problem

Return the maximum length of a contiguous subarray with equal numbers of 0 and 1.

## Requirements

- `nums` is a comma-separated binary array.

## Source

- Source: LeetCode problem `contiguous-array`.
- URL: https://leetcode.com/problems/contiguous-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_contiguous_array_max_len_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut first = vec![-2; 2 * a.len() + 1]; let off = a.len() as i32; first[off as usize] = -1; let mut sum = 0; let mut best = 0; let mut i = 0usize; while i < a.len() { sum += if a[i] == 1 { 1 } else { -1 }; let key = (sum + off) as usize; if first[key] == -2 { first[key] = i as i32; } else { let len = i as i32 - first[key]; if len > best { best = len; } } i += 1; } best
}
```
