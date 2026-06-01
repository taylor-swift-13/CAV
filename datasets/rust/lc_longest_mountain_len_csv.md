# LC Longest Mountain Length CSV

## Problem

Return the length of the longest mountain subarray.

## Requirements

- A mountain strictly increases then strictly decreases and has length at least 3.

## Source

- Source: LeetCode problem `longest-mountain-in-array`.
- URL: https://leetcode.com/problems/longest-mountain-in-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_longest_mountain_len_csv(arr: &str) -> i32 {
    let a: Vec<i32> = arr.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut best = 0; let mut peak = 1usize; while peak + 1 < a.len() { if a[peak - 1] < a[peak] && a[peak] > a[peak + 1] { let mut l = peak; let mut r = peak; while l > 0 && a[l - 1] < a[l] { l -= 1; } while r + 1 < a.len() && a[r] > a[r + 1] { r += 1; } let len = (r - l + 1) as i32; if len > best { best = len; } } peak += 1; } best
}
```
