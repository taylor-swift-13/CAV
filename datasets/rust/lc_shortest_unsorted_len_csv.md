# LC Shortest Unsorted Continuous Subarray Length CSV

## Problem

Return the shortest subarray length that must be sorted to make the whole array sorted.

## Requirements

- `nums` is a comma-separated list of signed integers.

## Source

- Source: LeetCode problem `shortest-unsorted-continuous-subarray`.
- URL: https://leetcode.com/problems/shortest-unsorted-continuous-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_shortest_unsorted_len_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut b = a.clone(); b.sort(); let mut l = 0usize; while l < a.len() && a[l] == b[l] { l += 1; } if l == a.len() { return 0; } let mut r = a.len() - 1; while a[r] == b[r] { r -= 1; } (r - l + 1) as i32
}
```
