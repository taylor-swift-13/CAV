# LC Find Peak Index CSV

## Problem

Return an index `i` such that `nums[i]` is greater than its neighbors; endpoints only need their one neighbor.

## Requirements

- `nums` is nonempty.
- Adjacent values are distinct in the supplied tests.

## Source

- Source: LeetCode problem `find-peak-element`.
- URL: https://leetcode.com/problems/find-peak-element/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_find_peak_index_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut l = 0usize; let mut r = a.len() - 1;
    while l < r { let m = l + (r - l) / 2; if a[m] < a[m + 1] { l = m + 1; } else { r = m; } }
    l as i32
}
```
