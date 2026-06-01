# LC Search Rotated Index CSV

## Problem

Return the index of `target` in a rotated sorted distinct integer array, or `-1` if absent.

## Requirements

- `nums` is comma-separated and nonempty.
- Values are distinct.

## Source

- Source: LeetCode problem `search-in-rotated-sorted-array`.
- URL: https://leetcode.com/problems/search-in-rotated-sorted-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_search_rotated_index_csv(nums: &str, target: i32) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();
    let mut l = 0i32; let mut r = a.len() as i32 - 1;
    while l <= r { let mid = l + (r - l) / 2; let mv = a[mid as usize]; if mv == target { return mid; } if a[l as usize] <= mv { if a[l as usize] <= target && target < mv { r = mid - 1; } else { l = mid + 1; } } else if mv < target && target <= a[r as usize] { l = mid + 1; } else { r = mid - 1; } }
    -1
}
```
