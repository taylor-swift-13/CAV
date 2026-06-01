# LC Boats To Save People Count CSV

## Problem

Return the minimum number of boats needed to rescue everyone.

## Requirements

- `people` is a comma-separated list of weights.
- Each boat carries at most two people with total weight at most `limit`.

## Source

- Source: LeetCode problem `boats-to-save-people`.
- URL: https://leetcode.com/problems/boats-to-save-people/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_boats_rescue_count_csv(people: &str, limit: i32) -> i32 {
    let mut a: Vec<i32> = people.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.sort(); let mut l = 0usize; let mut r = a.len() as i32 - 1; let mut boats = 0; while l as i32 <= r { if a[l] + a[r as usize] <= limit { l += 1; } r -= 1; boats += 1; } boats
}
```
