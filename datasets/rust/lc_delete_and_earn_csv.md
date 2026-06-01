# LC Delete And Earn CSV

## Problem

Return the maximum points from the delete-and-earn rule.

## Requirements

- `nums` is a nonempty comma-separated list of positive integers less than 1000.

## Source

- Source: LeetCode problem `delete-and-earn`.
- URL: https://leetcode.com/problems/delete-and-earn/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_delete_and_earn_csv(nums: &str) -> i32 {
    let mut points = vec![0; 1000]; let mut maxv = 0usize; for part in nums.split(',') { let v = part.parse::<usize>().unwrap(); points[v] += v as i32; if v > maxv { maxv = v; } } let mut take = 0; let mut skip = 0; let mut v = 1usize; while v <= maxv { let ntake = skip + points[v]; let nskip = if take > skip { take } else { skip }; take = ntake; skip = nskip; v += 1; } if take > skip { take } else { skip }
}
```
