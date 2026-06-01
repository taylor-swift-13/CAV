# LC Count Nice Pairs CSV

## Problem

Return the number of nice pairs where `nums[i] + rev(nums[j]) == nums[j] + rev(nums[i])`.

## Requirements

- `nums` is a comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `count-nice-pairs-in-an-array`.
- URL: https://leetcode.com/problems/count-nice-pairs-in-an-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_count_nice_pairs_csv(nums: &str) -> i32 {
    fn rev(mut x: i32) -> i32 { let mut r = 0; while x > 0 { r = r * 10 + x % 10; x /= 10; } r } let a: Vec<i32> = nums.split(',').map(|x| { let v = x.parse::<i32>().unwrap(); v - rev(v) }).collect(); let mut ans = 0; let mut i = 0usize; while i < a.len() { let mut j = i + 1; while j < a.len() { if a[i] == a[j] { ans += 1; } j += 1; } i += 1; } ans
}
```
